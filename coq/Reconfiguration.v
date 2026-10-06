(* Reconfiguration.v: reconfiguration inside a run (gap 20 of REGIME-AUDIT.md). Axiom-free.

   Every other module fixes the topology and the rules for a whole run. Here a run starts under
   a configuration A, switches once to a configuration B, and finishes under B. Events submitted
   under A may still be in flight at the switch: they are then applied under B's rules, through a
   translation tau. The switch may also transform the state, by a migration map m.

   1. Single registry (the Governance Rewrite System of Governance.v under free delivery, the
      setting of GovernanceConverse.cc_exact_from). A = (applyA, rhoA, rhoA_star, validA) on
      states SA and events EA; B = (applyB, rhoB, rhoB_star, validB) on SB and EB; m : SA -> SB;
      tau : EA -> EB. A run is a word of the combined system (lstep sw):
        InA s Ba Bb  -> InA s' Ba' Bb               an A step (apply an A-event, or compensate)
        InA s Ba Bb  -> InB (m s, map tau Ba ++ Bb)  the switch, allowed when sw s Ba
        InB c        -> InB c'                      a B step
      Bb are the B-events submitted after the switch; the A-events still in Ba at the switch are
      in flight and become B-events. The live switch may happen anywhere (sw = live_sw); the
      barrier switch only at a quiescent configuration, an A normal form (sw = barrier_sw: no
      event in flight, the state repaired). LiveConv s0 and BarConv s0: every pair of buffers
      (Ba, Bb) has a unique normal form from InA s0 Ba Bb.

      Write gov e x := rho_star (apply e x), f := rhoB_star o m (migrate, then repair under B),
      and CCB x for CC1 and CC2 of B on the states B reaches from x (cc_exact_from's condition).

      - barrier_exact: BarConv s0 <-> BarCond s0, where BarCond s0 is
          CCB (m t) for every quiescent t reachable from s0           (B converges after the switch)
          and AmodF s0: the A normal forms of each buffer agree after f (A converges modulo f).
      - barrier_exact_faithful: when f is injective on the quiescent states reachable from s0
        (Faithful s0), AmodF s0 is A's own condition, so
          BarConv s0 <-> CCA s0 /\ (CCB (m t) for every quiescent reachable t).
        This is the audit's claim (a change at a quiescent barrier reduces to two runs of the
        existing cells), with the qualifier it needs: forgetful_migration shows a migration that
        is not faithful hides a divergence of A.
      - live_exact (the main theorem): LiveConv s0 <-> LiveCond s0, where LiveCond s0 is
          (B)  CCB (m s) for EVERY s reachable from s0 under A, quiescent or not;
          (S1) rhoB_star (m (applyA e s)) = rhoB_star (applyB (tau e) (m s)) for every reachable s
               and every A-event e (an in-flight event commutes with the switch);
          (S2) rhoB_star (m (rhoA s)) = rhoB_star (m s) for every reachable invalid s (the switch
               absorbs A's compensation).
        These are the cross-configuration critical pairs: an A-step against the switch.
        A's own condition is NOT a conjunct: it is implied modulo f (live_implies_barrier), and
        exactly when Faithful s0 (live_exact_faithful: LiveConv s0 <-> CCA s0 /\ LiveCond s0).
      - live_no_change: with B = A, m and tau identities, LiveConv s0 <-> CCA s0, which is
        cc_exact_from: the theorem recovers the single-configuration result.
      - Witnesses (each failing conjunct is a divergence, built from the runs): s1_runs,
        s2_runs, live_b_runs and barrier_b_runs (CCB failures via cc1/cc2_fail_diverge_from),
        amodf_runs.
      Counterexamples (A converges from the start and B from the migrated start, the barrier
      switch converges, the live one diverges; each fails exactly one conjunct of LiveCond):
      - cap_raise: a cap of 5 raised to 10 with in-flight adds. (S2) fails: an add applied under
        A is clamped at 5 and stays 5; switched first, it is applied under B and gives 6.
      - doubling_migration: m doubles the state, the event adds 1 on both sides. (S1) fails.
      - migrated_transient: A-states between an event and its repair are migrated; B repairs the
        migrated raw state differently. (B) fails at m s for a non-quiescent s only.
      - forgetful_migration: A diverges, the migration forgets the difference, every live run
        converges: A's condition is not necessary, and BarConv holds without CCA.
      Non-vacuity: rescaled_cap (cap 5 to cap 10 with m doubling and each A add becoming an add
      of 2, with native B adds of 1): online-safe, with every condition and Faithful holding.
      lww_target (a last-writer-wins B): unsafe. instances_classified classifies all six;
      finite_instance discharges the hypotheses of classify_finite.

   2. Classification (the basis of gsm's planned CheckMigration). Classified s0 o for
      o in {Online, BarrierOnly, Unsafe}: LiveConv; BarConv and not LiveConv; not BarConv.
      - classified_unique: at most one outcome holds (live_implies_barrier).
      - classify: given decisions of LiveCond and BarCond, exactly one is produced.
      - Finite instances (finite state and event lists, decidable validity and equality):
        reach is decidable (reach_dec, by a generic closure computation, star_fin_dec), hence
        LiveConv is decidable (live_dec); under Faithful s0 so is BarConv (barrier_dec_faithful),
        and Faithful s0 itself is decidable (faithful_dec); classify_finite returns the outcome.
        Without Faithful, CCA s0 plus the B part is sufficient for BarConv (barrier_sufficient).

   3. Federations: topology changes (FedMachine semantics of FederationEvents.v: every Apply
      normalizes, so what is in flight at the switch is the buffered events). A generic
      deterministic form first (section Det): steps stepA, stepB, an equivalence on B-states
      respected by stepB, a migration M and a translation tau, free delivery. A live run applies
      a permutation of u under A, migrates, then a permutation of the in-flight rest (translated)
      together with the B-events.
      - det_live_exact: DLive s0 <-> PermB (M s0) /\ DS1 s0, where PermB x says every
        permutation of B-events from x agrees and DS1 s0 says M (stepA e t) ~ stepB (tau e) (M t)
        at every reachable t. The B-condition is needed only at the migrated START: DS1 carries
        it to every reachable A-state.
      - det_barrier_exact, det_barrier_faithful: the barrier form, with the B-condition at every
        migrated reachable state and A's condition modulo M (exactly A's when M reflects ~).
      - fed_live_exact, fed_barrier_exact: the FedMachine instances. A and B are two acyclic
        federations with their own topology (src, f, o) and events; M is the migration (for
        instance B's normalizer: the new edges propagate once, a new registry is initialized).
        By fed_exact, PermB is C1R1 /\ C2R of B (every same-registry pair declared), so
          live:    DLive s0 <-> C1R1_B (M s0) /\ C2R_B (M s0) /\ DS1 s0
          barrier: DBar s0 <-> C1R1_A s0 /\ C2R_A s0 /\ forall u, C1R1_B /\ C2R_B at M (runF_A u s0)
        (barrier under: M maps valid consistent states to valid consistent states, and M
        reflects and preserves feq).
      - late_edge: adding an edge 0 -> 1 whose target event reads the shared part. A and B each
        converge and the barrier switch converges, but an event submitted before the edge and
        applied after it reads the new source value: the live switch diverges. late_edge_fresh:
        from a start whose target already agrees with the new image, the same change is
        online-safe, and fed_live_exact's hypotheses all hold (non-vacuity).

   Scope. The live theorems are exact for the single registry under free delivery (rewriting
   model with compensation steps) and for federations under FedMachine semantics. Not covered:
   a live switch in the distributed model, where propagation (projections sent under A, merged
   under B) is itself in flight (DistributedExact.v's model); declared independence or causal
   and at-least-once delivery across the switch; and a local (finite) form of AmodF when the
   migration is not faithful. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.Trace NC.FederationEvents
  NC.FederationEventsConverse.
Import ListNotations.

(* ============================================================================================ *)
(* Preliminaries.                                                                                *)
(* ============================================================================================ *)

Lemma perm_remove1 : forall {E : Type} (dec : forall a b : E, {a = b} + {a <> b}) e l,
  In e l -> Permutation l (e :: remove1 dec e l).
Proof.
  intros E dec e l. induction l as [| x l IH]; intros H; [destruct H |].
  simpl. destruct (dec x e) as [-> | Hne].
  - apply Permutation_refl.
  - destruct H as [-> | H]; [contradiction |].
    eapply Permutation_trans; [apply perm_skip, IH, H | apply perm_swap].
Qed.

Lemma remove1_head : forall {E : Type} (dec : forall a b : E, {a = b} + {a <> b}) e l,
  remove1 dec e (e :: l) = l.
Proof. intros. simpl. destruct (dec e e) as [_ | N]; [reflexivity | contradiction]. Qed.

Lemma reach_trans : forall {S E : Type} (apply : E -> S -> S) rho valid x y z,
  reach apply rho valid x y -> reach apply rho valid y z -> reach apply rho valid x z.
Proof.
  intros S E apply rho valid x y z H1 H2.
  induction H2 as [| e s _ IH | s _ IH Hinv].
  - exact H1.
  - apply r_apply. exact IH.
  - apply r_comp; [exact IH | exact Hinv].
Qed.

(* The states a run of the free system reaches are reachable. *)
Lemma star_reach : forall {S E : Type} (dec : forall a b : E, {a = b} + {a <> b})
  (apply : E -> S -> S) rho valid x L y L',
  star (step dec apply rho valid free_enabled) (x, L) (y, L') -> reach apply rho valid x y.
Proof.
  intros S E dec apply rho valid x L y L' H.
  exact (star_closed _ (fun c => reach apply rho valid x (fst c))
           (fun c d Hc Hs => reach_step dec apply rho valid free_enabled x c d Hc Hs)
           (x, L) (y, L') (r_init _ _ _ _) H).
Qed.

(* A normal form of the free system has an empty buffer. *)
Lemma nf_free_nil : forall {S E : Type} (dec : forall a b : E, {a = b} + {a <> b})
  (apply : E -> S -> S) rho valid s B,
  normal_form (step dec apply rho valid free_enabled) (s, B) -> B = [].
Proof.
  intros S E dec apply rho valid s B H. destruct B as [| e B]; [reflexivity |].
  exfalso. apply H. eexists. apply st_apply; [left; reflexivity | unfold free_enabled; left; reflexivity].
Qed.

(* ============================================================================================ *)
(* 1. Single registry: the switch model.                                                         *)
(* ============================================================================================ *)

Section Switch.
  Context {SA EA SB EB : Type}.
  Variable eqA : forall a b : EA, {a = b} + {a <> b}.
  Variable eqB : forall a b : EB, {a = b} + {a <> b}.
  Variable applyA : EA -> SA -> SA.
  Variables rhoA rhoA_star : SA -> SA.
  Variable validA : SA -> Prop.
  Variable PhiA : SA -> nat.
  Variable applyB : EB -> SB -> SB.
  Variables rhoB rhoB_star : SB -> SB.
  Variable validB : SB -> Prop.
  Variable PhiB : SB -> nat.
  Variable m : SA -> SB.
  Variable tau : EA -> EB.

  Local Notation stA := (step eqA applyA rhoA validA free_enabled).
  Local Notation stB := (step eqB applyB rhoB validB free_enabled).
  Local Notation reachA := (reach applyA rhoA validA).
  Local Notation reachB := (reach applyB rhoB validB).
  Local Notation govA e s := (rhoA_star (applyA e s)).
  Local Notation govB e x := (rhoB_star (applyB e x)).

  Hypothesis wfcA : forall s, ~ validA s -> PhiA (rhoA s) < PhiA s.
  Hypothesis reachA_star : forall s B, star stA (s, B) (rhoA_star s, B).
  Hypothesis validA_star : forall s, validA (rhoA_star s).
  Hypothesis wfcB : forall x, ~ validB x -> PhiB (rhoB x) < PhiB x.
  Hypothesis reachB_star : forall x L, star stB (x, L) (rhoB_star x, L).
  Hypothesis validB_star : forall x, validB (rhoB_star x).

  (* ---- The combined system. ---- *)

  Inductive cfg : Type :=
  | InA : SA -> list EA -> list EB -> cfg
  | InB : SB * list EB -> cfg.

  Inductive lstep (sw : SA -> list EA -> Prop) : cfg -> cfg -> Prop :=
  | l_a : forall s Ba s' Ba' Bb, stA (s, Ba) (s', Ba') -> lstep sw (InA s Ba Bb) (InA s' Ba' Bb)
  | l_sw : forall s Ba Bb, sw s Ba -> lstep sw (InA s Ba Bb) (InB (m s, map tau Ba ++ Bb))
  | l_b : forall c c', stB c c' -> lstep sw (InB c) (InB c').

  (* The live switch may happen anywhere; the barrier switch only at an A normal form. *)
  Definition live_sw (_ : SA) (_ : list EA) : Prop := True.
  Definition barrier_sw (s : SA) (Ba : list EA) : Prop := normal_form stA (s, Ba).

  Definition LiveConv (s0 : SA) : Prop := forall Ba Bb, UN (lstep live_sw) (InA s0 Ba Bb).
  Definition BarConv (s0 : SA) : Prop := forall Ba Bb, UN (lstep barrier_sw) (InA s0 Ba Bb).

  (* cc_exact_from's condition for A from s0 and for B from x. *)
  Definition CCA (s0 : SA) : Prop :=
    (forall s e1 e2, reachA s0 s -> govA e2 (govA e1 s) = govA e1 (govA e2 s)) /\
    (forall s e, reachA s0 s -> ~ validA s -> govA e s = govA e (rhoA s)).
  Definition CCB (x : SB) : Prop :=
    (forall y e1 e2, reachB x y -> govB e2 (govB e1 y) = govB e1 (govB e2 y)) /\
    (forall y e, reachB x y -> ~ validB y -> govB e y = govB e (rhoB y)).

  (* The cross-configuration critical pairs. *)
  Definition S1 (s0 : SA) : Prop := forall s e, reachA s0 s ->
    rhoB_star (m (applyA e s)) = rhoB_star (applyB (tau e) (m s)).
  Definition S2 (s0 : SA) : Prop := forall s, reachA s0 s -> ~ validA s ->
    rhoB_star (m (rhoA s)) = rhoB_star (m s).

  Definition LiveCond (s0 : SA) : Prop :=
    (forall s, reachA s0 s -> CCB (m s)) /\ S1 s0 /\ S2 s0.

  (* A converges modulo f := rhoB_star o m. *)
  Definition AmodF (s0 : SA) : Prop := forall Ba t1 t2,
    star stA (s0, Ba) (t1, []) -> normal_form stA (t1, []) ->
    star stA (s0, Ba) (t2, []) -> normal_form stA (t2, []) ->
    rhoB_star (m t1) = rhoB_star (m t2).

  Definition BarB (s0 : SA) : Prop :=
    forall t, reachA s0 t -> normal_form stA (t, []) -> CCB (m t).

  Definition BarCond (s0 : SA) : Prop := BarB s0 /\ AmodF s0.

  (* f is injective on the quiescent states reachable from s0. *)
  Definition Faithful (s0 : SA) : Prop := forall t1 t2, reachA s0 t1 -> reachA s0 t2 ->
    normal_form stA (t1, []) -> normal_form stA (t2, []) ->
    rhoB_star (m t1) = rhoB_star (m t2) -> t1 = t2.

  (* ---- B under its condition: the normal form is a fold. ---- *)

  Definition FB (y : SB) (L : list EB) : SB := fold_left (fun z e => govB e z) L y.
  Definition GB (x : SB) (L : list EB) : SB := FB (rhoB_star x) L.

  Lemma runB_FB : forall L y, star stB (y, L) (FB y L, []).
  Proof.
    induction L as [| e L IH]; intros y; [apply star_refl |].
    eapply star_step.
    - apply st_apply; [left; reflexivity | unfold free_enabled; left; reflexivity].
    - rewrite remove1_head. eapply star_trans; [apply reachB_star | apply IH].
  Qed.

  Lemma FB_valid : forall L y, validB y -> validB (FB y L).
  Proof.
    induction L as [| e L IH]; intros y Hy; [exact Hy |].
    simpl. apply IH. apply validB_star.
  Qed.

  Lemma GB_run : forall x L, star stB (x, L) (GB x L, []) /\ normal_form stB (GB x L, []).
  Proof.
    intros x L. split.
    - eapply star_trans; [apply reachB_star | apply runB_FB].
    - apply nf_valid_empty. apply FB_valid. apply validB_star.
  Qed.

  Lemma CCB_UN : forall x, CCB x -> forall L, UN stB (x, L).
  Proof.
    intros x H. exact (proj2 (cc_exact_from eqB applyB rhoB rhoB_star validB PhiB wfcB
                               reachB_star validB_star x) H).
  Qed.

  Lemma UN_CCB : forall x, (forall L, UN stB (x, L)) -> CCB x.
  Proof.
    intros x H. exact (proj1 (cc_exact_from eqB applyB rhoB rhoB_star validB PhiB wfcB
                               reachB_star validB_star x) H).
  Qed.

  Lemma nfB_GB : forall x L n, CCB x -> star stB (x, L) n -> normal_form stB n -> n = (GB x L, []).
  Proof.
    intros x L n H S N. destruct (GB_run x L) as [S' N'].
    exact (CCB_UN x H L n (GB x L, []) S N S' N').
  Qed.

  Lemma CCB_reach : forall x y, CCB x -> reachB x y -> CCB y.
  Proof.
    intros x y [H1 H2] Hr. split.
    - intros z e1 e2 Hz. apply H1. exact (reach_trans _ _ _ _ _ _ Hr Hz).
    - intros z e Hz. apply H2. exact (reach_trans _ _ _ _ _ _ Hr Hz).
  Qed.

  Lemma reachB_gov : forall x y e, reachB x y -> reachB x (govB e y).
  Proof.
    intros x y e H. apply (reach_trans _ _ _ _ (applyB e y)); [apply r_apply; exact H |].
    exact (star_reach eqB applyB rhoB validB _ [] _ [] (reachB_star (applyB e y) [])).
  Qed.

  Lemma reachB_rho_star : forall x, reachB x (rhoB_star x).
  Proof. intros x. exact (star_reach eqB applyB rhoB validB _ [] _ [] (reachB_star x [])). Qed.

  Lemma govB_rho : forall x e, CCB x -> govB e x = govB e (rhoB_star x).
  Proof.
    intros x e H.
    assert (S : star stB (x, [e]) (govB e x, [])).
    { eapply star_step; [apply st_apply; [left; reflexivity | unfold free_enabled; left; reflexivity] |].
      rewrite remove1_head. apply reachB_star. }
    pose proof (nfB_GB x [e] _ H S (nf_valid_empty eqB applyB rhoB validB _ (validB_star _))) as E.
    injection E as E. exact E.
  Qed.

  Lemma FB_perm : forall x, CCB x -> forall L L', Permutation L L' ->
    forall y, reachB x y -> FB y L = FB y L'.
  Proof.
    intros x Hx L L' P. induction P as [| a l l' P IH | a b l | l l' l'' P1 IH1 P2 IH2];
      intros y Hy.
    - reflexivity.
    - simpl. apply IH. apply reachB_gov. exact Hy.
    - simpl. rewrite (proj1 Hx y a b Hy). reflexivity.
    - rewrite (IH1 y Hy). apply IH2. exact Hy.
  Qed.

  Lemma GB_perm : forall x L L', CCB x -> Permutation L L' -> GB x L = GB x L'.
  Proof.
    intros x L L' H P. unfold GB. apply (FB_perm x H L L' P). apply reachB_rho_star.
  Qed.

  (* ---- Runs of the combined system. ---- *)

  Lemma lift_A : forall sw s Ba s' Ba' Bb, star stA (s, Ba) (s', Ba') ->
    star (lstep sw) (InA s Ba Bb) (InA s' Ba' Bb).
  Proof.
    intros sw s Ba s' Ba' Bb S.
    assert (G : forall c c', star stA c c' ->
      star (lstep sw) (InA (fst c) (snd c) Bb) (InA (fst c') (snd c') Bb)).
    { intros c c' S'. induction S' as [c | c d c'' H _ IH]; [apply star_refl |].
      eapply star_step; [| exact IH]. destruct c, d. apply l_a. exact H. }
    exact (G _ _ S).
  Qed.

  Lemma lift_B : forall sw c c', star stB c c' -> star (lstep sw) (InB c) (InB c').
  Proof.
    intros sw c c' S. induction S as [c | c d c'' H S IH].
    - apply star_refl.
    - eapply star_step; [apply l_b; exact H | exact IH].
  Qed.

  Lemma nf_InB : forall sw c, normal_form (lstep sw) (InB c) <-> normal_form stB c.
  Proof.
    intros sw c. split.
    - intros H [d Hd]. apply H. exists (InB d). apply l_b. exact Hd.
    - intros H [y Hy]. inversion Hy as [| | c1 c' Hs]; subst. apply H. exists c'. exact Hs.
  Qed.

  Lemma lstep_B_inv : forall sw c n, star (lstep sw) (InB c) n ->
    exists c', n = InB c' /\ star stB c c'.
  Proof.
    intros sw c n S. remember (InB c) as x eqn:Ex. revert c Ex.
    induction S as [x | x y z H S IH]; intros c Ex; subst.
    - exists c. split; [reflexivity | apply star_refl].
    - inversion H as [| | c1 c' Hs]; subst.
      destruct (IH c' eq_refl) as [c'' [-> S']]. exists c''. split; [reflexivity |].
      eapply star_step; [exact Hs | exact S'].
  Qed.

  (* Every normal form of a run from InA s Ba Bb comes after exactly one switch. *)
  Lemma lstep_decomp : forall sw,
    (forall s Ba Bb, ~ normal_form (lstep sw) (InA s Ba Bb)) ->
    forall s Ba Bb n, star (lstep sw) (InA s Ba Bb) n -> normal_form (lstep sw) n ->
    exists s' Ba' c, star stA (s, Ba) (s', Ba') /\ sw s' Ba' /\
      star stB (m s', map tau Ba' ++ Bb) c /\ normal_form stB c /\ n = InB c.
  Proof.
    intros sw Hnot s Ba Bb n S. remember (InA s Ba Bb) as x eqn:Ex. revert s Ba Ex.
    induction S as [x | x y z H S IH]; intros s Ba Ex Hn; subst.
    - exfalso. exact (Hnot s Ba Bb Hn).
    - inversion H as [s1 B1 s' Ba' Bb1 Hs | s1 B1 Bb1 Hsw | ]; subst.
      + destruct (IH s' Ba' eq_refl Hn) as [s'' [Ba'' [c [SA' [Hsw [SB' [Nc Ec]]]]]]].
        exists s'', Ba'', c. split; [eapply star_step; [exact Hs | exact SA'] |].
        repeat split; assumption.
      + destruct (lstep_B_inv sw _ _ S) as [c [-> Sc]].
        exists s, Ba, c. split; [apply star_refl |]. split; [exact Hsw |].
        split; [exact Sc |]. split; [exact (proj1 (nf_InB sw c) Hn) | reflexivity].
  Qed.

  Lemma live_not_nf : forall s Ba Bb, ~ normal_form (lstep live_sw) (InA s Ba Bb).
  Proof. intros s Ba Bb H. apply H. eexists. apply l_sw. exact I. Qed.

  Lemma barrier_not_nf : forall s Ba Bb, ~ normal_form (lstep barrier_sw) (InA s Ba Bb).
  Proof.
    intros s Ba Bb H. apply H. eexists. apply l_sw. intros [[s' Ba'] Hs].
    apply H. eexists. apply l_a. exact Hs.
  Qed.

  (* The runs every necessity proof and every witness uses. *)

  (* Switch at a reachable state: every B normal form from (m s, Bb) is a run normal form. *)
  Lemma switch_runs : forall sw s0 s Bb c, reachA s0 s -> sw s [] ->
    star stB (m s, Bb) c -> normal_form stB c ->
    exists w, star (lstep sw) (InA s0 w Bb) (InB c) /\ normal_form (lstep sw) (InB c).
  Proof.
    intros sw s0 s Bb c Hr Hsw S N. destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w Hw].
    exists w. split; [| exact (proj2 (nf_InB sw c) N)].
    eapply star_trans; [apply lift_A; pose proof (Hw []) as H; rewrite app_nil_r in H; exact H |].
    eapply star_step; [apply l_sw; exact Hsw |]. simpl. apply lift_B. exact S.
  Qed.

  (* (S1): applying e under A then switching, and switching then applying tau e under B. *)
  Theorem s1_runs : forall s0 s e, reachA s0 s -> exists w,
    star (lstep live_sw) (InA s0 (w ++ [e]) []) (InB (rhoB_star (m (applyA e s)), [])) /\
    star (lstep live_sw) (InA s0 (w ++ [e]) []) (InB (rhoB_star (applyB (tau e) (m s)), [])) /\
    normal_form (lstep live_sw) (InB (rhoB_star (m (applyA e s)), [])) /\
    normal_form (lstep live_sw) (InB (rhoB_star (applyB (tau e) (m s)), [])).
  Proof.
    intros s0 s e Hr. destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w Hw].
    exists w. split; [| split; [| split]].
    - eapply star_trans; [apply lift_A; exact (Hw [e]) |].
      eapply star_step.
      { apply l_a. apply st_apply; [left; reflexivity | unfold free_enabled; left; reflexivity]. }
      rewrite remove1_head. eapply star_step; [apply l_sw; exact I |].
      simpl. apply lift_B. apply reachB_star.
    - eapply star_trans; [apply lift_A; exact (Hw [e]) |].
      eapply star_step; [apply l_sw; exact I |]. simpl.
      apply lift_B. eapply star_step.
      { apply st_apply; [left; reflexivity | unfold free_enabled; left; reflexivity]. }
      rewrite remove1_head. apply reachB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
  Qed.

  (* (S2): switching an invalid state, and compensating under A first. *)
  Theorem s2_runs : forall s0 s, reachA s0 s -> ~ validA s -> exists w,
    star (lstep live_sw) (InA s0 w []) (InB (rhoB_star (m s), [])) /\
    star (lstep live_sw) (InA s0 w []) (InB (rhoB_star (m (rhoA s)), [])) /\
    normal_form (lstep live_sw) (InB (rhoB_star (m s), [])) /\
    normal_form (lstep live_sw) (InB (rhoB_star (m (rhoA s)), [])).
  Proof.
    intros s0 s Hr Hinv. destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w Hw].
    pose proof (Hw []) as H. rewrite app_nil_r in H.
    exists w. split; [| split; [| split]].
    - eapply star_trans; [apply lift_A; exact H |].
      eapply star_step; [apply l_sw; exact I |]. simpl. apply lift_B. apply reachB_star.
    - eapply star_trans; [apply lift_A; exact H |].
      eapply star_step; [apply l_a; apply st_comp; exact Hinv |].
      eapply star_step; [apply l_sw; exact I |]. simpl. apply lift_B. apply reachB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
  Qed.

  (* ---- The barrier theorem. ---- *)

  Lemma barB_nec : forall s0, BarConv s0 -> BarB s0.
  Proof.
    intros s0 H t Hr Hnf. apply UN_CCB. intros L n1 n2 S1' N1 S2' N2.
    destruct (switch_runs barrier_sw s0 t L n1 Hr Hnf S1' N1) as [w1 [R1 M1]].
    destruct (switch_runs barrier_sw s0 t L n2 Hr Hnf S2' N2) as [w2 [R2 M2]].
    destruct (reach_run eqA applyA rhoA validA s0 t Hr) as [w Hw].
    assert (Hwt : star stA (s0, w) (t, [])) by (pose proof (Hw []) as X; rewrite app_nil_r in X; exact X).
    assert (P : forall c, star stB (m t, L) c -> star (lstep barrier_sw) (InA s0 w L) (InB c)).
    { intros c Sc. eapply star_trans; [apply lift_A; exact Hwt |].
      eapply star_step; [apply l_sw; exact Hnf |]. apply lift_B. exact Sc. }
    pose proof (H w L (InB n1) (InB n2) (P n1 S1') M1 (P n2 S2') M2) as E.
    injection E as E. exact E.
  Qed.

  Lemma amodf_nec : forall s0, BarConv s0 -> AmodF s0.
  Proof.
    intros s0 H Ba t1 t2 S1' N1 S2' N2.
    assert (P : forall t, star stA (s0, Ba) (t, []) -> normal_form stA (t, []) ->
      star (lstep barrier_sw) (InA s0 Ba []) (InB (rhoB_star (m t), []))).
    { intros t St Nt. eapply star_trans; [apply lift_A; exact St |].
      eapply star_step; [apply l_sw; exact Nt |]. apply lift_B. apply reachB_star. }
    assert (Nf : forall t, normal_form (lstep barrier_sw) (InB (rhoB_star (m t), []))).
    { intros t. apply nf_InB. apply nf_valid_empty. apply validB_star. }
    pose proof (H Ba [] _ _ (P t1 S1' N1) (Nf t1) (P t2 S2' N2) (Nf t2)) as E.
    injection E as E. exact E.
  Qed.

  Theorem barrier_exact : forall s0, BarConv s0 <-> BarCond s0.
  Proof.
    intros s0. split.
    - intros H. split; [apply barB_nec | apply amodf_nec]; exact H.
    - intros [HB HA] Ba Bb n1 n2 S1' N1 S2' N2.
      destruct (lstep_decomp barrier_sw barrier_not_nf s0 Ba Bb n1 S1' N1)
        as [t1 [B1 [c1 [SA1 [Sw1 [SB1 [Nc1 ->]]]]]]].
      destruct (lstep_decomp barrier_sw barrier_not_nf s0 Ba Bb n2 S2' N2)
        as [t2 [B2 [c2 [SA2 [Sw2 [SB2 [Nc2 ->]]]]]]].
      pose proof (nf_free_nil eqA applyA rhoA validA t1 B1 Sw1) as ->.
      pose proof (nf_free_nil eqA applyA rhoA validA t2 B2 Sw2) as ->.
      simpl in SB1, SB2.
      assert (R1 : reachA s0 t1) by exact (star_reach eqA applyA rhoA validA _ _ _ _ SA1).
      assert (R2 : reachA s0 t2) by exact (star_reach eqA applyA rhoA validA _ _ _ _ SA2).
      rewrite (nfB_GB (m t1) Bb c1 (HB t1 R1 Sw1) SB1 Nc1).
      rewrite (nfB_GB (m t2) Bb c2 (HB t2 R2 Sw2) SB2 Nc2).
      unfold GB. rewrite (HA Ba t1 t2 SA1 Sw1 SA2 Sw2). reflexivity.
  Qed.

  Lemma CCA_UN_iff : forall s0, (forall Ba, UN stA (s0, Ba)) <-> CCA s0.
  Proof.
    intros s0. exact (cc_exact_from eqA applyA rhoA rhoA_star validA PhiA wfcA
                        reachA_star validA_star s0).
  Qed.

  Lemma amodf_faithful : forall s0, Faithful s0 -> (AmodF s0 <-> CCA s0).
  Proof.
    intros s0 HF. rewrite <- CCA_UN_iff. split.
    - intros H Ba [t1 B1] [t2 B2] S1' N1 S2' N2.
      pose proof (nf_free_nil eqA applyA rhoA validA t1 B1 N1) as ->.
      pose proof (nf_free_nil eqA applyA rhoA validA t2 B2 N2) as ->.
      f_equal. apply HF; try assumption.
      + exact (star_reach eqA applyA rhoA validA _ _ _ _ S1').
      + exact (star_reach eqA applyA rhoA validA _ _ _ _ S2').
      + exact (H Ba t1 t2 S1' N1 S2' N2).
    - intros H Ba t1 t2 S1' N1 S2' N2.
      pose proof (H Ba _ _ S1' N1 S2' N2) as E. injection E as ->. reflexivity.
  Qed.

  (* The audit's claim, with its qualifier: at a quiescent barrier, convergence of the run is
     convergence of each side. *)
  Theorem barrier_exact_faithful : forall s0, Faithful s0 ->
    (BarConv s0 <-> CCA s0 /\ BarB s0).
  Proof.
    intros s0 HF. rewrite barrier_exact. unfold BarCond. rewrite (amodf_faithful s0 HF).
    tauto.
  Qed.

  (* Without the qualifier, each side converging is still sufficient. *)
  Theorem barrier_sufficient : forall s0, CCA s0 -> BarB s0 -> BarConv s0.
  Proof.
    intros s0 HA HB. apply barrier_exact. split; [exact HB |].
    intros Ba t1 t2 S1' N1 S2' N2.
    pose proof (proj2 (CCA_UN_iff s0) HA Ba _ _ S1' N1 S2' N2) as E.
    injection E as ->. reflexivity.
  Qed.

  (* ---- The live theorem. ---- *)

  Lemma live_step_inv : forall s0, LiveCond s0 -> forall s Ba s' Ba' Bb, reachA s0 s ->
    stA (s, Ba) (s', Ba') -> GB (m s') (map tau Ba' ++ Bb) = GB (m s) (map tau Ba ++ Bb).
  Proof.
    intros s0 [HB [H1 H2]] s Ba s' Ba' Bb Hr Hs.
    inversion Hs as [s1 B1 e Hin Hen E1 E2 | s1 B1 Hinv E1 E2]; subst.
    - unfold GB at 1. rewrite (H1 s e Hr). rewrite (govB_rho (m s) (tau e) (HB s Hr)).
      rewrite (GB_perm (m s) (map tau Ba ++ Bb) (tau e :: map tau (remove1 eqA e Ba) ++ Bb)
                 (HB s Hr)).
      + reflexivity.
      + change (tau e :: map tau (remove1 eqA e Ba) ++ Bb)
          with ((tau e :: map tau (remove1 eqA e Ba)) ++ Bb).
        apply Permutation_app_tail.
        change (tau e :: map tau (remove1 eqA e Ba)) with (map tau (e :: remove1 eqA e Ba)).
        apply Permutation_map. apply perm_remove1. exact Hin.
    - unfold GB. rewrite (H2 s Hr Hinv). reflexivity.
  Qed.

  Lemma live_star_inv : forall s0, LiveCond s0 -> forall c c', star stA c c' ->
    reachA s0 (fst c) -> forall Bb,
    GB (m (fst c')) (map tau (snd c') ++ Bb) = GB (m (fst c)) (map tau (snd c) ++ Bb).
  Proof.
    intros s0 HL c c' S. induction S as [c | c d c' H S IH]; intros Hr Bb; [reflexivity |].
    rewrite IH; [| exact (reach_step eqA applyA rhoA validA free_enabled s0 c d Hr H)].
    destruct c as [s Ba], d as [s' Ba']. exact (live_step_inv s0 HL s Ba s' Ba' Bb Hr H).
  Qed.

  Lemma live_b_nec : forall s0, LiveConv s0 -> forall s, reachA s0 s -> CCB (m s).
  Proof.
    intros s0 H s Hr. apply UN_CCB. intros L n1 n2 S1' N1 S2' N2.
    destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w Hw].
    assert (Hws : star stA (s0, w) (s, [])) by (pose proof (Hw []) as X; rewrite app_nil_r in X; exact X).
    assert (P : forall c, star stB (m s, L) c -> star (lstep live_sw) (InA s0 w L) (InB c)).
    { intros c Sc. eapply star_trans; [apply lift_A; exact Hws |].
      eapply star_step; [apply l_sw; exact I |]. apply lift_B. exact Sc. }
    pose proof (H w L (InB n1) (InB n2) (P n1 S1') (proj2 (nf_InB _ n1) N1)
                  (P n2 S2') (proj2 (nf_InB _ n2) N2)) as E.
    injection E as E. exact E.
  Qed.

  Theorem live_exact : forall s0, LiveConv s0 <-> LiveCond s0.
  Proof.
    intros s0. split.
    - intros H. split; [| split].
      + apply live_b_nec. exact H.
      + intros s e Hr. destruct (s1_runs s0 s e Hr) as [w [R1 [R2 [N1 N2]]]].
        pose proof (H (w ++ [e]) [] _ _ R1 N1 R2 N2) as E. injection E as E. exact E.
      + intros s Hr Hinv. destruct (s2_runs s0 s Hr Hinv) as [w [R1 [R2 [N1 N2]]]].
        pose proof (H w [] _ _ R2 N2 R1 N1) as E. injection E as E. exact E.
    - intros HL Ba Bb n1 n2 S1' N1 S2' N2.
      destruct (lstep_decomp live_sw live_not_nf s0 Ba Bb n1 S1' N1)
        as [t1 [B1 [c1 [SA1 [_ [SB1 [Nc1 ->]]]]]]].
      destruct (lstep_decomp live_sw live_not_nf s0 Ba Bb n2 S2' N2)
        as [t2 [B2 [c2 [SA2 [_ [SB2 [Nc2 ->]]]]]]].
      assert (R1 : reachA s0 t1) by exact (star_reach eqA applyA rhoA validA _ _ _ _ SA1).
      assert (R2 : reachA s0 t2) by exact (star_reach eqA applyA rhoA validA _ _ _ _ SA2).
      rewrite (nfB_GB _ _ c1 (proj1 HL t1 R1) SB1 Nc1).
      rewrite (nfB_GB _ _ c2 (proj1 HL t2 R2) SB2 Nc2).
      pose proof (live_star_inv s0 HL _ _ SA1 (r_init _ _ _ _) Bb) as E1.
      pose proof (live_star_inv s0 HL _ _ SA2 (r_init _ _ _ _) Bb) as E2.
      simpl in E1, E2. rewrite E1, E2. reflexivity.
  Qed.

  Theorem live_implies_barrier : forall s0, LiveConv s0 -> BarConv s0.
  Proof.
    intros s0 H Ba Bb n1 n2 S1' N1 S2' N2.
    assert (Sub : forall x y, star (lstep barrier_sw) x y -> star (lstep live_sw) x y).
    { intros x y S. induction S as [x | x y z Hs _ IH]; [apply star_refl |].
      eapply star_step; [| exact IH].
      destruct Hs as [s Ba1 s' Ba' Bb1 Ha | s Ba1 Bb1 _ | c c' Hb].
      - apply l_a. exact Ha.
      - apply l_sw. exact I.
      - apply l_b. exact Hb. }
    assert (NfSub : forall n, normal_form (lstep barrier_sw) n -> normal_form (lstep live_sw) n).
    { intros [s Ba1 Bb1 | c] Hn.
      - exfalso. exact (barrier_not_nf s Ba1 Bb1 Hn).
      - apply nf_InB. exact (proj1 (nf_InB barrier_sw c) Hn). }
    exact (H Ba Bb n1 n2 (Sub _ _ S1') (NfSub _ N1) (Sub _ _ S2') (NfSub _ N2)).
  Qed.

  (* With a faithful migration, the live condition has the expected shape: A's condition, B's
     condition and the cross pairs. *)
  Theorem live_exact_faithful : forall s0, Faithful s0 ->
    (LiveConv s0 <-> CCA s0 /\ LiveCond s0).
  Proof.
    intros s0 HF. split.
    - intros H. split; [| apply live_exact; exact H].
      apply (proj1 (barrier_exact_faithful s0 HF)). apply live_implies_barrier. exact H.
    - intros [_ H]. apply live_exact. exact H.
  Qed.

  (* ---- Witnesses for the B conditions and for AmodF. ---- *)

  (* A CC failure of B at a state B reaches from m s (s reachable under A): two live runs from
     one start reach different normal forms. *)
  Theorem live_b_runs : forall s0 s y e1 e2, reachA s0 s -> reachB (m s) y ->
    govB e2 (govB e1 y) <> govB e1 (govB e2 y) ->
    exists w w' n1 n2, star (lstep live_sw) (InA s0 w (w' ++ [e1; e2])) n1 /\
      normal_form (lstep live_sw) n1 /\ star (lstep live_sw) (InA s0 w (w' ++ [e1; e2])) n2 /\
      normal_form (lstep live_sw) n2 /\ n1 <> n2.
  Proof.
    intros s0 s y e1 e2 Hr Hy Hne.
    destruct (cc1_fail_diverge_from eqB applyB rhoB rhoB_star validB reachB_star validB_star
                (m s) y e1 e2 Hy Hne) as [w' [n1 [n2 [S1' [N1 [S2' [N2 D]]]]]]].
    destruct (switch_runs live_sw s0 s _ n1 Hr I S1' N1) as [w [R1 M1]].
    destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w0 Hw].
    assert (Hws : star stA (s0, w0) (s, [])) by (pose proof (Hw []) as X; rewrite app_nil_r in X; exact X).
    assert (P : forall c, star stB (m s, w' ++ [e1; e2]) c ->
      star (lstep live_sw) (InA s0 w0 (w' ++ [e1; e2])) (InB c)).
    { intros c Sc. eapply star_trans; [apply lift_A; exact Hws |].
      eapply star_step; [apply l_sw; exact I |]. apply lift_B. exact Sc. }
    exists w0, w', (InB n1), (InB n2). split; [exact (P n1 S1') |].
    split; [exact (proj2 (nf_InB _ n1) N1) |]. split; [exact (P n2 S2') |].
    split; [exact (proj2 (nf_InB _ n2) N2) |]. intro E. injection E as E. exact (D E).
  Qed.

  Theorem live_b2_runs : forall s0 s y e, reachA s0 s -> reachB (m s) y -> ~ validB y ->
    govB e y <> govB e (rhoB y) ->
    exists w w' n1 n2, star (lstep live_sw) (InA s0 w (w' ++ [e])) n1 /\
      normal_form (lstep live_sw) n1 /\ star (lstep live_sw) (InA s0 w (w' ++ [e])) n2 /\
      normal_form (lstep live_sw) n2 /\ n1 <> n2.
  Proof.
    intros s0 s y e Hr Hy Hinv Hne.
    destruct (cc2_fail_diverge_from eqB applyB rhoB rhoB_star validB reachB_star validB_star
                (m s) y e Hy Hinv Hne) as [w' [n1 [n2 [S1' [N1 [S2' [N2 D]]]]]]].
    destruct (reach_run eqA applyA rhoA validA s0 s Hr) as [w0 Hw].
    assert (Hws : star stA (s0, w0) (s, [])) by (pose proof (Hw []) as X; rewrite app_nil_r in X; exact X).
    assert (P : forall c, star stB (m s, w' ++ [e]) c ->
      star (lstep live_sw) (InA s0 w0 (w' ++ [e])) (InB c)).
    { intros c Sc. eapply star_trans; [apply lift_A; exact Hws |].
      eapply star_step; [apply l_sw; exact I |]. apply lift_B. exact Sc. }
    exists w0, w', (InB n1), (InB n2). split; [exact (P n1 S1') |].
    split; [exact (proj2 (nf_InB _ n1) N1) |]. split; [exact (P n2 S2') |].
    split; [exact (proj2 (nf_InB _ n2) N2) |]. intro E. injection E as E. exact (D E).
  Qed.

  (* AmodF fails: two A normal forms of one buffer that B tells apart give two barrier runs. *)
  Theorem amodf_runs : forall s0 Ba t1 t2,
    star stA (s0, Ba) (t1, []) -> normal_form stA (t1, []) ->
    star stA (s0, Ba) (t2, []) -> normal_form stA (t2, []) ->
    star (lstep barrier_sw) (InA s0 Ba []) (InB (rhoB_star (m t1), [])) /\
    star (lstep barrier_sw) (InA s0 Ba []) (InB (rhoB_star (m t2), [])) /\
    normal_form (lstep barrier_sw) (InB (rhoB_star (m t1), [])) /\
    normal_form (lstep barrier_sw) (InB (rhoB_star (m t2), [])).
  Proof.
    intros s0 Ba t1 t2 S1' N1 S2' N2. split; [| split; [| split]].
    - eapply star_trans; [apply lift_A; exact S1' |].
      eapply star_step; [apply l_sw; exact N1 |]. apply lift_B. apply reachB_star.
    - eapply star_trans; [apply lift_A; exact S2' |].
      eapply star_step; [apply l_sw; exact N2 |]. apply lift_B. apply reachB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
    - apply nf_InB. apply nf_valid_empty. apply validB_star.
  Qed.

  (* A CC failure of B after a quiescent reachable state: two barrier runs diverge. *)
  Theorem barrier_b_runs : forall s0 t y e1 e2, reachA s0 t -> normal_form stA (t, []) ->
    reachB (m t) y -> govB e2 (govB e1 y) <> govB e1 (govB e2 y) ->
    exists w w' n1 n2, star (lstep barrier_sw) (InA s0 w (w' ++ [e1; e2])) n1 /\
      normal_form (lstep barrier_sw) n1 /\ star (lstep barrier_sw) (InA s0 w (w' ++ [e1; e2])) n2 /\
      normal_form (lstep barrier_sw) n2 /\ n1 <> n2.
  Proof.
    intros s0 t y e1 e2 Hr Hnf Hy Hne.
    destruct (cc1_fail_diverge_from eqB applyB rhoB rhoB_star validB reachB_star validB_star
                (m t) y e1 e2 Hy Hne) as [w' [n1 [n2 [S1' [N1 [S2' [N2 D]]]]]]].
    destruct (reach_run eqA applyA rhoA validA s0 t Hr) as [w0 Hw].
    assert (Hwt : star stA (s0, w0) (t, [])) by (pose proof (Hw []) as X; rewrite app_nil_r in X; exact X).
    assert (P : forall c, star stB (m t, w' ++ [e1; e2]) c ->
      star (lstep barrier_sw) (InA s0 w0 (w' ++ [e1; e2])) (InB c)).
    { intros c Sc. eapply star_trans; [apply lift_A; exact Hwt |].
      eapply star_step; [apply l_sw; exact Hnf |]. apply lift_B. exact Sc. }
    exists w0, w', (InB n1), (InB n2). split; [exact (P n1 S1') |].
    split; [exact (proj2 (nf_InB _ n1) N1) |]. split; [exact (P n2 S2') |].
    split; [exact (proj2 (nf_InB _ n2) N2) |]. intro E. injection E as E. exact (D E).
  Qed.
End Switch.

(* ============================================================================================ *)
(* The same configuration on both sides: the theorem recovers cc_exact_from.                     *)
(* ============================================================================================ *)

Theorem live_no_change : forall {S E : Type} (eq : forall a b : E, {a = b} + {a <> b})
  (apply : E -> S -> S) (rho rho_star : S -> S) (valid : S -> Prop) (Phi : S -> nat),
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  (forall s B, star (step eq apply rho valid free_enabled) (s, B) (rho_star s, B)) ->
  (forall s, valid (rho_star s)) ->
  forall s0, LiveConv eq eq apply rho valid apply rho valid (fun s => s) (fun e => e) s0 <->
             CCA apply rho rho_star valid s0.
Proof.
  intros S E eq apply rho rho_star valid Phi wfc rs vs s0.
  assert (Fix : forall t, normal_form (step eq apply rho valid free_enabled) (t, []) -> rho_star t = t).
  { intros t N. pose proof (star_from_nf _ _ _ N (rs t [])) as Et. injection Et as Et. symmetry. exact Et. }
  split.
  - intros H.
    assert (HF : Faithful eq apply rho valid rho_star (fun s => s) s0).
    { intros t1 t2 _ _ N1 N2 Heq. simpl in Heq. rewrite (Fix t1 N1), (Fix t2 N2) in Heq. exact Heq. }
    exact (proj1 (proj1 (live_exact_faithful eq eq apply rho rho_star valid Phi apply rho rho_star
                              valid Phi (fun s => s) (fun e => e) wfc rs vs wfc rs vs s0 HF) H)).
  - intros [H1 H2]. apply (live_exact eq eq apply rho valid apply rho rho_star valid Phi
                             (fun s => s) (fun e => e) wfc rs vs).
    split; [| split].
    + intros s Hs. split.
      * intros y e1 e2 Hy. apply H1. exact (reach_trans _ _ _ _ _ _ Hs Hy).
      * intros y e Hy. apply H2. exact (reach_trans _ _ _ _ _ _ Hs Hy).
    + intros s e _. reflexivity.
    + intros s Hs Hinv.
      assert (HC : CCB apply rho rho_star valid s).
      { split.
        - intros y e1 e2 Hy. apply H1. exact (reach_trans _ _ _ _ _ _ Hs Hy).
        - intros y e Hy. apply H2. exact (reach_trans _ _ _ _ _ _ Hs Hy). }
      assert (S1' : star (step eq apply rho valid free_enabled) (s, []) (rho_star (rho s), [])).
      { eapply star_step; [apply st_comp; exact Hinv | apply rs]. }
      pose proof (CCB_UN eq apply rho rho_star valid Phi wfc rs vs s HC [] _ _ S1'
                    (nf_valid_empty eq apply rho valid _ (vs _)) (rs s [])
                    (nf_valid_empty eq apply rho valid _ (vs _))) as Heq.
      injection Heq as Heq. exact Heq.
Qed.

(* ============================================================================================ *)
(* Registries as records, for the instances and the classification.                             *)
(* ============================================================================================ *)

Record Reg (S E : Type) : Type := mkReg {
  g_eq : forall a b : E, {a = b} + {a <> b};
  g_apply : E -> S -> S;
  g_rho : S -> S;
  g_star : S -> S;
  g_valid : S -> Prop;
  g_Phi : S -> nat;
  g_wfc : forall s, ~ g_valid s -> g_Phi (g_rho s) < g_Phi s;
  g_reach : forall s B, star (step g_eq g_apply g_rho g_valid free_enabled) (s, B) (g_star s, B);
  g_vstar : forall s, g_valid (g_star s)
}.

Arguments mkReg {S E}.
Arguments g_eq {S E}. Arguments g_apply {S E}. Arguments g_rho {S E}. Arguments g_star {S E}.
Arguments g_valid {S E}. Arguments g_Phi {S E}. Arguments g_wfc {S E}. Arguments g_reach {S E}.
Arguments g_vstar {S E}.

Section Wrappers.
  Context {SA EA SB EB : Type}.
  Variable A : Reg SA EA.
  Variable B : Reg SB EB.
  Variable m : SA -> SB.
  Variable tau : EA -> EB.

  Definition RLive (s0 : SA) : Prop :=
    LiveConv (g_eq A) (g_eq B) (g_apply A) (g_rho A) (g_valid A) (g_apply B) (g_rho B) (g_valid B) m tau s0.
  Definition RBar (s0 : SA) : Prop :=
    BarConv (g_eq A) (g_eq B) (g_apply A) (g_rho A) (g_valid A) (g_apply B) (g_rho B) (g_valid B) m tau s0.
  Definition RCCA (s0 : SA) : Prop := CCA (g_apply A) (g_rho A) (g_star A) (g_valid A) s0.
  Definition RCCB (x : SB) : Prop := CCB (g_apply B) (g_rho B) (g_star B) (g_valid B) x.
  Definition RLiveCond (s0 : SA) : Prop :=
    LiveCond (g_apply A) (g_rho A) (g_valid A) (g_apply B) (g_rho B) (g_star B) (g_valid B) m tau s0.
  Definition RBarCond (s0 : SA) : Prop :=
    BarCond (g_eq A) (g_apply A) (g_rho A) (g_valid A) (g_apply B) (g_rho B) (g_star B) (g_valid B) m s0.
  Definition RBarB (s0 : SA) : Prop :=
    BarB (g_eq A) (g_apply A) (g_rho A) (g_valid A) (g_apply B) (g_rho B) (g_star B) (g_valid B) m s0.
  Definition RFaithful (s0 : SA) : Prop :=
    Faithful (g_eq A) (g_apply A) (g_rho A) (g_valid A) (g_star B) m s0.

  Theorem rlive_exact : forall s0, RLive s0 <-> RLiveCond s0.
  Proof. exact (live_exact _ _ _ _ _ _ _ _ _ _ m tau (g_wfc B) (g_reach B) (g_vstar B)). Qed.

  Theorem rbarrier_exact : forall s0, RBar s0 <-> RBarCond s0.
  Proof. exact (barrier_exact _ _ _ _ _ _ _ _ _ _ m tau (g_wfc B) (g_reach B) (g_vstar B)). Qed.

  Theorem rbarrier_exact_faithful : forall s0, RFaithful s0 -> (RBar s0 <-> RCCA s0 /\ RBarB s0).
  Proof.
    exact (barrier_exact_faithful _ _ _ _ _ _ _ _ _ _ _ _ m tau (g_wfc A) (g_reach A) (g_vstar A)
             (g_wfc B) (g_reach B) (g_vstar B)).
  Qed.

  Theorem rlive_exact_faithful : forall s0, RFaithful s0 -> (RLive s0 <-> RCCA s0 /\ RLiveCond s0).
  Proof.
    exact (live_exact_faithful _ _ _ _ _ _ _ _ _ _ _ _ m tau (g_wfc A) (g_reach A) (g_vstar A)
             (g_wfc B) (g_reach B) (g_vstar B)).
  Qed.

  Theorem rlive_implies_barrier : forall s0, RLive s0 -> RBar s0.
  Proof. exact (live_implies_barrier _ _ _ _ _ _ _ _ m tau). Qed.

  Theorem rbarrier_sufficient : forall s0, RCCA s0 -> RBarB s0 -> RBar s0.
  Proof.
    exact (barrier_sufficient _ _ _ _ _ _ _ _ _ _ _ _ m tau (g_wfc A) (g_reach A) (g_vstar A)
             (g_wfc B) (g_reach B) (g_vstar B)).
  Qed.
End Wrappers.

(* ============================================================================================ *)
(* 2. Classification.                                                                            *)
(* ============================================================================================ *)

Inductive outcome : Type := Online | BarrierOnly | Unsafe.

Definition Classified {SA EA SB EB : Type} (A : Reg SA EA) (B : Reg SB EB) (m : SA -> SB)
  (tau : EA -> EB) (s0 : SA) (o : outcome) : Prop :=
  match o with
  | Online => RLive A B m tau s0
  | BarrierOnly => RBar A B m tau s0 /\ ~ RLive A B m tau s0
  | Unsafe => ~ RBar A B m tau s0
  end.

(* At most one outcome holds. *)
Theorem classified_unique : forall {SA EA SB EB : Type} (A : Reg SA EA) (B : Reg SB EB) m tau s0 o1 o2,
  Classified A B m tau s0 o1 -> Classified A B m tau s0 o2 -> o1 = o2.
Proof.
  intros SA EA SB EB A B m tau s0 o1 o2 H1 H2.
  pose proof (rlive_implies_barrier A B m tau s0) as LB.
  destruct o1, o2; simpl in *; try reflexivity; try tauto.
Qed.

(* Given decisions of the two exact conditions, exactly one outcome is produced. *)
Theorem classify : forall {SA EA SB EB : Type} (A : Reg SA EA) (B : Reg SB EB) m tau s0,
  {RLiveCond A B m tau s0} + {~ RLiveCond A B m tau s0} ->
  {RBarCond A B m s0} + {~ RBarCond A B m s0} ->
  {o : outcome | Classified A B m tau s0 o}.
Proof.
  intros SA EA SB EB A B m tau s0 DL DB.
  destruct DL as [L | L].
  - exists Online. simpl. exact (proj2 (rlive_exact A B m tau s0) L).
  - destruct DB as [Bc | Bc].
    + exists BarrierOnly. simpl. split; [exact (proj2 (rbarrier_exact A B m tau s0) Bc) |].
      intro H. apply L. exact (proj1 (rlive_exact A B m tau s0) H).
    + exists Unsafe. simpl. intro H. apply Bc. exact (proj1 (rbarrier_exact A B m tau s0) H).
Qed.

(* ---- Decidability on finite instances. ---- *)

Lemma list_forall_or_witness : forall {X : Type} (P : X -> Prop) (l : list X),
  (forall x, {P x} + {~ P x}) -> ((forall x, In x l -> P x) + {x : X | In x l /\ ~ P x})%type.
Proof.
  intros X P l Hd. induction l as [| a l IH].
  - left. intros x [].
  - destruct (Hd a) as [Ha | Ha].
    + destruct IH as [IH | [x [Hx Hn]]].
      * left. intros x [<- | Hx]; [exact Ha | apply IH; exact Hx].
      * right. exists x. split; [right; exact Hx | exact Hn].
    + right. exists a. split; [left; reflexivity | exact Ha].
Qed.

Lemma dec_forall_fin : forall {X : Type} (l : list X), (forall x, In x l) ->
  forall P : X -> Prop, (forall x, {P x} + {~ P x}) -> {forall x, P x} + {~ forall x, P x}.
Proof.
  intros X l Hl P Hd. destruct (list_forall_or_witness P l Hd) as [H | [x [_ Hn]]].
  - left. intros x. apply H. apply Hl.
  - right. intro H. exact (Hn (H x)).
Qed.

Lemma dec_imp : forall P Q : Prop, {P} + {~ P} -> {Q} + {~ Q} -> {P -> Q} + {~ (P -> Q)}.
Proof. intros P Q [p | p] [q | q]; [left | right | left | left]; tauto. Qed.

Lemma dec_and : forall P Q : Prop, {P} + {~ P} -> {Q} + {~ Q} -> {P /\ Q} + {~ (P /\ Q)}.
Proof. intros P Q [p | p] [q | q]; [left | right | right | right]; tauto. Qed.

Lemma dec_not : forall P : Prop, {P} + {~ P} -> {~ P} + {~ ~ P}.
Proof. intros P [p | p]; [right | left]; tauto. Qed.

Lemma dec_iff : forall P Q : Prop, (P <-> Q) -> {P} + {~ P} -> {Q} + {~ Q}.
Proof. intros P Q H [p | p]; [left | right]; tauto. Qed.

(* Reachability in a finite successor graph is decidable: the layers of a breadth-first closure
   stop growing within |all| rounds. *)
Section Closure.
  Context {X : Type}.
  Variable eqX : forall a b : X, {a = b} + {a <> b}.
  Variable all : list X.
  Hypothesis all_full : forall x, In x all.
  Variable succ : X -> list X.

  Definition Rsucc (a b : X) : Prop := In b (succ a).

  Fixpoint layer (x0 : X) (k : nat) : list X :=
    match k with
    | 0 => [x0]
    | S k' => layer x0 k' ++ flat_map succ (layer x0 k')
    end.

  Definition inb (z : X) (l : list X) : bool := if in_dec eqX z l then true else false.
  Definition cnt (A l : list X) : nat := length (filter (fun z => inb z l) A).

  Lemma inb_iff : forall z l, inb z l = true <-> In z l.
  Proof.
    intros z l. unfold inb. destruct (in_dec eqX z l) as [H | H]; split; intro X0;
      try exact H; try reflexivity; try discriminate X0; contradiction.
  Qed.

  Lemma cnt_le : forall A l1 l2, (forall z, In z l1 -> In z l2) -> cnt A l1 <= cnt A l2.
  Proof.
    intros A l1 l2 H. unfold cnt. induction A as [| a A IH]; simpl; [lia |].
    destruct (inb a l1) eqn:E1; destruct (inb a l2) eqn:E2; simpl; try lia.
    exfalso. apply inb_iff in E1. apply H in E1. apply inb_iff in E1. congruence.
  Qed.

  Lemma cnt_lt : forall A l1 l2 b, (forall z, In z l1 -> In z l2) -> In b A -> In b l2 ->
    ~ In b l1 -> cnt A l1 < cnt A l2.
  Proof.
    intros A l1 l2 b H HbA Hb2 Hb1. induction A as [| a A IH]; [destruct HbA |].
    pose proof (cnt_le A l1 l2 H) as Le. unfold cnt in *. simpl.
    destruct HbA as [-> | HbA].
    - destruct (inb b l1) eqn:E1; [apply inb_iff in E1; contradiction |].
      destruct (inb b l2) eqn:E2; [| apply (proj2 (inb_iff b l2)) in Hb2; congruence].
      simpl. lia.
    - specialize (IH HbA).
      destruct (inb a l1) eqn:E1; destruct (inb a l2) eqn:E2; simpl; try lia.
      exfalso. apply inb_iff in E1. apply H in E1. apply inb_iff in E1. congruence.
  Qed.

  Lemma cnt_bound : forall A l, cnt A l <= length A.
  Proof.
    intros A l. unfold cnt. induction A as [| a A IH]; simpl; [lia |].
    destruct (inb a l); simpl; lia.
  Qed.

  Lemma layer_sound : forall x0 k y, In y (layer x0 k) -> star Rsucc x0 y.
  Proof.
    intros x0 k. induction k as [| k IH]; intros y H; simpl in H.
    - destruct H as [<- | []]. apply star_refl.
    - apply in_app_or in H. destruct H as [H | H]; [apply IH; exact H |].
      apply in_flat_map in H. destruct H as [a [Ha Hy]].
      eapply star_trans; [apply IH; exact Ha | apply star_one; exact Hy].
  Qed.

  Lemma layer_sub : forall x0 k z, In z (layer x0 k) -> In z (layer x0 (S k)).
  Proof. intros x0 k z H. simpl. apply in_or_app. left. exact H. Qed.

  Lemma layer_sub_le : forall x0 k j, k <= j -> forall z, In z (layer x0 k) -> In z (layer x0 j).
  Proof.
    intros x0 k j H. induction H as [| j _ IH]; intros z Hz; [exact Hz |].
    apply layer_sub. apply IH. exact Hz.
  Qed.

  Lemma layer_x0 : forall x0 k, In x0 (layer x0 k).
  Proof. intros x0 k. apply (layer_sub_le x0 0 k (Nat.le_0_l k)). left. reflexivity. Qed.

  Lemma layer_succ : forall x0 k a b, In a (layer x0 k) -> In b (succ a) -> In b (layer x0 (S k)).
  Proof.
    intros x0 k a b Ha Hb. simpl. apply in_or_app. right. apply in_flat_map. exists a. split; assumption.
  Qed.

  Definition closedL (l : list X) : Prop := forall a b, In a l -> In b (succ a) -> In b l.

  Lemma closed_or_grow : forall x0 k,
    (exists j, j <= k /\ closedL (layer x0 j)) \/ S k <= cnt all (layer x0 k).
  Proof.
    intros x0 k. induction k as [| k IH].
    - right. pose proof (cnt_lt all [] (layer x0 0) x0 (fun z H => match H with end)
                           (all_full x0) (or_introl eq_refl) (fun H => H)) as H. lia.
    - destruct IH as [[j [Hj Hc]] | IH]; [left; exists j; split; [lia | exact Hc] |].
      assert (Dsucc : forall a, ((forall b, In b (succ a) -> In b (layer x0 k)) +
                                {b : X | In b (succ a) /\ ~ In b (layer x0 k)})%type).
      { intros a. exact (list_forall_or_witness (fun b => In b (layer x0 k)) (succ a)
                           (fun b => in_dec eqX b _)). }
      destruct (list_forall_or_witness (fun a => forall b, In b (succ a) -> In b (layer x0 k))
                  (layer x0 k)) as [Hc | [a [Ha Hn]]].
      + intros a. destruct (Dsucc a) as [H | [b [Hb Hnb]]]; [left; exact H |].
        right. intro H. exact (Hnb (H b Hb)).
      + left. exists k. split; [lia | intros a b Ha Hb; exact (Hc a Ha b Hb)].
      + destruct (Dsucc a) as [H | [b [Hb Hnb]]]; [exfalso; exact (Hn H) |].
        right. pose proof (cnt_lt all (layer x0 k) (layer x0 (S k)) b (layer_sub x0 k) (all_full b)
                             (layer_succ x0 k a b Ha Hb) Hnb). lia.
  Qed.

  Lemma closed_layer : forall x0, exists j, j <= length all /\ closedL (layer x0 j).
  Proof.
    intros x0. destruct (closed_or_grow x0 (length all)) as [H | H]; [exact H |].
    exfalso. pose proof (cnt_bound all (layer x0 (length all))). lia.
  Qed.

  Theorem star_fin_iff : forall x0 y, star Rsucc x0 y <-> In y (layer x0 (length all)).
  Proof.
    intros x0 y. split.
    - intros S. destruct (closed_layer x0) as [j [Hj Hc]].
      apply (layer_sub_le x0 j (length all) Hj).
      apply (star_closed Rsucc (fun z => In z (layer x0 j)) (fun a b Ha Hb => Hc a b Ha Hb) x0 y
               (layer_x0 x0 j) S).
    - apply layer_sound.
  Qed.

  Theorem star_fin_dec : forall x0 y, {star Rsucc x0 y} + {~ star Rsucc x0 y}.
  Proof.
    intros x0 y. destruct (in_dec eqX y (layer x0 (length all))) as [H | H].
    - left. apply star_fin_iff. exact H.
    - right. rewrite star_fin_iff. exact H.
  Qed.
End Closure.

Section ReachDec.
  Context {S E : Type}.
  Variable eqS : forall a b : S, {a = b} + {a <> b}.
  Variable allS : list S.
  Hypothesis allS_full : forall s, In s allS.
  Variable evs : list E.
  Hypothesis evs_full : forall e, In e evs.
  Variable apply : E -> S -> S.
  Variable rho : S -> S.
  Variable valid : S -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.

  Definition rsucc (s : S) : list S :=
    map (fun e => apply e s) evs ++ (if valid_dec s then [] else [rho s]).

  Lemma reach_star_iff : forall s0 s, reach apply rho valid s0 s <-> star (Rsucc rsucc) s0 s.
  Proof.
    intros s0 s. split.
    - intros H. induction H as [| e s _ IH | s _ IH Hinv].
      + apply star_refl.
      + eapply star_trans; [exact IH |]. apply star_one. unfold Rsucc, rsucc.
        apply in_or_app. left. exact (in_map (fun e => apply e s) evs e (evs_full e)).
      + eapply star_trans; [exact IH |]. apply star_one. unfold Rsucc, rsucc.
        apply in_or_app. right. destruct (valid_dec s) as [Hv | _]; [contradiction | left; reflexivity].
    - intros H. refine (star_closed (Rsucc rsucc) (reach apply rho valid s0) _ s0 s (r_init _ _ _ _) H).
      intros a b Ha Hb. unfold Rsucc, rsucc in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
      + apply in_map_iff in Hb. destruct Hb as [e [<- _]]. apply r_apply. exact Ha.
      + destruct (valid_dec a) as [_ | Hv]; [destruct Hb |].
        destruct Hb as [<- | []]. apply r_comp; assumption.
  Qed.

  Theorem reach_dec : forall s0 s, {reach apply rho valid s0 s} + {~ reach apply rho valid s0 s}.
  Proof.
    intros s0 s. apply (dec_iff _ _ (iff_sym (reach_star_iff s0 s))).
    exact (star_fin_dec eqS allS allS_full rsucc s0 s).
  Qed.
End ReachDec.

Section FiniteClassification.
  Context {SA EA SB EB : Type}.
  Variable A : Reg SA EA.
  Variable B : Reg SB EB.
  Variable m : SA -> SB.
  Variable tau : EA -> EB.
  Variable eqSA : forall a b : SA, {a = b} + {a <> b}.
  Variable eqSB : forall a b : SB, {a = b} + {a <> b}.
  Variable allA : list SA.
  Hypothesis allA_full : forall s, In s allA.
  Variable allB : list SB.
  Hypothesis allB_full : forall x, In x allB.
  Variable evsA : list EA.
  Hypothesis evsA_full : forall e, In e evsA.
  Variable evsB : list EB.
  Hypothesis evsB_full : forall e, In e evsB.
  Hypothesis validA_dec : forall s, {g_valid A s} + {~ g_valid A s}.
  Hypothesis validB_dec : forall x, {g_valid B x} + {~ g_valid B x}.

  Local Notation stA := (step (g_eq A) (g_apply A) (g_rho A) (g_valid A) free_enabled).
  Local Notation reachA := (reach (g_apply A) (g_rho A) (g_valid A)).
  Local Notation reachB := (reach (g_apply B) (g_rho B) (g_valid B)).

  Let rA := reach_dec eqSA allA allA_full evsA evsA_full (g_apply A) (g_rho A) (g_valid A) validA_dec.
  Let rB := reach_dec eqSB allB allB_full evsB evsB_full (g_apply B) (g_rho B) (g_valid B) validB_dec.
  Let fA := fun P => dec_forall_fin allA allA_full P.
  Let fB := fun P => dec_forall_fin allB allB_full P.
  Let fEA := fun P => dec_forall_fin evsA evsA_full P.
  Let fEB := fun P => dec_forall_fin evsB evsB_full P.

  Lemma nfA_nil_iff : forall t, normal_form stA (t, []) <-> g_valid A t.
  Proof.
    intros t. split.
    - intros N. destruct (validA_dec t) as [H | H]; [exact H |].
      exfalso. apply N. eexists. apply st_comp. exact H.
    - intros H. apply nf_valid_empty. exact H.
  Qed.

  Lemma CCB_dec : forall x, {RCCB B x} + {~ RCCB B x}.
  Proof.
    intros x. apply dec_and.
    - apply fB. intros y. apply fEB. intros e1. apply fEB. intros e2.
      apply dec_imp; [apply rB | apply eqSB].
    - apply fB. intros y. apply fEB. intros e.
      apply dec_imp; [apply rB |]. apply dec_imp; [apply dec_not; apply validB_dec | apply eqSB].
  Qed.

  Lemma CCA_dec : forall s0, {RCCA A s0} + {~ RCCA A s0}.
  Proof.
    intros s0. apply dec_and.
    - apply fA. intros s. apply fEA. intros e1. apply fEA. intros e2.
      apply dec_imp; [apply rA | apply eqSA].
    - apply fA. intros s. apply fEA. intros e.
      apply dec_imp; [apply rA |]. apply dec_imp; [apply dec_not; apply validA_dec | apply eqSA].
  Qed.

  Lemma LiveCond_dec : forall s0, {RLiveCond A B m tau s0} + {~ RLiveCond A B m tau s0}.
  Proof.
    intros s0. apply dec_and; [| apply dec_and].
    - apply fA. intros s. apply dec_imp; [apply rA | apply CCB_dec].
    - apply fA. intros s. apply fEA. intros e. apply dec_imp; [apply rA | apply eqSB].
    - apply fA. intros s. apply dec_imp; [apply rA |].
      apply dec_imp; [apply dec_not; apply validA_dec | apply eqSB].
  Qed.

  Lemma BarB_dec : forall s0, {RBarB A B m s0} + {~ RBarB A B m s0}.
  Proof.
    intros s0. apply fA. intros t. apply dec_imp; [apply rA |].
    apply dec_imp; [apply (dec_iff _ _ (iff_sym (nfA_nil_iff t))); apply validA_dec | apply CCB_dec].
  Qed.

  Theorem live_dec : forall s0, {RLive A B m tau s0} + {~ RLive A B m tau s0}.
  Proof.
    intros s0. apply (dec_iff _ _ (iff_sym (rlive_exact A B m tau s0))). apply LiveCond_dec.
  Qed.

  Theorem faithful_dec : forall s0, {RFaithful A B m s0} + {~ RFaithful A B m s0}.
  Proof.
    intros s0. apply fA. intros t1. apply fA. intros t2.
    apply dec_imp; [apply rA |]. apply dec_imp; [apply rA |].
    apply dec_imp; [apply (dec_iff _ _ (iff_sym (nfA_nil_iff t1))); apply validA_dec |].
    apply dec_imp; [apply (dec_iff _ _ (iff_sym (nfA_nil_iff t2))); apply validA_dec |].
    apply dec_imp; [apply eqSB | apply eqSA].
  Qed.

  Theorem barrier_dec_faithful : forall s0, RFaithful A B m s0 ->
    {RBar A B m tau s0} + {~ RBar A B m tau s0}.
  Proof.
    intros s0 HF. apply (dec_iff _ _ (iff_sym (rbarrier_exact_faithful A B m tau s0 HF))).
    apply dec_and; [apply CCA_dec | apply BarB_dec].
  Qed.

  (* The trichotomy on finite instances: under a faithful migration, the outcome is computed. *)
  Theorem classify_finite : forall s0, RFaithful A B m s0 -> {o : outcome | Classified A B m tau s0 o}.
  Proof.
    intros s0 HF. destruct (live_dec s0) as [L | L].
    - exists Online. exact L.
    - destruct (barrier_dec_faithful s0 HF) as [Bc | Bc].
      + exists BarrierOnly. split; assumption.
      + exists Unsafe. exact Bc.
  Qed.
End FiniteClassification.

(* ============================================================================================ *)
(* Instances: counterexamples and non-vacuity.                                                  *)
(* ============================================================================================ *)

Definition unit_eq_dec (a b : unit) : {a = b} + {a <> b} :=
  match a, b with tt, tt => left eq_refl end.

(* A registry whose every state is valid: the repair is the identity. *)
Definition triv {S E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (apply : E -> S -> S) :
  Reg S E :=
  mkReg eq apply (fun s => s) (fun s => s) (fun _ => True) (fun _ => 0)
    (fun s H => match H I with end) (fun s B => star_refl _ (s, B)) (fun _ => I).

(* A counter capped at k: an event adds add e, an overflow is clamped to k. *)
Lemma cap_wfc : forall k s, ~ s <= k -> (fun s => s - k) ((fun _ : nat => k) s) < (fun s => s - k) s.
Proof. intros k s H. simpl. lia. Qed.

Lemma cap_reach : forall k {E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (add : E -> nat) s B,
  star (step eq (fun e s => s + add e) (fun _ => k) (fun s => s <= k) free_enabled) (s, B)
       (Nat.min s k, B).
Proof.
  intros k E eq add s B. destruct (le_lt_dec s k) as [H | H].
  - rewrite (Nat.min_l s k H). apply star_refl.
  - rewrite (Nat.min_r s k) by lia. apply star_one. apply (st_comp eq (fun e s => s + add e) (fun _ => k)
      (fun s => s <= k) free_enabled s B). lia.
Qed.

Definition cap (k : nat) {E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (add : E -> nat) :
  Reg nat E :=
  mkReg eq (fun e s => s + add e) (fun _ => k) (fun s => Nat.min s k) (fun s => s <= k)
    (fun s => s - k) (cap_wfc k) (cap_reach k eq add) (fun s => Nat.le_min_r s k).

Lemma min_add : forall s a b k, Nat.min (Nat.min (s + a) k + b) k = Nat.min (s + a + b) k.
Proof.
  intros s a b k. destruct (le_lt_dec (s + a) k) as [H | H].
  - rewrite (Nat.min_l (s + a) k H). reflexivity.
  - rewrite (Nat.min_r (s + a) k) by lia. rewrite (Nat.min_r (k + b) k) by lia.
    rewrite (Nat.min_r (s + a + b) k) by lia. reflexivity.
Qed.

(* Every cap registry converges from every state. *)
Lemma cap_cc : forall k {E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (add : E -> nat) s0,
  CCA (g_apply (cap k eq add)) (g_rho (cap k eq add)) (g_star (cap k eq add)) (g_valid (cap k eq add)) s0.
Proof.
  intros k E eq add s0. split; simpl.
  - intros s e1 e2 _. rewrite !min_add. f_equal. lia.
  - intros s e _ H. rewrite (Nat.min_r (s + add e) k) by lia.
    rewrite (Nat.min_r (k + add e) k) by lia. reflexivity.
Qed.

Lemma cap_nf_le : forall k {E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (add : E -> nat) t,
  normal_form (step eq (fun e s => s + add e) (fun _ => k) (fun s => s <= k) free_enabled) (t, []) ->
  t <= k.
Proof.
  intros k E eq add t N. destruct (le_lt_dec t k) as [H | H]; [exact H |].
  exfalso. apply N. eexists. apply st_comp. lia.
Qed.

Lemma cap_reach_all : forall k {E : Type} (eq : forall a b : E, {a = b} + {a <> b}) (add : E -> nat) e,
  add e = 1 -> forall n, reach (fun e s => s + add e) (fun _ => k) (fun s => s <= k) 0 n.
Proof.
  intros k E eq add e He n. induction n as [| n IH]; [apply r_init |].
  pose proof (r_apply (fun e s => s + add e) (fun _ => k) (fun s => s <= k) 0 e n IH) as H.
  simpl in H. rewrite He in H. replace (S n) with (n + 1) by lia. exact H.
Qed.

(* ---- cap_raise: a cap of 5 raised to 10. (S2) fails. ---- *)

Definition capA : Reg nat unit := cap 5 unit_eq_dec (fun _ => 1).
Definition capB : Reg nat unit := cap 10 unit_eq_dec (fun _ => 1).

Theorem cap_raise :
  RCCA capA 0 /\ (forall x, RCCB capB x) /\ RBar capA capB (fun s => s) (fun e => e) 0 /\
  ~ RLive capA capB (fun s => s) (fun e => e) 0 /\
  ~ S2 (g_apply capA) (g_rho capA) (g_valid capA) (g_star capB) (fun s => s) 0.
Proof.
  assert (HA : RCCA capA 0) by apply cap_cc.
  assert (HB : forall x, RCCB capB x) by (intros x; apply cap_cc).
  assert (NS2 : ~ S2 (g_apply capA) (g_rho capA) (g_valid capA) (g_star capB) (fun s => s) 0).
  { intros H. assert (R6 : reach (g_apply capA) (g_rho capA) (g_valid capA) 0 6).
    { exact (cap_reach_all 5 unit_eq_dec (fun _ => 1) tt eq_refl 6). }
    specialize (H 6 R6). simpl in H. assert (Hn : ~ 6 <= 5) by lia. specialize (H Hn). discriminate H. }
  split; [exact HA |]. split; [exact HB |]. split; [| split; [| exact NS2]].
  - apply rbarrier_exact_faithful.
    + intros t1 t2 _ _ N1 N2 E. simpl in E.
      pose proof (cap_nf_le 5 unit_eq_dec (fun _ => 1) t1 N1).
      pose proof (cap_nf_le 5 unit_eq_dec (fun _ => 1) t2 N2).
      rewrite (Nat.min_l t1 10), (Nat.min_l t2 10) in E by lia. exact E.
    + split; [exact HA |]. intros t _ _. apply HB.
  - intros H. apply (proj1 (rlive_exact capA capB _ _ 0)) in H. destruct H as [_ [_ H2]].
    exact (NS2 H2).
Qed.

(* ---- doubling_migration: m doubles the state, every event adds 1. (S1) fails. ---- *)

Definition succA : Reg nat unit := triv unit_eq_dec (fun _ s => S s).

Theorem doubling_migration :
  RCCA succA 0 /\ (forall x, RCCB succA x) /\ RBar succA succA (fun s => 2 * s) (fun e => e) 0 /\
  ~ RLive succA succA (fun s => 2 * s) (fun e => e) 0 /\
  ~ S1 (g_apply succA) (g_rho succA) (g_valid succA) (g_apply succA) (g_star succA)
       (fun s => 2 * s) (fun e => e) 0.
Proof.
  assert (HC : forall s0, CCA (g_apply succA) (g_rho succA) (g_star succA) (g_valid succA) s0).
  { intros s0. split; simpl.
    - intros s [] [] _. reflexivity.
    - intros s e _ H. exfalso. exact (H I). }
  assert (NS1 : ~ S1 (g_apply succA) (g_rho succA) (g_valid succA) (g_apply succA) (g_star succA)
                     (fun s => 2 * s) (fun e => e) 0).
  { intros H. specialize (H 0 tt (r_init _ _ _ _)). simpl in H. discriminate H. }
  split; [apply HC |]. split; [intros x; apply HC |]. split; [| split; [| exact NS1]].
  - apply rbarrier_exact_faithful.
    + intros t1 t2 _ _ _ _ E. simpl in E. lia.
    + split; [apply HC |]. intros t _ _. apply HC.
  - intros H. apply (proj1 (rlive_exact succA succA _ _ 0)) in H. destruct H as [_ [H1 _]].
    exact (NS1 H1).
Qed.

(* ---- migrated_transient: (B) fails only at a migrated non-quiescent state. ---- *)

(* A: the event moves 0 to the invalid 1, and A repairs 1 to 0. *)
Lemma trA_wfc : forall s, ~ s = 0 -> (fun s : nat => s) ((fun _ : nat => 0) s) < (fun s : nat => s) s.
Proof. intros s H. simpl. lia. Qed.

Lemma trA_reach : forall s (B : list unit),
  star (step unit_eq_dec (fun _ _ => 1) (fun _ => 0) (fun s => s = 0) free_enabled) (s, B)
       ((fun _ => 0) s, B).
Proof.
  intros s B. destruct (Nat.eq_dec s 0) as [-> | H]; [apply star_refl |].
  apply star_one. apply (st_comp unit_eq_dec (fun _ _ => 1) (fun _ => 0) (fun s => s = 0) free_enabled s B).
  exact H.
Qed.

Definition trA : Reg nat unit :=
  mkReg unit_eq_dec (fun _ _ => 1) (fun _ => 0) (fun _ => 0) (fun s => s = 0) (fun s => s)
    trA_wfc trA_reach (fun _ => eq_refl).

(* B: 1 is invalid and repairs to 0; event true moves 1 to 2 and fixes every other state; event
   false is the identity. *)
Definition trB_apply (e : bool) (x : nat) : nat := if e then (if Nat.eqb x 1 then 2 else x) else x.
Definition trB_star (x : nat) : nat := if Nat.eqb x 1 then 0 else x.
Definition trB_Phi (x : nat) : nat := if Nat.eqb x 1 then 1 else 0.

Lemma trB_wfc : forall x, ~ x <> 1 -> trB_Phi ((fun _ : nat => 0) x) < trB_Phi x.
Proof.
  intros x H. destruct (Nat.eq_dec x 1) as [-> | H']; [unfold trB_Phi; simpl; lia | contradiction].
Qed.

Lemma trB_reach : forall x B,
  star (step bool_dec trB_apply (fun _ => 0) (fun x => x <> 1) free_enabled) (x, B) (trB_star x, B).
Proof.
  intros x B. unfold trB_star. destruct (Nat.eq_dec x 1) as [-> | H].
  - simpl. apply star_one.
    apply (st_comp bool_dec trB_apply (fun _ => 0) (fun x => x <> 1) free_enabled 1 B).
    intro H. apply H. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq x 1) H). apply star_refl.
Qed.

Lemma trB_vstar : forall x, trB_star x <> 1.
Proof.
  intros x. unfold trB_star. destruct (Nat.eqb x 1) eqn:E; [discriminate |].
  apply Nat.eqb_neq. exact E.
Qed.

Definition trB : Reg nat bool :=
  mkReg bool_dec trB_apply (fun _ => 0) trB_star (fun x => x <> 1) trB_Phi trB_wfc trB_reach trB_vstar.

Lemma trA_reach01 : forall s, reach (g_apply trA) (g_rho trA) (g_valid trA) 0 s -> s = 0 \/ s = 1.
Proof. intros s H. induction H; simpl; auto. Qed.

Lemma trB_reach0 : forall y, reach (g_apply trB) (g_rho trB) (g_valid trB) 0 y -> y = 0.
Proof.
  intros y H. induction H as [| e y _ IH | y _ IH Hinv]; [reflexivity | |].
  - subst. destruct e; reflexivity.
  - subst. exfalso. apply Hinv. simpl. discriminate.
Qed.

Theorem migrated_transient :
  RCCA trA 0 /\ RBar trA trB (fun s => s) (fun _ => false) 0 /\
  S1 (g_apply trA) (g_rho trA) (g_valid trA) (g_apply trB) (g_star trB) (fun s => s) (fun _ => false) 0 /\
  S2 (g_apply trA) (g_rho trA) (g_valid trA) (g_star trB) (fun s => s) 0 /\
  RCCB trB 0 /\ ~ RCCB trB 1 /\
  ~ RLive trA trB (fun s => s) (fun _ => false) 0.
Proof.
  assert (HA : RCCA trA 0) by (split; simpl; intros; reflexivity).
  assert (HB0 : RCCB trB 0).
  { split.
    - intros y e1 e2 Hy. rewrite (trB_reach0 y Hy). destruct e1, e2; reflexivity.
    - intros y e Hy Hinv. rewrite (trB_reach0 y Hy) in Hinv. exfalso. apply Hinv. simpl. discriminate. }
  assert (NB1 : ~ RCCB trB 1).
  { intros [_ H2]. assert (Hinv : ~ g_valid trB 1) by (simpl; intro H; apply H; reflexivity).
    specialize (H2 1 true (r_init _ _ _ _) Hinv). simpl in H2. discriminate H2. }
  split; [exact HA |]. split; [| split; [| split; [| split; [exact HB0 | split; [exact NB1 |]]]]].
  - apply rbarrier_exact_faithful.
    + intros t1 t2 R1 R2 N1 N2 _.
      assert (V : forall t, reach (g_apply trA) (g_rho trA) (g_valid trA) 0 t ->
        normal_form (step (g_eq trA) (g_apply trA) (g_rho trA) (g_valid trA) free_enabled) (t, []) -> t = 0).
      { intros t R N. destruct (trA_reach01 t R) as [-> | ->]; [reflexivity |].
        exfalso. apply N. eexists. apply st_comp. simpl. discriminate. }
      rewrite (V t1 R1 N1), (V t2 R2 N2). reflexivity.
    + split; [exact HA |]. intros t R N.
      destruct (trA_reach01 t R) as [-> | ->]; [exact HB0 |].
      exfalso. apply N. eexists. apply st_comp. simpl. discriminate.
  - intros s e R. destruct (trA_reach01 s R) as [-> | ->]; reflexivity.
  - intros s R Hinv. destruct (trA_reach01 s R) as [-> | ->]; [exfalso; apply Hinv; reflexivity |].
    reflexivity.
  - intros H. apply (proj1 (rlive_exact trA trB _ _ 0)) in H. destruct H as [HB _].
    apply NB1. apply (HB 1). exact (r_apply (g_apply trA) (g_rho trA) (g_valid trA) 0 tt 0 (r_init _ _ _ _)).
Qed.

(* ---- forgetful_migration: A diverges, the migration forgets the difference. ---- *)

Definition lwwA : Reg nat bool := triv bool_dec (fun e (_ : nat) => if e then 1 else 2).
Definition unitB : Reg unit unit := triv unit_eq_dec (fun _ _ => tt).

Theorem forgetful_migration :
  RLive lwwA unitB (fun _ => tt) (fun _ => tt) 0 /\ RBar lwwA unitB (fun _ => tt) (fun _ => tt) 0 /\
  ~ RCCA lwwA 0.
Proof.
  assert (L : RLive lwwA unitB (fun _ => tt) (fun _ => tt) 0).
  { apply rlive_exact. split; [| split].
    - intros s _. split; simpl.
      + intros y e1 e2 _. reflexivity.
      + intros y e _ H. exfalso. exact (H I).
    - intros s e _. reflexivity.
    - intros s _ H. exfalso. exact (H I). }
  split; [exact L |]. split; [apply rlive_implies_barrier; exact L |].
  intros [H1 _]. specialize (H1 0 true false (r_init _ _ _ _)). simpl in H1. discriminate H1.
Qed.

(* ---- rescaled_cap: online-safe, every condition holding (non-vacuity). ---- *)

Definition capB2 : Reg nat bool := cap 10 bool_dec (fun e => if e then 2 else 1).

Theorem rescaled_cap : forall s0,
  RLive capA capB2 (fun s => 2 * s) (fun _ => true) s0 /\
  RCCA capA s0 /\ RLiveCond capA capB2 (fun s => 2 * s) (fun _ => true) s0 /\
  RFaithful capA capB2 (fun s => 2 * s) s0.
Proof.
  intros s0.
  assert (LC : RLiveCond capA capB2 (fun s => 2 * s) (fun _ => true) s0).
  { split; [| split].
    - intros s _. apply cap_cc.
    - intros s e _. simpl. f_equal. lia.
    - intros s _ H. change (Nat.min (2 * 5) 10 = Nat.min (2 * s) 10).
      change (~ s <= 5) in H. rewrite (Nat.min_r (2 * s) 10) by lia. reflexivity. }
  split; [apply rlive_exact; exact LC |]. split; [apply cap_cc |]. split; [exact LC |].
  intros t1 t2 _ _ N1 N2 E. change (Nat.min (2 * t1) 10 = Nat.min (2 * t2) 10) in E.
  pose proof (cap_nf_le 5 unit_eq_dec (fun _ => 1) t1 N1).
  pose proof (cap_nf_le 5 unit_eq_dec (fun _ => 1) t2 N2).
  rewrite (Nat.min_l (2 * t1) 10), (Nat.min_l (2 * t2) 10) in E by lia. lia.
Qed.

(* ---- lww_target: B diverges after the switch: unsafe. ---- *)

Theorem lww_target :
  RCCA succA 0 /\ ~ RBar succA lwwA (fun s => s) (fun _ => true) 0.
Proof.
  split.
  - split; simpl; [intros s [] [] _; reflexivity | intros s e _ H; exfalso; exact (H I)].
  - intros H. apply (proj1 (rbarrier_exact succA lwwA _ _ 0)) in H. destruct H as [HB _].
    destruct (HB 0 (r_init _ _ _ _) (nf_valid_empty _ _ _ _ 0 I)) as [H1 _].
    specialize (H1 0 true false (r_init _ _ _ _)). simpl in H1. discriminate H1.
Qed.

(* The four outcomes, classified. *)
Theorem instances_classified :
  Classified capA capB (fun s => s) (fun e => e) 0 BarrierOnly /\
  Classified succA succA (fun s => 2 * s) (fun e => e) 0 BarrierOnly /\
  Classified trA trB (fun s => s) (fun _ => false) 0 BarrierOnly /\
  Classified capA capB2 (fun s => 2 * s) (fun _ => true) 0 Online /\
  Classified lwwA unitB (fun _ => tt) (fun _ => tt) 0 Online /\
  Classified succA lwwA (fun s => s) (fun _ => true) 0 Unsafe.
Proof.
  destruct cap_raise as [_ [_ [B1 [L1 _]]]].
  destruct doubling_migration as [_ [_ [B2 [L2 _]]]].
  destruct migrated_transient as [_ [B3 [_ [_ [_ [_ L3]]]]]].
  split; [split; assumption |]. split; [split; assumption |]. split; [split; assumption |].
  split; [exact (proj1 (rescaled_cap 0)) |]. split; [exact (proj1 forgetful_migration) |].
  exact (proj2 lww_target).
Qed.

(* The finite hypotheses of classify_finite are satisfiable: a two-state instance (a flag set by
   its event, migrated by the identity). *)
Definition flagA : Reg bool bool := triv bool_dec (fun e (_ : bool) => e).

Lemma bool_full : forall b : bool, In b [true; false].
Proof. intros []; simpl; auto. Qed.

Lemma unit_full : forall u : unit, In u [tt].
Proof. intros []; simpl; auto. Qed.

Theorem finite_instance : {o : outcome | Classified flagA flagA (fun b => b) (fun e => e) false o}.
Proof.
  apply (classify_finite flagA flagA (fun b => b) (fun e => e) bool_dec bool_dec
           [true; false] bool_full [true; false] bool_full [true; false] bool_full
           [true; false] bool_full (fun _ => left I) (fun _ => left I)).
  intros t1 t2 _ _ _ _ E. exact E.
Qed.

(* ============================================================================================ *)
(* 3. Deterministic systems with free delivery, and federations (FedMachine semantics).          *)
(* ============================================================================================ *)

Section Det.
  Context {SA EA SB EB : Type}.
  Variable stepA : EA -> SA -> SA.
  Variable stepB : EB -> SB -> SB.
  Variable eqvA : SA -> SA -> Prop.
  Variable eqvB : SB -> SB -> Prop.
  Hypothesis eqvB_refl : forall x, eqvB x x.
  Hypothesis eqvB_sym : forall x y, eqvB x y -> eqvB y x.
  Hypothesis eqvB_trans : forall x y z, eqvB x y -> eqvB y z -> eqvB x z.
  Hypothesis stepB_ext : forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y).
  Variable M : SA -> SB.
  Variable tau : EA -> EB.

  Local Notation runA := (runT stepA).
  Local Notation runB := (runT stepB).

  (* A live run: u under A, the switch, then the in-flight rest r (translated) and the B-events
     in any order. A barrier run: r = []. *)
  Definition OutLive (s0 : SA) (Ea : list EA) (Eb : list EB) (y : SB) : Prop :=
    exists u r v, Permutation (u ++ r) Ea /\ Permutation v (map tau r ++ Eb) /\
      y = runB v (M (runA u s0)).
  Definition OutBar (s0 : SA) (Ea : list EA) (Eb : list EB) (y : SB) : Prop :=
    exists u v, Permutation u Ea /\ Permutation v Eb /\ y = runB v (M (runA u s0)).

  Definition DLive (s0 : SA) : Prop :=
    forall Ea Eb y1 y2, OutLive s0 Ea Eb y1 -> OutLive s0 Ea Eb y2 -> eqvB y1 y2.
  Definition DBar (s0 : SA) : Prop :=
    forall Ea Eb y1 y2, OutBar s0 Ea Eb y1 -> OutBar s0 Ea Eb y2 -> eqvB y1 y2.

  Definition PermB (x : SB) : Prop :=
    forall v v', Permutation v v' -> eqvB (runB v x) (runB v' x).
  Definition PermA (s : SA) : Prop :=
    forall u u', Permutation u u' -> eqvA (runA u s) (runA u' s).
  Definition DS1 (s0 : SA) : Prop :=
    forall u e, eqvB (M (stepA e (runA u s0))) (stepB (tau e) (M (runA u s0))).

  Lemma runB_ext : forall v x y, eqvB x y -> eqvB (runB v x) (runB v y).
  Proof.
    induction v as [| e v IH]; intros x y H; [exact H |].
    rewrite !runT_cons. apply IH. apply stepB_ext. exact H.
  Qed.

  Lemma M_run : forall s0, DS1 s0 -> forall u, eqvB (M (runA u s0)) (runB (map tau u) (M s0)).
  Proof.
    intros s0 H u. induction u as [| e u IH] using rev_ind; [apply eqvB_refl |].
    rewrite runT_app, map_app, runT_app. simpl.
    apply (eqvB_trans _ _ _ (H u e)). apply stepB_ext. exact IH.
  Qed.

  Theorem det_live_exact : forall s0, DLive s0 <-> PermB (M s0) /\ DS1 s0.
  Proof.
    intros s0. split.
    - intros H. split.
      + intros v v' P. apply (H [] v').
        * exists [], [], v. split; [apply Permutation_refl |]. split; [simpl; exact P | reflexivity].
        * exists [], [], v'. split; [apply Permutation_refl |].
          split; [apply Permutation_refl | reflexivity].
      + intros u e. apply (H (u ++ [e]) []).
        * exists (u ++ [e]), [], []. split; [rewrite app_nil_r; apply Permutation_refl |].
          split; [apply Permutation_refl |]. simpl. rewrite runT_app. reflexivity.
        * exists u, [e], [tau e]. split; [apply Permutation_refl |].
          split; [apply Permutation_refl | reflexivity].
    - intros [HP HS] Ea Eb y1 y2 [u1 [r1 [v1 [P1 [Q1 ->]]]]] [u2 [r2 [v2 [P2 [Q2 ->]]]]].
      assert (K : forall u r v, Permutation (u ++ r) Ea -> Permutation v (map tau r ++ Eb) ->
        eqvB (runB v (M (runA u s0))) (runB (map tau Ea ++ Eb) (M s0))).
      { intros u r v P Q. apply (eqvB_trans _ (runB v (runB (map tau u) (M s0)))).
        - apply runB_ext. apply M_run. exact HS.
        - rewrite <- runT_app. apply HP.
          apply (Permutation_trans (Permutation_app_head (map tau u) Q)).
          rewrite app_assoc, <- map_app. apply Permutation_app_tail. apply Permutation_map. exact P. }
      apply (eqvB_trans _ _ _ (K u1 r1 v1 P1 Q1)). apply eqvB_sym. exact (K u2 r2 v2 P2 Q2).
  Qed.

  Theorem det_barrier_exact : forall s0, DBar s0 <->
    (forall u, PermB (M (runA u s0))) /\
    (forall u u', Permutation u u' -> eqvB (M (runA u s0)) (M (runA u' s0))).
  Proof.
    intros s0. split.
    - intros H. split.
      + intros u v v' P. apply (H u v').
        * exists u, v. split; [apply Permutation_refl | split; [exact P | reflexivity]].
        * exists u, v'. split; [apply Permutation_refl | split; [apply Permutation_refl | reflexivity]].
      + intros u u' P. apply (H u' []).
        * exists u, []. split; [exact P | split; [apply Permutation_refl | reflexivity]].
        * exists u', []. split; [apply Permutation_refl | split; [apply Permutation_refl | reflexivity]].
    - intros [HP HM] Ea Eb y1 y2 [u1 [v1 [P1 [Q1 ->]]]] [u2 [v2 [P2 [Q2 ->]]]].
      apply (eqvB_trans _ (runB v1 (M (runA u2 s0)))).
      + apply runB_ext. apply HM. exact (Permutation_trans P1 (Permutation_sym P2)).
      + apply HP. exact (Permutation_trans Q1 (Permutation_sym Q2)).
  Qed.

  (* When M reflects and preserves the equivalences, the A part is A's own permutation
     convergence: the barrier condition is each side's condition. *)
  Theorem det_barrier_faithful : (forall x y, eqvA x y <-> eqvB (M x) (M y)) ->
    forall s0, DBar s0 <-> (forall u, PermB (M (runA u s0))) /\ PermA s0.
  Proof.
    intros HM s0. rewrite det_barrier_exact. split; intros [H1 H2]; split; try exact H1.
    - intros u u' P. apply HM. apply H2. exact P.
    - intros u u' P. apply HM. apply H2. exact P.
  Qed.

  Theorem det_live_implies_barrier : forall s0, DLive s0 -> DBar s0.
  Proof.
    intros s0 H Ea Eb y1 y2 [u1 [v1 [P1 [Q1 E1]]]] [u2 [v2 [P2 [Q2 E2]]]].
    apply (H Ea Eb).
    - exists u1, [], v1. rewrite app_nil_r. split; [exact P1 | split; [exact Q1 | exact E1]].
    - exists u2, [], v2. rewrite app_nil_r. split; [exact P2 | split; [exact Q2 | exact E2]].
  Qed.
End Det.

(* Permutation convergence of a FedMachine with every same-registry pair declared is TraceConv. *)
Lemma permB_traceconv : forall (V : Type) (f : nat -> (nat -> V) -> V -> V) (rho : nat -> V -> V)
  (E : Type) (reg : E -> nat) (sig : E -> V -> V) (o : list nat) x,
  PermB (applyF V f rho E reg sig o) (feq V) x <->
  TraceConv V f rho E reg sig (fun _ _ => True) o x.
Proof.
  intros V f rho E reg sig o x. split.
  - intros H es1 es2 T. apply H. exact (tequiv_perm _ _ _ T).
  - intros H v v' P. apply H.
    apply (perm_tequiv_total (Ifed E reg (fun _ _ => True)) (fun _ => True)); [| exact P |].
    + intros a b _ _. right. exact I.
    + apply Forall_forall. intros. exact I.
Qed.

Section FedSwitch.
  Variables (VA VB : Type).
  Variable srcA : nat -> list nat.
  Variable fA : nat -> (nat -> VA) -> VA -> VA.
  Variable validA : nat -> VA -> Prop.
  Variable rhoA : nat -> VA -> VA.
  Variable EA : Type.
  Variable regA : EA -> nat.
  Variable sigA : EA -> VA -> VA.
  Variable oA : list nat.
  Variable srcB : nat -> list nat.
  Variable fB : nat -> (nat -> VB) -> VB -> VB.
  Variable validB : nat -> VB -> Prop.
  Variable rhoB : nat -> VB -> VB.
  Variable EB : Type.
  Variable regB : EB -> nat.
  Variable sigB : EB -> VB -> VB.
  Variable oB : list nat.
  Variable M : (nat -> VA) -> (nat -> VB).
  Variable tau : EA -> EB.
  Hypothesis HCA : Common VA srcA fA validA rhoA EA regA sigA oA.
  Hypothesis HCB : Common VB srcB fB validB rhoB EB regB sigB oB.

  Local Notation aA := (applyF VA fA rhoA EA regA sigA oA).
  Local Notation aB := (applyF VB fB rhoB EB regB sigB oB).

  Definition FLive (s0 : nat -> VA) : Prop := DLive aA aB (feq VB) M tau s0.
  Definition FBar (s0 : nat -> VA) : Prop := DBar aA aB (feq VB) M s0.
  Definition FS1 (s0 : nat -> VA) : Prop := DS1 aA aB (feq VB) M tau s0.

  Let feq_refl : forall x, feq VB x x := fun x k => eq_refl.
  Let feq_sym' : forall x y, feq VB x y -> feq VB y x := feq_sym VB.
  Let feq_trans' : forall x y z, feq VB x y -> feq VB y z -> feq VB x z := feq_trans VB.

  (* A live topology change: exact, with B's condition at the migrated start only. *)
  Theorem fed_live_exact : forall s0, Inv VB validB (M s0) -> Cons VB fB oB (M s0) ->
    (FLive s0 <-> (C1R1 VB fB rhoB EB regB sigB oB (M s0) /\
                   C2R VB fB rhoB EB regB sigB (fun _ _ => True) oB (M s0)) /\ FS1 s0).
  Proof.
    intros s0 HI HC. unfold FLive, FS1.
    rewrite (det_live_exact aA aB (feq VB) feq_refl feq_sym' feq_trans'
               (applyF_ext VB srcB fB validB rhoB EB regB sigB oB HCB) M tau s0).
    rewrite permB_traceconv.
    rewrite (fed_exact VB srcB fB validB rhoB EB regB sigB (fun _ _ => True) oB HCB (M s0) HI HC).
    tauto.
  Qed.

  (* A topology change at a barrier: each side's exact condition. *)
  Theorem fed_barrier_exact : forall s0, Inv VA validA s0 -> Cons VA fA oA s0 ->
    (forall t, Inv VA validA t -> Cons VA fA oA t -> Inv VB validB (M t) /\ Cons VB fB oB (M t)) ->
    (forall t t', feq VA t t' <-> feq VB (M t) (M t')) ->
    (FBar s0 <->
     (C1R1 VA fA rhoA EA regA sigA oA s0 /\ C2R VA fA rhoA EA regA sigA (fun _ _ => True) oA s0) /\
     (forall u, C1R1 VB fB rhoB EB regB sigB oB (M (runF VA fA rhoA EA regA sigA oA u s0)) /\
                C2R VB fB rhoB EB regB sigB (fun _ _ => True) oB
                  (M (runF VA fA rhoA EA regA sigA oA u s0)))).
  Proof.
    intros s0 HI HC HM HF. unfold FBar.
    rewrite (det_barrier_faithful aA aB (feq VA) (feq VB) feq_trans'
               (applyF_ext VB srcB fB validB rhoB EB regB sigB oB HCB) M HF s0).
    assert (EA' : PermA aA (feq VA) s0 <->
      (C1R1 VA fA rhoA EA regA sigA oA s0 /\ C2R VA fA rhoA EA regA sigA (fun _ _ => True) oA s0)).
    { rewrite <- (fed_exact VA srcA fA validA rhoA EA regA sigA (fun _ _ => True) oA HCA s0 HI HC).
      exact (permB_traceconv VA fA rhoA EA regA sigA oA s0). }
    assert (EB' : forall u, PermB aB (feq VB) (M (runT aA u s0)) <->
      (C1R1 VB fB rhoB EB regB sigB oB (M (runF VA fA rhoA EA regA sigA oA u s0)) /\
       C2R VB fB rhoB EB regB sigB (fun _ _ => True) oB (M (runF VA fA rhoA EA regA sigA oA u s0)))).
    { intros u. change (runT aA u s0) with (runF VA fA rhoA EA regA sigA oA u s0).
      destruct (HM _ (runF_inv VA srcA fA validA rhoA EA regA sigA oA HCA u s0 HI)
                     (runF_cons VA srcA fA validA rhoA EA regA sigA oA HCA u s0 HI HC)) as [HI' HC'].
      rewrite <- (fed_exact VB srcB fB validB rhoB EB regB sigB (fun _ _ => True) oB HCB _ HI' HC').
      exact (permB_traceconv VB fB rhoB EB regB sigB oB _). }
    split.
    - intros [H1 H2]. split; [exact (proj1 EA' H2) |]. intros u. exact (proj1 (EB' u) (H1 u)).
    - intros [H2 H1]. split; [intros u; exact (proj2 (EB' u) (H1 u)) | exact (proj2 EA' H2)].
  Qed.

  Theorem fed_live_implies_barrier : forall s0, FLive s0 -> FBar s0.
  Proof. intros s0. exact (det_live_implies_barrier aA aB (feq VB) M tau s0). Qed.
End FedSwitch.

(* ---- late_edge: adding the edge 0 -> 1 to a two-registry federation. ---- *)

(* Registry states are pairs (shared, local). Before the change registry 1 has no source, and its
   shared part is local data; after it, registry 1's shared part is the image of registry 0's
   first component. The migration is B's normalizer: the new edge propagates once. The event (on
   registry 1) adds the shared part to the local part. *)
Definition le_srcA (_ : nat) : list nat := [].
Definition le_srcB (j : nat) : list nat := if Nat.eqb j 1 then [0] else [].
Definition le_fA (_ : nat) (_ : nat -> nat * nat) (x : nat * nat) : nat * nat := x.
Definition le_fB (j : nat) (t : nat -> nat * nat) (x : nat * nat) : nat * nat :=
  if Nat.eqb j 1 then (fst (t 0), snd x) else x.
Definition le_valid (_ : nat) (_ : nat * nat) : Prop := True.
Definition le_rho (_ : nat) (x : nat * nat) : nat * nat := x.
Definition le_reg (_ : unit) : nat := 1.
Definition le_sig (_ : unit) (x : nat * nat) : nat * nat := (fst x, snd x + fst x).
Definition le_o : list nat := [0; 1].
Definition le_M (t : nat -> nat * nat) : nat -> nat * nat := N (nat * nat) le_fB le_rho le_o t.

Local Notation leA := (applyF (nat * nat) le_fA le_rho unit le_reg le_sig le_o).
Local Notation leB := (applyF (nat * nat) le_fB le_rho unit le_reg le_sig le_o).

Lemma le_common_A : Common (nat * nat) le_srcA le_fA le_valid le_rho unit le_reg le_sig le_o.
Proof.
  constructor.
  - intros; reflexivity.
  - simpl. split; [intro H; destruct H as [H | []]; discriminate |].
    split; [intros k H; destruct H |]. split; [intro H; destruct H |].
    split; [intros k H; destruct H | exact I].
  - intros; exact I.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; exact I.
  - intros []. simpl. auto.
Qed.

Lemma le_common_B : Common (nat * nat) le_srcB le_fB le_valid le_rho unit le_reg le_sig le_o.
Proof.
  constructor.
  - intros j z1 z2 x H. unfold le_fB. destruct (Nat.eqb j 1) eqn:E; [| reflexivity].
    rewrite (H 0); [reflexivity |]. unfold le_srcB. rewrite E. left. reflexivity.
  - simpl. split; [intro H; destruct H as [H | []]; discriminate |].
    split; [intros k H; destruct H |]. split; [intro H; destruct H |]. split; [| exact I].
    intros k H. destruct H as [<- | []]. intro H. destruct H as [H | []]. discriminate.
  - intros; exact I.
  - intros j z z' x _ _ _. unfold le_fB. destruct (Nat.eqb j 1); reflexivity.
  - intros; reflexivity.
  - intros; exact I.
  - intros []. simpl. auto.
Qed.

Lemma le_M_at : forall t k, le_M t k = if Nat.eqb k 1 then (fst (t 0), snd (t 1)) else t k.
Proof. intros t [| [| k]]; reflexivity. Qed.

Lemma le_A_at : forall t k, leA tt t k = if Nat.eqb k 1 then (fst (t 1), snd (t 1) + fst (t 1)) else t k.
Proof. intros t [| [| k]]; reflexivity. Qed.

Lemma le_B_at : forall t k,
  leB tt t k = if Nat.eqb k 1 then (fst (t 0), snd (t 1) + fst (t 1)) else t k.
Proof. intros t [| [| k]]; reflexivity. Qed.

Lemma le_perm_unit : forall (l l' : list unit), Permutation l l' -> l = l'.
Proof.
  intros l l' P. pose proof (Permutation_length P) as H. clear P. revert l' H.
  induction l as [| [] l IH]; intros [| [] l'] H; simpl in H; try discriminate; [reflexivity |].
  f_equal. apply IH. lia.
Qed.

(* The stale start: registry 1's shared part (0) differs from the image the new edge will write (7). *)
Definition le_stale (k : nat) : nat * nat := if Nat.eqb k 0 then (7, 0) else (0, 0).
(* The fresh start: registry 1's shared part already equals the image. *)
Definition le_fresh (_ : nat) : nat * nat := (7, 0).

(* A and B each converge, and the barrier change converges from every start, but a live change
   from the stale start diverges: an event submitted before the edge and applied after it reads
   the new source value. *)
Theorem late_edge :
  (forall s0, PermA leA (feq (nat * nat)) s0) /\ (forall x, PermB leB (feq (nat * nat)) x) /\
  (forall s0, FBar (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
                le_fB le_rho unit le_reg le_sig le_o le_M s0) /\
  ~ FLive (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
          le_fB le_rho unit le_reg le_sig le_o le_M (fun e => e) le_stale /\
  ~ FS1 (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
        le_fB le_rho unit le_reg le_sig le_o le_M (fun e => e) le_stale.
Proof.
  assert (NS : ~ FS1 (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
                     le_fB le_rho unit le_reg le_sig le_o le_M (fun e => e) le_stale).
  { intros H. specialize (H [] tt 1). vm_compute in H. discriminate H. }
  split; [intros s0 u u' P; rewrite (le_perm_unit u u' P); intro k; reflexivity |].
  split; [intros x v v' P; rewrite (le_perm_unit v v' P); intro k; reflexivity |].
  split; [| split; [| exact NS]].
  - intros s0. unfold FBar.
    apply (det_barrier_exact leA leB (feq (nat * nat)) (feq_trans (nat * nat))
             (applyF_ext _ _ _ _ _ _ _ _ _ le_common_B) le_M s0).
    split.
    + intros u v v' P. rewrite (le_perm_unit v v' P). intro k. reflexivity.
    + intros u u' P. rewrite (le_perm_unit u u' P). intro k. reflexivity.
  - intros H. apply NS.
    exact (proj2 (proj1 (det_live_exact leA leB (feq (nat * nat)) (fun x k => eq_refl)
             (feq_sym _) (feq_trans _) (applyF_ext _ _ _ _ _ _ _ _ _ le_common_B) le_M (fun e => e)
             le_stale) H)).
Qed.

(* The same change from the fresh start is online-safe, and every hypothesis of fed_live_exact
   holds there, so B's exact condition holds at the migrated start (non-vacuity). *)
Theorem late_edge_fresh :
  FLive (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
        le_fB le_rho unit le_reg le_sig le_o le_M (fun e => e) le_fresh /\
  C1R1 (nat * nat) le_fB le_rho unit le_reg le_sig le_o (le_M le_fresh) /\
  C2R (nat * nat) le_fB le_rho unit le_reg le_sig (fun _ _ => True) le_o (le_M le_fresh).
Proof.
  assert (Inv0 : forall u, (runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u le_fresh) 0 = (7, 0) /\
                           fst (runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u le_fresh 1) = 7).
  { intros u. assert (G : forall t, t 0 = (7, 0) -> fst (t 1) = 7 ->
      runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u t 0 = (7, 0) /\
      fst (runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u t 1) = 7).
    { induction u as [| [] u IH]; intros t H0 H1; [split; assumption |].
      apply IH; rewrite le_A_at; simpl; assumption. }
    apply G; reflexivity. }
  assert (L : FLive (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
                    le_fB le_rho unit le_reg le_sig le_o le_M (fun e => e) le_fresh).
  { apply (det_live_exact leA leB (feq (nat * nat)) (fun x k => eq_refl)
             (feq_sym _) (feq_trans _) (applyF_ext _ _ _ _ _ _ _ _ _ le_common_B) le_M (fun e => e)
             le_fresh).
    split.
    - intros v v' P. rewrite (le_perm_unit v v' P). intro k. reflexivity.
    - intros u [] k. destruct (Inv0 u) as [H0 H1].
      change (runT leA u le_fresh) with (runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u le_fresh).
      revert H0 H1. generalize (runF (nat * nat) le_fA le_rho unit le_reg le_sig le_o u le_fresh) as t.
      intros t H0 H1. rewrite le_M_at, le_B_at, !le_A_at, !le_M_at.
      destruct k as [| [| k]]; simpl; [reflexivity | | reflexivity].
      rewrite H0. simpl. rewrite H1. reflexivity. }
  assert (HI : Inv (nat * nat) le_valid (le_M le_fresh)) by (intros k; exact I).
  assert (HC : Cons (nat * nat) le_fB le_o (le_M le_fresh)).
  { intros j Hj. destruct Hj as [<- | [<- | []]]; reflexivity. }
  destruct (proj1 (fed_live_exact (nat * nat) (nat * nat) le_fA le_rho unit le_reg le_sig le_o
                     le_srcB le_fB le_valid le_rho unit le_reg le_sig le_o le_M (fun e => e)
                     le_common_B le_fresh HI HC) L) as [[C1 C2] _].
  split; [exact L | split; assumption].
Qed.
