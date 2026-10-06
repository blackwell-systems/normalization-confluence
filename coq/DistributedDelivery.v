(* DistributedDelivery.v: causal and at-least-once event delivery in the distributed model of an
   acyclic federation, exactly (gap 15 (c) of REGIME-AUDIT.md). Axiom-free.

   DistributedExact.v characterizes the distributed model (local events and propagation steps as
   separate actions, FederationEvents.v) for exactly-once delivery compared up to federated trace
   equivalence: DistConv s0 <-> XUR s0 /\ TraceConv (N s0) (dist_exact_tc). For causal or
   at-least-once delivery only a sufficient condition followed, by restricting DistConv. This file
   states the exact condition for any delivery class.

   A delivery class is a set Adm of admissible event sequences, closed under prefixes (adm_prefix),
   with a comparison Rel between admissible sequences, reflexive on them (rel_refl). A distributed
   word w is admissible when its event sequence evs w is.
     XURD Adm s0      := XU (DistributedExact.XUat) at every state drun p s0 such that
                         evs p ++ [e] is admissible: the reachability of XU is the class's own.
     DistConvD Adm Rel s0 := admissible words with Rel-related event sequences agree after the
                         final flush.
     FedConvD Adm Rel s   := the FedMachine runs of Rel-related admissible sequences agree (feq).
   - dist_delivery_exact : Inv s0 -> (DistConvD Adm Rel s0 <-> XURD Adm s0 /\ FedConvD Adm Rel (N s0)).
     The first conjunct is the propagation layer (an event at a stale state against the event at
     its flush), the second the event-order layer on the FedMachine (P1 with the class's delivery).
   - dist_exact_tc_recovered: Adm = every sequence, Rel = federated trace equivalence gives
     DistributedExact.dist_exact_tc (and dist_exact through it).

   The FedMachine compares states pointwise (feq), so the event-order conditions are stated up to an
   equivalence. Section SetoidALO proves the causal exactly-once and causal at-least-once exact
   theorems of GovernanceConverse.causal_exact and AtLeastOnceExact.causal_alo_exact_idem for a
   step that respects an equivalence eqv (no functional extensionality):
   - causal_conv_s_exact : CConvS s0 <-> CCRonS s0,
   - causal_alo_s_exact  : CALOConvS s0 <-> CCRonS s0 /\ forall a, IdemAtS s0 a;
   at eqv = eq they rederive the Leibniz theorems (causal_alo_exact_recovered,
   causal_exact_recovered).

   Instances (hb an irreflexive happens-before on events; FedMachine step applyF from N s0).
   - Causal exactly-once (Adm = causal hb, Rel = Permutation):
       dist_causal_exact : DistCausal s0 <-> XURC s0 /\ CCRF (N s0),
     XURC: XU at the states reached by words whose events, extended by e, are causally consistent;
     CCRF: concurrent pairs commute on the FedMachine after every causally consistent prefix.
   - Free at-least-once (Adm = every sequence, duplicates allowed; Rel = same set of events):
       dist_alo_exact : DistALO s0 <-> XUR s0 /\ CommRF (N s0) /\ forall a, IdemRF (N s0) a,
     with XUR exactly dist_exact's propagation condition, CommRF: distinct events commute on the
     FedMachine after every duplicate-free prefix, IdemRF: a is idempotent on the FedMachine where
     it is first delivered.
   - Causal at-least-once (Adm = causal_alo hb, Rel = same set):
       dist_causal_alo_exact : DistCALO s0 <-> XURCA s0 /\ CCRF (N s0) /\ forall a, IdemF (N s0) a.

   Counterexamples and non-vacuity (two registries, V = nat * nat (shared, local); registry 1's
   shared part copies registry 0's; every state valid, no repair).
   - tr_causal_instance: TRead on registry 1 adds its shared value to its local part, RSet on
     registry 0 sets the shared value to 1, TRead happens before RSet, from the zero start. XURC,
     CCRF, IdemF and XURCA hold: causal delivery and causal at-least-once delivery converge. XUR
     fails (RSet, then TRead with no propagation in between, reads a stale value), so DistConv
     (dist_exact) fails and so does free at-least-once delivery. The naive claim "restricting
     dist_exact is exact for causal delivery" is false: its condition is not necessary.
   - snap_xu_needed: one event Snap on registry 1 (copy the shared value into the local part), from
     a valid start whose target is stale. Every FedMachine condition holds (CCRF, CommRF, IdemRF,
     IdemF), XURC fails at the start, and causal, free at-least-once and causal at-least-once
     delivery all fail: the propagation conjunct is needed.
   - set_comm_needed: Set1 and Set2 overwrite registry 0, no causal order. XU holds everywhere, every
     event is idempotent, CCRF and CommRF fail, and every class diverges.
   - inc_idem_needed: Incr increments registry 0. XU holds, DistConv holds (dist_exact), CommRF
     holds, IdemRF fails, DistALO fails: dist_exact's condition is not sufficient for
     at-least-once delivery, and the idempotence clause is needed.
   - mk_alo_holds: a max-register on registry 0 and a mark on registry 1 satisfy every condition
     of every class from every valid start (non-vacuity of dist_alo_exact with events on both
     registries).

   gsm. xu_xurd: gsm's static XU (FedReport.ProjectionSafe) gives XURD for every delivery class
   from every valid start (xur_xurd: so does reachable XUR), so the propagation conjunct needs no
   new check; what the delivery class changes is the FedMachine conjunct. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.CausalReplay NC.AtLeastOnce NC.AtLeastOnceExact.
Require Import NC.FederationEvents NC.FederationEventsConverse NC.DistributedExact.
Require NC.GovernanceConverse.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Causal exactly-once and causal at-least-once convergence up to an equivalence.            *)
(* ============================================================================================ *)

Lemma causal_alo_app_prefix : forall {E : Type} (hb : E -> E -> Prop) l r,
  causal_alo hb (l ++ r) -> causal_alo hb l.
Proof.
  intros E hb l r H a b Hab l1 r1 El Hb Ha. subst l.
  apply (H a b Hab l1 (r1 ++ r)); [rewrite app_assoc; reflexivity | exact Hb |].
  apply in_or_app. left. exact Ha.
Qed.

Section SetoidALO.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.
  Variable hb : E -> E -> Prop.
  Hypothesis hb_irrefl : forall x, ~ hb x x.
  Variable eqv : S -> S -> Prop.
  Hypothesis eqv_refl : forall s, eqv s s.
  Hypothesis eqv_sym : forall s t, eqv s t -> eqv t s.
  Hypothesis eqv_trans : forall s t u, eqv s t -> eqv t u -> eqv s u.
  Hypothesis step_ext : forall e s t, eqv s t -> eqv (step e s) (step e t).

  Local Notation run := (runT step).

  (* Causal exactly-once convergence: causally consistent orders of the same events agree. *)
  Definition CConvS (s0 : S) : Prop :=
    forall o1 o2, causal hb o1 -> causal hb o2 -> Permutation o1 o2 -> eqv (run o1 s0) (run o2 s0).

  (* Causal at-least-once convergence: causally consistent deliveries with the same events agree. *)
  Definition CALOConvS (s0 : S) : Prop :=
    forall d1 d2, causal_alo hb d1 -> causal_alo hb d2 -> (forall x, In x d1 <-> In x d2) ->
      eqv (run d1 s0) (run d2 s0).

  Definition CCRonS (s0 : S) : Prop :=
    forall p a b, concurrent hb a b -> causal hb (p ++ [a; b]) ->
      eqv (step b (step a (run p s0))) (step a (step b (run p s0))).

  Definition IdemAtS (s0 : S) (a : E) : Prop :=
    forall u, causal hb (u ++ [a]) -> eqv (step a (step a (run u s0))) (step a (run u s0)).

  Definition AbsorbAtS (s0 : S) (a : E) : Prop :=
    forall w, causal hb w -> In a w -> (forall b, In b w -> ~ hb a b) -> eqv (step a (run w s0)) (run w s0).

  Lemma run_ext : forall l s t, eqv s t -> eqv (run l s) (run l t).
  Proof.
    induction l as [| e l IH]; intros s t H; [exact H |].
    rewrite !runT_cons. apply IH. apply step_ext. exact H.
  Qed.

  Lemma ccr_tequiv_s : forall s0, CCRonS s0 ->
    forall o1 o2, tequiv (concurrent hb) o1 o2 -> causal hb o1 -> eqv (run o1 s0) (run o2 s0).
  Proof.
    intros s0 HC o1 o2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2]; intros Hc.
    - apply eqv_refl.
    - rewrite !runT_app, !runT_cons. apply run_ext. apply HC; [exact Hab |].
      apply (GovernanceConverse.causal_prefix hb _ r). rewrite <- app_assoc. exact Hc.
    - apply eqv_sym. apply IH. apply (proj2 (GovernanceConverse.tequiv_causal hb l1 l2 H)). exact Hc.
    - eapply eqv_trans; [exact (IH1 Hc) |]. apply IH2.
      apply (proj1 (GovernanceConverse.tequiv_causal hb l1 l2 H1)). exact Hc.
  Qed.

  Theorem causal_conv_s_exact : forall s0, CConvS s0 <-> CCRonS s0.
  Proof.
    intros s0. split.
    - intros H p a b Hab Hc.
      assert (Hc' : causal hb (p ++ [b; a])) by (apply GovernanceConverse.causal_swap; [apply Hab | exact Hc]).
      pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hc Hc' (Permutation_app_head p (perm_swap b a []))) as Eq.
      rewrite !runT_app in Eq. exact Eq.
    - intros HC o1 o2 H1 H2 HP. apply (ccr_tequiv_s s0 HC); [| exact H1].
      apply causal_tequiv; assumption.
  Qed.

  Lemma absorb_dedup_s : forall s0, (forall a, AbsorbAtS s0 a) ->
    forall d, causal_alo hb d -> eqv (run d s0) (run (dedup dec d) s0).
  Proof.
    intros s0 HA d. induction d as [| x p IH] using rev_ind; intros Hca; [apply eqv_refl |].
    pose proof (causal_alo_prefix hb p x Hca) as Hcp.
    rewrite dedup_snoc, runT_app. change (run [x] (run p s0)) with (step x (run p s0)).
    destruct (in_dec dec x (dedup dec p)) as [Hin | Hin].
    - eapply eqv_trans; [apply step_ext; exact (IH Hcp) |]. apply HA.
      + exact (causal_alo_dedup_causal dec hb p hb_irrefl Hcp).
      + exact Hin.
      + intros b Hb Hxb. apply dedup_In in Hb.
        exact (Hca x b Hxb p [x] eq_refl Hb (or_introl eq_refl)).
    - rewrite runT_app. apply step_ext. exact (IH Hcp).
  Qed.

  Lemma absorb_idem_s : forall s0 a, AbsorbAtS s0 a -> IdemAtS s0 a.
  Proof.
    intros s0 a HA u Hc.
    pose proof (HA (u ++ [a]) Hc (in_or_app u [a] a (or_intror (or_introl eq_refl)))) as H.
    rewrite runT_app in H. apply H.
    intros b Hb Hab. apply in_app_or in Hb. destruct Hb as [Hb | [<- | []]]; [| exact (hb_irrefl a Hab)].
    destruct Hc as [Hnd Hcc].
    apply (prec_before_contra u a [] b Hnd Hb).
    apply Hcc; [exact Hab | apply in_or_app; right; left; reflexivity | apply in_or_app; left; exact Hb].
  Qed.

  Lemma idem_absorb_s : forall s0 a, CCRonS s0 -> IdemAtS s0 a -> AbsorbAtS s0 a.
  Proof.
    intros s0 a HC HI w Hc Ha Hns.
    apply in_split in Ha. destruct Ha as [l [r ->]].
    assert (Hconc : forall b, In b r -> concurrent hb a b).
    { intros b Hb. destruct Hc as [Hnd Hcc]. split; [| split].
      - intros ->. apply (NoDup_remove_2 l r b Hnd). apply in_or_app. right. exact Hb.
      - apply Hns. apply in_or_app. right. right. exact Hb.
      - intro Hba. apply (prec_after_contra l a r b Hnd Hb).
        apply Hcc; [exact Hba | apply in_or_app; right; right; exact Hb
                   | apply in_or_app; right; left; reflexivity]. }
    assert (Ht : tequiv (concurrent hb) (l ++ a :: r) ((l ++ r) ++ [a])).
    { rewrite <- app_assoc. apply NC.AtLeastOnceExact.tequiv_app_l. apply tequiv_to_back. exact Hconc. }
    assert (Hc' : causal hb ((l ++ r) ++ [a]))
      by exact (proj1 (GovernanceConverse.tequiv_causal hb _ _ Ht) Hc).
    pose proof (ccr_tequiv_s s0 HC _ _ Ht Hc) as E1.
    eapply eqv_trans; [apply step_ext; exact E1 |].
    eapply eqv_trans; [| apply eqv_sym; exact E1].
    rewrite runT_app. exact (HI (l ++ r) Hc').
  Qed.

  Theorem causal_alo_s_exact : forall s0, CALOConvS s0 <-> CCRonS s0 /\ forall a, IdemAtS s0 a.
  Proof.
    intros s0. split.
    - intros H. split.
      + apply causal_conv_s_exact. intros o1 o2 H1 H2 HP.
        apply H; [apply causal_causal_alo; exact H1 | apply causal_causal_alo; exact H2 |].
        intros x. split; [apply (Permutation_in x HP) | apply (Permutation_in x (Permutation_sym HP))].
      + intros a. apply absorb_idem_s. intros w Hc Ha Hns.
        pose proof (H (w ++ [a]) w (causal_snoc_alo hb w a Hc Hns) (causal_causal_alo hb w Hc)) as Eq.
        rewrite runT_app in Eq. apply Eq.
        intros x. rewrite in_app_iff. simpl. split; [| tauto]. intros [Hx | [<- | []]]; assumption.
    - intros [HC HI] d1 d2 H1 H2 Hs.
      assert (HA : forall a, AbsorbAtS s0 a) by (intros a; apply idem_absorb_s; [exact HC | apply HI]).
      eapply eqv_trans; [exact (absorb_dedup_s s0 HA d1 H1) |].
      eapply eqv_trans; [| apply eqv_sym; exact (absorb_dedup_s s0 HA d2 H2)].
      apply (proj2 (causal_conv_s_exact s0) HC).
      + exact (causal_alo_dedup_causal dec hb d1 hb_irrefl H1).
      + exact (causal_alo_dedup_causal dec hb d2 hb_irrefl H2).
      + apply NoDup_Permutation; [apply dedup_NoDup | apply dedup_NoDup |].
        intros x. rewrite !dedup_In. apply Hs.
  Qed.
End SetoidALO.

(* At eqv = eq the setoid theorems are the Leibniz ones. *)
Theorem causal_alo_exact_recovered : forall {S E : Type} (dec : forall x y : E, {x = y} + {x <> y})
  (step : E -> S -> S) (hb : E -> E -> Prop), (forall x, ~ hb x x) -> forall s0,
  CALOConv step (fun _ => True) hb s0 <->
  CCRon step (fun _ => True) hb s0 /\ forall a, IdemAt step (fun _ => True) hb s0 a.
Proof.
  intros S E dec step hb Hirr s0.
  assert (A : CALOConv step (fun _ => True) hb s0 <-> CALOConvS step hb eq s0).
  { split.
    - intros H d1 d2 H1 H2 Hs.
      assert (Ho : causal hb (dedup dec d1)) by exact (causal_alo_dedup_causal dec hb d1 Hirr H1).
      rewrite (H d1 (dedup dec d1) (Forall_True _) H1 Ho (fun x => dedup_In dec d1 x)).
      symmetry. apply H; [exact (Forall_True _) | exact H2 | exact Ho |].
      intros x. rewrite dedup_In. split; intros Hx; apply Hs; exact Hx.
    - intros H d o _ Hd Ho Hs. apply H; [exact Hd | apply causal_causal_alo; exact Ho |].
      intros x. symmetry. apply Hs. }
  assert (B : CCRon step (fun _ => True) hb s0 <-> CCRonS step hb eq s0).
  { split; [intros H p a b Hab Hc; exact (H p a b (Forall_True _) Hab Hc) |
             intros H p a b _ Hab Hc; exact (H p a b Hab Hc)]. }
  assert (C : forall a, IdemAt step (fun _ => True) hb s0 a <-> IdemAtS step hb eq s0 a).
  { intros a. split; [intros H u Hc; exact (H u (Forall_True _) Hc) | intros H u _ Hc; exact (H u Hc)]. }
  rewrite A, B. rewrite (causal_alo_s_exact dec step hb Hirr eq (fun s => eq_refl)
                           (fun s t H => eq_sym H) (fun s t u H1 H2 => eq_trans H1 H2)
                           (fun e s t H => f_equal (step e) H) s0).
  split; intros [H1 H2]; split; try exact H1; intros a; apply C; apply H2.
Qed.

Theorem causal_exact_recovered : forall {S E : Type} (step : E -> S -> S) (hb : E -> E -> Prop) s0,
  GovernanceConverse.CausalConv step hb s0 <-> GovernanceConverse.CCR step hb s0.
Proof.
  intros S E step hb s0.
  pose proof (causal_conv_s_exact step hb eq (fun s => eq_refl) (fun s t H => eq_sym H)
                (fun s t u H1 H2 => eq_trans H1 H2) (fun e s t H => f_equal (step e) H) s0) as H.
  unfold CConvS, CCRonS in H. unfold GovernanceConverse.CausalConv, GovernanceConverse.CCR.
  split.
  - intros C. apply H. intros o1 o2 H1 H2 HP. exact (C o1 o2 H1 H2 HP).
  - intros C o1 o2 H1 H2 HP. exact (proj2 H C o1 o2 H1 H2 HP).
Qed.

(* ============================================================================================ *)
(* 2. The distributed model under a delivery class.                                             *)
(* ============================================================================================ *)

Section DistDelivery.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable o : list nat.
  Hypothesis HC : Common V src f valid rho E reg sig o.

  Local Notation feqF := (feq V).
  Local Notation InvF := (Inv V valid).
  Local Notation aF := (applyF V f rho E reg sig o).
  Local Notation rF := (runF V f rho E reg sig o).
  Local Notation nF := (N V f rho o).
  Local Notation dF := (drun V f E reg sig).
  Local Notation okF := (okact E o).
  Local Notation evsF := (evs E).
  Local Notation DE := (DEv E).
  Local Notation DP := (DProp E).
  Local Notation XUatF := (XUat V f rho E reg sig o).

  (* ---------- a delivery class ---------- *)

  Section Class.
  Variable Adm : list E -> Prop.
  Variable Rel : list E -> list E -> Prop.
  Hypothesis adm_prefix : forall l r, Adm (l ++ r) -> Adm l.
  Hypothesis rel_refl : forall l, Adm l -> Rel l l.

  Definition XURD (s0 : nat -> V) : Prop :=
    forall p e, Forall okF p -> Adm (evsF p ++ [e]) -> XUatF (dF p s0) e.

  Definition DistConvD (s0 : nat -> V) : Prop :=
    forall w1 w2, Forall okF w1 -> Forall okF w2 -> Adm (evsF w1) -> Adm (evsF w2) ->
      Rel (evsF w1) (evsF w2) -> feqF (nF (dF w1 s0)) (nF (dF w2 s0)).

  Definition FedConvD (s : nat -> V) : Prop :=
    forall l1 l2, Adm l1 -> Adm l2 -> Rel l1 l2 -> feqF (rF l1 s) (rF l2 s).

  Lemma dd_flush_reach : forall s0, InvF s0 -> XURD s0 ->
    forall w p, Forall okF p -> Forall okF w -> Adm (evsF p ++ evsF w) ->
      feqF (nF (dF w (dF p s0))) (rF (evsF w) (nF (dF p s0))).
  Proof.
    intros s0 Hi Hx w. induction w as [| a w IH]; intros p Hp Hw Ha; [intro k; reflexivity |].
    inversion Hw as [| ? ? Hok Hw']; subst.
    assert (Hpa : Forall okF (p ++ [a])) by (apply ok_app; [exact Hp | constructor; [exact Hok | constructor]]).
    assert (Ep : dstep V f E reg sig a (dF p s0) = dF (p ++ [a]) s0) by (rewrite drun_app; reflexivity).
    assert (It : InvF (dF p s0)) by (apply (drun_inv V src f valid rho E reg sig o HC); exact Hi).
    assert (Ha' : Adm (evsF (p ++ [a]) ++ evsF w)).
    { rewrite evs_app, <- app_assoc. destruct a; exact Ha. }
    change (dF (a :: w) (dF p s0)) with (dF w (dstep V f E reg sig a (dF p s0))). rewrite Ep.
    eapply feq_trans; [exact (IH (p ++ [a]) Hpa Hw' Ha') |].
    rewrite <- Ep. destruct a as [e | j]; simpl.
    - change (rF (e :: evsF w) (nF (dF p s0))) with (rF (evsF w) (aF e (nF (dF p s0)))).
      apply (runF_ext V src f valid rho E reg sig o HC).
      apply (flush_ev_at V src f valid rho E reg sig o HC); [exact It |].
      apply Hx; [exact Hp |]. apply (adm_prefix _ (evsF w)). rewrite <- app_assoc. exact Ha.
    - apply (runF_ext V src f valid rho E reg sig o HC).
      apply (flush_prop V src f valid rho E reg sig o HC); [exact It | exact Hok].
  Qed.

  Theorem dist_flush_d : forall s0, InvF s0 -> XURD s0 ->
    forall w, Forall okF w -> Adm (evsF w) -> feqF (nF (dF w s0)) (rF (evsF w) (nF s0)).
  Proof. intros s0 Hi Hx w Hw Ha. exact (dd_flush_reach s0 Hi Hx w [] ltac:(constructor) Hw Ha). Qed.

  (* The exact condition for any delivery class. *)
  Theorem dist_delivery_exact : forall s0, InvF s0 ->
    (DistConvD s0 <-> XURD s0 /\ FedConvD (nF s0)).
  Proof.
    intros s0 Hi. split.
    - intros Hd.
      assert (Hx : XURD s0).
      { intros p e Hp Ha. unfold XUat.
        destruct (dist_xu_runs V src f valid rho E reg sig o HC s0 p e Hi) as [A B].
        assert (Ok1 : Forall okF (p ++ [DE e]))
          by (apply ok_app; [exact Hp | constructor; [exact Logic.I | constructor]]).
        assert (Ok2 : Forall okF (p ++ map DP o ++ [DE e]))
          by (apply ok_app; [exact Hp | apply ok_app; [exact (ok_props E o) | constructor; [exact Logic.I | constructor]]]).
        assert (Ev1 : evsF (p ++ [DE e]) = evsF p ++ [e]) by (rewrite evs_app; reflexivity).
        assert (Ev2 : evsF (p ++ map DP o ++ [DE e]) = evsF p ++ [e])
          by (rewrite !evs_app, evs_props; reflexivity).
        pose proof (Hd _ _ Ok1 Ok2) as H. rewrite Ev1, Ev2 in H.
        pose proof (H Ha Ha (rel_refl _ Ha) (reg e)) as H'. rewrite A, B in H'. symmetry. exact H'. }
      split; [exact Hx |].
      intros l1 l2 H1 H2 Hr.
      pose proof (dist_flush_d s0 Hi Hx (map DE l1) (ok_evs E o l1)) as A1. rewrite evs_evs in A1.
      pose proof (dist_flush_d s0 Hi Hx (map DE l2) (ok_evs E o l2)) as A2. rewrite evs_evs in A2.
      eapply feq_trans; [apply feq_sym; exact (A1 H1) |].
      eapply feq_trans; [| exact (A2 H2)].
      apply Hd; [exact (ok_evs E o l1) | exact (ok_evs E o l2) | rewrite evs_evs; exact H1
                | rewrite evs_evs; exact H2 | rewrite !evs_evs; exact Hr].
    - intros [Hx Hf] w1 w2 H1 H2 A1 A2 Hr.
      eapply feq_trans; [exact (dist_flush_d s0 Hi Hx w1 H1 A1) |].
      eapply feq_trans; [exact (Hf _ _ A1 A2 Hr) | apply feq_sym; exact (dist_flush_d s0 Hi Hx w2 H2 A2)].
  Qed.
  End Class.

  (* ---------- exactly-once, federated trace equivalence: dist_exact_tc ---------- *)

  Variable I : E -> E -> Prop.

  Theorem dist_exact_tc_recovered : forall s0, InvF s0 ->
    (DistConv V f rho E reg sig I o s0 <->
     XUR V f rho E reg sig o s0 /\ TraceConv V f rho E reg sig I o (nF s0)).
  Proof.
    intros s0 Hi.
    pose proof (dist_delivery_exact (fun _ => True) (tequiv (Ifed E reg I)) (fun _ _ _ => Logic.I)
                  (fun l _ => teq_refl _ l) s0 Hi) as H.
    assert (A : DistConv V f rho E reg sig I o s0 <-> DistConvD (fun _ => True) (tequiv (Ifed E reg I)) s0).
    { split; intros D w1 w2 H1 H2; [intros _ _; apply D; assumption | apply D; trivial]. }
    assert (B : XUR V f rho E reg sig o s0 <-> XURD (fun _ => True) s0).
    { split; intros X p e Hp; [intros _; apply X; exact Hp | apply X; trivial]. }
    assert (C : TraceConv V f rho E reg sig I o (nF s0) <-> FedConvD (fun _ => True) (tequiv (Ifed E reg I)) (nF s0)).
    { split; intros T l1 l2; [intros _ _; apply T | apply T; trivial]. }
    rewrite A, B, C. exact H.
  Qed.

  (* ---------- the instances: causal, free at-least-once, causal at-least-once ---------- *)

  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable hb : E -> E -> Prop.
  Hypothesis hb_irrefl : forall x, ~ hb x x.

  Definition SameSetE (l1 l2 : list E) : Prop := forall x, In x l1 <-> In x l2.

  Definition XURC (s0 : nat -> V) : Prop := XURD (causal hb) s0.
  Definition XURCA (s0 : nat -> V) : Prop := XURD (causal_alo hb) s0.

  Definition DistCausal (s0 : nat -> V) : Prop := DistConvD (causal hb) (@Permutation E) s0.
  Definition DistALO (s0 : nat -> V) : Prop := DistConvD (fun _ => True) SameSetE s0.
  Definition DistCALO (s0 : nat -> V) : Prop := DistConvD (causal_alo hb) SameSetE s0.

  (* The FedMachine conditions, pointwise. *)
  Definition CCRF (s : nat -> V) : Prop := CCRonS aF hb feqF s.
  Definition IdemF (s : nat -> V) (a : E) : Prop := IdemAtS aF hb feqF s a.

  Definition CommRF (s : nat -> V) : Prop :=
    forall p a b, a <> b -> NoDup (p ++ [a; b]) -> feqF (aF b (aF a (rF p s))) (aF a (aF b (rF p s))).
  Definition IdemRF (s : nat -> V) (a : E) : Prop :=
    forall u, NoDup (u ++ [a]) -> feqF (aF a (aF a (rF u s))) (aF a (rF u s)).

  Lemma dd_feq_refl : forall s, feqF s s.
  Proof. intros s k. reflexivity. Qed.

  Lemma dd_ext : forall e s t, feqF s t -> feqF (aF e s) (aF e t).
  Proof. exact (applyF_ext V src f valid rho E reg sig o HC). Qed.

  Lemma dd_run : forall l s, rF l s = runT aF l s.
  Proof. reflexivity. Qed.

  Theorem dist_causal_exact : forall s0, InvF s0 -> (DistCausal s0 <-> XURC s0 /\ CCRF (nF s0)).
  Proof.
    intros s0 Hi. unfold DistCausal, XURC, CCRF.
    rewrite (dist_delivery_exact (causal hb) (@Permutation E) (GovernanceConverse.causal_prefix hb)
               (fun l _ => Permutation_refl l) s0 Hi).
    rewrite <- (causal_conv_s_exact aF hb feqF dd_feq_refl (@feq_sym V) (@feq_trans V) dd_ext (nF s0)).
    reflexivity.
  Qed.

  Lemma dd_fedconv_alo : forall (h : E -> E -> Prop) (A : list E -> Prop) s,
    (forall l, A l <-> causal_alo h l) ->
    FedConvD A SameSetE s <-> CALOConvS aF h feqF s.
  Proof.
    intros h A s HA. split.
    - intros H d1 d2 H1 H2 Hs. apply H; [apply HA; exact H1 | apply HA; exact H2 | exact Hs].
    - intros H l1 l2 H1 H2 Hs. apply H; [apply HA; exact H1 | apply HA; exact H2 | exact Hs].
  Qed.

  Theorem dist_causal_alo_exact : forall s0, InvF s0 ->
    (DistCALO s0 <-> XURCA s0 /\ CCRF (nF s0) /\ forall a, IdemF (nF s0) a).
  Proof.
    intros s0 Hi. unfold DistCALO, XURCA, CCRF, IdemF.
    rewrite (dist_delivery_exact (causal_alo hb) SameSetE (causal_alo_app_prefix hb)
               (fun l _ x => iff_refl _) s0 Hi).
    rewrite (dd_fedconv_alo hb (causal_alo hb) (nF s0) (fun l => iff_refl _)).
    rewrite (causal_alo_s_exact dec aF hb hb_irrefl feqF dd_feq_refl (@feq_sym V) (@feq_trans V) dd_ext (nF s0)).
    reflexivity.
  Qed.

  (* The free forms: hb empty. *)
  Lemma dd_ccr_nohb : forall s, CCRonS aF (nohb (E := E)) feqF s <-> CommRF s.
  Proof.
    intros s. split.
    - intros H p a b Hab Hnd. apply H; [apply concurrent_nohb; exact Hab | apply causal_nohb; exact Hnd].
    - intros H p a b Hab Hc. apply H; [exact (proj1 Hab) | exact (proj1 Hc)].
  Qed.

  Lemma dd_idem_nohb : forall s a, IdemAtS aF (nohb (E := E)) feqF s a <-> IdemRF s a.
  Proof.
    intros s a. split.
    - intros H u Hnd. apply H. apply causal_nohb. exact Hnd.
    - intros H u Hc. apply H. exact (proj1 Hc).
  Qed.

  Theorem dist_alo_exact : forall s0, InvF s0 ->
    (DistALO s0 <-> XUR V f rho E reg sig o s0 /\ CommRF (nF s0) /\ forall a, IdemRF (nF s0) a).
  Proof.
    intros s0 Hi. unfold DistALO.
    rewrite (dist_delivery_exact (fun _ => True) SameSetE (fun _ _ _ => Logic.I)
               (fun l _ x => iff_refl _) s0 Hi).
    rewrite (dd_fedconv_alo nohb (fun _ => True) (nF s0) (fun l => conj (fun _ => causal_alo_nohb l) (fun _ => Logic.I))).
    rewrite (causal_alo_s_exact dec aF nohb nohb_irrefl feqF dd_feq_refl (@feq_sym V) (@feq_trans V) dd_ext (nF s0)).
    rewrite dd_ccr_nohb.
    assert (B : XUR V f rho E reg sig o s0 <-> XURD (fun _ => True) s0).
    { split; intros X p e Hp; [intros _; apply X; exact Hp | apply X; trivial]. }
    rewrite <- B. split; intros [X [C D]]; (split; [exact X | split; [exact C | intros a; apply dd_idem_nohb; apply D]]).
  Qed.

  (* Reachability inclusions: every class's XU is implied by dist_exact's XUR. *)
  Lemma xur_xurd : forall (A : list E -> Prop) s0, XUR V f rho E reg sig o s0 -> XURD A s0.
  Proof. intros A s0 X p e Hp _. apply X. exact Hp. Qed.

  (* gsm's static XU check (FedReport.ProjectionSafe) gives the propagation conjunct of every
     delivery class, from every valid start. *)
  Theorem xu_xurd : XU V f valid E reg sig -> forall (A : list E -> Prop) s0, InvF s0 -> XURD A s0.
  Proof.
    intros X A s0 Hi p e Hp _. unfold XUat.
    assert (It : InvF (dF p s0)) by (apply (drun_inv V src f valid rho E reg sig o HC); exact Hi).
    apply X; [apply (N_inv V src f valid rho E reg sig o HC); exact It | apply It].
  Qed.
End DistDelivery.

(* ============================================================================================ *)
(* 3. Instances. V = nat * nat (shared, local); registry 1's shared part copies registry 0's.   *)
(* ============================================================================================ *)

Definition dc_f (j : nat) (z : nat -> nat * nat) (x : nat * nat) : nat * nat :=
  if Nat.eqb j 1 then (fst (z 0), snd x) else x.
Definition dc_valid (_ : nat) (_ : nat * nat) : Prop := True.
Definition dc_rho (_ : nat) (x : nat * nat) : nat * nat := x.

Lemma dc_common : forall (E : Type) (reg : E -> nat) (sig : E -> nat * nat -> nat * nat),
  (forall e, reg e = 0 \/ reg e = 1) -> Common (nat * nat) src2 dc_f dc_valid dc_rho E reg sig [0; 1].
Proof.
  intros E reg sig Hreg. constructor.
  - intros [| [| j]] z1 z2 x H; unfold dc_f; simpl; try reflexivity.
    rewrite (H 0 (or_introl eq_refl)). reflexivity.
  - exact topo2.
  - intros; exact Logic.I.
  - intros [| [| j]] z z' x _ _ _; reflexivity.
  - intros; reflexivity.
  - intros; exact Logic.I.
  - intros e. destruct (Hreg e) as [-> | ->]; [left | right; left]; reflexivity.
Qed.

Lemma dc_inv : forall t, Inv (nat * nat) dc_valid t.
Proof. intros t k. exact Logic.I. Qed.

Definition dc_zero (_ : nat) : nat * nat := (0, 0).

(* ----- T happens before R ----- *)

Inductive tev : Type := TRead | RSet.
Definition tev_eq : forall x y : tev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition tr_reg (e : tev) : nat := match e with TRead => 1 | RSet => 0 end.
Definition tr_sig (e : tev) (x : nat * nat) : nat * nat :=
  match e with TRead => (fst x, snd x + fst x) | RSet => (1, snd x) end.
Definition tr_hb (a b : tev) : Prop := a = TRead /\ b = RSet.

Lemma tr_irrefl : forall x, ~ tr_hb x x.
Proof. intros x [-> H]. discriminate H. Qed.

Lemma tr_common : Common (nat * nat) src2 dc_f dc_valid dc_rho tev tr_reg tr_sig [0; 1].
Proof. apply dc_common. intros [|]; [right | left]; reflexivity. Qed.

Local Notation TRd := (drun (nat * nat) dc_f tev tr_reg tr_sig).
Local Notation TRa := (applyF (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1]).
Local Notation TRx := (XUat (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1]).

Lemma tr_xu_R : forall t, TRx t RSet.
Proof. intros t. reflexivity. Qed.

Lemma tr_xu_T : forall t, fst (t 1) = fst (t 0) -> TRx t TRead.
Proof. intros t H. unfold XUat. simpl. rewrite H. reflexivity. Qed.

(* Without RSet the target's shared part stays the source's. *)
Lemma tr_inv : forall p t, Forall (okact tev [0; 1]) p -> ~ In RSet (evs tev p) ->
  fst (t 1) = fst (t 0) -> fst (TRd p t 1) = fst (TRd p t 0).
Proof.
  induction p as [| a p IH]; intros t Hok Hn Ht; [exact Ht |].
  inversion Hok as [| ? ? Ha Hok']; subst. simpl. destruct a as [[|] | j].
  - apply IH; [exact Hok' | intro H; apply Hn; right; exact H | exact Ht].
  - exfalso. apply Hn. left. reflexivity.
  - apply IH; [exact Hok' | exact Hn |]. simpl in Ha.
    destruct Ha as [<- | [<- | []]]; [exact Ht | reflexivity].
Qed.

Lemma tr_no_R : forall l, causal_alo tr_hb (l ++ [TRead]) -> ~ In RSet l.
Proof. intros l H HR. exact (H TRead RSet (conj eq_refl eq_refl) l [TRead] eq_refl HR (or_introl eq_refl)). Qed.

Lemma tr_xurca : XURCA (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero.
Proof.
  intros p [|] Hp Hc; [| apply tr_xu_R].
  apply tr_xu_T. apply tr_inv; [exact Hp | apply tr_no_R; exact Hc | reflexivity].
Qed.

Lemma tr_xurc : XURC (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero.
Proof.
  intros p e Hp Hc. apply tr_xurca; [exact Hp |]. apply causal_causal_alo. exact Hc.
Qed.

Lemma tr_ccrf : forall s, CCRF (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb s.
Proof.
  intros s p a b [Hne [H1 H2]] _. exfalso.
  destruct a, b; try (apply Hne; reflexivity); [apply H1 | apply H2]; split; reflexivity.
Qed.

Lemma tr_idemf : forall a, IdemF (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb
                             (N (nat * nat) dc_f dc_rho [0; 1] dc_zero) a.
Proof.
  intros [|] u Hc.
  - assert (Hu : u = []).
    { destruct u as [| x u]; [reflexivity | exfalso].
      destruct x.
      + pose proof (proj1 Hc) as Hnd. simpl in Hnd. apply NoDup_cons_iff in Hnd. apply (proj1 Hnd).
        apply in_or_app. right. left. reflexivity.
      + exact (tr_no_R (RSet :: u) (causal_causal_alo _ _ Hc) (or_introl eq_refl)). }
    subst u. intros [| [| k]]; reflexivity.
  - intros [| [| k]]; reflexivity.
Qed.

Theorem tr_causal_instance :
  XURC (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero /\
  XURCA (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero /\
  CCRF (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb (N (nat * nat) dc_f dc_rho [0; 1] dc_zero) /\
  DistCausal (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero /\
  DistCALO (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] tr_hb dc_zero /\
  ~ XUR (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] dc_zero /\
  ~ DistConv (nat * nat) dc_f dc_rho tev tr_reg tr_sig (fun _ _ => True) [0; 1] dc_zero /\
  ~ DistALO (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] dc_zero.
Proof.
  assert (Hx : ~ XUR (nat * nat) dc_f dc_rho tev tr_reg tr_sig [0; 1] dc_zero).
  { intro H. pose proof (H [DEv tev RSet] TRead ltac:(repeat constructor)) as X.
    unfold XUat in X. simpl in X. discriminate X. }
  split; [exact tr_xurc |]. split; [exact tr_xurca |]. split; [apply tr_ccrf |].
  split.
  { apply (dist_causal_exact (nat * nat) src2 dc_f dc_valid dc_rho tev tr_reg tr_sig [0; 1] tr_common
             tr_hb dc_zero (dc_inv _)). split; [exact tr_xurc | apply tr_ccrf]. }
  split.
  { apply (dist_causal_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho tev tr_reg tr_sig [0; 1] tr_common
             tev_eq tr_hb tr_irrefl dc_zero (dc_inv _)).
    split; [exact tr_xurca | split; [apply tr_ccrf | apply tr_idemf]]. }
  split; [exact Hx |]. split.
  - intro D. apply Hx.
    exact (proj1 (proj1 (dist_exact (nat * nat) src2 dc_f dc_valid dc_rho tev tr_reg tr_sig (fun _ _ => True)
                           [0; 1] tr_common dc_zero (dc_inv _)) D)).
  - intro D. apply Hx.
    exact (proj1 (proj1 (dist_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho tev tr_reg tr_sig [0; 1] tr_common
                           tev_eq dc_zero (dc_inv _)) D)).
Qed.

(* ----- the propagation conjunct is needed: Snap at a stale start ----- *)

Inductive snev : Type := Snap.
Definition snev_eq : forall x y : snev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition sn_reg (_ : snev) : nat := 1.
Definition sn_sig (_ : snev) (x : nat * nat) : nat * nat := (fst x, fst x).
Definition sn_s0 (k : nat) : nat * nat := if Nat.eqb k 0 then (1, 0) else (0, 0).

Lemma sn_common : Common (nat * nat) src2 dc_f dc_valid dc_rho snev sn_reg sn_sig [0; 1].
Proof. apply dc_common. intros e. right. reflexivity. Qed.

Local Notation SNa := (applyF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1]).
Local Notation SNr := (runF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1]).
Local Notation SNn := (N (nat * nat) dc_f dc_rho [0; 1]).

Lemma sn_cons : forall u t, fst (SNr u (SNn t) 1) = fst (SNr u (SNn t) 0).
Proof.
  induction u as [| e u IH]; intros t; [reflexivity |].
  change (SNr (e :: u) (SNn t)) with (SNr u (SNa e (SNn t))). apply IH.
Qed.

Lemma sn_idem : forall t, fst (t 1) = fst (t 0) -> feq (nat * nat) (SNa Snap (SNa Snap t)) (SNa Snap t).
Proof.
  intros t H [| [| k]]; try reflexivity.
  unfold sn_reg, sn_sig. cbn. destruct (t 0) as [a0 b0], (t 1) as [a1 b1]. simpl in H. subst a1.
  reflexivity.
Qed.

Theorem snap_xu_needed :
  CCRF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb (SNn sn_s0) /\
  CommRF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] (SNn sn_s0) /\
  (forall a, IdemRF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] (SNn sn_s0) a) /\
  (forall a, IdemF (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb (SNn sn_s0) a) /\
  ~ XURC (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb sn_s0 /\
  ~ DistCausal (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb sn_s0 /\
  ~ DistALO (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] sn_s0 /\
  ~ DistCALO (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb sn_s0.
Proof.
  assert (Hx0 : ~ XUat (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] sn_s0 Snap)
    by (unfold XUat; simpl; discriminate).
  assert (Hxc : ~ XURC (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb sn_s0).
  { intro H. apply Hx0. apply (H [] Snap); [constructor |]. apply causal_nohb. repeat constructor. simpl; tauto. }
  assert (Hxa : ~ XURCA (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] nohb sn_s0).
  { intro H. apply Hx0. apply (H [] Snap); [constructor | apply causal_alo_nohb]. }
  assert (Hxr : ~ XUR (nat * nat) dc_f dc_rho snev sn_reg sn_sig [0; 1] sn_s0).
  { intro H. apply Hx0. apply (H [] Snap). constructor. }
  split; [intros p [] [] [Hne _]; exfalso; apply Hne; reflexivity |].
  split; [intros p [] [] Hne; exfalso; apply Hne; reflexivity |].
  split; [intros [] u _; apply sn_idem; apply sn_cons |].
  split; [intros [] u _; apply sn_idem; apply sn_cons |].
  split; [exact Hxc |].
  split.
  { intro D. apply Hxc.
    exact (proj1 (proj1 (dist_causal_exact (nat * nat) src2 dc_f dc_valid dc_rho snev sn_reg sn_sig [0; 1]
                           sn_common nohb sn_s0 (dc_inv _)) D)). }
  split.
  { intro D. apply Hxr.
    exact (proj1 (proj1 (dist_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho snev sn_reg sn_sig [0; 1]
                           sn_common snev_eq sn_s0 (dc_inv _)) D)). }
  intro D. apply Hxa.
  exact (proj1 (proj1 (dist_causal_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho snev sn_reg sn_sig [0; 1]
                         sn_common snev_eq nohb nohb_irrefl sn_s0 (dc_inv _)) D)).
Qed.

(* ----- the commutation clause is needed: two overwrites of registry 0 ----- *)

Inductive stev : Type := Set1 | Set2.
Definition stev_eq : forall x y : stev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition st_reg (_ : stev) : nat := 0.
Definition st_sig (e : stev) (x : nat * nat) : nat * nat :=
  match e with Set1 => (1, snd x) | Set2 => (2, snd x) end.

Lemma st_common : Common (nat * nat) src2 dc_f dc_valid dc_rho stev st_reg st_sig [0; 1].
Proof. apply dc_common. intros e. left. reflexivity. Qed.

Local Notation STa := (applyF (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1]).

Theorem set_comm_needed : forall s0,
  XUR (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] s0 /\
  (forall a t, feq (nat * nat) (STa a (STa a t)) (STa a t)) /\
  ~ CommRF (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) /\
  ~ CCRF (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] nohb (N (nat * nat) dc_f dc_rho [0; 1] s0) /\
  ~ DistCausal (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] nohb s0 /\
  ~ DistALO (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] s0 /\
  ~ DistCALO (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] nohb s0.
Proof.
  intros s0.
  assert (Hc : ~ CommRF (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0)).
  { intro H. pose proof (H [] Set1 Set2 ltac:(discriminate)
                           ltac:(repeat constructor; simpl; intuition discriminate) 0) as E.
    simpl in E. discriminate E. }
  assert (Hcc : ~ CCRF (nat * nat) dc_f dc_rho stev st_reg st_sig [0; 1] nohb (N (nat * nat) dc_f dc_rho [0; 1] s0)).
  { intro H. apply Hc. intros p a b Hab Hnd. apply H; [split; [exact Hab | split; intros []] |].
    apply causal_nohb. exact Hnd. }
  split; [intros p e _; reflexivity |].
  split; [intros [|] t [| [| k]]; reflexivity |].
  split; [exact Hc |]. split; [exact Hcc |].
  split.
  { intro D. apply Hcc.
    exact (proj2 (proj1 (dist_causal_exact (nat * nat) src2 dc_f dc_valid dc_rho stev st_reg st_sig [0; 1]
                           st_common nohb s0 (dc_inv _)) D)). }
  split.
  { intro D. apply Hc.
    exact (proj1 (proj2 (proj1 (dist_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho stev st_reg st_sig [0; 1]
                                  st_common stev_eq s0 (dc_inv _)) D))). }
  intro D. apply Hcc.
  exact (proj1 (proj2 (proj1 (dist_causal_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho stev st_reg st_sig
                                [0; 1] st_common stev_eq nohb nohb_irrefl s0 (dc_inv _)) D))).
Qed.

(* ----- the idempotence clause is needed: an increment of registry 0 ----- *)

Inductive inev : Type := Incr.
Definition inev_eq : forall x y : inev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition in_reg (_ : inev) : nat := 0.
Definition in_sig (_ : inev) (x : nat * nat) : nat * nat := (S (fst x), snd x).

Lemma in_common : Common (nat * nat) src2 dc_f dc_valid dc_rho inev in_reg in_sig [0; 1].
Proof. apply dc_common. intros e. left. reflexivity. Qed.

Lemma in_repeat : forall l : list inev, l = repeat Incr (length l).
Proof. induction l as [| [] l IH]; [reflexivity | simpl; rewrite <- IH; reflexivity]. Qed.

Theorem inc_idem_needed : forall s0,
  DistConv (nat * nat) dc_f dc_rho inev in_reg in_sig (fun _ _ => True) [0; 1] s0 /\
  XUR (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] s0 /\
  CommRF (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) /\
  ~ IdemRF (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) Incr /\
  ~ DistALO (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] s0.
Proof.
  intros s0.
  assert (Hx : XUR (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] s0) by (intros p e _; reflexivity).
  assert (Hi : ~ IdemRF (nat * nat) dc_f dc_rho inev in_reg in_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) Incr).
  { intro H. pose proof (H [] ltac:(repeat constructor; simpl; tauto) 0) as E. simpl in E.
    injection E as E. lia. }
  split.
  { apply (dist_exact_tc (nat * nat) src2 dc_f dc_valid dc_rho inev in_reg in_sig (fun _ _ => True) [0; 1]
             in_common s0 (dc_inv _)).
    split; [exact Hx |]. intros l1 l2 Ht k.
    rewrite (in_repeat l1), (in_repeat l2), (Permutation_length (tequiv_perm _ _ _ Ht)). reflexivity. }
  split; [exact Hx |].
  split; [intros p [] [] Hne; exfalso; apply Hne; reflexivity |].
  split; [exact Hi |].
  intro D. apply Hi.
  exact (proj2 (proj2 (proj1 (dist_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho inev in_reg in_sig [0; 1]
                                in_common inev_eq s0 (dc_inv _)) D)) Incr).
Qed.

(* ----- non-vacuity: a max-register on registry 0 and a mark on registry 1 ----- *)

Inductive mkev : Type := Max (k : nat) | Mark.
Definition mkev_eq : forall x y : mkev, {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Defined.
Definition mk_reg (e : mkev) : nat := match e with Max _ => 0 | Mark => 1 end.
Definition mk_sig (e : mkev) (x : nat * nat) : nat * nat :=
  match e with Max k => (Nat.max k (fst x), snd x) | Mark => (fst x, 1) end.

Lemma mk_common : Common (nat * nat) src2 dc_f dc_valid dc_rho mkev mk_reg mk_sig [0; 1].
Proof. apply dc_common. intros [k |]; [left | right]; reflexivity. Qed.

Local Notation MKa := (applyF (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1]).

Theorem mk_alo_holds : forall s0,
  XUR (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] s0 /\
  CommRF (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) /\
  (forall a, IdemRF (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) a) /\
  DistALO (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] s0 /\
  DistCausal (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] nohb s0 /\
  DistCALO (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] nohb s0.
Proof.
  intros s0.
  assert (Hx : XUR (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] s0)
    by (intros p [k |] _; reflexivity).
  assert (Hc : forall a b t, feq (nat * nat) (MKa b (MKa a t)) (MKa a (MKa b t))).
  { intros [j |] [k |] t [| [| m]]; unfold mk_reg, mk_sig; cbn; try reflexivity;
    destruct (t 0) as [x0 y0]; cbn; f_equal; lia. }
  assert (Hd : forall a t, feq (nat * nat) (MKa a (MKa a t)) (MKa a t)).
  { intros [j |] t [| [| m]]; unfold mk_reg, mk_sig; cbn; try reflexivity;
    destruct (t 0) as [x0 y0]; cbn; f_equal; lia. }
  assert (HC : CommRF (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0))
    by (intros p a b _ _; apply Hc).
  assert (HI : forall a, IdemRF (nat * nat) dc_f dc_rho mkev mk_reg mk_sig [0; 1] (N (nat * nat) dc_f dc_rho [0; 1] s0) a)
    by (intros a u _; apply Hd).
  split; [exact Hx |]. split; [exact HC |]. split; [exact HI |].
  split.
  { apply (dist_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho mkev mk_reg mk_sig [0; 1] mk_common mkev_eq s0
             (dc_inv _)). split; [exact Hx | split; [exact HC | exact HI]]. }
  split.
  { apply (dist_causal_exact (nat * nat) src2 dc_f dc_valid dc_rho mkev mk_reg mk_sig [0; 1] mk_common nohb s0
             (dc_inv _)). split; [apply xur_xurd; exact Hx | intros p a b _ _; apply Hc]. }
  apply (dist_causal_alo_exact (nat * nat) src2 dc_f dc_valid dc_rho mkev mk_reg mk_sig [0; 1] mk_common mkev_eq
           nohb nohb_irrefl s0 (dc_inv _)).
  split; [apply xur_xurd; exact Hx | split; [intros p a b _ _; apply Hc | intros a u _; apply Hd]].
Qed.
