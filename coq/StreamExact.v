(* StreamExact.v: the exact (necessary and sufficient) condition for stream agreement. Axiom-free.

   Stream.v proves that finished processors with equal received sets agree (stream_agreement,
   stream_convergence, base_cor_quiescent) from SUFFICIENT conditions: WFC, CC1 on co-enabled pairs
   and CC2 at every state. GovernanceConverse.v proves the rewrite-system iffs (jc_exact: confluence
   from c0 iff JC c0; cc_exact_from: under free delivery, unique normal forms from s0 iff CC1 and CC2
   on the states reachable from s0). This file lifts the exact condition to stream processors.

   Stream agreement from s0 (StreamAgree s0): for every stream, every two processors from s0
   (is_processor), every two times at which they are settled with the same received SET have the
   same state psi.

   The processor discipline prstep (Stream.v) compensates before it applies: an event is applied
   only from a valid state. So the rewrite-system conditions are too strong at stream level, and
   the exact condition is the joinability condition of prstep itself.

   - PJC c0 (processor joinability): at every configuration reachable from c0 by prstep, with a
     valid state, the successors of every two distinct enabled buffered events are prstep-joinable.
     There is no compensation critical pair: prstep is deterministic at invalid states.
   - pjc_exact: CR prstep c0 <-> PJC c0 (any enabledness, any well-founded potential).
   - stream_agree_set_function (no qualifier): StreamAgree s0 <-> for every duplicate-free E, all
     finished reductions from (s0, E) end in the same state.
   - pjc_stream_agreement (no qualifier): (forall E, NoDup E -> PJC (s0, E)) -> StreamAgree s0.
   - stream_exact (headline, qualifier Progress: at a valid state every non-empty buffer has an
     enabled event, the causal closure of received sets, as in Stream.settled_empty_buffer):
     StreamAgree s0 <-> forall E, NoDup E -> PJC (s0, E).
   - stream_diverge: the "only if" direction made concrete. A PJC failure at a configuration
     reachable from (s0, E) gives two processors that both receive E, both settle, and disagree.
   - cc_pjc, stream_agreement_recovered: under Stream.v's hypotheses PJC holds everywhere, so
     Stream.stream_agreement is a corollary of the exact theorem.
   - jc_stream_agreement: the rewrite-system condition of jc_exact (GovernanceConverse.JC) at every
     (s0, E) is sufficient for stream agreement.

   Free delivery (every buffered event is enabled; canonical repair rho_star, valid and reached by
   compensation). Write gov e s = rho_star (apply e s) and grun s w for the governed run of w.
   - PCC s0: for every duplicate-free word w ++ [e1; e2], the governed steps of e1 and e2 commute at
     grun (rho_star s0) w. This is CC1 at the states the processor can reach; CC2 does not appear.
   - stream_exact_free: StreamAgree s0 <-> PCC s0.
   - stream_diverge_free: a PCC failure gives two processors that receive w ++ [e1; e2], settle, and
     disagree.

   Counterexamples (the natural iff with the rewrite-system condition is false).
   - jc_not_necessary: a registry where CC2 fails at s0 itself, so JC (s0, [e]) fails and
     cc_exact_from's condition fails, yet every two processors from s0 agree: a processor never
     applies an event at an invalid state.
   - progress_needed: without Progress, PJC is not necessary. Two events that each enable only while
     the other is buffered: the finished buffers differ, the finished states agree.
   - jc_fail_disagree: a free registry whose governed steps do not commute; JC and PCC fail and two
     concrete processors with the same received set settle in different states.

   Non-vacuity: zw_stream_exact (the Z withdrawal registry of GovernanceWF.v and Stream.v satisfies
   Progress, PJC at every configuration and PCC from every start; the agreement of Stream.v's zp1 and
   zp2 at time 2 is rederived through stream_exact_free), and the three counterexample registries,
   which discharge every hypothesis of the sections they instantiate. *)

Require Import NC.Newman NC.GovernanceCausal NC.GovernanceWF NC.Stream.
Require NC.Governance NC.GovernanceConverse.
From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
From Coq Require Import ZArith ZArith.Zwf.
Import ListNotations.

(* ===================== The exact condition for any enabledness ===================== *)

Section StreamExact.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply   : Event -> State -> State.
  Variable rho     : State -> State.
  Variable valid   : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.

  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).

  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm : forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  Local Notation pstep := (prstep event_eq_dec apply rho valid enabled).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).
  Local Notation proc := (is_processor event_eq_dec apply rho valid enabled).
  Local Notation done := (settled event_eq_dec apply rho valid enabled).

  (* ---------- the condition ---------- *)

  Definition PJC (c0 : State * list Event) : Prop :=
    forall sigma B, star pstep c0 (sigma, B) -> valid sigma ->
      forall e1 e2, In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
        joinable pstep (apply e1 sigma, rm e1 B) (apply e2 sigma, rm e2 B).

  Definition StreamAgree (s0 : State) : Prop :=
    forall (Str : Event -> Prop) p1 p2 t1 t2,
      proc Str s0 p1 -> proc Str s0 p2 -> done p1 t1 -> done p2 t2 ->
      (forall e, In e (recv p1 t1) <-> In e (recv p2 t2)) ->
      psi p1 t1 = psi p2 t2.

  (* The causal closure of received sets: at a valid state a non-empty buffer has an enabled event. *)
  Definition Progress : Prop :=
    forall s B, valid s -> B <> [] -> exists e, In e B /\ enabled e s B.

  (* ---------- the buffer is a set ---------- *)

  Lemma sx_pstep_perm :
    forall s B s' B' C, pstep (s, B) (s', B') -> Permutation B C ->
      exists C', pstep (s, C) (s', C') /\ Permutation B' C'.
  Proof.
    intros s B s' B' C H HP.
    inversion H as [s1 B1 e Hv Hin Hen E1 E2 | s1 B1 Hinv E1 E2]; subst.
    - exists (rm e C). split.
      + apply ps_apply; [exact Hv | exact (Permutation_in e HP Hin) | exact (enabled_perm e s B C HP Hen)].
      + apply st_rm_perm. exact HP.
    - exists C. split; [apply ps_comp; exact Hinv | exact HP].
  Qed.

  Lemma sx_star_pstep_perm :
    forall c c', star pstep c c' -> forall C, Permutation (snd c) C ->
      exists C', star pstep (fst c, C) (fst c', C') /\ Permutation (snd c') C'.
  Proof.
    intros c c' H. induction H as [c | c d c' Hcd _ IH]; intros C HP.
    - exists C. split; [apply star_refl | exact HP].
    - destruct c as [s B], d as [s1 B1]. simpl in HP.
      destruct (sx_pstep_perm s B s1 B1 C Hcd HP) as [C1 [H1 HP1]].
      destruct (IH C1 HP1) as [C' [H2 HP2]]. simpl in H2.
      exists C'. split; [eapply star_step; [exact H1 | exact H2] | exact HP2].
  Qed.

  Lemma sx_nf_pstep_perm :
    forall s B C, normal_form pstep (s, B) -> Permutation B C -> normal_form pstep (s, C).
  Proof.
    intros s B C Hnf HP [[s' C'] H]. apply Hnf.
    destruct (sx_pstep_perm s C s' C' B H (Permutation_sym HP)) as [B' [HB _]].
    exists (s', B'). exact HB.
  Qed.

  (* ---------- processors that hold a fixed set ---------- *)

  Definition const_proc (E : list Event) (n : State * list Event) : processor :=
    mkProc (fun _ => E) (fun _ => n).

  Lemma sx_const_proc_is :
    forall s0 E n, NoDup E -> star pstep (s0, E) n -> proc (fun e => In e E) s0 (const_proc E n).
  Proof.
    intros s0 E n Hnd Hs. split; [intros t; exact Hnd |].
    split; [intros t e H; exact H |].
    split; [intros t; exists []; simpl; rewrite app_nil_r; reflexivity |].
    split; [intros e He; exists 0; intros t _; exact He |].
    intros t. exact Hs.
  Qed.

  (* ---------- unique normal forms give confluence (termination, decidable next move) ---------- *)

  Lemma sx_un_cr :
    forall c0, (forall n1 n2, star pstep c0 n1 -> normal_form pstep n1 ->
                              star pstep c0 n2 -> normal_form pstep n2 -> n1 = n2) ->
               CR pstep c0.
  Proof.
    intros c0 H y z Sy Sz.
    destruct (st_pnf_exists event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec
                enabled_dec y) as [ny [Hy Ny]].
    destruct (st_pnf_exists event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec
                enabled_dec z) as [nz [Hz Nz]].
    assert (E : ny = nz).
    { apply H.
      - exact (star_trans _ _ _ _ Sy Hy).
      - exact Ny.
      - exact (star_trans _ _ _ _ Sz Hz).
      - exact Nz. }
    subst nz. exists ny. split; assumption.
  Qed.

  (* ---------- PJC is exact for confluence of the processor discipline ---------- *)

  Theorem pjc_exact : forall c0, CR pstep c0 <-> PJC c0.
  Proof.
    intros c0. split.
    - intros H sigma B Hr Hv e1 e2 Hin1 Hin2 Hen1 Hen2 _. apply H.
      + eapply star_trans; [exact Hr |]. apply star_one. apply ps_apply; assumption.
      + eapply star_trans; [exact Hr |]. apply star_one. apply ps_apply; assumption.
    - intros HJ. apply (GovernanceConverse.newman_on pstep (fun c => star pstep c0 c)).
      + intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
      + intros [sigma B] X1 X2 Hr H1 H2.
        inversion H1 as [s1 B1 e1 Hv1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst.
        * inversion H2 as [s2 B2 e2 Hv2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- destruct (event_eq_dec e1 e2) as [-> | Hne].
             ++ exists (apply e2 sigma, rm e2 B). split; apply star_refl.
             ++ exact (HJ sigma B Hr Hv1 e1 e2 Hin1 Hin2 Hen1 Hen2 Hne).
          -- contradiction.
        * inversion H2 as [s2 B2 e2 Hv2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- contradiction.
          -- exists (rho sigma, B). split; apply star_refl.
      + intros x _. exact (st_SN_prstep event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf x).
      + apply star_refl.
  Qed.

  (* ---------- agreement is a property of the finished states from each set ---------- *)

  Definition FinalUnique (s0 : State) : Prop :=
    forall E, NoDup E -> forall n1 n2,
      star pstep (s0, E) n1 -> normal_form pstep n1 ->
      star pstep (s0, E) n2 -> normal_form pstep n2 -> fst n1 = fst n2.

  Theorem stream_agree_set_function : forall s0, StreamAgree s0 <-> FinalUnique s0.
  Proof.
    intros s0. split.
    - intros H E Hnd n1 n2 S1 N1 S2 N2.
      exact (H (fun e => In e E) (const_proc E n1) (const_proc E n2) 0 0
               (sx_const_proc_is s0 E n1 Hnd S1) (sx_const_proc_is s0 E n2 Hnd S2) N1 N2
               (fun e => iff_refl _)).
    - intros H Str p1 p2 t1 t2 [Nd1 [_ [_ [_ C1]]]] [Nd2 [_ [_ [_ C2]]]] D1 D2 Hset.
      assert (HP : Permutation (recv p2 t2) (recv p1 t1))
        by (apply NoDup_Permutation; [exact (Nd2 t2) | exact (Nd1 t1) | intros e; symmetry; apply Hset]).
      destruct (sx_star_pstep_perm _ _ (C2 t2) (recv p1 t1) HP) as [C [S2 HC]]. simpl in S2.
      unfold psi. destruct (conf p2 t2) as [s2 B2] eqn:Ec. simpl in *.
      assert (N2 : normal_form pstep (s2, C)).
      { apply (sx_nf_pstep_perm s2 B2 C); [| exact HC]. unfold settled in D2. rewrite Ec in D2. exact D2. }
      exact (H (recv p1 t1) (Nd1 t1) (conf p1 t1) (s2, C) (C1 t1) D1 S2 N2).
  Qed.

  (* Sufficiency, with no qualifier. *)
  Theorem pjc_stream_agreement :
    forall s0, (forall E, NoDup E -> PJC (s0, E)) -> StreamAgree s0.
  Proof.
    intros s0 H. apply stream_agree_set_function.
    intros E Hnd n1 n2 S1 N1 S2 N2.
    pose proof (proj2 (pjc_exact (s0, E)) (H E Hnd)) as Hcr.
    rewrite (GovernanceConverse.CR_UN pstep (s0, E) Hcr n1 n2 S1 N1 S2 N2). reflexivity.
  Qed.

  Lemma sx_nf_empty_progress : Progress -> forall n, normal_form pstep n -> snd n = [].
  Proof.
    intros Hp [s B] Hnf. simpl. destruct B as [| x B]; [reflexivity | exfalso].
    pose proof (st_nf_valid event_eq_dec apply rho valid enabled valid_dec (s, x :: B) Hnf) as Hv.
    simpl in Hv. destruct (Hp s (x :: B) Hv ltac:(discriminate)) as [e [Hin Hen]].
    apply Hnf. exists (apply e s, rm e (x :: B)). apply ps_apply; assumption.
  Qed.

  (* The exact theorem: under Progress, stream agreement from s0 iff PJC at every (s0, E). *)
  Theorem stream_exact :
    Progress -> forall s0, StreamAgree s0 <-> (forall E, NoDup E -> PJC (s0, E)).
  Proof.
    intros Hp s0. split; [| apply pjc_stream_agreement].
    intros H E Hnd. apply pjc_exact. apply sx_un_cr.
    intros [s1 B1] [s2 B2] S1 N1 S2 N2.
    pose proof (proj1 (stream_agree_set_function s0) H E Hnd _ _ S1 N1 S2 N2) as Es. simpl in Es.
    pose proof (sx_nf_empty_progress Hp _ N1) as E1. pose proof (sx_nf_empty_progress Hp _ N2) as E2.
    simpl in E1, E2. subst. reflexivity.
  Qed.

  (* The converse made concrete: a PJC failure gives two disagreeing processors on the same set. *)
  Theorem stream_diverge :
    Progress -> forall s0 E sigma B e1 e2,
      NoDup E -> star pstep (s0, E) (sigma, B) -> valid sigma ->
      In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      ~ joinable pstep (apply e1 sigma, rm e1 B) (apply e2 sigma, rm e2 B) ->
      exists p1 p2,
        proc (fun e => In e E) s0 p1 /\ proc (fun e => In e E) s0 p2 /\
        done p1 0 /\ done p2 0 /\ recv p1 0 = E /\ recv p2 0 = E /\ psi p1 0 <> psi p2 0.
  Proof.
    intros Hp s0 E sigma B e1 e2 Hnd Hr Hv Hin1 Hin2 Hen1 Hen2 Hne Hnj.
    destruct (st_pnf_exists event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec
                enabled_dec (apply e1 sigma, rm e1 B)) as [n1 [S1 N1]].
    destruct (st_pnf_exists event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec
                enabled_dec (apply e2 sigma, rm e2 B)) as [n2 [S2 N2]].
    assert (R1 : star pstep (s0, E) n1).
    { eapply star_trans; [exact Hr |]. eapply star_step; [exact (ps_apply event_eq_dec apply rho valid enabled sigma B e1 Hv Hin1 Hen1) | exact S1]. }
    assert (R2 : star pstep (s0, E) n2).
    { eapply star_trans; [exact Hr |]. eapply star_step; [exact (ps_apply event_eq_dec apply rho valid enabled sigma B e2 Hv Hin2 Hen2) | exact S2]. }
    exists (const_proc E n1), (const_proc E n2).
    split; [exact (sx_const_proc_is s0 E n1 Hnd R1) |].
    split; [exact (sx_const_proc_is s0 E n2 Hnd R2) |].
    split; [exact N1 |]. split; [exact N2 |]. split; [reflexivity |]. split; [reflexivity |].
    unfold psi. simpl. intro Es. apply Hnj. exists n1. split; [exact S1 |].
    replace n1 with n2; [exact S2 |].
    destruct n1 as [x1 b1], n2 as [x2 b2]. simpl in Es.
    pose proof (sx_nf_empty_progress Hp _ N1) as E1. pose proof (sx_nf_empty_progress Hp _ N2) as E2.
    simpl in E1, E2. subst. reflexivity.
  Qed.

  (* ---------- Stream.v's sufficient conditions imply PJC: stream_agreement recovered ---------- *)

  Variable rho_star : State -> State.
  Local Notation cstep := (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Hypothesis rho_star_reach : forall sigma B, star cstep (sigma, B) (rho_star sigma, B).
  Hypothesis cc1_coenabled : forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma))).
  Hypothesis cc2 : forall sigma e,
      ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma)).
  Hypothesis enabled_after_remove :
    forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (rm e1 B) /\ enabled e2 (rho_star (apply e1 sigma)) (rm e1 B).
  Hypothesis enabled_after_comp :
    forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  Theorem cc_pjc : forall c, PJC c.
  Proof.
    intros c. apply pjc_exact. apply sx_un_cr. intros n1 n2 S1 N1 S2 N2.
    apply (st_cstep_unique_nf event_eq_dec apply rho rho_star valid enabled P ltP wf_ltP Phi wfc_wf
             rho_star_reach cc1_coenabled cc2 enabled_after_remove enabled_after_comp c).
    - exact (star_prstep_cstep event_eq_dec apply rho valid enabled _ _ S1).
    - exact (nf_prstep_cstep event_eq_dec apply rho valid enabled valid_dec _ N1).
    - exact (star_prstep_cstep event_eq_dec apply rho valid enabled _ _ S2).
    - exact (nf_prstep_cstep event_eq_dec apply rho valid enabled valid_dec _ N2).
  Qed.

  (* Stream.stream_agreement, as a corollary of the exact theorem (sufficiency half). *)
  Corollary stream_agreement_recovered : forall s0, StreamAgree s0.
  Proof. intros s0. apply pjc_stream_agreement. intros E _. apply cc_pjc. Qed.
End StreamExact.

(* ===================== The rewrite-system condition JC is sufficient ===================== *)

(* GovernanceConverse.jc_exact is stated for Governance.step; the stream model runs on
   GovernanceCausal.step. The two systems have the same rules, so a JC configuration of the former
   is a PJC configuration of the processor discipline. *)

Lemma sx_remove1_eq : forall {Event : Type} (dec : forall a b : Event, {a = b} + {a <> b}) e l,
    Governance.remove1 dec e l = GovernanceCausal.remove1 dec e l.
Proof.
  intros Event dec e l. induction l as [| x l IH]; simpl; [reflexivity |].
  destruct (dec x e); [reflexivity | rewrite IH; reflexivity].
Qed.

Section JCSufficient.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.
  Variable Phi      : State -> nat.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).
  Local Notation pstep := (prstep event_eq_dec apply rho valid enabled).

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star gstep (sigma, B) (rho_star sigma, B).
  Hypothesis enabled_after_comp : forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm : forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  Lemma sx_pstep_gstep : forall c d, pstep c d -> gstep c d.
  Proof.
    intros c d H. destruct H as [s B e _ Hin Hen | s B Hinv].
    - rewrite <- sx_remove1_eq. apply Governance.st_apply; assumption.
    - apply Governance.st_comp. exact Hinv.
  Qed.

  Lemma sx_nf_pstep_gstep : forall c, normal_form pstep c -> normal_form gstep c.
  Proof.
    intros c Hnf [c' H]. apply Hnf. destruct H as [s B e Hin Hen | s B Hinv].
    - destruct (valid_dec s) as [Hv | Hv].
      + exists (apply e s, GovernanceCausal.remove1 event_eq_dec e B). apply ps_apply; assumption.
      + exists (rho s, B). apply ps_comp; exact Hv.
    - exists (rho s, B). apply ps_comp; exact Hinv.
  Qed.

  Theorem jc_pjc : forall c0, GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled c0 ->
    PJC event_eq_dec apply rho valid enabled c0.
  Proof.
    intros c0 HJ.
    pose proof (proj2 (GovernanceConverse.jc_exact event_eq_dec apply rho rho_star valid Phi enabled wfc
                         rho_star_reach enabled_after_comp c0) HJ) as Hcr.
    apply (pjc_exact event_eq_dec apply rho valid enabled nat lt lt_wf Phi wfc).
    apply (sx_un_cr event_eq_dec apply rho valid enabled nat lt lt_wf Phi wfc valid_dec enabled_dec).
    intros n1 n2 S1 N1 S2 N2.
    apply (GovernanceConverse.CR_UN gstep c0 Hcr).
    - exact (stream_star_sub _ _ sx_pstep_gstep _ _ S1).
    - exact (sx_nf_pstep_gstep _ N1).
    - exact (stream_star_sub _ _ sx_pstep_gstep _ _ S2).
    - exact (sx_nf_pstep_gstep _ N2).
  Qed.

  (* The rewrite-system exact condition, at every received set, is sufficient for stream agreement. *)
  Theorem jc_stream_agreement : forall s0,
    (forall E, NoDup E -> GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled (s0, E)) ->
    StreamAgree event_eq_dec apply rho valid enabled s0.
  Proof.
    intros s0 H. apply (pjc_stream_agreement event_eq_dec apply rho valid enabled nat lt lt_wf Phi wfc
                          enabled_perm).
    intros E Hnd. apply jc_pjc. exact (H E Hnd).
  Qed.
End JCSufficient.

(* ===================== Free delivery: CC1 at processor-reachable states ===================== *)

Section FreeStreamExact.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.

  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.

  (* Free delivery: every buffered event may fire. *)
  Definition fen (e : Event) (_ : State) (B : list Event) : Prop := In e B.

  Local Notation fpstep := (prstep event_eq_dec apply rho valid fen).
  Local Notation fcstep := (GovernanceCausal.step event_eq_dec apply rho valid fen).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).
  Local Notation proc := (is_processor event_eq_dec apply rho valid fen).
  Local Notation done := (settled event_eq_dec apply rho valid fen).

  (* Canonical repair: reached by the system, and valid (Def. "Iterated Compensation"). *)
  Hypothesis rho_star_reach : forall sigma B, star fcstep (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  Definition gov (e : Event) (s : State) : State := rho_star (apply e s).

  Fixpoint grun (s : State) (w : list Event) : State :=
    match w with
    | [] => s
    | e :: w' => grun (gov e s) w'
    end.

  (* The exact condition: CC1 at every state the processor reaches, for fresh distinct events. *)
  Definition PCC (s0 : State) : Prop :=
    forall w e1 e2, NoDup (w ++ [e1; e2]) ->
      gov e2 (gov e1 (grun (rho_star s0) w)) = gov e1 (gov e2 (grun (rho_star s0) w)).

  Lemma fen_perm : forall e s B C, Permutation B C -> fen e s B -> fen e s C.
  Proof. intros e s B C HP H. exact (Permutation_in e HP H). Qed.

  Lemma fen_dec : forall e s B, {fen e s B} + {~ fen e s B}.
  Proof. intros e s B. exact (in_dec event_eq_dec e B). Defined.

  Lemma fen_progress : Progress valid fen.
  Proof. intros s [| x B] _ H; [congruence |]. exists x. split; left; reflexivity. Qed.

  (* A run that keeps its buffer takes only compensation steps, which are processor steps. *)
  Lemma fx_keep_buffer : forall c d, star fcstep c d ->
    length (snd d) <= length (snd c) /\ (length (snd d) = length (snd c) -> star fpstep c d).
  Proof.
    intros c d H. induction H as [c | c c1 d Hc _ [IH1 IH2]].
    - split; [apply le_n | intros _; apply star_refl].
    - destruct Hc as [s B e Hin Hen | s B Hinv]; simpl in *.
      + pose proof (GovernanceCausal.remove1_length_in event_eq_dec e B Hin). split; [lia | intros; lia].
      + split; [exact IH1 |]. intros Heq. eapply star_step; [apply ps_comp; exact Hinv | exact (IH2 Heq)].
  Qed.

  Lemma fx_repair : forall x B, star fpstep (x, B) (rho_star x, B).
  Proof. intros x B. exact (proj2 (fx_keep_buffer _ _ (rho_star_reach x B)) eq_refl). Qed.

  Lemma fx_grun_app : forall w v s, grun s (w ++ v) = grun (grun s w) v.
  Proof. induction w as [| e w IH]; intros v s; simpl; [reflexivity | apply IH]. Qed.

  Lemma fx_grun_valid : forall w s, valid s -> valid (grun s w).
  Proof. induction w as [| e w IH]; intros s Hv; simpl; [exact Hv | apply IH; apply rho_star_valid]. Qed.

  Lemma fx_run : forall w s B, valid s -> star fpstep (s, w ++ B) (grun s w, B).
  Proof.
    induction w as [| e w IH]; intros s B Hv; simpl; [apply star_refl |].
    eapply star_step.
    - apply (ps_apply event_eq_dec apply rho valid fen s (e :: w ++ B) e Hv (or_introl eq_refl)
               (or_introl eq_refl)).
    - rewrite (st_rm_head event_eq_dec). eapply star_trans; [apply fx_repair |].
      apply IH. apply rho_star_valid.
  Qed.

  Lemma fx_run_from : forall s0 w B, star fpstep (s0, w ++ B) (grun (rho_star s0) w, B).
  Proof.
    intros s0 w B. eapply star_trans; [apply fx_repair |]. apply fx_run. apply rho_star_valid.
  Qed.

  Lemma fx_nf_empty : forall s, valid s -> normal_form fpstep (s, []).
  Proof.
    intros s Hv [c' H]. inversion H as [? ? ? ? Hin | ? ? Hinv]; subst; [destruct Hin | contradiction].
  Qed.

  Lemma fx_det_nil : forall s c1 c2, fpstep (s, []) c1 -> fpstep (s, []) c2 -> c1 = c2 /\ snd c1 = [].
  Proof.
    intros s c1 c2 H1 H2.
    inversion H1 as [? ? ? ? Hin | ? ? Hinv1]; subst; [destruct Hin |].
    inversion H2 as [? ? ? ? Hin | ? ? Hinv2]; subst; [destruct Hin |].
    split; reflexivity.
  Qed.

  Lemma fx_det : forall c y, star fpstep c y -> snd c = [] -> normal_form fpstep y ->
    forall z, star fpstep c z -> normal_form fpstep z -> y = z.
  Proof.
    intros c y H. induction H as [c | c c1 y Hc _ IH]; intros Hs Ny z Hz Nz.
    - exact (star_from_nf _ _ _ Ny Hz).
    - destruct (stream_star_inv _ _ _ Hz) as [Ez | [c2 [Hc2 Hz']]].
      + subst z. exfalso. apply Nz. exists c1. exact Hc.
      + destruct c as [s B]. simpl in Hs. subst B.
        destruct (fx_det_nil s c1 c2 Hc Hc2) as [<- Hs1].
        exact (IH Hs1 Ny z Hz' Nz).
  Qed.

  (* Invariant of processor runs from (s0, E): the applied word w and the received rest B make up E,
     and the state lies on the compensation chain whose valid end is grun (rho_star s0) w. *)
  Definition FInv (s0 : State) (E : list Event) (c : State * list Event) : Prop :=
    exists w x, Permutation (w ++ snd c) E /\ star fpstep (x, []) (fst c, []) /\
                star fpstep (x, []) (grun (rho_star s0) w, []).

  Lemma fx_inv_valid : forall s0 E c, FInv s0 E c -> valid (fst c) ->
    exists w, Permutation (w ++ snd c) E /\ fst c = grun (rho_star s0) w.
  Proof.
    intros s0 E c [w [x [HP [Hx Hg]]]] Hv. exists w. split; [exact HP |].
    assert (E1 : (fst c, @nil Event) = (grun (rho_star s0) w, [])).
    { apply (fx_det (x, []) _ Hx eq_refl (fx_nf_empty _ Hv) _ Hg).
      apply fx_nf_empty. apply fx_grun_valid. apply rho_star_valid. }
    injection E1 as E1. exact E1.
  Qed.

  Lemma fx_inv_step : forall s0 E c d, FInv s0 E c -> fpstep c d -> FInv s0 E d.
  Proof.
    intros s0 E c d Hi H. destruct H as [s B e Hv Hin Hen | s B Hinv].
    - destruct (fx_inv_valid s0 E (s, B) Hi Hv) as [w [HP Hs]]. simpl in HP, Hs.
      exists (w ++ [e]), (apply e s). simpl. split; [| split; [apply star_refl |]].
      + rewrite <- app_assoc. simpl. eapply Permutation_trans; [| exact HP].
        apply Permutation_app_head. apply Permutation_sym. apply st_rm_perm_cons. exact Hin.
      + rewrite fx_grun_app. simpl. rewrite <- Hs. apply fx_repair.
    - destruct Hi as [w [x [HP [Hx Hg]]]]. exists w, x. simpl in *.
      split; [exact HP |]. split; [| exact Hg].
      eapply star_trans; [exact Hx |]. apply star_one. apply ps_comp. exact Hinv.
  Qed.

  Lemma fx_inv_reach : forall s0 E c, star fpstep (s0, E) c -> FInv s0 E c.
  Proof.
    intros s0 E c H.
    apply (GovernanceConverse.star_closed fpstep (FInv s0 E) (fx_inv_step s0 E) (s0, E) c); [| exact H].
    exists [], s0. simpl. split; [apply Permutation_refl |]. split; [apply star_refl | apply fx_repair].
  Qed.

  Lemma fx_nodup_pick : forall (w B : list Event) e1 e2,
    NoDup (w ++ B) -> In e1 B -> In e2 B -> e1 <> e2 -> NoDup (w ++ [e1; e2]).
  Proof.
    intros w B e1 e2 Hnd Hin1 Hin2 Hne.
    assert (HP : Permutation B (e1 :: e2 :: rm e2 (rm e1 B))).
    { eapply Permutation_trans; [apply (st_rm_perm_cons event_eq_dec e1 B Hin1) |].
      apply perm_skip. apply st_rm_perm_cons. apply st_in_rm_neq; assumption. }
    assert (Hnd' : NoDup ((w ++ [e1; e2]) ++ rm e2 (rm e1 B))).
    { rewrite <- app_assoc. simpl. apply (Permutation_NoDup (Permutation_app_head w HP)). exact Hnd. }
    exact (NoDup_app_remove_r _ _ Hnd').
  Qed.

  Lemma fx_two : forall sigma B e1 e2, In e2 B -> e1 <> e2 ->
    star fpstep (apply e1 sigma, rm e1 B) (gov e2 (gov e1 sigma), rm e2 (rm e1 B)).
  Proof.
    intros sigma B e1 e2 Hin2 Hne.
    assert (Hin2' : In e2 (rm e1 B)) by (apply st_in_rm_neq; assumption).
    eapply star_trans; [apply fx_repair |]. eapply star_step.
    - exact (ps_apply event_eq_dec apply rho valid fen (gov e1 sigma) (rm e1 B) e2 (rho_star_valid _)
               Hin2' Hin2').
    - apply fx_repair.
  Qed.

  Theorem pcc_pjc : forall s0, PCC s0 -> forall E, NoDup E -> PJC event_eq_dec apply rho valid fen (s0, E).
  Proof.
    intros s0 HC E Hnd sigma B Hr Hv e1 e2 Hin1 Hin2 _ _ Hne.
    destruct (fx_inv_valid s0 E (sigma, B) (fx_inv_reach s0 E _ Hr) Hv) as [w [HP Hs]].
    simpl in HP, Hs. subst sigma.
    assert (Hw : NoDup (w ++ [e1; e2])).
    { apply (fx_nodup_pick w B); [| assumption..]. exact (Permutation_NoDup (Permutation_sym HP) Hnd). }
    exists (gov e2 (gov e1 (grun (rho_star s0) w)), rm e2 (rm e1 B)). split.
    - apply fx_two; assumption.
    - rewrite (HC w e1 e2 Hw), (GovernanceCausal.remove1_comm event_eq_dec e1 e2 B).
      apply fx_two; [exact Hin1 | intro E1; apply Hne; symmetry; exact E1].
  Qed.

  Lemma fx_rm_skip : forall a e l, a <> e -> rm e (a :: l) = a :: rm e l.
  Proof. intros a e l H. simpl. destruct (event_eq_dec a e); [contradiction | reflexivity]. Qed.

  (* The two orders of e1 and e2 after w, each a complete processor run on the set w ++ [e1; e2]. *)
  Lemma fx_two_runs : forall s0 w e1 e2, e1 <> e2 ->
    star fpstep (s0, w ++ [e1; e2]) (gov e2 (gov e1 (grun (rho_star s0) w)), []) /\
    star fpstep (s0, w ++ [e1; e2]) (gov e1 (gov e2 (grun (rho_star s0) w)), []).
  Proof.
    intros s0 w e1 e2 Hne. set (sigma := grun (rho_star s0) w).
    assert (Hv : valid sigma) by (apply fx_grun_valid; apply rho_star_valid).
    split.
    - pose proof (fx_run_from s0 (w ++ [e1; e2]) []) as H.
      rewrite app_nil_r, fx_grun_app in H. exact H.
    - eapply star_trans; [apply fx_run_from |]. fold sigma.
      eapply star_step.
      + exact (ps_apply event_eq_dec apply rho valid fen sigma [e1; e2] e2 Hv
                 (or_intror (or_introl eq_refl)) (or_intror (or_introl eq_refl))).
      + rewrite (fx_rm_skip e1 e2 [e2] Hne), (st_rm_head event_eq_dec).
        eapply star_trans; [apply fx_repair |]. eapply star_step.
        * exact (ps_apply event_eq_dec apply rho valid fen (gov e2 sigma) [e1] e1 (rho_star_valid _)
                   (or_introl eq_refl) (or_introl eq_refl)).
        * rewrite (st_rm_head event_eq_dec). apply fx_repair.
  Qed.

  Lemma fx_nodup_ne : forall (w : list Event) e1 e2, NoDup (w ++ [e1; e2]) -> e1 <> e2.
  Proof.
    intros w e1 e2 H E. subst e2. apply (NoDup_remove_2 (w ++ [e1]) [] e1).
    - rewrite <- app_assoc. exact H.
    - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  Qed.

  (* The converse made concrete: a PCC failure gives two processors that receive the same set,
     settle, and disagree. *)
  Theorem stream_diverge_free : forall s0 w e1 e2, NoDup (w ++ [e1; e2]) ->
    gov e2 (gov e1 (grun (rho_star s0) w)) <> gov e1 (gov e2 (grun (rho_star s0) w)) ->
    exists p1 p2,
      proc (fun e => In e (w ++ [e1; e2])) s0 p1 /\ proc (fun e => In e (w ++ [e1; e2])) s0 p2 /\
      done p1 0 /\ done p2 0 /\ recv p1 0 = w ++ [e1; e2] /\ recv p2 0 = w ++ [e1; e2] /\
      psi p1 0 <> psi p2 0.
  Proof.
    intros s0 w e1 e2 Hnd Hne.
    destruct (fx_two_runs s0 w e1 e2 (fx_nodup_ne w e1 e2 Hnd)) as [S1 S2].
    exists (const_proc (w ++ [e1; e2]) (gov e2 (gov e1 (grun (rho_star s0) w)), [])),
           (const_proc (w ++ [e1; e2]) (gov e1 (gov e2 (grun (rho_star s0) w)), [])).
    split; [exact (sx_const_proc_is event_eq_dec apply rho valid fen s0 _ _ Hnd S1) |].
    split; [exact (sx_const_proc_is event_eq_dec apply rho valid fen s0 _ _ Hnd S2) |].
    split; [apply fx_nf_empty; apply rho_star_valid |].
    split; [apply fx_nf_empty; apply rho_star_valid |].
    split; [reflexivity |]. split; [reflexivity |]. exact Hne.
  Qed.

  (* The exact theorem under free delivery: stream agreement from s0 iff PCC s0. CC2 is not part
     of it: a processor compensates before it applies. *)
  Theorem stream_exact_free : forall s0,
    StreamAgree event_eq_dec apply rho valid fen s0 <-> PCC s0.
  Proof.
    intros s0. split.
    - intros H w e1 e2 Hnd.
      destruct (fx_two_runs s0 w e1 e2 (fx_nodup_ne w e1 e2 Hnd)) as [S1 S2].
      exact (H (fun e => In e (w ++ [e1; e2])) (const_proc (w ++ [e1; e2]) (_, []))
               (const_proc (w ++ [e1; e2]) (_, [])) 0 0
               (sx_const_proc_is event_eq_dec apply rho valid fen s0 _ _ Hnd S1)
               (sx_const_proc_is event_eq_dec apply rho valid fen s0 _ _ Hnd S2)
               (fx_nf_empty _ (rho_star_valid _)) (fx_nf_empty _ (rho_star_valid _))
               (fun e => iff_refl _)).
    - intros HC. apply (pjc_stream_agreement event_eq_dec apply rho valid fen P ltP wf_ltP Phi wfc_wf
                          fen_perm).
      apply pcc_pjc. exact HC.
  Qed.

  (* The general exact theorem applies too (free delivery satisfies Progress). *)
  Corollary stream_exact_free_pjc : forall s0,
    StreamAgree event_eq_dec apply rho valid fen s0 <->
    (forall E, NoDup E -> PJC event_eq_dec apply rho valid fen (s0, E)).
  Proof.
    exact (stream_exact event_eq_dec apply rho valid fen P ltP wf_ltP Phi wfc_wf valid_dec fen_dec
             fen_perm fen_progress).
  Qed.
End FreeStreamExact.

(* ============================================================================================ *)
(* Counterexample 1: the rewrite-system condition is not necessary at stream level.             *)
(* ============================================================================================ *)

(* One event (unit), states nat, only 1 is invalid and compensates to 0, the event adds 2. From
   s0 = 1 the rewrite system may apply the event at the invalid state (ending at 3) or compensate
   first (ending at 2): CC2 fails at s0, JC (1, [tt]) fails, cc_exact_from's condition fails. A
   processor compensates before it applies, so every processor from 1 ends at 2 and any two agree. *)

Definition a_apply (_ : unit) (s : nat) : nat := s + 2.
Definition a_rho (_ : nat) : nat := 0.
Definition a_valid (s : nat) : Prop := s <> 1.
Definition a_rho_star (s : nat) : nat := if Nat.eqb s 1 then 0 else s.
Definition a_Phi (s : nat) : nat := if Nat.eqb s 1 then 1 else 0.

Definition unit_eq_dec : forall a b : unit, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma a_wfc : forall s, ~ a_valid s -> a_Phi (a_rho s) < a_Phi s.
Proof.
  intros s H. destruct (Nat.eq_dec s 1) as [-> | Hs]; [cbv; lia | exfalso; exact (H Hs)].
Qed.

Lemma a_rho_star_reach : forall s B,
  star (GovernanceCausal.step unit_eq_dec a_apply a_rho a_valid fen) (s, B) (a_rho_star s, B).
Proof.
  intros s B. unfold a_rho_star. destruct (Nat.eqb_spec s 1) as [-> | Hs].
  - apply star_one. apply GovernanceCausal.st_comp. intro H. apply H. reflexivity.
  - apply star_refl.
Qed.

Lemma a_rho_star_valid : forall s, a_valid (a_rho_star s).
Proof. intros s. unfold a_valid, a_rho_star. destruct (Nat.eqb_spec s 1); lia. Qed.

Lemma a_gnf : forall s, a_valid s ->
  normal_form (Governance.step unit_eq_dec a_apply a_rho a_valid fen) (s, []).
Proof.
  intros s Hv [c' H]. inversion H as [? ? ? Hin | ? ? Hinv]; subst; [destruct Hin | exact (Hinv Hv)].
Qed.

Theorem jc_not_necessary :
  (* every hypothesis of the free-delivery stream section, *)
  (forall s, ~ a_valid s -> a_Phi (a_rho s) < a_Phi s) /\
  (forall s B, star (GovernanceCausal.step unit_eq_dec a_apply a_rho a_valid fen) (s, B) (a_rho_star s, B)) /\
  (forall s, a_valid (a_rho_star s)) /\
  (* CC2 fails at the start state 1, which is reachable from itself, *)
  ~ a_valid 1 /\ a_rho_star (a_apply tt 1) <> a_rho_star (a_apply tt (a_rho 1)) /\
  ~ (forall sigma e, GovernanceConverse.reach a_apply a_rho a_valid 1 sigma -> ~ a_valid sigma ->
       a_rho_star (a_apply e sigma) = a_rho_star (a_apply e (a_rho sigma))) /\
  (* the rewrite-system exact condition fails, *)
  ~ GovernanceConverse.JC unit_eq_dec a_apply a_rho a_rho_star a_valid fen (1, [tt]) /\
  (* yet every two processors from 1 agree once settled on the same set. *)
  StreamAgree unit_eq_dec a_apply a_rho a_valid fen 1.
Proof.
  assert (Hcc2 : a_rho_star (a_apply tt 1) <> a_rho_star (a_apply tt (a_rho 1))) by (cbv; discriminate).
  assert (Hinv : ~ a_valid 1) by (intro H; apply H; reflexivity).
  split; [exact a_wfc |]. split; [exact a_rho_star_reach |]. split; [exact a_rho_star_valid |].
  split; [exact Hinv |]. split; [exact Hcc2 |].
  split; [intro H; exact (Hcc2 (H 1 tt (GovernanceConverse.r_init _ _ _ _) Hinv)) |].
  split.
  - intro HJ. destruct (HJ 1 [tt] (star_refl _ _)) as [_ J2].
    destruct (J2 tt Hinv (or_introl eq_refl) (or_introl eq_refl)) as [w [A1 A2]].
    cbn in A1, A2.
    rewrite <- (star_from_nf _ _ _ (a_gnf 3 ltac:(unfold a_valid; lia)) A1) in A2.
    pose proof (star_from_nf _ _ _ (a_gnf 2 ltac:(unfold a_valid; lia)) A2) as E. discriminate E.
  - apply (stream_exact_free unit_eq_dec a_apply a_rho a_rho_star a_valid nat lt lt_wf a_Phi a_wfc
             a_rho_star_reach a_rho_star_valid 1).
    intros w [] [] Hnd. exfalso. exact (fx_nodup_ne w tt tt Hnd eq_refl).
Qed.

(* ============================================================================================ *)
(* Counterexample 2: without Progress, PJC is not necessary.                                    *)
(* ============================================================================================ *)

(* One state (unit), two events, each enabled only while the other is still buffered. From
   (tt, [true; false]) the finished configurations are (tt, [false]) and (tt, [true]): PJC fails,
   while finished states, the only thing a processor exposes, always agree. *)

Definition b_apply (_ : bool) (s : unit) : unit := s.
Definition b_rho (s : unit) : unit := s.
Definition b_valid (_ : unit) : Prop := True.
Definition b_enabled (e : bool) (_ : unit) (B : list bool) : Prop := In (negb e) B.
Definition b_Phi (_ : unit) : nat := 0.

Local Notation b_pstep := (prstep Bool.bool_dec b_apply b_rho b_valid b_enabled).

Lemma b_nf : forall x, normal_form b_pstep (tt, [x]).
Proof.
  intros x [c' H]. inversion H as [? ? e Hv Hin Hen | ? ? Hinv]; subst; [| exact (Hinv I)].
  destruct Hin as [Ex | []]. destruct Hen as [Hb | []]. rewrite Ex in Hb. destruct e; discriminate Hb.
Qed.

(* The decidability hypotheses (in Type, so stated separately). *)
Definition b_valid_dec (s : unit) : {b_valid s} + {~ b_valid s} := left I.
Definition b_enabled_dec (e : bool) (s : unit) (B : list bool) : {b_enabled e s B} + {~ b_enabled e s B} :=
  in_dec Bool.bool_dec (negb e) B.

Theorem progress_needed :
  (forall s, ~ b_valid s -> b_Phi (b_rho s) < b_Phi s) /\
  (forall e s B C, Permutation B C -> b_enabled e s B -> b_enabled e s C) /\
  ~ Progress b_valid b_enabled /\
  StreamAgree Bool.bool_dec b_apply b_rho b_valid b_enabled tt /\
  ~ PJC Bool.bool_dec b_apply b_rho b_valid b_enabled (tt, [true; false]).
Proof.
  split; [intros s H; exfalso; exact (H I) |].
  split; [intros e s B C HP H; exact (Permutation_in _ HP H) |].
  split.
  - intro H. destruct (H tt [true] I ltac:(discriminate)) as [e [Hin Hen]].
    destruct Hin as [<- | []]. destruct Hen as [Hb | []]. discriminate Hb.
  - split.
    + intros Str p1 p2 t1 t2 _ _ _ _ _. destruct (psi p1 t1), (psi p2 t2). reflexivity.
    + intro H.
      destruct (H tt [true; false] (star_refl _ _) I true false (or_introl eq_refl)
                  (or_intror (or_introl eq_refl)) (or_intror (or_introl eq_refl))
                  (or_introl eq_refl) ltac:(discriminate)) as [w [A1 A2]].
      cbn in A1, A2.
      rewrite <- (star_from_nf _ _ _ (b_nf false) A1) in A2.
      pose proof (star_from_nf _ _ _ (b_nf true) A2) as E. discriminate E.
Qed.

(* ============================================================================================ *)
(* Counterexample 3: JC fails and two processors disagree.                                       *)
(* ============================================================================================ *)

(* Free delivery, every state valid, no compensation. Event 0 doubles, every other event adds 1.
   From 0: doubling then adding gives 1, adding then doubling gives 2. *)

Definition c_apply (e : nat) (s : nat) : nat := if Nat.eqb e 0 then s * 2 else s + 1.
Definition c_rho (s : nat) : nat := s.
Definition c_rho_star (s : nat) : nat := s.
Definition c_valid (_ : nat) : Prop := True.
Definition c_Phi (_ : nat) : nat := 0.

Local Notation c_gstep := (Governance.step Nat.eq_dec c_apply c_rho c_valid fen).
Local Notation c_proc := (is_processor Nat.eq_dec c_apply c_rho c_valid fen).
Local Notation c_settled := (settled Nat.eq_dec c_apply c_rho c_valid fen).

Lemma c_wfc : forall s, ~ c_valid s -> c_Phi (c_rho s) < c_Phi s.
Proof. intros s H. exfalso. exact (H I). Qed.

Lemma c_reach : forall s B,
  star (GovernanceCausal.step Nat.eq_dec c_apply c_rho c_valid fen) (s, B) (c_rho_star s, B).
Proof. intros. apply star_refl. Qed.

Lemma c_gnf : forall s, normal_form c_gstep (s, []).
Proof. intros s [c' H]. inversion H as [? ? ? Hin | ? ? Hinv]; subst; [destruct Hin | exact (Hinv I)]. Qed.

Theorem jc_fail_disagree :
  ~ GovernanceConverse.JC Nat.eq_dec c_apply c_rho c_rho_star c_valid fen (0, [0; 1]) /\
  ~ PJC Nat.eq_dec c_apply c_rho c_valid fen (0, [0; 1]) /\
  ~ PCC c_apply c_rho_star 0 /\
  ~ StreamAgree Nat.eq_dec c_apply c_rho c_valid fen 0 /\
  exists p1 p2,
    c_proc (fun e => In e [0; 1]) 0 p1 /\ c_proc (fun e => In e [0; 1]) 0 p2 /\
    c_settled p1 0 /\ c_settled p2 0 /\ recv p1 0 = [0; 1] /\ recv p2 0 = [0; 1] /\
    psi p1 0 <> psi p2 0.
Proof.
  assert (Hnd : NoDup ([] ++ [0; 1])) by (repeat constructor; simpl; intuition discriminate).
  assert (Hne : gov c_apply c_rho_star 1 (gov c_apply c_rho_star 0 (grun c_apply c_rho_star (c_rho_star 0) []))
             <> gov c_apply c_rho_star 0 (gov c_apply c_rho_star 1 (grun c_apply c_rho_star (c_rho_star 0) [])))
    by (cbv; discriminate).
  assert (Hpcc : ~ PCC c_apply c_rho_star 0) by (intro H; exact (Hne (H [] 0 1 Hnd))).
  assert (Hagree : ~ StreamAgree Nat.eq_dec c_apply c_rho c_valid fen 0).
  { rewrite (stream_exact_free Nat.eq_dec c_apply c_rho c_rho_star c_valid nat lt lt_wf c_Phi c_wfc
               c_reach (fun _ => I) 0). exact Hpcc. }
  split; [| split; [| split; [exact Hpcc | split; [exact Hagree |]]]].
  - (* via jc_exact: the rewrite system is not confluent from (0, [0; 1]) *)
    intro HJ.
    pose proof (proj2 (GovernanceConverse.jc_exact Nat.eq_dec c_apply c_rho c_rho_star c_valid c_Phi fen
                         c_wfc (fun s B => star_refl _ _) (fun _ _ _ H => H) (0, [0; 1])) HJ) as Hcr.
    assert (R1 : star c_gstep (0, [0; 1]) (1, [])).
    { eapply star_step; [apply (Governance.st_apply _ _ _ _ _ 0 [0; 1] 0); left; reflexivity |].
      cbn. eapply star_step; [apply (Governance.st_apply _ _ _ _ _ 0 [1] 1); left; reflexivity |].
      cbn. apply star_refl. }
    assert (R2 : star c_gstep (0, [0; 1]) (2, [])).
    { eapply star_step; [apply (Governance.st_apply _ _ _ _ _ 0 [0; 1] 1); right; left; reflexivity |].
      cbn. eapply star_step; [apply (Governance.st_apply _ _ _ _ _ 1 [0] 0); left; reflexivity |].
      cbn. apply star_refl. }
    destruct (Hcr _ _ R1 R2) as [w [A1 A2]].
    rewrite <- (star_from_nf _ _ _ (c_gnf 1) A1) in A2.
    pose proof (star_from_nf _ _ _ (c_gnf 2) A2) as E. discriminate E.
  - intro HP.
    pose proof (proj2 (pjc_exact Nat.eq_dec c_apply c_rho c_valid fen nat lt lt_wf c_Phi c_wfc (0, [0; 1]))
                  HP) as Hcr.
    destruct (fx_two_runs Nat.eq_dec c_apply c_rho c_rho_star c_valid c_reach (fun _ => I) 0 [] 0 1
                ltac:(discriminate)) as [S1 S2].
    destruct (Hcr _ _ S1 S2) as [w [A1 A2]].
    rewrite <- (star_from_nf _ _ _ (fx_nf_empty Nat.eq_dec c_apply c_rho c_valid _ I) A1) in A2.
    pose proof (star_from_nf _ _ _ (fx_nf_empty Nat.eq_dec c_apply c_rho c_valid _ I) A2) as E.
    cbv in E; discriminate E.
  - exact (stream_diverge_free Nat.eq_dec c_apply c_rho c_rho_star c_valid c_reach (fun _ => I)
             0 [] 0 1 Hnd Hne).
Qed.

(* ============================================================================================ *)
(* Non-vacuity on an infinite domain: the Z withdrawal registry of GovernanceWF.v and Stream.v. *)
(* ============================================================================================ *)

Open Scope Z_scope.

Theorem zw_stream_exact :
  Progress zw_valid zw_enabled /\
  (forall c, PJC Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled c) /\
  (forall s0, PCC zw_apply zw_rho_star s0) /\
  (forall s0, StreamAgree Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled s0) /\
  psi zp1 2 = psi zp2 2.
Proof.
  destruct zw_stream_registry as [Hw [_ [Hr [H1 [H2 [Hear [Heac [Hep [Hval [_ Hprog]]]]]]]]]].
  assert (Hpcc : forall s0, PCC zw_apply zw_rho_star s0).
  { intros s0 w e1 e2 _. unfold gov. apply zw_cc1. }
  assert (Hag : forall s0, StreamAgree Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled s0).
  { intros s0. exact (proj2 (stream_exact_free Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid Z (Zwf 0)
                               (Zwf_well_founded 0) zw_Phi Hw Hr Hval s0) (Hpcc s0)). }
  split; [intros s B _ H; exact (Hprog s B H) |].
  split.
  - exact (cc_pjc Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled Z (Zwf 0) (Zwf_well_founded 0) zw_Phi Hw
             zw_valid_dec zw_enabled_dec zw_rho_star Hr H1 H2 Hear Heac).
  - split; [exact Hpcc |]. split; [exact Hag |].
    destruct zw_processors as [P1 [P2 [_ [_ [Hs _]]]]].
    destruct (Hs 2%nat) as [S1 S2].
    apply (Hag 1 zstream zp1 zp2 2%nat 2%nat P1 P2 S1 S2). intros e. simpl. intuition.
Qed.

(* The general exact theorem holds on the same registry: both sides are true. *)
Theorem zw_stream_exact_iff : forall s0,
  StreamAgree Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled s0 <->
  (forall E, NoDup E -> PJC Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled (s0, E)).
Proof.
  destruct zw_stream_registry as [Hw [_ [_ [_ [_ [_ [_ [Hep _]]]]]]]].
  destruct zw_stream_exact as [Hprog _].
  exact (stream_exact Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled Z (Zwf 0) (Zwf_well_founded 0) zw_Phi
           Hw zw_valid_dec zw_enabled_dec Hep Hprog).
Qed.


(* The rewrite-system route (jc_stream_agreement) on the same registry: JC holds at every
   configuration (zw_confluent with jc_exact, nat potential), so stream agreement follows. *)
Theorem zw_jc_stream_agreement : forall s0 : Z,
  (forall E, GovernanceConverse.JC Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled (s0, E)) /\
  StreamAgree Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled s0.
Proof.
  destruct zw_stream_registry as [_ [Hw [_ [_ [_ [_ [Heac [Hep _]]]]]]]].
  intros s0.
  assert (HJ : forall E, GovernanceConverse.JC Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled (s0, E)).
  { intros E. apply (proj1 (GovernanceConverse.jc_exact Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid
                              zw_Phi_nat zw_enabled Hw zw_rho_star_reach zw_enabled_after_comp (s0, E))).
    apply zw_confluent. }
  split; [exact HJ |].
  exact (jc_stream_agreement Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled zw_Phi_nat Hw
           zw_rho_star_reach zw_enabled_after_comp zw_valid_dec zw_enabled_dec Hep s0 (fun E _ => HJ E)).
Qed.

Close Scope Z_scope.
