(* AtomicRepair.v: atomic repair, where each delivery is followed by repair to completion before
   any other event fires. Under atomic repair CC2 is not needed for unique normal forms; it is the
   price of the interleaved model of GovernanceConverse.v, where an event may fire at an invalid
   state before repair finishes. Axiom-free.

   The interleaved model (Governance.step with GovernanceConverse.free_enabled) has two moves: apply
   a buffered event's raw transition, at any state, or take one repair step at an invalid state.
   The atomic model has one move: deliver a buffered event e and repair to completion,
     (sigma, B) -> (gov e sigma, B \ {e}),   gov e s := rho_star (apply e s).

   Main results.
     atomic_exact: for every start x and any rho_star, every buffer from x has a unique atomic
       normal form IFF the governed steps commute, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma), at
       every state reachable from x by governed steps. No validity, repair or WFC hypothesis is
       used: the atomic system terminates because the buffer shrinks.
     atomic_perm: the same unique normal forms are exactly invariance of the governed run from x
       under permutations of the buffer.
     atomic_history: NormalizationDerived.FreeHistoryDescent s0 is atomic convergence from the
       canonical start rho_star s0.
     atomic_derived_from, atomic_split: under the hypotheses of cc_exact (free delivery, WFC,
       rho_star a reduct that repairs to validity), interleaved unique normal forms from s0 IFF
       atomic unique normal forms from rho_star s0 AND state descent (equivalently CC2) on the
       states reachable from s0. This is NormalizationDerived.nd_derived_from read through
       atomic_history. atomic_derived_valid: the same from a valid start, where rho_star s0 = s0.
     atomic_not_descent: the gap is real. X = {0, 1, 2}, valid = {0, 1}, rho 2 = 0, an event f with
       f s = 2 and an event e with e 0 = 0, e 1 = 0, e 2 = 1. From 0, every atomic run converges,
       but under the interleaved step of cc_exact the buffer [f; e] has the two normal forms 0
       (f, repair, e) and 1 (f, e), and CC2 fails at the reachable invalid state 2.
     atomic_not_descent_framework: in the framework's terms, history descent holds from 0 and
       state descent fails, so cc_exact_from's right side fails on its CC2 half alone. *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Governance NC.CanonicalExecution NC.PresentedExecution.
Require NC.GovernanceConverse NC.LayerInterfaces NC.NormalizationDerived.
Import ListNotations.

(* ============================================================================================ *)
(* The atomic step and its exact condition.                                                     *)
(* ============================================================================================ *)

Section Atomic.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho_star : State -> State.

  Local Notation rm := (remove1 event_eq_dec).
  Local Notation gov e s := (rho_star (apply e s)).
  Local Notation run := (grun rho_star apply).
  Local Notation UN := GovernanceConverse.UN.

  (* Deliver a buffered event and repair to completion. *)
  Inductive astep : State * list Event -> State * list Event -> Prop :=
  | as_deliver : forall sigma B e, In e B -> astep (sigma, B) (gov e sigma, rm e B).

  (* States reachable from x by governed steps. *)
  Inductive greach (x : State) : State -> Prop :=
  | g_init : greach x x
  | g_step : forall e s, greach x s -> greach x (gov e s).

  (* Governed steps commute at every state reachable from x. *)
  Definition GovCommuteOn (x : State) : Prop :=
    forall sigma e1 e2, greach x sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma).

  Lemma a_rm_head : forall e l, rm e (e :: l) = l.
  Proof. intros e l. simpl. destruct (event_eq_dec e e) as [_ | E]; [reflexivity | contradiction]. Qed.

  Lemma a_rm_skip : forall e x l, x <> e -> rm e (x :: l) = x :: rm e l.
  Proof. intros e x l H. simpl. destruct (event_eq_dec x e) as [E | _]; [contradiction | reflexivity]. Qed.

  Lemma a_in_rm : forall e x l, In x l -> x <> e -> In x (rm e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |].
    simpl. destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma a_perm_rm : forall e l, In e l -> Permutation l (e :: rm e l).
  Proof.
    intros e l. induction l as [| y l IH]; intros Hin; [destruct Hin |].
    simpl. destruct (event_eq_dec y e) as [-> | Hy]; [apply Permutation_refl |].
    destruct Hin as [-> | Hin]; [contradiction |].
    eapply perm_trans; [apply perm_skip; exact (IH Hin) | apply perm_swap].
  Qed.

  (* Normal forms are exactly the empty buffers. *)
  Lemma a_nf_empty : forall s, normal_form astep (s, []).
  Proof. intros s [y H]. inversion H as [s' B e Hin E1 E2]. destruct Hin. Qed.

  Lemma a_nf_nil : forall s B, normal_form astep (s, B) -> B = [].
  Proof.
    intros s [| e B] N; [reflexivity |]. exfalso. apply N. eexists.
    apply as_deliver. left. reflexivity.
  Qed.

  (* The atomic system terminates: the buffer shrinks. *)
  Lemma a_SN : forall c, SN astep c.
  Proof.
    assert (K : forall n s B, length B < n -> SN astep (s, B)).
    { intros n. induction n as [| n IH]; intros s B Hl; [lia |].
      constructor. intros y H. inversion H as [s' B' e Hin E1 E2]; subst.
      apply IH. pose proof (remove1_length_in event_eq_dec e B Hin). lia. }
    intros [s B]. exact (K (S (length B)) s B (Nat.lt_succ_diag_r _)).
  Qed.

  (* Delivering a word in order runs the governed semantics. *)
  Lemma a_word : forall w s B, star astep (s, w ++ B) (run w s, B).
  Proof.
    intros w. induction w as [| e w IH]; intros s B; [apply star_refl |].
    eapply star_step; [apply as_deliver; left; reflexivity |].
    simpl app. rewrite a_rm_head. exact (IH (gov e s) B).
  Qed.

  Lemma a_greach_run : forall x sigma, greach x sigma -> exists w, sigma = run w x.
  Proof.
    intros x sigma H. induction H as [| e s _ [w IH]].
    - exists []. reflexivity.
    - exists (w ++ [e]). rewrite grun_snoc, <- IH. reflexivity.
  Qed.

  Lemma a_greach_star : forall x c d, star astep c d -> greach x (fst c) -> greach x (fst d).
  Proof.
    intros x c d S. induction S as [c | c y z H _ IH]; intros Hc; [exact Hc |].
    apply IH. destruct H as [s B e _]. simpl in *. apply g_step. exact Hc.
  Qed.

  (* The exact condition for atomic repair: governed steps commute at the governed-reachable
     states. *)
  Theorem atomic_exact : forall x,
    (forall B, UN astep (x, B)) <-> GovCommuteOn x.
  Proof.
    intros x. split.
    - intros H sigma e1 e2 Hs. destruct (event_eq_dec e1 e2) as [-> | Hd]; [reflexivity |].
      destruct (a_greach_run x sigma Hs) as [w ->].
      assert (S1 : star astep (x, w ++ [e1; e2]) (gov e2 (gov e1 (run w x)), [])).
      { eapply star_trans; [apply a_word |].
        eapply star_step; [apply as_deliver; left; reflexivity |]. rewrite a_rm_head.
        eapply star_step; [apply as_deliver; left; reflexivity |]. rewrite a_rm_head.
        apply star_refl. }
      assert (S2 : star astep (x, w ++ [e1; e2]) (gov e1 (gov e2 (run w x)), [])).
      { eapply star_trans; [apply a_word |].
        eapply star_step; [apply as_deliver; right; left; reflexivity |].
        rewrite (a_rm_skip e2 e1 [e2] Hd), a_rm_head.
        eapply star_step; [apply as_deliver; left; reflexivity |]. rewrite a_rm_head.
        apply star_refl. }
      pose proof (H _ _ _ S1 (a_nf_empty _) S2 (a_nf_empty _)) as E. injection E as E. exact E.
    - intros HC B0. apply GovernanceConverse.CR_UN.
      apply (GovernanceConverse.newman_on astep (fun c => greach x (fst c))).
      + intros c d Hc H. exact (a_greach_star x c d (star_one _ _ _ H) Hc).
      + intros c y z Hc H1 H2.
        destruct H1 as [s B e1 Hin1]. inversion H2 as [s' B' e2 Hin2 E1 E2]; subst.
        destruct (event_eq_dec e1 e2) as [-> | Hne].
        * exists (gov e2 s, rm e2 B). split; apply star_refl.
        * exists (gov e2 (gov e1 s), rm e2 (rm e1 B)). split.
          -- apply star_one. apply as_deliver. apply a_in_rm; [exact Hin2 |].
             intro E. apply Hne. symmetry. exact E.
          -- rewrite (HC s e1 e2 Hc), remove1_comm. apply star_one. apply as_deliver.
             apply a_in_rm; [exact Hin1 | exact Hne].
      + intros c _. apply a_SN.
      + apply g_init.
  Qed.

  (* Every atomic run delivers a permutation of the buffer. *)
  Lemma a_star_perm : forall c d, star astep c d ->
    exists t, Permutation (snd c) (t ++ snd d) /\ fst d = run t (fst c).
  Proof.
    intros c d S. induction S as [c | c y z H _ IH].
    - exists []. split; [apply Permutation_refl | reflexivity].
    - destruct H as [s B e Hin]. destruct IH as [t [P E]]. simpl in *.
      exists (e :: t). split; [| exact E].
      eapply perm_trans; [apply (a_perm_rm e B Hin) |]. simpl. apply perm_skip. exact P.
  Qed.

  (* Every permutation of the buffer is an atomic run. *)
  Lemma a_run_perm : forall t' t s, Permutation t t' -> star astep (s, t) (run t' s, []).
  Proof.
    intros t'. induction t' as [| e t' IH]; intros t s P.
    - rewrite (Permutation_nil (Permutation_sym P)). apply star_refl.
    - assert (Hin : In e t) by (apply (Permutation_in e (Permutation_sym P)); left; reflexivity).
      eapply star_step; [apply as_deliver; exact Hin |]. apply IH.
      apply (Permutation_cons_inv (a:=e)).
      eapply perm_trans; [apply Permutation_sym, a_perm_rm; exact Hin | exact P].
  Qed.

  (* Atomic unique normal forms from x are permutation invariance of the governed run from x. *)
  Theorem atomic_perm : forall x,
    (forall B, UN astep (x, B)) <->
    (forall t t', Permutation t t' -> run t x = run t' x).
  Proof.
    intros x. split.
    - intros H t t' P.
      pose proof (H t _ _ (a_run_perm t t x (Permutation_refl t)) (a_nf_empty _)
                         (a_run_perm t' t x P) (a_nf_empty _)) as E.
      injection E as E. exact E.
    - intros H B [s1 B1] [s2 B2] S1 N1 S2 N2.
      rewrite (a_nf_nil _ _ N1) in *. rewrite (a_nf_nil _ _ N2) in *.
      destruct (a_star_perm _ _ S1) as [t1 [P1 E1]]. destruct (a_star_perm _ _ S2) as [t2 [P2 E2]].
      simpl in *. rewrite app_nil_r in P1, P2. rewrite E1, E2.
      f_equal. apply H. eapply perm_trans; [apply Permutation_sym; exact P1 | exact P2].
  Qed.

  (* NormalizationDerived's history descent is atomic convergence from the canonical start. *)
  Theorem atomic_history : forall s0,
    NormalizationDerived.FreeHistoryDescent apply rho_star s0 <->
    (forall B, UN astep (rho_star s0, B)).
  Proof.
    intros s0. rewrite (atomic_perm (rho_star s0)).
    unfold NormalizationDerived.FreeHistoryDescent, NormalizationDerived.gsem, PInv. split.
    - intros H t t' P. apply H. apply swap_peq_perm. exact P.
    - intros H t t' E. apply H. apply swap_peq_perm. exact E.
  Qed.
End Atomic.

(* ============================================================================================ *)
(* Interleaved convergence is atomic convergence plus state descent (CC2).                      *)
(* ============================================================================================ *)

Section Split.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable Phi      : State -> nat.

  Local Notation fstep :=
    (step event_eq_dec apply rho valid (GovernanceConverse.free_enabled (State:=State))).
  Local Notation astep := (astep event_eq_dec apply rho_star).
  Local Notation UN := GovernanceConverse.UN.

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star fstep (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  (* nd_derived_from read through atomic_history. *)
  Theorem atomic_derived_from : forall s0,
    (forall B, UN fstep (s0, B)) <->
    (forall B, UN astep (rho_star s0, B)) /\
    NormalizationDerived.StateDescentReach apply rho rho_star valid s0.
  Proof.
    intros s0. rewrite <- (atomic_history event_eq_dec apply rho_star s0).
    exact (NormalizationDerived.nd_derived_from event_eq_dec apply rho rho_star valid Phi wfc
             rho_star_reach rho_star_valid s0).
  Qed.

  (* The same with state descent written as CC2 on the states reachable from s0. *)
  Theorem atomic_split : forall s0,
    (forall B, UN fstep (s0, B)) <->
    (forall B, UN astep (rho_star s0, B)) /\
    (forall sigma e, GovernanceConverse.reach apply rho valid s0 sigma -> ~ valid sigma ->
       rho_star (apply e sigma) = rho_star (apply e (rho sigma))).
  Proof.
    intros s0. rewrite atomic_derived_from.
    pose proof (NormalizationDerived.nd_descends_cc2 event_eq_dec apply rho rho_star valid
                  rho_star_reach rho_star_valid s0) as D.
    unfold NormalizationDerived.CC2Reach in D. tauto.
  Qed.

  (* From a valid start, rho_star s0 = s0: interleaved convergence from s0 is atomic convergence
     from s0 plus CC2 on the states reachable from s0. *)
  Theorem atomic_derived_valid : forall s0, valid s0 ->
    (forall B, UN fstep (s0, B)) <->
    (forall B, UN astep (s0, B)) /\
    (forall sigma e, GovernanceConverse.reach apply rho valid s0 sigma -> ~ valid sigma ->
       rho_star (apply e sigma) = rho_star (apply e (rho sigma))).
  Proof.
    intros s0 Hv. rewrite atomic_split.
    rewrite (NormalizationDerived.nd_N_fix event_eq_dec apply rho rho_star valid rho_star_reach
               s0 Hv).
    tauto.
  Qed.

  (* Interleaved convergence implies atomic convergence from the canonical start. *)
  Corollary interleaved_atomic : forall s0,
    (forall B, UN fstep (s0, B)) -> forall B, UN astep (rho_star s0, B).
  Proof. intros s0 H. exact (proj1 (proj1 (atomic_derived_from s0) H)). Qed.
End Split.

(* ============================================================================================ *)
(* The converse fails: atomic convergence without CC2.                                          *)
(* ============================================================================================ *)

(* X = {0, 1, 2} inside nat (only these are produced), valid = {0, 1}, rho s = 0. Events: XF
   sends every state to 2; XE sends 0 and 1 to 0 and 2 to 1. *)
Inductive xev := XF | XE.

Definition xev_eq_dec : forall a b : xev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition x_apply (e : xev) (s : nat) : nat :=
  match e with
  | XF => 2
  | XE => match s with 2 => 1 | _ => 0 end
  end.
Definition x_rho (_ : nat) : nat := 0.
Definition x_valid (s : nat) : Prop := s < 2.
Definition x_Phi (s : nat) : nat := if Nat.ltb s 2 then 0 else 1.
Definition x_rho_star (s : nat) : nat := if Nat.ltb s 2 then s else 0.

(* The interleaved step of cc_exact (free delivery) and the atomic step, for this system. *)
Definition x_fstep := step xev_eq_dec x_apply x_rho x_valid (GovernanceConverse.free_enabled (State:=nat)).
Definition x_astep := astep xev_eq_dec x_apply x_rho_star.

(* The system meets every hypothesis of cc_exact. *)
Lemma x_wfc : forall s, ~ x_valid s -> x_Phi (x_rho s) < x_Phi s.
Proof.
  intros s H. unfold x_valid in H. unfold x_Phi, x_rho. simpl.
  destruct (Nat.ltb_spec s 2); [lia | lia].
Qed.

Lemma x_rho_star_reach : forall s B, star x_fstep (s, B) (x_rho_star s, B).
Proof.
  intros s B. unfold x_rho_star. destruct (Nat.ltb_spec s 2) as [_ | H]; [apply star_refl |].
  apply star_one. apply st_comp. unfold x_valid. lia.
Qed.

Lemma x_rho_star_valid : forall s, x_valid (x_rho_star s).
Proof. intros s. unfold x_valid, x_rho_star. destruct (Nat.ltb_spec s 2); lia. Qed.

Lemma x_greach_zero : forall s, greach x_apply x_rho_star 0 s -> s = 0.
Proof.
  intros s H. induction H as [| e s _ IH]; [reflexivity |]. subst s. destruct e; reflexivity.
Qed.

Lemma x_nf : forall s, x_valid s -> normal_form x_fstep (s, []).
Proof.
  intros s Hv [y H]. inversion H as [s' B e Hin _ E1 E2 | s' B Hinv E1 E2]; subst.
  - destruct Hin.
  - apply Hinv. exact Hv.
Qed.

(* (a) atomic convergence from 0 for every buffer; (b) the interleaved buffer [XF; XE] from 0
   has two normal forms; (c) CC2 fails at the state 2, reachable from 0 and invalid. *)
Theorem atomic_not_descent :
  (forall B, GovernanceConverse.UN x_astep (0, B)) /\
  ~ GovernanceConverse.UN x_fstep (0, [XF; XE]) /\
  (star x_fstep (0, [XF; XE]) (0, []) /\ normal_form x_fstep (0, []) /\
   star x_fstep (0, [XF; XE]) (1, []) /\ normal_form x_fstep (1, [])) /\
  GovernanceConverse.reach x_apply x_rho x_valid 0 2 /\ ~ x_valid 2 /\
  x_rho_star (x_apply XE 2) <> x_rho_star (x_apply XE (x_rho 2)).
Proof.
  assert (S0 : star x_fstep (0, [XF; XE]) (0, [])).
  { eapply star_step; [apply (st_apply _ _ _ _ _ 0 [XF; XE] XF); left; reflexivity |]. simpl.
    eapply star_step; [apply st_comp; unfold x_valid; lia |]. unfold x_rho.
    eapply star_step; [apply (st_apply _ _ _ _ _ 0 [XE] XE); left; reflexivity |]. simpl.
    apply star_refl. }
  assert (S1 : star x_fstep (0, [XF; XE]) (1, [])).
  { eapply star_step; [apply (st_apply _ _ _ _ _ 0 [XF; XE] XF); left; reflexivity |]. simpl.
    eapply star_step; [apply (st_apply _ _ _ _ _ 2 [XE] XE); left; reflexivity |]. simpl.
    apply star_refl. }
  assert (N0 : normal_form x_fstep (0, [])) by (apply x_nf; unfold x_valid; lia).
  assert (N1 : normal_form x_fstep (1, [])) by (apply x_nf; unfold x_valid; lia).
  split; [| split; [| split; [| split; [| split]]]].
  - intros B. apply (proj2 (atomic_exact xev_eq_dec x_apply x_rho_star 0)).
    intros sigma e1 e2 Hs. rewrite (x_greach_zero sigma Hs). destruct e1, e2; reflexivity.
  - intros H. pose proof (H _ _ S0 N0 S1 N1) as E. discriminate E.
  - repeat split; assumption.
  - apply (GovernanceConverse.r_apply x_apply x_rho x_valid 0 XF 0). apply GovernanceConverse.r_init.
  - unfold x_valid. lia.
  - simpl. discriminate.
Qed.

(* The same in the framework's terms: history descent (atomic convergence from rho_star 0 = 0)
   holds, state descent fails, and so does the right side of cc_exact_from. *)
Theorem atomic_not_descent_framework :
  NormalizationDerived.FreeHistoryDescent x_apply x_rho_star 0 /\
  ~ NormalizationDerived.StateDescentReach x_apply x_rho x_rho_star x_valid 0 /\
  ~ (forall B, GovernanceConverse.UN x_fstep (0, B)) /\
  ~ (forall sigma e, GovernanceConverse.reach x_apply x_rho x_valid 0 sigma -> ~ x_valid sigma ->
       x_rho_star (x_apply e sigma) = x_rho_star (x_apply e (x_rho sigma))).
Proof.
  destruct atomic_not_descent as [HA [HU [_ [Hr [Hinv Hne]]]]].
  split; [| split; [| split]].
  - apply (proj2 (atomic_history xev_eq_dec x_apply x_rho_star 0)). exact HA.
  - intros HS. pose proof (HS XE 2 Hr) as E. discriminate E.
  - intros H. apply HU. apply H.
  - intros H. apply Hne. apply H; assumption.
Qed.

(* The split theorem applies to this system and confirms the reading: the interleaved failure is
   all on the state side. *)
Theorem atomic_not_descent_split :
  (forall B, GovernanceConverse.UN x_astep (x_rho_star 0, B)) /\
  ~ (forall B, GovernanceConverse.UN x_fstep (0, B)).
Proof.
  destruct atomic_not_descent as [HA [HU _]]. split; [exact HA |].
  intros H. apply HU. apply H.
Qed.

(* Non-vacuity of the split: on GovernanceConverse.v's one-boolean system (only false valid,
   repair to false) both sides hold. *)
Lemma q_wfc : forall s, ~ GovernanceConverse.q_valid s ->
  GovernanceConverse.q_Phi (GovernanceConverse.q_rho s) < GovernanceConverse.q_Phi s.
Proof. intros [|] H; [simpl; auto | exfalso; apply H; reflexivity]. Qed.

Lemma q_reach : forall s B,
  star GovernanceConverse.q_step (s, B) (GovernanceConverse.q_rho s, B).
Proof.
  intros [|] B.
  - eapply star_step; [apply st_comp; discriminate | apply star_refl].
  - apply star_refl.
Qed.

Theorem atomic_split_nonvacuous :
  (forall B, GovernanceConverse.UN GovernanceConverse.q_step (false, B)) /\
  (forall B, GovernanceConverse.UN
     (astep Bool.bool_dec GovernanceConverse.q_apply GovernanceConverse.q_rho) (false, B)).
Proof.
  assert (A : forall B, GovernanceConverse.UN
     (astep Bool.bool_dec GovernanceConverse.q_apply GovernanceConverse.q_rho) (false, B)).
  { apply (proj2 (atomic_exact Bool.bool_dec GovernanceConverse.q_apply GovernanceConverse.q_rho
                    false)).
    intros sigma e1 e2 _. reflexivity. }
  split; [| exact A].
  apply (proj2 (atomic_derived_valid Bool.bool_dec GovernanceConverse.q_apply
                  GovernanceConverse.q_rho GovernanceConverse.q_rho GovernanceConverse.q_valid
                  GovernanceConverse.q_Phi q_wfc q_reach (fun _ => eq_refl) false eq_refl)).
  split; [exact A | intros sigma e _ _; reflexivity].
Qed.
