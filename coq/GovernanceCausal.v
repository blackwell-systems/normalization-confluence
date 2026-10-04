(* GovernanceCausal.v: the Governance Rewrite System's Convergence Theorem under CAUSAL delivery,
   mechanized axiom-free.

   Governance.v proves convergence from WFC and CC, with CC1 (order independence of two events,
   each followed by repair) required for EVERY pair of events. Under causal delivery an event only
   becomes enabled once the events it depends on have been applied, so two causally ordered events
   are never enabled at the same time. This file proves the same Convergence Theorem with CC1
   required only for pairs of DISTINCT events that are enabled TOGETHER, which is strictly weaker:
   the old hypothesis implies the new one, and the witness at the end satisfies the new one while
   violating the old. Termination (WFC), CC2, and the enabledness facts are unchanged.

   The proof is Governance.v's, with the one CC1 use instantiated at the co-enabled pair the
   critical-pair case already has in hand. *)

Require Import NC.Newman.
From Coq Require Import List.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import Wellfounded.Inverse_Image.
From Coq Require Import Lia.
Import ListNotations.

Section GovernanceCausal.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.

  (* The registry's semantic operators, abstract exactly as in the paper. *)
  Variable apply    : Event -> State -> State.  (* apply(e, sigma)             *)
  Variable rho      : State -> State.           (* rho_R: one compensation step *)
  Variable rho_star : State -> State.           (* rho_R^*: iterate to validity *)
  Variable valid    : State -> Prop.            (* V_R(sigma) = top             *)
  Variable Phi      : State -> nat.             (* WFC potential                *)
  Variable enabled  : Event -> State -> list Event -> Prop.

  Definition Config : Type := (State * list Event)%type.

  (* Buffer as a list; |B| is length, B \ {e} removes one occurrence. *)
  Fixpoint remove1 (e : Event) (l : list Event) : list Event :=
    match l with
    | [] => []
    | x :: xs => if event_eq_dec x e then xs else x :: remove1 e xs
    end.

  Lemma remove1_length_in :
    forall e l, In e l -> length (remove1 e l) < length l.
  Proof.
    intros e l. induction l as [| x xs IH]; intros Hin.
    - inversion Hin.
    - simpl in Hin. simpl. destruct (event_eq_dec x e) as [Heq | Hne].
      + simpl. lia.
      + simpl. destruct Hin as [Hx | Hin'].
        * subst x. contradiction.
        * specialize (IH Hin'). lia.
  Qed.

  (* The two rewrite rules (Def. "Governance Rewrite System"). *)
  Inductive step : Config -> Config -> Prop :=
  | st_apply : forall sigma B e,
      In e B -> enabled e sigma B ->
      step (sigma, B) (apply e sigma, remove1 e B)
  | st_comp : forall sigma B,
      ~ valid sigma ->
      step (sigma, B) (rho sigma, B).

  (* ---- Paper conditions, as hypotheses ---- *)

  (* WFC (Axiom "WFC"): compensation strictly decreases the potential. *)
  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.

  (* rho* specification (Def. "Iterated Compensation"): (sigma,B) reduces to
     (rho* sigma, B) by compensation steps. (rho* also reaches a valid state,
     but confluence does not depend on that, so it is not assumed here.) *)
  Hypothesis rho_star_reach : forall sigma B, star step (sigma, B) (rho_star sigma, B).

  (* CC1 (order independence) and CC2 (compensation absorption), Axiom "CC". *)
  (* CC1, required only for distinct events that are enabled together (causal delivery). *)
  Hypothesis cc1_coenabled : forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma))).
  Hypothesis cc2 : forall sigma e,
      ~ valid sigma ->
      rho_star (apply e sigma) = rho_star (apply e (rho sigma)).

  (* Enabledness persistence, exactly the two facts the paper's Local
     Confluence proof invokes: after applying+compensating the other event
     (removing it from B), a distinct enabled event stays enabled; and
     compensation (which does not change B) preserves enabledness. *)
  Hypothesis enabled_after_remove :
    forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (remove1 e1 B) /\ enabled e2 (rho_star (apply e1 sigma)) (remove1 e1 B).
  Hypothesis enabled_after_comp :
    forall sigma B e,
      enabled e sigma B -> enabled e (rho sigma) B.

  Lemma remove1_comm :
    forall e1 e2 l, remove1 e2 (remove1 e1 l) = remove1 e1 (remove1 e2 l).
  Proof.
    intros e1 e2 l. induction l as [| x xs IH]; simpl; [reflexivity|].
    destruct (event_eq_dec x e1) as [E1 | N1]; destruct (event_eq_dec x e2) as [E2 | N2];
      subst; simpl;
      repeat match goal with
             | [ |- context[event_eq_dec ?a ?b] ] => destruct (event_eq_dec a b); subst; simpl
             end;
      try reflexivity; try congruence; try (rewrite IH; reflexivity).
  Qed.

  (* ================= Termination (Lemma "Termination") ================= *)

  Definition ltlex (p q : nat * nat) : Prop :=
    fst p < fst q \/ (fst p = fst q /\ snd p < snd q).

  Lemma wf_ltlex : well_founded ltlex.
  Proof.
    intros [a b]. revert b.
    induction a as [a IHa] using (well_founded_induction lt_wf).
    intros b. induction b as [b IHb] using (well_founded_induction lt_wf).
    constructor. intros [a' b'] [Hlt | [Heq Hlt]]; simpl in *.
    - apply IHa; exact Hlt.
    - subst a'. apply IHb; exact Hlt.
  Qed.

  Definition measure (c : Config) : nat * nat := (length (snd c), Phi (fst c)).

  Lemma step_decreases : forall c c', step c c' -> ltlex (measure c') (measure c).
  Proof.
    intros c c' Hstep. destruct Hstep as [sigma B e Hin Hen | sigma B Hinv]; unfold measure, ltlex; simpl.
    - left. apply remove1_length_in; exact Hin.
    - right. split; [reflexivity | apply wfc; exact Hinv].
  Qed.

  Theorem terminating : forall c, SN step c.
  Proof.
    (* SN step c = Acc (fun a b => step b a) c: every reduct is accessible. *)
    assert (Hwf : well_founded (fun c c' => ltlex (measure c) (measure c'))).
    { apply (Wellfounded.Inverse_Image.wf_inverse_image _ _ ltlex measure wf_ltlex). }
    intros c. specialize (Hwf c).
    induction Hwf as [c _ IH].
    constructor. intros c' Hstep. apply IH. apply step_decreases; exact Hstep.
  Qed.

  (* ================= Local Confluence (Lemma "Local Confluence") ======= *)

  (* From (sigma, B), applying an enabled e and compensating reaches
     (rho_star (apply e sigma), remove1 e B) in the rewrite system. *)
  Lemma apply_then_normalize :
    forall sigma B e,
      In e B -> enabled e sigma B ->
      star step (sigma, B) (rho_star (apply e sigma), remove1 e B).
  Proof.
    intros sigma B e Hin Hen.
    eapply star_step.
    - apply st_apply; [exact Hin | exact Hen].
    - apply rho_star_reach.
  Qed.

  Theorem causal_locally_confluent_step : locally_confluent step.
  Proof.
    intros [sigma B] X1 X2 H1 H2.
    inversion H1 as [sigma1 B1 e1 Hin1 Hen1 EA1 EB1 | sigma1 B1 Hinv1 EA1 EB1]; subst.
    - (* first move: apply e1 *)
      inversion H2 as [sigma2 B2 e2 Hin2 Hen2 EA2 EB2 | sigma2 B2 Hinv2 EA2 EB2]; subst.
      + (* Case 1: two apply steps *)
        destruct (event_eq_dec e1 e2) as [->|Hne].
        * (* same event: identical successors *)
          exists (apply e2 sigma, remove1 e2 B). split; apply star_refl.
        * (* distinct events, close by CC1 *)
          destruct (enabled_after_remove sigma B e1 e2 Hen1 Hen2 Hne) as [Hin2' Hen2'].
          destruct (enabled_after_remove sigma B e2 e1 Hen2 Hen1 (fun H => Hne (eq_sym H))) as [Hin1' Hen1'].
          exists (rho_star (apply e2 (rho_star (apply e1 sigma))), remove1 e2 (remove1 e1 B)).
          split.
          -- (* from X1 = (apply e1 sigma, remove1 e1 B) *)
             eapply star_trans; [apply rho_star_reach|].
             apply apply_then_normalize; [exact Hin2' | exact Hen2'].
          -- (* from X2 = (apply e2 sigma, remove1 e2 B), then CC1 + remove1_comm *)
             rewrite (cc1_coenabled sigma B e1 e2 Hen1 Hen2 Hne). rewrite remove1_comm.
             eapply star_trans; [apply rho_star_reach|].
             apply apply_then_normalize; [exact Hin1' | exact Hen1'].
      + (* Case 2: apply (X1) vs compensation (X2), close by CC2 *)
        exists (rho_star (apply e1 sigma), remove1 e1 B). split.
        * apply rho_star_reach.
        * (* X2 = (rho sigma, B): apply e1 (still enabled), normalize; CC2 *)
          rewrite (cc2 sigma e1 Hinv2).
          apply apply_then_normalize.
          -- exact Hin1.
          -- apply enabled_after_comp; exact Hen1.
    - (* first move: compensation *)
      inversion H2 as [sigma2 B2 e2 Hin2 Hen2 EA2 EB2 | sigma2 B2 Hinv2 EA2 EB2]; subst.
      + (* Case 2 mirrored: compensation (X1) vs apply (X2) *)
        exists (rho_star (apply e2 sigma), remove1 e2 B). split.
        * rewrite (cc2 sigma e2 Hinv1).
          apply apply_then_normalize.
          -- exact Hin2.
          -- apply enabled_after_comp; exact Hen2.
        * apply rho_star_reach.
      + (* Case 3: two compensation steps, identical successor *)
        exists (rho sigma, B). split; apply star_refl.
  Qed.

  (* ================= Convergence (Main Result) ======================== *)

  Theorem causal_governance_confluent : confluent step.
  Proof.
    apply confluent_of_SN.
    - exact causal_locally_confluent_step.
    - exact terminating.
  Qed.

  Theorem causal_governance_unique_normal_forms :
    forall c n1 n2,
      star step c n1 -> normal_form step n1 ->
      star step c n2 -> normal_form step n2 ->
      n1 = n2.
  Proof.
    intros c n1 n2 S1 NF1 S2 NF2.
    eapply unique_normal_forms; try eassumption.
    exact causal_governance_confluent.
  Qed.

End GovernanceCausal.

(* ============================================================
   Witness: strictly beyond Governance.v. A flag with two events, add (true) and remove (false).
   Remove is only enabled once add has been applied (its causal predecessor has left the buffer),
   so the two are never enabled together. Every hypothesis of causal_governance_confluent is
   discharged with no axioms, while the all-pairs CC1 of Governance.v is false for this system:
   add and remove do not commute. Axiom-free.
   ============================================================ *)

From Coq Require Import Bool.

Definition cw_eq_dec := Bool.bool_dec.
Definition cw_apply (e : bool) (_ : bool) : bool := e.     (* add sets true, remove sets false *)
Definition cw_rho (s : bool) : bool := s.                  (* compensation-free *)
Definition cw_valid (_ : bool) : Prop := True.
Definition cw_Phi (_ : bool) : nat := 0.
Definition cw_enabled (e : bool) (_ : bool) (B : list bool) : Prop :=
  In e B /\ (e = false -> ~ In true B).                     (* remove waits for add *)

Definition cw_step :=
  step (State:=bool) (Event:=bool) cw_eq_dec cw_apply cw_rho cw_valid cw_enabled.

Lemma cw_not_coenabled :
  forall s B e1 e2, cw_enabled e1 s B -> cw_enabled e2 s B -> e1 <> e2 -> False.
Proof.
  intros s B e1 e2 [H1 R1] [H2 R2] Hne.
  destruct e1, e2; try (apply Hne; reflexivity).
  - apply (R2 eq_refl). exact H1.
  - apply (R1 eq_refl). exact H2.
Qed.

Definition cw_confluent : confluent cw_step :=
  @causal_governance_confluent bool bool cw_eq_dec cw_apply cw_rho cw_rho cw_valid cw_Phi cw_enabled
    (fun s Hinv => False_ind _ (Hinv I))
    (fun s B => star_refl _ (s, B))
    (fun s B e1 e2 H1 H2 Hne => False_ind _ (cw_not_coenabled s B e1 e2 H1 H2 Hne))
    (fun s e Hinv => False_ind _ (Hinv I))
    (fun s B e1 e2 H1 H2 Hne => False_ind _ (cw_not_coenabled s B e1 e2 H1 H2 Hne))
    (fun s B e H => H).

(* The all-pairs CC1 that Governance.v requires fails here: add and remove do not commute. *)
Theorem cw_violates_all_pairs_cc1 :
  ~ (forall s e1 e2,
       cw_rho (cw_apply e2 (cw_rho (cw_apply e1 s))) = cw_rho (cw_apply e1 (cw_rho (cw_apply e2 s)))).
Proof. intro H. specialize (H false true false). discriminate H. Qed.
