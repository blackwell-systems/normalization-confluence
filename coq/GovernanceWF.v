(* GovernanceWF.v: the Convergence Theorem with Well-Founded Compensation over an ARBITRARY
   well-founded order, mechanized axiom-free.

   Governance.v proves convergence with a natural-number potential (Phi : State -> nat, WFC:
   Phi (rho sigma) < Phi sigma). Nothing in the proof needs the potential to be a natural number:
   termination only needs the lexicographic measure (|B|, Phi sigma) to be well-founded, and a
   lexicographic product of well-founded orders is well-founded. This file states WFC for a
   potential into any type P with any well-founded strict order ltP (ordinals, lexicographic
   products, integers bounded below, ...) and proves:
     - termination of the Governance Rewrite System (lexicographic on |B| and the potential),
     - confluence and unique normal forms (local confluence is Governance.v's own lemma, which
       never uses the potential; Newman.v closes the argument),
   for both the all-pairs CC system (Governance.v) and the causal system (GovernanceCausal.v).
   The variant "compensation is itself well-founded" (no potential at all) is the instance
   P = State, Phi = identity. The nat-valued theorems are recovered as corollaries (P = nat, lt).

   Non-vacuity on an infinite domain: a withdrawal registry on the unbounded state space Z (an
   integer balance, repair raises an overdraft by one toward the floor 0), with an integer-valued
   potential under the well-founded order Zwf 0, discharges every hypothesis. *)

Require Import NC.Newman NC.Governance NC.GovernanceCausal.
From Coq Require Import List.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import Wellfounded.Inverse_Image.
From Coq Require Import Lia.
From Coq Require Import ZArith.
From Coq Require Import ZArith.Zwf.
Import ListNotations.

(* ===================== Lexicographic products of well-founded orders ===================== *)

Section Lex.
  Context {A B : Type}.
  Variable RA : A -> A -> Prop.
  Variable RB : B -> B -> Prop.

  Definition lex2 (p q : A * B) : Prop :=
    RA (fst p) (fst q) \/ (fst p = fst q /\ RB (snd p) (snd q)).

  Theorem wf_lex2 : well_founded RA -> well_founded RB -> well_founded lex2.
  Proof.
    intros WA WB [a b]. revert b.
    pose proof (WA a) as Ha. induction Ha as [a _ IHa].
    intros b. pose proof (WB b) as Hb. induction Hb as [b _ IHb].
    constructor. intros [a' b'] [H | [E H]]; simpl in *.
    - apply IHa; exact H.
    - subst a'. apply IHb; exact H.
  Qed.
End Lex.

(* ===================== Generic termination ===================== *)

(* Any relation on configurations that lowers the measure (|B|, Phi sigma) lexicographically,
   with Phi valued in a well-founded order, is terminating. Shared by both rewrite systems. *)
Section Termination.
  Context {State Event : Type}.
  Variable P : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.

  Definition wf_measure (c : State * list Event) : nat * P := (length (snd c), Phi (fst c)).

  Lemma SN_of_lex_decrease :
    forall R : State * list Event -> State * list Event -> Prop,
      (forall c c', R c c' -> lex2 lt ltP (wf_measure c') (wf_measure c)) ->
      forall c, SN R c.
  Proof.
    intros R Hdec.
    assert (Hwf : well_founded (fun c c' => lex2 lt ltP (wf_measure c) (wf_measure c'))).
    { apply (wf_inverse_image _ _ (lex2 lt ltP) wf_measure). apply wf_lex2; [exact lt_wf | exact wf_ltP]. }
    intros c. specialize (Hwf c). induction Hwf as [c _ IH].
    constructor. intros c' Hstep. apply IH. apply Hdec; exact Hstep.
  Qed.
End Termination.

(* ===================== All-pairs CC (Governance.v's system) ===================== *)

Section GovernanceWF.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.

  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.

  (* The potential lives in an arbitrary type with an arbitrary well-founded strict order. *)
  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (Governance.remove1 event_eq_dec).

  (* WFC over a well-founded order. *)
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).

  Hypothesis rho_star_reach : forall sigma B, star gstep (sigma, B) (rho_star sigma, B).
  Hypothesis cc1 : forall sigma e1 e2,
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

  Lemma wf_step_decreases :
    forall c c', gstep c c' -> lex2 lt ltP (wf_measure P Phi c') (wf_measure P Phi c).
  Proof.
    intros c c' Hstep.
    destruct Hstep as [sigma B e Hin Hen | sigma B Hinv]; unfold wf_measure, lex2; simpl.
    - left. apply Governance.remove1_length_in; exact Hin.
    - right. split; [reflexivity | apply wfc_wf; exact Hinv].
  Qed.

  Theorem governance_wf_terminating : forall c, SN gstep c.
  Proof. apply (SN_of_lex_decrease P ltP wf_ltP Phi). exact wf_step_decreases. Qed.

  Theorem governance_wf_confluent : confluent gstep.
  Proof.
    apply confluent_of_SN.
    - exact (Governance.locally_confluent_step event_eq_dec apply rho rho_star valid enabled
               rho_star_reach cc1 cc2 enabled_after_remove enabled_after_comp).
    - exact governance_wf_terminating.
  Qed.

  Theorem governance_wf_unique_normal_forms :
    forall c n1 n2,
      star gstep c n1 -> normal_form gstep n1 ->
      star gstep c n2 -> normal_form gstep n2 ->
      n1 = n2.
  Proof.
    intros c n1 n2 S1 NF1 S2 NF2.
    eapply unique_normal_forms; try eassumption. exact governance_wf_confluent.
  Qed.
End GovernanceWF.

(* ===================== Causal CC (GovernanceCausal.v's system) ===================== *)

Section GovernanceCausalWF.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.

  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.

  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.

  Local Notation cstep := (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).

  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).
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

  Theorem causal_governance_wf_terminating : forall c, SN cstep c.
  Proof.
    apply (SN_of_lex_decrease P ltP wf_ltP Phi).
    intros c c' Hstep.
    destruct Hstep as [sigma B e Hin Hen | sigma B Hinv]; unfold wf_measure, lex2; simpl.
    - left. apply GovernanceCausal.remove1_length_in; exact Hin.
    - right. split; [reflexivity | apply wfc_wf; exact Hinv].
  Qed.

  Theorem causal_governance_wf_confluent : confluent cstep.
  Proof.
    apply confluent_of_SN.
    - exact (GovernanceCausal.causal_locally_confluent_step event_eq_dec apply rho rho_star valid
               enabled rho_star_reach cc1_coenabled cc2 enabled_after_remove enabled_after_comp).
    - exact causal_governance_wf_terminating.
  Qed.

  Theorem causal_governance_wf_unique_normal_forms :
    forall c n1 n2,
      star cstep c n1 -> normal_form cstep n1 ->
      star cstep c n2 -> normal_form cstep n2 ->
      n1 = n2.
  Proof.
    intros c n1 n2 S1 NF1 S2 NF2.
    eapply unique_normal_forms; try eassumption. exact causal_governance_wf_confluent.
  Qed.
End GovernanceCausalWF.

(* ===================== Corollaries: the special cases ===================== *)

Section Corollaries.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).

  Hypothesis cc2 : forall sigma e,
      ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma)).
  Hypothesis enabled_after_comp :
    forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  (* No potential at all: compensation itself is well-founded (no infinite run of repairs
     through invalid states). Instance P = State, Phi = identity. *)
  Corollary governance_comp_wf_confluent :
    well_founded (fun s' s => ~ valid s /\ s' = rho s) ->
      (forall sigma B, star gstep (sigma, B) (rho_star sigma, B)) ->
      (forall sigma e1 e2,
          rho_star (apply e2 (rho_star (apply e1 sigma)))
        = rho_star (apply e1 (rho_star (apply e2 sigma)))) ->
      (forall sigma B e1 e2,
          enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
          In e2 (Governance.remove1 event_eq_dec e1 B)
          /\ enabled e2 (rho_star (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
      confluent gstep.
  Proof.
    intros Hwf reach cc1 ear.
    apply (governance_wf_confluent event_eq_dec apply rho rho_star valid enabled State
             (fun s' s => ~ valid s /\ s' = rho s) Hwf (fun s => s)); try assumption.
    intros sigma Hinv. split; [exact Hinv | reflexivity].
  Qed.

  (* A potential into a lexicographic product of two well-founded orders. *)
  Corollary governance_lex_confluent :
    forall (P1 P2 : Type) (lt1 : P1 -> P1 -> Prop) (lt2 : P2 -> P2 -> Prop)
           (Phi : State -> P1 * P2),
      well_founded lt1 -> well_founded lt2 ->
      (forall sigma, ~ valid sigma -> lex2 lt1 lt2 (Phi (rho sigma)) (Phi sigma)) ->
      (forall sigma B, star gstep (sigma, B) (rho_star sigma, B)) ->
      (forall sigma e1 e2,
          rho_star (apply e2 (rho_star (apply e1 sigma)))
        = rho_star (apply e1 (rho_star (apply e2 sigma)))) ->
      (forall sigma B e1 e2,
          enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
          In e2 (Governance.remove1 event_eq_dec e1 B)
          /\ enabled e2 (rho_star (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
      confluent gstep.
  Proof.
    intros P1 P2 lt1 lt2 Phi W1 W2 wfc reach cc1 ear.
    exact (governance_wf_confluent event_eq_dec apply rho rho_star valid enabled (P1 * P2)
             (lex2 lt1 lt2) (wf_lex2 lt1 lt2 W1 W2) Phi wfc reach cc1 cc2 ear enabled_after_comp).
  Qed.
End Corollaries.

(* Governance.v's nat-valued Convergence Theorem, recovered with P = nat, ltP = lt. The statement
   is the type of Governance.governance_confluent, argument for argument (checked below). *)
Corollary governance_confluent_from_wf :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho rho_star : State -> State) (valid : State -> Prop)
    (Phi : State -> nat) (enabled : Event -> State -> list Event -> Prop),
  (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
  (forall sigma B, star (Governance.step event_eq_dec apply rho valid enabled)
                        (sigma, B) (rho_star sigma, B)) ->
  (forall sigma e1 e2,
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma)))) ->
  (forall sigma e, ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma))) ->
  (forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (Governance.remove1 event_eq_dec e1 B)
      /\ enabled e2 (rho_star (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
  (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
  confluent (Governance.step event_eq_dec apply rho valid enabled).
Proof.
  intros State Event dec apply rho rho_star valid Phi enabled wfc reach cc1 cc2 ear eac.
  exact (governance_wf_confluent dec apply rho rho_star valid enabled nat lt lt_wf Phi
           wfc reach cc1 cc2 ear eac).
Qed.

(* GovernanceCausal.v's nat-valued causal theorem, recovered the same way. *)
Corollary causal_governance_confluent_from_wf :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho rho_star : State -> State) (valid : State -> Prop)
    (Phi : State -> nat) (enabled : Event -> State -> list Event -> Prop),
  (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
  (forall sigma B, star (GovernanceCausal.step event_eq_dec apply rho valid enabled)
                        (sigma, B) (rho_star sigma, B)) ->
  (forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma)))) ->
  (forall sigma e, ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma))) ->
  (forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (GovernanceCausal.remove1 event_eq_dec e1 B)
      /\ enabled e2 (rho_star (apply e1 sigma)) (GovernanceCausal.remove1 event_eq_dec e1 B)) ->
  (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
  confluent (GovernanceCausal.step event_eq_dec apply rho valid enabled).
Proof.
  intros State Event dec apply rho rho_star valid Phi enabled wfc reach cc1 cc2 ear eac.
  exact (causal_governance_wf_confluent dec apply rho rho_star valid enabled nat lt lt_wf Phi
           wfc reach cc1 cc2 ear eac).
Qed.

(* The recovered statements are the original statements (the two types unify syntactically). *)
Goal True.
Proof.
  let t1 := type of @Governance.governance_confluent in
  let t2 := type of @governance_confluent_from_wf in unify t1 t2.
  let t1 := type of @GovernanceCausal.causal_governance_confluent in
  let t2 := type of @causal_governance_confluent_from_wf in unify t1 t2.
  exact I.
Qed.

(* ============================================================
   Non-vacuity on an infinite domain: a withdrawal registry on Z.

   State  = Z, an integer balance (unbounded in both directions).
   Event  = nat, a withdrawal of that amount: apply n s = s - n.
   valid  = 0 <= s (no overdraft); repair rho s = s + 1 (one unit of overdraft is covered);
   rho*   = max s 0; enabled e s B = e is pending in B.
   Potential: Phi s = -s in Z, under Zwf 0 (x below y when 0 <= y and x < y), a well-founded
   order on an infinite type that is not the natural numbers. Every hypothesis of
   governance_wf_confluent is discharged below, with no axioms.
   ============================================================ *)

Open Scope Z_scope.

Definition zw_apply (n : nat) (s : Z) : Z := s - Z.of_nat n.
Definition zw_rho (s : Z) : Z := s + 1.
Definition zw_rho_star (s : Z) : Z := Z.max s 0.
Definition zw_valid (s : Z) : Prop := 0 <= s.
Definition zw_enabled (e : nat) (_ : Z) (B : list nat) : Prop := In e B.
Definition zw_Phi (s : Z) : Z := - s.

Local Notation zw_step := (Governance.step Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).

Lemma zw_wfc : forall s, ~ zw_valid s -> Zwf 0 (zw_Phi (zw_rho s)) (zw_Phi s).
Proof. unfold zw_valid, zw_Phi, zw_rho, Zwf; intros; lia. Qed.

Lemma zw_rho_star_reach :
  forall s B, star zw_step (s, B) (zw_rho_star s, B).
Proof.
  assert (H : forall (n : nat) s B, Z.to_nat (- s) = n -> star zw_step (s, B) (zw_rho_star s, B)).
  { induction n as [| n IH]; intros s B Hn; unfold zw_rho_star.
    - replace (Z.max s 0) with s by lia. apply star_refl.
    - destruct (Z_le_gt_dec 0 s) as [Hv | Hinv].
      + replace (Z.max s 0) with s by lia. apply star_refl.
      + eapply star_step.
        * apply Governance.st_comp. unfold zw_valid. lia.
        * replace (Z.max s 0) with (Z.max (zw_rho s) 0) by (unfold zw_rho; lia).
          apply IH. unfold zw_rho. lia. }
  intros s B. apply (H (Z.to_nat (- s))). reflexivity.
Qed.

Lemma zw_cc1 : forall s e1 e2,
    zw_rho_star (zw_apply e2 (zw_rho_star (zw_apply e1 s)))
  = zw_rho_star (zw_apply e1 (zw_rho_star (zw_apply e2 s))).
Proof. intros; unfold zw_rho_star, zw_apply; lia. Qed.

Lemma zw_cc2 : forall s e,
    ~ zw_valid s -> zw_rho_star (zw_apply e s) = zw_rho_star (zw_apply e (zw_rho s)).
Proof. intros s e H; unfold zw_valid in H; unfold zw_rho_star, zw_apply, zw_rho; lia. Qed.

Lemma in_remove1_neq :
  forall (e1 e2 : nat) B, In e2 B -> e1 <> e2 -> In e2 (Governance.remove1 Nat.eq_dec e1 B).
Proof.
  intros e1 e2 B. induction B as [| x xs IH]; intros Hin Hne; [inversion Hin|].
  simpl. destruct (Nat.eq_dec x e1) as [-> | Hx].
  - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
  - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
Qed.

Lemma zw_enabled_after_remove :
  forall s B e1 e2,
    zw_enabled e1 s B -> zw_enabled e2 s B -> e1 <> e2 ->
    In e2 (Governance.remove1 Nat.eq_dec e1 B)
    /\ zw_enabled e2 (zw_rho_star (zw_apply e1 s)) (Governance.remove1 Nat.eq_dec e1 B).
Proof.
  intros s B e1 e2 _ H2 Hne. unfold zw_enabled.
  split; apply in_remove1_neq; assumption.
Qed.

Lemma zw_enabled_after_comp :
  forall s B e, zw_enabled e s B -> zw_enabled e (zw_rho s) B.
Proof. unfold zw_enabled; auto. Qed.

(* The Z withdrawal registry is confluent with unique normal forms, by the generalized theorem
   with an integer-valued potential. *)
Theorem zw_confluent : confluent zw_step.
Proof.
  exact (governance_wf_confluent Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled
           Z (Zwf 0) (Zwf_well_founded 0) zw_Phi zw_wfc zw_rho_star_reach zw_cc1 zw_cc2
           zw_enabled_after_remove zw_enabled_after_comp).
Qed.

Theorem zw_unique_normal_forms :
  forall c n1 n2,
    star zw_step c n1 -> normal_form zw_step n1 ->
    star zw_step c n2 -> normal_form zw_step n2 ->
    n1 = n2.
Proof.
  exact (governance_wf_unique_normal_forms Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid
           zw_enabled Z (Zwf 0) (Zwf_well_founded 0) zw_Phi zw_wfc zw_rho_star_reach zw_cc1 zw_cc2
           zw_enabled_after_remove zw_enabled_after_comp).
Qed.

(* The instance uses the whole unbounded domain: an overdraft of any depth is a legitimate start
   state, and it repairs to the floor 0 (so no finite bound on the number of repair steps holds
   uniformly over the state space). *)
Lemma zw_any_overdraft_repairs :
  forall (s : Z) B, s < 0 -> star zw_step (s, B) (0, B).
Proof.
  intros s B Hs. replace 0 with (zw_rho_star s) by (unfold zw_rho_star; lia).
  apply zw_rho_star_reach.
Qed.

Close Scope Z_scope.
