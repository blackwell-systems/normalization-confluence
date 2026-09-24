(* Defensibility checks for the mechanized confluence proof.

   A proof that merely COMPILES can still be weak in ways coqc does not catch:
     (1) vacuous hypotheses  - if no model satisfies the assumptions, the theorem
         is about nothing;
     (2) a non-discriminating conclusion - if `confluent` were provable for every
         relation, proving it would say nothing.
   This file rules both out. It exhibits a concrete registry that satisfies every
   hypothesis of governance_confluent with NO axioms (so the theorem is not
   vacuous and yields an unconditional confluence result), shows the instance has
   genuine nondeterminism (a real peak that must be joined), and proves a concrete
   relation for which `confluent` is FALSE (so the predicate is discriminating). *)

Require Import NC.Newman.
Require Import NC.Governance.
From Stdlib Require Import List Lia Bool.
Import ListNotations.

(* =====================================================================
   1. A concrete registry satisfying every condition (non-vacuity).

   State = nat is a count of outstanding invariant violations ("repair debt").
   An event may add debt (apply e s = S s); compensation clears one unit
   (rho = pred); a state is valid when debt is zero; rho* fully repairs to the
   canonical valid state 0. Enabled means "in the buffer". This is a real
   state-determined-compensation registry, exactly the design the paper's
   examples use, and it satisfies WFC and CC.
   ===================================================================== *)

Definition eq_dec := Bool.bool_dec.        (* Event = bool: two distinct events *)
Definition apply_ (e : bool) (s : nat) : nat := S s.
Definition rho_ (s : nat) : nat := Nat.pred s.
Definition rhostar_ (s : nat) : nat := 0.
Definition valid_ (s : nat) : Prop := s = 0.
Definition Phi_ (s : nat) : nat := s.
Definition enabled_ (e : bool) (s : nat) (B : list bool) : Prop := In e B.

Definition step_ := step (State:=nat) (Event:=bool) eq_dec apply_ rho_ valid_ enabled_.

Lemma in_remove1_neq :
  forall (x e : bool) l, In x l -> x <> e -> In x (remove1 eq_dec e l).
Proof.
  intros x e l. induction l as [| y ys IH]; simpl; intros Hin Hne.
  - exact Hin.
  - destruct (eq_dec y e) as [->|Hye].
    + destruct Hin as [->|Hin']; [contradiction | exact Hin'].
    + destruct Hin as [->|Hin']; simpl; [left; reflexivity | right; apply IH; assumption].
Qed.

Lemma ex_wfc : forall s, ~ valid_ s -> Phi_ (rho_ s) < Phi_ s.
Proof. intros [|n] H; unfold valid_ in H; [contradiction | unfold Phi_, rho_; simpl; lia]. Qed.

Lemma ex_reach : forall s B, star step_ (s, B) (rhostar_ s, B).
Proof.
  intros s B. unfold rhostar_. induction s as [| n IH].
  - apply star_refl.
  - eapply star_step.
    + apply st_comp. unfold valid_. discriminate.
    + exact IH.
Qed.

Lemma ex_cc1 :
  forall s e1 e2,
    rhostar_ (apply_ e2 (rhostar_ (apply_ e1 s))) =
    rhostar_ (apply_ e1 (rhostar_ (apply_ e2 s))).
Proof. reflexivity. Qed.

Lemma ex_cc2 :
  forall s e, ~ valid_ s -> rhostar_ (apply_ e s) = rhostar_ (apply_ e (rho_ s)).
Proof. reflexivity. Qed.

Lemma ex_ear :
  forall s B e1 e2,
    enabled_ e1 s B -> enabled_ e2 s B -> e1 <> e2 ->
    In e2 (remove1 eq_dec e1 B) /\ enabled_ e2 (rhostar_ (apply_ e1 s)) (remove1 eq_dec e1 B).
Proof.
  intros s B e1 e2 H1 H2 Hne. unfold enabled_ in *.
  assert (In e2 (remove1 eq_dec e1 B)) by (apply in_remove1_neq; [exact H2 | congruence]).
  split; assumption.
Qed.

Lemma ex_eac :
  forall s B e, enabled_ e s B -> enabled_ e (rho_ s) B.
Proof. unfold enabled_. intros; assumption. Qed.

(* The payoff: an UNCONDITIONAL confluence result for the concrete system,
   obtained by discharging every hypothesis. No axioms, no admits. *)
Definition example_confluent : confluent step_ :=
  @governance_confluent nat bool eq_dec apply_ rho_ rhostar_ valid_ Phi_ enabled_
    ex_wfc ex_reach ex_cc1 ex_cc2 ex_ear ex_eac.

Definition example_unique_nf :
  forall c n1 n2,
    star step_ c n1 -> normal_form step_ n1 ->
    star step_ c n2 -> normal_form step_ n2 ->
    n1 = n2 :=
  @governance_unique_normal_forms nat bool eq_dec apply_ rho_ rhostar_ valid_ Phi_ enabled_
    ex_wfc ex_reach ex_cc1 ex_cc2 ex_ear ex_eac.

(* The instance genuinely branches: from (1, [true; false]) with debt, all three
   rules fire (apply true, apply false, compensate) to DISTINCT successors, so the
   confluence result above is closing real nondeterminism, not a degenerate system. *)
Example instance_has_a_real_peak :
  step_ (1, [true; false]) (apply_ true 1, remove1 eq_dec true [true; false]) /\
  step_ (1, [true; false]) (apply_ false 1, remove1 eq_dec false [true; false]) /\
  step_ (1, [true; false]) (rho_ 1, [true; false]).
Proof.
  repeat split.
  - apply st_apply; [simpl; left; reflexivity | unfold enabled_; simpl; left; reflexivity].
  - apply st_apply; [simpl; right; left; reflexivity | unfold enabled_; simpl; right; left; reflexivity].
  - apply st_comp. unfold valid_. discriminate.
Qed.

(* =====================================================================
   2. `confluent` is discriminating: a concrete NON-confluent relation.
   Without this, "we proved confluent" could be empty if the predicate were
   provable for everything. It is not.
   ===================================================================== *)

Inductive tri := TA | TB | TC.

Definition Rtri (x y : tri) : Prop :=
  (x = TA /\ y = TB) \/ (x = TA /\ y = TC).

Lemma tri_TB_nf : normal_form Rtri TB.
Proof. intros [y Hy]. destruct Hy as [[H _]|[H _]]; discriminate. Qed.

Lemma tri_TC_nf : normal_form Rtri TC.
Proof. intros [y Hy]. destruct Hy as [[H _]|[H _]]; discriminate. Qed.

Lemma not_confluent_tri : ~ confluent Rtri.
Proof.
  intros CONF.
  assert (SB : star Rtri TA TB) by (eapply star_step; [left; split; reflexivity | apply star_refl]).
  assert (SC : star Rtri TA TC) by (eapply star_step; [right; split; reflexivity | apply star_refl]).
  destruct (CONF TA TB TC SB SC) as [w [HBw HCw]].
  assert (TB = w) by (apply (star_from_nf Rtri); [apply tri_TB_nf | exact HBw]).
  assert (TC = w) by (apply (star_from_nf Rtri); [apply tri_TC_nf | exact HCw]).
  subst. discriminate.
Qed.
