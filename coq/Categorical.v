(* Categorical.v: the structural core of the companion paper's federation-as-limit account,
   mechanized at the paper's level of abstraction. The normalizer is an abstract idempotent
   endomap, exactly as Governance.v treats the registry operators abstractly.

   This mechanizes:
   - Lemma 0 (a registry's valid set is the fixed-point set = the image of its idempotent
     normalizer, and that set is the equalizer of id and the normalizer), and
   - the abstract skeleton of Theorem 1 (an idempotent normalizer is a retraction onto that set:
     it lands in the set and fixes it, so it splits the inclusion of the set into the state space).

   Everything is axiom-free. The concrete instance at the end (clamp-to-cap, a genuinely
   collapsing normalizer, mirroring compensation) discharges the idempotence hypothesis with no
   hypotheses of its own, so the results are not vacuous. *)

Section IdempotentRetraction.
  Context {A : Type} (rho : A -> A).
  Hypothesis idem : forall x, rho (rho x) = rho x.

  (* The valid set two ways: fixed points of the normalizer, and its image. *)
  Definition Fixed (x : A) : Prop := rho x = x.
  Definition InImage (x : A) : Prop := exists y, rho y = x.

  (* Lemma 0, part 1: image = fixed points. The forward direction is exactly idempotence. *)
  Lemma image_iff_fixed : forall x, InImage x <-> Fixed x.
  Proof.
    intro x. split.
    - intros [y Hy]. unfold Fixed. rewrite <- Hy. apply idem.
    - intro Hx. exists x. exact Hx.
  Qed.

  (* Lemma 0, part 2: the fixed-point set is the equalizer of id and rho. In Set the equalizer of
     (id, rho) has carrier {x | id x = rho x}; that predicate is Fixed up to symmetry, so the
     fixed-point set IS the equalizer carrier (a limit). *)
  Lemma fixed_is_equalizer : forall x, Fixed x <-> (fun z => z) x = rho x.
  Proof. intro x. unfold Fixed. split; intro H; symmetry; exact H. Qed.

  (* Theorem 1 (abstract skeleton): rho is a retraction onto Fixed.
     (a) rho lands in the fixed set (idempotence); (b) rho fixes the fixed set (definitional).
     Together rho splits the inclusion Fixed -> A, i.e. it is a retraction onto its image, which
     by image_iff_fixed is the limit L = Fixed. *)
  Lemma retract_into_fixed : forall x, Fixed (rho x).
  Proof. intro x. unfold Fixed. apply idem. Qed.

  Lemma retract_fixes_fixed : forall x, Fixed x -> rho x = x.
  Proof. intros x H. exact H. Qed.

  (* Equalizer universal property, axiom-free fragment. Any fork u : Z -> A that already lands in
     Fixed factors through the inclusion, and the factoring A-map is u itself. Full uniqueness into
     the subset type {x | Fixed x} needs proof irrelevance of Fixed (available when A has decidable
     equality, e.g. gsm's finite state types); the computational content, that the mediator's
     underlying values are forced, is axiom-free and stated here. *)
  Section Universal.
    Context {Z : Type} (u : Z -> A).
    Hypothesis u_fixed : forall z, Fixed (u z).

    Lemma mediator_lands_in_fixed : forall z, Fixed (u z).
    Proof. exact u_fixed. Qed.

    Lemma mediator_values_unique :
      forall m : Z -> A,
        (forall z, m z = u z) -> forall z, rho (m z) = m z.
    Proof. intros m Hm z. rewrite Hm. apply u_fixed. Qed.
  End Universal.
End IdempotentRetraction.

(* Non-vacuity: a concrete idempotent normalizer that genuinely collapses (clamp to a cap at 3,
   the shape of a real compensation), so the section's hypothesis is satisfiable and the results
   are about something. Its fixed set is exactly {n | n <= 3}. *)
From Coq Require Import Arith.PeanoNat.

Definition clamp3 (n : nat) : nat := Nat.min n 3.

Lemma clamp3_idem : forall n, clamp3 (clamp3 n) = clamp3 n.
Proof.
  intro n. unfold clamp3.
  apply Nat.min_l. apply Nat.le_min_r.
Qed.

Lemma clamp3_fixed_iff : forall n, Fixed clamp3 n <-> n <= 3.
Proof.
  intro n. unfold Fixed, clamp3. split.
  - intro H. rewrite <- H. apply Nat.le_min_r.
  - intro H. apply Nat.min_l. exact H.
Qed.

(* The abstract retraction results instantiate at clamp3 with no remaining hypotheses: clamp3 is a
   retraction onto {n | n <= 3}. *)
Definition clamp3_retracts_into : forall n, Fixed clamp3 (clamp3 n) :=
  retract_into_fixed clamp3 clamp3_idem.

Definition clamp3_image_iff_fixed : forall x, InImage clamp3 x <-> Fixed clamp3 x :=
  image_iff_fixed clamp3 clamp3_idem.

(* --------------------------------------------------------------------------- *)
(* Proposition 1: the federated consistent set is an equalizer, hence a finite  *)
(* limit in Set. Mechanized at the paper's abstraction level: the targets are a *)
(* finite list, and a target's current shared component and its resolver value  *)
(* are abstract maps sh, res : St -> T -> Sh. The consistent set L_F is the set  *)
(* of federated states where every target's shared component equals its         *)
(* resolver value; the two parallel maps sharedOf, resolvedOf send a state to    *)
(* the tuple (modeled as a list over the targets) of shared components and of    *)
(* resolver values. L_F = eq(sharedOf, resolvedOf). Modeling the product over    *)
(* targets as a list keeps the equalizer characterization axiom-free, with no    *)
(* functional extensionality. *)

From Coq Require Import Lists.List.
Import ListNotations.

(* Pointwise agreement over a finite index list is exactly equality of the two
   list-valued maps: the equalizer of a product is the conjunction of the
   component equalizers. Both directions are structural, axiom-free. *)
Lemma pointwise_to_map {A B : Type} (f h : A -> B) (l : list A) :
  (forall x, In x l -> f x = h x) -> map f l = map h l.
Proof.
  induction l as [|a l IH]; simpl; intro H.
  - reflexivity.
  - f_equal.
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma map_to_pointwise {A B : Type} (f h : A -> B) (l : list A) :
  map f l = map h l -> forall x, In x l -> f x = h x.
Proof.
  induction l as [|a l IH]; simpl; intro Heq.
  - intros x [].
  - injection Heq as Hhd Htl. intros x Hin.
    destruct Hin as [Hx|Hx].
    + rewrite <- Hx. exact Hhd.
    + apply IH; [exact Htl | exact Hx].
Qed.

Section FederatedEqualizer.
  Context {St T Sh : Type}.
  Variable targets : list T.       (* the federation's targets (finite) *)
  Variable sh  : St -> T -> Sh.    (* a target's current shared component *)
  Variable res : St -> T -> Sh.    (* the resolver value from that target's sources *)

  (* The two parallel maps into the product over targets (modeled as a list). *)
  Definition sharedOf   (s : St) : list Sh := map (sh s) targets.
  Definition resolvedOf (s : St) : list Sh := map (res s) targets.

  (* L_F: every target's shared component already equals its resolver value. *)
  Definition Consistent (s : St) : Prop :=
    forall B, In B targets -> sh s B = res s B.

  (* The equalizer of the two maps. *)
  Definition Equalizer (s : St) : Prop := sharedOf s = resolvedOf s.

  (* Proposition 1: the consistent set is exactly the equalizer, so the federated
     normal forms are a finite limit in Set (an equalizer of a product, each factor
     itself the equalizer of Lemma 0). *)
  Theorem consistent_iff_equalizer : forall s, Consistent s <-> Equalizer s.
  Proof.
    intro s. unfold Consistent, Equalizer, sharedOf, resolvedOf. split.
    - apply pointwise_to_map.
    - apply map_to_pointwise.
  Qed.
End FederatedEqualizer.

(* Non-vacuity: a two-target instance where consistency is a genuine constraint
   (the state must be 0), so Proposition 1 is not about an empty or trivial
   equalizer. *)
Example ex_consistent_zero :
  Consistent (true :: false :: nil) (fun (s : nat) (_ : bool) => s) (fun _ _ => 0) 0.
Proof. intros B _. reflexivity. Qed.

Example ex_inconsistent_one :
  ~ Consistent (true :: false :: nil) (fun (s : nat) (_ : bool) => s) (fun _ _ => 0) 1.
Proof. intro H. specialize (H true (or_introl eq_refl)). discriminate H. Qed.
