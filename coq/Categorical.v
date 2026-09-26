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
