(* Federated convergence (monotone cycles), mechanized.

   The federated paper's deepest result, Thm. "Monotone Convergence Despite
   Cycles", says: when shared domains are ordered lattices and the federated
   repair operator Phi is monotone, then - on ANY topology, cycles included - Phi
   has a least fixed point s* obtained by Kleene iteration from bottom, and every
   fair order of component updates converges to the same s*. It is proved from
   Knaster-Tarski plus the convergence of chaotic iteration.

   This file mechanizes the constructive, finite-lattice core the paper relies on
   ("the ascending chain stabilizes for a finite lattice"): for a monotone self-map
   of a partial order with a least element, the Kleene iteration from bottom is
   ascending, and once it stabilizes the stable value is the LEAST fixed point -
   and the least fixed point is unique, which is the order-independence of the
   limit. This avoids the impredicative arbitrary-meet formulation of
   Knaster-Tarski (which would need excluded middle / propositional extensionality),
   so the development stays axiom-free. Checked with Rocq 9.3.

   Scope: this covers existence and Kleene-reachability of the least fixed point
   (the federated normal form, s-star) and its uniqueness. The chaotic-iteration
   result - that every fair ASYNCHRONOUS component-wise schedule reaches s-star, not
   just the synchronous Phi-iteration - is mechanized in Chaotic.v. *)

From Coq Require Import Bool.

Section Fixpoints.
  Context {L : Type}.
  Variable le : L -> L -> Prop.

  (* A partial order: the lattice's underlying order. Antisymmetry yields Leibniz
     equality, as it does in any concrete lattice (e.g. the bool instance below). *)
  Hypothesis le_refl    : forall x, le x x.
  Hypothesis le_trans   : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.

  Variable f : L -> L.
  Hypothesis f_mono : forall x y, le x y -> le (f x) (f y).

  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  Definition fixed_point (x : L) : Prop := f x = x.

  (* Kleene iteration from bottom: iter n = f^n(bot). *)
  Fixpoint iter (n : nat) : L :=
    match n with
    | 0 => bot
    | S k => f (iter k)
    end.

  (* The iteration is an ascending chain. *)
  Lemma iter_ascending : forall n, le (iter n) (iter (S n)).
  Proof.
    induction n as [| n IH].
    - apply bot_least.
    - simpl. apply f_mono. exact IH.
  Qed.

  (* Every fixed point bounds the whole iteration from above (bottom is below
     everything, and monotonicity carries that up the chain). *)
  Lemma iter_below_fixed : forall x, fixed_point x -> forall n, le (iter n) x.
  Proof.
    intros x Hfx. induction n as [| n IH].
    - apply bot_least.
    - simpl. unfold fixed_point in Hfx. rewrite <- Hfx. apply f_mono. exact IH.
  Qed.

  (* "Least fixed point" packaged: fixed, and below every fixed point. *)
  Definition is_lfp (m : L) : Prop :=
    fixed_point m /\ forall x, fixed_point x -> le m x.

  (* Kleene reaches the least fixed point: once the ascending iteration stabilizes
     (f (iter n) = iter n - guaranteed for a finite lattice), iter n IS the least
     fixed point. This is the constructive core of Thm. Monotone-Cycles. *)
  Theorem kleene_lfp :
    forall n, f (iter n) = iter n -> is_lfp (iter n).
  Proof.
    intros n Hstab. split.
    - exact Hstab.
    - intros x Hfx. apply iter_below_fixed. exact Hfx.
  Qed.

  (* Order-independence of the limit: the least fixed point is unique, so however
     it is computed, the federated normal form is the same value. *)
  Theorem lfp_unique : forall m1 m2, is_lfp m1 -> is_lfp m2 -> m1 = m2.
  Proof.
    intros m1 m2 [F1 L1] [F2 L2].
    apply le_antisym; [apply L1; exact F2 | apply L2; exact F1].
  Qed.
End Fixpoints.

(* ============================================================
   Non-vacuity: a concrete finite lattice (bool) with a monotone operator whose
   Kleene iteration stabilizes and reaches the least fixed point. Axiom-free.
   ============================================================ *)

Definition ble (a b : bool) : Prop := implb a b = true.

Lemma ble_refl : forall x, ble x x.
Proof. destruct x; reflexivity. Qed.

Lemma ble_trans : forall x y z, ble x y -> ble y z -> ble x z.
Proof. destruct x, y, z; unfold ble; simpl; intros; try reflexivity; discriminate. Qed.

Lemma ble_antisym : forall x y, ble x y -> ble y x -> x = y.
Proof. destruct x, y; unfold ble; simpl; intros H1 H2; try reflexivity; discriminate. Qed.

Lemma ble_bot_least : forall x, ble false x.
Proof. destruct x; reflexivity. Qed.

(* A monotone operator on bool: constant true (validity-restoring repair that,
   once fired, stays). *)
Definition ftrue (_ : bool) : bool := true.

Lemma ftrue_mono : forall x y, ble x y -> ble (ftrue x) (ftrue y).
Proof. intros; apply ble_refl. Qed.

(* The iteration false, true, true, ... stabilizes at step 1, and that value is
   the least fixed point - computed, no axioms. *)
Example bool_lfp_true :
  is_lfp ble ftrue (iter ftrue false 1).
Proof.
  apply (kleene_lfp ble ftrue ftrue_mono false ble_bot_least 1).
  reflexivity.
Qed.

Example bool_lfp_value : iter ftrue false 1 = true.
Proof. reflexivity. Qed.
