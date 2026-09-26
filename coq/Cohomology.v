(* Cohomology.v: the operational core of the companion's cohomological layer (Sections 5-6),
   mechanized axiom-free. The full nerve / cocycle assembly (H^1 as a quotient, cycle-basis
   generation) stays paper-level; what is mechanized here is the per-cycle content the diagnostic
   computes and the cycle-basis result rests on:

   - Section 5's gluing counterexample: two confluent subsystems with the SAME valid set but
     different normalizers on the shared state glue to an order-dependent (non-confluent) union, so
     agreement on valid values is not enough.
   - Section 6's completion theorem, single-cycle essence: in the invertible fragment each edge acts
     as a group translation, the loop composite is translation by the holonomy, and it has a fixed
     point (a global section closes) iff the holonomy is trivial. So a section exists iff H^1
     vanishes on that cycle.
   - The negation loop as the minimal nonzero obstruction: the flip on {0,1} has no fixed point, so
     the loop orbits and no consistent global assignment exists. *)

From Coq Require Import Lists.List Bool.
Import ListNotations.

(* --------------------------------------------------------------------------- *)
(* Section 5: gluing is not naive. *)

Section GluingCounterexample.
  (* States 0,1,2. rA repairs 1 -> 0, rB repairs 1 -> 2; both fix 0 and 2, so both have valid set
     {0,2} and agree on which values are valid. *)
  Definition rA (n : nat) : nat := match n with 1 => 0 | k => k end.
  Definition rB (n : nat) : nat := match n with 1 => 2 | k => k end.

  Lemma rA_idem : forall n, rA (rA n) = rA n.
  Proof. intro n. destruct n as [|[|[|n]]]; reflexivity. Qed.
  Lemma rB_idem : forall n, rB (rB n) = rB n.
  Proof. intro n. destruct n as [|[|[|n]]]; reflexivity. Qed.

  Lemma agree_on_valid : (rA 0 = 0 /\ rB 0 = 0) /\ (rA 2 = 2 /\ rB 2 = 2).
  Proof. repeat split; reflexivity. Qed.

  Lemma disagree_as_normalizers : rA 1 <> rB 1.
  Proof. cbn. discriminate. Qed.

  (* Yet the union is order-dependent on the shared state: composing the two normalizers in the two
     orders on the value 1 disagrees, so the glued system is non-confluent. *)
  Theorem gluing_order_dependent : rA (rB 1) <> rB (rA 1).
  Proof. cbn. discriminate. Qed.
End GluingCounterexample.

(* --------------------------------------------------------------------------- *)
(* Section 6: the completion theorem for a single cycle, invertible fragment. *)

(* The loop composite of a cycle: apply the edge maps in loop order. A global section around the
   cycle is a start value the loop composite fixes (going around returns to it). *)
Definition loop_composite {S : Type} (edges : list (S -> S)) (s : S) : S :=
  fold_left (fun x f => f x) edges s.

Definition has_section {S : Type} (edges : list (S -> S)) : Prop :=
  exists s, loop_composite edges s = s.

(* In the invertible fragment each edge acts as a group translation, so the loop composite is
   translation by the holonomy (the product of the edge elements). Such a translation has a fixed
   point iff the holonomy is the identity. This is the completion theorem for one cycle: a section
   exists iff the holonomy is trivial. *)
Section InvertibleHolonomy.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.

  Theorem fixed_point_iff_trivial_holonomy :
    forall h, (exists x, op h x = x) <-> h = e.
  Proof.
    intro h. split.
    - intros [x Hx].
      transitivity (op h (op x (inv x))).
      + rewrite inv_r. rewrite id_r. reflexivity.
      + rewrite assoc. rewrite Hx. apply inv_r.
    - intro Hh. exists e. rewrite Hh. apply id_l.
  Qed.
End InvertibleHolonomy.

(* The minimal nonzero obstruction: the shared fiber {0,1} as the group Z/2 under xor, and the
   negation edge is translation by the nontrivial element. Its holonomy is nontrivial, so it has no
   fixed point: the negation loop orbits and admits no global section. *)
Section FlipObstruction.
  Lemma xorb_assoc' : forall a b c, xorb a (xorb b c) = xorb (xorb a b) c.
  Proof. intros a b c; destruct a, b, c; reflexivity. Qed.
  Lemma xorb_id_l : forall a, xorb false a = a. Proof. destruct a; reflexivity. Qed.
  Lemma xorb_id_r : forall a, xorb a false = a. Proof. destruct a; reflexivity. Qed.
  Lemma xorb_inv_r : forall a, xorb a a = false. Proof. destruct a; reflexivity. Qed.

  (* Trivial holonomy (identity edge) settles: a fixed point exists. *)
  Theorem identity_holonomy_has_section : exists x : bool, xorb false x = x.
  Proof.
    apply (fixed_point_iff_trivial_holonomy xorb false (fun x => x)
           xorb_assoc' xorb_id_l xorb_id_r xorb_inv_r false).
    reflexivity.
  Qed.

  (* Nontrivial holonomy (the flip) has no fixed point: the loop orbits. *)
  Theorem flip_no_section : ~ (exists x : bool, xorb true x = x).
  Proof.
    intro H.
    apply (fixed_point_iff_trivial_holonomy xorb false (fun x => x)
           xorb_assoc' xorb_id_l xorb_id_r xorb_inv_r true) in H.
    discriminate H.
  Qed.
End FlipObstruction.

(* --------------------------------------------------------------------------- *)
(* Toward the non-abelian case. The single-cycle criterion above uses no        *)
(* commutativity, so it holds for a non-abelian G. Its multi-loop form is the    *)
(* section criterion for a bouquet of loops (all sharing one shared value): a    *)
(* simultaneous global section exists iff EVERY loop's holonomy is trivial. This  *)
(* is the necessary-and-sufficient content behind the minimal-coordination        *)
(* reading: to make a section exist you must coordinate (drop the constraint of)  *)
(* exactly the loops with non-trivial holonomy. It holds for arbitrary G. What is  *)
(* open, and non-abelian, is the minimum over the whole nerve (spanning-tree      *)
(* choice, shared edges, conjugation), where the count can drop below the         *)
(* cycle-basis size; see CATEGORICAL-STRUCTURE.md, section 10.3. *)
Section SimultaneousSection.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.

  Theorem simultaneous_section_iff : forall gs : list G,
    (exists s, Forall (fun g => op g s = s) gs) <-> Forall (fun g => g = e) gs.
  Proof.
    intro gs. split.
    - intros [s Hs]. apply Forall_forall. intros g Hg.
      apply (proj1 (fixed_point_iff_trivial_holonomy op e inv assoc id_l id_r inv_r g)).
      exists s. rewrite Forall_forall in Hs. apply Hs; exact Hg.
    - intro H. rewrite Forall_forall in H. exists e. apply Forall_forall. intros g Hg.
      rewrite (H g Hg). apply id_l.
  Qed.
End SimultaneousSection.
