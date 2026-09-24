(* Soundness of gsm's WFC and CC certification, mechanized.

   gsm (the reference implementation) does not merely happen to satisfy the
   paper's conditions - it VERIFIES them at build time and refuses to build a
   machine that fails (Registry.Build in verify.go sets rep.WFC / rep.CC). Its
   two certification arguments are:

     - WFC: repair iteration terminates. gsm checks this by cycle detection over
       the finite (bitpacked) state space (computeNormalForms in verify.go). The
       underlying mathematical fact is that a repair which strictly decreases a
       potential whenever the state is invalid is strongly normalizing.

     - CC: commutation of event pairs. gsm certifies this either by BRUTE FORCE
       over the finite state space, or - the compositional path, PairsDisjoint in
       verify.go - by FOOTPRINT DISJOINTNESS: events that write disjoint variables
       commute without any enumeration. In gsm's bitpacked State (state.go:setRaw),
       a write touches only its variable's bit-field, so disjoint footprints are
       disjoint bit updates.

   This file mechanizes the soundness of both arguments over a faithful state
   model (a valuation over indexed variables), axiom-free. The brute-force CC path
   is a finite decidable enumeration whose soundness is definitional, so it is not
   mechanized here; the disjointness path is the real theorem. Checked with
   Rocq 9.3. *)

Require Import NC.Newman.
From Coq Require Import List Arith.Wf_nat Wellfounded.Inverse_Image Lia.
Import ListNotations.

(* ============================================================
   State model: a valuation over indexed variables, mirroring gsm's bitpacked
   State (each variable a disjoint field; a write updates only its field).
   ============================================================ *)

(* Both recurse structurally on the state (the list), so an update or read of a
   variable index reduces even when the index is a variable. *)
Fixpoint write (i x : nat) (s : list nat) {struct s} : list nat :=
  match s with
  | [] => []                          (* out of range: no-op *)
  | h :: t => match i with
              | 0 => x :: t
              | S i' => h :: write i' x t
              end
  end.

Fixpoint read (i : nat) (s : list nat) {struct s} : nat :=
  match s with
  | [] => 0
  | h :: t => match i with
              | 0 => h
              | S i' => read i' t
              end
  end.

(* Reading a variable is unaffected by writing a DIFFERENT variable. *)
Lemma read_write_ne :
  forall s i j x, i <> j -> read i (write j x s) = read i s.
Proof.
  induction s as [| h t IH]; intros i j x Hne.
  - reflexivity.
  - destruct j as [| j]; destruct i as [| i]; simpl.
    + exfalso; apply Hne; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. congruence.
Qed.

(* Writes to DIFFERENT variables commute (Leibniz equality, no funext). This is
   the core fact behind gsm's footprint-disjointness CC certification. *)
Lemma write_comm :
  forall s i j x y, i <> j -> write i x (write j y s) = write j y (write i x s).
Proof.
  induction s as [| h t IH]; intros i j x y Hne.
  - reflexivity.
  - destruct i as [| i]; destruct j as [| j]; simpl.
    + exfalso; apply Hne; reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal. apply IH. congruence.
Qed.

(* ============================================================
   CC by footprint disjointness (the PairsDisjoint path).
   ============================================================ *)

(* An event with footprint {i}: it writes variable i to a value computed from the
   variables it reads - here modeled as depending only on its own footprint,
   read i s (the disjointness discipline gsm enforces). *)
Definition applyE (i : nat) (f : nat -> nat) (s : list nat) : list nat :=
  write i (f (read i s)) s.

(* Two events with DISJOINT footprints commute: apply order does not matter. This
   is exactly CC1 (order independence) for the disjoint case, discharged
   compositionally rather than by enumeration. *)
Theorem disjoint_events_commute :
  forall i j f g s,
    i <> j ->
    applyE i f (applyE j g s) = applyE j g (applyE i f s).
Proof.
  intros i j f g s Hne. unfold applyE.
  rewrite (read_write_ne s i j (g (read j s)) Hne).
  rewrite (read_write_ne s j i (f (read i s)) (fun H => Hne (eq_sym H))).
  apply write_comm. exact Hne.
Qed.

(* ============================================================
   WFC: a repair that strictly decreases a potential when invalid terminates.
   ============================================================ *)

Section WFC.
  Variable valid  : list nat -> Prop.
  Variable repair : list nat -> list nat.
  Variable Phi    : list nat -> nat.

  (* gsm's WFC obligation: each repair of an invalid state makes progress. *)
  Hypothesis wfc_decreases : forall s, ~ valid s -> Phi (repair s) < Phi s.

  (* The repair relation: an invalid state rewrites to its repair. *)
  Definition rstep (a b : list nat) : Prop := ~ valid a /\ b = repair a.

  (* Strong normalization of repair: no infinite compensation chain. This is the
     property gsm's cycle-detection check certifies for a concrete machine. *)
  Theorem repair_terminates : forall s, Acc (fun a b => rstep b a) s.
  Proof.
    assert (Hwf : well_founded (fun a b => Phi a < Phi b)).
    { apply (wf_inverse_image _ _ lt Phi lt_wf). }
    intros s. specialize (Hwf s).
    induction Hwf as [s _ IH].
    constructor. intros a [Hinv Heq]. subst a. apply IH. apply wfc_decreases. exact Hinv.
  Qed.
End WFC.

(* ============================================================
   Non-vacuity witnesses (both certifications are satisfiable, no axioms).
   ============================================================ *)

(* CC: two concrete disjoint increment-events (like inc_a on var 0, inc_b on var 1
   in gsm's confluence_test.go) commute. *)
Example inc0_inc1_commute :
  forall s,
    applyE 0 (fun x => S x) (applyE 1 (fun x => S x) s) =
    applyE 1 (fun x => S x) (applyE 0 (fun x => S x) s).
Proof. intros s. apply disjoint_events_commute. discriminate. Qed.

(* WFC: a clamp-style repair on variable 0 (valid when read 0 <= 3, repair sets it
   to 3, like the a_cap invariant in confluence_test.go) terminates. Potential is
   the excess above the cap. *)
Definition ex_valid  (s : list nat) : Prop := read 0 s <= 3.
Definition ex_repair (s : list nat) : list nat := write 0 3 s.
Definition ex_Phi    (s : list nat) : nat := read 0 s - 3.

Lemma ex_wfc_decreases : forall s, ~ ex_valid s -> ex_Phi (ex_repair s) < ex_Phi s.
Proof.
  intros s H. unfold ex_valid in H. unfold ex_Phi, ex_repair.
  assert (read 0 s > 3) by lia.
  destruct s as [| h t]; simpl in *; [lia|]. lia.
Qed.

Theorem ex_repair_terminates :
  forall s, Acc (fun a b => rstep ex_valid ex_repair b a) s.
Proof. apply (repair_terminates ex_valid ex_repair ex_Phi ex_wfc_decreases). Qed.
