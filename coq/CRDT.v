(* CRDTs as the compensation-free fragment of normalization confluence.

   A CRDT buys convergence by restricting to operations that can never leave the
   convergence structure: op-based CRDTs (CmRDT) require concurrent operations to
   commute; state-based CRDTs (CvRDT) require a join-semilattice and merge by least
   upper bound. Normalization confluence keeps convergence while dropping that
   restriction: events may violate an invariant, and a compensation repairs them.

   This file makes the relationship precise and machine-checks it, in four parts:

   1. cmrdt_SEC: an op-based CRDT's strong eventual consistency is an instance of
      run_perm_invariant (Checker.v): commuting operations applied in any order over
      the same delivered set reach the same state.

   2. cmrdt_governed_SEC: the embedding is faithful. Put a CmRDT inside a governed
      machine with the trivial invariant (every state valid) and identity
      compensation; then WFC is trivial, the governed step equals the raw operation,
      and convergence is again run_perm_invariant.

   3. cvrdt_SEC / cvrdt_absorbs_duplicates: a state-based CRDT is the semilattice
      special case. A commutative, associative, idempotent join makes merge
      order-independent (the same order-independence lemma) and idempotent
      (duplicate delivery is absorbed).

   4. Strict inclusion (the witness_ theorems): a concrete governed machine that
      CONVERGES yet is neither CRDT. Its raw operations do not commute (so it is no
      CmRDT), and an
      event drives a valid state to an invalid one (so its operations are not the
      structure-preserving endomaps of a CvRDT). It converges only via compensation.

   Everything is axiom-free and reuses run_perm_invariant from Checker.v. *)

Require Import NC.Checker.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* ===== 1. Op-based CRDT (CmRDT): SEC is a corollary of run_perm_invariant ===== *)

Section CmRDT.
  Context {S Op : Type}.
  Variable apply : Op -> S -> S.

  (* The defining CmRDT requirement: (concurrent) operations commute. *)
  Hypothesis ops_commute : forall o1 o2 s, apply o1 (apply o2 s) = apply o2 (apply o1 s).

  (* Strong eventual consistency: two replicas that delivered the same set of
     operations, in any order, reach the same state. This is exactly
     run_perm_invariant, so a CmRDT's central guarantee is a one-line instance of a
     theorem the governance development already proved. *)
  Theorem cmrdt_SEC :
    forall ops1 ops2, Permutation ops1 ops2 ->
    forall s, run apply ops1 s = run apply ops2 s.
  Proof. apply run_perm_invariant. exact ops_commute. Qed.
End CmRDT.

(* ===== 2. The embedding is faithful: CmRDT = governance with trivial repair ===== *)

Section CmRDT_as_Governance.
  Context {S Op : Type}.
  Variable apply : Op -> S -> S.
  Variable normalize : S -> S.

  (* Trivial invariant: every state is already valid, so compensation is identity. *)
  Hypothesis repair_trivial : forall s, normalize s = s.
  Hypothesis ops_commute : forall o1 o2 s, apply o1 (apply o2 s) = apply o2 (apply o1 s).

  (* A governed step applies the operation, then normalizes (compensates). *)
  Definition gstep (o : Op) (s : S) : S := normalize (apply o s).

  Lemma gstep_is_apply : forall o s, gstep o s = apply o s.
  Proof. intros o s. unfold gstep. apply repair_trivial. Qed.

  (* WFC is trivial (normalization is the identity, terminating in zero steps); CC
     holds because the governed steps commute, inheriting it from the raw ops. *)
  Lemma gstep_commute : forall o1 o2 s, gstep o1 (gstep o2 s) = gstep o2 (gstep o1 s).
  Proof. intros o1 o2 s. rewrite !gstep_is_apply. apply ops_commute. Qed.

  Theorem cmrdt_governed_SEC :
    forall ops1 ops2, Permutation ops1 ops2 ->
    forall s, run gstep ops1 s = run gstep ops2 s.
  Proof. apply run_perm_invariant. exact gstep_commute. Qed.
End CmRDT_as_Governance.

(* ===== 3. State-based CRDT (CvRDT): the semilattice special case ===== *)

Section CvRDT.
  Context {S : Type}.
  Variable join : S -> S -> S.

  (* A join-semilattice: commutative, associative, idempotent. *)
  Hypothesis join_comm  : forall a b, join a b = join b a.
  Hypothesis join_assoc : forall a b c, join (join a b) c = join a (join b c).
  Hypothesis join_idem  : forall a, join a a = a.

  (* Merging a received state into the local state. *)
  Definition merge (x s : S) : S := join s x.

  Lemma merge_commute : forall x y s, merge x (merge y s) = merge y (merge x s).
  Proof.
    intros x y s. unfold merge. rewrite !join_assoc. rewrite (join_comm y x). reflexivity.
  Qed.

  (* Order-independence: merging a set of received states in any order converges,
     again by the same order-independence lemma. *)
  Theorem cvrdt_SEC :
    forall xs1 xs2, Permutation xs1 xs2 ->
    forall s, run merge xs1 s = run merge xs2 s.
  Proof. apply run_perm_invariant. exact merge_commute. Qed.

  (* Idempotence handles duplicate delivery: merging the same state twice equals
     once. Normalization confluence does not require this in general; it is the extra
     property a CvRDT bundles in to tolerate at-least-once delivery. *)
  Lemma cvrdt_absorbs_duplicates : forall x s, merge x (merge x s) = merge x s.
  Proof. intros x s. unfold merge. rewrite join_assoc. rewrite join_idem. reflexivity. Qed.
End CvRDT.

(* ===== 4. Strict inclusion: a convergent governed machine that is no CRDT ===== *)

Section StrictInclusion.
  (* Witness: the state is one boolean; only `false` is valid. Two events: `settrue`
     (s := true) and `flip` (s := negb s). Compensation restores validity by resetting
     to false. The governed steps converge, but the raw operations do not commute (so
     it is not an op-based CRDT), and an event drives a valid state to an invalid one
     (so its operations are not the structure-preserving endomaps of a state-based
     CRDT). It converges only because compensation repairs the violation. *)
  Definition settrue (_ : bool) : bool := true.
  Definition flip (s : bool) : bool := negb s.
  Definition validb (s : bool) : bool := negb s. (* valid iff s = false *)
  Definition fixb (_ : bool) : bool := false.    (* compensation to the valid state *)

  (* The governed step: apply the raw operation, then compensate. *)
  Definition gov (f : bool -> bool) (s : bool) : bool := fixb (f s).

  Lemma gov_commute : forall f g s, gov f (gov g s) = gov g (gov f s).
  Proof. reflexivity. Qed.

  (* The governed machine converges: any ordering of the same events agrees. *)
  Theorem witness_converges :
    forall es1 es2, Permutation es1 es2 ->
    forall s, run gov es1 s = run gov es2 s.
  Proof. apply run_perm_invariant. exact gov_commute. Qed.

  (* It is NOT an op-based CRDT: the raw operations do not commute, so they cannot be
     the concurrent operations of a CmRDT. *)
  Theorem witness_not_cmrdt :
    ~ (forall (f g : bool -> bool) (s : bool), f (g s) = g (f s)).
  Proof.
    intro H. specialize (H flip settrue false).
    unfold flip, settrue in H. simpl in H. discriminate H.
  Qed.

  (* It is NOT a state-based CRDT: an event maps a valid state to an invalid one,
     whereas a CvRDT's operations keep the state inside the semilattice (they never
     produce a state that needs repair). *)
  Theorem witness_leaves_valid_space :
    exists s, validb s = true /\ validb (settrue s) = false.
  Proof. exists false. split; reflexivity. Qed.
End StrictInclusion.
