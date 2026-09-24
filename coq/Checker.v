(* A verified convergence checker, for differential testing against gsm.

   gsm verifies WFC and CC in Go and emits a machine's step tables
   (step[event][state] = the normalized next state). Those tables encode the
   runtime behavior: applying an event is a table lookup. The convergence
   guarantee is that applying the SAME events in ANY order reaches the SAME state.

   This file proves that guarantee follows from a decidable property of the
   tables -- that the per-event step functions pairwise COMMUTE -- and packages a
   boolean checker for it, proven sound. Extracted to OCaml (see extraction/), the
   checker independently certifies gsm's emitted tables: if gsm's (unverified) Go
   ever produced tables that do not actually converge, the verified checker flags
   it. This attaches a machine-checked oracle to gsm's real output. Axiom-free. *)

From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Import ListNotations.

(* ===== The mathematical core: commuting steps converge regardless of order ===== *)

Section OrderIndependence.
  Context {S E : Type}.
  Variable step : E -> S -> S.

  Definition commuting : Prop :=
    forall e1 e2 s, step e1 (step e2 s) = step e2 (step e1 s).

  (* Apply a sequence of events left to right. *)
  Definition run (es : list E) (s : S) : S :=
    fold_left (fun st e => step e st) es s.

  Lemma run_cons : forall e es s, run (e :: es) s = run es (step e s).
  Proof. reflexivity. Qed.

  (* The convergence theorem: if steps commute, running any permutation of an
     event list gives the same state. This is order-independent convergence. *)
  Theorem run_perm_invariant :
    commuting -> forall es1 es2, Permutation es1 es2 -> forall s, run es1 s = run es2 s.
  Proof.
    intros Hc es1 es2 Hperm. induction Hperm as
      [ | e l1 l2 _ IH | e1 e2 l | l1 l2 l3 _ IH1 _ IH2 ]; intro s.
    - reflexivity.
    - rewrite !run_cons. apply IH.
    - rewrite !run_cons. rewrite (Hc e1 e2 s). reflexivity.
    - rewrite IH1. apply IH2.
  Qed.
End OrderIndependence.

(* ===== The decidable checker over concrete step tables ===== *)

(* A machine is n states (0..n-1), nE events, and step tables: stepT is a list of
   nE rows, each a list of n next-states. Lookups default to 0 out of range. *)
Definition lookup (l : list nat) (i : nat) : nat := nth i l 0.
Definition stepf (stepT : list (list nat)) (e s : nat) : nat := lookup (nth e stepT []) s.

(* check_commuting is true iff every ordered pair of events commutes on every
   state: stepf e1 (stepf e2 s) = stepf e2 (stepf e1 s). *)
Definition check_commuting (n nE : nat) (stepT : list (list nat)) : bool :=
  forallb (fun e1 =>
    forallb (fun e2 =>
      forallb (fun s =>
        Nat.eqb (stepf stepT e1 (stepf stepT e2 s))
                (stepf stepT e2 (stepf stepT e1 s)))
        (seq 0 n))
      (seq 0 nE))
    (seq 0 nE).

(* Soundness: if the checker passes, the step functions commute on the whole
   declared range of events and states. *)
Theorem check_commuting_sound :
  forall n nE stepT,
    check_commuting n nE stepT = true ->
    forall e1 e2 s, e1 < nE -> e2 < nE -> s < n ->
      stepf stepT e1 (stepf stepT e2 s) = stepf stepT e2 (stepf stepT e1 s).
Proof.
  intros n nE stepT H e1 e2 s He1 He2 Hs.
  unfold check_commuting in H.
  rewrite forallb_forall in H.
  assert (In e1 (seq 0 nE)) by (apply in_seq; lia).
  specialize (H e1 H0). rewrite forallb_forall in H.
  assert (In e2 (seq 0 nE)) by (apply in_seq; lia).
  specialize (H e2 H1). rewrite forallb_forall in H.
  assert (In s (seq 0 n)) by (apply in_seq; lia).
  specialize (H s H2). apply Nat.eqb_eq in H. exact H.
Qed.

(* closed: applying any in-range event to an in-range state stays in range (gsm's
   step tables map to valid state ids). This keeps intermediate states in range so
   commutation applies throughout a run. *)
Definition closed (n nE : nat) (stepT : list (list nat)) : bool :=
  forallb (fun e => forallb (fun s => Nat.ltb (stepf stepT e s) n) (seq 0 n)) (seq 0 nE).

Lemma closed_step :
  forall n nE stepT, closed n nE stepT = true ->
    forall e s, e < nE -> s < n -> stepf stepT e s < n.
Proof.
  intros n nE stepT H e s He Hs. unfold closed in H.
  rewrite forallb_forall in H.
  assert (In e (seq 0 nE)) by (apply in_seq; lia).
  specialize (H e H0). rewrite forallb_forall in H.
  assert (In s (seq 0 n)) by (apply in_seq; lia).
  specialize (H s H1). apply Nat.ltb_lt in H. exact H.
Qed.

(* End-to-end convergence for a concrete machine: if the checker passes and the
   tables are closed, any two permutations of the same in-range event list reach
   the same state from any in-range start. This is exactly the runtime guarantee,
   certified independently of gsm's Go. *)
Theorem checked_converges :
  forall n nE stepT,
    check_commuting n nE stepT = true ->
    closed n nE stepT = true ->
    forall es1 es2, Permutation es1 es2 ->
      (forall e, In e es1 -> e < nE) ->
      forall s, s < n -> run (stepf stepT) es1 s = run (stepf stepT) es2 s.
Proof.
  intros n nE stepT Hchk Hcl es1 es2 Hperm.
  induction Hperm as [ | x l1 l2 Hp IH | x y l | l1 l2 l3 Hp1 IH1 Hp2 IH2 ];
    intros Hrange s Hs.
  - reflexivity.
  - rewrite !run_cons.
    assert (Hx : x < nE) by (apply Hrange; left; reflexivity).
    apply IH.
    + intros e He. apply Hrange. right. exact He.
    + apply (closed_step n nE stepT Hcl x s Hx Hs).
  - rewrite !run_cons.
    assert (Hx : x < nE) by (apply Hrange; right; left; reflexivity).
    assert (Hy : y < nE) by (apply Hrange; left; reflexivity).
    rewrite (check_commuting_sound n nE stepT Hchk y x s Hy Hx Hs). reflexivity.
  - assert (Hr2 : forall e, In e l2 -> e < nE).
    { intros e He. apply Hrange. apply (Permutation_in _ (Permutation_sym Hp1) He). }
    rewrite (IH1 Hrange s Hs). apply IH2; assumption.
Qed.
