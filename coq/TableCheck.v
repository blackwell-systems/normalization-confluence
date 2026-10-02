(* The table oracle, aligned with gsm's Build.

   Checker.v certifies that EVERY ordered pair of events commutes on EVERY state
   id it is given. gsm's Build checks less, and its runtime needs less:
   - it checks only the pairs declared independent (Registry.Independent), or
     every pair when none is declared;
   - it checks them only on the states its runtime applies events to: the valid
     states (the fixed points of the normal-form table, which is how the runtime's
     IsValid is defined) plus the zero state Machine.NewState returns.
   So the old table oracle rejected convergent machines (any machine with
   declared pairs, and any machine that fails only on an invariant-invalid
   encoding no run reaches).

   check_tables decides exactly Build's property, over a domain defined by the
   tables themselves (gsm cannot shrink it):
     inV s := s < n /\ NF s = s          the runtime's IsValid
     inD s := s < n /\ (inV s \/ s = 0)  Build's CC domain
   and requires:
     - every declared pair names in-range events;
     - NF retracts onto valid states (NF (NF s) = NF s on every state): the
       table image of WFC, which is what Machine.Normalize returns;
     - every step from every state lands on a valid state;
     - every declared pair commutes on inD.
   On tables gsm's Build computes, the first three always hold (every NF entry is
   a valid state and every step is an NF entry), so the verdict is the CC check
   alone: exactly verifyCC.

   The guarantee (check_tables_converges): from any state in inD, two event
   sequences that differ only by reordering adjacent declared-independent events
   reach the same state (Trace.run_tequiv). With every pair declared it is order
   independence under any permutation (check_tables_converges_all).

   Lookups go through an axiom-free binary trie (O(log n) per lookup, proven
   equal to list nth), not PArray, whose specification is axiomatic. Range tests
   use Nat.compare, which ExtrOcamlNatInt maps to an O(1) comparison (Nat.ltb
   would extract to a linear-time recursion). Axiom-free. *)

Require Import NC.Trace.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Import ListNotations.

(* ===== an axiom-free binary trie keyed by nat ===== *)

(* Index 0 is the root; index 2h+1 is index h of the left subtree, and index
   2h+2 is index h of the right subtree (a Braun tree). *)
Inductive trie := TLeaf | TNode (v : nat) (l r : trie).

Fixpoint tget (t : trie) (k : nat) : nat :=
  match t with
  | TLeaf => 0
  | TNode v l r =>
    if Nat.eqb k 0 then v
    else let h := Nat.div2 k in
         if Nat.eqb (k - h - h) 1 then tget l h else tget r (h - 1)
  end.

Fixpoint evens (l : list nat) : list nat :=
  match l with [] => [] | x :: t => x :: odds t end
with odds (l : list nat) : list nat :=
  match l with [] => [] | _ :: t => evens t end.

Fixpoint of_listF (fuel : nat) (l : list nat) : trie :=
  match fuel with
  | 0 => TLeaf
  | S f =>
    match l with
    | [] => TLeaf
    | x :: t => TNode x (of_listF f (evens t)) (of_listF f (odds t))
    end
  end.

Definition of_list (l : list nat) : trie := of_listF (length l) l.

Lemma evens_odds_length : forall l, length (evens l) <= length l /\ length (odds l) <= length l.
Proof.
  induction l as [| x t [He Ho]]; simpl; [lia |]. split; lia.
Qed.

Lemma evens_odds_nth : forall l j,
  nth j (evens l) 0 = nth (2 * j) l 0 /\ nth j (odds l) 0 = nth (2 * j + 1) l 0.
Proof.
  induction l as [| x t IH]; intros j.
  - destruct j; simpl; split; reflexivity.
  - simpl evens. simpl odds. destruct j as [| j'].
    + simpl. split; [reflexivity |]. destruct (IH 0) as [He _]. exact He.
    + split.
      * replace (2 * S j') with (S (2 * j' + 1)) by lia. simpl nth at 1.
        destruct (IH j') as [_ Ho]. rewrite Ho. reflexivity.
      * replace (2 * S j' + 1) with (S (2 * S j')) by lia. simpl nth at 1.
        destruct (IH (S j')) as [He _]. rewrite He. reflexivity.
Qed.

(* The key arithmetic of tget: a positive index is 2h+1 or 2h'+2. *)
Lemma tget_index : forall k, k <> 0 ->
  let h := Nat.div2 k in
  (k - h - h = 1 /\ k = 2 * h + 1) \/ (k - h - h <> 1 /\ h <> 0 /\ k = 2 * (h - 1) + 2).
Proof.
  intros k Hk h. pose proof (Nat.div2_odd k) as Hd. fold h in Hd.
  destruct (Nat.odd k); simpl in Hd; [left | right]; lia.
Qed.

Lemma tget_of_listF : forall f l, length l <= f -> forall k, tget (of_listF f l) k = nth k l 0.
Proof.
  induction f as [| f IH]; intros l Hl k.
  - destruct l; simpl in Hl; [| lia]. destruct k; reflexivity.
  - destruct l as [| x t]; [destruct k; reflexivity |].
    simpl in Hl. pose proof (evens_odds_length t) as [He Ho].
    simpl of_listF. simpl tget.
    destruct (Nat.eqb_spec k 0) as [-> | Hk]; [reflexivity |].
    destruct (tget_index k Hk) as [[H1 Hk1] | [H1 [Hh Hk2]]].
    + rewrite H1, Nat.eqb_refl. rewrite IH by lia.
      destruct (evens_odds_nth t (Nat.div2 k)) as [Hn _]. rewrite Hn.
      rewrite Hk1 at 2. replace (2 * Nat.div2 k + 1) with (S (2 * Nat.div2 k)) by lia. reflexivity.
    + apply Nat.eqb_neq in H1. rewrite H1. rewrite IH by lia.
      destruct (evens_odds_nth t (Nat.div2 k - 1)) as [_ Hn]. rewrite Hn.
      rewrite Hk2 at 2. replace (2 * (Nat.div2 k - 1) + 2) with (S (2 * (Nat.div2 k - 1) + 1)) by lia.
      reflexivity.
Qed.

Theorem tget_of_list : forall l k, tget (of_list l) k = nth k l 0.
Proof. intros l k. apply tget_of_listF. lia. Qed.

(* ===== an O(1) range test under extraction ===== *)

Definition ltn (a b : nat) : bool :=
  match Nat.compare a b with Lt => true | _ => false end.

Lemma ltn_spec : forall a b, ltn a b = true <-> a < b.
Proof.
  intros a b. unfold ltn. rewrite <- Nat.compare_lt_iff.
  destruct (Nat.compare a b); split; intro H; congruence.
Qed.

(* ===== the aligned table check ===== *)

(* Every unordered pair {i, j} of distinct events, as (i, j) with i < j. *)
Definition allPairs (nE : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq (S i) (nE - S i))) (seq 0 nE).

Lemma allPairs_in : forall nE a b, a < b -> b < nE -> In (a, b) (allPairs nE).
Proof.
  intros nE a b Hab Hb. unfold allPairs. apply in_flat_map. exists a. split.
  - apply in_seq. lia.
  - apply in_map_iff. exists b. split; [reflexivity |]. apply in_seq. lia.
Qed.

Section Tables.
  (* n state ids, nE events, the normal-form table NF, one step table per event,
     and the declared pairs (None: every pair, gsm's default). *)
  Variables (n nE : nat) (NF : trie) (T : list trie) (P : option (list (nat * nat))).

  Definition nfv (s : nat) : nat := tget NF s.
  Definition row (e : nat) : trie := nth e T TLeaf.
  Definition stp (e s : nat) : nat := tget (row e) s.

  Definition inV (s : nat) : bool := ltn s n && Nat.eqb (nfv s) s.
  Definition inD (s : nat) : bool := ltn s n && (Nat.eqb (nfv s) s || Nat.eqb s 0).

  Definition pairsOf : list (nat * nat) :=
    match P with None => allPairs nE | Some l => l end.

  (* The independence relation the guarantee is stated for. *)
  Definition indep (a b : nat) : Prop :=
    match P with
    | None => a < nE /\ b < nE
    | Some l => In (a, b) l \/ In (b, a) l
    end.

  Definition pairs_ok : bool :=
    forallb (fun p => ltn (fst p) nE && ltn (snd p) nE) pairsOf.

  Definition nf_ok : bool := forallb (fun s => inV (nfv s)) (seq 0 n).

  Definition steps_ok : bool :=
    forallb (fun e => let r := row e in forallb (fun s => inV (tget r s)) (seq 0 n)) (seq 0 nE).

  Definition comm_ok : bool :=
    forallb (fun p =>
      let ra := row (fst p) in let rb := row (snd p) in
      forallb (fun s => implb (inD s) (Nat.eqb (tget ra (tget rb s)) (tget rb (tget ra s))))
        (seq 0 n))
      pairsOf.

  Definition check_tables : bool := pairs_ok && nf_ok && steps_ok && comm_ok.

  Hypothesis Hchk : check_tables = true.

  Lemma check_parts : pairs_ok = true /\ nf_ok = true /\ steps_ok = true /\ comm_ok = true.
  Proof.
    unfold check_tables in Hchk. repeat rewrite andb_true_iff in Hchk. tauto.
  Qed.

  (* Every declared pair names events that exist, so a declaration cannot
     silently refer to an event the tables do not have. *)
  Theorem check_tables_pairs_in_range :
    forall a b, In (a, b) pairsOf -> a < nE /\ b < nE.
  Proof.
    intros a b Hin. destruct check_parts as [Hp _].
    unfold pairs_ok in Hp. rewrite forallb_forall in Hp. specialize (Hp (a, b) Hin).
    simpl in Hp. apply andb_true_iff in Hp. destruct Hp as [Ha Hb].
    apply ltn_spec in Ha. apply ltn_spec in Hb. split; assumption.
  Qed.

  Lemma in_seq0 : forall k m, k < m -> In k (seq 0 m).
  Proof. intros k m H. apply in_seq. lia. Qed.

  (* Machine.Normalize returns a valid state, from any state. *)
  Theorem check_tables_nf_valid : forall s, s < n -> inV (nfv s) = true.
  Proof.
    intros s Hs. destruct check_parts as [_ [Hnf _]].
    unfold nf_ok in Hnf. rewrite forallb_forall in Hnf. apply Hnf, in_seq0, Hs.
  Qed.

  (* Machine.Apply lands on a valid state, from any state. *)
  Theorem check_tables_step_valid : forall e s, e < nE -> s < n -> inV (stp e s) = true.
  Proof.
    intros e s He Hs. destruct check_parts as [_ [_ [Hst _]]].
    unfold steps_ok in Hst. rewrite forallb_forall in Hst.
    specialize (Hst e (in_seq0 _ _ He)). simpl in Hst. rewrite forallb_forall in Hst.
    apply Hst, in_seq0, Hs.
  Qed.

  Lemma comm_listed : forall a b s, In (a, b) pairsOf -> inD s = true ->
    stp a (stp b s) = stp b (stp a s).
  Proof.
    intros a b s Hin HD. destruct check_parts as [_ [_ [_ Hc]]].
    unfold comm_ok in Hc. rewrite forallb_forall in Hc. specialize (Hc (a, b) Hin).
    simpl in Hc. rewrite forallb_forall in Hc.
    assert (Hs : s < n).
    { unfold inD in HD. apply andb_true_iff in HD. apply ltn_spec. tauto. }
    specialize (Hc s (in_seq0 _ _ Hs)). rewrite HD in Hc. simpl in Hc.
    apply Nat.eqb_eq. exact Hc.
  Qed.

  (* Every declared-independent pair commutes on Build's CC domain. *)
  Theorem check_tables_commute : forall a b s, indep a b -> inD s = true ->
    stp a (stp b s) = stp b (stp a s).
  Proof.
    intros a b s Hab HD. unfold indep in Hab. destruct P as [l |] eqn:HP.
    - destruct Hab as [Hab | Hba].
      + apply comm_listed; [unfold pairsOf; rewrite HP; exact Hab | exact HD].
      + symmetry. apply comm_listed; [unfold pairsOf; rewrite HP; exact Hba | exact HD].
    - destruct Hab as [Ha Hb].
      destruct (Nat.lt_trichotomy a b) as [Hlt | [-> | Hgt]].
      + apply comm_listed; [unfold pairsOf; rewrite HP; apply allPairs_in; assumption | exact HD].
      + reflexivity.
      + symmetry. apply comm_listed; [unfold pairsOf; rewrite HP; apply allPairs_in; assumption | exact HD].
  Qed.

  Lemma inV_inD : forall s, inV s = true -> inD s = true.
  Proof.
    intros s H. unfold inV in H. unfold inD. apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite H1, H2. reflexivity.
  Qed.

  Lemma inD_lt : forall s, inD s = true -> s < n.
  Proof. intros s H. unfold inD in H. apply andb_true_iff in H. apply ltn_spec. tauto. Qed.

  (* The runtime guarantee: from a valid state or the zero state, event sequences
     that differ only by reordering declared-independent events reach the same
     state. *)
  Theorem check_tables_converges :
    forall es1 es2, tequiv indep es1 es2 -> Forall (fun e => e < nE) es1 ->
    forall s, inD s = true -> runT stp es1 s = runT stp es2 s.
  Proof.
    intros es1 es2 Hte Hev s Hs.
    apply (run_tequiv stp indep (fun e => e < nE) (fun s => inV s = true) (fun s => inD s = true));
      try assumption.
    - exact inV_inD.
    - intros e t He Ht. apply check_tables_step_valid; [exact He | apply inD_lt; exact Ht].
    - intros a b t _ _ Hab Ht. apply check_tables_commute; assumption.
  Qed.

  (* With no pairs declared (gsm's default), every permutation converges. *)
  Theorem check_tables_converges_all :
    P = None ->
    forall es1 es2, Permutation es1 es2 -> Forall (fun e => e < nE) es1 ->
    forall s, inD s = true -> runT stp es1 s = runT stp es2 s.
  Proof.
    intros HP es1 es2 Hp Hev s Hs. apply check_tables_converges; [| exact Hev | exact Hs].
    apply (perm_tequiv_total indep (fun e => e < nE)); [| exact Hp | exact Hev].
    intros a b Ha Hb. unfold indep. rewrite HP. split; assumption.
  Qed.
End Tables.
