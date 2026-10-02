(* SPIKE PROTOTYPE (spike/checker-perf): a faster table oracle, proven equal
   to check_tables.

   check_tables (TableCheck.v) spends its time in lookups: each is a walk of
   about 20 levels down a Braun tree over 2^20 states, a cache miss per level,
   and it makes about 80 of them per state (the nf, steps and comm passes each
   look up the state itself, then the lookups the property needs). This file
   keeps the same property and changes only how it is computed:

   - a 16-ary trie (w16), keyed most significant digit first, so a lookup over
     2^20 keys is 5 levels instead of 20. The digit is found by four
     comparisons, not by division (Nat.div is not mapped by ExtrOcamlNatInt and
     extracts to a linear-time recursion). Axiom-free, no PArray;
   - one fused pass over the states that reads NF[s] and every T[e][s]
     sequentially from the input lists (no lookup at all), so only the lookups
     the property itself needs remain: NF at each step target, and T[a] at
     T[b][s] and T[b] at T[a][s] for each declared pair.

   check_fast_eq proves check_fast equal to check_tables on the Braun tries the
   current front end builds, so every theorem about check_tables
   (check_tables_converges and the rest) holds for check_fast unchanged. *)

Require Import NC.Trace.
Require Import NC.TableCheck.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Lia.
Import ListNotations.

(* ===== an int comparison the OCaml compiler specializes ===== *)

(* ltn (TableCheck.v) goes through Nat.compare, which extracts to a polymorphic
   OCaml function, so every comparison is a call into the runtime's generic
   compare. lt_dec is extracted inline as (<), which ocamlopt and ocamlc compile
   to an integer comparison wherever the operands are known to be ints. It is a
   notation, not a definition, so that the comparison is extracted inline at
   each use, where the operand types are known. *)
Notation ltd a b := (if Compare_dec.lt_dec a b then true else false).

Lemma ltd_spec : forall a b, ltd a b = true <-> a < b.
Proof. intros a b. destruct (Compare_dec.lt_dec a b); split; intro; congruence || lia. Qed.

Lemma ltd_ltn : forall a b, ltd a b = ltn a b.
Proof. intros a b. apply eq_iff_eq_true. rewrite ltd_spec, ltn_spec. reflexivity. Qed.

(* ===== a 16-ary trie ===== *)

Inductive w16 :=
| WL (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : nat)
| WN (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : w16).

(* (x_j, k - j * p) where j = k / p, for k < 16 * p, by binary search. *)
(* (x_j, b + j * p) where j = (k - b) / p, for b <= k < b + 16 * p, by binary
   search. It never subtracts: nat subtraction extracts to a call that clamps
   at 0 through a polymorphic max. *)
Definition pick {A : Type} (p b k : nat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) : A * nat :=
  if ltd k (b + 8 * p) then if ltd k (b + 4 * p) then if ltd k (b + 2 * p) then if ltd k (b + 1 * p) then (x0, b + 0 * p) else (x1, b + 1 * p) else if ltd k (b + 3 * p) then (x2, b + 2 * p) else (x3, b + 3 * p) else if ltd k (b + 6 * p) then if ltd k (b + 5 * p) then (x4, b + 4 * p) else (x5, b + 5 * p) else if ltd k (b + 7 * p) then (x6, b + 6 * p) else (x7, b + 7 * p) else if ltd k (b + 12 * p) then if ltd k (b + 10 * p) then if ltd k (b + 9 * p) then (x8, b + 8 * p) else (x9, b + 9 * p) else if ltd k (b + 11 * p) then (x10, b + 10 * p) else (x11, b + 11 * p) else if ltd k (b + 14 * p) then if ltd k (b + 13 * p) then (x12, b + 12 * p) else (x13, b + 13 * p) else if ltd k (b + 15 * p) then (x14, b + 14 * p) else (x15, b + 15 * p).

Lemma pick_spec : forall {A : Type} (p b k : nat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A), 0 < p -> b <= k -> k < b + 16 * p ->
  pick p b k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 = (nth ((k - b) / p) [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15] x15, b + (k - b) / p * p).
Proof.
  intros A p b k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 Hp Hb Hk.
  pose proof (Nat.div_mod_eq (k - b) p) as Hdm. pose proof (Nat.mod_upper_bound (k - b) p ltac:(lia)) as Hm.
  assert (Hj : (k - b) / p < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
  remember ((k - b) / p) as j eqn:Ej. remember ((k - b) mod p) as r eqn:Er.
  unfold pick.
  repeat (match goal with
          | |- context [ltd ?a ?c] =>
            let H := fresh "H" in destruct (ltd a c) eqn:H;
            [apply ltd_spec in H | assert (~ a < c) by (intro HH; apply ltd_spec in HH; congruence); clear H]
          end).
  all: do 16 (destruct j as [| j]; [simpl; f_equal; nia |]); exfalso; lia.
Qed.

(* The all-zero trie of depth d (shared, so O(d) to build). *)
Fixpoint zt (d : nat) : w16 :=
  match d with
  | 0 => WL 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
  | S d' => let z := zt d' in WN z z z z z z z z z z z z z z z z
  end.

(* Lookup in a trie of depth d whose children each cover p = 16^d keys, the
   trie covering keys b to b + 16 * p - 1. *)
Fixpoint wget (p b : nat) (t : w16) (k : nat) : nat :=
  match t with
  | WL x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => if ltd k (b + 8 * 1) then if ltd k (b + 4 * 1) then if ltd k (b + 2 * 1) then if ltd k (b + 1 * 1) then x0 else x1 else if ltd k (b + 3 * 1) then x2 else x3 else if ltd k (b + 6 * 1) then if ltd k (b + 5 * 1) then x4 else x5 else if ltd k (b + 7 * 1) then x6 else x7 else if ltd k (b + 12 * 1) then if ltd k (b + 10 * 1) then if ltd k (b + 9 * 1) then x8 else x9 else if ltd k (b + 11 * 1) then x10 else x11 else if ltd k (b + 14 * 1) then if ltd k (b + 13 * 1) then x12 else x13 else if ltd k (b + 15 * 1) then x14 else x15
  | WN c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 => if ltd k (b + 8 * p) then if ltd k (b + 4 * p) then if ltd k (b + 2 * p) then if ltd k (b + 1 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 0 * p) c0 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 1 * p) c1 k else if ltd k (b + 3 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 2 * p) c2 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 3 * p) c3 k else if ltd k (b + 6 * p) then if ltd k (b + 5 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 4 * p) c4 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 5 * p) c5 k else if ltd k (b + 7 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 6 * p) c6 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 7 * p) c7 k else if ltd k (b + 12 * p) then if ltd k (b + 10 * p) then if ltd k (b + 9 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 8 * p) c8 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 9 * p) c9 k else if ltd k (b + 11 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 10 * p) c10 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 11 * p) c11 k else if ltd k (b + 14 * p) then if ltd k (b + 13 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 12 * p) c12 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 13 * p) c13 k else if ltd k (b + 15 * p) then wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 14 * p) c14 k else wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + 15 * p) c15 k
  end.

(* wget is pick, then a recursive lookup; it is written out with the comparison
   tree inline so the extracted code allocates nothing per level and recurses
   structurally. *)
Lemma wget_WL : forall p b k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, wget p b (WL x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) k = fst (pick 1 b k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).
Proof.
  intros. cbn [wget]. unfold pick.
  repeat match goal with |- context [Compare_dec.lt_dec ?a ?c] => destruct (Compare_dec.lt_dec a c) end;
  reflexivity.
Qed.

Lemma wget_WN : forall p b k c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15, wget p b (WN c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15) k =
  let '(c, b') := pick p b k c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 in wget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) b' c k.
Proof.
  intros. cbn [wget]. unfold pick.
  repeat match goal with |- context [Compare_dec.lt_dec ?a ?c] => destruct (Compare_dec.lt_dec a c) end;
  reflexivity.
Qed.

(* Group a list 16 at a time, padding the last group with z. *)
Fixpoint chunkF {A B : Type} (f : nat) (mk : A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> B)
    (z : A) (l : list A) : list B :=
  match f with
  | 0 => []
  | S f' => match l with
            | [] => []
            | _ => mk (nth 0 l z) (nth 1 l z) (nth 2 l z) (nth 3 l z) (nth 4 l z) (nth 5 l z) (nth 6 l z) (nth 7 l z) (nth 8 l z) (nth 9 l z) (nth 10 l z) (nth 11 l z) (nth 12 l z) (nth 13 l z) (nth 14 l z) (nth 15 l z) :: chunkF f' mk z (skipn 16 l)
            end
  end.

(* Tail-recursive forms, so the extracted code runs in constant stack: OCaml
   4.14 native code has the 8 MiB system stack, and List.length and chunkF
   recurse once per element (or per group of 16). *)
Fixpoint lenT {A : Type} (l : list A) (a : nat) : nat :=
  match l with [] => a | _ :: t => lenT t (S a) end.

Fixpoint chunkT {A B : Type} (f : nat) mk (z : A) (l : list A) (acc : list B) : list B :=
  match f with
  | 0 => rev_append acc []
  | S f' => match l with
            | [] => rev_append acc []
            | _ => chunkT f' mk z (skipn 16 l) (mk (nth 0 l z) (nth 1 l z) (nth 2 l z) (nth 3 l z) (nth 4 l z) (nth 5 l z) (nth 6 l z) (nth 7 l z) (nth 8 l z) (nth 9 l z) (nth 10 l z) (nth 11 l z) (nth 12 l z) (nth 13 l z) (nth 14 l z) (nth 15 l z) :: acc)
            end
  end.

Definition chunk {A B : Type} mk (z : A) (l : list A) : list B := chunkT (lenT l 0) mk z l [].

Fixpoint levels (l : list nat) (d : nat) : list w16 :=
  match d with
  | 0 => chunk WL 0 l
  | S d' => chunk WN (zt d') (levels l d')
  end.

(* The least d (up to fuel) with 16^(d+1) >= m, given p = 16^(current d). *)
Fixpoint depthF (f m p : nat) : nat :=
  match f with
  | 0 => 0
  | S f' => if ltd (16 * p) m then S (depthF f' m (16 * p)) else 0
  end.

Record wt := { wd : nat; wp : nat; wroot : w16 }.

Definition of_list16 (l : list nat) : wt :=
  let m := lenT l 0 in
  let d := depthF m m 1 in
  {| wd := d; wp := Nat.pow 16 d; wroot := nth 0 (levels l d) (zt d) |}.

Definition wlook (t : wt) (k : nat) : nat :=
  if ltd k (16 * wp t) then wget (wp t) 0 (wroot t) k else 0.

(* ===== correctness of the trie ===== *)

Lemma skipn_nth : forall {A} (l : list A) i j z, nth j (skipn i l) z = nth (i + j) l z.
Proof.
  intros A l i. revert l. induction i as [| i IH]; intros l j z; [reflexivity |].
  destruct l; simpl; [destruct j; reflexivity | apply IH].
Qed.

Lemma chunkF_cons : forall {A B} f mk (z : A) (l : list A), l <> [] ->
  chunkF (S f) mk z l = (mk (nth 0 l z) (nth 1 l z) (nth 2 l z) (nth 3 l z) (nth 4 l z) (nth 5 l z) (nth 6 l z) (nth 7 l z) (nth 8 l z) (nth 9 l z) (nth 10 l z) (nth 11 l z) (nth 12 l z) (nth 13 l z) (nth 14 l z) (nth 15 l z) : B) :: chunkF f mk z (skipn 16 l).
Proof. intros A B f mk z l H. destruct l; [congruence | reflexivity]. Qed.

Lemma chunkF_nth : forall {A B} f mk (z : A) (l : list A) j, length l <= 16 * f ->
  nth j (chunkF f mk z l) (mk z z z z z z z z z z z z z z z z) = (mk (nth (16 * j + 0) l z) (nth (16 * j + 1) l z) (nth (16 * j + 2) l z) (nth (16 * j + 3) l z) (nth (16 * j + 4) l z) (nth (16 * j + 5) l z) (nth (16 * j + 6) l z) (nth (16 * j + 7) l z) (nth (16 * j + 8) l z) (nth (16 * j + 9) l z) (nth (16 * j + 10) l z) (nth (16 * j + 11) l z) (nth (16 * j + 12) l z) (nth (16 * j + 13) l z) (nth (16 * j + 14) l z) (nth (16 * j + 15) l z) : B).
Proof.
  intros A B f. induction f as [| f IH]; intros mk z l j Hl.
  - destruct l; [| simpl in Hl; lia]. simpl. destruct j; reflexivity.
  - destruct l as [| x t] eqn:El.
    + simpl. destruct j; reflexivity.
    + rewrite <- El. rewrite chunkF_cons by congruence. destruct j as [| j].
      * cbn [nth]. f_equal; f_equal; lia.
      * cbn [nth]. rewrite IH.
        -- repeat rewrite skipn_nth. f_equal; f_equal; lia.
        -- rewrite skipn_length. subst l. simpl in Hl |- *. lia.
Qed.

Lemma lenT_eq : forall {A} (l : list A) a, lenT l a = length l + a.
Proof. intros A l. induction l as [| x t IH]; intro a; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma chunkT_eq : forall {A B} f mk (z : A) (l : list A) (acc : list B),
  chunkT f mk z l acc = rev acc ++ chunkF f mk z l.
Proof.
  intros A B f. induction f as [| f IH]; intros mk z l acc.
  - simpl. rewrite rev_append_rev, app_nil_r. reflexivity.
  - destruct l as [| x t] eqn:El.
    + simpl. rewrite rev_append_rev, app_nil_r. reflexivity.
    + rewrite <- El. rewrite chunkF_cons by congruence. subst l.
      cbn [chunkT]. rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma chunk_nth : forall {A B} mk (z : A) (l : list A) j,
  nth j (chunk mk z l) (mk z z z z z z z z z z z z z z z z) = (mk (nth (16 * j + 0) l z) (nth (16 * j + 1) l z) (nth (16 * j + 2) l z) (nth (16 * j + 3) l z) (nth (16 * j + 4) l z) (nth (16 * j + 5) l z) (nth (16 * j + 6) l z) (nth (16 * j + 7) l z) (nth (16 * j + 8) l z) (nth (16 * j + 9) l z) (nth (16 * j + 10) l z) (nth (16 * j + 11) l z) (nth (16 * j + 12) l z) (nth (16 * j + 13) l z) (nth (16 * j + 14) l z) (nth (16 * j + 15) l z) : B).
Proof. intros. unfold chunk. rewrite chunkT_eq, lenT_eq. simpl. apply chunkF_nth. lia. Qed.

Lemma nth_nil0 : forall {A} j (z : A), nth j [] z = z.
Proof. intros A j z. destruct j; reflexivity. Qed.

Lemma q16 : forall x, Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 (16 * x)))) = x.
Proof.
  intro x. replace (16 * x) with (2 * (2 * (2 * (2 * x)))) by lia.
  repeat rewrite Nat.div2_double. reflexivity.
Qed.

Lemma pow16_pos : forall d, 0 < Nat.pow 16 d.
Proof. intro d. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma zt_get : forall d p b k, wget p b (zt d) k = 0.
Proof.
  induction d as [| d IH]; intros p b k.
  - simpl. repeat (destruct (ltd _ _)); reflexivity.
  - simpl. repeat (destruct (ltd _ _)); apply IH.
Qed.

Lemma levels_get : forall l d j b r, r < Nat.pow 16 (S d) ->
  wget (Nat.pow 16 d) b (nth j (levels l d) (zt d)) (b + r) = nth (j * Nat.pow 16 (S d) + r) l 0.
Proof.
  intros l d. induction d as [| d IH]; intros j b r Hr.
  - simpl levels. simpl zt. rewrite (chunk_nth WL 0 l j). rewrite wget_WL.
    rewrite pick_spec by (simpl in *; lia). cbn [fst].
    replace (b + r - b) with r by lia. rewrite Nat.div_1_r.
    simpl in Hr. do 16 (destruct r as [| r]; [cbn [nth]; f_equal; simpl; lia |]). lia.
  - simpl levels. cbn [zt]. rewrite (chunk_nth WN (zt d) (levels l d) j). rewrite wget_WN.
    rewrite pick_spec.
    + rewrite Nat.pow_succ_r' at 1. rewrite q16.
      replace (b + r - b) with r by lia.
      set (p := 16 ^ S d) in *.
      assert (Hp : 0 < p) by apply pow16_pos.
      assert (Hrr : r < 16 * p) by (unfold p in *; rewrite Nat.pow_succ_r' in Hr; exact Hr).
      pose proof (Nat.div_mod_eq r p) as Hdm. pose proof (Nat.mod_upper_bound r p ltac:(lia)) as Hm.
      assert (Hq : r / p < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
      replace (16 ^ S (S d)) with (16 * p) by (unfold p; rewrite (Nat.pow_succ_r' 16 (S d)); reflexivity).
      remember (r / p) as q eqn:Eq. clear Eq.
      replace (b + r) with (b + q * p + r mod p) by lia.
      do 16 (destruct q as [| q]; [cbn [nth]; rewrite IH by exact Hm; f_equal; nia |]). lia.
    + apply pow16_pos.
    + lia.
    + rewrite <- Nat.pow_succ_r'. lia.
Qed.

Lemma depthF_bound : forall f m p, m <= p * 16 ^ S f -> m <= p * 16 ^ S (depthF f m p).
Proof.
  induction f as [| f IH]; intros m p H; [exact H |].
  cbn [depthF]. destruct (ltd (16 * p) m) eqn:E.
  - assert (H' : m <= 16 * p * 16 ^ S f) by (rewrite (Nat.pow_succ_r' 16 (S f)) in H; lia).
    specialize (IH m (16 * p) H'). rewrite (Nat.pow_succ_r' 16 (S (depthF f m (16 * p)))). lia.
  - assert (~ 16 * p < m) by (intro HH; apply ltd_spec in HH; congruence).
    rewrite Nat.pow_succ_r', Nat.pow_0_r. lia.
Qed.

Theorem wlook_of_list16 : forall l k, wlook (of_list16 l) k = nth k l 0.
Proof.
  intros l k. unfold wlook, of_list16. cbn [wp wd wroot]. rewrite lenT_eq, Nat.add_0_r.
  set (d := depthF (length l) (length l) 1).
  destruct (ltd k (16 * 16 ^ d)) eqn:E.
  - apply ltd_spec in E. rewrite <- Nat.pow_succ_r' in E.
    pose proof (levels_get l d 0 0 k E) as G. simpl Nat.add in G. rewrite G. reflexivity.
  - assert (Hk : ~ k < 16 * 16 ^ d) by (intro HH; apply ltd_spec in HH; congruence).
    assert (Hl : length l <= 1 * 16 ^ S d).
    { apply depthF_bound. pose proof (Nat.pow_gt_lin_r 16 (S (length l)) ltac:(lia)). lia. }
    rewrite Nat.pow_succ_r' in Hl. rewrite nth_overflow by lia. reflexivity.
Qed.

(* ===== the fused check ===== *)

(* The tries are arguments, built once by check_fast, so the extracted code does
   not rebuild them per state. *)
Definition inVw (n : nat) (nfw : wt) (x : nat) : bool := ltd x n && Nat.eqb (wlook nfw x) x.

(* Each declared pair with its two tries resolved once. *)
Definition rpairsW (nE : nat) (tw : list wt) (P : option (list (nat * nat))) : list (nat * nat * wt * wt) :=
  map (fun p => (fst p, snd p, nth (fst p) tw (of_list16 []), nth (snd p) tw (of_list16 [])))
    (pairsOf nE P).

(* State s, with nfs = NF[s] and col = [T[0][s]; ...; T[nE-1][s]]. *)
Definition state_okW (n : nat) (nfw : wt) (rp : list (nat * nat * wt * wt)) (s nfs : nat) (col : list nat) : bool :=
  inVw n nfw nfs && forallb (inVw n nfw) col
  && implb (ltd s n && (Nat.eqb nfs s || Nat.eqb s 0))
       (forallb (fun q => match q with (a, b, ta, tb) =>
                   Nat.eqb (wlook ta (nth b col 0)) (wlook tb (nth a col 0)) end) rp).

Fixpoint scanW (n : nat) (nfw : wt) (rp : list (nat * nat * wt * wt)) (s : nat) (nfl : list nat)
    (rows : list (list nat)) : bool :=
  match nfl with
  | [] => true
  | x :: t => state_okW n nfw rp s x (map (hd 0) rows) && scanW n nfw rp (S s) t (map (@tl nat) rows)
  end.

Definition check_fast (n nE : nat) (NFl : list nat) (Tl : list (list nat)) (P : option (list (nat * nat))) : bool :=
  let nfw := of_list16 NFl in
  let rp := rpairsW nE (map of_list16 Tl) P in
  pairs_ok nE P && scanW n nfw rp 0 NFl Tl.

Section Fast.
  Variables (n nE : nat) (NFl : list nat) (Tl : list (list nat)) (P : option (list (nat * nat))).

  Definition NFw : wt := of_list16 NFl.
  Definition Tw : list wt := map of_list16 Tl.
  Definition inVf (x : nat) : bool := inVw n NFw x.
  Definition rpairs := rpairsW nE Tw P.
  Definition state_ok := state_okW n NFw rpairs.
  Definition scan := scanW n NFw rpairs.

  Lemma scan_iff : forall nfl rows s, scan s nfl rows = true <->
    forall i, i < length nfl -> state_ok (s + i) (nth i nfl 0) (map (fun r => nth i r 0) rows) = true.
  Proof.
    unfold scan. induction nfl as [| x t IH]; intros rows s; cbn [scanW]; fold state_ok.
    - split; [intros _ i Hi; simpl in Hi; lia | reflexivity].
    - rewrite andb_true_iff, IH.
      assert (Hhd : map (hd 0) rows = map (fun r => nth 0 r 0) rows)
        by (apply map_ext; intros [| ? ?]; reflexivity).
      assert (Htl : forall i, map (fun r => nth i r 0) (map (@tl nat) rows) = map (fun r => nth (S i) r 0) rows).
      { intro i. rewrite map_map. apply map_ext. intros [| ? ?]; [destruct i |]; reflexivity. }
      rewrite Hhd. split.
      + intros [H0 Hs] i Hi. destruct i as [| i].
        * rewrite Nat.add_0_r. exact H0.
        * specialize (Hs i ltac:(simpl in Hi; lia)). rewrite Htl in Hs.
          replace (s + S i) with (S s + i) by lia. exact Hs.
      + intros H. split.
        * specialize (H 0 ltac:(simpl; lia)). rewrite Nat.add_0_r in H. exact H.
        * intros i Hi. rewrite Htl. replace (S s + i) with (s + S i) by lia.
          apply H. simpl. lia.
  Qed.

  Let NF := of_list NFl.
  Let T := map of_list Tl.

  Lemma row_eq : forall e k, stp T e k = nth k (nth e Tl []) 0.
  Proof.
    intros e k. unfold stp, row, T. change TLeaf with (of_list []).
    rewrite map_nth. apply tget_of_list.
  Qed.

  Lemma nfv_eq : forall k, nfv NF k = nth k NFl 0.
  Proof. intro k. apply tget_of_list. Qed.

  Lemma inVf_eq : forall x, inVf x = inV n NF x.
  Proof. intro x. unfold inVf, inVw, inV, NFw. rewrite wlook_of_list16, nfv_eq, ltd_ltn. reflexivity. Qed.

  Lemma wlook_row : forall a x, wlook (nth a Tw (of_list16 [])) x = nth x (nth a Tl []) 0.
  Proof. intros a x. unfold Tw. rewrite map_nth. apply wlook_of_list16. Qed.

  Lemma col_nth : forall i b, nth b (map (fun r => nth i r 0) Tl) 0 = nth i (nth b Tl []) 0.
  Proof.
    intros i b. rewrite <- (map_nth (fun r => nth i r 0) Tl [] b).
    f_equal. destruct i; reflexivity.
  Qed.

  Hypothesis HnE : length Tl = nE.
  Hypothesis Hn : length NFl = n.

  Lemma state_ok_iff : forall i, state_ok i (nth i NFl 0) (map (fun r => nth i r 0) Tl) = true <->
    inV n NF (nfv NF i) = true
    /\ (forall e, e < nE -> inV n NF (stp T e i) = true)
    /\ (inD n NF i = true -> forall p, In p (pairsOf nE P) ->
          Nat.eqb (stp T (fst p) (stp T (snd p) i)) (stp T (snd p) (stp T (fst p) i)) = true).
  Proof.
    intro i. unfold state_ok, state_okW. fold (inVf (nth i NFl 0)). change (inVw n NFw) with inVf. rewrite !andb_true_iff, inVf_eq, nfv_eq, forallb_forall.
    assert (HinD : inD n NF i = (ltd i n && (Nat.eqb (nth i NFl 0) i || Nat.eqb i 0))).
    { unfold inD. rewrite nfv_eq, ltd_ltn. reflexivity. }
    rewrite <- HinD.
    split.
    - intros [[Hnf Hst] Hc]. split; [exact Hnf |]. split.
      + intros e He. rewrite row_eq, <- inVf_eq. apply Hst.
        apply in_map_iff. exists (nth e Tl []). split; [reflexivity |]. apply nth_In. lia.
      + intros HD q Hq. rewrite HD in Hc. simpl in Hc. rewrite forallb_forall in Hc.
        specialize (Hc (fst q, snd q, nth (fst q) Tw (of_list16 []), nth (snd q) Tw (of_list16 []))).
        cbv beta iota in Hc. rewrite !row_eq. rewrite wlook_row, wlook_row, col_nth, col_nth in Hc.
        apply Hc. unfold rpairs, rpairsW. apply in_map_iff. exists q. split; [reflexivity | exact Hq].
    - intros [Hnf [Hst Hc]]. split; [split |].
      + exact Hnf.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as [r [<- Hr]].
        apply In_nth with (d := []) in Hr. destruct Hr as [e [He <-]].
        rewrite inVf_eq, <- row_eq. apply Hst. lia.
      + destruct (inD n NF i) eqn:HD; [| reflexivity]. simpl. apply forallb_forall.
        intros q Hq. unfold rpairs, rpairsW in Hq. apply in_map_iff in Hq. destruct Hq as [pq [<- Hpq]].
        cbv beta iota. rewrite wlook_row, wlook_row, col_nth, col_nth, <- !row_eq. apply Hc; [reflexivity | exact Hpq].
  Qed.

  Lemma seq_forall : forall (f : nat -> bool) m, forallb f (seq 0 m) = true <-> forall i, i < m -> f i = true.
  Proof.
    intros f m. rewrite forallb_forall. split.
    - intros H i Hi. apply H. apply in_seq. lia.
    - intros H i Hi. apply in_seq in Hi. apply H. lia.
  Qed.

  Theorem check_fast_eq : check_fast n nE NFl Tl P = check_tables n nE NF T P.
  Proof.
    change (check_fast n nE NFl Tl P) with (pairs_ok nE P && scan 0 NFl Tl).
    unfold check_tables. rewrite <- !andb_assoc. f_equal.
    apply eq_iff_eq_true. rewrite scan_iff, Hn. rewrite !andb_true_iff.
    unfold nf_ok, steps_ok, comm_ok. rewrite !seq_forall, forallb_forall.
    setoid_rewrite seq_forall. setoid_rewrite state_ok_iff. cbn [Nat.add].
    split.
    - intros H. split; [| split].
      + intros i Hi. apply (H i Hi).
      + intros e He i Hi. apply (H i Hi). exact He.
      + intros q Hq i Hi. destruct (inD n NF i) eqn:HD; [| reflexivity]. simpl.
        apply (H i Hi); assumption.
    - intros [Hnf [Hst Hc]] i Hi. split; [| split].
      + apply Hnf, Hi.
      + intros e He. apply Hst; assumption.
      + intros HD q Hq. specialize (Hc q Hq i Hi). rewrite HD in Hc. exact Hc.
  Qed.
End Fast.

(* The runtime guarantee, for check_fast: exactly check_tables_converges. *)
Theorem check_fast_converges :
  forall n nE NFl Tl P, length NFl = n -> length Tl = nE ->
  check_fast n nE NFl Tl P = true ->
  forall es1 es2, tequiv (indep nE P) es1 es2 -> Forall (fun e => e < nE) es1 ->
  forall s, inD n (of_list NFl) s = true ->
  runT (stp (map of_list Tl)) es1 s = runT (stp (map of_list Tl)) es2 s.
Proof.
  intros n nE NFl Tl P Hn HnE Hchk. rewrite check_fast_eq in Hchk by assumption.
  intros es1 es2 Hte Hev s Hs. eapply check_tables_converges; eassumption.
Qed.
