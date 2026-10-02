(* The table oracle as extracted: check_fast, a faster computation of exactly
   check_tables.

   check_tables (TableCheck.v) spends its time in lookups: each is a walk of
   about 20 levels down a Braun tree over 2^20 states, a cache miss per level,
   and it makes two of them per declared pair per state (plus the lookups the
   nf and steps passes make). This file keeps the same property and changes
   only how it is computed:

   - one cell per state s (cells): NF[s] and the column T[0][s] ...
     T[nE-1][s], cut into blocks of 16 (blk), so that T[e][s] is found by
     skipping e / 16 blocks and four comparisons (qget). The rows are
     transposed 16 states at a time (cellsB), so the transposition allocates
     per state only the cell's own blocks;
   - a 16-ary trie (v16) over the cells, keyed most significant digit first,
     so a lookup over 2^20 keys is 5 levels instead of 20. A level finds its
     digit by four comparisons against thresholds built by addition: no
     division (Nat.div is not mapped by ExtrOcamlNatInt and extracts to a
     linear-time recursion) and no multiplication (the Go generated from this
     proof checks every product for overflow with a division);
   - one pass over the cells that, for state s, looks up the cell of each step
     target x_e = T[e][s] once (nE trie walks per state, whatever the number
     of pairs), keeps them in blocks indexed by event, and answers each
     declared pair (a, b) from them: T[a][T[b][s]] is entry a of x_b's
     column, T[b][T[a][s]] is entry b of x_a's. Each pair is split once into
     block indices and digits (rpairOf), so a pair costs four block reads.

   check_fast_eq proves check_fast equal to check_tables (on the Braun tries
   built from the same lists), so every theorem about check_tables
   (check_tables_converges and the rest) holds for check_fast unchanged
   (check_fast_converges). Every list helper it runs is tail-recursive (mapA,
   chunkH, lenT, cellsB, scanI, commI, bget, qget, bfaL, pairsAll), so the
   extracted code's stack depth does not grow with the number of states,
   events or declared pairs; the only non-tail recursion is the trie depth, at
   most 8 levels. That matters because OCaml 4.14 native code runs on the
   8 MiB system stack: check_tables' extraction overflowed it at 2^20 states.
   Axiom-free, no PArray, no primitive integers. *)

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

(* Case on every comparison of a comparison tree, one branch at a time (the
   other branch is dropped at once, so the cases are the tree's leaves, not
   every combination of its comparisons). *)
Ltac split_ltd :=
  cbv zeta;
  repeat match goal with
         | |- context [Compare_dec.lt_dec ?a ?c] =>
           let H := fresh "H" in destruct (Compare_dec.lt_dec a c) as [H | H]; cbv beta iota
         end.

(* ===== blocks of 16 ===== *)

Inductive blk (A : Type) := B16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A).
Arguments B16 {A}.

Definition l16 {A : Type} (t : blk A) : list A :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15] end.

(* Entry k - b of t, for b <= k < b + 16, by binary search on k. It is also
   the leaf step of the trie lookup vget (vget_VL), which the extracted code
   runs: the thresholds are sums, so nothing is subtracted (nat subtraction
   extracts to a clamp at 0 through a polymorphic max) and nothing is
   multiplied. *)
Definition bsel {A : Type} (b k : nat) (t : blk A) : A :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    (let t8_8 := b + 8 in if ltd k t8_8 then (let t4_4 := b + 4 in if ltd k t4_4 then (let t2_2 := b + 2 in if ltd k t2_2 then (let t1_1 := b + 1 in if ltd k t1_1 then x0 else x1) else (let t3_1 := t2_2 + 1 in if ltd k t3_1 then x2 else x3)) else (let t6_2 := t4_4 + 2 in if ltd k t6_2 then (let t5_1 := t4_4 + 1 in if ltd k t5_1 then x4 else x5) else (let t7_1 := t6_2 + 1 in if ltd k t7_1 then x6 else x7))) else (let t12_4 := t8_8 + 4 in if ltd k t12_4 then (let t10_2 := t8_8 + 2 in if ltd k t10_2 then (let t9_1 := t8_8 + 1 in if ltd k t9_1 then x8 else x9) else (let t11_1 := t10_2 + 1 in if ltd k t11_1 then x10 else x11)) else (let t14_2 := t12_4 + 2 in if ltd k t14_2 then (let t13_1 := t12_4 + 1 in if ltd k t13_1 then x12 else x13) else (let t15_1 := t14_2 + 1 in if ltd k t15_1 then x14 else x15)))) end.

Lemma bsel_spec : forall {A : Type} (b k : nat) (t : blk A) (d : A), b <= k -> k < b + 16 ->
  bsel b k t = nth (k - b) (l16 t) d.
Proof.
  intros A b k [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15] d Hb Hk.
  unfold bsel, l16. split_ltd;
  remember (k - b) as j eqn:Ej;
  do 16 (destruct j as [| j]; [cbn [nth]; first [reflexivity | exfalso; lia] |]); exfalso; lia.
Qed.

Definition bmap {A B : Type} (g : A -> B) (t : blk A) : blk B :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    B16 (g x0) (g x1) (g x2) (g x3) (g x4) (g x5) (g x6) (g x7) (g x8) (g x9) (g x10) (g x11) (g x12) (g x13) (g x14) (g x15) end.

Lemma bsel_map : forall {A B : Type} (g : A -> B) b k t, bsel b k (bmap g t) = g (bsel b k t).
Proof. intros A B g b k [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15]. unfold bsel, bmap. split_ltd; reflexivity. Qed.

(* Entry k - b of the concatenated blocks, z past their end: the reading that
   qget and bfaL are proven against (bget_chunk relates it to list nth). *)
Fixpoint bget {A : Type} (z : A) (bs : list (blk A)) (b k : nat) : A :=
  match bs with
  | [] => z
  | t :: r => if ltd k (b + 16) then bsel b k t else bget z r (b + 16) k
  end.

(* f holds on the entries of t whose index b + i is below m. *)
Definition bfa1 {A : Type} (f : A -> bool) (m b : nat) (t : blk A) : bool :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    implb (ltd b m) (f x0)
    && implb (ltd (b + 1) m) (f x1)
    && implb (ltd (b + 2) m) (f x2)
    && implb (ltd (b + 3) m) (f x3)
    && implb (ltd (b + 4) m) (f x4)
    && implb (ltd (b + 5) m) (f x5)
    && implb (ltd (b + 6) m) (f x6)
    && implb (ltd (b + 7) m) (f x7)
    && implb (ltd (b + 8) m) (f x8)
    && implb (ltd (b + 9) m) (f x9)
    && implb (ltd (b + 10) m) (f x10)
    && implb (ltd (b + 11) m) (f x11)
    && implb (ltd (b + 12) m) (f x12)
    && implb (ltd (b + 13) m) (f x13)
    && implb (ltd (b + 14) m) (f x14)
    && implb (ltd (b + 15) m) (f x15) end.

(* f holds on entries b .. m - 1 of the concatenated blocks. *)
Fixpoint bfaL {A : Type} (f : A -> bool) (m b : nat) (bs : list (blk A)) : bool :=
  match bs with
  | [] => true
  | t :: r => bfa1 f m b t && bfaL f m (b + 16) r
  end.

(* ===== grouping a list 16 at a time ===== *)

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

(* Tail-recursive forms, so the extracted code's stack does not grow with the
   input: OCaml 4.14 native code has the 8 MiB system stack, and List.length
   and chunkF recurse once per element (or per group of 16). *)
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

(* chunkT reading each group by hd and tl: 2 list steps per element, where
   chunkT's nth takes 8.5 on average. *)
Fixpoint chunkH {A B : Type} (f : nat) mk (z : A) (l : list A) (acc : list B) : list B :=
  match f with
  | 0 => rev_append acc []
  | S f' => match l with
            | [] => rev_append acc []
            | _ => let l1 := tl l in let l2 := tl l1 in let l3 := tl l2 in let l4 := tl l3 in let l5 := tl l4 in let l6 := tl l5 in let l7 := tl l6 in let l8 := tl l7 in let l9 := tl l8 in let l10 := tl l9 in let l11 := tl l10 in let l12 := tl l11 in let l13 := tl l12 in let l14 := tl l13 in let l15 := tl l14 in
                   chunkH f' mk z (tl l15) (mk (hd z l) (hd z l1) (hd z l2) (hd z l3) (hd z l4) (hd z l5) (hd z l6) (hd z l7) (hd z l8) (hd z l9) (hd z l10) (hd z l11) (hd z l12) (hd z l13) (hd z l14) (hd z l15) :: acc)
            end
  end.

Lemma chunkH_eq : forall {A B} f mk (z : A) (l : list A) (acc : list B), chunkH f mk z l acc = chunkT f mk z l acc.
Proof.
  intros A B f. induction f as [| f IH]; intros mk z l acc; [reflexivity |].
  destruct l as [| x0 l]; [reflexivity |].
  do 15 (destruct l as [| ? l]; [cbn; apply IH |]). cbn. apply IH.
Qed.

Definition chunk {A B : Type} mk (z : A) (l : list A) : list B := chunkH (lenT l 0) mk z l [].

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

Lemma chunk_eq : forall {A B} mk (z : A) (l : list A), (chunk mk z l : list B) = chunkF (length l) mk z l.
Proof. intros. unfold chunk. rewrite chunkH_eq, chunkT_eq, lenT_eq, Nat.add_0_r. reflexivity. Qed.

Lemma chunk_nth : forall {A B} mk (z : A) (l : list A) j,
  nth j (chunk mk z l) (mk z z z z z z z z z z z z z z z z) = (mk (nth (16 * j + 0) l z) (nth (16 * j + 1) l z) (nth (16 * j + 2) l z) (nth (16 * j + 3) l z) (nth (16 * j + 4) l z) (nth (16 * j + 5) l z) (nth (16 * j + 6) l z) (nth (16 * j + 7) l z) (nth (16 * j + 8) l z) (nth (16 * j + 9) l z) (nth (16 * j + 10) l z) (nth (16 * j + 11) l z) (nth (16 * j + 12) l z) (nth (16 * j + 13) l z) (nth (16 * j + 14) l z) (nth (16 * j + 15) l z) : B).
Proof. intros. rewrite chunk_eq. apply chunkF_nth. lia. Qed.

(* ===== reading blocks ===== *)

Lemma nth_l16_chunk : forall {A} (l : list A) z d i, i < 16 ->
  nth i (l16 (B16 (nth 0 l z) (nth 1 l z) (nth 2 l z) (nth 3 l z) (nth 4 l z) (nth 5 l z) (nth 6 l z) (nth 7 l z) (nth 8 l z) (nth 9 l z) (nth 10 l z) (nth 11 l z) (nth 12 l z) (nth 13 l z) (nth 14 l z) (nth 15 l z))) d
  = nth i l z.
Proof. intros A l z d i Hi. do 16 (destruct i as [| i]; [reflexivity |]). lia. Qed.

Lemma bget_chunkF : forall {A} (z : A) f l b k, length l <= 16 * f -> b <= k ->
  bget z (chunkF f B16 z l) b k = nth (k - b) l z.
Proof.
  intros A z f. induction f as [| f IH]; intros l b k Hl Hb.
  - destruct l; [| simpl in Hl; lia]. simpl. destruct (k - b); reflexivity.
  - destruct l as [| x t] eqn:El; [simpl; destruct (k - b); reflexivity |].
    rewrite <- El. rewrite chunkF_cons by congruence. cbn [bget].
    destruct (Compare_dec.lt_dec k (b + 16)) as [H | H]; cbv beta iota.
    + rewrite (bsel_spec _ _ _ z) by lia. apply nth_l16_chunk. lia.
    + rewrite IH; [| rewrite skipn_length; subst l; simpl in Hl |- *; lia | lia].
      rewrite skipn_nth. f_equal. lia.
Qed.

Theorem bget_chunk : forall {A} (z : A) l k, bget z (chunk B16 z l) 0 k = nth k l z.
Proof. intros. rewrite chunk_eq, bget_chunkF by lia. f_equal. lia. Qed.

Lemma chunkF_length : forall {A B} f mk (z : A) (l : list A), length l <= 16 * f ->
  length l <= 16 * length (chunkF f mk z l : list B).
Proof.
  intros A B f. induction f as [| f IH]; intros mk z l Hl; [simpl in *; lia |].
  destruct l as [| x t] eqn:El; [simpl; lia |].
  rewrite <- El in Hl |- *. rewrite chunkF_cons by congruence. cbn [length].
  pose proof (IH mk z (skipn 16 l)) as H. rewrite skipn_length in H.
  specialize (H ltac:(lia)). lia.
Qed.

Lemma chunk_length : forall {A B} mk (z : A) (l : list A), length l <= 16 * length (chunk mk z l : list B).
Proof. intros. rewrite chunk_eq. apply chunkF_length. lia. Qed.

Lemma bget_map : forall {A B} (z : A) (z' : B) (g : A -> B) bs b k, b <= k -> k < b + 16 * length bs ->
  bget z' (map (bmap g) bs) b k = g (bget z bs b k).
Proof.
  intros A B z z' g bs. induction bs as [| t r IH]; intros b k Hb Hk; [simpl in Hk; lia |].
  cbn [map bget]. destruct (Compare_dec.lt_dec k (b + 16)); cbv beta iota.
  - apply bsel_map.
  - apply IH; simpl in Hk; lia.
Qed.

Lemma bfa1_iff : forall {A} (f : A -> bool) m b (t : blk A) z, bfa1 f m b t = true <->
  (forall i, i < 16 -> b + i < m -> f (nth i (l16 t) z) = true).
Proof.
  intros A f m b [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15] z. unfold bfa1, l16. rewrite !andb_true_iff, !implb_true_iff.
  setoid_rewrite ltd_spec. split.
  - intros H. decompose [and] H. clear H. intros i Hi Hm.
    do 16 (destruct i as [| i]; [cbn [nth]; match goal with Hx : _ -> f ?x = true |- f ?x = true => apply Hx; lia end |]).
    lia.
  - intros H. repeat split; intro Hm;
    first [match type of Hm with b + ?c < m => apply (H c); lia end | apply (H 0); lia].
Qed.

Lemma bfaL_iff : forall {A} (z : A) f m bs b, bfaL f m b bs = true <->
  forall k, b <= k -> k < m -> k < b + 16 * length bs -> f (bget z bs b k) = true.
Proof.
  intros A z f m bs. induction bs as [| t r IH]; intro b; cbn [bfaL].
  - split; [intros _ k Hb Hm Hk; simpl in Hk; lia | reflexivity].
  - rewrite andb_true_iff, IH, (bfa1_iff _ _ _ _ z). split.
    + intros [H0 H1] k Hb Hm Hk. cbn [bget].
      destruct (Compare_dec.lt_dec k (b + 16)) as [Hl | Hl]; cbv beta iota.
      * rewrite (bsel_spec _ _ _ z) by lia. apply H0; lia.
      * apply H1; simpl in Hk; lia.
    + intros H. split.
      * intros i Hi Hm. specialize (H (b + i) ltac:(lia) Hm ltac:(simpl; lia)). cbn [bget] in H.
        destruct (Compare_dec.lt_dec (b + i) (b + 16)); [| lia]. cbv beta iota in H.
        rewrite (bsel_spec _ _ _ z) in H by lia. replace (b + i - b) with i in H by lia. exact H.
      * intros k Hb Hm Hk. specialize (H k ltac:(lia) Hm ltac:(simpl; lia)). cbn [bget] in H.
        destruct (Compare_dec.lt_dec k (b + 16)); [lia | exact H].
Qed.

(* Entry d of t, for d < 16: four comparisons against constants. *)
Definition dsel {A : Type} (d : nat) (t : blk A) : A :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    (if ltd d 8 then (if ltd d 4 then (if ltd d 2 then (if ltd d 1 then x0 else x1) else (if ltd d 3 then x2 else x3)) else (if ltd d 6 then (if ltd d 5 then x4 else x5) else (if ltd d 7 then x6 else x7))) else (if ltd d 12 then (if ltd d 10 then (if ltd d 9 then x8 else x9) else (if ltd d 11 then x10 else x11)) else (if ltd d 14 then (if ltd d 13 then x12 else x13) else (if ltd d 15 then x14 else x15)))) end.

Lemma dsel_spec : forall {A : Type} d (t : blk A) z, d < 16 -> dsel d t = nth d (l16 t) z.
Proof.
  intros A d [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15] z Hd. unfold dsel, l16. split_ltd;
  do 16 (destruct d as [| d]; [cbn [nth]; first [reflexivity | exfalso; lia] |]); exfalso; lia.
Qed.

(* Entry 16 * q + d of the concatenated blocks (d < 16), z past their end.
   With q and d computed once per declared pair, a read is q list steps and
   four comparisons against constants. *)
Fixpoint qget {A : Type} (z : A) (bs : list (blk A)) (q d : nat) : A :=
  match bs with
  | [] => z
  | t :: r => match q with 0 => dsel d t | S q' => qget z r q' d end
  end.

Lemma qget_bget : forall {A} (z : A) bs b q d, d < 16 -> qget z bs q d = bget z bs b (b + 16 * q + d).
Proof.
  intros A z bs. induction bs as [| t r IH]; intros b q d Hd; [reflexivity |].
  cbn [qget bget]. destruct q as [| q].
  - destruct (Compare_dec.lt_dec (b + 16 * 0 + d) (b + 16)); [| lia]. cbv beta iota.
    rewrite (dsel_spec _ _ z), (bsel_spec _ _ _ z) by lia. f_equal. lia.
  - destruct (Compare_dec.lt_dec (b + 16 * S q + d) (b + 16)); [lia |]. cbv beta iota.
    rewrite (IH (b + 16)) by exact Hd. f_equal. lia.
Qed.

(* a / 16, by halving (Nat.div is not mapped by ExtrOcamlNatInt). *)
Definition hi16 (a : nat) : nat := Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 a))).

Lemma hi16_spec : forall a, 16 * hi16 a + (a - 16 * hi16 a) = a /\ a - 16 * hi16 a < 16.
Proof.
  intro a. assert (H : hi16 a = a / 16).
  { unfold hi16. rewrite !Nat.div2_div, !Nat.Div0.div_div. reflexivity. }
  rewrite H. pose proof (Nat.div_mod a 16 ltac:(lia)). pose proof (Nat.mod_upper_bound a 16 ltac:(lia)). lia.
Qed.

Lemma qget_at : forall {A} (z : A) bs a, qget z bs (hi16 a) (a - 16 * hi16 a) = bget z bs 0 a.
Proof.
  intros A z bs a. destruct (hi16_spec a) as [E D].
  rewrite (qget_bget z bs 0) by exact D. f_equal. lia.
Qed.

(* ===== a 16-ary trie ===== *)

Inductive v16 (A : Type) :=
| VL (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A)
| VN (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : v16 A).
Arguments VL {A}.
Arguments VN {A}.

(* Lookup in a trie whose children each cover p keys (p = 16^depth), the trie
   covering keys b to b + 16 * p - 1. It recurses structurally and allocates
   nothing; the digit at each level is found by four comparisons against
   thresholds built by addition. *)
Fixpoint vget {A : Type} (p b : nat) (t : v16 A) (k : nat) : A :=
  match t with
  | VL x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => (let t8_8 := b + 8 in if ltd k t8_8 then (let t4_4 := b + 4 in if ltd k t4_4 then (let t2_2 := b + 2 in if ltd k t2_2 then (let t1_1 := b + 1 in if ltd k t1_1 then x0 else x1) else (let t3_1 := t2_2 + 1 in if ltd k t3_1 then x2 else x3)) else (let t6_2 := t4_4 + 2 in if ltd k t6_2 then (let t5_1 := t4_4 + 1 in if ltd k t5_1 then x4 else x5) else (let t7_1 := t6_2 + 1 in if ltd k t7_1 then x6 else x7))) else (let t12_4 := t8_8 + 4 in if ltd k t12_4 then (let t10_2 := t8_8 + 2 in if ltd k t10_2 then (let t9_1 := t8_8 + 1 in if ltd k t9_1 then x8 else x9) else (let t11_1 := t10_2 + 1 in if ltd k t11_1 then x10 else x11)) else (let t14_2 := t12_4 + 2 in if ltd k t14_2 then (let t13_1 := t12_4 + 1 in if ltd k t13_1 then x12 else x13) else (let t15_1 := t14_2 + 1 in if ltd k t15_1 then x14 else x15))))
  | VN c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 =>
    let q := Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p))) in
    let p2 := p + p in let p4 := p2 + p2 in let p8 := p4 + p4 in
    (let t8_8 := b + p8 in if ltd k t8_8 then (let t4_4 := b + p4 in if ltd k t4_4 then (let t2_2 := b + p2 in if ltd k t2_2 then (let t1_1 := b + p in if ltd k t1_1 then vget q b c0 k else vget q t1_1 c1 k) else (let t3_1 := t2_2 + p in if ltd k t3_1 then vget q t2_2 c2 k else vget q t3_1 c3 k)) else (let t6_2 := t4_4 + p2 in if ltd k t6_2 then (let t5_1 := t4_4 + p in if ltd k t5_1 then vget q t4_4 c4 k else vget q t5_1 c5 k) else (let t7_1 := t6_2 + p in if ltd k t7_1 then vget q t6_2 c6 k else vget q t7_1 c7 k))) else (let t12_4 := t8_8 + p4 in if ltd k t12_4 then (let t10_2 := t8_8 + p2 in if ltd k t10_2 then (let t9_1 := t8_8 + p in if ltd k t9_1 then vget q t8_8 c8 k else vget q t9_1 c9 k) else (let t11_1 := t10_2 + p in if ltd k t11_1 then vget q t10_2 c10 k else vget q t11_1 c11 k)) else (let t14_2 := t12_4 + p2 in if ltd k t14_2 then (let t13_1 := t12_4 + p in if ltd k t13_1 then vget q t12_4 c12 k else vget q t13_1 c13 k) else (let t15_1 := t14_2 + p in if ltd k t15_1 then vget q t14_2 c14 k else vget q t15_1 c15 k))))
  end.

Lemma vget_VL : forall {A} p b k (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A),
  vget p b (VL x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) k = bsel b k (B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15).
Proof. reflexivity. Qed.

Lemma vget_VN : forall {A} p b k (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : v16 A),
  0 < p -> b <= k -> k < b + 16 * p ->
  vget p b (VN c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15) k =
  vget (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) (b + (k - b) / p * p)
    (nth ((k - b) / p) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15] c15) k.
Proof.
  intros A p b k c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 Hp Hb Hk.
  pose proof (Nat.div_mod_eq (k - b) p) as Hdm. pose proof (Nat.mod_upper_bound (k - b) p ltac:(lia)) as Hm.
  assert (Hj : (k - b) / p < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
  remember ((k - b) / p) as j eqn:Ej. remember ((k - b) mod p) as r eqn:Er.
  remember (Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 p)))) as q eqn:Eq.
  cbn [vget]. rewrite <- Eq. split_ltd;
  do 16 (destruct j as [| j]; [cbn [nth]; f_equal; lia |]); exfalso; lia.
Qed.

(* The all-z trie of depth d (shared, so O(d) to build). *)
Fixpoint ztV {A : Type} (z : A) (d : nat) : v16 A :=
  match d with
  | 0 => VL z z z z z z z z z z z z z z z z
  | S d' => let t := ztV z d' in VN t t t t t t t t t t t t t t t t
  end.

Fixpoint levelsV {A : Type} (z : A) (l : list A) (d : nat) : list (v16 A) :=
  match d with
  | 0 => chunk VL z l
  | S d' => chunk VN (ztV z d') (levelsV z l d')
  end.

(* The least d (up to fuel) with 16^(d+1) >= m, given p = 16^(current d). *)
Fixpoint depthF (f m p : nat) : nat :=
  match f with
  | 0 => 0
  | S f' => if ltd (16 * p) m then S (depthF f' m (16 * p)) else 0
  end.

(* 16^(depthF f m p) * p, computed alongside depthF: Nat.pow is extracted from
   Nat.mul inside the Nat module, which ExtrOcamlNatInt does not map, so it is
   unary there (pow 16 6 overflows the stack). Top-level multiplication is
   mapped to OCaml's ( * ). *)
Fixpoint powF (f m p : nat) : nat :=
  match f with
  | 0 => p
  | S f' => if ltd (16 * p) m then powF f' m (16 * p) else p
  end.

Lemma powF_eq : forall f m p, powF f m p = p * 16 ^ depthF f m p.
Proof.
  induction f as [| f IH]; intros m p; cbn [powF depthF].
  - simpl. lia.
  - destruct (ltd (16 * p) m); [rewrite IH; simpl; lia | simpl; lia].
Qed.

(* The bound 16 * p is computed once, here, not per lookup. *)
Record vt (A : Type) := { vp : nat; vlim : nat; vroot : v16 A }.
Arguments vp {A}.
Arguments vlim {A}.
Arguments vroot {A}.

Definition of_listV {A : Type} (z : A) (l : list A) : vt A :=
  let m := lenT l 0 in
  let d := depthF m m 1 in
  let p := powF m m 1 in
  {| vp := p; vlim := 16 * p; vroot := nth 0 (levelsV z l d) (ztV z d) |}.

Definition vlook {A : Type} (z : A) (t : vt A) (k : nat) : A :=
  if ltd k (vlim t) then vget (vp t) 0 (vroot t) k else z.

(* ===== correctness of the trie ===== *)

Lemma q16 : forall x, Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 (16 * x)))) = x.
Proof.
  intro x. replace (16 * x) with (2 * (2 * (2 * (2 * x)))) by lia.
  repeat rewrite Nat.div2_double. reflexivity.
Qed.

Lemma pow16_pos : forall d, 0 < Nat.pow 16 d.
Proof. intro d. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma levelsV_get : forall {A} (z : A) l d j b r, r < Nat.pow 16 (S d) ->
  vget (Nat.pow 16 d) b (nth j (levelsV z l d) (ztV z d)) (b + r) = nth (j * Nat.pow 16 (S d) + r) l z.
Proof.
  intros A z l d. induction d as [| d IH]; intros j b r Hr.
  - simpl levelsV. simpl ztV. rewrite (chunk_nth VL z l j). rewrite vget_VL.
    rewrite (bsel_spec _ _ _ z) by (simpl in *; lia). cbn [l16].
    replace (b + r - b) with r by lia.
    simpl in Hr. do 16 (destruct r as [| r]; [cbn [nth]; f_equal; simpl; lia |]). lia.
  - simpl levelsV. cbn [ztV]. rewrite (chunk_nth VN (ztV z d) (levelsV z l d) j).
    set (p := 16 ^ S d) in *.
    assert (Hp : 0 < p) by apply pow16_pos.
    assert (Hrr : r < 16 * p) by (unfold p in *; rewrite Nat.pow_succ_r' in Hr; exact Hr).
    rewrite vget_VN by lia.
    unfold p at 1. rewrite Nat.pow_succ_r' at 1. rewrite q16. fold p.
    replace (b + r - b) with r by lia.
    pose proof (Nat.div_mod_eq r p) as Hdm. pose proof (Nat.mod_upper_bound r p ltac:(lia)) as Hm.
    assert (Hq : r / p < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    replace (16 ^ S (S d)) with (16 * p) by (unfold p; rewrite (Nat.pow_succ_r' 16 (S d)); reflexivity).
    remember (r / p) as q eqn:Eq. clear Eq.
    replace (b + r) with (b + q * p + r mod p) by lia.
    do 16 (destruct q as [| q]; [cbn [nth]; rewrite IH by exact Hm; f_equal; nia |]). lia.
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

Theorem vlook_of_listV : forall {A} (z : A) l k, vlook z (of_listV z l) k = nth k l z.
Proof.
  intros A z l k. unfold vlook, of_listV. cbn [vp vlim vroot]. rewrite lenT_eq, Nat.add_0_r, powF_eq, Nat.mul_1_l.
  set (d := depthF (length l) (length l) 1).
  destruct (ltd k (16 * 16 ^ d)) eqn:E.
  - apply ltd_spec in E. rewrite <- Nat.pow_succ_r' in E.
    pose proof (levelsV_get z l d 0 0 k E) as G. simpl Nat.add in G. rewrite G. reflexivity.
  - assert (Hk : ~ k < 16 * 16 ^ d) by (intro HH; apply ltd_spec in HH; congruence).
    assert (Hl : length l <= 1 * 16 ^ S d).
    { apply depthF_bound. pose proof (Nat.pow_gt_lin_r 16 (S (length l)) ltac:(lia)). lia. }
    rewrite Nat.pow_succ_r' in Hl. rewrite nth_overflow by lia. reflexivity.
Qed.

(* ===== tail-recursive list builders ===== *)

(* The extracted code must run in stack independent of the input: OCaml 4.14
   native code has the 8 MiB system stack, and List.map recurses once per
   element (events, declared pairs). *)
Fixpoint mapA {A B : Type} (f : A -> B) (l : list A) (acc : list B) : list B :=
  match l with [] => rev_append acc [] | x :: t => mapA f t (f x :: acc) end.

Definition mapT {A B : Type} (f : A -> B) (l : list A) : list B := mapA f l [].

Lemma mapA_eq : forall {A B} (f : A -> B) l acc, mapA f l acc = rev acc ++ map f l.
Proof.
  intros A B f l. induction l as [| x t IH]; intro acc; simpl.
  - rewrite rev_append_rev, app_nil_r. reflexivity.
  - rewrite IH. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma mapT_eq : forall {A B} (f : A -> B) l, mapT f l = map f l.
Proof. intros. unfold mapT. rewrite mapA_eq. reflexivity. Qed.

(* Every pair (i, j) with i < j < nE, built tail-recursively (allPairs, in
   TableCheck.v, recurses once per event and per pair). *)
Fixpoint pairsRow (i j k : nat) (acc : list (nat * nat)) : list (nat * nat) :=
  match k with 0 => acc | S k' => pairsRow i (S j) k' ((i, j) :: acc) end.

Fixpoint pairsAll (nE i k : nat) (acc : list (nat * nat)) : list (nat * nat) :=
  match k with 0 => acc | S k' => pairsAll nE (S i) k' (pairsRow i (S i) (nE - S i) acc) end.

Definition allPairsT (nE : nat) : list (nat * nat) := pairsAll nE 0 nE [].

Lemma pairsRow_in : forall i j k acc p,
  In p (pairsRow i j k acc) <-> (fst p = i /\ j <= snd p < j + k) \/ In p acc.
Proof.
  intros i j k. revert j. induction k as [| k IH]; intros j acc [a b]; simpl.
  - split; [tauto | intros [[_ H] | H]; [lia | exact H]].
  - rewrite IH. simpl. split.
    + intros [[Ha Hb] | [Heq | Hin]]; [left; split; [exact Ha | lia] | | tauto].
      inversion Heq; subst. left. split; [reflexivity | lia].
    + intros [[Ha Hb] | Hin].
      * destruct (Nat.eq_dec b j) as [-> | Hne]; [right; left; subst; reflexivity |].
        left. split; [exact Ha | lia].
      * right; right; exact Hin.
Qed.

Lemma pairsAll_in : forall nE i k acc p,
  In p (pairsAll nE i k acc) <-> (i <= fst p < i + k /\ fst p < snd p < nE) \/ In p acc.
Proof.
  intros nE i k. revert i. induction k as [| k IH]; intros i acc [a b]; simpl.
  - split; [tauto | intros [[H _] | H]; [lia | exact H]].
  - rewrite IH, pairsRow_in. simpl. split.
    + intros [[Ha Hb] | [[Ha Hb] | Hin]]; [left; lia | left; subst; lia | tauto].
    + intros [[Ha Hb] | Hin]; [| tauto].
      destruct (Nat.eq_dec a i) as [-> | Hne]; [right; left; lia | left; lia].
Qed.

Lemma allPairs_in_iff : forall nE a b, In (a, b) (allPairs nE) <-> a < b /\ b < nE.
Proof.
  intros nE a b. unfold allPairs. rewrite in_flat_map. split.
  - intros [i [Hi Hm]]. apply in_seq in Hi. apply in_map_iff in Hm.
    destruct Hm as [j [Heq Hj]]. inversion Heq; subst. apply in_seq in Hj. lia.
  - intros [Hab Hb]. exists a. split; [apply in_seq; lia |].
    apply in_map_iff. exists b. split; [reflexivity | apply in_seq; lia].
Qed.

Definition pairsOfT (nE : nat) (P : option (list (nat * nat))) : list (nat * nat) :=
  match P with None => allPairsT nE | Some l => l end.

Lemma pairsOfT_in : forall nE P p, In p (pairsOfT nE P) <-> In p (pairsOf nE P).
Proof.
  intros nE [l |] [a b]; unfold pairsOfT, pairsOf; [reflexivity |].
  unfold allPairsT. rewrite pairsAll_in, allPairs_in_iff. simpl. lia.
Qed.

Definition pairs_okW (nE : nat) (P : option (list (nat * nat))) : bool :=
  forallb (fun p => ltd (fst p) nE && ltd (snd p) nE) (pairsOfT nE P).

Lemma pairs_okW_eq : forall nE P, pairs_okW nE P = pairs_ok nE P.
Proof.
  intros nE P. apply eq_iff_eq_true. unfold pairs_okW, pairs_ok. rewrite !forallb_forall.
  split; intros H p Hp.
  - rewrite <- ltd_ltn, <- ltd_ltn. apply H. apply pairsOfT_in. exact Hp.
  - rewrite ltd_ltn, ltd_ltn. apply H. apply pairsOfT_in. exact Hp.
Qed.

(* ===== the cells ===== *)

(* State lk's cell: its normal form and its column T[0][lk] ... T[nE-1][lk]
   in blocks of 16. *)
Record cell := { lk : nat; lnf : nat; lcol : list (blk nat) }.

(* The cell lookups return past the last state: its key n fails cell_ok. *)
Definition zcell (n : nat) : cell := {| lk := n; lnf := 0; lcol := [] |}.

Definition cell_ok (n : nat) (c : cell) : bool := ltd (lk c) n && Nat.eqb (lnf c) (lk c).

Definition zb : blk nat := B16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0.

(* The event blocks of one block of 16 states: entry e of the result is block
   g of row e, where rowsB holds each row from block g on. *)
Definition hgroup (rowsB : list (list (blk nat))) : list (blk (blk nat)) := chunk B16 zb (mapT (hd zb) rowsB).

(* One cell per state, transposing the rows 16 states at a time: each row is
   cut into blocks of 16 states once (rowsB), and the cell of state s is digit
   d = s mod 16 of the current block of every row (hb). So the transposition
   allocates per state only the cell's own blocks, not a list over the events;
   d = 16 means the next block is due. *)
Fixpoint cellsB (s d : nat) (nfl : list nat) (hb : list (blk (blk nat))) (rowsB : list (list (blk nat)))
    (acc : list cell) : list cell :=
  match nfl with
  | [] => rev_append acc []
  | x :: t =>
    if ltd d 16 then
      cellsB (S s) (S d) t hb rowsB ({| lk := s; lnf := x; lcol := mapT (bmap (dsel d)) hb |} :: acc)
    else
      let hb' := hgroup rowsB in
      cellsB (S s) 1 t hb' (mapT (@tl (blk nat)) rowsB) ({| lk := s; lnf := x; lcol := mapT (bmap (dsel 0)) hb' |} :: acc)
  end.

Definition cells (NFl : list nat) (Tl : list (list nat)) : list cell :=
  cellsB 0 16 NFl [] (mapT (chunk B16 0) Tl) [].

Lemma cellsB_app : forall nfl s d hb rowsB acc, cellsB s d nfl hb rowsB acc = rev acc ++ cellsB s d nfl hb rowsB [].
Proof.
  induction nfl as [| x t IH]; intros s d hb rowsB acc; cbn [cellsB].
  - rewrite rev_append_rev. reflexivity.
  - destruct (Compare_dec.lt_dec d 16); cbv beta iota zeta; rewrite IH, (IH _ _ _ _ [_]); cbn [rev app];
    rewrite <- app_assoc; reflexivity.
Qed.

Lemma hd_skipn : forall {A} (l : list A) g z, hd z (skipn g l) = nth g l z.
Proof. intros A l g z. rewrite <- (Nat.add_0_r g) at 2. rewrite <- skipn_nth. destruct (skipn g l); reflexivity. Qed.

Lemma tl_skipn : forall {A} g (l : list A), tl (skipn g l) = skipn (S g) l.
Proof.
  intros A g. induction g as [| g IH]; intros [| x l]; try reflexivity.
  cbn [skipn]. apply IH.
Qed.

Lemma nth_map_d : forall {A B} (f : A -> B) l d d' i, f d = d' -> nth i (map f l) d' = f (nth i l d).
Proof. intros A B f l d d' i <-. apply map_nth. Qed.

(* A declared pair (a, b) with a and b each split once into a block index
   and a digit, for qget. *)
Record rpair := { qa : nat; da : nat; qb : nat; db : nat }.

Definition rpairOf (p : nat * nat) : rpair :=
  let a := fst p in let b := snd p in
  let ha := hi16 a in let hb := hi16 b in
  {| qa := ha; da := a - 16 * ha; qb := hb; db := b - 16 * hb |}.

(* ls holds the cell of each step target x_e; T[a][x_b] is entry a of x_b's
   column, T[b][x_a] entry b of x_a's. *)
Definition pair_okI (z : cell) (ls : list (blk cell)) (r : rpair) : bool :=
  Nat.eqb (qget 0 (lcol (qget z ls (qb r) (db r))) (qa r) (da r))
          (qget 0 (lcol (qget z ls (qa r) (da r))) (qb r) (db r)).

Fixpoint commI (z : cell) (ls : list (blk cell)) (rp : list rpair) : bool :=
  match rp with [] => true | r :: t => pair_okI z ls r && commI z ls t end.

Lemma commI_eq : forall z ls rp, commI z ls rp = forallb (pair_okI z ls) rp.
Proof. intros z ls rp. induction rp as [| r t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* ===== the fused check ===== *)

(* State s with cell c. ls holds the cell of each step target x_e = T[e][s],
   in blocks indexed by event. *)
Definition state_okI (n nE : nat) (ct : vt cell) (rp : list rpair) (s : nat) (c : cell) : bool :=
  let ls := mapT (bmap (vlook (zcell n) ct)) (lcol c) in
  cell_ok n (vlook (zcell n) ct (lnf c))
  && bfaL (cell_ok n) nE 0 ls
  && implb (ltd s n && (Nat.eqb (lnf c) s || Nat.eqb s 0)) (commI (zcell n) ls rp).

Fixpoint scanI (n nE : nat) (ct : vt cell) (rp : list rpair) (s : nat) (cs : list cell) : bool :=
  match cs with
  | [] => true
  | c :: t => state_okI n nE ct rp s c && scanI n nE ct rp (S s) t
  end.

Definition check_fast (n nE : nat) (NFl : list nat) (Tl : list (list nat)) (P : option (list (nat * nat))) : bool :=
  let cs := cells NFl Tl in
  pairs_okW nE P && scanI n nE (of_listV (zcell n) cs) (mapT rpairOf (pairsOfT nE P)) 0 cs.

Lemma scanI_iff : forall n nE ct rp cs s, scanI n nE ct rp s cs = true <->
  forall i, i < length cs -> state_okI n nE ct rp (s + i) (nth i cs (zcell n)) = true.
Proof.
  intros n nE ct rp. induction cs as [| c t IH]; intro s; cbn [scanI].
  - split; [intros _ i Hi; simpl in Hi; lia | reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [H0 Hs] [| i] Hi; [rewrite Nat.add_0_r; exact H0 |].
      replace (s + S i) with (S s + i) by lia. apply Hs. simpl in Hi. lia.
    + intros H. split; [specialize (H 0 ltac:(simpl; lia)); rewrite Nat.add_0_r in H; exact H |].
      intros i Hi. replace (S s + i) with (s + S i) by lia. apply (H (S i)). simpl. lia.
Qed.

Section Fast.
  Variables (n nE : nat) (NFl : list nat) (Tl : list (list nat)) (P : option (list (nat * nat))).

  Hypothesis HnE : length Tl = nE.
  Hypothesis Hn : length NFl = n.

  Let NF := of_list NFl.
  Let T := map of_list Tl.
  Let cs := cells NFl Tl.
  Let ct := of_listV (zcell n) cs.
  Let look := vlook (zcell n) ct.

  Lemma row_eq : forall e k, stp T e k = nth k (nth e Tl []) 0.
  Proof.
    intros e k. unfold stp, row, T. change TLeaf with (of_list []).
    rewrite map_nth. apply tget_of_list.
  Qed.

  Lemma nfv_eq : forall k, nfv NF k = nth k NFl 0.
  Proof. intro k. apply tget_of_list. Qed.

  Let RB := map (chunk B16 0) Tl.
  Let HB (g : nat) := chunk B16 zb (map (fun rb => nth g rb zb) RB).

  (* cb holds state x's column T[0][x] ... T[nE-1][x]. *)
  Definition CP (x : nat) (cb : list (blk nat)) : Prop :=
    (forall a, a < nE -> bget 0 cb 0 a = nth x (nth a Tl []) 0) /\ nE <= 16 * length cb.

  Lemma HB_col : forall g d, d < 16 -> CP (16 * g + d) (mapT (bmap (dsel d)) (HB g)).
  Proof.
    intros g d Hd. rewrite mapT_eq. unfold HB.
    assert (Hlen : nE <= 16 * length (chunk B16 zb (map (fun rb => nth g rb zb) RB))).
    { pose proof (chunk_length B16 zb (map (fun rb => nth g rb zb) RB)) as L.
      unfold RB in L. rewrite !map_length, HnE in L. exact L. }
    split; [| rewrite map_length; exact Hlen].
    intros a Ha. rewrite (bget_map zb) by lia. rewrite bget_chunk.
    rewrite (nth_map_d _ _ []) by (destruct g; reflexivity).
    unfold RB. rewrite (nth_map_d _ _ []) by reflexivity.
    unfold zb. rewrite (chunk_nth B16 0). rewrite (dsel_spec _ _ 0) by exact Hd. cbn [l16].
    do 16 (destruct d as [| d]; [reflexivity |]). lia.
  Qed.

  Definition J (s d : nat) (hb : list (blk (blk nat))) (rowsB : list (list (blk nat))) : Prop :=
    exists g, (d = 16 /\ s = 16 * g /\ rowsB = map (skipn g) RB)
           \/ (d < 16 /\ s = 16 * g + d /\ hb = HB g /\ rowsB = map (skipn (S g)) RB).

  Lemma hgroup_HB : forall g, hgroup (map (skipn g) RB) = HB g.
  Proof.
    intro g. unfold hgroup, HB. rewrite mapT_eq, map_map. f_equal. apply map_ext. intro rb. apply hd_skipn.
  Qed.

  Lemma cellsB_spec : forall nfl s d hb rowsB, J s d hb rowsB ->
    let R := cellsB s d nfl hb rowsB [] in
    length R = length nfl /\ forall i z, i < length nfl ->
      lk (nth i R z) = s + i /\ lnf (nth i R z) = nth i nfl 0 /\ CP (s + i) (lcol (nth i R z)).
  Proof.
    induction nfl as [| x t IH]; intros s d hb rowsB HJ R; subst R.
    - split; [reflexivity | intros i z Hi; simpl in Hi; lia].
    - cbn [cellsB]. destruct HJ as [g [[Ed [Es Er]] | [Hd [Es [Eh Er]]]]].
      + destruct (Compare_dec.lt_dec d 16); [lia |]. cbv beta iota zeta.
        rewrite cellsB_app. cbn [rev app].
        assert (HJ' : J (S s) 1 (hgroup rowsB) (mapT (@tl (blk nat)) rowsB)).
        { exists g. right. split; [lia |]. split; [lia |]. split; [rewrite Er; apply hgroup_HB |].
          rewrite Er, mapT_eq, map_map. apply map_ext. intro rb. apply tl_skipn. }
        destruct (IH _ _ _ _ HJ') as [IHl IHn]. split; [cbn [length]; rewrite IHl; reflexivity |].
        intros [| i] z Hi; cbn [nth].
        * cbn [lk lnf lcol]. rewrite Nat.add_0_r. split; [reflexivity | split; [reflexivity |]].
          rewrite Er, hgroup_HB, Es. rewrite <- (Nat.add_0_r (16 * g)) at 1. apply HB_col. lia.
        * replace (s + S i) with (S s + i) by lia. apply IHn. simpl in Hi. lia.
      + destruct (Compare_dec.lt_dec d 16); [| lia]. cbv beta iota zeta.
        rewrite cellsB_app. cbn [rev app].
        assert (HJ' : J (S s) (S d) hb rowsB).
        { destruct (Compare_dec.lt_dec (S d) 16).
          - exists g. right. split; [lia |]. split; [lia |]. split; assumption.
          - exists (S g). left. split; [lia |]. split; [lia |]. exact Er. }
        destruct (IH _ _ _ _ HJ') as [IHl IHn]. split; [cbn [length]; rewrite IHl; reflexivity |].
        intros [| i] z Hi; cbn [nth].
        * cbn [lk lnf lcol]. rewrite Nat.add_0_r. split; [reflexivity | split; [reflexivity |]].
          rewrite Eh, Es. apply HB_col. exact Hd.
        * replace (s + S i) with (S s + i) by lia. apply IHn. simpl in Hi. lia.
  Qed.

  Lemma cs_spec : length cs = n /\ forall x, x < n ->
    lk (nth x cs (zcell n)) = x /\ lnf (nth x cs (zcell n)) = nth x NFl 0 /\ CP x (lcol (nth x cs (zcell n))).
  Proof.
    assert (HJ : J 0 16 [] (mapT (chunk B16 0) Tl)).
    { exists 0. left. split; [reflexivity |]. split; [reflexivity |].
      rewrite mapT_eq. unfold RB. rewrite map_map. reflexivity. }
    destruct (cellsB_spec NFl _ _ _ _ HJ) as [L N]. unfold cs, cells. split; [rewrite L; exact Hn |].
    intros x Hx. apply N. lia.
  Qed.

  Lemma cs_length : length cs = n.
  Proof. apply cs_spec. Qed.

  Lemma look_eq : forall x, look x = nth x cs (zcell n).
  Proof. intro x. unfold look, ct. apply vlook_of_listV. Qed.

  (* A cell lookup is valid exactly when its key is a valid state. *)
  Lemma look_ok : forall x, cell_ok n (look x) = inV n NF x.
  Proof.
    intro x. rewrite look_eq. unfold inV. rewrite nfv_eq, <- ltd_ltn.
    destruct (Compare_dec.lt_dec x n) as [Hx | Hx].
    - destruct (proj2 cs_spec x Hx) as [Ek [Ef _]]. unfold cell_ok. rewrite Ek, Ef.
      destruct (Compare_dec.lt_dec x n); [reflexivity | lia].
    - rewrite nth_overflow by (rewrite cs_length; lia). unfold cell_ok, zcell. cbn [lk lnf].
      destruct (Compare_dec.lt_dec n n); [lia |]. reflexivity.
  Qed.

  Lemma look_col : forall x a, x < n -> a < nE -> bget 0 (lcol (look x)) 0 a = stp T a x.
  Proof.
    intros x a Hx Ha. rewrite look_eq. destruct (proj2 cs_spec x Hx) as [_ [_ [C _]]].
    rewrite C, row_eq by exact Ha. reflexivity.
  Qed.

  (* The blocks of state s's step-target cells. *)
  Lemma ls_get : forall s e, s < n -> e < nE ->
    bget (zcell n) (mapT (bmap look) (lcol (nth s cs (zcell n)))) 0 e = look (stp T e s).
  Proof.
    intros s e Hs He. destruct (proj2 cs_spec s Hs) as [_ [_ [C L]]].
    rewrite mapT_eq, (bget_map 0) by lia. rewrite C, row_eq by exact He. reflexivity.
  Qed.

  Lemma ls_length : forall s, s < n ->
    nE <= 16 * length (mapT (bmap look) (lcol (nth s cs (zcell n)))).
  Proof.
    intros s Hs. destruct (proj2 cs_spec s Hs) as [_ [_ [_ L]]]. rewrite mapT_eq, map_length. exact L.
  Qed.

  Lemma state_okI_iff : forall s, s < n -> (forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE) ->
    state_okI n nE ct (mapT rpairOf (pairsOfT nE P)) s (nth s cs (zcell n)) = true <->
    inV n NF (nfv NF s) = true
    /\ (forall e, e < nE -> inV n NF (stp T e s) = true)
    /\ (inD n NF s = true -> forall p, In p (pairsOf nE P) ->
          Nat.eqb (stp T (fst p) (stp T (snd p) s)) (stp T (snd p) (stp T (fst p) s)) = true).
  Proof.
    intros s Hs Hpr. unfold state_okI. cbv zeta. fold look. rewrite commI_eq, (mapT_eq rpairOf).
    set (ls := mapT (bmap look) (lcol (nth s cs (zcell n)))).
    assert (Hlnf : lnf (nth s cs (zcell n)) = nfv NF s) by (rewrite nfv_eq; apply (proj2 cs_spec s Hs)).
    assert (HinD : inD n NF s = (ltd s n && (Nat.eqb (lnf (nth s cs (zcell n))) s || Nat.eqb s 0))).
    { unfold inD. rewrite Hlnf, ltd_ltn. reflexivity. }
    assert (Hsteps : bfaL (cell_ok n) nE 0 ls = true <-> forall e, e < nE -> inV n NF (stp T e s) = true).
    { rewrite (bfaL_iff (zcell n)). split.
      - intros H e He. rewrite <- look_ok, <- ls_get by assumption. apply H; [lia | exact He |].
        pose proof (ls_length s Hs) as L. fold ls in L. lia.
      - intros H k _ Hk _. unfold ls. rewrite ls_get, look_ok by assumption. apply H, Hk. }
    (* With every step valid, each pair reads the two step targets' columns. *)
    assert (Hpair : (forall e, e < nE -> inV n NF (stp T e s) = true) -> forall p, In p (pairsOf nE P) ->
      pair_okI (zcell n) ls (rpairOf p) = Nat.eqb (stp T (fst p) (stp T (snd p) s)) (stp T (snd p) (stp T (fst p) s))).
    { intros Hst p Hp. destruct (Hpr p Hp) as [Ha Hb].
      assert (Hlt : forall e, e < nE -> stp T e s < n).
      { intros e He. specialize (Hst e He). unfold inV in Hst. apply andb_true_iff in Hst.
        apply ltn_spec. tauto. }
      unfold pair_okI, rpairOf. cbv zeta. cbn [qa qb da db]. rewrite !qget_at.
      unfold ls. rewrite !ls_get by assumption. rewrite !look_col by first [apply Hlt; assumption | assumption]. reflexivity. }
    rewrite <- HinD, look_ok, Hlnf, !andb_true_iff, Hsteps. split.
    - intros [[Hnf Hst] Hc]. split; [exact Hnf |]. split; [exact Hst |].
      intros HD p Hp. rewrite HD in Hc. simpl in Hc. rewrite forallb_forall in Hc.
      rewrite <- Hpair by assumption. apply Hc. apply in_map. apply pairsOfT_in. exact Hp.
    - intros [Hnf [Hst Hc]]. split; [split; assumption |].
      destruct (inD n NF s) eqn:HD; [| reflexivity]. simpl. apply forallb_forall.
      intros r Hr. apply in_map_iff in Hr. destruct Hr as [p [<- Hp]]. apply pairsOfT_in in Hp.
      rewrite Hpair by assumption. apply Hc; [reflexivity | exact Hp].
  Qed.

  Lemma seq_forall : forall (f : nat -> bool) m, forallb f (seq 0 m) = true <-> forall i, i < m -> f i = true.
  Proof.
    intros f m. rewrite forallb_forall. split.
    - intros H i Hi. apply H. apply in_seq. lia.
    - intros H i Hi. apply in_seq in Hi. apply H. lia.
  Qed.

  Theorem check_fast_eq : check_fast n nE NFl Tl P = check_tables n nE NF T P.
  Proof.
    change (check_fast n nE NFl Tl P) with (pairs_okW nE P && scanI n nE ct (mapT rpairOf (pairsOfT nE P)) 0 cs).
    rewrite pairs_okW_eq. unfold check_tables. rewrite <- !andb_assoc.
    destruct (pairs_ok nE P) eqn:Hpo; [| reflexivity]. cbn [andb].
    assert (Hpr : forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE).
    { intros p Hp. unfold pairs_ok in Hpo. rewrite forallb_forall in Hpo. specialize (Hpo p Hp).
      apply andb_true_iff in Hpo. destruct Hpo as [Ha Hb]. apply ltn_spec in Ha. apply ltn_spec in Hb. split; assumption. }
    apply eq_iff_eq_true. rewrite scanI_iff, cs_length. rewrite !andb_true_iff.
    unfold nf_ok, steps_ok, comm_ok. rewrite !seq_forall, forallb_forall.
    setoid_rewrite seq_forall. cbn [Nat.add].
    split.
    - intros H. pose proof (fun i Hi => proj1 (state_okI_iff i Hi Hpr) (H i Hi)) as H'.
      split; [| split].
      + intros i Hi. apply (H' i Hi).
      + intros e He i Hi. apply (H' i Hi). exact He.
      + intros q Hq i Hi. destruct (inD n NF i) eqn:HD; [| reflexivity]. simpl.
        apply (H' i Hi); assumption.
    - intros [Hnf [Hst Hc]] i Hi. apply (state_okI_iff i Hi Hpr). split; [| split].
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
