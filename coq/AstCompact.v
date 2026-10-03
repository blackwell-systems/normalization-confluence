(* The rules oracle in compact memory: checkBuildC.

   checkBuildT (AstTables.v) keeps the valuation box as a list and one
   check_fast cell per state (a record, a list and a 16-entry block for every
   16 events), so at 2^20 states it holds about 300 to 500 MiB where checkBuild
   holds about 90 to 150 MiB, mostly the box list. checkBuildC decides the same
   property (checkBuildC_eq) and keeps only the tables, packed:

   - the box is never a list: foldD enumerates it on the fly (descending, so
     every list it builds comes out in ascending order with no reversal);
   - the table entries are one sequence E: state s's column NF[s], T[0][s],
     ..., T[nE-1][s] at positions s*W .. s*W+W-1 (W = nE + 1). It is held as a
     list of 16-entry blocks (Lb), built 16 states at a time: 16 columns are
     exactly W blocks, so no block is padded except the last;
   - a 16-ary trie over Lb's suffixes (keyed by block index, counted from the
     end) finds the block holding a state's column in one lookup; the column
     is then read from there (rdv), at most a few blocks on;
   - the scan checks only what checkBuild's ccA checks: for every state s that
     is valid or 0 (NF[s] = s or s = 0), every declared pair commutes. The
     validity parts of the table check are implied by wfc (tables_fn_eq), so
     they are not rechecked. As in check_fast, the step targets' columns are
     found once per state and every pair is read from them.

   Peak memory is then the blocks (about 10 bytes per entry) plus transient
   lists. Axiom-free; every loop is tail-recursive or bounded by the number
   of variables. The new unary loops (loopD, upto) run over one domain size
   and over the events, as tail calls. *)

Require Import NC.Trace.
Require Import NC.TableCheck.
Require Import NC.TableFast.
Require Import NC.TableFn.
Require Import NC.AstChecker.
Require Import NC.AstTables.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Lia.
Import ListNotations.

Local Open Scope bool_scope.

(* ===== reading a sequence held as blocks ===== *)

(* The suffixes of a list, last first (sfx l [] = rev (sufR l)). *)
Fixpoint sfx {A} (l : list A) (acc : list (list A)) : list (list A) :=
  match l with [] => acc | _ :: t => sfx t (l :: acc) end.

Fixpoint sufR {A} (l : list A) : list (list A) :=
  match l with [] => [] | _ :: t => l :: sufR t end.

Lemma sfx_eq : forall {A} (l : list A) acc, sfx l acc = rev (sufR l) ++ acc.
Proof.
  intros A l. induction l as [| x t IH]; intro acc; cbn [sfx sufR rev]; [reflexivity |].
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma sufR_length : forall {A} (l : list A), length (sufR l) = length l.
Proof. intros A l. induction l; cbn; [reflexivity | rewrite IHl; reflexivity]. Qed.

Lemma sufR_nth : forall {A} (l : list A) q, q < length l -> nth q (sufR l) [] = skipn q l.
Proof.
  intros A l. induction l as [| x t IH]; intros q Hq; cbn in Hq; [lia |].
  destruct q as [| q]; [reflexivity |]. cbn [sufR nth skipn]. apply IH. lia.
Qed.

(* ===== more on blocks ===== *)

Lemma bget_app : forall {A} (z : A) bs2 bs1 b k, b <= k ->
  bget z (bs1 ++ bs2) b k = if ltd k (b + 16 * length bs1) then bget z bs1 b k else bget z bs2 (b + 16 * length bs1) k.
Proof.
  intros A z bs2 bs1. induction bs1 as [| t r IH]; intros b k Hb; cbn [app length bget].
  - destruct (Compare_dec.lt_dec k (b + 16 * 0)); [lia | cbv beta iota; f_equal; lia].
  - destruct (Compare_dec.lt_dec k (b + 16)) as [H | H]; cbv beta iota.
    + destruct (Compare_dec.lt_dec k (b + 16 * S (length r))); [reflexivity | lia].
    + rewrite IH by lia. replace (b + 16 + 16 * length r) with (b + 16 * S (length r)) by lia.
      destruct (Compare_dec.lt_dec k (b + 16 * S (length r))) as [H1 | H1];
        destruct (Compare_dec.lt_dec k (b + 16 * S (length r))); cbv beta iota; try lia; reflexivity.
Qed.

Lemma bget_shift : forall {A} (z : A) bs b c k, b <= k -> bget z bs (b + c) (k + c) = bget z bs b k.
Proof.
  intros A z bs. induction bs as [| t r IH]; intros b c k Hb; cbn [bget]; [reflexivity |].
  destruct (Compare_dec.lt_dec (k + c) (b + c + 16)) as [H1 | H1];
    destruct (Compare_dec.lt_dec k (b + 16)) as [H2 | H2]; cbv beta iota; try lia.
  - rewrite (bsel_spec _ _ _ z), (bsel_spec b k t z) by lia. f_equal. lia.
  - replace (b + c + 16) with (b + 16 + c) by lia. apply IH. lia.
Qed.

Lemma bget_beyond : forall {A} (z : A) bs b k, b + 16 * length bs <= k -> bget z bs b k = z.
Proof.
  intros A z bs. induction bs as [| t r IH]; intros b k Hk; cbn [bget]; [reflexivity |].
  cbn [length] in Hk. destruct (Compare_dec.lt_dec k (b + 16)); [lia | cbv beta iota]. apply IH. lia.
Qed.

Lemma chunkF_len : forall {A B} f mk (z : A) (l : list A), length l <= 16 * f ->
  length l <= 16 * length (chunkF f mk z l : list B) /\ 16 * length (chunkF f mk z l : list B) < length l + 16.
Proof.
  intros A B f. induction f as [| f IH]; intros mk z l Hl; [destruct l; cbn in *; lia |].
  destruct l as [| x t] eqn:El; [cbn; lia |].
  rewrite <- El in Hl |- *. rewrite chunkF_cons by congruence. cbn [length].
  pose proof (IH mk z (skipn 16 l)) as H. rewrite skipn_length in H. specialize (H ltac:(lia)).
  subst l. cbn [length] in *. lia.
Qed.

Lemma chunk_exact : forall {A B} mk (z : A) (l : list A) q, length l = 16 * q -> length (chunk mk z l : list B) = q.
Proof.
  intros A B mk z l q Hl. rewrite chunk_eq. pose proof (chunkF_len (length l) mk z l ltac:(lia)) as [H1 H2]. lia.
Qed.

Lemma rev_rev_app : forall {A} (c b : list A), rev_append (rev_append c []) b = c ++ b.
Proof. intros A c b. rewrite !rev_append_rev, app_nil_r, rev_involutive. reflexivity. Qed.

(* ===== views and reads ===== *)

(* Entry d of t for 16 <= d < 32: four comparisons against constants. *)
Definition dselH {A : Type} (d : nat) (t : blk A) : A :=
  match t with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =>
    (if ltd d 24 then (if ltd d 20 then (if ltd d 18 then (if ltd d 17 then x0 else x1) else (if ltd d 19 then x2 else x3)) else (if ltd d 22 then (if ltd d 21 then x4 else x5) else (if ltd d 23 then x6 else x7))) else (if ltd d 28 then (if ltd d 26 then (if ltd d 25 then x8 else x9) else (if ltd d 27 then x10 else x11)) else (if ltd d 30 then (if ltd d 29 then x12 else x13) else (if ltd d 31 then x14 else x15)))) end.

Lemma dselH_spec : forall {A : Type} d (t : blk A) z, 16 <= d -> d < 32 -> dselH d t = nth (d - 16) (l16 t) z.
Proof.
  intros A d [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15] z H1 H2. unfold dselH, l16. split_ltd;
  remember (d - 16) as j eqn:Ej;
  do 16 (destruct j as [| j]; [cbn [nth]; first [reflexivity | exfalso; lia] |]); exfalso; lia.
Qed.

(* Entry 16 * q + s of the blocks t, for s < 32: skip q blocks, then four
   comparisons against constants in that block or the next. *)
Fixpoint rdq (t : list (blk nat)) (q s : nat) : nat :=
  match t with
  | [] => 0
  | b :: r =>
    match q with
    | 0 => if ltd s 16 then dsel s b else match r with [] => 0 | b' :: _ => dselH s b' end
    | S q' => rdq r q' s
    end
  end.

Lemma rdq_spec : forall t q s, s < 32 -> rdq t q s = bget 0 t 0 (16 * q + s).
Proof.
  induction t as [| b r IH]; intros q s Hs; [reflexivity |].
  destruct q as [| q]; cbn [rdq].
  - rewrite Nat.mul_0_r, Nat.add_0_l. cbn [bget].
    destruct (Compare_dec.lt_dec s 16) as [H | H]; cbv beta iota.
    + destruct (Compare_dec.lt_dec s (0 + 16)); [| lia]. rewrite (dsel_spec _ _ 0), (bsel_spec _ _ _ 0) by lia.
      f_equal. lia.
    + destruct (Compare_dec.lt_dec s (0 + 16)); [lia |]. cbv beta iota.
      destruct r as [| b' r']; [reflexivity |]. cbn [bget].
      destruct (Compare_dec.lt_dec s (0 + 16 + 16)); [| lia]. rewrite (dselH_spec _ _ 0), (bsel_spec _ _ _ 0) by lia.
      reflexivity.
  - rewrite IH by exact Hs. cbn [bget]. destruct (Compare_dec.lt_dec (16 * S q + s) (0 + 16)); [lia | cbv beta iota].
    replace (16 * S q + s) with (16 * q + s + 16) by lia. rewrite <- (bget_shift 0 r 0 16) by lia. reflexivity.
Qed.

Lemma bget_skipn : forall {A} (z : A) q bs b k, b + 16 * q <= k ->
  bget z bs b k = bget z (skipn q bs) (b + 16 * q) k.
Proof.
  intros A z q. induction q as [| q IH]; intros bs b k Hk; [rewrite Nat.add_0_r; reflexivity |].
  destruct bs as [| t r]; [destruct (S q); reflexivity |]. cbn [skipn bget].
  destruct (Compare_dec.lt_dec k (b + 16)); [lia | cbv beta iota].
  rewrite IH by lia. f_equal. lia.
Qed.

(* Entries o .. o + 15 of the 32 entries of b0 then b1, for o < 16: a block
   aligned at entry o. Four comparisons against constants pick the shift. *)
Definition realign (o : nat) (b0 b1 : blk nat) : blk nat :=
  match b0, b1 with B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, B16 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 =>
    (if ltd o 8 then (if ltd o 4 then (if ltd o 2 then (if ltd o 1 then B16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 else B16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0) else (if ltd o 3 then B16 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 else B16 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2)) else (if ltd o 6 then (if ltd o 5 then B16 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 else B16 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4) else (if ltd o 7 then B16 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 else B16 x7 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6))) else (if ltd o 12 then (if ltd o 10 then (if ltd o 9 then B16 x8 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 else B16 x9 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8) else (if ltd o 11 then B16 x10 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 else B16 x11 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)) else (if ltd o 14 then (if ltd o 13 then B16 x12 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 else B16 x13 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12) else (if ltd o 15 then B16 x14 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 else B16 x15 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14)))) end.

Lemma realign_spec : forall o b0 b1 i, o < 16 -> i < 16 ->
  nth i (l16 (realign o b0 b1)) 0 = nth (o + i) (l16 b0 ++ l16 b1) 0.
Proof.
  intros o [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15] [y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15] i Ho Hi. unfold realign, l16. split_ltd;
  do 16 (destruct o as [| o]; [try (exfalso; lia); do 16 (destruct i as [| i]; [reflexivity |]); exfalso; lia |]); exfalso; lia.
Qed.

(* The column of a view as K blocks aligned at its first entry. zk is zb,
   passed in once (the generated Go builds a constant afresh at each use). *)
Fixpoint alignN (k o : nat) (zk : blk nat) (t : list (blk nat)) : list (blk nat) :=
  match k with
  | 0 => []
  | S k' => match t with [] => [] | b0 :: r => realign o b0 (hd zk r) :: alignN k' o zk r end
  end.

Lemma qget_l16 : forall bs h d, d < 16 -> qget 0 bs h d = nth d (l16 (nth h bs zb)) 0.
Proof.
  induction bs as [| b r IH]; intros h d Hd.
  - destruct h; cbn; do 16 (destruct d as [| d]; [reflexivity |]); lia.
  - destruct h as [| h]; cbn [qget nth]; [apply dsel_spec, Hd | apply IH, Hd].
Qed.

Lemma alignN_rdq : forall k o t h d, o < 16 -> d < 16 -> h < k ->
  qget 0 (alignN k o zb t) h d = rdq t h (o + d).
Proof.
  induction k as [| k IH]; intros o t h d Ho Hd Hh; [lia |].
  destruct t as [| b0 r]; [destruct h; reflexivity |]. cbn [alignN].
  destruct h as [| h].
  - cbn [qget rdq]. rewrite (dsel_spec _ _ 0) by exact Hd. fold (l16 (realign o b0 (hd zb r))).
    rewrite realign_spec by assumption.
    destruct (Compare_dec.lt_dec (o + d) 16) as [H | H]; cbv beta iota.
    + rewrite (dsel_spec _ _ 0) by exact H. apply app_nth1. destruct b0; cbn; lia.
    + rewrite app_nth2 by (destruct b0; cbn; lia).
      replace (length (l16 b0)) with 16 by (destruct b0; reflexivity).
      destruct r as [| b' r']; cbn [hd].
      * unfold zb. cbn [l16]. remember (o + d - 16) as j. do 16 (destruct j as [| j]; [reflexivity |]). lia.
      * rewrite (dselH_spec _ _ 0) by lia. reflexivity.
  - cbn [qget rdq]. apply IH; lia.
Qed.

(* A state's view: the suffix of the blocks starting with the block that
   holds its column's first entry, and that entry's digit in the block. *)
Record view := { vtl : list (blk nat); vof : nat }.

Definition zview : view := {| vtl := []; vof := 0 |}.

(* ST is the trie over sfx Lb [], L the number of blocks, L1 = L - 1. *)
Definition viewOf (W L L1 : nat) (ST : vt (list (blk nat))) (zl : list (blk nat)) (x : nat) : view :=
  let k := x * W in
  let q := hi16 k in
  {| vtl := if ltd q L then vlook zl ST (L1 - q) else zl; vof := k - 16 * q |}.

(* An offset j into a column, split once into a block count and a digit. *)
Record split := { sq : nat; sd : nat }.

Definition splitJ (j : nat) : split := let h := hi16 j in {| sq := h; sd := j - 16 * h |}.

(* Entry j of a view's column, j given split. *)
Definition rdj (v : view) (qd : split) : nat := rdq (vtl v) (sq qd) (vof v + sd qd).

Section Read.
  Variables (W : nat) (E : list nat) (Lb : list (blk nat)).
  Hypothesis HLb : forall k, bget 0 Lb 0 k = nth k E 0.

  Let L := length Lb.
  Let ST := of_listV [] (sfx Lb []).

  Lemma view_tail : forall q, (if ltd q L then vlook [] ST (L - 1 - q) else []) = skipn q Lb.
  Proof.
    intro q. destruct (Compare_dec.lt_dec q L) as [Hq | Hq]; cbv beta iota.
    - unfold ST. rewrite vlook_of_listV, sfx_eq, app_nil_r.
      rewrite rev_nth by (rewrite sufR_length; lia). rewrite sufR_length.
      fold L. replace (L - S (L - 1 - q)) with q by lia. apply sufR_nth. exact Hq.
    - rewrite skipn_all2 by lia. reflexivity.
  Qed.

  (* Reading a view reads E. *)
  Theorem rdj_view : forall x j, rdj (viewOf W L (L - 1) ST [] x) (splitJ j) = nth (x * W + j) E 0.
  Proof.
    intros x j. unfold rdj, viewOf, splitJ. cbv zeta. cbn [vtl vof sq sd]. rewrite view_tail.
    set (k := x * W). destruct (hi16_spec k) as [Ek Dk]. destruct (hi16_spec j) as [Ej Dj].
    rewrite rdq_spec by lia.
    set (q := hi16 k). set (h := hi16 j).
    replace (16 * h + (k - 16 * q + (j - 16 * h))) with (16 * h + (k - 16 * q + (j - 16 * h)) + (0 + 16 * q) - (0 + 16 * q)) by lia.
    rewrite <- (Nat.add_0_l (16 * h + (k - 16 * q + (j - 16 * h)))).
    rewrite <- (bget_shift 0 (skipn q Lb) 0 (16 * q)) by lia.
    rewrite <- bget_skipn by lia. rewrite HLb. f_equal. lia.
  Qed.
End Read.

(* ===== the scan ===== *)

(* f i, ..., f (i + k - 1), tail-recursively. *)
Fixpoint upto {A} (f : nat -> A) (i k : nat) (acc : list A) : list A :=
  match k with 0 => acc | S k' => upto f i k' (f (i + k') :: acc) end.

Lemma upto_eq : forall {A} (f : nat -> A) k i acc, upto f i k acc = map f (seq i k) ++ acc.
Proof.
  intros A f k. induction k as [| k IH]; intros i acc; [reflexivity |].
  cbn [upto]. rewrite IH, seq_S, map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.

(* A declared pair (a, b): a and b split into a block index and a digit, to
   find the targets' views, and the offsets 1 + a and 1 + b split, to read
   T[a] and T[b] from them. *)
Record cpair := { cqa : nat; cda : nat; cqb : nat; cdb : nat; csa : split; csb : split }.

Definition cpairOf (p : nat * nat) : cpair :=
  let a := fst p in let b := snd p in
  let ha := hi16 a in let hb := hi16 b in
  {| cqa := ha; cda := a - 16 * ha; cqb := hb; cdb := b - 16 * hb; csa := splitJ (S a); csb := splitJ (S b) |}.

(* T[a][x_b] = T[b][x_a], read from the targets' aligned columns: entry 1 + a
   of x_b's column is digit sd at block sq of csa. z is the empty column,
   passed in once: the Go generated from this proof builds a constant afresh
   at each use. *)
Definition pair_okC (z : list (blk nat)) (ls : list (blk (list (blk nat)))) (r : cpair) : bool :=
  Nat.eqb (qget 0 (qget z ls (cqb r) (cdb r)) (sq (csa r)) (sd (csa r)))
          (qget 0 (qget z ls (cqa r) (cda r)) (sq (csb r)) (sd (csb r))).

Fixpoint commC (z : list (blk nat)) (ls : list (blk (list (blk nat)))) (rp : list cpair) : bool :=
  match rp with [] => true | r :: t => pair_okC z ls r && commC z ls t end.

(* A view's column, aligned, in K blocks. *)
Definition alignV (K : nat) (zk : blk nat) (v : view) : list (blk nat) := alignN K (vof v) zk (vtl v).

(* State s: if it is valid or 0, every declared pair commutes there. spB
   holds the offsets 1 .. nE, split, in blocks of 16; each step target's
   column is aligned once, block by block, so every pair reads it at a digit
   fixed by the pair. *)
Definition state_okC (n nE K L L1 : nat) (ST : vt (list (blk nat))) (z : list (blk nat)) (zk : blk nat) (spB : list (blk split))
    (rp : list cpair) (s : nat) : bool :=
  let W := S nE in
  let vs := viewOf W L L1 ST z s in
  if ltd s n && (Nat.eqb (rdq (vtl vs) 0 (vof vs)) s || Nat.eqb s 0) then
    commC z (mapT (bmap (fun qd => alignV K zk (viewOf W L L1 ST z (rdj vs qd)))) spB) rp
  else true.

Definition scanC (n nE : nat) (Lb : list (blk nat)) (P : option (list (nat * nat))) : bool :=
  let L := lenT Lb 0 in
  let zs := splitJ 0 in
  allK (state_okC n nE (S (hi16 nE)) L (L - 1) (of_listV [] (sfx Lb [])) [] zb
          (chunk B16 zs (upto (fun e => splitJ (S e)) 0 nE [])) (mapT cpairOf (pairsOfT nE P))) 0 n.

Lemma commC_eq : forall z ls rp, commC z ls rp = forallb (pair_okC z ls) rp.
Proof. intros z ls rp. induction rp as [| r t IH]; cbn [commC forallb]; [reflexivity | rewrite IH; reflexivity]. Qed.

(* The scan decides: every state below n that is valid or 0 (on the tables
   read from E) has every declared pair commuting. *)
Theorem scanC_spec : forall n nE E Lb P,
  (forall k, bget 0 Lb 0 k = nth k E 0) ->
  (forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE) ->
  let nf := fun x => nth (x * S nE) E 0 in
  let st := fun e x => nth (x * S nE + S e) E 0 in
  scanC n nE Lb P = true <->
  forall s, s < n -> inDf n nf s = true -> forall p, In p (pairsOf nE P) -> pair_okF st s p = true.
Proof.
  intros n nE E Lb P HLb Hpr nf st. unfold scanC. cbv zeta. rewrite allK_iff.
  rewrite lenT_eq, Nat.add_0_r.
  set (W := S nE). set (L := length Lb). set (ST := of_listV [] (sfx Lb [])).
  assert (R : forall x j, rdj (viewOf W L (L - 1) ST [] x) (splitJ j) = nth (x * W + j) E 0) by (intros; apply rdj_view, HLb).
  assert (R0 : forall x, rdq (vtl (viewOf W L (L - 1) ST [] x)) 0 (vof (viewOf W L (L - 1) ST [] x)) = nth (x * W) E 0).
  { intro x. rewrite <- (Nat.add_0_r (x * W)), <- R. unfold rdj, splitJ. cbn [sq sd]. rewrite Nat.add_0_r. reflexivity. }
  set (sp := upto (fun e => splitJ (S e)) 0 nE []).
  set (spB := chunk B16 (splitJ 0) sp).
  (* Reading entry 1 + e of an aligned column reads E. *)
  assert (RA : forall x e, e < nE ->
    qget 0 (alignV (S (hi16 nE)) zb (viewOf W L (L - 1) ST [] x)) (sq (splitJ (S e))) (sd (splitJ (S e))) = nth (x * W + S e) E 0).
  { intros x e He. rewrite <- R. unfold alignV, rdj, splitJ. cbn [sq sd].
    destruct (hi16_spec (S e)) as [E1 D1]. destruct (hi16_spec (x * W)) as [E2 D2].
    apply alignN_rdq; [unfold viewOf; cbn [vof]; lia | exact D1 |].
    assert (hi16 (S e) <= hi16 nE).
    { unfold hi16. repeat apply Nat.div2_le_mono. lia. }
    lia. }
  assert (Hst : forall s, s < n -> state_okC n nE (S (hi16 nE)) L (L - 1) ST [] zb spB (mapT cpairOf (pairsOfT nE P)) s = true <->
            (inDf n nf s = true -> forall p, In p (pairsOf nE P) -> pair_okF st s p = true)).
  { intros s Hs. unfold state_okC. fold W. cbv zeta.
    set (vs := viewOf W L (L - 1) ST [] s).
    assert (HD : (ltd s n && (Nat.eqb (rdq (vtl vs) 0 (vof vs)) s || Nat.eqb s 0)) = inDf n nf s).
    { unfold inDf, vs. rewrite R0. reflexivity. }
    rewrite HD. destruct (inDf n nf s) eqn:ED; [| split; [intros _ H; discriminate | reflexivity]].
    set (vw := fun e => alignV (S (hi16 nE)) zb (viewOf W L (L - 1) ST [] (rdj vs (splitJ (S e))))).
    set (ls := mapT (bmap (fun qd => alignV (S (hi16 nE)) zb (viewOf W L (L - 1) ST [] (rdj vs qd)))) spB).
    assert (Hsp : length sp = nE) by (unfold sp; rewrite upto_eq, app_nil_r, map_length, seq_length; reflexivity).
    assert (Hls : forall e, e < nE -> qget [] ls (hi16 e) (e - 16 * hi16 e) = vw e).
    { intros e He. unfold ls. rewrite qget_at, mapT_eq.
      rewrite (bget_map (splitJ 0)) by (pose proof (chunk_length B16 (splitJ 0) sp) as LC; fold spB in LC; lia).
      unfold spB. rewrite bget_chunk. unfold sp. rewrite upto_eq, app_nil_r.
      rewrite (nth_map_lt _ _ _ 0) by (rewrite seq_length; exact He). rewrite seq_nth by exact He. reflexivity. }
    rewrite commC_eq, forallb_forall. split.
    - intros H _ p Hp. specialize (H (cpairOf p)). destruct (Hpr p Hp) as [Ha Hb].
      assert (Hin : In (cpairOf p) (mapT cpairOf (pairsOfT nE P))).
      { rewrite mapT_eq. apply in_map, pairsOfT_in, Hp. }
      specialize (H Hin). unfold pair_okC, cpairOf in H. cbn [cqa cda cqb cdb csa csb] in H.
      rewrite !Hls in H by assumption. unfold vw in H. rewrite !RA in H by assumption.
      unfold vs in H. rewrite !R in H. unfold pair_okF, st. cbn [fst snd]. exact H.
    - intros H r Hr. rewrite mapT_eq in Hr. apply in_map_iff in Hr. destruct Hr as [p [<- Hp]].
      apply pairsOfT_in in Hp. destruct (Hpr p Hp) as [Ha Hb]. specialize (H eq_refl p Hp).
      unfold pair_okC, cpairOf. cbn [cqa cda cqb cdb csa csb].
      rewrite !Hls by assumption. unfold vw, vs. rewrite !RA by assumption. rewrite !R.
      unfold pair_okF, st in H. cbn [fst snd] in H. exact H. }
  split.
  - intros H s Hs. apply (Hst s Hs), H; lia.
  - intros H s _ Hs'. apply (Hst s ltac:(lia)), H. lia.
Qed.

(* ===== enumerating the box without a list ===== *)

(* g (k-1), then g (k-2), ..., then g 0, threading acc. *)
Fixpoint loopD {A} (g : nat -> A -> A) (k : nat) (acc : A) : A :=
  match k with 0 => acc | S k' => loopD g k' (g k' acc) end.

(* fold_right f acc over the box in boxR's order: the last valuation is
   visited first. *)
Fixpoint foldD {A} (ds : list nat) (f : valn -> A -> A) (acc : A) : A :=
  match ds with
  | [] => f [] acc
  | d :: rest => loopD (fun x a => foldD rest (fun w => f (x :: w)) a) d acc
  end.

Lemma loopD_eq : forall {A} (g : nat -> A -> A) k acc, loopD g k acc = fold_right g acc (seq 0 k).
Proof.
  intros A g k. induction k as [| k IH]; intro acc; [reflexivity |].
  cbn [loopD]. rewrite IH, seq_S, fold_right_app. reflexivity.
Qed.

Lemma fold_right_map_eq : forall {A B C} (f : B -> C -> C) (g : A -> B) a l,
  fold_right f a (map g l) = fold_right (fun x => f (g x)) a l.
Proof. intros A B C f g a l. induction l as [| x t IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma foldD_eq : forall ds {A} (f : valn -> A -> A) acc, foldD ds f acc = fold_right f acc (boxR ds).
Proof.
  induction ds as [| d rest IH]; intros A f acc; [reflexivity |].
  cbn [foldD boxR]. rewrite loopD_eq. generalize (seq 0 d). intro l. revert acc.
  induction l as [| x t IHl]; intro acc; [reflexivity |].
  cbn [fold_right flat_map]. rewrite fold_right_app, <- IHl, IH, fold_right_map_eq. reflexivity.
Qed.

(* The box split into a prefix of variables, enumerated by foldD, and a suffix
   whose box (at most bound states) is listed once: each valuation is a
   prefix's digits in front of a shared suffix valuation, so a state costs
   only the prefix's list cells. *)
Fixpoint splitSuf (bound : nat) (ds : list nat) : list nat * list nat :=
  match ds with
  | [] => ([], [])
  | d :: rest =>
    let ps := splitSuf bound rest in
    match fst ps with
    | [] => if ltd (d * prodL (snd ps)) (S bound) then ([], d :: snd ps) else ([d], snd ps)
    | _ => (d :: fst ps, snd ps)
    end
  end.

Lemma splitSuf_app : forall bound ds, fst (splitSuf bound ds) ++ snd (splitSuf bound ds) = ds.
Proof.
  intros bound ds. induction ds as [| d rest IH]; [reflexivity |]. cbn [splitSuf].
  destruct (splitSuf bound rest) as [p s]. cbn [fst snd] in *. subst rest.
  destruct p as [| x p]; [destruct (Compare_dec.lt_dec (d * prodL s) (S bound)) |]; reflexivity.
Qed.

(* The bound is 4096 states, written 16 * 16 * 16: a literal extracts as that
   many successors. *)
Definition foldB {A} (ds : list nat) (f : valn -> A -> A) (acc : A) : A :=
  let ps := splitSuf (16 * 16 * 16) ds in
  let R := rev_append (boxT (snd ps)) [] in
  foldD (fst ps) (fun pv a => fold_left (fun a' w => f (pv ++ w) a') R a) acc.

Lemma map_flat_map_eq : forall {A B C} (f : B -> C) (g : A -> list B) l,
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. intros A B C f g l. induction l as [| x t IH]; cbn; [reflexivity | rewrite map_app, IH; reflexivity]. Qed.

Lemma flat_map_flat_map_eq : forall {A B C} (f : B -> list C) (g : A -> list B) l,
  flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
Proof. intros A B C f g l. induction l as [| x t IH]; cbn; [reflexivity | rewrite flat_map_app, IH; reflexivity]. Qed.

Lemma flat_map_ext_eq : forall {A B} (f g : A -> list B) l, (forall x, f x = g x) -> flat_map f l = flat_map g l.
Proof. intros A B f g l H. induction l as [| x t IH]; cbn; [reflexivity | rewrite H, IH; reflexivity]. Qed.

Lemma flat_map_map_eq : forall {A B C} (f : B -> list C) (g : A -> B) l,
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. intros A B C f g l. induction l as [| x t IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma boxR_app : forall p s, boxR (p ++ s) = flat_map (fun pv => map (fun w => pv ++ w) (boxR s)) (boxR p).
Proof.
  induction p as [| d p IH]; intro s.
  - cbn [app boxR flat_map]. rewrite app_nil_r. induction (boxR s) as [| w t IHt]; cbn; [reflexivity | rewrite <- IHt; reflexivity].
  - cbn [app boxR]. rewrite IH, flat_map_flat_map_eq. apply flat_map_ext_eq. intro x.
    rewrite map_flat_map_eq, flat_map_map_eq. apply flat_map_ext_eq. intro pv. rewrite map_map. reflexivity.
Qed.

Lemma fold_left_rev : forall {A B} (f : A -> B -> A) l i, fold_left f (rev l) i = fold_right (fun x y => f y x) i l.
Proof. intros A B f l. induction l as [| x t IH]; intro i; cbn; [reflexivity | rewrite fold_left_app, IH; reflexivity]. Qed.

Lemma foldB_eq : forall {A} ds (f : valn -> A -> A) acc, foldB ds f acc = fold_right f acc (boxR ds).
Proof.
  intros A ds f acc. unfold foldB. cbv zeta. rewrite foldD_eq.
  rewrite <- (splitSuf_app (16 * 16 * 16) ds) at 2. rewrite boxR_app.
  generalize (boxR (fst (splitSuf (16 * 16 * 16) ds))). intro l. induction l as [| pv t IH]; [reflexivity |].
  cbn [fold_right flat_map]. rewrite fold_right_app, IH, rev_append_rev, app_nil_r, boxT_eq, fold_left_rev.
  rewrite fold_right_map_eq. reflexivity.
Qed.

(* ===== pass 1: normal forms and wfc ===== *)

Definition p1 (m : machine) (F : nat) (v : valn) (st : bool * list nat) : bool * list nat :=
  if fst st then (let w := normalize m F v in (allValid m w, enc (doms m) w :: snd st)) else st.

Lemma p1_spec : forall m L, let r := fold_right (p1 m (fuelOf m)) (true, []) L in
  fst r = forallb (fun v => allValid m (normalize m (fuelOf m) v)) L
  /\ (fst r = true -> snd r = map (fun v => enc (doms m) (normalize m (fuelOf m) v)) L).
Proof.
  intros m L. induction L as [| v t [IH1 IH2]]; [split; reflexivity |]. cbn [fold_right forallb map].
  destruct (fold_right (p1 m (fuelOf m)) (true, []) t) as [b l] eqn:Er. cbn [fst snd] in *. unfold p1. cbn [fst snd].
  destruct b.
  - rewrite <- IH1, andb_true_r. split; [reflexivity |]. intros _. rewrite IH2 by reflexivity. reflexivity.
  - rewrite <- IH1, andb_false_r. split; [reflexivity | discriminate].
Qed.

(* ===== pass 2: the blocks ===== *)

(* State v's column: NF of v, then NF of each event's guarded effect. *)
Definition colOf (m : machine) (look : nat -> nat) (v : valn) : list nat :=
  look (enc (doms m) v) :: mapT (fun ge => look (enc (doms m) (gapp m ge v))) (evs m).

(* map f l, reversed, onto acc, in one pass. *)
Fixpoint revMap {A B} (f : A -> B) (l : list A) (acc : list B) : list B :=
  match l with [] => acc | x :: t => revMap f t (f x :: acc) end.

Lemma revMap_eq : forall {A B} (f : A -> B) l acc, revMap f l acc = rev (map f l) ++ acc.
Proof.
  intros A B f l. induction l as [| x t IH]; intro acc; [reflexivity |].
  cbn [revMap map rev]. rewrite IH, <- app_assoc. reflexivity.
Qed.

(* colOf m look v ++ buf, with two passes over the events. *)
Definition colOnto (m : machine) (look : nat -> nat) (v : valn) (buf : list nat) : list nat :=
  look (enc (doms m) v) :: rev_append (revMap (fun ge => look (enc (doms m) (gapp m ge v))) (evs m) []) buf.

Lemma colOnto_eq : forall m look v buf, colOnto m look v buf = colOf m look v ++ buf.
Proof.
  intros. unfold colOnto, colOf. rewrite revMap_eq, app_nil_r, rev_append_rev, rev_involutive, mapT_eq.
  reflexivity.
Qed.

(* Columns accumulate in buf (in order, since the box is visited from the
   end); at the first state of each group of 16 (number divisible by 16) the
   group's columns become blocks: W blocks for a full group. *)
Definition p2 (m : machine) (look : nat -> nat) (v : valn) (st : list nat * list (blk nat)) : list nat * list (blk nat) :=
  let buf := colOnto m look v (fst st) in
  let i := enc (doms m) v in
  if Nat.eqb (i - 16 * hi16 i) 0 then ([], rev_append (rev_append (chunk B16 0 buf) []) (snd st))
  else (buf, snd st).

Lemma colOf_length : forall m look v, length (colOf m look v) = S (length (evs m)).
Proof. intros. unfold colOf. cbn [length]. rewrite mapT_eq, map_length. reflexivity. Qed.

Lemma flat_map_length_u : forall {A} (f : A -> list nat) W l, (forall v, length (f v) = W) ->
  length (flat_map f l) = length l * W.
Proof. intros A f W l H. induction l as [| x t IH]; cbn; [reflexivity | rewrite app_length, H, IH; lia]. Qed.

Lemma nth_app_ge : forall {A} (l1 l2 : list A) k d, length l1 <= k -> nth k (l1 ++ l2) d = nth (k - length l1) l2 d.
Proof. intros. apply app_nth2. exact H. Qed.

(* The invariant of pass 2 over the states i, i+1, ... (l), F their columns:
   buf holds the columns of the states of i's group (none if i starts a
   group), and acc reads the rest of F. *)
Lemma p2_inv : forall m look l i,
  (forall j, j < length l -> enc (doms m) (nth j l []) = i + j) ->
  let W := S (length (evs m)) in
  let F := flat_map (colOf m look) l in
  let r := i - 16 * hi16 i in
  let h := if Nat.eqb r 0 then 0 else Nat.min (16 - r) (length l) in
  let R := fold_right (p2 m look) ([], []) l in
  fst R = firstn (h * W) F /\ forall k, bget 0 (snd R) 0 k = nth (h * W + k) F 0.
Proof.
  intros m look l. induction l as [| v t IH]; intros i Hi W F r h R.
  - unfold R, F. cbn [fold_right fst snd flat_map]. split; [rewrite firstn_nil; reflexivity |].
    intro k. cbn [bget]. symmetry. apply nth_overflow. cbn. lia.
  - assert (Ht : forall j, j < length t -> enc (doms m) (nth j t []) = S i + j).
    { intros j Hj. specialize (Hi (S j) ltac:(cbn; lia)). cbn [nth] in Hi. lia. }
    destruct (IH (S i) Ht) as [B A]. clear IH.
    set (F' := flat_map (colOf m look) t) in *.
    set (r' := S i - 16 * hi16 (S i)) in *.
    set (h' := if Nat.eqb r' 0 then 0 else Nat.min (16 - r') (length t)) in *.
    unfold R. cbn [fold_right]. destruct (fold_right (p2 m look) ([], []) t) as [buf acc] eqn:Ef.
    cbn [fst snd] in B, A.
    assert (Hv : enc (doms m) v = i) by (specialize (Hi 0 ltac:(cbn; lia)); cbn in Hi; lia).
    assert (HF : F = colOf m look v ++ F') by reflexivity.
    assert (Hc : length (colOf m look v) = W) by apply colOf_length.
    assert (HF' : length F' = length t * W) by (apply flat_map_length_u; intro; apply colOf_length).
    destruct (hi16_spec i) as [Ei Di]. destruct (hi16_spec (S i)) as [Es Ds].
    unfold p2. cbn [fst snd]. rewrite Hv. fold r. rewrite colOnto_eq.
    assert (Hbuf : colOf m look v ++ buf = firstn ((1 + h') * W) F).
    { rewrite B, HF. replace ((1 + h') * W) with (length (colOf m look v) + h' * W) by (rewrite Hc; lia).
      rewrite firstn_app_2. reflexivity. }
    destruct (Nat.eqb_spec r 0) as [Hr | Hr].
    + (* i starts a group: flush it. *)
      assert (Hh : h = 0) by (unfold h, r in *; destruct (Nat.eqb_spec (i - 16 * hi16 i) 0); [reflexivity | lia]).
      assert (Hr' : r' <> 0) by (unfold r', r in *; lia).
      assert (Hh' : h' = Nat.min (16 - r') (length t)) by (unfold h'; destruct (Nat.eqb_spec r' 0); [lia | reflexivity]).
      assert (Hr1 : r' = 1) by (unfold r', r in *; lia).
      cbn [fst snd]. rewrite Hh. split; [reflexivity |]. intro k. rewrite rev_rev_app, Hbuf, Nat.mul_0_l, Nat.add_0_l.
      set (G := firstn ((1 + h') * W) F).
      assert (Hle : h' <= length t) by lia.
      assert (HG : length G = (1 + h') * W) by (unfold G; rewrite firstn_length, HF, app_length, Hc, HF'; nia).
      destruct (Nat.eq_dec h' 15) as [H15 | H15].
      * (* a full group: exactly W blocks *)
        assert (Lc : length (chunk B16 0 G : list (blk nat)) = W) by (apply chunk_exact; rewrite HG, H15; lia).
        rewrite bget_app by lia. rewrite Lc.
        destruct (Compare_dec.lt_dec k (0 + 16 * W)) as [Hk | Hk]; cbv beta iota.
        -- rewrite bget_chunk. unfold G. rewrite nth_firstn. destruct (Compare_dec.lt_dec k ((1 + h') * W)) as [H | H].
           ++ apply Nat.ltb_lt in H. rewrite H. reflexivity.
           ++ rewrite H15 in H. lia.
        -- replace k with (k - 16 * W + (0 + 16 * W)) at 1 by lia. rewrite bget_shift by lia.
           rewrite A, HF, nth_app_ge by (rewrite Hc; lia). rewrite Hc, H15. f_equal. lia.
      * (* the last, partial group: G is all of F, and acc reads nothing *)
        assert (Hlt : h' = length t) by (rewrite Hh'; lia).
        assert (HGF : G = F) by (unfold G; apply firstn_all2; rewrite HF, app_length, Hc, HF', Hlt; lia).
        rewrite HGF. destruct (Compare_dec.lt_dec k (16 * length (chunk B16 0 F : list (blk nat)))) as [Hk | Hk].
        -- rewrite bget_app, bget_chunk by lia. destruct (Compare_dec.lt_dec k (0 + 16 * length (chunk B16 0 F))); [reflexivity | lia].
        -- rewrite bget_app by lia. destruct (Compare_dec.lt_dec k (0 + 16 * length (chunk B16 0 F))); [lia | cbv beta iota].
           pose proof (chunk_length B16 0 F) as LC.
           replace k with (k - 16 * length (chunk B16 0 F) + (0 + 16 * length (chunk B16 0 F))) at 1 by lia.
           rewrite bget_shift by lia. rewrite A.
           rewrite (nth_overflow F) by lia. apply nth_overflow. rewrite HF'. unfold W in *. rewrite Hlt. lia.
    + (* i is inside its group: keep the column in buf *)
      cbn [fst snd].
      assert (Hh1 : h = 1 + h').
      { unfold h, h'. destruct (Nat.eqb_spec r 0); [lia |].
        destruct (Nat.eqb_spec r' 0) as [Hr' | Hr']; cbn [length]; unfold r, r' in *; lia. }
      rewrite Hh1. split; [exact Hbuf |]. intro k. rewrite A, HF, nth_app_ge by (rewrite Hc; lia).
      rewrite Hc. f_equal. lia.
Qed.

(* ===== the compact rules oracle ===== *)

Definition checkBuildC (m : machine) (P : option (list (nat * nat))) : bool :=
  bounded m && signSafe m &&
  (let ds := doms m in
   let r1 := foldB ds (p1 m (fuelOf m)) (true, []) in
   fst r1 &&
   (let nE := lenT (evs m) 0 in
    pairs_okW nE P &&
    (let n := lenT (snd r1) 0 in
     let look := vlook 0 (of_listV 0 (snd r1)) in
     let Lb := snd (foldB ds (p2 m look) ([], [])) in
     scanC n nE Lb P))).

(* ===== checkBuildC is checkBuild ===== *)

Lemma nth_flat_map_u : forall {A} (f : A -> list nat) W (l : list A) dflt x j, (forall v, length (f v) = W) ->
  x < length l -> j < W -> nth (x * W + j) (flat_map f l) 0 = nth j (f (nth x l dflt)) 0.
Proof.
  intros A f W l dflt. induction l as [| v t IH]; intros x j H Hx Hj; cbn in Hx; [lia |].
  cbn [flat_map]. destruct x as [| x].
  - cbn [Nat.mul nth]. rewrite app_nth1 by (rewrite H; lia). reflexivity.
  - rewrite app_nth2 by (rewrite H; nia). rewrite H. replace (S x * W + j - W) with (x * W + j) by nia.
    cbn [nth]. apply IH; [exact H | lia | exact Hj].
Qed.

Section CompactBridge.
  Variable m : machine.
  Variable P : option (list (nat * nat)).
  Hypothesis Hwfc : wfc m = true.

  Let ds := doms m.
  Let Bx := boxR ds.
  Let n := prodL ds.
  Let nE := length (evs m).
  Let NFl := map (fun v => enc ds (normalize m (fuelOf m) v)) Bx.
  Let look := vlook 0 (of_listV 0 NFl).
  Let E := flat_map (colOf m look) Bx.

  Lemma look_nfR : forall k, k < n -> look k = nfR m k.
  Proof.
    intros k Hk. unfold look. rewrite vlook_of_listV. unfold NFl.
    rewrite (@nth_map_lt valn nat _ _ _ []) by (unfold Bx; rewrite boxR_len; exact Hk). reflexivity.
  Qed.

  Lemma E_entry : forall x j, x < n -> j < S nE ->
    nth (x * S nE + j) E 0 = match j with 0 => nfR m x | S e => stR m e x end.
  Proof.
    intros x j Hx Hj. unfold E. rewrite (@nth_flat_map_u valn _ (S nE) Bx []); [| intro; apply colOf_length | unfold Bx; rewrite boxR_len; exact Hx | exact Hj].
    destruct (enc_dec m x Hx) as [Ex Ix]. unfold Bx, ds in *.
    unfold colOf. destruct j as [| e]; cbn [nth].
    - rewrite Ex. apply look_nfR, Hx.
    - rewrite mapT_eq, (nth_map_lt _ _ _ noEvent) by (fold nE; lia). fold (evAt m e).
      pose proof (gapp_inBx m (evAt m e) _ Ix) as Hg. destruct (dec_enc m _ Hg) as [Hlt Hd].
      rewrite look_nfR by exact Hlt. unfold nfR, stR. rewrite stepI_gapp. f_equal. f_equal. exact Hd.
  Qed.

  Lemma Lb_reads : forall k, bget 0 (snd (fold_right (p2 m look) ([], []) Bx)) 0 k = nth k E 0.
  Proof.
    intro k. assert (Hi : forall j, j < length Bx -> enc (doms m) (nth j Bx []) = 0 + j).
    { intros j Hj. unfold Bx in Hj. rewrite boxR_len in Hj. apply (enc_dec m j Hj). }
    destruct (p2_inv m look Bx 0 Hi) as [_ R]. rewrite R. reflexivity.
  Qed.

  Lemma scan_ccA : forall Lb, (forall k, bget 0 Lb 0 k = nth k E 0) ->
    pairsOkA m P = true -> scanC n nE Lb P = ccA m P.
  Proof.
    intros Lb HLb Hpo. assert (Hpr : forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE).
    { intros p Hp. unfold pairsOkA in Hpo. rewrite forallb_forall in Hpo.
      specialize (Hpo p ltac:(destruct P; exact Hp)). apply andb_true_iff in Hpo. rewrite !ltn_spec in Hpo. exact Hpo. }
    apply eq_iff_eq_true. rewrite (scanC_spec n nE E Lb P HLb Hpr). cbv zeta.
    assert (HD : forall s, s < n -> inDf n (fun x => nth (x * S nE) E 0) s = inDA m (nth s Bx [])).
    { intros s Hs. unfold Bx, ds. rewrite <- (inDf_inDA m Hwfc s Hs). unfold inDf.
      rewrite <- (Nat.add_0_r (s * S nE)), (E_entry s 0 Hs) by lia. reflexivity. }
    assert (HP : forall s p, s < n -> In p (pairsOf nE P) ->
      pair_okF (fun e x => nth (x * S nE + S e) E 0) s p
      = valeqb (stepI m (fst p) (stepI m (snd p) (nth s Bx []))) (stepI m (snd p) (stepI m (fst p) (nth s Bx [])))).
    { intros s [a b] Hs Hp. destruct (Hpr _ Hp) as [Ha Hb]. cbn [fst snd] in *. unfold Bx, ds.
      transitivity (pair_okF (stR m) s (a, b)); [| apply (pair_okF_valeqb m s (a, b) Hs)]. unfold pair_okF. cbn [fst snd].
      rewrite (E_entry s (S a)), (E_entry s (S b)) by lia.
      destruct (enc_dec m s Hs) as [_ Is].
      assert (Hsa : stR m a s < n) by (apply (dec_enc m), stepI_inBx, Is).
      assert (Hsb : stR m b s < n) by (apply (dec_enc m), stepI_inBx, Is).
      rewrite (E_entry _ (S a) Hsb), (E_entry _ (S b) Hsa) by lia. reflexivity. }
    unfold ccA. rewrite forallb_forall. split.
    - intros H v Hv. apply box_in in Hv. destruct (dec_enc m v Hv) as [Hlt Hd].
      destruct (inDA m v) eqn:ED; [| reflexivity]. cbn [implb]. apply forallb_forall.
      intros p Hp. assert (Hp' : In p (pairsOf nE P)) by (destruct P; exact Hp).
      specialize (H _ Hlt). rewrite HD in H by exact Hlt. unfold Bx, ds in H. rewrite Hd in H.
      specialize (H ED p Hp'). rewrite HP in H by assumption. unfold Bx, ds in H. rewrite Hd in H. exact H.
    - intros H s Hs HDs p Hp. destruct (enc_dec m s Hs) as [_ Is].
      specialize (H _ (proj2 (box_in _ _) Is)). rewrite HD in HDs by exact Hs. unfold Bx, ds in HDs. rewrite HDs in H.
      cbn [implb] in H. rewrite forallb_forall in H. rewrite HP by assumption.
      apply H. destruct P; exact Hp.
  Qed.
End CompactBridge.

Theorem checkBuildC_eq : forall m P, checkBuildC m P = checkBuild m P.
Proof.
  intros m P. unfold checkBuildC, checkBuild. cbv zeta.
  destruct (bounded m), (signSafe m); cbn [andb]; try reflexivity.
  rewrite !foldB_eq. destruct (p1_spec m (boxR (doms m))) as [H1 H2].
  set (r1 := fold_right (p1 m (fuelOf m)) (true, []) (boxR (doms m))) in *.
  assert (Hw : fst r1 = wfc m).
  { rewrite H1. unfold wfc. apply forallb_same. intro x. rewrite box_in. reflexivity. }
  rewrite Hw. destruct (wfc m) eqn:Hwfc; [| destruct (pairsOkA m P); reflexivity]. cbn [andb].
  rewrite (H2 Hw), !lenT_eq, !Nat.add_0_r, map_length, boxR_len.
  assert (Hpo : pairs_okW (length (evs m)) P = pairsOkA m P) by (rewrite pairs_okW_eq; destruct P; reflexivity).
  rewrite Hpo. destruct (pairsOkA m P) eqn:EP; [| reflexivity]. cbn [andb].
  apply (scan_ccA m P Hwfc); [apply Lb_reads | exact EP].
Qed.

(* So every checkBuild theorem holds for checkBuildC; the runtime guarantee,
   for example: *)
Theorem checkBuildC_converges : forall m P, checkBuildC m P = true ->
  forall es1 es2, tequiv (indepA m P) es1 es2 -> Forall (fun e => e < length (evs m)) es1 ->
  forall v, In v (box (doms m)) -> inDA m v = true -> runT (stepI m) es1 v = runT (stepI m) es2 v.
Proof. intros m P H. rewrite checkBuildC_eq in H. apply checkBuild_converges with (P := P), H. Qed.
