(* The table oracle over accessor functions: check_fn.

   check_fast (TableFast.v) takes the tables as lists, so its caller must
   materialize every entry as a list cell (about 480 MB for 2^20 states and 20
   events, in OCaml or in the Go generated from this proof) and check_fast then
   copies them into its own index. check_fn takes the tables as two functions
   instead:
     nf s     the normal form of state s
     st e s   the state event e leads to from state s
   so a caller that already holds its tables (gsm holds them as arrays) passes
   two accessors over them and nothing is copied. Each read is a call.

   check_fn decides the same property as check_tables (TableCheck.v), on the
   functions themselves:
     - every declared pair names events below nE;
     - nf s is a valid state for every s < n (valid: x < n and nf x = x);
     - st e s is a valid state for every e < nE and s < n;
     - every declared pair commutes at every s < n that is valid or 0.
   The guarantee (check_fn_converges) is stated on the functions as given: from
   a valid state or the zero state, event sequences that differ only by
   reordering declared-independent events reach the same state under st. So
   what is proven is about whatever function the accessor computes; the caller
   must pass accessors that are pure and total (the same answer for the same
   arguments on every call, and an answer for every argument) and return
   non-negative values that fit the extraction's int (nat is extracted to
   OCaml int and Go int64).

   check_fast_fn proves check_fast equal to check_fn on the list accessors
   (fun s => nth s NFl 0) and (fun e s => nth s (nth e Tl []) 0), and
   check_tables_fn proves check_tables equal to check_fn on the Braun tries'
   lookups, so the list and function entry points decide the same property.

   Every loop is tail-recursive (allK, commF, pairsAll), so the extracted
   code's stack depth does not grow with the number of states, events or
   declared pairs. Axiom-free. *)

Require Import NC.Trace.
Require Import NC.TableCheck.
Require Import NC.TableFast.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Lia.
Import ListNotations.

(* f holds at i, i + 1, ..., i + k - 1. *)
Fixpoint allK (f : nat -> bool) (i k : nat) : bool :=
  match k with 0 => true | S k' => f i && allK f (S i) k' end.

Lemma allK_iff : forall f k i, allK f i k = true <-> forall j, i <= j -> j < i + k -> f j = true.
Proof.
  intros f k. induction k as [| k IH]; intro i; cbn [allK].
  - split; [intros _ j Hi Hj; lia | reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [H0 H1] j Hi Hj. destruct (Nat.eq_dec j i) as [-> | Hne]; [exact H0 |]. apply H1; lia.
    + intros H. split; [apply H; lia |]. intros j Hi Hj. apply H; lia.
Qed.

Lemma allK_ext : forall f g k i, (forall j, f j = g j) -> allK f i k = allK g i k.
Proof. intros f g k. induction k as [| k IH]; intros i H; cbn [allK]; [reflexivity | rewrite H, IH by exact H; reflexivity]. Qed.

Section Fn.
  Variables (n nE : nat) (nf : nat -> nat) (st : nat -> nat -> nat).

  Definition inVf (x : nat) : bool := ltd x n && Nat.eqb (nf x) x.
  Definition inDf (s : nat) : bool := ltd s n && (Nat.eqb (nf s) s || Nat.eqb s 0).

  Definition pair_okF (s : nat) (p : nat * nat) : bool :=
    Nat.eqb (st (fst p) (st (snd p) s)) (st (snd p) (st (fst p) s)).

  Fixpoint commF (s : nat) (rp : list (nat * nat)) : bool :=
    match rp with [] => true | p :: t => pair_okF s p && commF s t end.

  Lemma commF_eq : forall s rp, commF s rp = forallb (pair_okF s) rp.
  Proof. intros s rp. induction rp as [| p t IH]; cbn [commF forallb]; [reflexivity | rewrite IH; reflexivity]. Qed.

  Definition state_okF (rp : list (nat * nat)) (s : nat) : bool :=
    inVf (nf s) && allK (fun e => inVf (st e s)) 0 nE && implb (inDf s) (commF s rp).
End Fn.

Definition check_fn (n nE : nat) (nf : nat -> nat) (st : nat -> nat -> nat) (P : option (list (nat * nat))) : bool :=
  pairs_okW nE P && allK (state_okF n nE nf st (pairsOfT nE P)) 0 n.

(* check_fn as a statement. *)
Lemma check_fn_iff : forall n nE nf st P, check_fn n nE nf st P = true <->
  (forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE)
  /\ forall s, s < n ->
       inVf n nf (nf s) = true
       /\ (forall e, e < nE -> inVf n nf (st e s) = true)
       /\ (inDf n nf s = true -> forall p, In p (pairsOf nE P) -> pair_okF st s p = true).
Proof.
  intros n nE nf st P. unfold check_fn. rewrite andb_true_iff, pairs_okW_eq, allK_iff.
  assert (Hp : pairs_ok nE P = true <-> forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE).
  { unfold pairs_ok. rewrite forallb_forall. split; intros H p Hp; specialize (H p Hp).
    - apply andb_true_iff in H. rewrite !ltn_spec in H. exact H.
    - apply andb_true_iff. rewrite !ltn_spec. exact H. }
  rewrite Hp. apply and_iff_compat_l. split.
  - intros H s Hs. specialize (H s ltac:(lia) ltac:(lia)). unfold state_okF in H.
    rewrite !andb_true_iff, allK_iff in H. destruct H as [[Hnf Hst] Hc].
    split; [exact Hnf |]. split; [intros e He; apply Hst; lia |].
    intros HD p Hp'. rewrite HD in Hc. simpl in Hc. rewrite commF_eq, forallb_forall in Hc.
    apply Hc. apply pairsOfT_in. exact Hp'.
  - intros H s _ Hs. specialize (H s ltac:(lia)). destruct H as [Hnf [Hst Hc]]. unfold state_okF.
    rewrite !andb_true_iff, allK_iff. split; [split; [exact Hnf | intros e _ He; apply Hst; lia] |].
    destruct (inDf n nf s) eqn:HD; [| reflexivity]. simpl. rewrite commF_eq, forallb_forall.
    intros p Hp'. apply Hc; [reflexivity | apply pairsOfT_in; exact Hp'].
Qed.

(* The runtime guarantee, on the accessor functions themselves. *)
Theorem check_fn_converges :
  forall n nE nf st P, check_fn n nE nf st P = true ->
  forall es1 es2, tequiv (indep nE P) es1 es2 -> Forall (fun e => e < nE) es1 ->
  forall s, inDf n nf s = true -> runT st es1 s = runT st es2 s.
Proof.
  intros n nE nf st P Hchk. apply check_fn_iff in Hchk. destruct Hchk as [Hpr Hs].
  assert (HDlt : forall s, inDf n nf s = true -> s < n).
  { intros s H. unfold inDf in H. apply andb_true_iff in H. apply ltd_spec. tauto. }
  assert (Hcomm : forall a b s, In (a, b) (pairsOf nE P) -> inDf n nf s = true -> st a (st b s) = st b (st a s)).
  { intros a b s Hab HD. destruct (Hs s (HDlt s HD)) as [_ [_ Hc]].
    specialize (Hc HD (a, b) Hab). unfold pair_okF in Hc. apply Nat.eqb_eq. exact Hc. }
  apply (run_tequiv st (indep nE P) (fun e => e < nE) (fun s => inVf n nf s = true) (fun s => inDf n nf s = true)).
  - intros s H. unfold inVf in H. unfold inDf. apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite H1, H2. reflexivity.
  - intros e s He HD. apply (Hs s (HDlt s HD)). exact He.
  - intros a b s Ha Hb Hab HD. unfold indep in Hab. destruct P as [l |] eqn:HP.
    + destruct Hab as [Hab | Hba].
      * apply Hcomm; [unfold pairsOf; exact Hab | exact HD].
      * symmetry. apply Hcomm; [unfold pairsOf; exact Hba | exact HD].
    + destruct (Nat.lt_trichotomy a b) as [Hlt | [-> | Hgt]].
      * apply Hcomm; [unfold pairsOf; apply allPairs_in; lia | exact HD].
      * reflexivity.
      * symmetry. apply Hcomm; [unfold pairsOf; apply allPairs_in; lia | exact HD].
Qed.

(* check_fn depends only on the values of its accessors. *)
Lemma check_fn_ext : forall n nE nf nf' st st' P,
  (forall x, nf x = nf' x) -> (forall e x, st e x = st' e x) ->
  check_fn n nE nf st P = check_fn n nE nf' st' P.
Proof.
  intros n nE nf nf' st st' P Hnf Hst. unfold check_fn. f_equal. apply allK_ext. intro s.
  unfold state_okF, inVf, inDf. f_equal; [f_equal |].
  - rewrite !Hnf. reflexivity.
  - apply allK_ext. intro e. rewrite !Hst, !Hnf. reflexivity.
  - f_equal; [rewrite !Hnf; reflexivity |].
    induction (pairsOfT nE P) as [| p t IH]; cbn [commF]; [reflexivity |].
    rewrite IH. unfold pair_okF. rewrite !Hst. reflexivity.
Qed.

(* check_tables is check_fn on its tries' lookups. *)
Theorem check_tables_fn : forall n nE NF T P, check_tables n nE NF T P = check_fn n nE (nfv NF) (stp T) P.
Proof.
  intros n nE NF T P. apply eq_iff_eq_true. rewrite check_fn_iff. unfold check_tables.
  rewrite !andb_true_iff. unfold pairs_ok, nf_ok, steps_ok, comm_ok.
  rewrite !forallb_forall.
  assert (Hseq : forall m i, In i (seq 0 m) <-> i < m) by (intros m i; rewrite in_seq; lia).
  assert (HV : forall x, inV n NF x = inVf n (nfv NF) x) by (intro x; unfold inV, inVf; rewrite ltd_ltn; reflexivity).
  assert (HD : forall x, inD n NF x = inDf n (nfv NF) x) by (intro x; unfold inD, inDf; rewrite ltd_ltn; reflexivity).
  split.
  - intros [[[Hp Hnf] Hst] Hc]. split.
    + intros p Hin. specialize (Hp p Hin). apply andb_true_iff in Hp. rewrite !ltn_spec in Hp. exact Hp.
    + intros s Hs. split; [rewrite <- HV; apply Hnf, Hseq, Hs |]. split.
      * intros e He. specialize (Hst e (proj2 (Hseq _ _) He)). cbv zeta in Hst. rewrite forallb_forall in Hst.
        rewrite <- HV. apply Hst, Hseq, Hs.
      * intros Hds p Hin. specialize (Hc p Hin). cbv zeta in Hc. rewrite forallb_forall in Hc.
        specialize (Hc s (proj2 (Hseq _ _) Hs)). rewrite HD, Hds in Hc. exact Hc.
  - intros [Hp Hs]. split; [split; [split |] |].
    + intros p Hin. apply andb_true_iff. rewrite !ltn_spec. apply Hp, Hin.
    + intros s Hin. rewrite HV. apply Hs, Hseq, Hin.
    + intros e He. cbv zeta. rewrite forallb_forall. intros s Hin. rewrite HV.
      apply (Hs s (proj1 (Hseq _ _) Hin)), Hseq, He.
    + intros p Hin. cbv zeta. rewrite forallb_forall. intros s Hs'. apply Hseq in Hs'.
      rewrite HD. destruct (inDf n (nfv NF) s) eqn:E; [| reflexivity]. simpl.
      apply (Hs s Hs'); [exact E | exact Hin].
Qed.

(* ===== check_fast's scan over any cells =====

   check_fast builds its cells from the tables as lists (TableFast.cells), but
   its scan (scanI) needs only that cell x holds x, nf x and the column
   st 0 x ... st (nE-1) x. A caller that can build the cells directly, state by
   state, skips the lists and the transposition: AstTables.v builds them from
   the rules. scan_cells_fn: for any such cells, the scan decides check_fn on
   nf and st. *)
Section Cells.
  Variables (n nE : nat) (nf : nat -> nat) (st : nat -> nat -> nat) (cs : list cell) (P : option (list (nat * nat))).

  Hypothesis Hlen : length cs = n.
  Hypothesis Hcell : forall x, x < n ->
    lk (nth x cs (zcell n)) = x /\ lnf (nth x cs (zcell n)) = nf x
    /\ (forall a, a < nE -> bget 0 (lcol (nth x cs (zcell n))) 0 a = st a x)
    /\ nE <= 16 * length (lcol (nth x cs (zcell n))).

  Let ct := of_listV (zcell n) cs.
  Let look := vlook (zcell n) ct.

  Lemma lookC_eq : forall x, look x = nth x cs (zcell n).
  Proof. intro x. apply vlook_of_listV. Qed.

  Lemma lookC_ok : forall x, cell_ok n (look x) = inVf n nf x.
  Proof.
    intro x. rewrite lookC_eq. unfold cell_ok, inVf.
    destruct (Compare_dec.lt_dec x n) as [Hx | Hx].
    - destruct (Hcell x Hx) as [Ek [Ef _]]. rewrite Ek, Ef.
      destruct (Compare_dec.lt_dec x n); [reflexivity | lia].
    - rewrite nth_overflow by lia. unfold zcell. cbn [lk lnf].
      destruct (Compare_dec.lt_dec n n); [lia | reflexivity].
  Qed.

  Lemma lsC_get : forall s e, s < n -> e < nE ->
    bget (zcell n) (mapT (bmap look) (lcol (nth s cs (zcell n)))) 0 e = look (st e s).
  Proof.
    intros s e Hs He. destruct (Hcell s Hs) as [_ [_ [C L]]].
    rewrite mapT_eq, (bget_map 0) by lia. rewrite C by exact He. reflexivity.
  Qed.

  Lemma lsC_length : forall s, s < n -> nE <= 16 * length (mapT (bmap look) (lcol (nth s cs (zcell n)))).
  Proof. intros s Hs. destruct (Hcell s Hs) as [_ [_ [_ L]]]. rewrite mapT_eq, map_length. exact L. Qed.

  Lemma state_okC_iff : forall s, s < n -> (forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE) ->
    state_okI n nE ct (mapT rpairOf (pairsOfT nE P)) s (nth s cs (zcell n)) = true <->
    inVf n nf (nf s) = true
    /\ (forall e, e < nE -> inVf n nf (st e s) = true)
    /\ (inDf n nf s = true -> forall p, In p (pairsOf nE P) -> pair_okF st s p = true).
  Proof.
    intros s Hs Hpr. unfold state_okI. cbv zeta. fold look. rewrite commI_eq, (mapT_eq rpairOf).
    set (ls := mapT (bmap look) (lcol (nth s cs (zcell n)))).
    destruct (Hcell s Hs) as [_ [Hlnf _]].
    assert (HinD : inDf n nf s = (ltd s n && (Nat.eqb (lnf (nth s cs (zcell n))) s || Nat.eqb s 0))).
    { unfold inDf. rewrite Hlnf. reflexivity. }
    assert (Hsteps : bfaL (cell_ok n) nE 0 ls = true <-> forall e, e < nE -> inVf n nf (st e s) = true).
    { rewrite (bfaL_iff (zcell n)). split.
      - intros H e He. rewrite <- lookC_ok, <- lsC_get by assumption. apply H; [lia | exact He |].
        pose proof (lsC_length s Hs) as L. fold ls in L. lia.
      - intros H k _ Hk _. unfold ls. rewrite lsC_get, lookC_ok by assumption. apply H, Hk. }
    (* With every step valid, each pair reads the two step targets' columns. *)
    assert (Hpair : (forall e, e < nE -> inVf n nf (st e s) = true) -> forall p, In p (pairsOf nE P) ->
      pair_okI (zcell n) ls (rpairOf p) = pair_okF st s p).
    { intros Hst p Hp. destruct (Hpr p Hp) as [Ha Hb].
      assert (Hlt : forall e, e < nE -> st e s < n).
      { intros e He. specialize (Hst e He). unfold inVf in Hst. apply andb_true_iff in Hst.
        apply ltd_spec. tauto. }
      unfold pair_okI, pair_okF, rpairOf. cbv zeta. cbn [qa qb da db]. rewrite !qget_at.
      unfold ls. rewrite !lsC_get by assumption. rewrite !lookC_eq.
      destruct (Hcell _ (Hlt _ Hb)) as [_ [_ [Cb _]]]. destruct (Hcell _ (Hlt _ Ha)) as [_ [_ [Ca _]]].
      rewrite Cb, Ca by assumption. reflexivity. }
    rewrite <- HinD, lookC_ok, Hlnf, !andb_true_iff, Hsteps. split.
    - intros [[Hnf Hst] Hc]. split; [exact Hnf |]. split; [exact Hst |].
      intros HD p Hp. rewrite HD in Hc. simpl in Hc. rewrite forallb_forall in Hc.
      rewrite <- Hpair by assumption. apply Hc. apply in_map. apply pairsOfT_in. exact Hp.
    - intros [Hnf [Hst Hc]]. split; [split; assumption |].
      destruct (inDf n nf s) eqn:HD; [| reflexivity]. simpl. apply forallb_forall.
      intros r Hr. apply in_map_iff in Hr. destruct Hr as [p [<- Hp]]. apply pairsOfT_in in Hp.
      rewrite Hpair by assumption. apply Hc; [reflexivity | exact Hp].
  Qed.

  Theorem scan_cells_fn :
    pairs_okW nE P && scanI n nE ct (mapT rpairOf (pairsOfT nE P)) 0 cs = check_fn n nE nf st P.
  Proof.
    apply eq_iff_eq_true. rewrite check_fn_iff, andb_true_iff, scanI_iff, Hlen, pairs_okW_eq.
    assert (Hp : pairs_ok nE P = true <-> forall p, In p (pairsOf nE P) -> fst p < nE /\ snd p < nE).
    { unfold pairs_ok. rewrite forallb_forall. split; intros H p Hp; specialize (H p Hp).
      - apply andb_true_iff in H. rewrite !ltn_spec in H. exact H.
      - apply andb_true_iff. rewrite !ltn_spec. exact H. }
    rewrite Hp. split.
    - intros [Hpr H]. split; [exact Hpr |]. intros s Hs. apply (state_okC_iff s Hs Hpr), (H s Hs).
    - intros [Hpr H]. split; [exact Hpr |]. intros s Hs. apply (state_okC_iff s Hs Hpr), (H s Hs).
  Qed.
End Cells.

(* The list entry point is check_fn on the list accessors. *)
Theorem check_fast_fn : forall n nE NFl Tl P, length NFl = n -> length Tl = nE ->
  check_fast n nE NFl Tl P = check_fn n nE (fun s => nth s NFl 0) (fun e s => nth s (nth e Tl []) 0) P.
Proof.
  intros n nE NFl Tl P Hn HnE. rewrite check_fast_eq by assumption. rewrite check_tables_fn.
  apply check_fn_ext.
  - intro x. apply tget_of_list.
  - intros e x. unfold stp, row. change TLeaf with (of_list []). rewrite map_nth. apply tget_of_list.
Qed.
