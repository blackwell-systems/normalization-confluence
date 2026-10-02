(* The rules oracle, computed through step tables: checkBuildT.

   checkBuild (AstChecker.v) checks commutation pair by pair: for every state
   and every declared pair (a, b) it evaluates the rules four times (stepI a,
   stepI b, and each again on the other's result). That is states x pairs x 4
   steps, each an evaluation of the expression trees plus a normalization, and
   at 2^20 states and 190 pairs it takes minutes. checkBuildT decides the same
   property (checkBuildT_eq) and evaluates the rules once per state and event:

   - the states are numbered by a mixed-radix encoding (enc): variable 0 is
     the most significant digit, so state number s is entry s of the box
     enumeration (boxT, which lists boxR's valuations in boxR's order);
   - NF[s] is the number of the normal form of state s, from one
     normalization per state;
   - T[e][s] is NF of the state event e's guarded effect reaches from state s
     (gapp; the step is that state's normal form, so it is read from NF, not
     normalized again);
   - the cells check_fast scans (TableFast.v: state s, NF[s] and the column
     T[0][s] ... T[nE-1][s]) are built straight from the rules, state by state,
     with no table lists and no transposition, and the scan is check_fast's
     (scanI), which TableFn.scan_cells_fn proves equal to check_fn.

   Why this is checkBuild. wfc stays on the rules side, as checkBuild has it:
   the tables cannot replace it (a repair cycle whose length divides the fuel
   can return to its start, so NF would look like a retraction while wfc
   fails). Under wfc, the parts of check_fn about the tables (every NF entry
   and every step is a valid state) always hold; a state's number is a fixed
   point of NF exactly when the state is valid, and 0 is the zero state's
   number, so check_fn's domain (valid or 0) is checkBuild's (inDA); and since
   enc is injective on the box, equal step numbers are equal states. So
   check_fn on these tables is pairsOkA && ccA (tables_fn_eq), and
   checkBuildT m P = checkBuild m P for every machine and every declaration
   (checkBuildT_eq). Every theorem about checkBuild holds for checkBuildT
   unchanged.

   Every loop the extraction runs is tail-recursive or bounded by the number of
   variables (boxT, encA), so the stack does not grow with the states, events
   or pairs. No new unary nat recursion (layer is AstChecker's). Axiom-free. *)

Require Import NC.Trace.
Require Import NC.TableCheck.
Require Import NC.TableFast.
Require Import NC.TableFn.
Require Import NC.AstChecker.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Bool.
From Coq Require Import Lia.
Import ListNotations.

Local Open Scope bool_scope.

(* ===== the state numbering ===== *)

(* The product of the domain sizes: fuelOf's fold. *)
Definition prodL (ds : list nat) : nat := fold_left Init.Nat.mul ds 1.

Lemma fold_mul : forall l a, fold_left Init.Nat.mul l a = a * fold_left Init.Nat.mul l 1.
Proof.
  induction l as [| x t IH]; intro a; cbn [fold_left]; [lia |].
  rewrite IH, (IH (1 * x)). lia.
Qed.

Lemma prodL_cons : forall d ds, prodL (d :: ds) = d * prodL ds.
Proof. intros d ds. unfold prodL. cbn [fold_left]. rewrite fold_mul. lia. Qed.

(* The number of a valuation, by Horner's rule: variable 0 is the most
   significant digit. Tail-recursive on the variables. *)
Fixpoint encA (ds v : list nat) (acc : nat) : nat :=
  match ds, v with
  | d :: ds', x :: v' => encA ds' v' (acc * d + x)
  | _, _ => acc
  end.

Definition enc (ds v : list nat) : nat := encA ds v 0.

(* The same number, positionally (proofs only). *)
Fixpoint encR (ds v : list nat) : nat :=
  match ds, v with
  | _ :: ds', x :: v' => x * prodL ds' + encR ds' v'
  | _, _ => 0
  end.

Lemma encA_eq : forall ds v acc, length v = length ds -> encA ds v acc = acc * prodL ds + encR ds v.
Proof.
  induction ds as [| d ds IH]; intros [| x v] acc Hl; cbn [length] in Hl; try discriminate.
  - unfold prodL. cbn. lia.
  - cbn [encA encR]. rewrite IH by lia. rewrite prodL_cons. nia.
Qed.

(* The box, listed in boxR's order with tail-recursive loops: layer (from
   AstChecker.v) prepends in reverse, so it is given the tails reversed. *)
Fixpoint boxT (ds : list nat) : list valn :=
  match ds with
  | [] => [ [] ]
  | d :: rest => layer d (rev_append (boxT rest) []) []
  end.

Lemma prependAll_eq : forall x ws acc, prependAll x ws acc = rev (map (cons x) ws) ++ acc.
Proof.
  intros x ws. induction ws as [| w t IH]; intro acc; cbn [prependAll map rev]; [reflexivity |].
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma layer_eq : forall k wsr acc,
  layer k wsr acc = flat_map (fun v => map (cons v) (rev wsr)) (seq 0 k) ++ acc.
Proof.
  induction k as [| k IH]; intros wsr acc; cbn [layer]; [reflexivity |].
  rewrite IH, prependAll_eq, seq_S, flat_map_app. cbn [flat_map]. rewrite app_nil_r, map_rev.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma boxT_eq : forall ds, boxT ds = boxR ds.
Proof.
  induction ds as [| d rest IH]; [reflexivity |]. cbn [boxT boxR].
  rewrite layer_eq, rev_append_rev, app_nil_r, app_nil_r, rev_involutive, IH. reflexivity.
Qed.

Lemma flat_length : forall (W : list (list nat)) d a,
  length (flat_map (fun v => map (cons v) W) (seq a d)) = d * length W.
Proof.
  intros W d. induction d as [| d IH]; intro a; [reflexivity |].
  cbn [seq flat_map]. rewrite app_length, map_length, IH. lia.
Qed.

Lemma boxR_len : forall ds, length (boxR ds) = prodL ds.
Proof.
  induction ds as [| d rest IH]; [reflexivity |].
  cbn [boxR]. rewrite flat_length. unfold valn in *. rewrite IH, prodL_cons. reflexivity.
Qed.

Lemma nth_flat : forall (W : list (list nat)) d a x r, r < length W -> x < d ->
  nth (x * length W + r) (flat_map (fun v => map (cons v) W) (seq a d)) [] = (a + x) :: nth r W [].
Proof.
  intros W d. induction d as [| d IH]; intros a x r Hr Hx; [lia |].
  cbn [seq flat_map]. destruct x as [| x].
  - rewrite app_nth1 by (rewrite map_length; lia). cbn [Nat.mul Nat.add].
    rewrite (nth_indep _ [] (a :: [])) by (rewrite map_length; exact Hr).
    rewrite map_nth. f_equal. lia.
  - rewrite app_nth2 by (rewrite map_length; lia). rewrite map_length.
    replace (S x * length W + r - length W) with (x * length W + r) by lia.
    rewrite IH by lia. f_equal. lia.
Qed.

(* A valuation in the box is entry (its number) of the box, and its number is
   below the box size. *)
Lemma enc_box : forall ds v, In v (boxR ds) -> encR ds v < prodL ds /\ nth (encR ds v) (boxR ds) [] = v.
Proof.
  induction ds as [| d rest IH]; intros v Hv; cbn [boxR] in Hv |- *.
  - destruct Hv as [<- | []]. cbn. split; [unfold prodL; cbn; lia | reflexivity].
  - apply in_flat_map in Hv. destruct Hv as [x [Hx Hm]]. apply in_seq in Hx.
    apply in_map_iff in Hm. destruct Hm as [w [<- Hw]].
    destruct (IH w Hw) as [Hlt Hnth]. rewrite <- boxR_len in Hlt.
    cbn [encR]. rewrite <- boxR_len. split.
    + rewrite prodL_cons, <- boxR_len. unfold valn in *. nia.
    + rewrite nth_flat by (unfold valn in *; lia). cbn [Nat.add]. f_equal. exact Hnth.
Qed.

(* Entry s of the box is in the box and has number s. *)
Lemma box_enc : forall ds s, s < prodL ds -> encR ds (nth s (boxR ds) []) = s /\ In (nth s (boxR ds) []) (boxR ds).
Proof.
  intros ds s Hs. split; [| apply nth_In; rewrite boxR_len; exact Hs].
  revert s Hs. induction ds as [| d rest IH]; intros s Hs.
  - unfold prodL in Hs. cbn in Hs. assert (s = 0) by lia. subst. reflexivity.
  - rewrite prodL_cons in Hs. set (N := prodL rest) in *.
    assert (HN : 0 < N) by (destruct N; lia).
    pose proof (Nat.div_mod_eq s N) as Hdm. pose proof (Nat.mod_upper_bound s N ltac:(lia)) as Hm.
    assert (Hq : s / N < d) by (apply Nat.Div0.div_lt_upper_bound; lia).
    cbn [boxR]. replace s with (s / N * length (boxR rest) + s mod N) at 1
      by (unfold N in *; rewrite boxR_len; lia).
    rewrite nth_flat by (unfold N in *; rewrite ?boxR_len; lia).
    cbn [encR]. rewrite IH by exact Hm. fold N. lia.
Qed.

Lemma enc_inj : forall ds v w, In v (boxR ds) -> In w (boxR ds) -> encR ds v = encR ds w -> v = w.
Proof.
  intros ds v w Hv Hw E. destruct (enc_box ds v Hv) as [_ Nv]. destruct (enc_box ds w Hw) as [_ Nw].
  rewrite <- Nv, <- Nw, E. reflexivity.
Qed.

(* Number 0 is the zero state. *)
Lemma enc_zero : forall ds v, In v (boxR ds) -> (encR ds v = 0 <-> v = repeat 0 (length ds)).
Proof.
  induction ds as [| d rest IH]; intros v Hv; cbn [boxR] in Hv.
  - destruct Hv as [<- | []]. cbn. tauto.
  - apply in_flat_map in Hv. destruct Hv as [x [_ Hm]].
    apply in_map_iff in Hm. destruct Hm as [w [<- Hw]].
    assert (HN : 0 < prodL rest) by (rewrite <- boxR_len; destruct (boxR rest); [destruct Hw | cbn; lia]).
    cbn [encR length repeat]. split.
    + intros H. assert (Hw0 : encR rest w = 0) by lia. assert (x = 0) by nia. subst.
      f_equal. apply (IH w Hw), Hw0.
    + intros H. injection H as -> E. rewrite (proj2 (IH w Hw) E). lia.
Qed.

Lemma enc_eq : forall ds v, In v (boxR ds) -> enc ds v = encR ds v.
Proof.
  intros ds v Hv. unfold enc. rewrite encA_eq by (apply boxR_length; exact Hv). lia.
Qed.

Lemma valeqb_refl : forall a, valeqb a a = true.
Proof. induction a as [| x t IH]; cbn [valeqb]; [reflexivity | rewrite Nat.eqb_refl, IH; reflexivity]. Qed.

Lemma valeqb_iff : forall a b, valeqb a b = true <-> a = b.
Proof. intros a b. split; [apply valeqb_eq | intros <-; apply valeqb_refl]. Qed.

(* ===== the cells, from the rules ===== *)

(* The state event ge's guarded effect reaches from s: stepG normalizes it. *)
Definition gapp (m : machine) (ge : gevent) (s : valn) : valn :=
  if evalP (mins m) s (fst ge) then applyT m (snd ge) s else s.

Lemma stepI_gapp : forall m e s, stepI m e s = normalize m (fuelOf m) (gapp m (evAt m e) s).
Proof. reflexivity. Qed.

(* State s (valuation v): NF[s] and the column T[0][s] ... T[nE-1][s], where
   look k reads NF[k]. *)
Definition cellOf (m : machine) (look : nat -> nat) (s : nat) (v : valn) : cell :=
  {| lk := s; lnf := look s;
     lcol := chunk B16 0 (mapT (fun ge => look (enc (doms m) (gapp m ge v))) (evs m)) |}.

Fixpoint cellsR (m : machine) (look : nat -> nat) (s : nat) (vs : list valn) (acc : list cell) : list cell :=
  match vs with
  | [] => rev_append acc []
  | v :: t => cellsR m look (S s) t (cellOf m look s v :: acc)
  end.

Definition checkBuildT (m : machine) (P : option (list (nat * nat))) : bool :=
  bounded m && signSafe m &&
  (let ds := doms m in
   let bx := boxT ds in
   let nv := mapT (normalize m (fuelOf m)) bx in
   forallb (allValid m) nv &&
   (let n := lenT bx 0 in
    let nE := lenT (evs m) 0 in
    let look := vlook 0 (of_listV 0 (mapT (enc ds) nv)) in
    let cs := cellsR m look 0 bx [] in
    pairs_okW nE P && scanI n nE (of_listV (zcell n) cs) (mapT rpairOf (pairsOfT nE P)) 0 cs)).

(* ===== checkBuildT is checkBuild ===== *)

Lemma cellsR_app : forall m look vs s acc, cellsR m look s vs acc = rev acc ++ cellsR m look s vs [].
Proof.
  intros m look vs. induction vs as [| v t IH]; intros s acc; cbn [cellsR].
  - rewrite rev_append_rev. reflexivity.
  - rewrite IH, (IH _ [_]). cbn [rev app]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma cellsR_spec : forall m look vs s, length (cellsR m look s vs []) = length vs /\
  forall i z, i < length vs -> nth i (cellsR m look s vs []) z = cellOf m look (s + i) (nth i vs []).
Proof.
  intros m look vs. induction vs as [| v t IH]; intro s.
  - split; [reflexivity | intros i z Hi; cbn in Hi; lia].
  - cbn [cellsR]. rewrite cellsR_app. cbn [rev app]. destruct (IH (S s)) as [L N]. split.
    + cbn [length]. rewrite L. reflexivity.
    + intros [| i] z Hi; cbn [nth]; [rewrite Nat.add_0_r; reflexivity |].
      rewrite N by (cbn in Hi; lia). f_equal. lia.
Qed.

Lemma forallb_same : forall {A} (f : A -> bool) l1 l2, (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
  intros A f l1 l2 H. apply eq_iff_eq_true. rewrite !forallb_forall.
  split; intros G x Hx; apply G, H, Hx.
Qed.

Section Bridge.
  Variable m : machine.
  Variable P : option (list (nat * nat)).

  Let ds := doms m.
  Let F := fuelOf m.
  Let Bx := boxR ds.
  Let n := prodL ds.
  Let nE := length (evs m).
  Let dec (s : nat) : valn := nth s Bx [].

  (* The tables, as check_fn's accessors. *)
  Definition nfR (s : nat) : nat := enc ds (normalize m F (dec s)).
  Definition stR (e s : nat) : nat := enc ds (stepI m e (dec s)).

  Lemma inBx_iff : forall v, In v Bx <-> inRange ds v.
  Proof. intro v. unfold Bx. rewrite <- box_in. apply box_iff. Qed.

  Lemma normalize_inBx : forall v, In v Bx -> In (normalize m F v) Bx.
  Proof. intros v Hv. apply inBx_iff. apply normalize_pres. apply inBx_iff, Hv. Qed.

  Lemma gapp_inBx : forall ge v, In v Bx -> In (gapp m ge v) Bx.
  Proof.
    intros ge v Hv. apply inBx_iff. unfold gapp. destruct (evalP (mins m) v (fst ge));
      [apply applyT_pres |]; apply inBx_iff, Hv.
  Qed.

  Lemma stepI_inBx : forall e v, In v Bx -> In (stepI m e v) Bx.
  Proof. intros e v Hv. rewrite stepI_gapp. apply normalize_inBx, gapp_inBx, Hv. Qed.

  Lemma dec_enc : forall v, In v Bx -> enc ds v < n /\ dec (enc ds v) = v.
  Proof. intros v Hv. rewrite enc_eq by exact Hv. apply enc_box, Hv. Qed.

  Lemma enc_dec : forall s, s < n -> enc ds (dec s) = s /\ In (dec s) Bx.
  Proof.
    intros s Hs. destruct (box_enc ds s Hs) as [E I]. split; [| exact I].
    rewrite enc_eq by exact I. exact E.
  Qed.

  Lemma enc_eqb : forall v w, In v Bx -> In w Bx -> Nat.eqb (enc ds v) (enc ds w) = valeqb v w.
  Proof.
    intros v w Hv Hw. apply eq_iff_eq_true. rewrite Nat.eqb_eq, valeqb_iff. split; [| intros ->; reflexivity].
    rewrite !enc_eq by assumption. apply enc_inj; assumption.
  Qed.

  Hypothesis Hwfc : wfc m = true.

  Lemma wfc_valid : forall v, In v Bx -> allValid m (normalize m F v) = true.
  Proof.
    intros v Hv. unfold wfc in Hwfc. rewrite forallb_forall in Hwfc. apply Hwfc.
    apply box_in. exact Hv.
  Qed.

  (* A valid state's number is a valid table state. *)
  Lemma inVf_enc : forall w, In w Bx -> allValid m w = true -> inVf n nfR (enc ds w) = true.
  Proof.
    intros w Hw Hval. destruct (dec_enc w Hw) as [Hlt Hd]. unfold inVf. apply andb_true_iff. split.
    - apply ltd_spec. exact Hlt.
    - apply Nat.eqb_eq. unfold nfR. rewrite Hd, normalize_valid_id by exact Hval. reflexivity.
  Qed.

  (* check_fn's domain is checkBuild's. *)
  Lemma inDf_inDA : forall s, s < n -> inDf n nfR s = inDA m (dec s).
  Proof.
    intros s Hs. destruct (enc_dec s Hs) as [Es Is]. set (v := dec s) in *.
    unfold inDf, inDA. destruct (Compare_dec.lt_dec s n) as [_ | ]; [| lia]. cbn [andb].
    unfold nfR. fold v. rewrite <- Es at 1 2. rewrite enc_eqb by first [exact Is | apply normalize_inBx, Is].
    f_equal.
    - apply eq_iff_eq_true. rewrite valeqb_iff. split.
      + intros E. rewrite <- E. apply wfc_valid, Is.
      + intros Hval. apply normalize_valid_id, Hval.
    - apply eq_iff_eq_true. rewrite Nat.eqb_eq, valeqb_iff, enc_eq by exact Is.
      unfold zeroV. apply enc_zero, Is.
  Qed.

  Lemma pair_okF_valeqb : forall s p, s < n ->
    pair_okF stR s p = valeqb (stepI m (fst p) (stepI m (snd p) (dec s))) (stepI m (snd p) (stepI m (fst p) (dec s))).
  Proof.
    intros s [a b] Hs. destruct (enc_dec s Hs) as [_ Is]. unfold pair_okF, stR. cbn [fst snd].
    rewrite (proj2 (dec_enc _ (stepI_inBx b _ Is))), (proj2 (dec_enc _ (stepI_inBx a _ Is))).
    apply enc_eqb; apply stepI_inBx, stepI_inBx, Is.
  Qed.

  Lemma tables_fn_eq : check_fn n nE nfR stR P = pairsOkA m P && ccA m P.
  Proof.
    apply eq_iff_eq_true. rewrite check_fn_iff, andb_true_iff.
    assert (HP : pairsOf nE P = pairsA m P) by (destruct P; reflexivity).
    rewrite HP.
    assert (H1 : (forall p, In p (pairsA m P) -> fst p < nE /\ snd p < nE) <-> pairsOkA m P = true).
    { unfold pairsOkA. rewrite forallb_forall. split; intros H p Hp; specialize (H p Hp).
      - apply andb_true_iff. rewrite !ltn_spec. exact H.
      - apply andb_true_iff in H. rewrite !ltn_spec in H. exact H. }
    enough (H2 : (forall s, s < n -> inVf n nfR (nfR s) = true
                    /\ (forall e, e < nE -> inVf n nfR (stR e s) = true)
                    /\ (inDf n nfR s = true -> forall p, In p (pairsA m P) -> pair_okF stR s p = true))
                 <-> ccA m P = true) by tauto.
    { unfold ccA. rewrite forallb_forall. split.
      + intros H v Hv. apply box_in in Hv. fold ds in Hv. fold Bx in Hv.
        destruct (dec_enc v Hv) as [Hlt Hd]. destruct (H _ Hlt) as [_ [_ Hc]].
        rewrite inDf_inDA, Hd in Hc by exact Hlt.
        destruct (inDA m v) eqn:HD; [| reflexivity]. cbn [implb]. apply forallb_forall.
        intros p Hp. specialize (Hc eq_refl p Hp). rewrite pair_okF_valeqb, Hd in Hc by exact Hlt. exact Hc.
      + intros H s Hs. destruct (enc_dec s Hs) as [_ Is]. split; [| split].
        * unfold nfR. apply inVf_enc; [apply normalize_inBx, Is | apply wfc_valid, Is].
        * intros e _. unfold stR. apply inVf_enc; [apply stepI_inBx, Is |].
          rewrite stepI_gapp. apply wfc_valid, gapp_inBx, Is.
        * intros HD p Hp. rewrite inDf_inDA in HD by exact Hs.
          specialize (H (dec s) (proj2 (box_in _ _) Is)). rewrite HD in H. cbn [implb] in H.
          rewrite forallb_forall in H. rewrite pair_okF_valeqb by exact Hs. apply H, Hp. }
  Qed.
End Bridge.

Lemma nth_map_lt : forall {A B} (f : A -> B) l d d' i, i < length l -> nth i (map f l) d = f (nth i l d').
Proof.
  intros A B f l d d' i Hi. rewrite (nth_indep _ d (f d')) by (rewrite map_length; exact Hi). apply map_nth.
Qed.

(* The cells checkBuildT builds are the cells of the tables nfR and stR. *)
Lemma cells_ok : forall m,
  let ds := doms m in
  let bx := boxT ds in
  let look := vlook 0 (of_listV 0 (mapT (enc ds) (mapT (normalize m (fuelOf m)) bx))) in
  let cs := cellsR m look 0 bx [] in
  let n := prodL ds in
  length cs = n /\ forall x, x < n ->
    lk (nth x cs (zcell n)) = x /\ lnf (nth x cs (zcell n)) = nfR m x
    /\ (forall a, a < length (evs m) -> bget 0 (lcol (nth x cs (zcell n))) 0 a = stR m a x)
    /\ length (evs m) <= 16 * length (lcol (nth x cs (zcell n))).
Proof.
  intros m ds bx look cs n.
  assert (Hbx : bx = boxR ds) by apply boxT_eq.
  assert (Hlen : length bx = n) by (rewrite Hbx; apply boxR_len).
  (* look k reads NF[k]. *)
  assert (Hlook : forall k, k < n -> look k = nfR m k).
  { intros k Hk. unfold look. rewrite vlook_of_listV, !mapT_eq, map_map.
    rewrite (@nth_map_lt valn nat _ _ _ []) by lia. unfold nfR. rewrite Hbx. reflexivity. }
  destruct (cellsR_spec m look bx 0) as [Lc N]. split; [unfold cs; rewrite Lc; exact Hlen |].
  intros x Hx. unfold cs. rewrite N by lia. cbn [Nat.add]. unfold cellOf. cbn [lk lnf lcol].
  set (v := nth x bx []).
  assert (Hv : In v (boxR ds)) by (unfold v; rewrite Hbx; apply nth_In; rewrite <- Hbx; lia).
  set (L := mapT (fun ge => look (enc ds (gapp m ge v))) (evs m)).
  assert (HL : length L = length (evs m)) by (unfold L; rewrite mapT_eq, map_length; reflexivity).
  split; [reflexivity |]. split; [apply Hlook, Hx |]. split.
  - intros a Ha. rewrite bget_chunk. unfold L. rewrite mapT_eq.
    rewrite (nth_map_lt _ _ _ noEvent) by exact Ha. fold (evAt m a).
    pose proof (gapp_inBx m (evAt m a) v Hv) as Hg. destruct (dec_enc m _ Hg) as [Hlt Hd].
    rewrite Hlook by exact Hlt. unfold nfR, stR. rewrite stepI_gapp. f_equal. f_equal.
    etransitivity; [exact Hd |]. unfold v. rewrite Hbx. reflexivity.
  - rewrite <- HL. apply chunk_length.
Qed.

Lemma forallb_map_eq : forall {A B} (f : B -> bool) (g : A -> B) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. intros A B f g l. induction l as [| x t IH]; cbn [map forallb]; [reflexivity | rewrite IH; reflexivity]. Qed.

(* checkBuildT decides exactly checkBuild, on every machine and declaration. *)
Theorem checkBuildT_eq : forall m P, checkBuildT m P = checkBuild m P.
Proof.
  intros m P. unfold checkBuildT, checkBuild. cbv zeta.
  destruct (bounded m), (signSafe m); cbn [andb]; try reflexivity.
  assert (Hw : forallb (allValid m) (mapT (normalize m (fuelOf m)) (boxT (doms m))) = wfc m).
  { rewrite mapT_eq, boxT_eq, forallb_map_eq. unfold wfc. apply forallb_same.
    intro x. rewrite box_in. reflexivity. }
  rewrite Hw. destruct (wfc m) eqn:Hwfc; [| destruct (pairsOkA m P); reflexivity]. cbn [andb].
  rewrite !lenT_eq, !Nat.add_0_r, boxT_eq, boxR_len. rewrite <- (boxT_eq (doms m)).
  destruct (cells_ok m) as [Hl Hc].
  rewrite (scan_cells_fn _ _ (nfR m) (stR m) _ P Hl Hc), (tables_fn_eq m P Hwfc).
  rewrite andb_true_r. reflexivity.
Qed.

(* So every checkBuild theorem holds for checkBuildT; the runtime guarantee,
   for example: *)
Theorem checkBuildT_converges : forall m P, checkBuildT m P = true ->
  forall es1 es2, tequiv (indepA m P) es1 es2 -> Forall (fun e => e < length (evs m)) es1 ->
  forall v, In v (box (doms m)) -> inDA m v = true -> runT (stepI m) es1 v = runT (stepI m) es2 v.
Proof. intros m P H. rewrite checkBuildT_eq in H. apply checkBuild_converges with (P := P), H. Qed.
