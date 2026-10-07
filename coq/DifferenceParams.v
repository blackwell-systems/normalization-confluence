(* DifferenceParams.v: difference constraints for events with integer parameters ("withdraw
   amount", "reserve qty", "book n rooms"; roadmap item 8, the arithmetic route). Axiom-free.

   Model. DifferenceAbstraction's registries (gsm's combinators, saturating writes, invariants
   with repairs, the governed step pgov K k = K repair steps after the event, the runtime step
   prun normalizing first), with events that take arguments. Event kind k declares m parameters,
   parameter j in a range [lo_j, hi_j]; in its guard and effect DV (n + j) reads parameter j.
   Parameters are read-only. pgov K k ps s applies kind k with arguments ps.

   The joint state. For one event, s ++ ps (n + m coordinates); for a CC1 pair, s ++ ps1 ++ ps2
   (n + m1 + m2). joint P l places the events of l in the joint state as an unparameterized
   registry (jev, clipI) and computes the parameterized one exactly (jcc1, jidem, jvalid, jitr).
   A parameter stays a coordinate when every comparison and write it occurs in is a difference
   constraint over the joint state. Then it costs nothing: guards x - p >= c, p <= a, writes
   x := p + c.

   Does x := x - p fit? No, not as a coordinate. x + p is a sum of two coordinates, and the
   region relation does not survive it at any threshold: addw_no_threshold gives, for every W,
   two joint states in range, related at W, where CC1 fails at one and holds at the other. And
   addp_check_passes / addp_diverges: the representative check of x := x + p with p a coordinate
   passes and the registry diverges (doubling: x + p = w only far from every anchor). What does
   fit: an EXACT parameter, read as its value. A comparison or write that is not a difference
   constraint with parameters as coordinates (fbA, fbW: x := x + p, x := x - p, reserved + q <=
   stock) reads its parameters as constants (mask, tx with sg); for each value of the exact
   parameters it is then a difference constraint with a constant offset, in dfrag, with |p| in mu
   or gam. Related joint states agree on every coordinate whose range has width at most 2W
   (exact_eq), so an exact parameter of width at most 2 (gam + mu) is the same in a state and its
   representative. So balance := balance - amount fits exactly when the threshold pays amount's
   magnitude: the size stays independent of the variables' ranges and grows with amount's.
   exact_needs_width: below that, related states differ on CC1.

   The fragment (pfrag P A gam mu, boolean): dfrag of the variables' registry; for each kind, the
   effect writes variables only (tgt_ok), exact parameters have width <= 2 (gam + mu) (exok), and
   for every value of the exact parameters (sigs) the joint registry of every event and of every
   pair of events is in dfrag, parameter bounds among the anchors.

   Theorems (each an iff over the declared ranges of variables AND parameters, for every W at
   least the threshold; the representatives are RepS of the joint box jb P [k1; k2], every
   coordinate within (n + m1 + m2)(W + 1) of an anchor).
   - pterm_abs: repair within K steps (threshold gam + K mu; the invariants have no parameters).
   - pcc1v_abs: CC1 for the pairs of I at every valid state and all arguments (gam + 4(K + 1) mu).
   - pidemv_abs: idempotence of kind k, the same arguments twice (gam + 3(K + 1) mu, n + m).
   - pgsm_exact, pgsm_sound: gsm's guarantee for sequences of events with arguments, trace
     equivalence over the kinds; pbuild_sound, pbuild_perm, pidem_build: end to end from the
     boolean checks (pterm_check, pcc1v_check, pidemv_check, exact specifications);
     pcheck_fail_real: a failing check is a real failure.
   - pcc1_domain_size, pidem_domain_size: at most (|A| (2R + 1))^N, N = n + m1 + m2 (or n + m),
     R = N (W + 1): independent of the widths of all ranges, abstract parameters' included.
   The special cases: m0_special (with embed_frag, embed_cc1_box, embed_cc1_rep, pgov_embed):
   DifferenceAbstraction's dcc1v_abs is pcc1v_abs with no parameters. pradius0, preps0_in_dom: at
   threshold 0 the radius of the joint box is n + m1 + m2 (n + 2m for m parameters each), the
   cutoff of AbstractionCutoff.cc1_abs and AbstractionGsm.cc1_valid_abs, n + m for idempotence.

   Non-vacuity (ranges up to 10^9).
   - wallet_p_*: balance in [-1000, 10^9]; deposit(a), withdraw(b) when balance >= b, fee(f),
     amounts in [1, 3]; set(v), v in [-1000, 10^9] abstract; overdraft repair. Deposits converge,
     fees converge, set is idempotent; the other pairs diverge at real states (the guard; the
     upper bound, 10^9 - 1 with 3 and 3; the repair at 0).
   - facts_*: deposited += a, requested += b, the overdraft flag derived by invariants: every
     pair converges, any permutation, from every state (242208 joint representatives per pair).
   - stock_*: restock(q), reserve(q) if reserved + q <= stock; restocks converge.
   - room_*: book(n) under a cap, cancel(n), setcap(c) with c in [0, 10^9] abstract; cancels
     converge.
   Boundaries.
   - addw_*: x := x + p with p a coordinate, every threshold fails; refused unless 2 (gam + mu)
     covers p's range.
   - addp_*: the check passes (7600 representatives), the registry diverges, refused.
   - sum2_*: x := p + q, the same (241920 representatives).
   - exact_needs_width: an exact parameter's range is paid in the threshold. *)

Require Import NC.Newman NC.Governance NC.SymmetryCutoff NC.AbstractionCutoff NC.Trace NC.DifferenceAbstraction.
From Coq Require Import List Arith Lia Bool ZArith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* ============================================================================================ *)
(* Registries with parameterized events.                                                        *)
(* ============================================================================================ *)

(* An event kind: the declared range [lo_j, hi_j] of each parameter, a guard and an effect. In
   the guard and the effect, DV i reads variable i for i < n and parameter i - n for
   n <= i < n + m (n variables, m parameters); a larger index reads 0. Parameters are read-only. *)
Record pevent : Type := mkE {
  eprm : list (Z * Z);
  eguard : dpred;
  eeff : transform }.

(* A registry: the declared range of each variable, the event kinds, the invariants (over the
   variables only). *)
Record pprog : Type := mkPP {
  plo : list Z;
  phi : list Z;
  pev : list pevent;
  pinv : list (dpred * transform) }.

(* An unknown kind is a no-op. *)
Definition dummyE : pevent := mkE [] DTrue [].

(* The registry without its events: the variables and the invariants. *)
Definition base (P : pprog) : dprog := mkD (plo P) (phi P) [] (pinv P).

Definition pn (P : pprog) : nat := length (plo P).
Definition nk (P : pprog) : nat := length (pev P).
Definition evOf (P : pprog) (k : nat) : pevent := nth k (pev P) dummyE.
Definition prmOf (P : pprog) (k : nat) : list (Z * Z) := eprm (evOf P k).
Definition nprm (P : pprog) (k : nat) : nat := length (prmOf P k).

Section PSem.
  Variable P : pprog.

  (* A write: the target saturates at its declared bounds (gsm's SetInt); the value is read in the
     state extended by the arguments. *)
  Definition pwrite (ps s : list Z) (a : assign) : list Z :=
    upd s (fst a) (clampZ (nth (fst a) (plo P) 0%Z) (nth (fst a) (phi P) 0%Z) (evalD (s ++ ps) (snd a))).

  Definition papplyT (ps : list Z) (t : transform) (s : list Z) : list Z := fold_left (pwrite ps) t s.

  (* Event k applied with arguments ps: a no-op when the guard is false. *)
  Definition pevt (ev : pevent) (ps s : list Z) : list Z :=
    if evalP (s ++ ps) (eguard ev) then papplyT ps (eeff ev) s else s.

  Definition pap (k : nat) (ps s : list Z) : list Z := pevt (evOf P k) ps s.

  Definition pvalid (s : list Z) : bool := dvalid (base P) s.
  Definition prepair (s : list Z) : list Z := drepair (base P) s.

  (* The governed step: the event with its arguments, then K repair steps. *)
  Definition pgov (K k : nat) (ps s : list Z) : list Z := itr K prepair (pap k ps s).

  (* gsm's runtime step: normalize, then the governed step. *)
  Definition prun (K k : nat) (ps s : list Z) : list Z := pgov K k ps (itr K prepair s).

  (* The states: every variable in range. The arguments of kind k: every parameter in range. *)
  Definition PInBox (s : list Z) : Prop := InBox (base P) s.
End PSem.

Definition bx (lo hi s : list Z) : Prop :=
  length s = length lo /\ forall i, (i < length lo)%nat -> (nth i lo 0 <= nth i s 0 <= nth i hi 0)%Z.

Definition PArgs (P : pprog) (k : nat) (ps : list Z) : Prop :=
  bx (map fst (prmOf P k)) (map snd (prmOf P k)) ps.

Lemma inbox_bx : forall Q s, InBox Q s <-> bx (dlo Q) (dhi Q) s.
Proof. intros Q s. unfold InBox, bx, nv. reflexivity. Qed.

(* ============================================================================================ *)
(* The joint state: the variables followed by the arguments of one or two events.               *)
(* ============================================================================================ *)

(* tx n off m ex sg e: the expression of an event with m parameters placed in a joint state whose
   parameter block starts at off. A parameter j marked exact in ex reads its value nth j sg
   (a constant); any other parameter reads its coordinate off + j; an index beyond reads 0. *)
Fixpoint tx (n off m : nat) (ex : list bool) (sg : list Z) (e : dexp) : dexp :=
  match e with
  | DV i => if Nat.ltb i n then DV i
            else if Nat.ltb i (n + m) then
              (if nth (i - n) ex false then DL (nth (i - n) sg 0%Z) else DV (off + (i - n)))
            else DL 0
  | DL c => DL c
  | DAdd a b => DAdd (tx n off m ex sg a) (tx n off m ex sg b)
  | DSub a b => DSub (tx n off m ex sg a) (tx n off m ex sg b)
  end.

(* A comparison falls back to exact parameters when, with every parameter a coordinate, it is not
   a difference constraint (for example reserved + q <= stock). *)
Definition fbA (n m : nat) (a b : dexp) : bool :=
  match norm (DSub (tx n n m [] [] a) (tx n n m [] [] b)) with Some _ => false | None => true end.

(* A write falls back when, with every parameter a coordinate, it is not x := y + c or x := c
   (for example x := x + p, x := x - p, x := p + q). *)
Definition fbW (n m : nat) (e : dexp) : bool :=
  match norm (tx n n m [] [] e) with Some (_, None, _) => false | _ => true end.

Fixpoint txP (n off m : nat) (ex : list bool) (sg : list Z) (p : dpred) : dpred :=
  match p with
  | DTrue => DTrue
  | DCmp o a b => if fbA n m a b then DCmp o (tx n off m ex sg a) (tx n off m ex sg b)
                  else DCmp o (tx n off m [] [] a) (tx n off m [] [] b)
  | DAnd p q => DAnd (txP n off m ex sg p) (txP n off m ex sg q)
  | DOr p q => DOr (txP n off m ex sg p) (txP n off m ex sg q)
  | DNot p => DNot (txP n off m ex sg p)
  end.

Definition txW (n off m : nat) (ex : list bool) (sg : list Z) (e : dexp) : dexp :=
  if fbW n m e then tx n off m ex sg e else tx n off m [] [] e.

(* The exact parameters of an event: those read by a comparison or a write that falls back. *)
Fixpoint occ (i : nat) (e : dexp) : bool :=
  match e with
  | DV k => Nat.eqb k i
  | DL _ => false
  | DAdd a b | DSub a b => occ i a || occ i b
  end.

Fixpoint occP (n m i : nat) (p : dpred) : bool :=
  match p with
  | DTrue => false
  | DCmp _ a b => fbA n m a b && (occ i a || occ i b)
  | DAnd p q | DOr p q => occP n m i p || occP n m i q
  | DNot p => occP n m i p
  end.

Definition occT (n m i : nat) (t : transform) : bool := existsb (fun a => fbW n m (snd a) && occ i (snd a)) t.

Definition emask (n : nat) (ev : pevent) : list bool :=
  map (fun j => occP n (length (eprm ev)) (n + j) (eguard ev) || occT n (length (eprm ev)) (n + j) (eeff ev))
      (seq 0 (length (eprm ev))).

Definition mask (P : pprog) (k : nat) : list bool := emask (pn P) (evOf P k).

(* An event placed in the joint state, its exact parameters read from sg. *)
Definition jev (n off : nat) (ev : pevent) (sg : list Z) : dpred * transform :=
  (txP n off (length (eprm ev)) (emask n ev) sg (eguard ev),
   map (fun a => (fst a, txW n off (length (eprm ev)) (emask n ev) sg (snd a))) (eeff ev)).

(* An invariant in the joint state: indices beyond the variables read 0, as in the registry. *)
Definition clipI (n : nat) (iv : dpred * transform) : dpred * transform :=
  (txP n n 0 [] [] (fst iv), map (fun a => (fst a, tx n n 0 [] [] (snd a))) (snd iv)).

Fixpoint jevs (P : pprog) (off : nat) (l : list (nat * list Z)) : list (dpred * transform) :=
  match l with
  | [] => []
  | (k, sg) :: l' => jev (pn P) off (evOf P k) sg :: jevs P (off + nprm P k) l'
  end.

Definition jlo (P : pprog) (ks : list nat) : list Z := plo P ++ flat_map (fun k => map fst (prmOf P k)) ks.
Definition jhi (P : pprog) (ks : list nat) : list Z := phi P ++ flat_map (fun k => map snd (prmOf P k)) ks.

(* The joint box of kinds ks: the variables and the parameters of each kind, with their ranges. *)
Definition jb (P : pprog) (ks : list nat) : dprog := mkD (jlo P ks) (jhi P ks) [] [].

(* The joint registry of the events l = [(k1, sg1); ...]: an unparameterized registry over the
   joint state, parameters as read-only coordinates, exact parameters as the constants sg. *)
Definition joint (P : pprog) (l : list (nat * list Z)) : dprog :=
  mkD (jlo P (map fst l)) (jhi P (map fst l)) (jevs P (pn P) l) (map (clipI (pn P)) (pinv P)).

(* ============================================================================================ *)
(* The joint registry computes the parameterized one.                                           *)
(* ============================================================================================ *)

Lemma nth_app_r : forall (l r : list Z) i, nth (length l + i) (l ++ r) 0%Z = nth i r 0%Z.
Proof. induction l as [|x l IH]; intros r i; simpl; auto. Qed.

Lemma upd_app : forall s R k v, (k < length s)%nat -> upd (s ++ R) k v = upd s k v ++ R.
Proof.
  induction s as [|x s IH]; intros R [|k] v H; simpl in *; try lia; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.

Lemma nth_nil_false : forall j, nth j (@nil bool) false = false.
Proof. intros [|j]; reflexivity. Qed.

Theorem tx_eval : forall n m ex sg s pre ps post off e, length s = n -> length ps = m ->
  off = (n + length pre)%nat ->
  (forall j, (j < m)%nat -> nth j ex false = true -> nth j sg 0%Z = nth j ps 0%Z) ->
  evalD (s ++ pre ++ ps ++ post) (tx n off m ex sg e) = evalD (s ++ ps) e.
Proof.
  intros n m ex sg s pre ps post off e Hs Hp Ho Ha.
  induction e as [i | c | a IHa b IHb | a IHa b IHb]; simpl; try (rewrite IHa, IHb); try reflexivity.
  destruct (Nat.ltb_spec i n) as [H1 | H1].
  - simpl. rewrite !app_nth1 by lia. reflexivity.
  - rewrite (app_nth2 s ps) by lia. rewrite Hs.
    destruct (Nat.ltb_spec i (n + m)) as [H2 | H2].
    + destruct (nth (i - n) ex false) eqn:E.
      * simpl. apply Ha; [lia | exact E].
      * simpl. subst off. replace (n + length pre + (i - n))%nat with (length s + (length pre + (i - n)))%nat by lia.
        rewrite nth_app_r, nth_app_r. apply app_nth1. lia.
    + simpl. rewrite nth_overflow by lia. reflexivity.
Qed.

Theorem txP_eval : forall n m ex sg s pre ps post off p, length s = n -> length ps = m ->
  off = (n + length pre)%nat ->
  (forall j, (j < m)%nat -> nth j ex false = true -> nth j sg 0%Z = nth j ps 0%Z) ->
  evalP (s ++ pre ++ ps ++ post) (txP n off m ex sg p) = evalP (s ++ ps) p.
Proof.
  intros n m ex sg s pre ps post off p Hs Hp Ho Ha.
  assert (H0 : forall j, (j < m)%nat -> nth j [] false = true -> nth j (@nil Z) 0%Z = nth j ps 0%Z)
    by (intros j _ H; rewrite nth_nil_false in H; discriminate).
  induction p as [| o a b | p IHp q IHq | p IHp q IHq | p IHp]; simpl.
  - reflexivity.
  - destruct (fbA n m a b); simpl.
    + rewrite (tx_eval n m ex sg s pre ps post off a), (tx_eval n m ex sg s pre ps post off b) by assumption. reflexivity.
    + rewrite (tx_eval n m [] [] s pre ps post off a), (tx_eval n m [] [] s pre ps post off b) by assumption. reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - rewrite IHp. reflexivity.
Qed.

(* Invariants read only the variables. *)
Lemma clip_eval : forall n s R e, length s = n -> evalD (s ++ R) (tx n n 0 [] [] e) = evalD s e.
Proof.
  intros n s R e Hs. pose proof (tx_eval n 0 [] [] s [] [] R n e Hs eq_refl ltac:(simpl; lia)) as H.
  simpl in H. rewrite app_nil_r in H. rewrite H. reflexivity.
  intros j Hj. lia.
Qed.

Lemma clipP_eval : forall n s R p, length s = n -> evalP (s ++ R) (txP n n 0 [] [] p) = evalP s p.
Proof.
  intros n s R p Hs. pose proof (txP_eval n 0 [] [] s [] [] R n p Hs eq_refl ltac:(simpl; lia)) as H.
  simpl in H. rewrite app_nil_r in H. rewrite H. reflexivity.
  intros j Hj. lia.
Qed.

Lemma find_map' : forall {X Y : Type} (f : Y -> bool) (g : X -> Y) l,
  find f (map g l) = option_map g (find (fun x => f (g x)) l).
Proof. intros X Y f g l. induction l as [|x l IH]; simpl; [reflexivity|]. destruct (f (g x)); [reflexivity | exact IH]. Qed.

Lemma forallb_map' : forall {X Y : Type} (f : Y -> bool) (g : X -> Y) l,
  forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma applyT_len : forall Q t s, length (applyT Q t s) = length s.
Proof.
  intros Q t. unfold applyT. induction t as [|a t IH]; intros s; simpl; [reflexivity|].
  rewrite IH. unfold write. apply upd_len.
Qed.

Lemma drepair_len : forall Q s, length (drepair Q s) = length s.
Proof. intros Q s. unfold drepair. destruct (find _ _); [apply applyT_len | reflexivity]. Qed.

Lemma itr_len : forall Q j s, length (itr j (drepair Q) s) = length s.
Proof. intros Q j. induction j as [|j IH]; intros s; cbn [itr]; [reflexivity|]. rewrite IH. apply drepair_len. Qed.

Lemma papplyT_len : forall P ps t s, length (papplyT P ps t s) = length s.
Proof.
  intros P ps t. unfold papplyT. induction t as [|a t IH]; intros s; simpl; [reflexivity|].
  rewrite IH. unfold pwrite. apply upd_len.
Qed.

Lemma pap_len : forall P k ps s, length (pap P k ps s) = length s.
Proof. intros P k ps s. unfold pap, pevt. destruct (evalP _ _); [apply papplyT_len | reflexivity]. Qed.

Lemma pgov_len : forall P K k ps s, length (pgov P K k ps s) = length s.
Proof. intros P K k ps s. unfold pgov, prepair. rewrite (itr_len (base P)). apply pap_len. Qed.

Definition tgt_ok (n : nat) (t : transform) : bool := forallb (fun a => Nat.ltb (fst a) n) t.

Section JointSem.
  Variable P : pprog.
  Local Notation n := (pn P).
  Hypothesis Hlen : length (phi P) = n.
  Hypothesis HTi : forall iv, In iv (pinv P) -> tgt_ok n (snd iv) = true.

  (* Any joint dprog: its first n bounds are the variables' bounds; its invariants are the
     registry's, read on the variables. *)
  Variable Q : dprog.
  Hypothesis HQlo : forall k, (k < n)%nat -> nth k (dlo Q) 0%Z = nth k (plo P) 0%Z.
  Hypothesis HQhi : forall k, (k < n)%nat -> nth k (dhi Q) 0%Z = nth k (phi P) 0%Z.
  Hypothesis HQinv : dinv Q = map (clipI n) (pinv P).

  Lemma jw_apply : forall t m ex sg pre ps post off s, length s = n -> length ps = m ->
    off = (n + length pre)%nat ->
    (forall j, (j < m)%nat -> nth j ex false = true -> nth j sg 0%Z = nth j ps 0%Z) ->
    tgt_ok n t = true ->
    applyT Q (map (fun a => (fst a, txW n off m ex sg (snd a))) t) (s ++ pre ++ ps ++ post) =
    papplyT P ps t s ++ pre ++ ps ++ post.
  Proof.
    intros t m ex sg pre ps post off. unfold applyT, papplyT.
    induction t as [|[k e] t IH]; intros s Hs Hp Ho Ha Ht; simpl; [reflexivity|].
    unfold tgt_ok in Ht. simpl in Ht. apply andb_true_iff in Ht as [Hk Ht]. apply Nat.ltb_lt in Hk.
    assert (E : write Q (s ++ pre ++ ps ++ post) (k, txW n off m ex sg e) = pwrite P ps s (k, e) ++ pre ++ ps ++ post).
    { unfold write, pwrite. simpl. rewrite HQlo, HQhi by exact Hk.
      assert (V : evalD (s ++ pre ++ ps ++ post) (txW n off m ex sg e) = evalD (s ++ ps) e).
      { unfold txW. destruct (fbW n m e).
        - apply tx_eval; assumption.
        - apply tx_eval; try assumption. intros j _ H. rewrite nth_nil_false in H. discriminate. }
      rewrite V. apply upd_app. lia. }
    rewrite E. apply IH; [unfold pwrite; rewrite upd_len; exact Hs | exact Hp | exact Ho | exact Ha | exact Ht].
  Qed.

  Lemma jevt : forall ev sg pre ps post off s, length s = n -> length ps = length (eprm ev) ->
    off = (n + length pre)%nat ->
    (forall j, (j < length (eprm ev))%nat -> nth j (emask n ev) false = true -> nth j sg 0%Z = nth j ps 0%Z) ->
    tgt_ok n (eeff ev) = true ->
    evt Q (jev n off ev sg) (s ++ pre ++ ps ++ post) = pevt P ev ps s ++ pre ++ ps ++ post.
  Proof.
    intros ev sg pre ps post off s Hs Hp Ho Ha Ht. unfold evt, jev, pevt. simpl.
    rewrite (txP_eval n (length (eprm ev)) (emask n ev) sg s pre ps post off) by assumption.
    destruct (evalP (s ++ ps) (eguard ev)); [|reflexivity].
    apply jw_apply; assumption.
  Qed.

  Lemma jw_clip : forall t s R, length s = n -> tgt_ok n t = true ->
    applyT Q (map (fun a => (fst a, tx n n 0 [] [] (snd a))) t) (s ++ R) = applyT (base P) t s ++ R.
  Proof.
    unfold applyT. induction t as [|[k e] t IH]; intros s R Hs Ht; simpl; [reflexivity|].
    unfold tgt_ok in Ht. simpl in Ht. apply andb_true_iff in Ht as [Hk Ht]. apply Nat.ltb_lt in Hk.
    assert (E : write Q (s ++ R) (k, tx n n 0 [] [] e) = write (base P) s (k, e) ++ R).
    { unfold write. simpl. rewrite HQlo, HQhi by exact Hk. rewrite clip_eval by exact Hs. apply upd_app. lia. }
    rewrite E. apply IH; [unfold write; rewrite upd_len; exact Hs | exact Ht].
  Qed.

  Lemma jvalid : forall s R, length s = n -> dvalid Q (s ++ R) = pvalid P s.
  Proof.
    intros s R Hs. unfold dvalid, pvalid. rewrite HQinv, forallb_map'. simpl.
    apply forallb_ext_in. intros iv _. unfold clipI. simpl. apply clipP_eval. exact Hs.
  Qed.

  Lemma jrepair : forall s R, length s = n -> drepair Q (s ++ R) = prepair P s ++ R.
  Proof.
    intros s R Hs. unfold prepair, drepair. rewrite HQinv, find_map'. simpl.
    rewrite (find_ext_in (fun x => negb (evalP (s ++ R) (fst (clipI n x)))) (fun iv => negb (evalP s (fst iv)))).
    - destruct (find (fun iv => negb (evalP s (fst iv))) (pinv P)) as [iv|] eqn:E; simpl; [|reflexivity].
      apply find_some in E. destruct E as [Hiv _]. unfold clipI. simpl.
      apply jw_clip; [exact Hs | exact (HTi iv Hiv)].
    - intros iv _. unfold clipI. simpl. rewrite clipP_eval by exact Hs. reflexivity.
  Qed.

  Lemma jitr : forall K s R, length s = n -> itr K (drepair Q) (s ++ R) = itr K (prepair P) s ++ R.
  Proof.
    induction K as [|K IH]; intros s R Hs; cbn [itr]; [reflexivity|].
    rewrite jrepair by exact Hs. apply IH. unfold prepair. rewrite drepair_len. exact Hs.
  Qed.
End JointSem.

(* ============================================================================================ *)
(* The fragment check.                                                                          *)
(* ============================================================================================ *)

Definition rng (lo hi : Z) : list Z := map (fun i => lo + Z.of_nat i)%Z (seq 0 (Z.to_nat (hi - lo + 1))).

(* The values the check gives to the parameters of kind k: every value of an exact parameter's
   range; one value (its lower bound) for any other parameter, which stays a coordinate. *)
Definition sigs (P : pprog) (k : nat) : list (list Z) :=
  tupL (map (fun j => if nth j (mask P k) false
                      then rng (nth j (map fst (prmOf P k)) 0%Z) (nth j (map snd (prmOf P k)) 0%Z)
                      else [nth j (map fst (prmOf P k)) 0%Z]) (seq 0 (nprm P k))).

(* Exact parameters have ranges of width at most 2 (gam + mu). *)
Definition exok (P : pprog) (gam mu : Z) (k : nat) : bool :=
  forallb (fun j => implb (nth j (mask P k) false)
    (Z.leb (nth j (map snd (prmOf P k)) 0%Z - nth j (map fst (prmOf P k)) 0%Z) (2 * (gam + mu))))
    (seq 0 (nprm P k)).

(* The parameterized difference fragment: the variables' registry is in the difference fragment;
   every event writes only variables, its exact parameters are narrow, and for every value of the
   exact parameters every single and every pair of events, placed in the joint state, is in the
   difference fragment (dfrag), parameter bounds among the anchors. *)
Definition pfrag (P : pprog) (A : list Z) (gam mu : Z) : bool :=
  dfrag (base P) A gam mu &&
  forallb (fun k => tgt_ok (pn P) (eeff (evOf P k)) && exok P gam mu k && bnd_ok (jb P [k]) A &&
     forallb (fun sg => dfrag (joint P [(k, sg)]) A gam mu) (sigs P k)) (seq 0 (nk P)) &&
  forallb (fun k1 => forallb (fun k2 => bnd_ok (jb P [k1; k2]) A &&
     forallb (fun sg1 => forallb (fun sg2 => dfrag (joint P [(k1, sg1); (k2, sg2)]) A gam mu) (sigs P k2))
       (sigs P k1)) (seq 0 (nk P))) (seq 0 (nk P)).

Lemma forallb_seq : forall (f : nat -> bool) m, forallb f (seq 0 m) = true -> forall k, (k < m)%nat -> f k = true.
Proof. intros f m H k Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Section FragParts.
  Variable P : pprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : pfrag P A gam mu = true.

  Lemma pfrag_base : dfrag (base P) A gam mu = true.
  Proof. unfold pfrag in HF. apply andb_true_iff in HF as [H _]. apply andb_true_iff in H as [H _]. exact H. Qed.

  Lemma pfrag_one : forall k, (k < nk P)%nat ->
    tgt_ok (pn P) (eeff (evOf P k)) = true /\ exok P gam mu k = true /\ bnd_ok (jb P [k]) A = true /\
    forall sg, In sg (sigs P k) -> dfrag (joint P [(k, sg)]) A gam mu = true.
  Proof.
    intros k Hk. unfold pfrag in HF. apply andb_true_iff in HF as [H _]. apply andb_true_iff in H as [_ H].
    pose proof (forallb_seq _ _ H k Hk) as H1. simpl in H1.
    apply andb_true_iff in H1 as [H1 H4]. apply andb_true_iff in H1 as [H1 H3]. apply andb_true_iff in H1 as [H1 H2].
    rewrite forallb_forall in H4. split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]].
  Qed.

  Lemma pfrag_two : forall k1 k2, (k1 < nk P)%nat -> (k2 < nk P)%nat ->
    bnd_ok (jb P [k1; k2]) A = true /\
    forall sg1 sg2, In sg1 (sigs P k1) -> In sg2 (sigs P k2) -> dfrag (joint P [(k1, sg1); (k2, sg2)]) A gam mu = true.
  Proof.
    intros k1 k2 H1 H2. unfold pfrag in HF. apply andb_true_iff in HF as [_ H].
    pose proof (forallb_seq _ _ H k1 H1) as H3. simpl in H3. pose proof (forallb_seq _ _ H3 k2 H2) as H4. simpl in H4.
    apply andb_true_iff in H4 as [Hb H4]. split; [exact Hb|]. intros sg1 sg2 S1 S2.
    rewrite forallb_forall in H4. specialize (H4 sg1 S1). rewrite forallb_forall in H4. exact (H4 sg2 S2).
  Qed.

  Lemma base_parts : length (phi P) = pn P /\ (0 <= gam)%Z /\ (0 <= mu)%Z /\
    forall iv, In iv (pinv P) -> tgt_ok (pn P) (snd iv) = true.
  Proof.
    pose proof pfrag_base as H. destruct (frag_parts (base P) A gam mu H) as [Hb [G [M [_ Hi]]]].
    destruct (bnd_ok_parts (base P) A Hb) as [L _]. split; [exact L | split; [exact G | split; [exact M|]]].
    intros iv Hiv. destruct (Hi iv Hiv) as [_ Ht]. destruct (tok_parts (base P) A mu _ Ht) as [Ha _].
    unfold tgt_ok. rewrite forallb_forall in Ha |- *. intros a Hin. specialize (Ha a Hin).
    unfold aok in Ha. apply andb_true_iff in Ha as [Ha _]. exact Ha.
  Qed.
End FragParts.

(* ---- The generic tuple enumeration. ---- *)

Lemma tupL_spec : forall Ds l, In l (tupL Ds) <->
  length l = length Ds /\ forall i, (i < length Ds)%nat -> In (nth i l 0%Z) (nth i Ds []).
Proof.
  induction Ds as [|D Ds IH]; intros l; simpl.
  - split.
    + intros [<- | []]. split; [reflexivity | intros i Hi; lia].
    + intros [Hl _]. destruct l; [left; reflexivity | discriminate].
  - rewrite in_flat_map. split.
    + intros [x [Hx Hl]]. apply in_map_iff in Hl. destruct Hl as [t [<- Ht]]. apply IH in Ht. destruct Ht as [Ht1 Ht2].
      split; [simpl; lia|]. intros [|i] Hi; simpl; [exact Hx | apply Ht2; lia].
    + intros [Hl Hi]. destruct l as [|x t]; [discriminate|]. exists x. split; [exact (Hi 0%nat ltac:(lia))|].
      apply in_map. apply IH. split; [simpl in Hl; lia|]. intros i Hi'. exact (Hi (S i) ltac:(lia)).
Qed.

Lemma nth_map_seq : forall {X : Type} (f : nat -> X) a m i d, (i < m)%nat -> nth i (map f (seq a m)) d = f (a + i)%nat.
Proof.
  intros X f a m. revert a. induction m as [|m IH]; intros a i d Hi; [lia|].
  destruct i as [|i]; simpl; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma rng_in : forall lo hi v, (lo <= v <= hi)%Z -> In v (rng lo hi).
Proof.
  intros lo hi v H. unfold rng. apply in_map_iff. exists (Z.to_nat (v - lo)). split; [rewrite Z2Nat.id by lia; lia|].
  apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.

(* The representative values of the exact parameters of an argument list. *)
Definition hat (P : pprog) (k : nat) (ps : list Z) : list Z :=
  map (fun j => if nth j (mask P k) false then nth j ps 0%Z else nth j (map fst (prmOf P k)) 0%Z) (seq 0 (nprm P k)).

Lemma hat_sigs : forall P k ps, PArgs P k ps -> In (hat P k ps) (sigs P k).
Proof.
  intros P k ps [Hl Hb]. unfold sigs, hat. apply tupL_spec. rewrite !lenM, !lenS. split; [reflexivity|].
  intros i Hi. rewrite !nth_map_seq by exact Hi. simpl.
  destruct (nth i (mask P k) false); [|left; reflexivity].
  apply rng_in. rewrite lenM in Hb. apply Hb. unfold nprm in Hi. exact Hi.
Qed.

(* Agreement on the exact parameters. *)
Definition agree (P : pprog) (k : nat) (a b : list Z) : Prop :=
  forall j, (j < nprm P k)%nat -> nth j (mask P k) false = true -> nth j a 0%Z = nth j b 0%Z.

Lemma hat_agree : forall P k ps, agree P k (hat P k ps) ps.
Proof. intros P k ps j Hj Hm. unfold hat. rewrite nth_map_seq by exact Hj. simpl. rewrite Hm. reflexivity. Qed.

Lemma agree_trans : forall P k a b c, agree P k a b -> agree P k b c -> agree P k a c.
Proof. intros P k a b c H1 H2 j Hj Hm. rewrite (H1 j Hj Hm). exact (H2 j Hj Hm). Qed.

Lemma agree_sym : forall P k a b, agree P k a b -> agree P k b a.
Proof. intros P k a b H j Hj Hm. symmetry. exact (H j Hj Hm). Qed.

(* ---- Exactness: related states agree on a coordinate whose range is narrow. ---- *)

Theorem exact_eq : forall Q A W J J' i, bnd_ok Q A = true -> RelS W A J J' -> InBox Q J -> InBox Q J' ->
  (i < nv Q)%nat -> (nth i (dhi Q) 0 - nth i (dlo Q) 0 <= 2 * W)%Z -> nth i J 0%Z = nth i J' 0%Z.
Proof.
  intros Q A W J J' i Hb [Hl HR] [L1 B1] [L2 B2] Hi Hw.
  destruct (bnd_ok_parts Q A Hb) as [_ Hbd]. destruct (Hbd i Hi) as [_ [Hlo Hhi]].
  pose proof (B1 i Hi). pose proof (B2 i Hi).
  assert (Hx : In (nth i J 0%Z, nth i J' 0%Z) (combine J J' ++ anc A)) by (apply in_or_app; left; apply in_combine_nth; lia).
  assert (Ha : In (nth i (dlo Q) 0%Z, nth i (dlo Q) 0%Z) (combine J J' ++ anc A)) by (apply in_or_app; right; apply in_anc; exact Hlo).
  assert (Hh : In (nth i (dhi Q) 0%Z, nth i (dhi Q) 0%Z) (combine J J' ++ anc A)) by (apply in_or_app; right; apply in_anc; exact Hhi).
  pose proof (HR _ _ Hx Ha) as N1. pose proof (HR _ _ Hx Hh) as N2. simpl in N1, N2. unfold near in N1, N2. lia.
Qed.

(* ---- Splitting a joint state. ---- *)

Lemma firstn_app_len : forall (l r : list Z), firstn (length l) (l ++ r) = l.
Proof. induction l as [|x l IH]; intros r; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma skipn_app_len : forall (l r : list Z), skipn (length l) (l ++ r) = r.
Proof. induction l as [|x l IH]; intros r; simpl; [reflexivity | exact (IH r)]. Qed.

Lemma bx_app : forall l1 l2 h1 h2 s1 s2, length s1 = length l1 -> length l1 = length h1 ->
  (bx (l1 ++ l2) (h1 ++ h2) (s1 ++ s2) <-> bx l1 h1 s1 /\ bx l2 h2 s2).
Proof.
  intros l1 l2 h1 h2 s1 s2 L1 L2. unfold bx. rewrite !lenA. split.
  - intros [Hl Hb]. split; split; try lia.
    + intros i Hi. pose proof (Hb i ltac:(lia)) as H. rewrite !app_nth1 in H by lia. exact H.
    + intros i Hi. pose proof (Hb (length l1 + i)%nat ltac:(lia)) as H.
      assert (E1 : nth (length l1 + i) (s1 ++ s2) 0%Z = nth i s2 0%Z) by (rewrite <- L1; apply nth_app_r).
      assert (E2 : nth (length l1 + i) (h1 ++ h2) 0%Z = nth i h2 0%Z) by (rewrite L2; apply nth_app_r).
      rewrite nth_app_r, E1, E2 in H. exact H.
  - intros [[Hl1 Hb1] [Hl2 Hb2]]. split; [lia|]. intros i Hi.
    destruct (Nat.lt_ge_cases i (length l1)) as [H | H].
    + rewrite !app_nth1 by lia. exact (Hb1 i H).
    + replace i with (length l1 + (i - length l1))%nat by lia.
      assert (E1 : nth (length l1 + (i - length l1)) (s1 ++ s2) 0%Z = nth (i - length l1) s2 0%Z) by (rewrite <- L1; apply nth_app_r).
      assert (E2 : nth (length l1 + (i - length l1)) (h1 ++ h2) 0%Z = nth (i - length l1) h2 0%Z) by (rewrite L2; apply nth_app_r).
      rewrite nth_app_r, E1, E2. apply Hb2. lia.
Qed.

(* ---- The joint registry of one and of two events. ---- *)

Lemma jlo_var : forall P ks k, (k < pn P)%nat -> nth k (jlo P ks) 0%Z = nth k (plo P) 0%Z.
Proof. intros P ks k H. unfold jlo. apply app_nth1. exact H. Qed.

Lemma jhi_var : forall P ks k, length (phi P) = pn P -> (k < pn P)%nat -> nth k (jhi P ks) 0%Z = nth k (phi P) 0%Z.
Proof. intros P ks k L H. unfold jhi. apply app_nth1. lia. Qed.

Lemma jlo_p1 : forall P k1 ks j, (j < nprm P k1)%nat ->
  nth (pn P + j) (jlo P (k1 :: ks)) 0%Z = nth j (map fst (prmOf P k1)) 0%Z.
Proof. intros P k1 ks j H. unfold jlo. simpl. unfold pn. rewrite nth_app_r. apply app_nth1. rewrite lenM. exact H. Qed.

Lemma jhi_p1 : forall P k1 ks j, length (phi P) = pn P -> (j < nprm P k1)%nat ->
  nth (pn P + j) (jhi P (k1 :: ks)) 0%Z = nth j (map snd (prmOf P k1)) 0%Z.
Proof. intros P k1 ks j L H. unfold jhi. simpl. rewrite <- L, nth_app_r. apply app_nth1. rewrite lenM. exact H. Qed.

Lemma jlo_p2 : forall P k1 k2 j, (j < nprm P k2)%nat ->
  nth (pn P + nprm P k1 + j) (jlo P [k1; k2]) 0%Z = nth j (map fst (prmOf P k2)) 0%Z.
Proof.
  intros P k1 k2 j H. unfold jlo. simpl. unfold pn. rewrite <- Nat.add_assoc, nth_app_r.
  unfold nprm. rewrite <- (lenM fst (prmOf P k1)), nth_app_r. apply app_nth1. rewrite lenM. exact H.
Qed.

Lemma jhi_p2 : forall P k1 k2 j, length (phi P) = pn P -> (j < nprm P k2)%nat ->
  nth (pn P + nprm P k1 + j) (jhi P [k1; k2]) 0%Z = nth j (map snd (prmOf P k2)) 0%Z.
Proof.
  intros P k1 k2 j L H. unfold jhi. simpl. rewrite <- L, <- Nat.add_assoc, nth_app_r.
  unfold nprm. rewrite <- (lenM snd (prmOf P k1)), nth_app_r. apply app_nth1. rewrite lenM. exact H.
Qed.

Lemma jlen : forall P ks, length (jlo P ks) = (pn P + fold_right Nat.add 0 (map (nprm P) ks))%nat.
Proof.
  intros P ks. unfold jlo, pn. rewrite lenA. f_equal. induction ks as [|k ks IH]; simpl; [reflexivity|].
  rewrite lenA, lenM, IH. reflexivity.
Qed.

Section Joint2.
  Variable P : pprog.
  Local Notation n := (pn P).
  Hypothesis Hlen : length (phi P) = n.
  Hypothesis HTi : forall iv, In iv (pinv P) -> tgt_ok n (snd iv) = true.

  Section Two.
    Variables k1 k2 : nat.
    Variables sg1 sg2 : list Z.
    Hypothesis T1 : tgt_ok n (eeff (evOf P k1)) = true.
    Hypothesis T2 : tgt_ok n (eeff (evOf P k2)) = true.
    Local Notation Q := (joint P [(k1, sg1); (k2, sg2)]).

    Lemma jgov2a : forall K s ps1 ps2, length s = n -> length ps1 = nprm P k1 -> agree P k1 sg1 ps1 ->
      dgov Q K 0 (s ++ ps1 ++ ps2) = pgov P K k1 ps1 s ++ ps1 ++ ps2.
    Proof.
      intros K s ps1 ps2 Hs H1 A1. unfold dgov, pgov.
      change (dap Q 0 (s ++ ps1 ++ ps2)) with (evt Q (jev n n (evOf P k1) sg1) (s ++ [] ++ ps1 ++ ps2)).
      rewrite (jevt P Hlen Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk)
                 (evOf P k1) sg1 [] ps1 ps2 n s Hs H1 ltac:(simpl; lia) A1 T1).
      simpl. apply (jitr P Hlen HTi Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk) eq_refl).
      rewrite pap_len. exact Hs.
    Qed.

    Lemma jgov2b : forall K s ps1 ps2, length s = n -> length ps1 = nprm P k1 -> length ps2 = nprm P k2 ->
      agree P k2 sg2 ps2 -> dgov Q K 1 (s ++ ps1 ++ ps2) = pgov P K k2 ps2 s ++ ps1 ++ ps2.
    Proof.
      intros K s ps1 ps2 Hs H1 H2 A2. unfold dgov, pgov.
      change (dap Q 1 (s ++ ps1 ++ ps2)) with (evt Q (jev n (n + nprm P k1) (evOf P k2) sg2) (s ++ ps1 ++ ps2)).
      replace (s ++ ps1 ++ ps2) with (s ++ ps1 ++ ps2 ++ []) by (rewrite app_nil_r; reflexivity).
      rewrite (jevt P Hlen Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk)
                 (evOf P k2) sg2 ps1 ps2 [] (n + nprm P k1) s Hs H2 ltac:(lia) A2 T2).
      rewrite app_nil_r. apply (jitr P Hlen HTi Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk) eq_refl).
      rewrite pap_len. exact Hs.
    Qed.

    (* CC1 of the joint registry at s ++ ps1 ++ ps2 is CC1 of the two events with arguments ps1, ps2. *)
    Theorem jcc1 : forall K s ps1 ps2, length s = n -> length ps1 = nprm P k1 -> length ps2 = nprm P k2 ->
      agree P k1 sg1 ps1 -> agree P k2 sg2 ps2 ->
      (dgov Q K 1 (dgov Q K 0 (s ++ ps1 ++ ps2)) = dgov Q K 0 (dgov Q K 1 (s ++ ps1 ++ ps2)) <->
       pgov P K k2 ps2 (pgov P K k1 ps1 s) = pgov P K k1 ps1 (pgov P K k2 ps2 s)).
    Proof.
      intros K s ps1 ps2 Hs H1 H2 A1 A2.
      rewrite (jgov2a K s ps1 ps2 Hs H1 A1), (jgov2b K s ps1 ps2 Hs H1 H2 A2).
      rewrite (jgov2b K _ ps1 ps2 ltac:(rewrite pgov_len; exact Hs) H1 H2 A2).
      rewrite (jgov2a K _ ps1 ps2 ltac:(rewrite pgov_len; exact Hs) H1 A1).
      split; intros E; [apply app_inv_tail in E; exact E | rewrite E; reflexivity].
    Qed.

    Lemma jvalid2 : forall s R, length s = n -> dvalid Q (s ++ R) = pvalid P s.
    Proof. intros s R Hs. apply (jvalid P Q eq_refl s R Hs). Qed.
  End Two.

  Section One.
    Variable k : nat.
    Variable sg : list Z.
    Hypothesis T : tgt_ok n (eeff (evOf P k)) = true.
    Local Notation Q := (joint P [(k, sg)]).

    Lemma jgov1 : forall K s ps, length s = n -> length ps = nprm P k -> agree P k sg ps ->
      dgov Q K 0 (s ++ ps) = pgov P K k ps s ++ ps.
    Proof.
      intros K s ps Hs H1 A1. unfold dgov, pgov.
      change (dap Q 0 (s ++ ps)) with (evt Q (jev n n (evOf P k) sg) (s ++ [] ++ ps)).
      replace (s ++ [] ++ ps) with (s ++ [] ++ ps ++ []) by (rewrite app_nil_r; reflexivity).
      rewrite (jevt P Hlen Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk)
                 (evOf P k) sg [] ps [] n s Hs H1 ltac:(simpl; lia) A1 T).
      simpl. rewrite app_nil_r.
      apply (jitr P Hlen HTi Q (fun k Hk => jlo_var P _ k Hk) (fun k Hk => jhi_var P _ k Hlen Hk) eq_refl).
      rewrite pap_len. exact Hs.
    Qed.

    Theorem jidem : forall K s ps, length s = n -> length ps = nprm P k -> agree P k sg ps ->
      (dgov Q K 0 (dgov Q K 0 (s ++ ps)) = dgov Q K 0 (s ++ ps) <->
       pgov P K k ps (pgov P K k ps s) = pgov P K k ps s).
    Proof.
      intros K s ps Hs H1 A1. rewrite (jgov1 K s ps Hs H1 A1).
      rewrite (jgov1 K _ ps ltac:(rewrite pgov_len; exact Hs) H1 A1).
      split; intros E; [apply app_inv_tail in E; exact E | rewrite E; reflexivity].
    Qed.
  End One.
End Joint2.

(* ============================================================================================ *)
(* The conditions gsm checks, over the declared ranges and over the representatives.             *)
(* ============================================================================================ *)

(* Splitting a joint state into the variables and the arguments of one or two events. *)
Definition sv (P : pprog) (J : list Z) : list Z := firstn (pn P) J.
Definition sa (P : pprog) (J : list Z) : list Z := skipn (pn P) J.
Definition sa1 (P : pprog) (k1 : nat) (J : list Z) : list Z := firstn (nprm P k1) (skipn (pn P) J).
Definition sa2 (P : pprog) (k1 : nat) (J : list Z) : list Z := skipn (nprm P k1) (skipn (pn P) J).

(* Repair within K steps from every state in range (the invariants carry no parameters). *)
Definition PTermBox (P : pprog) (K : nat) : Prop := DTermBox (base P) K.
Definition PTermRep (P : pprog) (A : list Z) (W : Z) (K : nat) : Prop := DTermRep (base P) A W K.

(* CC1 for the pairs of I at every valid state in range and all arguments in range. *)
Definition PCC1VBox (P : pprog) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, PInBox P s -> pvalid P s = true -> forall k1 k2, (k1 < nk P)%nat -> (k2 < nk P)%nat -> I k1 k2 ->
  forall ps1 ps2, PArgs P k1 ps1 -> PArgs P k2 ps2 ->
    pgov P K k2 ps2 (pgov P K k1 ps1 s) = pgov P K k1 ps1 (pgov P K k2 ps2 s).

(* The same over the representatives of the joint box of k1 and k2. *)
Definition PCC1VRep (P : pprog) (A : list Z) (W : Z) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall k1 k2, (k1 < nk P)%nat -> (k2 < nk P)%nat -> I k1 k2 ->
  forall J, In J (RepS (jb P [k1; k2]) A W) -> pvalid P (sv P J) = true ->
    pgov P K k2 (sa2 P k1 J) (pgov P K k1 (sa1 P k1 J) (sv P J)) =
    pgov P K k1 (sa1 P k1 J) (pgov P K k2 (sa2 P k1 J) (sv P J)).

(* Idempotence of kind k (the same arguments twice) at every valid state. *)
Definition PIdemVBox (P : pprog) (K k : nat) : Prop :=
  forall s ps, PInBox P s -> PArgs P k ps -> pvalid P s = true ->
    pgov P K k ps (pgov P K k ps s) = pgov P K k ps s.

Definition PIdemVRep (P : pprog) (A : list Z) (W : Z) (K k : nat) : Prop :=
  forall J, In J (RepS (jb P [k]) A W) -> pvalid P (sv P J) = true ->
    pgov P K k (sa P J) (pgov P K k (sa P J) (sv P J)) = pgov P K k (sa P J) (sv P J).

Lemma split2 : forall n (J : list Z), J = firstn n J ++ skipn n J.
Proof. intros n J. symmetry. apply firstn_skipn. Qed.

Lemma split3 : forall n m (J : list Z), J = firstn n J ++ firstn m (skipn n J) ++ skipn m (skipn n J).
Proof. intros n m J. rewrite !firstn_skipn. reflexivity. Qed.

Section Cutoff.
  Variable P : pprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : pfrag P A gam mu = true.

  Local Notation n := (pn P).

  Lemma Hlen : length (phi P) = n.
  Proof. apply (base_parts P A gam mu HF). Qed.
  Lemma G0 : (0 <= gam)%Z.
  Proof. apply (base_parts P A gam mu HF). Qed.
  Lemma M0 : (0 <= mu)%Z.
  Proof. apply (base_parts P A gam mu HF). Qed.
  Lemma HTi : forall iv, In iv (pinv P) -> tgt_ok n (snd iv) = true.
  Proof. apply (base_parts P A gam mu HF). Qed.

  Lemma box2 : forall k1 k2 s ps1 ps2, length s = n -> length ps1 = nprm P k1 ->
    (InBox (jb P [k1; k2]) (s ++ ps1 ++ ps2) <-> PInBox P s /\ PArgs P k1 ps1 /\ PArgs P k2 ps2).
  Proof.
    intros k1 k2 s ps1 ps2 Hs H1. rewrite inbox_bx. unfold jb, jlo, jhi, PInBox, PArgs. simpl. rewrite !app_nil_r.
    rewrite inbox_bx. simpl. rewrite bx_app by (pose proof Hlen; unfold pn in *; lia).
    rewrite bx_app by (rewrite ?lenM; unfold nprm in H1; lia). reflexivity.
  Qed.

  Lemma box1 : forall k s ps, length s = n -> (InBox (jb P [k]) (s ++ ps) <-> PInBox P s /\ PArgs P k ps).
  Proof.
    intros k s ps Hs. rewrite inbox_bx. unfold jb, jlo, jhi, PInBox, PArgs. simpl. rewrite !app_nil_r.
    rewrite inbox_bx. simpl. rewrite bx_app by (pose proof Hlen; unfold pn in *; lia). reflexivity.
  Qed.

  Lemma exok_parts : forall k j, (k < nk P)%nat -> (j < nprm P k)%nat -> nth j (mask P k) false = true ->
    (nth j (map snd (prmOf P k)) 0 - nth j (map fst (prmOf P k)) 0 <= 2 * (gam + mu))%Z.
  Proof.
    intros k j Hk Hj Hm. destruct (pfrag_one P A gam mu HF k Hk) as [_ [He _]]. unfold exok in He.
    pose proof (forallb_seq _ _ He j Hj) as H. simpl in H. rewrite Hm in H. simpl in H. apply Z.leb_le. exact H.
  Qed.

  Lemma nth_mid : forall (s ps1 ps2 : list Z) j, length s = n -> (j < length ps1)%nat ->
    nth (n + j) (s ++ ps1 ++ ps2) 0%Z = nth j ps1 0%Z.
  Proof. intros s ps1 ps2 j Hs Hj. rewrite <- Hs, nth_app_r. apply app_nth1. exact Hj. Qed.

  Lemma nth_end : forall (s ps1 ps2 : list Z) m1 j, length s = n -> length ps1 = m1 ->
    nth (n + m1 + j) (s ++ ps1 ++ ps2) 0%Z = nth j ps2 0%Z.
  Proof. intros s ps1 ps2 m1 j Hs H1. rewrite <- Hs, <- H1, <- Nat.add_assoc, !nth_app_r. reflexivity. Qed.

  (* CC1 for I at every valid state, all arguments: threshold gam + 4 (K + 1) mu. The joint state has
     n + m1 + m2 coordinates; the representatives are the joint states with every coordinate
     within (n + m1 + m2)(W + 1) of an anchor. *)
  Theorem pcc1v_abs : forall K W I, (wcc1 gam mu K <= W)%Z -> (PCC1VBox P K I <-> PCC1VRep P A W K I).
  Proof.
    intros K W I Hw. pose proof G0 as G. pose proof M0 as M. unfold wcc1 in Hw.
    assert (HW : (0 <= W)%Z) by nia.
    split.
    - intros H k1 k2 H1 H2 HI J HJ Hv.
      destruct (pfrag_two P A gam mu HF k1 k2 H1 H2) as [Hb _].
      apply (RepS_spec (jb P [k1; k2]) A W J Hb HW) in HJ. destruct HJ as [Hbox _].
      assert (LJ : length J = (n + nprm P k1 + nprm P k2)%nat).
      { destruct Hbox as [L _]. unfold nv in L. rewrite L. unfold jb. simpl dlo. rewrite jlen. simpl. lia. }
      rewrite (split3 n (nprm P k1) J) in Hbox.
      apply box2 in Hbox; [| unfold sv; rewrite firstn_length; lia | rewrite firstn_length, skipn_length; lia].
      destruct Hbox as [Hs [Hp1 Hp2]]. apply H; assumption.
    - intros H s Hs Hv k1 k2 H1 H2 HI ps1 ps2 Hp1 Hp2.
      destruct (pfrag_one P A gam mu HF k1 H1) as [T1 _]. destruct (pfrag_one P A gam mu HF k2 H2) as [T2 _].
      destruct (pfrag_two P A gam mu HF k1 k2 H1 H2) as [Hb HD].
      set (Q := joint P [(k1, hat P k1 ps1); (k2, hat P k2 ps2)]).
      assert (HQ : dfrag Q A gam mu = true) by (apply HD; apply hat_sigs; assumption).
      assert (Ls : length s = n) by (destruct Hs as [L _]; exact L).
      assert (L1 : length ps1 = nprm P k1) by (destruct Hp1 as [L _]; rewrite lenM in L; exact L).
      assert (L2 : length ps2 = nprm P k2) by (destruct Hp2 as [L _]; rewrite lenM in L; exact L).
      set (J := s ++ ps1 ++ ps2).
      assert (HJ : InBox Q J) by (change (InBox (jb P [k1; k2]) J); apply box2; auto).
      destruct (compress_d Q A W J Hb HW HJ) as [J' [HJ' R]].
      assert (HJ'b : InBox Q J') by (apply (rep_box Q A gam mu HQ W J' HW HJ')).
      assert (LJ' : length J' = (n + nprm P k1 + nprm P k2)%nat).
      { destruct HJ'b as [L _]. unfold nv in L. rewrite L. simpl dlo. rewrite jlen. simpl. lia. }
      set (s' := sv P J'). set (q1 := sa1 P k1 J'). set (q2 := sa2 P k1 J').
      assert (EJ : J' = s' ++ q1 ++ q2) by apply split3.
      assert (Ls' : length s' = n) by (unfold s', sv; rewrite firstn_length; lia).
      assert (Lq1 : length q1 = nprm P k1) by (unfold q1, sa1; rewrite firstn_length, skipn_length; lia).
      assert (Lq2 : length q2 = nprm P k2) by (unfold q2, sa2; rewrite !skipn_length; lia).
      assert (LJn : length J = nv Q) by (destruct HJ as [L _]; exact L).
      (* The exact parameters agree. *)
      assert (Ag1 : agree P k1 (hat P k1 ps1) q1).
      { apply (agree_trans P k1 _ ps1); [apply hat_agree|]. intros j Hj Hm.
        rewrite <- (nth_mid s ps1 ps2 j Ls ltac:(lia)), <- (nth_mid s' q1 q2 j Ls' ltac:(lia)). fold J. rewrite <- EJ.
        apply (exact_eq Q A W J J' (n + j) Hb R HJ HJ'b).
        - unfold nv. simpl dlo. rewrite jlen. simpl. lia.
        - simpl dlo. simpl dhi. change (map fst [(k1, hat P k1 ps1); (k2, hat P k2 ps2)]) with [k1; k2].
          rewrite jlo_p1, jhi_p1 by (try apply Hlen; exact Hj). pose proof (exok_parts k1 j H1 Hj Hm). nia. }
      assert (Ag2 : agree P k2 (hat P k2 ps2) q2).
      { apply (agree_trans P k2 _ ps2); [apply hat_agree|]. intros j Hj Hm.
        rewrite <- (nth_end s ps1 ps2 (nprm P k1) j Ls L1), <- (nth_end s' q1 q2 (nprm P k1) j Ls' Lq1). fold J. rewrite <- EJ.
        apply (exact_eq Q A W J J' (n + nprm P k1 + j) Hb R HJ HJ'b).
        - unfold nv. simpl dlo. rewrite jlen. simpl. lia.
        - simpl dlo. simpl dhi. change (map fst [(k1, hat P k1 ps1); (k2, hat P k2 ps2)]) with [k1; k2].
          rewrite jlo_p2, jhi_p2 by (try apply Hlen; exact Hj). pose proof (exok_parts k2 j H2 Hj Hm). nia. }
      (* Validity transfers. *)
      assert (Hv' : pvalid P s' = true).
      { assert (E1 : dvalid Q J' = pvalid P s') by (rewrite EJ; unfold Q; apply jvalid2; exact Ls').
        assert (E2 : dvalid Q J = pvalid P s) by (unfold J, Q; apply jvalid2; exact Ls).
        rewrite <- E1, <- (valid_pair Q A gam mu HQ W J J' R LJn ltac:(nia)), E2. exact Hv. }
      pose proof (H k1 k2 H1 H2 HI J' HJ' Hv') as C'. fold s' q1 q2 in C'.
      apply (jcc1 P Hlen HTi k1 k2 _ _ T1 T2 K s' q1 q2 Ls' Lq1 Lq2 Ag1 Ag2) in C'. rewrite <- EJ in C'.
      apply (jcc1 P Hlen HTi k1 k2 _ _ T1 T2 K s ps1 ps2 Ls L1 L2
               (hat_agree P k1 ps1) (hat_agree P k2 ps2)).
      fold J. apply (cc1_pair Q A gam mu HQ K 0 1 W J J' R LJn Hw). exact C'.
  Qed.

  (* Idempotence at every valid state, all arguments: threshold gam + 3 (K + 1) mu, the joint state
     with n + m coordinates. *)
  Theorem pidemv_abs : forall K k W, (k < nk P)%nat -> (widem gam mu K <= W)%Z ->
    (PIdemVBox P K k <-> PIdemVRep P A W K k).
  Proof.
    intros K k W Hk Hw. pose proof G0 as G. pose proof M0 as M. unfold widem in Hw.
    assert (HW : (0 <= W)%Z) by nia.
    destruct (pfrag_one P A gam mu HF k Hk) as [T [_ [Hb HD]]].
    split.
    - intros H J HJ Hv.
      apply (RepS_spec (jb P [k]) A W J Hb HW) in HJ. destruct HJ as [Hbox _].
      assert (LJ : length J = (n + nprm P k)%nat).
      { destruct Hbox as [L _]. unfold nv in L. rewrite L. unfold jb. simpl dlo. rewrite jlen. simpl. lia. }
      rewrite (split2 n J) in Hbox. apply box1 in Hbox; [| rewrite firstn_length; lia].
      destruct Hbox as [Hs Hp]. apply H; assumption.
    - intros H s ps Hs Hp Hv.
      set (Q := joint P [(k, hat P k ps)]).
      assert (HQ : dfrag Q A gam mu = true) by (apply HD; apply hat_sigs; assumption).
      assert (Ls : length s = n) by (destruct Hs as [L _]; exact L).
      assert (L1 : length ps = nprm P k) by (destruct Hp as [L _]; rewrite lenM in L; exact L).
      set (J := s ++ ps).
      assert (HJ : InBox Q J) by (change (InBox (jb P [k]) J); apply box1; auto).
      destruct (compress_d Q A W J Hb HW HJ) as [J' [HJ' R]].
      assert (HJ'b : InBox Q J') by (apply (rep_box Q A gam mu HQ W J' HW HJ')).
      assert (LJ' : length J' = (n + nprm P k)%nat).
      { destruct HJ'b as [L _]. unfold nv in L. rewrite L. simpl dlo. rewrite jlen. simpl. lia. }
      set (s' := sv P J'). set (q := sa P J').
      assert (EJ : J' = s' ++ q) by apply split2.
      assert (Ls' : length s' = n) by (unfold s', sv; rewrite firstn_length; lia).
      assert (Lq : length q = nprm P k) by (unfold q, sa; rewrite skipn_length; lia).
      assert (LJn : length J = nv Q) by (destruct HJ as [L _]; exact L).
      assert (Ag : agree P k (hat P k ps) q).
      { apply (agree_trans P k _ ps); [apply hat_agree|]. intros j Hj Hm.
        rewrite <- (nth_mid s ps [] j Ls ltac:(lia)), <- (nth_mid s' q [] j Ls' ltac:(lia)).
        rewrite !app_nil_r. fold J. rewrite <- EJ.
        apply (exact_eq Q A W J J' (n + j) Hb R HJ HJ'b).
        - unfold nv. simpl dlo. rewrite jlen. simpl. lia.
        - simpl dlo. simpl dhi. change (map fst [(k, hat P k ps)]) with [k].
          rewrite jlo_p1, jhi_p1 by (try apply Hlen; exact Hj). pose proof (exok_parts k j Hk Hj Hm). nia. }
      assert (Hv' : pvalid P s' = true).
      { assert (E1 : dvalid Q J' = pvalid P s') by (rewrite EJ; apply (jvalid P Q eq_refl); exact Ls').
        assert (E2 : dvalid Q J = pvalid P s) by (unfold J; apply (jvalid P Q eq_refl); exact Ls).
        rewrite <- E1, <- (valid_pair Q A gam mu HQ W J J' R LJn ltac:(nia)), E2. exact Hv. }
      pose proof (H J' HJ' Hv') as C'. fold s' q in C'.
      apply (jidem P Hlen HTi k _ T K s' q Ls' Lq Ag) in C'. rewrite <- EJ in C'.
      apply (jidem P Hlen HTi k _ T K s ps Ls L1 (hat_agree P k ps)).
      fold J. apply (idem_pair Q A gam mu HQ K 0 W J J' R LJn Hw). exact C'.
  Qed.

  (* Repair within K steps: the registry without its events, threshold gam + K mu. *)
  Theorem pterm_abs : forall K W, (wterm gam mu K <= W)%Z -> (PTermBox P K <-> PTermRep P A W K).
  Proof. intros K W Hw. apply (dterm_abs (base P) A gam mu (pfrag_base P A gam mu HF) K W Hw). Qed.
End Cutoff.

(* ============================================================================================ *)
(* gsm's guarantee for events with arguments.                                                   *)
(* ============================================================================================ *)

(* An event occurrence: a kind and its arguments. *)
Definition pstep (P : pprog) (K : nat) (e : nat * list Z) (s : list Z) : list Z := pgov P K (fst e) (snd e) s.
Definition prstep (P : pprog) (K : nat) (e : nat * list Z) (s : list Z) : list Z := prun P K (fst e) (snd e) s.
Definition PEv (P : pprog) (e : nat * list Z) : Prop := (fst e < nk P)%nat /\ PArgs P (fst e) (snd e).
Definition liftI (I : nat -> nat -> Prop) (a b : nat * list Z) : Prop := I (fst a) (fst b).

(* From every valid state in range, trace-equivalent sequences of events with arguments in range
   reach the same state. *)
Definition PRunConv (P : pprog) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, PInBox P s -> pvalid P s = true -> forall es1 es2, tequiv (liftI I) es1 es2 ->
    Forall (PEv P) es1 -> runT (pstep P K) es1 s = runT (pstep P K) es2 s.

Section Gsm.
  Variable P : pprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : pfrag P A gam mu = true.

  Lemma HBb : bnd_ok (base P) A = true.
  Proof. exact (proj1 (frag_parts (base P) A gam mu (pfrag_base P A gam mu HF))). Qed.

  Lemma pwrite_box : forall ps s a, PInBox P s -> PInBox P (pwrite P ps s a).
  Proof.
    intros ps s [k e] [Hs Hb]. destruct (bnd_ok_parts (base P) A HBb) as [_ Hbd]. unfold pwrite; simpl.
    split; [rewrite upd_len; exact Hs|]. intros i Hi.
    destruct (Nat.eq_dec i k) as [-> | Hne].
    - rewrite upd_nth_eq by (unfold nv in *; simpl in *; lia). apply clamp_in. apply (Hbd k Hi).
    - rewrite upd_nth_neq by exact Hne. apply Hb. exact Hi.
  Qed.

  Lemma pap_box : forall k ps s, PInBox P s -> PInBox P (pap P k ps s).
  Proof.
    intros k ps s Hs. unfold pap, pevt. destruct (evalP _ _); [|exact Hs].
    unfold papplyT. generalize (eeff (evOf P k)) as t. intros t. revert s Hs.
    induction t as [|a t IH]; intros s Hs; simpl; [exact Hs|]. apply IH. apply pwrite_box. exact Hs.
  Qed.

  Lemma pgov_box : forall K k ps s, PInBox P s -> PInBox P (pgov P K k ps s).
  Proof. intros K k ps s Hs. unfold pgov, prepair. apply (itr_box (base P) A HBb). apply pap_box. exact Hs. Qed.

  Lemma prun_box : forall K k ps s, PInBox P s -> PInBox P (prun P K k ps s).
  Proof. intros K k ps s Hs. unfold prun. apply pgov_box. apply (itr_box (base P) A HBb). exact Hs. Qed.

  Lemma term_rep_box_p : forall K W, (wcc1 gam mu K <= W)%Z -> PTermRep P A W K -> PTermBox P K.
  Proof.
    intros K W Hw H. pose proof (M0 P A gam mu HF).
    apply (proj2 (pterm_abs P A gam mu HF K W ltac:(unfold wterm, wcc1 in *; nia))). exact H.
  Qed.

  Lemma pgov_valid : forall K W k ps s, (wcc1 gam mu K <= W)%Z -> PTermRep P A W K -> PInBox P s ->
    pvalid P (pgov P K k ps s) = true.
  Proof. intros K W k ps s Hw HT Hs. apply (term_rep_box_p K W Hw HT). apply pap_box. exact Hs. Qed.

  (* Given repair within K steps over the representatives: CC1 for I at the valid joint
     representatives iff trace-equivalent runs with arguments agree from every valid state. *)
  Theorem pgsm_exact : forall K W I, (wcc1 gam mu K <= W)%Z -> PTermRep P A W K ->
    (PCC1VRep P A W K I <-> PRunConv P K I).
  Proof.
    intros K W I Hw HT. rewrite <- (pcc1v_abs P A gam mu HF K W I Hw). split.
    - intros H s Hs Hv es1 es2 Hte Hev.
      apply (run_tequiv (pstep P K) (liftI I) (PEv P) (fun t => PInBox P t /\ pvalid P t = true)
                        (fun t => PInBox P t /\ pvalid P t = true)); try assumption.
      + intros t Ht. exact Ht.
      + intros e t _ [Ht _]. split; [apply pgov_box, Ht | apply (pgov_valid K W); assumption].
      + intros a b t [Ha Pa] [Hb Pb] HI [Ht Hv']. symmetry. exact (H t Ht Hv' _ _ Ha Hb HI _ _ Pa Pb).
      + split; assumption.
    - intros H s Hs Hv k1 k2 H1 H2 HI ps1 ps2 P1 P2.
      pose proof (H s Hs Hv [(k1, ps1); (k2, ps2)] [(k2, ps2); (k1, ps1)]
                    (teq_swap (liftI I) [] (k1, ps1) (k2, ps2) [] HI)) as E.
      apply E. constructor; [split; assumption|]. constructor; [split; assumption|]. constructor.
  Qed.

  (* gsm's runtime (normalize, then the governed step) from EVERY state in range. *)
  Theorem pgsm_sound : forall K W I, (wcc1 gam mu K <= W)%Z -> PTermRep P A W K -> PCC1VRep P A W K I ->
    forall s, PInBox P s -> forall es1 es2, tequiv (liftI I) es1 es2 -> Forall (PEv P) es1 ->
      runT (prstep P K) es1 s = runT (prstep P K) es2 s.
  Proof.
    intros K W I Hw HT HC s Hs es1 es2 Hte Hev.
    pose proof (term_rep_box_p K W Hw HT) as HTB. pose proof (proj2 (pcc1v_abs P A gam mu HF K W I Hw) HC) as HZ.
    apply (run_tequiv (prstep P K) (liftI I) (PEv P) (PInBox P) (PInBox P)); try assumption.
    - intros t Ht. exact Ht.
    - intros e t _ Ht. apply prun_box. exact Ht.
    - intros a b t [Ha Pa] [Hb Pb] HI Ht. unfold prstep, prun.
      set (u := itr K (prepair P) t).
      assert (Hu : PInBox P u) by (apply (itr_box (base P) A HBb), Ht).
      assert (Vu : pvalid P u = true) by (apply HTB, Ht).
      assert (V1 : forall k ps, pvalid P (pgov P K k ps u) = true) by (intros k ps; apply (pgov_valid K W); assumption).
      unfold prepair. rewrite (itr_valid_fix (base P) K _ (V1 _ _)), (itr_valid_fix (base P) K _ (V1 _ _)).
      symmetry. exact (HZ u Hu Vu _ _ Ha Hb HI _ _ Pa Pb).
  Qed.
End Gsm.

(* ============================================================================================ *)
(* The finite checks.                                                                           *)
(* ============================================================================================ *)

Definition pterm_check (P : pprog) (A : list Z) (W : Z) (K : nat) : bool := dterm_check (base P) A W K.

Definition pcc1v_check (P : pprog) (A : list Z) (W : Z) (K : nat) (Ib : nat -> nat -> bool) : bool :=
  forallb (fun k1 => forallb (fun k2 => if Ib k1 k2 then
    forallb (fun J => implb (pvalid P (sv P J))
      (leq (pgov P K k2 (sa2 P k1 J) (pgov P K k1 (sa1 P k1 J) (sv P J)))
           (pgov P K k1 (sa1 P k1 J) (pgov P K k2 (sa2 P k1 J) (sv P J)))))
      (RepS (jb P [k1; k2]) A W) else true) (seq 0 (nk P))) (seq 0 (nk P)).

Definition pidemv_check (P : pprog) (A : list Z) (W : Z) (K k : nat) : bool :=
  forallb (fun J => implb (pvalid P (sv P J))
    (leq (pgov P K k (sa P J) (pgov P K k (sa P J) (sv P J))) (pgov P K k (sa P J) (sv P J))))
    (RepS (jb P [k]) A W).

Theorem pterm_check_spec : forall P A W K, pterm_check P A W K = true <-> PTermRep P A W K.
Proof. intros P A W K. apply dterm_check_spec. Qed.

Theorem pcc1v_check_spec : forall P A W K Ib,
  pcc1v_check P A W K Ib = true <-> PCC1VRep P A W K (fun a b => Ib a b = true).
Proof.
  intros P A W K Ib. unfold pcc1v_check, PCC1VRep. split.
  - intros H k1 k2 H1 H2 HI J HJ Hv. pose proof (forallb_seq _ _ H k1 H1) as H3. simpl in H3.
    pose proof (forallb_seq _ _ H3 k2 H2) as H4. simpl in H4. rewrite HI in H4.
    rewrite forallb_forall in H4. specialize (H4 J HJ). rewrite implb_t in H4. apply leq_spec. exact (H4 Hv).
  - intros H. apply forallb_forall. intros k1 H1. apply forallb_forall. intros k2 H2.
    apply in_seq in H1. apply in_seq in H2. destruct (Ib k1 k2) eqn:HI; [|reflexivity].
    apply forallb_forall. intros J HJ. apply implb_t. intros Hv. apply leq_spec.
    apply H; [lia | lia | exact HI | exact HJ | exact Hv].
Qed.

Theorem pidemv_check_spec : forall P A W K k, pidemv_check P A W K k = true <-> PIdemVRep P A W K k.
Proof.
  intros P A W K k. unfold pidemv_check, PIdemVRep. rewrite forallb_forall. split.
  - intros H J HJ Hv. specialize (H J HJ). rewrite implb_t in H. apply leq_spec. exact (H Hv).
  - intros H J HJ. apply implb_t. intros Hv. apply leq_spec. exact (H J HJ Hv).
Qed.

(* Build for events with arguments, end to end: the fragment check and the two representative
   checks at the threshold wcc1 give gsm's runtime guarantee from every state in range, for every
   two trace-equivalent sequences of events with arguments in range. *)
Theorem pbuild_sound : forall P A gam mu K Ib, pfrag P A gam mu = true ->
  pterm_check P A (wcc1 gam mu K) K = true -> pcc1v_check P A (wcc1 gam mu K) K Ib = true ->
  forall s, PInBox P s -> forall es1 es2, tequiv (liftI (fun a b => Ib a b = true)) es1 es2 ->
    Forall (PEv P) es1 -> runT (prstep P K) es1 s = runT (prstep P K) es2 s.
Proof.
  intros P A gam mu K Ib HF HT HC.
  exact (pgsm_sound P A gam mu HF K (wcc1 gam mu K) _ (Z.le_refl _)
           (proj1 (pterm_check_spec P A _ K) HT) (proj1 (pcc1v_check_spec P A _ K Ib) HC)).
Qed.

(* Idempotence from the check, at every valid state and all arguments. *)
Theorem pidem_build : forall P A gam mu K k, pfrag P A gam mu = true -> (k < nk P)%nat ->
  pidemv_check P A (widem gam mu K) K k = true -> PIdemVBox P K k.
Proof.
  intros P A gam mu K k HF Hk H.
  apply (proj2 (pidemv_abs P A gam mu HF K k (widem gam mu K) Hk (Z.le_refl _))). apply pidemv_check_spec. exact H.
Qed.

(* A failure of the check is a real failure: its witness is a state and arguments in range. *)
Theorem pcheck_fail_real : forall P A gam mu K Ib, pfrag P A gam mu = true ->
  pcc1v_check P A (wcc1 gam mu K) K Ib = false -> ~ PCC1VBox P K (fun a b => Ib a b = true).
Proof.
  intros P A gam mu K Ib HF HC H.
  apply (pcc1v_abs P A gam mu HF K (wcc1 gam mu K) _ (Z.le_refl _)) in H.
  apply pcc1v_check_spec in H. congruence.
Qed.

(* Declared pairs need only one orientation: trace equivalence for a relation is the same as for
   its symmetric closure. So a check over k1 <= k2 covers every pair. *)
Lemma tequiv_sym_cover : forall {E : Type} (I J : E -> E -> Prop), (forall a b, J a b -> I a b \/ I b a) ->
  forall l1 l2, tequiv J l1 l2 -> tequiv I l1 l2.
Proof.
  intros E I J HJ l1 l2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2].
  - apply teq_refl.
  - destruct (HJ a b Hab) as [Hi | Hi]; [apply teq_swap; exact Hi|].
    apply teq_sym. apply teq_swap. exact Hi.
  - apply teq_sym. exact IH.
  - eapply teq_trans; eassumption.
Qed.

(* Every pair checked in one orientation: any permutation of events with arguments converges. *)
Theorem pbuild_perm : forall P A gam mu K, pfrag P A gam mu = true ->
  pterm_check P A (wcc1 gam mu K) K = true -> pcc1v_check P A (wcc1 gam mu K) K Nat.leb = true ->
  forall s, PInBox P s -> forall es1 es2, Permutation es1 es2 -> Forall (PEv P) es1 ->
    runT (prstep P K) es1 s = runT (prstep P K) es2 s.
Proof.
  intros P A gam mu K HF HT HC s Hs es1 es2 Hp Hev.
  apply (pbuild_sound P A gam mu K Nat.leb HF HT HC s Hs); [|exact Hev].
  apply (tequiv_sym_cover _ (fun _ _ => True)).
  - intros a b _. unfold liftI. destruct (Nat.leb (fst a) (fst b)) eqn:E; [left; reflexivity|].
    right. apply Nat.leb_gt in E. apply Nat.leb_le. lia.
  - apply (perm_tequiv_total (fun _ _ => True) (PEv P)); [intros; exact I | exact Hp | exact Hev].
Qed.

(* ============================================================================================ *)
(* The size of the representative domain: independent of the widths of the ranges.             *)
(* ============================================================================================ *)

Lemma prod_dom : forall A R los his, (0 <= R)%Z -> length los = length his ->
  (fold_right Nat.mul 1%nat (map (@length Z) (domsF A R los his)) <= (length A * Z.to_nat (2 * R + 1)) ^ length los)%nat.
Proof.
  intros A R los. induction los as [|lo los IH]; intros [|hi his] HR Hl; simpl in *; try lia.
  apply Nat.mul_le_mono.
  - eapply Nat.le_trans; [apply lenF | apply dom_length; exact HR].
  - apply IH; [exact HR | lia].
Qed.

(* Every registry: at most (|A| (2 R + 1))^N representatives, N the number of coordinates and R
   the radius N (W + 1). *)
Theorem RepS_size : forall Q A W, (0 <= W)%Z -> length (dlo Q) = length (dhi Q) ->
  (length (RepS Q A W) <= (length A * Z.to_nat (2 * radius Q W + 1)) ^ nv Q)%nat.
Proof.
  intros Q A W HW Hl. rewrite RepS_length. unfold nv. apply prod_dom; [unfold radius, nv; nia | exact Hl].
Qed.

(* The joint box of two events: N = n + m1 + m2 coordinates. *)
Theorem pcc1_domain_size : forall P A gam mu k1 k2 W, pfrag P A gam mu = true -> (0 <= W)%Z ->
  nv (jb P [k1; k2]) = (pn P + nprm P k1 + nprm P k2)%nat /\
  radius (jb P [k1; k2]) W = (Z.of_nat (pn P + nprm P k1 + nprm P k2) * (W + 1))%Z /\
  (length (RepS (jb P [k1; k2]) A W) <=
     (length A * Z.to_nat (2 * (Z.of_nat (pn P + nprm P k1 + nprm P k2) * (W + 1)) + 1)) ^ (pn P + nprm P k1 + nprm P k2))%nat.
Proof.
  intros P A gam mu k1 k2 W HF HW. pose proof (Hlen P A gam mu HF) as L.
  assert (N : nv (jb P [k1; k2]) = (pn P + nprm P k1 + nprm P k2)%nat) by (unfold nv, jb; simpl dlo; rewrite jlen; simpl; lia).
  assert (Rd : radius (jb P [k1; k2]) W = (Z.of_nat (pn P + nprm P k1 + nprm P k2) * (W + 1))%Z) by (unfold radius; rewrite N; reflexivity).
  split; [exact N | split; [exact Rd|]].
  rewrite <- Rd, <- N. apply RepS_size; [exact HW|]. unfold jb, jlo, jhi; simpl. rewrite !lenA, !lenM.
  unfold pn in L. lia.
Qed.

(* The joint box of one event: N = n + m. *)
Theorem pidem_domain_size : forall P A gam mu k W, pfrag P A gam mu = true -> (0 <= W)%Z ->
  nv (jb P [k]) = (pn P + nprm P k)%nat /\
  (length (RepS (jb P [k]) A W) <=
     (length A * Z.to_nat (2 * (Z.of_nat (pn P + nprm P k) * (W + 1)) + 1)) ^ (pn P + nprm P k))%nat.
Proof.
  intros P A gam mu k W HF HW. pose proof (Hlen P A gam mu HF) as L.
  assert (N : nv (jb P [k]) = (pn P + nprm P k)%nat) by (unfold nv, jb; simpl dlo; rewrite jlen; simpl; lia).
  split; [exact N|]. assert (Rd : radius (jb P [k]) W = (Z.of_nat (pn P + nprm P k) * (W + 1))%Z) by (unfold radius; rewrite N; reflexivity).
  rewrite <- Rd, <- N. apply RepS_size; [exact HW|]. unfold jb, jlo, jhi; simpl. rewrite !lenA, !lenM.
  unfold pn in L. lia.
Qed.

(* ============================================================================================ *)
(* The special cases: no parameters (DifferenceAbstraction) and threshold 0 (AbstractionGsm).    *)
(* ============================================================================================ *)

(* At threshold 0 (no arithmetic: gam = mu = 0) the radius of the joint box of two events is
   n + m1 + m2, the cutoff n + 2m of cc1_abs and cc1_valid_abs, and that of one event is n + m, the
   cutoff of idem_valid_abs; the representatives reps N C of the comparison fragment lie in the
   domain, and the relation at threshold 0 is the order type fixing the anchors (rel0_oiso). *)
Theorem pradius0 : forall P k1 k2 k,
  radius (jb P [k1; k2]) 0 = Z.of_nat (pn P + nprm P k1 + nprm P k2) /\
  radius (jb P [k]) 0 = Z.of_nat (pn P + nprm P k).
Proof.
  intros P k1 k2 k. unfold radius, nv, jb. simpl dlo. rewrite !jlen. simpl. split; lia.
Qed.

Theorem preps0_in_dom : forall P k1 k2 c C,
  incl (reps (pn P + nprm P k1 + nprm P k2) (c :: C)) (dom (c :: C) (radius (jb P [k1; k2]) 0)).
Proof. intros P k1 k2 c C. rewrite (proj1 (pradius0 P k1 k2 k1)). apply reps_in_dom. Qed.

(* No parameters: a registry of DifferenceAbstraction as one with parameterless events. *)
Definition embed (P0 : dprog) : pprog :=
  mkPP (dlo P0) (dhi P0) (map (fun ev => mkE [] (fst ev) (snd ev)) (dev P0)) (dinv P0).

Lemma evOf_embed : forall P0 k,
  evOf (embed P0) k = mkE [] (fst (nth k (dev P0) (DTrue, []))) (snd (nth k (dev P0) (DTrue, []))).
Proof.
  intros P0 k. unfold evOf, embed. simpl.
  change dummyE with ((fun ev : dpred * transform => mkE [] (fst ev) (snd ev)) (DTrue, [])).
  rewrite map_nth. reflexivity.
Qed.

Lemma prmOf_embed : forall P0 k, prmOf (embed P0) k = [].
Proof. intros P0 k. unfold prmOf. rewrite evOf_embed. reflexivity. Qed.

Lemma nprm_embed : forall P0 k, nprm (embed P0) k = 0%nat.
Proof. intros P0 k. unfold nprm. rewrite prmOf_embed. reflexivity. Qed.

Lemma papplyT_embed : forall P0 t s, papplyT (embed P0) [] t s = applyT P0 t s.
Proof.
  intros P0 t. unfold papplyT, applyT. induction t as [|a t IH]; intros s; simpl; [reflexivity|].
  rewrite <- IH. f_equal. unfold pwrite, write. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma pap_embed : forall P0 k s, pap (embed P0) k [] s = dap P0 k s.
Proof.
  intros P0 k s. unfold pap. rewrite evOf_embed. unfold pevt. simpl. rewrite app_nil_r, papplyT_embed.
  unfold dap. destruct (nth_error (dev P0) k) as [ev|] eqn:E.
  - rewrite (nth_error_nth (dev P0) k (DTrue, []) E). reflexivity.
  - apply nth_error_None in E. rewrite (nth_overflow (dev P0) (DTrue, []) E). reflexivity.
Qed.

Theorem pgov_embed : forall P0 K k s, pgov (embed P0) K k [] s = dgov P0 K k s.
Proof. intros P0 K k s. unfold pgov, dgov. rewrite pap_embed. reflexivity. Qed.

Lemma PArgs_embed : forall P0 k ps, PArgs (embed P0) k ps <-> ps = [].
Proof.
  intros P0 k ps. unfold PArgs, bx. rewrite prmOf_embed. simpl. split.
  - intros [H _]. destruct ps; [reflexivity | discriminate].
  - intros ->. split; [reflexivity | intros i Hi; lia].
Qed.

Lemma flat_embed : forall P0 (f : Z * Z -> Z) ks, flat_map (fun k => map f (prmOf (embed P0) k)) ks = [].
Proof. intros P0 f ks. induction ks as [|k ks IH]; simpl; [reflexivity|]. rewrite prmOf_embed. exact IH. Qed.

Lemma jb_embed : forall P0 ks, jb (embed P0) ks = mkD (dlo P0) (dhi P0) [] [].
Proof. intros P0 ks. unfold jb, jlo, jhi. rewrite !flat_embed, !app_nil_r. reflexivity. Qed.

Theorem embed_cc1_box : forall P0 K I, PCC1VBox (embed P0) K I <-> DCC1VBox P0 K I.
Proof.
  intros P0 K I. unfold PCC1VBox, DCC1VBox. unfold nk, nke. simpl. rewrite lenM. split.
  - intros H s Hs Hv k1 k2 H1 H2 HI. rewrite <- !pgov_embed.
    apply H; try assumption; apply PArgs_embed; reflexivity.
  - intros H s Hs Hv k1 k2 H1 H2 HI ps1 ps2 P1 P2. apply PArgs_embed in P1, P2. subst. rewrite !pgov_embed.
    apply H; assumption.
Qed.

Lemma skipn_len_all : forall (l : list Z), skipn (length l) l = [].
Proof. induction l as [|x l IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma firstn_len_all : forall (l : list Z), firstn (length l) l = l.
Proof. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Theorem embed_cc1_rep : forall P0 A W K I, bnd_ok P0 A = true -> (0 <= W)%Z ->
  (PCC1VRep (embed P0) A W K I <-> DCC1VRep P0 A W K I).
Proof.
  intros P0 A W K I Hb HW. unfold PCC1VRep, DCC1VRep. unfold nk, nke. simpl. rewrite lenM.
  assert (E : forall J, In J (RepS P0 A W) -> sv (embed P0) J = J /\ (forall k, sa1 (embed P0) k J = []) /\
                 forall k, sa2 (embed P0) k J = []).
  { intros J HJ. apply (RepS_spec P0 A W J Hb HW) in HJ. destruct HJ as [[L _] _].
    unfold sv, sa1, sa2, pn. simpl. unfold nv in L. rewrite <- L, firstn_len_all, skipn_len_all.
    split; [reflexivity | split; intros k; rewrite nprm_embed; [reflexivity | reflexivity]]. }
  split.
  - intros H s Hs Hv k1 k2 H1 H2 HI. destruct (E s Hs) as [E1 [E2 E3]].
    assert (Hs' : In s (RepS (jb (embed P0) [k1; k2]) A W)) by (rewrite jb_embed; exact Hs).
    specialize (H k1 k2 H1 H2 HI s Hs'). rewrite E1, E2, E3, !pgov_embed in H. apply H. exact Hv.
  - intros H k1 k2 H1 H2 HI J HJ Hv. rewrite jb_embed in HJ. destruct (E J HJ) as [E1 [E2 E3]].
    rewrite E1, E2, E3, !pgov_embed. rewrite E1 in Hv. apply H; assumption.
Qed.

(* The fragment check: a registry in the difference fragment is, as a parameterless registry, in
   the parameterized one. *)
Fixpoint allv (n : nat) (e : dexp) : bool :=
  match e with
  | DV i => Nat.ltb i n
  | DL _ => true
  | DAdd a b | DSub a b => allv n a && allv n b
  end.

Lemma tx_id : forall n off ex sg e, allv n e = true -> tx n off 0 ex sg e = e.
Proof.
  intros n off ex sg e. induction e as [i | c | a IHa b IHb | a IHa b IHb]; simpl; intros H; try reflexivity.
  - rewrite H. reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
Qed.

Lemma merge_some_l : forall a b o i, merge a b = Some o -> a = Some i -> o = Some i.
Proof. intros [a|] [b|] o i H E; simpl in H; try discriminate; injection E as <-; injection H as <-; reflexivity. Qed.

Lemma merge_some_r : forall a b o i, merge a b = Some o -> b = Some i -> o = Some i.
Proof. intros [a|] [b|] o i H E; simpl in H; try discriminate; injection E as <-; injection H as <-; reflexivity. Qed.

Lemma norm_allv : forall n e p q c, norm e = Some (p, q, c) ->
  (forall i, p = Some i -> (i < n)%nat) -> (forall i, q = Some i -> (i < n)%nat) -> allv n e = true.
Proof.
  intros n e. induction e as [i | c0 | a IHa b IHb | a IHa b IHb]; intros p q c H Hp Hq; simpl in H |- *.
  - injection H as <- <- <-. apply Nat.ltb_lt. apply Hp. reflexivity.
  - reflexivity.
  - destruct (norm a) as [[[p1 q1] c1]|]; [|discriminate]. destruct (norm b) as [[[p2 q2] c2]|]; [|discriminate].
    simpl in H. destruct (merge p1 p2) as [p'|] eqn:Ep; [|discriminate]. destruct (merge q1 q2) as [q'|] eqn:Eq; [|discriminate].
    injection H as <- <- <-. apply andb_true_iff. split.
    + apply (IHa p1 q1 c1 eq_refl); intros i Hi; [apply Hp; exact (merge_some_l _ _ _ _ Ep Hi) | apply Hq; exact (merge_some_l _ _ _ _ Eq Hi)].
    + apply (IHb p2 q2 c2 eq_refl); intros i Hi; [apply Hp; exact (merge_some_r _ _ _ _ Ep Hi) | apply Hq; exact (merge_some_r _ _ _ _ Eq Hi)].
  - destruct (norm a) as [[[p1 q1] c1]|]; [|discriminate]. destruct (norm b) as [[[p2 q2] c2]|]; [|discriminate].
    simpl in H. destruct (merge p1 q2) as [p'|] eqn:Ep; [|discriminate]. destruct (merge q1 p2) as [q'|] eqn:Eq; [|discriminate].
    injection H as <- <- <-. apply andb_true_iff. split.
    + apply (IHa p1 q1 c1 eq_refl); intros i Hi; [apply Hp; exact (merge_some_l _ _ _ _ Ep Hi) | apply Hq; exact (merge_some_l _ _ _ _ Eq Hi)].
    + apply (IHb p2 q2 c2 eq_refl); intros i Hi; [apply Hq; exact (merge_some_r _ _ _ _ Eq Hi) | apply Hp; exact (merge_some_r _ _ _ _ Ep Hi)].
Qed.

Lemma pok_id : forall n A gam off ex sg p, pok n A gam p = true -> txP n off 0 ex sg p = p.
Proof.
  intros n A gam off ex sg p. induction p as [| o a b | p IHp q IHq | p IHp q IHq | p IHp]; simpl; intros H.
  - reflexivity.
  - change (atom_ok n A gam (norm (DSub a b)) = true) in H.
    assert (Hv : allv n (DSub a b) = true).
    { destruct (norm (DSub a b)) as [[[[i|] [j|]] c]|] eqn:E; simpl in H; try discriminate;
        apply (norm_allv n _ _ _ _ E); intros k Hk; try discriminate; injection Hk as <-;
        repeat match goal with Hb : _ && _ = true |- _ => apply andb_true_iff in Hb as [? ?] end;
        apply Nat.ltb_lt; assumption. }
    simpl in Hv. apply andb_true_iff in Hv as [Ha Hb]. rewrite !tx_id by assumption.
    destruct (fbA n 0 a b); reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite IHp, IHq by assumption. reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite IHp, IHq by assumption. reflexivity.
  - rewrite IHp by assumption. reflexivity.
Qed.

Lemma aok_allv : forall n A a, aok n A a = true -> allv n (snd a) = true.
Proof.
  intros n A [k e] H. unfold aok in H. simpl in *. apply andb_true_iff in H as [_ H].
  destruct (norm e) as [[[[j|] [q|]] c]|] eqn:E; try discriminate;
    apply (norm_allv n e _ _ _ E); intros i Hi; try discriminate; injection Hi as <-; apply Nat.ltb_lt; exact H.
Qed.

Lemma tr_id : forall n A off ex sg t, forallb (aok n A) t = true ->
  map (fun a => (fst a, txW n off 0 ex sg (snd a))) t = t.
Proof.
  intros n A off ex sg t H. rewrite forallb_forall in H. rewrite <- (map_id t) at 2. apply map_ext_in.
  intros a Ha. unfold txW. pose proof (aok_allv n A a (H a Ha)) as Hv.
  destruct (fbW n 0 (snd a)); rewrite tx_id by exact Hv; destruct a; reflexivity.
Qed.

Lemma trc_id : forall n A t, forallb (aok n A) t = true -> map (fun a => (fst a, tx n n 0 [] [] (snd a))) t = t.
Proof.
  intros n A t H. rewrite forallb_forall in H. rewrite <- (map_id t) at 2. apply map_ext_in.
  intros a Ha. rewrite tx_id by exact (aok_allv n A a (H a Ha)). destruct a; reflexivity.
Qed.

Lemma dfrag_sub : forall P0 A gam mu evs, dfrag P0 A gam mu = true -> incl evs (dev P0) ->
  dfrag (mkD (dlo P0) (dhi P0) evs (dinv P0)) A gam mu = true.
Proof.
  intros P0 A gam mu evs H Hi. unfold dfrag in *.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff. split; [apply andb_true_iff; split; [exact H|] | exact H5].
  rewrite forallb_forall in H4 |- *. intros ev Hev. apply H4. apply Hi. exact Hev.
Qed.

Section Embed.
  Variable P0 : dprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : dfrag P0 A gam mu = true.

  Lemma ev_ok : forall k, (k < nke P0)%nat -> pok (nv P0) A gam (fst (nth k (dev P0) (DTrue, []))) = true /\
    tok (nv P0) A mu (snd (nth k (dev P0) (DTrue, []))) = true.
  Proof.
    intros k Hk. destruct (frag_parts P0 A gam mu HF) as [_ [_ [_ [He _]]]]. apply He. apply nth_In. exact Hk.
  Qed.

  Lemma inv_id : map (clipI (nv P0)) (dinv P0) = dinv P0.
  Proof.
    rewrite <- (map_id (dinv P0)) at 2. apply map_ext_in. intros iv Hiv.
    destruct (proj2 (proj2 (proj2 (proj2 (frag_parts P0 A gam mu HF)))) iv Hiv) as [Hp Ht].
    destruct (tok_parts P0 A mu _ Ht) as [Ha _]. unfold clipI. rewrite (pok_id _ _ _ _ _ _ _ Hp), (trc_id _ _ _ Ha).
    destruct iv; reflexivity.
  Qed.

  Lemma jev_id : forall off k, (k < nke P0)%nat ->
    jev (nv P0) off (evOf (embed P0) k) [] = nth k (dev P0) (DTrue, []).
  Proof.
    intros off k Hk. destruct (ev_ok k Hk) as [Hp Ht]. destruct (tok_parts P0 A mu _ Ht) as [Ha _].
    rewrite evOf_embed. unfold jev. simpl. rewrite (pok_id _ _ _ _ _ _ _ Hp), (tr_id _ _ _ _ _ _ Ha).
    destruct (nth k (dev P0) (DTrue, [])); reflexivity.
  Qed.

  Theorem embed_frag : pfrag (embed P0) A gam mu = true.
  Proof.
    destruct (frag_parts P0 A gam mu HF) as [Hb _].
    assert (Hn : nk (embed P0) = nke P0) by (unfold nk, nke; simpl; apply lenM).
    assert (Hsg : forall k, sigs (embed P0) k = [[]]) by (intros k; unfold sigs; rewrite nprm_embed; reflexivity).
    unfold pfrag. rewrite Hn. apply andb_true_iff. split; [apply andb_true_iff; split|].
    - change (dfrag (mkD (dlo P0) (dhi P0) [] (dinv P0)) A gam mu = true). apply dfrag_sub; [exact HF | intros x []].
    - apply forallb_forall. intros k Hk. apply in_seq in Hk. destruct (ev_ok k ltac:(lia)) as [Hp Ht].
      destruct (tok_parts P0 A mu _ Ht) as [Ha _].
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
      + unfold tgt_ok. rewrite evOf_embed. simpl. rewrite forallb_forall in Ha |- *. intros a Hin.
        specialize (Ha a Hin). unfold aok in Ha. apply andb_true_iff in Ha as [Ha _]. exact Ha.
      + unfold exok. rewrite nprm_embed. reflexivity.
      + rewrite jb_embed. exact Hb.
      + rewrite Hsg. simpl. rewrite andb_true_r. unfold joint. simpl map. unfold jlo, jhi. rewrite !flat_embed, !app_nil_r.
        cbn [jevs]. unfold pn. simpl plo. rewrite (jev_id _ k ltac:(lia)). change (length (dlo P0)) with (nv P0). rewrite inv_id.
        apply dfrag_sub; [exact HF|]. intros x [<- | []]. apply nth_In. unfold nke in Hk. lia.
    - apply forallb_forall. intros k1 H1. apply forallb_forall. intros k2 H2. apply in_seq in H1. apply in_seq in H2.
      apply andb_true_iff. split; [rewrite jb_embed; exact Hb|]. rewrite !Hsg. simpl. rewrite !andb_true_r.
      unfold joint. simpl map. unfold jlo, jhi. rewrite !flat_embed, !app_nil_r.
      cbn [jevs]. unfold pn. simpl plo. rewrite (jev_id _ k1 ltac:(lia)), (jev_id _ k2 ltac:(lia)).
      change (length (dlo P0)) with (nv P0). rewrite inv_id.
      apply dfrag_sub; [exact HF|]. intros x [<- | [<- | []]]; apply nth_In; unfold nke in *; lia.
  Qed.

  (* DifferenceAbstraction's dcc1v_abs as the case of no parameters. *)
  Theorem m0_special : forall K W I, (wcc1 gam mu K <= W)%Z -> (DCC1VBox P0 K I <-> DCC1VRep P0 A W K I).
  Proof.
    intros K W I Hw. pose proof (gam_nonneg P0 A gam mu HF). pose proof (mu_nonneg P0 A gam mu HF).
    unfold wcc1 in Hw. destruct (frag_parts P0 A gam mu HF) as [Hb _].
    rewrite <- embed_cc1_box, <- (embed_cc1_rep P0 A W K I Hb ltac:(nia)).
    apply (pcc1v_abs (embed P0) A gam mu embed_frag K W I). unfold wcc1. exact Hw.
  Qed.
End Embed.

(* ============================================================================================ *)
(* Non-vacuity.                                                                                 *)
(* ============================================================================================ *)

(* ---- A wallet, written directly: balance in [-1000, 10^9]. Events: deposit(a) and fee(f), the
   balance moved by the amount; withdraw(b) when balance >= b; set(v), the balance set to v in
   [-1000, 10^9]. Amounts in [1, 3]. Invariant balance >= 0, repair balance := 0. The amounts are
   exact parameters (balance := balance + a falls back); v is an abstract parameter (a copy), its
   range 10^9 wide. ---- *)
Definition wallet_p : pprog :=
  mkPP [(-1000)%Z] [H9]
    [mkE [(1%Z, 3%Z)] DTrue [(0%nat, DAdd (DV 0) (DV 1))];
     mkE [(1%Z, 3%Z)] (DCmp CGe (DV 0) (DV 1)) [(0%nat, DSub (DV 0) (DV 1))];
     mkE [(1%Z, 3%Z)] DTrue [(0%nat, DSub (DV 0) (DV 1))];
     mkE [((-1000)%Z, H9)] DTrue [(0%nat, DV 1)]]
    [(DCmp CGe (DV 0) (DL 0), [(0%nat, DL 0)])].

Definition wallet_pA : list Z := [(-1000)%Z; H9; 0%Z; 1%Z; 3%Z].

(* Checked pairs: two deposits, two fees. *)
Definition wallet_pI (a b : nat) : bool := (Nat.eqb a 0 && Nat.eqb b 0) || (Nat.eqb a 2 && Nat.eqb b 2).

Theorem wallet_p_frag : pfrag wallet_p wallet_pA 0 3 = true /\ wcc1 0 3 1 = 24%Z /\ widem 0 3 1 = 18%Z /\
  mask wallet_p 0 = [true] /\ mask wallet_p 1 = [true] /\ mask wallet_p 2 = [true] /\ mask wallet_p 3 = [false].
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem wallet_p_reps : length (RepS (jb wallet_p [0; 0]) wallet_pA 24) = 2754%nat /\
  length (RepS (jb wallet_p [3]) wallet_pA 18) = 24964%nat.
Proof. split; vm_compute; reflexivity. Qed.

Theorem wallet_p_checks : pterm_check wallet_p wallet_pA 24 1 = true /\
  pcc1v_check wallet_p wallet_pA 24 1 wallet_pI = true /\
  pidemv_check wallet_p wallet_pA 18 1 3 = true /\
  pcc1v_check wallet_p wallet_pA 24 1 (fun _ _ => true) = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Two deposits, and two fees, commute at every balance and all amounts: the runtime converges
   from every balance for every reordering of the checked pairs. *)
Theorem wallet_p_converges : forall s, PInBox wallet_p s ->
  forall es1 es2, tequiv (liftI (fun a b => wallet_pI a b = true)) es1 es2 -> Forall (PEv wallet_p) es1 ->
  runT (prstep wallet_p 1) es1 s = runT (prstep wallet_p 1) es2 s.
Proof.
  destruct wallet_p_checks as [HT [HC _]].
  exact (pbuild_sound wallet_p wallet_pA 0 3 1 wallet_pI (proj1 wallet_p_frag) HT HC).
Qed.

(* set(v) is idempotent at every valid balance and every v in [-1000, 10^9]. *)
Theorem wallet_p_set_idem : PIdemVBox wallet_p 1 3.
Proof.
  destruct wallet_p_checks as [_ [_ [HI _]]].
  exact (pidem_build wallet_p wallet_pA 0 3 1 3 (proj1 wallet_p_frag) ltac:(cbv; lia) HI).
Qed.

(* Not every pair commutes; the failures are real, at balances and amounts in range:
   - withdraw guard: balance 1, deposit 1 and withdraw 2 give 0 and 2;
   - saturation at the upper bound: balance 10^9 - 1, deposit 3 and withdraw 3 give 10^9 - 3 and
     10^9 - 1;
   - repair at the lower bound: balance 0, deposit 1 and fee 3 give 0 and 1;
   - two withdrawals: balance 3, withdraw 2 and withdraw 3 give 1 and 0. *)
Theorem wallet_p_diverges : ~ PCC1VBox wallet_p 1 (fun _ _ => true = true) /\
  pgov wallet_p 1 1 [2%Z] (pgov wallet_p 1 0 [1%Z] [1%Z]) = [0%Z] /\
  pgov wallet_p 1 0 [1%Z] (pgov wallet_p 1 1 [2%Z] [1%Z]) = [2%Z] /\
  pgov wallet_p 1 1 [3%Z] (pgov wallet_p 1 0 [3%Z] [(H9 - 1)%Z]) = [(H9 - 3)%Z] /\
  pgov wallet_p 1 0 [3%Z] (pgov wallet_p 1 1 [3%Z] [(H9 - 1)%Z]) = [(H9 - 1)%Z] /\
  pgov wallet_p 1 2 [3%Z] (pgov wallet_p 1 0 [1%Z] [0%Z]) = [0%Z] /\
  pgov wallet_p 1 0 [1%Z] (pgov wallet_p 1 2 [3%Z] [0%Z]) = [1%Z] /\
  pgov wallet_p 1 1 [3%Z] (pgov wallet_p 1 1 [2%Z] [3%Z]) = [1%Z] /\
  pgov wallet_p 1 1 [2%Z] (pgov wallet_p 1 1 [3%Z] [3%Z]) = [0%Z].
Proof.
  split; [exact (pcheck_fail_real wallet_p wallet_pA 0 3 1 (fun _ _ => true) (proj1 wallet_p_frag)
                   (proj2 (proj2 (proj2 wallet_p_checks))))|].
  repeat split; vm_compute; reflexivity.
Qed.

(* ---- The wallet with events that record facts and invariants that derive outcomes: deposited
   and requested in [0, 10^9], flag in [0, 1]. deposit(a): deposited := deposited + a;
   withdraw(b): requested := requested + b; amounts in [1, 2]. Invariants: requested <= deposited
   or flag = 1 (repair flag := 1); deposited < requested or flag = 0 (repair flag := 0). Every
   pair converges, at every state and all amounts. ---- *)
Definition facts_p : pprog :=
  mkPP [0%Z; 0%Z; 0%Z] [H9; H9; 1%Z]
    [mkE [(1%Z, 2%Z)] DTrue [(0%nat, DAdd (DV 0) (DV 3))];
     mkE [(1%Z, 2%Z)] DTrue [(1%nat, DAdd (DV 1) (DV 3))]]
    [(DOr (DCmp CLe (DV 1) (DV 0)) (DCmp CEq (DV 2) (DL 1)), [(2%nat, DL 1)]);
     (DOr (DCmp CLt (DV 0) (DV 1)) (DCmp CEq (DV 2) (DL 0)), [(2%nat, DL 0)])].

Definition facts_A : list Z := [0%Z; H9; 1%Z; 2%Z].

Theorem facts_frag : pfrag facts_p facts_A 0 2 = true /\ wcc1 0 2 1 = 16%Z /\
  mask facts_p 0 = [true] /\ mask facts_p 1 = [true].
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem facts_reps : length (RepS (jb facts_p [0; 1]) facts_A 16) = 242208%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem facts_checks : pterm_check facts_p facts_A 16 1 = true /\ pcc1v_check facts_p facts_A 16 1 Nat.leb = true.
Proof. split; [vm_compute; reflexivity | vm_cast_no_check (eq_refl true)]. Qed.

(* Every reordering of deposits and withdrawals, any amounts, converges from every state. *)
Theorem facts_converges : forall s, PInBox facts_p s ->
  forall es1 es2, Permutation es1 es2 -> Forall (PEv facts_p) es1 ->
  runT (prstep facts_p 1) es1 s = runT (prstep facts_p 1) es2 s.
Proof.
  destruct facts_checks as [HT HC].
  exact (pbuild_perm facts_p facts_A 0 2 1 (proj1 facts_frag) HT HC).
Qed.

(* The derived flag, at the bound: deposited 10^9 - 1, requested 10^9; a deposit of 2 saturates
   deposited at 10^9 and clears the flag, in either order with a withdrawal. *)
Theorem facts_flag : pgov facts_p 1 0 [2%Z] [(H9 - 1)%Z; H9; 1%Z] = [H9; H9; 0%Z] /\
  pgov facts_p 1 1 [1%Z] (pgov facts_p 1 0 [2%Z] [(H9 - 1)%Z; H9; 1%Z]) =
  pgov facts_p 1 0 [2%Z] (pgov facts_p 1 1 [1%Z] [(H9 - 1)%Z; H9; 1%Z]).
Proof. split; vm_compute; reflexivity. Qed.

(* ---- Inventory: stock and reserved in [0, 10^9], qty in [1, 2]. restock(q): stock := stock + q;
   reserve(q): if reserved + q <= stock then reserved := reserved + q (a comparison of a sum with
   a variable: q exact, the guard is reserved - stock <= -q). Invariant reserved <= stock, repair
   reserved := stock. ---- *)
Definition stock_p : pprog :=
  mkPP [0%Z; 0%Z] [H9; H9]
    [mkE [(1%Z, 2%Z)] DTrue [(0%nat, DAdd (DV 0) (DV 2))];
     mkE [(1%Z, 2%Z)] (DCmp CLe (DAdd (DV 1) (DV 2)) (DV 0)) [(1%nat, DAdd (DV 1) (DV 2))]]
    [(DCmp CLe (DV 1) (DV 0), [(1%nat, DV 0)])].

Definition stock_A : list Z := [0%Z; H9; 1%Z; 2%Z].

Definition restocks_p (a b : nat) : bool := Nat.eqb a 0 && Nat.eqb b 0.

Theorem stock_frag : pfrag stock_p stock_A 2 2 = true /\ wcc1 2 2 1 = 18%Z /\
  mask stock_p 0 = [true] /\ mask stock_p 1 = [true].
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem stock_checks : pterm_check stock_p stock_A 18 1 = true /\ pcc1v_check stock_p stock_A 18 1 restocks_p = true.
Proof. split; vm_compute; reflexivity. Qed.

(* Restocks commute at every state and all quantities. *)
Theorem stock_converges : forall s, PInBox stock_p s ->
  forall es1 es2, tequiv (liftI (fun a b => restocks_p a b = true)) es1 es2 -> Forall (PEv stock_p) es1 ->
  runT (prstep stock_p 1) es1 s = runT (prstep stock_p 1) es2 s.
Proof.
  destruct stock_checks as [HT HC].
  exact (pbuild_sound stock_p stock_A 2 2 1 restocks_p (proj1 stock_frag) HT HC).
Qed.

(* Two reserves do not commute when stock runs short (stock 2, reserved 0, quantities 1 and 2),
   nor do reserve and restock at an empty stock. *)
Theorem stock_reserve_diverges :
  pgov stock_p 1 1 [2%Z] (pgov stock_p 1 1 [1%Z] [2%Z; 0%Z]) = [2%Z; 1%Z] /\
  pgov stock_p 1 1 [1%Z] (pgov stock_p 1 1 [2%Z] [2%Z; 0%Z]) = [2%Z; 2%Z] /\
  pgov stock_p 1 1 [1%Z] (pgov stock_p 1 0 [2%Z] [0%Z; 0%Z]) = [2%Z; 1%Z] /\
  pgov stock_p 1 0 [2%Z] (pgov stock_p 1 1 [1%Z] [0%Z; 0%Z]) = [2%Z; 0%Z].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- Room booking under a capacity: booked and cap in [0, 10^9]. book(n): if booked + n <= cap
   then booked := booked + n; cancel(n): booked := booked - n (saturating at 0); n in [1, 2];
   setcap(c): cap := c, c in [0, 10^9] an abstract parameter. Invariant booked <= cap, repair
   booked := cap. ---- *)
Definition room_p : pprog :=
  mkPP [0%Z; 0%Z] [H9; H9]
    [mkE [(1%Z, 2%Z)] (DCmp CLe (DAdd (DV 0) (DV 2)) (DV 1)) [(0%nat, DAdd (DV 0) (DV 2))];
     mkE [(1%Z, 2%Z)] DTrue [(0%nat, DSub (DV 0) (DV 2))];
     mkE [(0%Z, H9)] DTrue [(1%nat, DV 2)]]
    [(DCmp CLe (DV 0) (DV 1), [(0%nat, DV 1)])].

Definition room_A : list Z := [0%Z; H9; 1%Z; 2%Z].

Definition cancels (a b : nat) : bool := Nat.eqb a 1 && Nat.eqb b 1.

Theorem room_frag : pfrag room_p room_A 2 2 = true /\
  mask room_p 0 = [true] /\ mask room_p 1 = [true] /\ mask room_p 2 = [false].
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem room_checks : pterm_check room_p room_A 18 1 = true /\ pcc1v_check room_p room_A 18 1 cancels = true.
Proof. split; vm_compute; reflexivity. Qed.

(* Cancellations commute at every state and all counts. *)
Theorem room_converges : forall s, PInBox room_p s ->
  forall es1 es2, tequiv (liftI (fun a b => cancels a b = true)) es1 es2 -> Forall (PEv room_p) es1 ->
  runT (prstep room_p 1) es1 s = runT (prstep room_p 1) es2 s.
Proof.
  destruct room_checks as [HT HC].
  exact (pbuild_sound room_p room_A 2 2 1 cancels (proj1 room_frag) HT HC).
Qed.

(* Two bookings do not commute one room below the cap (booked 2, cap 3, n = 1 and 2); booking and
   cancelling do not commute at a full house; lowering the cap and cancelling do not commute. *)
Theorem room_diverges :
  pgov room_p 1 0 [2%Z] (pgov room_p 1 0 [1%Z] [2%Z; 4%Z]) = [3%Z; 4%Z] /\
  pgov room_p 1 0 [1%Z] (pgov room_p 1 0 [2%Z] [2%Z; 4%Z]) = [4%Z; 4%Z] /\
  pgov room_p 1 1 [1%Z] (pgov room_p 1 0 [1%Z] [4%Z; 4%Z]) = [3%Z; 4%Z] /\
  pgov room_p 1 0 [1%Z] (pgov room_p 1 1 [1%Z] [4%Z; 4%Z]) = [4%Z; 4%Z] /\
  pgov room_p 1 1 [1%Z] (pgov room_p 1 2 [3%Z] [4%Z; 9%Z]) = [2%Z; 3%Z] /\
  pgov room_p 1 2 [3%Z] (pgov room_p 1 1 [1%Z] [4%Z; 9%Z]) = [3%Z; 3%Z].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The domain of a pair involving setcap is independent of the width of c's range: the joint box
   of (setcap, cancel) has 4 coordinates, each within 4 (W + 1) of an anchor. *)
Theorem room_setcap_domain : nv (jb room_p [2; 1]) = 4%nat /\ radius (jb room_p [2; 1]) 18 = 76%Z /\
  (length (RepS (jb room_p [2; 1]) room_A 18) <= (4 * 153) ^ 4)%nat.
Proof.
  split; [reflexivity | split; [reflexivity|]].
  destruct (pcc1_domain_size room_p room_A 2 2 2 1 18 (proj1 room_frag) ltac:(lia)) as [_ [_ H]]. exact H.
Qed.

(* ============================================================================================ *)
(* Boundaries: a parameter added to a value is exact, and its range is paid in the threshold.   *)
(* ============================================================================================ *)

(* ---- x := x + p with p kept as a coordinate does not keep the region relation, at any
   threshold. Variables x, w in [0, 10^9], z in [0, 1]; A(p), p in [0, 10^9]: if x <> w then
   x := x + p; B: if x = w then z := 1. For every W, the joint states (W + 1, 2W + 2, 0; W + 1) and
   (W + 1, 2W + 3, 0; W + 1) are in range and related at W, and CC1 of A and B fails at the first
   and holds at the second. ---- *)
Definition addw : pprog :=
  mkPP [0%Z; 0%Z; 0%Z] [H9; H9; 1%Z]
    [mkE [(0%Z, H9)] (DCmp CNe (DV 0) (DV 1)) [(0%nat, DAdd (DV 0) (DV 3))];
     mkE [] (DCmp CEq (DV 0) (DV 1)) [(2%nat, DL 1)]] [].

Definition addw_A : list Z := [0%Z; 1%Z; H9].

Lemma addw_stepA : forall x w z p,
  pgov addw 0 0 [p] [x; w; z] = if negb (Z.eqb x w) then [clampZ 0 H9 (x + p); w; z] else [x; w; z].
Proof. intros x w z p. reflexivity. Qed.

Lemma addw_stepB : forall x w z, pgov addw 0 1 [] [x; w; z] = if Z.eqb x w then [x; w; 1%Z] else [x; w; z].
Proof. intros x w z. reflexivity. Qed.

Theorem addw_no_threshold : forall W, (0 <= W <= 100000000)%Z ->
  PInBox addw [W + 1; W + 1 + (W + 1); 0]%Z /\ PInBox addw [W + 1; W + 1 + (W + 1) + 1; 0]%Z /\
  PArgs addw 0 [(W + 1)%Z] /\
  RelS W addw_A ([W + 1; W + 1 + (W + 1); 0] ++ [W + 1])%Z ([W + 1; W + 1 + (W + 1) + 1; 0] ++ [W + 1])%Z /\
  pgov addw 0 1 [] (pgov addw 0 0 [(W + 1)%Z] [W + 1; W + 1 + (W + 1); 0]%Z) <>
    pgov addw 0 0 [(W + 1)%Z] (pgov addw 0 1 [] [W + 1; W + 1 + (W + 1); 0]%Z) /\
  pgov addw 0 1 [] (pgov addw 0 0 [(W + 1)%Z] [W + 1; W + 1 + (W + 1) + 1; 0]%Z) =
    pgov addw 0 0 [(W + 1)%Z] (pgov addw 0 1 [] [W + 1; W + 1 + (W + 1) + 1; 0]%Z).
Proof.
  intros W HW.
  assert (C : clampZ 0 H9 (W + 1 + (W + 1)) = (W + 1 + (W + 1))%Z).
  { unfold clampZ, H9. destruct (Z.ltb_spec (W + 1 + (W + 1)) 0); [lia|]. destruct (Z.ltb_spec 1000000000 (W + 1 + (W + 1))); lia. }
  assert (E1 : Z.eqb (W + 1) (W + 1 + (W + 1)) = false) by (apply Z.eqb_neq; lia).
  assert (E2 : Z.eqb (W + 1) (W + 1 + (W + 1) + 1) = false) by (apply Z.eqb_neq; lia).
  assert (E3 : Z.eqb (W + 1 + (W + 1)) (W + 1 + (W + 1) + 1) = false) by (apply Z.eqb_neq; lia).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [reflexivity|]. intros [|[|[|i]]] Hi; unfold base, nv in Hi; simpl in Hi |- *; unfold H9; lia.
  - split; [reflexivity|]. intros [|[|[|i]]] Hi; unfold base, nv in Hi; simpl in Hi |- *; unfold H9; lia.
  - split; [reflexivity|]. intros [|i] Hi; simpl in Hi |- *; unfold H9; lia.
  - split; [reflexivity|]. intros x y Hx Hy. simpl in Hx, Hy.
    destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; destruct Hy as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
      cbn [fst snd]; unfold near, H9; lia.
  - rewrite addw_stepA, E1. simpl negb. cbv iota. rewrite C, addw_stepB, Z.eqb_refl, addw_stepB, E1, addw_stepA, E1.
    simpl negb. cbv iota. rewrite C. discriminate.
  - rewrite addw_stepA, E2. simpl negb. cbv iota. rewrite C, addw_stepB, E3, addw_stepB, E2, addw_stepA, E2.
    simpl negb. cbv iota. rewrite C. reflexivity.
Qed.

(* The fragment check refuses it unless the threshold covers p's range. *)
Theorem addw_refused : forall A gam mu, pfrag addw A gam mu = true -> (H9 <= 2 * (gam + mu))%Z.
Proof.
  intros A gam mu H. pose proof (exok_parts addw A gam mu H 0 0 ltac:(cbv; lia) ltac:(cbv; lia) eq_refl) as E.
  exact E.
Qed.

(* ---- The representative check, run on x := x + p with p a coordinate, passes and the registry
   diverges. Variables x in [1000, 10^9], w in [0, 10^6], z in [0, 1]; A(p), p in [1000, 10^6]:
   if x <> w then x := x + p; B: if x = w then z := 1. Anchors {0, 1, 1000, 10^6, 10^9}. At the
   threshold 0 the check of (A, B) passes over 7600 joint representatives (x + p = w needs w near
   2000, which is far from every anchor); at (1000, 2000, 0) with p = 1000 the orders give z = 1
   and z = 0. ---- *)
Definition addp : pprog :=
  mkPP [1000%Z; 0%Z; 0%Z] [H9; M6; 1%Z]
    [mkE [(1000%Z, M6)] (DCmp CNe (DV 0) (DV 1)) [(0%nat, DAdd (DV 0) (DV 3))];
     mkE [] (DCmp CEq (DV 0) (DV 1)) [(2%nat, DL 1)]] [].

Definition cx_A : list Z := [0%Z; 1%Z; 1000%Z; M6; H9].

Definition cx_I (a b : nat) : bool := Nat.eqb a 0 && Nat.eqb b 1.

Theorem addp_check_passes : length (RepS (jb addp [0; 1]) cx_A 0) = 7600%nat /\
  pcc1v_check addp cx_A 0 0 cx_I = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem addp_diverges : PInBox addp [1000%Z; 2000%Z; 0%Z] /\ PArgs addp 0 [1000%Z] /\
  pgov addp 0 1 [] (pgov addp 0 0 [1000%Z] [1000%Z; 2000%Z; 0%Z]) = [2000%Z; 2000%Z; 1%Z] /\
  pgov addp 0 0 [1000%Z] (pgov addp 0 1 [] [1000%Z; 2000%Z; 0%Z]) = [2000%Z; 2000%Z; 0%Z] /\
  ~ PCC1VBox addp 0 (fun a b => cx_I a b = true).
Proof.
  assert (B : PInBox addp [1000%Z; 2000%Z; 0%Z]) by (apply inboxb_spec; reflexivity).
  assert (Pa : PArgs addp 0 [1000%Z]).
  { split; [reflexivity|]. intros [|i] Hi; simpl in Hi |- *; [unfold M6; lia | lia]. }
  split; [exact B | split; [exact Pa | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]]].
  intros H. assert (Pb : PArgs addp 1 []) by (split; [reflexivity | intros i Hi; simpl in Hi; lia]).
  pose proof (H _ B eq_refl 0 1 ltac:(cbv; lia) ltac:(cbv; lia) eq_refl _ _ Pa Pb) as E.
  vm_compute in E. discriminate.
Qed.

Theorem addp_refused : forall A gam mu, pfrag addp A gam mu = true -> (M6 - 1000 <= 2 * (gam + mu))%Z.
Proof.
  intros A gam mu H. exact (exok_parts addp A gam mu H 0 0 ltac:(cbv; lia) ltac:(cbv; lia) eq_refl).
Qed.

(* ---- A sum of two parameters: x := p + q, p, q in [1000, 10^6], x in [0, 10^9], w in [0, 10^6]:
   A(p, q): if x <> w then x := p + q; B: if x = w then z := 1. The check of (A, B) at threshold 0
   passes over 241920 joint representatives; at (0, 2000, 0) with p = q = 1000 the orders give
   z = 1 and z = 0. ---- *)
Definition sum2_p : pprog :=
  mkPP [0%Z; 0%Z; 0%Z] [H9; M6; 1%Z]
    [mkE [(1000%Z, M6); (1000%Z, M6)] (DCmp CNe (DV 0) (DV 1)) [(0%nat, DAdd (DV 3) (DV 4))];
     mkE [] (DCmp CEq (DV 0) (DV 1)) [(2%nat, DL 1)]] [].

Theorem sum2_check_passes : pcc1v_check sum2_p cx_A 0 0 cx_I = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem sum2_diverges : PInBox sum2_p [0%Z; 2000%Z; 0%Z] /\
  pgov sum2_p 0 1 [] (pgov sum2_p 0 0 [1000%Z; 1000%Z] [0%Z; 2000%Z; 0%Z]) = [2000%Z; 2000%Z; 1%Z] /\
  pgov sum2_p 0 0 [1000%Z; 1000%Z] (pgov sum2_p 0 1 [] [0%Z; 2000%Z; 0%Z]) = [2000%Z; 2000%Z; 0%Z].
Proof. split; [apply inboxb_spec; reflexivity | split; vm_compute; reflexivity]. Qed.

Theorem sum2_refused : forall A gam mu, pfrag sum2_p A gam mu = true -> (M6 - 1000 <= 2 * (gam + mu))%Z.
Proof.
  intros A gam mu H. exact (exok_parts sum2_p A gam mu H 0 0 ltac:(cbv; lia) ltac:(cbv; lia) eq_refl).
Qed.

(* ---- An exact parameter's range must be paid in the threshold. x, y, z in [0, 100];
   A(p), p in [0, 15]: x := x + p; B: if x = y then z := z + 1. Anchors {0, 15, 100}. The joint
   states (20, 27, 0; 7) and (20, 27, 0; 8) are related at threshold 6 (p differs, 15 > 2 * 6),
   and CC1 of A and B fails at the first and holds at the second. The registry is in the fragment
   with mu = 15, whose threshold covers the range. ---- *)
Definition wide_p : pprog :=
  mkPP [0%Z; 0%Z; 0%Z] [100%Z; 100%Z; 100%Z]
    [mkE [(0%Z, 15%Z)] DTrue [(0%nat, DAdd (DV 0) (DV 3))];
     mkE [] (DCmp CEq (DV 0) (DV 1)) [(2%nat, DAdd (DV 2) (DL 1))]] [].

Definition wide_A : list Z := [0%Z; 15%Z; 100%Z].

Theorem exact_needs_width : pfrag wide_p wide_A 0 15 = true /\
  RelS 6 wide_A [20%Z; 27%Z; 0%Z; 7%Z] [20%Z; 27%Z; 0%Z; 8%Z] /\
  pgov wide_p 0 1 [] (pgov wide_p 0 0 [7%Z] [20%Z; 27%Z; 0%Z]) <>
    pgov wide_p 0 0 [7%Z] (pgov wide_p 0 1 [] [20%Z; 27%Z; 0%Z]) /\
  pgov wide_p 0 1 [] (pgov wide_p 0 0 [8%Z] [20%Z; 27%Z; 0%Z]) =
    pgov wide_p 0 0 [8%Z] (pgov wide_p 0 1 [] [20%Z; 27%Z; 0%Z]).
Proof.
  split; [vm_compute; reflexivity|]. split; [split; [reflexivity | apply relb_spec; vm_compute; reflexivity]|].
  split; [vm_compute; discriminate | vm_compute; reflexivity].
Qed.
