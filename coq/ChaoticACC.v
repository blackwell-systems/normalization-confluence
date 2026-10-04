(* ChaoticACC.v: the monotone regime under the ASCENDING CHAIN CONDITION instead of finite
   height, mechanized axiom-free.

   Chaotic.v proves that chaotic (asynchronous) iteration reaches the least fixed point using a
   rank : L -> nat that strictly increases along the strict order (finite height). Federation.v
   proves that once the Kleene iteration stabilizes, its value is the least fixed point, and
   assumes stabilization at a given n. This file removes both finiteness assumptions:

   - Chaotic iteration: it suffices that there is no infinite strictly ascending chain BELOW the
     least fixed point (well-foundedness of the converse of the strict order, restricted to
     elements below lfp). No rank. The finite-height theorem of Chaotic.v and the global ACC
     version are corollaries.
   - Kleene iteration: under ACC the iteration cannot strictly ascend forever (fully
     constructive, no further assumption), hence the existence of a stabilizing index is
     not-not true; and with a decision procedure for "f x = x" (the stabilization test, the only
     checking an implementation does) a stabilizing index and the least fixed point are
     COMPUTED, as a sigma type, by recursion on the accessibility proof. Finite height (a bounded
     rank) implies ACC, which recovers Federation.v's finite-lattice reading.

   Non-vacuity: option nat with None at the bottom and Some n ordered by REVERSE nat order
   (None < ... < Some 2 < Some 1 < Some 0) satisfies ACC, is infinite, and has strictly ascending
   chains of every finite length, so it has no finite height and admits NO strictly increasing
   rank into nat (proved). Its square, with a monotone two-component operator, discharges every
   hypothesis of the generalized chaotic and Kleene theorems. *)

Require Import NC.Newman NC.Federation NC.Chaotic.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Wellfounded.Inverse_Image.
From Coq Require Import Wellfounded.Inclusion.
From Coq Require Import Lia.

(* y lies strictly above x. ACC for le is: well_founded (ascends le). *)
Definition ascends {L : Type} (le : L -> L -> Prop) (y x : L) : Prop := le x y /\ x <> y.

(* y lies strictly above x and below the bound m. *)
Definition ascends_below {L : Type} (le : L -> L -> Prop) (m : L) (y x : L) : Prop :=
  le y m /\ ascends le y x.

(* ===================== Kleene iteration under ACC ===================== *)

Section KleeneACC.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable f : L -> L.
  Hypothesis f_mono : forall x y, le x y -> le (f x) (f y).
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  (* ACC: no infinite strictly ascending chain. *)
  Hypothesis acc : well_founded (ascends le).

  Lemma iter_not_forever_acc :
    (forall n, f (iter f bot n) <> iter f bot n) ->
    forall x, Acc (ascends le) x -> forall n, x <> iter f bot n.
  Proof.
    intros Hnever x Hacc. induction Hacc as [x _ IH]. intros n Hx. subst x.
    apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
    split.
    - apply (iter_ascending le f f_mono bot bot_least n).
    - intro E. apply (Hnever n). simpl in E. symmetry. exact E.
  Qed.

  (* Fully constructive: the Kleene iteration cannot strictly ascend forever. *)
  Theorem kleene_acc_not_forever : ~ (forall n, f (iter f bot n) <> iter f bot n).
  Proof.
    intro Hnever. apply (iter_not_forever_acc Hnever bot (acc bot) 0). reflexivity.
  Qed.

  (* Hence (still constructive, no decidability) a least fixed point cannot fail to exist. *)
  Corollary kleene_acc_lfp_nn : ~ ~ exists m, is_lfp le f m.
  Proof.
    intro Hno. apply kleene_acc_not_forever. intros n Hfix.
    apply Hno. exists (iter f bot n). apply (kleene_lfp le f f_mono bot bot_least n Hfix).
  Qed.

  (* With the stabilization test decidable, the index and the least fixed point are computed. *)
  Hypothesis stab_dec : forall x, {f x = x} + {f x <> x}.

  Theorem kleene_acc_stabilizes : {n : nat | f (iter f bot n) = iter f bot n}.
  Proof.
    assert (H : forall x, Acc (ascends le) x -> forall n, x = iter f bot n ->
                {m : nat | f (iter f bot m) = iter f bot m}).
    { intros x Hacc. induction Hacc as [x _ IH]. intros n Hx.
      destruct (stab_dec (iter f bot n)) as [E | NE].
      - exists n. exact E.
      - apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
        subst x. split.
        + apply (iter_ascending le f f_mono bot bot_least n).
        + intro E. apply NE. simpl in E. symmetry. exact E. }
    apply (H bot (acc bot) 0). reflexivity.
  Defined.

  Theorem kleene_acc_lfp : {m : L | is_lfp le f m}.
  Proof.
    destruct kleene_acc_stabilizes as [n Hn].
    exists (iter f bot n). apply (kleene_lfp le f f_mono bot bot_least n Hn).
  Defined.
End KleeneACC.

(* Finite height (a strictly increasing rank bounded by H) implies ACC. *)
Lemma finite_height_acc :
  forall {L : Type} (le : L -> L -> Prop) (rank : L -> nat) (H : nat),
    (forall x y, le x y -> x <> y -> rank x < rank y) ->
    (forall x, rank x <= H) ->
    well_founded (ascends le).
Proof.
  intros L le rank H Hstrict Hbound.
  apply (wf_incl _ _ (fun y x => H - rank y < H - rank x)).
  - intros y x [Hle Hne]. specialize (Hstrict x y Hle Hne). specialize (Hbound y). lia.
  - apply (wf_inverse_image _ _ lt (fun x => H - rank x) lt_wf).
Qed.

(* Federation.v's finite-lattice reading, recovered: under finite height the Kleene iteration
   stabilizes (computably, given the stabilization test) at the least fixed point. *)
Corollary kleene_finite_height_lfp :
  forall {L : Type} (le : L -> L -> Prop) (f : L -> L) (bot : L) (rank : L -> nat) (H : nat),
    (forall x y, le x y -> le (f x) (f y)) ->
    (forall x, le bot x) ->
    (forall x y, le x y -> x <> y -> rank x < rank y) ->
    (forall x, rank x <= H) ->
    (forall x, {f x = x} + {f x <> x}) ->
    {m : L | is_lfp le f m}.
Proof.
  intros L le f bot rank H Hmono Hbot Hstrict Hbound Hdec.
  exact (kleene_acc_lfp le f Hmono bot Hbot (finite_height_acc le rank H Hstrict Hbound) Hdec).
Defined.

(* ===================== Chaotic iteration under ACC ===================== *)

Section ChaoticACC.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.

  Variable F : L -> L.
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  Variable lfp : L.
  Hypothesis lfp_least : forall x, F x = x -> le lfp x.

  Variable I : Type.
  Variable update : I -> L -> L.
  Variable classicUpdate : forall i x, {update i x = x} + {update i x <> x}.

  Hypothesis up_incr  : forall i x, sound le F x -> le x (update i x).
  Hypothesis up_sound : forall i x, sound le F x -> sound le F (update i x).
  Hypothesis up_below : forall i x, le x lfp -> le (update i x) lfp.
  Hypothesis all_fixed : forall x, (forall i, update i x = x) -> F x = x.
  Hypothesis step_dec : forall x, {y | step I update x y} + {normal_form (step I update) x}.

  (* ACC below the least fixed point, in place of Chaotic.v's rank. *)
  Hypothesis acc_below : well_founded (ascends_below le lfp).

  Lemma step_ascends_below :
    forall x y, reachable le F lfp x -> step I update x y -> ascends_below le lfp y x.
  Proof.
    intros x y [Hs Hb] [i [-> Hne]]. split.
    - apply up_below; exact Hb.
    - split; [apply up_incr; exact Hs | exact Hne].
  Qed.

  Lemma reachable_step_acc :
    forall x y, reachable le F lfp x -> step I update x y -> reachable le F lfp y.
  Proof.
    intros x y [Hs Hb] [i [-> _]]. split; [apply up_sound | apply up_below]; assumption.
  Qed.

  Theorem chaotic_acc_terminates : forall x, reachable le F lfp x -> SN (step I update) x.
  Proof.
    intros x. pose proof (acc_below x) as Hacc. induction Hacc as [x _ IH]. intros Hx.
    constructor. intros y Hstep. apply IH.
    - apply step_ascends_below; assumption.
    - apply (reachable_step_acc x y); assumption.
  Qed.

  Theorem chaotic_acc_reaches_lfp : forall x, reachable le F lfp x -> star (step I update) x lfp.
  Proof.
    intros x. pose proof (acc_below x) as Hacc. induction Hacc as [x _ IH]. intros Hx.
    destruct (step_dec x) as [[y Hstep] | Hnf].
    - eapply star_step; [exact Hstep|].
      apply IH; [apply step_ascends_below; assumption | apply (reachable_step_acc x y); assumption].
    - rewrite (normal_is_lfp le le_antisym F lfp lfp_least I update classicUpdate all_fixed x Hx Hnf).
      apply star_refl.
  Qed.

  Corollary chaotic_acc_from_bot : star (step I update) bot lfp.
  Proof. apply chaotic_acc_reaches_lfp, (reachable_bot le F bot bot_least lfp). Qed.
End ChaoticACC.

(* Global ACC (no infinite ascending chain anywhere) implies ACC below the lfp. *)
Lemma acc_below_of_acc :
  forall {L : Type} (le : L -> L -> Prop) (m : L),
    well_founded (ascends le) -> well_founded (ascends_below le m).
Proof.
  intros L le m W. apply (wf_incl _ _ (ascends le)); [intros y x [_ H]; exact H | exact W].
Qed.

(* Chaotic.v's finite-height theorem, recovered: its rank gives ACC below the lfp. The statement
   is exactly the type of Chaotic.chaotic_reaches_lfp. *)
Corollary chaotic_reaches_lfp_from_acc :
  forall {L : Type} (le : L -> L -> Prop),
    (forall x y, le x y -> le y x -> x = y) ->
    forall (F : L -> L) (rank : L -> nat),
    (forall x y, le x y -> x <> y -> rank x < rank y) ->
    forall lfp : L,
    (forall x, F x = x -> le lfp x) ->
    forall (I : Type) (update : I -> L -> L),
    (forall i x, {update i x = x} + {update i x <> x}) ->
    (forall i x, sound le F x -> le x (update i x)) ->
    (forall i x, sound le F x -> sound le F (update i x)) ->
    (forall i x, le x lfp -> le (update i x) lfp) ->
    (forall x, (forall i, update i x = x) -> F x = x) ->
    (forall x, {y | step I update x y} + {normal_form (step I update) x}) ->
    forall x, reachable le F lfp x -> star (step I update) x lfp.
Proof.
  intros L le Hanti F rank Hstrict lfp Hleast I update Hcl Hincr Hsound Hbelow Hfixed Hdec.
  apply (chaotic_acc_reaches_lfp le Hanti F lfp Hleast I update Hcl Hincr Hsound Hbelow Hfixed Hdec).
  apply (wf_incl _ _ (fun y x => rank lfp - rank y < rank lfp - rank x)).
  - intros y x [Hyl [Hle Hne]].
    pose proof (Hstrict x y Hle Hne).
    pose proof (rank_mono le rank Hstrict y lfp Hyl). lia.
  - apply (wf_inverse_image _ _ lt (fun x => rank lfp - rank x) lt_wf).
Qed.

(* ============================================================
   Non-vacuity: an infinite lattice with ACC and no finite height.

   OL = option nat. None is the bottom; Some m <= Some n iff n <= m (reverse nat order); so the
   order is None < ... < Some 2 < Some 1 < Some 0. A strictly ascending chain from Some n has at
   most n + 1 elements, so there is no infinite ascending chain (ACC); but the chains
   None < Some n < Some (n-1) < ... < Some 0 have unbounded length, so the height is infinite and
   no strictly increasing rank into nat exists (ole_no_rank).
   ============================================================ *)

Definition OL := option nat.

Definition ole (x y : OL) : Prop :=
  match x, y with
  | None, _ => True
  | Some _, None => False
  | Some m, Some n => n <= m
  end.

Lemma ole_refl : forall x, ole x x.
Proof. intros [m|]; simpl; [lia | exact I]. Qed.

Lemma ole_trans : forall x y z, ole x y -> ole y z -> ole x z.
Proof. intros [a|] [b|] [c|]; simpl; intros; try lia; tauto. Qed.

Lemma ole_antisym : forall x y, ole x y -> ole y x -> x = y.
Proof.
  intros [a|] [b|]; simpl; intros H1 H2; try tauto.
  - f_equal; lia.
Qed.

Definition OL_eq_dec : forall x y : OL, {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Lemma ole_acc_some : forall n, Acc (ascends ole) (Some n).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf).
  constructor. intros [m|] [Hle Hne]; simpl in Hle.
  - apply IH. assert (m <> n) by (intro; subst; apply Hne; reflexivity). lia.
  - contradiction.
Qed.

Theorem ole_acc : well_founded (ascends ole).
Proof.
  intros [n|].
  - apply ole_acc_some.
  - constructor. intros [m|] [_ Hne]; [apply ole_acc_some | contradiction Hne; reflexivity].
Qed.

(* No finite height: no strictly increasing rank into nat exists, so Chaotic.v's hypotheses
   cannot be met on this lattice while the ACC versions can. *)
Theorem ole_no_rank :
  forall rank : OL -> nat, (forall x y, ole x y -> x <> y -> rank x < rank y) -> False.
Proof.
  intros rank Hstrict.
  assert (Hdesc : forall k, rank (Some k) + k <= rank (Some 0)).
  { induction k as [| k IH]; [lia|].
    assert (rank (Some (S k)) < rank (Some k)).
    { apply Hstrict; simpl; [lia | intro E; injection E; lia]. }
    lia. }
  specialize (Hdesc (S (rank (Some 0)))). lia.
Qed.

(* The square OL * OL, componentwise. *)
Definition PL := (OL * OL)%type.
Definition ple (x y : PL) : Prop := ole (fst x) (fst y) /\ ole (snd x) (snd y).

Lemma ple_antisym : forall x y, ple x y -> ple y x -> x = y.
Proof.
  intros [a b] [c d] [H1 H2] [H3 H4]; simpl in *.
  rewrite (ole_antisym a c H1 H3), (ole_antisym b d H2 H4). reflexivity.
Qed.

Definition PL_eq_dec : forall x y : PL, {x = y} + {x <> y}.
Proof. decide equality; apply OL_eq_dec. Defined.

Theorem ple_acc : well_founded (ascends ple).
Proof.
  assert (H : forall a, Acc (ascends ole) a -> forall b, Acc (ascends ole) b ->
              Acc (ascends ple) (a, b)).
  { intros a Ha. induction Ha as [a _ IHa]. intros b Hb. induction Hb as [b _ IHb].
    constructor. intros [c d] [[H1 H2] Hne]; simpl in *.
    destruct (OL_eq_dec a c) as [<- | Hac].
    - apply IHb. split; [exact H2 | intro E; subst; apply Hne; reflexivity].
    - apply IHa; [split; assumption | apply ole_acc]. }
  intros [a b]. apply H; apply ole_acc.
Qed.

Theorem ple_no_rank :
  forall rank : PL -> nat, (forall x y, ple x y -> x <> y -> rank x < rank y) -> False.
Proof.
  intros rank Hstrict. apply (ole_no_rank (fun a => rank (a, None))).
  intros x y Hle Hne. apply Hstrict.
  - split; [exact Hle | exact I].
  - intro E. injection E. exact Hne.
Qed.

(* A monotone operator: component 1 is capped at level k (any value at or above Some k in the
   order, i.e. index at most k, is kept; bottom jumps to Some k); component 2 copies component 1.
   Its least fixed point is (Some k, Some k). *)
Definition cap (k : nat) (a : OL) : OL :=
  match a with None => Some k | Some n => Some (Nat.min n k) end.

Lemma cap_mono : forall k a b, ole a b -> ole (cap k a) (cap k b).
Proof. intros k [m|] [n|]; simpl; intros H; try lia; tauto. Qed.

Lemma cap_incr_bound : forall k a, ole a (Some k) -> cap k a = Some k.
Proof. intros k [n|]; simpl; intros H; [f_equal; lia | reflexivity]. Qed.

Definition PF (k : nat) (x : PL) : PL := (cap k (fst x), fst x).

Lemma PF_mono : forall k x y, ple x y -> ple (PF k x) (PF k y).
Proof. intros k [a b] [c d] [H1 H2]; simpl in *. split; [apply cap_mono; exact H1 | exact H1]. Qed.

Definition pbot : PL := (None, None).
Lemma pbot_least : forall x, ple pbot x.
Proof. intros [a b]; split; exact I. Qed.

Definition plfp (k : nat) : PL := (Some k, Some k).

Lemma plfp_least : forall k x, PF k x = x -> ple (plfp k) x.
Proof.
  intros k [a b] E. unfold PF in E; simpl in E. injection E as E1 E2. subst b.
  destruct a as [n|]; simpl in *.
  - injection E1 as E1. split; simpl; lia.
  - discriminate.
Qed.

(* Components: true updates component 1, false updates component 2. *)
Definition pupd (k : nat) (i : bool) (x : PL) : PL :=
  if i then (cap k (fst x), snd x) else (fst x, fst x).

Lemma pupd_dec : forall k i x, {pupd k i x = x} + {pupd k i x <> x}.
Proof. intros; apply PL_eq_dec. Qed.

Lemma pup_incr : forall k i x, sound ple (PF k) x -> ple x (pupd k i x).
Proof.
  intros k i [a b] [H1 H2]; simpl in *. destruct i; simpl.
  - split; [exact H1 | apply ole_refl].
  - split; [apply ole_refl | exact H2].
Qed.

Lemma pup_sound : forall k i x, sound ple (PF k) x -> sound ple (PF k) (pupd k i x).
Proof.
  intros k i [a b] [H1 H2]; simpl in *. unfold sound, ple, PF. destruct i; simpl.
  - split; [apply cap_mono; exact H1 | apply (ole_trans _ a); assumption].
  - split; [exact H1 | apply ole_refl].
Qed.

Lemma pup_below : forall k i x, ple x (plfp k) -> ple (pupd k i x) (plfp k).
Proof.
  intros k i [a b] [H1 H2]; simpl in *. destruct i; simpl.
  - rewrite (cap_incr_bound k a H1). split; [apply ole_refl | exact H2].
  - split; exact H1.
Qed.

Lemma pall_fixed : forall k x, (forall i, pupd k i x = x) -> PF k x = x.
Proof.
  intros k [a b] H. pose proof (H true) as Ht. pose proof (H false) as Hf.
  simpl in Ht, Hf. injection Ht as Ht. injection Hf as Hf. subst b.
  unfold PF; simpl. rewrite Ht. reflexivity.
Qed.

Lemma pstep_dec :
  forall k x, {y | step bool (pupd k) x y} + {normal_form (step bool (pupd k)) x}.
Proof.
  intros k x.
  destruct (PL_eq_dec (pupd k true x) x) as [Et | Nt].
  - destruct (PL_eq_dec (pupd k false x) x) as [Ef | Nf].
    + right. intros [y [i [-> Hne]]]. destruct i; [rewrite Et in Hne | rewrite Ef in Hne];
        apply Hne; reflexivity.
    + left. exists (pupd k false x). exists false. split; [reflexivity | intro E; apply Nf; symmetry; exact E].
  - left. exists (pupd k true x). exists true. split; [reflexivity | intro E; apply Nt; symmetry; exact E].
Qed.

(* On the infinite, infinite-height lattice PL, for every cap k, every productive chaotic
   schedule from bottom reaches the least fixed point (Some k, Some k): ACC suffices. *)
Theorem pl_chaotic_reaches_lfp :
  forall k x, reachable ple (PF k) (plfp k) x -> star (step bool (pupd k)) x (plfp k).
Proof.
  intros k.
  exact (chaotic_acc_reaches_lfp ple ple_antisym (PF k) (plfp k) (plfp_least k) bool (pupd k)
           (pupd_dec k) (pup_incr k) (pup_sound k) (pup_below k) (pall_fixed k) (pstep_dec k)
           (acc_below_of_acc ple (plfp k) ple_acc)).
Qed.

Corollary pl_chaotic_from_bot : forall k, star (step bool (pupd k)) pbot (plfp k).
Proof.
  intros k. apply pl_chaotic_reaches_lfp. apply (reachable_bot ple (PF k) pbot pbot_least).
Qed.

(* On the same lattice, the Kleene iteration of PF k from bottom computes a least fixed point. *)
Definition pl_kleene_lfp (k : nat) : {m : PL | is_lfp ple (PF k) m} :=
  kleene_acc_lfp ple (PF k) (PF_mono k) pbot pbot_least ple_acc (fun x => PL_eq_dec (PF k x) x).

Theorem pl_kleene_lfp_value : forall k, proj1_sig (pl_kleene_lfp k) = plfp k.
Proof.
  intros k. destruct (pl_kleene_lfp k) as [m [Hfix Hleast]]; simpl.
  apply ple_antisym.
  - apply Hleast. unfold fixed_point, PF, plfp; simpl. rewrite Nat.min_id. reflexivity.
  - apply plfp_least. exact Hfix.
Qed.

(* The recovered statement is Chaotic.v's statement (the two types unify syntactically). *)
Goal True.
Proof.
  let t1 := type of @Chaotic.chaotic_reaches_lfp in
  let t2 := type of @chaotic_reaches_lfp_from_acc in unify t1 t2.
  exact I.
Qed.
