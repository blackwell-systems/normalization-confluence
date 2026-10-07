(* ProjectionChains.v: versioned projection channels beyond two-level networks (REGIME-AUDIT.md
   gap 21, residue (a)). Axiom-free.

   The question. ProjectionChannels.v proves, for channels that deliver projections late,
   reordered or duplicated and gsm's versioned merge (MergeProjectionAfter), that the exact
   condition is XU at every CHANNEL-reachable state (CXUR true, chan_exact, vsettle_exact_cond),
   and that on two-level networks this is XU at every state of the current-value model (XUR), the
   condition of DistributedExact.dist_exact (vchan_twolevel_exact). Does CXUR true = XUR hold on
   every acyclic network, with chains (a projection of a projection) and targets with several
   sources? It does exactly when the channels reach no stale combination the current-value model
   cannot produce.

   Model. That of ProjectionChannels.v (a send snapshots the whole state; a delivery merges the
   snapshot at the target; disciplined versions). Rch y x: x is y or reads, through registries of
   o, a registry Rch-reachable from y ("x is below y"). rt marks pure roots (repair the identity).
     Nested src o rt : whenever a registry y that is not a pure root lies above a target j that is
                       not a pure root (Rch y j, y <> j), every source of j is below y too.
   Two-level networks are nested (twolevel_nested); so is every network whose targets have at
   most one source, chains and trees of any depth, with no pure root marked (single_nested).

   Results.
     vchan_nested_emulate : on a nested network, every state a disciplined versioned channel run
                            reaches is, at every registry, the state of a current-value run. The
                            invariant places every live projection at a position of a
                            current-value word (its snapshot's sources there, nothing below its
                            target after it), positions monotone in the version and along the
                            network; an event or an applied projection of r is inserted after the
                            last action touching r and the positions of r's readers.
     cxur_nested          : CXUR true s0 <-> XUR s0 on a nested network.
     vchan_nested_exact   : ChanConv true s0 <-> XUR s0 /\ C2R (N s0), SettleConv s0 <-> the same,
                            and SettleConv s0 <-> DistConv s0: dist_exact's condition, unchanged.
     vchan_single_exact   : the same for single-source networks (gsm's certified projection
                            deployments: acyclic, every target with one source).
     vchan_twolevel_exact_recovered : ProjectionChannels.vchan_twolevel_exact as a corollary.
   Beyond nested networks the equality fails.
     vchan_skip_counterexample : four registries, 1 reads 0, 2 reads 0 and 1, 3 reads 1 and 2
                            (2 lies above 3, but 3's source 1 is not below 2; not nested for any
                            marking of pure roots). From a start where 1 holds a stale flag, the
                            current-value model never shows registry 3 "1 unset while 2 saw 0 and
                            1 both set" (an invariant), so reachable XU holds and DistConv holds;
                            a disciplined versioned run (1's projection delivered after 0 flips
                            and after 2 applied the fresh pair) shows it, XU fails there, and
                            ChanConv true, SettleConv and CXUR true all fail. gsm's static XU
                            (ProjectionSafe) rejects the event, so the certificate is unaffected.
     chain_instance       : non-vacuity, a chain 0 -> 1 -> 2 (not two-level for any marking)
                            where the single-source theorem applies, SettleConv and DistConv hold.
   Not covered: whether the equality holds on non-nested networks that do not contain the pattern
   of vchan_skip_counterexample (a diamond, a target reading a root and a chain); the exact
   network class remains open between Nested and that pattern. Static XU + C2 stays sufficient on
   every acyclic network (ProjectionChannels.vsettle_xu_c2), and chan_exact_global is the
   every-start condition on every acyclic network.

   States are compared pointwise (feq); no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.FederationEvents NC.FederationEventsConverse NC.FederationGRS.
Require Import NC.DistributedExact NC.ProjectionChannels.
Import ListNotations.

(* ---------------------------------------------------------------------------------- *)
(* List helpers (stated here so the file builds on Coq 8.18 through Rocq 9.3).         *)
(* ---------------------------------------------------------------------------------- *)

Section Lists.
  Variable A : Type.

  Definition ins (q : nat) (a : A) (w : list A) : list A := firstn q w ++ a :: skipn q w.

  Lemma pc_len_app : forall (l r : list A), length (l ++ r) = length l + length r.
  Proof. intros l r. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma pc_firstn_all : forall (l : list A), firstn (length l) l = l.
  Proof. intros l. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma pc_firstn_len : forall n (l : list A), n <= length l -> length (firstn n l) = n.
  Proof.
    induction n as [| n IH]; intros [| x l] H; simpl in *; try reflexivity; try lia.
    rewrite IH by lia. reflexivity.
  Qed.

  Lemma pc_skipn_len : forall n (l : list A), length (skipn n l) = length l - n.
  Proof.
    induction n as [| n IH]; intros [| x l]; simpl; try reflexivity; try lia. apply IH.
  Qed.

  Lemma pc_firstn_skipn : forall n (l : list A), firstn n l ++ skipn n l = l.
  Proof.
    induction n as [| n IH]; intros [| x l]; simpl; try reflexivity. rewrite IH. reflexivity.
  Qed.

  Lemma pc_firstn_app_le : forall n (l r : list A), n <= length l -> firstn n (l ++ r) = firstn n l.
  Proof.
    induction n as [| n IH]; intros [| x l] r H; simpl in *; try reflexivity; try lia.
    rewrite IH by lia. reflexivity.
  Qed.

  Lemma pc_firstn_app_ge : forall n (l r : list A), length l <= n ->
    firstn n (l ++ r) = l ++ firstn (n - length l) r.
  Proof.
    induction n as [| n IH]; intros l r H.
    - destruct l; simpl in *; [reflexivity | lia].
    - destruct l as [| x l]; simpl in *; [reflexivity | rewrite IH by lia; reflexivity].
  Qed.

  Lemma pc_skipn_app_le : forall n (l r : list A), n <= length l -> skipn n (l ++ r) = skipn n l ++ r.
  Proof.
    induction n as [| n IH]; intros [| x l] r H; simpl in *; try reflexivity; try lia.
    apply IH. lia.
  Qed.

  Lemma pc_skipn_app_ge : forall n (l r : list A), length l <= n ->
    skipn n (l ++ r) = skipn (n - length l) r.
  Proof.
    induction n as [| n IH]; intros [| x l] r H; simpl in *; try reflexivity; try lia.
    apply IH. lia.
  Qed.

  Lemma pc_firstn_firstn_le : forall n m (l : list A), n <= m -> firstn n (firstn m l) = firstn n l.
  Proof.
    induction n as [| n IH]; intros [| m] [| x l] H; simpl; try reflexivity; try lia.
    rewrite IH by lia. reflexivity.
  Qed.

  Lemma pc_firstn_split : forall q p (l : list A), q <= p ->
    firstn p l = firstn q l ++ firstn (p - q) (skipn q l).
  Proof.
    induction q as [| q IH]; intros p l H.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
    - destruct p as [| p]; [lia |]. destruct l as [| x l]; simpl; [destruct (p - q); reflexivity |].
      rewrite (IH p l) by lia. reflexivity.
  Qed.

  Lemma pc_skipn_skipn : forall q p (l : list A), q <= p -> skipn p l = skipn (p - q) (skipn q l).
  Proof.
    induction q as [| q IH]; intros p l H.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
    - destruct p as [| p]; [lia |]. destruct l as [| x l]; simpl; [destruct (p - q); reflexivity |].
      apply IH. lia.
  Qed.

  Lemma pc_Forall_skipn : forall (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
  Proof.
    intros P n. induction n as [| n IH]; intros [| x l] H; simpl; try exact H; try constructor.
    apply IH. inversion H; assumption.
  Qed.

  Lemma pc_Forall_firstn : forall (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
  Proof.
    intros P n. induction n as [| n IH]; intros [| x l] H; simpl; try constructor.
    - inversion H; assumption.
    - apply IH. inversion H; assumption.
  Qed.

  Lemma ins_len : forall q a w, q <= length w -> length (ins q a w) = S (length w).
  Proof.
    intros q a w H. unfold ins. rewrite pc_len_app. simpl. rewrite pc_firstn_len, pc_skipn_len by exact H.
    lia.
  Qed.

  Lemma ins_firstn_le : forall q a w p, p <= q -> q <= length w -> firstn p (ins q a w) = firstn p w.
  Proof.
    intros q a w p Hp Hq. unfold ins.
    rewrite pc_firstn_app_le by (rewrite pc_firstn_len by exact Hq; exact Hp).
    apply pc_firstn_firstn_le. exact Hp.
  Qed.

  Lemma ins_firstn_gt : forall q a w p, q <= p -> q <= length w ->
    firstn (S p) (ins q a w) = firstn q w ++ a :: firstn (p - q) (skipn q w).
  Proof.
    intros q a w p Hp Hq. unfold ins.
    rewrite pc_firstn_app_ge by (rewrite pc_firstn_len by exact Hq; lia).
    rewrite pc_firstn_len by exact Hq. replace (S p - q) with (S (p - q)) by lia. reflexivity.
  Qed.

  Lemma ins_skipn_le : forall q a w p, p <= q -> q <= length w ->
    skipn p (ins q a w) = skipn p (firstn q w) ++ a :: skipn q w.
  Proof.
    intros q a w p Hp Hq. unfold ins.
    apply pc_skipn_app_le. rewrite pc_firstn_len by exact Hq. exact Hp.
  Qed.

  Lemma ins_skipn_gt : forall q a w p, q <= p -> q <= length w ->
    skipn (S p) (ins q a w) = skipn p w.
  Proof.
    intros q a w p Hp Hq. unfold ins.
    rewrite pc_skipn_app_ge by (rewrite pc_firstn_len by exact Hq; lia).
    rewrite pc_firstn_len by exact Hq. replace (S p - q) with (S (p - q)) by lia. simpl.
    symmetry. apply pc_skipn_skipn. exact Hp.
  Qed.

  Lemma ins_Forall : forall (P : A -> Prop) q a w, Forall P w -> P a -> Forall P (ins q a w).
  Proof.
    intros P q a w Hw Ha. unfold ins. apply Forall_app. split; [apply pc_Forall_firstn; exact Hw |].
    constructor; [exact Ha | apply pc_Forall_skipn; exact Hw].
  Qed.

  (* Minimum and maximum of a list, with a default. *)
  Definition minl (d : nat) (l : list nat) : nat := fold_right Nat.min d l.
  Definition maxl (d : nat) (l : list nat) : nat := fold_right Nat.max d l.

  Lemma minl_le_d : forall d l, minl d l <= d.
  Proof. intros d l. induction l as [| x l IH]; simpl; lia. Qed.

  Lemma minl_le : forall d l x, In x l -> minl d l <= x.
  Proof.
    intros d l. induction l as [| y l IH]; intros x H; [destruct H |].
    destruct H as [<- | H]; simpl; [lia |]. specialize (IH x H). lia.
  Qed.

  Lemma minl_ge : forall d l b, b <= d -> (forall x, In x l -> b <= x) -> b <= minl d l.
  Proof.
    intros d l b Hd. induction l as [| y l IH]; intros H; simpl; [exact Hd |].
    pose proof (H y (or_introl eq_refl)). assert (b <= minl d l) by (apply IH; intros; apply H; right; assumption).
    lia.
  Qed.

  Lemma maxl_ge_d : forall d l, d <= maxl d l.
  Proof. intros d l. induction l as [| x l IH]; simpl; lia. Qed.

  Lemma maxl_ge : forall d l x, In x l -> x <= maxl d l.
  Proof.
    intros d l. induction l as [| y l IH]; intros x H; [destruct H |].
    destruct H as [<- | H]; simpl; [lia |]. specialize (IH x H). lia.
  Qed.

  Lemma maxl_le : forall d l b, d <= b -> (forall x, In x l -> x <= b) -> maxl d l <= b.
  Proof.
    intros d l b Hd. induction l as [| y l IH]; intros H; simpl; [exact Hd |].
    pose proof (H y (or_introl eq_refl)). assert (maxl d l <= b) by (apply IH; intros; apply H; right; assumption).
    lia.
  Qed.
End Lists.

Arguments ins {A} _ _ _.

(* ---------------------------------------------------------------------------------- *)
(* Reachability in the network and insertion into a current-value word.               *)
(* ---------------------------------------------------------------------------------- *)

Definition actor {E : Type} (reg : E -> nat) (a : act E) : nat :=
  match a with DEv _ e => reg e | DProp _ j => j end.

Section Reach.
  Variable src : nat -> list nat.
  Variable o : list nat.

  (* Rch y x: x is y, or x reads (through registries of o) a registry Rch-reachable from y. *)
  Inductive Rch (y : nat) : nat -> Prop :=
  | rch_refl : Rch y y
  | rch_step : forall x z, In x o -> In z (src x) -> Rch y z -> Rch y x.

  Fixpoint idx (a : nat) (l : list nat) : nat :=
    match l with [] => 0 | b :: l' => if Nat.eqb a b then 0 else S (idx a l') end.

  Lemma rch_inv : forall y x, Rch y x -> x = y \/ exists z, In x o /\ In z (src x) /\ Rch y z.
  Proof.
    intros y x H. destruct H as [| x z Hx Hz H]; [left; reflexivity |]. right. exists z. tauto.
  Qed.

  Lemma rch_trans : forall x y z, Rch x y -> Rch y z -> Rch x z.
  Proof.
    intros x y z H1 H2. induction H2 as [| w u Hw Hu H IH]; [exact H1 |].
    eapply rch_step; eassumption.
  Qed.

  Hypothesis Ho : topoF src o.

  Lemma topo_idx_l : forall l x z, topoF src l -> In x l -> In z (src x) -> In z l -> idx z l < idx x l.
  Proof.
    induction l as [| a l IH]; intros x z Ht Hx Hz Hzl; [destruct Hx |].
    destruct Ht as [Ha [Hs Hr]].
    destruct Hx as [<- | Hx]; [exfalso; exact (Hs z Hz Hzl) |].
    assert (Nx : x <> a) by (intro E'; subst; contradiction).
    simpl. destruct (Nat.eqb x a) eqn:Ex; [apply Nat.eqb_eq in Ex; contradiction |].
    destruct (Nat.eqb z a) eqn:Ez; [lia |].
    destruct Hzl as [Hza | Hzl]; [subst; rewrite Nat.eqb_refl in Ez; discriminate |].
    pose proof (IH x z Hr Hx Hz Hzl). lia.
  Qed.

  Lemma rch_order : forall y x, Rch y x -> x = y \/ (In x o /\ (~ In y o \/ idx y o < idx x o)).
  Proof.
    intros y x H. induction H as [| x z Hx Hz H IH]; [left; reflexivity |]. right. split; [exact Hx |].
    destruct IH as [-> | [Hzo Hy]].
    - destruct (in_dec Nat.eq_dec y o) as [Hyo | Hyo]; [right | left; exact Hyo].
      exact (topo_idx_l o x y Ho Hx Hz Hyo).
    - pose proof (topo_idx_l o x z Ho Hx Hz Hzo). destruct Hy as [Hy | Hy]; [left; exact Hy | right; lia].
  Qed.

  Lemma rch_antisym : forall x y, Rch x y -> Rch y x -> x = y.
  Proof.
    intros x y H1 H2. destruct (rch_order x y H1) as [-> | [Hy1 Hx1]]; [reflexivity |].
    destruct (rch_order y x H2) as [-> | [Hx2 Hy2]]; [reflexivity |].
    destruct Hx1 as [Hx1 | Hx1]; [contradiction |]. destruct Hy2 as [Hy2 | Hy2]; [contradiction |]. lia.
  Qed.

  (* A reader of a registry is never Rch-below... the registry it reads. *)
  Lemma rch_reader : forall x r, In x o -> In r (src x) -> ~ Rch x r.
  Proof.
    intros x r Hx Hr H. assert (Rch r x) by (apply (rch_step r x r Hx Hr); constructor).
    assert (x = r) by (apply rch_antisym; assumption). subst.
    exact (topo_noself src o r Ho Hx Hr).
  Qed.

  Lemma exists_dec : forall (P : nat -> Prop) (l : list nat), (forall z, In z l -> {P z} + {~ P z}) ->
    {exists z, In z l /\ P z} + {~ exists z, In z l /\ P z}.
  Proof.
    intros P l. induction l as [| a l IH]; intros D.
    - right. intros [z [[] _]].
    - destruct (D a (or_introl eq_refl)) as [Ha | Ha]; [left; exists a; split; [left; reflexivity | exact Ha] |].
      destruct (IH (fun z Hz => D z (or_intror Hz))) as [Hex | Hn].
      + left. destruct Hex as [z [Hz Pz]]. exists z. split; [right; exact Hz | exact Pz].
      + right. intros [z [[<- | Hz] Pz]]; [contradiction | apply Hn; exists z; split; assumption].
  Qed.

  Definition msr (x : nat) : nat := if in_dec Nat.eq_dec x o then S (idx x o) else 0.

  Lemma rch_dec_n : forall y n x, msr x < n -> {Rch y x} + {~ Rch y x}.
  Proof.
    intros y n. induction n as [| n IH]; intros x Hm; [lia |].
    destruct (Nat.eq_dec x y) as [-> | Ne]; [left; constructor |].
    destruct (in_dec Nat.eq_dec x o) as [Hx | Hx].
    - assert (D : forall z, In z (src x) -> {Rch y z} + {~ Rch y z}).
      { intros z Hz. apply IH. unfold msr in *. destruct (in_dec Nat.eq_dec x o) as [_ | C]; [| contradiction].
        destruct (in_dec Nat.eq_dec z o) as [Hzo | Hzo]; [| lia].
        pose proof (topo_idx_l o x z Ho Hx Hz Hzo). lia. }
      destruct (exists_dec (Rch y) (src x) D) as [Hex | Hn].
      + left. destruct Hex as [z [Hz Hr]]. exact (rch_step y x z Hx Hz Hr).
      + right. intros H. destruct (rch_inv y x H) as [E' | [z [_ [Hz Hr]]]]; [contradiction |].
        apply Hn. exists z. split; assumption.
    - right. intros H. destruct (rch_inv y x H) as [E' | [z [Hxo _]]]; contradiction.
  Qed.

  Definition rch_dec (y x : nat) : {Rch y x} + {~ Rch y x} := rch_dec_n y (S (msr x)) x (Nat.lt_succ_diag_r _).

  Definition rchb (y x : nat) : bool := if rch_dec y x then true else false.

  Lemma rchb_true : forall y x, rchb y x = true <-> Rch y x.
  Proof. intros y x. unfold rchb. destruct (rch_dec y x); split; intros; congruence. Qed.

  Lemma rchb_false : forall y x, rchb y x = false <-> ~ Rch y x.
  Proof. intros y x. unfold rchb. destruct (rch_dec y x); split; intros; try congruence; contradiction. Qed.

End Reach.

Section Ins.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.

  Local Notation dF := (drun V f E reg sig).
  Local Notation actor := (actor reg).

  (* An action leaves r alone: it is not r's, and its registry does not read r. *)
  Definition NoTouch (r : nat) (a : act E) : Prop := actor a <> r /\ ~ In r (src (actor a)).

  Hypothesis Hloc : forall j z1 z2 x, (forall k, In k (src j) -> z1 k = z2 k) -> f j z1 x = f j z2 x.

  Lemma dF_agree : forall S r t t', Forall (NoTouch r) S -> (forall k, k <> r -> t k = t' k) ->
    (forall k, k <> r -> dF S t k = dF S t' k) /\ dF S t r = t r /\ dF S t' r = t' r.
  Proof.
    induction S as [| a S IH]; intros r t t' HS Ht; [split; [exact Ht | split; reflexivity] |].
    inversion HS as [| ? ? [Ha1 Ha2] HS']; subst. cbn [drun].
    assert (Ag : forall k, k <> r -> dstep V f E reg sig a t k = dstep V f E reg sig a t' k).
    { intros k Hk. destruct a as [e | j]; simpl in Ha1, Ha2 |- *.
      - unfold evstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply Ht; exact Hk].
        rewrite (Ht (reg e) Ha1). reflexivity.
      - unfold fstep, upd. destruct (Nat.eqb k j) eqn:Ek; [| apply Ht; exact Hk].
        rewrite (Ht j Ha1). apply Hloc. intros z Hz. apply Ht. intro E'. subst. contradiction. }
    assert (Ar : forall u, dstep V f E reg sig a u r = u r).
    { intros u. destruct a as [e | j]; simpl in Ha1 |- *.
      - unfold evstep. apply (upd_neq V). intro E'. apply Ha1. symmetry. exact E'.
      - unfold fstep. apply (upd_neq V). intro E'. apply Ha1. symmetry. exact E'. }
    destruct (IH r _ _ HS' Ag) as [A1 [A2 A3]].
    split; [exact A1 |]. rewrite A2, A3, !Ar. split; reflexivity.
  Qed.

  (* Inserting an action of r into a current-value word, where nothing after the insertion point
     is r's or reads r: every other registry is unchanged at every later prefix. *)
  Lemma ins_state : forall q a W s, q <= length W -> Forall (NoTouch (actor a)) (skipn q W) ->
    forall p, q <= p -> p <= length W ->
      (forall k, k <> actor a -> dF (firstn (S p) (ins q a W)) s k = dF (firstn p W) s k) /\
      dF (firstn (S p) (ins q a W)) s (actor a) = dstep V f E reg sig a (dF (firstn q W) s) (actor a) /\
      dF (firstn p W) s (actor a) = dF (firstn q W) s (actor a).
  Proof.
    intros q a W s Hq Hn p Hp HpW.
    rewrite (ins_firstn_gt _ q a W p Hp Hq). rewrite (pc_firstn_split _ q p W Hp).
    rewrite !(drun_app V f E reg sig). cbn [drun].
    set (t := dF (firstn q W) s).
    assert (HS : Forall (NoTouch (actor a)) (firstn (p - q) (skipn q W))) by (apply pc_Forall_firstn; exact Hn).
    assert (Ht : forall k, k <> actor a -> dstep V f E reg sig a t k = t k).
    { intros k Hk. destruct a as [e | j]; simpl in Hk |- *.
      - unfold evstep. apply (upd_neq V). exact Hk.
      - unfold fstep. apply (upd_neq V). exact Hk. }
    destruct (dF_agree _ (actor a) _ _ HS Ht) as [A1 [A2 A3]].
    split; [exact A1 |]. split; [exact A2 | exact A3].
  Qed.

  Lemma ins_state_full : forall q a W s, q <= length W -> Forall (NoTouch (actor a)) (skipn q W) ->
    (forall k, k <> actor a -> dF (ins q a W) s k = dF W s k) /\
    dF (ins q a W) s (actor a) = dstep V f E reg sig a (dF (firstn q W) s) (actor a) /\
    dF W s (actor a) = dF (firstn q W) s (actor a).
  Proof.
    intros q a W s Hq Hn.
    assert (L : length (ins q a W) = S (length W)) by (apply ins_len; exact Hq).
    destruct (ins_state q a W s Hq Hn (length W) Hq (le_n _)) as [A1 [A2 A3]].
    assert (F1 : firstn (S (length W)) (ins q a W) = ins q a W)
      by (rewrite <- L; apply pc_firstn_all).
    assert (F2 : firstn (length W) W = W) by apply pc_firstn_all.
    rewrite F1, F2 in A1. rewrite F1 in A2. rewrite F2 in A3.
    split; [exact A1 |]. split; [exact A2 | exact A3].
  Qed.
End Ins.

(* ---------------------------------------------------------------------------------- *)
(* Nested networks: every versioned channel state is a current-value state.            *)
(* ---------------------------------------------------------------------------------- *)

Section NestedSec.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  Variable o : list nat.

  Hypothesis HC : Common V src f valid rho E reg sig o.

  Local Notation dF := (drun V f E reg sig).
  Local Notation okF := (okact E o).
  Local Notation actorF := (actor reg).
  Local Notation RchF := (Rch src o).
  Local Notation cfgC := (cfg V).
  Local Notation csC := (cs V).
  Local Notation cbC := (cb V).
  Local Notation clC := (cl V).
  Local Notation cvC := (cv V).
  Local Notation cstepT := (cstep V f E reg sig true).
  Local Notation crunT := (crun V f E reg sig true).
  Local Notation discT := (disc V f E reg sig true).
  Local Notation okcF := (okc E o).
  Local Notation NoT := (NoTouch src E reg).

  Lemma Ho : topoF src o.
  Proof. exact (c_topo _ _ _ _ _ _ _ _ _ HC). Qed.

  Local Notation rchbF := (rchb src o Ho).

  (* rt marks pure roots (repair is the identity); their projections change nothing. *)
  Variable rt : nat -> bool.
  Hypothesis HR : forall k, rt k = true -> forall z x, f k z x = x.

  (* Nested: whenever a registry y (not a pure root) lies above a target j (not a pure root), so
     does every source of j. *)
  Definition Nested : Prop :=
    forall j y k, In j o -> rt j = false -> rt y = false -> y <> j -> RchF y j -> In k (src j) -> RchF y k.

  Hypothesis HN : Nested.

  Definition Live (c : cfgC) (y : nat) (m : msg V) : Prop :=
    In m (cbC c y) /\ clC c y < fst m /\ rt y = false.

  (* The emulation invariant: a current-value word W reaches the channel state; every live
     projection in flight to y has a position P y v in W where its sources' values are the
     snapshot's and after which nothing below y acts; positions are monotone in the version and
     along the network. *)
  Definition EmuN (s0 : nat -> V) (c : cfgC) (W : list (act E)) (P : nat -> nat -> nat) : Prop :=
    Forall okF W /\ (forall k, dF W s0 k = csC c k) /\
    (forall y m, In m (cbC c y) -> In y o) /\
    (forall y m, Live c y m -> P y (fst m) <= length W /\
       forall k, In k (src y) -> snd m k = dF (firstn (P y (fst m)) W) s0 k) /\
    (forall y m, Live c y m -> Forall (fun a => ~ RchF y (actorF a)) (skipn (P y (fst m)) W)) /\
    (forall y m1 m2, Live c y m1 -> Live c y m2 -> fst m1 < fst m2 -> P y (fst m1) <= P y (fst m2)) /\
    (forall x y mx my, Live c x mx -> Live c y my -> x <> y -> RchF y x -> P x (fst mx) <= P y (fst my)).

  Lemma actor_in : forall a, okF a -> In (actorF a) o.
  Proof. intros [e | j] H; simpl in *; [exact (c_reg _ _ _ _ _ _ _ _ _ HC e) | exact H]. Qed.

  Lemma Forall_skipn_mono : forall (Q : act E -> Prop) W p q, p <= q -> Forall Q (skipn p W) -> Forall Q (skipn q W).
  Proof.
    intros Q W p q H Hf. rewrite (pc_skipn_skipn _ p q W H). apply pc_Forall_skipn. exact Hf.
  Qed.

  (* Removing projections in flight (or raising the last applied version) keeps the invariant. *)
  Lemma emu_shrink : forall s0 c c' W P, (forall k, csC c' k = csC c k) ->
    (forall y m, In m (cbC c' y) -> In m (cbC c y)) -> (forall y m, Live c' y m -> Live c y m) ->
    EmuN s0 c W P -> EmuN s0 c' W P.
  Proof.
    intros s0 c c' W P Hs Hb Hl [O [S0 [B [E1 [E2 [E3 E4]]]]]].
    split; [exact O |]. split; [intros k; rewrite Hs; apply S0 |].
    split; [intros y m Hm; exact (B y m (Hb y m Hm)) |].
    split; [intros y m Hm; exact (E1 y m (Hl y m Hm)) |].
    split; [intros y m Hm; exact (E2 y m (Hl y m Hm)) |].
    split; [intros y m1 m2 H1 H2; exact (E3 y m1 m2 (Hl y m1 H1) (Hl y m2 H2)) |].
    intros x y mx my Hx Hy; exact (E4 x y mx my (Hl x mx Hx) (Hl y my Hy)).
  Qed.

  (* The shift of positions when an action of r is inserted at q: a position after q, or at q
     above r, moves past the inserted action. *)
  Definition shp (q r y p : nat) : nat :=
    if Nat.ltb q p || (Nat.eqb p q && rchbF y r) then S p else p.

  Lemma shp_cases : forall q r y p,
    (shp q r y p = S p /\ (q < p \/ (p = q /\ RchF y r))) \/
    (shp q r y p = p /\ (p < q \/ (p = q /\ ~ RchF y r))).
  Proof.
    intros q r y p. unfold shp. destruct (Nat.ltb q p) eqn:L.
    - left. split; [reflexivity |]. left. apply Nat.ltb_lt. exact L.
    - apply Nat.ltb_ge in L. destruct (Nat.eqb p q) eqn:Eq; simpl.
      + apply Nat.eqb_eq in Eq. destruct (rchbF y r) eqn:R.
        * left. split; [reflexivity |]. right. split; [exact Eq | exact (proj1 (rchb_true src o Ho y r) R)].
        * right. split; [reflexivity |]. right. split; [exact Eq | exact (proj1 (rchb_false src o Ho y r) R)].
      + apply Nat.eqb_neq in Eq. right. split; [reflexivity |]. left. lia.
  Qed.

  Lemma shp_mono : forall q r y1 y2 p1 p2, p1 <= p2 -> (p1 = p2 -> RchF y1 r -> RchF y2 r) ->
    shp q r y1 p1 <= shp q r y2 p2.
  Proof.
    intros q r y1 y2 p1 p2 H Hr.
    destruct (shp_cases q r y1 p1) as [[A1 B1] | [A1 B1]]; destruct (shp_cases q r y2 p2) as [[A2 B2] | [A2 B2]];
      rewrite A1, A2; try lia.
    destruct B1 as [B1 | [B1 R1]]; destruct B2 as [B2 | [B2 R2]]; try lia.
    subst. exfalso. exact (R2 (Hr eq_refl R1)).
  Qed.

  Lemma skipn_firstn_split : forall (W : list (act E)) p q, p <= q -> q <= length W ->
    skipn p W = skipn p (firstn q W) ++ skipn q W.
  Proof.
    intros W p q Hp Hq. rewrite <- (pc_firstn_skipn _ q W) at 1.
    apply pc_skipn_app_le. rewrite pc_firstn_len by exact Hq. exact Hp.
  Qed.

  (* Inserting an action of r at q keeps the invariant, given that q is below every live position
     above r and above every live position of a reader of r. *)
  Lemma emu_ins : forall s0 c c' W P q a,
    EmuN s0 c W P -> okF a -> q <= length W -> Forall (NoT (actorF a)) (skipn q W) ->
    (forall y m, Live c' y m -> RchF y (actorF a) -> q <= P y (fst m)) ->
    (forall x m, Live c' x m -> In (actorF a) (src x) -> P x (fst m) <= q) ->
    (forall y m, In m (cbC c' y) -> In m (cbC c y)) -> (forall y m, Live c' y m -> Live c y m) ->
    (forall k, dF (ins q a W) s0 k = csC c' k) ->
    EmuN s0 c' (ins q a W) (fun y v => shp q (actorF a) y (P y v)).
  Proof.
    intros s0 c c' W P q a [O [S0 [B [E1 [E2 [E3 E4]]]]]] Ha Hq Hn Hup Hrd Hb Hl Hs.
    set (r := actorF a) in *.
    assert (Lw : length (ins q a W) = S (length W)) by (apply ins_len; exact Hq).
    split; [apply ins_Forall; assumption |].
    split; [exact Hs |].
    split; [intros y m Hm; exact (B y m (Hb y m Hm)) |].
    split.
    { intros y m Hm. destruct (E1 y m (Hl y m Hm)) as [Pl Pv]. set (p := P y (fst m)) in *.
      assert (Hyo : In y o) by exact (B y m (Hb y m (proj1 Hm))).
      destruct (shp_cases q r y p) as [[A1 B1] | [A1 B1]]; rewrite A1.
      - assert (Hqp : q <= p) by (destruct B1 as [B1 | [B1 _]]; lia).
        split; [lia |]. intros k Hk.
        assert (Nk : k <> r).
        { intro Ek. subst k. pose proof (Hrd y m Hm Hk) as Le. fold p in Le.
          destruct B1 as [B1 | [_ B1]]; [lia | exact (rch_reader src o Ho y r Hyo Hk B1)]. }
        rewrite (Pv k Hk). symmetry.
        exact (proj1 (ins_state V src f E reg sig (c_local _ _ _ _ _ _ _ _ _ HC) q a W s0 Hq Hn p Hqp Pl) k Nk).
      - assert (Hpq : p <= q) by (destruct B1 as [B1 | [B1 _]]; lia).
        split; [lia |]. intros k Hk. rewrite (Pv k Hk). rewrite (ins_firstn_le _ q a W p Hpq Hq). reflexivity. }
    split.
    { intros y m Hm. pose proof (E2 y m (Hl y m Hm)) as F. destruct (E1 y m (Hl y m Hm)) as [Pl _].
      set (p := P y (fst m)) in *.
      destruct (shp_cases q r y p) as [[A1 B1] | [A1 B1]]; rewrite A1.
      - assert (Hqp : q <= p) by (destruct B1 as [B1 | [B1 _]]; lia).
        rewrite (ins_skipn_gt _ q a W p Hqp Hq). exact F.
      - assert (Hpq : p <= q) by (destruct B1 as [B1 | [B1 _]]; lia).
        rewrite (ins_skipn_le _ q a W p Hpq Hq). rewrite (skipn_firstn_split W p q Hpq Hq) in F.
        apply Forall_app in F as [F1 F2]. apply Forall_app. split; [exact F1 |].
        constructor; [| exact F2].
        intro R. destruct B1 as [B1 | [_ B1]]; [| exact (B1 R)].
        pose proof (Hup y m Hm R) as Le. fold p in Le. lia. }
    split.
    { intros y m1 m2 H1 H2 Hlt. apply shp_mono; [exact (E3 y m1 m2 (Hl y m1 H1) (Hl y m2 H2) Hlt) |].
      intros _ R. exact R. }
    intros x y mx my Hx Hy Ne R. apply shp_mono; [exact (E4 x y mx my (Hl x mx Hx) (Hl y my Hy) Ne R) |].
    intros _ R'. exact (rch_trans src o y x r R R').
  Qed.

  Lemma pc_in_skipn : forall (W : list (act E)) n a, In a (skipn n W) -> In a W.
  Proof.
    intros W n. revert W. induction n as [| n IH]; intros [| b W] a H; simpl in *; try exact H; try contradiction.
    right. exact (IH W a H).
  Qed.

  (* The shortest prefix after which nothing touches r. *)
  Definition touchb (r : nat) (a : act E) : bool :=
    Nat.eqb (actorF a) r || (if in_dec Nat.eq_dec r (src (actorF a)) then true else false).

  Fixpoint ltouch (r : nat) (W : list (act E)) : nat :=
    match W with
    | [] => 0
    | a :: W' => match ltouch r W' with 0 => if touchb r a then 1 else 0 | S n => S (S n) end
    end.

  Lemma touchb_false : forall r a, touchb r a = false -> NoT r a.
  Proof.
    intros r a H. unfold touchb in H. apply orb_false_iff in H as [H1 H2]. apply Nat.eqb_neq in H1.
    split; [exact H1 |]. destruct (in_dec Nat.eq_dec r (src (actorF a))); [discriminate | assumption].
  Qed.

  Lemma touchb_true : forall r a, NoT r a -> touchb r a = false.
  Proof.
    intros r a [H1 H2]. unfold touchb. apply orb_false_iff. split; [apply Nat.eqb_neq; exact H1 |].
    destruct (in_dec Nat.eq_dec r (src (actorF a))); [contradiction | reflexivity].
  Qed.

  Lemma ltouch_len : forall r W, ltouch r W <= length W.
  Proof.
    intros r W. induction W as [| a W IH]; simpl; [lia |].
    destruct (ltouch r W); [destruct (touchb r a); lia | lia].
  Qed.

  Lemma ltouch_suffix : forall r W, Forall (NoT r) (skipn (ltouch r W) W).
  Proof.
    intros r W. induction W as [| a W IH]; simpl; [constructor |].
    destruct (ltouch r W) as [| n] eqn:L.
    - destruct (touchb r a) eqn:T; simpl; [exact IH |]. constructor; [apply touchb_false; exact T | exact IH].
    - exact IH.
  Qed.

  Lemma ltouch_min : forall r W p, Forall (NoT r) (skipn p W) -> ltouch r W <= p.
  Proof.
    intros r W. induction W as [| a W IH]; intros p H; simpl; [lia |].
    destruct p as [| p].
    - simpl in H. inversion H as [| ? ? Ha Hw]; subst.
      pose proof (IH 0 Hw) as L. destruct (ltouch r W); [| lia]. rewrite (touchb_true r a Ha). lia.
    - simpl in H. pose proof (IH p H) as L. destruct (ltouch r W); [destruct (touchb r a); lia | lia].
  Qed.

  (* The live positions of the readers of r, and of the registries above j. *)
  Definition livepos (c : cfgC) (P : nat -> nat -> nat) (x : nat) : list nat :=
    map (fun m => P x (fst m)) (filter (fun m => Nat.ltb (clC c x) (fst m)) (cbC c x)).

  Definition readers_pos (c : cfgC) (P : nat -> nat -> nat) (r : nat) : list nat :=
    flat_map (fun x => if rt x then [] else if in_dec Nat.eq_dec r (src x) then livepos c P x else []) o.

  Definition above_pos (c : cfgC) (P : nat -> nat -> nat) (j : nat) : list nat :=
    flat_map (fun y => if rt y then [] else if Nat.eq_dec y j then [] else if rchbF y j then livepos c P y else []) o.

  Lemma livepos_in : forall c P x m, Live c x m -> In (P x (fst m)) (livepos c P x).
  Proof.
    intros c P x m [Hm [Hl _]]. unfold livepos. apply in_map_iff. exists m. split; [reflexivity |].
    apply filter_In. split; [exact Hm | apply Nat.ltb_lt; exact Hl].
  Qed.

  Lemma livepos_el : forall c P x n, rt x = false -> In n (livepos c P x) -> exists m, Live c x m /\ n = P x (fst m).
  Proof.
    intros c P x n Hr H. unfold livepos in H. apply in_map_iff in H as [m [<- Hm]].
    apply filter_In in Hm as [Hm Hl]. exists m. split; [| reflexivity].
    split; [exact Hm |]. split; [apply Nat.ltb_lt; exact Hl | exact Hr].
  Qed.

  Lemma readers_in : forall c P r x m, In x o -> Live c x m -> In r (src x) -> In (P x (fst m)) (readers_pos c P r).
  Proof.
    intros c P r x m Hx Hm Hr. unfold readers_pos. apply in_flat_map. exists x. split; [exact Hx |].
    destruct Hm as [Hm1 [Hm2 Hm3]]. rewrite Hm3.
    destruct (in_dec Nat.eq_dec r (src x)) as [_ | C]; [| contradiction].
    apply livepos_in. split; [exact Hm1 | split; assumption].
  Qed.

  Lemma readers_el : forall c P r n, In n (readers_pos c P r) ->
    exists x m, In x o /\ Live c x m /\ In r (src x) /\ n = P x (fst m).
  Proof.
    intros c P r n H. unfold readers_pos in H. apply in_flat_map in H as [x [Hx H]].
    destruct (rt x) eqn:Rx; [destruct H |].
    destruct (in_dec Nat.eq_dec r (src x)) as [Hr | Hr]; [| destruct H].
    destruct (livepos_el c P x n Rx H) as [m [Hm ->]]. exists x, m. tauto.
  Qed.

  Lemma above_in : forall c P j y m, In y o -> Live c y m -> y <> j -> RchF y j -> In (P y (fst m)) (above_pos c P j).
  Proof.
    intros c P j y m Hy Hm Ne R. unfold above_pos. apply in_flat_map. exists y. split; [exact Hy |].
    destruct Hm as [Hm1 [Hm2 Hm3]]. rewrite Hm3.
    destruct (Nat.eq_dec y j) as [C | _]; [contradiction |].
    rewrite (proj2 (rchb_true src o Ho y j) R). apply livepos_in. split; [exact Hm1 | split; assumption].
  Qed.

  Lemma above_el : forall c P j n, In n (above_pos c P j) ->
    exists y m, In y o /\ Live c y m /\ y <> j /\ RchF y j /\ n = P y (fst m).
  Proof.
    intros c P j n H. unfold above_pos in H. apply in_flat_map in H as [y [Hy H]].
    destruct (rt y) eqn:Ry; [destruct H |].
    destruct (Nat.eq_dec y j) as [_ | Ne]; [destruct H |].
    destruct (rchbF y j) eqn:R; [| destruct H].
    destruct (livepos_el c P y n Ry H) as [m [Hm ->]]. exists y, m.
    split; [exact Hy |]. split; [exact Hm |]. split; [exact Ne |]. split; [apply (rchb_true src o Ho); exact R | reflexivity].
  Qed.

  (* After the position of a live projection to y, nothing touches a registry below y. *)
  Lemma e2_notouch : forall s0 c W P y m r, EmuN s0 c W P -> Live c y m -> RchF y r ->
    Forall (NoT r) (skipn (P y (fst m)) W).
  Proof.
    intros s0 c W P y m r [O [_ [_ [_ [E2 _]]]]] Hm R. pose proof (E2 y m Hm) as F.
    apply Forall_forall. intros a Ha. pose proof (proj1 (Forall_forall _ _) F a Ha) as Na.
    pose proof (actor_in a (proj1 (Forall_forall _ _) O a (pc_in_skipn W _ a Ha))) as Ao.
    split.
    - intro Ea. apply Na. rewrite Ea. exact R.
    - intro Hr. apply Na. exact (rch_step src o y (actorF a) r Ao Hr R).
  Qed.

  Lemma reader_ne : forall x y r, In x o -> In r (src x) -> RchF y r -> x <> y.
  Proof. intros x y r Hx Hr R ->. exact (rch_reader src o Ho y r Hx Hr R). Qed.

  (* Inserting an action of r just after the last action touching r and the live positions of r's
     readers. *)
  Lemma emu_ins_at : forall s0 c c' W P a,
    EmuN s0 c W P -> okF a ->
    (forall y m, In m (cbC c' y) -> In m (cbC c y)) -> (forall y m, Live c' y m -> Live c y m) ->
    (forall k, dF (ins (maxl (ltouch (actorF a) W) (readers_pos c P (actorF a))) a W) s0 k = csC c' k) ->
    EmuN s0 c' (ins (maxl (ltouch (actorF a) W) (readers_pos c P (actorF a))) a W)
      (fun y v => shp (maxl (ltouch (actorF a) W) (readers_pos c P (actorF a))) (actorF a) y (P y v)).
  Proof.
    intros s0 c c' W P a He Ha Hb Hl Hs. set (r := actorF a) in *.
    set (q := maxl (ltouch r W) (readers_pos c P r)).
    pose proof He as He0. destruct He0 as [O [S0 [B [E1 [E2 [E3 E4]]]]]].
    apply (emu_ins s0 c c' W P q a He Ha).
    - apply maxl_le; [apply ltouch_len |]. intros n Hn. destruct (readers_el c P r n Hn) as [x [m [_ [Hm [_ ->]]]]].
      exact (proj1 (E1 x m Hm)).
    - apply (Forall_skipn_mono _ W (ltouch r W) q); [apply maxl_ge_d | apply ltouch_suffix].
    - intros y m Hm R. apply (Hl y m) in Hm. apply maxl_le.
      + apply ltouch_min. exact (e2_notouch s0 c W P y m r He Hm R).
      + intros n Hn. destruct (readers_el c P r n Hn) as [x [mx [Hx [Hmx [Hr ->]]]]].
        apply (E4 x y mx m Hmx Hm (reader_ne x y r Hx Hr R)). exact (rch_step src o y x r Hx Hr R).
    - intros x m Hm Hr. apply maxl_ge. apply (Hl x m) in Hm.
      apply (readers_in c P r x m); [exact (B x m (proj1 Hm)) | exact Hm | exact Hr].
    - exact Hb.
    - exact Hl.
    - exact Hs.
  Qed.

  Lemma q_le : forall s0 c W P r, EmuN s0 c W P -> maxl (ltouch r W) (readers_pos c P r) <= length W.
  Proof.
    intros s0 c W P r [_ [_ [_ [E1 _]]]]. apply maxl_le; [apply ltouch_len |].
    intros n Hn. destruct (readers_el c P r n Hn) as [x [m [_ [Hm [_ ->]]]]]. exact (proj1 (E1 x m Hm)).
  Qed.

  Lemma q_notouch : forall W c P r, Forall (NoT r) (skipn (maxl (ltouch r W) (readers_pos c P r)) W).
  Proof. intros W c P r. apply (Forall_skipn_mono _ W (ltouch r W)); [apply maxl_ge_d | apply ltouch_suffix]. Qed.

  (* A local event. *)
  Lemma emu_ev : forall s0 c W P e, EmuN s0 c W P -> exists W' P', EmuN s0 (cstepT (CEv e) c) W' P'.
  Proof.
    intros s0 c W P e He. set (a := DEv E e).
    set (q := maxl (ltouch (actorF a) W) (readers_pos c P (actorF a))).
    exists (ins q a W), (fun y v => shp q (actorF a) y (P y v)).
    apply (emu_ins_at s0 c _ W P a He Logic.I); [intros y m H; exact H | intros y m H; exact H |].
    intros k. pose proof (q_le s0 c W P (actorF a) He) as Hq.
    destruct (ins_state_full V src f E reg sig (c_local _ _ _ _ _ _ _ _ _ HC) q a W s0 Hq
                (q_notouch W c P (actorF a))) as [A1 [A2 A3]].
    destruct He as [_ [S0 _]]. fold q.
    change (cs V (cstep V f E reg sig true (CEv e) c) k) with (evstep V E reg sig e (cs V c) k).
    change (actorF a) with (reg e) in A1, A2, A3.
    destruct (Nat.eq_dec k (reg e)) as [-> | Ne].
    - rewrite A2. change (dstep V f E reg sig a ?t (reg e)) with (evstep V E reg sig e t (reg e)).
      rewrite !(evstep_at V E reg sig e _ (reg e) eq_refl). rewrite <- A3, S0. reflexivity.
    - rewrite (A1 k Ne). rewrite (evstep_off V E reg sig e _ k Ne). apply S0.
  Qed.

  Lemma minl_in : forall d l, minl d l = d \/ In (minl d l) l.
  Proof.
    intros d l. induction l as [| x l IH]; simpl; [left; reflexivity |].
    destruct (Nat.le_ge_cases x (minl d l)).
    - right. left. lia.
    - destruct IH as [IH | IH]; [left; lia | right; right; rewrite Nat.min_r by lia; exact IH].
  Qed.

  Lemma dF_suffix : forall W s0 p k, Forall (NoT k) (skipn p W) -> dF W s0 k = dF (firstn p W) s0 k.
  Proof.
    intros W s0 p k H. rewrite <- (pc_firstn_skipn _ p W) at 1. rewrite (drun_app V f E reg sig).
    exact (proj1 (proj2 (dF_agree V src f E reg sig (c_local _ _ _ _ _ _ _ _ _ HC) _ k _ _ H (fun _ _ => eq_refl)))).
  Qed.

  Lemma live_send : forall c j v y m, VInv V c -> cvC c j < v ->
    Live (cstepT (CSend j v) c) y m -> (y = j /\ m = (v, csC c)) \/ (Live c y m /\ (y = j -> fst m < v)).
  Proof.
    intros c j v y m Hv Hlt [Hm [Hl Hr]]. cbn [cstep cs cb cl cv] in Hm, Hl.
    destruct (Nat.eq_dec y j) as [-> | Ne].
    - rewrite (setb_eq V) in Hm. destruct Hm as [<- | Hm]; [left; split; reflexivity |].
      right. split; [split; [exact Hm | split; assumption] |].
      intros _. pose proof (proj2 (Hv j) m Hm). lia.
    - rewrite (setb_neq V _ _ _ _ Ne) in Hm. right. split; [split; [exact Hm | split; assumption] |].
      intros E'. contradiction.
  Qed.

  (* A send. *)
  Lemma emu_send : forall s0 c W P j v, EmuN s0 c W P -> VInv V c -> cvC c j < v -> In j o ->
    exists P', EmuN s0 (cstepT (CSend j v) c) W P'.
  Proof.
    intros s0 c W P j v He Hv Hlt Hj. pose proof He as He0. destruct He0 as [O [S0 [B [E1 [E2 [E3 E4]]]]]].
    set (c' := cstepT (CSend j v) c).
    assert (Bc : forall y m, In m (cbC c' y) -> In m (cbC c y) \/ (y = j /\ m = (v, csC c))).
    { intros y m Hm. unfold c' in Hm. cbn [cstep cb] in Hm. destruct (Nat.eq_dec y j) as [-> | Ne].
      - rewrite (setb_eq V) in Hm. destruct Hm as [<- | Hm]; [right; split; reflexivity | left; exact Hm].
      - rewrite (setb_neq V _ _ _ _ Ne) in Hm. left. exact Hm. }
    assert (B' : forall y m, In m (cbC c' y) -> In y o).
    { intros y m Hm. destruct (Bc y m Hm) as [H | [-> _]]; [exact (B y m H) | exact Hj]. }
    destruct (rt j) eqn:Rj.
    - (* a projection to a pure root is never live *)
      exists P. split; [exact O |]. split; [exact S0 |]. split; [exact B' |].
      assert (L : forall y m, Live c' y m -> Live c y m).
      { intros y m Hm. destruct (live_send c j v y m Hv Hlt Hm) as [[-> _] | [H _]]; [| exact H].
        destruct Hm as [_ [_ C]]. congruence. }
      split; [intros y m Hm; exact (E1 y m (L y m Hm)) |].
      split; [intros y m Hm; exact (E2 y m (L y m Hm)) |].
      split; [intros y m1 m2 H1 H2; exact (E3 y m1 m2 (L y m1 H1) (L y m2 H2)) |].
      intros x y mx my Hx Hy; exact (E4 x y mx my (L x mx Hx) (L y my Hy)).
    - set (pj := minl (length W) (above_pos c P j)).
      exists (fun y u => if Nat.eqb y j && Nat.eqb u v then pj else P y u).
      assert (Old : forall y m, Live c y m -> (y = j -> fst m < v) ->
                (if Nat.eqb y j && Nat.eqb (fst m) v then pj else P y (fst m)) = P y (fst m)).
      { intros y m Hm Hy. destruct (Nat.eqb y j) eqn:Ey; [| reflexivity].
        apply Nat.eqb_eq in Ey. specialize (Hy Ey). destruct (Nat.eqb (fst m) v) eqn:Ev; [| reflexivity].
        apply Nat.eqb_eq in Ev. lia. }
      assert (New : (if Nat.eqb j j && Nat.eqb (fst (v, csC c)) v then pj else P j (fst (v, csC c))) = pj).
      { simpl. rewrite !Nat.eqb_refl. reflexivity. }
      (* pj is the end of W or the position of a live projection above j *)
      assert (Pj : pj = length W \/ exists y m, In y o /\ Live c y m /\ y <> j /\ RchF y j /\ pj = P y (fst m)).
      { destruct (minl_in (length W) (above_pos c P j)) as [H | H]; [left; exact H |].
        right. exact (above_el c P j pj H). }
      assert (PjS : forall r, (forall y m, Live c y m -> y <> j -> RchF y j -> RchF y r) ->
                Forall (NoT r) (skipn pj W)).
      { intros r Hr. destruct Pj as [-> | [y [m [_ [Hm [Ne [R ->]]]]]]].
        - rewrite skipn_all2 by lia. constructor.
        - apply (e2_notouch s0 c W P y m r He Hm). exact (Hr y m Hm Ne R). }
      assert (Pmin : forall n, n <= length W -> (forall y m, Live c y m -> y <> j -> RchF y j -> n <= P y (fst m)) -> n <= pj).
      { intros n Hn H. apply minl_ge; [exact Hn |]. intros x Hx.
        destruct (above_el c P j x Hx) as [y [m [_ [Hm [Ne [R ->]]]]]]. exact (H y m Hm Ne R). }
      assert (Pup : forall y m, Live c y m -> y <> j -> RchF y j -> pj <= P y (fst m)).
      { intros y m Hm Ne R. apply minl_le. apply above_in; [exact (B y m (proj1 Hm)) | exact Hm | exact Ne | exact R]. }
      split; [exact O |]. split; [exact S0 |]. split; [exact B' |].
      split.
      { intros y m Hm. destruct (live_send c j v y m Hv Hlt Hm) as [[-> ->] | [Hm' Hy]].
        - rewrite New. split; [apply minl_le_d |]. intros k Hk. simpl. rewrite <- S0.
          apply dF_suffix. apply PjS. intros y m' Hm' Ne R.
          exact (HN j y k Hj Rj (proj2 (proj2 Hm')) Ne R Hk).
        - rewrite (Old y m Hm' Hy). exact (E1 y m Hm'). }
      split.
      { intros y m Hm. destruct (live_send c j v y m Hv Hlt Hm) as [[-> ->] | [Hm' Hy]].
        - rewrite New. destruct Pj as [-> | [y [m [_ [Hm1 [Ne [R ->]]]]]]].
          + rewrite skipn_all2 by lia. constructor.
          + eapply Forall_impl; [| exact (E2 y m Hm1)]. intros a Na Ra. apply Na.
            exact (rch_trans src o y j _ R Ra).
        - rewrite (Old y m Hm' Hy). exact (E2 y m Hm'). }
      split.
      { intros y m1 m2 H1 H2 L12.
        destruct (live_send c j v y m1 Hv Hlt H1) as [[Ey1 Em1] | [H1' Hy1]];
          destruct (live_send c j v y m2 Hv Hlt H2) as [[Ey2 Em2] | [H2' Hy2]].
        - subst. simpl in L12. lia.
        - subst m1. simpl in L12. pose proof (Hy2 Ey1). lia.
        - subst y m2. rewrite New, (Old j m1 H1' Hy1). apply Pmin; [exact (proj1 (E1 j m1 H1')) |].
          intros y m Hm Ne R. exact (E4 j y m1 m H1' Hm (fun E' => Ne (eq_sym E')) R).
        - rewrite (Old y m1 H1' Hy1), (Old y m2 H2' Hy2). exact (E3 y m1 m2 H1' H2' L12). }
      intros x y mx my Hx Hy Ne R.
      destruct (live_send c j v x mx Hv Hlt Hx) as [[Ex Emx] | [Hx' Hx2]];
        destruct (live_send c j v y my Hv Hlt Hy) as [[Ey Emy] | [Hy' Hy2]].
      + subst. contradiction.
      + subst x mx. rewrite New, (Old y my Hy' Hy2). apply Pup; [exact Hy' | intro E'; apply Ne; symmetry; exact E' | exact R].
      + subst y my. rewrite New, (Old x mx Hx' Hx2). apply Pmin; [exact (proj1 (E1 x mx Hx')) |].
        intros y m Hm Ne' R'. apply (E4 x y mx m Hx' Hm).
        * intros Exy. apply Ne. subst. exact (rch_antisym src o Ho _ _ R' R).
        * exact (rch_trans src o y j x R' R).
      + rewrite (Old x mx Hx' Hx2), (Old y my Hy' Hy2). exact (E4 x y mx my Hx' Hy' Ne R).
  Qed.

  (* A delivery: a refused projection, or one to a pure root, changes nothing; an applied
     projection to j becomes a propagation step of j, inserted at its position. *)
  Lemma emu_merge : forall s0 c c1 W P j m, EmuN s0 c W P -> In j o -> In m (cbC c j) ->
    (forall k, csC c1 k = csC c k) -> (forall k, clC c1 k = clC c k) ->
    (forall y m', In m' (cbC c1 y) -> In m' (cbC c y)) ->
    exists W' P', EmuN s0 (merge V f true j m c1) W' P'.
  Proof.
    intros s0 c c1 W P j m He Hj Hm Hs1 Hl1 Hb1.
    assert (L1 : forall y m', Live c1 y m' -> Live c y m').
    { intros y m' [H1 [H2 H3]]. split; [exact (Hb1 y m' H1) |]. rewrite <- Hl1. split; assumption. }
    unfold merge, applies. destruct (Nat.ltb (clC c1 j) (fst m)) eqn:Ap.
    2: { exists W, P. apply (emu_shrink s0 c c1 W P Hs1 Hb1 L1 He). }
    apply Nat.ltb_lt in Ap. rewrite Hl1 in Ap.
    set (c' := Cfg V (upd V (csC c1) j (f j (snd m) (csC c1 j))) (cbC c1) (setn (clC c1) j (fst m)) (cv V c1)).
    assert (Lc : forall y m', Live c' y m' -> Live c y m').
    { intros y m' [H1 [H2 H3]]. apply L1. split; [exact H1 |]. split; [| exact H3].
      unfold c' in H2. cbn [cl] in H2. destruct (Nat.eq_dec y j) as [-> | Ne].
      - rewrite (setn_eq) in H2. rewrite Hl1. lia.
      - rewrite (setn_neq _ _ _ _ Ne) in H2. exact H2. }
    destruct (rt j) eqn:Rj.
    - (* a pure root: the merge is the identity *)
      exists W, P. apply (emu_shrink s0 c c' W P); [| exact Hb1 | exact Lc | exact He].
      intros k. unfold c'. cbn [cs]. rewrite (HR j Rj). unfold upd.
      destruct (Nat.eqb k j) eqn:Ek; [apply Nat.eqb_eq in Ek; subst k |]; apply Hs1.
    - pose proof He as He0. destruct He0 as [O [S0 [B [E1 [E2 [E3 E4]]]]]].
      assert (Hlm : Live c j m) by (split; [exact Hm | split; [exact Ap | exact Rj]]).
      set (q := P j (fst m)). set (a := DProp E j).
      exists (ins q a W), (fun y v => shp q (actorF a) y (P y v)).
      assert (Hq : q <= length W) by exact (proj1 (E1 j m Hlm)).
      assert (Hn : Forall (NoT j) (skipn q W)) by exact (e2_notouch s0 c W P j m j He Hlm (rch_refl src o j)).
      apply (emu_ins s0 c c' W P q a He Hj Hq Hn).
      + intros y m' Hm' R. pose proof (Lc y m' Hm') as Hc. destruct (Nat.eq_dec y j) as [-> | Ne].
        * apply (E3 j m m' Hlm Hc). destruct Hm' as [_ [H2 _]]. unfold c' in H2. cbn [cl] in H2.
          rewrite setn_eq in H2. exact H2.
        * exact (E4 j y m m' Hlm Hc (fun E' => Ne (eq_sym E')) R).
      + intros x m' Hm' Hr. pose proof (Lc x m' Hm') as Hc. assert (Hx : In x o) by exact (B x m' (proj1 Hc)).
        apply (E4 x j m' m Hc Hlm).
        * intros ->. exact (topo_noself src o j Ho Hx Hr).
        * exact (rch_step src o j x j Hx Hr (rch_refl src o j)).
      + intros y m' H. exact (Hb1 y m' H).
      + exact Lc.
      + intros k. destruct (ins_state_full V src f E reg sig (c_local _ _ _ _ _ _ _ _ _ HC) q a W s0 Hq Hn)
          as [A1 [A2 A3]].
        change (actorF a) with j in A1, A2, A3. unfold c'. cbn [cs].
        destruct (Nat.eq_dec k j) as [-> | Ne].
        * rewrite A2, (upd_eq V). change (dstep V f E reg sig a ?t j) with (fstep V f t j j).
          rewrite (fstep_eq V f). rewrite Hs1, <- S0, A3.
          apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk. symmetry. exact (proj2 (E1 j m Hlm) k Hk).
        * rewrite (A1 k Ne), (upd_neq V _ _ _ _ Ne), Hs1. apply S0.
  Qed.

  Lemma emu_step : forall s0 c W P a, EmuN s0 c W P -> VInv V c -> okcF a ->
    (match a with CSend j v => cvC c j < v | _ => True end) ->
    exists W' P', EmuN s0 (cstepT a c) W' P'.
  Proof.
    intros s0 c W P a He Hv Ha Hd. pose proof He as He0. destruct He0 as [_ [_ [B _]]].
    destruct a as [e | j v | j i | j i].
    - exact (emu_ev s0 c W P e He).
    - destruct (emu_send s0 c W P j v He Hv Hd Ha) as [P' H]. exists W, P'. exact H.
    - cbn [cstep]. destruct (nth_error (cbC c j) i) as [m |] eqn:Hn; [| exists W, P; exact He].
      apply (emu_merge s0 c _ W P j m He Ha (nth_error_in V _ _ _ Hn)); [intros; reflexivity | intros; reflexivity |].
      intros y m' Hm'. cbn [cb] in Hm'. destruct (Nat.eq_dec y j) as [-> | Ne].
      + rewrite (setb_eq V) in Hm'. exact (rmn_in V _ _ _ Hm').
      + rewrite (setb_neq V _ _ _ _ Ne) in Hm'. exact Hm'.
    - cbn [cstep]. destruct (nth_error (cbC c j) i) as [m |] eqn:Hn; [| exists W, P; exact He].
      apply (emu_merge s0 c c W P j m He Ha (nth_error_in V _ _ _ Hn)); intros; [reflexivity | reflexivity | assumption].
  Qed.

  Lemma emu_run : forall s0 w c W P, EmuN s0 c W P -> VInv V c -> Forall okcF w -> discT w c ->
    exists W' P', EmuN s0 (crunT w c) W' P'.
  Proof.
    intros s0 w. induction w as [| a w IH]; intros c W P He Hv Hw Hd; [exists W, P; exact He |].
    inversion Hw as [| ? ? Ha Hw']; subst. destruct Hd as [Hd1 Hd].
    destruct (emu_step s0 c W P a He Hv Ha Hd1) as [W1 [P1 He1]].
    exact (IH (cstepT a c) W1 P1 He1 (vinv_step V f E reg sig true a c Hv Hd1) Hw' Hd).
  Qed.

  (* Headline (emulation): on a nested network every state a disciplined versioned channel run
     reaches (projections late, reordered, duplicated) is the state of a current-value run. *)
  Theorem vchan_nested_emulate : forall s0 w, Forall okcF w -> discT w (init V s0) ->
    exists W, Forall okF W /\ forall k, dF W s0 k = csC (crunT w (init V s0)) k.
  Proof.
    intros s0 w Hw Hd.
    assert (He : EmuN s0 (init V s0) [] (fun _ _ => 0)).
    { split; [constructor |]. split; [intros k; reflexivity |].
      split; [intros y m [] |]. split; [intros y m [[] _] |]. split; [intros y m [[] _] |].
      split; [intros y m1 m2 [[] _] |]. intros x y mx my [[] _]. }
    destruct (emu_run s0 w (init V s0) [] (fun _ _ => 0) He (vinv_init V s0) Hw Hd) as [W [P [O [S0 _]]]].
    exists W. split; [exact O | exact S0].
  Qed.
End NestedSec.

(* ---------------------------------------------------------------------------------- *)
(* The exact condition on nested networks; two-level and single-source corollaries.    *)
(* ---------------------------------------------------------------------------------- *)

Section NestedExact.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  Variable o : list nat.

  Hypothesis HC : Common V src f valid rho E reg sig o.

  Local Notation InvF := (Inv V valid).
  Local Notation XURF := (XUR V f rho E reg sig o).
  Local Notation CXURF := (CXUR V f rho E reg sig o).
  Local Notation C2Rf := (C2R V f rho E reg sig I o).
  Local Notation nF := (N V f rho o).
  Local Notation ChanConvF := (ChanConv V f rho E reg sig I o).
  Local Notation SettleConvF := (SettleConv V f E reg sig I o).
  Local Notation DistConvF := (DistConv V f rho E reg sig I o).

  Variable rt : nat -> bool.
  Hypothesis HR : forall k, rt k = true -> forall z x, f k z x = x.
  Hypothesis HN : Nested src o rt.

  (* Reachable XU over versioned channels is reachable XU over the current-value model. *)
  Theorem cxur_nested : forall s0, CXURF true s0 <-> XURF s0.
  Proof.
    intros s0. split; [apply cxur_xur |].
    intros Hx p e Hp Hd.
    destruct (vchan_nested_emulate V src f valid rho E reg sig o HC rt HR HN s0 p Hp Hd) as [W [Ok Hs]].
    apply (xuat_feq V src f valid rho E reg sig o HC (drun V f E reg sig W s0)); [exact Hs |].
    exact (Hx W e Ok).
  Qed.

  (* Headline (nested, versioned): the exact condition over channels is the current-value model's
     own (DistributedExact.dist_exact), compared after a flush or at drain. *)
  Theorem vchan_nested_exact : forall s0, InvF s0 ->
    (CXURF true s0 <-> XURF s0) /\
    (ChanConvF true s0 <-> XURF s0 /\ C2Rf (nF s0)) /\
    (SettleConvF s0 <-> XURF s0 /\ C2Rf (nF s0)) /\
    (SettleConvF s0 <-> DistConvF s0).
  Proof.
    intros s0 Hi.
    assert (A : ChanConvF true s0 <-> XURF s0 /\ C2Rf (nF s0)).
    { rewrite (chan_exact V src f valid rho E reg sig I o HC true s0 Hi). rewrite cxur_nested. reflexivity. }
    assert (B : SettleConvF s0 <-> XURF s0 /\ C2Rf (nF s0))
      by (rewrite (vsettle_exact V src f valid rho E reg sig I o HC s0 Hi); exact A).
    split; [apply cxur_nested |]. split; [exact A |]. split; [exact B |].
    rewrite B. symmetry. exact (dist_exact V src f valid rho E reg sig I o HC s0 Hi).
  Qed.
End NestedExact.

Lemma rch_read : forall src o y x, Rch src o y x -> x = y \/ exists w, In y (src w).
Proof.
  intros src o y x H. induction H as [| x z Hx Hz H IH]; [left; reflexivity |].
  right. destruct IH as [-> | IH]; [exists x; exact Hz | exact IH].
Qed.

(* Two-level networks are nested: no registry above a target is anything but a pure root. *)
Lemma twolevel_nested : forall (V : Type) src f o rt, TwoLevel V src f rt -> Nested src o rt.
Proof.
  intros V src f o rt HT j y k Hj Rj Ry Ne R Hk.
  destruct (rch_read src o y j R) as [E' | [w Hw]]; [subst; contradiction |].
  exfalso. exact (proj2 (HT y) Ry w Hw).
Qed.

(* Networks where every target has at most one source are nested, with no pure root marked. *)
Definition SingleSource (src : nat -> list nat) (o : list nat) : Prop :=
  forall j, In j o -> forall k k', In k (src j) -> In k' (src j) -> k = k'.

Lemma single_nested : forall src o, SingleSource src o -> Nested src o (fun _ => false).
Proof.
  intros src o HS j y k Hj _ _ Ne R Hk.
  destruct (rch_inv src o y j R) as [E' | [z [_ [Hz Rz]]]]; [subst; contradiction |].
  rewrite (HS j Hj k z Hk Hz). exact Rz.
Qed.

(* Recovered: ProjectionChannels.vchan_twolevel_exact. *)
Theorem vchan_twolevel_exact_recovered : forall V src f valid rho E reg sig I o,
  Common V src f valid rho E reg sig o -> forall rt, TwoLevel V src f rt ->
  forall s0, Inv V valid s0 ->
    (ChanConv V f rho E reg sig I o true s0 <->
       XUR V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o (N V f rho o s0)) /\
    (SettleConv V f E reg sig I o s0 <->
       XUR V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o (N V f rho o s0)) /\
    (SettleConv V f E reg sig I o s0 <-> DistConv V f rho E reg sig I o s0).
Proof.
  intros V src f valid rho E reg sig I o HC rt HT s0 Hi.
  destruct (vchan_nested_exact V src f valid rho E reg sig I o HC rt (fun k Hk => proj1 (HT k) Hk)
              (twolevel_nested V src f o rt HT) s0 Hi) as [_ [A [B C]]].
  split; [exact A |]. split; [exact B | exact C].
Qed.

(* Headline (single-source networks, gsm's certified projection deployments): chains and trees
   of any depth; versioned channels reach nothing the current-value model does not. *)
Theorem vchan_single_exact : forall V src f valid rho E reg sig I o,
  Common V src f valid rho E reg sig o -> SingleSource src o ->
  forall s0, Inv V valid s0 ->
    (CXUR V f rho E reg sig o true s0 <-> XUR V f rho E reg sig o s0) /\
    (ChanConv V f rho E reg sig I o true s0 <->
       XUR V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o (N V f rho o s0)) /\
    (SettleConv V f E reg sig I o s0 <->
       XUR V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o (N V f rho o s0)) /\
    (SettleConv V f E reg sig I o s0 <-> DistConv V f rho E reg sig I o s0).
Proof.
  intros V src f valid rho E reg sig I o HC HS s0 Hi.
  apply (vchan_nested_exact V src f valid rho E reg sig I o HC (fun _ => false)); [| exact (single_nested src o HS) | exact Hi].
  intros k Hk. discriminate Hk.
Qed.

(* ========================================================================================= *)
(* Instances. Four registries over four booleans (b1, b2, b3, b4); every state is valid.       *)
(*   registry 0: a root; Flip sets b1.                                                        *)
(*   registry 1: reads 0, b1 := 0.b1 (a copy of the flag).                                    *)
(*   registry 2: reads 0 and 1, (b1, b2) := (0.b1, 1.b1).                                      *)
(*   registry 3: reads 1 and 2, (b1, b2, b3) := (1.b1, 2.b1, 2.b2); Mark sets b4 when its       *)
(*               shared part shows "1 stale while 2 saw 0 and 1 both set" (b1 = false, b2 = b3  *)
(*               = true).                                                                       *)
(* Registry 2 lies above 3 but 1, a source of 3, is not below 2: the network is not nested.    *)
(* ========================================================================================= *)

Record q4 : Type := Q4 { b1 : bool; b2 : bool; b3 : bool; b4 : bool }.

Definition k_src (k : nat) : list nat := match k with 1 => [0] | 2 => [0; 1] | 3 => [1; 2] | _ => [] end.

Definition k_f (k : nat) (z : nat -> q4) (x : q4) : q4 :=
  match k with
  | 1 => Q4 (b1 (z 0)) (b2 x) (b3 x) (b4 x)
  | 2 => Q4 (b1 (z 0)) (b1 (z 1)) (b3 x) (b4 x)
  | 3 => Q4 (b1 (z 1)) (b1 (z 2)) (b2 (z 2)) (b4 x)
  | _ => x
  end.

Definition k_valid (_ : nat) (_ : q4) : Prop := True.
Definition k_rho (_ : nat) (x : q4) : q4 := x.

Inductive kev : Type := Flip | Mark.

Definition k_reg (e : kev) : nat := match e with Flip => 0 | Mark => 3 end.

Definition k_bad (x : q4) : bool := negb (b1 x) && b2 x && b3 x.

Definition k_sig (e : kev) (x : q4) : q4 :=
  match e with
  | Flip => Q4 true (b2 x) (b3 x) (b4 x)
  | Mark => if k_bad x then Q4 (b1 x) (b2 x) (b3 x) true else x
  end.

Definition k_I (_ _ : kev) : Prop := False.

Definition k_o : list nat := [0; 1; 2; 3].

Definition qF : q4 := Q4 false false false false.

(* The start: registry 1 holds a stale copy (b1 = true while 0.b1 = false). *)
Definition k_s0 (k : nat) : q4 := match k with 1 => Q4 true false false false | _ => qF end.

Lemma k_topo : topoF k_src k_o.
Proof.
  unfold k_o. simpl. repeat split.
  - intros [H | [H | [H | []]]]; discriminate.
  - intros k [].
  - intros [H | [H | []]]; discriminate.
  - intros k [<- | []] [H | [H | [H | []]]]; discriminate.
  - intros [H | []]; discriminate.
  - intros k [<- | [<- | []]] [H | [H | []]]; discriminate.
  - intros [].
  - intros k [<- | [<- | []]] [H | []]; discriminate.
Qed.

Lemma k_common : Common q4 k_src k_f k_valid k_rho kev k_reg k_sig k_o.
Proof.
  constructor.
  - intros [| [| [| [| j]]]] z1 z2 x H; simpl; try reflexivity.
    + rewrite (H 0); [reflexivity | left; reflexivity].
    + rewrite (H 0), (H 1); [reflexivity | right; left; reflexivity | left; reflexivity].
    + rewrite (H 1), (H 2); [reflexivity | right; left; reflexivity | left; reflexivity].
  - exact k_topo.
  - intros. exact Logic.I.
  - intros [| [| [| [| j]]]] z z' x _ _ _; reflexivity.
  - intros. reflexivity.
  - intros. exact Logic.I.
  - intros []; unfold k_o; simpl; tauto.
Qed.

(* The current-value invariant: if registry 2 shows both flags set, registry 1's flag (and 0's)
   are set; registry 3 never shows the stale combination. *)
Definition k_inv (t : nat -> q4) : Prop :=
  (b1 (t 2) && b2 (t 2) = true -> b1 (t 1) = true /\ b1 (t 0) = true) /\ k_bad (t 3) = false.

Lemma k_inv_step : forall a t, okact kev k_o a -> k_inv t -> k_inv (dstep q4 k_f kev k_reg k_sig a t).
Proof.
  intros [e | j] t Ha [H1 H2].
  - destruct e.
    + unfold k_inv, k_bad in *; simpl in *.
      split; [| exact H2]. intros H. destruct (H1 H) as [A _]. split; [exact A | reflexivity].
    + assert (Hm : k_sig Mark (t 3) = t 3) by (unfold k_sig; rewrite H2; reflexivity).
      assert (Ht : forall k, dstep q4 k_f kev k_reg k_sig (DEv kev Mark) t k = t k).
      { intros k. simpl. unfold evstep, upd. simpl. destruct (Nat.eqb k 3) eqn:Ek; [| reflexivity].
        apply Nat.eqb_eq in Ek. subst k. exact Hm. }
      unfold k_inv. rewrite !Ht. split; assumption.
  - unfold k_o in Ha. unfold k_inv, k_bad in *.
    destruct Ha as [<- | [<- | [<- | [<- | []]]]]; simpl dstep; unfold fstep, upd; simpl in *;
      destruct (b1 (t 0)), (b1 (t 1)), (b1 (t 2)), (b2 (t 2)), (b1 (t 3)), (b2 (t 3)), (b3 (t 3));
      simpl in *; intuition congruence.
Qed.

Lemma k_inv_run : forall p t, Forall (okact kev k_o) p -> k_inv t -> k_inv (drun q4 k_f kev k_reg k_sig p t).
Proof.
  induction p as [| a p IH]; intros t Hp Ht; [exact Ht |].
  inversion Hp as [| ? ? Ha Hp']; subst. simpl. apply IH; [exact Hp' | apply k_inv_step; assumption].
Qed.

Lemma k_inv_s0 : k_inv k_s0.
Proof. split; [intros H; discriminate H | reflexivity]. Qed.

(* XU holds at every state satisfying the invariant. *)
Lemma k_xuat : forall t e, k_inv t -> XUat q4 k_f k_rho kev k_reg k_sig k_o t e.
Proof.
  intros t [] [H1 H2]; unfold XUat.
  - simpl. reflexivity.
  - assert (Hm : k_sig Mark (t 3) = t 3) by (unfold k_sig; rewrite H2; reflexivity).
    cbn [k_reg]. rewrite Hm. unfold N, frun, k_o. simpl. unfold fstep, upd, k_rho. simpl.
    destruct (b1 (t 0)); reflexivity.
Qed.

Definition k_run (w : list (cact kev)) := crun q4 k_f kev k_reg k_sig true w (init q4 k_s0).

(* The channel run: 1 is sent the snapshot with 0 unset; 0 flips; 2 is sent (0 set, 1 still
   showing its stale set flag) and applies it; then 1 applies its late projection (0 unset); 3 is
   sent (1 unset, 2 showing both set) and applies it. *)
Definition k_w : list (cact kev) :=
  [CSend 1 1; CEv Flip; CSend 2 1; CDel 2 0; CDel 1 0; CSend 3 1; CDel 3 0].

Lemma k_not_nested : forall rt, (forall k, rt k = true -> forall z x, k_f k z x = x) -> ~ Nested k_src k_o rt.
Proof.
  intros rt HR HN.
  assert (R3 : rt 3 = false).
  { destruct (rt 3) eqn:R; [| reflexivity]. pose proof (HR 3 R (fun _ => Q4 true true true true) qF) as H.
    discriminate H. }
  assert (R2 : rt 2 = false).
  { destruct (rt 2) eqn:R; [| reflexivity]. pose proof (HR 2 R (fun _ => Q4 true true true true) qF) as H.
    discriminate H. }
  assert (H23 : Rch k_src k_o 2 3).
  { apply (rch_step k_src k_o 2 3 2); [unfold k_o; simpl; tauto | simpl; tauto | constructor]. }
  pose proof (HN 3 2 1 ltac:(unfold k_o; simpl; tauto) R3 R2 ltac:(discriminate) H23 ltac:(simpl; tauto)) as H21.
  destruct (rch_order k_src k_o k_topo 2 1 H21) as [E' | [_ [C | C]]]; [discriminate E' | | simpl in C; lia].
  apply C. unfold k_o. simpl. tauto.
Qed.

(* Counterexample: beyond nested networks, versioned channels reach a stale combination the
   current-value model never produces. On this four-registry network (Common), reachable XU holds
   from k_s0 (so DistConv, dist_exact), registry 3 never shows the combination in the
   current-value model, but a disciplined versioned channel run shows it, XU fails there, and the
   channels diverge, compared after a flush and at drain. gsm's static XU rejects Mark. *)
Theorem vchan_skip_counterexample :
  Common q4 k_src k_f k_valid k_rho kev k_reg k_sig k_o /\
  (forall rt, (forall k, rt k = true -> forall z x, k_f k z x = x) -> ~ Nested k_src k_o rt) /\
  (forall p, Forall (okact kev k_o) p -> k_bad (drun q4 k_f kev k_reg k_sig p k_s0 3) = false) /\
  XUR q4 k_f k_rho kev k_reg k_sig k_o k_s0 /\
  C2R q4 k_f k_rho kev k_reg k_sig k_I k_o (N q4 k_f k_rho k_o k_s0) /\
  DistConv q4 k_f k_rho kev k_reg k_sig k_I k_o k_s0 /\
  Forall (okc kev k_o) k_w /\ disc q4 k_f kev k_reg k_sig true k_w (init q4 k_s0) /\
  cs q4 (k_run k_w) 3 = Q4 false true true false /\ k_bad (cs q4 (k_run k_w) 3) = true /\
  ~ XUat q4 k_f k_rho kev k_reg k_sig k_o (cs q4 (k_run k_w)) Mark /\
  ~ CXUR q4 k_f k_rho kev k_reg k_sig k_o true k_s0 /\
  ~ ChanConv q4 k_f k_rho kev k_reg k_sig k_I k_o true k_s0 /\
  ~ SettleConv q4 k_f kev k_reg k_sig k_I k_o k_s0 /\
  ~ XU q4 k_f k_valid kev k_reg k_sig.
Proof.
  pose proof k_common as HC.
  assert (Hi : Inv q4 k_valid k_s0) by (intros k; exact Logic.I).
  assert (Hx : XUR q4 k_f k_rho kev k_reg k_sig k_o k_s0).
  { intros p e Hp. apply k_xuat. apply k_inv_run; [exact Hp | exact k_inv_s0]. }
  assert (H2 : C2R q4 k_f k_rho kev k_reg k_sig k_I k_o (N q4 k_f k_rho k_o k_s0))
    by (intros p e1 e2 _ HI; destruct HI).
  assert (Ok : Forall (okc kev k_o) k_w) by (repeat constructor; unfold k_o; simpl; tauto).
  assert (Dc : disc q4 k_f kev k_reg k_sig true k_w (init q4 k_s0))
    by (simpl; unfold setn; simpl; repeat split; lia).
  assert (Nx : ~ XUat q4 k_f k_rho kev k_reg k_sig k_o (cs q4 (k_run k_w)) Mark)
    by (intro H; vm_compute in H; discriminate H).
  assert (Nc : ~ CXUR q4 k_f k_rho kev k_reg k_sig k_o true k_s0)
    by (intro H; exact (Nx (H k_w Mark Ok Dc))).
  split; [exact HC |]. split; [exact k_not_nested |].
  split; [intros p Hp; exact (proj2 (k_inv_run p k_s0 Hp k_inv_s0)) |].
  split; [exact Hx |]. split; [exact H2 |].
  split; [apply (proj2 (dist_exact _ _ _ _ _ _ _ _ _ _ HC k_s0 Hi)); split; assumption |].
  split; [exact Ok |]. split; [exact Dc |].
  split; [reflexivity |]. split; [reflexivity |]. split; [exact Nx |]. split; [exact Nc |].
  assert (Nch : ~ ChanConv q4 k_f k_rho kev k_reg k_sig k_I k_o true k_s0)
    by (intro H; apply Nc; exact (proj1 (proj1 (chan_exact _ _ _ _ _ _ _ _ _ _ HC true k_s0 Hi) H))).
  split; [exact Nch |]. split.
  - intro H. apply Nch. exact (proj1 (vsettle_exact _ _ _ _ _ _ _ _ _ _ HC k_s0 Hi) H).
  - intro H. specialize (H Mark (fun _ => Q4 true true true true) (Q4 false true true false)
                          (fun _ => Logic.I) Logic.I).
    vm_compute in H. discriminate H.
Qed.

(* Non-vacuity of the single-source theorem beyond two-level networks: the chain 0 -> 1 -> 2,
   registry 1 copying 0's flag and registry 2 copying 1's (a projection of a projection), with a
   local event Mark on 2. It is not two-level for any marking of pure roots. *)
Definition ch_src (k : nat) : list nat := match k with 1 => [0] | 2 => [1] | _ => [] end.

Definition ch_f (k : nat) (z : nat -> q4) (x : q4) : q4 :=
  match k with
  | 1 => Q4 (b1 (z 0)) (b2 x) (b3 x) (b4 x)
  | 2 => Q4 (b1 (z 1)) (b2 x) (b3 x) (b4 x)
  | _ => x
  end.

Definition ch_reg (e : kev) : nat := match e with Flip => 0 | Mark => 2 end.

Definition ch_sig (e : kev) (x : q4) : q4 :=
  match e with Flip => Q4 true (b2 x) (b3 x) (b4 x) | Mark => Q4 (b1 x) true (b3 x) (b4 x) end.

Definition ch_o : list nat := [0; 1; 2].

Lemma ch_common : Common q4 ch_src ch_f k_valid k_rho kev ch_reg ch_sig ch_o.
Proof.
  constructor.
  - intros [| [| [| j]]] z1 z2 x H; simpl; try reflexivity.
    + rewrite (H 0); [reflexivity | left; reflexivity].
    + rewrite (H 1); [reflexivity | left; reflexivity].
  - unfold ch_o. simpl. repeat split.
    + intros [H | [H | []]]; discriminate.
    + intros k [].
    + intros [H | []]; discriminate.
    + intros k [<- | []] [H | [H | []]]; discriminate.
    + intros [].
    + intros k [<- | []] [H | []]; discriminate.
  - intros. exact Logic.I.
  - intros [| [| [| j]]] z z' x _ _ _; reflexivity.
  - intros. reflexivity.
  - intros. exact Logic.I.
  - intros []; unfold ch_o; simpl; tauto.
Qed.

Theorem chain_instance :
  Common q4 ch_src ch_f k_valid k_rho kev ch_reg ch_sig ch_o /\ SingleSource ch_src ch_o /\
  (forall rt, ~ TwoLevel q4 ch_src ch_f rt) /\
  forall s0, Inv q4 k_valid s0 ->
    (CXUR q4 ch_f k_rho kev ch_reg ch_sig ch_o true s0 <-> XUR q4 ch_f k_rho kev ch_reg ch_sig ch_o s0) /\
    XUR q4 ch_f k_rho kev ch_reg ch_sig ch_o s0 /\
    SettleConv q4 ch_f kev ch_reg ch_sig k_I ch_o s0 /\ DistConv q4 ch_f k_rho kev ch_reg ch_sig k_I ch_o s0.
Proof.
  pose proof ch_common as HC.
  assert (HS : SingleSource ch_src ch_o).
  { intros j _ k k' Hk Hk'. destruct j as [| [| [| j]]]; simpl in *; try contradiction;
      destruct Hk as [<- | []]; destruct Hk' as [<- | []]; reflexivity. }
  assert (HX : XU q4 ch_f k_valid kev ch_reg ch_sig) by (intros [] z b _ _; reflexivity).
  assert (H2 : C2 q4 ch_f k_valid kev ch_reg ch_sig k_I) by (intros e1 e2 z b _ HI; destruct HI).
  split; [exact HC |]. split; [exact HS |].
  split.
  - intros rt HT. destruct (rt 1) eqn:R.
    + pose proof (proj1 (HT 1) R (fun _ => Q4 true true true true) qF) as H. discriminate H.
    + exact (proj2 (HT 1) R 2 (or_introl eq_refl)).
  - intros s0 Hi. destruct (vchan_single_exact _ _ _ _ _ _ _ _ k_I _ HC HS s0 Hi) as [A [_ [_ D]]].
    pose proof (vsettle_xu_c2 _ _ _ _ _ _ _ _ _ _ HC HX H2 s0 Hi) as S.
    split; [exact A |]. split; [exact (xu_xur _ _ _ _ _ _ _ _ _ HC HX s0 Hi) |].
    split; [exact S | exact (proj1 D S)].
Qed.
