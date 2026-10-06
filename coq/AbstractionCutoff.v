(* AbstractionCutoff.v: abstraction for checking, check relationships between values, not the
   values (roadmap item 8, step 2; gsm roadmap item 1b). Axiom-free.

   Model. A registry over integer-valued states: a state is a list of n integers (the variables),
   an event is (k, p), a kind k with a list p of integer parameters, apply ap, a repair step rp
   (leaving valid states alone, rp_fix) and an invariant vd. It is an instance of Governance.v's
   rewrite system with free delivery. Repair is bounded: TermK says that K repair steps reach a
   valid state from every state, and then the governed step is govK e s = rp^K (ap e s).
   - un_bounded: under TermK, every buffer from every state has a unique normal form iff CC1 and
     CC2 hold at every state (GovernanceConverse.cc_exact_from at each start).

   Order-invariant fragment (section OrderInvariant). Declared constants C. OIso C X f: f
   preserves the order (Z.compare) on the values X together with C and fixes every constant.
   OrdInv: apply, repair and the invariant commute with every such f (rules compare values and
   the declared constants, and copy them). The representative domain reps N C is C, the N
   integers above each constant, and N integers below the least one (or 0 .. N-1 when C is
   empty): exactly length C * (N + 1) + N values (reps_length).
   - compress: for any finite list X of values, cmp C X is an order isomorphism on X and C that
     fixes C and maps X into reps (length X) C.
   - Cutoffs: TermK over Z iff over reps N C for N >= n (term_abs); a WFC potential over Z iff
     one over the representative states (wfc_abs, N >= n); CC1 over Z iff over reps N C for
     N >= n + 2m (cc1_abs); CC2 for N >= n + m (cc2_abs); given TermK over the representatives,
     unique normal forms for every start and buffer iff CC1 and CC2 over them (un_abs).
   - One check per order type: each CC1 and CC2 instance has the truth value of every instance
     with the same order type (cc1_order_type, cc2_order_type).
   - abs_check: the finite boolean check over reps N C; abs_check_exact: it passes iff TermK and
     unique normal forms hold over all of Z.
   - closure_ap, closure_rp: order invariance forces rules to output only input values and
     constants (no fresh values).

   The fragment decided (section Syntax). A rule language with variables, integer constants,
   +, -, *, if-then-else and comparisons. ord_frag C P (only comparisons among variables and
   declared constants, no arithmetic) is a boolean check, sound for OrdInv (ord_frag_sound).
   build_sound: wf, ord_frag and abs_check imply unique normal forms over all of Z.

   Linear fragment (section Linear). Every program in the language: the conditions are generated
   as quantifier-free formulas over n + 2m integer variables (phi_term, phi_cc1, phi_cc2),
   and each condition holds over Z iff its formula is valid (phi_term_exact, phi_cc1_exact,
   phi_cc2_exact, lin_exact). lin_frag (multiplication only by a literal) makes every generated
   formula linear (lin_frag_linear), so the formulas are Presburger (QF_LIA with if-then-else)
   and decidable by an SMT solver. The solver is the external trusted step; the theorem is what
   makes its answer about convergence. No finite representative set is claimed here.

   Boundaries.
   - exact13_*: an undeclared exact test "if amount = 13 then x := tag" passes the
     representative check over reps 5 [] and diverges over Z; ord_frag refuses it; with 13
     declared it is in the fragment and the check over reps 5 [13] fails, as it should.
   - triangle_*: an additive guard x < y < z < x + y passes the order-pattern check over reps 3 []
     and diverges at (2, 3, 4); ord_frag refuses it and its CC1 formula is refuted at (2, 3, 4).
   - copy_tight: the cutoff cannot drop below n (two variables need two representatives).
   Non-vacuity.
   - capped_*: capped inventory (restock to a level, repair clamps at the declared cap 5),
     checked over 7 representatives, converges for every integer state and buffer.
   - wallet_*: a wallet with integer balances (deposit, withdraw, overdraft flag maintained by
     repair) in the linear fragment: its formulas are valid (proved here as a solver would), so it
     converges for every integer balance and buffer.
   - sym_abs, capped_catalog: composed with SymmetryCutoff.un_cutoff, a catalog of any size of
     capped items converges, through one item checked over 7 representatives. *)

Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.SymmetryCutoff.
From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.

(* ============================================================================================ *)
(* List helpers.                                                                                *)
(* ============================================================================================ *)

Lemma lenA : forall {A : Type} (l1 l2 : list A), length (l1 ++ l2) = (length l1 + length l2)%nat.
Proof. intros A l1 l2. induction l1 as [|x l1 IH]; simpl; auto. Qed.

Lemma lenM : forall {A B : Type} (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f l. induction l as [|x l IH]; simpl; auto. Qed.

Lemma lenS : forall a k, length (seq a k) = k.
Proof. intros a k. revert a. induction k as [|k IH]; intros a; simpl; auto. Qed.

Lemma lenF : forall {A : Type} (P : A -> bool) l, (length (filter P l) <= length l)%nat.
Proof. intros A P l. induction l as [|x l IH]; simpl; [lia|]. destruct (P x); simpl; lia. Qed.

Lemma nodup_filter' : forall {A : Type} (P : A -> bool) l, NoDup l -> NoDup (filter P l).
Proof.
  intros A P l H. induction H as [|x l Hn Hd IH]; simpl; [constructor|].
  destruct (P x); [|exact IH]. constructor; [|exact IH].
  intros Hin. apply filter_In in Hin. apply Hn. apply Hin.
Qed.

Lemma filter_le : forall {A : Type} (P Q : A -> bool) l,
  (forall x, In x l -> P x = true -> Q x = true) -> (length (filter P l) <= length (filter Q l))%nat.
Proof.
  intros A P Q l. induction l as [|x l IH]; intros H; simpl; [lia|].
  assert (IH' : (length (filter P l) <= length (filter Q l))%nat) by (apply IH; intros y Hy; apply H; right; exact Hy).
  destruct (P x) eqn:Hp.
  - rewrite (H x (or_introl eq_refl) Hp). simpl. lia.
  - destruct (Q x); simpl; lia.
Qed.

Lemma filter_lt : forall {A : Type} (P Q : A -> bool) l y,
  (forall x, In x l -> P x = true -> Q x = true) -> In y l -> Q y = true -> P y = false ->
  (length (filter P l) < length (filter Q l))%nat.
Proof.
  intros A P Q l y. induction l as [|x l IH]; intros H Hy HQ HP; simpl; [destruct Hy|].
  assert (Hle : (length (filter P l) <= length (filter Q l))%nat)
    by (apply filter_le; intros z Hz; apply H; right; exact Hz).
  destruct Hy as [<- | Hy].
  - rewrite HP, HQ. simpl. lia.
  - assert (Hlt : (length (filter P l) < length (filter Q l))%nat)
      by (apply IH; [intros z Hz; apply H; right; exact Hz | exact Hy | exact HQ | exact HP]).
    destruct (P x) eqn:Hp.
    + rewrite (H x (or_introl eq_refl) Hp). simpl. lia.
    + destruct (Q x); simpl; lia.
Qed.

Lemma filter_all : forall {A : Type} (l : list A), filter (fun _ => true) l = l.
Proof. intros A l. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma filter_nil : forall {A : Type} (P : A -> bool) l, (forall x, In x l -> P x = false) -> filter P l = [].
Proof.
  intros A P l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma map_fix_in : forall (f : Z -> Z) l, (forall x, In x l -> f x = x) -> map f l = l.
Proof.
  intros f l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma map_fix_pt : forall (f : Z -> Z) l v, map f l = l -> In v l -> f v = v.
Proof.
  intros f l v. induction l as [|x l IH]; intros H Hv; simpl in *; [contradiction|].
  injection H as H1 H2. destruct Hv as [<- | Hv]; [exact H1 | exact (IH H2 Hv)].
Qed.

(* Integers in (a, b]: a NoDup list of them has at most b - a elements. *)
Lemma nodup_interval : forall (l : list Z) a b, NoDup l -> (forall x, In x l -> a < x <= b)%Z ->
  (length l <= Z.to_nat (b - a))%nat.
Proof.
  intros l a b Hd H.
  set (ints := map (fun i => a + 1 + Z.of_nat i)%Z (seq 0 (Z.to_nat (b - a)))).
  replace (Z.to_nat (b - a)) with (length ints) by (unfold ints; rewrite lenM, lenS; reflexivity).
  apply NoDup_incl_length; [exact Hd|]. intros x Hx. specialize (H x Hx).
  unfold ints. apply in_map_iff. exists (Z.to_nat (x - a - 1)). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. split; [lia|]. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
Qed.

(* ============================================================================================ *)
(* Bounded repair: unique normal forms over every state iff CC1 and CC2 at every state.         *)
(* ============================================================================================ *)

Section Bounded.
  Context {E : Type}.
  Variable edec : forall x y : E, {x = y} + {x <> y}.
  Variable ap : E -> list Z -> list Z.     (* apply *)
  Variable rp : list Z -> list Z.          (* repair step *)
  Variable vd : list Z -> bool.            (* invariant *)
  Variable n K : nat.                      (* number of variables; repair bound *)

  Definition TermK : Prop := forall s, length s = n -> vd (itr K rp s) = true.
  Definition govK (e : E) (s : list Z) : list Z := itr K rp (ap e s).
  Definition CC1Z : Prop :=
    forall s e1 e2, length s = n -> govK e2 (govK e1 s) = govK e1 (govK e2 s).
  Definition CC2Z : Prop :=
    forall s e, length s = n -> vd s = false -> govK e s = govK e (rp s).
  Definition UNZ : Prop :=
    forall s, length s = n -> forall B, UN (step edec ap rp (valid1 vd) free_enabled) (s, B).

  Hypothesis len_ap : forall e s, length s = n -> length (ap e s) = n.
  Hypothesis len_rp : forall s, vd s = false -> length (rp s) = n.
  Hypothesis rp_fix : forall s, vd s = true -> rp s = s.

  Lemma rp_len : forall s, length s = n -> length (rp s) = n.
  Proof.
    intros s H. destruct (vd s) eqn:Hv; [rewrite (rp_fix s Hv); exact H | exact (len_rp s Hv)].
  Qed.

  Lemma itr_len : forall j s, length s = n -> length (itr j rp s) = n.
  Proof. induction j as [|j IH]; intros s H; simpl; [exact H | apply IH, rp_len, H]. Qed.

  Lemma itr_stable_after : forall j i s, vd (itr j rp s) = true -> itr (j + i) rp s = itr j rp s.
  Proof. intros j i s H. rewrite itr_add. apply itr_fix. apply rp_fix. exact H. Qed.

  Lemma itr_valid_mono : forall j i s, vd (itr j rp s) = true -> vd (itr (j + i) rp s) = true.
  Proof. intros j i s H. rewrite itr_stable_after by exact H. exact H. Qed.

  Lemma govK_len : forall e s, length s = n -> length (govK e s) = n.
  Proof. intros e s H. unfold govK. apply itr_len, len_ap, H. Qed.

  Fixpoint steps (j : nat) (s : list Z) : nat :=
    match j with 0 => 0 | S j' => if vd s then 0 else S (steps j' (rp s)) end.

  Lemma steps_stable : forall j t, vd (itr j rp t) = true -> steps (S j) t = steps j t.
  Proof.
    induction j as [|j IH]; intros t H; simpl in *.
    - rewrite H. reflexivity.
    - destruct (vd t) eqn:Hv; [reflexivity|]. f_equal. apply IH. exact H.
  Qed.

  Lemma reachB : forall j s B,
    star (step edec ap rp (valid1 vd) free_enabled) (s, B) (itr j rp s, B).
  Proof.
    induction j as [|j IH]; intros s B; simpl; [apply star_refl|].
    destruct (vd s) eqn:Hv.
    - rewrite (rp_fix s Hv). apply IH.
    - eapply star_step; [apply st_comp; unfold valid1; congruence | apply IH].
  Qed.

  Lemma reach_len : forall s0 s, reach ap rp (valid1 vd) s0 s -> length s0 = n -> length s = n.
  Proof.
    intros s0 s H H0. induction H as [| e s H IH | s H IH Hinv];
      [exact H0 | apply len_ap, IH | apply rp_len, IH].
  Qed.

  Section WithTerm.
    Hypothesis term : TermK.

    Lemma term_all : forall s, vd (itr (S K) rp s) = true.
    Proof.
      intros s. simpl. destruct (vd s) eqn:Hv.
      - rewrite (rp_fix s Hv). rewrite itr_fix by (apply rp_fix; exact Hv). exact Hv.
      - apply term. apply len_rp. exact Hv.
    Qed.

    (* The potential: the number of repair steps to validity. *)
    Definition PhiB (s : list Z) : nat := steps (S K) s.
    Definition rstarB (s : list Z) : list Z := itr (S K) rp s.

    Lemma wfcB : forall s, ~ valid1 vd s -> PhiB (rp s) < PhiB s.
    Proof.
      intros s Hs. unfold valid1 in Hs. unfold PhiB.
      assert (Hv : vd s = false) by (destruct (vd s); [contradiction | reflexivity]).
      rewrite (steps_stable K (rp s)) by (apply term, len_rp, Hv).
      simpl. rewrite Hv. lia.
    Qed.

    Lemma rstarB_valid : forall s, valid1 vd (rstarB s).
    Proof. intros s. exact (term_all s). Qed.

    Lemma rstarB_gov : forall e s, length s = n -> rstarB (ap e s) = govK e s.
    Proof.
      intros e s H. unfold rstarB, govK. replace (S K) with (K + 1)%nat by lia.
      apply itr_stable_after. apply term. apply len_ap. exact H.
    Qed.

    (* Unique normal forms from every state of length n, for every buffer, iff CC1 and CC2. *)
    Theorem un_bounded : UNZ <-> CC1Z /\ CC2Z.
    Proof.
      pose proof (fun s0 => cc_exact_from edec ap rp rstarB (valid1 vd) PhiB wfcB
                              (fun s B => reachB (S K) s B) rstarB_valid s0) as HX.
      split.
      - intros H. split.
        + intros s e1 e2 Hs. destruct (proj1 (HX s) (H s Hs)) as [C1 _].
          assert (Hr : reach ap rp (valid1 vd) s s) by constructor.
          pose proof (C1 s e1 e2 Hr) as Eq.
          rewrite (rstarB_gov e1 s Hs), (rstarB_gov e2 s Hs) in Eq.
          rewrite (rstarB_gov e2 _ (govK_len e1 s Hs)), (rstarB_gov e1 _ (govK_len e2 s Hs)) in Eq.
          exact Eq.
        + intros s e Hs Hv. destruct (proj1 (HX s) (H s Hs)) as [_ C2].
          assert (Hr : reach ap rp (valid1 vd) s s) by constructor.
          assert (Hn : ~ valid1 vd s) by (unfold valid1; congruence).
          pose proof (C2 s e Hr Hn) as Eq.
          rewrite (rstarB_gov e s Hs), (rstarB_gov e (rp s) (rp_len s Hs)) in Eq. exact Eq.
      - intros [C1 C2] s Hs B. apply (proj2 (HX s)). split.
        + intros sg e1 e2 Hr. pose proof (reach_len s sg Hr Hs) as Hl.
          rewrite (rstarB_gov e1 sg Hl), (rstarB_gov e2 sg Hl).
          rewrite (rstarB_gov e2 _ (govK_len e1 sg Hl)), (rstarB_gov e1 _ (govK_len e2 sg Hl)).
          apply C1. exact Hl.
        + intros sg e Hr Hn. pose proof (reach_len s sg Hr Hs) as Hl.
          rewrite (rstarB_gov e sg Hl), (rstarB_gov e (rp sg) (rp_len sg Hl)).
          apply C2; [exact Hl|]. unfold valid1 in Hn. destruct (vd sg); [contradiction | reflexivity].
    Qed.

    (* A CC1 failure at a start refutes unique normal forms from that start. *)
    Lemma un_at : forall s, length s = n ->
      (forall B, UN (step edec ap rp (valid1 vd) free_enabled) (s, B)) ->
      forall e1 e2, govK e2 (govK e1 s) = govK e1 (govK e2 s).
    Proof.
      intros s Hs H e1 e2.
      destruct (proj1 (cc_exact_from edec ap rp rstarB (valid1 vd) PhiB wfcB
                         (fun s B => reachB (S K) s B) rstarB_valid s) H) as [C1 _].
      assert (Hr : reach ap rp (valid1 vd) s s) by constructor.
      pose proof (C1 s e1 e2 Hr) as Eq.
      rewrite (rstarB_gov e1 s Hs), (rstarB_gov e2 s Hs) in Eq.
      rewrite (rstarB_gov e2 _ (govK_len e1 s Hs)), (rstarB_gov e1 _ (govK_len e2 s Hs)) in Eq.
      exact Eq.
    Qed.
  End WithTerm.
End Bounded.

(* ============================================================================================ *)
(* Order isomorphisms fixing the declared constants, and the compression into representatives. *)
(* ============================================================================================ *)

(* f preserves the order on X together with C, and fixes every constant. *)
Definition OIso (C X : list Z) (f : Z -> Z) : Prop :=
  (forall x y, In x (X ++ C) -> In y (X ++ C) -> Z.compare (f x) (f y) = Z.compare x y) /\
  (forall c, In c C -> f c = c).

Lemma oiso_sub : forall C X Y f, incl Y (X ++ C) -> OIso C X f -> OIso C Y f.
Proof.
  intros C X Y f Hi [H1 H2]. split; [|exact H2]. intros x y Hx Hy.
  assert (G : forall z, In z (Y ++ C) -> In z (X ++ C)).
  { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz]; [apply Hi; exact Hz|].
    apply in_or_app. right. exact Hz. }
  apply H1; apply G; assumption.
Qed.

Lemma oiso_inj : forall C X f l1 l2, OIso C X f -> incl l1 (X ++ C) -> incl l2 (X ++ C) ->
  map f l1 = map f l2 -> l1 = l2.
Proof.
  intros C X f l1. induction l1 as [|x l1 IH]; intros [|y l2] Hf H1 H2 Hm; simpl in Hm;
    try discriminate; [reflexivity|].
  injection Hm as Hxy Hm. f_equal.
  - destruct Hf as [Hc _].
    pose proof (Hc x y (H1 x (or_introl eq_refl)) (H2 y (or_introl eq_refl))) as E.
    rewrite Hxy, Z.compare_refl in E. symmetry in E. apply Z.compare_eq_iff in E. exact E.
  - apply IH; [exact Hf | intros z Hz; apply H1; right; exact Hz
              | intros z Hz; apply H2; right; exact Hz | exact Hm].
Qed.

Lemma oiso_lt : forall C X f x y, OIso C X f -> In x (X ++ C) -> In y (X ++ C) ->
  (x < y <-> f x < f y)%Z.
Proof.
  intros C X f x y [Hc _] Hx Hy. rewrite <- !Z.compare_lt_iff, (Hc x y Hx Hy). reflexivity.
Qed.

Lemma oiso_le : forall C X f x y, OIso C X f -> In x (X ++ C) -> In y (X ++ C) ->
  (x <= y <-> f x <= f y)%Z.
Proof.
  intros C X f x y [Hc _] Hx Hy. rewrite <- !Z.compare_le_iff, (Hc x y Hx Hy). reflexivity.
Qed.

Lemma oiso_eq : forall C X f x y, OIso C X f -> In x (X ++ C) -> In y (X ++ C) ->
  (x = y <-> f x = f y).
Proof.
  intros C X f x y [Hc _] Hx Hy. rewrite <- !Z.compare_eq_iff, (Hc x y Hx Hy). reflexivity.
Qed.

(* The greatest constant at or below v. *)
Fixpoint lo (C : list Z) (v : Z) : option Z :=
  match C with
  | [] => None
  | c :: C' => match lo C' v with
               | None => if Z.leb c v then Some c else None
               | Some d => if Z.leb c v then Some (Z.max c d) else Some d
               end
  end.

Lemma lo_none : forall C v, lo C v = None -> forall c, In c C -> (v < c)%Z.
Proof.
  induction C as [|c C IH]; intros v H c' Hc'; [destruct Hc'|]. simpl in H.
  destruct (lo C v) as [d|] eqn:Hl; [destruct (Z.leb c v); discriminate|].
  destruct (Z.leb_spec c v) as [H0 | H0]; [discriminate|].
  destruct Hc' as [<- | Hc']; [exact H0 | exact (IH v Hl c' Hc')].
Qed.

Lemma lo_some : forall C v d, lo C v = Some d ->
  In d C /\ (d <= v)%Z /\ forall c, In c C -> (c <= v)%Z -> (c <= d)%Z.
Proof.
  induction C as [|c C IH]; intros v d H; simpl in H; [discriminate|].
  destruct (lo C v) as [d'|] eqn:Hl.
  - destruct (IH v d' Hl) as [Hi [Hv Hm]].
    destruct (Z.leb_spec c v) as [Hc | Hc]; injection H as <-.
    + split; [destruct (Z.max_spec c d') as [[_ ->] | [_ ->]]; [right; exact Hi | left; reflexivity]|].
      split; [lia|]. intros c' [<- | Hc'] Hc'v; [lia|]. specialize (Hm c' Hc' Hc'v). lia.
    + split; [right; exact Hi|]. split; [exact Hv|]. intros c' [<- | Hc'] Hc'v; [lia|].
      exact (Hm c' Hc' Hc'v).
  - pose proof (lo_none C v Hl) as Hn.
    destruct (Z.leb_spec c v) as [Hc | Hc]; [|discriminate]. injection H as <-.
    split; [left; reflexivity|]. split; [exact Hc|].
    intros c' [<- | Hc'] Hc'v; [lia|]. specialize (Hn c' Hc'). lia.
Qed.

Lemma lo_const : forall C c, In c C -> lo C c = Some c.
Proof.
  intros C c Hc. destruct (lo C c) as [d|] eqn:Hl.
  - destruct (lo_some C c d Hl) as [_ [Hd Hm]]. specialize (Hm c Hc (Z.le_refl c)).
    f_equal. lia.
  - pose proof (lo_none C c Hl c Hc). lia.
Qed.

(* The least constant (0 when there is none). *)
Definition mn (C : list Z) : Z := match C with [] => 0%Z | c :: C' => fold_right Z.min c C' end.

Lemma mn_spec : forall c C', In (mn (c :: C')) (c :: C') /\ forall d, In d (c :: C') -> (mn (c :: C') <= d)%Z.
Proof.
  intros c C'. simpl. induction C' as [|x C' [IH1 IH2]]; simpl.
  - split; [left; reflexivity|]. intros d [<- | []]. lia.
  - split.
    + destruct (Z.min_spec x (fold_right Z.min c C')) as [[_ ->] | [_ ->]].
      * right; left; reflexivity.
      * destruct IH1 as [<- | H]; [left; reflexivity | right; right; exact H].
    + intros d [Hd | [Hd | Hd]].
      * subst d. specialize (IH2 c (or_introl eq_refl)). lia.
      * subst d. lia.
      * specialize (IH2 d (or_intror Hd)). lia.
Qed.

(* Number of distinct values of X satisfying P. *)
Definition cnt (P : Z -> bool) (X : list Z) : nat := length (filter P (nodup Z.eq_dec X)).

Lemma cnt_le : forall P Q X, (forall x, In x X -> P x = true -> Q x = true) -> (cnt P X <= cnt Q X)%nat.
Proof. intros P Q X H. apply filter_le. intros x Hx. apply H. apply (nodup_In Z.eq_dec). exact Hx. Qed.

Lemma cnt_lt : forall P Q X y, (forall x, In x X -> P x = true -> Q x = true) -> In y X ->
  Q y = true -> P y = false -> (cnt P X < cnt Q X)%nat.
Proof.
  intros P Q X y H Hy HQ HP. apply (filter_lt P Q _ y); [| apply nodup_In; exact Hy | exact HQ | exact HP].
  intros x Hx. apply H. apply (nodup_In Z.eq_dec). exact Hx.
Qed.

Lemma cnt_len : forall P X, (cnt P X <= length X)%nat.
Proof.
  intros P X. unfold cnt. eapply Nat.le_trans; [apply lenF|].
  apply NoDup_incl_length; [apply NoDup_nodup|]. intros x Hx. apply nodup_In in Hx. exact Hx.
Qed.

Lemma cnt_len_lt : forall P X y, In y X -> P y = false -> (cnt P X < length X)%nat.
Proof.
  intros P X y Hy Hp. unfold cnt. eapply Nat.lt_le_trans.
  - apply (filter_lt P (fun _ => true) _ y); [auto | apply nodup_In; exact Hy | reflexivity | exact Hp].
  - rewrite filter_all. apply NoDup_incl_length; [apply NoDup_nodup|].
    intros x Hx. apply nodup_In in Hx. exact Hx.
Qed.

Lemma cnt_pos : forall P X y, In y X -> P y = true -> (1 <= cnt P X)%nat.
Proof.
  intros P X y Hy Hp.
  assert (H : (cnt (fun _ => false) X < cnt P X)%nat)
    by (apply (cnt_lt _ P X y); [intros x _ Hx; discriminate Hx | exact Hy | exact Hp | reflexivity]).
  unfold cnt in H at 1. rewrite filter_nil in H by (intros; reflexivity). simpl in H. lia.
Qed.

Lemma cnt_interval : forall X a v, (a <= v)%Z ->
  (Z.of_nat (cnt (fun x => Z.ltb a x && Z.leb x v) X) <= v - a)%Z.
Proof.
  intros X a v Hav. unfold cnt.
  pose proof (nodup_interval (filter (fun x => Z.ltb a x && Z.leb x v) (nodup Z.eq_dec X)) a v
                (nodup_filter' _ _ (NoDup_nodup Z.eq_dec X))) as H.
  assert (Hb : forall x, In x (filter (fun x => Z.ltb a x && Z.leb x v) (nodup Z.eq_dec X)) -> (a < x <= v)%Z).
  { intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx]. apply andb_true_iff in Hx.
    destruct Hx as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. lia. }
  specialize (H Hb). apply Nat2Z.inj_le in H. rewrite Z2Nat.id in H by lia. exact H.
Qed.

(* The compression of X: order type and constants kept, values moved next to the constants. *)
Definition cmp (C X : list Z) (v : Z) : Z :=
  match lo C v with
  | Some a => (a + Z.of_nat (cnt (fun x => Z.ltb a x && Z.leb x v) X))%Z
  | None => match C with
            | [] => Z.of_nat (cnt (fun x => Z.ltb x v) X)
            | _ => (mn C - Z.of_nat (cnt (fun x => Z.leb v x && Z.ltb x (mn C)) X))%Z
            end
  end.

(* The representatives: C, the N integers above each constant, and N below the least one. *)
Definition reps (N : nat) (C : list Z) : list Z :=
  C ++ flat_map (fun c => map (fun i => c + Z.of_nat i)%Z (seq 1 N)) C ++
  match C with
  | [] => map Z.of_nat (seq 0 N)
  | _ => map (fun i => mn C - Z.of_nat i)%Z (seq 1 N)
  end.

Theorem reps_length : forall N C, length (reps N C) = (length C * (N + 1) + N)%nat.
Proof.
  intros N C. unfold reps. rewrite !lenA.
  assert (Hf : length (flat_map (fun c => map (fun i => c + Z.of_nat i)%Z (seq 1 N)) C) = (length C * N)%nat).
  { induction C as [|c C IH]; simpl; [reflexivity|]. rewrite lenA, lenM, lenS, IH. lia. }
  rewrite Hf. destruct C; simpl; rewrite lenM, lenS; lia.
Qed.

Lemma reps_C : forall N C, incl C (reps N C).
Proof. intros N C c Hc. unfold reps. apply in_or_app. left. exact Hc. Qed.

Lemma reps_mono : forall N1 N2 C, (N1 <= N2)%nat -> incl (reps N1 C) (reps N2 C).
Proof.
  intros N1 N2 C Hle x Hx. unfold reps in *.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [apply in_or_app; left; exact Hx|].
  apply in_or_app; right. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - apply in_or_app; left. apply in_flat_map in Hx. destruct Hx as [c [Hc Hx]].
    apply in_flat_map. exists c. split; [exact Hc|]. apply in_map_iff in Hx.
    destruct Hx as [i [<- Hi]]. apply in_map_iff. exists i. split; [reflexivity|].
    apply in_seq in Hi. apply in_seq. lia.
  - apply in_or_app; right. destruct C as [|c C'].
    + apply in_map_iff in Hx. destruct Hx as [i [<- Hi]]. apply in_map_iff. exists i.
      split; [reflexivity|]. apply in_seq in Hi. apply in_seq. lia.
    + apply in_map_iff in Hx. destruct Hx as [i [<- Hi]]. apply in_map_iff. exists i.
      split; [reflexivity|]. apply in_seq in Hi. apply in_seq. lia.
Qed.

Lemma cmp_const : forall C X c, In c C -> cmp C X c = c.
Proof.
  intros C X c Hc. unfold cmp. rewrite (lo_const C c Hc). unfold cnt.
  rewrite filter_nil; [simpl; lia|]. intros x _. apply andb_false_iff.
  destruct (Z.ltb_spec c x); [right; apply Z.leb_gt; lia | left; reflexivity].
Qed.

Lemma notC_of_none : forall C x, lo C x = None -> ~ In x C.
Proof. intros C x H Hx. pose proof (lo_none C x H x Hx). lia. Qed.

Lemma cmp_strict : forall C X x y, In x (X ++ C) -> In y (X ++ C) -> (x < y)%Z ->
  (cmp C X x < cmp C X y)%Z.
Proof.
  intros C X x y Hx Hy Hxy. unfold cmp.
  destruct (lo C x) as [a|] eqn:Ha; destruct (lo C y) as [b|] eqn:Hb.
  - destruct (lo_some C x a Ha) as [HaC [Hax Ham]]. destruct (lo_some C y b Hb) as [HbC [Hby Hbm]].
    assert (Hab : (a <= b)%Z) by (apply Hbm; [exact HaC | lia]).
    destruct (Z.eq_dec a b) as [<- | Hne].
    + assert (HyX : In y X).
      { apply in_app_or in Hy. destruct Hy as [Hy | Hy]; [exact Hy|].
        exfalso. pose proof (lo_const C y Hy) as E. rewrite Hb in E. injection E as E. lia. }
      assert (Hlt : (cnt (fun z => Z.ltb a z && Z.leb z x) X < cnt (fun z => Z.ltb a z && Z.leb z y) X)%nat).
      { apply (cnt_lt _ _ X y); [| exact HyX | |].
        - intros z _ Hz. apply andb_true_iff in Hz. destruct Hz as [H1 H2].
          apply Z.leb_le in H2. rewrite H1. simpl. apply Z.leb_le. lia.
        - apply andb_true_iff. split; [apply Z.ltb_lt | apply Z.leb_le]; lia.
        - apply andb_false_iff. right. apply Z.leb_gt. exact Hxy. }
      lia.
    + assert (Hxb : (x < b)%Z).
      { destruct (Z.ltb_spec x b) as [H | H]; [exact H|]. specialize (Ham b HbC H). lia. }
      pose proof (cnt_interval X a x Hax). lia.
  - exfalso. destruct (lo_some C x a Ha) as [HaC [Hax _]]. pose proof (lo_none C y Hb a HaC). lia.
  - destruct (lo_some C y b Hb) as [HbC [_ _]]. destruct C as [|c C']; [destruct HbC|].
    assert (HxX : In x X).
    { apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact Hx|].
      exfalso. exact (notC_of_none _ x Ha Hx). }
    destruct (mn_spec c C') as [HmC Hmm].
    assert (Hxm : (x < mn (c :: C'))%Z) by (exact (lo_none _ x Ha _ HmC)).
    assert (H1 : (1 <= cnt (fun z => Z.leb x z && Z.ltb z (mn (c :: C'))) X)%nat).
    { apply (cnt_pos _ X x); [assumption|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    specialize (Hmm b HbC). lia.
  - destruct C as [|c C'].
    + assert (HxX : In x X) by (rewrite app_nil_r in Hx; exact Hx).
      assert (Hlt : (cnt (fun z => Z.ltb z x) X < cnt (fun z => Z.ltb z y) X)%nat).
      { apply (cnt_lt _ _ X x); [| exact HxX | apply Z.ltb_lt; exact Hxy | apply Z.ltb_ge; lia].
        intros z _ Hz. apply Z.ltb_lt in Hz. apply Z.ltb_lt. lia. }
      lia.
    + assert (HxX : In x X).
      { apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact Hx|].
        exfalso. exact (notC_of_none _ x Ha Hx). }
      destruct (mn_spec c C') as [HmC _].
      assert (Hxm : (x < mn (c :: C'))%Z) by (exact (lo_none _ x Ha _ HmC)).
      assert (Hlt : (cnt (fun z => Z.leb y z && Z.ltb z (mn (c :: C'))) X <
                     cnt (fun z => Z.leb x z && Z.ltb z (mn (c :: C'))) X)%nat).
      { apply (cnt_lt _ _ X x); [| exact HxX | |].
        - intros z _ Hz. apply andb_true_iff in Hz. destruct Hz as [H1 H2].
          apply Z.leb_le in H1. rewrite H2, andb_true_r. apply Z.leb_le. lia.
        - apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
        - apply andb_false_iff. left. apply Z.leb_gt. exact Hxy. }
      lia.
Qed.

(* Compression: an order isomorphism on X and C fixing C, with values in reps (length X) C. *)
Theorem compress : forall C X,
  OIso C X (cmp C X) /\ forall x, In x X -> In (cmp C X x) (reps (length X) C).
Proof.
  intros C X. split; [split|].
  - intros x y Hx Hy. destruct (Z.compare_spec x y) as [-> | H | H].
    + apply Z.compare_refl.
    + apply Z.compare_lt_iff. apply cmp_strict; assumption.
    + apply Z.compare_gt_iff. apply cmp_strict; assumption.
  - intros c Hc. apply cmp_const. exact Hc.
  - intros x Hx. unfold cmp, reps. destruct (lo C x) as [a|] eqn:Ha.
    + destruct (lo_some C x a Ha) as [HaC _].
      pose proof (cnt_len (fun z => Z.ltb a z && Z.leb z x) X) as Hle.
      destruct (cnt (fun z => Z.ltb a z && Z.leb z x) X) as [|i] eqn:Hc.
      * apply in_or_app. left. rewrite Z.add_0_r. exact HaC.
      * apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists a.
        split; [exact HaC|]. apply in_map_iff. exists (S i). split; [reflexivity|].
        apply in_seq. lia.
    + destruct C as [|c C'].
      * apply in_or_app. right. apply in_or_app. right. apply in_map_iff.
        exists (cnt (fun z => Z.ltb z x) X). split; [reflexivity|]. apply in_seq. split; [lia|].
        pose proof (cnt_len_lt (fun z => Z.ltb z x) X x Hx (Z.ltb_irrefl x)). lia.
      * apply in_or_app. right. apply in_or_app. right. apply in_map_iff.
        exists (cnt (fun z => Z.leb x z && Z.ltb z (mn (c :: C'))) X). split; [reflexivity|].
        destruct (mn_spec c C') as [HmC _].
        assert (Hxm : (x < mn (c :: C'))%Z) by (exact (lo_none _ x Ha _ HmC)).
        assert (H1 : (1 <= cnt (fun z => Z.leb x z && Z.ltb z (mn (c :: C'))) X)%nat).
        { apply (cnt_pos _ X x); [assumption|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        pose proof (cnt_len (fun z => Z.leb x z && Z.ltb z (mn (c :: C'))) X). apply in_seq. lia.
Qed.

(* ============================================================================================ *)
(* Tuples over a finite domain.                                                                 *)
(* ============================================================================================ *)

Fixpoint tup (D : list Z) (k : nat) : list (list Z) :=
  match k with
  | 0 => [[]]
  | S k' => flat_map (fun x => map (cons x) (tup D k')) D
  end.

Lemma tup_spec : forall D k l, In l (tup D k) <-> length l = k /\ incl l D.
Proof.
  intros D k. induction k as [|k IH]; intros l; simpl.
  - split.
    + intros [<- | []]. split; [reflexivity | intros x []].
    + intros [H _]. destruct l; [left; reflexivity | discriminate].
  - rewrite in_flat_map. split.
    + intros [x [Hx Hl]]. apply in_map_iff in Hl. destruct Hl as [t [<- Ht]].
      apply IH in Ht. destruct Ht as [Ht1 Ht2]. split; [simpl; rewrite Ht1; reflexivity|].
      intros y [<- | Hy]; [exact Hx | exact (Ht2 y Hy)].
    + intros [Hl Hi]. destruct l as [|x t]; [discriminate|]. exists x.
      split; [apply Hi; left; reflexivity|]. apply in_map_iff. exists t. split; [reflexivity|].
      apply IH. split; [simpl in Hl; lia|]. intros y Hy. apply Hi. right. exact Hy.
Qed.

Lemma tup_map : forall D k (f : Z -> Z) s, length s = k -> (forall x, In x s -> In (f x) D) ->
  In (map f s) (tup D k).
Proof.
  intros D k f s Hl Hi. apply tup_spec. split; [rewrite lenM; exact Hl|].
  intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- Hx]]. apply Hi. exact Hx.
Qed.

Definition evdec (x y : nat * list Z) : {x = y} + {x <> y}.
Proof. decide equality; [apply (list_eq_dec Z.eq_dec) | apply Nat.eq_dec]. Defined.

Definition leq (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.

Lemma leq_spec : forall l1 l2, leq l1 l2 = true <-> l1 = l2.
Proof. intros l1 l2. unfold leq. destruct (list_eq_dec Z.eq_dec l1 l2); split; congruence. Qed.

(* Repair terminates from every state of a finite list: a uniform bound exists. *)
Lemma term_bound : forall (rp : list Z -> list Z) (vd : list Z -> bool) (L : list (list Z)),
  (forall s, vd s = true -> rp s = s) ->
  (forall s, In s L -> exists j, vd (itr j rp s) = true) ->
  exists K, forall s, In s L -> vd (itr K rp s) = true.
Proof.
  intros rp vd L Hfix. induction L as [|s0 L IH]; intros H; [exists 0%nat; intros s []|].
  destruct (H s0 (or_introl eq_refl)) as [j0 Hj0].
  destruct IH as [K0 HK0]; [intros s Hs; apply H; right; exact Hs|].
  exists (j0 + K0)%nat. intros s [<- | Hs].
  - rewrite itr_add, itr_fix by (apply Hfix; exact Hj0). exact Hj0.
  - replace (j0 + K0)%nat with (K0 + j0)%nat by lia.
    rewrite itr_add, itr_fix by (apply Hfix; apply HK0; exact Hs). apply HK0. exact Hs.
Qed.

(* ============================================================================================ *)
(* The order-invariant fragment: cutoffs over the representatives.                              *)
(* ============================================================================================ *)

Section OrderInvariant.
  Variable C : list Z.                          (* declared constants *)
  Variable n m nk : nat.                        (* variables, event parameters, event kinds *)
  Variable ap : nat * list Z -> list Z -> list Z.
  Variable rp : list Z -> list Z.
  Variable vd : list Z -> bool.

  (* Shape: events outside the declared signature do nothing, states keep n variables, repair
     leaves valid states alone. *)
  Record Shaped : Prop := {
    sh_noop : forall k p s, ~ (k < nk /\ length p = m)%nat -> ap (k, p) s = s;
    sh_len_ap : forall e s, length s = n -> length (ap e s) = n;
    sh_len_rp : forall s, vd s = false -> length (rp s) = n;
    sh_rp_fix : forall s, vd s = true -> rp s = s }.

  (* Order invariance: apply, repair and the invariant commute with every order isomorphism of
     the values involved that fixes the declared constants. *)
  Record OrdInv : Prop := {
    oi_ap : forall f k p s, length s = n -> OIso C (s ++ p) f ->
      ap (k, map f p) (map f s) = map f (ap (k, p) s);
    oi_rp : forall f s, length s = n -> OIso C s f -> rp (map f s) = map f (rp s);
    oi_vd : forall f s, length s = n -> OIso C s f -> vd (map f s) = vd s }.

  Local Notation G K := (govK ap rp K).

  (* ---- Order invariance forces closure: no fresh values. ---- *)

  Definition bump (Y : list Z) (z : Z) : Z := if in_dec Z.eq_dec z Y then z else (z + 1)%Z.

  Lemma bump_oiso : forall X, OIso C X (bump (X ++ C)).
  Proof.
    intros X. split.
    - intros x y Hx Hy. unfold bump.
      destruct (in_dec Z.eq_dec x (X ++ C)); [|contradiction].
      destruct (in_dec Z.eq_dec y (X ++ C)); [reflexivity | contradiction].
    - intros c Hc. unfold bump. destruct (in_dec Z.eq_dec c (X ++ C)) as [_ | N]; [reflexivity|].
      exfalso. apply N. apply in_or_app. right. exact Hc.
  Qed.

  Lemma bump_fix : forall Y l, incl l Y -> map (bump Y) l = l.
  Proof.
    intros Y l H. apply map_fix_in. intros x Hx. unfold bump.
    destruct (in_dec Z.eq_dec x Y) as [_ | N]; [reflexivity|]. exfalso. exact (N (H x Hx)).
  Qed.

  Lemma bump_out : forall Y v, ~ In v Y -> bump Y v <> v.
  Proof. intros Y v H. unfold bump. destruct (in_dec Z.eq_dec v Y); [contradiction | lia]. Qed.

  Theorem closure_ap : OrdInv -> forall k p s v, length s = n -> In v (ap (k, p) s) ->
    In v (s ++ p ++ C).
  Proof.
    intros H k p s v Hs Hv. rewrite app_assoc.
    destruct (in_dec Z.eq_dec v ((s ++ p) ++ C)) as [Hi | Hn]; [exact Hi|]. exfalso.
    pose proof (oi_ap H (bump ((s ++ p) ++ C)) k p s Hs (bump_oiso (s ++ p))) as E.
    rewrite (bump_fix _ p), (bump_fix _ s) in E
      by (intros x Hx; rewrite !in_app_iff; tauto).
    symmetry in E. exact (bump_out _ v Hn (map_fix_pt _ _ v E Hv)).
  Qed.

  Theorem closure_rp : OrdInv -> forall s v, length s = n -> In v (rp s) -> In v (s ++ C).
  Proof.
    intros H s v Hs Hv.
    destruct (in_dec Z.eq_dec v (s ++ C)) as [Hi | Hn]; [exact Hi|]. exfalso.
    pose proof (oi_rp H (bump (s ++ C)) s Hs (bump_oiso s)) as E.
    rewrite (bump_fix _ s) in E by (intros x Hx; rewrite !in_app_iff; tauto).
    symmetry in E. exact (bump_out _ v Hn (map_fix_pt _ _ v E Hv)).
  Qed.

  (* ---- Event normalization. ---- *)

  Definition nev (e : nat * list Z) : nat * list Z :=
    if Nat.ltb (fst e) nk && Nat.eqb (length (snd e)) m then e else (nk, []).

  Lemma nev_shape : forall e,
    ((fst (nev e) < nk)%nat /\ length (snd (nev e)) = m) \/ nev e = (nk, []).
  Proof.
    intros [k p]. unfold nev; simpl. destruct (Nat.ltb_spec k nk); destruct (Nat.eqb_spec (length p) m);
      simpl; auto.
  Qed.

  Section Inv.
    Hypothesis HS : Shaped.
    Hypothesis HO : OrdInv.

    Lemma ap_nev : forall e s, ap (nev e) s = ap e s.
    Proof.
      intros [k p] s. unfold nev; simpl.
      destruct (Nat.ltb_spec k nk); destruct (Nat.eqb_spec (length p) m); simpl; try reflexivity;
        rewrite (sh_noop HS nk [] s) by (simpl; lia); symmetry; apply (sh_noop HS); lia.
    Qed.

    Lemma gov_nev : forall K e s, G K (nev e) s = G K e s.
    Proof. intros K e s. unfold govK. rewrite ap_nev. reflexivity. Qed.

    Lemma rp_len_n : forall s, length s = n -> length (rp s) = n.
    Proof. exact (rp_len rp vd n (sh_len_rp HS) (sh_rp_fix HS)). Qed.

    Lemma G_len : forall K e s, length s = n -> length (G K e s) = n.
    Proof. intros K. exact (govK_len ap rp vd n K (sh_len_ap HS) (sh_len_rp HS) (sh_rp_fix HS)). Qed.

    Lemma itr_closed : forall j t v, length t = n -> In v (itr j rp t) -> In v (t ++ C).
    Proof.
      induction j as [|j IH]; intros t v Ht Hv; simpl in Hv.
      - apply in_or_app. left. exact Hv.
      - pose proof (IH (rp t) v (rp_len_n t Ht) Hv) as H. apply in_app_or in H.
        destruct H as [H | H]; [exact (closure_rp HO t v Ht H) | apply in_or_app; right; exact H].
    Qed.

    Theorem gov_closed : forall K k p s v, length s = n -> In v (G K (k, p) s) -> In v (s ++ p ++ C).
    Proof.
      intros K k p s v Hs Hv. unfold govK in Hv.
      pose proof (itr_closed K _ v (sh_len_ap HS (k, p) s Hs) Hv) as H.
      apply in_app_or in H. destruct H as [H | H]; [exact (closure_ap HO k p s v Hs H)|].
      rewrite !in_app_iff. tauto.
    Qed.

    Lemma itr_map_f : forall j f Y t, length t = n -> incl t (Y ++ C) -> OIso C Y f ->
      itr j rp (map f t) = map f (itr j rp t).
    Proof.
      induction j as [|j IH]; intros f Y t Ht Hi Hf; simpl; [reflexivity|].
      rewrite (oi_rp HO f t Ht (oiso_sub C Y t f Hi Hf)).
      apply (IH f Y); [exact (rp_len_n t Ht) | | exact Hf].
      intros v Hv. pose proof (closure_rp HO t v Ht Hv) as H. apply in_app_or in H.
      destruct H as [H | H]; [exact (Hi v H) | apply in_or_app; right; exact H].
    Qed.

    Theorem gov_map : forall K f Y k p s, length s = n -> incl (s ++ p) (Y ++ C) -> OIso C Y f ->
      G K (k, map f p) (map f s) = map f (G K (k, p) s).
    Proof.
      intros K f Y k p s Hs Hi Hf. unfold govK.
      rewrite (oi_ap HO f k p s Hs (oiso_sub C Y _ f Hi Hf)).
      apply (itr_map_f K f Y); [exact (sh_len_ap HS (k, p) s Hs) | | exact Hf].
      intros v Hv. pose proof (closure_ap HO k p s v Hs Hv) as H.
      rewrite app_assoc in H. apply in_app_or in H.
      destruct H as [H | H]; [exact (Hi v H) | apply in_or_app; right; exact H].
    Qed.

    (* ---- One check per order type. ---- *)

    Theorem cc1_order_type : forall K f s k1 p1 k2 p2, length s = n -> OIso C (s ++ p1 ++ p2) f ->
      (G K (k2, p2) (G K (k1, p1) s) = G K (k1, p1) (G K (k2, p2) s) <->
       G K (k2, map f p2) (G K (k1, map f p1) (map f s)) =
       G K (k1, map f p1) (G K (k2, map f p2) (map f s))).
    Proof.
      intros K f s k1 p1 k2 p2 Hs Hf. set (X := s ++ p1 ++ p2).
      assert (T1 : forall p, incl p X -> incl (s ++ p) (X ++ C)).
      { intros p Hp v Hv. apply in_app_or in Hv. apply in_or_app. left.
        destruct Hv as [Hv | Hv]; [unfold X; rewrite !in_app_iff; tauto | exact (Hp v Hv)]. }
      assert (Hp1 : incl p1 X) by (intros v Hv; unfold X; rewrite !in_app_iff; tauto).
      assert (Hp2 : incl p2 X) by (intros v Hv; unfold X; rewrite !in_app_iff; tauto).
      assert (T2 : forall k p p', incl p X -> incl p' X ->
                     incl (G K (k, p) s ++ p') (X ++ C)).
      { intros k p p' Hp Hp' v Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv].
        - pose proof (gov_closed K k p s v Hs Hv) as H. rewrite !in_app_iff in H.
          destruct H as [H | [H | H]]; [apply (T1 p Hp); apply in_or_app; left; exact H
                                        | apply (T1 p Hp); apply in_or_app; right; exact H
                                        | apply in_or_app; right; exact H].
        - apply in_or_app. left. exact (Hp' v Hv). }
      assert (Cl : forall k p k' p', incl p X -> incl p' X ->
                     incl (G K (k', p') (G K (k, p) s)) (X ++ C)).
      { intros k p k' p' Hp Hp' v Hv.
        pose proof (gov_closed K k' p' _ v (G_len K (k, p) s Hs) Hv) as H.
        rewrite app_assoc in H. apply in_app_or in H. destruct H as [H | H].
        - exact (T2 k p p' Hp Hp' v H).
        - apply in_or_app. right. exact H. }
      rewrite (gov_map K f X k1 p1 s Hs (T1 p1 Hp1) Hf), (gov_map K f X k2 p2 s Hs (T1 p2 Hp2) Hf).
      rewrite (gov_map K f X k2 p2 _ (G_len K _ s Hs)
                 (T2 k1 p1 p2 Hp1 Hp2) Hf).
      rewrite (gov_map K f X k1 p1 _ (G_len K _ s Hs)
                 (T2 k2 p2 p1 Hp2 Hp1) Hf).
      split; [intros E; rewrite E; reflexivity|].
      intros E. exact (oiso_inj C X f _ _ Hf (Cl k1 p1 k2 p2 Hp1 Hp2) (Cl k2 p2 k1 p1 Hp2 Hp1) E).
    Qed.

    Theorem cc2_order_type : forall K f s k p, length s = n -> OIso C (s ++ p) f ->
      (vd s = false -> G K (k, p) s = G K (k, p) (rp s)) <->
      (vd (map f s) = false -> G K (k, map f p) (map f s) = G K (k, map f p) (rp (map f s))).
    Proof.
      intros K f s k p Hs Hf. set (X := s ++ p).
      assert (Hsx : incl s (X ++ C)) by (intros v Hv; unfold X; rewrite !in_app_iff; tauto).
      assert (T1 : incl (s ++ p) (X ++ C)) by (intros v Hv; apply in_or_app; left; exact Hv).
      assert (Hrs : incl (rp s) (X ++ C)).
      { intros v Hv. pose proof (closure_rp HO s v Hs Hv) as H. apply in_app_or in H.
        destruct H as [H | H]; [exact (Hsx v H) | apply in_or_app; right; exact H]. }
      assert (T2 : incl (rp s ++ p) (X ++ C)).
      { intros v Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv]; [exact (Hrs v Hv)|].
        apply in_or_app; left; unfold X; rewrite in_app_iff; tauto. }
      assert (Cl : forall t, length t = n -> incl (t ++ p) (X ++ C) -> incl (G K (k, p) t) (X ++ C)).
      { intros t Ht Hi v Hv. pose proof (gov_closed K k p t v Ht Hv) as H. rewrite app_assoc in H.
        apply in_app_or in H. destruct H as [H | H]; [exact (Hi v H) | apply in_or_app; right; exact H]. }
      rewrite (oi_vd HO f s Hs (oiso_sub C X s f Hsx Hf)).
      rewrite (oi_rp HO f s Hs (oiso_sub C X s f Hsx Hf)).
      rewrite (gov_map K f X k p s Hs T1 Hf), (gov_map K f X k p (rp s) (rp_len_n s Hs) T2 Hf).
      split; intros H Hv; specialize (H Hv); [rewrite H; reflexivity|].
      exact (oiso_inj C X f _ _ Hf (Cl s Hs T1) (Cl (rp s) (rp_len_n s Hs) T2) H).
    Qed.
  End Inv.

  (* ---- The representative domain and the conditions over it. ---- *)

  Definition evD (N : nat) : list (nat * list Z) :=
    flat_map (fun k => map (pair k) (tup (reps N C) m)) (seq 0 nk) ++ [(nk, [])].

  Definition TermD (K N : nat) : Prop :=
    forall s, In s (tup (reps N C) n) -> vd (itr K rp s) = true.
  Definition CC1D (K N : nat) : Prop :=
    forall s e1 e2, In s (tup (reps N C) n) -> In e1 (evD N) -> In e2 (evD N) ->
      G K e2 (G K e1 s) = G K e1 (G K e2 s).
  Definition CC2D (K N : nat) : Prop :=
    forall s e, In s (tup (reps N C) n) -> In e (evD N) -> vd s = false ->
      G K e s = G K e (rp s).

  (* The finite check gsm runs. *)
  Definition abs_check (K N : nat) : bool :=
    forallb (fun s => vd (itr K rp s) &&
      forallb (fun e1 => (vd s || leq (G K e1 s) (G K e1 (rp s))) &&
        forallb (fun e2 => leq (G K e2 (G K e1 s)) (G K e1 (G K e2 s))) (evD N)) (evD N))
      (tup (reps N C) n).

  Theorem abs_check_spec : forall K N, abs_check K N = true <-> TermD K N /\ CC1D K N /\ CC2D K N.
  Proof.
    intros K N. unfold abs_check, TermD, CC1D, CC2D. rewrite forallb_forall. split.
    - intros H. split; [|split].
      + intros s Hs. specialize (H s Hs). apply andb_true_iff in H. apply H.
      + intros s e1 e2 Hs H1 H2. specialize (H s Hs). apply andb_true_iff in H.
        destruct H as [_ H]. rewrite forallb_forall in H. specialize (H e1 H1).
        apply andb_true_iff in H. destruct H as [_ H]. rewrite forallb_forall in H.
        apply leq_spec. exact (H e2 H2).
      + intros s e Hs He Hv. specialize (H s Hs). apply andb_true_iff in H.
        destruct H as [_ H]. rewrite forallb_forall in H. specialize (H e He).
        apply andb_true_iff in H. destruct H as [H _]. rewrite Hv in H. apply leq_spec. exact H.
    - intros [H1 [H2 H3]] s Hs. apply andb_true_iff. split; [exact (H1 s Hs)|].
      apply forallb_forall. intros e1 He1. apply andb_true_iff. split.
      + destruct (vd s) eqn:Hv; [reflexivity|]. simpl. apply leq_spec. exact (H3 s e1 Hs He1 Hv).
      + apply forallb_forall. intros e2 He2. apply leq_spec. exact (H2 s e1 e2 Hs He1 He2).
  Qed.

  Section Cutoff.
    Hypothesis HS : Shaped.
    Hypothesis HO : OrdInv.

    Lemma cmp_in_reps : forall X N x, (length X <= N)%nat -> In x X -> In (cmp C X x) (reps N C).
    Proof.
      intros X N x HN Hx. apply (reps_mono (length X) N C HN). exact (proj2 (compress C X) x Hx).
    Qed.

    Lemma nev_in_evD : forall N f e, (forall x, In x (snd (nev e)) -> In (f x) (reps N C)) ->
      In (fst (nev e), map f (snd (nev e))) (evD N).
    Proof.
      intros N f e Hi. unfold evD. apply in_or_app. destruct (nev_shape e) as [[Hk Hl] | E].
      - left. apply in_flat_map. exists (fst (nev e)). split; [apply in_seq; lia|].
        apply in_map. apply tup_map; [exact Hl | exact Hi].
      - right. rewrite E. left. reflexivity.
    Qed.

    Lemma nev_len : forall e, (length (snd (nev e)) <= m)%nat.
    Proof. intros e. destruct (nev_shape e) as [[_ Hl] | E]; [lia | rewrite E; simpl; lia]. Qed.

    (* Repair within K steps: cutoff n. *)
    Theorem term_abs : forall K N, (n <= N)%nat -> (TermK rp vd n K <-> TermD K N).
    Proof.
      intros K N HN. split.
      - intros H s Hs. apply H. apply tup_spec in Hs. apply Hs.
      - intros H s Hs. set (f := cmp C s). destruct (compress C s) as [Hf Hr].
        assert (Hm : In (map f s) (tup (reps N C) n))
          by (apply tup_map; [exact Hs | intros x Hx; apply cmp_in_reps; [lia | exact Hx]]).
        specialize (H _ Hm).
        rewrite (itr_map_f HS HO K f s s Hs (fun v Hv => in_or_app _ _ _ (or_introl Hv)) Hf) in H.
        assert (Hi : incl (itr K rp s) (s ++ C)) by (intros v Hv; exact (itr_closed HS HO K s v Hs Hv)).
        rewrite (oi_vd HO f _ (itr_len rp vd n (sh_len_rp HS) (sh_rp_fix HS) K s Hs)
                   (oiso_sub C s _ f Hi Hf)) in H.
        exact H.
    Qed.

    (* WFC (a potential decreasing under repair): cutoff n. *)
    Theorem wfc_abs : forall N, (n <= N)%nat ->
      ((exists Phi : list Z -> nat, forall s, length s = n -> vd s = false -> Phi (rp s) < Phi s) <->
       (exists Phi : list Z -> nat, forall s, In s (tup (reps N C) n) -> vd s = false -> Phi (rp s) < Phi s)).
    Proof.
      intros N HN. split.
      - intros [Phi H]. exists Phi. intros s Hs. apply H. apply tup_spec in Hs. apply Hs.
      - intros [Phi H].
        assert (Hd : forall s, In s (tup (reps N C) n) -> exists j, vd (itr j rp s) = true).
        { intros s. remember (Phi s) as q eqn:Eq. revert s Eq.
          induction q as [q IH] using (well_founded_induction lt_wf). intros s Eq Hs.
          destruct (vd s) eqn:Hv; [exists 0%nat; exact Hv|].
          assert (Hrs : In (rp s) (tup (reps N C) n)).
          { apply tup_spec in Hs. destruct Hs as [Hl Hi]. apply tup_spec.
            split; [exact (sh_len_rp HS s Hv)|]. intros v Hv'.
            pose proof (closure_rp HO s v Hl Hv') as Hc. apply in_app_or in Hc.
            destruct Hc as [Hc | Hc]; [exact (Hi v Hc) | exact (reps_C N C v Hc)]. }
          destruct (IH (Phi (rp s)) ltac:(subst q; exact (H s Hs Hv)) (rp s) eq_refl Hrs) as [j Hj].
          exists (S j). exact Hj. }
        destruct (term_bound rp vd _ (sh_rp_fix HS) Hd) as [K HK].
        pose proof (proj2 (term_abs K N HN) HK) as HT.
        exists (PhiB rp vd K). intros s Hs Hv.
        apply (wfcB rp vd n K (sh_len_rp HS) HT). unfold valid1. congruence.
    Qed.

    (* CC1: cutoff n + 2m. *)
    Theorem cc1_abs : forall K N, (n + 2 * m <= N)%nat -> (CC1Z ap rp n K <-> CC1D K N).
    Proof.
      intros K N HN. split.
      - intros H s e1 e2 Hs _ _. apply H. apply tup_spec in Hs. apply Hs.
      - intros H s e1 e2 Hs.
        rewrite <- (gov_nev HS K e1 s), <- (gov_nev HS K e2 s).
        rewrite <- (gov_nev HS K e2 (G K (nev e1) s)), <- (gov_nev HS K e1 (G K (nev e2) s)).
        pose proof (nev_len e1) as L1. pose proof (nev_len e2) as L2.
        destruct (nev e1) as [k1 p1] eqn:E1. destruct (nev e2) as [k2 p2] eqn:E2. simpl in L1, L2.
        set (X := s ++ p1 ++ p2). set (f := cmp C X). destruct (compress C X) as [Hf _].
        assert (HX : (length X <= N)%nat) by (unfold X; rewrite !lenA; lia).
        assert (Hin : forall x, In x X -> In (f x) (reps N C)) by (intros x Hx; apply cmp_in_reps; assumption).
        apply (cc1_order_type HS HO K f s k1 p1 k2 p2 Hs Hf).
        apply H.
        + apply tup_map; [exact Hs|]. intros x Hx. apply Hin. unfold X. rewrite !in_app_iff. tauto.
        + pose proof (nev_in_evD N f e1) as G1. rewrite E1 in G1. apply G1. simpl.
          intros x Hx. apply Hin. unfold X. rewrite !in_app_iff. tauto.
        + pose proof (nev_in_evD N f e2) as G2. rewrite E2 in G2. apply G2. simpl.
          intros x Hx. apply Hin. unfold X. rewrite !in_app_iff. tauto.
    Qed.

    (* CC2: cutoff n + m. *)
    Theorem cc2_abs : forall K N, (n + m <= N)%nat -> (CC2Z ap rp vd n K <-> CC2D K N).
    Proof.
      intros K N HN. split.
      - intros H s e Hs _ Hv. apply H; [apply tup_spec in Hs; apply Hs | exact Hv].
      - intros H s e Hs.
        assert (R : forall t, G K e t = G K (nev e) t) by (intros t; symmetry; apply (gov_nev HS)).
        rewrite (R s), (R (rp s)).
        pose proof (nev_len e) as L. destruct (nev e) as [k p] eqn:E. simpl in L.
        set (X := s ++ p). set (f := cmp C X). destruct (compress C X) as [Hf _].
        assert (HX : (length X <= N)%nat) by (unfold X; rewrite !lenA; lia).
        assert (Hin : forall x, In x X -> In (f x) (reps N C)) by (intros x Hx; apply cmp_in_reps; assumption).
        apply (cc2_order_type HS HO K f s k p Hs Hf). intros Hv.
        apply H; [| | exact Hv].
        + apply tup_map; [exact Hs|]. intros x Hx. apply Hin. unfold X. rewrite !in_app_iff. tauto.
        + pose proof (nev_in_evD N f e) as G1. rewrite E in G1. apply G1. simpl.
          intros x Hx. apply Hin. unfold X. rewrite !in_app_iff. tauto.
    Qed.

    (* Unique normal forms over all of Z iff CC1 and CC2 over the representatives. *)
    Theorem un_abs : forall K N, (n + 2 * m <= N)%nat -> TermD K N ->
      (UNZ evdec ap rp vd n <-> CC1D K N /\ CC2D K N).
    Proof.
      intros K N HN HT. pose proof (proj2 (term_abs K N ltac:(lia)) HT) as HZ.
      rewrite (un_bounded evdec ap rp vd n K (sh_len_ap HS) (sh_len_rp HS) (sh_rp_fix HS) HZ).
      rewrite (cc1_abs K N HN), (cc2_abs K N ltac:(lia)). reflexivity.
    Qed.

    (* The finite check passes iff, over all of Z, repair reaches validity within K steps and every
       buffer from every state has a unique normal form. *)
    Theorem abs_check_exact : forall K N, (n + 2 * m <= N)%nat ->
      (abs_check K N = true <-> TermK rp vd n K /\ UNZ evdec ap rp vd n).
    Proof.
      intros K N HN. rewrite abs_check_spec. split.
      - intros [H1 [H2 H3]]. split; [exact (proj2 (term_abs K N ltac:(lia)) H1)|].
        apply (un_abs K N HN H1). split; assumption.
      - intros [HT HU]. pose proof (proj1 (term_abs K N ltac:(lia)) HT) as H1.
        split; [exact H1|]. apply (un_abs K N HN H1). exact HU.
    Qed.

    Corollary abs_check_sound : forall K N, (n + 2 * m <= N)%nat -> abs_check K N = true ->
      forall s, length s = n -> forall B, UN (step evdec ap rp (valid1 vd) free_enabled) (s, B).
    Proof. intros K N HN H. exact (proj2 (proj1 (abs_check_exact K N HN) H)). Qed.
  End Cutoff.
End OrderInvariant.

(* ============================================================================================ *)
(* A rule language, and the fragment checks.                                                    *)
(* ============================================================================================ *)

(* Expressions over an environment of integers (a state, followed by the event's parameters):
   variables, integer literals, +, -, *, if-then-else; formulas: comparisons and connectives. *)
Inductive expr : Type :=
| Vr (i : nat)
| Cst (z : Z)
| Pl (a b : expr)
| Mi (a b : expr)
| Ml (a b : expr)
| If (c : form) (a b : expr)
with form : Type :=
| FT
| FF
| FLt (a b : expr)
| FLe (a b : expr)
| FEq (a b : expr)
| FNot (c : form)
| FAnd (c d : form)
| FOr (c d : form).

Scheme expr_mut := Induction for expr Sort Prop
with form_mut := Induction for form Sort Prop.
Combined Scheme ef_mut from expr_mut, form_mut.

Fixpoint evalE (env : list Z) (e : expr) : Z :=
  match e with
  | Vr i => nth i env 0%Z
  | Cst z => z
  | Pl a b => (evalE env a + evalE env b)%Z
  | Mi a b => (evalE env a - evalE env b)%Z
  | Ml a b => (evalE env a * evalE env b)%Z
  | If c a b => if evalF env c then evalE env a else evalE env b
  end
with evalF (env : list Z) (c : form) : bool :=
  match c with
  | FT => true
  | FF => false
  | FLt a b => Z.ltb (evalE env a) (evalE env b)
  | FLe a b => Z.leb (evalE env a) (evalE env b)
  | FEq a b => Z.eqb (evalE env a) (evalE env b)
  | FNot c => negb (evalF env c)
  | FAnd c d => evalF env c && evalF env d
  | FOr c d => evalF env c || evalF env d
  end.

(* Variables in range. *)
Fixpoint bndE (N : nat) (e : expr) : bool :=
  match e with
  | Vr i => Nat.ltb i N
  | Cst _ => true
  | Pl a b | Mi a b | Ml a b => bndE N a && bndE N b
  | If c a b => bndF N c && bndE N a && bndE N b
  end
with bndF (N : nat) (c : form) : bool :=
  match c with
  | FT | FF => true
  | FLt a b | FLe a b | FEq a b => bndE N a && bndE N b
  | FNot c => bndF N c
  | FAnd c d | FOr c d => bndF N c && bndF N d
  end.

(* The order-invariant fragment: only variables and declared constants, compared and copied. *)
Fixpoint oE (C : list Z) (e : expr) : bool :=
  match e with
  | Vr _ => true
  | Cst z => existsb (Z.eqb z) C
  | If c a b => oF C c && oE C a && oE C b
  | _ => false
  end
with oF (C : list Z) (c : form) : bool :=
  match c with
  | FT | FF => true
  | FLt a b | FLe a b | FEq a b => oE C a && oE C b
  | FNot c => oF C c
  | FAnd c d | FOr c d => oF C c && oF C d
  end.

(* A program: per event kind, the new value of each variable over (state ++ parameters); the
   repair, the new value of each variable over the state; the invariant over the state. *)
Record prog : Type := mkProg { pk : list (list expr); pr : list expr; pinv : form }.

Definition sap (P : prog) (m : nat) (e : nat * list Z) (s : list Z) : list Z :=
  match nth_error (pk P) (fst e) with
  | Some c => if Nat.eqb (length (snd e)) m then map (evalE (s ++ snd e)) c else s
  | None => s
  end.
Definition svd (P : prog) (s : list Z) : bool := evalF s (pinv P).
Definition srp (P : prog) (s : list Z) : list Z := if svd P s then s else map (evalE s) (pr P).

Definition wf (P : prog) (n m : nat) : bool :=
  forallb (fun c => Nat.eqb (length c) n && forallb (bndE (n + m)) c) (pk P) &&
  Nat.eqb (length (pr P)) n && forallb (bndE n) (pr P) && bndF n (pinv P).

Definition ord_frag (C : list Z) (P : prog) : bool :=
  forallb (forallb (oE C)) (pk P) && forallb (oE C) (pr P) && oF C (pinv P).

Ltac bsplit := repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
  end.

Lemma ord_eval : forall C env f, OIso C env f ->
  (forall e, oE C e = true -> bndE (length env) e = true ->
     In (evalE env e) (env ++ C) /\ evalE (map f env) e = f (evalE env e)) /\
  (forall c, oF C c = true -> bndF (length env) c = true -> evalF (map f env) c = evalF env c).
Proof.
  intros C env f Hf.
  apply (ef_mut (fun e => oE C e = true -> bndE (length env) e = true ->
                   In (evalE env e) (env ++ C) /\ evalE (map f env) e = f (evalE env e))
                (fun c => oF C c = true -> bndF (length env) c = true ->
                   evalF (map f env) c = evalF env c)).
  - intros i _ Hb. simpl in *. apply Nat.ltb_lt in Hb.
    split; [apply in_or_app; left; apply nth_In; exact Hb|].
    rewrite (nth_indep (map f env) 0%Z (f 0%Z)) by (rewrite lenM; exact Hb). apply map_nth.
  - intros z Ho _. simpl in *. apply existsb_exists in Ho. destruct Ho as [c [Hc Hz]].
    apply Z.eqb_eq in Hz. subst z.
    split; [apply in_or_app; right; exact Hc | symmetry; apply (proj2 Hf); exact Hc].
  - intros a _ b _ Ho _. discriminate.
  - intros a _ b _ Ho _. discriminate.
  - intros a _ b _ Ho _. discriminate.
  - intros c IHc a IHa b IHb Ho Hb. simpl in *. bsplit.
    rewrite IHc by assumption. destruct (evalF env c); [apply IHa | apply IHb]; assumption.
  - reflexivity.
  - reflexivity.
  - intros a IHa b IHb Ho Hb. simpl in *. bsplit.
    destruct (IHa ltac:(assumption) ltac:(assumption)) as [Ia Ea]. destruct (IHb ltac:(assumption) ltac:(assumption)) as [Ib Eb]. rewrite Ea, Eb.
    pose proof (oiso_lt C env f _ _ Hf Ia Ib) as L.
    apply eq_iff_eq_true. rewrite !Z.ltb_lt. symmetry. exact L.
  - intros a IHa b IHb Ho Hb. simpl in *. bsplit.
    destruct (IHa ltac:(assumption) ltac:(assumption)) as [Ia Ea]. destruct (IHb ltac:(assumption) ltac:(assumption)) as [Ib Eb]. rewrite Ea, Eb.
    pose proof (oiso_le C env f _ _ Hf Ia Ib) as L.
    apply eq_iff_eq_true. rewrite !Z.leb_le. symmetry. exact L.
  - intros a IHa b IHb Ho Hb. simpl in *. bsplit.
    destruct (IHa ltac:(assumption) ltac:(assumption)) as [Ia Ea]. destruct (IHb ltac:(assumption) ltac:(assumption)) as [Ib Eb]. rewrite Ea, Eb.
    pose proof (oiso_eq C env f _ _ Hf Ia Ib) as L.
    apply eq_iff_eq_true. rewrite !Z.eqb_eq. symmetry. exact L.
  - intros c IHc Ho Hb. simpl in *. rewrite (IHc Ho Hb). reflexivity.
  - intros c IHc d IHd Ho Hb. simpl in *. bsplit. rewrite (IHc ltac:(assumption) ltac:(assumption)), (IHd ltac:(assumption) ltac:(assumption)). reflexivity.
  - intros c IHc d IHd Ho Hb. simpl in *. bsplit. rewrite (IHc ltac:(assumption) ltac:(assumption)), (IHd ltac:(assumption) ltac:(assumption)). reflexivity.
Qed.

Lemma wf_parts : forall P n m, wf P n m = true ->
  (forall c, In c (pk P) -> length c = n /\ forall e, In e c -> bndE (n + m) e = true) /\
  length (pr P) = n /\ (forall e, In e (pr P) -> bndE n e = true) /\ bndF n (pinv P) = true.
Proof.
  intros P n m H. unfold wf in H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2]. rewrite forallb_forall in H1, H3.
  split; [|split; [apply Nat.eqb_eq; exact H2 | split; [exact H3 | exact H4]]].
  intros c Hc. specialize (H1 c Hc). apply andb_true_iff in H1 as [Ha Hb].
  rewrite forallb_forall in Hb. split; [apply Nat.eqb_eq; exact Ha | exact Hb].
Qed.

Lemma ord_parts : forall C P, ord_frag C P = true ->
  (forall c e, In c (pk P) -> In e c -> oE C e = true) /\
  (forall e, In e (pr P) -> oE C e = true) /\ oF C (pinv P) = true.
Proof.
  intros C P H. unfold ord_frag in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  rewrite forallb_forall in H1, H2. split; [|split; [exact H2 | exact H3]].
  intros c e Hc He. specialize (H1 c Hc). rewrite forallb_forall in H1. exact (H1 e He).
Qed.

(* Every well-formed program has the shape the cutoff needs. *)
Theorem prog_shaped : forall P n m, wf P n m = true ->
  Shaped n m (length (pk P)) (sap P m) (srp P) (svd P).
Proof.
  intros P n m H. destruct (wf_parts P n m H) as [Hk [Hr [_ _]]]. constructor.
  - intros k p s Hn. unfold sap; simpl. destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|reflexivity].
    assert (Hlt : (k < length (pk P))%nat) by (apply nth_error_Some; congruence).
    destruct (Nat.eqb_spec (length p) m); [exfalso; apply Hn; split; assumption | reflexivity].
  - intros [k p] s Hs. unfold sap; simpl. destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|exact Hs].
    destruct (Nat.eqb (length p) m); [|exact Hs]. rewrite lenM. exact (proj1 (Hk c (nth_error_In _ _ Hc))).
  - intros s Hv. unfold srp. rewrite Hv. rewrite lenM. exact Hr.
  - intros s Hv. unfold srp. rewrite Hv. reflexivity.
Qed.

(* The fragment check is sound: a well-formed program in the fragment is order invariant. *)
Theorem ord_frag_sound : forall C P n m, wf P n m = true -> ord_frag C P = true ->
  OrdInv C n (sap P m) (srp P) (svd P).
Proof.
  intros C P n m Hw Ho. destruct (wf_parts P n m Hw) as [Hk [_ [Hrb Hib]]].
  destruct (ord_parts C P Ho) as [Ok [Or Oi]].
  assert (Vd : forall f s, length s = n -> OIso C s f -> svd P (map f s) = svd P s).
  { intros f s Hs Hf. unfold svd. apply (proj2 (ord_eval C s f Hf)); [exact Oi | rewrite Hs; exact Hib]. }
  constructor.
  - intros f k p s Hs Hf. unfold sap; simpl. destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|reflexivity].
    rewrite lenM. destruct (Nat.eqb_spec (length p) m) as [Hl | Hl]; [|reflexivity].
    destruct (Hk c (nth_error_In _ _ Hc)) as [_ Hb].
    rewrite <- map_app, map_map. apply map_ext_in. intros e He.
    apply (proj1 (ord_eval C (s ++ p) f Hf));
      [exact (Ok c e (nth_error_In _ _ Hc) He) | rewrite lenA, Hs, Hl; exact (Hb e He)].
  - intros f s Hs Hf. unfold srp. rewrite (Vd f s Hs Hf). destruct (svd P s); [reflexivity|].
    rewrite map_map. apply map_ext_in. intros e He.
    apply (proj1 (ord_eval C s f Hf)); [exact (Or e He) | rewrite Hs; exact (Hrb e He)].
  - exact Vd.
Qed.

(* Build for a rule description: well-formed, in the fragment, and the finite check passes. *)
Theorem build_sound : forall C P n m K N, wf P n m = true -> ord_frag C P = true ->
  (n + 2 * m <= N)%nat ->
  abs_check C n m (length (pk P)) (sap P m) (srp P) (svd P) K N = true ->
  forall s, length s = n -> forall B,
    UN (step evdec (sap P m) (srp P) (valid1 (svd P)) free_enabled) (s, B).
Proof.
  intros C P n m K N Hw Ho HN Hc.
  exact (abs_check_sound C n m _ _ _ _ (prog_shaped P n m Hw) (ord_frag_sound C P n m Hw Ho) K N HN Hc).
Qed.

(* ============================================================================================ *)
(* The linear fragment: the conditions as formulas, exact.                                      *)
(* ============================================================================================ *)

Fixpoint substE (sg : list expr) (e : expr) : expr :=
  match e with
  | Vr i => nth i sg (Cst 0%Z)
  | Cst z => Cst z
  | Pl a b => Pl (substE sg a) (substE sg b)
  | Mi a b => Mi (substE sg a) (substE sg b)
  | Ml a b => Ml (substE sg a) (substE sg b)
  | If c a b => If (substF sg c) (substE sg a) (substE sg b)
  end
with substF (sg : list expr) (c : form) : form :=
  match c with
  | FT => FT
  | FF => FF
  | FLt a b => FLt (substE sg a) (substE sg b)
  | FLe a b => FLe (substE sg a) (substE sg b)
  | FEq a b => FEq (substE sg a) (substE sg b)
  | FNot c => FNot (substF sg c)
  | FAnd c d => FAnd (substF sg c) (substF sg d)
  | FOr c d => FOr (substF sg c) (substF sg d)
  end.

Lemma subst_eval : forall env sg,
  (forall e, evalE env (substE sg e) = evalE (map (evalE env) sg) e) /\
  (forall c, evalF env (substF sg c) = evalF (map (evalE env) sg) c).
Proof.
  intros env sg.
  apply (ef_mut (fun e => evalE env (substE sg e) = evalE (map (evalE env) sg) e)
                (fun c => evalF env (substF sg c) = evalF (map (evalE env) sg) c)).
  - intros i. simpl. exact (eq_sym (map_nth (evalE env) sg (Cst 0%Z) i)).
  - intros z. reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros c IHc a IHa b IHb. simpl. rewrite IHc, IHa, IHb. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros a IHa b IHb. simpl. rewrite IHa, IHb. reflexivity.
  - intros c IHc. simpl. rewrite IHc. reflexivity.
  - intros c IHc d IHd. simpl. rewrite IHc, IHd. reflexivity.
  - intros c IHc d IHd. simpl. rewrite IHc, IHd. reflexivity.
Qed.

Lemma evE_subst : forall env sg e, evalE env (substE sg e) = evalE (map (evalE env) sg) e.
Proof. intros env sg. exact (proj1 (subst_eval env sg)). Qed.

Lemma evF_subst : forall env sg c, evalF env (substF sg c) = evalF (map (evalE env) sg) c.
Proof. intros env sg. exact (proj2 (subst_eval env sg)). Qed.

(* Linear: multiplication only by a literal. *)
Definition isCst (e : expr) : bool := match e with Cst _ => true | _ => false end.

Fixpoint linE (e : expr) : bool :=
  match e with
  | Vr _ | Cst _ => true
  | Pl a b | Mi a b => linE a && linE b
  | Ml a b => (isCst a || isCst b) && linE a && linE b
  | If c a b => linF c && linE a && linE b
  end
with linF (c : form) : bool :=
  match c with
  | FT | FF => true
  | FLt a b | FLe a b | FEq a b => linE a && linE b
  | FNot c => linF c
  | FAnd c d | FOr c d => linF c && linF d
  end.

Definition lin_frag (P : prog) : bool :=
  forallb (forallb linE) (pk P) && forallb linE (pr P) && linF (pinv P).

Lemma isCst_subst : forall sg a, isCst a = true -> isCst (substE sg a) = true.
Proof. intros sg a H. destruct a; try discriminate. reflexivity. Qed.

Lemma subst_lin : forall sg, forallb linE sg = true ->
  (forall e, linE e = true -> linE (substE sg e) = true) /\
  (forall c, linF c = true -> linF (substF sg c) = true).
Proof.
  intros sg Hs. rewrite forallb_forall in Hs.
  apply (ef_mut (fun e => linE e = true -> linE (substE sg e) = true)
                (fun c => linF c = true -> linF (substF sg c) = true)).
  - intros i _. simpl. destruct (nth_in_or_default i sg (Cst 0%Z)) as [H | ->]; [exact (Hs _ H) | reflexivity].
  - intros z _. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption.
    apply orb_true_iff in H. destruct H as [H | H]; rewrite (isCst_subst sg _ H); simpl;
      [reflexivity | rewrite orb_true_r; reflexivity].
  - intros c IHc a IHa b IHb H. simpl in *. bsplit. rewrite IHc, IHa, IHb by assumption. reflexivity.
  - intros _. reflexivity.
  - intros _. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption. reflexivity.
  - intros a IHa b IHb H. simpl in *. bsplit. rewrite IHa, IHb by assumption. reflexivity.
  - intros c IHc H. simpl in *. apply IHc. exact H.
  - intros c IHc d IHd H. simpl in *. bsplit. rewrite IHc, IHd by assumption. reflexivity.
  - intros c IHc d IHd H. simpl in *. bsplit. rewrite IHc, IHd by assumption. reflexivity.
Qed.

Lemma ev_seq : forall (pre l post : list Z),
  map (fun i => nth i (pre ++ l ++ post) 0%Z) (seq (length pre) (length l)) = l.
Proof.
  intros pre l. revert pre. induction l as [|x l IH]; intros pre post; [reflexivity|].
  simpl. rewrite nth_middle. f_equal.
  specialize (IH (pre ++ [x]) post). rewrite lenA in IH. simpl in IH.
  replace (length pre + 1)%nat with (S (length pre)) in IH by lia.
  rewrite <- app_assoc in IH. exact IH.
Qed.

Section Linear.
  Variable P : prog.
  Variable n m K : nat.

  Definition nkP : nat := length (pk P).
  Definition slot (o : nat) : list expr := map Vr (seq o m).
  Definition S0 : list expr := map Vr (seq 0 n).

  (* Symbolic execution: the state after an event of kind k whose parameters are the variables
     o .. o + m - 1, the repair as an if-then-else, the governed step, list equality. *)
  Definition symA (k o : nat) (sg : list expr) : list expr :=
    match nth_error (pk P) k with Some c => map (substE (sg ++ slot o)) c | None => sg end.
  Definition iteL (c : form) (a b : list expr) : list expr :=
    map (fun ab => If c (fst ab) (snd ab)) (combine a b).
  Definition symR (sg : list expr) : list expr :=
    iteL (substF sg (pinv P)) sg (map (substE sg) (pr P)).
  Definition symG (k o : nat) (sg : list expr) : list expr := itr K symR (symA k o sg).
  Definition eqL (a b : list expr) : form :=
    fold_right (fun ab acc => FAnd (FEq (fst ab) (snd ab)) acc) FT (combine a b).

  (* The generated formulas, over the variables 0 .. n + 2m - 1: the state, then the parameters of
     the first event, then those of the second. Kind nkP stands for every event outside the
     declared kinds (it does nothing). *)
  Definition phi_term : form := substF (itr K symR S0) (pinv P).
  Definition phi_cc1 (k1 k2 : nat) : form :=
    eqL (symG k2 (n + m) (symG k1 n S0)) (symG k1 n (symG k2 (n + m) S0)).
  Definition phi_cc2 (k : nat) : form :=
    FOr (substF S0 (pinv P)) (eqL (symG k n S0) (symG k n (symR S0))).

  (* Validity: true under every assignment of integers to the variables. *)
  Definition FValid (phi : form) : Prop :=
    forall env, length env = (n + 2 * m)%nat -> evalF env phi = true.

  (* ---- Linearity of the generated formulas. ---- *)

  Lemma forallb_map_subst : forall sg l, forallb linE sg = true -> forallb linE l = true ->
    forallb linE (map (substE sg) l) = true.
  Proof.
    intros sg l Hs Hl. pose proof (proj1 (subst_lin sg Hs)) as G. rewrite forallb_forall in *.
    intros x Hx. apply in_map_iff in Hx. destruct Hx as [e [<- He]]. apply G. exact (Hl e He).
  Qed.

  Lemma lin_vars : forall o k, forallb linE (map Vr (seq o k)) = true.
  Proof.
    intros o k. apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- _]].
    reflexivity.
  Qed.

  Section Lin.
    Hypothesis HL : lin_frag P = true.

    Lemma lin_parts : (forall c, In c (pk P) -> forallb linE c = true) /\
      forallb linE (pr P) = true /\ linF (pinv P) = true.
    Proof.
      unfold lin_frag in HL. apply andb_true_iff in HL as [H H3]. apply andb_true_iff in H as [H1 H2].
      rewrite forallb_forall in H1. split; [exact H1 | split; [exact H2 | exact H3]].
    Qed.

    Lemma lin_symA : forall k o sg, forallb linE sg = true -> forallb linE (symA k o sg) = true.
    Proof.
      intros k o sg Hs. unfold symA. destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|exact Hs].
      apply forallb_map_subst; [|exact (proj1 lin_parts c (nth_error_In _ _ Hc))].
      rewrite forallb_app, Hs. apply lin_vars.
    Qed.

    Lemma lin_iteL : forall c a b, linF c = true -> forallb linE a = true -> forallb linE b = true ->
      forallb linE (iteL c a b) = true.
    Proof.
      intros c a. induction a as [|x a IH]; intros [|y b] Hc Ha Hb; try reflexivity.
      simpl in Ha, Hb. apply andb_true_iff in Ha as [Hx Ha]. apply andb_true_iff in Hb as [Hy Hb].
      unfold iteL; simpl. rewrite Hc, Hx, Hy. simpl. apply (IH b); assumption.
    Qed.

    Lemma lin_symR : forall sg, forallb linE sg = true -> forallb linE (symR sg) = true.
    Proof.
      intros sg Hs. unfold symR. apply lin_iteL; [| exact Hs | apply forallb_map_subst; [exact Hs | apply lin_parts]].
      apply (proj2 (subst_lin sg Hs)). apply lin_parts.
    Qed.

    Lemma lin_itr : forall j sg, forallb linE sg = true -> forallb linE (itr j symR sg) = true.
    Proof. induction j as [|j IH]; intros sg Hs; simpl; [exact Hs | apply IH, lin_symR, Hs]. Qed.

    Lemma lin_symG : forall k o sg, forallb linE sg = true -> forallb linE (symG k o sg) = true.
    Proof. intros k o sg Hs. unfold symG. apply lin_itr, lin_symA, Hs. Qed.

    Lemma lin_eqL : forall a b, forallb linE a = true -> forallb linE b = true -> linF (eqL a b) = true.
    Proof.
      intros a. induction a as [|x a IH]; intros [|y b] Ha Hb; try reflexivity.
      simpl in Ha, Hb. apply andb_true_iff in Ha as [Hx Ha]. apply andb_true_iff in Hb as [Hy Hb].
      unfold eqL; simpl. rewrite Hx, Hy. simpl. apply (IH b); assumption.
    Qed.

    (* With multiplication only by literals, every generated formula is linear integer arithmetic
       (with if-then-else), so the validity question is Presburger and decidable. *)
    Theorem lin_frag_linear : linF phi_term = true /\
      (forall k1 k2, linF (phi_cc1 k1 k2) = true) /\ (forall k, linF (phi_cc2 k) = true).
    Proof.
      split; [|split].
      - unfold phi_term. apply (proj2 (subst_lin _ (lin_itr K S0 (lin_vars 0 n)))). apply lin_parts.
      - intros k1 k2. unfold phi_cc1. apply lin_eqL; repeat apply lin_symG; apply lin_vars.
      - intros k. unfold phi_cc2. simpl. rewrite (proj2 (subst_lin _ (lin_vars 0 n))) by apply lin_parts.
        simpl. apply lin_eqL; apply lin_symG; [apply lin_vars | apply lin_symR, lin_vars].
    Qed.
  End Lin.

  (* ---- Exactness: each condition holds over Z iff its formula is valid. ---- *)

  Section Exact.
    Hypothesis Hw : wf P n m = true.

    Lemma ev_iteL : forall env c a b, length a = length b ->
      map (evalE env) (iteL c a b) = if evalF env c then map (evalE env) a else map (evalE env) b.
    Proof.
      intros env c a. induction a as [|x a IH]; intros [|y b] H; simpl in H; try discriminate.
      - unfold iteL. simpl. destruct (evalF env c); reflexivity.
      - specialize (IH b ltac:(lia)). unfold iteL in *. simpl. rewrite IH.
        destruct (evalF env c); reflexivity.
    Qed.

    Lemma len_iteL : forall c a b, length a = length b -> length (iteL c a b) = length a.
    Proof.
      intros c a. unfold iteL. induction a as [|x a IH]; intros [|y b] H; simpl in *; try discriminate; auto.
    Qed.

    Lemma len_pr : length (pr P) = n.
    Proof. exact (proj1 (proj2 (wf_parts P n m Hw))). Qed.

    Lemma len_symR : forall sg, length sg = n -> length (symR sg) = n.
    Proof. intros sg H. unfold symR. rewrite len_iteL; [exact H | rewrite lenM, len_pr; exact H]. Qed.

    Lemma len_itr : forall j sg, length sg = n -> length (itr j symR sg) = n.
    Proof. induction j as [|j IH]; intros sg H; simpl; [exact H | apply IH, len_symR, H]. Qed.

    Lemma len_symA : forall k o sg, length sg = n -> length (symA k o sg) = n.
    Proof.
      intros k o sg H. unfold symA. destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|exact H].
      rewrite lenM. exact (proj1 (proj1 (wf_parts P n m Hw) c (nth_error_In _ _ Hc))).
    Qed.

    Lemma len_symG : forall k o sg, length sg = n -> length (symG k o sg) = n.
    Proof. intros k o sg H. unfold symG. apply len_itr, len_symA, H. Qed.

    Lemma len_S0 : length S0 = n.
    Proof. unfold S0. rewrite lenM, lenS. reflexivity. Qed.

    Lemma ev_symR : forall env sg, length sg = n ->
      map (evalE env) (symR sg) = srp P (map (evalE env) sg).
    Proof.
      intros env sg H. unfold symR, srp, svd. rewrite ev_iteL by (rewrite lenM, len_pr; exact H).
      rewrite evF_subst. destruct (evalF (map (evalE env) sg) (pinv P)); [reflexivity|].
      rewrite map_map. apply map_ext. intros e. apply evE_subst.
    Qed.

    Lemma ev_itr : forall env j sg, length sg = n ->
      map (evalE env) (itr j symR sg) = itr j (srp P) (map (evalE env) sg).
    Proof.
      intros env j. induction j as [|j IH]; intros sg H; simpl; [reflexivity|].
      rewrite IH by (apply len_symR, H). rewrite ev_symR by exact H. reflexivity.
    Qed.

    Lemma len_ev_slot : forall env o, length (map (evalE env) (slot o)) = m.
    Proof. intros env o. unfold slot. rewrite !lenM, lenS. reflexivity. Qed.

    Lemma ev_symA : forall env k o sg, length sg = n ->
      map (evalE env) (symA k o sg) = sap P m (k, map (evalE env) (slot o)) (map (evalE env) sg).
    Proof.
      intros env k o sg H. unfold symA, sap; simpl. destruct (nth_error (pk P) k) as [c|]; [|reflexivity].
      rewrite len_ev_slot, Nat.eqb_refl, map_map. apply map_ext. intros e.
      rewrite evE_subst, map_app. reflexivity.
    Qed.

    Lemma ev_symG : forall env k o sg, length sg = n ->
      map (evalE env) (symG k o sg) =
      govK (sap P m) (srp P) K (k, map (evalE env) (slot o)) (map (evalE env) sg).
    Proof.
      intros env k o sg H. unfold symG, govK. rewrite ev_itr by (apply len_symA, H).
      rewrite ev_symA by exact H. reflexivity.
    Qed.

    Lemma ev_eqL : forall env a b, length a = length b ->
      (evalF env (eqL a b) = true <-> map (evalE env) a = map (evalE env) b).
    Proof.
      intros env a. induction a as [|x a IH]; intros [|y b] H; simpl in H; try discriminate.
      - split; reflexivity.
      - specialize (IH b ltac:(lia)). unfold eqL in *. simpl. rewrite andb_true_iff, Z.eqb_eq, IH. split.
        + intros [-> ->]. reflexivity.
        + intros E. injection E as E1 E2. split; assumption.
    Qed.

    Lemma env3 : forall s p1 p2, length s = n -> length p1 = m -> length p2 = m ->
      map (evalE (s ++ p1 ++ p2)) S0 = s /\ map (evalE (s ++ p1 ++ p2)) (slot n) = p1 /\
      map (evalE (s ++ p1 ++ p2)) (slot (n + m)) = p2.
    Proof.
      intros s p1 p2 Hs H1 H2. unfold S0, slot. rewrite !map_map. simpl. split; [|split].
      - pose proof (ev_seq [] s (p1 ++ p2)) as E. simpl in E. rewrite Hs in E. exact E.
      - pose proof (ev_seq s p1 p2) as E. rewrite Hs, H1 in E. exact E.
      - pose proof (ev_seq (s ++ p1) p2 []) as E. rewrite lenA, Hs, H1, H2, app_nil_r, <- app_assoc in E.
        exact E.
    Qed.

    Lemma split3 : forall env : list Z, length env = (n + 2 * m)%nat ->
      exists s p1 p2 : list Z, env = s ++ p1 ++ p2 /\ length s = n /\ length p1 = m /\ length p2 = m.
    Proof.
      intros env H. exists (firstn n env), (firstn m (skipn n env)), (skipn m (skipn n env)).
      rewrite !firstn_skipn. split; [reflexivity|].
      pose proof (firstn_skipn n env) as E1. pose proof (firstn_skipn m (skipn n env)) as E2.
      assert (L1 : length (firstn n env) = n) by (apply firstn_length_le; lia).
      assert (L2 : length (skipn n env) = (2 * m)%nat).
      { rewrite <- E1, lenA, L1 in H. lia. }
      assert (L3 : length (firstn m (skipn n env)) = m) by (apply firstn_length_le; lia).
      split; [exact L1|]. split; [exact L3|]. rewrite <- E2, lenA, L3 in L2. lia.
    Qed.

    Lemma sap_norm : forall e, exists k p, (k <= nkP)%nat /\ length p = m /\
      forall s, sap P m e s = sap P m (k, p) s.
    Proof.
      intros [k q]. unfold sap; simpl.
      destruct (nth_error (pk P) k) as [c|] eqn:Hc.
      - assert (Hk : (k < nkP)%nat) by (unfold nkP; apply nth_error_Some; congruence).
        destruct (Nat.eqb_spec (length q) m) as [Hq | Hq].
        + exists k, q. split; [lia|]. split; [exact Hq|]. intros s. rewrite Hc, Hq, Nat.eqb_refl. reflexivity.
        + exists nkP, (repeat 0%Z m). split; [lia|]. split; [apply len_repeat'|]. intros s.
          assert (Hn : nth_error (pk P) nkP = None) by (apply nth_error_None; unfold nkP; lia).
          rewrite Hn. reflexivity.
      - exists nkP, (repeat 0%Z m). split; [lia|]. split; [apply len_repeat'|]. intros s.
        assert (Hn : nth_error (pk P) nkP = None) by (apply nth_error_None; unfold nkP; lia).
        rewrite Hn. reflexivity.
    Qed.

    Lemma gov_norm : forall e k p, (forall s, sap P m e s = sap P m (k, p) s) ->
      forall t, govK (sap P m) (srp P) K e t = govK (sap P m) (srp P) K (k, p) t.
    Proof. intros e k p H t. unfold govK. rewrite H. reflexivity. Qed.

    Ltac lens := repeat first [apply len_symG | apply len_symR | apply len_symA | apply len_S0
                               | assumption].

    Theorem phi_term_exact : TermK (srp P) (svd P) n K <-> FValid phi_term.
    Proof.
      split.
      - intros H env Hl. destruct (split3 env Hl) as [s [p1 [p2 [-> [Hs [H1 H2]]]]]].
        destruct (env3 s p1 p2 Hs H1 H2) as [E0 _].
        unfold phi_term. rewrite evF_subst, ev_itr by lens. rewrite E0. apply H. exact Hs.
      - intros H s Hs. set (z := repeat 0%Z m).
        assert (Hz : length z = m) by apply len_repeat'.
        pose proof (H (s ++ z ++ z) ltac:(rewrite !lenA; lia)) as E.
        destruct (env3 s z z Hs Hz Hz) as [E0 _].
        unfold phi_term in E. rewrite evF_subst, ev_itr in E by lens. rewrite E0 in E. exact E.
    Qed.

    Theorem phi_cc1_exact : CC1Z (sap P m) (srp P) n K <->
      (forall k1 k2, (k1 <= nkP)%nat -> (k2 <= nkP)%nat -> FValid (phi_cc1 k1 k2)).
    Proof.
      split.
      - intros H k1 k2 _ _ env Hl. destruct (split3 env Hl) as [s [p1 [p2 [-> [Hs [H1 H2]]]]]].
        destruct (env3 s p1 p2 Hs H1 H2) as [E0 [E1 E2]].
        unfold phi_cc1. apply ev_eqL; [rewrite !len_symG by lens; reflexivity|].
        rewrite !ev_symG by lens. rewrite E0, E1, E2. apply H. exact Hs.
      - intros H s e1 e2 Hs.
        destruct (sap_norm e1) as [k1 [p1 [Hk1 [Hp1 N1]]]]. destruct (sap_norm e2) as [k2 [p2 [Hk2 [Hp2 N2]]]].
        rewrite !(gov_norm e1 k1 p1 N1), !(gov_norm e2 k2 p2 N2).
        pose proof (H k1 k2 Hk1 Hk2 (s ++ p1 ++ p2) ltac:(rewrite !lenA; lia)) as E.
        destruct (env3 s p1 p2 Hs Hp1 Hp2) as [E0 [E1 E2]].
        unfold phi_cc1 in E. apply ev_eqL in E; [|rewrite !len_symG by lens; reflexivity].
        rewrite !ev_symG in E by lens. rewrite E0, E1, E2 in E. exact E.
    Qed.

    Theorem phi_cc2_exact : CC2Z (sap P m) (srp P) (svd P) n K <->
      (forall k, (k <= nkP)%nat -> FValid (phi_cc2 k)).
    Proof.
      split.
      - intros H k _ env Hl. destruct (split3 env Hl) as [s [p1 [p2 [-> [Hs [H1 H2]]]]]].
        destruct (env3 s p1 p2 Hs H1 H2) as [E0 [E1 _]].
        unfold phi_cc2. simpl. rewrite evF_subst, E0. fold (svd P s).
        destruct (svd P s) eqn:Hv; [reflexivity|]. simpl.
        apply ev_eqL; [rewrite !len_symG by lens; reflexivity|].
        rewrite !ev_symG by lens. rewrite ev_symR by lens. rewrite E0, E1. apply H; assumption.
      - intros H s e Hs Hv.
        destruct (sap_norm e) as [k [p [Hk [Hp N]]]]. rewrite !(gov_norm e k p N).
        set (z := repeat 0%Z m). assert (Hz : length z = m) by apply len_repeat'.
        pose proof (H k Hk (s ++ p ++ z) ltac:(rewrite !lenA; lia)) as E.
        destruct (env3 s p z Hs Hp Hz) as [E0 [E1 _]].
        unfold phi_cc2 in E. simpl in E. rewrite evF_subst, E0 in E. fold (svd P s) in E.
        rewrite Hv in E. simpl in E.
        apply ev_eqL in E; [|rewrite !len_symG by lens; reflexivity].
        rewrite !ev_symG in E by lens. rewrite ev_symR in E by lens. rewrite E0, E1 in E. exact E.
    Qed.

    (* The reduction: if the generated formulas are valid (the solver's answer), every buffer from
       every integer state has a unique normal form; and conversely. *)
    Theorem lin_exact : FValid phi_term ->
      (UNZ evdec (sap P m) (srp P) (svd P) n <->
       (forall k1 k2, (k1 <= nkP)%nat -> (k2 <= nkP)%nat -> FValid (phi_cc1 k1 k2)) /\
       (forall k, (k <= nkP)%nat -> FValid (phi_cc2 k))).
    Proof.
      intros HT. pose proof (prog_shaped P n m Hw) as HS.
      rewrite (un_bounded evdec (sap P m) (srp P) (svd P) n K (sh_len_ap _ _ _ _ _ _ HS)
                 (sh_len_rp _ _ _ _ _ _ HS) (sh_rp_fix _ _ _ _ _ _ HS) (proj2 phi_term_exact HT)).
      rewrite phi_cc1_exact, phi_cc2_exact. reflexivity.
    Qed.

    Corollary lin_sound : FValid phi_term ->
      (forall k1 k2, (k1 <= nkP)%nat -> (k2 <= nkP)%nat -> FValid (phi_cc1 k1 k2)) ->
      (forall k, (k <= nkP)%nat -> FValid (phi_cc2 k)) ->
      forall s, length s = n -> forall B,
        UN (step evdec (sap P m) (srp P) (valid1 (svd P)) free_enabled) (s, B).
    Proof. intros HT H1 H2. exact (proj2 (lin_exact HT) (conj H1 H2)). Qed.
  End Exact.
End Linear.

(* ============================================================================================ *)
(* Composition with the symmetry reduction: a collection of items with integer fields.          *)
(* ============================================================================================ *)

(* A keyed collection of order-invariant items: one item checked over the representatives
   implies unique normal forms for every collection of any size (SymmetryCutoff.un_cutoff). *)
Theorem sym_abs : forall C n m nk ap rp vd K N,
  Shaped n m nk ap rp vd -> OrdInv C n ap rp vd -> (n + 2 * m <= N)%nat ->
  abs_check C n m nk ap rp vd K N = true ->
  forall l0, (forall s, In s l0 -> length s = n) -> forall B,
    UN (step (kdec evdec) (aL ap) (rL rp) (validL vd) free_enabled) (l0, B).
Proof.
  intros C n m nk ap rp vd K N HS HO HN Hc l0 Hl0 B.
  destruct (proj1 (abs_check_exact C n m nk ap rp vd HS HO K N HN) Hc) as [HT HU].
  apply (proj2 (un_cutoff evdec ap rp vd (PhiB rp vd K)
                  (wfcB rp vd n K (sh_len_rp _ _ _ _ _ _ HS) HT)
                  (fun s H => sh_rp_fix _ _ _ _ _ _ HS s H) l0)).
  intros k s0 Hk B'. apply HU. apply Hl0. eapply nth_error_In. exact Hk.
Qed.

(* ============================================================================================ *)
(* Non-vacuity: capped inventory (order fragment, declared cap).                                *)
(* ============================================================================================ *)

(* One variable (stock), one event kind Restock(level): stock := max(stock, level); invariant
   stock <= 5; repair clamps stock to the declared cap 5. *)
Definition capped : prog :=
  mkProg [[If (FLt (Vr 0) (Vr 1)) (Vr 1) (Vr 0)]] [Cst 5%Z] (FLe (Vr 0) (Cst 5%Z)).

Theorem capped_frag : wf capped 1 1 = true /\ ord_frag [5%Z] capped = true.
Proof. split; reflexivity. Qed.

(* Seven representatives: 5, 6, 7, 8 and 2, 3, 4. *)
Theorem capped_reps : reps 3 [5%Z] = [5; 6; 7; 8; 4; 3; 2]%Z /\ length (reps 3 [5%Z]) = 7%nat.
Proof. split; reflexivity. Qed.

Theorem capped_check : abs_check [5%Z] 1 1 1 (sap capped 1) (srp capped) (svd capped) 1 3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem capped_un : forall s, length s = 1%nat -> forall B,
  UN (step evdec (sap capped 1) (srp capped) (valid1 (svd capped)) free_enabled) (s, B).
Proof. exact (build_sound [5%Z] capped 1 1 1 3 eq_refl eq_refl ltac:(lia) capped_check). Qed.

Theorem capped_repair_fires : svd capped [7%Z] = false /\ srp capped [7%Z] = [5%Z].
Proof. split; reflexivity. Qed.

(* A catalog of capped items, any size, through one item over seven representatives. *)
Theorem capped_catalog : forall l0, (forall s, In s l0 -> length s = 1%nat) -> forall B,
  UN (step (kdec evdec) (aL (sap capped 1)) (rL (srp capped)) (validL (svd capped)) free_enabled)
     (l0, B).
Proof.
  exact (sym_abs [5%Z] 1 1 1 _ _ _ 1 3 (prog_shaped capped 1 1 eq_refl)
           (ord_frag_sound [5%Z] capped 1 1 eq_refl eq_refl) ltac:(lia) capped_check).
Qed.

(* ============================================================================================ *)
(* Non-vacuity: a wallet with integer balances (linear fragment).                               *)
(* ============================================================================================ *)

(* Variables (balance, overdrawn); Deposit(a): balance + a; Withdraw(a): balance - a; invariant:
   overdrawn = 1 exactly when balance < 0, else 0; repair recomputes the flag. *)
Definition wallet : prog :=
  mkProg [[Pl (Vr 0) (Vr 2); Vr 1]; [Mi (Vr 0) (Vr 2); Vr 1]]
         [Vr 0; If (FLt (Vr 0) (Cst 0%Z)) (Cst 1%Z) (Cst 0%Z)]
         (FOr (FAnd (FLt (Vr 0) (Cst 0%Z)) (FEq (Vr 1) (Cst 1%Z)))
              (FAnd (FLe (Cst 0%Z) (Vr 0)) (FEq (Vr 1) (Cst 0%Z)))).

Theorem wallet_frag : wf wallet 2 1 = true /\ lin_frag wallet = true /\
  forall C, ord_frag C wallet = false.
Proof. split; [reflexivity | split; [reflexivity | intros C; reflexivity]]. Qed.

(* A small decision procedure for these formulas, standing in for the solver: case split on the
   innermost comparisons, then linear arithmetic. *)
Ltac noif t := lazymatch t with context [if _ then _ else _] => fail | _ => idtac end.
Ltac zred := cbn -[Z.eqb Z.ltb Z.leb Z.add Z.sub Z.mul].
Ltac zstep := match goal with
  | |- context [Z.ltb ?x ?y] => noif x; noif y; destruct (Z.ltb_spec x y)
  | |- context [Z.leb ?x ?y] => noif x; noif y; destruct (Z.leb_spec x y)
  | |- context [Z.eqb ?x ?y] => noif x; noif y; destruct (Z.eqb_spec x y)
  end; zred; try (exfalso; lia).
Ltac zsolve := zred; repeat zstep; try reflexivity.

Theorem wallet_formulas : FValid 2 1 (phi_term wallet 2 1) /\
  (forall k1 k2, (k1 <= nkP wallet)%nat -> (k2 <= nkP wallet)%nat ->
     FValid 2 1 (phi_cc1 wallet 2 1 1 k1 k2)) /\
  (forall k, (k <= nkP wallet)%nat -> FValid 2 1 (phi_cc2 wallet 2 1 1 k)).
Proof.
  unfold nkP; simpl. split; [|split].
  - intros env H. destruct env as [|b [|o [|a1 [|a2 [|x t]]]]]; simpl in H; try discriminate. zsolve.
  - intros k1 k2 H1 H2 env H.
    destruct env as [|b [|o [|a1 [|a2 [|x t]]]]]; simpl in H; try discriminate.
    destruct k1 as [|[|[|k1]]]; [| | | lia]; destruct k2 as [|[|[|k2]]]; try lia; zsolve.
  - intros k Hk env H. destruct env as [|b [|o [|a1 [|a2 [|x t]]]]]; simpl in H; try discriminate.
    destruct k as [|[|[|k]]]; try lia; zsolve.
Qed.

(* Verified for every integer balance and every buffer, through the formulas. *)
Theorem wallet_un : forall s, length s = 2%nat -> forall B,
  UN (step evdec (sap wallet 1) (srp wallet) (valid1 (svd wallet)) free_enabled) (s, B).
Proof.
  destruct wallet_formulas as [HT [H1 H2]].
  exact (lin_sound wallet 2 1 1 eq_refl HT H1 H2).
Qed.

Theorem wallet_repair_fires : svd wallet [(-3)%Z; 0%Z] = false /\ srp wallet [(-3)%Z; 0%Z] = [(-3)%Z; 1%Z].
Proof. split; reflexivity. Qed.

(* ============================================================================================ *)
(* Boundary: an undeclared exact test.                                                          *)
(* ============================================================================================ *)

(* One variable (last), event Pay(amount, tag): if amount = 13 then last := tag. 13 is not
   declared. *)
Definition ex13 : prog := mkProg [[If (FEq (Vr 1) (Cst 13%Z)) (Vr 2) (Vr 0)]] [Vr 0] FT.

Lemma ex13_shaped : Shaped 1 2 1 (sap ex13 2) (srp ex13) (svd ex13).
Proof. exact (prog_shaped ex13 1 2 eq_refl). Qed.

Lemma ex13_term : TermK (srp ex13) (svd ex13) 1 0.
Proof. intros s _. reflexivity. Qed.

(* The representative check with no declared constants passes. *)
Theorem exact13_passes : abs_check [] 1 2 1 (sap ex13 2) (srp ex13) (svd ex13) 0 5 = true.
Proof. vm_compute. reflexivity. Qed.

(* Over the integers it diverges: Pay(13, 1) and Pay(13, 2) from last = 0. *)
Theorem exact13_diverges :
  ~ (forall B, UN (step evdec (sap ex13 2) (srp ex13) (valid1 (svd ex13)) free_enabled) ([0%Z], B)).
Proof.
  intros H.
  pose proof (un_at evdec (sap ex13 2) (srp ex13) (svd ex13) 1 0 (sh_len_ap _ _ _ _ _ _ ex13_shaped)
                (sh_len_rp _ _ _ _ _ _ ex13_shaped) (sh_rp_fix _ _ _ _ _ _ ex13_shaped) ex13_term
                [0%Z] eq_refl H (0%nat, [13%Z; 1%Z]) (0%nat, [13%Z; 2%Z])) as E.
  vm_compute in E. discriminate.
Qed.

(* The fragment check refuses it; with 13 declared it is in the fragment and the check fails. *)
Theorem exact13_refused : wf ex13 1 2 = true /\ ord_frag [] ex13 = false.
Proof. split; reflexivity. Qed.

Theorem exact13_declared : ord_frag [13%Z] ex13 = true /\
  abs_check [13%Z] 1 2 1 (sap ex13 2) (srp ex13) (svd ex13) 0 5 = false.
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

(* ============================================================================================ *)
(* Boundary: an additive rule fools the order-pattern check.                                    *)
(* ============================================================================================ *)

(* Variables (x, y, z); guard x < y < z < x + y; event A: if guard then x := y; event B: if guard
   then y := x. *)
Definition tri_g : form :=
  FAnd (FLt (Vr 0) (Vr 1)) (FAnd (FLt (Vr 1) (Vr 2)) (FLt (Vr 2) (Pl (Vr 0) (Vr 1)))).
Definition triangle : prog :=
  mkProg [[If tri_g (Vr 1) (Vr 0); Vr 1; Vr 2]; [Vr 0; If tri_g (Vr 0) (Vr 1); Vr 2]]
         [Vr 0; Vr 1; Vr 2] FT.

Lemma triangle_shaped : Shaped 3 0 2 (sap triangle 0) (srp triangle) (svd triangle).
Proof. exact (prog_shaped triangle 3 0 eq_refl). Qed.

(* The order-pattern check over 0, 1, 2 (one value per order position) passes. *)
Theorem triangle_passes : abs_check [] 3 0 2 (sap triangle 0) (srp triangle) (svd triangle) 0 3 = true.
Proof. vm_compute. reflexivity. Qed.

(* At (2, 3, 4) the guard holds and A, B diverge. *)
Theorem triangle_diverges :
  ~ (forall B, UN (step evdec (sap triangle 0) (srp triangle) (valid1 (svd triangle)) free_enabled)
                  ([2%Z; 3%Z; 4%Z], B)).
Proof.
  intros H.
  pose proof (un_at evdec (sap triangle 0) (srp triangle) (svd triangle) 3 0
                (sh_len_ap _ _ _ _ _ _ triangle_shaped) (sh_len_rp _ _ _ _ _ _ triangle_shaped)
                (sh_rp_fix _ _ _ _ _ _ triangle_shaped) (fun s _ => eq_refl)
                [2%Z; 3%Z; 4%Z] eq_refl H (0%nat, []) (1%nat, [])) as E.
  vm_compute in E. discriminate.
Qed.

(* The fragment check refuses it (it adds), and the linear route rejects it: its CC1 formula is
   refuted at (2, 3, 4). *)
Theorem triangle_refused : wf triangle 3 0 = true /\ ord_frag [] triangle = false /\
  lin_frag triangle = true.
Proof. split; [|split]; reflexivity. Qed.

Theorem triangle_formula_refuted : evalF [2%Z; 3%Z; 4%Z] (phi_cc1 triangle 3 0 0 0 1) = false /\
  ~ FValid 3 0 (phi_cc1 triangle 3 0 0 0 1).
Proof.
  split; [vm_compute; reflexivity|]. intros H. specialize (H [2%Z; 3%Z; 4%Z] eq_refl).
  vm_compute in H. discriminate.
Qed.

(* ============================================================================================ *)
(* The cutoff cannot drop below n.                                                              *)
(* ============================================================================================ *)

(* Variables (x, y); A: x := y; B: y := x. Order invariant with no constants. They diverge exactly
   when x <> y, which one representative cannot show. *)
Definition copy : prog := mkProg [[Vr 1; Vr 1]; [Vr 0; Vr 0]] [Vr 0; Vr 1] FT.

Lemma copy_shaped : Shaped 2 0 2 (sap copy 0) (srp copy) (svd copy).
Proof. exact (prog_shaped copy 2 0 eq_refl). Qed.

Theorem copy_tight : ord_frag [] copy = true /\
  abs_check [] 2 0 2 (sap copy 0) (srp copy) (svd copy) 0 1 = true /\
  abs_check [] 2 0 2 (sap copy 0) (srp copy) (svd copy) 0 2 = false /\
  ~ (forall B, UN (step evdec (sap copy 0) (srp copy) (valid1 (svd copy)) free_enabled) ([0%Z; 1%Z], B)).
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  intros H.
  pose proof (un_at evdec (sap copy 0) (srp copy) (svd copy) 2 0
                (sh_len_ap _ _ _ _ _ _ copy_shaped) (sh_len_rp _ _ _ _ _ _ copy_shaped)
                (sh_rp_fix _ _ _ _ _ _ copy_shaped) (fun s _ => eq_refl)
                [0%Z; 1%Z] eq_refl H (0%nat, []) (1%nat, [])) as E.
  vm_compute in E. discriminate.
Qed.
