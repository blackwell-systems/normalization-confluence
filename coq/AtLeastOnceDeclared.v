(* AtLeastOnceDeclared.v: the exact (necessary and sufficient) condition for at-least-once
   delivery when a registry DECLARES its independent pairs I (gap 15 (a) of REGIME-AUDIT.md).
   Axiom-free.

   The model of declared independence. Trace.v (run_tequiv) and gsm's Build give the
   exactly-once guarantee for a registry that declares Independent pairs: two event sequences that
   differ only by reordering declared-independent events (Mazurkiewicz trace equivalence, tequiv I)
   must reach the same state, and gsm reports every undeclared pair that does not commute as one
   that must be causally ordered (CausalOrderRequired). So a delivery is pinned to a reference
   history o (what the sender emitted), and the order o fixes on undeclared pairs is the order every
   replica must see. AtLeastOnceExact.v proves exact at-least-once conditions for free delivery and
   for causal delivery only.

   Setting. A governed step (step e) applies event e and repairs. Ev is the set of events in range,
   hb an irreflexive happens-before that constrains which histories exist (nohb: every duplicate-free
   list is a history), and I the declared independence: symmetric, irreflexive, and never declared
   on a pair hb orders (I_hb). A reference history o is a causal (hb) duplicate-free list over Ev.

   - ALOI o d (an at-least-once delivery d of the history o under I): every pair that some copy in
     d delivers out of o's order is declared independent:
       prec a b o -> d = l ++ r -> In b l -> In a r -> I a b.
     d may repeat events; each copy, the first or a redelivery, may move only as far as I permits.
     On exactly-once deliveries this is precisely trace equivalence (aloi_nodup_iff):
       NoDup d -> Permutation d o -> (ALOI o d <-> tequiv I d o).
   - DALOConv s0: every ALOI delivery d of a history o (same events) reaches run o s0.
   - CommI s0: declared pairs commute after every reachable exactly-once prefix:
       causal hb (p ++ [a; b]) -> I a b -> step b (step a (run p s0)) = step a (step b (run p s0)).
   - TConvI s0: exactly-once trace convergence (tequiv I runs from a history agree).
   - IdemAt s0 a (AtLeastOnceExact): a is idempotent at every state run u s0 with u ++ [a] a history.
   - AbsorbI s0 a: after every history w containing a whose later events are all declared
     independent of a (exactly the histories after which a redelivery of a may land), a redelivery
     of a is a no-op.
   - SafeI s0 a: an ALOI delivery whose only duplicates are copies of a reaches the state of its
     exactly-once projection.

   Exact results.
   - tconv_exact          : TConvI s0 <-> CommI s0.
   - dalo_exact           : DALOConv s0 <-> CommI s0 /\ forall a, IdemAt s0 a.
   - dalo_exact_absorb    : DALOConv s0 <-> CommI s0 /\ forall a, AbsorbI s0 a.
   - dalo_exact_trace     : DALOConv s0 <-> TConvI s0 /\ forall a, IdemAt s0 a.
   - safe_i_exact         : SafeI s0 a <-> AbsorbI s0 a.
   - safe_i_iff_idem      : CommI s0 -> (SafeI s0 a <-> IdemAt s0 a).
   - aloi_nodup_iff       : the model is trace equivalence on exactly-once deliveries.
   With no causal constraint (hb = nohb), IdemAt is IdemReach: the idempotence clause is the free
   one, and only the commutation clause narrows, from every pair (CommReach) to declared pairs.

   Retries unordered (a weaker transport: only first copies respect the declared order).
   - DALOConvR s0: every d whose first copies form a trace-equivalent history (ALOI o (dedup d))
     reaches run o s0; a redelivery may land anywhere, also past an undeclared partner.
   - dalo_r_exact : DALOConvR s0 <-> CommI s0 /\ forall a, AbsorbR s0 a, where AbsorbR s0 a: a
     redelivery of a is absorbed after EVERY history containing a.
   - safe_r_exact : SafeR s0 a <-> AbsorbR s0 a (per event).
   - dalo_r_implies : DALOConvR s0 -> DALOConv s0; strict by fl_retry_order_needed.

   Recovered as corollaries (proved through dalo_exact, not through AtLeastOnceExact's theorems).
   - free_dalo_iff, alo_exact_declared: I = distinctness, hb = nohb gives ALOConv and alo_exact.
   - causal_dalo_iff, causal_alo_exact_declared: I = concurrent hb gives CALOConv and
     causal_alo_exact_idem.

   gsm (Report.NotIdempotent lists the events a with some valid s, step a (step a s) <> step a s).
   - dalo_notidem_needs_dedup, dalo_notidem_needs_dedup_once: sound at reachable witnesses (a
     witness state reached by an ALOI delivery duplicating only a, or by a history).
   - dalo_gsm_unlisted_safe: complete when CommI s0 holds and every reachable state is valid.
   - dalo_unlisted_converge: under the same hypotheses, deliveries that duplicate only unlisted
     events converge, so deduplicating the listed events suffices.
   - build_comm_i, dalo_gsm_build: Build's check (declared pairs commute at every valid state) and
     valid reachable states give CommI; with NotIdempotent empty every ALOI delivery converges.

   Counterexamples and non-vacuity.
   - fl_declared_exact: the flag with a max-register, Add and Remove undeclared (gsm would report
     them as must be causally ordered), every other distinct pair declared: DALOConv, CommI, IdemAt
     and SafeI hold from every start. Free at-least-once delivery fails there (~ ALOConv, in
     fl_retry_order_needed), so the instance is out of reach of alo_exact.
   - fl_retry_order_needed: in the same registry, the delivery [Add; Remove; Add], whose first
     copies are exactly the history [Add; Remove], is not ALOI (the retry of Add crosses the
     undeclared Remove) and diverges, although Add is idempotent at every state (gsm does not list
     it). The qualifier that retries too respect the declared order cannot be dropped to first
     deliveries only: SafeR fails for Add and DALOConvR fails, although CommI holds, so under
     unordered retries NotIdempotent is not complete.
   - fl_partner_overtakes: Add and Remove DECLARED independent. Every event is idempotent at every
     state (IdemAt holds, gsm lists nothing), but the redelivery of Add overtakes its declared
     partner Remove: Add needs deduplication, CommI and DALOConv fail. The commutation clause is
     needed, and completeness of NotIdempotent needs CommI (gsm's Build rejects this declaration).
   - fl_gsm_build: the same registry passes gsm's checks (Build on the declared pairs, NotIdempotent
     empty), and dalo_gsm_build gives DALOConv.
   - mx_declared_r: the clamped max-register with every distinct pair declared satisfies CommI and
     AbsorbR, so DALOConvR holds (non-vacuity of dalo_r_exact).
   - inc_declared_fails: the capped increment: CommI holds, IdemAt fails, DALOConv fails (the
     idempotence clause is needed).
   - jmp_declared_unreachable: an event NotIdempotent lists (witness at an unreachable state) is
     safe and DALOConv holds: NotIdempotent over-reports without reachability. *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.CausalReplay NC.AtLeastOnce NC.AtLeastOnceExact.
Require NC.GovernanceConverse.
Import ListNotations.

(* ============================================================================================ *)
(* List and order facts.                                                                        *)
(* ============================================================================================ *)

Lemma decl_tequiv_mono : forall {E : Type} (R R' : E -> E -> Prop),
  (forall a b, R a b -> R' a b) -> forall l1 l2, tequiv R l1 l2 -> tequiv R' l1 l2.
Proof.
  intros E R R' HR l1 l2 H.
  induction H as [l | l a b r Hab | l1 l2 _ IH | l1 l2 l3 _ IH1 _ IH2].
  - apply teq_refl.
  - apply teq_swap. apply HR. exact Hab.
  - apply teq_sym. exact IH.
  - apply teq_trans with l2; assumption.
Qed.

(* Bubble an event to the front past events related to it. *)
Lemma decl_bubble : forall {E : Type} (R : E -> E -> Prop) l a r,
  (forall b, In b l -> R b a) -> tequiv R (l ++ a :: r) (a :: l ++ r).
Proof.
  intros E R. induction l as [| b l IH]; intros a r H; simpl; [apply teq_refl |].
  apply teq_trans with (l2 := b :: a :: l ++ r).
  - apply tequiv_cons. apply IH. intros b' Hb'. apply H. right. exact Hb'.
  - apply (teq_swap R [] b a (l ++ r)). apply H. left. reflexivity.
Qed.

Lemma decl_prec_neq : forall {E : Type} (x y : E) o, NoDup o -> prec x y o -> x <> y.
Proof.
  intros E x y o. induction o as [| z t IH]; intros Hnd H; simpl in H; [contradiction |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hz Hnd].
  destruct H as [[-> Hy] | H].
  - intros ->. exact (Hz Hy).
  - exact (IH Hnd H).
Qed.

Lemma decl_prec_asym : forall {E : Type} (x y : E) o, NoDup o -> prec x y o -> prec y x o -> False.
Proof.
  intros E x y o. induction o as [| z t IH]; intros Hnd H1 H2; simpl in H1, H2; [contradiction |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hz Hnd].
  destruct H1 as [[Ez Hy] | H1]; destruct H2 as [[Ez' Hx] | H2].
  - subst. exact (Hz Hx).
  - subst z. exact (Hz (prec_in_r _ _ _ H2)).
  - subst z. exact (Hz (prec_in_r _ _ _ H1)).
  - exact (IH Hnd H1 H2).
Qed.

Lemma decl_prec_total : forall {E : Type} (x y : E) o, In x o -> In y o -> x <> y ->
  prec x y o \/ prec y x o.
Proof.
  intros E x y o. induction o as [| z t IH]; intros Hx Hy Hne; [destruct Hx |].
  simpl in Hx, Hy. simpl.
  destruct Hx as [Ex | Hx].
  - subst z. destruct Hy as [Ey | Hy]; [exfalso; exact (Hne Ey) |].
    left. left. split; [reflexivity | exact Hy].
  - destruct Hy as [Ey | Hy].
    + subst z. right. left. split; [reflexivity | exact Hx].
    + destruct (IH Hx Hy Hne) as [H | H]; [left | right]; right; exact H.
Qed.

(* A split with y on the left and x on the right puts y before x. *)
Lemma decl_inv_prec : forall {E : Type} (d l r : list E) x y,
  d = l ++ r -> In y l -> In x r -> prec y x d.
Proof.
  intros E d l. revert d. induction l as [| z l IH]; intros d r x y Ed Hy Hx; [destruct Hy |].
  subst d. simpl. destruct Hy as [Ez | Hy].
  - left. split; [exact Ez | apply in_or_app; right; exact Hx].
  - right. exact (IH _ r x y eq_refl Hy Hx).
Qed.

Lemma decl_prec_split : forall {E : Type} (d : list E) y x,
  prec y x d -> exists l r, d = l ++ r /\ In y l /\ In x r.
Proof.
  intros E d y x. induction d as [| z t IH]; intros H; simpl in H; [contradiction |].
  destruct H as [[Ez Hx] | H].
  - exists [z], t. split; [reflexivity | split; [left; exact Ez | exact Hx]].
  - destruct (IH H) as [l [r [Et [Hy Hx]]]]. exists (z :: l), r.
    split; [rewrite Et; reflexivity | split; [right; exact Hy | exact Hx]].
Qed.

Lemma decl_prec_snoc_inv : forall {E : Type} (q : list E) x y z,
  prec y x (q ++ [z]) -> prec y x q \/ (x = z /\ In y q).
Proof.
  intros E q x y z. induction q as [| w q IH]; intros H; simpl in H.
  - destruct H as [[_ []] | []].
  - destruct H as [[Ew Hx] | H].
    + apply in_app_or in Hx. destruct Hx as [Hx | [Hx | []]].
      * left. left. split; [exact Ew | exact Hx].
      * right. split; [symmetry; exact Hx | left; exact Ew].
    + destruct (IH H) as [H' | [Ex Hy]].
      * left. right. exact H'.
      * right. split; [exact Ex | right; exact Hy].
Qed.

Lemma decl_prec_app_r : forall {E : Type} (a b : E) q t, prec a b q -> prec a b (q ++ t).
Proof.
  intros E a b q t. induction q as [| x q IH]; intros H; simpl in *; [contradiction |].
  destruct H as [[Ex Hin] | H]; [left; split; [exact Ex | apply in_or_app; left; exact Hin] |].
  right. exact (IH H).
Qed.

Lemma decl_prec_snoc : forall {E : Type} (a b : E) q, In a q -> prec a b (q ++ [b]).
Proof.
  intros E a b q. induction q as [| x q IH]; intros Ha; simpl in *; [contradiction |].
  destruct Ha as [Ex | Ha]; [left; split; [exact Ex | apply in_or_app; right; left; reflexivity] |].
  right. exact (IH Ha).
Qed.

(* Precedence in the exactly-once projection comes from precedence in the delivery. *)
Lemma decl_prec_dedup : forall {E : Type} dec (d : list E) y x,
  prec y x (dedup dec d) -> prec y x d.
Proof.
  intros E dec d y x. induction d as [| z p IH] using rev_ind; intros H; [destruct H |].
  rewrite dedup_snoc in H. destruct (in_dec dec z (dedup dec p)) as [Hz | Hz].
  - apply decl_prec_app_r. exact (IH H).
  - destruct (decl_prec_snoc_inv _ x y z H) as [H' | [-> Hy]].
    + apply decl_prec_app_r. exact (IH H').
    + apply decl_prec_snoc. apply (dedup_In dec). exact Hy.
Qed.

Lemma decl_prec_insert : forall {E : Type} (l r : list E) a y x,
  prec y x (l ++ r) -> prec y x (l ++ a :: r).
Proof.
  intros E l r a y x. induction l as [| z l IH]; intros H; simpl in *; [right; exact H |].
  destruct H as [[Ez Hx] | H].
  - left. split; [exact Ez | apply in_insert; exact Hx].
  - right. exact (IH H).
Qed.

Lemma decl_prec_mid_l : forall {E : Type} (l r : list E) a b, In b l -> prec b a (l ++ a :: r).
Proof.
  intros E l r a b. induction l as [| z l IH]; intros Hb; [destruct Hb |]. simpl.
  destruct Hb as [Ez | Hb].
  - left. split; [exact Ez | apply in_or_app; right; left; reflexivity].
  - right. exact (IH Hb).
Qed.

Lemma decl_prec_mid_r : forall {E : Type} (l r : list E) a b, In b r -> prec a b (l ++ a :: r).
Proof.
  intros E l r a b Hb. induction l as [| z l IH]; simpl.
  - left. split; [reflexivity | exact Hb].
  - right. exact IH.
Qed.

Lemma decl_prec_last_contra : forall {E : Type} (u : list E) a b,
  NoDup (u ++ [a]) -> prec a b (u ++ [a]) -> False.
Proof.
  intros E u a b. induction u as [| z u IH]; intros Hnd H; simpl in H.
  - destruct H as [[_ []] | []].
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hz Hnd].
    destruct H as [[Ez _] | H].
    + subst z. apply Hz. apply in_or_app. right. left. reflexivity.
    + exact (IH Hnd H).
Qed.

(* ============================================================================================ *)
(* The declared-independence model.                                                              *)
(* ============================================================================================ *)

Section Declared.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.       (* governed step: apply, then repair *)
  Variable Ev : E -> Prop.           (* events in range *)
  Variable hb : E -> E -> Prop.      (* happens-before: which histories exist *)
  Variable I : E -> E -> Prop.       (* declared independence *)
  Hypothesis hb_irrefl : forall x, ~ hb x x.
  Hypothesis I_sym : forall a b, I a b -> I b a.
  Hypothesis I_irrefl : forall a, ~ I a a.
  Hypothesis I_hb : forall a b, I a b -> ~ hb a b.

  Local Notation run := (runT step).

  (* d is an at-least-once delivery of the history o under I: every pair that some copy in d
     delivers out of o's order is declared independent. *)
  Definition ALOI (o d : list E) : Prop :=
    forall a b, prec a b o -> forall l r, d = l ++ r -> In b l -> In a r -> I a b.

  (* At-least-once convergence under declared independence. *)
  Definition DALOConv (s0 : S) : Prop :=
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d <-> In x o) -> ALOI o d ->
      run d s0 = run o s0.

  (* Declared pairs commute after every reachable exactly-once prefix. *)
  Definition CommI (s0 : S) : Prop :=
    forall p a b, Forall Ev (p ++ [a; b]) -> causal hb (p ++ [a; b]) -> I a b ->
      step b (step a (run p s0)) = step a (step b (run p s0)).

  (* Exactly-once convergence under declared independence: trace-equivalent histories agree. *)
  Definition TConvI (s0 : S) : Prop :=
    forall o1 o2, Forall Ev o1 -> causal hb o1 -> tequiv I o1 o2 -> run o1 s0 = run o2 s0.

  (* A redelivery of a is absorbed after every history containing a whose later events are all
     declared independent of a. *)
  Definition AbsorbI (s0 : S) (a : E) : Prop :=
    forall w, Forall Ev w -> causal hb w -> In a w -> (forall b, prec a b w -> I a b) ->
      step a (run w s0) = run w s0.

  (* a needs no deduplication under I. *)
  Definition SafeI (s0 : S) (a : E) : Prop :=
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d <-> In x o) -> ALOI o d ->
      DupOnly (eq a) d -> run d s0 = run (dedup dec d) s0.

  (* gsm's Build check on declared pairs: they commute at every valid state. *)
  Definition BuildI (valid : S -> Prop) : Prop :=
    forall a b s, Ev a -> Ev b -> I a b -> valid s -> step b (step a s) = step a (step b s).

  (* ----- the model on exactly-once deliveries is trace equivalence ----- *)

  Lemma I_conc_hb : forall a b, I a b -> concurrent hb a b.
  Proof.
    intros a b H. split; [| split].
    - intros ->. exact (I_irrefl b H).
    - exact (I_hb a b H).
    - exact (I_hb b a (I_sym a b H)).
  Qed.

  Lemma tequiv_I_causal : forall o1 o2, tequiv I o1 o2 -> causal hb o1 -> causal hb o2.
  Proof.
    intros o1 o2 H Hc.
    exact (proj1 (NC.GovernanceConverse.tequiv_causal hb o1 o2 (decl_tequiv_mono I _ I_conc_hb o1 o2 H)) Hc).
  Qed.

  (* Two duplicate-free orders whose inversions are all declared pairs are trace-equivalent. *)
  Lemma inv_tequiv : forall o l1, NoDup l1 -> Permutation l1 o ->
    (forall a b, prec a b o -> prec b a l1 -> I a b) -> tequiv I l1 o.
  Proof.
    induction o as [| a o IH]; intros l1 Hnd HP Hinv.
    - apply Permutation_sym, Permutation_nil in HP. subst. apply teq_refl.
    - assert (Ha : In a l1) by (apply (Permutation_in a (Permutation_sym HP)); left; reflexivity).
      apply in_split in Ha. destruct Ha as [l [r ->]].
      assert (Har : ~ In a (l ++ r)) by (apply NoDup_remove_2; exact Hnd).
      apply teq_trans with (l2 := a :: l ++ r).
      + apply decl_bubble. intros b Hb. apply I_sym. apply Hinv.
        * left. split; [reflexivity |].
          assert (Hb' : In b (a :: o)) by (apply (Permutation_in b HP); apply in_or_app; left; exact Hb).
          destruct Hb' as [Eb | Hb']; [| exact Hb'].
          exfalso. apply Har. apply in_or_app. left. rewrite Eb. exact Hb.
        * apply decl_prec_mid_l. exact Hb.
      + apply tequiv_cons. apply IH.
        * exact (NoDup_remove_1 _ _ _ Hnd).
        * exact (Permutation_app_inv l r [] o a HP).
        * intros x y Hxy Hyx. apply Hinv; [right; exact Hxy | apply decl_prec_insert; exact Hyx].
  Qed.

  (* Trace-equivalent duplicate-free orders differ only on declared pairs. *)
  Lemma tequiv_inv : forall l1 l2, tequiv I l1 l2 -> NoDup l1 ->
    forall x y, prec x y l1 -> prec y x l2 -> I x y.
  Proof.
    intros l1 l2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2];
      intros Hnd x y Hxy Hyx.
    - exfalso. exact (decl_prec_asym x y l Hnd Hxy Hyx).
    - destruct (dec x a) as [-> | Hxa]; [destruct (dec y b) as [-> | Hyb] |].
      + exact Hab.
      + exfalso. apply (decl_prec_asym a y (l ++ a :: b :: r) Hnd Hxy).
        apply NC.GovernanceConverse.prec_swap; [intros [Ey _]; exact (Hyb Ey) | exact Hyx].
      + exfalso. apply (decl_prec_asym x y (l ++ a :: b :: r) Hnd Hxy).
        apply NC.GovernanceConverse.prec_swap; [intros [_ Ex]; exact (Hxa Ex) | exact Hyx].
    - apply I_sym. apply (IH (Permutation_NoDup (tequiv_perm _ _ _ (teq_sym _ _ _ H)) Hnd) y x Hyx Hxy).
    - assert (Hnd2 : NoDup l2) by exact (Permutation_NoDup (tequiv_perm _ _ _ H1) Hnd).
      assert (Hne : x <> y) by exact (decl_prec_neq x y l1 Hnd Hxy).
      assert (Hx2 : In x l2) by exact (Permutation_in x (tequiv_perm _ _ _ H1) (GovernanceConverse.prec_in_l _ _ _ Hxy)).
      assert (Hy2 : In y l2) by exact (Permutation_in y (tequiv_perm _ _ _ H1) (prec_in_r _ _ _ Hxy)).
      destruct (decl_prec_total x y l2 Hx2 Hy2 Hne) as [H | H].
      + exact (IH2 Hnd2 x y H Hyx).
      + exact (IH1 Hnd x y Hxy H).
  Qed.

  Theorem aloi_nodup_iff : forall o d, NoDup d -> Permutation d o -> (ALOI o d <-> tequiv I d o).
  Proof.
    intros o d Hnd HP. split.
    - intros HA. apply inv_tequiv; [exact Hnd | exact HP |].
      intros a b Hab Hba. destruct (decl_prec_split d b a Hba) as [l [r [Ed [Hb Ha]]]].
      exact (HA a b Hab l r Ed Hb Ha).
    - intros Ht a b Hab l r Ed Hb Ha.
      apply (tequiv_inv o d (teq_sym _ _ _ Ht) (Permutation_NoDup HP Hnd) a b Hab).
      exact (decl_inv_prec d l r a b Ed Hb Ha).
  Qed.

  Lemma aloi_prefix : forall o p q, ALOI o (p ++ q) -> ALOI o p.
  Proof.
    intros o p q H a b Hab l r Ep Hb Ha. apply (H a b Hab l (r ++ q)); [| exact Hb | ].
    - rewrite Ep, <- app_assoc. reflexivity.
    - apply in_or_app. left. exact Ha.
  Qed.

  Lemma aloi_dedup : forall o d, ALOI o d -> ALOI o (dedup dec d).
  Proof.
    intros o d H a b Hab l r Ed Hb Ha.
    pose proof (decl_prec_dedup dec d b a (decl_inv_prec _ l r a b Ed Hb Ha)) as Hp.
    destruct (decl_prec_split d b a Hp) as [l' [r' [Ed' [Hb' Ha']]]].
    exact (H a b Hab l' r' Ed' Hb' Ha').
  Qed.

  (* A duplicate-free list inside a history, whose inversions are declared, is a history. *)
  Lemma inv_causal : forall o w, causal hb o -> NoDup w -> (forall x, In x w -> In x o) ->
    (forall a b, prec a b o -> prec b a w -> I a b) -> causal hb w.
  Proof.
    intros o w [_ Hco] Hnd Hin Hinv. split; [exact Hnd |]. intros x y Hxy Hx Hy.
    assert (Hne : x <> y) by (intros ->; exact (hb_irrefl y Hxy)).
    destruct (decl_prec_total x y w Hx Hy Hne) as [H | H]; [exact H |].
    exfalso. exact (I_hb x y (Hinv x y (Hco x y Hxy (Hin x Hx) (Hin y Hy)) H) Hxy).
  Qed.

  Lemma aloi_dedup_causal : forall o d, causal hb o -> (forall x, In x d -> In x o) -> ALOI o d ->
    causal hb (dedup dec d).
  Proof.
    intros o d Ho Hin HA. apply (inv_causal o); [exact Ho | apply dedup_NoDup | |].
    - intros x Hx. apply Hin. apply (dedup_In dec). exact Hx.
    - intros a b Hab Hba. destruct (decl_prec_split _ b a Hba) as [l [r [Ed [Hb Ha]]]].
      exact (aloi_dedup o d HA a b Hab l r Ed Hb Ha).
  Qed.

  (* ----- exactly-once convergence ----- *)

  Lemma comm_i_tequiv : forall s0, CommI s0 ->
    forall o1 o2, tequiv I o1 o2 -> causal hb o1 -> Forall Ev o1 -> run o1 s0 = run o2 s0.
  Proof.
    intros s0 HC o1 o2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2];
      intros Hc Hev.
    - reflexivity.
    - rewrite !runT_app, !runT_cons. rewrite (HC l a b); [reflexivity | | | exact Hab].
      + replace (l ++ a :: b :: r) with ((l ++ [a; b]) ++ r) in Hev
          by (rewrite <- app_assoc; reflexivity).
        apply Forall_app in Hev. exact (proj1 Hev).
      + apply (NC.GovernanceConverse.causal_prefix hb _ r). rewrite <- app_assoc. exact Hc.
    - symmetry. apply IH.
      + exact (tequiv_I_causal l2 l1 (teq_sym _ _ _ H) Hc).
      + apply (Permutation_Forall (Permutation_sym (tequiv_perm _ _ _ H))). exact Hev.
    - rewrite (IH1 Hc Hev). apply IH2.
      + exact (tequiv_I_causal l1 l2 H1 Hc).
      + apply (Permutation_Forall (tequiv_perm _ _ _ H1)). exact Hev.
  Qed.

  Theorem tconv_exact : forall s0, TConvI s0 <-> CommI s0.
  Proof.
    intros s0. split.
    - intros H p a b Hev Hc Hab.
      pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hev Hc (teq_swap I p a b [] Hab)) as Eq.
      rewrite !runT_app in Eq. exact Eq.
    - intros HC o1 o2 Hev Hc Ht. exact (comm_i_tequiv s0 HC o1 o2 Ht Hc Hev).
  Qed.

  (* ----- witnesses: the deliveries the necessity directions use ----- *)

  Lemma aloi_swap : forall p a b, NoDup (p ++ [a; b]) -> I a b -> ALOI (p ++ [a; b]) (p ++ [b; a]).
  Proof.
    intros p a b Hnd Hab x y Hxy l r Ed Hy Hx.
    pose proof (decl_inv_prec _ l r x y Ed Hy Hx) as Hyx.
    destruct (dec x a) as [-> | Hxa]; [destruct (dec y b) as [-> | Hyb] |].
    - exact Hab.
    - exfalso. apply (decl_prec_asym a y (p ++ [a; b]) Hnd Hxy).
      apply NC.GovernanceConverse.prec_swap; [intros [Ey _]; exact (Hyb Ey) | exact Hyx].
    - exfalso. apply (decl_prec_asym x y (p ++ [a; b]) Hnd Hxy).
      apply NC.GovernanceConverse.prec_swap; [intros [_ Ex]; exact (Hxa Ex) | exact Hyx].
  Qed.

  Lemma aloi_snoc_absorb : forall w a, NoDup w -> (forall b, prec a b w -> I a b) ->
    ALOI w (w ++ [a]).
  Proof.
    intros w a Hnd Ha x y Hxy l r Ed Hy Hx.
    pose proof (decl_inv_prec _ l r x y Ed Hy Hx) as Hyx.
    destruct (dec x a) as [-> | Hxa].
    - exact (Ha y Hxy).
    - destruct (decl_prec_snoc_inv w x y a Hyx) as [H | [Ex _]].
      + exfalso. exact (decl_prec_asym x y w Hnd Hxy H).
      + exfalso. exact (Hxa Ex).
  Qed.

  Lemma aloi_snoc_dup : forall u a, NoDup (u ++ [a]) -> ALOI (u ++ [a]) (u ++ [a; a]).
  Proof.
    intros u a Hnd x y Hxy l r Ed Hy Hx.
    pose proof (decl_inv_prec _ l r x y Ed Hy Hx) as Hyx.
    replace (u ++ [a; a]) with ((u ++ [a]) ++ [a]) in Hyx by (rewrite <- app_assoc; reflexivity).
    destruct (decl_prec_snoc_inv (u ++ [a]) x y a Hyx) as [H | [-> _]].
    - exfalso. exact (decl_prec_asym x y _ Hnd Hxy H).
    - exfalso. exact (decl_prec_last_contra u a y Hnd Hxy).
  Qed.

  Lemma forall_in : forall (o d : list E), Forall Ev o -> (forall x, In x d -> In x o) -> Forall Ev d.
  Proof.
    intros o d Ho H. apply Forall_forall. intros x Hx. rewrite Forall_forall in Ho. exact (Ho x (H x Hx)).
  Qed.

  (* ----- absorption removes the duplicates ----- *)

  Lemma absorb_dedup_i : forall s0 (P : E -> Prop), (forall a, P a -> AbsorbI s0 a) ->
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d -> In x o) -> ALOI o d ->
      DupOnly P d -> run d s0 = run (dedup dec d) s0.
  Proof.
    intros s0 P HA o d. induction d as [| x p IH] using rev_ind; intros Hev Ho Hin HAl Hdo;
      [reflexivity |].
    assert (Hinp : forall y, In y p -> In y o) by (intros y Hy; apply Hin; apply in_or_app; left; exact Hy).
    rewrite dedup_snoc, runT_app, run1,
      (IH Hev Ho Hinp (aloi_prefix o p [x] HAl) (dupOnly_prefix P p x Hdo)).
    destruct (in_dec dec x (dedup dec p)) as [Hx | Hx].
    - assert (Hxp : In x p) by (apply (dedup_In dec); exact Hx).
      apply HA.
      + apply (Hdo p x []); [reflexivity | exact Hxp].
      + apply (forall_in o); [exact Hev |]. intros y Hy. apply Hinp. apply (dedup_In dec). exact Hy.
      + exact (aloi_dedup_causal o p Ho Hinp (aloi_prefix o p [x] HAl)).
      + exact Hx.
      + intros b Hxb.
        assert (Hne : x <> b) by exact (decl_prec_neq x b _ (dedup_NoDup dec p) Hxb).
        destruct (decl_prec_split p x b (decl_prec_dedup dec p x b Hxb)) as [l [r [Ep [Hxl Hbr]]]].
        assert (Hbo : In b o) by (apply Hinp; rewrite Ep; apply in_or_app; right; exact Hbr).
        destruct (decl_prec_total x b o (Hinp x Hxp) Hbo Hne) as [H | H].
        * apply (HAl x b H (l ++ r) [x]); [rewrite Ep; reflexivity | | left; reflexivity].
          apply in_or_app. right. exact Hbr.
        * apply I_sym. apply (HAl b x H l (r ++ [x])); [| exact Hxl | ].
          -- rewrite Ep, <- app_assoc. reflexivity.
          -- apply in_or_app. left. exact Hbr.
    - rewrite runT_app. reflexivity.
  Qed.

  (* ----- the per-event exact condition ----- *)

  Theorem safe_i_exact : forall s0 a, SafeI s0 a <-> AbsorbI s0 a.
  Proof.
    intros s0 a. split.
    - intros HS w Hev Hc Ha Hlater.
      assert (Hd : dedup dec (w ++ [a]) = w).
      { rewrite dedup_snoc, (dedup_nodup_id dec w (proj1 Hc)).
        destruct (in_dec dec a w) as [_ | Hn]; [reflexivity | contradiction]. }
      pose proof (HS w (w ++ [a])) as H. rewrite Hd, runT_app, run1 in H. apply H.
      + exact Hev.
      + exact Hc.
      + intros x. rewrite in_app_iff. simpl. split; [intros [Hx | [<- | []]]; assumption | tauto].
      + exact (aloi_snoc_absorb w a (proj1 Hc) Hlater).
      + exact (dupOnly_nodup_snoc w a (proj1 Hc)).
    - intros HA o d Hev Ho Hset HAl Hdo.
      apply (absorb_dedup_i s0 (eq a)) with (o := o); try assumption.
      + intros x <-. exact HA.
      + intros x Hx. apply Hset. exact Hx.
  Qed.

  Lemma absorb_idem_i : forall s0 a, AbsorbI s0 a -> IdemAt step Ev hb s0 a.
  Proof.
    intros s0 a HA u Hev Hc.
    pose proof (HA (u ++ [a]) Hev Hc (in_or_app u [a] a (or_intror (or_introl eq_refl)))) as H.
    rewrite runT_app, run1 in H. apply H.
    intros b Hb. exfalso. exact (decl_prec_last_contra u a b (proj1 Hc) Hb).
  Qed.

  Lemma idem_absorb_i : forall s0 a, CommI s0 -> IdemAt step Ev hb s0 a -> AbsorbI s0 a.
  Proof.
    intros s0 a HC HI w Hev Hc Ha Hlater.
    apply in_split in Ha. destruct Ha as [l [r ->]].
    assert (Ht : tequiv I (l ++ a :: r) ((l ++ r) ++ [a])).
    { rewrite <- app_assoc. apply tequiv_app_l. apply tequiv_to_back.
      intros b Hb. apply Hlater. apply decl_prec_mid_r. exact Hb. }
    assert (Hc' : causal hb ((l ++ r) ++ [a])) by exact (tequiv_I_causal _ _ Ht Hc).
    assert (Hev' : Forall Ev ((l ++ r) ++ [a])) by exact (Permutation_Forall (tequiv_perm _ _ _ Ht) Hev).
    rewrite (comm_i_tequiv s0 HC _ _ Ht Hc Hev), runT_app, run1.
    exact (HI (l ++ r) Hev' Hc').
  Qed.

  Theorem safe_i_iff_idem : forall s0 a, CommI s0 -> (SafeI s0 a <-> IdemAt step Ev hb s0 a).
  Proof.
    intros s0 a HC. rewrite safe_i_exact. split; [apply absorb_idem_i | apply idem_absorb_i; exact HC].
  Qed.

  (* ----- the run-level exact condition ----- *)

  Theorem dalo_exact_absorb : forall s0, DALOConv s0 <-> CommI s0 /\ forall a, AbsorbI s0 a.
  Proof.
    intros s0. split.
    - intros H. split.
      + intros p a b Hev Hc Hab.
        assert (HP : Permutation (p ++ [a; b]) (p ++ [b; a]))
          by (apply Permutation_app_head; apply perm_swap).
        pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hev Hc
                      (fun x => conj (Permutation_in x (Permutation_sym HP)) (Permutation_in x HP))
                      (aloi_swap p a b (proj1 Hc) Hab)) as Eq.
        rewrite !runT_app in Eq. symmetry. exact Eq.
      + intros a w Hev Hc Ha Hlater.
        pose proof (H w (w ++ [a])) as Eq. rewrite runT_app, run1 in Eq. apply Eq.
        * exact Hev.
        * exact Hc.
        * intros x. rewrite in_app_iff. simpl. split; [intros [Hx | [<- | []]]; assumption | tauto].
        * exact (aloi_snoc_absorb w a (proj1 Hc) Hlater).
    - intros [HC HA] o d Hev Ho Hset HAl.
      assert (Hin : forall x, In x d -> In x o) by (intros x Hx; apply Hset; exact Hx).
      rewrite (absorb_dedup_i s0 (fun _ => True) (fun a _ => HA a) o d Hev Ho Hin HAl
                 (fun _ _ _ _ _ => Logic.I)).
      assert (HP : Permutation (dedup dec d) o).
      { apply NoDup_Permutation; [apply dedup_NoDup | exact (proj1 Ho) |].
        intros x. rewrite dedup_In. apply Hset. }
      apply (comm_i_tequiv s0 HC).
      + exact (proj1 (aloi_nodup_iff o (dedup dec d) (dedup_NoDup dec d) HP) (aloi_dedup o d HAl)).
      + exact (aloi_dedup_causal o d Ho Hin HAl).
      + apply (forall_in o); [exact Hev |]. intros x Hx. apply Hin. apply (dedup_In dec). exact Hx.
  Qed.

  Theorem dalo_exact : forall s0, DALOConv s0 <-> CommI s0 /\ forall a, IdemAt step Ev hb s0 a.
  Proof.
    intros s0. rewrite dalo_exact_absorb. split; intros [HC H]; split; try exact HC; intros a.
    - apply absorb_idem_i. exact (H a).
    - apply idem_absorb_i; [exact HC | exact (H a)].
  Qed.

  Theorem dalo_exact_trace : forall s0,
    DALOConv s0 <-> TConvI s0 /\ forall a, IdemAt step Ev hb s0 a.
  Proof. intros s0. rewrite dalo_exact, tconv_exact. reflexivity. Qed.

  Theorem dalo_safe : forall s0, DALOConv s0 -> forall a, SafeI s0 a.
  Proof.
    intros s0 H a. apply safe_i_exact. exact (proj2 (proj1 (dalo_exact_absorb s0) H) a).
  Qed.

  (* ----- gsm: NotIdempotent under declared independence ----- *)

  (* Soundness at reachable witnesses: a witness state reached by an ALOI delivery that duplicates
     only a, after which a may be delivered twice, means a needs deduplication. *)
  Theorem dalo_notidem_needs_dedup : forall s0 a u o,
    Forall Ev o -> causal hb o -> (forall x, In x (u ++ [a]) <-> In x o) ->
    ALOI o (u ++ [a; a]) -> DupOnly (eq a) u ->
    step a (step a (run u s0)) <> step a (run u s0) -> ~ SafeI s0 a.
  Proof.
    intros s0 a u o Hev Ho Hset HAl Hdo Hne HS. apply Hne.
    assert (Hdo1 : DupOnly (eq a) (u ++ [a])).
    { intros l x r Ed Hx. destruct (rev_case r) as [-> | [z [r' ->]]].
      - apply app_inj_tail in Ed. destruct Ed as [_ ->]. reflexivity.
      - rewrite app_comm_cons, app_assoc in Ed. apply app_inj_tail in Ed.
        destruct Ed as [Eu _]. exact (Hdo l x r' Eu Hx). }
    assert (Hdo2 : DupOnly (eq a) ((u ++ [a]) ++ [a])).
    { intros l x r Ed Hx. destruct (rev_case r) as [-> | [z [r' ->]]].
      - apply app_inj_tail in Ed. destruct Ed as [_ ->]. reflexivity.
      - rewrite app_comm_cons, app_assoc in Ed. apply app_inj_tail in Ed.
        destruct Ed as [Eu _]. exact (Hdo1 l x r' Eu Hx). }
    assert (HAl2 : ALOI o ((u ++ [a]) ++ [a])) by (rewrite <- app_assoc; exact HAl).
    assert (HAl1 : ALOI o (u ++ [a])) by exact (aloi_prefix o _ [a] HAl2).
    assert (Hset2 : forall x, In x ((u ++ [a]) ++ [a]) <-> In x o).
    { intros x. rewrite <- Hset, !in_app_iff. simpl. tauto. }
    pose proof (HS o (u ++ [a]) Hev Ho Hset HAl1 Hdo1) as E1.
    pose proof (HS o ((u ++ [a]) ++ [a]) Hev Ho Hset2 HAl2 Hdo2) as E2.
    rewrite (dedup_snoc dec (u ++ [a]) a) in E2.
    destruct (in_dec dec a (dedup dec (u ++ [a]))) as [_ | Hn].
    - assert (Eq : run ((u ++ [a]) ++ [a]) s0 = run (u ++ [a]) s0) by (rewrite E2, E1; reflexivity).
      rewrite !runT_app, !run1 in Eq. exact Eq.
    - exfalso. apply Hn. apply dedup_In. apply in_or_app. right. left. reflexivity.
  Qed.

  (* The common case: the witness state is reached by a history. *)
  Theorem dalo_notidem_needs_dedup_once : forall s0 a u,
    Forall Ev (u ++ [a]) -> causal hb (u ++ [a]) ->
    step a (step a (run u s0)) <> step a (run u s0) -> ~ SafeI s0 a.
  Proof.
    intros s0 a u Hev Hc Hne.
    apply (dalo_notidem_needs_dedup s0 a u (u ++ [a]) Hev Hc (fun x => iff_refl _)
             (aloi_snoc_dup u a (proj1 Hc))); [| exact Hne].
    intros l x r Ed Hx. exfalso. subst u. apply (NoDup_remove_2 l r x).
    - exact (NoDup_app_remove_r (l ++ x :: r) [a] (proj1 Hc)).
    - apply in_or_app. left. exact Hx.
  Qed.

  (* Completeness: when declared pairs commute at reachable states and every reachable state is
     valid, an event NotIdempotent does not list needs no deduplication. *)
  Theorem dalo_gsm_unlisted_safe : forall (valid : S -> Prop) s0 a, CommI s0 ->
    (forall u, Forall Ev u -> causal hb u -> valid (run u s0)) ->
    (forall s, valid s -> step a (step a s) = step a s) -> SafeI s0 a.
  Proof.
    intros valid s0 a HC Hval Hid. apply (proj2 (safe_i_iff_idem s0 a HC)).
    intros u Hev Hc. apply Hid, Hval.
    - apply Forall_app in Hev. exact (proj1 Hev).
    - exact (NC.GovernanceConverse.causal_prefix hb u [a] Hc).
  Qed.

  (* Deduplicating the listed events suffices: a delivery that duplicates only unlisted events
     converges. *)
  Theorem dalo_unlisted_converge : forall (valid : S -> Prop) s0, CommI s0 ->
    (forall u, Forall Ev u -> causal hb u -> valid (run u s0)) ->
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d <-> In x o) -> ALOI o d ->
      DupOnly (fun a => forall s, valid s -> step a (step a s) = step a s) d ->
      run d s0 = run o s0.
  Proof.
    intros valid s0 HC Hval o d Hev Ho Hset HAl Hdo.
    assert (Hin : forall x, In x d -> In x o) by (intros x Hx; apply Hset; exact Hx).
    rewrite (absorb_dedup_i s0 _ (fun a Ha => proj1 (safe_i_exact s0 a)
               (dalo_gsm_unlisted_safe valid s0 a HC Hval Ha)) o d Hev Ho Hin HAl Hdo).
    assert (HP : Permutation (dedup dec d) o).
    { apply NoDup_Permutation; [apply dedup_NoDup | exact (proj1 Ho) |].
      intros x. rewrite dedup_In. apply Hset. }
    apply (comm_i_tequiv s0 HC).
    + exact (proj1 (aloi_nodup_iff o (dedup dec d) (dedup_NoDup dec d) HP) (aloi_dedup o d HAl)).
    + exact (aloi_dedup_causal o d Ho Hin HAl).
    + apply (forall_in o); [exact Hev |]. intros x Hx. apply Hin. apply (dedup_In dec). exact Hx.
  Qed.

  (* Build's check on declared pairs, with every reachable state valid, gives CommI. *)
  Theorem build_comm_i : forall (valid : S -> Prop) s0, BuildI valid ->
    (forall u, Forall Ev u -> causal hb u -> valid (run u s0)) -> CommI s0.
  Proof.
    intros valid s0 HB Hval p a b Hev Hc Hab.
    apply Forall_app in Hev. destruct Hev as [Hp Hab'].
    inversion Hab' as [| ? ? Ha Hb']; subst. inversion Hb' as [| ? ? Hb _]; subst.
    apply HB; [exact Ha | exact Hb | exact Hab |]. apply Hval; [exact Hp |].
    exact (NC.GovernanceConverse.causal_prefix hb p [a; b] Hc).
  Qed.

  (* Build passes on the declared pairs and NotIdempotent lists no event in range: every
     at-least-once delivery under I converges. *)
  Theorem dalo_gsm_build : forall (valid : S -> Prop) s0, BuildI valid ->
    (forall u, Forall Ev u -> causal hb u -> valid (run u s0)) ->
    (forall a, Ev a -> forall s, valid s -> step a (step a s) = step a s) -> DALOConv s0.
  Proof.
    intros valid s0 HB Hval Hid. apply (proj2 (dalo_exact s0)).
    split; [exact (build_comm_i valid s0 HB Hval) |].
    intros a u Hev Hc. apply Forall_app in Hev. destruct Hev as [Hu Ha].
    inversion Ha as [| ? ? Ha' _]; subst. apply (Hid a Ha'). apply Hval; [exact Hu |].
    exact (NC.GovernanceConverse.causal_prefix hb u [a] Hc).
  Qed.

  (* ----- retries unordered: only first deliveries respect the declared order ----- *)

  (* A weaker transport: the first copies form a trace-equivalent history (ALOI o (dedup d)), and
     a redelivery may land anywhere after its first copy, also past an undeclared partner. *)
  Definition DALOConvR (s0 : S) : Prop :=
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d <-> In x o) ->
      ALOI o (dedup dec d) -> run d s0 = run o s0.

  (* A redelivery of a is absorbed after every history containing a. *)
  Definition AbsorbR (s0 : S) (a : E) : Prop :=
    forall w, Forall Ev w -> causal hb w -> In a w -> step a (run w s0) = run w s0.

  Definition SafeR (s0 : S) (a : E) : Prop :=
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d <-> In x o) ->
      ALOI o (dedup dec d) -> DupOnly (eq a) d -> run d s0 = run (dedup dec d) s0.

  Lemma dedup_app_prefix : forall p q, exists t, dedup dec (p ++ q) = dedup dec p ++ t.
  Proof.
    intros p q. induction q as [| x q IH] using rev_ind.
    - exists []. rewrite !app_nil_r. reflexivity.
    - destruct IH as [t Et]. rewrite app_assoc, dedup_snoc, Et.
      destruct (in_dec dec x (dedup dec p ++ t)); [exists t; reflexivity |].
      exists (t ++ [x]). rewrite app_assoc. reflexivity.
  Qed.

  Lemma aloi_self : forall o, NoDup o -> ALOI o o.
  Proof.
    intros o Hnd a b Hab l r Eo Hb Ha. exfalso.
    exact (decl_prec_asym a b o Hnd Hab (decl_inv_prec o l r a b Eo Hb Ha)).
  Qed.

  Lemma aloi_nodup_causal : forall o w, causal hb o -> NoDup w -> (forall x, In x w -> In x o) ->
    ALOI o w -> causal hb w.
  Proof.
    intros o w Ho Hnd Hin HA. apply (inv_causal o w Ho Hnd Hin).
    intros a b Hab Hba. destruct (decl_prec_split w b a Hba) as [l [r [Ed [Hb Ha]]]].
    exact (HA a b Hab l r Ed Hb Ha).
  Qed.

  Lemma absorb_dedup_r : forall s0 (P : E -> Prop), (forall a, P a -> AbsorbR s0 a) ->
    forall o d, Forall Ev o -> causal hb o -> (forall x, In x d -> In x o) ->
      ALOI o (dedup dec d) -> DupOnly P d -> run d s0 = run (dedup dec d) s0.
  Proof.
    intros s0 P HA o d. induction d as [| x p IH] using rev_ind; intros Hev Ho Hin HAl Hdo;
      [reflexivity |].
    assert (Hinp : forall y, In y p -> In y o) by (intros y Hy; apply Hin; apply in_or_app; left; exact Hy).
    assert (HAp : ALOI o (dedup dec p)).
    { destruct (dedup_app_prefix p [x]) as [t Et]. rewrite Et in HAl. exact (aloi_prefix o _ t HAl). }
    rewrite dedup_snoc, runT_app, run1, (IH Hev Ho Hinp HAp (dupOnly_prefix P p x Hdo)).
    destruct (in_dec dec x (dedup dec p)) as [Hx | Hx].
    - apply HA.
      + apply (Hdo p x []); [reflexivity | apply (dedup_In dec); exact Hx].
      + apply (forall_in o); [exact Hev |]. intros y Hy. apply Hinp. apply (dedup_In dec). exact Hy.
      + apply (aloi_nodup_causal o); [exact Ho | apply dedup_NoDup | | exact HAp].
        intros y Hy. apply Hinp. apply (dedup_In dec). exact Hy.
      + exact Hx.
    - rewrite runT_app. reflexivity.
  Qed.

  Theorem safe_r_exact : forall s0 a, SafeR s0 a <-> AbsorbR s0 a.
  Proof.
    intros s0 a. split.
    - intros HS w Hev Hc Ha.
      assert (Hd : dedup dec (w ++ [a]) = w).
      { rewrite dedup_snoc, (dedup_nodup_id dec w (proj1 Hc)).
        destruct (in_dec dec a w) as [_ | Hn]; [reflexivity | contradiction]. }
      pose proof (HS w (w ++ [a])) as H. rewrite Hd, runT_app, run1 in H. apply H.
      + exact Hev.
      + exact Hc.
      + intros x. rewrite in_app_iff. simpl. split; [intros [Hx | [<- | []]]; assumption | tauto].
      + exact (aloi_self w (proj1 Hc)).
      + exact (dupOnly_nodup_snoc w a (proj1 Hc)).
    - intros HA o d Hev Ho Hset HAl Hdo.
      apply (absorb_dedup_r s0 (eq a)) with (o := o); try assumption.
      + intros x <-. exact HA.
      + intros x Hx. apply Hset. exact Hx.
  Qed.

  Theorem dalo_r_exact : forall s0, DALOConvR s0 <-> CommI s0 /\ forall a, AbsorbR s0 a.
  Proof.
    intros s0. split.
    - intros H. split.
      + intros p a b Hev Hc Hab.
        assert (HP : Permutation (p ++ [a; b]) (p ++ [b; a]))
          by (apply Permutation_app_head; apply perm_swap).
        assert (Hnd' : NoDup (p ++ [b; a])) by exact (Permutation_NoDup HP (proj1 Hc)).
        pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hev Hc
                      (fun x => conj (Permutation_in x (Permutation_sym HP)) (Permutation_in x HP))) as Eq.
        rewrite (dedup_nodup_id dec _ Hnd') in Eq.
        specialize (Eq (aloi_swap p a b (proj1 Hc) Hab)).
        rewrite !runT_app in Eq. symmetry. exact Eq.
      + intros a w Hev Hc Ha.
        assert (Hd : dedup dec (w ++ [a]) = w).
        { rewrite dedup_snoc, (dedup_nodup_id dec w (proj1 Hc)).
          destruct (in_dec dec a w) as [_ | Hn]; [reflexivity | contradiction]. }
        pose proof (H w (w ++ [a])) as Eq. rewrite Hd, runT_app, run1 in Eq. apply Eq.
        * exact Hev.
        * exact Hc.
        * intros x. rewrite in_app_iff. simpl. split; [intros [Hx | [<- | []]]; assumption | tauto].
        * exact (aloi_self w (proj1 Hc)).
    - intros [HC HA] o d Hev Ho Hset HAl.
      assert (Hin : forall x, In x d -> In x o) by (intros x Hx; apply Hset; exact Hx).
      assert (Hin' : forall x, In x (dedup dec d) -> In x o)
        by (intros x Hx; apply Hin; apply (dedup_In dec); exact Hx).
      rewrite (absorb_dedup_r s0 (fun _ => True) (fun a _ => HA a) o d Hev Ho Hin HAl
                 (fun _ _ _ _ _ => Logic.I)).
      assert (HP : Permutation (dedup dec d) o).
      { apply NoDup_Permutation; [apply dedup_NoDup | exact (proj1 Ho) |].
        intros x. rewrite dedup_In. apply Hset. }
      apply (comm_i_tequiv s0 HC).
      + exact (proj1 (aloi_nodup_iff o (dedup dec d) (dedup_NoDup dec d) HP) HAl).
      + exact (aloi_nodup_causal o _ Ho (dedup_NoDup dec d) Hin' HAl).
      + apply (forall_in o); [exact Hev | exact Hin'].
  Qed.

  (* Unordered retries are a strictly weaker transport: convergence there implies it under ALOI. *)
  Theorem dalo_r_implies : forall s0, DALOConvR s0 -> DALOConv s0.
  Proof.
    intros s0 H o d Hev Ho Hset HAl. exact (H o d Hev Ho Hset (aloi_dedup o d HAl)).
  Qed.
End Declared.

Arguments ALOI {E} I o d.
Arguments DALOConv {S E} step Ev hb I s0.
Arguments CommI {S E} step Ev hb I s0.
Arguments TConvI {S E} step Ev hb I s0.
Arguments AbsorbI {S E} step Ev hb I s0 a.
Arguments SafeI {S E} dec step Ev hb I s0 a.
Arguments BuildI {S E} step Ev I valid.
Arguments DALOConvR {S E} dec step Ev hb I s0.
Arguments AbsorbR {S E} step Ev hb s0 a.
Arguments SafeR {S E} dec step Ev hb I s0 a.

(* ============================================================================================ *)
(* Free and causal delivery as instances.                                                       *)
(* ============================================================================================ *)

Section Instances.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.
  Variable Ev : E -> Prop.

  (* Free delivery: every distinct pair declared, no causal constraint. *)
  Definition neqI (a b : E) : Prop := a <> b.

  Lemma neqI_sym : forall a b, neqI a b -> neqI b a.
  Proof. intros a b H E1. apply H. symmetry. exact E1. Qed.

  Lemma neqI_irrefl : forall a, ~ neqI a a.
  Proof. intros a H. apply H. reflexivity. Qed.

  Lemma neqI_hb : forall a b, neqI a b -> ~ (@nohb E) a b.
  Proof. intros a b _ []. Qed.

  Theorem free_dalo_iff : forall s0, DALOConv step Ev nohb neqI s0 <-> ALOConv step Ev s0.
  Proof.
    intros s0. split.
    - intros H d o Hev Hnd Hset. apply H.
      + apply (forall_in Ev d); [exact Hev |]. intros x Hx. apply Hset. exact Hx.
      + apply causal_nohb. exact Hnd.
      + intros x. symmetry. apply Hset.
      + intros a b Hab _ _ _ _ _. exact (decl_prec_neq a b o Hnd Hab).
    - intros H o d Hev Ho Hset _. apply H.
      + apply (forall_in Ev o); [exact Hev |]. intros x Hx. apply Hset. exact Hx.
      + exact (proj1 (causal_nohb o) Ho).
      + intros x. symmetry. apply Hset.
  Qed.

  Lemma free_comm_iff : forall s0, CommI step Ev nohb neqI s0 <-> CommReach step Ev s0.
  Proof.
    intros s0. split.
    - intros H p a b Hev Hab Hnd. exact (H p a b Hev (proj2 (causal_nohb _) Hnd) Hab).
    - intros H p a b Hev Hc Hab. exact (H p a b Hev Hab (proj1 (causal_nohb _) Hc)).
  Qed.

  (* alo_exact, recovered through the declared-independence theorem. *)
  Theorem alo_exact_declared : forall s0,
    ALOConv step Ev s0 <-> CommReach step Ev s0 /\ forall a, IdemReach step Ev s0 a.
  Proof.
    intros s0. rewrite <- free_dalo_iff, <- free_comm_iff.
    rewrite (dalo_exact dec step Ev nohb neqI nohb_irrefl neqI_sym neqI_irrefl neqI_hb s0).
    split; intros [HC H]; split; try exact HC; intros a; apply idem_iff; exact (H a).
  Qed.

  (* Causal delivery: exactly the concurrent pairs declared. *)
  Variable hb : E -> E -> Prop.
  Hypothesis hb_irrefl : forall x, ~ hb x x.

  Lemma conc_irrefl : forall a, ~ concurrent hb a a.
  Proof. intros a [H _]. apply H. reflexivity. Qed.

  Lemma conc_hb : forall a b, concurrent hb a b -> ~ hb a b.
  Proof. intros a b [_ [H _]]. exact H. Qed.

  Theorem causal_dalo_iff : forall s0,
    DALOConv step Ev hb (concurrent hb) s0 <-> CALOConv step Ev hb s0.
  Proof.
    intros s0. split.
    - intros H d o Hev Hca Ho Hset. apply H.
      + apply (forall_in Ev d); [exact Hev |]. intros x Hx. apply Hset. exact Hx.
      + exact Ho.
      + intros x. symmetry. apply Hset.
      + intros a b Hab l r Ed Hb Ha. split; [| split].
        * exact (decl_prec_neq a b o (proj1 Ho) Hab).
        * intro Hhb. exact (Hca a b Hhb l r Ed Hb Ha).
        * intro Hhb. destruct Ho as [Hnd Hco].
          apply (decl_prec_asym a b o Hnd Hab).
          apply Hco; [exact Hhb | exact (prec_in_r _ _ _ Hab) | exact (GovernanceConverse.prec_in_l _ _ _ Hab)].
    - intros H o d Hev Ho Hset HAl. apply H.
      + apply (forall_in Ev o); [exact Hev |]. intros x Hx. apply Hset. exact Hx.
      + intros a b Hab l r Ed Hb Ha.
        assert (Hp : prec a b o).
        { destruct Ho as [_ Hco]. apply Hco; [exact Hab | |]; apply Hset.
          - rewrite Ed. apply in_or_app. right. exact Ha.
          - rewrite Ed. apply in_or_app. left. exact Hb. }
        exact (conc_hb a b (HAl a b Hp l r Ed Hb Ha) Hab).
      + exact Ho.
      + intros x. symmetry. apply Hset.
  Qed.

  Lemma causal_comm_iff : forall s0, CommI step Ev hb (concurrent hb) s0 <-> CCRon step Ev hb s0.
  Proof.
    intros s0. split.
    - intros H p a b Hev Hab Hc. exact (H p a b Hev Hc Hab).
    - intros H p a b Hev Hc Hab. exact (H p a b Hev Hab Hc).
  Qed.

  (* causal_alo_exact_idem, recovered through the declared-independence theorem. *)
  Theorem causal_alo_exact_declared : forall s0,
    CALOConv step Ev hb s0 <-> CCRon step Ev hb s0 /\ forall a, IdemAt step Ev hb s0 a.
  Proof.
    intros s0. rewrite <- causal_dalo_iff, <- causal_comm_iff.
    exact (dalo_exact dec step Ev hb (concurrent hb) hb_irrefl (concurrent_sym hb) conc_irrefl conc_hb s0).
  Qed.
End Instances.

Arguments neqI {E} a b.

(* ============================================================================================ *)
(* Counterexamples and non-vacuity.                                                              *)
(* ============================================================================================ *)

(* The flag with a max-register: Add and Remove do not commute, every other distinct pair does. *)
Definition fl_dep (a b : fev) : bool :=
  match a, b with
  | FAdd, FRemove | FRemove, FAdd => true
  | _, _ => false
  end.

(* Declared: every distinct pair except Add/Remove (gsm would report Add/Remove as a pair that must
   be causally ordered). *)
Definition fl_I (a b : fev) : Prop := a <> b /\ fl_dep a b = false.

Lemma fl_I_sym : forall a b, fl_I a b -> fl_I b a.
Proof.
  intros a b [Hne Hd]. split; [intros E1; apply Hne; symmetry; exact E1 |].
  destruct a as [| | i], b as [| | j]; exact Hd.
Qed.

Lemma fl_I_irrefl : forall a, ~ fl_I a a.
Proof. intros a [H _]. apply H. reflexivity. Qed.

Lemma fl_I_hb : forall a b, fl_I a b -> ~ (@nohb fev) a b.
Proof. intros a b _ []. Qed.

Lemma fl_I_comm : forall a b s, fl_I a b -> fl_step b (fl_step a s) = fl_step a (fl_step b s).
Proof.
  intros a b [f n] [_ Hd].
  destruct a as [| | i], b as [| | j]; simpl in *; try reflexivity; try discriminate Hd.
  f_equal. lia.
Qed.

Theorem fl_declared_exact : forall s0,
  DALOConv fl_step (fun _ => True) nohb fl_I s0 /\
  CommI fl_step (fun _ => True) nohb fl_I s0 /\
  (forall a, IdemAt fl_step (fun _ => True) nohb s0 a) /\
  (forall a, SafeI fev_dec fl_step (fun _ => True) nohb fl_I s0 a).
Proof.
  intros s0.
  assert (HC : CommI fl_step (fun _ => True) nohb fl_I s0)
    by (intros p a b _ _ Hab; exact (fl_I_comm a b _ Hab)).
  assert (HI : forall a, IdemAt fl_step (fun _ => True) nohb s0 a)
    by (intros a u _ _; exact (fl_idem a _ Logic.I)).
  assert (HD : DALOConv fl_step (fun _ => True) nohb fl_I s0)
    by exact (proj2 (dalo_exact fev_dec fl_step (fun _ => True) nohb fl_I nohb_irrefl
                       fl_I_sym fl_I_irrefl fl_I_hb s0) (conj HC HI)).
  split; [exact HD |]. split; [exact HC |]. split; [exact HI |].
  exact (dalo_safe fev_dec fl_step (fun _ => True) nohb fl_I nohb_irrefl fl_I_sym fl_I_irrefl fl_I_hb s0 HD).
Qed.

Lemma fl_nodup_ar : NoDup [FAdd; FRemove].
Proof. constructor; [intros [H | []]; discriminate H | constructor; [intros [] | constructor]]. Qed.

(* Retries must respect the declared order too. In the registry above every ALOI delivery
   converges and NotIdempotent lists nothing, yet the delivery [Add; Remove; Add], whose
   exactly-once projection is the history [Add; Remove] itself, diverges: the retry of Add crosses
   the undeclared Remove, so it is not ALOI. Ordering only first deliveries is not enough, and free
   at-least-once delivery fails. *)
Theorem fl_retry_order_needed :
  DALOConv fl_step (fun _ => True) nohb fl_I (false, 0) /\
  ~ ALOConv fl_step (fun _ => True) (false, 0) /\
  (forall s, fl_step FAdd (fl_step FAdd s) = fl_step FAdd s) /\
  dedup fev_dec [FAdd; FRemove; FAdd] = [FAdd; FRemove] /\
  ~ ALOI fl_I [FAdd; FRemove] [FAdd; FRemove; FAdd] /\
  runT fl_step [FAdd; FRemove; FAdd] (false, 0) <> runT fl_step [FAdd; FRemove] (false, 0) /\
  ~ SafeR fev_dec fl_step (fun _ => True) nohb fl_I (false, 0) FAdd /\
  ~ DALOConvR fev_dec fl_step (fun _ => True) nohb fl_I (false, 0).
Proof.
  assert (Hs : forall x, In x [FAdd; FRemove; FAdd] <-> In x [FAdd; FRemove]) by (intros x; simpl; tauto).
  assert (Hc : causal nohb [FAdd; FRemove]) by exact (proj2 (causal_nohb _) fl_nodup_ar).
  assert (HA : ALOI fl_I [FAdd; FRemove] (dedup fev_dec [FAdd; FRemove; FAdd])).
  { exact (aloi_self fl_I [FAdd; FRemove] fl_nodup_ar). }
  split; [exact (proj1 (fl_declared_exact (false, 0))) |].
  split; [exact (proj2 (proj2 (proj2 (proj2 flag_idem_needs_dedup)))) |].
  split; [intros s; exact (fl_idem FAdd s Logic.I) |].
  split; [reflexivity |]. split; [| split; [discriminate | split]].
  2: { intro H. specialize (H [FAdd; FRemove] [FAdd; FRemove; FAdd] (Forall_True _) Hc Hs HA fl_dup_add).
       vm_compute in H. discriminate H. }
  2: { intro H. specialize (H [FAdd; FRemove] [FAdd; FRemove; FAdd] (Forall_True _) Hc Hs HA).
       vm_compute in H. discriminate H. }
  intros H. assert (Hp : prec FAdd FRemove [FAdd; FRemove]) by (left; split; [reflexivity | left; reflexivity]).
  destruct (H FAdd FRemove Hp [FAdd; FRemove] [FAdd] eq_refl (or_intror (or_introl eq_refl))
              (or_introl eq_refl)) as [_ Hd].
  discriminate Hd.
Qed.

(* Add and Remove DECLARED independent (every distinct pair declared). Every event is idempotent at
   every state, so IdemAt holds and NotIdempotent lists nothing, but the redelivery of Add overtakes
   its declared partner Remove: Add needs deduplication, and CommI and DALOConv fail. gsm's Build
   rejects this declaration (CC1 fails on the declared pair), which is what restores CommI. *)
Theorem fl_partner_overtakes :
  (forall a s, fl_step a (fl_step a s) = fl_step a s) /\
  (forall a, IdemAt fl_step (fun _ => True) nohb (false, 0) a) /\
  ALOI neqI [FAdd; FRemove] [FAdd; FRemove; FAdd] /\
  ~ SafeI fev_dec fl_step (fun _ => True) nohb neqI (false, 0) FAdd /\
  ~ CommI fl_step (fun _ => True) nohb neqI (false, 0) /\
  ~ DALOConv fl_step (fun _ => True) nohb neqI (false, 0).
Proof.
  assert (HA : ALOI neqI [FAdd; FRemove] [FAdd; FRemove; FAdd]).
  { intros a b Hab _ _ _ _ _. exact (decl_prec_neq a b _ fl_nodup_ar Hab). }
  assert (Hns : ~ SafeI fev_dec fl_step (fun _ => True) nohb neqI (false, 0) FAdd).
  { intro H. specialize (H [FAdd; FRemove] [FAdd; FRemove; FAdd] (Forall_True _)
                           (proj2 (causal_nohb _) fl_nodup_ar)).
    assert (Hs : forall x, In x [FAdd; FRemove; FAdd] <-> In x [FAdd; FRemove]) by (intros x; simpl; tauto).
    specialize (H Hs HA fl_dup_add). vm_compute in H. discriminate H. }
  split; [intros a s; exact (fl_idem a s Logic.I) |].
  split; [intros a u _ _; exact (fl_idem a _ Logic.I) |].
  split; [exact HA |]. split; [exact Hns |]. split.
  - intro H. specialize (H [] FAdd FRemove (Forall_True _) (proj2 (causal_nohb _) fl_nodup_ar)
                          ltac:(discriminate)). discriminate H.
  - intro H. exact (Hns (dalo_safe fev_dec fl_step (fun _ => True) nohb neqI nohb_irrefl
                           neqI_sym neqI_irrefl neqI_hb (false, 0) H FAdd)).
Qed.

(* No declared pairs on unit events. *)
Definition unitI (_ _ : unit) : Prop := False.

Lemma unitI_sym : forall a b, unitI a b -> unitI b a.
Proof. intros a b []. Qed.

Lemma unitI_irrefl : forall a, ~ unitI a a.
Proof. intros a []. Qed.

Lemma unitI_hb : forall a b, unitI a b -> ~ (@nohb unit) a b.
Proof. intros a b []. Qed.

Lemma unit_comm_i : forall {S : Type} (step : unit -> S -> S) s0,
  CommI step (fun _ => True) nohb unitI s0.
Proof. intros S step s0 p a b _ _ []. Qed.

(* The capped increment: CommI holds, the idempotence clause fails at the reachable state 0, and
   at-least-once delivery diverges: the idempotence clause is needed. *)
Theorem inc_declared_fails :
  CommI inc_step (fun _ => True) nohb unitI 0 /\
  ~ IdemAt inc_step (fun _ => True) nohb 0 tt /\
  ~ DALOConv inc_step (fun _ => True) nohb unitI 0 /\
  ~ SafeI unit_dec inc_step (fun _ => True) nohb unitI 0 tt.
Proof.
  split; [apply unit_comm_i |]. split; [| split].
  - intro H. specialize (H [] (Forall_True _) (proj2 (causal_nohb _) (nodup1 tt))). discriminate H.
  - intro H. rewrite (dalo_exact unit_dec inc_step (fun _ => True) nohb unitI nohb_irrefl
                        unitI_sym unitI_irrefl unitI_hb 0) in H.
    destruct H as [_ H]. specialize (H tt [] (Forall_True _) (proj2 (causal_nohb _) (nodup1 tt))).
    discriminate H.
  - apply (dalo_notidem_needs_dedup_once unit_dec inc_step (fun _ => True) nohb unitI 0 tt []);
      [constructor; [exact Logic.I | constructor] | exact (proj2 (causal_nohb _) (nodup1 tt)) | discriminate].
Qed.

(* An event NotIdempotent lists (its witness, state 2, is unreachable from 0) is safe and every
   at-least-once delivery converges: NotIdempotent over-reports without reachability. *)
Theorem jmp_declared_unreachable :
  NotIdempotent jmp_step (fun _ => True) tt /\
  DALOConv jmp_step (fun _ => True) nohb unitI 0 /\
  SafeI unit_dec jmp_step (fun _ => True) nohb unitI 0 tt.
Proof.
  assert (Hidem : forall a, IdemAt jmp_step (fun _ => True) nohb 0 a).
  { intros [] u _ Hc. rewrite (unit_nodup_snoc u (proj1 (causal_nohb _) Hc)). reflexivity. }
  split; [exists 2; split; [exact Logic.I | discriminate] |]. split.
  - apply (proj2 (dalo_exact unit_dec jmp_step (fun _ => True) nohb unitI nohb_irrefl
                    unitI_sym unitI_irrefl unitI_hb 0)).
    split; [apply unit_comm_i | exact Hidem].
  - apply (proj2 (safe_i_iff_idem unit_dec jmp_step (fun _ => True) nohb unitI nohb_irrefl
                    unitI_sym unitI_irrefl unitI_hb 0 tt (unit_comm_i _ _))).
    apply Hidem.
Qed.

(* gsm's checks pass on the flag registry with Add/Remove undeclared: Build holds on the declared
   pairs and NotIdempotent lists nothing, so every ALOI delivery converges (dalo_gsm_build). *)
Theorem fl_gsm_build :
  BuildI fl_step (fun _ => True) fl_I (fun _ => True) /\
  (forall a s, fl_step a (fl_step a s) = fl_step a s) /\
  DALOConv fl_step (fun _ => True) nohb fl_I (false, 0).
Proof.
  assert (HB : BuildI fl_step (fun _ => True) fl_I (fun _ => True))
    by (intros a b s _ _ Hab _; exact (fl_I_comm a b s Hab)).
  split; [exact HB |]. split; [intros a s; exact (fl_idem a s Logic.I) |].
  exact (dalo_gsm_build fev_dec fl_step (fun _ => True) nohb fl_I nohb_irrefl fl_I_sym fl_I_irrefl
           fl_I_hb (fun _ => True) (false, 0) HB (fun _ _ _ => Logic.I)
           (fun a _ s _ => fl_idem a s Logic.I)).
Qed.

(* Unordered retries, non-vacuity: the clamped max-register with every distinct pair declared
   satisfies CommI and AbsorbR, so DALOConvR (and hence DALOConv) holds from every start. *)
Theorem mx_declared_r : forall s0,
  CommI mx_step (fun _ => True) nohb neqI s0 /\
  (forall a, AbsorbR mx_step (fun _ => True) nohb s0 a) /\
  DALOConvR Nat.eq_dec mx_step (fun _ => True) nohb neqI s0 /\
  DALOConv mx_step (fun _ => True) nohb neqI s0.
Proof.
  intros s0.
  assert (HC : CommI mx_step (fun _ => True) nohb neqI s0).
  { intros p a b _ _ _. symmetry. exact (mx_comm a b _ Logic.I). }
  assert (HA : forall a, AbsorbR mx_step (fun _ => True) nohb s0 a).
  { intros a w _ Hc Ha.
    pose proof (proj1 (alo_exact_absorb Nat.eq_dec mx_step (fun _ => True) s0)
                  (proj1 (mx_alo_exact s0))) as [_ H].
    exact (H a w (Forall_True _) (proj1 (causal_nohb w) Hc) Ha). }
  assert (HR : DALOConvR Nat.eq_dec mx_step (fun _ => True) nohb neqI s0)
    by exact (proj2 (dalo_r_exact Nat.eq_dec mx_step (fun _ => True) nohb neqI nohb_irrefl
                       neqI_sym neqI_irrefl neqI_hb s0) (conj HC HA)).
  split; [exact HC |]. split; [exact HA |]. split; [exact HR |].
  exact (dalo_r_implies Nat.eq_dec mx_step (fun _ => True) nohb neqI s0 HR).
Qed.
