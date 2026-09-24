(* Chaotic (asynchronous) iteration convergence, mechanized.

   The federated monotone-cycles theorem's second half: not only does the
   federated repair operator have a least fixed point (Federation.v), but every
   FAIR ASYNCHRONOUS schedule of component updates from bottom converges to it,
   regardless of order. That is the classical convergence of chaotic iteration
   (Cousot 1977) and it is what "converges regardless of application order" means
   for a distributed system with no global clock.

   Rather than model infinite fair schedules, we reframe it constructively. A
   chaotic step updates one component with the operator's current value; a step is
   PRODUCTIVE when it changes the state. Below the least fixed point a monotone
   update only moves up, so productive steps strictly increase a rank and there
   are finitely many: the productive-step relation is terminating, and a state
   with no productive step (every component already at its updated value) is a
   fixed point of the whole operator, hence the least fixed point. So from bottom,
   ANY sequence of productive updates reaches the SAME least fixed point: that is
   order-independent convergence. Axiom-free; checked with Rocq 9.3. *)

Require Import NC.Newman.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Wellfounded.Inverse_Image.
From Coq Require Import Lia.

Section Chaotic.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_refl    : forall x, le x x.
  Hypothesis le_trans   : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.

  Variable F : L -> L.               (* the federated repair operator *)
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  (* A rank giving the lattice finite height: strictly increasing on strict order.
     (A finite lattice has one; this is the "ascending chain stabilizes" content.) *)
  Variable rank : L -> nat.
  Hypothesis rank_strict : forall x y, le x y -> x <> y -> rank x < rank y.

  Lemma rank_mono : forall x y, le x y -> rank x <= rank y.
  Proof.
    intros x y H. destruct (Nat.eq_dec (rank x) (rank y)) as [E | NE]; [lia|].
    assert (x <> y) by (intro; subst; lia).
    apply Nat.lt_le_incl. apply rank_strict; assumption.
  Qed.

  (* The least fixed point (from Federation.v's development; taken here as given). *)
  Variable lfp : L.
  Hypothesis lfp_fixed : F lfp = lfp.
  Hypothesis lfp_least : forall x, F x = x -> le lfp x.

  (* Component updates: I indexes the components, update i is "apply F to
     component i". The defining properties of a component decomposition of F. *)
  Variable I : Type.
  Variable update : I -> L -> L.

  (* Deciding, per component, whether an update changes the state (decidable for a
     finite index with decidable state equality). *)
  Variable classicUpdate : forall i x, {update i x = x} + {update i x <> x}.

  Definition sound (x : L) : Prop := le x (F x).           (* below its own image *)

  Hypothesis up_incr  : forall i x, sound x -> le x (update i x).
  Hypothesis up_sound : forall i x, sound x -> sound (update i x).
  Hypothesis up_below : forall i x, le x lfp -> le (update i x) lfp.
  Hypothesis all_fixed : forall x, (forall i, update i x = x) -> F x = x.

  (* A reachable state of the iteration: below its image and below the lfp. Bottom
     is reachable, and productive updates preserve it. *)
  Definition reachable (x : L) : Prop := sound x /\ le x lfp.

  Lemma reachable_bot : reachable bot.
  Proof. split; [apply bot_least | apply bot_least]. Qed.

  (* A productive chaotic step: update some component, changing the state. *)
  Definition step (x y : L) : Prop := exists i, y = update i x /\ x <> y.

  Lemma reachable_step : forall x y, reachable x -> step x y -> reachable y.
  Proof.
    intros x y [Hs Hb] [i [-> _]]. split; [apply up_sound | apply up_below]; assumption.
  Qed.

  Lemma step_rank : forall x y, reachable x -> step x y -> rank x < rank y.
  Proof.
    intros x y [Hs _] [i [-> Hne]]. apply rank_strict; [apply up_incr | exact Hne]; assumption.
  Qed.

  (* Termination: the productive-step relation is strongly normalizing. Measure is
     (rank lfp - rank x); a productive step increases rank, so the measure drops. *)
  Definition gap (x : L) : nat := rank lfp - rank x.

  Lemma step_gap : forall x y, reachable x -> step x y -> gap y < gap x.
  Proof.
    intros x y Hx Hstep. unfold gap.
    assert (Hr : rank x < rank y) by (apply step_rank; assumption).
    assert (Hylfp : le y lfp) by (apply (reachable_step x y); assumption).
    assert (rank y <= rank lfp) by (apply rank_mono; exact Hylfp).
    lia.
  Qed.

  Theorem chaotic_terminates : forall x, reachable x -> SN step x.
  Proof.
    assert (Hwf : well_founded (fun a b => gap a < gap b)) by
      (apply (wf_inverse_image _ _ lt gap lt_wf)).
    intros x Hx. specialize (Hwf x). revert Hx.
    induction Hwf as [x _ IH]. intros Hx.
    constructor. intros y Hstep. apply IH.
    - apply step_gap; assumption.
    - apply (reachable_step x y); assumption.
  Qed.

  (* A normal form of the chaotic relation (no productive step: every component is
     already at its updated value) is the least fixed point. *)
  Lemma normal_is_lfp :
    forall x, reachable x -> normal_form step x -> x = lfp.
  Proof.
    intros x [Hs Hb] Hnf.
    assert (Hfix : forall i, update i x = x).
    { intro i. destruct (classicUpdate i x) as [Heq | Hne]; [exact Heq|].
      exfalso. apply Hnf. exists (update i x). exists i. split; [reflexivity | congruence]. }
    apply le_antisym; [exact Hb | apply lfp_least, all_fixed, Hfix].
  Qed.

  (* To WALK the iteration to the fixed point we must be able to test, at each
     state, whether a productive component exists (a finite fair search). *)
  Hypothesis step_dec :
    forall x, {y | step x y} + {normal_form step x}.

  Theorem chaotic_reaches_lfp : forall x, reachable x -> star step x lfp.
  Proof.
    assert (Hwf : well_founded (fun a b => gap a < gap b)) by
      (apply (wf_inverse_image _ _ lt gap lt_wf)).
    intros x Hx. specialize (Hwf x). revert Hx.
    induction Hwf as [x _ IH]. intros Hx.
    destruct (step_dec x) as [[y Hstep] | Hnf].
    - eapply star_step; [exact Hstep|].
      apply IH; [apply step_gap; assumption | apply (reachable_step x y); assumption].
    - assert (x = lfp) by (apply normal_is_lfp; assumption). subst. apply star_refl.
  Qed.

  (* Order-independence, stated two ways: the iteration from bottom reaches the lfp
     (whatever productive steps are taken), and every reachable normal form is the
     lfp (so the destination is schedule-independent). *)
  Corollary chaotic_from_bot : star step bot lfp.
  Proof. apply chaotic_reaches_lfp, reachable_bot. Qed.

  Corollary chaotic_limit_unique :
    forall x y, reachable x -> normal_form step x -> reachable y -> normal_form step y -> x = y.
  Proof.
    intros x y Hx Nx Hy Ny.
    rewrite (normal_is_lfp x Hx Nx). rewrite (normal_is_lfp y Hy Ny). reflexivity.
  Qed.
End Chaotic.

(* ============================================================
   Non-vacuity: a concrete instance discharging every hypothesis. The two-point
   lattice false < true, with the constant-true operator and one component. From
   the bottom (false), the chaotic iteration reaches the least fixed point (true).
   Axiom-free.
   ============================================================ *)

Definition ble (a b : bool) : Prop := implb a b = true.

Lemma ble_antisym : forall x y, ble x y -> ble y x -> x = y.
Proof. destruct x, y; unfold ble; simpl; intros; (reflexivity || discriminate). Qed.

Definition Ftrue (_ : bool) : bool := true.
Lemma ble_bot_least : forall x, ble false x. Proof. destruct x; reflexivity. Qed.

Definition brank (b : bool) : nat := if b then 1 else 0.
Lemma brank_strict : forall x y, ble x y -> x <> y -> brank x < brank y.
Proof. destruct x, y; unfold ble, brank; simpl; intros H Hne; try (exfalso; congruence); lia. Qed.

Lemma ble_lfp_least : forall x, Ftrue x = x -> ble true x.
Proof. unfold Ftrue; intros x H; rewrite <- H; reflexivity. Qed.

Definition bupd (_ : unit) (_ : bool) : bool := true.
Lemma bupd_dec : forall (i : unit) (x : bool), {bupd i x = x} + {bupd i x <> x}.
Proof. intros i x; unfold bupd; destruct x; [left; reflexivity | right; discriminate]. Qed.

Lemma bup_incr : forall i x, sound ble Ftrue x -> ble x (bupd i x).
Proof. intros i x _; unfold bupd, ble; destruct x; reflexivity. Qed.
Lemma bup_sound : forall i x, sound ble Ftrue x -> sound ble Ftrue (bupd i x).
Proof. intros i x _; unfold sound, Ftrue, bupd, ble; reflexivity. Qed.
Lemma bup_below : forall i x, ble x true -> ble (bupd i x) true.
Proof. intros i x _; unfold bupd, ble; reflexivity. Qed.
Lemma ball_fixed : forall x, (forall i, bupd i x = x) -> Ftrue x = x.
Proof. intros x H; unfold Ftrue; exact (H tt). Qed.

Lemma bstep_dec :
  forall x, {y | step unit bupd x y} + {normal_form (step unit bupd) x}.
Proof.
  intro x. destruct x.
  - right. intros [y [i [Hy Hne]]]. unfold bupd in Hy. subst y. apply Hne; reflexivity.
  - left. exists true. exists tt. split; [reflexivity | discriminate].
Qed.

(* The chaotic iteration from bottom provably reaches the least fixed point. *)
Definition bool_chaotic_reaches_lfp : star (step unit bupd) false true :=
  @chaotic_from_bot bool ble ble_antisym Ftrue false ble_bot_least brank brank_strict
    true ble_lfp_least unit bupd bupd_dec bup_incr bup_sound bup_below ball_fixed bstep_dec.
