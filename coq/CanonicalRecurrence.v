(* CanonicalRecurrence.v: layer C of the regime map, settlement dynamics, as fair recurrence on
   a finite state space. Axiom-free. A preregistered experiment (docs/THEORY.md, "Layer C").

   Hypothesis under test: fair convergence is exactly the absence of a bad fair recurrent
   behavior, made concrete as a finite lasso.

   Setting (section Kernel). A state type X with decidable equality, scheduler labels nat with
   the label list js, an asynchronous update u : nat -> X -> X, and infinite schedules
   sg : nat -> nat. The run is DistributedCycles.prs (x_{t+1} = u (sg t) x_t), fairness is
   DistributedCycles.Fair (every step names a label of js, every label of js is named infinitely
   often), exactly as DistributedCycles.v and SignedResolver.v use them. Finiteness (a list xs
   containing every state) is a hypothesis of the sections that need it, not of the definitions.

   Lassos. FairLasso s0 x p q: x is reached from s0 by the js-word p, q is a nonempty js-word that
   returns x to x, and every label of js occurs in q. OnLoop x q y: y is a state the loop visits
   (y = wrun (firstn k q) x, k < length q). BadLasso G s0: a fair lasso from s0 with a loop state
   outside G. This is the classical fair-cycle / Buchi-emptiness characterization (Emerson and Lei
   1986; Clarke, Emerson and Sistla 1986; Vardi and Wolper 1986), not a new result; the experiment
   is whether it compresses this development's settlement results.

   Settlement. EvAlways G sg s0: from some step on, the run stays in G. FairSettles G s0: every
   fair schedule's run is eventually always in G. FairSettlesNN: the same with the conclusion
   double negated (classically equal).

   1. Generic kernel (sections Kernel, Finite).
      - bad_lasso_witness, bad_lasso_refutes (no finiteness): a bad fair lasso is a fair schedule
        whose run leaves G infinitely often, so FairSettles and FairSettlesNN fail.
      - nobad_nn: on a finite X, no bad fair lasso gives FairSettlesNN.
      - nobad_hits: on a finite X, no bad fair lasso gives a visit to G after every time.
      - recurrence_nn_exact: FairSettlesNN G s0 <-> ~ BadLasso G s0 (finite X, G decidable).
      - recurrence_closed_exact: for G closed under the steps, FairSettles G s0 <-> ~ BadLasso.
      - recurrence_classical: with excluded middle as a PREMISE, FairSettles <-> ~ BadLasso.
   2. C1, canonical recurrence. A canonical observation N : X -> C and a target c (decidable
      equality on C). CanonSettles s0 c := FairSettles (fun x => N x = c) s0, BadCanonLasso s0 c
      := BadLasso (fun x => N x = c) s0.
      - C1_nn: CanonSettlesNN s0 c <-> ~ BadCanonLasso s0 c (finite X; axiom-free, exact).
      - C1_closed: when the fiber of c is closed under the steps, CanonSettles <-> ~ BadCanonLasso.
      - C1_classical: (forall P, P \/ ~ P) -> (CanonSettles <-> ~ BadCanonLasso).
      - C1_refutes: BadCanonLasso -> ~ CanonSettles (no finiteness).
   3. C2, raw settlement. Settled x := Stable X u js x (fixed by every label).
      - C2: FairSettles Settled s0 <-> ~ BadLasso Settled s0 (finite X, constructive: Settled is
        closed).
      - C2_loops: FairSettles Settled s0 <-> every loop state of every fair lasso from s0 is the
        loop's base point, and that point is settled (every fair recurrent loop is a singleton
        fixed point).
      - C2_reach: FairSettles Settled s0 <-> every fair run reaches a settled state.
   4. The constructive leak (section LPO). The strong form FairSettles <- ~ BadLasso is not
      provable axiom-free in general: lpo_leak builds a four-state instance with no bad fair
      lasso on which FairSettles implies the limited principle of omniscience for boolean
      sequences. The axiom-free kernel therefore states C1 in the double-negated form, in the
      closed-fiber form, or with excluded middle as a premise; all three are proved.

   5. Bridges (Parts 4 to 8). Each recovery proves that no bad fair lasso exists and reads the
      settlement off the kernel. Part 4 is a shared, regime-independent toolkit: pigeon (a finite
      type repeats along any sequence), infl_loop_fixed (an inflationary loop fixes every label
      it uses), loop_floor (from a sound start below a loop state, the iterates of the loop word
      stabilize below it at a state its labels fix).
      - (a) chaotic_reaches_lfp_lasso: Chaotic.chaotic_reaches_lfp, through ch_nobad (a fair
        loop at a reachable state is a singleton at a normal form; Chaotic.normal_is_lfp names it)
        and chaotic_settles_lasso (fair-schedule settlement at lfp). Added: L listed, labels a
        finite list js with updates outside js inert. Not used: rank, bot, step_dec.
      - (b) signed_settlement_lasso: SignedResolver.signed_settlement's statement. sr_below_nobad
        (below slfp every fair recurrent state is slfp: the bottom run under the loop word
        stabilizes at a fixed point below the loop) and sr_sound_nobad (from a sound start every
        fair loop is a singleton fixed point, C2). Added: Sh listed.
      - (c) signed_fidelity_lasso: signed_fidelity's statement. sr_unique_nobad: the top run
        bounds every fair loop by a fixed point, which is slfp by uniqueness. Added: Sh listed.
      - (d) fairflush_lasso, fairflushR_lasso: DistributedCyclesExact.FairFlushAt and FairFlushR
        are C2 (Sh listed). flip2_fair_lasso: flip2_fair_livelock as the explicit bad fair lasso
        fa -0-> fb -1-> fb -0-> fa, refuting FairFlushR. nonfair_cycle_not_refuting: a bad cycle
        that misses a label (the drop network) leaves C1 and C2 true.
      - (e) copyback_ghost_lasso: SignedResolver.copyback_ghost as a settled singleton loop in the
        wrong canonical fiber: C2 holds from (1, 1), C1 fails for slfp = (0, 0).
   6. Classification (Parts 8 to 10): class_negation_cycle (bad non-singleton fair lasso, bad for
      every target), flip2_fair_lasso (bad fair lasso with one fixed point), copyback_ghost_lasso
      (wrong singleton), class_good_resolver (no bad fair lasso from any start),
      class_multiple_fixed_points (two reachable singleton classes: C2 holds, every target has a
      bad lasso), semantic_oscillation (new: a fair raw oscillation a <-> b with N a = N b, so C2
      fails and C1 holds), and lasso_classification collecting them.
   See coq/docs/recurrence.md for the statements, bridge sizes and leaks. *)

From Coq Require Import List Arith Lia Bool.
Require Import NC.Newman NC.DistributedCycles.
Require NC.Chaotic.
Require Import NC.CohomologyGraph NC.SignedCycles NC.CanonicalExecution NC.DistributedCyclesExact
  NC.SignedResolver.
Import ListNotations.

(* ============================================================================================ *)
(* Part 1. The generic kernel.                                                                  *)
(* ============================================================================================ *)

Section Kernel.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable js : list nat.
  Variable u : nat -> X -> X.

  Definition wrun (w : list nat) (x : X) : X := fold_left (fun x j => u j x) w x.
  Definition Path (w : list nat) : Prop := Forall (fun j => In j js) w.
  Definition seg (sg : nat -> nat) (n k : nat) : list nat := map sg (seq n k).

  Definition FairLasso (s0 x : X) (p q : list nat) : Prop :=
    Path p /\ wrun p s0 = x /\ q <> [] /\ Path q /\ wrun q x = x /\ (forall j, In j js -> In j q).
  Definition OnLoop (x : X) (q : list nat) (y : X) : Prop :=
    exists k, k < length q /\ wrun (firstn k q) x = y.
  Definition BadLasso (G : X -> Prop) (s0 : X) : Prop :=
    exists x p q y, FairLasso s0 x p q /\ OnLoop x q y /\ ~ G y.

  Definition EvAlways (G : X -> Prop) (sg : nat -> nat) (s0 : X) : Prop :=
    exists N, forall n, N <= n -> G (prs X u sg n s0).
  Definition FairSettles (G : X -> Prop) (s0 : X) : Prop :=
    forall sg, Fair js sg -> EvAlways G sg s0.
  Definition FairSettlesNN (G : X -> Prop) (s0 : X) : Prop :=
    forall sg, Fair js sg -> ~ ~ EvAlways G sg s0.
  Definition Closed (G : X -> Prop) : Prop := forall j x, In j js -> G x -> G (u j x).
  Definition PDec (G : X -> Prop) : Prop := forall x, G x \/ ~ G x.

  (* ----- words and runs ----- *)

  Lemma wrun_app : forall p q x, wrun (p ++ q) x = wrun q (wrun p x).
  Proof. intros. unfold wrun. apply fold_left_app. Qed.

  Lemma seg_len : forall sg n k, length (seg sg n k) = k.
  Proof. intros. unfold seg. rewrite map_length. apply seq_length. Qed.

  Lemma prs_seg : forall sg s0 n k, prs X u sg (n + k) s0 = wrun (seg sg n k) (prs X u sg n s0).
  Proof.
    intros sg s0 n k. induction k as [| k IH]; [rewrite Nat.add_0_r; reflexivity |].
    rewrite Nat.add_succ_r. cbn [prs]. rewrite IH. unfold seg. rewrite seq_S, map_app, wrun_app.
    reflexivity.
  Qed.

  Lemma firstn_seg : forall sg k n m, k <= m -> firstn k (seg sg n m) = seg sg n k.
  Proof.
    intros sg k. induction k as [| k IH]; intros n m Hk; [reflexivity |].
    destruct m as [| m]; [lia |]. unfold seg in *. cbn [seq map firstn]. f_equal. apply IH. lia.
  Qed.

  Lemma seg_path : forall sg, Fair js sg -> forall n k, Path (seg sg n k).
  Proof.
    intros sg [Hin _] n k. apply Forall_forall. intros j Hj. unfold seg in Hj.
    apply in_map_iff in Hj. destruct Hj as [i [<- _]]. apply Hin.
  Qed.

  (* Every window of a fair schedule can be closed so that it names every label. *)
  Lemma fair_window : forall sg, Fair js sg -> forall n, exists m, n < m /\
    forall j, In j js -> exists i, n <= i < m /\ sg i = j.
  Proof.
    intros sg [_ Hinf] n.
    assert (H : forall l, incl l js -> exists m, n < m /\ forall j, In j l -> exists i, n <= i < m /\ sg i = j).
    { intros l. induction l as [| a l IH]; intros Hl.
      - exists (S n). split; [lia | intros j []].
      - destruct IH as [m1 [Hm1 H1]]; [intros x Hx; apply Hl; right; exact Hx |].
        destruct (Hinf a n (Hl a (or_introl eq_refl))) as [m0 [Hm0 E0]].
        exists (Nat.max m1 (S m0)). split; [lia |]. intros j [<- | Hj].
        + exists m0. split; [lia | exact E0].
        + destruct (H1 j Hj) as [i [Hi Ei]]. exists i. split; [lia | exact Ei]. }
    apply H. intros x Hx. exact Hx.
  Qed.

  Lemma window_in_seg : forall sg n m, (forall j, In j js -> exists i, n <= i < m /\ sg i = j) ->
    forall m', m <= m' -> forall j, In j js -> In j (seg sg n (m' - n)).
  Proof.
    intros sg n m H m' Hm j Hj. destruct (H j Hj) as [i [Hi <-]]. unfold seg.
    apply in_map. apply in_seq. lia.
  Qed.

  (* A run segment that returns to its start and names every label is a fair lasso. *)
  Lemma seg_lasso : forall sg s0 n m, Fair js sg -> n < m ->
    prs X u sg m s0 = prs X u sg n s0 ->
    (forall j, In j js -> In j (seg sg n (m - n))) ->
    FairLasso s0 (prs X u sg n s0) (seg sg 0 n) (seg sg n (m - n)) /\
    forall k, k < m - n -> OnLoop (prs X u sg n s0) (seg sg n (m - n)) (prs X u sg (n + k) s0).
  Proof.
    intros sg s0 n m Hf Hnm Em Hall. split.
    - split; [apply seg_path; exact Hf |]. split; [symmetry; exact (prs_seg sg s0 0 n) |].
      split; [intro E; pose proof (seg_len sg n (m - n)) as L; rewrite E in L; simpl in L; lia |].
      split; [apply seg_path; exact Hf |]. split; [| exact Hall].
      rewrite <- prs_seg. replace (n + (m - n)) with m by lia. exact Em.
    - intros k Hk. exists k. split; [rewrite seg_len; exact Hk |].
      rewrite firstn_seg by lia. symmetry. apply prs_seg.
  Qed.

  (* ----- the lasso schedule: p, then q forever ----- *)

  Fixpoint qpow (q : list nat) (k : nat) : list nat :=
    match k with 0 => [] | S k => q ++ qpow q k end.
  Definition lsg (p q : list nat) (n : nat) : nat := nth n (p ++ qpow q (S n)) 0.

  Lemma qpow_add : forall q a b, qpow q (a + b) = qpow q a ++ qpow q b.
  Proof. intros q a b. induction a as [| a IH]; [reflexivity |]. simpl. rewrite IH, app_assoc. reflexivity. Qed.

  Lemma qpow_len : forall q k, length (qpow q k) = k * length q.
  Proof. intros q k. induction k as [| k IH]; [reflexivity |]. simpl. rewrite app_length, IH. lia. Qed.

  Lemma qpow_snoc : forall q k, qpow q (S k) = qpow q k ++ q.
  Proof. intros q k. replace (S k) with (k + 1) by lia. rewrite qpow_add. simpl. rewrite app_nil_r. reflexivity. Qed.

  Lemma qpow_in : forall q k j, In j (qpow q k) -> In j q.
  Proof.
    intros q k j. induction k as [| k IH]; [intros [] |]. simpl. intro H.
    apply in_app_or in H. destruct H as [H | H]; [exact H | exact (IH H)].
  Qed.

  Lemma wrun_qpow : forall q x, wrun q x = x -> forall k, wrun (qpow q k) x = x.
  Proof. intros q x H k. induction k as [| k IH]; [reflexivity |]. simpl. rewrite wrun_app, H. exact IH. Qed.

  Lemma lsg_nth : forall p q, q <> [] -> forall i a, i < length (p ++ qpow q a) ->
    lsg p q i = nth i (p ++ qpow q a) 0.
  Proof.
    intros p q Hq i a Hi. unfold lsg.
    assert (Lq : 1 <= length q) by (destruct q; [congruence | simpl; lia]).
    destruct (Nat.le_gt_cases (S i) a) as [Le | Gt].
    - replace a with (S i + (a - S i)) by lia. rewrite qpow_add, app_assoc. symmetry. apply app_nth1.
      rewrite app_length, qpow_len. nia.
    - replace (S i) with (a + (S i - a)) by lia. rewrite qpow_add, app_assoc. apply app_nth1. exact Hi.
  Qed.

  Lemma firstn_snoc : forall (L : list nat) n, n < length L -> firstn (S n) L = firstn n L ++ [nth n L 0].
  Proof.
    induction L as [| a L IH]; intros n Hn; [simpl in Hn; lia |].
    destruct n as [| n]; [reflexivity |]. simpl in Hn. change (a :: firstn (S n) L = (a :: firstn n L) ++ [nth n L 0]). rewrite IH by lia. reflexivity.
  Qed.

  Lemma firstn_app_len : forall (a b : list nat) k, firstn (length a + k) (a ++ b) = a ++ firstn k b.
  Proof. induction a as [| x a IH]; intros b k; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

  Lemma prs_list : forall sg (L : list nat) x n, n <= length L -> (forall i, i < n -> sg i = nth i L 0) ->
    prs X u sg n x = wrun (firstn n L) x.
  Proof.
    intros sg L x n. induction n as [| n IH]; intros Hn H; [reflexivity |].
    cbn [prs]. rewrite IH by (intros; try apply H; lia). rewrite firstn_snoc by lia.
    rewrite wrun_app, (H n) by lia. reflexivity.
  Qed.

  Lemma nth_lasso : forall p q N k, k < length q ->
    nth (length p + N * length q + k) (p ++ qpow q (S N)) 0 = nth k q 0.
  Proof.
    intros p q N k Hk. rewrite qpow_snoc, app_assoc. rewrite app_nth2 by (rewrite app_length, qpow_len; lia).
    rewrite app_length, qpow_len. f_equal. lia.
  Qed.

  Lemma lasso_fair : forall p q, Path p -> Path q -> q <> [] -> (forall j, In j js -> In j q) ->
    Fair js (lsg p q).
  Proof.
    intros p q Hp Hq Hne Hall. split.
    - intro n. unfold lsg. assert (L : n < length (p ++ qpow q (S n))).
      { rewrite app_length, qpow_len. destruct q; [congruence | simpl; nia]. }
      pose proof (nth_In _ 0 L) as H. apply in_app_or in H. destruct H as [H | H].
      + exact (proj1 (Forall_forall _ p) Hp _ H).
      + exact (proj1 (Forall_forall _ q) Hq _ (qpow_in q _ _ H)).
    - intros j n Hj. destruct (In_nth q j 0 (Hall j Hj)) as [k [Hk Ek]].
      exists (length p + n * length q + k). split; [destruct q; [congruence | simpl; nia] |].
      rewrite (lsg_nth p q Hne _ (S n)) by (rewrite app_length, qpow_len; simpl; lia).
      rewrite nth_lasso by exact Hk. exact Ek.
  Qed.

  Lemma lasso_visits : forall s0 x p q y, FairLasso s0 x p q -> OnLoop x q y ->
    forall N, exists n, N <= n /\ prs X u (lsg p q) n s0 = y.
  Proof.
    intros s0 x p q y (Hp & Ep & Hne & Hq & Eq & Hall) (k & Hk & Ek) N.
    exists (length p + N * length q + k). split; [destruct q; [congruence | simpl; nia] |].
    rewrite (prs_list (lsg p q) (p ++ qpow q (S N))).
    - rewrite qpow_snoc, <- Nat.add_assoc, firstn_app_len.
      replace (N * length q) with (length (qpow q N)) by apply qpow_len.
      rewrite firstn_app_len, !wrun_app, Ep, wrun_qpow by exact Eq. exact Ek.
    - rewrite app_length, qpow_len. simpl. lia.
    - intros i Hi. apply lsg_nth; [exact Hne |]. rewrite app_length, qpow_len. simpl. lia.
  Qed.

  (* ----- the refutation direction (no finiteness) ----- *)

  Theorem bad_lasso_witness : forall G s0, BadLasso G s0 ->
    exists sg, Fair js sg /\ forall N, exists n, N <= n /\ ~ G (prs X u sg n s0).
  Proof.
    intros G s0 (x & p & q & y & HL & Hy & Ny). exists (lsg p q).
    destruct HL as (Hp & Ep & Hne & Hq & Eq & Hall) eqn:HL'. split; [apply lasso_fair; assumption |].
    intro N. destruct (lasso_visits s0 x p q y HL Hy N) as [n [Hn En]]. exists n. split; [exact Hn |].
    rewrite En. exact Ny.
  Qed.

  Theorem bad_lasso_refutes : forall G s0, BadLasso G s0 -> ~ FairSettles G s0 /\ ~ FairSettlesNN G s0.
  Proof.
    intros G s0 HB. destruct (bad_lasso_witness G s0 HB) as [sg [Hf Hinf]].
    assert (K : ~ EvAlways G sg s0).
    { intros [N HN]. destruct (Hinf N) as [n [Hn Gn]]. exact (Gn (HN n Hn)). }
    split; [intro H; exact (K (H sg Hf)) | intro H; exact (H sg Hf K)].
  Qed.
End Kernel.

(* ----- the canonical layer and raw settlement (definitions; no finiteness) ----- *)

Section Canon.
  Variable X : Type.
  Variable js : list nat.
  Variable u : nat -> X -> X.
  Variable C : Type.
  Variable N : X -> C.

  Definition Fiber (c : C) (x : X) : Prop := N x = c.
  Definition CanonSettles (s0 : X) (c : C) : Prop := FairSettles X js u (Fiber c) s0.
  Definition CanonSettlesNN (s0 : X) (c : C) : Prop := FairSettlesNN X js u (Fiber c) s0.
  Definition BadCanonLasso (s0 : X) (c : C) : Prop := BadLasso X js u (Fiber c) s0.

  Theorem C1_refutes : forall s0 c, BadCanonLasso s0 c -> ~ CanonSettles s0 c /\ ~ CanonSettlesNN s0 c.
  Proof. intros s0 c. apply bad_lasso_refutes. Qed.

  Lemma closed_stays : forall G, Closed X js u G -> forall sg, Fair js sg -> forall s0 n,
    G (prs X u sg n s0) -> forall m, n <= m -> G (prs X u sg m s0).
  Proof.
    intros G Hc sg [Hin _] s0 n Hn m Hm. induction Hm as [| m _ IH]; [exact Hn |].
    cbn [prs]. apply Hc; [apply Hin | exact IH].
  Qed.

  Lemma settled_closed : Closed X js u (Stable X u js).
  Proof. intros j x Hj Hx. rewrite (Hx j Hj). exact Hx. Qed.

  Lemma path_firstn : forall k w, Path js w -> Path js (firstn k w).
  Proof.
    induction k as [| k IH]; intros w Hw; [constructor |]. destruct w as [| a w]; [constructor |].
    inversion Hw; subst. simpl. constructor; [assumption | apply IH; assumption].
  Qed.

  Lemma settled_wrun : forall x, Stable X u js x -> forall w, Path js w -> wrun X u w x = x.
  Proof.
    intros x Hx w Hw. induction Hw as [| a w Ha _ IH]; [reflexivity |].
    simpl. rewrite (Hx a Ha). exact IH.
  Qed.

  (* C2, the reach form (no finiteness): eventually always settled iff some settled state is
     reached, since settled states are absorbing. *)
  Theorem C2_reach : forall s0, FairSettles X js u (Stable X u js) s0 <->
    (forall sg, Fair js sg -> exists n, Stable X u js (prs X u sg n s0)).
  Proof.
    intros s0. split.
    - intros H sg Hf. destruct (H sg Hf) as [M HM]. exists M. apply HM. lia.
    - intros H sg Hf. destruct (H sg Hf) as [n Hn]. exists n. intros m Hm.
      exact (closed_stays _ settled_closed sg Hf s0 n Hn m Hm).
  Qed.
End Canon.

(* ============================================================================================ *)
(* Part 2. The finite kernel: C1 and C2.                                                        *)
(* ============================================================================================ *)

Section Finite.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable xs : list X.
  Hypothesis xs_full : forall x, In x xs.
  Variable js : list nat.
  Variable u : nat -> X -> X.

  Section Target.
    Variable G : X -> Prop.
    Hypothesis Gdec : PDec X G.
    Variable s0 : X.
    Hypothesis nobad : ~ BadLasso X js u G s0.

    (* The base point of a run segment that is a fair loop is in G. *)
    Lemma loop_good : forall sg n m, Fair js sg -> n < m -> prs X u sg m s0 = prs X u sg n s0 ->
      (forall j, In j js -> exists i, n <= i < m /\ sg i = j) -> G (prs X u sg n s0).
    Proof.
      intros sg n m Hf Hnm Em Hw.
      destruct (seg_lasso X js u sg s0 n m Hf Hnm Em (window_in_seg js sg n m Hw m (le_n m))) as [HL HO].
      destruct (Gdec (prs X u sg n s0)) as [Gy | Ny]; [exact Gy |]. exfalso. apply nobad.
      exists (prs X u sg n s0), (seg sg 0 n), (seg sg n (m - n)), (prs X u sg n s0).
      split; [exact HL | split; [| exact Ny]].
      pose proof (HO 0 ltac:(lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
    Qed.

    (* A state outside G is visited only finitely often (double negated). *)
    Lemma state_finitely_often : forall sg, Fair js sg -> forall y, ~ G y ->
      ~ ~ exists B, forall n, B <= n -> prs X u sg n s0 <> y.
    Proof.
      intros sg Hf y Ny H.
      assert (H1 : ~ ~ exists n0, prs X u sg n0 s0 = y).
      { intro H2. apply H. exists 0. intros n _ E. apply H2. exists n. exact E. }
      apply H1. intros [n0 E0].
      destruct (fair_window js sg Hf n0) as [m [Hm Hw]].
      assert (H3 : ~ ~ exists n1, m <= n1 /\ prs X u sg n1 s0 = y).
      { intro H4. apply H. exists m. intros n Hn E. apply H4. exists n. split; assumption. }
      apply H3. intros [n1 [Hn1 E1]]. apply Ny. rewrite <- E0.
      apply (loop_good sg n0 n1 Hf ltac:(lia) ltac:(congruence)).
      intros j Hj. destruct (Hw j Hj) as [i [Hi Ei]]. exists i. split; [lia | exact Ei].
    Qed.

    Lemma nn_bound : forall sg, Fair js sg -> forall l : list X,
      ~ ~ exists B, forall y, In y l -> ~ G y -> forall n, B <= n -> prs X u sg n s0 <> y.
    Proof.
      intros sg Hf l. induction l as [| y l IH].
      - intro H. apply H. exists 0. intros y [].
      - intro H. apply IH. intros [B1 H1]. destruct (Gdec y) as [Gy | Ny].
        + apply H. exists B1. intros z [<- | Hz] Nz; [contradiction |]. exact (H1 z Hz Nz).
        + apply (state_finitely_often sg Hf y Ny). intros [B2 H2]. apply H. exists (Nat.max B1 B2).
          intros z [<- | Hz] Nz n Hn; [apply H2; lia | apply (H1 z Hz Nz); lia].
    Qed.

    Theorem nobad_nn : FairSettlesNN X js u G s0.
    Proof.
      intros sg Hf H. apply (nn_bound sg Hf xs). intros [B HB]. apply H. exists B. intros n Hn.
      destruct (Gdec (prs X u sg n s0)) as [Gn | Nn]; [exact Gn |].
      exfalso. exact (HB _ (xs_full _) Nn n Hn eq_refl).
    Qed.

    (* The positive direction by pigeonhole on window boundaries. *)
    Definition Inv (sg : nat -> nat) (n0 : nat) (W : list X) (c : nat) : Prop :=
      forall x, In x W -> exists t, n0 <= t /\ t < c /\ prs X u sg t s0 = x /\
        forall j, In j js -> exists i, t <= i < c /\ sg i = j.

    Lemma hits_aux : forall sg, Fair js sg -> forall n0 d W c, length xs <= length W + d -> NoDup W ->
      n0 <= c -> Inv sg n0 W c -> exists n, n0 <= n /\ G (prs X u sg n s0).
    Proof.
      intros sg Hf n0 d. induction d as [| d IH]; intros W c Hl Hnd Hc Hinv;
        destruct (in_dec X_eq_dec (prs X u sg c s0) W) as [Hin | Hout].
      - destruct (Hinv _ Hin) as (t & Ht & Htc & Et & Hw). exists t. split; [exact Ht |].
        apply (loop_good sg t c Hf Htc ltac:(congruence) Hw).
      - exfalso. assert (L : length (prs X u sg c s0 :: W) <= length xs).
        { apply NoDup_incl_length; [constructor; assumption | intros x _; apply xs_full]. }
        simpl in L. lia.
      - destruct (Hinv _ Hin) as (t & Ht & Htc & Et & Hw). exists t. split; [exact Ht |].
        apply (loop_good sg t c Hf Htc ltac:(congruence) Hw).
      - destruct (fair_window js sg Hf c) as [m [Hm Hw]].
        apply (IH (prs X u sg c s0 :: W) m); [simpl; lia | constructor; assumption | lia |].
        intros x [<- | Hx].
        + exists c. split; [exact Hc | split; [exact Hm | split; [reflexivity | exact Hw]]].
        + destruct (Hinv x Hx) as (t & Ht & Htc & Et & Hw'). exists t.
          split; [exact Ht | split; [lia | split; [exact Et |]]].
          intros j Hj. destruct (Hw' j Hj) as [i [Hi Ei]]. exists i. split; [lia | exact Ei].
    Qed.

    Theorem nobad_hits : forall sg, Fair js sg -> forall n0, exists n, n0 <= n /\ G (prs X u sg n s0).
    Proof.
      intros sg Hf n0. apply (hits_aux sg Hf n0 (length xs) [] n0); [simpl; lia | constructor | lia |].
      intros x [].
    Qed.
  End Target.

  Theorem recurrence_nn_exact : forall G s0, PDec X G ->
    (FairSettlesNN X js u G s0 <-> ~ BadLasso X js u G s0).
  Proof.
    intros G s0 Hd. split; [intros H B; exact (proj2 (bad_lasso_refutes X js u G s0 B) H) |].
    apply nobad_nn. exact Hd.
  Qed.

  Theorem recurrence_closed_exact : forall G s0, PDec X G -> Closed X js u G ->
    (FairSettles X js u G s0 <-> ~ BadLasso X js u G s0).
  Proof.
    intros G s0 Hd Hc. split; [intros H B; exact (proj1 (bad_lasso_refutes X js u G s0 B) H) |].
    intros Hn sg Hf. destruct (nobad_hits G Hd s0 Hn sg Hf 0) as [n [_ Gn]].
    exists n. intros m Hm. exact (closed_stays X js u G Hc sg Hf s0 n Gn m Hm).
  Qed.

  Theorem recurrence_classical : (forall P : Prop, P \/ ~ P) -> forall G s0,
    (FairSettles X js u G s0 <-> ~ BadLasso X js u G s0).
  Proof.
    intros XM G s0. split; [intros H B; exact (proj1 (bad_lasso_refutes X js u G s0 B) H) |].
    intros Hn sg Hf. destruct (XM (EvAlways X u G sg s0)) as [E | E]; [exact E |].
    exfalso. exact (nobad_nn G (fun x => XM (G x)) s0 Hn sg Hf E).
  Qed.
End Finite.

(* ----- C1 and C2 ----- *)

Section C1C2.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable xs : list X.
  Hypothesis xs_full : forall x, In x xs.
  Variable js : list nat.
  Variable u : nat -> X -> X.
  Variable C : Type.
  Variable C_eq_dec : forall a b : C, {a = b} + {a <> b}.
  Variable N : X -> C.

  Lemma fiber_dec : forall c, PDec X (Fiber X C N c).
  Proof. intros c x. unfold Fiber. destruct (C_eq_dec (N x) c); [left | right]; assumption. Qed.

  (* C1, axiom-free and exact: every fair run is (double negated) eventually always in the fiber
     of c iff no fair lasso from s0 has a loop state outside it. *)
  Theorem C1_nn : forall s0 c, CanonSettlesNN X js u C N s0 c <-> ~ BadCanonLasso X js u C N s0 c.
  Proof. intros s0 c. apply (recurrence_nn_exact X xs xs_full). apply fiber_dec. Qed.

  (* C1 in the strong (eventually always) form, for a fiber closed under the steps. *)
  Theorem C1_closed : forall s0 c, Closed X js u (Fiber X C N c) ->
    (CanonSettles X js u C N s0 c <-> ~ BadCanonLasso X js u C N s0 c).
  Proof. intros s0 c Hc. apply (recurrence_closed_exact X X_eq_dec xs xs_full); [apply fiber_dec | exact Hc]. Qed.

  (* C1 in the strong form with excluded middle as a premise (not an axiom). *)
  Theorem C1_classical : (forall P : Prop, P \/ ~ P) -> forall s0 c,
    (CanonSettles X js u C N s0 c <-> ~ BadCanonLasso X js u C N s0 c).
  Proof. intros XM s0 c. apply (recurrence_classical X xs xs_full js u XM). Qed.

  Lemma settled_dec : PDec X (Stable X u js).
  Proof.
    intro x. assert (H : forall l, (forall j, In j l -> u j x = x) \/ ~ (forall j, In j l -> u j x = x)).
    { induction l as [| a l [IH | IH]].
      - left. intros j [].
      - destruct (X_eq_dec (u a x) x) as [E | E].
        + left. intros j [<- | Hj]; [exact E | exact (IH j Hj)].
        + right. intro H. exact (E (H a (or_introl eq_refl))).
      - right. intro H. apply IH. intros j Hj. exact (H j (or_intror Hj)). }
    exact (H js).
  Qed.

  (* C2, raw settlement: every fair run eventually stays settled iff no fair lasso from s0 has an
     unsettled loop state. *)
  Theorem C2 : forall s0, FairSettles X js u (Stable X u js) s0 <-> ~ BadLasso X js u (Stable X u js) s0.
  Proof.
    intros s0. apply (recurrence_closed_exact X X_eq_dec xs xs_full); [exact settled_dec |].
    apply settled_closed.
  Qed.

  Lemma onloop_base : forall x q, q <> [] -> OnLoop X u x q x.
  Proof. intros x q Hq. exists 0. split; [destruct q; [congruence | simpl; lia] | reflexivity]. Qed.

  (* C2, loop form: every fair recurrent loop is a singleton fixed point. *)
  Theorem C2_loops : forall s0, FairSettles X js u (Stable X u js) s0 <->
    (forall x p q, FairLasso X js u s0 x p q -> forall y, OnLoop X u x q y -> y = x /\ Stable X u js x).
  Proof.
    intros s0. rewrite C2. split.
    - intros H x p q HL y Hy.
      assert (Sx : Stable X u js x).
      { destruct (settled_dec x) as [S | NS]; [exact S |]. exfalso. apply H.
        exists x, p, q, x. destruct HL as (A & B & Hq & D & E & F) eqn:HL'.
        split; [exact HL | split; [apply onloop_base; exact Hq | exact NS]]. }
      split; [| exact Sx]. destruct Hy as [k [_ <-]]. apply (settled_wrun X js u); [exact Sx |].
      apply path_firstn. destruct HL as (_ & _ & _ & Hq & _). exact Hq.
    - intros H (x & p & q & y & HL & Hy & Ny). destruct (H x p q HL y Hy) as [-> Sx]. exact (Ny Sx).
  Qed.
End C1C2.

(* ============================================================================================ *)
(* Part 3. The constructive leak: the strong form of C1 implies LPO on a four-state instance.   *)
(* States g0, h, b, g1. Label 0: g0 -> h -> b; label 1: h -> g0; b -> g1 under every label; g1   *)
(* and g0 (under 1) are fixed. G = "not b". No fair lasso visits b (b leads only to g1), so no  *)
(* bad fair lasso exists, yet whether a fair run ever visits b depends on whether the schedule  *)
(* ever names 0 twice in a row, which a boolean sequence can encode.                            *)
(* ============================================================================================ *)

Inductive L4 : Type := lg0 | lh | lb | lg1.
Definition l4_eq_dec : forall x y : L4, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition l4u (j : nat) (x : L4) : L4 :=
  match x, j with
  | lg0, 0 => lh | lg0, _ => lg0
  | lh, 0 => lb | lh, _ => lg0
  | lb, _ => lg1 | lg1, _ => lg1
  end.
Definition l4js : list nat := [0; 1].
Definition notb (x : L4) : Prop := x <> lb.

Lemma l4_full : forall x, In x [lg0; lh; lb; lg1].
Proof. intros []; simpl; tauto. Qed.

Lemma l4_g1 : forall w, wrun L4 l4u w lg1 = lg1.
Proof. induction w as [| a w IH]; [reflexivity |]. exact IH. Qed.

Lemma l4_nobad : ~ BadLasso L4 l4js l4u notb lg0.
Proof.
  intros (x & p & q & y & (_ & _ & _ & _ & Eq & _) & (k & Hk & Ek) & Ny).
  unfold notb in Ny. assert (Ey : y = lb) by (destruct y; try reflexivity; exfalso; apply Ny; discriminate). rewrite Ey in Ek.
  assert (Ex : x = lg1).
  { rewrite <- Eq, <- (firstn_skipn k q), wrun_app, Ek.
    destruct (skipn k q) as [| a r] eqn:Es.
    - exfalso. pose proof (firstn_skipn k q) as F. rewrite Es, app_nil_r in F.
      assert (length (firstn k q) <= k) by (clear; revert q; induction k; intros [| ? ?]; simpl; try lia;
        specialize (IHk l); lia).
      rewrite F in H. lia.
    - simpl. apply l4_g1. }
  subst x. rewrite l4_g1 in Ek. discriminate Ek.
Qed.

(* The schedule encoding a boolean sequence a: blocks 0, 1, (if a k then 0 else 1). *)
Fixpoint ph (n : nat) : nat := match n with 0 => 0 | S n => if Nat.eqb (ph n) 2 then 0 else S (ph n) end.
Fixpoint blk (n : nat) : nat := match n with 0 => 0 | S n => if Nat.eqb (ph n) 2 then S (blk n) else blk n end.
Definition asg (a : nat -> bool) (n : nat) : nat :=
  match ph n with 0 => 0 | 1 => 1 | _ => if a (blk n) then 0 else 1 end.

Lemma ph_blk : forall k, ph (3 * k) = 0 /\ blk (3 * k) = k /\ ph (S (3 * k)) = 1 /\
  blk (S (3 * k)) = k /\ ph (S (S (3 * k))) = 2 /\ blk (S (S (3 * k))) = k.
Proof.
  induction k as [| k (P0 & B0 & P1 & B1 & P2 & B2)]; [repeat split; reflexivity |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia.
  assert (ph_S : forall n, ph (S n) = if Nat.eqb (ph n) 2 then 0 else S (ph n)) by reflexivity.
  assert (blk_S : forall n, blk (S n) = if Nat.eqb (ph n) 2 then S (blk n) else blk n) by reflexivity.
  assert (Q0 : ph (S (S (S (3 * k)))) = 0) by (rewrite ph_S, P2; reflexivity).
  assert (C0 : blk (S (S (S (3 * k)))) = S k) by (rewrite blk_S, P2, B2; reflexivity).
  assert (Q1 : ph (S (S (S (S (3 * k))))) = 1) by (rewrite ph_S, Q0; reflexivity).
  assert (C1 : blk (S (S (S (S (3 * k))))) = S k) by (rewrite blk_S, Q0, C0; reflexivity).
  assert (Q2 : ph (S (S (S (S (S (3 * k)))))) = 2) by (rewrite ph_S, Q1; reflexivity).
  assert (C2 : blk (S (S (S (S (S (3 * k)))))) = S k) by (rewrite blk_S, Q1, C1; reflexivity).
  repeat split; assumption.
Qed.

Lemma asg_fair : forall a, Fair l4js (asg a).
Proof.
  intros a. split.
  - intro n. unfold asg. destruct (ph n) as [| [| m]]; simpl; [tauto | tauto |].
    destruct (a (blk n)); simpl; tauto.
  - intros j n [<- | [<- | []]].
    + exists (3 * n). split; [lia |]. unfold asg. rewrite (proj1 (ph_blk n)). reflexivity.
    + exists (S (3 * n)). split; [lia |]. unfold asg. rewrite (proj1 (proj2 (proj2 (ph_blk n)))). reflexivity.
Qed.

Lemma asg_run : forall a k, (forall i, i < k -> a i = false) -> prs L4 l4u (asg a) (3 * k) lg0 = lg0.
Proof.
  intros a k. induction k as [| k IH]; intros H; [reflexivity |].
  replace (3 * S k) with (S (S (S (3 * k)))) by lia. cbn [prs]. rewrite IH by (intros; apply H; lia).
  destruct (ph_blk k) as (P0 & B0 & P1 & B1 & P2 & B2). unfold asg. rewrite P0, P1, P2, B2.
  rewrite (H k) by lia. reflexivity.
Qed.

Lemma asg_hit : forall a k, (forall i, i < k -> a i = false) -> a k = true ->
  prs L4 l4u (asg a) (S (S (S (S (3 * k))))) lg0 = lb.
Proof.
  intros a k H E. cbn [prs]. rewrite asg_run by exact H.
  destruct (ph_blk k) as (P0 & B0 & P1 & B1 & P2 & B2). destruct (ph_blk (S k)) as (Q0 & _).
  replace (3 * S k) with (S (S (S (3 * k)))) in Q0 by lia.
  unfold asg. rewrite P0, P1, P2, B2, Q0, E. reflexivity.
Qed.

Lemma least_true : forall (a : nat -> bool) k, (forall i, i < k -> a i = false) \/
  (exists k', k' < k /\ a k' = true /\ forall i, i < k' -> a i = false).
Proof.
  intros a k. induction k as [| k [IH | IH]].
  - left. intros i Hi. lia.
  - destruct (a k) eqn:E.
    + right. exists k. split; [lia | split; [exact E | exact IH]].
    + left. intros i Hi. destruct (Nat.eq_dec i k) as [-> | Ne]; [exact E | apply IH; lia].
  - right. destruct IH as [k' [Hk' R]]. exists k'. split; [lia | exact R].
Qed.

Lemma notb_dec : PDec L4 notb.
Proof. intros []; unfold notb; [left | left | right | left]; congruence. Qed.

(* The leak, mechanized: no bad fair lasso, the double-negated settlement holds, and the strong
   (eventually always) settlement implies LPO for boolean sequences. *)
Theorem lpo_leak :
  ~ BadLasso L4 l4js l4u notb lg0 /\
  FairSettlesNN L4 l4js l4u notb lg0 /\
  (FairSettles L4 l4js l4u notb lg0 ->
     forall a : nat -> bool, (exists k, a k = true) \/ (forall k, a k = false)).
Proof.
  split; [exact l4_nobad |]. split.
  { exact (proj2 (recurrence_nn_exact L4 [lg0; lh; lb; lg1] l4_full l4js l4u notb lg0 notb_dec)
             l4_nobad). }
  intros H a. destruct (H (asg a) (asg_fair a)) as [B HB].
  destruct (least_true a B) as [Hlow | [k [_ [Ek _]]]]; [| left; exists k; exact Ek].
  right. intro k. destruct (a k) eqn:E; [| reflexivity]. exfalso.
  destruct (least_true a (S k)) as [Hk | [k' [Hk' [Ek' Hb]]]]; [rewrite (Hk k) in E; [discriminate | lia] |].
  assert (Kb : B <= k').
  { destruct (Nat.le_gt_cases B k') as [L | L]; [exact L |]. rewrite (Hlow k' L) in Ek'. discriminate. }
  apply (HB (S (S (S (S (3 * k'))))) ltac:(lia)). apply asg_hit; assumption.
Qed.

(* ============================================================================================ *)
(* Part 4. Shared bridge toolkit: pigeonhole on a finite state type, and inflationary loops.    *)
(* Regime-independent lemmas used by the bridges below; not part of the C1/C2 kernel.           *)
(* ============================================================================================ *)

Section Pigeon.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable xs : list X.
  Hypothesis xs_full : forall x, In x xs.

  Lemma in_remove' : forall (l : list X) x y, In x l -> x <> y -> In x (remove X_eq_dec y l).
  Proof.
    induction l as [| a l IH]; intros x y H N; [destruct H |]. simpl.
    destruct (X_eq_dec y a) as [E | E].
    - subst a. destruct H as [H | H]; [congruence | apply IH; assumption].
    - destruct H as [<- | H]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma remove_len_le : forall (l : list X) y, length (remove X_eq_dec y l) <= length l.
  Proof.
    induction l as [| a l IH]; intros y; [simpl; lia |]. simpl.
    destruct (X_eq_dec y a); simpl; specialize (IH y); lia.
  Qed.

  Lemma remove_len_lt : forall (l : list X) y, In y l -> length (remove X_eq_dec y l) < length l.
  Proof.
    induction l as [| a l IH]; intros y H; [destruct H |]. simpl. destruct (X_eq_dec y a) as [E | E].
    - pose proof (remove_len_le l y). lia.
    - destruct H as [H | H]; [congruence |]. simpl. specialize (IH y H). lia.
  Qed.

  Lemma search0 : forall (f : nat -> X) m,
    (exists k, k < m /\ f (S k) = f 0) \/ (forall k, k < m -> f (S k) <> f 0).
  Proof.
    intros f m. induction m as [| m [IH | IH]].
    - right. intros k Hk. lia.
    - left. destruct IH as [k [Hk E]]. exists k. split; [lia | exact E].
    - destruct (X_eq_dec (f (S m)) (f 0)) as [E | E].
      + left. exists m. split; [lia | exact E].
      + right. intros k Hk. destruct (Nat.eq_dec k m) as [-> | Ne]; [exact E | apply IH; lia].
  Qed.

  Lemma pigeon_aux : forall n (l : list X) (f : nat -> X), length l <= n ->
    (forall i, i <= n -> In (f i) l) -> exists a b, a < b <= n /\ f a = f b.
  Proof.
    induction n as [| n IH]; intros l f Hl Hin.
    - destruct l; [destruct (Hin 0 (le_n 0)) | simpl in Hl; lia].
    - destruct (search0 f (S n)) as [[k [Hk E]] | Hne].
      + exists 0, (S k). split; [lia | symmetry; exact E].
      + destruct (IH (remove X_eq_dec (f 0) l) (fun i => f (S i))) as (a & b & Hab & E).
        * pose proof (remove_len_lt l (f 0) (Hin 0 ltac:(lia))). lia.
        * intros i Hi. apply in_remove'; [apply Hin; lia | apply Hne; lia].
        * exists (S a), (S b). split; [lia | exact E].
  Qed.

  Theorem pigeon : forall f : nat -> X, exists a b, a < b /\ f a = f b.
  Proof.
    intros f. destruct (pigeon_aux (length xs) xs f (le_n _) (fun i _ => xs_full (f i))) as (a & b & H & E).
    exists a, b. split; [lia | exact E].
  Qed.
End Pigeon.

Section Inflationary.
  Variable X : Type.
  Variable le : X -> X -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable u : nat -> X -> X.
  Variable Sd : X -> Prop.
  Hypothesis incr : forall j x, Sd x -> le x (u j x).
  Hypothesis Sd_step : forall j x, Sd x -> Sd (u j x).

  Lemma infl_wrun : forall w x, Sd x -> Sd (wrun X u w x) /\ le x (wrun X u w x).
  Proof.
    induction w as [| a w IH]; intros x Hx; [split; [exact Hx | apply le_refl] |].
    change (wrun X u (a :: w) x) with (wrun X u w (u a x)).
    destruct (IH (u a x) (Sd_step a x Hx)) as [H1 H2].
    split; [exact H1 | eapply le_trans; [apply incr; exact Hx | exact H2]].
  Qed.

  (* An inflationary loop is a fixed point of every label it uses. *)
  Lemma infl_loop_fixed : forall q z, Sd z -> wrun X u q z = z -> forall i, In i q -> u i z = z.
  Proof.
    induction q as [| a q IH]; intros z Hz E i Hi; [destruct Hi |].
    change (wrun X u (a :: q) z) with (wrun X u q (u a z)) in E.
    assert (Ea : u a z = z).
    { apply le_antisym; [| apply incr; exact Hz]. rewrite <- E at 2.
      exact (proj2 (infl_wrun q (u a z) (Sd_step a z Hz))). }
    rewrite Ea in E. destruct Hi as [<- | Hi]; [exact Ea | exact (IH z Hz E i Hi)].
  Qed.

  Hypothesis mono : forall j x y, le x y -> le (u j x) (u j y).

  Lemma mono_wrun : forall w x y, le x y -> le (wrun X u w x) (wrun X u w y).
  Proof.
    induction w as [| a w IH]; intros x y H; [exact H |].
    change (le (wrun X u w (u a x)) (wrun X u w (u a y))). apply IH. apply mono. exact H.
  Qed.

  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable xs : list X.
  Hypothesis xs_full : forall x, In x xs.

  (* From a sound start b below a loop state z of the word q, the iterates of q from b stabilize
     (finitely many states) at a state that every label of q fixes and that lies below z. *)
  Lemma loop_floor : forall b q z, Sd b -> le b z -> wrun X u q z = z ->
    exists w, Sd w /\ le w z /\ (forall i, In i q -> u i w = w).
  Proof.
    intros b q z Hb Hbz Ez.
    destruct (pigeon X X_eq_dec xs xs_full (fun k => wrun X u (qpow q k) b)) as (a & c & Hac & E).
    exists (wrun X u (qpow q a) b). split; [exact (proj1 (infl_wrun _ b Hb)) | split].
    - rewrite <- (wrun_qpow X u q z Ez a). apply mono_wrun. exact Hbz.
    - intros i Hi. apply (infl_loop_fixed (qpow q (c - a))).
      + exact (proj1 (infl_wrun _ b Hb)).
      + cbv beta in E. rewrite <- wrun_app, <- qpow_add. replace (a + (c - a)) with c by lia.
        symmetry. exact E.
      + destruct (c - a) as [| m] eqn:Em; [lia |]. simpl. apply in_or_app. left. exact Hi.
  Qed.
End Inflationary.

(* ============================================================================================ *)
(* Part 5. Recovery (a): Chaotic.chaotic_reaches_lfp.                                           *)
(* Chaotic.v's hypotheses, with two additions (the finiteness leak): the lattice L is listed    *)
(* (xs), and the components are the finite label list js (updates outside js are inert). The   *)
(* rank, bot and step_dec hypotheses are not used: finiteness replaces the rank. A fair loop at *)
(* a reachable state is inflationary, so it is a singleton at a normal form (infl_loop_fixed), *)
(* and Chaotic.normal_is_lfp identifies it: no bad lasso, so C1 gives fair settlement at lfp.   *)
(* ============================================================================================ *)

Section ChaoticBridge.
  Variable L : Type.
  Variable L_eq_dec : forall x y : L, {x = y} + {x <> y}.
  Variable xs : list L.
  Hypothesis xs_full : forall x, In x xs.
  Variable le : L -> L -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable F : L -> L.
  Variable lfp : L.
  Hypothesis lfp_fixed : F lfp = lfp.
  Hypothesis lfp_least : forall x, F x = x -> le lfp x.
  Variable update : nat -> L -> L.
  Variable classicUpdate : forall i x, {update i x = x} + {update i x <> x}.
  Hypothesis up_incr : forall i x, Chaotic.sound le F x -> le x (update i x).
  Hypothesis up_sound : forall i x, Chaotic.sound le F x -> Chaotic.sound le F (update i x).
  Hypothesis up_below : forall i x, le x lfp -> le (update i x) lfp.
  Hypothesis all_fixed : forall x, (forall i, update i x = x) -> F x = x.
  Variable js : list nat.
  Hypothesis inert : forall i x, ~ In i js -> update i x = x.

  Local Notation reach := (Chaotic.reachable le F lfp).

  Lemma ch_reach_wrun : forall w x, reach x -> reach (wrun L update w x).
  Proof.
    induction w as [| a w IH]; intros x [Hs Hb]; [split; assumption |].
    apply IH. split; [apply up_sound | apply up_below]; assumption.
  Qed.

  Lemma ch_lfp_fixed : forall i, update i lfp = lfp.
  Proof.
    intro i. apply le_antisym; [apply up_below, le_refl | apply up_incr].
    unfold Chaotic.sound. rewrite lfp_fixed. apply le_refl.
  Qed.

  Lemma ch_nobad : forall x, reach x -> ~ BadLasso L js update (fun y => y = lfp) x.
  Proof.
    intros x Hx (z & p & q & y & (_ & Ez & _ & _ & Eq & Hall) & (k & _ & Ek) & Ny). apply Ny.
    assert (Hz : reach z) by (rewrite <- Ez; apply ch_reach_wrun; exact Hx).
    pose proof (infl_loop_fixed L le le_refl le_trans le_antisym update (Chaotic.sound le F)
                  up_incr up_sound q z (proj1 Hz) Eq) as Fz.
    assert (Zl : z = lfp).
    { apply (Chaotic.normal_is_lfp le le_antisym F lfp lfp_least nat update classicUpdate all_fixed z Hz).
      intros [y' [i [-> Ne]]]. apply Ne. symmetry.
      destruct (in_dec Nat.eq_dec i js) as [Hi | Hi]; [apply Fz, Hall, Hi | apply inert, Hi]. }
    rewrite <- Ek, Zl. generalize (firstn k q) as w. intro w. induction w as [| a w IH]; [reflexivity |].
    change (wrun L update w (update a lfp) = lfp). rewrite ch_lfp_fixed. exact IH.
  Qed.

  (* Fair-schedule settlement at lfp from every reachable state, through C1. *)
  Theorem chaotic_settles_lasso : forall x, reach x -> forall sg, Fair js sg -> Settles L update sg x lfp.
  Proof.
    intros x Hx. refine (proj2 (recurrence_closed_exact L L_eq_dec xs xs_full js update (fun y => y = lfp) x
                                  _ _) (ch_nobad x Hx)).
    - intro y. destruct (L_eq_dec y lfp); [left | right]; assumption.
    - intros j y _ ->. apply ch_lfp_fixed.
  Qed.

  Lemma ch_run_star : forall sg x n, star (Chaotic.step nat update) x (prs L update sg n x).
  Proof.
    intros sg x n. induction n as [| n IH]; [apply star_refl |]. cbn [prs].
    destruct (classicUpdate (sg n) (prs L update sg n x)) as [E | E]; [rewrite E; exact IH |].
    apply (star_trans _ _ _ _ IH). eapply star_step; [| apply star_refl].
    exists (sg n). split; [reflexivity | intro H; apply E; symmetry; exact H].
  Qed.

  (* chaotic_reaches_lfp, recovered: run any fair schedule (one exists: the lasso schedule of js)
     until it settles; its steps are productive steps or no-ops. *)
  Theorem chaotic_reaches_lfp_lasso : forall x, reach x -> star (Chaotic.step nat update) x lfp.
  Proof.
    intros x Hx. assert (D : js = [] \/ js <> []) by (destruct js; [left | right]; congruence).
    destruct D as [Ejs | Ne].
    - replace x with lfp; [apply star_refl |]. symmetry.
      apply (Chaotic.normal_is_lfp le le_antisym F lfp lfp_least nat update classicUpdate all_fixed x Hx).
      intros [y' [i [-> Nq]]]. apply Nq. symmetry. apply inert. rewrite Ejs. intros [].
    - assert (Hf : Fair js (lsg [] js)).
      { apply lasso_fair; [constructor | apply Forall_forall; tauto | exact Ne | tauto]. }
      destruct (chaotic_settles_lasso x Hx _ Hf) as [N HN]. rewrite <- (HN N (le_n N)). apply ch_run_star.
  Qed.
End ChaoticBridge.

(* ============================================================================================ *)
(* Part 6. Recoveries (b) and (c): SignedResolver.signed_settlement and signed_fidelity.        *)
(* The Resolver section's hypotheses, plus one addition (the finiteness leak): the state type   *)
(* Sh is listed (shs). SignedResolver assumes finite height, not a finite state type. Each     *)
(* bridge shows that no bad fair lasso exists (sr_below_nobad, sr_unique_nobad, sr_sound_nobad) *)
(* and reads the settlement off C1 (recurrence_closed_exact) or C2; the E conjuncts are         *)
(* SignedResolver.kernel_E and kernel_esh applied to the lasso-derived settlement.              *)
(* ============================================================================================ *)

Section Stays.
  Variable X : Type.
  Variable js : list nat.
  Variable u : nat -> X -> X.

  Lemma stable_stays : forall sg, Fair js sg -> forall s0 M, Stable X u js (prs X u sg M s0) ->
    forall n, M <= n -> prs X u sg n s0 = prs X u sg M s0.
  Proof.
    intros sg [Hin _] s0 M HM n Hn. induction Hn as [| n _ IH]; [reflexivity |].
    cbn [prs]. rewrite IH. apply HM, Hin.
  Qed.

  Lemma prs_wrun : forall sg s0 n, prs X u sg n s0 = wrun X u (seg sg 0 n) s0.
  Proof. intros sg s0 n. exact (prs_seg X u sg s0 0 n). Qed.

  Lemma fixed_wrun : forall x, (forall j, u j x = x) -> forall w, wrun X u w x = x.
  Proof.
    intros x Hx w. induction w as [| a w IH]; [reflexivity |].
    change (wrun X u w (u a x) = x). rewrite Hx. exact IH.
  Qed.
End Stays.

Section SignedBridge.
  Variables (X Sh : Type).
  Variable leX : X -> X -> Prop.
  Hypothesis leX_refl : forall a, leX a a.
  Hypothesis leX_trans : forall a b c, leX a b -> leX b c -> leX a c.
  Hypothesis leX_antisym : forall a b, leX a b -> leX b a -> a = b.
  Variables botX topX : X.
  Hypothesis botX_least : forall a, leX botX a.
  Hypothesis topX_greatest : forall a, leX a topX.
  Variable rX : X -> nat.
  Hypothesis rX_strict : forall a b, leX a b -> a <> b -> rX a < rX b.
  Variable hX : nat.
  Hypothesis rX_bound : forall a, rX a <= hX.
  Variable x_eq_dec : forall a b : X, {a = b} + {a <> b}.
  Variable js : list nat.
  Variable get : nat -> Sh -> X.
  Variable set : nat -> X -> Sh -> Sh.
  Hypothesis get_set_eq : forall j x s, In j js -> get j (set j x s) = x.
  Hypothesis get_set_neq : forall j k x s, k <> j -> get k (set j x s) = get k s.
  Hypothesis sh_ext : forall s t, (forall j, In j js -> get j s = get j t) -> s = t.
  Variable z0 : Sh.
  Variable Fv : nat -> Sh -> X.
  Variable sg : list (@edge bool).
  (* The finiteness leak: the state type is listed. *)
  Variable shs : list Sh.
  Hypothesis shs_full : forall s, In s shs.

  Local Notation lo o := (le_o X Sh leX js get o).
  Local Notation RU := (rupd X Sh js set Fv).
  Local Notation FS := (Fsync X Sh js set Fv).
  Local Notation SL o := (slfp X Sh botX topX hX x_eq_dec js get set sh_ext z0 Fv o).
  Local Notation BO o := (bot_o X Sh botX topX js set z0 o).
  Local Notation TO o := (top_o X Sh botX topX js set z0 o).
  Local Notation SEQ := (sh_eq_dec X Sh x_eq_dec js get sh_ext).
  Local Notation SettledR := (r_settled X Sh js set Fv).

  Section Loops.
    Variable o : nat -> bool.
    Hypothesis Hm : forall v, In v js -> forall s t, lo o s t -> leo X leX o v (Fv v s) (Fv v t).

    Let lrefl := le_o_refl X Sh leX leX_refl js get o.
    Let ltrans := le_o_trans X Sh leX leX_trans js get o.
    Let lanti := le_o_antisym X Sh leX leX_antisym js get sh_ext o.
    Let incr : forall j x, lo o x (FS x) -> lo o x (RU j x) :=
      fun j x H => s_incr X Sh leX leX_refl js get set get_set_eq get_set_neq Fv o tt j x H.
    Let sstep : forall j x, lo o x (FS x) -> lo o (RU j x) (FS (RU j x)) :=
      fun j x H => s_sound X Sh leX leX_refl leX_trans js get set get_set_eq get_set_neq Fv o Hm tt j x H.
    Let mono : forall j x y, lo o x y -> lo o (RU j x) (RU j y) :=
      fun j x y H => s_mono X Sh leX js get set get_set_eq get_set_neq Fv o Hm tt j x y H.
    Let decr : forall j x, lo o (FS x) x -> lo o (RU j x) x :=
      fun j x H => s_decr X Sh leX leX_refl js get set get_set_eq get_set_neq Fv o tt j x H.
    Let cosound : forall j x, lo o (FS x) x -> lo o (FS (RU j x)) (RU j x) :=
      fun j x H => s_cosound X Sh leX leX_refl leX_trans js get set get_set_eq get_set_neq Fv o Hm tt j x H.
    Let lfix := slfp_fixed X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX
                  rX_bound x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm.
    Let lleast := slfp_least X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX
                    rX_bound x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm.

    Lemma stable_fs : forall w, (forall i, In i js -> RU i w = w) -> FS w = w.
    Proof. intros w H. exact (proj1 (settled_fixed X Sh js get set get_set_eq get_set_neq sh_ext Fv w) H). Qed.

    Lemma fs_fixed_all : forall w, FS w = w -> forall j, RU j w = w.
    Proof. intros w H j. exact (s_fixed X Sh js get set get_set_eq get_set_neq sh_ext Fv tt j w H). Qed.

    (* A fair loop lies above slfp: the bottom run under the loop word stabilizes below it. *)
    Lemma sr_floor : forall z q, wrun Sh RU q z = z -> (forall j, In j js -> In j q) -> lo o (SL o) z.
    Proof.
      intros z q Ez Hall.
      destruct (loop_floor Sh (lo o) lrefl ltrans lanti RU (fun x => lo o x (FS x)) incr sstep mono SEQ shs
                  shs_full (BO o) q z
                  (bot_o_least X Sh leX botX topX botX_least topX_greatest js get set get_set_eq get_set_neq z0 o _)
                  (bot_o_least X Sh leX botX topX botX_least topX_greatest js get set get_set_eq get_set_neq z0 o z)
                  Ez) as (w & _ & Hwz & Fw).
      apply (ltrans _ w _); [| exact Hwz]. apply lleast. apply stable_fs. intros i Hi. apply Fw, Hall, Hi.
    Qed.

    (* Dually, a fair loop lies below a fixed point: the top run stabilizes above it. *)
    Lemma sr_ceiling : forall z q, wrun Sh RU q z = z -> (forall j, In j js -> In j q) ->
      exists w, FS w = w /\ lo o z w.
    Proof.
      intros z q Ez Hall.
      destruct (loop_floor Sh (fun a b => lo o b a) lrefl (fun a b c H1 H2 => ltrans c b a H2 H1)
                  (fun a b H1 H2 => lanti a b H2 H1) RU (fun x => lo o (FS x) x) decr cosound
                  (fun j x y H => mono j y x H) SEQ shs shs_full (TO o) q z
                  (top_o_greatest X Sh leX botX topX botX_least topX_greatest js get set get_set_eq get_set_neq z0 o _)
                  (top_o_greatest X Sh leX botX topX botX_least topX_greatest js get set get_set_eq get_set_neq z0 o z)
                  Ez) as (w & _ & Hwz & Fw).
      exists w. split; [apply stable_fs; intros i Hi; apply Fw, Hall, Hi | exact Hwz].
    Qed.

    Lemma wrun_below : forall w h, lo o h (SL o) -> lo o (wrun Sh RU w h) (SL o).
    Proof.
      induction w as [| a w IH]; intros h H; [exact H |]. apply IH.
      exact (s_below X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX rX_bound
               x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm a h H).
    Qed.

    (* (b) Below slfp, every fair recurrent state is slfp. *)
    Lemma sr_below_nobad : forall h0, lo o h0 (SL o) -> ~ BadLasso Sh js RU (fun x => x = SL o) h0.
    Proof.
      intros h0 H0 (z & p & q & y & (_ & Ez & _ & _ & Eq & Hall) & (k & _ & Ek) & Ny). apply Ny.
      assert (Zl : z = SL o).
      { apply lanti; [rewrite <- Ez; apply wrun_below; exact H0 | exact (sr_floor z q Eq Hall)]. }
      rewrite <- Ek, Zl. apply fixed_wrun. apply fs_fixed_all. exact lfix.
    Qed.

    (* (c) With one fixed point, every fair recurrent state from every start is slfp. *)
    Lemma sr_unique_nobad : (forall p q, FS p = p -> FS q = q -> p = q) ->
      forall h0, ~ BadLasso Sh js RU (fun x => x = SL o) h0.
    Proof.
      intros Hu h0 (z & p & q & y & (_ & _ & _ & _ & Eq & Hall) & (k & _ & Ek) & Ny). apply Ny.
      destruct (sr_ceiling z q Eq Hall) as [w [Fw Hzw]].
      assert (Zl : z = SL o) by (apply lanti; [rewrite (Hu w (SL o) Fw lfix) in Hzw; exact Hzw | exact (sr_floor z q Eq Hall)]).
      rewrite <- Ek, Zl. apply fixed_wrun. apply fs_fixed_all. exact lfix.
    Qed.

    (* From a sound start, every fair recurrent loop is a singleton fixed point (C2). *)
    Lemma sr_sound_nobad : forall h0, lo o h0 (FS h0) -> ~ BadLasso Sh js RU (Stable Sh RU js) h0.
    Proof.
      intros h0 H0 (z & p & q & y & (_ & Ez & _ & Hq & Eq & Hall) & (k & _ & Ek) & Ny). apply Ny.
      assert (Sz : lo o z (FS z)) by (rewrite <- Ez; exact (proj1 (infl_wrun Sh (lo o) lrefl ltrans RU _ incr sstep p h0 H0))).
      assert (Stz : Stable Sh RU js z).
      { intros j Hj. exact (infl_loop_fixed Sh (lo o) lrefl ltrans lanti RU _ incr sstep q z Sz Eq j (Hall j Hj)). }
      rewrite <- Ek, (settled_wrun Sh js RU z Stz (firstn k q) (path_firstn js k q Hq)). exact Stz.
    Qed.
  End Loops.

  Local Notation SettlesE o h0 :=
    (EffectiveCanon (fun _ => SL o) RU (r_ok js) (r_flush js) SettledR h0 /\
     Settlement RU (r_ok js) (r_flush js) SettledR h0 /\
     CanonAgree (fun _ => SL o) (r_ev Sh) RU r_kind (r_ok js) SettledR h0 /\
     CanonConv RU r_kind (r_ok js) SettledR r_eqh h0).

  Lemma sl_closed : forall o, FS (SL o) = SL o -> Closed Sh js RU (fun x => x = SL o).
  Proof. intros o H j x _ ->. exact (s_fixed X Sh js get set get_set_eq get_set_neq sh_ext Fv tt j _ H). Qed.

  Lemma sl_dec : forall o, PDec Sh (fun x => x = SL o).
  Proof. intros o x. destruct (SEQ x (SL o)); [left | right]; assumption. Qed.

  (* signed_settlement, recovered through C1 (conjuncts 2 and 4) and C2 (conjunct 3); the
     statement is signed_settlement's, with the finiteness of Sh added. *)
  Theorem signed_settlement_lasso : SgOn js sg -> Resp X Sh leX js get Fv sg -> forall o, Switching sg o ->
    (FS (SL o) = SL o /\ forall p, FS p = p -> lo o (SL o) p) /\
    (forall h0 sch, lo o h0 (SL o) -> Fair js sch -> Settles Sh RU sch h0 (SL o)) /\
    (forall h0 sch, lo o h0 (FS h0) -> Fair js sch ->
       exists q, (FS q = q /\ lo o h0 q /\ (forall p, FS p = p -> lo o h0 p -> lo o q p)) /\
                 Settles Sh RU sch h0 q) /\
    (forall h0, lo o h0 (SL o) -> SettlesE o h0).
  Proof.
    intros Hon Hr o Hsw. pose proof (switched_monotone X Sh leX js get Fv sg Hon Hr o Hsw) as Hm.
    pose proof (slfp_fixed X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX
                  rX_bound x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm) as Hfix.
    pose proof (slfp_least X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX
                  rX_bound x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm) as Hleast.
    pose proof (le_o_antisym X Sh leX leX_antisym js get sh_ext o) as lanti.
    assert (Hset : forall h0 sch, lo o h0 (SL o) -> Fair js sch -> Settles Sh RU sch h0 (SL o)).
    { intros h0 sch H0. exact (proj2 (recurrence_closed_exact Sh SEQ shs shs_full js RU _ h0 (sl_dec o)
                                        (sl_closed o Hfix)) (sr_below_nobad o Hm h0 H0) sch). }
    split; [split; [exact Hfix | exact Hleast] |]. split; [exact Hset |]. split.
    - intros h0 sch H0 Hf.
      destruct (proj2 (C2 Sh SEQ shs shs_full js RU h0) (sr_sound_nobad o Hm h0 H0) sch Hf) as [M HM].
      assert (St : Stable Sh RU js (prs Sh RU sch M h0)) by (apply HM; lia).
      exists (prs Sh RU sch M h0). split; [split; [| split] |].
      + apply stable_fs. exact St.
      + rewrite prs_wrun. exact (proj2 (infl_wrun Sh (lo o) (le_o_refl X Sh leX leX_refl js get o)
          (le_o_trans X Sh leX leX_trans js get o) RU _
          (fun j x H => s_incr X Sh leX leX_refl js get set get_set_eq get_set_neq Fv o tt j x H)
          (fun j x H => s_sound X Sh leX leX_refl leX_trans js get set get_set_eq get_set_neq Fv o Hm tt j x H)
          _ h0 H0)).
      + intros p Fp Hp. rewrite prs_wrun. rewrite <- (fixed_wrun Sh RU p (fs_fixed_all p Fp) (seg sch 0 M)).
        apply (mono_wrun Sh (lo o) RU
                 (fun j x y H => s_mono X Sh leX js get set get_set_eq get_set_neq Fv o Hm tt j x y H)). exact Hp.
      + exists M. exact (stable_stays Sh js RU sch Hf h0 M St).
    - intros h0 H0.
      assert (Pst : forall j s, lo o s (SL o) -> lo o (RU j s) (SL o)) by (intros j s; exact (wrun_below o Hm [j] s)).
      assert (Pse : forall s, lo o s (SL o) -> forall sch, Fair js sch -> Settles Sh RU sch s (SL o))
        by (intros s Hs sch; exact (Hset s sch Hs)).
      assert (Pfi : forall s, lo o s (SL o) -> FS s = s -> s = SL o) by (intros s Hs Fs; exact (lanti _ _ Hs (Hleast s Fs))).
      split; [exact (kernel_E X Sh js get set get_set_eq get_set_neq sh_ext Fv (SL o) Hfix _ Pst Pse Pfi h0 H0) |].
      exact (kernel_esh X Sh js get set get_set_eq get_set_neq sh_ext Fv (SL o) Hfix _ Pst Pse Pfi h0 H0).
  Qed.

  (* signed_fidelity, recovered through C1; the statement is signed_fidelity's, with the
     finiteness of Sh added. *)
  Theorem signed_fidelity_lasso : SgOn js sg -> Resp X Sh leX js get Fv sg -> forall o, Switching sg o ->
    (forall p q, FS p = p -> FS q = q -> p = q) ->
    FS (SL o) = SL o /\
    (forall sch, Fair js sch -> forall h0, Settles Sh RU sch h0 (SL o)) /\
    (forall h0, SettlesE o h0).
  Proof.
    intros Hon Hr o Hsw Hu. pose proof (switched_monotone X Sh leX js get Fv sg Hon Hr o Hsw) as Hm.
    pose proof (slfp_fixed X Sh leX leX_refl leX_trans botX topX botX_least topX_greatest rX rX_strict hX
                  rX_bound x_eq_dec js get set get_set_eq get_set_neq sh_ext z0 Fv o Hm) as Hfix.
    assert (Hset : forall sch, Fair js sch -> forall h0, Settles Sh RU sch h0 (SL o)).
    { intros sch Hf h0. exact (proj2 (recurrence_closed_exact Sh SEQ shs shs_full js RU _ h0 (sl_dec o)
                                        (sl_closed o Hfix)) (sr_unique_nobad o Hm Hu h0) sch Hf). }
    split; [exact Hfix | split; [exact Hset |]].
    assert (Pfi : forall s, True -> FS s = s -> s = SL o) by (intros s _ Fs; exact (Hu s _ Fs Hfix)).
    intros h0. split.
    - exact (kernel_E X Sh js get set get_set_eq get_set_neq sh_ext Fv (SL o) Hfix (fun _ => True)
               (fun _ _ _ => I) (fun s _ sch Hf => Hset sch Hf s) Pfi h0 I).
    - exact (kernel_esh X Sh js get set get_set_eq get_set_neq sh_ext Fv (SL o) Hfix (fun _ => True)
               (fun _ _ _ => I) (fun s _ sch Hf => Hset sch Hf s) Pfi h0 I).
  Qed.
End SignedBridge.

(* ============================================================================================ *)
(* Part 7. Recovery (d): fair flushing in the distributed cyclic model (DistributedCyclesExact). *)
(* FairFlushAt t (every fair schedule reaches a quiescent state) is C2 for the propagation      *)
(* steps of t's locals, on a listed Sh (the finiteness leak: DistributedCycles assumes finite   *)
(* height, not a finite state type). FairFlushR is C2 at every reachable state.                 *)
(* ============================================================================================ *)

Section FlushBridge.
  Variables Loc Sh : Type.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable shs : list Sh.
  Hypothesis shs_full : forall s, In s shs.
  Variable bot : Sh.
  Variable u : Loc -> nat -> Sh -> Sh.
  Variable js : list nat.

  Theorem fairflush_lasso : forall t, FairFlushAt Loc Sh u js t <->
    ~ BadLasso Sh js (u (fst t)) (Stable Sh (u (fst t)) js) (snd t).
  Proof.
    intros t. rewrite <- (C2 Sh sh_eq_dec shs shs_full js (u (fst t)) (snd t)), C2_reach.
    unfold FairFlushAt. tauto.
  Qed.

  Theorem fairflushR_lasso : forall E ev r s0, FairFlushR Loc Sh bot u js E ev r s0 <->
    (forall w, OK js E r w ->
       ~ BadLasso Sh js (u (fst (crun Loc Sh bot u E ev w s0)))
                  (Stable Sh (u (fst (crun Loc Sh bot u E ev w s0))) js) (snd (crun Loc Sh bot u E ev w s0))).
  Proof.
    intros E ev r s0. unfold FairFlushR. split; intros H w Hw.
    - apply (proj1 (fairflush_lasso _)). exact (H w Hw).
    - apply (proj2 (fairflush_lasso _)). exact (H w Hw).
  Qed.
End FlushBridge.

(* The refutation direction needs no finiteness: a bad fair lasso refutes FairFlushAt. *)
Lemma bad_lasso_no_fairflush : forall (Loc Sh : Type) (u : Loc -> nat -> Sh -> Sh) js t,
  BadLasso Sh js (u (fst t)) (Stable Sh (u (fst t)) js) (snd t) -> ~ FairFlushAt Loc Sh u js t.
Proof.
  intros Loc Sh u js t B H. apply (proj1 (bad_lasso_refutes _ _ _ _ _ B)).
  apply (proj2 (C2_reach Sh js (u (fst t)) (snd t))). exact H.
Qed.

Lemma fl_full : forall x, In x [fz; fa; fb].
Proof. intros []; simpl; tauto. Qed.

(* flip2_fair_livelock as an explicit bad FAIR lasso: from fa, the word 0, 1, 0 returns to fa,
   names both labels, and visits the unquiescent states fa and fb. This refutes FairFlushAt and
   FairFlushR (flip2_fair_livelock's last conjunct), although the repair has one fixed point. *)
Theorem flip2_fair_lasso :
  FairLasso Fl fjs2 (fu2 tt) fa fa [] [0; 1; 0] /\
  OnLoop Fl (fu2 tt) fa [0; 1; 0] fa /\ OnLoop Fl (fu2 tt) fa [0; 1; 0] fb /\
  ~ Stable Fl (fu2 tt) fjs2 fa /\ ~ Stable Fl (fu2 tt) fjs2 fb /\
  BadLasso Fl fjs2 (fu2 tt) (Stable Fl (fu2 tt) fjs2) fa /\
  (forall l, UniqueFP unit Fl fz fl_eq_dec fF fu2 2 fjs2 l) /\
  ~ FairFlushAt unit Fl fu2 fjs2 (tt, fa) /\
  ~ FairFlushR unit Fl fz fu2 fjs2 unit fid false (tt, fa).
Proof.
  assert (HL : FairLasso Fl fjs2 (fu2 tt) fa fa [] [0; 1; 0]).
  { split; [constructor | split; [reflexivity | split; [discriminate | split]]].
    - repeat constructor; simpl; tauto.
    - split; [reflexivity | intros j [<- | [<- | []]]; simpl; tauto]. }
  assert (O1 : OnLoop Fl (fu2 tt) fa [0; 1; 0] fa) by (exists 0; split; [simpl; lia | reflexivity]).
  assert (O2 : OnLoop Fl (fu2 tt) fa [0; 1; 0] fb) by (exists 1; split; [simpl; lia | reflexivity]).
  assert (Na : ~ Stable Fl (fu2 tt) fjs2 fa) by (intro H; specialize (H 0 (or_introl eq_refl)); discriminate H).
  assert (Nb : ~ Stable Fl (fu2 tt) fjs2 fb) by (intro H; specialize (H 0 (or_introl eq_refl)); discriminate H).
  assert (B : BadLasso Fl fjs2 (fu2 tt) (Stable Fl (fu2 tt) fjs2) fa) by (exists fa, [], [0; 1; 0], fa; tauto).
  assert (NF : ~ FairFlushAt unit Fl fu2 fjs2 (tt, fa)) by exact (bad_lasso_no_fairflush unit Fl fu2 fjs2 (tt, fa) B).
  do 6 (split; [assumption |]). split; [exact f2_unique |]. split; [exact NF |].
  intro H. exact (NF (H [] (Forall_nil _))).
Qed.

(* The fairness encoding test. In the drop network (label 0 swaps fa and fb, label 1 drops every
   value to fz), the cycle fa -> fb -> fa under 0, 0 is bad (fa is not quiescent) but not fair
   (it never names 1). It does not refute C1 or C2: every fair loop is the fixed point fz, so
   every fair schedule from every start settles, raw and canonically (N = identity, target fz). *)
Definition fud (j : nat) (x : Fl) : Fl := match j with 0 => fsw x | _ => fz end.

Lemma fud_fz : forall w, wrun Fl fud w fz = fz.
Proof. induction w as [| [| j] w IH]; [reflexivity | exact IH | exact IH]. Qed.

Lemma fud_loops : forall s0 x p q y, FairLasso Fl fjs2 fud s0 x p q -> OnLoop Fl fud x q y -> y = fz.
Proof.
  intros s0 x p q y (_ & _ & _ & _ & Eq & Hall) (k & _ & <-).
  destruct (in_split 1 q (Hall 1 (or_intror (or_introl eq_refl)))) as (q1 & q2 & ->).
  assert (Ex : x = fz).
  { rewrite <- Eq, wrun_app. change (wrun Fl fud q2 (fud 1 (wrun Fl fud q1 x)) = fz). apply fud_fz. }
  rewrite Ex. apply fud_fz.
Qed.

Theorem nonfair_cycle_not_refuting :
  wrun Fl fud [0; 0] fa = fa /\ Path fjs2 [0; 0] /\ OnLoop Fl fud fa [0; 0] fb /\
  ~ Stable Fl fud fjs2 fa /\ ~ (forall j, In j fjs2 -> In j [0; 0]) /\
  (forall s0, ~ BadLasso Fl fjs2 fud (Stable Fl fud fjs2) s0) /\
  (forall s0, FairSettles Fl fjs2 fud (Stable Fl fud fjs2) s0) /\
  (forall s0, CanonSettles Fl fjs2 fud Fl (fun x => x) s0 fz).
Proof.
  assert (Sz : Stable Fl fud fjs2 fz) by (intros [| j] _; reflexivity).
  assert (NB : forall s0, ~ BadLasso Fl fjs2 fud (Stable Fl fud fjs2) s0).
  { intros s0 (x & p & q & y & HL & Hy & Ny). rewrite (fud_loops s0 x p q y HL Hy) in Ny. exact (Ny Sz). }
  split; [reflexivity | split; [repeat constructor; simpl; tauto |]].
  split; [exists 1; split; [simpl; lia | reflexivity] |].
  split; [intro H; specialize (H 0 (or_introl eq_refl)); discriminate H |].
  split; [intro H; specialize (H 1 (or_intror (or_introl eq_refl))); simpl in H; lia |].
  split; [exact NB |]. split; [intro s0; exact (proj2 (C2 Fl fl_eq_dec _ fl_full fjs2 fud s0) (NB s0)) |].
  intro s0. apply (proj2 (C1_closed Fl fl_eq_dec _ fl_full fjs2 fud Fl fl_eq_dec (fun x => x) s0 fz
                            ltac:(intros [| j] x _ H; unfold Fiber in *; subst x; reflexivity))).
  intros (x & p & q & y & HL & Hy & Ny). exact (Ny (fud_loops s0 x p q y HL Hy)).
Qed.

(* ============================================================================================ *)
(* Part 8. Recovery (e), the ghost, and the classification by lasso witnesses.                  *)
(* Two-vertex boolean resolver networks of SignedResolver.v (states bool * bool, finite).       *)
(* ============================================================================================ *)

Definition ss2_all : list SS2 := [(false, false); (false, true); (true, false); (true, true)].
Lemma ss2_full : forall s : SS2, In s ss2_all.
Proof. intros [[|] [|]]; simpl; tauto. Qed.
Definition ss2_eq_dec : forall s t : SS2, {s = t} + {s <> t}.
Proof. intros [a b] [c d]. destruct (bool_dec a c), (bool_dec b d); [left | right | right | right]; congruence. Defined.

Lemma ss2_fiber_dec : forall c, PDec SS2 (Fiber SS2 SS2 (fun s => s) c).
Proof. intros c s. unfold Fiber. destruct (ss2_eq_dec s c); [left | right]; assumption. Qed.

Lemma cb_tt_fixed : forall j, rupd2 cb_F j (true, true) = (true, true).
Proof. intros j. unfold rupd2, rupd. destruct (in_dec Nat.eq_dec j js2) as [[<- | [<- | []]] | _]; reflexivity. Qed.

Lemma cb_ff_fixed : forall j, rupd2 cb_F j (false, false) = (false, false).
Proof. intros j. unfold rupd2, rupd. destruct (in_dec Nat.eq_dec j js2) as [[<- | [<- | []]] | _]; reflexivity. Qed.

Lemma cb_lasso_tt : forall s0 p, Path js2 p -> wrun SS2 (rupd2 cb_F) p s0 = (true, true) ->
  FairLasso SS2 js2 (rupd2 cb_F) s0 (true, true) p [0; 1].
Proof.
  intros s0 p Hp E. split; [exact Hp | split; [exact E | split; [discriminate | split]]].
  - repeat constructor; simpl; tauto.
  - split; [reflexivity | intros j [<- | [<- | []]]; simpl; tauto].
Qed.

Lemma cb_lasso_ff : forall s0 p, Path js2 p -> wrun SS2 (rupd2 cb_F) p s0 = (false, false) ->
  FairLasso SS2 js2 (rupd2 cb_F) s0 (false, false) p [0; 1].
Proof.
  intros s0 p Hp E. split; [exact Hp | split; [exact E | split; [discriminate | split]]].
  - repeat constructor; simpl; tauto.
  - split; [reflexivity | intros j [<- | [<- | []]]; simpl; tauto].
Qed.

(* (e) copyback_ghost as a settled singleton loop in the wrong canonical fiber: from the sound
   start (1, 1) every fair loop is the singleton fixed point (1, 1), so raw settlement (C2) holds,
   but (1, 1) is not slfp = (0, 0), so a bad canonical lasso exists and canonical settlement at
   slfp (C1) fails. *)
Theorem copyback_ghost_lasso :
  FairLasso SS2 js2 (rupd2 cb_F) (true, true) (true, true) [] [0; 1] /\
  (forall x p q, FairLasso SS2 js2 (rupd2 cb_F) (true, true) x p q ->
     forall y, OnLoop SS2 (rupd2 cb_F) x q y -> y = x /\ Stable SS2 (rupd2 cb_F) js2 x) /\
  FairSettles SS2 js2 (rupd2 cb_F) (Stable SS2 (rupd2 cb_F) js2) (true, true) /\
  slfp2 cb_F ofalse = (false, false) /\
  BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse) /\
  ~ CanonSettles SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse).
Proof.
  destruct copyback_ghost as (_ & _ & _ & Hl & _).
  pose proof (fixed_wrun SS2 (rupd2 cb_F) _ cb_tt_fixed) as W.
  assert (HL : FairLasso SS2 js2 (rupd2 cb_F) (true, true) (true, true) [] [0; 1])
    by (apply cb_lasso_tt; [constructor | reflexivity]).
  assert (Loops : forall x p q, FairLasso SS2 js2 (rupd2 cb_F) (true, true) x p q ->
     forall y, OnLoop SS2 (rupd2 cb_F) x q y -> y = x /\ Stable SS2 (rupd2 cb_F) js2 x).
  { intros x p q (_ & Ex & _) y (k & _ & <-). rewrite <- Ex, !W. split; [reflexivity | intros j _; apply cb_tt_fixed]. }
  assert (B : BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse)).
  { exists (true, true), [], [0; 1], (true, true). split; [exact HL | split; [apply onloop_base; discriminate |]].
    unfold Fiber. rewrite Hl. discriminate. }
  split; [exact HL | split; [exact Loops | split]].
  - exact (proj2 (C2_loops SS2 ss2_eq_dec _ ss2_full js2 (rupd2 cb_F) (true, true)) Loops).
  - split; [exact Hl | split; [exact B | exact (proj1 (C1_refutes _ _ _ _ _ _ _ B))]].
Qed.

(* Classification 1, the negation cycle x0 := not x1, x1 := x0: a bad NON-singleton fair lasso
   (four distinct states), bad for every canonical target, and no singleton loop anywhere. *)
Theorem class_negation_cycle :
  FairLasso SS2 js2 (rupd2 neg_F) (false, false) (false, false) [] [0; 1; 0; 1] /\
  OnLoop SS2 (rupd2 neg_F) (false, false) [0; 1; 0; 1] (true, false) /\
  BadLasso SS2 js2 (rupd2 neg_F) (Stable SS2 (rupd2 neg_F) js2) (false, false) /\
  (forall c, BadCanonLasso SS2 js2 (rupd2 neg_F) SS2 (fun s => s) (false, false) c) /\
  (forall s, ~ Stable SS2 (rupd2 neg_F) js2 s).
Proof.
  destruct neg2_no_fixed_point as (_ & _ & _ & _ & Hnf & _).
  assert (NS : forall s, ~ Stable SS2 (rupd2 neg_F) js2 s)
    by (intros s H; apply (Hnf s); apply settled2_fixed; exact H).
  assert (HL : FairLasso SS2 js2 (rupd2 neg_F) (false, false) (false, false) [] [0; 1; 0; 1]).
  { split; [constructor | split; [reflexivity | split; [discriminate | split]]].
    - repeat constructor; simpl; tauto.
    - split; [reflexivity | intros j [<- | [<- | []]]; simpl; tauto]. }
  assert (O0 : OnLoop SS2 (rupd2 neg_F) (false, false) [0; 1; 0; 1] (false, false)) by (apply onloop_base; discriminate).
  assert (O1 : OnLoop SS2 (rupd2 neg_F) (false, false) [0; 1; 0; 1] (true, false))
    by (exists 1; split; [simpl; lia | reflexivity]).
  split; [exact HL | split; [exact O1 | split]].
  - exists (false, false), [], [0; 1; 0; 1], (false, false). split; [exact HL | split; [exact O0 | apply NS]].
  - split; [| exact NS]. intro c. destruct (ss2_eq_dec c (false, false)) as [-> | Ne].
    + exists (false, false), [], [0; 1; 0; 1], (true, false). split; [exact HL | split; [exact O1 |]].
      unfold Fiber. discriminate.
    + exists (false, false), [], [0; 1; 0; 1], (false, false). split; [exact HL | split; [exact O0 |]].
      unfold Fiber. intro E. exact (Ne (eq_sym E)).
Qed.

(* Classification 4, a good monotone resolver (neg_chain_settles: x0 := true, x1 := not x0):
   no bad fair lasso for the target slfp = (1, 0) from any start, read off the recovered
   signed_settlement_lasso. *)
Theorem class_good_resolver : forall h0,
  CanonSettles SS2 js2 (rupd2 nc_F) SS2 (fun s => s) h0 (true, false) /\
  ~ BadCanonLasso SS2 js2 (rupd2 nc_F) SS2 (fun s => s) h0 (true, false).
Proof.
  assert (Hon : SgOn js2 nc_sg) by (intros u v b [E | []]; injection E as <- <- <-; simpl; tauto).
  assert (Hr : Resp2 nc_F nc_sg).
  { intros v Hv s t H. destruct Hv as [<- | [<- | []]]; [reflexivity |].
    pose proof (H 0 true (or_introl eq_refl)) as H1. simpl in H1. revert H1. s2; unfold sbl; simpl; auto. }
  assert (Hs : Switching nc_sg otg) by (intros u v b [E | []]; injection E as <- <- <-; reflexivity).
  destruct neg_chain_settles as (Hl & Hlow & _).
  destruct (signed_settlement_lasso bool SS2 sbl sbl_refl sbl_trans sbl_antisym false true sbl_bot sbl_top
              sb2n sb2n_strict 1 sb2n_bound bool_dec js2 get2 set2 get2_set_eq get2_set_neq s2_ext z2
              nc_F nc_sg ss2_all ss2_full Hon Hr otg Hs) as (_ & H1 & _).
  intro h0. assert (CS : CanonSettles SS2 js2 (rupd2 nc_F) SS2 (fun s => s) h0 (true, false)).
  { intros sch Hf. destruct (H1 h0 sch (Hlow h0) Hf) as [N HN]. exists N. intros n Hn. unfold Fiber.
    rewrite <- Hl. exact (HN n Hn). }
  split; [exact CS | intro B; exact (proj1 (C1_refutes _ _ _ _ _ _ _ B) CS)].
Qed.

(* Classification 5, several fixed points (copyback from (0, 1)): two singleton fair recurrent
   classes, {(1, 1)} and {(0, 0)}, both reachable. Raw settlement holds (C2), and every canonical
   target has a bad lasso (the outcome depends on the schedule). *)
Lemma cb_step_stable : forall j s, In j js2 -> Stable SS2 (rupd2 cb_F) js2 (rupd2 cb_F j s).
Proof.
  intros j [a b] Hj k Hk. destruct Hj as [<- | [<- | []]]; destruct Hk as [<- | [<- | []]]; reflexivity.
Qed.

Theorem class_multiple_fixed_points :
  Stable SS2 (rupd2 cb_F) js2 (true, true) /\ Stable SS2 (rupd2 cb_F) js2 (false, false) /\
  FairLasso SS2 js2 (rupd2 cb_F) (false, true) (true, true) [0] [0; 1] /\
  FairLasso SS2 js2 (rupd2 cb_F) (false, true) (false, false) [1] [0; 1] /\
  FairSettles SS2 js2 (rupd2 cb_F) (Stable SS2 (rupd2 cb_F) js2) (false, true) /\
  (forall c, BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (false, true) c) /\
  (forall c, ~ CanonSettles SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (false, true) c).
Proof.
  assert (L1 : FairLasso SS2 js2 (rupd2 cb_F) (false, true) (true, true) [0] [0; 1])
    by (apply cb_lasso_tt; [repeat constructor; simpl; tauto | reflexivity]).
  assert (L2 : FairLasso SS2 js2 (rupd2 cb_F) (false, true) (false, false) [1] [0; 1])
    by (apply cb_lasso_ff; [repeat constructor; simpl; tauto | reflexivity]).
  assert (B : forall c, BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (false, true) c).
  { intro c. destruct (ss2_eq_dec c (true, true)) as [-> | Ne].
    - exists (false, false), [1], [0; 1], (false, false). split; [exact L2 | split; [apply onloop_base; discriminate |]].
      unfold Fiber. discriminate.
    - exists (true, true), [0], [0; 1], (true, true). split; [exact L1 | split; [apply onloop_base; discriminate |]].
      unfold Fiber. intro E. exact (Ne (eq_sym E)). }
  split; [intros j _; apply cb_tt_fixed | split; [intros j _; apply cb_ff_fixed |]].
  split; [exact L1 | split; [exact L2 | split]].
  - apply (proj2 (C2_loops SS2 ss2_eq_dec _ ss2_full js2 (rupd2 cb_F) (false, true))).
    intros x p q (_ & _ & Hq & Pq & Eq & _) y (k & _ & <-).
    destruct q as [| a q']; [congruence |]. inversion Pq as [| ? ? Ha Pq']; subst.
    pose proof (cb_step_stable a x Ha) as Sa.
    change (wrun SS2 (rupd2 cb_F) q' (rupd2 cb_F a x) = x) in Eq.
    rewrite (settled_wrun SS2 js2 (rupd2 cb_F) _ Sa q' Pq') in Eq. rewrite Eq in Sa.
    split; [apply (settled_wrun SS2 js2 (rupd2 cb_F) x Sa); apply path_firstn; exact Pq | exact Sa].
  - split; [exact B | intro c; exact (proj1 (C1_refutes _ _ _ _ _ _ _ (B c)))].
Qed.

(* ============================================================================================ *)
(* Part 9. A new example: raw oscillation with constant meaning. States a, b, z; the one label  *)
(* swaps a and b and sends z to a; N a = N b = true, N z = false. From z, the only fair run is  *)
(* z, a, b, a, b, ...: raw settlement fails (C2: the fair lasso a -> b -> a is not settled),    *)
(* while canonical settlement at true holds (C1: no fair loop visits z).                        *)
(* ============================================================================================ *)

Inductive Osc : Type := oa | ob | oz.
Definition osc_eq_dec : forall x y : Osc, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition osc_u (_ : nat) (x : Osc) : Osc := match x with oa => ob | ob => oa | oz => oa end.
Definition osc_js : list nat := [0].
Definition osc_N (x : Osc) : bool := match x with oz => false | _ => true end.

Lemma osc_full : forall x, In x [oa; ob; oz].
Proof. intros []; simpl; tauto. Qed.

Lemma osc_not_z : forall w x, w <> [] -> wrun Osc osc_u w x <> oz.
Proof.
  induction w as [| a w IH]; intros x H; [congruence |]. destruct w as [| b w].
  - destruct x; discriminate.
  - change (wrun Osc osc_u (b :: w) (osc_u a x) <> oz). apply IH. discriminate.
Qed.

Theorem semantic_oscillation :
  FairLasso Osc osc_js osc_u oz oa [0] [0; 0] /\ OnLoop Osc osc_u oa [0; 0] ob /\ oa <> ob /\
  osc_N oa = osc_N ob /\
  BadLasso Osc osc_js osc_u (Stable Osc osc_u osc_js) oz /\
  ~ FairSettles Osc osc_js osc_u (Stable Osc osc_u osc_js) oz /\
  ~ BadCanonLasso Osc osc_js osc_u bool osc_N oz true /\
  CanonSettles Osc osc_js osc_u bool osc_N oz true.
Proof.
  assert (HL : FairLasso Osc osc_js osc_u oz oa [0] [0; 0]).
  { split; [repeat constructor; simpl; tauto | split; [reflexivity | split; [discriminate | split]]].
    - repeat constructor; simpl; tauto.
    - split; [reflexivity | intros j [<- | []]; simpl; tauto]. }
  assert (B : BadLasso Osc osc_js osc_u (Stable Osc osc_u osc_js) oz).
  { exists oa, [0], [0; 0], oa. split; [exact HL | split; [apply onloop_base; discriminate |]].
    intro H. specialize (H 0 (or_introl eq_refl)). discriminate H. }
  assert (NB : ~ BadCanonLasso Osc osc_js osc_u bool osc_N oz true).
  { intros (x & p & q & y & (_ & _ & Hq & _ & Eq & _) & (k & Hk & <-) & Ny). apply Ny. unfold Fiber.
    assert (Hz : wrun Osc osc_u (firstn k q) x <> oz).
    { destruct k as [| k].
      - simpl. rewrite <- Eq. apply osc_not_z. exact Hq.
      - apply osc_not_z. destruct q as [| a q]; [congruence | discriminate]. }
    destruct (wrun Osc osc_u (firstn k q) x); [reflexivity | reflexivity | congruence]. }
  split; [exact HL | split; [exists 1; split; [simpl; lia | reflexivity] | split; [discriminate |]]].
  split; [reflexivity | split; [exact B | split; [exact (proj1 (bad_lasso_refutes _ _ _ _ _ B)) |]]].
  split; [exact NB |].
  apply (proj2 (C1_closed Osc osc_eq_dec _ osc_full osc_js osc_u bool bool_dec osc_N oz true
                  ltac:(intros j [] _ H; unfold Fiber in *; simpl in *; congruence))).
  exact NB.
Qed.

(* ============================================================================================ *)
(* Part 10. The classification, in one statement: each instance as a lasso witness or its       *)
(* absence.                                                                                     *)
(*   negation cycle           bad non-singleton fair lasso, bad for every canonical target      *)
(*   flip2 fair livelock      bad fair lasso although the repair has one fixed point            *)
(*   copyback ghost           settled singleton lasso in the wrong canonical fiber              *)
(*   good monotone resolver   no bad fair lasso for slfp, from every start                      *)
(*   several fixed points     several singleton fair recurrent classes reachable: C2 holds,     *)
(*                            every canonical target has a bad lasso                            *)
(*   semantic oscillation     bad raw lasso, no bad canonical lasso                             *)
(* ============================================================================================ *)

Theorem lasso_classification :
  (forall c, BadCanonLasso SS2 js2 (rupd2 neg_F) SS2 (fun s => s) (false, false) c) /\
  BadLasso Fl fjs2 (fu2 tt) (Stable Fl (fu2 tt) fjs2) fa /\
  (FairSettles SS2 js2 (rupd2 cb_F) (Stable SS2 (rupd2 cb_F) js2) (true, true) /\
   BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse)) /\
  (forall h0, ~ BadCanonLasso SS2 js2 (rupd2 nc_F) SS2 (fun s => s) h0 (true, false)) /\
  (FairSettles SS2 js2 (rupd2 cb_F) (Stable SS2 (rupd2 cb_F) js2) (false, true) /\
   forall c, BadCanonLasso SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (false, true) c) /\
  (BadLasso Osc osc_js osc_u (Stable Osc osc_u osc_js) oz /\
   ~ BadCanonLasso Osc osc_js osc_u bool osc_N oz true).
Proof.
  destruct class_negation_cycle as (_ & _ & _ & N1 & _).
  destruct flip2_fair_lasso as (_ & _ & _ & _ & _ & F1 & _).
  destruct copyback_ghost_lasso as (_ & _ & G1 & _ & G2 & _).
  destruct class_multiple_fixed_points as (_ & _ & _ & _ & M1 & M2 & _).
  destruct semantic_oscillation as (_ & _ & _ & _ & S1 & _ & S2 & _).
  split; [exact N1 | split; [exact F1 | split; [split; [exact G1 | exact G2] | split]]].
  - intro h0. exact (proj2 (class_good_resolver h0)).
  - split; [split; [exact M1 | exact M2] | split; [exact S1 | exact S2]].
Qed.
