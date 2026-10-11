(* SelfStabilization.v: a preregistered external-recovery experiment. Axiom-free.

   Question. The framework's layer C (CanonicalRecurrence.v) and its A-C interface
   (LayerInterfaces.v) were built to recover results proved in this repository. Can they, FROZEN
   (no existing .v file is edited), recover a well-known theorem proved outside it: Dijkstra's
   self-stabilization (E. W. Dijkstra, "Self-stabilizing systems in spite of distributed control",
   Communications of the ACM 17(11):643-644, 1974)?

   Definitions follow the standard textbook treatment (S. Dolev, "Self-Stabilization", MIT Press,
   2000, ch. 2): a system is self-stabilizing for a legitimate set L if (closure) every step from L
   stays in L and (convergence) every execution from every state reaches L. Executions are chosen by
   a daemon. The kernel's runs (DistributedCycles.prs) apply one label per step, so every statement
   below is for the CENTRAL daemon. Two daemons are covered:
   - fair central daemon: the schedules of DistributedCycles.Fair (every step names a machine of js,
     every machine is named infinitely often; naming a machine that is not privileged is a no-op
     step). A continuously privileged machine is therefore eventually moved (weak fairness).
   - unfair central daemon: any sequence of real moves ("regardless of which enabled move is
     chosen", Dijkstra 1974), as LayerInterfaces.LStep. Convergence is strong normalization of the
     moves made outside L (UnfairStab below).
   The distributed daemon (several machines moving in one step) is not covered.

   Part 1 (target 1, generic). For a finite system and a decidable L closed under every step:
     stab_fair_from:   every fair run from s0 eventually stays in L iff no fair lasso from s0 has a
                       loop state outside L. One line: CanonicalRecurrence.C1_closed with the
                       observation N := Lb : X -> bool and the target true.
     stab_fair_exact:  self-stabilization under the fair daemon (closure and convergence from every
                       state) iff closure and no fair loop has a state outside L.
   Part 2 (target 3, generic). The unfair central daemon through the frozen A-C interface:
     unfair_no_loop:   (LayerInterfaces.sn_iff_no_loop) unfair convergence from s0 iff no reachable
                       moving loop outside L.
     unfair_exact:     a consequence of LayerInterfaces.fair_sn_exact, for L closed and no
                       deadlock outside L:
                       unfair convergence from s0 iff fair convergence from s0 and no reachable loop
                       outside L that starves a machine.
     Both are stated on the L-frozen system uL j x := if Lb x then x else u j x, whose moves are
     the moves made outside L. This adapter is generic but is not in the kernels (reported as a
     leak in coq/README.md).
   Part 3 (target 2). Dijkstra's K-state token ring on lists: rstep, legb ("exactly one
   privilege"), and ring_closed (closure). The core, shared by both daemons, is Dijkstra's
   fresh-value argument on a returning trace: core_leg (if the bottom moves somewhere in a run
   that returns to its start, and K >= n, the start is legitimate). fair_fires: in a fair loop
   the bottom moves. unfair_fires: in a loop of real moves the bottom moves.
   Part 4. The ring as a finite system RX n K (lists of length n with values below K, listed by
   rxs), with ring_closure and ring_no_deadlock (some machine is always privileged).
   Part 5 (target 2). For every n >= 2 and K >= n:
     ring_no_bad_lasso, ring_fair_selfstab   fair central daemon, through stab_fair_from (C1_closed).
     ring_unfair_selfstab                    unfair central daemon, through unfair_no_loop
                                             (sn_iff_no_loop): the setting of Dijkstra 1974.
     ring_no_starved_loop                    the same through unfair_exact (fair_sn_exact).
   Part 6. ring_bound_matters: n = 4, K = 2 has a bad fair lasso, so neither daemon stabilizes.
   ring3_nonvacuous: n = K = 3, an illegitimate start that both results cover.
   The bound. This file proves the K >= n condition (n = number of machines). Dijkstra's 1974
   paper (EWD426) numbers the machines 0..N; its condition K > N is K >= n here, and its Note 1
   says K >= N suffices under a central daemon, which is K >= n - 1 here. Fokkink, Hoepman and
   Pang (Nordic Journal of Computing 12(1), 2005) later gave a formal proof and showed that bound
   is sharp. That bound is not proved here.
   Not covered: the distributed daemon; Dijkstra's further conditions on L (every privilege occurs
   in some legitimate state, legitimate states are mutually reachable). *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Logic.Eqdep_dec.
Require Import NC.Newman NC.DistributedCycles NC.CanonicalRecurrence NC.LayerInterfaces.
Require NC.GovernanceWFConverse.
Import ListNotations.

(* ============================================================================================ *)
(* Part 1. Self-stabilization under the fair central daemon is C1 on the fiber of L.            *)
(* ============================================================================================ *)

(* ----- word lemmas used by both daemons (any system) ----- *)

Section Words.
  Variable X : Type.
  Variable u : nat -> X -> X.

  Lemma wrun_firstn_S : forall q x k, k < length q ->
    wrun X u (firstn (S k) q) x = u (nth k q 0) (wrun X u (firstn k q) x).
  Proof. intros q x k Hk. rewrite firstn_snoc by exact Hk. rewrite wrun_app. reflexivity. Qed.

  Lemma wrun_skipn : forall q x k, wrun X u (skipn k q) (wrun X u (firstn k q) x) = wrun X u q x.
  Proof. intros q x k. rewrite <- wrun_app, firstn_skipn. reflexivity. Qed.

  Lemma path_skipn : forall js k w, Path js w -> Path js (skipn k w).
  Proof.
    intros js k. induction k as [| k IH]; intros w Hw; [exact Hw |].
    destruct w as [| a w]; [constructor |]. inversion Hw; subst. apply IH. assumption.
  Qed.

  Lemma path_nth : forall js w k, Path js w -> k < length w -> In (nth k w 0) js.
  Proof. intros js w k Hw Hk. exact (proj1 (Forall_forall _ w) Hw _ (nth_In w 0 Hk)). Qed.
End Words.

Section Stab.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable xs : list X.
  Hypothesis xs_full : forall x, In x xs.
  Variable js : list nat.
  Variable u : nat -> X -> X.
  Variable Lb : X -> bool.

  (* The legitimate set, as the fiber of the observation Lb over true. *)
  Definition Legit (x : X) : Prop := Lb x = true.

  (* Self-stabilization under the fair central daemon (Dolev 2000, ch. 2). *)
  Definition FairSelfStab : Prop := Closed X js u Legit /\ forall s0, FairSettles X js u Legit s0.

  (* Target 1, from one start. Kernel theorem used: C1_closed (nothing else). *)
  Theorem stab_fair_from : Closed X js u Legit -> forall s0,
    FairSettles X js u Legit s0 <-> ~ BadLasso X js u Legit s0.
  Proof. intros Hc s0. exact (C1_closed X X_eq_dec xs xs_full js u bool Bool.bool_dec Lb s0 true Hc). Qed.

  (* A bad lasso from some start is a bad fair loop (take the loop base as the start). *)
  Lemma bad_loop_iff : (exists s0, BadLasso X js u Legit s0) <->
    exists x q y, FairLasso X js u x x [] q /\ OnLoop X u x q y /\ ~ Legit y.
  Proof.
    split.
    - intros (s0 & x & p & q & y & (Hp & Ep & Hq & Pq & Eq & Hall) & Hy & Ny).
      exists x, q, y. split; [| split; assumption].
      split; [constructor | split; [reflexivity | tauto]].
    - intros (x & q & y & HL & Hy & Ny). exists x, x, [], q, y. tauto.
  Qed.

  (* Target 1: self-stabilization under the fair daemon iff closure and no fair loop leaves L. *)
  Theorem stab_fair_exact : FairSelfStab <-> Closed X js u Legit /\
    forall x q y, FairLasso X js u x x [] q -> OnLoop X u x q y -> Legit y.
  Proof.
    split.
    - intros [Hc Hs]. split; [exact Hc |]. intros x q y HL Hy.
      destruct (Bool.bool_dec (Lb y) true) as [E | E]; [exact E |]. exfalso.
      apply (proj1 (stab_fair_from Hc x) (Hs x)). exists x, [], q, y. tauto.
    - intros [Hc H]. split; [exact Hc |]. intros s0. apply (stab_fair_from Hc). intros HB.
      destruct (proj1 bad_loop_iff (ex_intro _ s0 HB)) as (x & q & y & HL & Hy & Ny).
      exact (Ny (H x q y HL Hy)).
  Qed.

  (* ========================================================================================== *)
  (* Part 2. The unfair central daemon through the A-C interface.                               *)
  (* ========================================================================================== *)

  (* The L-frozen system: its moves are exactly the moves of u made outside L. *)
  Definition uL (j : nat) (x : X) : X := if Lb x then x else u j x.

  (* Convergence under an arbitrary central daemon: every sequence of moves from s0 made outside
     L is finite. *)
  Definition UnfairStab (s0 : X) : Prop := SN (LStep X js uL) s0.

  (* No deadlock outside L: every illegitimate state has an enabled move. *)
  Definition NoDeadlock : Prop := forall x, ~ Legit x -> exists j, In j js /\ u j x <> x.

  Lemma uL_in : forall j x, Lb x = true -> uL j x = x.
  Proof. intros j x H. unfold uL. rewrite H. reflexivity. Qed.

  Lemma uL_out : forall j x, Lb x = false -> uL j x = u j x.
  Proof. intros j x H. unfold uL. rewrite H. reflexivity. Qed.

  Lemma lstep_uL : forall x y, LStep X js uL x y <-> ~ Legit x /\ LStep X js u x y.
  Proof.
    intros x y. unfold LStep, uL, Legit. destruct (Lb x).
    - split; [intros (j & _ & E & Ne); congruence | intros [H _]; congruence].
    - split; [intros H; split; [discriminate | exact H] | intros [_ H]; exact H].
  Qed.

  (* Target 3, form 1. Kernel theorem used: sn_iff_no_loop. *)
  Theorem unfair_no_loop : forall s0, UnfairStab s0 <-> ~ LoopFrom X js uL s0.
  Proof. intros s0. exact (sn_iff_no_loop X X_eq_dec js uL xs xs_full s0). Qed.

  (* Runs of u and of uL agree until L is reached, and both stay in L afterwards. *)
  Lemma prs_uL : Closed X js u Legit -> forall sg, (forall n, In (sg n) js) -> forall s0 n,
    (Legit (prs X uL sg n s0) /\ Legit (prs X u sg n s0)) \/ prs X uL sg n s0 = prs X u sg n s0.
  Proof.
    intros Hc sg Hin s0 n. induction n as [| n [[A B] | E]]; [right; reflexivity | |]; cbn [prs].
    - left. split; [rewrite uL_in by exact A; exact A | apply Hc; [apply Hin | exact B]].
    - rewrite E. destruct (Lb (prs X u sg n s0)) eqn:L.
      + left. rewrite uL_in by exact L. split; [exact L | apply Hc; [apply Hin | exact L]].
      + right. apply uL_out. exact L.
  Qed.

  Lemma fair_uL : Closed X js u Legit -> forall s0, FairSettles X js u Legit s0 ->
    FairSettles X js uL (Stable X uL js) s0.
  Proof.
    intros Hc s0 H sg Hf. destruct (H sg Hf) as [N HN]. exists N. intros n Hn.
    assert (Lg : Legit (prs X uL sg n s0)).
    { destruct (prs_uL Hc sg (proj1 Hf) s0 n) as [[A _] | E]; [exact A | rewrite E; exact (HN n Hn)]. }
    intros j _. apply uL_in. exact Lg.
  Qed.

  Lemma closed_wrun : forall G, Closed X js u G -> forall w z, Path js w -> G z -> G (wrun X u w z).
  Proof.
    intros G Hc w. induction w as [| a w IH]; intros z Hw Gz; [exact Gz |].
    inversion Hw as [| ? ? Ha Hw']; subst. apply IH; [exact Hw' | apply Hc; assumption].
  Qed.

  (* Along a word whose u-run ends outside L, the frozen run is the u-run. *)
  Lemma wrun_uL : Closed X js u Legit -> forall w z, Path js w -> ~ Legit (wrun X u w z) ->
    wrun X uL w z = wrun X u w z.
  Proof.
    intros Hc w. induction w as [| a w IH]; intros z Hw Nz; [reflexivity |].
    inversion Hw as [| ? ? Ha Hw']; subst. change (wrun X uL w (uL a z) = wrun X u w (u a z)).
    destruct (Lb z) eqn:L.
    - exfalso. apply Nz. apply (closed_wrun Legit Hc); [constructor; assumption | exact L].
    - rewrite uL_out by exact L. apply IH; [exact Hw' | exact Nz].
  Qed.

  (* A bad fair lasso of u from s0 gives a reachable cycle of moves outside L. *)
  Lemma bad_lasso_cycle : Closed X js u Legit -> NoDeadlock -> forall s0,
    BadLasso X js u Legit s0 -> ~ UnfairStab s0.
  Proof.
    intros Hc Hd s0 (x & p & q & y & (Hp & Ep & Hq & Pq & Eq & Hall) & (k0 & Hk0 & Ey) & Ny) Hsn.
    set (ys k := wrun X u (firstn k q) x).
    assert (Nx : ~ Legit x).
    { intro Lx. apply Ny. rewrite <- Ey. apply (closed_wrun Legit Hc); [apply path_firstn; exact Pq | exact Lx]. }
    assert (Nys : forall k, ~ Legit (ys k)).
    { intros k Lk. apply Nx. rewrite <- Eq, <- (wrun_skipn X u q x k).
      apply (closed_wrun Legit Hc); [apply path_skipn; exact Pq | exact Lk]. }
    assert (Lq : 0 < length q) by (destruct q; [congruence | simpl; lia]).
    destruct (bsearch (fun k => u (nth k q 0) (ys k) <> ys k)
                (fun k => match X_eq_dec (u (nth k q 0) (ys k)) (ys k) with
                          | left E => or_intror (fun H => H E) | right E => or_introl E end) (length q))
      as [[k [Hk Mk]] | Hno].
    - assert (Sk : ys (S k) = u (nth k q 0) (ys k)) by (apply wrun_firstn_S; exact Hk).
      assert (St : LStep X js uL (ys k) (ys (S k))).
      { apply lstep_uL. split; [apply Nys |]. exists (nth k q 0).
        split; [apply path_nth; assumption | split; [symmetry; exact Sk | rewrite Sk; exact Mk]]. }
      assert (Back : star (LStep X js uL) (ys (S k)) (ys k)).
      { eapply star_trans.
        - apply (wrun_star X X_eq_dec js uL (skipn (S k) q) (ys (S k))). apply path_skipn. exact Pq.
        - unfold ys at 1. rewrite (wrun_uL Hc) by (try (apply path_skipn; exact Pq); rewrite wrun_skipn, Eq; exact Nx).
          rewrite wrun_skipn, Eq. pose proof (wrun_star X X_eq_dec js uL (firstn k q) x (path_firstn _ k q Pq)) as H.
          rewrite (wrun_uL Hc) in H by (try (apply path_firstn; exact Pq); apply Nys). exact H. }
      assert (Reach : star (LStep X js uL) s0 (ys k)).
      { eapply star_trans; [apply (wrun_star X X_eq_dec js uL p s0 Hp) |].
        rewrite (wrun_uL Hc) by (try exact Hp; rewrite Ep; exact Nx). rewrite Ep.
        pose proof (wrun_star X X_eq_dec js uL (firstn k q) x (path_firstn _ k q Pq)) as H.
        rewrite (wrun_uL Hc) in H by (try (apply path_firstn; exact Pq); apply Nys). exact H. }
      exact (sn_no_cycle _ _ (GovernanceWFConverse.SN_star_closed _ _ _ Reach Hsn) _ St Back).
    - assert (Fix : forall k, k <= length q -> ys k = x).
      { intros k. induction k as [| k IH]; intros Hk; [reflexivity |].
        rewrite <- (IH ltac:(lia)). unfold ys at 1. rewrite wrun_firstn_S by lia.
        destruct (X_eq_dec (u (nth k q 0) (ys k)) (ys k)) as [E | E]; [exact E |].
        exfalso. exact (Hno k ltac:(lia) E). }
      destruct (Hd x Nx) as [j [Hj Mj]]. apply Mj.
      destruct (In_nth q j 0 (Hall j Hj)) as [k [Hk <-]].
      rewrite <- (Fix k) at 1 2 by lia. destruct (X_eq_dec (u (nth k q 0) (ys k)) (ys k)) as [E | E]; [exact E |].
      exfalso. exact (Hno k Hk E).
  Qed.

  (* Target 3, form 2. Kernel theorems used: C1_closed (through stab_fair_from), sn_iff_no_loop,
     fair_sn_exact. Unfair convergence is fair convergence plus no reachable starved loop. *)
  Theorem unfair_exact : Closed X js u Legit -> NoDeadlock -> forall s0,
    UnfairStab s0 <-> FairSettles X js u Legit s0 /\ ~ StarvedLoop X js uL s0.
  Proof.
    intros Hc Hd s0. split.
    - intros H. split.
      + apply (stab_fair_from Hc). intro HB. exact (bad_lasso_cycle Hc Hd s0 HB H).
      + intros (p & q & j & Hp & HL & _). apply (proj1 (unfair_no_loop s0) H). exists p, q. tauto.
    - intros [Hf Hn]. apply (proj2 (fair_sn_exact X X_eq_dec js uL xs xs_full s0 (fair_uL Hc s0 Hf))).
      exact Hn.
  Qed.
End Stab.

(* ============================================================================================ *)
(* Part 3. Dijkstra's K-state token ring (Dijkstra 1974, the K-state solution).                 *)
(* Machines 0..n-1 in a ring, each holding a value below K. Machine 0 (the bottom) is privileged *)
(* iff its value equals that of machine n-1, and its move increments its value modulo K; a       *)
(* machine i > 0 is privileged iff its value differs from that of machine i-1, and its move      *)
(* copies that value. Legitimate: exactly one machine is privileged. The raw dynamics act on     *)
(* lists; Part 5 packages them as a finite state type.                                          *)
(* ============================================================================================ *)

Section Ring.
  Variable n K : nat.

  Definition get (y : list nat) (i : nat) : nat := nth i y 0.
  Definition priv (y : list nat) (i : nat) : bool :=
    match i with
    | 0 => Nat.eqb (get y 0) (get y (n - 1))
    | S i' => negb (Nat.eqb (get y (S i')) (get y i'))
    end.
  Definition inc (a : nat) : nat := if Nat.eqb (S a) K then 0 else S a.
  Definition newv (y : list nat) (i : nat) : nat :=
    match i with 0 => inc (get y 0) | S i' => get y i' end.
  (* The move of machine j: a no-op unless j is a privileged machine. *)
  Definition rstep (j : nat) (y : list nat) : list nat :=
    if Nat.ltb j n && priv y j then map (fun i => if Nat.eqb i j then newv y j else get y i) (seq 0 n)
    else y.
  (* Legitimate: exactly one privileged machine. *)
  Definition legb (y : list nat) : bool := Nat.eqb (length (filter (priv y) (seq 0 n))) 1.
  Definition Leg (y : list nat) : Prop :=
    exists i, i < n /\ priv y i = true /\ forall k, k < n -> priv y k = true -> k = i.

  (* ----- reading a move ----- *)

  Lemma nth_map_seq : forall (f : nat -> nat) m i, i < m -> nth i (map f (seq 0 m)) 0 = f i.
  Proof.
    intros f m i Hi. rewrite (nth_indep _ 0 (f 0)) by (rewrite map_length, seq_length; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. reflexivity.
  Qed.

  Lemma rstep_idle : forall j y, Nat.ltb j n && priv y j = false -> rstep j y = y.
  Proof. intros j y H. unfold rstep. rewrite H. reflexivity. Qed.

  Lemma rstep_moves : forall j y, j < n -> priv y j = true ->
    forall i, i < n -> get (rstep j y) i = if Nat.eqb i j then newv y j else get y i.
  Proof.
    intros j y Hj Hp i Hi. unfold rstep. rewrite (proj2 (Nat.ltb_lt j n) Hj), Hp. simpl.
    unfold get at 1. apply nth_map_seq. exact Hi.
  Qed.

  (* Every position other than the mover keeps its value. *)
  Lemma rstep_other : forall j y i, i < n -> i <> j -> get (rstep j y) i = get y i.
  Proof.
    intros j y i Hi Ne. destruct (Nat.ltb j n && priv y j) eqn:E.
    - apply andb_true_iff in E. destruct E as [E1 E2]. apply Nat.ltb_lt in E1.
      rewrite (rstep_moves j y E1 E2 i Hi). destruct (Nat.eqb_spec i j); [contradiction | reflexivity].
    - rewrite (rstep_idle j y E). reflexivity.
  Qed.

  Lemma rstep_self : forall j y, j < n ->
    get (rstep j y) j = if priv y j then newv y j else get y j.
  Proof.
    intros j y Hj. destruct (priv y j) eqn:P.
    - rewrite (rstep_moves j y Hj P j Hj), Nat.eqb_refl. reflexivity.
    - rewrite rstep_idle; [reflexivity | rewrite P, andb_false_r; reflexivity].
  Qed.

  Lemma priv0_iff : forall y, priv y 0 = true <-> get y 0 = get y (n - 1).
  Proof. intros y. simpl. apply Nat.eqb_eq. Qed.

  Lemma privS_iff : forall y i, priv y (S i) = false <-> get y (S i) = get y i.
  Proof.
    intros y i. simpl. destruct (Nat.eqb_spec (get y (S i)) (get y i)); simpl; split; congruence.
  Qed.

  Lemma privS_true : forall y i, priv y (S i) = true <-> get y (S i) <> get y i.
  Proof.
    intros y i. simpl. destruct (Nat.eqb_spec (get y (S i)) (get y i)); simpl; split; congruence.
  Qed.

  Lemma inc_lt : 0 < K -> forall a, inc a < K \/ a >= K.
  Proof. intros HK a. unfold inc. destruct (Nat.eqb_spec (S a) K); lia. Qed.

  Lemma inc_bound : 0 < K -> forall a, a < K -> inc a < K.
  Proof. intros HK a Ha. unfold inc. destruct (Nat.eqb_spec (S a) K); lia. Qed.

  Lemma inc_ne : 2 <= K -> forall a, a < K -> inc a <> a.
  Proof. intros HK a Ha. unfold inc. destruct (Nat.eqb_spec (S a) K); lia. Qed.

  (* ----- exactly one privilege ----- *)

  Lemma count0 : forall (f : nat -> bool) m, length (filter f (seq 0 m)) = 0 -> forall k, k < m -> f k = false.
  Proof.
    intros f m H k Hk. destruct (f k) eqn:E; [| reflexivity]. exfalso.
    assert (I : In k (filter f (seq 0 m))) by (apply filter_In; split; [apply in_seq; lia | exact E]).
    destruct (filter f (seq 0 m)); [destruct I | discriminate].
  Qed.

  Lemma count0_back : forall (f : nat -> bool) m, (forall k, k < m -> f k = false) -> length (filter f (seq 0 m)) = 0.
  Proof.
    intros f m H. destruct (filter f (seq 0 m)) as [| a l] eqn:E; [reflexivity |].
    assert (I : In a (filter f (seq 0 m))) by (rewrite E; left; reflexivity).
    apply filter_In in I. destruct I as [I Fa]. apply in_seq in I. rewrite (H a ltac:(lia)) in Fa. discriminate.
  Qed.

  Lemma count1 : forall (f : nat -> bool) m, length (filter f (seq 0 m)) = 1 <->
    exists i, i < m /\ f i = true /\ forall k, k < m -> f k = true -> k = i.
  Proof.
    intros f m. induction m as [| m IH].
    - simpl. split; [discriminate | intros (i & Hi & _); lia].
    - rewrite seq_S, filter_app, app_length. simpl. destruct (f m) eqn:Fm; simpl.
      + split.
        * intros H. exists m. split; [lia | split; [exact Fm |]]. intros k Hk Fk.
          destruct (Nat.eq_dec k m) as [-> | Ne]; [reflexivity |].
          rewrite (count0 f m ltac:(lia) k ltac:(lia)) in Fk. discriminate.
        * intros (i & Hi & Fi & U). rewrite (count0_back f m); [reflexivity |].
          intros k Hk. destruct (f k) eqn:Fk; [| reflexivity]. pose proof (U k ltac:(lia) Fk).
          pose proof (U m ltac:(lia) Fm). lia.
      + rewrite Nat.add_0_r. rewrite IH. split.
        * intros (i & Hi & Fi & U). exists i. split; [lia | split; [exact Fi |]]. intros k Hk Fk.
          destruct (Nat.eq_dec k m) as [-> | Ne]; [congruence | apply U; [lia | exact Fk]].
        * intros (i & Hi & Fi & U). exists i.
          assert (i <> m) by (intro E; subst; congruence).
          split; [lia | split; [exact Fi |]]. intros k Hk Fk. apply U; [lia | exact Fk].
  Qed.

  Lemma legb_iff : forall y, legb y = true <-> Leg y.
  Proof. intros y. unfold legb. rewrite Nat.eqb_eq. apply count1. Qed.

  (* All machines equal: exactly machine 0 is privileged. *)
  Lemma all_eq_leg : 2 <= n -> forall y c, (forall i, i < n -> get y i = c) -> Leg y.
  Proof.
    intros Hn y c H. exists 0. split; [lia |]. split; [apply priv0_iff; rewrite !H by lia; reflexivity |].
    intros [| k] Hk P; [reflexivity |]. exfalso. apply privS_true in P. apply P. rewrite !H by lia. reflexivity.
  Qed.

  (* A run of unprivileged machines 1..m-1 carries one value. *)
  Lemma chain_down : forall y m, (forall k, S k < m -> get y (S k) = get y k) ->
    forall k, k < m -> get y k = get y 0.
  Proof.
    intros y m H k. induction k as [| k IH]; intros Hk; [reflexivity |]. rewrite H by lia. apply IH. lia.
  Qed.

  Lemma chain_up : forall y a m, (forall k, a <= k -> S k < m -> get y (S k) = get y k) ->
    forall d, a + d < m -> get y (a + d) = get y a.
  Proof.
    intros y a m H d. induction d as [| d IH]; intros Hd; [rewrite Nat.add_0_r; reflexivity |].
    replace (a + S d) with (S (a + d)) by lia. rewrite H by lia. apply IH. lia.
  Qed.
  (* ----- closure: a legitimate state steps to a legitimate state ----- *)

  Theorem ring_closed : 2 <= n -> 2 <= K -> forall j y, get y 0 < K -> Leg y -> Leg (rstep j y).
  Proof.
    intros Hn HK j y Hy0 (i & Hi & Pi & U).
    destruct (Nat.ltb j n && priv y j) eqn:E; [| rewrite rstep_idle by exact E; exists i; tauto].
    apply andb_true_iff in E. destruct E as [Ej Pj]. apply Nat.ltb_lt in Ej.
    pose proof (U j Ej Pj) as ->.
    (* unprivileged machines k >= 1, k <> i, copy their left neighbour already *)
    assert (Cp : forall k, S k < n -> S k <> i -> get y (S k) = get y k).
    { intros k Hk Ne. apply privS_iff. destruct (priv y (S k)) eqn:P; [| reflexivity].
      exfalso. exact (Ne (U _ Hk P)). }
    pose proof (rstep_moves i y Hi Pi) as M.
    destruct i as [| i].
    - (* the bottom moves: all equal c before, only machine 1 privileged after *)
      set (c := get y 0) in *.
      assert (All : forall k, k < n -> get y k = c) by (apply chain_down; intros k Hk; apply Cp; lia).
      assert (Ic : inc c <> c) by (apply inc_ne; assumption).
      assert (G0 : get (rstep 0 y) 0 = inc c) by (rewrite (M 0) by lia; reflexivity).
      assert (Gk : forall k, 0 < k -> k < n -> get (rstep 0 y) k = c).
      { intros k Hk0 Hk. rewrite (M k Hk). destruct (Nat.eqb_spec k 0); [lia | apply All; exact Hk]. }
      exists 1. split; [lia | split].
      + apply privS_true. rewrite G0, Gk by lia. intro H; apply Ic; symmetry; exact H.
      + intros [| [| k]] Hk P; [| reflexivity |].
        * apply priv0_iff in P. rewrite G0, Gk in P by lia. contradiction.
        * apply privS_true in P. rewrite !Gk in P by lia. contradiction.
    - (* machine S i moves: values a^(S i) b^(n - S i) with a <> b *)
      set (a := get y 0) in *.
      assert (Lo : forall k, k <= i -> get y k = a).
      { intros k Hk. apply (chain_down y (S i)); [intros k' Hk'; apply Cp; lia | lia]. }
      assert (Hi' : get y (S i) <> get y i) by (apply privS_true; exact Pi).
      assert (Hp0 : get y 0 <> get y (n - 1)).
      { intro E. assert (P0 : priv y 0 = true) by (apply priv0_iff; exact E). pose proof (U 0 ltac:(lia) P0). lia. }
      assert (Up : forall d, S i + d < n -> get y (S i + d) = get y (S i)).
      { apply chain_up. intros k Hk Hk'. apply Cp; lia. }
      assert (GS : get (rstep (S i) y) (S i) = a).
      { rewrite (M (S i) Hi), Nat.eqb_refl. simpl. apply Lo. lia. }
      assert (Go : forall k, k < n -> k <> S i -> get (rstep (S i) y) k = get y k).
      { intros k Hk Ne. rewrite (M k Hk). destruct (Nat.eqb_spec k (S i)); [contradiction | reflexivity]. }
      destruct (Nat.eq_dec (S i) (n - 1)) as [Last | NLast].
      + (* the last machine copies: all equal a, only the bottom privileged *)
        apply (all_eq_leg Hn _ a). intros k Hk. destruct (Nat.eq_dec k (S i)) as [-> | Ne]; [exact GS |].
        rewrite Go by assumption. apply Lo. lia.
      + assert (Hb : get y (n - 1) = get y (S i)).
        { replace (n - 1) with (S i + (n - 1 - S i)) by lia. apply Up. lia. }
        exists (S (S i)). split; [lia | split].
        * apply privS_true. rewrite GS, Go by lia. rewrite Cp by lia. rewrite (Lo i (le_n i)) in Hi'. exact Hi'.
        * intros [| k] Hk P.
          -- exfalso. apply priv0_iff in P. rewrite !Go in P by lia. rewrite Hb in P. fold a in P.
             rewrite (Lo i (le_n i)) in Hi'. apply Hi'. symmetry. exact P.
          -- apply privS_true in P. destruct (Nat.lt_ge_cases k i) as [Lt | Ge].
             ++ exfalso. apply P. rewrite !Go by lia. rewrite !Lo by lia. reflexivity.
             ++ destruct (Nat.eq_dec k i) as [-> | Nki]; [exfalso; apply P; rewrite GS, Go by lia; symmetry; apply Lo; lia |].
                destruct (Nat.eq_dec k (S i)) as [-> | Nks]; [reflexivity |].
                exfalso. apply P. rewrite !Go by lia. apply Cp; lia.
  Qed.
  (* ----- the fresh value v: absent from machines 1..n-1, then propagated as a prefix ----- *)

  Definition Absent (v : nat) (y : list nat) : Prop := forall i, 0 < i -> i < n -> get y i <> v.
  Definition Pre (v : nat) (y : list nat) : Prop :=
    get y 0 = v /\ forall i k, i <= k -> k < n -> get y k = v -> get y i = v.
  (* Moves of the bottom still needed to reach v. *)
  Definition dist (v c : nat) : nat := if Nat.leb c v then v - c else v + K - c.
  (* Legitimate, or v spreading as a prefix from the bottom, or v absent and the bottom at most D
     moves away from it. *)
  Definition Good (v D : nat) (y : list nat) : Prop :=
    get y 0 < K /\ (Leg y \/ Pre v y \/ (Absent v y /\ get y 0 <> v /\ dist v (get y 0) <= D)).

  Lemma keep0 : forall j y, j <> 0 \/ priv y 0 = false -> get (rstep j y) 0 = get y 0.
  Proof.
    intros j y H. destruct (Nat.ltb j n && priv y j) eqn:M; [| rewrite rstep_idle by exact M; reflexivity].
    apply andb_true_iff in M. destruct M as [Mj Pj]. apply Nat.ltb_lt in Mj.
    rewrite (rstep_moves j y Mj Pj 0) by lia. destruct (Nat.eqb_spec 0 j) as [<- | Ne]; [| reflexivity].
    destruct H as [H | H]; [contradiction | congruence].
  Qed.

  Lemma ok0_step : 2 <= n -> 0 < K -> forall j y, get y 0 < K -> get (rstep j y) 0 < K.
  Proof.
    intros Hn HK j y H. destruct (Nat.eq_dec j 0) as [-> | Ne]; [| rewrite keep0 by (left; exact Ne); exact H].
    rewrite rstep_self by lia. destruct (priv y 0); [apply inc_bound; assumption | exact H].
  Qed.

  Lemma fresh_pre : forall v y, Absent v y -> get y 0 = v -> Pre v y.
  Proof.
    intros v y Ab E. split; [exact E |]. intros i k Hik Hk Ek. destruct k as [| k].
    - replace i with 0 by lia. exact E.
    - exfalso. exact (Ab (S k) ltac:(lia) Hk Ek).
  Qed.

  Lemma pre_fire : 2 <= n -> forall v y, Pre v y -> priv y 0 = true -> Leg y.
  Proof.
    intros Hn v y [E0 Pf] P. apply priv0_iff in P. apply (all_eq_leg Hn y v). intros i Hi.
    apply (Pf i (n - 1)); [lia | lia | congruence].
  Qed.

  (* A copy move keeps the prefix shape. *)
  Lemma pre_step : forall v j y, Pre v y -> j <> 0 \/ priv y 0 = false -> Pre v (rstep j y).
  Proof.
    intros v j y [E0 Pf] Hj.
    assert (Tail : forall t s, t <= s -> s < n -> get y t <> v -> get y s <> v).
    { intros t s Hts Hs Nt Es. exact (Nt (Pf t s Hts Hs Es)). }
    destruct (Nat.ltb j n && priv y j) eqn:M; [| rewrite rstep_idle by exact M; split; assumption].
    apply andb_true_iff in M. destruct M as [Mj Pj]. apply Nat.ltb_lt in Mj.
    destruct j as [| j]; [destruct Hj as [Hj | Hj]; [lia | congruence] |].
    pose proof (rstep_moves (S j) y Mj Pj) as G. apply privS_true in Pj.
    assert (Go : forall t, t < n -> t <> S j -> get (rstep (S j) y) t = get y t).
    { intros t Ht Ne. rewrite (G t Ht). destruct (Nat.eqb_spec t (S j)); [contradiction | reflexivity]. }
    assert (GS : get (rstep (S j) y) (S j) = get y j) by (rewrite (G (S j) Mj), Nat.eqb_refl; reflexivity).
    split; [rewrite Go by lia; exact E0 |]. intros i k Hik Hk Ek.
    destruct (Nat.eq_dec (get y j) v) as [Ej | Nj].
    - assert (NS : get y (S j) <> v) by congruence.
      destruct (Nat.eq_dec k (S j)) as [-> | Nk].
      + destruct (Nat.eq_dec i (S j)) as [-> | Ni]; [exact Ek |].
        rewrite Go by lia. apply (Pf i j); [lia | lia | exact Ej].
      + rewrite Go in Ek by lia. assert (k < S j).
        { destruct (Nat.lt_ge_cases k (S j)) as [L | L]; [exact L |]. exfalso. exact (Tail (S j) k L Hk NS Ek). }
        rewrite Go by lia. exact (Pf i k Hik Hk Ek).
    - destruct (Nat.eq_dec k (S j)) as [-> | Nk]; [rewrite GS in Ek; contradiction |].
      rewrite Go in Ek by lia. assert (k < j).
      { destruct (Nat.lt_ge_cases k j) as [L | L]; [exact L |]. exfalso. exact (Tail j k L Hk Nj Ek). }
      rewrite Go by lia. exact (Pf i k Hik Hk Ek).
  Qed.

  Lemma dist_pos : forall v c, c < K -> c <> v -> 0 < dist v c.
  Proof. intros v c Hc Ne. unfold dist. destruct (Nat.leb_spec c v); lia. Qed.

  Lemma dist_inc : forall v c, v < K -> c < K -> c <> v -> inc c <> v -> dist v (inc c) + 1 = dist v c.
  Proof.
    intros v c Hv Hc Nc Ne. unfold inc, dist in *. destruct (Nat.eqb_spec (S c) K) as [E | E].
    - destruct (Nat.leb_spec 0 v); destruct (Nat.leb_spec c v); lia.
    - destruct (Nat.leb_spec (S c) v); destruct (Nat.leb_spec c v); lia.
  Qed.

  (* A move of the bottom from the third stage: v arrives (a fresh value), or the distance drops. *)
  Lemma third_fire : 2 <= n -> forall v y, v < K -> Absent v y -> get y 0 <> v -> get y 0 < K ->
    priv y 0 = true -> Pre v (rstep 0 y) \/
    (Absent v (rstep 0 y) /\ get (rstep 0 y) 0 <> v /\ dist v (get (rstep 0 y) 0) + 1 = dist v (get y 0)).
  Proof.
    intros Hn v y Hv Ab N0 Hy P.
    assert (Ab' : Absent v (rstep 0 y)) by (intros i Hi0 Hi; rewrite rstep_other by lia; apply Ab; assumption).
    assert (G0 : get (rstep 0 y) 0 = inc (get y 0)) by (rewrite rstep_self, P by lia; reflexivity).
    destruct (Nat.eq_dec (inc (get y 0)) v) as [E | E].
    - left. apply fresh_pre; [exact Ab' | rewrite G0; exact E].
    - right. rewrite G0. split; [exact Ab' | split; [exact E | apply dist_inc; assumption]].
  Qed.

  Lemma third_other : forall v j y, Absent v y -> get y 0 <> v -> j <> 0 \/ priv y 0 = false ->
    Absent v (rstep j y) /\ get (rstep j y) 0 = get y 0.
  Proof.
    intros v j y Ab N0 Hj. split; [| apply keep0; exact Hj].
    intros i Hi0 Hi. destruct (Nat.ltb j n && priv y j) eqn:M; [| rewrite rstep_idle by exact M; apply Ab; assumption].
    apply andb_true_iff in M. destruct M as [Mj Pj]. apply Nat.ltb_lt in Mj.
    rewrite (rstep_moves j y Mj Pj i Hi). destruct (Nat.eqb_spec i j) as [-> | Ne]; [| apply Ab; assumption].
    destruct j as [| j]; [lia |]. simpl. destruct j as [| j]; [exact N0 | apply Ab; lia].
  Qed.

  Lemma good_step : 2 <= n -> 2 <= K -> forall v D j y, v < K -> Good v D y -> Good v D (rstep j y).
  Proof.
    intros Hn HK v D j y Hv [Hy [L | [Pr | (Ab & N0 & Dd)]]]; split; try (apply ok0_step; [exact Hn | lia | exact Hy]).
    - left. apply ring_closed; assumption.
    - destruct (Nat.eq_dec j 0) as [-> | Ne]; [destruct (priv y 0) eqn:P |].
      + left. apply ring_closed; try assumption. exact (pre_fire Hn v y Pr P).
      + right; left. apply pre_step; [exact Pr | right; exact P].
      + right; left. apply pre_step; [exact Pr | left; exact Ne].
    - destruct (Nat.eq_dec j 0) as [-> | Ne]; [destruct (priv y 0) eqn:P |].
      + destruct (third_fire Hn v y Hv Ab N0 Hy P) as [Pr | (Ab' & N' & D')]; [right; left; exact Pr |].
        right; right. split; [exact Ab' | split; [exact N' | lia]].
      + destruct (third_other v 0 y Ab N0 (or_intror P)) as [Ab' E]. right; right. rewrite E. tauto.
      + destruct (third_other v j y Ab N0 (or_introl Ne)) as [Ab' E]. right; right. rewrite E. tauto.
  Qed.

  Lemma good_drop : 2 <= n -> 2 <= K -> forall v D y, v < K -> Good v (S D) y -> priv y 0 = true ->
    Good v D (rstep 0 y).
  Proof.
    intros Hn HK v D y Hv [Hy [L | [Pr | (Ab & N0 & Dd)]]] P; split; try (apply ok0_step; [exact Hn | lia | exact Hy]).
    - left. apply ring_closed; assumption.
    - left. apply ring_closed; try assumption. exact (pre_fire Hn v y Pr P).
    - destruct (third_fire Hn v y Hv Ab N0 Hy P) as [Pr | (Ab' & N' & D')]; [right; left; exact Pr |].
      right; right. split; [exact Ab' | split; [exact N' | lia]].
  Qed.

  Lemma fresh_value : forall l : list nat, length l < K -> exists v, v < K /\ ~ In v l.
  Proof.
    intros l Hl.
    destruct (bsearch (fun v => ~ In v l)
                (fun v => match in_dec Nat.eq_dec v l with
                          | left Hi => or_intror (fun H => H Hi) | right Hn => or_introl Hn end) K)
      as [[v [Hv Nv]] | H]; [exists v; tauto |].
    exfalso. assert (Inc : incl (seq 0 K) l).
    { intros v Hv. apply in_seq in Hv. destruct (in_dec Nat.eq_dec v l) as [Hi | Hn]; [exact Hi |].
      exfalso. exact (H v ltac:(lia) Hn). }
    pose proof (NoDup_incl_length (seq_NoDup K 0) Inc) as Le. rewrite seq_length in Le. lia.
  Qed.
  Lemma trace_fwd : forall (P : nat -> Prop) m, (forall k, k < m -> P k -> P (S k)) ->
    forall k1 k2, k1 <= k2 -> k2 <= m -> P k1 -> P k2.
  Proof.
    intros P m H k1 k2 H12. induction H12 as [| k2 H12 IH]; intros H2m P1; [exact P1 |].
    apply H; [lia | apply IH; [lia | exact P1]].
  Qed.

  (* ----- the core: a returning run in which the bottom moves starts legitimate ----- *)

  Section Core.
    (* A trace z 0 -> z 1 -> ... -> z m of moves a 0, ..., a (m-1) that returns to its start. *)
    Variable z : nat -> list nat.
    Variable a : nat -> nat.
    Variable m : nat.
    Hypothesis hz : forall k, k < m -> z (S k) = rstep (a k) (z k).
    Hypothesis hloop : z m = z 0.
    Hypothesis Hn : 2 <= n.
    Hypothesis HnK : n <= K.
    Hypothesis ok0 : get (z 0) 0 < K.

    Lemma tr_closed : forall (Q : list nat -> Prop), (forall j y, Q y -> Q (rstep j y)) ->
      forall k1 k2, k1 <= k2 -> k2 <= m -> Q (z k1) -> Q (z k2).
    Proof.
      intros Q HQ. apply (trace_fwd (fun k => Q (z k)) m). intros k Hk Qk. rewrite hz by exact Hk.
      apply HQ. exact Qk.
    Qed.

    (* Dijkstra's argument (fresh value): if the bottom moves somewhere in the trace, the start
       is legitimate. Uses K >= n to find a value absent from machines 1..n-1. *)
    Theorem core_leg : (exists k, k < m /\ a k = 0 /\ priv (z k) 0 = true) -> Leg (z 0).
    Proof.
      intros (k0 & Hk0 & A0 & P0). assert (HK : 2 <= K) by lia.
      destruct (fresh_value (map (get (z 0)) (seq 1 (n - 1)))) as [v [Hv Nv]];
        [rewrite map_length, seq_length; lia |].
      assert (Ab : Absent v (z 0)).
      { intros i Hi0 Hi E. apply Nv. rewrite <- E. apply in_map. apply in_seq. lia. }
      (* one pass of the trace lowers the stage *)
      assert (Pass : forall D, Good v (S D) (z 0) -> Good v D (z 0)).
      { intros D G. rewrite <- hloop. apply (tr_closed (Good v D) (fun j y => good_step Hn HK v D j y Hv) (S k0));
          [lia | lia |]. rewrite hz, A0 by exact Hk0. apply good_drop; try assumption.
        apply (tr_closed (Good v (S D)) (fun j y => good_step Hn HK v (S D) j y Hv) 0); [lia | lia | exact G]. }
      assert (G0 : Good v 0 (z 0)).
      { assert (Gd : Good v (dist v (get (z 0) 0)) (z 0)).
        { split; [exact ok0 |]. destruct (Nat.eq_dec (get (z 0) 0) v) as [E | E].
          - right; left. apply fresh_pre; assumption.
          - right; right. split; [exact Ab | split; [exact E | lia]]. }
        clear Ab Nv. induction (dist v (get (z 0) 0)) as [| D IH]; [exact Gd | apply IH, Pass, Gd]. }
      (* stage 0 (legitimate or a spreading prefix) is closed; the bottom's move makes it legitimate *)
      assert (Gk : Good v 0 (z k0)).
      { apply (tr_closed (Good v 0) (fun j y => good_step Hn HK v 0 j y Hv) 0); [lia | lia | exact G0]. }
      assert (Lk : get (z k0) 0 < K /\ Leg (z k0)).
      { destruct Gk as [Hy [L | [Pr | (_ & N0 & Dd)]]]; split; try assumption.
        - exact (pre_fire Hn v _ Pr P0).
        - pose proof (dist_pos v _ Hy N0). lia. }
      assert (Lm : get (z m) 0 < K /\ Leg (z m)).
      { apply (tr_closed (fun y => get y 0 < K /\ Leg y)) with (k1 := k0); [| lia | lia | exact Lk].
        intros j y [Hy L]. split; [apply ok0_step; [exact Hn | lia | exact Hy] | apply ring_closed; assumption]. }
      rewrite hloop in Lm. exact (proj2 Lm).
    Qed.
    Lemma fire_dec : forall k, (a k = 0 /\ priv (z k) 0 = true) \/ ~ (a k = 0 /\ priv (z k) 0 = true).
    Proof.
      intros k. destruct (Nat.eq_dec (a k) 0) as [E | E]; [destruct (priv (z k) 0) |].
      - left. split; [exact E | reflexivity].
      - right. intros [_ H]. discriminate.
      - right. intros [H _]. contradiction.
    Qed.

    (* Fair daemon: if every machine is named in the trace, the bottom moves in it. *)
    Lemma fair_fires : (forall j, j < n -> exists k, k < m /\ a k = j) ->
      exists k, k < m /\ a k = 0 /\ priv (z k) 0 = true.
    Proof.
      intros Hall. destruct (bsearch _ fire_dec m) as [H | Hno]; [exact H |]. exfalso.
      set (c := get (z 0) 0).
      set (E i y := forall t, t <= i -> t < n -> get y t = c).
      (* without a move of the bottom, a prefix of machines holding c stays so *)
      assert (St : forall i k, k < m -> E i (z k) -> E i (z (S k))).
      { intros i k Hk Ei t Ht Htn. rewrite hz by exact Hk.
        destruct (Nat.ltb (a k) n && priv (z k) (a k)) eqn:M; [| rewrite rstep_idle by exact M; apply Ei; lia].
        apply andb_true_iff in M. destruct M as [Ma Pa]. apply Nat.ltb_lt in Ma.
        rewrite (rstep_moves (a k) (z k) Ma Pa t Htn). destruct (Nat.eqb_spec t (a k)) as [-> | Ne]; [| apply Ei; lia].
        destruct (a k) as [| j] eqn:Ak; [exfalso; apply (Hno k Hk); split; [exact Ak | exact Pa] |].
        simpl. apply Ei; lia. }
      assert (Back : forall i k, k <= m -> E i (z k) -> E i (z 0)).
      { intros i k Hk Ek. rewrite <- hloop. apply (trace_fwd (fun k => E i (z k)) m (St i) k m); [lia | lia | exact Ek]. }
      assert (Fw : forall i k, k <= m -> E i (z 0) -> E i (z k)).
      { intros i k Hk E0. apply (trace_fwd (fun k => E i (z k)) m (St i) 0 k); [lia | exact Hk | exact E0]. }
      assert (Up : forall i, i < n -> E i (z 0)).
      { induction i as [| i IH]; intros Hi.
        - intros t Ht _. replace t with 0 by lia. reflexivity.
        - destruct (Hall (S i) Hi) as [k1 [Hk1 Ak1]].
          pose proof (Fw i k1 ltac:(lia) (IH ltac:(lia))) as Ek1.
          apply (Back (S i) (S k1)); [lia |]. intros t Ht Htn.
          destruct (Nat.eq_dec t (S i)) as [-> | Ne]; [| apply (St i k1 Hk1 Ek1); lia].
          rewrite hz, Ak1 by exact Hk1. rewrite rstep_self by exact Hi.
          destruct (priv (z k1) (S i)) eqn:P; simpl.
          + apply Ek1; lia.
          + apply privS_iff in P. rewrite P. apply Ek1; lia. }
      destruct (Hall 0 ltac:(lia)) as [k0 [Hk0 Ak0]].
      apply (Hno k0 Hk0). split; [exact Ak0 |]. pose proof (Fw (n - 1) k0 ltac:(lia) (Up (n - 1) ltac:(lia))) as Ek.
      apply priv0_iff. rewrite !Ek by lia. reflexivity.
    Qed.

    (* Unfair daemon: in a nonempty trace of real moves, the bottom moves. *)
    Lemma unfair_fires : 0 < m -> (forall k, k < m -> a k < n /\ priv (z k) (a k) = true) ->
      exists k, k < m /\ a k = 0 /\ priv (z k) 0 = true.
    Proof.
      intros Hm Hmv.
      destruct (bsearch (fun k => a k = 0) (fun k => match Nat.eq_dec (a k) 0 with
                                                    | left E => or_introl E | right E => or_intror E end) m)
        as [[k [Hk Ak]] | Hno].
      - exists k. split; [exact Hk | split; [exact Ak |]]. rewrite <- Ak. apply Hmv. exact Hk.
      - exfalso.
        assert (Mv : forall k t, k < m -> t < n -> get (z (S k)) t = if Nat.eqb t (a k) then newv (z k) (a k) else get (z k) t).
        { intros k t Hk Ht. rewrite hz by exact Hk. destruct (Hmv k Hk) as [Ma Pa]. apply rstep_moves; assumption. }
        set (Const i := forall k, k <= m -> get (z k) i = get (z 0) i).
        assert (C0 : Const 0).
        { intros k Hk. refine (trace_fwd (fun k => get (z k) 0 = get (z 0) 0) m _ 0 k ltac:(lia) Hk eq_refl).
          intros k' Hk' E. rewrite Mv by lia. destruct (Nat.eqb_spec 0 (a k')) as [Ea | _]; [exfalso; apply (Hno k' Hk'); lia | exact E]. }
        assert (CS : forall i, S i < n -> Const i -> Const (S i)).
        { intros i Hi Ci. set (c := get (z 0) i).
          assert (Keep : forall k1 k2, k1 <= k2 -> k2 <= m -> get (z k1) (S i) = c -> get (z k2) (S i) = c).
          { apply (trace_fwd (fun k => get (z k) (S i) = c) m). intros k Hk E. rewrite Mv by lia.
            destruct (Nat.eqb_spec (S i) (a k)) as [Ea | _]; [| exact E].
            rewrite <- Ea. simpl. apply Ci. lia. }
          destruct (Nat.eq_dec (get (z 0) (S i)) c) as [Eb | Nb].
          - intros k Hk. rewrite Eb. apply (Keep 0 k); [lia | exact Hk | exact Eb].
          - intros k Hk. refine (trace_fwd (fun k => get (z k) (S i) = get (z 0) (S i)) m _ 0 k ltac:(lia) Hk eq_refl).
            intros k' Hk' E. rewrite Mv by lia. destruct (Nat.eqb_spec (S i) (a k')) as [Ea | _]; [| exact E].
            exfalso. apply Nb. rewrite <- hloop. apply (Keep (S k') m); [lia | lia |].
            rewrite Mv, <- Ea, Nat.eqb_refl by lia. simpl. apply Ci. lia. }
        assert (Call : forall i, i < n -> Const i).
        { induction i as [| i IH]; intros Hi; [exact C0 | apply CS; [exact Hi | apply IH; lia]]. }
        destruct (Hmv 0 Hm) as [Ma Pa]. destruct (a 0) as [| j] eqn:A0; [exact (Hno 0 Hm A0) |].
        apply privS_true in Pa. apply Pa. rewrite <- (Call (S j) Ma 1) by lia.
        rewrite Mv, A0, Nat.eqb_refl by lia. simpl. symmetry. apply (Call j ltac:(lia) 0). lia.
    Qed.
  End Core.
End Ring.

(* ============================================================================================ *)
(* Part 4. The ring as a finite layer-C system: states are the lists of length n with values     *)
(* below K, the labels are the machines 0..n-1, and Lb tests "exactly one privilege".            *)
(* ============================================================================================ *)

Section RingSystem.
  Variable n K : nat.

  Definition okb (y : list nat) : bool := Nat.eqb (length y) n && forallb (fun c => Nat.ltb c K) y.
  Definition RX : Type := { y : list nat | okb y = true }.

  Lemma okb_get : forall y, okb y = true -> forall i, i < n -> get y i < K.
  Proof.
    intros y H i Hi. apply andb_true_iff in H. destruct H as [L F]. apply Nat.eqb_eq in L.
    rewrite forallb_forall in F. apply Nat.ltb_lt. apply F. unfold get. apply nth_In. lia.
  Qed.

  Lemma rstep_ok : forall j y, okb y = true -> okb (rstep n K j y) = true.
  Proof.
    intros j y H. destruct (Nat.ltb j n && priv n y j) eqn:M; [| rewrite rstep_idle by exact M; exact H].
    apply andb_true_iff in M. destruct M as [Mj Pj]. apply Nat.ltb_lt in Mj.
    assert (G : forall i, i < n -> get y i < K) by (apply okb_get; exact H).
    unfold rstep. rewrite (proj2 (Nat.ltb_lt j n) Mj), Pj. simpl. apply andb_true_iff. split.
    - apply Nat.eqb_eq. rewrite map_length, seq_length. reflexivity.
    - apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [i [<- Hi]].
      apply in_seq in Hi. apply Nat.ltb_lt. destruct (Nat.eqb_spec i j) as [-> | _]; [| apply G; lia].
      destruct j as [| j]; simpl; [apply inc_bound; [pose proof (G 0 Mj); lia | apply G; lia] | apply G; lia].
  Qed.

  Definition ustep (j : nat) (x : RX) : RX := exist _ (rstep n K j (proj1_sig x)) (rstep_ok j _ (proj2_sig x)).
  Definition rjs : list nat := seq 0 n.
  Definition rLb (x : RX) : bool := legb n (proj1_sig x).

  Lemma sig_eq : forall x y : RX, proj1_sig x = proj1_sig y -> x = y.
  Proof. intros [x Hx] [y Hy] E. simpl in E. subst y. f_equal. apply UIP_dec. exact bool_dec. Qed.

  Definition RX_eq_dec : forall x y : RX, {x = y} + {x <> y}.
  Proof.
    intros x y. destruct (list_eq_dec Nat.eq_dec (proj1_sig x) (proj1_sig y)) as [E | E].
    - left. apply sig_eq. exact E.
    - right. intro H. subst. exact (E eq_refl).
  Defined.

  (* ----- finiteness: an explicit list of all states ----- *)

  Fixpoint words (m : nat) : list (list nat) :=
    match m with 0 => [[]] | S m => flat_map (fun l => map (fun c => c :: l) (seq 0 K)) (words m) end.

  Lemma words_full : forall l, Forall (fun c => c < K) l -> In l (words (length l)).
  Proof.
    induction l as [| c l IH]; intros H; [left; reflexivity |]. inversion H; subst. simpl.
    apply in_flat_map. exists l. split; [apply IH; assumption |].
    apply in_map_iff. exists c. split; [reflexivity | apply in_seq; lia].
  Qed.

  Definition lift_aux (l : list nat) (b : bool) : okb l = b -> list RX :=
    match b as b' return okb l = b' -> list RX with
    | true => fun H => [exist _ l H]
    | false => fun _ => []
    end.
  Definition rxs : list RX := flat_map (fun l => lift_aux l (okb l) eq_refl) (words n).

  Lemma rxs_full : forall x, In x rxs.
  Proof.
    intros [l H]. unfold rxs. apply in_flat_map. exists l. split.
    - pose proof H as H'. apply andb_true_iff in H'. destruct H' as [L F]. apply Nat.eqb_eq in L.
      rewrite <- L. apply words_full. apply Forall_forall. intros c Hc. rewrite forallb_forall in F.
      apply Nat.ltb_lt. apply F. exact Hc.
    - assert (Gen : forall b (E : okb l = b), In (exist _ l H) (lift_aux l b E)).
      { intros [|] E; simpl; [left; f_equal; apply UIP_dec; exact bool_dec | congruence]. }
      apply Gen.
  Qed.

  Lemma wrun_proj : forall w x, proj1_sig (wrun RX ustep w x) = wrun (list nat) (rstep n K) w (proj1_sig x).
  Proof. induction w as [| a w IH]; intros x; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

  (* ----- closure and no deadlock ----- *)

  Theorem ring_closure : 2 <= n -> 2 <= K -> Closed RX rjs ustep (Legit RX rLb).
  Proof.
    intros Hn HK j [y Hy] _ H. unfold Legit, rLb in *. simpl in *. apply legb_iff. apply legb_iff in H.
    apply ring_closed; try assumption. apply okb_get; [exact Hy | lia].
  Qed.

  Lemma ring_some_priv : 2 <= n -> forall y, exists i, i < n /\ priv n y i = true.
  Proof.
    intros Hn y.
    destruct (bsearch (fun i => priv n y (S i) = true)
                (fun i => match Bool.bool_dec (priv n y (S i)) true with
                          | left E => or_introl E | right E => or_intror E end) (n - 1))
      as [[i [Hi P]] | H]; [exists (S i); split; [lia | exact P] |].
    exists 0. split; [lia |]. apply (proj2 (priv0_iff n y)). symmetry. apply (chain_down y n); [| lia].
    intros k Hk. apply (proj1 (privS_iff n y k)). destruct (priv n y (S k)) eqn:P; [| reflexivity].
    exfalso. exact (H k ltac:(lia) P).
  Qed.

  Theorem ring_no_deadlock : 2 <= n -> 2 <= K -> NoDeadlock RX rjs ustep rLb.
  Proof.
    intros Hn HK [y Hy] _. destruct (ring_some_priv Hn y) as [i [Hi P]]. exists i.
    split; [apply in_seq; lia |]. intro E. apply (f_equal (fun x => get (proj1_sig x) i)) in E. simpl in E.
    rewrite rstep_self, P in E by exact Hi. destruct i as [| i]; simpl in E.
    - exact (inc_ne K HK (get y 0) (okb_get y Hy 0 Hi) E).
    - apply privS_true in P. apply P. symmetry. exact E.
  Qed.
End RingSystem.

(* ============================================================================================ *)
(* Part 5. Target 2: the ring self-stabilizes for every n >= 2 and K >= n, under the fair        *)
(* central daemon (through target 1) and under the unfair central daemon (through target 3).    *)
(* ============================================================================================ *)

Section RingResults.
  Variable n K : nat.
  Hypothesis Hn : 2 <= n.
  Hypothesis HnK : n <= K.

  Let HK : 2 <= K. Proof. lia. Qed.

  (* Lasso-freedom under the fair daemon: a fair loop names the bottom, the bottom moves in it
     (fair_fires), so its base is legitimate (core_leg) and so is every loop state (closure). *)
  Theorem ring_no_bad_lasso : forall s0, ~ BadLasso (RX n K) (rjs n) (ustep n K) (Legit _ (rLb n K)) s0.
  Proof.
    intros s0 (x & p & q & y & (Hp & Ep & Hq & Pq & Eq & Hall) & (k & Hk & Ey) & Ny).
    apply Ny. rewrite <- Ey. apply (closed_wrun _ (rjs n) _ _ (ring_closure n K Hn HK)); [apply path_firstn; exact Pq |].
    set (z k := wrun (list nat) (rstep n K) (firstn k q) (proj1_sig x)).
    assert (hz : forall k, k < length q -> z (S k) = rstep n K (nth k q 0) (z k))
      by (intros; apply wrun_firstn_S; assumption).
    assert (hloop : z (length q) = z 0) by (unfold z; rewrite firstn_all, <- wrun_proj, Eq; reflexivity).
    assert (ok0 : get (z 0) 0 < K) by (apply (okb_get n K); [exact (proj2_sig x) | lia]).
    unfold Legit, rLb. apply legb_iff. change (Leg n (z 0)).
    apply (core_leg n K z (fun k => nth k q 0) (length q) hz hloop Hn HnK ok0).
    apply (fair_fires n K z _ _ hz hloop Hn HnK ok0). intros j Hj.
    destruct (In_nth q j 0 (Hall j ltac:(apply in_seq; lia))) as [k' [Hk' E]]. exists k'. tauto.
  Qed.

  (* Target 2 (fair daemon): closure and convergence from every state. *)
  Theorem ring_fair_selfstab : FairSelfStab (RX n K) (rjs n) (ustep n K) (rLb n K).
  Proof.
    split; [exact (ring_closure n K Hn HK) |]. intros s0.
    apply (stab_fair_from _ (RX_eq_dec n K) (rxs n K) (rxs_full n K) _ _ _ (ring_closure n K Hn HK) s0).
    apply ring_no_bad_lasso.
  Qed.

  Lemma rstep_moved : forall j y, rstep n K j y <> y -> j < n /\ priv n y j = true.
  Proof.
    intros j y H. destruct (Nat.ltb j n && priv n y j) eqn:M; [| exfalso; exact (H (rstep_idle n K j y M))].
    apply andb_true_iff in M. destruct M as [M P]. apply Nat.ltb_lt in M. tauto.
  Qed.

  (* Target 2 (unfair daemon): no reachable moving loop outside L, so every sequence of moves
     reaches L (unfair_no_loop, i.e. LayerInterfaces.sn_iff_no_loop). *)
  Theorem ring_unfair_selfstab : forall s0, UnfairStab (RX n K) (rjs n) (ustep n K) (rLb n K) s0.
  Proof.
    intros s0. apply (unfair_no_loop _ (RX_eq_dec n K) (rxs n K) (rxs_full n K)).
    intros (p & q & Hp & Hq & Pq & Eq & Hm).
    set (uu := uL (RX n K) (ustep n K) (rLb n K)) in *.
    set (x := wrun (RX n K) uu p s0) in *.
    set (ys k := wrun (RX n K) uu (firstn k q) x).
    assert (Out : forall k, k < length q -> rLb n K (ys k) = false).
    { intros k Hk. destruct (rLb n K (ys k)) eqn:L; [| reflexivity]. exfalso. apply (Hm k Hk).
      unfold ystate, uu. apply uL_in. exact L. }
    set (z k := proj1_sig (ys k)).
    assert (hz : forall k, k < length q -> z (S k) = rstep n K (nth k q 0) (z k)).
    { intros k Hk. unfold z, ys. rewrite wrun_firstn_S by exact Hk. unfold uu.
      rewrite uL_out by exact (Out k Hk). reflexivity. }
    assert (hloop : z (length q) = z 0) by (unfold z, ys; rewrite firstn_all, Eq; reflexivity).
    assert (ok0 : get (z 0) 0 < K) by (apply (okb_get n K); [exact (proj2_sig (ys 0)) | lia]).
    assert (Lq : 0 < length q) by (destruct q; [congruence | simpl; lia]).
    assert (Mv : forall k, k < length q -> nth k q 0 < n /\ priv n (z k) (nth k q 0) = true).
    { intros k Hk. apply rstep_moved. intro E. apply (Hm k Hk). unfold ystate. apply sig_eq.
      change (proj1_sig (uu (nth k q 0) (ys k)) = proj1_sig (ys k)). unfold uu.
      rewrite uL_out by exact (Out k Hk). exact E. }
    pose proof (core_leg n K z (fun k => nth k q 0) (length q) hz hloop Hn HnK ok0
                  (unfair_fires n K z _ _ hz hloop Hn HnK ok0 Lq Mv)) as L.
    apply legb_iff in L. pose proof (Out 0 Lq) as O. change (legb n (z 0) = false) in O. congruence.
  Qed.

  (* The same through fair_sn_exact: no reachable starved loop outside L. *)
  Corollary ring_no_starved_loop : forall s0, ~ StarvedLoop (RX n K) (rjs n) (uL _ (ustep n K) (rLb n K)) s0.
  Proof.
    intros s0. apply (proj2 (proj1 (unfair_exact _ (RX_eq_dec n K) (rxs n K) (rxs_full n K) _ _ _
      (ring_closure n K Hn HK) (ring_no_deadlock n K Hn HK) s0) (ring_unfair_selfstab s0))).
  Qed.
End RingResults.

(* ============================================================================================ *)
(* Part 6. The bound matters, and non-vacuity.                                                  *)
(* n = 4 machines, K = 2 values (K = n - 2): the fair loop at 0010 under the machine word        *)
(* 0 3 2 1 0 3 2 1 names every machine and returns, and 0010 has three privileges (machines 0,   *)
(* 2, 3). It is a bad fair lasso, so the ring with K = 2 < 4 = n does not stabilize under the    *)
(* fair daemon, nor under the unfair one. (An exhaustive search for n <= 6, outside Coq, finds   *)
(* bad fair loops exactly at K <= n - 2; K = n - 1 is not proved here, see the header.)          *)
(* ============================================================================================ *)

Definition bad4 : RX 4 2 := exist _ [0; 0; 1; 0] eq_refl.
Definition q4 : list nat := [0; 3; 2; 1; 0; 3; 2; 1].

Theorem ring4_bad_lasso : BadLasso (RX 4 2) (rjs 4) (ustep 4 2) (Legit _ (rLb 4 2)) bad4.
Proof.
  exists bad4, [], q4, bad4. split; [| split; [apply onloop_base; discriminate | intro H; vm_compute in H; discriminate]].
  split; [constructor |]. split; [reflexivity |]. split; [discriminate |].
  split; [unfold Path, q4, rjs; repeat constructor; simpl; tauto |].
  split; [apply sig_eq; rewrite wrun_proj; vm_compute; reflexivity |].
  intros j Hj. unfold rjs in Hj. simpl in Hj. unfold q4. simpl. tauto.
Qed.

(* K < n: neither fair nor unfair stabilization holds from 0010. Kernel theorems: C1_refutes
   (through bad_lasso_refutes) and, for the unfair daemon, the cycle of bad_lasso_cycle. *)
Theorem ring_bound_matters :
  ~ FairSettles (RX 4 2) (rjs 4) (ustep 4 2) (Legit _ (rLb 4 2)) bad4 /\
  ~ UnfairStab (RX 4 2) (rjs 4) (ustep 4 2) (rLb 4 2) bad4.
Proof.
  split.
  - exact (proj1 (bad_lasso_refutes _ _ _ _ _ ring4_bad_lasso)).
  - apply (bad_lasso_cycle _ (RX_eq_dec 4 2) _ _ _ (ring_closure 4 2 ltac:(lia) ltac:(lia))
             (ring_no_deadlock 4 2 ltac:(lia) ltac:(lia))). exact ring4_bad_lasso.
Qed.

(* Non-vacuity: for n = K = 3 the hypotheses hold, 012 is illegitimate (machines 1 and 2 are
   privileged), and both stabilization results apply to it. *)
Definition s3 : RX 3 3 := exist _ [0; 1; 2] eq_refl.

Theorem ring3_nonvacuous :
  ~ Legit _ (rLb 3 3) s3 /\ Legit _ (rLb 3 3) (exist _ [1; 1; 1] eq_refl : RX 3 3) /\
  FairSettles (RX 3 3) (rjs 3) (ustep 3 3) (Legit _ (rLb 3 3)) s3 /\
  UnfairStab (RX 3 3) (rjs 3) (ustep 3 3) (rLb 3 3) s3.
Proof.
  split; [intro H; vm_compute in H; discriminate |]. split; [reflexivity |].
  split; [exact (proj2 (ring_fair_selfstab 3 3 ltac:(lia) ltac:(lia)) s3) |].
  exact (ring_unfair_selfstab 3 3 ltac:(lia) ltac:(lia) s3).
Qed.
