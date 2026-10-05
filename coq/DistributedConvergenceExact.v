(* DistributedConvergenceExact.v: convergence among quiescent interleavings ALONE, in the distributed
   propagation model on MONOTONE CYCLIC federations WITHOUT resets (REGIME-AUDIT.md section 8, gap 14).
   Axiom-free.

   The gap. DistributedCyclesExact.flush_fed_iff is exact for the certified property
   FlushR /\ DAgreeQ /\ DConvQ (convergence TOGETHER WITH agreement with gsm's FedMachine), and its
   canonical state is the least fixed point Lfp. Convergence alone (FlushR /\ DConvQ) had only the
   sufficient condition quiet_conv_suff (XUcR, FMConv, NoGhostR), and conv_ghost_normal showed
   NoGhostR is not necessary: quiescent interleavings can agree on a common GHOST (a fixed point of
   the cyclic repair above the least one). This file gives the exact condition.

   The idea. Replace the FedMachine's canonical state (reset, then Kleene: Lfp) by the canonical
   state the propagation dynamics itself produces: the quiescent state a reachable state flushes to.
   Then the E/S/H decomposition of the canonical-execution framework goes through with that
   canonicalizer, read relationally (no choice function is needed, so the gate stays axiom-free).

   Notation (as in DistributedCycles.v): a state is (l, h); u l j the repair of target j; a
   propagation word is a list of targets in js; Quiet t: no propagation step changes t; Lfp, Nc
   (l, h) = (l, Lfp l), FM the FedMachine. New here (all at r = false, no resets):
     Flushes t q   : some propagation word takes t to the quiescent state q.
     FlushDetAt t  : t flushes to at most one quiescent state.
     FlushDetR     : every reachable state is FlushDetAt (canonical fidelity with the dynamics'
                     own canonicalizer: the ghost, if any, is determined).
     FlushXUR      : for every reachable state t, event e and flush q of t, the event applied at the
                     stale state t and the event applied at its flush q flush to a common state
                     (state descent for the flush canonicalizer, in joinable form).
     QM s es q     : the quiescent machine: flush s, then for each event apply it and flush again,
                     ending at q. It is the FedMachine with Normalize (reset, then Kleene) replaced
                     by propagation to quiescence, which keeps ghosts.
     QMConv s0     : trace-equivalent event sequences have the same quiescent-machine outcomes
                     (history descent for the flush canonicalizer).

   1. The exact condition (no lattice hypothesis; only the action structure of the model).
     conv_quiet_exact : FlushR /\ DConvQ <-> FlushR /\ FlushDetR /\ FlushXUR /\ QMConv.
     The forward direction holds for every r (conv_flushdet, conv_flushxu, conv_qmconv); the
     backward one (conv_quiet_suff) is for r = false: a reset moves a state's canonical flush to
     the least fixed point without an event (the reset epochs of DistributedCycles.v Q3 handle it).
     Each right-hand conjunct is necessary, by an instance where it alone fails:
       FlushR    : flip_conv_noflush (no reachable state ever quiesces; the others hold vacuously).
       FlushDetR : fork_conv_nodet (the flag cycle from the stale start (sa, sb) = (true, false)
                   flushes to the least fixed point by one word and to the ghost by another).
       FlushXUR  : copy_conv_noxu (copy_xu_fails: an event reads a stale shared value).
       QMConv    : fm_conv_noqm (fm_conv_fails: two declared-independent events do not commute).
     flushdet_event_iff : FlushDetR <-> the start and every post-event state are FlushDetAt.
     fair_conv_exact    : the same with FairFlushR.

   2. The ghost-free case recovers the earlier results. Under FlushR /\ NoGhostR every flush is the
     FedMachine normal form (noghost_flushes), so FlushDetR holds (noghost_flushdet), FlushXUR is
     XUcR (noghost_flushxu_iff) and QMConv is FMConv (Nc s0) (noghost_qmconv_iff, through noghost_qm:
     the quiescent machine IS the FedMachine). Corollaries:
       quiet_conv_recovered : FlushR -> NoGhostR -> (DConvQ <-> XUcR /\ FMConv)  (quiet_conv_iff).
       agree_conv_noghost   : FlushR -> (DAgreeQ /\ DConvQ <-> DConvQ /\ NoGhostR): agreement with
                              the FedMachine is convergence plus canonical fidelity to Lfp.
       flush_fed_recovered  : flush_fed_iff, rederived through conv_quiet_exact.
     quiet_conv_suff (DistributedCycles.v) stays the FlushR-free sufficient condition.

   3. Determinacy of the ghost from soundness (lattice hypotheses of DistributedCycles.v).
     sand_flushdet  : a sandwiched state (s <= h <= every fixed point above s, s sound) flushes only
                      to the least fixed point above s.
     sandr_flushdet, soundr_flushdet : SandR or SoundR gives FlushDetR.
     soundr_conv_iff : SoundR -> (DConvQ <-> FlushXUR /\ QMConv) (FlushR and FlushDetR are free).

   4. Instances.
     conv_ghost_instance : conv_ghost_normal (DistributedCyclesExact.v) is an instance: every
       conjunct holds, NoGhostR and DAgreeQ fail, and the quiescent machine's outcome for SetSA is
       the ghost ((false,false),(true,true)) while the FedMachine's is ((false,false),(false,false)).
     ghost_conv_not_fed : from a ghost start, a copy event on A and a raise on B (declared
       independent, different registries): FairFlushR and DConvQ hold, yet XUcR, FMConv (Nc s0),
       NoGhostR and DAgreeQ all fail. None of the three conjuncts of quiet_conv_suff is necessary
       for convergence alone; their flush-relative forms are.
     raise_only_conv : non-vacuity of SoundR and of every conjunct without a ghost. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.Federation NC.FederationEventsCycles NC.FederationEventsCyclesCheck
  NC.DistributedCycles NC.DistributedCyclesExact.
Import ListNotations.

Lemma fa_split : forall (A : Type) (P : A -> Prop) a b, Forall P (a ++ b) -> Forall P a /\ Forall P b.
Proof.
  intros A P a. induction a as [| x a IH]; intros b H; [split; [constructor | exact H] |].
  inversion H as [| ? ? Hx H']; subst. destruct (IH b H') as [Ha Hb].
  split; [constructor; assumption | exact Hb].
Qed.

(* ======================================================================================= *)
(* Part 1. The exact condition (generic; no lattice hypothesis).                           *)
(* ======================================================================================= *)

Section Conv.
  Set Default Proof Using "All".
  Variables Loc Sh : Type.
  Variable bot : Sh.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable u : Loc -> nat -> Sh -> Sh.
  Variable K : nat.
  Variable js : list nat.
  Variable E : Type.
  Variable ev : E -> Loc * Sh -> Loc * Sh.
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.

  Local Notation run := (crun Loc Sh bot u E ev).
  Local Notation OKw := (OK js E).
  Local Notation Qt := (Quiet Loc Sh u js).
  Local Notation PW c := (map (AProp E) c).
  Local Notation InJ := (fun j => In j js).
  Local Notation teq := (tequiv (Ifd E reg I)).
  Local Notation FlushR' := (FlushR Loc Sh bot u js E ev).
  Local Notation DConvQ' := (DConvQ Loc Sh bot u js E ev reg I).
  Local Notation NoGhostR' := (NoGhostR Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation XUcR' := (XUcR Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation FMConv' := (FMConv Loc Sh bot sh_eq_dec u K js E ev reg I).
  Local Notation FM' := (FM Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation DAgreeQ' := (DAgreeQ Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation NC := (Nc Loc Sh bot sh_eq_dec u K js).

  (* q is a quiescent state some propagation word reaches from t. *)
  Definition Flushes (t q : Loc * Sh) : Prop :=
    exists c, Forall InJ c /\ run (PW c) t = q /\ Qt q.

  Definition FlushDetAt (t : Loc * Sh) : Prop :=
    forall q1 q2, Flushes t q1 -> Flushes t q2 -> q1 = q2.

  (* E (canonical fidelity, ghost-tolerant): every reachable state flushes to at most one
     quiescent state. *)
  Definition FlushDetR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w q1 q2, OKw r w -> Flushes (run w s0) q1 -> Flushes (run w s0) q2 -> q1 = q2.

  (* S (state descent for the flush): an event at a reachable stale state and the same event at
     a flush of it flush to a common state. *)
  Definition FlushXUR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall p e q, OKw r p -> Flushes (run p s0) q ->
      exists q', Flushes (ev e (run p s0)) q' /\ Flushes (ev e q) q'.

  (* The quiescent machine: flush, then for each event apply it and flush again. *)
  Fixpoint QM (s : Loc * Sh) (es : list E) (q : Loc * Sh) : Prop :=
    match es with
    | [] => Flushes s q
    | e :: es' => exists s', Flushes s s' /\ QM (ev e s') es' q
    end.

  (* H (history descent for the flush): trace-equivalent event sequences have the same
     quiescent-machine outcomes. *)
  Definition QMConv (s0 : Loc * Sh) : Prop :=
    forall es1 es2, teq es1 es2 -> forall q, QM s0 es1 q -> QM s0 es2 q.

  (* ----- basic facts ----- *)

  Lemma flushes_quiet : forall t, Qt t -> Flushes t t.
  Proof. intros t H. exists []. split; [constructor | split; [reflexivity | exact H]]. Qed.

  Lemma flushes_qt : forall t q, Flushes t q -> Qt q.
  Proof. intros t q [c [_ [_ H]]]. exact H. Qed.

  Lemma flushes_fst : forall t q, Flushes t q -> fst q = fst t.
  Proof. intros t q [c [_ [R _]]]. rewrite <- R. apply fst_props. Qed.

  Lemma flushes_prop : forall j t q, In j js ->
    Flushes (cstep Loc Sh bot u E ev (AProp E j) t) q -> Flushes t q.
  Proof.
    intros j t q Hj [c [Hc [R Q]]]. exists (j :: c).
    split; [constructor; assumption | split; [exact R | exact Q]].
  Qed.

  (* A flush of a reachable state is reachable, by a word with the same events. *)
  Lemma flush_ok : forall r w c, OKw r w -> Forall InJ c -> OKw r (w ++ PW c).
  Proof. intros r w c Hw Hc. apply ok_app; [exact Hw | apply ok_props; exact Hc]. Qed.

  Lemma flush_run : forall s0 w c, run (w ++ PW c) s0 = run (PW c) (run w s0).
  Proof. intros. apply crun_app. Qed.

  Lemma flush_evs : forall w c, cevs E (w ++ PW c) = cevs E w.
  Proof. intros w c. rewrite cevs_app, cevs_props, app_nil_r. reflexivity. Qed.

  Lemma flushR_flushes : forall r s0 w, FlushR' r s0 -> OKw r w -> exists q, Flushes (run w s0) q.
  Proof.
    intros r s0 w Hf Hw. destruct (Hf w Hw) as [c [Hc Hq]]. rewrite crun_app in Hq.
    exists (run (PW c) (run w s0)), c. split; [exact Hc | split; [reflexivity | exact Hq]].
  Qed.

  (* A post-event state after a flush is reachable. *)
  Lemma ev_after_flush : forall s0 p c e,
    run (p ++ PW c ++ [AEv E e]) s0 = ev e (run (PW c) (run p s0)).
  Proof. intros. rewrite !crun_app. reflexivity. Qed.

  Lemma ev_ok : forall r p c e, OKw r p -> Forall InJ c -> OKw r (p ++ PW c ++ [AEv E e]).
  Proof.
    intros r p c e Hp Hc. apply ok_app; [exact Hp |]. apply ok_app; [apply ok_props; exact Hc | apply ok_ev1].
  Qed.

  Lemma ev_evs : forall p c e, cevs E (p ++ PW c ++ [AEv E e]) = cevs E p ++ [e].
  Proof. intros. rewrite !cevs_app, cevs_props. reflexivity. Qed.

  (* ----- the quiescent machine ----- *)

  (* Every outcome of the quiescent machine is a reachable quiescent state with the same events. *)
  Lemma qm_word : forall r es s q, QM s es q ->
    exists w, OKw r w /\ cevs E w = es /\ run w s = q /\ Qt q.
  Proof.
    intros r es. induction es as [| e es IH]; intros s q H.
    - destruct H as [c [Hc [R Q]]]. exists (PW c).
      split; [apply ok_props; exact Hc |]. split; [apply cevs_props |]. split; [exact R | exact Q].
    - destruct H as [s' [[c [Hc [R Q]]] Hm]].
      destruct (IH (ev e s') q Hm) as [w [Hw [C [Rw Qw]]]].
      exists (PW c ++ AEv E e :: w). split.
      + apply ok_app; [apply ok_props; exact Hc | constructor; [exact Logic.I | exact Hw]].
      + split; [rewrite cevs_app, cevs_props; cbn [cevs app]; rewrite C; reflexivity |].
        split; [| exact Qw]. rewrite crun_app, R. exact Rw.
  Qed.

  Lemma qm_snoc : forall es s e q q', QM s es q -> Flushes (ev e q) q' -> QM s (es ++ [e]) q'.
  Proof.
    intros es. induction es as [| a es IH]; intros s e q q' H Hq.
    - exists q. split; [exact H | exact Hq].
    - destruct H as [s' [Hs Hm]]. exists s'. split; [exact Hs |]. exact (IH _ e q q' Hm Hq).
  Qed.

  (* With every reachable state flushable, the quiescent machine has an outcome for every event
     sequence from every reachable state. *)
  Lemma qm_exists : forall r s0, FlushR' r s0 -> forall es p, OKw r p ->
    exists q, QM (run p s0) es q.
  Proof.
    intros r s0 Hf es. induction es as [| e es IH]; intros p Hp.
    - exact (flushR_flushes r s0 p Hf Hp).
    - destruct (flushR_flushes r s0 p Hf Hp) as [s' Hs]. pose proof Hs as [c [Hc [R _]]].
      destruct (IH (p ++ PW c ++ [AEv E e]) (ev_ok r p c e Hp Hc)) as [q Hq].
      rewrite ev_after_flush, R in Hq. exists q, s'. split; [exact Hs | exact Hq].
  Qed.

  (* Under FlushDetR the quiescent machine is a partial function. *)
  Lemma qm_det : forall r s0, FlushDetR r s0 -> forall es p q1 q2, OKw r p ->
    QM (run p s0) es q1 -> QM (run p s0) es q2 -> q1 = q2.
  Proof.
    intros r s0 Hd es. induction es as [| e es IH]; intros p q1 q2 Hp H1 H2.
    - exact (Hd p q1 q2 Hp H1 H2).
    - destruct H1 as [s1 [F1 M1]]. destruct H2 as [s2 [F2 M2]].
      assert (Es : s1 = s2) by exact (Hd p s1 s2 Hp F1 F2). subst s2.
      destruct F1 as [c [Hc [R _]]].
      apply (IH (p ++ PW c ++ [AEv E e])); [apply ev_ok; assumption | |];
        rewrite ev_after_flush, R; assumption.
  Qed.

  (* Tracking: under the three layers, a flush of every reachable state is the quiescent
     machine's outcome for the same events (no resets). *)
  Theorem qm_track : forall s0, FlushR' false s0 -> FlushDetR false s0 -> FlushXUR false s0 ->
    forall w q, OKw false w -> Flushes (run w s0) q -> QM s0 (cevs E w) q.
  Proof.
    intros s0 Hf Hd Hx w. induction w as [| a w IH] using List.rev_ind; intros q Hw Hq; [exact Hq |].
    destruct (fa_split _ _ w [a] Hw) as [Hw' Ha]. pose proof (Forall_inv Ha) as Ha'.
    rewrite cevs_app. rewrite crun_app in Hq. destruct a as [e | j |].
    - destruct (flushR_flushes false s0 w Hf Hw') as [q0 H0].
      pose proof (IH q0 Hw' H0) as M0.
      destruct (Hx w e q0 Hw' H0) as [q' [F1 F2]].
      assert (Eq : q = q').
      { apply (Hd (w ++ [AEv E e])); [apply ok_app; [exact Hw' | apply ok_ev1] | |];
          rewrite crun_app; assumption. }
      subst q'. exact (qm_snoc (cevs E w) s0 e q0 q M0 F2).
    - cbn [cevs]. rewrite app_nil_r. apply IH; [exact Hw' |].
      exact (flushes_prop j (run w s0) q Ha' Hq).
    - cbn in Ha'. discriminate Ha'.
  Qed.

  (* ----- the forward direction (every r) ----- *)

  Theorem conv_flushdet : forall r s0, DConvQ' r s0 -> FlushDetR r s0.
  Proof.
    intros r s0 Hc w q1 q2 Hw [c1 [H1 [R1 Q1]]] [c2 [H2 [R2 Q2]]].
    rewrite <- R1, <- R2, <- !flush_run.
    apply Hc; [apply flush_ok; assumption | apply flush_ok; assumption | | |].
    - rewrite !flush_evs. apply teq_refl.
    - rewrite flush_run, R1. exact Q1.
    - rewrite flush_run, R2. exact Q2.
  Qed.

  Theorem conv_flushxu : forall r s0, FlushR' r s0 -> DConvQ' r s0 -> FlushXUR r s0.
  Proof.
    intros r s0 Hf Hc p e q Hp Hq. pose proof Hq as [c [Hc0 [R _]]].
    assert (O1 : OKw r (p ++ PW [] ++ [AEv E e])) by exact (ev_ok r p [] e Hp ltac:(constructor)).
    assert (O2 : OKw r (p ++ PW c ++ [AEv E e])) by (apply ev_ok; assumption).
    destruct (flushR_flushes r s0 _ Hf O1) as [q1 F1]. destruct (flushR_flushes r s0 _ Hf O2) as [q2 F2].
    assert (E12 : q1 = q2).
    { destruct F1 as [d1 [D1 [S1 Q1]]]. destruct F2 as [d2 [D2 [S2 Q2]]].
      rewrite <- S1, <- S2, <- !flush_run.
      apply Hc; [apply flush_ok; assumption | apply flush_ok; assumption | | |].
      - rewrite !flush_evs, !ev_evs. apply teq_refl.
      - rewrite flush_run, S1. exact Q1.
      - rewrite flush_run, S2. exact Q2. }
    subst q2. rewrite ev_after_flush in F1, F2. rewrite R in F2.
    exists q1. split; [exact F1 | exact F2].
  Qed.

  Theorem conv_qmconv : forall r s0, FlushR' r s0 -> DConvQ' r s0 -> QMConv s0.
  Proof.
    intros r s0 Hf Hc es1 es2 Ht q H1.
    destruct (qm_word r es1 s0 q H1) as [w1 [O1 [C1 [R1 Q1]]]].
    destruct (qm_exists r s0 Hf es2 [] ltac:(constructor)) as [q2 H2].
    destruct (qm_word r es2 s0 q2 H2) as [w2 [O2 [C2 [R2 Q2]]]].
    assert (Eq : q = q2).
    { rewrite <- R1, <- R2. apply Hc; [exact O1 | exact O2 | rewrite C1, C2; exact Ht | |].
      - rewrite R1. exact Q1.
      - rewrite R2. exact Q2. }
    rewrite Eq. exact H2.
  Qed.

  (* ----- the backward direction (no resets) ----- *)

  Theorem conv_quiet_suff : forall s0, FlushR' false s0 -> FlushDetR false s0 ->
    FlushXUR false s0 -> QMConv s0 -> DConvQ' false s0.
  Proof.
    intros s0 Hf Hd Hx Hh w1 w2 O1 O2 Ht Q1 Q2.
    pose proof (qm_track s0 Hf Hd Hx w1 _ O1 (flushes_quiet _ Q1)) as M1.
    pose proof (qm_track s0 Hf Hd Hx w2 _ O2 (flushes_quiet _ Q2)) as M2.
    exact (qm_det false s0 Hd (cevs E w2) [] _ _ ltac:(constructor) (Hh _ _ Ht _ M1) M2).
  Qed.

  (* The exact condition for convergence among quiescent interleavings alone. *)
  Theorem conv_quiet_exact : forall s0,
    (FlushR' false s0 /\ DConvQ' false s0) <->
    (FlushR' false s0 /\ FlushDetR false s0 /\ FlushXUR false s0 /\ QMConv s0).
  Proof.
    intros s0. split.
    - intros [Hf Hc]. split; [exact Hf |].
      split; [exact (conv_flushdet false s0 Hc) |].
      split; [exact (conv_flushxu false s0 Hf Hc) | exact (conv_qmconv false s0 Hf Hc)].
    - intros [Hf [Hd [Hx Hh]]]. split; [exact Hf | exact (conv_quiet_suff s0 Hf Hd Hx Hh)].
  Qed.

  (* FlushDetR is checked at the start and at every post-event state. *)
  Theorem flushdet_event_iff : forall s0, FlushDetR false s0 <->
    (FlushDetAt s0 /\ forall p e, OKw false p -> FlushDetAt (ev e (run p s0))).
  Proof.
    intros s0. split.
    - intros Hd. split; [intros q1 q2; exact (Hd [] q1 q2 ltac:(constructor)) |].
      intros p e Hp q1 q2 H1 H2.
      apply (Hd (p ++ [AEv E e])); [apply ok_app; [exact Hp | apply ok_ev1] | |];
        rewrite crun_app; assumption.
    - intros [H0 He] w. induction w as [| a w IH] using List.rev_ind; intros q1 q2 Hw H1 H2;
        [exact (H0 q1 q2 H1 H2) |].
      destruct (fa_split _ _ w [a] Hw) as [Hw' Ha]. pose proof (Forall_inv Ha) as Ha'.
      rewrite crun_app in H1, H2. destruct a as [e | j |].
      + exact (He w e Hw' q1 q2 H1 H2).
      + exact (IH q1 q2 Hw' (flushes_prop j _ q1 Ha' H1) (flushes_prop j _ q2 Ha' H2)).
      + cbn in Ha'. discriminate Ha'.
  Qed.

  (* ===================================================================================== *)
  (* The ghost-free case: the flush is the FedMachine's normal form.                       *)
  (* ===================================================================================== *)

  Lemma noghost_flushes : forall r s0 w q, NoGhostR' r s0 -> OKw r w ->
    Flushes (run w s0) q -> q = NC (run w s0).
  Proof.
    intros r s0 w q Hg Hw Hq. pose proof (flushes_fst _ _ Hq) as Fq.
    destruct Hq as [c [Hc [R Q]]].
    pose proof (Hg (w ++ PW c) (flush_ok r w c Hw Hc)) as G. rewrite flush_run, R in G.
    transitivity (NC q); [exact (quiet_normal Loc Sh bot sh_eq_dec u K js q (G Q)) |].
    apply Nc_fst. exact Fq.
  Qed.

  Theorem noghost_flushdet : forall r s0, NoGhostR' r s0 -> FlushDetR r s0.
  Proof.
    intros r s0 Hg w q1 q2 Hw H1 H2.
    rewrite (noghost_flushes r s0 w q1 Hg Hw H1), (noghost_flushes r s0 w q2 Hg Hw H2). reflexivity.
  Qed.

  Lemma noghost_ev_flush : forall r s0 p e q, NoGhostR' r s0 -> OKw r p ->
    Flushes (ev e (run p s0)) q -> q = NC (ev e (run p s0)).
  Proof.
    intros r s0 p e q Hg Hp Hq.
    assert (O : OKw r (p ++ PW [] ++ [AEv E e])) by exact (ev_ok r p [] e Hp ltac:(constructor)).
    pose proof (noghost_flushes r s0 _ q Hg O) as X. rewrite ev_after_flush in X. exact (X Hq).
  Qed.

  Lemma noghost_ev_flush2 : forall r s0 p q e q', NoGhostR' r s0 -> OKw r p ->
    Flushes (run p s0) q -> Flushes (ev e q) q' -> q' = NC (ev e q).
  Proof.
    intros r s0 p q e q' Hg Hp [c [Hc [R Q]]] Hq'.
    pose proof (noghost_flushes r s0 _ q' Hg (ev_ok r p c e Hp Hc)) as X.
    rewrite ev_after_flush, R in X. exact (X Hq').
  Qed.

  Lemma flushR_ev2 : forall r s0 p q e, FlushR' r s0 -> OKw r p -> Flushes (run p s0) q ->
    exists q', Flushes (ev e q) q'.
  Proof.
    intros r s0 p q e Hf Hp [c [Hc [R Q]]].
    destruct (flushR_flushes r s0 _ Hf (ev_ok r p c e Hp Hc)) as [q' Hq'].
    rewrite ev_after_flush, R in Hq'. exists q'. exact Hq'.
  Qed.

  (* Without ghosts, flush-relative state descent is the FedMachine's (XUcR). *)
  Theorem noghost_flushxu_iff : forall r s0, FlushR' r s0 -> NoGhostR' r s0 ->
    (FlushXUR r s0 <-> XUcR' r s0).
  Proof.
    intros r s0 Hf Hg. split.
    - intros Hx p e Hp. unfold XUc.
      destruct (flushR_flushes r s0 p Hf Hp) as [q0 H0].
      pose proof (noghost_flushes r s0 p q0 Hg Hp H0) as E0.
      destruct (Hx p e q0 Hp H0) as [q' [F1 F2]].
      pose proof (noghost_ev_flush r s0 p e q' Hg Hp F1) as E1.
      pose proof (noghost_ev_flush2 r s0 p q0 e q' Hg Hp H0 F2) as E2.
      rewrite <- E0.
      rewrite <- (fst_Nc Loc Sh bot sh_eq_dec u K js (ev e (run p s0))),
              <- (fst_Nc Loc Sh bot sh_eq_dec u K js (ev e q0)), <- E1, <- E2.
      reflexivity.
    - intros Hxc p e q Hp Hq.
      pose proof (noghost_flushes r s0 p q Hg Hp Hq) as E0.
      assert (O1 : OKw r (p ++ PW [] ++ [AEv E e])) by exact (ev_ok r p [] e Hp ltac:(constructor)).
      destruct (flushR_flushes r s0 _ Hf O1) as [q1 F1]. rewrite ev_after_flush in F1.
      destruct (flushR_ev2 r s0 p q e Hf Hp Hq) as [q2 F2].
      pose proof (noghost_ev_flush r s0 p e q1 Hg Hp F1) as E1.
      pose proof (noghost_ev_flush2 r s0 p q e q2 Hg Hp Hq F2) as E2.
      assert (Eq : q1 = q2).
      { rewrite E1, E2, E0. apply Nc_fst. exact (Hxc p e Hp). }
      exists q1. split; [exact F1 | rewrite Eq; exact F2].
  Qed.

  (* Without ghosts, the quiescent machine IS the FedMachine. *)
  Theorem noghost_qm : forall r s0, NoGhostR' r s0 -> forall es p q, OKw r p ->
    QM (run p s0) es q -> q = FM' es (NC (run p s0)).
  Proof.
    intros r s0 Hg es. induction es as [| e es IH]; intros p q Hp H.
    - exact (noghost_flushes r s0 p q Hg Hp H).
    - destruct H as [s' [Hs Hm]].
      pose proof (noghost_flushes r s0 p s' Hg Hp Hs) as E0.
      destruct Hs as [c [Hc [R _]]].
      pose proof (IH (p ++ PW c ++ [AEv E e]) q (ev_ok r p c e Hp Hc)) as X.
      rewrite ev_after_flush, R in X. rewrite (X Hm), FM_cons, E0. reflexivity.
  Qed.

  Theorem noghost_qmconv_iff : forall r s0, FlushR' r s0 -> NoGhostR' r s0 ->
    (QMConv s0 <-> FMConv' (NC s0)).
  Proof.
    intros r s0 Hf Hg. split.
    - intros Hh es1 es2 Ht.
      destruct (qm_exists r s0 Hf es1 [] ltac:(constructor)) as [q1 M1].
      pose proof (Hh es1 es2 Ht q1 M1) as M2.
      pose proof (noghost_qm r s0 Hg es1 [] q1 ltac:(constructor) M1) as E1.
      pose proof (noghost_qm r s0 Hg es2 [] q1 ltac:(constructor) M2) as E2.
      transitivity q1; [symmetry; exact E1 | exact E2].
    - intros Hm es1 es2 Ht q M1.
      destruct (qm_exists r s0 Hf es2 [] ltac:(constructor)) as [q2 M2].
      pose proof (noghost_qm r s0 Hg es1 [] q ltac:(constructor) M1) as E1.
      pose proof (noghost_qm r s0 Hg es2 [] q2 ltac:(constructor) M2) as E2.
      assert (Eq : q = q2) by (rewrite E1, E2; exact (Hm es1 es2 Ht)).
      rewrite Eq. exact M2.
  Qed.

  (* quiet_conv_iff (DistributedCycles.v), rederived as the ghost-free case. *)
  Theorem quiet_conv_recovered : forall s0, FlushR' false s0 -> NoGhostR' false s0 ->
    (DConvQ' false s0 <-> XUcR' false s0 /\ FMConv' (NC s0)).
  Proof.
    intros s0 Hf Hg. split.
    - intros Hc. destruct (proj1 (conv_quiet_exact s0) (conj Hf Hc)) as [_ [_ [Hx Hh]]].
      split; [exact (proj1 (noghost_flushxu_iff false s0 Hf Hg) Hx) |].
      exact (proj1 (noghost_qmconv_iff false s0 Hf Hg) Hh).
    - intros [Hx Hm].
      refine (proj2 (proj2 (conv_quiet_exact s0) _)).
      split; [exact Hf |]. split; [exact (noghost_flushdet false s0 Hg) |].
      split; [exact (proj2 (noghost_flushxu_iff false s0 Hf Hg) Hx) |].
      exact (proj2 (noghost_qmconv_iff false s0 Hf Hg) Hm).
  Qed.

  (* Agreement with the FedMachine is convergence plus canonical fidelity to Lfp. *)
  Theorem agree_conv_noghost : forall s0, FlushR' false s0 ->
    ((DAgreeQ' false s0 /\ DConvQ' false s0) <-> (DConvQ' false s0 /\ NoGhostR' false s0)).
  Proof.
    intros s0 Hf. split.
    - intros [Ha Hc]. split; [exact Hc |]. intros w Hw Hq. rewrite (Ha w Hw Hq).
      rewrite (FM_normal Loc Sh bot sh_eq_dec u K js E ev);
        [reflexivity | symmetry; apply (Nc_idem Loc Sh bot sh_eq_dec u K js)].
    - intros [Hc Hg]. split; [| exact Hc].
      apply (quiet_agree_suff Loc Sh bot sh_eq_dec u K js E ev false s0); [| exact Hg].
      exact (proj1 (proj1 (quiet_conv_recovered s0 Hf Hg) Hc)).
  Qed.

  (* flush_fed_iff (DistributedCyclesExact.v), rederived through conv_quiet_exact. *)
  Theorem flush_fed_recovered : forall s0,
    (FlushR' false s0 /\ DAgreeQ' false s0 /\ DConvQ' false s0) <->
    (XUcR' false s0 /\ FMConv' (NC s0) /\ FlushR' false s0 /\ NoGhostR' false s0).
  Proof.
    intros s0. split.
    - intros [Hf [Ha Hc]].
      destruct (proj1 (agree_conv_noghost s0 Hf) (conj Ha Hc)) as [_ Hg].
      destruct (proj1 (quiet_conv_recovered s0 Hf Hg) Hc) as [Hx Hm]. tauto.
    - intros [Hx [Hm [Hf Hg]]].
      pose proof (proj2 (quiet_conv_recovered s0 Hf Hg) (conj Hx Hm)) as Hc.
      destruct (proj2 (agree_conv_noghost s0 Hf) (conj Hc Hg)) as [Ha _]. tauto.
  Qed.
End Conv.

(* ======================================================================================= *)
(* Part 2. Determinacy of the ghost from soundness (the lattice hypotheses).                *)
(* ======================================================================================= *)

Section Lat.
  Set Default Proof Using "All".
  Variables Loc Sh : Type.
  Variable le : Sh -> Sh -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable bot : Sh.
  Hypothesis bot_least : forall x, le bot x.
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, le x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable F : Loc -> Sh -> Sh.
  Variable u : Loc -> nat -> Sh -> Sh.
  Hypothesis u_incr : forall l j x, sound Loc Sh le F l x -> le x (u l j x).
  Hypothesis u_sound : forall l j x, sound Loc Sh le F l x -> sound Loc Sh le F l (u l j x).
  Hypothesis u_mono : forall l j x y, le x y -> le (u l j x) (u l j y).
  Hypothesis u_fixed : forall l j x, F l x = x -> u l j x = x.
  Variable K : nat.
  Hypothesis K_big : height < K.
  Variable js : list nat.
  Hypothesis Hcov : Cover Loc Sh F u js.
  Variable E : Type.
  Variable ev : E -> Loc * Sh -> Loc * Sh.
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.

  Local Notation sw := (sweep Loc Sh u).
  Local Notation Sd := (sound Loc Sh le F).
  Local Notation run := (crun Loc Sh bot u E ev).
  Local Notation FlushDetAt' := (FlushDetAt Loc Sh bot u js E ev).
  Local Notation FlushDetR' := (FlushDetR Loc Sh bot u js E ev).
  Local Notation FlushXUR' := (FlushXUR Loc Sh bot u js E ev).
  Local Notation QMConv' := (QMConv Loc Sh bot u js E ev reg I).
  Local Notation FlushR' := (FlushR Loc Sh bot u js E ev).
  Local Notation DConvQ' := (DConvQ Loc Sh bot u js E ev reg I).
  Local Notation FairFlushR' := (FairFlushR Loc Sh bot u js E ev).
  Local Notation SoundR' := (SoundR Loc Sh le bot F u js E ev).
  Local Notation SandR' := (SandR Loc Sh le bot F u js E ev).

  Lemma sw_mono' : forall l c x y, le x y -> le (sw l c x) (sw l c y).
  Proof.
    intros l c. induction c as [| j c IH]; intros x y H; [exact H |]. simpl. apply IH. apply u_mono. exact H.
  Qed.

  Lemma sw_fixed' : forall l c p, F l p = p -> sw l c p = p.
  Proof.
    intros l c. induction c as [| j c IH]; intros p H; [reflexivity |]. simpl. rewrite (u_fixed l j p H).
    apply IH. exact H.
  Qed.

  Lemma sw_up' : forall l c x, Sd l x -> le x (sw l c x).
  Proof.
    intros l c. induction c as [| j c IH]; intros x H; [apply le_refl |]. simpl.
    eapply le_trans; [apply u_incr; exact H | apply IH; apply u_sound; exact H].
  Qed.

  (* A sandwiched state flushes only to the least fixed point above its sound lower bound s. *)
  Theorem sand_flushdet : forall l h, Sand Loc Sh le F l h -> FlushDetAt' (l, h).
  Proof.
    intros l h [s [Hs [Hsh Hh]]].
    assert (Key : forall c, Quiet Loc Sh u js (l, sw l c h) ->
              F l (sw l c h) = sw l c h /\ le s (sw l c h) /\
              (forall p, F l p = p -> le s p -> le (sw l c h) p)).
    { intros c Q. split; [apply Hcov; exact Q |]. split.
      - eapply le_trans; [apply (sw_up' l c s Hs) | apply sw_mono'; exact Hsh].
      - intros p Fp Hp. rewrite <- (sw_fixed' l c p Fp). apply sw_mono'. exact (Hh p Fp Hp). }
    intros q1 q2 [c1 [_ [R1 Q1]]] [c2 [_ [R2 Q2]]].
    rewrite crun_props in R1, R2. cbn [fst snd] in R1, R2. subst q1 q2.
    destruct (Key c1 Q1) as [F1 [L1 M1]]. destruct (Key c2 Q2) as [F2 [L2 M2]].
    f_equal. apply le_antisym; [apply M1; assumption | apply M2; assumption].
  Qed.

  Theorem sandr_flushdet : forall r s0, SandR' r s0 -> FlushDetR' r s0.
  Proof.
    intros r s0 Hs w q1 q2 Hw. pose proof (sand_flushdet _ _ (Hs w Hw)) as D.
    rewrite <- surjective_pairing in D. exact (D q1 q2).
  Qed.

  Theorem soundr_flushdet : forall r s0, SoundR' r s0 -> FlushDetR' r s0.
  Proof.
    intros r s0 Hs. apply sandr_flushdet. intros w Hw. exists (snd (run w s0)).
    split; [exact (Hs w Hw) |]. split; [apply le_refl | intros p _ Hp; exact Hp].
  Qed.

  Lemma soundr_flushR : forall r s0, SoundR' r s0 -> FlushR' r s0.
  Proof.
    intros r s0 Hs.
    exact (fairflushR_flushR Loc Sh le le_refl le_trans le_antisym bot bot_least rank rank_strict
             height rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov E ev reg I
             r s0
             (soundr_fairflush Loc Sh le le_refl le_trans le_antisym bot bot_least rank rank_strict
                height rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov E ev reg
                I r s0 Hs)).
  Qed.

  (* Under reachable soundness, FlushR and FlushDetR are free: convergence alone is exactly the
     flush-relative state descent and history descent. *)
  Theorem soundr_conv_iff : forall s0, SoundR' false s0 ->
    (DConvQ' false s0 <-> FlushXUR' false s0 /\ QMConv' s0).
  Proof.
    intros s0 Hs. pose proof (soundr_flushR false s0 Hs) as Hf.
    pose proof (soundr_flushdet false s0 Hs) as Hd.
    pose proof (conv_quiet_exact Loc Sh bot sh_eq_dec u K js E ev reg I s0) as X. tauto.
  Qed.

  (* The same exact condition with the operational flush (every fair schedule settles). *)
  Theorem fair_conv_exact : forall s0,
    (FairFlushR' false s0 /\ DConvQ' false s0) <->
    (FairFlushR' false s0 /\ FlushDetR' false s0 /\ FlushXUR' false s0 /\ QMConv' s0).
  Proof.
    intros s0.
    pose proof (fairflushR_flushR Loc Sh le le_refl le_trans le_antisym bot bot_least rank rank_strict
                  height rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov E ev reg
                  I false s0) as FF.
    pose proof (conv_quiet_exact Loc Sh bot sh_eq_dec u K js E ev reg I s0) as X.
    split.
    - intros [Hf Hc]. destruct (proj1 X (conj (FF Hf) Hc)) as [_ R]. tauto.
    - intros [Hf R]. destruct (proj2 X (conj (FF Hf) R)) as [_ Hc]. tauto.
  Qed.
End Lat.

(* ======================================================================================= *)
(* Part 3. Each conjunct is necessary.                                                      *)
(* ======================================================================================= *)

(* FlushR: on flip1 (the swap fa <-> fb, one fixed point fz) from fa, no reachable state ever
   quiesces, so FlushDetR, FlushXUR and QMConv hold vacuously and FlushR fails. *)
Lemma f1_reach : forall w t, OK fjs1 unit false w -> snd t <> fz ->
  snd (crun unit Fl fz fu1 unit fid w t) <> fz.
Proof.
  intros w t Hw. revert t. induction Hw as [| a w Ha _ IH]; intros t Ht; [exact Ht |].
  cbn [crun]. apply IH. destruct a as [e | j |].
  - exact Ht.
  - destruct t as [[] x]. cbn [cstep fst snd] in *. destruct j as [| j]; [| exact Ht].
    destruct x; simpl; congruence.
  - cbn in Ha. discriminate Ha.
Qed.

Lemma f1_noflush : forall t q, snd t <> fz -> ~ Flushes unit Fl fz fu1 fjs1 unit fid t q.
Proof.
  intros t q Ht [c [_ [R Q]]]. pose proof (Q 0 (or_introl eq_refl)) as S.
  rewrite <- R, crun_props in S. destruct t as [[] x]. cbn [fst snd] in Ht, S.
  apply (f1_sweep c x Ht). destruct (sweep unit Fl fu1 tt c x); simpl in S; congruence.
Qed.

Theorem flip_conv_noflush :
  FlushDetR unit Fl fz fu1 fjs1 unit fid false (tt, fa) /\
  FlushXUR unit Fl fz fu1 fjs1 unit fid false (tt, fa) /\
  QMConv unit Fl fz fu1 fjs1 unit fid (fun _ => 0) noI (tt, fa) /\
  ~ FlushR unit Fl fz fu1 fjs1 unit fid false (tt, fa) /\
  ~ (FlushR unit Fl fz fu1 fjs1 unit fid false (tt, fa) /\
     DConvQ unit Fl fz fu1 fjs1 unit fid (fun _ => 0) noI false (tt, fa)).
Proof.
  assert (N : forall w q, OK fjs1 unit false w ->
                ~ Flushes unit Fl fz fu1 fjs1 unit fid (crun unit Fl fz fu1 unit fid w (tt, fa)) q).
  { intros w q Hw. apply f1_noflush. apply f1_reach; [exact Hw | discriminate]. }
  destruct flip_noflush as (_ & _ & _ & _ & nF).
  split; [intros w q1 q2 Hw H1; destruct (N w q1 Hw H1) |].
  split; [intros p e q Hp Hq; destruct (N p q Hp Hq) |].
  split.
  { intros es1 es2 _ q H. destruct es1 as [| e es1].
    - destruct (N [] q ltac:(constructor) H).
    - destruct H as [s' [Hs _]]. destruct (N [] s' ltac:(constructor) Hs). }
  split; [exact nF | intros [H _]; exact (nF H)].
Qed.

(* FlushDetR: the flag cycle of FederationEventsCycles.v (sa := lb || sb, sb := la || sa) with
   both alarms clear, from the stale start (sa, sb) = (true, false), with identity events.
   Propagating A first reaches the least fixed point, propagating B first reaches the ghost
   (true, true); FlushR, FlushXUR and QMConv hold. *)
Definition ks0 : B2 * B2 := ((false, false), (true, false)).

Theorem fork_conv_nodet :
  FlushR B2 B2 cbot cu cts unit bid false ks0 /\
  FlushXUR B2 B2 cbot cu cts unit bid false ks0 /\
  QMConv B2 B2 cbot cu cts unit bid (fun _ => 0) noI ks0 /\
  Flushes B2 B2 cbot cu cts unit bid ks0 ((false, false), (false, false)) /\
  Flushes B2 B2 cbot cu cts unit bid ks0 ((false, false), (true, true)) /\
  ~ FlushDetR B2 B2 cbot cu cts unit bid false ks0 /\
  ~ (FlushR B2 B2 cbot cu cts unit bid false ks0 /\
     DConvQ B2 B2 cbot cu cts unit bid (fun _ => 0) noI false ks0).
Proof.
  assert (F0 : Flushes B2 B2 cbot cu cts unit bid ks0 ((false, false), (false, false))).
  { exists [0]. split; [repeat constructor; simpl; tauto |]. split; [reflexivity |].
    intros j Hj; destruct Hj as [<- | [<- | []]]; reflexivity. }
  assert (F1 : Flushes B2 B2 cbot cu cts unit bid ks0 ((false, false), (true, true))).
  { exists [1]. split; [repeat constructor; simpl; tauto |]. split; [reflexivity |].
    intros j Hj; destruct Hj as [<- | [<- | []]]; reflexivity. }
  assert (nD : ~ FlushDetR B2 B2 cbot cu cts unit bid false ks0).
  { intro H. pose proof (H [] _ _ ltac:(constructor) F0 F1) as X. discriminate X. }
  split; [apply c_flushR |].
  split.
  { intros p e q _ Hq. exists q. split; [exact Hq |].
    exact (flushes_quiet B2 B2 cbot ceq_dec cu 3 cts unit bid (fun _ => 0) noI q
             (flushes_qt B2 B2 cbot ceq_dec cu 3 cts unit bid (fun _ => 0) noI _ q Hq)). }
  split.
  { intros es1 es2 Ht q H.
    rewrite <- (none_tequiv unit (fun _ => 0) noI
                  ltac:(intros a b [X | X]; [apply X; reflexivity | exact X]) es1 es2 Ht).
    exact H. }
  split; [exact F0 |]. split; [exact F1 |]. split; [exact nD |].
  intros [_ Hc]. apply nD.
  exact (conv_flushdet B2 B2 cbot ceq_dec cu 3 cts unit bid (fun _ => 0) noI false ks0 Hc).
Qed.

(* FlushXUR: copy_xu_fails (one fixed point, so no ghost): CopyA reads A's stale shared flag. *)
Theorem copy_conv_noxu :
  FlushR B2 B2 cbot uu cts cpev cpcev false cps0 /\
  FlushDetR B2 B2 cbot uu cts cpev cpcev false cps0 /\
  QMConv B2 B2 cbot uu cts cpev cpcev cpnreg noI cps0 /\
  ~ FlushXUR B2 B2 cbot uu cts cpev cpcev false cps0 /\
  ~ (FlushR B2 B2 cbot uu cts cpev cpcev false cps0 /\
     DConvQ B2 B2 cbot uu cts cpev cpcev cpnreg noI false cps0).
Proof.
  destruct copy_xu_fails as (_ & Hff & Hg & Hm & nX & _).
  assert (Hf : FlushR B2 B2 cbot uu cts cpev cpcev false cps0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 K3 cts
             u_cover cpev cpcev cpnreg noI false cps0 Hff). }
  assert (nXU : ~ FlushXUR B2 B2 cbot uu cts cpev cpcev false cps0).
  { intro H. apply nX.
    exact (proj1 (noghost_flushxu_iff B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI false cps0
                    Hf Hg) H). }
  split; [exact Hf |].
  split; [exact (noghost_flushdet B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI false cps0 Hg) |].
  split; [exact (proj2 (noghost_qmconv_iff B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI false
                          cps0 Hf Hg) Hm) |].
  split; [exact nXU |].
  intros [_ Hc]. apply nXU.
  exact (conv_flushxu B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI false cps0 Hf Hc).
Qed.

(* QMConv: fm_conv_fails (one fixed point): SetA and ClrA are declared independent and do not
   commute. *)
Theorem fm_conv_noqm : forall s0,
  FlushR B2 B2 cbot uu cts sev scev false s0 /\
  FlushDetR B2 B2 cbot uu cts sev scev false s0 /\
  FlushXUR B2 B2 cbot uu cts sev scev false s0 /\
  ~ QMConv B2 B2 cbot uu cts sev scev snreg sI s0 /\
  ~ (FlushR B2 B2 cbot uu cts sev scev false s0 /\
     DConvQ B2 B2 cbot uu cts sev scev snreg sI false s0).
Proof.
  intros s0. destruct (fm_conv_fails false s0) as (Hff & Hx & Hg & nM & _).
  assert (Hf : FlushR B2 B2 cbot uu cts sev scev false s0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 K3 cts
             u_cover sev scev snreg sI false s0 Hff). }
  assert (nQ : ~ QMConv B2 B2 cbot uu cts sev scev snreg sI s0).
  { intro H. apply nM.
    exact (proj1 (noghost_qmconv_iff B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI false s0 Hf Hg) H). }
  split; [exact Hf |].
  split; [exact (noghost_flushdet B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI false s0 Hg) |].
  split; [exact (proj2 (noghost_flushxu_iff B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI false s0
                          Hf Hg) Hx) |].
  split; [exact nQ |].
  intros [_ Hc]. apply nQ.
  exact (conv_qmconv B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI false s0 Hf Hc).
Qed.

(* ======================================================================================= *)
(* Part 4. Instances: convergence on a ghost.                                               *)
(* ======================================================================================= *)

(* conv_ghost_normal is an instance: every conjunct holds, NoGhostR and agreement fail. The
   quiescent machine sends SetSA to the ghost; the FedMachine sends it to the least fixed point.
   The interleavings agree, on the quiescent machine's state rather than the FedMachine's. *)
Theorem conv_ghost_instance :
  FlushR B2 B2 cbot gu cts gev gcev false gs0 /\
  FlushDetR B2 B2 cbot gu cts gev gcev false gs0 /\
  FlushXUR B2 B2 cbot gu cts gev gcev false gs0 /\
  QMConv B2 B2 cbot gu cts gev gcev gnreg noI gs0 /\
  DConvQ B2 B2 cbot gu cts gev gcev gnreg noI false gs0 /\
  ~ NoGhostR B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  ~ DAgreeQ B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  QM B2 B2 cbot gu cts gev gcev gs0 [SetSA] ((false, false), (true, true)) /\
  FM B2 B2 cbot ceq_dec gu 3 cts gev gcev [SetSA] (Nc B2 B2 cbot ceq_dec gu 3 cts gs0) =
    ((false, false), (false, false)).
Proof.
  destruct conv_ghost_normal as (_ & Hff & _ & _ & Hc & nG & nA).
  assert (Hf : FlushR B2 B2 cbot gu cts gev gcev false gs0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec gF gu gu_incr gu_sound gu_mono gu_fixed 3 K3 cts
             g_cover gev gcev gnreg noI false gs0 Hff). }
  destruct (proj1 (conv_quiet_exact B2 B2 cbot ceq_dec gu 3 cts gev gcev gnreg noI gs0) (conj Hf Hc))
    as [_ [Hd [Hx Hh]]].
  split; [exact Hf |]. split; [exact Hd |]. split; [exact Hx |]. split; [exact Hh |].
  split; [exact Hc |]. split; [exact nG |]. split; [exact nA |].
  split; [| vm_compute; reflexivity].
  exists gs0. split.
  - exists []. split; [constructor |]. split; [reflexivity |].
    intros j Hj; destruct Hj as [<- | [<- | []]]; reflexivity.
  - exists [1]. split; [repeat constructor; simpl; tauto |]. split; [vm_compute; reflexivity |].
    intros j Hj; destruct Hj as [<- | [<- | []]]; vm_compute; reflexivity.
Qed.

(* A copy event on A and a raise on B, on the network of conv_ghost_normal (sa := lb || sa || sb,
   sb := la || sa), from the ghost start ((false,false),(true,true)). The two events are on
   different registries, so they are declared independent. A's flag stays set, so CopyA always
   sets A's alarm and the events commute in the distributed model; the FedMachine resets the flag
   to the least fixed point, so there CopyA reads it unset unless B's alarm is up. *)
Inductive xev : Type := XCopyA | XRaiseB.
Definition xreg (e : xev) : bool := match e with XCopyA => true | XRaiseB => false end.
Definition xsig (e : xev) (x : bool * bool) : bool * bool :=
  match e with XCopyA => (snd x, snd x) | XRaiseB => (true, snd x) end.
Definition xcev : xev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset xev xreg xsig.
Definition xnreg : xev -> nat := nreg bool renc xev xreg.
Definition xs0 : B2 * B2 := ((false, false), (true, true)).
Definition isA (e : xev) : bool := match e with XCopyA => true | XRaiseB => false end.
Definition isB (e : xev) : bool := negb (isA e).

Lemma existsb_perm : forall (A : Type) (f : A -> bool) l1 l2,
  Permutation l1 l2 -> existsb f l1 = existsb f l2.
Proof.
  intros A f l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - destruct (f x), (f y); reflexivity.
  - congruence.
Qed.

Lemma x_inv : forall w t, OK cts xev false w -> fst (snd t) = true ->
  fst (snd (crun B2 B2 cbot gu xev xcev w t)) = true /\
  fst (fst (crun B2 B2 cbot gu xev xcev w t)) = fst (fst t) || existsb isA (cevs xev w) /\
  snd (fst (crun B2 B2 cbot gu xev xcev w t)) = snd (fst t) || existsb isB (cevs xev w).
Proof.
  intros w t Hw. revert t. induction Hw as [| a w Ha _ IH]; intros t Ht.
  - cbn [crun cevs existsb]. rewrite !orb_false_r. split; [exact Ht | split; reflexivity].
  - cbn [crun]. destruct t as [[x y] [c d]]. cbn [fst snd] in Ht. subst c.
    destruct a as [e | j |]; [| | cbn in Ha; discriminate Ha].
    + assert (Hs : fst (snd (cstep B2 B2 cbot gu xev xcev (AEv xev e) ((x, y), (true, d)))) = true)
        by (destruct e; reflexivity).
      destruct (IH _ Hs) as [A [B C]]. split; [exact A |].
      split; [etransitivity; [exact B |] | etransitivity; [exact C |]];
        destruct e; destruct x, y, d; reflexivity.
    + assert (Hs : fst (snd (cstep B2 B2 cbot gu xev xcev (AProp xev j) ((x, y), (true, d)))) = true)
        by (destruct j as [| [| j]]; destruct x, y, d; reflexivity).
      destruct (IH _ Hs) as [A [B C]]. split; [exact A |].
      split; [etransitivity; [exact B |] | etransitivity; [exact C |]];
        destruct j as [| [| j]]; destruct x, y, d; reflexivity.
Qed.

Lemma x_quiet : forall t, fst (snd t) = true -> Quiet B2 B2 gu cts t -> snd (snd t) = true.
Proof.
  intros [[x y] [c d]] Hc Hq. cbn [fst snd] in Hc |- *. subst c.
  pose proof (Hq 1 (or_intror (or_introl eq_refl))) as X.
  destruct d; [reflexivity |]. destruct x; vm_compute in X; discriminate X.
Qed.

(* Convergence on a ghost without any of the conditions of quiet_conv_suff: every fair schedule
   settles and quiescent interleavings agree (so all four conjuncts of conv_quiet_exact hold),
   while XUcR, FedMachine convergence, NoGhostR and agreement fail. *)
Theorem ghost_conv_not_fed :
  gF (fst xs0) (snd xs0) = snd xs0 /\
  snd xs0 <> Lfp B2 B2 cbot ceq_dec gu 3 cts (fst xs0) /\
  FairFlushR B2 B2 cbot gu cts xev xcev false xs0 /\
  DConvQ B2 B2 cbot gu cts xev xcev xnreg noI false xs0 /\
  FlushDetR B2 B2 cbot gu cts xev xcev false xs0 /\
  FlushXUR B2 B2 cbot gu cts xev xcev false xs0 /\
  QMConv B2 B2 cbot gu cts xev xcev xnreg noI xs0 /\
  ~ XUcR B2 B2 cbot ceq_dec gu 3 cts xev xcev false xs0 /\
  ~ FMConv B2 B2 cbot ceq_dec gu 3 cts xev xcev xnreg noI (Nc B2 B2 cbot ceq_dec gu 3 cts xs0) /\
  ~ NoGhostR B2 B2 cbot ceq_dec gu 3 cts xev xcev false xs0 /\
  ~ DAgreeQ B2 B2 cbot ceq_dec gu 3 cts xev xcev false xs0.
Proof.
  assert (Q0 : Quiet B2 B2 gu cts xs0) by (intros j Hj; destruct Hj as [<- | [<- | []]]; reflexivity).
  assert (Hff : FairFlushR B2 B2 cbot gu cts xev xcev false xs0).
  { intros w _. apply (step_sound_fairflush B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least
                         crank crank_strict 2 crank_bound ceq_dec gF gu gu_incr gu_sound gu_mono
                         gu_fixed 3 K3 cts g_cover gu_step_sound). }
  assert (Hf : FlushR B2 B2 cbot gu cts xev xcev false xs0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec gF gu gu_incr gu_sound gu_mono gu_fixed 3 K3 cts
             g_cover xev xcev xnreg noI false xs0 Hff). }
  assert (Hc : DConvQ B2 B2 cbot gu cts xev xcev xnreg noI false xs0).
  { intros w1 w2 O1 O2 Ht Q1 Q2.
    destruct (x_inv w1 xs0 O1 eq_refl) as [A1 [L1 M1]].
    destruct (x_inv w2 xs0 O2 eq_refl) as [A2 [L2 M2]].
    pose proof (x_quiet _ A1 Q1) as D1. pose proof (x_quiet _ A2 Q2) as D2.
    pose proof (tequiv_perm _ _ _ Ht) as P.
    rewrite (existsb_perm _ isA _ _ P) in L1. rewrite (existsb_perm _ isB _ _ P) in M1.
    destruct (crun B2 B2 cbot gu xev xcev w1 xs0) as [[a1 b1] [c1 d1]].
    destruct (crun B2 B2 cbot gu xev xcev w2 xs0) as [[a2 b2] [c2 d2]].
    simpl in *. congruence. }
  destruct (proj1 (conv_quiet_exact B2 B2 cbot ceq_dec gu 3 cts xev xcev xnreg noI xs0) (conj Hf Hc))
    as [_ [Hd [Hx Hh]]].
  split; [reflexivity |]. split; [vm_compute; discriminate |].
  split; [exact Hff |]. split; [exact Hc |]. split; [exact Hd |]. split; [exact Hx |].
  split; [exact Hh |].
  split.
  { intro H. pose proof (H [] XCopyA ltac:(constructor)) as X. unfold XUc in X. vm_compute in X.
    discriminate X. }
  split.
  { intro H.
    assert (T : tequiv (Ifd xev xnreg noI) [XCopyA; XRaiseB] [XRaiseB; XCopyA]).
    { apply teq_swap with (l := @nil xev) (r := @nil xev). left. intro X. vm_compute in X.
      discriminate X. }
    pose proof (H _ _ T) as X. vm_compute in X. discriminate X. }
  split.
  - intro H. pose proof (H [] ltac:(constructor) Q0) as X. vm_compute in X. discriminate X.
  - intro H. pose proof (H [] ltac:(constructor) Q0) as X. vm_compute in X. discriminate X.
Qed.

(* Non-vacuity without a ghost: raise-only events from a FedMachine normal form. Every reachable
   state is sound (so soundr_conv_iff applies), no ghost is reachable, and every conjunct holds. *)
Theorem raise_only_conv : forall l,
  SoundR B2 B2 cle cbot cF cu cts DistributedCycles.rev rcev false (l, dLfp l) /\
  NoGhostR B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev false (l, dLfp l) /\
  FlushR B2 B2 cbot cu cts DistributedCycles.rev rcev false (l, dLfp l) /\
  FlushDetR B2 B2 cbot cu cts DistributedCycles.rev rcev false (l, dLfp l) /\
  FlushXUR B2 B2 cbot cu cts DistributedCycles.rev rcev false (l, dLfp l) /\
  QMConv B2 B2 cbot cu cts DistributedCycles.rev rcev rnreg rI (l, dLfp l).
Proof.
  intros l. destruct (raise_only_exact l false) as (Hs & _ & Hff & Ha & Hc).
  pose proof (c_flushR DistributedCycles.rev rcev false (l, dLfp l)) as Hf.
  destruct (proj1 (flush_fed_recovered B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev rnreg rI
                     (l, dLfp l)) (conj Hf (conj Ha Hc))) as [_ [_ [_ Hg]]].
  destruct (proj1 (conv_quiet_exact B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev rnreg rI
                     (l, dLfp l)) (conj Hf Hc)) as [_ [Hd [Hx Hh]]].
  tauto.
Qed.
