(* DistributedCycles.v: the distributed propagation model on MONOTONE CYCLIC federations
   (REGIME-AUDIT.md section 8, the cyclic half of gap 1). Axiom-free.

   The gap. DistributedExact.v gives the exact condition for the distributed model of an ACYCLIC
   federation. On a cycle the repair equations have several solutions (bottom_matters), and gsm's
   FedMachine picks the least one: normalizeCyclic resets every shared value to bottom before its
   Kleene sweeps. Distributed nodes have no such reset. A propagation step overwrites a target's
   shared part with the image of its sources' CURRENT states, which may be stale or mid-iteration.

   Model. A state is (l, h): l the locals of every node, h every shared value, in a finite lattice
   (le, bot, rank <= height). F l is the synchronous repair and u l j the repair of target j alone,
   with the hypotheses of FederationEventsCycles.v (u_incr, u_sound, u_mono, u_fixed, Cover).
     Lfp l    := kleene l js K bot, the least fixed point of F l (Lfp_is_lfp).
     Nc (l,h) := (l, Lfp l): FedMachine.Normalize (phase 1 is the identity on the valid states the
                 nodes hold). The FedMachine step is Nc o ev e (FederationEventsCycles.gstep).
     Actions  : AEv e (a local event: any function ev e of the state, so it may read and write
                shared values), AProp j (h := u l j h), AReset (h := bot, every shared value at
                once; only in the protocol of Q3).
     Fair sg  : an infinite schedule of targets naming every target infinitely often.
     Quiet t  : no propagation step changes t (equivalently F l h = h: qstable_iff).

   Q1. Repair without events (locals l fixed; prs sg n h0 is the shared part after n steps).
     q1_from_bot      : from bottom, every fair schedule settles at Lfp l (Chaotic.v in fair-schedule
                        form).
     q1_below         : from ANY start h0 <= Lfp l, sound or not, every fair schedule settles at Lfp l.
     q1_sound_settles : from a sound start (h0 <= F l h0: bottom, any fixed point), every fair
                        schedule settles at the least fixed point ABOVE h0.
     q1_sound_iff     : for a sound start and a fair schedule, the run reaches Lfp l iff h0 <= Lfp l.
     q1_stuck         : if h0 >= p for a fixed point p <> Lfp l, no schedule ever reaches Lfp l.
     q1_unique_iff    : (given a top element and the dual step laws) every fair schedule from EVERY
                        start settles at Lfp l iff F l has exactly one fixed point.
     dist_schedule_dependence : on the flag cycle, an unsound stale start that settles at the least
                        fixed point under one fair schedule and at a ghost under another.
     dist_ring_livelock : on a monotone 3-cycle, a fair schedule from a stale start never reaches
                        any quiescent state.
     So distributed nodes reach gsm's least fixed point exactly from below it; above a non-least
     fixed point they stay there (a GHOST); from an arbitrary stale start the outcome can depend on
     the schedule, or never arrive.

   Q2. Events without resets (r = false). For a start s0 and allowed words w (OK r w):
     XUc t e   := fst (ev e t) = fst (ev e (Nc t)): the event's local outcome does not depend on
                  whether the node's shared part is stale or at the least fixed point;
     XUcR r s0 := XUc at every reachable state (the cyclic reachable XU);
     DAgreeQ   : every reachable quiescent state is the FedMachine state for the same events;
     DConvQ    : reachable quiescent states of words with trace-equivalent events are equal;
     NoGhostR  : every reachable quiescent state holds Lfp of its locals;
     FlushR    : from every reachable state some propagation word reaches quiescence;
     LowR      : every reachable state holds a shared part <= Lfp of its locals.
     track            : XUcR -> Nc (crun w s0) = FM (cevs w) (Nc s0) on every reachable word.
     quiet_ghost_only : under XUcR, a quiescent state has the FedMachine's locals and a shared part
                        that is a fixed point at or above the FedMachine's: ghosts are the only way
                        to disagree.
     quiet_agree_iff  : FlushR -> (DAgreeQ <-> XUcR /\ NoGhostR).
     quiet_conv_iff   : FlushR -> NoGhostR -> (DConvQ <-> XUcR /\ FMConv (Nc s0)).
     low_agree_iff, low_conv_iff : LowR implies FlushR and NoGhostR, so under LowR
                        DAgreeQ <-> XUcR and DConvQ <-> XUcR /\ FMConv (Nc s0).
     evlow_lowr, infl_evlow : LowR follows from EvLow (events keep a state below the least fixed
                        point of its locals), which INFLATIONARY events satisfy (they raise locals in
                        an order the repair is monotone in and never raise shared values).
     uniq_noghost, uniq_agree : when F l has one fixed point for every l, no ghost exists, so
                        XUcR gives DAgreeQ (and DConvQ with FMConv) with no other hypothesis.
     lens_quiet       : gsm's per-target C1cyc + C2cyc, over a set Hs covering every reachable
                        shared value, plus LowR, give DConvQ and DAgreeQ.
     dist_cyc_ghost   : counterexample. On the flag cycle with raise and clear events, C1cyc, C2cyc,
                        XUcR (from every start) and FedMachine convergence all hold, yet the word
                        RaiseA; propagate B; propagate A; ClearA is quiescent at the ghost
                        ((false,false),(true,true)), while the FedMachine, and the same events
                        flushed later, give ((false,false),(false,false)). DAgreeQ, DConvQ, NoGhostR
                        and LowR fail. The cyclic analog of the acyclic exact condition (reachable XU
                        plus FedMachine convergence) and gsm's per-target checks are not enough.
     dist_cyc_raise_only : the same cycle with raise-only events: LowR, DConvQ, DAgreeQ hold.
     dist_cyc_unique_no_reset : a registry cycle without shared-value feedback (sa := lb,
                        sb := la || sa) has one fixed point for every l, so with the same raise and
                        clear events every quiescent interleaving agrees with the FedMachine.
     The gap left: without LowR the exact statements keep the reachable hypotheses FlushR (and
     NoGhostR for DConvQ). FlushR can fail on a general lattice, and the only per-event check given
     for NoGhostR is EvLow.

   Q3. Reset epochs (r = true). EP = AReset followed by K sweeps of every target.
     EP_run      : crun EP t = Nc t.   epoch_flush : any reset followed by propagation to quiescence
                   ends at Nc t (and q1_from_bot: every fair schedule after the reset gets there).
     DistAgreeE  : Nc (crun w s0) = FM (cevs w) (Nc s0)    (compare after a final epoch);
     DistConvE   : trace-equivalent events give equal states after a final epoch.
     epoch_agree_iff : DistAgreeE true s0 <-> XUcR true s0.
     epoch_conv_iff  : DistConvE true s0 <-> XUcR true s0 /\ FMConv (Nc s0)
                       (the cyclic form of DistributedExact.dist_exact_tc).
     lens_epoch  : C1cyc + C2cyc over Hs covering the reachable shared values give DistConvE and
                   DistAgreeE (lens_xucr, lens_fmconv); hs_reach: it suffices that Hs contains the
                   start's values, bottom, what propagation writes (the images) and what events
                   write.
     dist_cyc_epoch_fix : on the ghost federation every run agrees with the FedMachine after a final
                   epoch, from every start; a staggered reset (A resets while B still holds the
                   ghost) re-creates the ghost in one propagation step, so the reset is a barrier.

   States are pairs compared with Leibniz equality; no extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.Federation NC.FederationEventsCycles NC.FederationEventsCyclesCheck.
Import ListNotations.

(* ======================================================================================= *)
(* Part 1. Fair asynchronous schedules of coordinate updates (generic).                     *)
(* ======================================================================================= *)

Section Fair.
  Variable Sh : Type.
  Variable le : Sh -> Sh -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, le x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable up : nat -> Sh -> Sh.          (* the propagation step of one target *)
  Variable js : list nat.                 (* the targets *)

  (* An infinite schedule: every step names a target, and every target is named infinitely
     often. *)
  Definition Fair (sg : nat -> nat) : Prop :=
    (forall n, In (sg n) js) /\ (forall j n, In j js -> exists m, n <= m /\ sg m = j).

  (* The shared values after the first n steps of the schedule. *)
  Fixpoint prs (sg : nat -> nat) (n : nat) (h : Sh) : Sh :=
    match n with 0 => h | S n' => up (sg n') (prs sg n' h) end.

  (* Quiescent: no propagation step changes anything. *)
  Definition Stable (h : Sh) : Prop := forall j, In j js -> up j h = h.

  (* The run settles at q: from some step on, the state is q. *)
  Definition Settles (sg : nat -> nat) (h0 q : Sh) : Prop :=
    exists N, forall n, N <= n -> prs sg n h0 = q.

  Lemma stab_dec_l : forall (l : list nat) h,
    {forall j, In j l -> up j h = h} + {exists j, In j l /\ up j h <> h}.
  Proof.
    induction l as [| a l IH]; intros h.
    - left. intros j [].
    - destruct (sh_eq_dec (up a h) h) as [Ea | Na].
      + destruct (IH h) as [Hs | Hn].
        * left. intros j [<- | Hj]; [exact Ea | apply Hs; exact Hj].
        * right. destruct Hn as [j [Hj Hn]]. exists j. split; [right; exact Hj | exact Hn].
      + right. exists a. split; [left; reflexivity | exact Na].
  Defined.

  Lemma rk_mono : forall x y, le x y -> rank x <= rank y.
  Proof.
    intros x y H. destruct (sh_eq_dec x y) as [-> | Ne]; [lia |].
    apply Nat.lt_le_incl. apply rank_strict; assumption.
  Qed.

  Lemma prs_S : forall sg n h, prs sg (S n) h = up (sg n) (prs sg n h).
  Proof. reflexivity. Qed.

  Lemma prs_mono : (forall j x y, le x y -> le (up j x) (up j y)) ->
    forall sg n x y, le x y -> le (prs sg n x) (prs sg n y).
  Proof.
    intros Hm sg n. induction n as [| n IH]; intros x y H; [exact H |].
    simpl. apply Hm. apply IH. exact H.
  Qed.

  Lemma prs_fixed : forall sg q, (forall j, up j q = q) -> forall n, prs sg n q = q.
  Proof.
    intros sg q Hq n. induction n as [| n IH]; [reflexivity |]. simpl. rewrite IH. apply Hq.
  Qed.

  Section Run.
    Variable P : Sh -> Prop.
    Hypothesis P_up : forall j x, P x -> P (up j x).
    Hypothesis P_incr : forall j x, P x -> le x (up j x).
    Variable sg : nat -> nat.
    Hypothesis Hf : Fair sg.
    Variable h0 : Sh.
    Hypothesis H0 : P h0.

    Lemma run_P : forall n, P (prs sg n h0).
    Proof. induction n as [| n IH]; [exact H0 | simpl; apply P_up; exact IH]. Qed.

    Lemma run_up : forall d n, le (prs sg n h0) (prs sg (d + n) h0).
    Proof.
      induction d as [| d IH]; intros n; [apply le_refl |].
      eapply le_trans; [apply IH |]. simpl. apply P_incr. apply run_P.
    Qed.

    Lemma run_progress : forall n, Stable (prs sg n h0) \/
      exists m, n < m /\ rank (prs sg n h0) < rank (prs sg m h0).
    Proof.
      intros n. destruct (stab_dec_l js (prs sg n h0)) as [Hs | [j [Hj Hn]]]; [left; exact Hs |].
      right. destruct (proj2 Hf j n Hj) as [m [Hm Em]].
      exists (S m). split; [lia |].
      assert (Le : le (prs sg n h0) (prs sg m h0)).
      { replace m with ((m - n) + n) by lia. apply run_up. }
      rewrite prs_S, Em.
      destruct (sh_eq_dec (prs sg m h0) (prs sg n h0)) as [Eq | Ne].
      - rewrite Eq. apply rank_strict; [apply P_incr; apply run_P |].
        intro H. apply Hn. symmetry. exact H.
      - pose proof (rank_strict _ _ Le (fun H => Ne (eq_sym H))) as R.
        pose proof (rk_mono _ _ (P_incr j _ (run_P m))) as R2. lia.
    Qed.

    Lemma run_reaches : forall k n, height - rank (prs sg n h0) <= k ->
      exists N, n <= N /\ Stable (prs sg N h0).
    Proof.
      induction k as [| k IH]; intros n Hk.
      - destruct (run_progress n) as [Hs | [m [Hm Hr]]]; [exists n; split; [lia | exact Hs] |].
        pose proof (rank_bound (prs sg m h0)). lia.
      - destruct (run_progress n) as [Hs | [m [Hm Hr]]]; [exists n; split; [lia | exact Hs] |].
        destruct (IH m) as [N [HN Hs]]; [lia |]. exists N. split; [lia | exact Hs].
    Qed.

    Lemma run_stays : forall N, Stable (prs sg N h0) -> forall d, prs sg (d + N) h0 = prs sg N h0.
    Proof.
      intros N Hs d. induction d as [| d IH]; [reflexivity |].
      simpl. rewrite IH. apply Hs. apply (proj1 Hf).
    Qed.

    (* Under a fair schedule, a run that only moves up (an invariant P on which every step is
       inflationary) settles at a quiescent state satisfying P. *)
    Theorem fair_settles : exists N, Stable (prs sg N h0) /\ P (prs sg N h0) /\
      forall n, N <= n -> prs sg n h0 = prs sg N h0.
    Proof.
      destruct (run_reaches (height - rank h0) 0) as [N [_ Hs]]; [simpl; lia |].
      exists N. split; [exact Hs |]. split; [apply run_P |].
      intros n Hn. replace n with ((n - N) + N) by lia. apply run_stays. exact Hs.
    Qed.
  End Run.
End Fair.

(* ======================================================================================= *)
(* Part 2. Repair without events (Q1): what fair asynchronous propagation converges to.    *)
(* ======================================================================================= *)

Section DistCyc.
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

  (* gsm's FedMachine normal form (phase 1 is the identity on the valid states the nodes hold):
     reset every shared value to bottom, then Kleene sweeps. Lfp l is its shared part. *)
  Definition Lfp (l : Loc) : Sh := kleene Loc Sh sh_eq_dec u l js K bot.
  Definition Nc : Loc * Sh -> Loc * Sh := Ncyc_with Loc Sh bot sh_eq_dec u (fun s => s) K js.

  Lemma Nc_eq : forall t, Nc t = (fst t, Lfp (fst t)).
  Proof. reflexivity. Qed.

  Lemma Lfp_is_lfp : forall l, is_lfp le (F l) (Lfp l).
  Proof.
    intros l.
    exact (proj2 (cyc_N_lfp Loc Sh le le_refl le_trans bot bot_least rank rank_strict height
                    rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed (fun s => s) K K_big js
                    Hcov (l, bot))).
  Qed.

  Lemma Lfp_fixed : forall l, F l (Lfp l) = Lfp l.
  Proof. intros l. exact (proj1 (Lfp_is_lfp l)). Qed.

  Lemma Lfp_least : forall l p, F l p = p -> le (Lfp l) p.
  Proof. intros l p H. exact (proj2 (Lfp_is_lfp l) p H). Qed.

  Definition QStable (l : Loc) (h : Sh) : Prop := Stable Sh (u l) js h.

  Lemma qstable_iff : forall l h, QStable l h <-> F l h = h.
  Proof.
    intros l h. split; [intro H; apply Hcov; exact H |].
    intros H j _. apply u_fixed. exact H.
  Qed.

  Lemma Lfp_stable : forall l, QStable l (Lfp l).
  Proof. intros l. apply qstable_iff. apply Lfp_fixed. Qed.

  Lemma below_u : forall l j h, le h (Lfp l) -> le (u l j h) (Lfp l).
  Proof. intros l j h H. rewrite <- (u_fixed l j (Lfp l) (Lfp_fixed l)). apply u_mono. exact H. Qed.

  Let Run (l : Loc) := prs Sh (u l).

  (* The invariant of a run from a sound start h0: sound, above h0, below every fixed point
     above h0. *)
  Definition PA (l : Loc) (h0 x : Sh) : Prop :=
    sound Loc Sh le F l x /\ le h0 x /\ (forall p, F l p = p -> le h0 p -> le x p).

  Lemma PA_up : forall l h0 j x, PA l h0 x -> PA l h0 (u l j x).
  Proof.
    intros l h0 j x [Hs [Hb Hp]]. split; [apply u_sound; exact Hs |].
    split; [eapply le_trans; [exact Hb | apply u_incr; exact Hs] |].
    intros p Fp Hp0. rewrite <- (u_fixed l j p Fp). apply u_mono. apply Hp; assumption.
  Qed.

  (* Q1(a). From a sound start, every fair schedule settles at the LEAST FIXED POINT ABOVE THE
     START. *)
  Theorem q1_sound_settles : forall l h0 sg, sound Loc Sh le F l h0 -> Fair js sg ->
    exists q, (F l q = q /\ le h0 q /\ (forall p, F l p = p -> le h0 p -> le q p)) /\
              Settles Sh (u l) sg h0 q.
  Proof.
    intros l h0 sg Hs Hf.
    assert (H0 : PA l h0 h0) by (split; [exact Hs | split; [apply le_refl | intros; assumption]]).
    destruct (fair_settles Sh le le_refl le_trans rank rank_strict height rank_bound sh_eq_dec
                (u l) js (PA l h0) (PA_up l h0) (fun j x Hx => u_incr l j x (proj1 Hx)) sg Hf h0 H0)
      as [N [St [[_ [Hb Hp]] Ht]]].
    exists (prs Sh (u l) sg N h0). split.
    - split; [apply qstable_iff; exact St |]. split; [exact Hb | exact Hp].
    - exists N. exact Ht.
  Qed.

  (* Q1(b). From bottom (gsm's reset), every fair schedule settles at the least fixed point. *)
  Theorem q1_from_bot : forall l sg, Fair js sg -> Settles Sh (u l) sg bot (Lfp l).
  Proof.
    intros l sg Hf.
    destruct (q1_sound_settles l bot sg (bot_least _) Hf) as [q [[Fq [_ Hq]] [N HN]]].
    assert (E : q = Lfp l).
    { apply le_antisym; [apply Hq; [apply Lfp_fixed | apply bot_least] | apply Lfp_least; exact Fq]. }
    subst q. exists N. exact HN.
  Qed.

  (* Q1(c). From ANY start below the least fixed point (sound or not), every fair schedule
     settles at the least fixed point: the run is squeezed between the run from bottom and the
     least fixed point. *)
  Theorem q1_below : forall l h0 sg, le h0 (Lfp l) -> Fair js sg -> Settles Sh (u l) sg h0 (Lfp l).
  Proof.
    intros l h0 sg H Hf. destruct (q1_from_bot l sg Hf) as [N HN]. exists N. intros n Hn.
    apply le_antisym.
    - rewrite <- (prs_fixed Sh (u l) sg (Lfp l) (fun j => u_fixed l j _ (Lfp_fixed l)) n).
      apply (prs_mono Sh le (u l) (u_mono l)). exact H.
    - rewrite <- (HN n Hn). apply (prs_mono Sh le (u l) (u_mono l)). apply bot_least.
  Qed.

  Lemma sound_run : forall l h0 sg n, sound Loc Sh le F l h0 ->
    sound Loc Sh le F l (prs Sh (u l) sg n h0) /\ le h0 (prs Sh (u l) sg n h0).
  Proof.
    intros l h0 sg n Hs. induction n as [| n [IHs IHb]]; [split; [exact Hs | apply le_refl] |].
    simpl. split; [apply u_sound; exact IHs |]. eapply le_trans; [exact IHb | apply u_incr; exact IHs].
  Qed.

  (* Q1, exact for sound starts: a fair run from a sound start reaches the least fixed point iff
     the start is below it. Otherwise it settles at a strictly larger fixed point. *)
  Theorem q1_sound_iff : forall l h0 sg, sound Loc Sh le F l h0 -> Fair js sg ->
    ((exists n, prs Sh (u l) sg n h0 = Lfp l) <-> le h0 (Lfp l)).
  Proof.
    intros l h0 sg Hs Hf. split.
    - intros [n Hn]. rewrite <- Hn. exact (proj2 (sound_run l h0 sg n Hs)).
    - intros H. destruct (q1_below l h0 sg H Hf) as [N HN]. exists N. apply HN. lia.
  Qed.

  (* Q1(d). A start above a fixed point p other than the least one never reaches the least
     fixed point, under ANY schedule. *)
  Theorem q1_stuck : forall l p h0, F l p = p -> p <> Lfp l -> le p h0 ->
    forall sg n, prs Sh (u l) sg n h0 <> Lfp l.
  Proof.
    intros l p h0 Fp Ne H sg n E. apply Ne. apply le_antisym; [| apply Lfp_least; exact Fp].
    rewrite <- E. rewrite <- (prs_fixed Sh (u l) sg p (fun j => u_fixed l j _ Fp) n).
    apply (prs_mono Sh le (u l) (u_mono l)). exact H.
  Qed.

  (* Q1(e). Every start: with a top element and the dual step laws (which coordinate updates
     satisfy), every fair schedule from EVERY start settles at the least fixed point exactly when
     the repair has a unique fixed point. *)
  Section Top.
    Variable top : Sh.
    Hypothesis top_greatest : forall x, le x top.
    Hypothesis u_decr : forall l j x, le (F l x) x -> le (u l j x) x.
    Hypothesis u_cosound : forall l j x, le (F l x) x -> le (F l (u l j x)) (u l j x).

    Lemma dual_rank_strict : forall x y, le y x -> x <> y -> height - rank x < height - rank y.
    Proof.
      intros x y Hyx Ne. pose proof (rank_strict y x Hyx (fun E => Ne (eq_sym E))).
      pose proof (rank_bound x). lia.
    Qed.

    Theorem q1_unique_iff : forall l sg, Fair js sg ->
      ((forall h0, Settles Sh (u l) sg h0 (Lfp l)) <-> (forall p, F l p = p -> p = Lfp l)).
    Proof.
      intros l sg Hf. split.
      - intros H p Fp. destruct (H p) as [N HN]. rewrite <- (HN N (le_n N)).
        symmetry. apply prs_fixed. intro j. apply u_fixed. exact Fp.
      - intros Hu h0.
        destruct (q1_from_bot l sg Hf) as [N1 H1].
        assert (Ht : le (F l top) top) by apply top_greatest.
        destruct (fair_settles Sh (fun x y => le y x) le_refl
                    (fun x y z Hxy Hyz => le_trans z y x Hyz Hxy) (fun x => height - rank x)
                    dual_rank_strict
                    height (fun x => Nat.le_sub_l height (rank x)) sh_eq_dec (u l) js
                    (fun x => le (F l x) x) (u_cosound l) (u_decr l) sg Hf top Ht)
          as [N2 [St [_ H2]]].
        assert (Z : prs Sh (u l) sg N2 top = Lfp l) by (apply Hu; apply qstable_iff; exact St).
        exists (N1 + N2). intros n Hn. apply le_antisym.
        + rewrite <- Z, <- (H2 n ltac:(lia)). apply (prs_mono Sh le (u l) (u_mono l)). apply top_greatest.
        + rewrite <- (H1 n ltac:(lia)). apply (prs_mono Sh le (u l) (u_mono l)). apply bot_least.
    Qed.
  End Top.

  (* ===================================================================================== *)
  (* Part 3. The distributed model with local events (Q2) and reset epochs (Q3).          *)
  (* ===================================================================================== *)

  Lemma sweep_app : forall l a b x,
    sweep Loc Sh u l (a ++ b) x = sweep Loc Sh u l b (sweep Loc Sh u l a x).
  Proof. intros l a. induction a as [| j a IH]; intros b x; [reflexivity | simpl; apply IH]. Qed.

  Lemma sweep_stable : forall l c x, (forall j, In j c -> u l j x = x) -> sweep Loc Sh u l c x = x.
  Proof.
    intros l c. induction c as [| j c IH]; intros x H; [reflexivity |].
    simpl. rewrite (H j (or_introl eq_refl)). apply IH. intros k Hk. apply H. right. exact Hk.
  Qed.

  Lemma sweep_mono : forall l c x y, le x y -> le (sweep Loc Sh u l c x) (sweep Loc Sh u l c y).
  Proof.
    intros l c. induction c as [| j c IH]; intros x y H; [exact H |]. simpl. apply IH. apply u_mono. exact H.
  Qed.

  Lemma kleene_S : forall l n x, kleene Loc Sh sh_eq_dec u l js (S n) x =
    if stable_dec Loc Sh sh_eq_dec u l js x then x else kleene Loc Sh sh_eq_dec u l js n (sweep Loc Sh u l js x).
  Proof. reflexivity. Qed.

  Lemma kleene_stable : forall l n x, (forall j, In j js -> u l j x = x) ->
    kleene Loc Sh sh_eq_dec u l js n x = x.
  Proof.
    intros l n x H. destruct n as [| n]; [reflexivity |]. rewrite kleene_S.
    destruct (stable_dec Loc Sh sh_eq_dec u l js x) as [_ | [j [Hj Hn]]]; [reflexivity |].
    exfalso. apply Hn. apply H. exact Hj.
  Qed.

  (* K sweeps of every target are exactly gsm's Kleene loop (which stops early when a sweep
     changes nothing). *)
  Lemma iter_kleene : forall l n x,
    sweep Loc Sh u l (concat (repeat js n)) x = kleene Loc Sh sh_eq_dec u l js n x.
  Proof.
    intros l n. induction n as [| n IH]; intros x; [reflexivity |].
    change (concat (repeat js (S n))) with (js ++ concat (repeat js n)).
    rewrite sweep_app, kleene_S.
    destruct (stable_dec Loc Sh sh_eq_dec u l js x) as [Hs | _].
    - rewrite (sweep_stable l js x Hs), IH. apply kleene_stable. exact Hs.
    - apply IH.
  Qed.

  Lemma Forall_app' : forall (A : Type) (P : A -> Prop) a b, Forall P a -> Forall P b -> Forall P (a ++ b).
  Proof.
    intros A P a. induction a as [| x a IH]; intros b Ha Hb; [exact Hb |].
    inversion Ha as [| ? ? Hx Ha']; subst. simpl. constructor; [exact Hx | apply IH; assumption].
  Qed.

  Lemma rounds_in : forall n, Forall (fun j => In j js) (concat (repeat js n)).
  Proof.
    induction n as [| n IH]; [constructor |].
    change (concat (repeat js (S n))) with (js ++ concat (repeat js n)).
    apply Forall_app'; [apply Forall_forall; auto | exact IH].
  Qed.

  Section Dist.
  Variable E : Type.
  Variable ev : E -> Loc * Sh -> Loc * Sh.   (* a local event on one node (Apply, then the
                                              component normalizer); may read and write shared
                                              values *)
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.

  (* The actions of the distributed model: a local event; a propagation step of target j (its
     shared part := the current image of its sources' current, possibly stale, states); and a
     reset of every shared value to bottom (a barrier: the first half of a reset epoch). *)
  Inductive cact : Type := AEv : E -> cact | AProp : nat -> cact | AReset : cact.

  Definition cstep (a : cact) (t : Loc * Sh) : Loc * Sh :=
    match a with
    | AEv e => ev e t
    | AProp j => (fst t, u (fst t) j (snd t))
    | AReset => (fst t, bot)
    end.

  Fixpoint crun (w : list cact) (t : Loc * Sh) : Loc * Sh :=
    match w with [] => t | a :: w' => crun w' (cstep a t) end.

  Fixpoint cevs (w : list cact) : list E :=
    match w with
    | [] => []
    | AEv e :: w' => e :: cevs w'
    | _ :: w' => cevs w'
    end.

  (* r = false: gsm's distributed model (events and propagation only). r = true: resets
     allowed too. *)
  Definition okc (r : bool) (a : cact) : Prop :=
    match a with AEv _ => True | AProp j => In j js | AReset => r = true end.

  Definition OK (r : bool) (w : list cact) : Prop := Forall (okc r) w.

  (* The FedMachine: gstep e = Nc o ev e (FederationEventsCycles.v). *)
  Definition FM (es : list E) (s : Loc * Sh) : Loc * Sh := grun (Loc * Sh) E Nc ev es s.
  Definition FMConv (s : Loc * Sh) : Prop := Converges (Loc * Sh) E Nc ev reg I s.

  Definition Quiet (t : Loc * Sh) : Prop := QStable (fst t) (snd t).

  (* XU on a cycle, at one state: the local outcome of the event does not depend on whether the
     node's shared part is stale (t) or at the least fixed point (Nc t). Nc depends only on
     locals, so this is exactly Nc (ev e t) = Nc (ev e (Nc t)). *)
  Definition XUc (t : Loc * Sh) (e : E) : Prop := fst (ev e t) = fst (ev e (Nc t)).
  Definition XUcR (r : bool) (s0 : Loc * Sh) : Prop := forall p e, OK r p -> XUc (crun p s0) e.

  (* Comparison after a final reset epoch (Nc), and comparison at quiescence. *)
  Definition DistAgreeE (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK r w -> Nc (crun w s0) = FM (cevs w) (Nc s0).
  Definition DistConvE (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w1 w2, OK r w1 -> OK r w2 -> tequiv (Ifd E reg I) (cevs w1) (cevs w2) ->
      Nc (crun w1 s0) = Nc (crun w2 s0).
  Definition DAgreeQ (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK r w -> Quiet (crun w s0) -> crun w s0 = FM (cevs w) (Nc s0).
  Definition DConvQ (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w1 w2, OK r w1 -> OK r w2 -> tequiv (Ifd E reg I) (cevs w1) (cevs w2) ->
      Quiet (crun w1 s0) -> Quiet (crun w2 s0) -> crun w1 s0 = crun w2 s0.
  (* No reachable ghost: every reachable quiescent state holds the least fixed point. *)
  Definition NoGhostR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK r w -> Quiet (crun w s0) -> snd (crun w s0) = Lfp (fst (crun w s0)).
  (* Every reachable state can be flushed to quiescence by propagation alone. *)
  Definition FlushR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK r w -> exists c, Forall (fun j => In j js) c /\ Quiet (crun (w ++ map AProp c) s0).
  (* Every reachable state is below the least fixed point of its locals. *)
  Definition LowR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK r w -> le (snd (crun w s0)) (Lfp (fst (crun w s0))).
  (* Events keep a state below the least fixed point of its locals. *)
  Definition EvLow : Prop :=
    forall e t, le (snd t) (Lfp (fst t)) -> le (snd (ev e t)) (Lfp (fst (ev e t))).

  Lemma crun_app : forall p q t, crun (p ++ q) t = crun q (crun p t).
  Proof. induction p as [| a p IH]; intros q t; [reflexivity | simpl; apply IH]. Qed.

  Lemma cevs_app : forall p q, cevs (p ++ q) = cevs p ++ cevs q.
  Proof.
    induction p as [| a p IH]; intros q; [reflexivity |]. destruct a; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma cevs_props : forall c, cevs (map AProp c) = [].
  Proof. induction c as [| j c IH]; [reflexivity | exact IH]. Qed.

  Lemma cevs_evs : forall es, cevs (map AEv es) = es.
  Proof. induction es as [| e es IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

  Lemma ok_app : forall r p q, OK r p -> OK r q -> OK r (p ++ q).
  Proof. intros r p q. apply Forall_app'. Qed.

  Lemma ok_evs : forall r es, OK r (map AEv es).
  Proof. intros r es. induction es as [| e es IH]; [constructor | simpl; constructor; [exact Logic.I | exact IH]]. Qed.

  Lemma ok_props : forall r c, Forall (fun j => In j js) c -> OK r (map AProp c).
  Proof.
    intros r c H. induction H as [| j c Hj _ IH]; [constructor | simpl; constructor; [exact Hj | exact IH]].
  Qed.

  Lemma ok_ev1 : forall r e, OK r [AEv e].
  Proof. intros. constructor; [exact Logic.I | constructor]. Qed.

  Lemma crun_props : forall c t, crun (map AProp c) t = (fst t, sweep Loc Sh u (fst t) c (snd t)).
  Proof. induction c as [| j c IH]; intros [l h]; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

  Lemma fst_props : forall c t, fst (crun (map AProp c) t) = fst t.
  Proof. intros c t. rewrite crun_props. reflexivity. Qed.

  Lemma Nc_fst : forall t t', fst t = fst t' -> Nc t = Nc t'.
  Proof. intros [l h] [l' h'] E'. simpl in E'. subst. reflexivity. Qed.

  Lemma Nc_idem : forall t, Nc (Nc t) = Nc t.
  Proof. reflexivity. Qed.

  Lemma fst_Nc : forall t, fst (Nc t) = fst t.
  Proof. reflexivity. Qed.

  Lemma FM_cons : forall e es s, FM (e :: es) s = FM es (Nc (ev e s)).
  Proof. intros. unfold FM, grun. rewrite runT_cons. reflexivity. Qed.

  Lemma FM_normal : forall es s, s = Nc s -> FM es s = Nc (FM es s).
  Proof.
    induction es as [| e es IH]; intros s Hs; [exact Hs |].
    rewrite FM_cons. apply IH. symmetry. apply Nc_idem.
  Qed.

  Lemma quiet_normal : forall t, snd t = Lfp (fst t) -> t = Nc t.
  Proof. intros [l h] H. simpl in H. subst h. reflexivity. Qed.

  (* Tracking: under reachable XU, the reset-and-recompute image of every reachable distributed
     state is the FedMachine state for the same events. *)
  Theorem track : forall r s0, XUcR r s0 -> forall w, OK r w -> Nc (crun w s0) = FM (cevs w) (Nc s0).
  Proof.
    intros r s0 Hx.
    assert (G : forall w p, OK r p -> OK r w ->
                  Nc (crun w (crun p s0)) = FM (cevs w) (Nc (crun p s0))).
    { induction w as [| a w IH]; intros p Hp Hw; [reflexivity |].
      inversion Hw as [| ? ? Ha Hw']; subst.
      assert (Ep : cstep a (crun p s0) = crun (p ++ [a]) s0) by (rewrite crun_app; reflexivity).
      assert (Hpa : OK r (p ++ [a])) by (apply ok_app; [exact Hp | constructor; [exact Ha | constructor]]).
      cbn [crun]. rewrite Ep, (IH (p ++ [a]) Hpa Hw'). rewrite <- Ep.
      destruct a as [e | j |]; cbn [cstep cevs].
      - rewrite FM_cons. f_equal. apply Nc_fst. apply Hx. exact Hp.
      - reflexivity.
      - reflexivity. }
    intros w Hw. exact (G w [] ltac:(constructor) Hw).
  Qed.

  (* ----- Q3: reset epochs ----- *)

  (* A reset epoch: reset every shared value, then K sweeps of every target. *)
  Definition EP : list cact := AReset :: map AProp (concat (repeat js K)).

  Lemma EP_run : forall t, crun EP t = Nc t.
  Proof.
    intros [l h]. unfold EP. cbn [crun cstep fst]. rewrite crun_props. cbn [fst snd].
    rewrite iter_kleene. reflexivity.
  Qed.

  Lemma EP_ok : OK true EP.
  Proof. constructor; [reflexivity | apply ok_props; apply rounds_in]. Qed.

  Lemma EP_evs : cevs EP = [].
  Proof. exact (cevs_props _). Qed.

  (* Any reset followed by propagation that reaches quiescence ends at the FedMachine normal form
     (and by q1_from_bot, every fair propagation schedule after the reset reaches it). *)
  Theorem epoch_flush : forall t c,
    Quiet (crun (AReset :: map AProp c) t) -> crun (AReset :: map AProp c) t = Nc t.
  Proof.
    intros [l h] c Hq. cbn [crun cstep fst] in *. rewrite crun_props in *. cbn [fst snd] in *.
    rewrite Nc_eq. cbn [fst]. f_equal. apply le_antisym.
    - assert (B : forall c x, le x (Lfp l) -> le (sweep Loc Sh u l c x) (Lfp l)).
      { induction c0 as [| j c0 IH]; intros x Hx; [exact Hx | simpl; apply IH; apply below_u; exact Hx]. }
      apply B. apply bot_least.
    - apply Lfp_least. apply qstable_iff. exact Hq.
  Qed.

  (* The two runs whose comparison IS XUc t e: "event at t" and "epoch, then event". *)
  Lemma xu_runs : forall s0 p e,
    crun (p ++ [AEv e]) s0 = ev e (crun p s0) /\
    crun (p ++ EP ++ [AEv e]) s0 = ev e (Nc (crun p s0)) /\
    cevs (p ++ [AEv e]) = cevs (p ++ EP ++ [AEv e]).
  Proof.
    intros s0 p e. split; [rewrite crun_app; reflexivity |].
    split; [rewrite !crun_app, EP_run; reflexivity |].
    rewrite !cevs_app, EP_evs. reflexivity.
  Qed.

  Theorem agree_suff : forall r s0, XUcR r s0 -> DistAgreeE r s0.
  Proof. intros r s0 Hx w Hw. exact (track r s0 Hx w Hw). Qed.

  Theorem conv_suff : forall r s0, XUcR r s0 -> FMConv (Nc s0) -> DistConvE r s0.
  Proof.
    intros r s0 Hx Hc w1 w2 H1 H2 Ht. rewrite (track r s0 Hx w1 H1), (track r s0 Hx w2 H2).
    apply Hc. exact Ht.
  Qed.

  (* Q3 headline (exact): with reset epochs available, every run agrees with the FedMachine once
     a final epoch completes, exactly when reachable XU holds. *)
  Theorem epoch_agree_iff : forall s0, DistAgreeE true s0 <-> XUcR true s0.
  Proof.
    intros s0. split; [| apply agree_suff].
    intros Ha p e Hp. unfold XUc. destruct (xu_runs s0 p e) as [A [B C]].
    assert (O1 : OK true (p ++ [AEv e])) by (apply ok_app; [exact Hp | apply ok_ev1]).
    assert (O2 : OK true (p ++ EP ++ [AEv e]))
      by (apply ok_app; [exact Hp | apply ok_app; [exact EP_ok | apply ok_ev1]]).
    pose proof (Ha _ O1) as H1. pose proof (Ha _ O2) as H2. rewrite A in H1. rewrite B in H2.
    rewrite <- C in H2. rewrite <- H2 in H1. rewrite <- (fst_Nc (ev e (crun p s0))), H1. reflexivity.
  Qed.

  (* Q3 headline (exact): all interleavings agree after a final epoch exactly when reachable XU
     holds and the FedMachine converges from the normalized start. *)
  Theorem epoch_conv_iff : forall s0, DistConvE true s0 <-> XUcR true s0 /\ FMConv (Nc s0).
  Proof.
    intros s0. split.
    - intros Hc.
      assert (Hx : XUcR true s0).
      { intros p e Hp. unfold XUc. destruct (xu_runs s0 p e) as [A [B C]].
        assert (O1 : OK true (p ++ [AEv e])) by (apply ok_app; [exact Hp | apply ok_ev1]).
        assert (O2 : OK true (p ++ EP ++ [AEv e]))
          by (apply ok_app; [exact Hp | apply ok_app; [exact EP_ok | apply ok_ev1]]).
        pose proof (Hc _ _ O1 O2 ltac:(rewrite C; apply teq_refl)) as H. rewrite A, B in H.
        rewrite <- (fst_Nc (ev e (crun p s0))), H. reflexivity. }
      split; [exact Hx |].
      intros es1 es2 Ht.
      pose proof (track true s0 Hx (map AEv es1) (ok_evs true es1)) as T1.
      pose proof (track true s0 Hx (map AEv es2) (ok_evs true es2)) as T2.
      rewrite cevs_evs in T1, T2. unfold FM in T1, T2. rewrite <- T1, <- T2.
      apply Hc; [apply ok_evs | apply ok_evs | rewrite !cevs_evs; exact Ht].
    - intros [Hx Hm]. apply conv_suff; assumption.
  Qed.

  (* ----- Q2: no reset; flush = propagation to quiescence ----- *)

  Theorem quiet_agree_suff : forall r s0, XUcR r s0 -> NoGhostR r s0 -> DAgreeQ r s0.
  Proof.
    intros r s0 Hx Hg w Hw Hq. rewrite (quiet_normal _ (Hg w Hw Hq)) at 1. exact (track r s0 Hx w Hw).
  Qed.

  (* Under reachable XU the only way a quiescent distributed state can differ from the
     FedMachine is a ghost: same locals, shared part at a fixed point at or above the least one. *)
  Theorem quiet_ghost_only : forall r s0, XUcR r s0 -> forall w, OK r w -> Quiet (crun w s0) ->
    fst (crun w s0) = fst (FM (cevs w) (Nc s0)) /\
    snd (FM (cevs w) (Nc s0)) = Lfp (fst (crun w s0)) /\
    F (fst (crun w s0)) (snd (crun w s0)) = snd (crun w s0) /\
    le (snd (FM (cevs w) (Nc s0))) (snd (crun w s0)).
  Proof.
    intros r s0 Hx w Hw Hq. rewrite <- (track r s0 Hx w Hw).
    assert (Fx : F (fst (crun w s0)) (snd (crun w s0)) = snd (crun w s0)) by (apply qstable_iff; exact Hq).
    split; [reflexivity |]. split; [reflexivity |]. split; [exact Fx |].
    apply Lfp_least. exact Fx.
  Qed.

  Lemma flushed_normal : forall r s0 p c, OK r p -> Forall (fun j => In j js) c ->
    NoGhostR r s0 -> Quiet (crun (p ++ map AProp c) s0) ->
    crun (p ++ map AProp c) s0 = Nc (crun p s0).
  Proof.
    intros r s0 p c Hp Hc Hg Hq.
    assert (O : OK r (p ++ map AProp c)) by (apply ok_app; [exact Hp | apply ok_props; exact Hc]).
    rewrite (quiet_normal _ (Hg _ O Hq)). apply Nc_fst. rewrite crun_app. apply fst_props.
  Qed.

  (* The two flushed runs whose comparison IS XUc t e, when every reachable state can be
     flushed and no reachable quiescent state is a ghost. *)
  Lemma xu_quiet_runs : forall r s0 p e, OK r p -> FlushR r s0 -> NoGhostR r s0 ->
    exists w1 w2, OK r w1 /\ OK r w2 /\ cevs w1 = cevs w2 /\
      Quiet (crun w1 s0) /\ Quiet (crun w2 s0) /\
      fst (crun w1 s0) = fst (ev e (crun p s0)) /\ fst (crun w2 s0) = fst (ev e (Nc (crun p s0))).
  Proof.
    intros r s0 p e Hp Hf Hg.
    destruct (Hf p Hp) as [c [Hc Hq]].
    assert (Op : OK r (p ++ map AProp c)) by (apply ok_app; [exact Hp | apply ok_props; exact Hc]).
    assert (O1 : OK r (p ++ [AEv e])) by (apply ok_app; [exact Hp | apply ok_ev1]).
    assert (O2 : OK r ((p ++ map AProp c) ++ [AEv e])) by (apply ok_app; [exact Op | apply ok_ev1]).
    destruct (Hf _ O1) as [c1 [Hc1 Hq1]]. destruct (Hf _ O2) as [c2 [Hc2 Hq2]].
    exists ((p ++ [AEv e]) ++ map AProp c1), (((p ++ map AProp c) ++ [AEv e]) ++ map AProp c2).
    split; [apply ok_app; [exact O1 | apply ok_props; exact Hc1] |].
    split; [apply ok_app; [exact O2 | apply ok_props; exact Hc2] |].
    split; [rewrite !cevs_app, !cevs_props, !app_nil_r; reflexivity |].
    split; [exact Hq1 |]. split; [exact Hq2 |].
    rewrite !(crun_app _ (map AProp _)), !fst_props, !crun_app. split; [reflexivity |].
    pose proof (flushed_normal r s0 p c Hp Hc Hg Hq) as FN. rewrite crun_app in FN.
    rewrite FN. reflexivity.
  Qed.

  (* Q2 headline (exact, given flushability): every reachable quiescent state is the FedMachine
     state for the same events iff reachable XU holds and no reachable quiescent state is a
     ghost (a fixed point above the least one). *)
  Theorem quiet_agree_iff : forall r s0, FlushR r s0 ->
    (DAgreeQ r s0 <-> XUcR r s0 /\ NoGhostR r s0).
  Proof.
    intros r s0 Hf. split.
    - intros Ha.
      assert (Hg : NoGhostR r s0).
      { intros w Hw Hq. rewrite (Ha w Hw Hq). rewrite FM_normal; [reflexivity | symmetry; apply Nc_idem]. }
      split; [| exact Hg].
      intros p e Hp. unfold XUc.
      destruct (xu_quiet_runs r s0 p e Hp Hf Hg) as [w1 [w2 [O1 [O2 [C [Q1 [Q2 [F1 F2]]]]]]]].
      rewrite <- F1, <- F2, (Ha w1 O1 Q1), (Ha w2 O2 Q2), C. reflexivity.
    - intros [Hx Hg]. apply quiet_agree_suff; assumption.
  Qed.

  Theorem quiet_conv_suff : forall r s0, XUcR r s0 -> NoGhostR r s0 -> FMConv (Nc s0) -> DConvQ r s0.
  Proof.
    intros r s0 Hx Hg Hc w1 w2 O1 O2 Ht Q1 Q2.
    rewrite (quiet_agree_suff r s0 Hx Hg w1 O1 Q1), (quiet_agree_suff r s0 Hx Hg w2 O2 Q2).
    apply Hc. exact Ht.
  Qed.

  (* Q2 headline (exact, given flushability and no reachable ghost): all quiescent interleavings
     agree iff reachable XU holds and the FedMachine converges. *)
  Theorem quiet_conv_iff : forall r s0, FlushR r s0 -> NoGhostR r s0 ->
    (DConvQ r s0 <-> XUcR r s0 /\ FMConv (Nc s0)).
  Proof.
    intros r s0 Hf Hg. split.
    - intros Hc.
      assert (Hx : XUcR r s0).
      { intros p e Hp. unfold XUc.
        destruct (xu_quiet_runs r s0 p e Hp Hf Hg) as [w1 [w2 [O1 [O2 [C [Q1 [Q2 [F1 F2]]]]]]]].
        rewrite <- F1, <- F2, (Hc w1 w2 O1 O2 ltac:(rewrite C; apply teq_refl) Q1 Q2). reflexivity. }
      split; [exact Hx |].
      intros es1 es2 Ht.
      destruct (Hf (map AEv es1) (ok_evs r es1)) as [c1 [Hc1 Q1]].
      destruct (Hf (map AEv es2) (ok_evs r es2)) as [c2 [Hc2 Q2]].
      assert (O1 : OK r (map AEv es1 ++ map AProp c1)) by (apply ok_app; [apply ok_evs | apply ok_props; exact Hc1]).
      assert (O2 : OK r (map AEv es2 ++ map AProp c2)) by (apply ok_app; [apply ok_evs | apply ok_props; exact Hc2]).
      pose proof (quiet_agree_suff r s0 Hx Hg _ O1 Q1) as A1.
      pose proof (quiet_agree_suff r s0 Hx Hg _ O2 Q2) as A2.
      rewrite cevs_app, cevs_props, cevs_evs, app_nil_r in A1, A2.
      unfold FM in A1, A2. rewrite <- A1, <- A2.
      apply Hc; [exact O1 | exact O2 | rewrite !cevs_app, !cevs_props, !cevs_evs, !app_nil_r; exact Ht
                 | exact Q1 | exact Q2].
    - intros [Hx Hm]. apply quiet_conv_suff; assumption.
  Qed.

  (* The no-ghost invariant: below the least fixed point at every reachable state. *)
  Lemma low_noghost : forall r s0, LowR r s0 -> NoGhostR r s0.
  Proof.
    intros r s0 Hl w Hw Hq. apply le_antisym; [exact (Hl w Hw) |].
    apply Lfp_least. apply qstable_iff. exact Hq.
  Qed.

  Lemma low_flush : forall r s0, LowR r s0 -> FlushR r s0.
  Proof.
    intros r s0 Hl w Hw. exists (concat (repeat js K)). split; [apply rounds_in |].
    unfold Quiet. rewrite crun_app, crun_props. cbn [fst snd].
    set (t := crun w s0). set (c := concat (repeat js K)).
    assert (E' : sweep Loc Sh u (fst t) c (snd t) = Lfp (fst t)).
    { apply le_antisym.
      - rewrite <- (sweep_stable (fst t) c (Lfp (fst t)) (fun j _ => u_fixed _ j _ (Lfp_fixed _))).
        apply sweep_mono. exact (Hl w Hw).
      - unfold Lfp. rewrite <- iter_kleene. apply sweep_mono. apply bot_least. }
    rewrite E'. apply Lfp_stable.
  Qed.

  (* Q2 corollaries under the no-ghost invariant (exact). *)
  Theorem low_agree_iff : forall r s0, LowR r s0 -> (DAgreeQ r s0 <-> XUcR r s0).
  Proof.
    intros r s0 Hl. rewrite (quiet_agree_iff r s0 (low_flush r s0 Hl)).
    split; [intros [H _]; exact H | intros H; split; [exact H | apply low_noghost; exact Hl]].
  Qed.

  Theorem low_conv_iff : forall r s0, LowR r s0 -> (DConvQ r s0 <-> XUcR r s0 /\ FMConv (Nc s0)).
  Proof. intros r s0 Hl. apply quiet_conv_iff; [apply low_flush | apply low_noghost]; exact Hl. Qed.

  (* No ghost can exist when the repair has a unique fixed point for every locals assignment
     (the every-start case of Q1, q1_unique_iff). *)
  Lemma uniq_noghost : forall r s0, (forall l p, F l p = p -> p = Lfp l) -> NoGhostR r s0.
  Proof. intros r s0 Hu w _ Hq. apply Hu. apply qstable_iff. exact Hq. Qed.

  Theorem uniq_agree : forall r s0, (forall l p, F l p = p -> p = Lfp l) ->
    XUcR r s0 -> DAgreeQ r s0 /\ (FMConv (Nc s0) -> DConvQ r s0).
  Proof.
    intros r s0 Hu Hx. pose proof (uniq_noghost r s0 Hu) as Hg.
    split; [apply quiet_agree_suff; assumption | intro Hm; apply quiet_conv_suff; assumption].
  Qed.

  (* A per-event sufficient condition for the invariant. *)
  Theorem evlow_lowr : forall r s0, EvLow -> le (snd s0) (Lfp (fst s0)) -> LowR r s0.
  Proof.
    intros r s0 He H0 w Hw. revert s0 H0. induction Hw as [| a w Ha _ IH]; intros s0 H0; [exact H0 |].
    cbn [crun]. apply IH. destruct a as [e | j |]; cbn [cstep fst snd].
    - apply He. exact H0.
    - apply below_u. exact H0.
    - apply bot_least.
  Qed.

  (* Inflationary events satisfy it: an event that only raises locals (in an order the repair
     is monotone in) and does not raise shared values. *)
  Section Infl.
    Variable lle : Loc -> Loc -> Prop.
    Hypothesis u_mono_l : forall l l' j h, lle l l' -> le (u l j h) (u l' j h).

    Lemma kleene_below : forall l q, (forall j, In j js -> le (u l j q) q) ->
      forall n x, le x q -> le (kleene Loc Sh sh_eq_dec u l js n x) q.
    Proof.
      intros l q Hq.
      assert (Sw : forall c x, (forall j, In j c -> In j js) -> le x q -> le (sweep Loc Sh u l c x) q).
      { induction c as [| j c IH]; intros x Hc Hx; [exact Hx |]. simpl. apply IH.
        - intros k Hk. apply Hc. right. exact Hk.
        - eapply le_trans; [apply u_mono; exact Hx | apply Hq; apply Hc; left; reflexivity]. }
      induction n as [| n IH]; intros x Hx; [exact Hx |]. rewrite kleene_S.
      destruct (stable_dec Loc Sh sh_eq_dec u l js x); [exact Hx |].
      apply IH. apply Sw; [auto | exact Hx].
    Qed.

    Lemma Lfp_mono : forall l l', lle l l' -> le (Lfp l) (Lfp l').
    Proof.
      intros l l' H. apply kleene_below; [| apply bot_least].
      intros j _. rewrite <- (u_fixed l' j (Lfp l') (Lfp_fixed l')) at 2. apply u_mono_l. exact H.
    Qed.

    Theorem infl_evlow : (forall e t, lle (fst t) (fst (ev e t)) /\ le (snd (ev e t)) (snd t)) -> EvLow.
    Proof.
      intros H e t Ht. destruct (H e t) as [Hl Hs].
      eapply le_trans; [exact Hs |]. eapply le_trans; [exact Ht | apply Lfp_mono; exact Hl].
    Qed.
  End Infl.
  End Dist.

  (* ===================================================================================== *)
  (* Part 4. gsm's per-target checks (C1cyc, C2cyc) in the distributed model.             *)
  (* ===================================================================================== *)

  Section Lens.
  Variables Lc Hc Rg : Type.
  Variable rg_eq_dec : forall a b : Rg, {a = b} + {a <> b}.
  Variable enc : Rg -> nat.
  Variable lget : Rg -> Loc -> Lc.
  Variable lset : Rg -> Lc -> Loc -> Loc.
  Hypothesis lget_lset_eq : forall j x l, lget j (lset j x l) = x.
  Hypothesis lget_lset_neq : forall j k x l, k <> j -> lget k (lset j x l) = lget k l.
  Hypothesis l_ext : forall l l', (forall k, lget k l = lget k l') -> l = l'.
  Variable sget : Rg -> Sh -> Hc.
  Variable sset : Rg -> Hc -> Sh -> Sh.
  Hypothesis sget_sset_eq : forall j x h, sget j (sset j x h) = x.
  Hypothesis sget_sset_neq : forall j k x h, k <> j -> sget k (sset j x h) = sget k h.
  Variable cvalid : Rg -> Lc * Hc -> Prop.
  Variable E : Type.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.
  Variable I : E -> E -> Prop.
  Hypothesis sig_valid : forall e x, cvalid (reg e) x -> cvalid (reg e) (sig e x).

  (* The least fixed point is valid (gsm checks this at Build and panics otherwise). *)
  Hypothesis lfp_valid : forall l, FValid Loc Sh Lc Hc Rg lget sget cvalid (l, Lfp l).

  (* Hs k: a set of shared values of registry k containing the least-fixed-point values. *)
  Variable Hs : Rg -> Hc -> Prop.
  Hypothesis Hs_lfp : forall l k, Hs k (sget k (Lfp l)).

  Local Notation evL := (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig).
  Local Notation nrL := (nreg Rg enc E reg).

  Definition HsAll (t : Loc * Sh) : Prop := forall k, Hs k (sget k (snd t)).

  (* Hs covers every shared value a node can hold in the distributed model. *)
  Definition HsReachR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OK E r w -> HsAll (crun E evL w s0).

  (* gsm's C1 read on a cycle, over a set covering the reachable values, gives reachable XU. *)
  Theorem lens_xucr : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    forall r s0, HsReachR r s0 -> XUcR E evL r s0.
  Proof.
    intros H1 r s0 Hr p e Hp. unfold XUc. rewrite Nc_eq. unfold cev, comp. cbn [fst snd].
    f_equal. apply H1; [apply (lfp_valid (fst (crun E evL p s0))) | apply Hs_lfp | apply (Hr p Hp)].
  Qed.

  (* C1cyc + C2cyc give FedMachine convergence from every normal form (cyc_check_converges). *)
  Theorem lens_fmconv : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs -> forall s0, FMConv E evL nrL I (Nc s0).
  Proof.
    intros H1 H2 s0.
    exact (cyc_check_converges Loc Sh Lc Hc Rg rg_eq_dec enc lget lset lget_lset_eq lget_lset_neq
             l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg sig I sig_valid (fun s => s) Lfp
             (fun s _ => eq_refl) (fun t => lfp_valid (fst t)) Hs (fun t k => Hs_lfp (fst t) k)
             H1 H2 s0).
  Qed.

  (* Q3 with gsm's checks: reset epochs restore agreement with the FedMachine. *)
  Theorem lens_epoch : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs -> forall r s0, HsReachR r s0 ->
    DistConvE E evL nrL I r s0 /\ DistAgreeE E evL r s0.
  Proof.
    intros H1 H2 r s0 Hr. pose proof (lens_xucr H1 r s0 Hr) as Hx.
    split; [apply conv_suff; [exact Hx | apply lens_fmconv; assumption] | apply agree_suff; exact Hx].
  Qed.

  (* Q2 with gsm's checks: without resets, the no-ghost invariant is what is missing. *)
  Theorem lens_quiet : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs -> forall r s0, HsReachR r s0 -> LowR E evL r s0 ->
    DConvQ E evL nrL I r s0 /\ DAgreeQ E evL r s0.
  Proof.
    intros H1 H2 r s0 Hr Hl. pose proof (lens_xucr H1 r s0 Hr) as Hx.
    pose proof (low_noghost E evL r s0 Hl) as Hg.
    split; [apply quiet_conv_suff; [exact Hx | exact Hg | apply lens_fmconv; assumption]
           | apply quiet_agree_suff; assumption].
  Qed.

  (* What Hs must contain: the start's values, bottom (if resets are used), what propagation
     writes (the morphism images), and what events write. *)
  Theorem hs_reach : forall r s0, HsAll s0 ->
    (r = true -> forall k, Hs k (sget k bot)) ->
    (forall l h j, HsAll (l, h) -> HsAll (l, u l j h)) ->
    (forall e x h, Hs (reg e) h -> Hs (reg e) (snd (sig e (x, h)))) ->
    HsReachR r s0.
  Proof.
    intros r s0 H0 Hb Hp He w Hw. revert s0 H0. induction Hw as [| a w Ha _ IH]; intros s0 H0; [exact H0 |].
    cbn [crun]. apply IH. destruct a as [e | j |]; cbn [cstep].
    - intro k. unfold cev, comp. cbn [snd].
      destruct (rg_eq_dec k (reg e)) as [-> | Ne].
      + rewrite sget_sset_eq. apply He. apply H0.
      + rewrite (sget_sset_neq _ _ _ _ Ne). apply H0.
    - destruct s0 as [l h]. apply Hp. exact H0.
    - intro k. apply Hb. exact Ha.
  Qed.
  End Lens.
End DistCyc.

(* ======================================================================================= *)
(* Part 5. Instances on the two-registry flag cycle of FederationEventsCycles.v.            *)
(* Locals (la, lb); shared (sa, sb): sa := lb || sb (A's flag, fed by B); sb := la || sa.   *)
(* ======================================================================================= *)

Definition dLfp : B2 -> B2 := Lfp B2 B2 cbot ceq_dec cu 3 cts.
Definition dNc : B2 * B2 -> B2 * B2 := Nc B2 B2 cbot ceq_dec cu 3 cts.
Definition irun : list (cact iev) -> B2 * B2 -> B2 * B2 := crun B2 B2 cbot cu iev icev.

Definition gs0 : B2 * B2 := ((false, false), (false, false)).

(* Raise A's alarm, propagate around the cycle (B then A), clear the alarm. *)
Definition w_ghost : list (cact iev) :=
  [AEv iev RaiseA'; AProp iev 1; AProp iev 0; AEv iev ClearA'].
(* The same events with no propagation in between, then a flush. *)
Definition w_clean : list (cact iev) :=
  [AEv iev RaiseA'; AEv iev ClearA'; AProp iev 0; AProp iev 1].

Lemma cv1_lfp : forall l, FValid B2 B2 bool bool bool rget rget cv1 (l, dLfp l).
Proof. intros l k. exact I. Qed.

Lemma i_xucr : forall r s0, XUcR B2 B2 cbot ceq_dec cu 3 cts iev icev r s0.
Proof.
  intros r s0.
  exact (lens_xucr B2 B2 cbot ceq_dec cu 3 cts bool bool bool rget rset rget rset cv1 iev ireg isig
           cv1_lfp Hall (fun _ _ => I) (proj1 cyc_check_instance) r s0 (fun _ _ _ => I)).
Qed.

Lemma i_fmconv : forall s0, FMConv B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI (dNc s0).
Proof.
  intros s0.
  exact (lens_fmconv B2 B2 cbot ceq_dec cu 3 cts bool bool bool bool_dec renc rget rset
           (rget_rset_eq bool) (rget_rset_neq bool) (r_ext bool) rget rset (rget_rset_eq bool)
           (rget_rset_neq bool) cv1 iev ireg isig iI (fun _ _ _ => I) cv1_lfp Hall (fun _ _ => I)
           (proj1 cyc_check_instance) (proj1 (proj2 cyc_check_instance)) s0).
Qed.

(* Q1 + Q2 counterexample. gsm's per-target checks hold (C1cyc, C2cyc), reachable XU holds from
   every start (the events' local outcomes ignore shared values: the acyclic exact condition's
   XU part), and the FedMachine converges from every normal form. Yet in the distributed model a
   raised-then-cleared alarm leaves a GHOST: the two shared flags keep each other set. The run
   w_ghost is quiescent at ((false, false), (true, true)), a non-least fixed point, while the
   FedMachine (and w_clean, with the same events) gives ((false, false), (false, false)); no
   propagation schedule ever leaves the ghost. *)
Theorem dist_cyc_ghost :
  C1cyc bool bool bool cv1 iev ireg isig Hall /\
  C2cyc bool bool bool cv1 iev ireg isig iI Hall /\
  (forall r s0, XUcR B2 B2 cbot ceq_dec cu 3 cts iev icev r s0) /\
  (forall s0, FMConv B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI (dNc s0)) /\
  gs0 = dNc gs0 /\
  OK cts iev false w_ghost /\ OK cts iev false w_clean /\
  cevs iev w_ghost = cevs iev w_clean /\
  irun w_ghost gs0 = ((false, false), (true, true)) /\
  irun w_clean gs0 = ((false, false), (false, false)) /\
  Quiet B2 B2 cu cts (irun w_ghost gs0) /\ Quiet B2 B2 cu cts (irun w_clean gs0) /\
  FM B2 B2 cbot ceq_dec cu 3 cts iev icev (cevs iev w_ghost) (dNc gs0) = ((false, false), (false, false)) /\
  (forall sg n, prs B2 (cu (false, false)) sg n (true, true) <> dLfp (false, false)) /\
  ~ DConvQ B2 B2 cbot cu cts iev icev inreg iI false gs0 /\
  ~ DAgreeQ B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  ~ NoGhostR B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  ~ LowR B2 B2 cle cbot ceq_dec cu 3 cts iev icev false gs0.
Proof.
  assert (Og : OK cts iev false w_ghost) by (repeat constructor; simpl; tauto).
  assert (Oc : OK cts iev false w_clean) by (repeat constructor; simpl; tauto).
  assert (Qg : Quiet B2 B2 cu cts (irun w_ghost gs0)) by (intros j [<- | [<- | []]]; reflexivity).
  assert (Qc : Quiet B2 B2 cu cts (irun w_clean gs0)) by (intros j [<- | [<- | []]]; reflexivity).
  split; [exact (proj1 cyc_check_instance) |].
  split; [exact (proj1 (proj2 cyc_check_instance)) |].
  split; [exact i_xucr |]. split; [exact i_fmconv |].
  split; [reflexivity |]. split; [exact Og |]. split; [exact Oc |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Qg |]. split; [exact Qc |]. split; [vm_compute; reflexivity |].
  split.
  { intros sg n.
    exact (q1_stuck B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank crank_strict 2
             crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 ltac:(lia) cts cts_cover
             (false, false) (true, true) (true, true) eq_refl ltac:(vm_compute; discriminate)
             (cle_refl _) sg n). }
  split; [intro H; pose proof (H _ _ Og Oc (teq_refl _ _) Qg Qc) as E; discriminate E |].
  split; [intro H; pose proof (H _ Og Qg) as E; vm_compute in E; discriminate E |].
  split; [intro H; pose proof (H _ Og Qg) as E; vm_compute in E; discriminate E |].
  intro H. pose proof (H _ Og) as E. vm_compute in E. destruct E as [E _]. discriminate E.
Qed.

(* Q3 on the same cycle: with reset epochs, every run agrees with the FedMachine after a final
   epoch, from EVERY start; the ghost run followed by an epoch is cleared. A staggered reset is
   not enough: if A resets its flag while B still holds the ghost, one propagation step of A
   restores it (the reset must be a barrier). *)
Theorem dist_cyc_epoch_fix :
  (forall r s0, DistConvE B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI r s0 /\
                DistAgreeE B2 B2 cbot ceq_dec cu 3 cts iev icev r s0) /\
  (forall s0, DistConvE B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI true s0 <->
              XUcR B2 B2 cbot ceq_dec cu 3 cts iev icev true s0 /\
              FMConv B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI (dNc s0)) /\
  irun (w_ghost ++ EP 3 cts iev) gs0 = ((false, false), (false, false)) /\
  irun [AProp iev 0] ((false, false), (false, true)) = ((false, false), (true, true)).
Proof.
  split.
  { intros r s0.
    exact (lens_epoch B2 B2 cbot ceq_dec cu 3 cts bool bool bool bool_dec renc rget rset
             (rget_rset_eq bool) (rget_rset_neq bool) (r_ext bool) rget rset (rget_rset_eq bool)
             (rget_rset_neq bool) cv1 iev ireg isig iI (fun _ _ _ => I) cv1_lfp Hall (fun _ _ => I)
             (proj1 cyc_check_instance) (proj1 (proj2 cyc_check_instance)) r s0 (fun _ _ _ => I)). }
  split; [intro s0; apply epoch_conv_iff |].
  split; vm_compute; reflexivity.
Qed.

(* Q2 positive instance (no resets): raise-only events on the same cycle. They only raise locals
   and never write shared values, so the no-ghost invariant holds from every start below the
   least fixed point, and every quiescent interleaving agrees with the FedMachine. *)
Inductive rev : Type := RaiseAr | RaiseBr.
Definition rregr (e : rev) : bool := match e with RaiseAr => true | RaiseBr => false end.
Definition rsigr (_ : rev) (x : bool * bool) : bool * bool := (true, snd x).
Definition rI (_ _ : rev) : Prop := False.
Definition rcev : rev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset rev rregr rsigr.
Definition rnreg : rev -> nat := nreg bool renc rev rregr.

Lemma cu_mono_l : forall l l' j h, cle l l' -> cle (cu l j h) (cu l' j h).
Proof. intros l l' [| [| j]] h; bf; unfold cle, cu, cF; simpl; intuition. Qed.

Theorem dist_cyc_raise_only : forall r s0, cle (snd s0) (dLfp (fst s0)) ->
  LowR B2 B2 cle cbot ceq_dec cu 3 cts rev rcev r s0 /\
  DConvQ B2 B2 cbot cu cts rev rcev rnreg rI r s0 /\
  DAgreeQ B2 B2 cbot ceq_dec cu 3 cts rev rcev r s0.
Proof.
  intros r s0 H0.
  assert (Hl : LowR B2 B2 cle cbot ceq_dec cu 3 cts rev rcev r s0).
  { apply (evlow_lowr B2 B2 cle cle_refl cle_trans cbot cbot_least crank crank_strict 2 crank_bound
             ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 ltac:(lia) cts cts_cover rev rcev r s0);
      [| exact H0].
    apply (infl_evlow B2 B2 cle cle_refl cle_trans cbot cbot_least crank crank_strict 2 crank_bound
             ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 ltac:(lia) cts cts_cover rev rcev cle
             cu_mono_l).
    intros [] t; bf; split; unfold cle; simpl; auto. }
  split; [exact Hl |].
  assert (H1 : C1cyc bool bool bool cv1 rev rregr rsigr Hall) by (intros e x h h' _ _ _; reflexivity).
  assert (H2 : C2cyc bool bool bool cv1 rev rregr rsigr rI Hall) by (intros a b x h _ [] _ _).
  pose proof (lens_xucr B2 B2 cbot ceq_dec cu 3 cts bool bool bool rget rset rget rset cv1 rev rregr
                rsigr cv1_lfp Hall (fun _ _ => I) H1 r s0 (fun _ _ _ => I)) as Hx.
  pose proof (lens_fmconv B2 B2 cbot ceq_dec cu 3 cts bool bool bool bool_dec renc rget rset
                (rget_rset_eq bool) (rget_rset_neq bool) (r_ext bool) rget rset (rget_rset_eq bool)
                (rget_rset_neq bool) cv1 rev rregr rsigr rI (fun _ _ _ => I) cv1_lfp Hall
                (fun _ _ => I) H1 H2 s0) as Hm.
  split.
  - apply (low_conv_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank crank_strict 2
             crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 ltac:(lia) cts cts_cover
             rev rcev rnreg rI r s0 Hl). split; assumption.
  - apply (low_agree_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank crank_strict 2
             crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 ltac:(lia) cts cts_cover
             rev rcev r s0 Hl). exact Hx.
Qed.

(* ----- Q1 on the cycle: schedule dependence from an unsound start, and the unique case ----- *)

Fixpoint par (n : nat) : bool := match n with 0 => true | S m => negb (par m) end.

(* Two alternating (hence fair) schedules: target A first, or target B first. *)
Definition sgA (n : nat) : nat := if par n then 0 else 1.
Definition sgB (n : nat) : nat := if par n then 1 else 0.

Lemma alt_fair : forall a b, (a = 0 /\ b = 1) \/ (a = 1 /\ b = 0) ->
  Fair cts (fun n => if par n then a else b).
Proof.
  intros a b Hab. split.
  - intro n. destruct (par n); destruct Hab as [[-> ->] | [-> ->]]; simpl; tauto.
  - intros j n Hj.
    assert (Hj' : j = a \/ j = b) by (destruct Hj as [<- | [<- | []]]; destruct Hab as [[-> ->] | [-> ->]]; auto).
    destruct Hj' as [-> | ->]; destruct (par n) eqn:P.
    + exists n. rewrite P. split; [lia | reflexivity].
    + exists (S n). simpl. rewrite P. split; [lia | reflexivity].
    + exists (S n). simpl. rewrite P. split; [lia | reflexivity].
    + exists n. rewrite P. split; [lia | reflexivity].
Qed.

(* With both alarms clear, the unsound stale start (sa, sb) = (true, false) settles at the least
   fixed point under one fair schedule and at the ghost under another: from a start that is
   neither below the least fixed point nor above another fixed point, the outcome depends on the
   schedule. *)
Theorem dist_schedule_dependence :
  Fair cts sgA /\ Fair cts sgB /\
  ~ cle (true, false) (dLfp (false, false)) /\
  ~ cle (true, true) (true, false) /\
  Settles B2 (cu (false, false)) sgA (true, false) (dLfp (false, false)) /\
  Settles B2 (cu (false, false)) sgB (true, false) (true, true) /\
  cF (false, false) (true, true) = (true, true) /\ dLfp (false, false) = (false, false).
Proof.
  assert (Fx : forall j x, cF (false, false) x = x -> cu (false, false) j x = x) by (intros; apply cu_fixed; assumption).
  split; [apply alt_fair; left; split; reflexivity |].
  split; [apply alt_fair; right; split; reflexivity |].
  split; [vm_compute; intros [H _]; discriminate H |].
  split; [unfold cle; simpl; intros [_ H]; discriminate H |].
  split.
  { exists 1. intros n Hn. destruct n as [| n]; [lia |]. change (dLfp (false, false)) with (false, false).
    induction n as [| n IH]; [reflexivity |].
    rewrite prs_S, IH by lia. apply Fx. reflexivity. }
  split.
  { exists 1. intros n Hn. destruct n as [| n]; [lia |].
    induction n as [| n IH]; [reflexivity |].
    rewrite prs_S, IH by lia. apply Fx. reflexivity. }
  split; reflexivity.
Qed.

(* The every-start case: when the repair has a unique fixed point (alarm A raised), every fair
   schedule from EVERY start settles at the least fixed point; with both alarms clear (two fixed
   points), for every fair schedule some start does not. *)
Definition ctop : B2 := (true, true).

Lemma ctop_greatest : forall x, cle x ctop.
Proof. intros; bf; split; reflexivity. Qed.
Lemma cu_decr : forall l j x, cle (cF l x) x -> cle (cu l j x) x.
Proof. intros l [| [| j]] x; bf; unfold cle, cu, cF; simpl; intuition. Qed.
Lemma cu_cosound : forall l j x, cle (cF l x) x -> cle (cF l (cu l j x)) (cu l j x).
Proof. intros l [| [| j]] x; bf; unfold cle, cu, cF; simpl; intuition. Qed.

Theorem dist_unique_fixed_point :
  (forall sg, Fair cts sg -> forall h0, Settles B2 (cu (true, false)) sg h0 (true, true)) /\
  (forall sg, Fair cts sg -> ~ forall h0, Settles B2 (cu (false, false)) sg h0 (dLfp (false, false))).
Proof.
  split.
  - intros sg Hf h0.
    pose proof (proj2 (q1_unique_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
                  crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3
                  ltac:(lia) cts cts_cover ctop ctop_greatest cu_decr cu_cosound (true, false) sg Hf))
      as H.
    apply H. intros p Hp. bf; vm_compute in Hp |- *; congruence.
  - intros sg Hf Hall'.
    pose proof (proj1 (q1_unique_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
                  crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3
                  ltac:(lia) cts cts_cover ctop ctop_greatest cu_decr cu_cosound (false, false) sg Hf)
                  Hall' (true, true) eq_refl) as E.
    vm_compute in E. discriminate E.
Qed.

(* ======================================================================================= *)
(* Part 6. Livelock: a monotone 3-cycle on which a fair schedule never reaches quiescence.  *)
(* Shared (a, b, c), no locals; a := b, b := c, c := a (each registry copies the next).     *)
(* ======================================================================================= *)

Definition R3 : Type := (bool * bool * bool)%type.
Definition r3le (x y : R3) : Prop :=
  match x, y with (a, b, c), (a', b', c') =>
    implb a a' = true /\ implb b b' = true /\ implb c c' = true end.
Definition r3bot : R3 := (false, false, false).
Definition b2n' (b : bool) : nat := if b then 1 else 0.
Definition r3rank (x : R3) : nat := match x with (a, b, c) => b2n' a + b2n' b + b2n' c end.
Definition r3_eq_dec : forall x y : R3, {x = y} + {x <> y}.
Proof. decide equality; [apply bool_dec | decide equality; apply bool_dec]. Defined.
Definition r3F (_ : unit) (x : R3) : R3 := match x with (a, b, c) => (b, c, a) end.
Definition r3u (_ : unit) (j : nat) (x : R3) : R3 :=
  match x with (a, b, c) =>
    match j with 0 => (b, b, c) | 1 => (a, c, c) | 2 => (a, b, a) | _ => (a, b, c) end end.
Definition r3js : list nat := [0; 1; 2].

Ltac bf3 := repeat match goal with
  | x : R3 |- _ => destruct x
  | x : _ * _ |- _ => destruct x
  | b : bool |- _ => destruct b
  | u : unit |- _ => destruct u
  end.

Lemma r3le_refl : forall x, r3le x x. Proof. intros; bf3; unfold r3le; auto. Qed.
Lemma r3le_trans : forall x y z, r3le x y -> r3le y z -> r3le x z.
Proof. intros x y z; bf3; unfold r3le; simpl; intuition congruence. Qed.
Lemma r3le_antisym : forall x y, r3le x y -> r3le y x -> x = y.
Proof. intros x y; bf3; unfold r3le; simpl; intuition congruence. Qed.
Lemma r3bot_least : forall x, r3le r3bot x. Proof. intros; bf3; unfold r3le; simpl; auto. Qed.
Lemma r3rank_strict : forall x y, r3le x y -> x <> y -> r3rank x < r3rank y.
Proof. intros x y; bf3; unfold r3le, r3rank, b2n'; simpl; intuition (try congruence; try lia). Qed.
Lemma r3rank_bound : forall x, r3rank x <= 3. Proof. intros; bf3; unfold r3rank, b2n'; simpl; lia. Qed.
Lemma r3u_incr : forall l j x, sound unit R3 r3le r3F l x -> r3le x (r3u l j x).
Proof. intros l [| [| [| j]]] x; bf3; unfold sound, r3le, r3u, r3F; simpl; intuition. Qed.
Lemma r3u_sound : forall l j x, sound unit R3 r3le r3F l x -> sound unit R3 r3le r3F l (r3u l j x).
Proof. intros l [| [| [| j]]] x; bf3; unfold sound, r3le, r3u, r3F; simpl; intuition. Qed.
Lemma r3u_mono : forall l j x y, r3le x y -> r3le (r3u l j x) (r3u l j y).
Proof. intros l [| [| [| j]]] x y; bf3; unfold r3le, r3u; simpl; intuition. Qed.
Lemma r3u_fixed : forall l j x, r3F l x = x -> r3u l j x = x.
Proof. intros l [| [| [| j]]] x; bf3; unfold r3u, r3F; simpl; intro H; congruence. Qed.
Lemma r3_cover : Cover unit R3 r3F r3u r3js.
Proof.
  intros l x H. pose proof (H 0 (or_introl eq_refl)) as H0.
  pose proof (H 1 (or_intror (or_introl eq_refl))) as H1.
  pose proof (H 2 (or_intror (or_intror (or_introl eq_refl)))) as H2.
  revert H0 H1 H2. bf3; unfold r3u, r3F; simpl; intros; congruence.
Qed.

Definition nxt (k : nat) : nat := match k with 5 => 0 | _ => S k end.
Fixpoint pos (n : nat) : nat := match n with 0 => 0 | S m => nxt (pos m) end.
Definition r3sched : list nat := [2; 0; 1; 2; 0; 1].
Definition r3sg (n : nat) : nat := nth (pos n) r3sched 0.
Definition r3h0 : R3 := (true, false, false).
Definition r3cs : list R3 :=
  [(true, false, false); (true, false, true); (false, false, true);
   (false, true, true); (false, true, false); (true, true, false)].

Lemma pos_lt : forall n, pos n < 6.
Proof.
  induction n as [| n IH]; [simpl; lia |]. simpl.
  destruct (pos n) as [| [| [| [| [| [| k]]]]]]; simpl; lia.
Qed.

Lemma r3_state : forall n, prs R3 (r3u tt) r3sg n r3h0 = nth (pos n) r3cs r3h0.
Proof.
  induction n as [| n IH]; [reflexivity |].
  rewrite prs_S, IH. unfold r3sg. cbn [pos]. generalize (pos_lt n).
  destruct (pos n) as [| [| [| [| [| [| k]]]]]]; intro H; try reflexivity; lia.
Qed.

Lemma r3_fair : Fair r3js r3sg.
Proof.
  split.
  - intro n. unfold r3sg. generalize (pos_lt n).
    destruct (pos n) as [| [| [| [| [| [| k]]]]]]; intro H; simpl; try tauto; lia.
  - intros j n Hj. generalize (pos_lt n). remember (pos n) as p eqn:Hp.
    destruct Hj as [<- | [<- | [<- | []]]];
    destruct p as [| [| [| [| [| [| k]]]]]]; intro H; try lia;
    first [ exists n; split; [lia | unfold r3sg; rewrite <- Hp; reflexivity]
          | exists (S n); split; [lia | unfold r3sg; cbn [pos]; rewrite <- Hp; reflexivity]
          | exists (S (S n)); split; [lia | unfold r3sg; cbn [pos]; rewrite <- Hp; reflexivity] ].
Qed.

(* Q1, arbitrary starts: fair asynchronous propagation need not reach ANY fixed point. On a
   monotone 3-cycle (every hypothesis of the cyclic development discharged), from the stale start
   (true, false, false) the fair periodic schedule c, a, b, c, a, b, ... moves the single set flag
   around the ring forever: no state along the run is quiescent, and the least fixed point
   (false, false, false) is never reached. *)
Theorem dist_ring_livelock :
  Cover unit R3 r3F r3u r3js /\
  (forall l j x, sound unit R3 r3le r3F l x -> r3le x (r3u l j x)) /\
  (forall l j x, sound unit R3 r3le r3F l x -> sound unit R3 r3le r3F l (r3u l j x)) /\
  (forall l j x y, r3le x y -> r3le (r3u l j x) (r3u l j y)) /\
  (forall l j x, r3F l x = x -> r3u l j x = x) /\
  Lfp unit R3 r3bot r3_eq_dec r3u 4 r3js tt = (false, false, false) /\
  r3F tt (true, true, true) = (true, true, true) /\
  Fair r3js r3sg /\
  (forall n, ~ Stable R3 (r3u tt) r3js (prs R3 (r3u tt) r3sg n r3h0)) /\
  (forall n, prs R3 (r3u tt) r3sg n r3h0 <> Lfp unit R3 r3bot r3_eq_dec r3u 4 r3js tt).
Proof.
  split; [exact r3_cover |]. split; [exact r3u_incr |]. split; [exact r3u_sound |].
  split; [exact r3u_mono |]. split; [exact r3u_fixed |].
  split; [vm_compute; reflexivity |]. split; [reflexivity |].
  split; [exact r3_fair |].
  split.
  - intros n Hs. rewrite r3_state in Hs. generalize (pos_lt n).
    pose proof (Hs 0 (or_introl eq_refl)) as S0.
    pose proof (Hs 1 (or_intror (or_introl eq_refl))) as S1.
    pose proof (Hs 2 (or_intror (or_intror (or_introl eq_refl)))) as S2.
    revert S0 S1 S2.
    destruct (pos n) as [| [| [| [| [| [| k]]]]]]; vm_compute; intros; try discriminate; lia.
  - intros n. rewrite r3_state. generalize (pos_lt n).
    destruct (pos n) as [| [| [| [| [| [| k]]]]]]; vm_compute; intros; try discriminate; lia.
Qed.

(* ======================================================================================= *)
(* Part 7. A registry cycle without shared-value feedback needs no reset.                   *)
(* A's flag is fed by B's alarm only (sa := lb); B's flag by A (sb := la || sa). The        *)
(* registries form a cycle A -> B -> A, but the repair has one fixed point for every locals *)
(* assignment, so every quiescent interleaving agrees with the FedMachine from every start, *)
(* clear events included (uniq_agree).                                                      *)
(* ======================================================================================= *)

Definition uF (l : B2) (x : B2) : B2 := (snd l, fst l || fst x).
Definition uu (l : B2) (j : nat) (x : B2) : B2 :=
  match j with
  | 0 => (fst (uF l x), snd x)
  | 1 => (fst x, snd (uF l x))
  | _ => x
  end.

Lemma uu_fixed : forall l j x, uF l x = x -> uu l j x = x.
Proof. intros l [| [| j]] x; bf; unfold uu, uF; simpl; intro H; congruence. Qed.
Lemma u_cover : Cover B2 B2 uF uu cts.
Proof.
  intros l x H. pose proof (H 0 (or_introl eq_refl)) as H0.
  pose proof (H 1 (or_intror (or_introl eq_refl))) as H1.
  revert H0 H1. bf; unfold uu, uF; simpl; intros H0 H1; congruence.
Qed.
Lemma uu_incr : forall l j x, sound B2 B2 cle uF l x -> cle x (uu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, uu, uF; simpl; intuition. Qed.
Lemma uu_sound : forall l j x, sound B2 B2 cle uF l x -> sound B2 B2 cle uF l (uu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, uu, uF; simpl; intuition. Qed.
Lemma uu_mono : forall l j x y, cle x y -> cle (uu l j x) (uu l j y).
Proof. intros l [| [| j]] x y; bf; unfold cle, uu, uF; simpl; intuition. Qed.

Definition uLfp : B2 -> B2 := Lfp B2 B2 cbot ceq_dec uu 3 cts.

Theorem dist_cyc_unique_no_reset :
  (forall l, is_lfp cle (uF l) (uLfp l)) /\
  (forall l p, uF l p = p -> p = uLfp l) /\
  (forall r s0, DAgreeQ B2 B2 cbot ceq_dec uu 3 cts iev icev r s0 /\
                DConvQ B2 B2 cbot uu cts iev icev inreg iI r s0).
Proof.
  assert (Hu : forall l p, uF l p = p -> p = uLfp l) by (intros l p; bf; vm_compute; congruence).
  split.
  { intro l. exact (Lfp_is_lfp B2 B2 cle cle_refl cle_trans cbot cbot_least crank crank_strict 2
                      crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 ltac:(lia) cts
                      u_cover l). }
  split; [exact Hu |].
  intros r s0.
  pose proof (lens_xucr B2 B2 cbot ceq_dec uu 3 cts bool bool bool rget rset rget rset cv1 iev ireg
                isig (fun _ _ => I) Hall (fun _ _ => I) (proj1 cyc_check_instance) r s0
                (fun _ _ _ => I)) as Hx.
  pose proof (lens_fmconv B2 B2 cbot ceq_dec uu 3 cts bool bool bool bool_dec renc rget rset
                (rget_rset_eq bool) (rget_rset_neq bool) (r_ext bool) rget rset (rget_rset_eq bool)
                (rget_rset_neq bool) cv1 iev ireg isig iI (fun _ _ _ => I) (fun _ _ => I) Hall
                (fun _ _ => I) (proj1 cyc_check_instance) (proj1 (proj2 cyc_check_instance)) s0) as Hm.
  destruct (uniq_agree B2 B2 cbot ceq_dec uF uu uu_fixed 3 cts u_cover iev icev inreg iI r s0 Hu Hx)
    as [A C].
  split; [exact A | exact (C Hm)].
Qed.
