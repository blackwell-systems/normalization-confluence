(* DistributedCyclesExact.v: the distributed propagation model on MONOTONE CYCLIC federations
   WITHOUT resets, exactly (REGIME-AUDIT.md section 8, the residual of gap 1). Axiom-free.

   The residual. DistributedCycles.v proves the no-reset model exact only relative to reachable
   hypotheses: quiet_agree_iff and quiet_conv_iff assume FlushR (every reachable state flushes to
   quiescence) and, for convergence, NoGhostR (no reachable quiescent ghost); low_agree_iff and
   low_conv_iff assume LowR. This file moves those hypotheses to the right-hand side, proves each
   conjunct necessary, and characterizes FlushR and NoGhostR.

   Notation (as in DistributedCycles.v): a state is (l, h); F l the synchronous repair, u l j the
   repair of target j; Lfp l the least fixed point; Nc (l, h) = (l, Lfp l) the FedMachine normal
   form; Fair sg: every target named infinitely often; Quiet t: no propagation step changes t.
   New here:
     FlushAt t      : some propagation word from t reaches a quiescent state.
     FairFlushAt t  : EVERY fair schedule from t reaches a quiescent state.
     FairFlushR     : FairFlushAt at every reachable state (the operational flush: nodes
                      propagate asynchronously and fairly).
     SoundR         : every reachable state is sound (h <= F l h).
     Sand l h       : h is sandwiched: s <= h <= every fixed point above s, for a sound s.
     GhostFree t    : every quiescent state reachable from t by propagation alone holds Lfp.
     UniqueFP l     : F l has one fixed point.

   1. Unconditional iffs (no reachable hypothesis on the left).
     flush_agree_iff : FlushR /\ DAgreeQ <-> XUcR /\ FlushR /\ NoGhostR.
     fair_agree_iff  : FairFlushR /\ DAgreeQ <-> XUcR /\ FairFlushR /\ NoGhostR.
     flush_fed_iff   : FlushR /\ DAgreeQ /\ DConvQ <-> XUcR /\ FMConv (Nc s0) /\ FlushR /\ NoGhostR.
     fair_fed_iff    : the same with FairFlushR.
     Each conjunct is necessary (an instance where it alone fails):
       XUcR       : copy_xu_fails (an event reads a stale shared value; unique fixed points).
       FMConv     : fm_conv_fails (two declared-independent events that do not commute).
       FlushR     : flip_noflush (no propagation word ever reaches quiescence, although the
                    repair has one fixed point and no ghost exists).
       FairFlushR : flip2_fair_livelock (a word reaches quiescence, but a fair schedule never
                    does; one fixed point, no ghost). ring_exact: the 3-ring of
                    dist_ring_livelock also has FlushR without FairFlushR (with a ghost).
       NoGhostR   : ghost_exact (dist_cyc_ghost: everything else holds, including FairFlushR).
     conv_ghost_normal: NoGhostR is NOT necessary for DConvQ alone: from a FedMachine normal start
       every quiescent interleaving agrees, yet each lands on a ghost. Agreement with the
       FedMachine is what NoGhostR adds.

   2. FlushR exactly.
     fair_flush_sound_iff : under a fair schedule, the run reaches quiescence iff it reaches a
                            sound state (soundness is the whole basin).
     flushat_sound_iff    : some word reaches quiescence iff some word reaches a sound state.
     fairflushR_sound_iff, flushR_sound_iff : the reachable forms.
     sand_settles         : from s <= h <= (least fixed point above s), s sound, every fair
                            schedule settles at the least fixed point above s. Recovers q1_below
                            (s = bot, sand_recovers) and q1_sound_settles (h = s).
     sandr_fairflush, soundr_fairflush, lowr_fairflush : sandwiched / sound / low reachable states
                            give FairFlushR (hence FlushR: fairflushR_flushR).
     evsand_sandr, evsound_soundr : per-event checks (events keep states sandwiched / sound).
     infl_evsound         : inflationary events that do not write shared values keep soundness;
     evlow_fairflush      : EvLow events (DistributedCycles.infl_evlow) keep LowR, so FairFlushR;
     nc_sound_low         : gsm starts (Nc t) are sound and low.
     step_sound_fairflush : a per-network check: if every single propagation step yields a sound
                            state, every fair schedule from every state settles (the 2-flag cycle;
                            not the 3-ring).
     Necessity status: none of SoundR, LowR, SandR is necessary: ghost_exact has a reachable
     state that is neither sound nor sandwiched, yet FairFlushR holds.

   3. NoGhostR exactly.
     noghost_event_iff : NoGhostR <-> the start and every post-event state (an event applied at a
                         reachable state) are GhostFree: each ghost is made by one event followed by
                         propagation. ghost_witness: every reachable ghost is reached by
                         propagation from the start or from a last event's output that is NOT below
                         the least fixed point of its locals.
     ghostfree_low, ghostfree_sound_iff : a low state is ghost-free; a SOUND state is ghost-free iff
                         it is low (q1_sound_iff for every propagation word).
     noghost_soundr_iff : SoundR -> (NoGhostR <-> LowR).  lowr_post_iff : LowR <-> the start and
                         every post-event state are low. So under SoundR, no ghost exactly when
                         every event, applied at a reachable state, leaves the shared values below
                         the least fixed point of the new locals.
     soundr_agree_iff, soundr_fed_iff : SoundR -> (DAgreeQ <-> XUcR /\ LowR) and
                         (DAgreeQ /\ DConvQ <-> XUcR /\ LowR /\ FMConv).
     noghost_inv_iff   : NoGhostR <-> some invariant (closed under events and propagation, holding
                         at the start) contains no ghost (the certificate form).
     unique_or_low_noghost : an invariant on which every state has UniqueFP locals or is low gives
                         NoGhostR; recovers uniq_noghost and evlow (unique_or_low_recovers).
     latched_exact     : non-vacuity beyond EvLow and global uniqueness: on the flag cycle with B's
                         alarm latched, clearing A's alarm is safe (the remaining locals pin the
                         fixed point); EvLow and global UniqueFP both fail.
     local_reset_ghost : a clear that also resets its OWN shared slot to bottom still leaves a ghost:
                         on a cycle the reset has to cover the cycle (a barrier, lens_epoch).
     ghostfree_unsound : an unsound state that is not low can be ghost-free (unique fixed point),
                         so LowR is not necessary without SoundR.

   4. gsm. lens_noreset_iff, lens_noreset_fair_iff: with gsm's per-target C1cyc and C2cyc over a
     set covering the reachable shared values, a cyclic projection deployment without resets is
     certified (FlushR /\ DAgreeQ /\ DConvQ) exactly when FlushR and NoGhostR hold.

   Non-vacuity: raise_only_exact (raise-only events: SoundR, LowR, FairFlushR, agreement and
   convergence), ghost_exact, ring_exact, flip_noflush, flip2_fair_livelock, latched_exact. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.Federation NC.FederationEventsCycles NC.FederationEventsCyclesCheck
  NC.DistributedCycles.
Import ListNotations.

(* ======================================================================================= *)
(* Part 0. Schedules: round robin, shifts, finite prefixes.                                 *)
(* ======================================================================================= *)

Section RoundRobin.
  Variable js : list nat.

  Fixpoint rrp (n : nat) : nat :=
    match n with
    | 0 => 0
    | S m => if Nat.ltb (S (rrp m)) (length js) then S (rrp m) else 0
    end.

  (* The round-robin schedule over js. *)
  Definition rrs (n : nat) : nat := nth (rrp n) js 0.

  Lemma rrp_S : forall n, rrp (S n) = if Nat.ltb (S (rrp n)) (length js) then S (rrp n) else 0.
  Proof. reflexivity. Qed.

  Lemma len_pos : js <> [] -> 0 < length js.
  Proof.
    intros Hne. destruct (length js) eqn:L; [| lia].
    apply length_zero_iff_nil in L. contradiction.
  Qed.

  Lemma rrp_lt : js <> [] -> forall n, rrp n < length js.
  Proof.
    intros Hne n. pose proof (len_pos Hne) as L.
    induction n as [| n IH]; [exact L |]. rewrite rrp_S.
    destruct (Nat.ltb_spec (S (rrp n)) (length js)); [assumption | exact L].
  Qed.

  Lemma rrp_adv : forall d n, rrp n + d < length js -> rrp (d + n) = rrp n + d.
  Proof.
    induction d as [| d IH]; intros n H; [simpl; lia |].
    change (S d + n) with (S (d + n)). rewrite rrp_S, IH by lia.
    destruct (Nat.ltb_spec (S (rrp n + d)) (length js)); lia.
  Qed.

  Lemma rrp_wrap : js <> [] -> forall n, exists m, n < m /\ rrp m = 0.
  Proof.
    intros Hne n. pose proof (rrp_lt Hne n) as Hl.
    set (d := length js - 1 - rrp n).
    assert (A : rrp (d + n) = length js - 1) by (rewrite rrp_adv; unfold d; lia).
    exists (S (d + n)). split; [lia |]. rewrite rrp_S, A.
    destruct (Nat.ltb_spec (S (length js - 1)) (length js)); [lia | reflexivity].
  Qed.

  Lemma rrp_hits : js <> [] -> forall n k, k < length js -> exists m, n <= m /\ rrp m = k.
  Proof.
    intros Hne n k Hk.
    destruct (Nat.le_gt_cases (rrp n) k) as [Le | Gt].
    - exists ((k - rrp n) + n). split; [lia |]. rewrite rrp_adv; lia.
    - destruct (rrp_wrap Hne n) as [m0 [Hm0 Z]].
      exists (k + m0). split; [lia |]. rewrite rrp_adv; rewrite Z; lia.
  Qed.

  Theorem rrs_fair : js <> [] -> Fair js rrs.
  Proof.
    intros Hne. split.
    - intro n. unfold rrs. apply nth_In. apply rrp_lt. exact Hne.
    - intros j n Hj. destruct (In_nth js j 0 Hj) as [k [Hk Ek]].
      destruct (rrp_hits Hne n k Hk) as [m [Hm Em]].
      exists m. split; [exact Hm |]. unfold rrs. rewrite Em. exact Ek.
  Qed.

  Lemma fair_shift : forall sg n, Fair js sg -> Fair js (fun i => sg (n + i)).
  Proof.
    intros sg n [H1 H2]. split; [intro i; apply H1 |].
    intros j m Hj. destruct (H2 j (n + m) Hj) as [k [Hk Ek]].
    exists (k - n). split; [lia |]. cbv beta. replace (n + (k - n)) with k by lia. exact Ek.
  Qed.

  Lemma fair_same : forall js' sg, Fair js sg -> (forall j, In j js <-> In j js') -> Fair js' sg.
  Proof.
    intros js' sg [H1 H2] Hs. split; [intro n; apply Hs; apply H1 |].
    intros j n Hj. apply H2. apply Hs. exact Hj.
  Qed.
End RoundRobin.

(* The first n targets of a schedule, as a word. *)
Fixpoint pw (sg : nat -> nat) (n : nat) : list nat :=
  match n with 0 => [] | S m => pw sg m ++ [sg m] end.

Lemma fa_app : forall (A : Type) (P : A -> Prop) a b, Forall P a -> Forall P b -> Forall P (a ++ b).
Proof.
  intros A P a. induction a as [| x a IH]; intros b Ha Hb; [exact Hb |].
  inversion Ha as [| ? ? Hx Ha']; subst. simpl. constructor; [exact Hx | apply IH; assumption].
Qed.

Lemma pw_in : forall js sg n, Fair js sg -> Forall (fun j => In j js) (pw sg n).
Proof.
  intros js sg n Hf. induction n as [| n IH]; [constructor |]. simpl.
  apply fa_app; [exact IH | constructor; [apply (proj1 Hf) | constructor]].
Qed.

Section Shift.
  Variable Sh : Type.
  Variable up : nat -> Sh -> Sh.

  Lemma prs_shift : forall sg n k h,
    prs Sh up sg (k + n) h = prs Sh up (fun i => sg (n + i)) k (prs Sh up sg n h).
  Proof.
    intros sg n k h. induction k as [| k IH]; [reflexivity |].
    change (S k + n) with (S (k + n)). cbn [prs]. rewrite IH. rewrite (Nat.add_comm k n).
    reflexivity.
  Qed.
End Shift.

(* ======================================================================================= *)
(* Part 1. The generic development.                                                          *)
(* ======================================================================================= *)

Section Exact.
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

  Local Notation Sd := (sound Loc Sh le F).
  Local Notation LF := (Lfp Loc Sh bot sh_eq_dec u K js).
  Local Notation sw := (sweep Loc Sh u).
  Local Notation PR l := (prs Sh (u l)).
  Local Notation ST l := (Stable Sh (u l) js).
  Local Notation InJ := (fun j => In j js).

  Lemma lf_fixed : forall l, F l (LF l) = LF l.
  Proof.
    exact (Lfp_fixed Loc Sh le le_refl le_trans bot bot_least rank rank_strict height rank_bound
             sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov).
  Qed.

  Lemma lf_least : forall l p, F l p = p -> le (LF l) p.
  Proof.
    exact (Lfp_least Loc Sh le le_refl le_trans bot bot_least rank rank_strict height rank_bound
             sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov).
  Qed.

  Lemma stable_fixed : forall l h, ST l h -> F l h = h.
  Proof. intros l h H. apply Hcov. exact H. Qed.

  Lemma fixed_stable : forall l h, F l h = h -> ST l h.
  Proof. intros l h H j _. apply u_fixed. exact H. Qed.

  Lemma fixed_sound : forall l h, F l h = h -> Sd l h.
  Proof. intros l h H. unfold sound. rewrite H. apply le_refl. Qed.

  Lemma u_below : forall l j h, le h (LF l) -> le (u l j h) (LF l).
  Proof.
    intros l j h H. eapply le_trans; [apply u_mono; exact H |].
    rewrite (u_fixed l j _ (lf_fixed l)). apply le_refl.
  Qed.

  Lemma sw_app : forall l a b x, sw l (a ++ b) x = sw l b (sw l a x).
  Proof. intros l a. induction a as [| j a IH]; intros b x; [reflexivity | simpl; apply IH]. Qed.

  Lemma sw_below : forall l c h, le h (LF l) -> le (sw l c h) (LF l).
  Proof.
    intros l c. induction c as [| j c IH]; intros h H; [exact H |]. simpl. apply IH.
    apply u_below. exact H.
  Qed.

  Lemma sw_up : forall l c h, Sd l h -> Sd l (sw l c h) /\ le h (sw l c h).
  Proof.
    intros l c. induction c as [| j c IH]; intros h H; [split; [exact H | apply le_refl] |].
    simpl. destruct (IH (u l j h) (u_sound l j h H)) as [S1 S2]. split; [exact S1 |].
    eapply le_trans; [apply u_incr; exact H | exact S2].
  Qed.

  Lemma prs_sw : forall l sg n h, PR l sg n h = sw l (pw sg n) h.
  Proof.
    intros l sg n h. induction n as [| n IH]; [reflexivity |].
    cbn [prs pw]. rewrite sw_app, <- IH. reflexivity.
  Qed.

  (* Some propagation word reaches a quiescent state / every fair schedule does. *)
  Definition FlushAt (t : Loc * Sh) : Prop :=
    exists c, Forall InJ c /\ ST (fst t) (sw (fst t) c (snd t)).
  Definition FairFlushAt (t : Loc * Sh) : Prop :=
    forall sg, Fair js sg -> exists n, ST (fst t) (PR (fst t) sg n (snd t)).

  (* A fair run reaches a quiescent state iff it reaches a sound state: from a sound state every
     step is inflationary (fair_settles), and a quiescent state is a fixed point. *)
  Theorem fair_flush_sound_iff : forall l h sg, Fair js sg ->
    ((exists n, ST l (PR l sg n h)) <-> (exists n, Sd l (PR l sg n h))).
  Proof.
    intros l h sg Hf. split.
    - intros [n Hn]. exists n. apply fixed_sound. apply stable_fixed. exact Hn.
    - intros [n Hn].
      destruct (fair_settles Sh le le_refl le_trans rank rank_strict height rank_bound sh_eq_dec
                  (u l) js (Sd l) (u_sound l) (fun j x Hx => u_incr l j x Hx)
                  (fun i => sg (n + i)) (fair_shift js sg n Hf) (PR l sg n h) Hn)
        as [N [St _]].
      exists (N + n). rewrite prs_shift. exact St.
  Qed.

  (* Every fair schedule reaching quiescence gives a finite flushing word (round robin). *)
  Lemma fair_to_word : forall l h, (forall sg, Fair js sg -> exists n, ST l (PR l sg n h)) ->
    exists c, Forall InJ c /\ ST l (sw l c h).
  Proof.
    intros l h H.
    assert (D : js = [] \/ js <> []) by (case js; [left; reflexivity | intros; right; discriminate]).
    destruct D as [D | D].
    - exists []. split; [constructor |]. intros j Hj. rewrite D in Hj. destruct Hj.
    - destruct (H (rrs js) (rrs_fair js D)) as [n Hn]. exists (pw (rrs js) n).
      split; [apply pw_in; apply rrs_fair; exact D |]. rewrite <- prs_sw. exact Hn.
  Qed.

  Theorem fairflush_flushat : forall t, FairFlushAt t -> FlushAt t.
  Proof. intros t H. apply fair_to_word. exact H. Qed.

  Definition Sand (l : Loc) (h : Sh) : Prop :=
    exists s, Sd l s /\ le s h /\ (forall p, F l p = p -> le s p -> le h p).

  (* The sandwich: from s <= h <= (every fixed point above s), with s sound, every fair schedule
     settles at the least fixed point above s. q1_below is s = bot; q1_sound_settles is h = s. *)
  Theorem sand_settles : forall l s h sg, Sd l s -> le s h ->
    (forall p, F l p = p -> le s p -> le h p) -> Fair js sg ->
    exists q, (F l q = q /\ le s q /\ (forall p, F l p = p -> le s p -> le q p)) /\
              Settles Sh (u l) sg h q.
  Proof.
    intros l s h sg Hs Hsh Hh Hf.
    destruct (q1_sound_settles Loc Sh le le_refl le_trans rank rank_strict height rank_bound
                sh_eq_dec F u u_incr u_sound u_mono u_fixed js Hcov l s sg Hs Hf)
      as [q [[Fq [Hsq Hq]] [N HN]]].
    exists q. split; [split; [exact Fq | split; [exact Hsq | exact Hq]] |].
    exists N. intros n Hn. apply le_antisym.
    - rewrite <- (prs_fixed Sh (u l) sg q (fun j => u_fixed l j q Fq) n).
      apply (prs_mono Sh le (u l) (u_mono l)). apply Hh; assumption.
    - rewrite <- (HN n Hn). apply (prs_mono Sh le (u l) (u_mono l)). exact Hsh.
  Qed.

  Lemma sand_low : forall l h, le h (LF l) -> Sand l h.
  Proof.
    intros l h H. exists bot. split; [unfold sound; apply bot_least |].
    split; [apply bot_least |]. intros p Fp _. eapply le_trans; [exact H | apply lf_least; exact Fp].
  Qed.

  Lemma sand_sound : forall l h, Sd l h -> Sand l h.
  Proof.
    intros l h H. exists h. split; [exact H |]. split; [apply le_refl | intros p _ Hp; exact Hp].
  Qed.

  Lemma sand_u : forall l j h, Sand l h -> Sand l (u l j h).
  Proof.
    intros l j h [s [Hs [Hsh Hh]]]. exists (u l j s). split; [apply u_sound; exact Hs |].
    split; [apply u_mono; exact Hsh |].
    intros p Fp Hp. rewrite <- (u_fixed l j p Fp). apply u_mono. apply Hh; [exact Fp |].
    eapply le_trans; [apply u_incr; exact Hs | exact Hp].
  Qed.

  Lemma sand_fairflush : forall l h, Sand l h -> FairFlushAt (l, h).
  Proof.
    intros l h [s [Hs [Hsh Hh]]] sg Hf. cbn [fst snd].
    destruct (sand_settles l s h sg Hs Hsh Hh Hf) as [q [[Fq _] [N HN]]].
    exists N. rewrite (HN N (le_n N)). apply fixed_stable. exact Fq.
  Qed.

  (* q1_below recovered from the sandwich. *)
  Theorem sand_recovers : forall l h0 sg, le h0 (LF l) -> Fair js sg -> Settles Sh (u l) sg h0 (LF l).
  Proof.
    intros l h0 sg H Hf.
    destruct (sand_settles l bot h0 sg ltac:(unfold sound; apply bot_least) (bot_least h0)
                (fun p Fp _ => le_trans _ _ _ H (lf_least l p Fp)) Hf) as [q [[Fq [_ Hq]] Hs]].
    assert (E : q = LF l).
    { apply le_antisym; [apply Hq; [apply lf_fixed | apply bot_least] | apply lf_least; exact Fq]. }
    rewrite <- E. exact Hs.
  Qed.

  (* Exact per state: some word reaches quiescence iff some word reaches a sound state. *)
  Theorem flushat_sound_iff : forall t,
    FlushAt t <-> exists c, Forall InJ c /\ Sd (fst t) (sw (fst t) c (snd t)).
  Proof.
    intros [l h]. cbn [fst snd]. split.
    - intros [c [Hc St]]. exists c. split; [exact Hc |]. apply fixed_sound. apply stable_fixed. exact St.
    - intros [c [Hc Hs]].
      destruct (fair_to_word l (sw l c h) (sand_fairflush l _ (sand_sound l _ Hs))) as [c' [Hc' St]].
      exists (c ++ c'). split; [apply fa_app; assumption |]. rewrite sw_app. exact St.
  Qed.

  (* A per-network check: every single propagation step yields a sound state. Then every fair
     schedule from every state settles. *)
  Definition StepSound : Prop := forall l j h, In j js -> Sd l (u l j h).

  Theorem step_sound_fairflush : StepSound -> forall t, FairFlushAt t.
  Proof.
    intros Hs [l h] sg Hf. cbn [fst snd]. apply (fair_flush_sound_iff l h sg Hf).
    exists 1. cbn [prs]. apply Hs. apply (proj1 Hf).
  Qed.

  Definition UniqueFP (l : Loc) : Prop := forall p, F l p = p -> p = LF l.

  (* ===================================================================================== *)
  (* With events.                                                                           *)
  (* ===================================================================================== *)

  Section Ev.
  Variable E : Type.
  Variable ev : E -> Loc * Sh -> Loc * Sh.
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.

  Local Notation run := (crun Loc Sh bot u E ev).
  Local Notation OKw := (OK js E).
  Local Notation Qt := (Quiet Loc Sh u js).
  Local Notation PW c := (map (AProp E) c).
  Local Notation FlushR' := (FlushR Loc Sh bot u js E ev).
  Local Notation NoGhostR' := (NoGhostR Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation DAgreeQ' := (DAgreeQ Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation DConvQ' := (DConvQ Loc Sh bot u js E ev reg I).
  Local Notation XUcR' := (XUcR Loc Sh bot sh_eq_dec u K js E ev).
  Local Notation LowR' := (LowR Loc Sh le bot sh_eq_dec u K js E ev).
  Local Notation EvLow' := (EvLow Loc Sh le bot sh_eq_dec u K js E ev).
  Local Notation FMConv' := (FMConv Loc Sh bot sh_eq_dec u K js E ev reg I).
  Local Notation NC := (Nc Loc Sh bot sh_eq_dec u K js).

  Definition FairFlushR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OKw r w -> FairFlushAt (run w s0).
  Definition SoundR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OKw r w -> Sd (fst (run w s0)) (snd (run w s0)).
  Definition SandR (r : bool) (s0 : Loc * Sh) : Prop :=
    forall w, OKw r w -> Sand (fst (run w s0)) (snd (run w s0)).
  Definition GhostFree (t : Loc * Sh) : Prop :=
    forall c, Forall InJ c -> Qt (run (PW c) t) -> snd (run (PW c) t) = LF (fst t).
  Definition EvSound : Prop :=
    forall e t, Sd (fst t) (snd t) -> Sd (fst (ev e t)) (snd (ev e t)).
  Definition EvSand : Prop :=
    forall e t, Sand (fst t) (snd t) -> Sand (fst (ev e t)) (snd (ev e t)).

  Lemma run_props : forall c t, run (PW c) t = (fst t, sw (fst t) c (snd t)).
  Proof. exact (crun_props Loc Sh bot u E ev). Qed.

  Lemma quiet_props : forall c t, Qt (run (PW c) t) <-> ST (fst t) (sw (fst t) c (snd t)).
  Proof. intros c t. rewrite run_props. split; intro H; exact H. Qed.

  Lemma run_app : forall p q t, run (p ++ q) t = run q (run p t).
  Proof. exact (crun_app Loc Sh bot u E ev). Qed.

  Lemma fst_pw : forall c t, fst (run (PW c) t) = fst t.
  Proof. exact (fst_props Loc Sh bot u E ev). Qed.

  Lemma flushR_at : forall r s0, FlushR' r s0 <-> (forall w, OKw r w -> FlushAt (run w s0)).
  Proof.
    intros r s0. split.
    - intros H w Hw. destruct (H w Hw) as [c [Hc Hq]]. exists c. split; [exact Hc |].
      rewrite run_app in Hq. apply quiet_props. exact Hq.
    - intros H w Hw. destruct (H w Hw) as [c [Hc Hq]]. exists c. split; [exact Hc |].
      rewrite run_app. apply quiet_props. exact Hq.
  Qed.

  Theorem fairflushR_flushR : forall r s0, FairFlushR r s0 -> FlushR' r s0.
  Proof.
    intros r s0 H. apply flushR_at. intros w Hw. apply fairflush_flushat. apply H. exact Hw.
  Qed.

  (* ----- 1. The unconditional iffs ----- *)

  Theorem flush_agree_iff : forall r s0,
    (FlushR' r s0 /\ DAgreeQ' r s0) <-> (XUcR' r s0 /\ FlushR' r s0 /\ NoGhostR' r s0).
  Proof.
    intros r s0. split.
    - intros [Hf Ha].
      destruct (proj1 (quiet_agree_iff Loc Sh bot sh_eq_dec u K js E ev r s0 Hf) Ha) as [Hx Hg].
      tauto.
    - intros [Hx [Hf Hg]]. split; [exact Hf |].
      apply (quiet_agree_iff Loc Sh bot sh_eq_dec u K js E ev r s0 Hf). tauto.
  Qed.

  Theorem fair_agree_iff : forall r s0,
    (FairFlushR r s0 /\ DAgreeQ' r s0) <-> (XUcR' r s0 /\ FairFlushR r s0 /\ NoGhostR' r s0).
  Proof.
    intros r s0. split.
    - intros [Hf Ha].
      destruct (proj1 (flush_agree_iff r s0) (conj (fairflushR_flushR r s0 Hf) Ha)) as [Hx [_ Hg]].
      tauto.
    - intros [Hx [Hf Hg]]. split; [exact Hf |].
      apply (proj2 (flush_agree_iff r s0)). split; [exact Hx | split; [| exact Hg]].
      apply fairflushR_flushR. exact Hf.
  Qed.

  Theorem flush_fed_iff : forall r s0,
    (FlushR' r s0 /\ DAgreeQ' r s0 /\ DConvQ' r s0) <->
    (XUcR' r s0 /\ FMConv' (NC s0) /\ FlushR' r s0 /\ NoGhostR' r s0).
  Proof.
    intros r s0. split.
    - intros [Hf [Ha Hc]].
      destruct (proj1 (flush_agree_iff r s0) (conj Hf Ha)) as [Hx [_ Hg]].
      destruct (proj1 (quiet_conv_iff Loc Sh bot sh_eq_dec u K js E ev reg I r s0 Hf Hg) Hc)
        as [_ Hm].
      tauto.
    - intros [Hx [Hm [Hf Hg]]]. split; [exact Hf |]. split.
      + apply (quiet_agree_iff Loc Sh bot sh_eq_dec u K js E ev r s0 Hf). tauto.
      + apply (quiet_conv_iff Loc Sh bot sh_eq_dec u K js E ev reg I r s0 Hf Hg). tauto.
  Qed.

  Theorem fair_fed_iff : forall r s0,
    (FairFlushR r s0 /\ DAgreeQ' r s0 /\ DConvQ' r s0) <->
    (XUcR' r s0 /\ FMConv' (NC s0) /\ FairFlushR r s0 /\ NoGhostR' r s0).
  Proof.
    intros r s0. split.
    - intros [Hf [Ha Hc]].
      destruct (proj1 (flush_fed_iff r s0) (conj (fairflushR_flushR r s0 Hf) (conj Ha Hc)))
        as [Hx [Hm [_ Hg]]].
      tauto.
    - intros [Hx [Hm [Hf Hg]]]. split; [exact Hf |].
      apply (proj2 (flush_fed_iff r s0)). split; [exact Hx | split; [exact Hm | split; [| exact Hg]]].
      apply fairflushR_flushR. exact Hf.
  Qed.

  (* ----- 2. FlushR exactly ----- *)

  Theorem fairflushR_sound_iff : forall r s0, FairFlushR r s0 <->
    (forall w, OKw r w -> forall sg, Fair js sg ->
       exists n, Sd (fst (run w s0)) (PR (fst (run w s0)) sg n (snd (run w s0)))).
  Proof.
    intros r s0. split.
    - intros H w Hw sg Hf. apply (fair_flush_sound_iff _ _ sg Hf). apply H; assumption.
    - intros H w Hw sg Hf. apply (fair_flush_sound_iff _ _ sg Hf). apply H; assumption.
  Qed.

  Theorem flushR_sound_iff : forall r s0, FlushR' r s0 <->
    (forall w, OKw r w -> exists c, Forall InJ c /\
       Sd (fst (run w s0)) (sw (fst (run w s0)) c (snd (run w s0)))).
  Proof.
    intros r s0. rewrite flushR_at. split.
    - intros H w Hw. apply flushat_sound_iff. apply H. exact Hw.
    - intros H w Hw. apply flushat_sound_iff. apply H. exact Hw.
  Qed.

  Theorem sandr_fairflush : forall r s0, SandR r s0 -> FairFlushR r s0.
  Proof.
    intros r s0 H w Hw. rewrite (surjective_pairing (run w s0)). apply sand_fairflush. apply H. exact Hw.
  Qed.

  Theorem soundr_fairflush : forall r s0, SoundR r s0 -> FairFlushR r s0.
  Proof. intros r s0 H. apply sandr_fairflush. intros w Hw. apply sand_sound. apply H. exact Hw. Qed.

  Theorem lowr_fairflush : forall r s0, LowR' r s0 -> FairFlushR r s0.
  Proof. intros r s0 H. apply sandr_fairflush. intros w Hw. apply sand_low. apply H. exact Hw. Qed.

  Theorem evsand_sandr : forall r s0, EvSand -> Sand (fst s0) (snd s0) -> SandR r s0.
  Proof.
    intros r s0 He H0 w Hw. revert s0 H0. induction Hw as [| a w Ha _ IH]; intros s0 H0; [exact H0 |].
    cbn [crun]. apply IH. destruct a as [e | j |]; cbn [cstep fst snd].
    - apply He. exact H0.
    - apply sand_u. exact H0.
    - apply sand_low. apply bot_least.
  Qed.

  Theorem evsound_soundr : forall r s0, EvSound -> Sd (fst s0) (snd s0) -> SoundR r s0.
  Proof.
    intros r s0 He H0 w Hw. revert s0 H0. induction Hw as [| a w Ha _ IH]; intros s0 H0; [exact H0 |].
    cbn [crun]. apply IH. destruct a as [e | j |]; cbn [cstep fst snd].
    - apply He. exact H0.
    - apply u_sound. exact H0.
    - unfold sound. apply bot_least.
  Qed.

  Theorem evlow_fairflush : forall r s0, EvLow' -> le (snd s0) (LF (fst s0)) -> FairFlushR r s0.
  Proof.
    intros r s0 He H0. apply lowr_fairflush.
    exact (evlow_lowr Loc Sh le le_refl le_trans bot bot_least rank rank_strict height rank_bound
             sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov E ev r s0 He H0).
  Qed.

  (* gsm's starts (Nc t: the shared part produced by the repair) are sound and low. *)
  Lemma nc_sound_low : forall t, Sd (fst (NC t)) (snd (NC t)) /\ le (snd (NC t)) (LF (fst (NC t))).
  Proof.
    intros t. rewrite (Nc_eq Loc Sh bot sh_eq_dec u K js t). cbn [fst snd].
    split; [apply fixed_sound; apply lf_fixed | apply le_refl].
  Qed.

  Section InflSound.
    Variable lle : Loc -> Loc -> Prop.
    Hypothesis F_mono_l : forall l l' h, lle l l' -> le (F l h) (F l' h).

    (* Inflationary events that leave the shared values alone keep every state sound. *)
    Theorem infl_evsound :
      (forall e t, lle (fst t) (fst (ev e t)) /\ snd (ev e t) = snd t) -> EvSound.
    Proof.
      intros H e t Hs. destruct (H e t) as [Hl Hh]. unfold sound. rewrite Hh.
      eapply le_trans; [exact Hs | apply F_mono_l; exact Hl].
    Qed.
  End InflSound.

  (* ----- 3. NoGhostR exactly ----- *)

  (* Every word is a pure propagation word, or ends with an event or reset followed by
     propagation. *)
  Lemma split_last : forall r w, OKw r w ->
    (exists c, Forall InJ c /\ w = PW c) \/
    (exists p a c, OKw r p /\ okc js E r a /\ (forall j, a <> AProp E j) /\ Forall InJ c /\
                   w = p ++ a :: PW c).
  Proof.
    intros r w Hw. induction Hw as [| a w Ha Hw' IH].
    - left. exists []. split; [constructor | reflexivity].
    - destruct IH as [[c [Hc ->]] | [p [b [c [Hp [Hb [Hn [Hc ->]]]]]]]].
      + destruct a as [e | j |].
        * right. exists [], (AEv E e), c. split; [constructor |]. split; [exact Ha |].
          split; [intros j Ej; discriminate Ej |]. split; [exact Hc | reflexivity].
        * left. exists (j :: c). split; [constructor; [exact Ha | exact Hc] | reflexivity].
        * right. exists [], (AReset E), c. split; [constructor |]. split; [exact Ha |].
          split; [intros j Ej; discriminate Ej |]. split; [exact Hc | reflexivity].
      + right. exists (a :: p), b, c. split; [constructor; [exact Ha | exact Hp] |].
        split; [exact Hb |]. split; [exact Hn |]. split; [exact Hc | reflexivity].
  Qed.

  Lemma ghostfree_low : forall t, le (snd t) (LF (fst t)) -> GhostFree t.
  Proof.
    intros t H c Hc Hq. apply quiet_props in Hq. rewrite run_props. cbn [fst snd].
    apply le_antisym; [apply sw_below; exact H | apply lf_least; apply stable_fixed; exact Hq].
  Qed.

  (* A sound state is ghost-free exactly when it is below the least fixed point. *)
  Theorem ghostfree_sound_iff : forall t, Sd (fst t) (snd t) ->
    (GhostFree t <-> le (snd t) (LF (fst t))).
  Proof.
    intros [l h] Hs. cbn [fst snd] in *. split; [| apply (ghostfree_low (l, h))].
    intros G.
    destruct (fair_to_word l h (sand_fairflush l h (sand_sound l h Hs))) as [c [Hc St]].
    pose proof (G c Hc (proj2 (quiet_props c (l, h)) St)) as E1.
    rewrite run_props in E1. cbn [fst snd] in E1.
    destruct (sw_up l c h Hs) as [_ Up]. rewrite E1 in Up. exact Up.
  Qed.

  (* Exact: no reachable ghost iff the start and every post-event state are ghost-free. *)
  Theorem noghost_event_iff : forall r s0,
    NoGhostR' r s0 <-> (GhostFree s0 /\ forall p e, OKw r p -> GhostFree (ev e (run p s0))).
  Proof.
    intros r s0. split.
    - intros Hg. split.
      + intros c Hc Hq. pose proof (Hg (PW c) (ok_props js E r c Hc) Hq) as G.
        rewrite fst_pw in G. exact G.
      + intros p e Hp c Hc Hq.
        assert (O : OKw r ((p ++ [AEv E e]) ++ PW c)).
        { apply ok_app; [apply ok_app; [exact Hp | apply ok_ev1] | apply ok_props; exact Hc]. }
        assert (R : run ((p ++ [AEv E e]) ++ PW c) s0 = run (PW c) (ev e (run p s0))).
        { rewrite !run_app. reflexivity. }
        pose proof (Hg _ O) as G. rewrite R in G. specialize (G Hq). rewrite fst_pw in G. exact G.
    - intros [H0 He] w Hw Hq.
      destruct (split_last r w Hw) as [[c [Hc ->]] | [p [a [c [Hp [Ha [Hn [Hc ->]]]]]]]].
      + rewrite fst_pw. apply H0; assumption.
      + rewrite run_app in Hq |- *. cbn [crun] in Hq |- *. rewrite fst_pw.
        destruct a as [e | j |].
        * apply He; assumption.
        * exfalso. apply (Hn j). reflexivity.
        * cbn [cstep] in *. apply (ghostfree_low (fst (run p s0), bot)); [apply bot_least | exact Hc | exact Hq].
  Qed.

  (* Where a ghost comes from: every reachable quiescent ghost is reached by propagation from the
     start or from the output of a last event, and that state is NOT below the least fixed point
     of its locals (an event moved shared values above it, and the cycle sustained them). *)
  Theorem ghost_witness : forall r s0 w, OKw r w -> Qt (run w s0) ->
    snd (run w s0) <> LF (fst (run w s0)) ->
    (exists c, Forall InJ c /\ w = PW c /\ ~ le (snd s0) (LF (fst s0))) \/
    (exists p e c, OKw r p /\ Forall InJ c /\ w = p ++ AEv E e :: PW c /\
       ~ le (snd (ev e (run p s0))) (LF (fst (ev e (run p s0))))).
  Proof.
    intros r s0 w Hw Hq Hne.
    destruct (split_last r w Hw) as [[c [Hc ->]] | [p [a [c [Hp [Ha [Hn [Hc ->]]]]]]]].
    - left. exists c. split; [exact Hc |]. split; [reflexivity |]. intro L.
      apply Hne. rewrite fst_pw. exact (ghostfree_low s0 L c Hc Hq).
    - rewrite run_app in Hq, Hne. cbn [crun] in Hq, Hne. rewrite fst_pw in Hne.
      destruct a as [e | j |].
      + right. exists p, e, c. split; [exact Hp |]. split; [exact Hc |]. split; [reflexivity |].
        intro L. apply Hne. exact (ghostfree_low _ L c Hc Hq).
      + exfalso. apply (Hn j). reflexivity.
      + exfalso. apply Hne. cbn [cstep] in *.
        exact (ghostfree_low (fst (run p s0), bot) (bot_least _) c Hc Hq).
  Qed.

  Lemma noghost_ghostfree : forall r s0, NoGhostR' r s0 -> forall w, OKw r w -> GhostFree (run w s0).
  Proof.
    intros r s0 Hg w Hw c Hc Hq.
    assert (O : OKw r (w ++ PW c)) by (apply ok_app; [exact Hw | apply ok_props; exact Hc]).
    pose proof (Hg _ O) as G. rewrite run_app in G. specialize (G Hq). rewrite fst_pw in G. exact G.
  Qed.

  (* Under reachable soundness, no ghost exactly when every reachable state is low. *)
  Theorem noghost_soundr_iff : forall r s0, SoundR r s0 -> (NoGhostR' r s0 <-> LowR' r s0).
  Proof.
    intros r s0 Hs. split.
    - intros Hg w Hw. apply (ghostfree_sound_iff (run w s0) (Hs w Hw)).
      apply (noghost_ghostfree r s0 Hg w Hw).
    - intros Hl.
      exact (low_noghost Loc Sh le le_refl le_trans le_antisym bot bot_least rank rank_strict height
               rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed K K_big js Hcov E ev r s0 Hl).
  Qed.

  (* LowR is a per-event condition at the reachable states: the start is low and every event,
     applied at a reachable state, leaves the shared values below the least fixed point of the
     new locals. *)
  Theorem lowr_post_iff : forall r s0, LowR' r s0 <->
    (le (snd s0) (LF (fst s0)) /\
     forall p e, OKw r p -> le (snd (ev e (run p s0))) (LF (fst (ev e (run p s0))))).
  Proof.
    intros r s0. split.
    - intros Hl. split; [exact (Hl [] ltac:(constructor)) |].
      intros p e Hp.
      assert (O : OKw r (p ++ [AEv E e])) by (apply ok_app; [exact Hp | apply ok_ev1]).
      pose proof (Hl _ O) as L. rewrite run_app in L. exact L.
    - intros [H0 He] w Hw.
      destruct (split_last r w Hw) as [[c [Hc ->]] | [p [a [c [Hp [Ha [Hn [Hc ->]]]]]]]].
      + rewrite run_props. apply sw_below. exact H0.
      + rewrite run_app. cbn [crun]. rewrite run_props. apply sw_below.
        destruct a as [e | j |].
        * apply He. exact Hp.
        * exfalso. apply (Hn j). reflexivity.
        * apply bot_least.
  Qed.

  Theorem soundr_agree_iff : forall r s0, SoundR r s0 -> (DAgreeQ' r s0 <-> XUcR' r s0 /\ LowR' r s0).
  Proof.
    intros r s0 Hs. pose proof (fairflushR_flushR r s0 (soundr_fairflush r s0 Hs)) as Hf.
    rewrite <- (noghost_soundr_iff r s0 Hs).
    exact (quiet_agree_iff Loc Sh bot sh_eq_dec u K js E ev r s0 Hf).
  Qed.

  Theorem soundr_fed_iff : forall r s0, SoundR r s0 ->
    (DAgreeQ' r s0 /\ DConvQ' r s0 <-> XUcR' r s0 /\ LowR' r s0 /\ FMConv' (NC s0)).
  Proof.
    intros r s0 Hs. pose proof (fairflushR_flushR r s0 (soundr_fairflush r s0 Hs)) as Hf.
    rewrite <- (noghost_soundr_iff r s0 Hs). split.
    - intros [Ha Hc]. destruct (proj1 (flush_fed_iff r s0) (conj Hf (conj Ha Hc))) as [Hx [Hm [_ Hg]]].
      tauto.
    - intros [Hx [Hg Hm]]. destruct (proj2 (flush_fed_iff r s0) (conj Hx (conj Hm (conj Hf Hg)))) as [_ H].
      exact H.
  Qed.

  (* The certificate form: an invariant closed under the actions, holding at the start. *)
  Definition GInv (r : bool) (s0 : Loc * Sh) (P : Loc * Sh -> Prop) : Prop :=
    P s0 /\ (forall t e, P t -> P (ev e t)) /\
    (forall t j, In j js -> P t -> P (fst t, u (fst t) j (snd t))) /\
    (r = true -> forall t, P t -> P (fst t, bot)).

  Lemma ginv_reach : forall r s0 P, GInv r s0 P -> forall w, OKw r w -> P (run w s0).
  Proof.
    intros r s0 P [H0 [He [Hp Hr]]] w Hw. revert s0 H0.
    induction Hw as [| a w Ha _ IH]; intros s0 H0; [exact H0 |]. cbn [crun]. apply IH.
    destruct a as [e | j |]; cbn [cstep].
    - apply He. exact H0.
    - apply Hp; [exact Ha | exact H0].
    - apply Hr; [exact Ha | exact H0].
  Qed.

  Theorem noghost_inv_iff : forall r s0, NoGhostR' r s0 <->
    exists P, GInv r s0 P /\ (forall t, P t -> Qt t -> snd t = LF (fst t)).
  Proof.
    intros r s0. split.
    - intros Hg. exists (fun t => exists w, OKw r w /\ run w s0 = t). split.
      + split; [exists []; split; [constructor | reflexivity] |].
        split.
        { intros t e [w [Hw <-]]. exists (w ++ [AEv E e]).
          split; [apply ok_app; [exact Hw | apply ok_ev1] | rewrite run_app; reflexivity]. }
        split.
        { intros t j Hj [w [Hw <-]]. exists (w ++ [AProp E j]).
          split; [apply ok_app; [exact Hw | constructor; [exact Hj | constructor]] |
                  rewrite run_app; reflexivity]. }
        intros Hr t [w [Hw <-]]. exists (w ++ [AReset E]).
        split; [apply ok_app; [exact Hw | constructor; [exact Hr | constructor]] |
                rewrite run_app; reflexivity].
      + intros t [w [Hw <-]] Hq. apply Hg; assumption.
    - intros [P [Hi Hq]] w Hw Hqw. apply Hq; [apply (ginv_reach r s0 P Hi w Hw) | exact Hqw].
  Qed.

  (* The per-state check beyond EvLow and global uniqueness: on an invariant, every state has
     locals with one fixed point, or is low. *)
  Theorem unique_or_low_noghost : forall r s0 P, GInv r s0 P ->
    (forall t, P t -> UniqueFP (fst t) \/ le (snd t) (LF (fst t))) -> NoGhostR' r s0.
  Proof.
    intros r s0 P Hi Hu. apply noghost_inv_iff. exists P. split; [exact Hi |].
    intros t Ht Hq. assert (Fx : F (fst t) (snd t) = snd t) by (apply stable_fixed; exact Hq).
    destruct (Hu t Ht) as [U | L]; [apply U; exact Fx |].
    apply le_antisym; [exact L | apply lf_least; exact Fx].
  Qed.

  (* uniq_noghost and the EvLow route are the two extreme invariants. *)
  Theorem unique_or_low_recovers : forall r s0,
    ((forall l, UniqueFP l) -> NoGhostR' r s0) /\
    (EvLow' -> le (snd s0) (LF (fst s0)) -> NoGhostR' r s0).
  Proof.
    intros r s0. split.
    - intros Hu. apply (unique_or_low_noghost r s0 (fun _ => True)).
      + split; [exact Logic.I | split; [intros; exact Logic.I | split; intros; exact Logic.I]].
      + intros t _. left. apply Hu.
    - intros He H0. apply (unique_or_low_noghost r s0 (fun t => le (snd t) (LF (fst t)))).
      + split; [exact H0 |]. split; [intros t e Ht; apply He; exact Ht |].
        split; [intros t j _ Ht; apply u_below; exact Ht | intros _ t _; apply bot_least].
      + intros t Ht. right. exact Ht.
  Qed.

  (* Identity events (no events at all, in effect). *)
  Lemma id_events : (forall e t, ev e t = t) -> forall r s0, XUcR' r s0 /\ FMConv' (NC s0).
  Proof.
    intros Hid r s0. split.
    - intros p e _. unfold XUc. rewrite !Hid. reflexivity.
    - assert (G : forall es, FM Loc Sh bot sh_eq_dec u K js E ev es (NC s0) = NC s0).
      { induction es as [| e es IH]; [reflexivity |].
        rewrite (FM_cons Loc Sh bot sh_eq_dec u K js E ev), Hid,
                (Nc_idem Loc Sh bot sh_eq_dec u K js). exact IH. }
      intros es1 es2 _. pose proof (G es1) as G1. pose proof (G es2) as G2.
      unfold FM in G1, G2. rewrite G1, G2. reflexivity.
  Qed.
  End Ev.

  (* ===================================================================================== *)
  (* 4. gsm's per-target checks: what is left to certify without resets.                    *)
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
  Hypothesis lfp_valid : forall l, FValid Loc Sh Lc Hc Rg lget sget cvalid (l, LF l).
  Variable Hs : Rg -> Hc -> Prop.
  Hypothesis Hs_lfp : forall l k, Hs k (sget k (LF l)).

  Local Notation evL := (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig).
  Local Notation nrL := (nreg Rg enc E reg).

  (* With C1cyc and C2cyc (gsm's cyclic checks) over a set covering the reachable shared values,
     a no-reset deployment is certified exactly when it flushes and has no reachable ghost. *)
  Theorem lens_noreset_iff : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs ->
    forall r s0, HsReachR Loc Sh bot u js Lc Hc Rg lget lset sget sset E reg sig Hs r s0 ->
    ((FlushR Loc Sh bot u js E evL r s0 /\ DAgreeQ Loc Sh bot sh_eq_dec u K js E evL r s0 /\
      DConvQ Loc Sh bot u js E evL nrL I r s0) <->
     (FlushR Loc Sh bot u js E evL r s0 /\ NoGhostR Loc Sh bot sh_eq_dec u K js E evL r s0)).
  Proof.
    intros H1 H2 r s0 Hr.
    pose proof (lens_xucr Loc Sh bot sh_eq_dec u K js Lc Hc Rg lget lset sget sset cvalid E reg sig
                  lfp_valid Hs Hs_lfp H1 r s0 Hr) as Hx.
    pose proof (lens_fmconv Loc Sh bot sh_eq_dec u K js Lc Hc Rg rg_eq_dec enc lget lset
                  lget_lset_eq lget_lset_neq l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg
                  sig I sig_valid lfp_valid Hs Hs_lfp H1 H2 s0) as Hm.
    rewrite (flush_fed_iff E evL nrL I r s0). tauto.
  Qed.

  Theorem lens_noreset_fair_iff : C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs ->
    forall r s0, HsReachR Loc Sh bot u js Lc Hc Rg lget lset sget sset E reg sig Hs r s0 ->
    ((FairFlushR E evL r s0 /\ DAgreeQ Loc Sh bot sh_eq_dec u K js E evL r s0 /\
      DConvQ Loc Sh bot u js E evL nrL I r s0) <->
     (FairFlushR E evL r s0 /\ NoGhostR Loc Sh bot sh_eq_dec u K js E evL r s0)).
  Proof.
    intros H1 H2 r s0 Hr.
    pose proof (lens_xucr Loc Sh bot sh_eq_dec u K js Lc Hc Rg lget lset sget sset cvalid E reg sig
                  lfp_valid Hs Hs_lfp H1 r s0 Hr) as Hx.
    pose proof (lens_fmconv Loc Sh bot sh_eq_dec u K js Lc Hc Rg rg_eq_dec enc lget lset
                  lget_lset_eq lget_lset_neq l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg
                  sig I sig_valid lfp_valid Hs Hs_lfp H1 H2 s0) as Hm.
    rewrite (fair_fed_iff E evL nrL I r s0). tauto.
  Qed.
  End Lens.
End Exact.

(* ======================================================================================= *)
(* Part 2. Shared helpers for the instances.                                                *)
(* ======================================================================================= *)

Lemma K3 : 2 < 3. Proof. lia. Qed.
Lemma K4 : 3 < 4. Proof. lia. Qed.
Lemma K2 : 1 < 2. Proof. lia. Qed.

Definition noI {A : Type} (_ _ : A) : Prop := False.

(* With no declared-independent pair, trace equivalence is equality. *)
Lemma none_tequiv : forall (E : Type) (reg : E -> nat) (I : E -> E -> Prop),
  (forall a b, ~ Ifd E reg I a b) -> forall l1 l2, tequiv (Ifd E reg I) l1 l2 -> l1 = l2.
Proof.
  intros E reg I Hn l1 l2 H.
  induction H as [l | l a b r Hab | l1 l2 _ IH | l1 l2 l3 _ IH1 _ IH2].
  - reflexivity.
  - exfalso. exact (Hn a b Hab).
  - symmetry. exact IH.
  - congruence.
Qed.

(* ======================================================================================= *)
(* Part 3. The two-flag cycle of FederationEventsCycles.v (sa := lb || sb, sb := la || sa). *)
(* ======================================================================================= *)

(* One propagation step always yields a sound state on this cycle, so every fair schedule from
   every state settles (whatever the events did). *)
Lemma cu_step_sound : StepSound B2 B2 cle cF cu cts.
Proof. intros l j h [<- | [<- | []]]; bf; vm_compute; split; reflexivity. Qed.

Lemma c_fairflush : forall t, FairFlushAt B2 B2 cu cts t.
Proof.
  exact (step_sound_fairflush B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
           crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 K3 cts
           cts_cover cu_step_sound).
Qed.

Lemma c_fairflushR : forall (E : Type) (ev : E -> B2 * B2 -> B2 * B2) r s0,
  FairFlushR B2 B2 cbot cu cts E ev r s0.
Proof. intros E ev r s0 w _. apply c_fairflush. Qed.

Lemma c_flushR : forall (E : Type) (ev : E -> B2 * B2 -> B2 * B2) r s0,
  FlushR B2 B2 cbot cu cts E ev r s0.
Proof.
  intros E ev r s0.
  exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
           crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 K3 cts
           cts_cover E ev (fun _ => 0) noI r s0 (c_fairflushR E ev r s0)).
Qed.

(* The NoGhostR conjunct is necessary: on dist_cyc_ghost every other right-hand conjunct holds
   (every fair schedule from every reachable state settles), and agreement fails. The reachable
   state after PingA; ClearA is neither sound nor sandwiched, so SoundR and SandR (and LowR) are
   sufficient for FairFlushR but not necessary. *)
Definition w_unsound : list (cact iev) := [AEv iev PingA; AEv iev ClearA'].

Theorem ghost_exact :
  FairFlushR B2 B2 cbot cu cts iev icev false gs0 /\
  FlushR B2 B2 cbot cu cts iev icev false gs0 /\
  XUcR B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  FMConv B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI (dNc gs0) /\
  ~ NoGhostR B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  ~ (FlushR B2 B2 cbot cu cts iev icev false gs0 /\
     DAgreeQ B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
     DConvQ B2 B2 cbot cu cts iev icev inreg iI false gs0) /\
  irun w_unsound gs0 = ((false, false), (true, false)) /\
  ~ SoundR B2 B2 cle cbot cF cu cts iev icev false gs0 /\
  ~ SandR B2 B2 cle cbot cF cu cts iev icev false gs0 /\
  ~ LowR B2 B2 cle cbot ceq_dec cu 3 cts iev icev false gs0.
Proof.
  destruct dist_cyc_ghost as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nC & nA & nG & nL).
  assert (Ow : OK cts iev false w_unsound) by (repeat constructor).
  assert (Est : irun w_unsound gs0 = ((false, false), (true, false))) by (vm_compute; reflexivity).
  split; [apply c_fairflushR |]. split; [apply c_flushR |].
  split; [apply i_xucr |]. split; [apply i_fmconv |]. split; [exact nG |].
  split; [intros [_ [Ha _]]; exact (nA Ha) |]. split; [exact Est |].
  split.
  { intro H. pose proof (H w_unsound Ow) as S. unfold irun in Est. rewrite Est in S.
    vm_compute in S. destruct S as [S _]. discriminate S. }
  split; [| exact nL].
  intro H. pose proof (H w_unsound Ow) as S. unfold irun in Est. rewrite Est in S.
  cbn [fst snd] in S. destruct S as [s [S1 [S2 S3]]].
  destruct s as [[|] [|]]; vm_compute in S1, S2;
    try (destruct S1 as [X Y]; first [discriminate X | discriminate Y]);
    try (destruct S2 as [X Y]; first [discriminate X | discriminate Y]).
  specialize (S3 (false, false) eq_refl (cbot_least _)). vm_compute in S3.
  destruct S3 as [X _]. discriminate X.
Qed.

(* Non-vacuity of the sound regime: raise-only events from a FedMachine normal form. Every
   reachable state is sound and low, every fair schedule settles, and every quiescent
   interleaving agrees with the FedMachine. *)
Lemma cF_mono_l : forall l l' h, cle l l' -> cle (cF l h) (cF l' h).
Proof. intros l l' h; bf; unfold cle, cF; simpl; intuition. Qed.

Theorem raise_only_exact : forall l r,
  SoundR B2 B2 cle cbot cF cu cts rev rcev r (l, dLfp l) /\
  LowR B2 B2 cle cbot ceq_dec cu 3 cts rev rcev r (l, dLfp l) /\
  FairFlushR B2 B2 cbot cu cts rev rcev r (l, dLfp l) /\
  DAgreeQ B2 B2 cbot ceq_dec cu 3 cts rev rcev r (l, dLfp l) /\
  DConvQ B2 B2 cbot cu cts rev rcev rnreg rI r (l, dLfp l).
Proof.
  intros l r.
  destruct (dist_cyc_raise_only r (l, dLfp l) (cle_refl _)) as [Hl [Hc Ha]].
  split.
  - apply (evsound_soundr B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 K3 cts
             cts_cover rev rcev rnreg rI r (l, dLfp l)).
    + apply (infl_evsound B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
               crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 K3 cts
               cts_cover rev rcev rnreg rI cle cF_mono_l).
      intros [] t; bf; vm_compute; split; try reflexivity; split; reflexivity.
    + bf; vm_compute; split; reflexivity.
  - split; [exact Hl |]. split; [apply c_fairflushR |]. split; [exact Ha | exact Hc].
Qed.

(* ======================================================================================= *)
(* Part 4. The 3-ring of dist_ring_livelock: FlushR without FairFlushR.                    *)
(* ======================================================================================= *)

Definition idev (_ : unit) (t : unit * R3) : unit * R3 := t.
Definition r3s0 : unit * R3 := (tt, r3h0).

Ltac r3w c := exists c; split;
  [ repeat (apply Forall_cons; [simpl; tauto |]); apply Forall_nil
  | intros j Hj; destruct Hj as [<- | [<- | [<- | []]]]; vm_compute; reflexivity ].

(* Every state of the ring has SOME flushing word. *)
Lemma r3_flushat : forall t, FlushAt unit R3 r3u r3js t.
Proof.
  intros [[] [[a b] c]]; destruct a, b, c;
  first [ r3w (@nil nat) | r3w [0] | r3w [1] | r3w [2] | r3w [1; 0] | r3w [0; 2] | r3w [2; 1] ].
Qed.

(* On the monotone 3-ring with no events, every reachable state can be flushed by some word,
   but the fair schedule of dist_ring_livelock never reaches quiescence, and a ghost (the ring
   all set) is reachable. *)
Theorem ring_exact :
  FlushR unit R3 r3bot r3u r3js unit idev false r3s0 /\
  ~ FairFlushR unit R3 r3bot r3u r3js unit idev false r3s0 /\
  XUcR unit R3 r3bot r3_eq_dec r3u 4 r3js unit idev false r3s0 /\
  ~ NoGhostR unit R3 r3bot r3_eq_dec r3u 4 r3js unit idev false r3s0.
Proof.
  destruct dist_ring_livelock as (_ & _ & _ & _ & _ & _ & _ & Hf & nS & _).
  split.
  { apply (proj2 (flushR_at unit R3 r3le r3le_refl r3le_trans r3le_antisym r3bot r3bot_least
                    r3rank r3rank_strict 3 r3rank_bound r3_eq_dec r3F r3u r3u_incr r3u_sound
                    r3u_mono r3u_fixed 4 K4 r3js r3_cover unit idev (fun _ => 0) noI false r3s0)).
    intros w _. apply r3_flushat. }
  split.
  { intro H. destruct (H [] ltac:(constructor) r3sg Hf) as [n Hn]. exact (nS n Hn). }
  split.
  { exact (proj1 (id_events unit R3 r3le r3le_refl r3le_trans r3le_antisym r3bot r3bot_least
                    r3rank r3rank_strict 3 r3rank_bound r3_eq_dec r3F r3u r3u_incr r3u_sound
                    r3u_mono r3u_fixed 4 K4 r3js r3_cover unit idev (fun _ => 0) noI
                    (fun _ _ => eq_refl) false r3s0)). }
  intro H.
  assert (O : OK r3js unit false [AProp unit 2; AProp unit 1]) by (repeat constructor; simpl; tauto).
  assert (Q : Quiet unit R3 r3u r3js (crun unit R3 r3bot r3u unit idev [AProp unit 2; AProp unit 1] r3s0)).
  { intros j Hj. destruct Hj as [<- | [<- | [<- | []]]]; vm_compute; reflexivity. }
  pose proof (H _ O Q) as X. vm_compute in X. discriminate X.
Qed.

(* ======================================================================================= *)
(* Part 5. FlushR and FairFlushR are necessary: two flip networks with ONE fixed point.     *)
(* Shared values {fz < fa, fz < fb} (fa, fb incomparable); the repair swaps fa and fb.      *)
(* ======================================================================================= *)

Inductive Fl : Type := fz | fa | fb.
Definition fle (x y : Fl) : Prop := x = fz \/ x = y.
Definition frank (x : Fl) : nat := match x with fz => 0 | _ => 1 end.
Definition fl_eq_dec : forall x y : Fl, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition fsw (x : Fl) : Fl := match x with fz => fz | fa => fb | fb => fa end.
Definition fF (_ : unit) (x : Fl) : Fl := fsw x.
(* flip1: one target, the swap. *)
Definition fu1 (_ : unit) (j : nat) (x : Fl) : Fl := match j with 0 => fsw x | _ => x end.
Definition fjs1 : list nat := [0].
(* flip2: the swap, and a second target that drops fa to fz. *)
Definition fu2 (_ : unit) (j : nat) (x : Fl) : Fl :=
  match j with 0 => fsw x | 1 => match x with fa => fz | _ => x end | _ => x end.
Definition fjs2 : list nat := [0; 1].
Definition fid (_ : unit) (t : unit * Fl) : unit * Fl := t.

Ltac fl := repeat match goal with
  | x : Fl |- _ => destruct x
  | x : unit |- _ => destruct x
  | x : unit * Fl |- _ => destruct x
  end.

Lemma fle_refl : forall x, fle x x. Proof. intros x. right. reflexivity. Qed.
Lemma fle_trans : forall x y z, fle x y -> fle y z -> fle x z.
Proof. intros x y z; fl; unfold fle; intuition congruence. Qed.
Lemma fle_antisym : forall x y, fle x y -> fle y x -> x = y.
Proof. intros x y; fl; unfold fle; intuition congruence. Qed.
Lemma fz_least : forall x, fle fz x. Proof. intros x. left. reflexivity. Qed.
Lemma frank_strict : forall x y, fle x y -> x <> y -> frank x < frank y.
Proof.
  intros x y; fl; unfold fle; simpl; intros [H | H] Hn;
    try discriminate; try (exfalso; apply Hn; reflexivity); lia.
Qed.
Lemma frank_bound : forall x, frank x <= 1. Proof. intros x; fl; simpl; lia. Qed.

Lemma fsound_z : forall l x, sound unit Fl fle fF l x -> x = fz.
Proof. intros l x; fl; unfold sound, fle, fF; simpl; intuition congruence. Qed.

Lemma fu1_incr : forall l j x, sound unit Fl fle fF l x -> fle x (fu1 l j x).
Proof. intros l j x H. rewrite (fsound_z l x H). apply fz_least. Qed.
Lemma fu1_sound : forall l j x, sound unit Fl fle fF l x -> sound unit Fl fle fF l (fu1 l j x).
Proof.
  intros l j x H. rewrite (fsound_z l x H). destruct j; unfold sound; apply fz_least.
Qed.
Lemma fu1_mono : forall l j x y, fle x y -> fle (fu1 l j x) (fu1 l j y).
Proof. intros l [| j] x y; fl; unfold fle; simpl; intuition congruence. Qed.
Lemma fu1_fixed : forall l j x, fF l x = x -> fu1 l j x = x.
Proof. intros l [| j] x; fl; unfold fF; simpl; congruence. Qed.
Lemma f1_cover : Cover unit Fl fF fu1 fjs1.
Proof. intros l x H. exact (H 0 (or_introl eq_refl)). Qed.

Lemma fu2_incr : forall l j x, sound unit Fl fle fF l x -> fle x (fu2 l j x).
Proof. intros l j x H. rewrite (fsound_z l x H). apply fz_least. Qed.
Lemma fu2_sound : forall l j x, sound unit Fl fle fF l x -> sound unit Fl fle fF l (fu2 l j x).
Proof.
  intros l j x H. rewrite (fsound_z l x H). destruct j as [| [| j]]; unfold sound; apply fz_least.
Qed.
Lemma fu2_mono : forall l j x y, fle x y -> fle (fu2 l j x) (fu2 l j y).
Proof. intros l [| [| j]] x y; fl; unfold fle; simpl; intuition congruence. Qed.
Lemma fu2_fixed : forall l j x, fF l x = x -> fu2 l j x = x.
Proof. intros l [| [| j]] x; fl; unfold fF; simpl; congruence. Qed.
Lemma f2_cover : Cover unit Fl fF fu2 fjs2.
Proof. intros l x H. exact (H 0 (or_introl eq_refl)). Qed.

Lemma f1_unique : forall l, UniqueFP unit Fl fz fl_eq_dec fF fu1 2 fjs1 l.
Proof. intros l p; fl; vm_compute; congruence. Qed.
Lemma f2_unique : forall l, UniqueFP unit Fl fz fl_eq_dec fF fu2 2 fjs2 l.
Proof. intros l p; fl; vm_compute; congruence. Qed.

Lemma f1_sweep : forall c x, x <> fz -> sweep unit Fl fu1 tt c x <> fz.
Proof.
  intros c. induction c as [| j c IH]; intros x Hx; [exact Hx |]. simpl. apply IH.
  destruct j; fl; simpl; congruence.
Qed.

(* The FlushR conjunct is necessary: on flip1 with no events, reachable XU, FedMachine
   convergence, a unique fixed point and no ghost all hold, but from fa no propagation word ever
   reaches quiescence (fa and fb swap forever). *)
Theorem flip_noflush :
  (forall l, UniqueFP unit Fl fz fl_eq_dec fF fu1 2 fjs1 l) /\
  XUcR unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid false (tt, fa) /\
  FMConv unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid (fun _ => 0) noI
    (Nc unit Fl fz fl_eq_dec fu1 2 fjs1 (tt, fa)) /\
  NoGhostR unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid false (tt, fa) /\
  ~ FlushR unit Fl fz fu1 fjs1 unit fid false (tt, fa).
Proof.
  pose proof (id_events unit Fl fle fle_refl fle_trans fle_antisym fz fz_least frank frank_strict 1
                frank_bound fl_eq_dec fF fu1 fu1_incr fu1_sound fu1_mono fu1_fixed 2 K2 fjs1
                f1_cover unit fid (fun _ => 0) noI (fun _ _ => eq_refl) false (tt, fa)) as [Hx Hm].
  split; [exact f1_unique |]. split; [exact Hx |]. split; [exact Hm |].
  split.
  { exact (proj1 (unique_or_low_recovers unit Fl fle fle_refl fle_trans fle_antisym fz fz_least
                    frank frank_strict 1 frank_bound fl_eq_dec fF fu1 fu1_incr fu1_sound fu1_mono
                    fu1_fixed 2 K2 fjs1 f1_cover unit fid (fun _ => 0) noI false (tt, fa))
             f1_unique). }
  intro H. destruct (H [] ltac:(constructor)) as [c [_ Hq]].
  cbn [app] in Hq. rewrite (crun_props unit Fl fz fu1 unit fid c (tt, fa)) in Hq.
  pose proof (Hq 0 (or_introl eq_refl)) as S. cbn [fst snd] in S.
  apply (f1_sweep c fa ltac:(discriminate)).
  destruct (sweep unit Fl fu1 tt c fa); simpl in S; congruence.
Qed.

Definition f2l : list nat := [0; 1; 0].
Definition f2sg : nat -> nat := rrs f2l.

Lemma f2_fair : Fair fjs2 f2sg.
Proof. apply (fair_same f2l); [apply rrs_fair; discriminate | intro j; simpl; tauto]. Qed.

Lemma f2_state : forall n,
  prs Fl (fu2 tt) f2sg n fa = if Nat.eqb (rrp f2l n) 0 then fa else fb.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [prs]. rewrite IH. unfold f2sg, rrs. rewrite (rrp_S f2l n).
  pose proof (rrp_lt f2l ltac:(discriminate) n) as Hl. simpl length in Hl.
  destruct (rrp f2l n) as [| [| [| p]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.

(* The FairFlushR conjunct is necessary even when FlushR holds: on flip2 with no events, every
   state has a flushing word (fa -> fz by the second target) and the repair has one fixed point,
   but the fair schedule 0, 1, 0, 0, 1, 0, ... moves fa -> fb -> fb -> fa forever. *)
Theorem flip2_fair_livelock :
  (forall l, UniqueFP unit Fl fz fl_eq_dec fF fu2 2 fjs2 l) /\
  XUcR unit Fl fz fl_eq_dec fu2 2 fjs2 unit fid false (tt, fa) /\
  FMConv unit Fl fz fl_eq_dec fu2 2 fjs2 unit fid (fun _ => 0) noI
    (Nc unit Fl fz fl_eq_dec fu2 2 fjs2 (tt, fa)) /\
  NoGhostR unit Fl fz fl_eq_dec fu2 2 fjs2 unit fid false (tt, fa) /\
  FlushR unit Fl fz fu2 fjs2 unit fid false (tt, fa) /\
  Fair fjs2 f2sg /\
  (forall n, ~ Stable Fl (fu2 tt) fjs2 (prs Fl (fu2 tt) f2sg n fa)) /\
  ~ FairFlushR unit Fl fz fu2 fjs2 unit fid false (tt, fa).
Proof.
  pose proof (id_events unit Fl fle fle_refl fle_trans fle_antisym fz fz_least frank frank_strict 1
                frank_bound fl_eq_dec fF fu2 fu2_incr fu2_sound fu2_mono fu2_fixed 2 K2 fjs2
                f2_cover unit fid (fun _ => 0) noI (fun _ _ => eq_refl) false (tt, fa)) as [Hx Hm].
  assert (nS : forall n, ~ Stable Fl (fu2 tt) fjs2 (prs Fl (fu2 tt) f2sg n fa)).
  { intros n Hn. rewrite f2_state in Hn. specialize (Hn 0 (or_introl eq_refl)).
    destruct (Nat.eqb (rrp f2l n) 0); discriminate Hn. }
  split; [exact f2_unique |]. split; [exact Hx |]. split; [exact Hm |].
  split.
  { exact (proj1 (unique_or_low_recovers unit Fl fle fle_refl fle_trans fle_antisym fz fz_least
                    frank frank_strict 1 frank_bound fl_eq_dec fF fu2 fu2_incr fu2_sound fu2_mono
                    fu2_fixed 2 K2 fjs2 f2_cover unit fid (fun _ => 0) noI false (tt, fa))
             f2_unique). }
  split.
  { apply (proj2 (flushR_at unit Fl fle fle_refl fle_trans fle_antisym fz fz_least frank
                    frank_strict 1 frank_bound fl_eq_dec fF fu2 fu2_incr fu2_sound fu2_mono
                    fu2_fixed 2 K2 fjs2 f2_cover unit fid (fun _ => 0) noI false (tt, fa))).
    intros w _. destruct (crun unit Fl fz fu2 unit fid w (tt, fa)) as [[] x].
    destruct x; [exists [] | exists [1] | exists [0; 1]];
      (split; [repeat (apply Forall_cons; [simpl; tauto |]); apply Forall_nil |
               intros j Hj; destruct Hj as [<- | [<- | []]]; reflexivity]). }
  split; [exact f2_fair |]. split; [exact nS |].
  intro H. destruct (H [] ltac:(constructor) f2sg f2_fair) as [n Hn]. exact (nS n Hn).
Qed.

(* ======================================================================================= *)
(* Part 6. XUcR and FMConv are necessary: the registry cycle with one fixed point           *)
(* (sa := lb, sb := la || sa) of dist_cyc_unique_no_reset, where no ghost exists.           *)
(* ======================================================================================= *)

Lemma uu_decr : forall l j x, cle (uF l x) x -> cle (uu l j x) x.
Proof. intros l [| [| j]] x; bf; unfold cle, uu, uF; simpl; intuition. Qed.
Lemma uu_cosound : forall l j x, cle (uF l x) x -> cle (uF l (uu l j x)) (uu l j x).
Proof. intros l [| [| j]] x; bf; unfold cle, uu, uF; simpl; intuition. Qed.

Lemma u_unique : forall l p, uF l p = p -> p = uLfp l.
Proof. exact (proj1 (proj2 dist_cyc_unique_no_reset)). Qed.

(* One fixed point, a top element and the dual step laws: every fair schedule from every state
   settles (q1_unique_iff). *)
Lemma u_fairflush : forall t, FairFlushAt B2 B2 uu cts t.
Proof.
  intros [l h] sg Hf. cbn [fst snd].
  destruct (proj2 (q1_unique_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
                     crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 K3
                     cts u_cover ctop ctop_greatest uu_decr uu_cosound l sg Hf) (u_unique l) h)
    as [N HN].
  exists N. rewrite (HN N (le_n N)). intros j _. apply uu_fixed.
  exact (proj1 (proj1 dist_cyc_unique_no_reset l)).
Qed.

Lemma u_fairflushR : forall (E : Type) (ev : E -> B2 * B2 -> B2 * B2) r s0,
  FairFlushR B2 B2 cbot uu cts E ev r s0.
Proof. intros E ev r s0 w _. apply u_fairflush. Qed.

(* A copy event: A's alarm := A's shared flag (it reads a possibly stale shared value). *)
Inductive cpev : Type := CopyA.
Definition cpreg (_ : cpev) : bool := true.
Definition cpsig (_ : cpev) (x : bool * bool) : bool * bool := (snd x, snd x).
Definition cpcev : cpev -> B2 * B2 -> B2 * B2 :=
  cev B2 B2 bool bool bool rget rset rget rset cpev cpreg cpsig.
Definition cpnreg : cpev -> nat := nreg bool renc cpev cpreg.
Definition cps0 : B2 * B2 := ((false, true), (false, false)).
Definition w_copy : list (cact cpev) := [AEv cpev CopyA; AProp cpev 0; AProp cpev 1].

(* The XUcR conjunct is necessary: every fair schedule settles, no ghost exists (one fixed
   point), the FedMachine converges (one event), the start is below the least fixed point, yet
   CopyA reads A's not-yet-propagated flag and the quiescent result differs from the FedMachine. *)
Theorem copy_xu_fails :
  cle (snd cps0) (uLfp (fst cps0)) /\
  FairFlushR B2 B2 cbot uu cts cpev cpcev false cps0 /\
  NoGhostR B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0 /\
  FMConv B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI (Nc B2 B2 cbot ceq_dec uu 3 cts cps0) /\
  ~ XUcR B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0 /\
  crun B2 B2 cbot uu cpev cpcev w_copy cps0 = ((false, true), (true, true)) /\
  FM B2 B2 cbot ceq_dec uu 3 cts cpev cpcev (cevs cpev w_copy)
     (Nc B2 B2 cbot ceq_dec uu 3 cts cps0) = ((true, true), (true, true)) /\
  ~ DAgreeQ B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0.
Proof.
  assert (Ow : OK cts cpev false w_copy) by (repeat constructor; simpl; tauto).
  assert (Qw : Quiet B2 B2 uu cts (crun B2 B2 cbot uu cpev cpcev w_copy cps0)).
  { intros j Hj. destruct Hj as [<- | [<- | []]]; vm_compute; reflexivity. }
  split; [vm_compute; split; reflexivity |].
  split; [apply u_fairflushR |].
  split; [exact (uniq_noghost B2 B2 cbot ceq_dec uF uu uu_fixed 3 cts u_cover cpev cpcev false cps0 u_unique) |].
  split.
  { intros es1 es2 Ht.
    rewrite (none_tequiv cpev cpnreg noI ltac:(intros [] [] [H | H]; [apply H; reflexivity | exact H])
               es1 es2 Ht).
    reflexivity. }
  split.
  { intro H. pose proof (H [] CopyA ltac:(constructor)) as X. unfold XUc in X. vm_compute in X.
    discriminate X. }
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  intro H. pose proof (H w_copy Ow Qw) as X. vm_compute in X. discriminate X.
Qed.

(* Two events on A declared independent although they do not commute. *)
Inductive sev : Type := SetA | ClrA.
Definition sreg (_ : sev) : bool := true.
Definition ssig (e : sev) (x : bool * bool) : bool * bool :=
  match e with SetA => (true, snd x) | ClrA => (false, snd x) end.
Definition sI (a b : sev) : Prop := a <> b.
Definition scev : sev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset sev sreg ssig.
Definition snreg : sev -> nat := nreg bool renc sev sreg.

(* The FMConv conjunct is necessary: every fair schedule settles, no ghost exists, reachable XU
   holds (the events ignore shared values), and the FedMachine does not converge. *)
Theorem fm_conv_fails : forall r s0,
  FairFlushR B2 B2 cbot uu cts sev scev r s0 /\
  XUcR B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
  NoGhostR B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
  ~ FMConv B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI (Nc B2 B2 cbot ceq_dec uu 3 cts s0) /\
  ~ (FlushR B2 B2 cbot uu cts sev scev r s0 /\ DAgreeQ B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
     DConvQ B2 B2 cbot uu cts sev scev snreg sI r s0).
Proof.
  intros r s0.
  assert (H1 : C1cyc bool bool bool cv1 sev sreg ssig Hall) by (intros [] x h h' _ _ _; reflexivity).
  assert (Hx : XUcR B2 B2 cbot ceq_dec uu 3 cts sev scev r s0).
  { exact (lens_xucr B2 B2 cbot ceq_dec uu 3 cts bool bool bool rget rset rget rset cv1 sev sreg ssig
             (fun _ _ => I) Hall (fun _ _ => I) H1 r s0 (fun _ _ _ => I)). }
  assert (nM : ~ FMConv B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI (Nc B2 B2 cbot ceq_dec uu 3 cts s0)).
  { intro H.
    assert (T : tequiv (Ifd sev snreg sI) [SetA; ClrA] [ClrA; SetA]).
    { apply teq_swap with (l := @nil sev) (r := @nil sev). right. discriminate. }
    pose proof (H _ _ T) as X. destruct s0 as [[a b] [c d]].
    destruct a, b, c, d; vm_compute in X; discriminate X. }
  split; [apply u_fairflushR |]. split; [exact Hx |].
  split; [exact (uniq_noghost B2 B2 cbot ceq_dec uF uu uu_fixed 3 cts u_cover sev scev r s0 u_unique) |].
  split; [exact nM |].
  intro H. apply nM.
  exact (proj1 (proj2 (proj1 (flush_fed_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least
                                 crank crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound
                                 uu_mono uu_fixed 3 K3 cts u_cover sev scev snreg sI r s0) H))).
Qed.

(* LowR is not necessary without soundness: an unsound start above the least fixed point that is
   ghost-free (one fixed point). *)
Definition bid (_ : unit) (t : B2 * B2) : B2 * B2 := t.
Definition us0 : B2 * B2 := ((false, false), (true, true)).

Theorem ghostfree_unsound :
  NoGhostR B2 B2 cbot ceq_dec uu 3 cts unit bid false us0 /\
  ~ LowR B2 B2 cle cbot ceq_dec uu 3 cts unit bid false us0 /\
  ~ SoundR B2 B2 cle cbot uF uu cts unit bid false us0.
Proof.
  split; [exact (uniq_noghost B2 B2 cbot ceq_dec uF uu uu_fixed 3 cts u_cover unit bid false us0 u_unique) |].
  split.
  - intro H. pose proof (H [] ltac:(constructor)) as X. vm_compute in X. destruct X as [X _]. discriminate X.
  - intro H. pose proof (H [] ltac:(constructor)) as X. vm_compute in X. destruct X as [X _]. discriminate X.
Qed.

(* ======================================================================================= *)
(* Part 7. NoGhostR is not necessary for convergence alone (from a FedMachine normal form). *)
(* A's flag also keeps itself: sa := lb || sa || sb, sb := la || sa. SetSA clears A's      *)
(* alarm and sets A's flag.                                                                  *)
(* ======================================================================================= *)

Definition gF (l x : B2) : B2 := (snd l || fst x || snd x, fst l || fst x).
Definition gu (l : B2) (j : nat) (x : B2) : B2 :=
  match j with
  | 0 => (fst (gF l x), snd x)
  | 1 => (fst x, snd (gF l x))
  | _ => x
  end.

Lemma gu_incr : forall l j x, sound B2 B2 cle gF l x -> cle x (gu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, gu, gF; simpl; intuition. Qed.
Lemma gu_sound : forall l j x, sound B2 B2 cle gF l x -> sound B2 B2 cle gF l (gu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, gu, gF; simpl; intuition. Qed.
Lemma gu_mono : forall l j x y, cle x y -> cle (gu l j x) (gu l j y).
Proof. intros l [| [| j]] x y; bf; unfold cle, gu, gF; simpl; intuition. Qed.
Lemma gu_fixed : forall l j x, gF l x = x -> gu l j x = x.
Proof. intros l [| [| j]] x; bf; unfold gu, gF; simpl; intro H; congruence. Qed.
Lemma g_cover : Cover B2 B2 gF gu cts.
Proof.
  intros l x H. pose proof (H 0 (or_introl eq_refl)) as H0.
  pose proof (H 1 (or_intror (or_introl eq_refl))) as H1.
  revert H0 H1. bf; unfold gu, gF; simpl; intros H0 H1; congruence.
Qed.
Lemma gu_step_sound : StepSound B2 B2 cle gF gu cts.
Proof. intros l j h [<- | [<- | []]]; bf; vm_compute; split; reflexivity. Qed.

Inductive gev : Type := SetSA.
Definition greg (_ : gev) : bool := true.
Definition gsig (_ : gev) (_ : bool * bool) : bool * bool := (false, true).
Definition gcev : gev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset gev greg gsig.
Definition gnreg : gev -> nat := nreg bool renc gev greg.
Local Notation grun' := (crun B2 B2 cbot gu gev gcev).

Lemma g_loc : forall w t, fst t = (false, false) -> fst (grun' w t) = (false, false).
Proof.
  induction w as [| a w IH]; intros t Ht; [exact Ht |]. cbn [crun]. apply IH.
  destruct t as [l [c d]]. cbn [fst] in Ht. subst l.
  destruct a as [[] | j |]; reflexivity.
Qed.

Lemma g_sa : forall w t, OK cts gev false w -> fst (snd t) = true -> fst (snd (grun' w t)) = true.
Proof.
  intros w t Hw. revert t. induction Hw as [| a w Ha _ IH]; intros t Ht; [exact Ht |].
  cbn [crun]. apply IH. destruct t as [[x y] [c d]]. cbn [fst snd] in Ht. subst c.
  destruct a as [[] | j |].
  - reflexivity.
  - destruct j as [| [| j]]; destruct x, y, d; reflexivity.
  - discriminate Ha.
Qed.

Lemma g_none : forall w, OK cts gev false w -> cevs gev w = [] -> grun' w gs0 = gs0.
Proof.
  intros w Hw. induction Hw as [| a w Ha _ IH]; intros Hc; [reflexivity |].
  destruct a as [e | j |].
  - discriminate Hc.
  - cbn [crun]. replace (cstep B2 B2 cbot gu gev gcev (AProp gev j) gs0) with gs0
      by (destruct j as [| [| j]]; reflexivity).
    apply IH. exact Hc.
  - discriminate Ha.
Qed.

Lemma g_some : forall w, OK cts gev false w -> cevs gev w <> [] -> fst (snd (grun' w gs0)) = true.
Proof.
  intros w Hw. induction Hw as [| a w Ha Hw' IH]; intros Hc; [exfalso; apply Hc; reflexivity |].
  destruct a as [e | j |].
  - cbn [crun]. apply g_sa; [exact Hw' | destruct e; reflexivity].
  - cbn [crun]. replace (cstep B2 B2 cbot gu gev gcev (AProp gev j) gs0) with gs0
      by (destruct j as [| [| j]]; reflexivity).
    apply IH. exact Hc.
  - discriminate Ha.
Qed.

Lemma g_quiet : forall t, fst t = (false, false) -> fst (snd t) = true -> Quiet B2 B2 gu cts t ->
  t = ((false, false), (true, true)).
Proof.
  intros [l [c d]] Hl Hc Hq. cbn [fst snd] in Hl, Hc. subst l c.
  pose proof (Hq 1 (or_intror (or_introl eq_refl))) as X. destruct d; [reflexivity |].
  vm_compute in X. discriminate X.
Qed.

(* From the FedMachine normal form ((false,false),(false,false)), every quiescent interleaving
   with the same events agrees (DConvQ), every fair schedule settles, reachable XU and FedMachine
   convergence hold, yet every quiescent state after an event is the ghost (true, true) at locals
   (false, false): convergence without agreement. *)
Theorem conv_ghost_normal :
  gs0 = Nc B2 B2 cbot ceq_dec gu 3 cts gs0 /\
  FairFlushR B2 B2 cbot gu cts gev gcev false gs0 /\
  XUcR B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  FMConv B2 B2 cbot ceq_dec gu 3 cts gev gcev gnreg noI (Nc B2 B2 cbot ceq_dec gu 3 cts gs0) /\
  DConvQ B2 B2 cbot gu cts gev gcev gnreg noI false gs0 /\
  ~ NoGhostR B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  ~ DAgreeQ B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0.
Proof.
  assert (Hn : forall a b, ~ Ifd gev gnreg noI a b) by (intros [] [] [H | H]; [apply H; reflexivity | exact H]).
  assert (W : OK cts gev false [AEv gev SetSA; AProp gev 1]) by (repeat constructor; simpl; tauto).
  assert (Q : Quiet B2 B2 gu cts (grun' [AEv gev SetSA; AProp gev 1] gs0)).
  { intros j Hj. destruct Hj as [<- | [<- | []]]; vm_compute; reflexivity. }
  split; [vm_compute; reflexivity |].
  split; [intros w _; apply (step_sound_fairflush B2 B2 cle cle_refl cle_trans cle_antisym cbot
           cbot_least crank crank_strict 2 crank_bound ceq_dec gF gu gu_incr gu_sound gu_mono gu_fixed
           3 K3 cts g_cover gu_step_sound) |].
  split.
  { exact (lens_xucr B2 B2 cbot ceq_dec gu 3 cts bool bool bool rget rset rget rset cv1 gev greg gsig
             (fun _ _ => I) Hall (fun _ _ => I) ltac:(intros [] x h h' _ _ _; reflexivity) false gs0
             (fun _ _ _ => I)). }
  split; [intros es1 es2 Ht; rewrite (none_tequiv gev gnreg noI Hn es1 es2 Ht); reflexivity |].
  split.
  { intros w1 w2 O1 O2 Ht Q1 Q2. pose proof (none_tequiv gev gnreg noI Hn _ _ Ht) as Ec.
    destruct (cevs gev w1) as [| e es] eqn:C1.
    - rewrite (g_none w1 O1 C1), (g_none w2 O2 (eq_sym Ec)). reflexivity.
    - assert (C2 : cevs gev w2 <> []) by (rewrite <- Ec; discriminate).
      rewrite (g_quiet _ (g_loc w1 gs0 eq_refl) (g_some w1 O1 ltac:(rewrite C1; discriminate)) Q1).
      rewrite (g_quiet _ (g_loc w2 gs0 eq_refl) (g_some w2 O2 C2) Q2). reflexivity. }
  split.
  - intro H. pose proof (H _ W Q) as X. vm_compute in X. discriminate X.
  - intro H. pose proof (H _ W Q) as X. vm_compute in X. discriminate X.
Qed.

(* ======================================================================================= *)
(* Part 8. NoGhostR per event: what a clear on a feedback loop needs.                       *)
(* ======================================================================================= *)

(* A clear that also resets its OWN shared slot to bottom still leaves a ghost: B's flag holds
   A's flag up again. On a cycle the reset must cover the cycle (a barrier, lens_epoch). *)
Inductive lev : Type := LRaise | LClearS.
Definition lreg (_ : lev) : bool := true.
Definition lsig (e : lev) (x : bool * bool) : bool * bool :=
  match e with LRaise => (true, snd x) | LClearS => (false, false) end.
Definition lcev : lev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset lev lreg lsig.
Definition w_local : list (cact lev) :=
  [AEv lev LRaise; AProp lev 1; AProp lev 0; AEv lev LClearS; AProp lev 0].

Theorem local_reset_ghost :
  (forall x, lsig LClearS x = (false, false)) /\
  OK cts lev false w_local /\
  crun B2 B2 cbot cu lev lcev w_local gs0 = ((false, false), (true, true)) /\
  Quiet B2 B2 cu cts (crun B2 B2 cbot cu lev lcev w_local gs0) /\
  FM B2 B2 cbot ceq_dec cu 3 cts lev lcev (cevs lev w_local) (dNc gs0) = ((false, false), (false, false)) /\
  ~ NoGhostR B2 B2 cbot ceq_dec cu 3 cts lev lcev false gs0 /\
  ~ DAgreeQ B2 B2 cbot ceq_dec cu 3 cts lev lcev false gs0.
Proof.
  assert (O : OK cts lev false w_local) by (repeat constructor; simpl; tauto).
  assert (Q : Quiet B2 B2 cu cts (crun B2 B2 cbot cu lev lcev w_local gs0)).
  { intros j Hj. destruct Hj as [<- | [<- | []]]; vm_compute; reflexivity. }
  split; [reflexivity |]. split; [exact O |]. split; [vm_compute; reflexivity |].
  split; [exact Q |]. split; [vm_compute; reflexivity |].
  split; intro H; pose proof (H _ O Q) as X; vm_compute in X; discriminate X.
Qed.

(* A clear on the loop is safe when the remaining locals pin the cycle's fixed point. B's alarm
   is latched (no event clears it), so every reachable locals assignment has one fixed point
   (unique_or_low_noghost). EvLow fails (ClearA from a low state with B's alarm down) and the
   repair does not have one fixed point for every locals assignment, so neither earlier
   sufficient condition applies; gsm's C1cyc and C2cyc hold, and the deployment is certified
   without resets (lens_noreset_fair_iff). *)
Inductive bev : Type := BRaiseA | BClearA | BRaiseB.
Definition breg (e : bev) : bool := match e with BRaiseB => false | _ => true end.
Definition bsig (e : bev) (x : bool * bool) : bool * bool :=
  match e with BClearA => (false, snd x) | _ => (true, snd x) end.
Definition bcev : bev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset bev breg bsig.
Definition bnreg : bev -> nat := nreg bool renc bev breg.
Definition bs0 : B2 * B2 := ((false, true), (true, true)).

Theorem latched_exact :
  bs0 = dNc bs0 /\
  NoGhostR B2 B2 cbot ceq_dec cu 3 cts bev bcev false bs0 /\
  FairFlushR B2 B2 cbot cu cts bev bcev false bs0 /\
  DAgreeQ B2 B2 cbot ceq_dec cu 3 cts bev bcev false bs0 /\
  DConvQ B2 B2 cbot cu cts bev bcev bnreg noI false bs0 /\
  ~ EvLow B2 B2 cle cbot ceq_dec cu 3 cts bev bcev /\
  ~ (forall l, UniqueFP B2 B2 cbot ceq_dec cF cu 3 cts l).
Proof.
  assert (H1 : C1cyc bool bool bool cv1 bev breg bsig Hall) by (intros [] x h h' _ _ _; reflexivity).
  assert (H2 : C2cyc bool bool bool cv1 bev breg bsig noI Hall) by (intros a b x h _ [] _ _).
  assert (Hg : NoGhostR B2 B2 cbot ceq_dec cu 3 cts bev bcev false bs0).
  { apply (unique_or_low_noghost B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed 3 K3 cts
             cts_cover bev bcev bnreg noI false bs0 (fun t => snd (fst t) = true)).
    - split; [reflexivity |]. split.
      + intros [[x y] h] e Hy. cbn [fst snd] in Hy. subst y. destruct e; reflexivity.
      + split; [intros t j _ Ht; exact Ht | intros Hr; discriminate Hr].
    - intros [[x y] h] Hy. cbn [fst snd] in Hy |- *. subst y. left. intros p Hp.
      destruct x; bf; vm_compute in Hp |- *; congruence. }
  assert (Hf : FairFlushR B2 B2 cbot cu cts bev bcev false bs0) by apply c_fairflushR.
  pose proof (proj2 (lens_noreset_fair_iff B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least
                       crank crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono
                       cu_fixed 3 K3 cts cts_cover bool bool bool bool_dec renc rget rset
                       (rget_rset_eq bool) (rget_rset_neq bool) (r_ext bool) rget rset
                       (rget_rset_eq bool) (rget_rset_neq bool) cv1 bev breg bsig noI
                       (fun _ _ _ => I) cv1_lfp Hall (fun _ _ => I) H1 H2 false bs0
                       (fun _ _ _ => I)) (conj Hf Hg)) as [_ [Ha Hc]].
  split; [vm_compute; reflexivity |]. split; [exact Hg |]. split; [exact Hf |].
  split; [exact Ha |]. split; [exact Hc |].
  split.
  - intro H. pose proof (H BClearA ((true, false), (true, true)) ltac:(vm_compute; split; reflexivity)) as X.
    vm_compute in X. destruct X as [X _]. discriminate X.
  - intro H. pose proof (H (false, false) (true, true) eq_refl) as X. vm_compute in X. discriminate X.
Qed.
