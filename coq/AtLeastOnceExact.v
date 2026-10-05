(* AtLeastOnceExact.v: the exact (necessary and sufficient) condition for at-least-once delivery,
   free and causal, at the run level. Axiom-free.

   AtLeastOnce.v proves sufficient conditions only: alo_absorbed (each redelivered event idempotent
   and commuting with the events delivered since its previous copy, at every state of the domain),
   alo_commuting_exactly_once and causal_alo_exactly_once (global commutation and global
   idempotence), and a local divergence witness (non_idempotent_diverges) with no reachability
   qualifier. This file states the exact conditions at a fixed start state s0.

   Setting. A governed step (step e) applies event e and repairs. Ev is the set of events in range.
   Runs start at s0. An at-least-once delivery is a list over Ev that may repeat events; an
   exactly-once delivery has no duplicates. hb is a happens-before relation (irreflexive); the free
   case is the instance hb = empty, where causal delivery is any delivery and causal_alo holds of
   every list.

   Exact results, causal form (section CausalExact).
   - CALOConv s0: every causally consistent at-least-once delivery d (AtLeastOnce.causal_alo) over
     Ev reaches, from s0, the state of every causally consistent exactly-once order o of the same
     events.
   - causal_alo_exact: CALOConv s0 <-> CCRon s0 /\ forall a, AbsorbAt s0 a.
     CCRon s0 is GovernanceConverse.CCR restricted to Ev: a concurrent pair commutes after every
     causally consistent prefix. AbsorbAt s0 a: after every causally consistent exactly-once run w
     from s0 that contains a and no causal successor of a, a redelivery of a is a no-op.
   - causal_alo_exact_idem: CALOConv s0 <-> CCRon s0 /\ forall a, IdemAt s0 a.
     IdemAt s0 a: a is idempotent at every state run u s0 at which it is causally deliverable, i.e.
     step a (step a (run u s0)) = step a (run u s0) whenever u ++ [a] is causally consistent.
     Given CCRon, absorption past the events delivered in between is automatic: the duplicate
     bubbles to its own first copy through concurrent events (idem_absorb).
   - safe_at_exact (per event): SafeAt s0 a (no causally consistent delivery that duplicates only a
     diverges from its exactly-once projection) <-> AbsorbAt s0 a; and under CCRon,
     SafeAt s0 a <-> IdemAt s0 a (safe_at_iff_idem).

   Exact results, free form (section FreeExact), the instance hb = empty.
   - alo_exact: ALOConv s0 <-> CommReach s0 /\ forall a, IdemReach s0 a.
   - alo_exact_absorb: ALOConv s0 <-> CommReach s0 /\ forall a, AbsorbReach s0 a.
   - safe_free_exact, safe_free_iff_idem: the per-event forms. needs_dedup_exact: a needs
     deduplication (~ SafeFree s0 a) iff not every reachable exactly-once run absorbs a's
     duplicate; needs_dedup_witness: one non-absorbing reachable run is a witness. alo_safe: under
     ALOConv no event needs deduplication.
   - alo_idem_reachable: ALOConv s0 forces idempotence at EVERY state reachable from s0 by an
     at-least-once delivery over Ev: the run-level converse of non_idempotent_diverges.

   gsm (Report.NotIdempotent lists the events a with some valid s, step a (step a s) <> step a s).
   - notidem_needs_dedup: a listed event whose witness state is reachable (s = run u s0, u a
     delivery duplicating only a) needs deduplication: ~ SafeFree s0 a. Causal form:
     causal_notidem_needs_dedup.
   - gsm_unlisted_safe: when exactly-once delivery converges from s0 (CommReach s0) and every
     reachable state is valid, an unlisted event is safe without deduplication. Causal form:
     causal_gsm_unlisted_safe. The exact relationship: under CommReach, needing deduplication is
     non-idempotence at a reachable state where a was just delivered (safe_free_iff_idem);
     NotIdempotent over-approximates it by quantifying over valid rather than reachable states.

   Old sufficient conditions recovered: old_free_implies / alo_commuting_recovered and
   old_causal_implies / causal_alo_recovered; ccr_on_true_iff links CCRon to GovernanceConverse.CCR.

   Counterexamples and non-vacuity.
   - inc_alo_fails: the capped increment satisfies CommReach but not IdemReach, so ALOConv fails
     and the event needs deduplication (the idempotence clause is needed).
   - fw_alo_fails: a first-writer-wins register: every event is idempotent at every state and every
     duplicate is absorbed at every reachable run (IdemReach and AbsorbReach hold), yet ALOConv
     fails, because exactly-once delivery already diverges (the commutation clause is needed).
   - flag_idem_needs_dedup: Add and Remove are idempotent at every state (IdemReach holds, gsm
     lists neither) yet Add needs deduplication under free delivery and ALOConv fails: a duplicate
     is not absorbed past the intervening Remove. Idempotence alone is not enough.
     So "unlisted implies safe" needs CommReach, and NotIdempotent is not necessary for needing
     deduplication.
   - jmp_unreachable: an event that is not idempotent at an unreachable state (so gsm, checking every
     state, lists it, and non_idempotent_diverges fires there) yet every at-least-once delivery from
     0 converges: global idempotence, the hypothesis of the old theorems, is not necessary, and
     NotIdempotent is not sufficient without reachability.
   - causal_absorb_qualifier: under causal delivery, absorption at every causal run containing a is
     not necessary: Add is not absorbed after [Add; Remove], yet every causally consistent
     at-least-once delivery converges (that redelivery is not causally consistent).
   - mx_alo_exact (all orders, max-register), fl_causal_alo_exact (causal flag with max-register),
     n_causal_alo_exact (CCR without global concurrent commutation, out of reach of
     causal_alo_exactly_once). *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.CausalReplay NC.AtLeastOnce.
Require NC.GovernanceConverse.
Import ListNotations.

(* ----- list facts ----- *)

Lemma prec_after_contra : forall {E : Type} (l : list E) a r b,
  NoDup (l ++ a :: r) -> In b r -> prec b a (l ++ a :: r) -> False.
Proof.
  induction l as [| x l IH]; intros a r b Hnd Hb H; simpl in *.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha _].
    destruct H as [[-> _] | H]; [exact (Ha Hb) | exact (Ha (prec_in_r _ _ _ H))].
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hx Hnd].
    destruct H as [[-> _] | H].
    + apply Hx. apply in_or_app. right. right. exact Hb.
    + exact (IH a r b Hnd Hb H).
Qed.

Lemma tequiv_app_l : forall {E : Type} (I : E -> E -> Prop) l m1 m2,
  tequiv I m1 m2 -> tequiv I (l ++ m1) (l ++ m2).
Proof.
  intros E I l m1 m2 H. induction l as [| x l IH]; [exact H |].
  simpl. apply tequiv_cons. exact IH.
Qed.

Lemma tequiv_to_back : forall {E : Type} (I : E -> E -> Prop) a r,
  (forall b, In b r -> I a b) -> tequiv I (a :: r) (r ++ [a]).
Proof.
  intros E I a r. induction r as [| b r IH]; intros H; [apply teq_refl |].
  apply teq_trans with (l2 := b :: a :: r).
  - apply (teq_swap I [] a b r). apply H. left. reflexivity.
  - simpl. apply tequiv_cons. apply IH. intros c Hc. apply H. right. exact Hc.
Qed.

Lemma Forall_dedup : forall {E : Type} dec (P : E -> Prop) d,
  Forall P d -> Forall P (dedup dec d).
Proof.
  intros E dec P d H. apply Forall_forall. intros x Hx. apply dedup_In in Hx.
  rewrite Forall_forall in H. exact (H x Hx).
Qed.

Lemma rev_case : forall {E : Type} (l : list E), l = [] \/ exists z r, l = r ++ [z].
Proof.
  intros E l. induction l as [| x l _] using rev_ind; [left; reflexivity |].
  right. exists x, l. reflexivity.
Qed.

(* A causally consistent exactly-once order is a causally consistent at-least-once delivery. *)
Lemma causal_causal_alo : forall {E : Type} (hb : E -> E -> Prop) o,
  causal hb o -> causal_alo hb o.
Proof.
  intros E hb o [Hnd Hc] a b Hab l r Eo Hb Ha.
  apply in_split in Ha. destruct Ha as [r1 [r2 Er]]. subst r o.
  assert (Eo : l ++ r1 ++ a :: r2 = (l ++ r1) ++ a :: r2) by (rewrite <- app_assoc; reflexivity).
  rewrite Eo in Hnd, Hc.
  apply (prec_before_contra (l ++ r1) a r2 b Hnd); [apply in_or_app; left; exact Hb |].
  apply Hc; [exact Hab | apply in_or_app; right; left; reflexivity |
              apply in_or_app; left; apply in_or_app; left; exact Hb].
Qed.

(* Redelivering a at the end of a causal run with no causal successor of a is causally
   consistent. *)
Lemma causal_snoc_alo : forall {E : Type} (hb : E -> E -> Prop) w a,
  causal hb w -> (forall b, In b w -> ~ hb a b) -> causal_alo hb (w ++ [a]).
Proof.
  intros E hb w a Hw Hns x y Hxy l r Ed Hy Hx.
  destruct (rev_case r) as [-> | [z [r' ->]]]; [destruct Hx |].
  rewrite app_assoc in Ed. apply app_inj_tail in Ed. destruct Ed as [-> ->].
  apply in_app_or in Hx. destruct Hx as [Hx | [-> | []]].
  - exact (causal_causal_alo hb _ Hw x y Hxy l r' eq_refl Hy Hx).
  - exact (Hns y (in_or_app _ _ _ (or_introl Hy)) Hxy).
Qed.

(* ============================================================================================ *)
(* The causal form.                                                                              *)
(* ============================================================================================ *)

Section CausalExact.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.       (* governed step: apply, then repair *)
  Variable Ev : E -> Prop.           (* events in range *)
  Variable hb : E -> E -> Prop.      (* happens-before *)
  Hypothesis hb_irrefl : forall x, ~ hb x x.

  Local Notation run := (runT step).

  Lemma run1 : forall x t, run [x] t = step x t.
  Proof. reflexivity. Qed.

  (* Causal at-least-once convergence from s0. *)
  Definition CALOConv (s0 : S) : Prop :=
    forall d o, Forall Ev d -> causal_alo hb d -> causal hb o -> (forall x, In x o <-> In x d) ->
      run d s0 = run o s0.

  (* GovernanceConverse.CCR restricted to the events in range. *)
  Definition CCRon (s0 : S) : Prop :=
    forall p a b, Forall Ev (p ++ [a; b]) -> concurrent hb a b -> causal hb (p ++ [a; b]) ->
      step b (step a (run p s0)) = step a (step b (run p s0)).

  (* A redelivery of a is absorbed at every causal exactly-once run that contains a and no causal
     successor of a (exactly the runs after which a causally consistent redelivery can land). *)
  Definition AbsorbAt (s0 : S) (a : E) : Prop :=
    forall w, Forall Ev w -> causal hb w -> In a w -> (forall b, In b w -> ~ hb a b) ->
      step a (run w s0) = run w s0.

  (* a is idempotent at every reachable state at which it is causally deliverable. *)
  Definition IdemAt (s0 : S) (a : E) : Prop :=
    forall u, Forall Ev (u ++ [a]) -> causal hb (u ++ [a]) ->
      step a (step a (run u s0)) = step a (run u s0).

  (* Every repeated delivery in d is of an event satisfying P. *)
  Definition DupOnly (P : E -> Prop) (d : list E) : Prop :=
    forall l x r, d = l ++ x :: r -> In x l -> P x.

  (* a needs no deduplication: a causal delivery whose only duplicates are copies of a reaches
     the state of its exactly-once projection. *)
  Definition SafeAt (s0 : S) (a : E) : Prop :=
    forall d, Forall Ev d -> causal_alo hb d -> DupOnly (eq a) d -> run d s0 = run (dedup dec d) s0.

  Lemma dupOnly_prefix : forall P p x, DupOnly P (p ++ [x]) -> DupOnly P p.
  Proof.
    intros P p x H l y r Ep Hy. apply (H l y (r ++ [x])); [| exact Hy].
    subst p. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma dupOnly_nodup_snoc : forall w a, NoDup w -> DupOnly (eq a) (w ++ [a]).
  Proof.
    intros w a Hnd l x r Ed Hx.
    destruct (rev_case r) as [-> | [z [r' ->]]].
    - apply app_inj_tail in Ed. destruct Ed as [_ ->]. reflexivity.
    - exfalso. rewrite app_comm_cons, app_assoc in Ed. apply app_inj_tail in Ed.
      destruct Ed as [Ew _]. subst w. apply (NoDup_remove_2 l r' x Hnd).
      apply in_or_app. left. exact Hx.
  Qed.

  (* Absorption at the duplicated events removes the duplicates. *)
  Lemma absorb_dedup : forall s0 (P : E -> Prop), (forall a, P a -> AbsorbAt s0 a) ->
    forall d, Forall Ev d -> causal_alo hb d -> DupOnly P d -> run d s0 = run (dedup dec d) s0.
  Proof.
    intros s0 P HA d. induction d as [| x p IH] using rev_ind; intros Hev Hca Hdo; [reflexivity |].
    apply Forall_app in Hev. destruct Hev as [Hp Hx]. inversion Hx as [| ? ? Hx' _]; subst.
    pose proof (causal_alo_prefix hb p x Hca) as Hcp.
    rewrite dedup_snoc, runT_app, run1, (IH Hp Hcp (dupOnly_prefix P p x Hdo)).
    destruct (in_dec dec x (dedup dec p)) as [Hin | Hin].
    - apply HA.
      + apply (Hdo p x []); [reflexivity | apply (dedup_In dec p x); exact Hin].
      + apply Forall_dedup. exact Hp.
      + exact (causal_alo_dedup_causal dec hb p hb_irrefl Hcp).
      + exact Hin.
      + intros b Hb Hxb. apply dedup_In in Hb.
        exact (Hca x b Hxb p [x] eq_refl Hb (or_introl eq_refl)).
    - rewrite runT_app. reflexivity.
  Qed.

  (* Exactly-once convergence from CCRon, by induction on trace equivalence. *)
  Lemma ccr_on_tequiv : forall s0, CCRon s0 ->
    forall o1 o2, tequiv (concurrent hb) o1 o2 -> causal hb o1 -> Forall Ev o1 ->
      run o1 s0 = run o2 s0.
  Proof.
    intros s0 HC o1 o2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2];
      intros Hc Hev.
    - reflexivity.
    - rewrite !runT_app, !runT_cons. rewrite (HC l a b); [reflexivity | | exact Hab |].
      + replace (l ++ a :: b :: r) with ((l ++ [a; b]) ++ r) in Hev
          by (rewrite <- app_assoc; reflexivity).
        apply Forall_app in Hev. exact (proj1 Hev).
      + apply (NC.GovernanceConverse.causal_prefix hb _ r). rewrite <- app_assoc. exact Hc.
    - symmetry. apply IH.
      + apply (proj2 (NC.GovernanceConverse.tequiv_causal hb l1 l2 H)). exact Hc.
      + apply (Permutation_Forall (Permutation_sym (tequiv_perm _ _ _ H))). exact Hev.
    - rewrite (IH1 Hc Hev). apply IH2.
      + apply (proj1 (NC.GovernanceConverse.tequiv_causal hb l1 l2 H1)). exact Hc.
      + apply (Permutation_Forall (tequiv_perm _ _ _ H1)). exact Hev.
  Qed.

  Lemma ccr_on_conv : forall s0, CCRon s0 ->
    forall o1 o2, causal hb o1 -> causal hb o2 -> Permutation o1 o2 -> Forall Ev o1 ->
      run o1 s0 = run o2 s0.
  Proof.
    intros s0 HC o1 o2 H1 H2 HP Hev. apply (ccr_on_tequiv s0 HC); [| exact H1 | exact Hev].
    apply causal_tequiv; assumption.
  Qed.

  (* Absorption gives idempotence at causal delivery points (no commutation needed). *)
  Lemma absorb_idem : forall s0 a, AbsorbAt s0 a -> IdemAt s0 a.
  Proof.
    intros s0 a HA u Hev Hc.
    pose proof (HA (u ++ [a]) Hev Hc (in_or_app u [a] a (or_intror (or_introl eq_refl)))) as H.
    rewrite runT_app, run1 in H. apply H.
    intros b Hb Hab. apply in_app_or in Hb. destruct Hb as [Hb | [<- | []]]; [| exact (hb_irrefl a Hab)].
    destruct Hc as [Hnd Hcc].
    apply (prec_before_contra u a [] b Hnd Hb).
    apply Hcc; [exact Hab | apply in_or_app; right; left; reflexivity | apply in_or_app; left; exact Hb].
  Qed.

  (* Under CCRon, idempotence at causal delivery points gives absorption: the redelivered event
     bubbles back to its first copy through events concurrent with it. *)
  Lemma idem_absorb : forall s0 a, CCRon s0 -> IdemAt s0 a -> AbsorbAt s0 a.
  Proof.
    intros s0 a HC HI w Hev Hc Ha Hns.
    apply in_split in Ha. destruct Ha as [l [r ->]].
    assert (Hconc : forall b, In b r -> concurrent hb a b).
    { intros b Hb. destruct Hc as [Hnd Hcc]. split; [| split].
      - intros ->. apply (NoDup_remove_2 l r b Hnd). apply in_or_app. right. exact Hb.
      - apply Hns. apply in_or_app. right. right. exact Hb.
      - intro Hba. apply (prec_after_contra l a r b Hnd Hb).
        apply Hcc; [exact Hba | apply in_or_app; right; right; exact Hb
                   | apply in_or_app; right; left; reflexivity]. }
    assert (Ht : tequiv (concurrent hb) (l ++ a :: r) ((l ++ r) ++ [a])).
    { rewrite <- app_assoc. apply tequiv_app_l. apply tequiv_to_back. exact Hconc. }
    assert (Hc' : causal hb ((l ++ r) ++ [a]))
      by exact (proj1 (NC.GovernanceConverse.tequiv_causal hb _ _ Ht) Hc).
    assert (Hev' : Forall Ev ((l ++ r) ++ [a]))
      by exact (Permutation_Forall (tequiv_perm _ _ _ Ht) Hev).
    rewrite (ccr_on_tequiv s0 HC _ _ Ht Hc Hev), runT_app, run1.
    exact (HI (l ++ r) Hev' Hc').
  Qed.

  (* ----- the per-event exact condition ----- *)

  Theorem safe_at_exact : forall s0 a, SafeAt s0 a <-> AbsorbAt s0 a.
  Proof.
    intros s0 a. split.
    - intros HS w Hev Hc Ha Hns.
      assert (Hd : dedup dec (w ++ [a]) = w).
      { rewrite dedup_snoc, (dedup_nodup_id dec w (proj1 Hc)).
        destruct (in_dec dec a w) as [_ | Hn]; [reflexivity | contradiction]. }
      pose proof (HS (w ++ [a])) as H. rewrite Hd, runT_app, run1 in H. apply H.
      + apply Forall_app. split; [exact Hev |]. constructor; [| constructor].
        rewrite Forall_forall in Hev. exact (Hev a Ha).
      + exact (causal_snoc_alo hb w a Hc Hns).
      + exact (dupOnly_nodup_snoc w a (proj1 Hc)).
    - intros HA d Hev Hca Hdo. apply (absorb_dedup s0 (eq a)); [| exact Hev | exact Hca | exact Hdo].
      intros x <-. exact HA.
  Qed.

  Theorem safe_at_iff_idem : forall s0 a, CCRon s0 -> (SafeAt s0 a <-> IdemAt s0 a).
  Proof.
    intros s0 a HC. rewrite safe_at_exact. split; [apply absorb_idem | apply idem_absorb; exact HC].
  Qed.

  (* ----- the run-level exact condition ----- *)

  Theorem causal_alo_exact : forall s0, CALOConv s0 <-> CCRon s0 /\ forall a, AbsorbAt s0 a.
  Proof.
    intros s0. split.
    - intros H. split.
      + intros p a b Hev Hab Hc.
        assert (Hc' : causal hb (p ++ [b; a]))
          by (apply NC.GovernanceConverse.causal_swap; [apply Hab | exact Hc]).
        assert (HP : Permutation (p ++ [a; b]) (p ++ [b; a]))
          by (apply Permutation_app_head; apply perm_swap).
        pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hev (causal_causal_alo hb _ Hc) Hc'
                      (fun x => conj (Permutation_in x (Permutation_sym HP))
                                     (Permutation_in x HP))) as Eq.
        rewrite !runT_app in Eq. exact Eq.
      + intros a w Hev Hc Ha Hns.
        pose proof (H (w ++ [a]) w) as Eq. rewrite runT_app, run1 in Eq. apply Eq.
        * apply Forall_app. split; [exact Hev |]. constructor; [| constructor].
          rewrite Forall_forall in Hev. exact (Hev a Ha).
        * exact (causal_snoc_alo hb w a Hc Hns).
        * exact Hc.
        * intros x. rewrite in_app_iff. simpl. split; [tauto |].
          intros [Hx | [<- | []]]; assumption.
    - intros [HC HA] d o Hev Hca Ho Heq.
      rewrite (absorb_dedup s0 (fun _ => True) (fun a _ => HA a) d Hev Hca (fun _ _ _ _ _ => I)).
      apply (ccr_on_conv s0 HC).
      + exact (causal_alo_dedup_causal dec hb d hb_irrefl Hca).
      + exact Ho.
      + apply NoDup_Permutation; [apply dedup_NoDup | exact (proj1 Ho) |].
        intros x. rewrite dedup_In, Heq. tauto.
      + apply Forall_dedup. exact Hev.
  Qed.

  Theorem causal_alo_exact_idem : forall s0, CALOConv s0 <-> CCRon s0 /\ forall a, IdemAt s0 a.
  Proof.
    intros s0. rewrite causal_alo_exact. split; intros [HC H]; split; try exact HC; intros a.
    - apply absorb_idem. exact (H a).
    - apply idem_absorb; [exact HC | exact (H a)].
  Qed.

  (* ----- gsm: NotIdempotent ----- *)

  (* gsm's Report.NotIdempotent: the second application changes some valid state. *)
  Definition NotIdempotent (valid : S -> Prop) (a : E) : Prop :=
    exists s, valid s /\ step a (step a s) <> step a s.

  (* A non-idempotence witness at a state reached by a causal delivery that duplicates only a,
     after which a can be delivered twice causally, means a needs deduplication. *)
  Theorem causal_notidem_needs_dedup : forall s0 a u,
    Forall Ev u -> Ev a -> causal_alo hb (u ++ [a; a]) -> DupOnly (eq a) u ->
    step a (step a (run u s0)) <> step a (run u s0) -> ~ SafeAt s0 a.
  Proof.
    intros s0 a u Hev Ha Hca Hdo Hne HS. apply Hne.
    assert (Hca1 : causal_alo hb (u ++ [a])).
    { apply (causal_alo_prefix hb _ a). rewrite <- app_assoc. exact Hca. }
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
    assert (Hev1 : Forall Ev (u ++ [a])) by (apply Forall_app; split; [exact Hev | constructor; [exact Ha | constructor]]).
    assert (Hev2 : Forall Ev ((u ++ [a]) ++ [a])) by (apply Forall_app; split; [exact Hev1 | constructor; [exact Ha | constructor]]).
    assert (Hca2 : causal_alo hb ((u ++ [a]) ++ [a])) by (rewrite <- app_assoc; exact Hca).
    pose proof (HS (u ++ [a]) Hev1 Hca1 Hdo1) as E1.
    pose proof (HS ((u ++ [a]) ++ [a]) Hev2 Hca2 Hdo2) as E2.
    rewrite (dedup_snoc dec (u ++ [a]) a) in E2.
    destruct (in_dec dec a (dedup dec (u ++ [a]))) as [_ | Hn].
    - assert (Eq : run ((u ++ [a]) ++ [a]) s0 = run (u ++ [a]) s0) by (rewrite E2, E1; reflexivity).
      rewrite !runT_app, !run1 in Eq. exact Eq.
    - exfalso. apply Hn. apply dedup_In. apply in_or_app. right. left. reflexivity.
  Qed.

  (* Under CCRon, an event idempotent at every valid state is safe without deduplication when
     every causally reachable state is valid. *)
  Theorem causal_gsm_unlisted_safe : forall (valid : S -> Prop) s0 a, CCRon s0 ->
    (forall u, Forall Ev u -> causal hb u -> valid (run u s0)) ->
    (forall s, valid s -> step a (step a s) = step a s) -> SafeAt s0 a.
  Proof.
    intros valid s0 a HC Hval Hid. apply (proj2 (safe_at_iff_idem s0 a HC)).
    intros u Hev Hc. apply Hid, Hval.
    - apply Forall_app in Hev. exact (proj1 Hev).
    - exact (NC.GovernanceConverse.causal_prefix hb u [a] Hc).
  Qed.
End CausalExact.


Arguments CALOConv {S E} step Ev hb s0.
Arguments CCRon {S E} step Ev hb s0.
Arguments AbsorbAt {S E} step Ev hb s0 a.
Arguments IdemAt {S E} step Ev hb s0 a.
Arguments DupOnly {E} P d.
Arguments SafeAt {S E} dec step Ev hb s0 a.
Arguments NotIdempotent {S E} step valid a.

Lemma Forall_True : forall {E : Type} (l : list E), Forall (fun _ => True) l.
Proof. intros E l. apply Forall_forall. intros; exact I. Qed.

(* CCRon over every event is GovernanceConverse.CCR. *)
Theorem ccr_on_true_iff : forall {S E : Type} (step : E -> S -> S) hb s0,
  CCRon step (fun _ => True) hb s0 <-> NC.GovernanceConverse.CCR step hb s0.
Proof.
  intros S E step hb s0. split.
  - intros H p a b Hab Hc. exact (H p a b (Forall_True _) Hab Hc).
  - intros H p a b _ Hab Hc. exact (H p a b Hab Hc).
Qed.

(* ============================================================================================ *)
(* The free (all-orders) form: the instance hb = empty.                                          *)
(* ============================================================================================ *)

Section FreeExact.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.
  Variable Ev : E -> Prop.

  Local Notation run := (runT step).

  Definition nohb : E -> E -> Prop := fun _ _ => False.

  Lemma nohb_irrefl : forall x, ~ nohb x x.
  Proof. intros x []. Qed.

  Lemma causal_nohb : forall o, causal nohb o <-> NoDup o.
  Proof. intros o. split; [intros [H _]; exact H | intros H; split; [exact H | intros a b []]]. Qed.

  Lemma causal_alo_nohb : forall d, causal_alo nohb d.
  Proof. intros d a b []. Qed.

  Lemma concurrent_nohb : forall a b, concurrent nohb a b <-> a <> b.
  Proof. intros a b. split; [intros [H _]; exact H | intros H; split; [exact H | split; intros []]]. Qed.

  (* Every at-least-once delivery over Ev reaches, from s0, the state of every exactly-once
     delivery of the same events. *)
  Definition ALOConv (s0 : S) : Prop :=
    forall d o, Forall Ev d -> NoDup o -> (forall x, In x o <-> In x d) -> run d s0 = run o s0.

  (* Exactly-once commutation at reachable states. *)
  Definition CommReach (s0 : S) : Prop :=
    forall p a b, Forall Ev (p ++ [a; b]) -> a <> b -> NoDup (p ++ [a; b]) ->
      step b (step a (run p s0)) = step a (step b (run p s0)).

  (* A duplicate of a is absorbed after every exactly-once run that contains a. *)
  Definition AbsorbReach (s0 : S) (a : E) : Prop :=
    forall w, Forall Ev w -> NoDup w -> In a w -> step a (run w s0) = run w s0.

  (* a is idempotent at every reachable state at which it is first delivered. *)
  Definition IdemReach (s0 : S) (a : E) : Prop :=
    forall u, Forall Ev (u ++ [a]) -> NoDup (u ++ [a]) ->
      step a (step a (run u s0)) = step a (run u s0).

  (* a needs no deduplication: a delivery whose only duplicates are copies of a reaches the state
     of its exactly-once projection. *)
  Definition SafeFree (s0 : S) (a : E) : Prop :=
    forall d, Forall Ev d -> DupOnly (eq a) d -> run d s0 = run (dedup dec d) s0.

  Lemma aloconv_iff : forall s0, ALOConv s0 <-> CALOConv step Ev nohb s0.
  Proof.
    intros s0. split.
    - intros H d o Hev _ Ho Heq. exact (H d o Hev (proj1 Ho) Heq).
    - intros H d o Hev Ho Heq. exact (H d o Hev (causal_alo_nohb d) (proj2 (causal_nohb o) Ho) Heq).
  Qed.

  Lemma comm_iff : forall s0, CommReach s0 <-> CCRon step Ev nohb s0.
  Proof.
    intros s0. split.
    - intros H p a b Hev Hab Hc. exact (H p a b Hev (proj1 Hab) (proj1 Hc)).
    - intros H p a b Hev Hab Hnd.
      exact (H p a b Hev (proj2 (concurrent_nohb a b) Hab) (proj2 (causal_nohb _) Hnd)).
  Qed.

  Lemma absorb_iff : forall s0 a, AbsorbReach s0 a <-> AbsorbAt step Ev nohb s0 a.
  Proof.
    intros s0 a. split.
    - intros H w Hev Hc Ha _. exact (H w Hev (proj1 Hc) Ha).
    - intros H w Hev Hnd Ha. exact (H w Hev (proj2 (causal_nohb w) Hnd) Ha (fun _ _ F => F)).
  Qed.

  Lemma idem_iff : forall s0 a, IdemReach s0 a <-> IdemAt step Ev nohb s0 a.
  Proof.
    intros s0 a. split.
    - intros H u Hev Hc. exact (H u Hev (proj1 Hc)).
    - intros H u Hev Hnd. exact (H u Hev (proj2 (causal_nohb _) Hnd)).
  Qed.

  Lemma safe_iff : forall s0 a, SafeFree s0 a <-> SafeAt dec step Ev nohb s0 a.
  Proof.
    intros s0 a. split.
    - intros H d Hev _ Hdo. exact (H d Hev Hdo).
    - intros H d Hev Hdo. exact (H d Hev (causal_alo_nohb d) Hdo).
  Qed.

  (* The exact condition, absorption form. *)
  Theorem alo_exact_absorb : forall s0,
    ALOConv s0 <-> CommReach s0 /\ forall a, AbsorbReach s0 a.
  Proof.
    intros s0. rewrite aloconv_iff, (causal_alo_exact dec step Ev nohb nohb_irrefl s0), comm_iff.
    split; intros [HC H]; split; try exact HC; intros a; apply absorb_iff; exact (H a).
  Qed.

  (* The exact condition, idempotence form. *)
  Theorem alo_exact : forall s0,
    ALOConv s0 <-> CommReach s0 /\ forall a, IdemReach s0 a.
  Proof.
    intros s0. rewrite aloconv_iff, (causal_alo_exact_idem dec step Ev nohb nohb_irrefl s0), comm_iff.
    split; intros [HC H]; split; try exact HC; intros a; apply idem_iff; exact (H a).
  Qed.

  (* Per event: a needs no deduplication iff its duplicate is absorbed at every reachable
     exactly-once run containing it. *)
  Theorem safe_free_exact : forall s0 a, SafeFree s0 a <-> AbsorbReach s0 a.
  Proof.
    intros s0 a. rewrite safe_iff, absorb_iff. exact (safe_at_exact dec step Ev nohb nohb_irrefl s0 a).
  Qed.

  (* Per event, when exactly-once delivery converges: a needs no deduplication iff it is
     idempotent at every reachable state at which it is first delivered. *)
  Theorem safe_free_iff_idem : forall s0 a, CommReach s0 -> (SafeFree s0 a <-> IdemReach s0 a).
  Proof.
    intros s0 a HC. rewrite safe_iff, idem_iff. apply (safe_at_iff_idem dec step Ev nohb nohb_irrefl).
    apply comm_iff. exact HC.
  Qed.

  (* a needs deduplication iff some reachable exactly-once run containing a does not absorb its
     duplicate; a concrete non-absorbing run is a witness. *)
  Theorem needs_dedup_exact : forall s0 a, ~ SafeFree s0 a <-> ~ AbsorbReach s0 a.
  Proof. intros s0 a. rewrite safe_free_exact. reflexivity. Qed.

  Theorem needs_dedup_witness : forall s0 a w, Forall Ev w -> NoDup w -> In a w ->
    step a (run w s0) <> run w s0 -> ~ SafeFree s0 a.
  Proof.
    intros s0 a w Hev Hnd Ha Hne HS. apply Hne.
    exact (proj1 (safe_free_exact s0 a) HS w Hev Hnd Ha).
  Qed.

  Theorem alo_safe : forall s0, ALOConv s0 -> forall a, SafeFree s0 a.
  Proof.
    intros s0 H a. apply safe_free_exact. exact (proj2 (proj1 (alo_exact_absorb s0) H) a).
  Qed.

  Lemma run2 : forall x y t, run [x; y] t = step y (step x t).
  Proof. reflexivity. Qed.

  (* The run-level converse of non_idempotent_diverges: at-least-once convergence forces
     idempotence at every state reachable by an at-least-once delivery over Ev. *)
  Theorem alo_idem_reachable : forall s0, ALOConv s0 ->
    forall u a, Forall Ev u -> Ev a -> step a (step a (run u s0)) = step a (run u s0).
  Proof.
    intros s0 H u a Hu Ha.
    assert (Hev1 : Forall Ev (u ++ [a])) by (apply Forall_app; split; [exact Hu | constructor; [exact Ha | constructor]]).
    assert (Hev2 : Forall Ev (u ++ [a; a])) by (apply Forall_app; split; [exact Hu | constructor; [exact Ha | exact (Forall_cons _ Ha (Forall_nil _))]]).
    pose proof (H (u ++ [a]) (dedup dec (u ++ [a])) Hev1 (dedup_NoDup dec _) (dedup_In dec _)) as E1.
    pose proof (H (u ++ [a; a]) (dedup dec (u ++ [a])) Hev2 (dedup_NoDup dec _)) as E2.
    assert (Eq : run (u ++ [a; a]) s0 = run (u ++ [a]) s0).
    { rewrite E1. apply E2. intros x. rewrite dedup_In, !in_app_iff. simpl. tauto. }
    rewrite !runT_app, run2, run1 in Eq. exact Eq.
  Qed.

  (* gsm: a NotIdempotent witness at a reachable state (reached by a delivery duplicating only a)
     means a needs deduplication. *)
  Theorem notidem_needs_dedup : forall s0 a u,
    Forall Ev u -> Ev a -> DupOnly (eq a) u ->
    step a (step a (run u s0)) <> step a (run u s0) -> ~ SafeFree s0 a.
  Proof.
    intros s0 a u Hu Ha Hdo Hne HS. apply safe_iff in HS.
    exact (causal_notidem_needs_dedup dec step Ev nohb s0 a u Hu Ha
             (causal_alo_nohb _) Hdo Hne HS).
  Qed.

  (* gsm: when exactly-once delivery converges from s0 and every reachable state is valid, an
     event that Report.NotIdempotent does not list (idempotent at every valid state) is safe
     without deduplication. *)
  Theorem gsm_unlisted_safe : forall (valid : S -> Prop) s0 a, CommReach s0 ->
    (forall u, Forall Ev u -> valid (run u s0)) ->
    (forall s, valid s -> step a (step a s) = step a s) -> SafeFree s0 a.
  Proof.
    intros valid s0 a HC Hval Hid. apply (proj2 (safe_free_iff_idem s0 a HC)).
    intros u Hev _. apply Hid, Hval. apply Forall_app in Hev. exact (proj1 Hev).
  Qed.
End FreeExact.

Arguments ALOConv {S E} step Ev s0.
Arguments CommReach {S E} step Ev s0.
Arguments AbsorbReach {S E} step Ev s0 a.
Arguments IdemReach {S E} step Ev s0 a.
Arguments SafeFree {S E} dec step Ev s0 a.

(* ============================================================================================ *)
(* The old sufficient conditions imply the exact ones.                                           *)
(* ============================================================================================ *)

Section Recovered.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.
  Variable Ev : E -> Prop.
  Variable D : S -> Prop.
  Hypothesis step_D : forall e s, D s -> D (step e s).

  (* All in-range events commute and are idempotent on D (alo_commuting_exactly_once). *)
  Theorem old_free_implies : forall s0, D s0 ->
    (forall a b, Ev a -> Ev b -> comm step D a b) -> (forall a, Ev a -> idem step D a) ->
    CommReach step Ev s0 /\ forall a, IdemReach step Ev s0 a.
  Proof.
    intros s0 Hs0 Hc Hi. split.
    - intros p a b Hev _ _. apply Forall_app in Hev. destruct Hev as [_ Hab].
      inversion Hab as [| ? ? Ha Hb']; subst. inversion Hb' as [| ? ? Hb _]; subst.
      symmetry. exact (Hc a b Ha Hb _ (runT_Dall step D step_D p s0 Hs0)).
    - intros a u Hev _. apply Forall_app in Hev. destruct Hev as [_ Ha].
      inversion Ha; subst. exact (Hi a ltac:(assumption) _ (runT_Dall step D step_D u s0 Hs0)).
  Qed.

  Theorem alo_commuting_recovered : forall s0, D s0 ->
    (forall a b, Ev a -> Ev b -> comm step D a b) -> (forall a, Ev a -> idem step D a) ->
    ALOConv step Ev s0.
  Proof.
    intros s0 Hs0 Hc Hi. apply (proj2 (alo_exact dec step Ev s0)).
    exact (old_free_implies s0 Hs0 Hc Hi).
  Qed.

  Variable hb : E -> E -> Prop.

  (* Concurrent pairs commute and in-range events are idempotent on D (causal_alo_exactly_once). *)
  Theorem old_causal_implies : forall s0, D s0 ->
    cc_concurrent step D hb -> (forall a, Ev a -> idem step D a) ->
    CCRon step Ev hb s0 /\ forall a, IdemAt step Ev hb s0 a.
  Proof.
    intros s0 Hs0 Hcc Hi. split.
    - intros p a b _ Hab _. symmetry. exact (Hcc a b Hab _ (runT_Dall step D step_D p s0 Hs0)).
    - intros a u Hev _. apply Forall_app in Hev. destruct Hev as [_ Ha].
      inversion Ha; subst. exact (Hi a ltac:(assumption) _ (runT_Dall step D step_D u s0 Hs0)).
  Qed.

  Theorem causal_alo_recovered : forall s0, (forall x, ~ hb x x) -> D s0 ->
    cc_concurrent step D hb -> (forall a, Ev a -> idem step D a) ->
    CALOConv step Ev hb s0.
  Proof.
    intros s0 Hirr Hs0 Hcc Hi. apply (proj2 (causal_alo_exact_idem dec step Ev hb Hirr s0)).
    exact (old_causal_implies s0 Hs0 Hcc Hi).
  Qed.
End Recovered.

(* ============================================================================================ *)
(* Counterexamples.                                                                              *)
(* ============================================================================================ *)

Definition unit_dec : forall x y : unit, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Lemma unit_nodup_snoc : forall u, NoDup (u ++ [tt]) -> u = [].
Proof.
  intros [| [] u] H; [reflexivity |]. exfalso. simpl in H. apply NoDup_cons_iff in H.
  apply (proj1 H). apply in_or_app. right. left. reflexivity.
Qed.

Lemma unit_comm_reach : forall {S : Type} (step : unit -> S -> S) s0, CommReach step (fun _ => True) s0.
Proof. intros S step s0 p [] [] _ H. exfalso. apply H. reflexivity. Qed.

Lemma nodup1 : forall {E : Type} (x : E), NoDup [x].
Proof. intros E x. constructor; [intros [] | constructor]. Qed.

Lemma dupOnly_nil : forall {E : Type} (P : E -> Prop), DupOnly P [].
Proof. intros E P [| y l] x r Ed; discriminate Ed. Qed.

(* The capped increment (AtLeastOnce.inc_step): exactly-once delivery converges (one event), the
   idempotence clause fails at the reachable state 0, at-least-once delivery diverges, and the
   event needs deduplication. *)
Theorem inc_alo_fails :
  CommReach inc_step (fun _ => True) 0 /\ ~ IdemReach inc_step (fun _ => True) 0 tt /\
  ~ ALOConv inc_step (fun _ => True) 0 /\ ~ SafeFree unit_dec inc_step (fun _ => True) 0 tt.
Proof.
  split; [apply unit_comm_reach |]. split; [| split].
  - intro H. specialize (H [] (Forall_True _) (nodup1 tt)).
    discriminate H.
  - intro H. specialize (H [tt; tt] [tt] (Forall_True _) (nodup1 tt)).
    assert (Eq : runT inc_step [tt; tt] 0 = runT inc_step [tt] 0).
    { apply H. intros [] . simpl. tauto. }
    discriminate Eq.
  - apply (notidem_needs_dedup unit_dec inc_step (fun _ => True) 0 tt []);
      [constructor | exact I | apply dupOnly_nil | discriminate].
Qed.

(* A first-writer-wins register: the first write sets the value, later writes are no-ops. Every
   event is idempotent at every state and every duplicate is absorbed at every reachable run, but
   exactly-once delivery already diverges: the commutation clause is needed. *)
Definition fw_step (b : bool) (n : nat) : nat :=
  match n with 0 => if b then 1 else 2 | S _ => n end.

Lemma fw_fix : forall b n, n <> 0 -> fw_step b n = n.
Proof. intros b [| n] H; [contradiction | reflexivity]. Qed.

Lemma fw_run_fix : forall w n, n <> 0 -> runT fw_step w n = n.
Proof.
  induction w as [| x w IH]; intros n H; [reflexivity |].
  rewrite runT_cons, (fw_fix x n H). exact (IH n H).
Qed.

Lemma fw_nz : forall b n, fw_step b n <> 0.
Proof. intros [] [| n]; discriminate. Qed.

Lemma fw_run_nz : forall w s a, In a w -> runT fw_step w s <> 0.
Proof.
  induction w as [| x w IH]; intros s a Ha; [destruct Ha |]. rewrite runT_cons.
  destruct Ha as [-> | Ha].
  - rewrite (fw_run_fix w _ (fw_nz a s)). apply fw_nz.
  - exact (IH _ a Ha).
Qed.

Theorem fw_alo_fails :
  (forall a s, fw_step a (fw_step a s) = fw_step a s) /\
  (forall a, IdemReach fw_step (fun _ => True) 0 a) /\
  (forall a, AbsorbReach fw_step (fun _ => True) 0 a) /\
  ~ CommReach fw_step (fun _ => True) 0 /\ ~ ALOConv fw_step (fun _ => True) 0.
Proof.
  assert (Hid : forall a s, fw_step a (fw_step a s) = fw_step a s) by (intros [] [| s]; reflexivity).
  split; [exact Hid |]. split; [intros a u _ _; apply Hid |]. split; [| split].
  - intros a w _ _ Ha. apply fw_fix. exact (fw_run_nz w 0 a Ha).
  - intro H. specialize (H [] true false (Forall_True _) ltac:(discriminate)).
    assert (Hnd : NoDup ([] ++ [true; false])).
    { simpl. constructor; [intros [H1 | []]; discriminate H1 | constructor; [intros [] | constructor]]. }
    specialize (H Hnd). discriminate H.
  - intro H. assert (Hnd : NoDup [false; true]).
    { constructor; [intros [H1 | []]; discriminate H1 | constructor; [intros [] | constructor]]. }
    specialize (H [true; false] [false; true] (Forall_True _) Hnd).
    assert (Eq : runT fw_step [true; false] 0 = runT fw_step [false; true] 0).
    { apply H. intros x. simpl. tauto. }
    discriminate Eq.
Qed.

(* Add on a flag is idempotent at every state, so gsm's NotIdempotent does not list it, yet under
   free delivery it needs deduplication: a redelivery after Remove is not absorbed. Without
   exactly-once convergence, "unlisted implies safe" fails, and NotIdempotent is not necessary. *)
Lemma fl_dup_add : DupOnly (eq FAdd) [FAdd; FRemove; FAdd].
Proof.
  intros l x r Ed Hx.
  destruct l as [| y1 [| y2 [| y3 l]]]; simpl in Ed; inversion Ed; subst; simpl in Hx;
    try contradiction.
  - destruct Hx as [Hx | []]. discriminate Hx.
  - reflexivity.
  - destruct l; discriminate.
Qed.

Theorem flag_idem_needs_dedup :
  (forall e s, fl_step e (fl_step e s) = fl_step e s) /\
  (forall a, IdemReach fl_step (fun _ => True) (false, 0) a) /\
  ~ NotIdempotent fl_step (fun _ => True) FAdd /\
  ~ SafeFree fev_dec fl_step (fun _ => True) (false, 0) FAdd /\
  ~ ALOConv fl_step (fun _ => True) (false, 0).
Proof.
  assert (Hns : ~ SafeFree fev_dec fl_step (fun _ => True) (false, 0) FAdd).
  { intro H. specialize (H [FAdd; FRemove; FAdd] (Forall_True _) fl_dup_add).
    vm_compute in H. discriminate H. }
  split; [intros e s; exact (fl_idem e s I) |].
  split; [intros a u _ _; exact (fl_idem a _ I) |]. split; [| split; [exact Hns |]].
  - intros [s [_ H]]. exact (H (fl_idem FAdd s I)).
  - intro H. exact (Hns (alo_safe fev_dec fl_step (fun _ => True) (false, 0) H FAdd)).
Qed.

(* An event that is not idempotent at the unreachable state 2: gsm, checking every state, lists
   it, and non_idempotent_diverges fires from 2, yet from 0 every at-least-once delivery converges
   and the event needs no deduplication. Global idempotence (the old hypothesis) is not
   necessary, and NotIdempotent is not sufficient without reachability. *)
Definition jmp_step (_ : unit) (n : nat) : nat :=
  match n with 0 | 1 => 1 | _ => S n end.

Theorem jmp_unreachable :
  ~ idem jmp_step (fun _ => True) tt /\ NotIdempotent jmp_step (fun _ => True) tt /\
  runT jmp_step [tt; tt] 2 <> runT jmp_step [tt] 2 /\
  ALOConv jmp_step (fun _ => True) 0 /\ SafeFree unit_dec jmp_step (fun _ => True) 0 tt.
Proof.
  assert (Hidem : forall a, IdemReach jmp_step (fun _ => True) 0 a).
  { intros [] u _ Hnd. rewrite (unit_nodup_snoc u Hnd). reflexivity. }
  split; [intro H; specialize (H 2 I); discriminate H |].
  split; [exists 2; split; [exact I | discriminate] |].
  split; [apply non_idempotent_diverges; discriminate |]. split.
  - apply (proj2 (alo_exact unit_dec jmp_step (fun _ => True) 0)).
    split; [apply unit_comm_reach | exact Hidem].
  - apply (proj2 (safe_free_iff_idem unit_dec jmp_step (fun _ => True) 0 tt (unit_comm_reach _ _))).
    apply Hidem.
Qed.

(* ============================================================================================ *)
(* Non-vacuity.                                                                                  *)
(* ============================================================================================ *)

(* All orders: the clamped max-register. *)
Theorem mx_alo_exact : forall s0,
  ALOConv mx_step (fun _ => True) s0 /\ CommReach mx_step (fun _ => True) s0 /\
  forall a, IdemReach mx_step (fun _ => True) s0 a.
Proof.
  intros s0.
  assert (H := old_free_implies mx_step (fun _ => True) (fun _ => True) (fun _ _ _ => I) s0 I
                 (fun a b _ _ => mx_comm a b) (fun a _ => mx_idem a)).
  split; [| exact H]. apply (proj2 (alo_exact Nat.eq_dec mx_step (fun _ => True) s0)). exact H.
Qed.

Lemma fl_causal_add_remove : causal fl_hb [FAdd; FRemove].
Proof.
  split; [repeat constructor; simpl; intuition discriminate |].
  intros a b [Ea Eb] Ha Hb. subst. simpl. left. split; [reflexivity | left; reflexivity].
Qed.

(* Causal: the flag with Add before Remove, next to a clamped max-register. *)
Theorem fl_causal_alo_exact : forall s0,
  CALOConv fl_step (fun _ => True) fl_hb s0 /\ CCRon fl_step (fun _ => True) fl_hb s0 /\
  forall a, IdemAt fl_step (fun _ => True) fl_hb s0 a.
Proof.
  intros s0.
  assert (H := old_causal_implies fl_step (fun _ => True) (fun _ => True) (fun _ _ _ => I) fl_hb s0 I
                 fl_cc (fun a _ => fl_idem a)).
  split; [| exact H]. apply (proj2 (causal_alo_exact_idem fev_dec fl_step (fun _ => True) fl_hb fl_irrefl s0)).
  exact H.
Qed.

(* Under causal delivery, absorption at every causal run containing a is not necessary: Add is not
   absorbed after [Add; Remove] (a redelivery there is not causally consistent), yet every
   causally consistent at-least-once delivery converges. *)
Theorem causal_absorb_qualifier :
  causal fl_hb [FAdd; FRemove] /\
  fl_step FAdd (runT fl_step [FAdd; FRemove] (false, 0)) <> runT fl_step [FAdd; FRemove] (false, 0) /\
  CALOConv fl_step (fun _ => True) fl_hb (false, 0).
Proof.
  split; [exact fl_causal_add_remove |]. split; [discriminate |].
  exact (proj1 (fl_causal_alo_exact (false, 0))).
Qed.

(* Causal, beyond causal_alo_exactly_once: GovernanceConverse's n_step, whose concurrent events NA
   and NB do not commute at state 1, so cc_concurrent fails; but CCR holds from 0 and every event
   is idempotent, so every causally consistent at-least-once delivery converges from 0. *)
Definition nev_dec : forall x y : NC.GovernanceConverse.nev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Lemma n_irrefl : forall x, ~ NC.GovernanceConverse.n_hb x x.
Proof. intros x [[-> | ->] Ex]; discriminate Ex. Qed.

Theorem n_causal_alo_exact :
  CALOConv NC.GovernanceConverse.n_step (fun _ => True) NC.GovernanceConverse.n_hb 0 /\
  ~ cc_concurrent NC.GovernanceConverse.n_step (fun _ => True) NC.GovernanceConverse.n_hb.
Proof.
  split.
  - apply (proj2 (causal_alo_exact_idem nev_dec NC.GovernanceConverse.n_step (fun _ => True)
                    NC.GovernanceConverse.n_hb n_irrefl 0)).
    split; [apply ccr_on_true_iff; exact NC.GovernanceConverse.n_ccr |].
    intros a u _ _. destruct a; destruct (runT NC.GovernanceConverse.n_step u 0) as [| [| s]]; reflexivity.
  - intro H.
    assert (Hc : concurrent NC.GovernanceConverse.n_hb NC.GovernanceConverse.NA NC.GovernanceConverse.NB).
    { split; [discriminate | split; intros [_ H1]; discriminate H1]. }
    specialize (H _ _ Hc 1 I). discriminate H.
Qed.
