(* ReconfigurationClosure.v: a finite exact form of the barrier's A part when the migration is
   not injective (gap 20 of REGIME-AUDIT.md, residue (c)). Axiom-free.

   Setting: section Det of Reconfiguration.v. Deterministic steps stepA, stepB, an equivalence
   eqvB on B-states respected by stepB, a migration M, a translation tau, free delivery.
   det_barrier_exact says the barrier switch converges from s0 iff (B) every migrated reachable
   state M (runA u s0) is permutation convergent under B, and (AmodM) A converges modulo M:
     forall u u', Permutation u u' -> M (runA u s0) ~ M (runA u' s0).
   det_barrier_faithful replaces AmodM by A's own convergence when M reflects the
   equivalences. Without that, AmodM quantifies over all pairs of permutations; this module gives
   it a local and a finite exact form.

   1. Generic (section Swap): a deterministic system step, an observation obs, an equivalence eqv
      on observations. PermObs s0: every two permutations from s0 have equivalent observations.
      - perm_swap_exact: PermObs s0 <-> SwapObs s0, where SwapObs s0 says that for every word u
        (the reachable state t = run u s0), events a, b and continuation w,
          obs (run w (step b (step a t))) ~ obs (run w (step a (step b t))).
        (=>) u a b w and u b a w are permutations of each other. (<=) induction on Permutation:
        a chain of adjacent transpositions, and eqv is transitive along it.
      - PC s0, the pair closure: the least relation containing the seeds
          (step b (step a t), step a (step b t))  for t = run u s0 and events a, b,
        and closed under applying one event to both components. ClosureOK s0: obs x ~ obs y on
        every pair of PC s0. closure_swap_exact: ClosureOK s0 <-> SwapObs s0;
        closure_perm_exact: PermObs s0 <-> ClosureOK s0.
      - The pruned closure PCg (gsm's search): seeds only for a chosen orientation sel a b of
        each pair of distinct events and only where the two states differ, closed only into
        pairs of different states. gsm_closure_exact: given decidable equality of states and
        sel covering every pair (a = b \/ sel a b \/ sel b a), checking PCg is checking PC.
      - perm_local_exact: when the observation is compatible with the steps (equivalent
        observations stay equivalent after one more event), the continuation drops: PermObs s0
        iff each pair of events commutes, up to eqv, at each reachable state. A migration M is
        not compatible in general, which is why the A part of the barrier needs the closure.
      - Finite instances (section SwapFinite: finite lists of states and events, decidable
        equality of states, decidable eqv on observations): run_star_iff and pc_star_iff
        characterize reachability and PC by the closure computation star_fin_dec of
        Reconfiguration.v; closure_dec, perm_obs_dec decide; closure_witness_exact:
          ~ PermObs s0 <-> exists x y, PC s0 x y /\ ~ obs x ~ obs y,
        so a search that enumerates PC finds a witness iff there is one: an exhausted search is
        a certificate.

   2. The barrier, exactly (section DetClosure, the Det setting).
      - amodm_swap_exact: AmodM s0 <-> forall u a b w,
          M (runA w (stepA b (stepA a (runA u s0)))) ~ M (runA w (stepA a (stepA b (runA u s0)))).
      - amodm_closure_exact: AmodM s0 <-> ClosureOK stepA M eqvB s0.
      - permB_local_exact: PermB x <-> every pair of B-events commutes (up to eqvB) at every
        state B reaches from x (stepB_ext removes the continuation); permA_eq_local_exact: the
        same for A with equality (the PermA gsm checks).
      - det_barrier_closure_exact: DBar s0 <-> (forall u, PermB (M (runA u s0))) /\ ClosureOK.
      - det_barrier_local_exact and det_live_local_exact: both outcomes as local conditions on
        reachable states plus the pair closure, the conditions gsm's CheckMigration checks.
      - det_barrier_faithful_closure: when M reflects and preserves the equivalences, ClosureOK
        is A's own convergence, and det_barrier_closure_faithful recovers det_barrier_faithful
        from det_barrier_closure_exact; det_closure_of_permA: when M preserves them, A's
        convergence implies ClosureOK (the sufficient direction).

   3. Complete classification (section DetFinite). DClassified s0 o for o in Online,
      BarrierOnly, Unsafe (DLive; DBar and not DLive; not DBar). det_classified_unique: at
      most one. On finite instances (finite state and event lists on both sides, decidable state
      equality, decidable eqvB): det_live_dec, det_barrier_dec, and det_classify_complete returns
      the outcome, with no faithfulness hypothesis and no unknown case. amodm_witness_exact: A
      fails to converge modulo M iff the pair closure has a pair that M separates;
      det_unsafe_exact: the barrier diverges iff B diverges after a barrier switch at some
      reachable state or the pair closure has a pair M separates.

   4. Instances. A is last-writer-wins on option bool (None the start, Some b the last write),
      which diverges (lww_diverges); each migration below is not injective on the states A
      reaches (merge_not_injective, partial_not_injective): the case gsm reported Unknown.
      - merged_online: mergeM sends both writes to true, B sets a flag and every A-event becomes
        the flag event: Online.
      - merged_barrier: mergeM again, B ignores the translated events: an in-flight write is
        lost (DS1 fails), the barrier converges: BarrierOnly, certified by the closure
        (merged_barrier_closure), with A diverging and M not injective.
      - partial_merge: partialM sends None and Some true to true, Some false to false. The seed at
        the start with events true, false is a pair it separates (partial_merge_witness): Unsafe.
      - closure_nonvacuous: the closure condition holds for mergeM and fails for partialM;
        gsm_search_instances: the same for the pruned closure, with sel_tf covering every pair.
      - merged_classified, merged_classified_outcomes: det_classify_complete runs on the three
        instances (its finite hypotheses all hold) and returns Online, BarrierOnly, Unsafe. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.GovernanceConverse NC.Trace NC.Reconfiguration.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Generic: permutations, adjacent swaps and the pair closure.                               *)
(* ============================================================================================ *)

Section Swap.
  Context {S E O : Type}.
  Variable step : E -> S -> S.
  Variable obs : S -> O.
  Variable eqv : O -> O -> Prop.
  Hypothesis eqv_refl : forall x, eqv x x.
  Hypothesis eqv_sym : forall x y, eqv x y -> eqv y x.
  Hypothesis eqv_trans : forall x y z, eqv x y -> eqv y z -> eqv x z.

  Local Notation run := (runT step).

  Definition PermObs (s0 : S) : Prop :=
    forall u u', Permutation u u' -> eqv (obs (run u s0)) (obs (run u' s0)).

  Definition SwapObs (s0 : S) : Prop :=
    forall u a b w,
      eqv (obs (run w (step b (step a (run u s0))))) (obs (run w (step a (step b (run u s0))))).

  Lemma run_swap : forall p a b w s, run (p ++ a :: b :: w) s = run w (step b (step a (run p s))).
  Proof. intros p a b w s. rewrite runT_app. reflexivity. Qed.

  Theorem perm_swap_exact : forall s0, PermObs s0 <-> SwapObs s0.
  Proof.
    intros s0. split.
    - intros H u a b w. rewrite <- !run_swap. apply H.
      apply Permutation_app_head. apply perm_swap.
    - intros H.
      assert (K : forall l l', Permutation l l' ->
                forall p, eqv (obs (run (p ++ l) s0)) (obs (run (p ++ l') s0))).
      { intros l l' P. induction P as [| x l l' P IH | x y l | l l' l'' P1 IH1 P2 IH2]; intros p.
        - apply eqv_refl.
        - replace (p ++ x :: l) with ((p ++ [x]) ++ l) by (rewrite <- app_assoc; reflexivity).
          replace (p ++ x :: l') with ((p ++ [x]) ++ l') by (rewrite <- app_assoc; reflexivity).
          apply IH.
        - rewrite !run_swap. apply H.
        - exact (eqv_trans _ _ _ (IH1 p) (IH2 p)). }
      intros u u' P. exact (K u u' P []).
  Qed.

  (* The pair closure: the seeds, two adjacent events in both orders at a reachable state, closed
     under applying the same event to both components. *)
  Inductive PC (s0 : S) : S -> S -> Prop :=
  | pc_seed : forall u a b, PC s0 (step b (step a (run u s0))) (step a (step b (run u s0)))
  | pc_step : forall e x y, PC s0 x y -> PC s0 (step e x) (step e y).

  Definition ClosureOK (s0 : S) : Prop := forall x y, PC s0 x y -> eqv (obs x) (obs y).

  Lemma pc_run : forall s0 w x y, PC s0 x y -> PC s0 (run w x) (run w y).
  Proof.
    intros s0 w. induction w as [| e w IH]; intros x y H; [exact H |].
    rewrite !runT_cons. apply IH. apply pc_step. exact H.
  Qed.

  Theorem pc_iff : forall s0 x y, PC s0 x y <->
    exists u a b w, x = run w (step b (step a (run u s0))) /\ y = run w (step a (step b (run u s0))).
  Proof.
    intros s0 x y. split.
    - intros H. induction H as [u a b | e x y _ [u [a [b [w [-> ->]]]]]].
      + exists u, a, b, []. split; reflexivity.
      + exists u, a, b, (w ++ [e]). rewrite !runT_app. split; reflexivity.
    - intros [u [a [b [w [-> ->]]]]]. apply pc_run. apply pc_seed.
  Qed.

  Theorem closure_swap_exact : forall s0, ClosureOK s0 <-> SwapObs s0.
  Proof.
    intros s0. split.
    - intros H u a b w. apply H. apply (proj2 (pc_iff s0 _ _)). exists u, a, b, w. split; reflexivity.
    - intros H x y P. apply pc_iff in P. destruct P as [u [a [b [w [-> ->]]]]]. apply H.
  Qed.

  Theorem closure_perm_exact : forall s0, PermObs s0 <-> ClosureOK s0.
  Proof. intros s0. rewrite perm_swap_exact. rewrite closure_swap_exact. tauto. Qed.

  (* A pair the closure reaches whose observations differ refutes PermObs, with no finiteness. *)
  Theorem closure_witness_refutes : forall s0 x y, PC s0 x y -> ~ eqv (obs x) (obs y) -> ~ PermObs s0.
  Proof.
    intros s0 x y P N H. apply N. apply (proj1 (closure_perm_exact s0) H). exact P.
  Qed.

  (* When the observation is compatible with the steps (equivalent observations stay equivalent
     after one more event), the continuation drops: PermObs is local at the reachable states.
     The migration M of the barrier is not compatible in general, which is why its A part needs
     the closure. *)
  Theorem perm_local_exact :
    (forall e x y, eqv (obs x) (obs y) -> eqv (obs (step e x)) (obs (step e y))) ->
    forall s0, PermObs s0 <->
      forall u a b, eqv (obs (step b (step a (run u s0)))) (obs (step a (step b (run u s0)))).
  Proof.
    intros Hc s0. rewrite perm_swap_exact. split.
    - intros H u a b. exact (H u a b []).
    - intros H u a b w. specialize (H u a b).
      assert (K : forall l x y, eqv (obs x) (obs y) -> eqv (obs (run l x)) (obs (run l y))).
      { intros l. induction l as [| e l IH]; intros x y Hxy; [exact Hxy |].
        rewrite !runT_cons. apply IH. apply Hc. exact Hxy. }
      apply K. exact H.
  Qed.

  (* gsm's search: one orientation per pair of events, seeds only where the two states differ,
     and pairs of equal states not expanded. *)
  Section Pruned.
    Variable eqS : forall a b : S, {a = b} + {a <> b}.
    Variable sel : E -> E -> Prop.
    Hypothesis sel_cover : forall a b, a = b \/ sel a b \/ sel b a.

    Inductive PCg (s0 : S) : S -> S -> Prop :=
    | pcg_seed : forall u a b, sel a b ->
        step b (step a (run u s0)) <> step a (step b (run u s0)) ->
        PCg s0 (step b (step a (run u s0))) (step a (step b (run u s0)))
    | pcg_step : forall e x y, PCg s0 x y -> step e x <> step e y -> PCg s0 (step e x) (step e y).

    Definition ClosureG (s0 : S) : Prop := forall x y, PCg s0 x y -> eqv (obs x) (obs y).

    Lemma pcg_pc : forall s0 x y, PCg s0 x y -> PC s0 x y.
    Proof.
      intros s0 x y H. induction H as [u a b _ _ | e x y _ IH _].
      - apply pc_seed.
      - apply pc_step. exact IH.
    Qed.

    Lemma pc_pcg : forall s0 x y, PC s0 x y -> x = y \/ PCg s0 x y \/ PCg s0 y x.
    Proof.
      intros s0 x y H. induction H as [u a b | e x y _ IH].
      - destruct (eqS (step b (step a (run u s0))) (step a (step b (run u s0)))) as [Eq | Ne];
          [left; exact Eq |].
        destruct (sel_cover a b) as [-> | [Hs | Hs]].
        + left. reflexivity.
        + right. left. apply pcg_seed; assumption.
        + right. right. apply pcg_seed; [exact Hs |]. intro Eq. apply Ne. symmetry. exact Eq.
      - destruct (eqS (step e x) (step e y)) as [Eq | Ne]; [left; exact Eq |].
        destruct IH as [-> | [IH | IH]].
        + left. reflexivity.
        + right. left. apply pcg_step; assumption.
        + right. right. apply pcg_step; [exact IH |]. intro Eq. apply Ne. symmetry. exact Eq.
    Qed.

    Theorem gsm_closure_exact : forall s0, ClosureG s0 <-> ClosureOK s0.
    Proof.
      intros s0. split.
      - intros H x y P. destruct (pc_pcg s0 x y P) as [-> | [G | G]].
        + apply eqv_refl.
        + apply H. exact G.
        + apply eqv_sym. apply H. exact G.
      - intros H x y G. apply H. apply pcg_pc. exact G.
    Qed.

    Theorem gsm_closure_perm_exact : forall s0, PermObs s0 <-> ClosureG s0.
    Proof. intros s0. rewrite gsm_closure_exact. apply closure_perm_exact. Qed.
  End Pruned.
End Swap.

(* Finite search lemmas. *)
Lemma dec_exists_fin : forall {X : Type} (l : list X), (forall x, In x l) ->
  forall P : X -> Prop, (forall x, {P x} + {~ P x}) -> {exists x, P x} + {~ exists x, P x}.
Proof.
  intros X l Hl P Hd.
  destruct (list_forall_or_witness (fun x => ~ P x) l (fun x => dec_not (P x) (Hd x)))
    as [H | [x [_ Hn]]].
  - right. intros [x Hx]. exact (H x (Hl x) Hx).
  - left. exists x. destruct (Hd x) as [Hx | Hx]; [exact Hx | contradiction].
Qed.

Lemma prod_full : forall {X Y : Type} (lx : list X) (ly : list Y),
  (forall x, In x lx) -> (forall y, In y ly) -> forall p : X * Y, In p (list_prod lx ly).
Proof. intros X Y lx ly Hx Hy [x y]. apply in_prod; [apply Hx | apply Hy]. Qed.

Definition prod_eq_dec {X Y : Type} (eqX : forall a b : X, {a = b} + {a <> b})
  (eqY : forall a b : Y, {a = b} + {a <> b}) : forall a b : X * Y, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Section SwapFinite.
  Context {S E O : Type}.
  Variable step : E -> S -> S.
  Variable obs : S -> O.
  Variable eqv : O -> O -> Prop.
  Hypothesis eqv_refl : forall x, eqv x x.
  Hypothesis eqv_sym : forall x y, eqv x y -> eqv y x.
  Hypothesis eqv_trans : forall x y z, eqv x y -> eqv y z -> eqv x z.
  Variable eqS : forall a b : S, {a = b} + {a <> b}.
  Variable allS : list S.
  Hypothesis allS_full : forall s, In s allS.
  Variable evs : list E.
  Hypothesis evs_full : forall e, In e evs.
  Hypothesis eqv_dec : forall x y, {eqv (obs x) (obs y)} + {~ eqv (obs x) (obs y)}.

  Local Notation run := (runT step).

  Definition ssucc (s : S) : list S := map (fun e => step e s) evs.
  Definition psucc (p : S * S) : list (S * S) := map (fun e => (step e (fst p), step e (snd p))) evs.

  Theorem run_star_iff : forall s0 t, (exists u, t = run u s0) <-> star (Rsucc ssucc) s0 t.
  Proof.
    intros s0 t. split.
    - intros [u ->]. revert s0. induction u as [| e u IH]; intros s0; [apply star_refl |].
      rewrite runT_cons. eapply star_step; [| apply IH].
      unfold Rsucc, ssucc. exact (in_map (fun e => step e s0) evs e (evs_full e)).
    - intros H. refine (star_closed (Rsucc ssucc) (fun t => exists u, t = run u s0) _ s0 t _ H).
      + intros a b [u ->] Hb. unfold Rsucc, ssucc in Hb. apply in_map_iff in Hb.
        destruct Hb as [e [<- _]]. exists (u ++ [e]). rewrite runT_app. reflexivity.
      + exists []. reflexivity.
  Qed.

  Lemma run_dec : forall s0 t, {exists u, t = run u s0} + {~ exists u, t = run u s0}.
  Proof.
    intros s0 t. apply (dec_iff _ _ (iff_sym (run_star_iff s0 t))).
    exact (star_fin_dec eqS allS allS_full ssucc s0 t).
  Qed.

  Lemma forall_run_dec : forall s0 (P : S -> Prop), (forall t, {P t} + {~ P t}) ->
    {forall u, P (run u s0)} + {~ forall u, P (run u s0)}.
  Proof.
    intros s0 P Hd.
    assert (Iff : (forall t, (exists u, t = run u s0) -> P t) <-> (forall u, P (run u s0))).
    { split; [intros H u; apply H; exists u; reflexivity | intros H t [u ->]; apply H]. }
    apply (dec_iff _ _ Iff). apply (dec_forall_fin allS allS_full). intros t.
    apply dec_imp; [apply run_dec | apply Hd].
  Qed.

  Theorem pc_star_iff : forall s0 x y, PC step s0 x y <->
    exists t a b, (exists u, t = run u s0) /\
      star (Rsucc psucc) (step b (step a t), step a (step b t)) (x, y).
  Proof.
    intros s0 x y. split.
    - intros H. induction H as [u a b | e x y _ [t [a [b [Ht Hs]]]]].
      + exists (run u s0), a, b. split; [exists u; reflexivity | apply star_refl].
      + exists t, a, b. split; [exact Ht |]. eapply star_trans; [exact Hs |]. apply star_one.
        unfold Rsucc, psucc. exact (in_map (fun e => (step e (fst (x, y)), step e (snd (x, y)))) evs e (evs_full e)).
    - intros [t [a [b [[u ->] Hs]]]].
      refine (star_closed (Rsucc psucc) (fun p => PC step s0 (fst p) (snd p)) _ _ (x, y) _ Hs).
      + intros p q Hp Hq. unfold Rsucc, psucc in Hq. apply in_map_iff in Hq.
        destruct Hq as [e [<- _]]. simpl. apply pc_step. exact Hp.
      + apply pc_seed.
  Qed.

  Lemma pc_dec : forall s0 x y, {PC step s0 x y} + {~ PC step s0 x y}.
  Proof.
    intros s0 x y. apply (dec_iff _ _ (iff_sym (pc_star_iff s0 x y))).
    apply (dec_exists_fin allS allS_full). intros t.
    apply (dec_exists_fin evs evs_full). intros a.
    apply (dec_exists_fin evs evs_full). intros b.
    apply dec_and; [apply run_dec |].
    exact (star_fin_dec (prod_eq_dec eqS eqS) (list_prod allS allS) (prod_full allS allS allS_full allS_full)
             psucc _ _).
  Qed.

  Theorem closure_dec : forall s0, {ClosureOK step obs eqv s0} + {~ ClosureOK step obs eqv s0}.
  Proof.
    intros s0.
    assert (Iff : (forall p : S * S, PC step s0 (fst p) (snd p) -> eqv (obs (fst p)) (obs (snd p))) <->
                  ClosureOK step obs eqv s0).
    { split; [intros H x y P; exact (H (x, y) P) | intros H [x y] P; exact (H x y P)]. }
    apply (dec_iff _ _ Iff).
    apply (dec_forall_fin (list_prod allS allS) (prod_full allS allS allS_full allS_full)).
    intros [x y]. apply dec_imp; [apply pc_dec | apply eqv_dec].
  Qed.

  Theorem perm_obs_dec : forall s0, {PermObs step obs eqv s0} + {~ PermObs step obs eqv s0}.
  Proof.
    intros s0. apply (dec_iff _ _ (iff_sym (closure_perm_exact step obs eqv eqv_refl eqv_trans s0))).
    apply closure_dec.
  Qed.

  (* The search is exact: it finds a separated pair iff PermObs fails. *)
  Theorem closure_witness_exact : forall s0,
    ~ PermObs step obs eqv s0 <-> exists x y, PC step s0 x y /\ ~ eqv (obs x) (obs y).
  Proof.
    intros s0. split.
    - intros N.
      destruct (list_forall_or_witness (fun p : S * S => PC step s0 (fst p) (snd p) -> eqv (obs (fst p)) (obs (snd p)))
                  (list_prod allS allS)) as [H | [[x y] [_ Hn]]].
      + intros [x y]. apply dec_imp; [apply pc_dec | apply eqv_dec].
      + exfalso. apply N. apply (closure_perm_exact step obs eqv eqv_refl eqv_trans s0).
        intros x y P. exact (H (x, y) (prod_full allS allS allS_full allS_full (x, y)) P).
      + exists x, y. simpl in Hn. destruct (pc_dec s0 x y) as [P | P].
        * split; [exact P |]. intro Q. exact (Hn (fun _ => Q)).
        * exfalso. apply Hn. intro P'. contradiction.
    - intros [x [y [P N]]]. exact (closure_witness_refutes step obs eqv eqv_refl eqv_trans s0 x y P N).
  Qed.
End SwapFinite.

(* ============================================================================================ *)
(* 2. The barrier's A part in section Det, exactly.                                             *)
(* ============================================================================================ *)

Section DetClosure.
  Context {SA EA SB EB : Type}.
  Variable stepA : EA -> SA -> SA.
  Variable stepB : EB -> SB -> SB.
  Variable eqvB : SB -> SB -> Prop.
  Hypothesis eqvB_refl : forall x, eqvB x x.
  Hypothesis eqvB_sym : forall x y, eqvB x y -> eqvB y x.
  Hypothesis eqvB_trans : forall x y z, eqvB x y -> eqvB y z -> eqvB x z.
  Hypothesis stepB_ext : forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y).
  Variable M : SA -> SB.
  Variable tau : EA -> EB.

  Local Notation runA := (runT stepA).
  Local Notation runB := (runT stepB).

  (* A converges modulo M: the A part of det_barrier_exact. *)
  Definition AmodM (s0 : SA) : Prop :=
    forall u u', Permutation u u' -> eqvB (M (runA u s0)) (M (runA u' s0)).

  Theorem amodm_swap_exact : forall s0, AmodM s0 <->
    forall u a b w,
      eqvB (M (runA w (stepA b (stepA a (runA u s0))))) (M (runA w (stepA a (stepA b (runA u s0))))).
  Proof. exact (perm_swap_exact stepA M eqvB eqvB_refl eqvB_trans). Qed.

  Theorem amodm_closure_exact : forall s0, AmodM s0 <-> ClosureOK stepA M eqvB s0.
  Proof. exact (closure_perm_exact stepA M eqvB eqvB_refl eqvB_trans). Qed.

  (* B's permutation convergence is local: stepB respects eqvB, so the continuation drops. *)
  Theorem permB_local_exact : forall x, PermB stepB eqvB x <->
    forall v a b, eqvB (stepB b (stepB a (runB v x))) (stepB a (stepB b (runB v x))).
  Proof. exact (perm_local_exact stepB (fun y => y) eqvB eqvB_refl eqvB_trans stepB_ext). Qed.

  (* A's own permutation convergence with equality, the PermA gsm checks, is local too. *)
  Theorem permA_eq_local_exact : forall s0, PermA stepA eq s0 <->
    forall u a b, stepA b (stepA a (runA u s0)) = stepA a (stepA b (runA u s0)).
  Proof.
    exact (perm_local_exact stepA (fun t => t) eq (fun x => eq_refl)
             (fun x y z H1 H2 => eq_trans H1 H2) (fun e x y H => f_equal (stepA e) H)).
  Qed.

  Theorem det_barrier_closure_exact : forall s0, DBar stepA stepB eqvB M s0 <->
    (forall u, PermB stepB eqvB (M (runA u s0))) /\ ClosureOK stepA M eqvB s0.
  Proof.
    intros s0. rewrite (det_barrier_exact stepA stepB eqvB eqvB_trans stepB_ext M s0).
    pose proof (amodm_closure_exact s0) as H. unfold AmodM in H. tauto.
  Qed.

  (* Both outcomes as local conditions at reachable states plus the pair closure. *)
  Theorem det_barrier_local_exact : forall s0, DBar stepA stepB eqvB M s0 <->
    (forall u v a b, eqvB (stepB b (stepB a (runB v (M (runA u s0))))) (stepB a (stepB b (runB v (M (runA u s0)))))) /\
    ClosureOK stepA M eqvB s0.
  Proof.
    intros s0. rewrite det_barrier_closure_exact. split; intros [H1 H2]; split; try exact H2.
    - intros u. apply permB_local_exact. apply H1.
    - intros u. apply permB_local_exact. apply H1.
  Qed.

  Theorem det_live_local_exact : forall s0, DLive stepA stepB eqvB M tau s0 <->
    (forall v a b, eqvB (stepB b (stepB a (runB v (M s0)))) (stepB a (stepB b (runB v (M s0))))) /\
    (forall u e, eqvB (M (stepA e (runA u s0))) (stepB (tau e) (M (runA u s0)))).
  Proof.
    intros s0. rewrite (det_live_exact stepA stepB eqvB eqvB_refl eqvB_sym eqvB_trans stepB_ext M tau s0).
    rewrite permB_local_exact. unfold DS1. tauto.
  Qed.

  Variable eqvA : SA -> SA -> Prop.

  (* det_barrier_faithful recovered: under reflection and preservation, the closure condition is
     A's own convergence. *)
  Theorem det_barrier_faithful_closure : (forall x y, eqvA x y <-> eqvB (M x) (M y)) ->
    forall s0, ClosureOK stepA M eqvB s0 <-> PermA stepA eqvA s0.
  Proof.
    intros HM s0. rewrite <- amodm_closure_exact. unfold AmodM, PermA. split.
    - intros H u u' P. apply HM. apply H. exact P.
    - intros H u u' P. apply HM. apply H. exact P.
  Qed.

  (* The sufficient direction gsm used: A's convergence implies the closure condition whenever M
     preserves the equivalences (with equality on A, always). *)
  Theorem det_closure_of_permA : (forall x y, eqvA x y -> eqvB (M x) (M y)) ->
    forall s0, PermA stepA eqvA s0 -> ClosureOK stepA M eqvB s0.
  Proof.
    intros HM s0 H. apply amodm_closure_exact. intros u u' P. apply HM. apply H. exact P.
  Qed.

  Theorem det_barrier_closure_faithful : (forall x y, eqvA x y <-> eqvB (M x) (M y)) ->
    forall s0, DBar stepA stepB eqvB M s0 <->
      (forall u, PermB stepB eqvB (M (runA u s0))) /\ PermA stepA eqvA s0.
  Proof.
    intros HM s0. rewrite det_barrier_closure_exact. rewrite (det_barrier_faithful_closure HM s0). tauto.
  Qed.
End DetClosure.

(* ============================================================================================ *)
(* 3. Complete classification on finite instances.                                              *)
(* ============================================================================================ *)

Definition DClassified {SA EA SB EB : Type} (stepA : EA -> SA -> SA) (stepB : EB -> SB -> SB)
  (eqvB : SB -> SB -> Prop) (M : SA -> SB) (tau : EA -> EB) (s0 : SA) (o : outcome) : Prop :=
  match o with
  | Online => DLive stepA stepB eqvB M tau s0
  | BarrierOnly => DBar stepA stepB eqvB M s0 /\ ~ DLive stepA stepB eqvB M tau s0
  | Unsafe => ~ DBar stepA stepB eqvB M s0
  end.

Theorem det_classified_unique : forall {SA EA SB EB : Type} stepA stepB eqvB (M : SA -> SB)
  (tau : EA -> EB) s0 o1 o2,
  DClassified (EB := EB) stepA stepB eqvB M tau s0 o1 ->
  DClassified stepA stepB eqvB M tau s0 o2 -> o1 = o2.
Proof.
  intros SA EA SB EB stepA stepB eqvB M tau s0 o1 o2 H1 H2.
  pose proof (det_live_implies_barrier stepA stepB eqvB M tau s0) as LB.
  destruct o1, o2; simpl in *; try reflexivity; try tauto.
Qed.

Section DetFinite.
  Context {SA EA SB EB : Type}.
  Variable stepA : EA -> SA -> SA.
  Variable stepB : EB -> SB -> SB.
  Variable eqvB : SB -> SB -> Prop.
  Hypothesis eqvB_refl : forall x, eqvB x x.
  Hypothesis eqvB_sym : forall x y, eqvB x y -> eqvB y x.
  Hypothesis eqvB_trans : forall x y z, eqvB x y -> eqvB y z -> eqvB x z.
  Hypothesis stepB_ext : forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y).
  Variable M : SA -> SB.
  Variable tau : EA -> EB.
  Variable eqSA : forall a b : SA, {a = b} + {a <> b}.
  Variable eqSB : forall a b : SB, {a = b} + {a <> b}.
  Variable allA : list SA.
  Hypothesis allA_full : forall s, In s allA.
  Variable allB : list SB.
  Hypothesis allB_full : forall x, In x allB.
  Variable evsA : list EA.
  Hypothesis evsA_full : forall e, In e evsA.
  Variable evsB : list EB.
  Hypothesis evsB_full : forall e, In e evsB.
  Hypothesis eqvB_dec : forall x y, {eqvB x y} + {~ eqvB x y}.

  Local Notation runA := (runT stepA).

  Lemma permB_dec : forall x, {PermB stepB eqvB x} + {~ PermB stepB eqvB x}.
  Proof.
    intros x. apply (dec_iff _ _ (iff_sym (permB_local_exact stepB eqvB eqvB_refl eqvB_trans stepB_ext x))).
    apply (forall_run_dec stepB eqSB allB allB_full evsB evsB_full x
             (fun y => forall a b, eqvB (stepB b (stepB a y)) (stepB a (stepB b y)))). intros y.
    apply (dec_forall_fin evsB evsB_full). intros a.
    apply (dec_forall_fin evsB evsB_full). intros b. apply eqvB_dec.
  Qed.

  Theorem det_live_dec : forall s0, {DLive stepA stepB eqvB M tau s0} + {~ DLive stepA stepB eqvB M tau s0}.
  Proof.
    intros s0.
    apply (dec_iff _ _ (iff_sym (det_live_exact stepA stepB eqvB eqvB_refl eqvB_sym eqvB_trans stepB_ext M tau s0))).
    apply dec_and; [apply permB_dec |]. unfold DS1.
    apply (forall_run_dec stepA eqSA allA allA_full evsA evsA_full s0
             (fun t => forall e, eqvB (M (stepA e t)) (stepB (tau e) (M t)))).
    intros t. apply (dec_forall_fin evsA evsA_full). intros e. apply eqvB_dec.
  Qed.

  Theorem det_barrier_dec : forall s0, {DBar stepA stepB eqvB M s0} + {~ DBar stepA stepB eqvB M s0}.
  Proof.
    intros s0.
    apply (dec_iff _ _ (iff_sym (det_barrier_closure_exact stepA stepB eqvB eqvB_refl eqvB_trans stepB_ext M s0))).
    apply dec_and.
    - apply (forall_run_dec stepA eqSA allA allA_full evsA evsA_full s0 (fun t => PermB stepB eqvB (M t))).
      intros t. apply permB_dec.
    - apply (closure_dec stepA M eqvB eqSA allA allA_full evsA evsA_full). intros x y. apply eqvB_dec.
  Qed.

  (* The trichotomy is decided with no faithfulness hypothesis: no unknown outcome remains. *)
  Theorem det_classify_complete : forall s0, {o : outcome | DClassified stepA stepB eqvB M tau s0 o}.
  Proof.
    intros s0. destruct (det_live_dec s0) as [L | L].
    - exists Online. exact L.
    - destruct (det_barrier_dec s0) as [Bc | Bc].
      + exists BarrierOnly. split; assumption.
      + exists Unsafe. exact Bc.
  Qed.

  (* The A part fails iff the pair closure has a pair M separates: the search gsm runs finds a
     witness iff one exists, so an exhausted search certifies A's convergence modulo M. *)
  Theorem amodm_witness_exact : forall s0,
    ~ AmodM stepA eqvB M s0 <-> exists x y, PC stepA s0 x y /\ ~ eqvB (M x) (M y).
  Proof.
    intros s0. exact (closure_witness_exact stepA M eqvB eqvB_refl eqvB_trans eqSA allA allA_full
                        evsA evsA_full (fun x y => eqvB_dec (M x) (M y)) s0).
  Qed.

  (* The barrier outcome on finite instances, as gsm decides it: Unsafe iff B diverges after a
     barrier switch at some reachable state or the closure has a pair M separates. *)
  Theorem det_unsafe_exact : forall s0, ~ DBar stepA stepB eqvB M s0 <->
    (exists u, ~ PermB stepB eqvB (M (runA u s0))) \/ (exists x y, PC stepA s0 x y /\ ~ eqvB (M x) (M y)).
  Proof.
    intros s0. rewrite (det_barrier_closure_exact stepA stepB eqvB eqvB_refl eqvB_trans stepB_ext M s0).
    rewrite <- (amodm_closure_exact stepA eqvB eqvB_refl eqvB_trans M s0).
    rewrite <- amodm_witness_exact. split.
    - intros N. destruct (forall_run_dec stepA eqSA allA allA_full evsA evsA_full s0
                           (fun t => PermB stepB eqvB (M t)) (fun t => permB_dec (M t))) as [H | H].
      + right. intro A. exact (N (conj H A)).
      + left. destruct (dec_exists_fin allA allA_full (fun t => (exists u, t = runA u s0) /\ ~ PermB stepB eqvB (M t)))
          as [[t [[u ->] Hn]] | Hn].
        * intros t. apply dec_and; [apply (run_dec stepA eqSA allA allA_full evsA evsA_full) |].
          apply dec_not. apply permB_dec.
        * exists u. exact Hn.
        * exfalso. apply H. intros u. destruct (permB_dec (M (runA u s0))) as [P | P]; [exact P |].
          exfalso. apply Hn. exists (runA u s0). split; [exists u; reflexivity | exact P].
    - intros [[u N] | N] [H1 H2]; [exact (N (H1 u)) | exact (N H2)].
  Qed.
End DetFinite.

(* ============================================================================================ *)
(* 4. Instances: non-injective migrations of a diverging A.                                     *)
(* ============================================================================================ *)

(* A: last-writer-wins on option bool. None is the start, Some b the last write. *)
Definition lwwA (e : bool) (_ : option bool) : option bool := Some e.
(* The migration that merges the two writes. *)
Definition mergeM (s : option bool) : bool := match s with None => false | Some _ => true end.
(* The migration that merges the start with one write. *)
Definition partialM (s : option bool) : bool := match s with None => true | Some b => b end.
Definition flagB (_ : unit) (_ : bool) : bool := true.
Definition idleB (_ : unit) (x : bool) : bool := x.
Definition toUnit (_ : bool) : unit := tt.

Lemma eq_refl' : forall {X : Type} (x : X), x = x.
Proof. reflexivity. Qed.
Lemma eq_sym' : forall {X : Type} (x y : X), x = y -> y = x.
Proof. intros X x y H. symmetry. exact H. Qed.
Lemma eq_trans' : forall {X : Type} (x y z : X), x = y -> y = z -> x = z.
Proof. intros X x y z H1 H2. rewrite H1. exact H2. Qed.
Lemma eq_ext' : forall {X E : Type} (f : E -> X -> X) e (x y : X), x = y -> f e x = f e y.
Proof. intros X E f e x y H. rewrite H. reflexivity. Qed.

Definition ob_eq_dec : forall a b : option bool, {a = b} + {a <> b}.
Proof. decide equality. apply bool_dec. Defined.

Lemma ob_full : forall s : option bool, In s [None; Some true; Some false].
Proof. intros [[|] |]; simpl; tauto. Qed.
Lemma b_full : forall b : bool, In b [true; false].
Proof. intros [|]; simpl; tauto. Qed.
Lemma u_full : forall u : unit, In u [tt].
Proof. intros []. simpl. tauto. Qed.

(* A diverges, and both migrations are non-injective on the states A reaches from None. *)
Theorem lww_diverges : ~ PermA lwwA eq None.
Proof.
  intro H. specialize (H [true; false] [false; true] (perm_swap false true [])).
  unfold runT in H. simpl in H. discriminate H.
Qed.

Lemma lww_run_cons : forall u e s, runT lwwA (u ++ [e]) s = Some e.
Proof. intros u e s. rewrite runT_app. reflexivity. Qed.

Theorem merge_not_injective :
  mergeM (runT lwwA [true] None) = mergeM (runT lwwA [false] None) /\
  runT lwwA [true] None <> runT lwwA [false] None.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem partial_not_injective :
  partialM (runT lwwA [] None) = partialM (runT lwwA [true] None) /\
  runT lwwA [] None <> runT lwwA [true] None.
Proof. split; [reflexivity | discriminate]. Qed.

(* Every pair of the closure under lwwA is two writes. *)
Lemma lww_pc_some : forall s0 x y, PC lwwA s0 x y -> exists a b, x = Some a /\ y = Some b.
Proof.
  intros s0 x y H. destruct H as [u a b | e x y _].
  - exists b, a. split; reflexivity.
  - exists e, e. split; reflexivity.
Qed.

(* The closure condition holds for mergeM: certified by the closure, not by faithfulness. *)
Theorem merged_barrier_closure : ClosureOK lwwA mergeM eq None.
Proof.
  intros x y P. destruct (lww_pc_some None x y P) as [a [b [-> ->]]]. reflexivity.
Qed.

(* merged_online: B sets a flag; every write becomes the flag event. Online, though A diverges
   and M is not injective. *)
Theorem merged_online : DClassified lwwA flagB eq mergeM toUnit None Online.
Proof.
  simpl. apply (det_live_exact lwwA flagB eq eq_refl' eq_sym' eq_trans' (eq_ext' flagB) mergeM toUnit None).
  split.
  - intros v v' P. destruct v as [| e v]; destruct v' as [| e' v'].
    + reflexivity.
    + apply Permutation_nil in P. discriminate P.
    + apply Permutation_sym, Permutation_nil in P. discriminate P.
    + rewrite !runT_cons. unfold flagB at 1 3.
      assert (K : forall w, runT flagB w true = true).
      { induction w as [| f w IH]; [reflexivity | rewrite runT_cons; exact IH]. }
      rewrite !K. reflexivity.
  - intros u e. destruct u as [| f u] using rev_ind; [reflexivity |].
    rewrite lww_run_cons. reflexivity.
Qed.

(* merged_barrier: B ignores the translated events. An in-flight write is lost, so the live
   switch diverges; the barrier switch converges by the closure (the case gsm called Unknown). *)
Theorem merged_barrier : DClassified lwwA idleB eq mergeM toUnit None BarrierOnly /\
  ~ PermA lwwA eq None /\ ~ (forall x y, mergeM x = mergeM y -> x = y).
Proof.
  split; [split | split; [exact lww_diverges |]].
  - apply (det_barrier_closure_exact lwwA idleB eq eq_refl' eq_trans' (eq_ext' idleB) mergeM None).
    split; [| exact merged_barrier_closure].
    intros u v v' P. assert (K : forall w x, runT idleB w x = x).
    { induction w as [| f w IH]; intros x; [reflexivity | rewrite runT_cons; apply IH]. }
    rewrite !K. reflexivity.
  - intro H. apply (det_live_exact lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) mergeM toUnit None) in H.
    destruct H as [_ H]. specialize (H [] true). simpl in H. discriminate H.
  - intro H. specialize (H (Some true) (Some false) eq_refl). discriminate H.
Qed.

(* partial_merge: the closure has a pair M separates, at the start with events true, false. *)
Theorem partial_merge_witness : PC lwwA None (Some false) (Some true) /\ partialM (Some false) <> partialM (Some true).
Proof.
  split; [exact (pc_seed lwwA None [] true false) | discriminate].
Qed.

Theorem partial_merge : DClassified lwwA idleB eq partialM toUnit None Unsafe /\
  ~ PermA lwwA eq None /\ ~ (forall x y, partialM x = partialM y -> x = y).
Proof.
  split; [| split; [exact lww_diverges |]].
  - simpl. intro H.
    apply (det_barrier_closure_exact lwwA idleB eq eq_refl' eq_trans' (eq_ext' idleB) partialM None) in H.
    destruct H as [_ H]. destruct partial_merge_witness as [P N]. exact (N (H _ _ P)).
  - intro H. specialize (H None (Some true) eq_refl). discriminate H.
Qed.

(* The closure condition is not vacuous either way: it holds for mergeM and fails for partialM. *)
Theorem closure_nonvacuous : ClosureOK lwwA mergeM eq None /\ ~ ClosureOK lwwA partialM eq None.
Proof.
  split; [exact merged_barrier_closure |].
  intro H. destruct partial_merge_witness as [P N]. exact (N (H _ _ P)).
Qed.

(* gsm's pruned search on the instances: the orientation true before false, and equal pairs
   skipped. sel covers every pair of events (non-vacuity of gsm_closure_exact's hypothesis). *)
Definition sel_tf (a b : bool) : Prop := a = true /\ b = false.

Lemma sel_tf_cover : forall a b, a = b \/ sel_tf a b \/ sel_tf b a.
Proof. intros [|] [|]; unfold sel_tf; tauto. Qed.

Theorem gsm_search_instances :
  ClosureG lwwA mergeM eq sel_tf None /\ ~ ClosureG lwwA partialM eq sel_tf None.
Proof.
  destruct closure_nonvacuous as [H1 H2]. split.
  - apply (gsm_closure_exact lwwA mergeM eq eq_refl' eq_sym' ob_eq_dec sel_tf sel_tf_cover None). exact H1.
  - intro H. apply H2.
    apply (gsm_closure_exact lwwA partialM eq eq_refl' eq_sym' ob_eq_dec sel_tf sel_tf_cover None). exact H.
Qed.

(* det_classify_complete runs on each instance: its finite hypotheses all hold. *)
Definition merged_classified (M : option bool -> bool) (stepB : unit -> bool -> bool) :
  {o : outcome | DClassified lwwA stepB eq M toUnit None o} :=
  det_classify_complete lwwA stepB eq eq_refl' eq_sym' eq_trans' (eq_ext' stepB) M toUnit
    ob_eq_dec bool_dec [None; Some true; Some false] ob_full [true; false] b_full [true; false] b_full
    [tt] u_full bool_dec None.

Theorem merged_classified_outcomes :
  proj1_sig (merged_classified mergeM flagB) = Online /\
  proj1_sig (merged_classified mergeM idleB) = BarrierOnly /\
  proj1_sig (merged_classified partialM idleB) = Unsafe.
Proof.
  split; [| split].
  - destruct (merged_classified mergeM flagB) as [o H]. simpl.
    exact (det_classified_unique _ _ _ _ _ _ _ _ H merged_online).
  - destruct (merged_classified mergeM idleB) as [o H]. simpl.
    exact (det_classified_unique _ _ _ _ _ _ _ _ H (proj1 merged_barrier)).
  - destruct (merged_classified partialM idleB) as [o H]. simpl.
    exact (det_classified_unique _ _ _ _ _ _ _ _ H (proj1 partial_merge)).
Qed.
