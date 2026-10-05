(* DistributedExact.v: the EXACT condition for event interleavings in the distributed model of an
   acyclic federation (local events and propagation steps as separate actions). Axiom-free.

   The gap. FederationEvents.v defines the distributed model: a run is any word of local events
   (DEv e: registry reg e applies sig e to its own state) and propagation steps (DProp j:
   registry j overwrites its shared part with the image of its sources' CURRENT states, which
   may themselves be stale). It proves only sufficiency: under XU (C1 at every valid target
   state) and each registry's own CC, every interleaving reaches, after a final flush N, the
   FedMachine run of its events (propagation_flush, dist_interleavings_converge). This file
   proves the exact condition, from a fixed valid start s0.

   Reachable stale combinations. A state t is reachable when t = drun p s0 for a word p of
   events and propagation steps. Its target value t j can be stale: its shared part is the image
   of an earlier source state, a value a local event wrote, or the start's own value. The image
   it will be repaired to is that of the flushed sources, N t. The pair (t j, N t) is a
   reachable (target state, image) combination.

     XUat t e   := ow (sig e (ow (t j))) = ow (sig e (t j))     with j := reg e, ow := f j (N t)
     XUR s0     := XUat t e for every reachable t and every event e        (reachable XU)
     LCCat t e1 e2 := ow (sig e2 (sig e1 (t j))) = ow (sig e1 (sig e2 (t j)))   (j := reg e1)
     LCCR s0    := LCCat t e1 e2 for every reachable t, e1 e2 declared independent on one
                   registry                                   (each registry's CC, up to repair,
                                                               at reachable states)
     DistConv s0 := for all words w1 w2 whose event sequences are federated-trace-equivalent,
                    N (drun w1 s0) = N (drun w2 s0)    (compare after the final flush, as
                                                         dist_interleavings_converge does)

   Results.
     dist_exact        : DistConv s0 <-> XUR s0 /\ C2R (N s0)
                         (C2R: the FedMachine's C2 at states reachable from the flushed start)
     dist_exact_local  : DistConv s0 <-> XUR s0 /\ LCCR s0
                         (the reachable form of the two hypotheses XU + LocalCC)
     dist_exact_tc     : DistConv s0 <-> XUR s0 /\ TraceConv (N s0)
     The converse is constructive from a failure witness: dist_xu_runs computes the two runs
     "event at t" (p ++ [DEv e]) and "flush, then event" (p ++ map DProp o ++ [DEv e]); they have
     the same events and their flushes differ at reg e exactly when XUat t e fails
     (dist_xu_diverge). lcc_runs does the same for two same-registry events (one swap).
     Reachable XU already implies the FedMachine's C1 at reachable witnesses (xur_c1r1).

   (a) XU is sufficient, recovered: dist_interleavings_converge_recovered (XU + LocalCC),
       xu_exact_condition; and the weaker pair XU + C2 suffices (dist_xu_c2_converge), which is
       what gsm checks (XU in FedReport.ProjectionSafe, C2 in Build).
   (b) Strictly weaker than XU: levels_exact_not_xu. gsm's `levels` federation (a guarded target
       event fires only at a shared value no source image produces and no local event writes):
       C1, C2 hold, XU fails, and from every valid start whose target is not at that value
       (every consistent start among them) the exact condition holds and every interleaving
       converges. From a stale start at that value it diverges, so the qualifier matters.
   (c) Distributed convergence implies FedMachine convergence: dist_implies_fed (and
       dist_implies_fed_flush for a start that is not consistent). The converse fails:
       dist_strictly_stronger_than_fed, on the federation of fed_grs_c1_c2_insufficient
       (FederationGRS.v): C1, C2 hold, so every FedMachine order converges from every consistent
       start, but reachable XU fails and two distributed runs with the SAME event sequence
       diverge from a consistent start.

   Every valid start. Quantifying the start (gsm checks statically, for every start):
     dist_exact_global     : (forall valid s0, DistConv s0) <-> XUG /\ C2G
                             (XUG: XU at every valid target state with the image of FLUSHED
                              sources; C2G: C2 at every consistent state)
     dist_exact_consistent : (forall valid consistent s0, DistConv s0) <->
                             (forall valid consistent s0, XUR s0) /\ C2G
     dist_global_exact_roots : when every target's sources are roots (their repair is the
                             identity: any two-registry federation, any star),
                             (forall valid s0, DistConv s0) <-> XU /\ C2,
                             so gsm's static XU + C2 check is exact for "every valid start".
   Non-vacuity: supply_dist_exact (the supply_instance federation satisfies every form);
   levels_exact_not_xu (exact condition without XU); dist_strictly_stronger_than_fed.

   States are compared pointwise (feq); no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.FederationEvents NC.FederationEventsConverse NC.FederationGRS.
Import ListNotations.

Section DistExact.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  Variable o : list nat.

  Local Notation feqF := (feq V).
  Local Notation InvF := (Inv V valid).
  Local Notation ConsF := (Cons V f o).
  Local Notation aF := (applyF V f rho E reg sig o).
  Local Notation rF := (runF V f rho E reg sig o).
  Local Notation nF := (N V f rho o).
  Local Notation frF := (frun V f).
  Local Notation evF := (evstep V E reg sig).
  Local Notation IfedF := (Ifed E reg I).
  Local Notation dF := (drun V f E reg sig).
  Local Notation okF := (okact E o).
  Local Notation evsF := (evs E).
  Local Notation DE := (DEv E).
  Local Notation DP := (DProp E).
  Local Notation TC := (TraceConv V f rho E reg sig I o).
  Local Notation C2Rf := (C2R V f rho E reg sig I o).
  Local Notation C1R1f := (C1R1 V f rho E reg sig o).
  Local Notation C2atf := (C2at V f E reg sig).

  (* XU at one reachable (target state, image) combination: the target value t (reg e), whose
     shared part may be stale, and the image of the flushed sources N t. *)
  Definition XUat (t : nat -> V) (e : E) : Prop :=
    f (reg e) (nF t) (sig e (f (reg e) (nF t) (t (reg e)))) = f (reg e) (nF t) (sig e (t (reg e))).

  (* Reachable XU: XUat at every state a distributed run from s0 reaches. *)
  Definition XUR (s0 : nat -> V) : Prop := forall p e, Forall okF p -> XUat (dF p s0) e.

  (* A registry's own CC on one declared pair, up to the repair, at a reachable state. *)
  Definition LCCat (t : nat -> V) (e1 e2 : E) : Prop :=
    f (reg e1) (nF t) (sig e2 (sig e1 (t (reg e1)))) =
    f (reg e1) (nF t) (sig e1 (sig e2 (t (reg e1)))).

  Definition LCCR (s0 : nat -> V) : Prop :=
    forall p e1 e2, Forall okF p -> reg e1 = reg e2 -> I e1 e2 -> LCCat (dF p s0) e1 e2.

  (* Distributed convergence from s0: words with trace-equivalent event sequences agree once
     propagation completes. *)
  Definition DistConv (s0 : nat -> V) : Prop :=
    forall w1 w2, Forall okF w1 -> Forall okF w2 -> tequiv IfedF (evsF w1) (evsF w2) ->
      feqF (nF (dF w1 s0)) (nF (dF w2 s0)).

  (* The start-free forms: XU with the image of flushed sources; C2 at every consistent state. *)
  Definition XUG : Prop := forall s e, InvF s -> XUat s e.

  Definition C2G : Prop :=
    forall s e1 e2, InvF s -> ConsF s -> reg e1 = reg e2 -> I e1 e2 -> C2atf s e1 e2.

  (* Every target reads only roots (registries whose repair is the identity). *)
  Definition RootSrc : Prop := forall e k, In k (src (reg e)) -> forall t x, f k t x = x.

  (* ---------------------------------------------------------------------------------- *)
  (* Words.                                                                              *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma drun_app : forall p q t, dF (p ++ q) t = dF q (dF p t).
  Proof. induction p as [| a p IH]; intros q t; [reflexivity |]. simpl. apply IH. Qed.

  Lemma drun_props : forall l t, dF (map DP l) t = frF l t.
  Proof.
    induction l as [| a l IH]; intros t; [reflexivity |].
    simpl. rewrite IH. reflexivity.
  Qed.

  Lemma evs_app : forall p q, evsF (p ++ q) = evsF p ++ evsF q.
  Proof.
    induction p as [| a p IH]; intros q; [reflexivity |].
    destruct a; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma evs_props : forall l, evsF (map DP l) = [].
  Proof. induction l as [| a l IH]; [reflexivity | exact IH]. Qed.

  Lemma evs_evs : forall es, evsF (map DE es) = es.
  Proof. induction es as [| a es IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

  Lemma ok_app : forall p q, Forall okF p -> Forall okF q -> Forall okF (p ++ q).
  Proof.
    induction p as [| a p IH]; intros q Hp Hq; [exact Hq |].
    inversion Hp as [| ? ? Ha Hp']; subst. simpl. constructor; [exact Ha | apply IH; assumption].
  Qed.

  Lemma ok_evs : forall es, Forall okF (map DE es).
  Proof. induction es as [| a es IH]; [constructor | simpl; constructor; [exact Logic.I | exact IH]]. Qed.

  Section WithCommon.
  Hypothesis HC : Common V src f valid rho E reg sig o.

  Lemma ok_props : Forall okF (map DP o).
  Proof.
    apply Forall_forall. intros a Ha. apply in_map_iff in Ha as [j [<- Hj]]. exact Hj.
  Qed.

  Lemma drun_inv : forall w t, InvF t -> InvF (dF w t).
  Proof.
    induction w as [| a w IH]; intros t H; [exact H |].
    simpl. apply IH. apply (dstep_inv _ _ _ _ _ _ _ _ _ HC). exact H.
  Qed.

  Lemma f_ext : forall j t t' x, feqF t t' -> f j t x = f j t' x.
  Proof. intros. apply (c_local _ _ _ _ _ _ _ _ _ HC). intros. auto. Qed.

  (* The flushed value at a registry of o is the repair of the registry's own value. *)
  Lemma N_at : forall u j, InvF u -> In j o -> nF u j = f j (nF u) (u j).
  Proof.
    intros u j Hu Hj. pose proof (N_frun _ _ _ _ _ _ _ _ _ HC u Hu) as Hn.
    rewrite (Hn j).
    rewrite (frun_solves _ _ _ _ _ _ _ _ _ HC o u (c_topo _ _ _ _ _ _ _ _ _ HC) j Hj).
    apply f_ext. apply feq_sym. exact Hn.
  Qed.

  Lemma N_out : forall u k, InvF u -> ~ In k o -> nF u k = u k.
  Proof.
    intros u k Hu Hk. unfold N. rewrite (frun_out _ _ o _ k Hk).
    apply (c_rho _ _ _ _ _ _ _ _ _ HC). apply Hu.
  Qed.

  (* An event on j leaves the flushed sources of j unchanged. *)
  Lemma N_src_ev : forall e t k, In k (src (reg e)) -> nF (evF e t) k = nF t k.
  Proof.
    intros e t k Hk.
    destruct (split_at _ _ _ _ _ _ _ _ _ HC (reg e) (c_reg _ _ _ _ _ _ _ _ _ HC e))
      as [o1 [L [Ho [Hj Hs]]]].
    pose proof (N_upL _ _ _ _ _ _ _ _ _ HC o1 L _ _ Ho (evstep_upL_self V E reg sig L e t Hj)) as U.
    unfold upL in U. apply U. apply Hs. exact Hk.
  Qed.

  Lemma f_N_ev : forall e t j x, j = reg e -> f j (nF (evF e t)) x = f j (nF t) x.
  Proof.
    intros e t j x ->. apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk. apply N_src_ev. exact Hk.
  Qed.

  Lemma N_ev_at : forall e t, InvF t -> nF (evF e t) (reg e) = f (reg e) (nF t) (sig e (t (reg e))).
  Proof.
    intros e t Ht.
    rewrite (N_at (evF e t) (reg e)); [| apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact Ht
                                       | apply (c_reg _ _ _ _ _ _ _ _ _ HC)].
    rewrite (f_N_ev e t (reg e) _ eq_refl). rewrite (evstep_at V E reg sig e t (reg e) eq_refl).
    reflexivity.
  Qed.

  (* Flushing commutes with an event at t exactly when XU holds at t. *)
  Lemma flush_ev_at : forall e t, InvF t -> XUat t e -> feqF (nF (evF e t)) (aF e (nF t)).
  Proof.
    intros e t Ht Hx. unfold applyF.
    pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e) as Re.
    assert (In_ : InvF (nF t)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact Ht).
    assert (I1 : InvF (evF e t)) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact Ht).
    assert (I2 : InvF (evF e (nF t))) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact In_).
    assert (Iz : InvF (nF (evF e t))) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact I1).
    apply (solve_unique _ _ _ _ _ _ _ _ _ HC o _ _ (evF e t) (evF e (nF t))
             (c_topo _ _ _ _ _ _ _ _ _ HC)).
    - intros k Hk. rewrite (N_out _ k I1 Hk), (N_out _ k I2 Hk).
      assert (Ne : k <> reg e) by (intro E'; subst; contradiction).
      rewrite !(evstep_off V E reg sig e _ k Ne). rewrite (N_out _ k Ht Hk). reflexivity.
    - intros j Hj. apply N_at; assumption.
    - intros j Hj. apply N_at; assumption.
    - intros j Hj. destruct (Nat.eq_dec j (reg e)) as [-> | Ne].
      + rewrite !(evstep_at V E reg sig e _ (reg e) eq_refl).
        rewrite !(f_N_ev e t (reg e) _ eq_refl).
        rewrite (N_at t (reg e) Ht Re). symmetry. exact Hx.
      + rewrite !(evstep_off V E reg sig e _ j Ne). rewrite (N_at t j Ht Hj).
        symmetry. apply (c_absorb _ _ _ _ _ _ _ _ _ HC); [exact Iz | exact In_ | apply Ht].
  Qed.

  (* Under reachable XU, every distributed run from s0 flushes to the FedMachine run of its
     events from the flushed start (propagation_flush, restricted to reachable states). *)
  Lemma flush_reach : forall s0, InvF s0 -> XUR s0 ->
    forall w p, Forall okF p -> Forall okF w ->
      feqF (nF (dF w (dF p s0))) (rF (evsF w) (nF (dF p s0))).
  Proof.
    intros s0 Hi Hx w. induction w as [| a w IH]; intros p Hp Hw; [intro k; reflexivity |].
    inversion Hw as [| ? ? Ha Hw']; subst.
    assert (Hpa : Forall okF (p ++ [a])) by (apply ok_app; [exact Hp | constructor; [exact Ha | constructor]]).
    assert (Ep : dstep V f E reg sig a (dF p s0) = dF (p ++ [a]) s0) by (rewrite drun_app; reflexivity).
    assert (It : InvF (dF p s0)) by (apply drun_inv; exact Hi).
    change (dF (a :: w) (dF p s0)) with (dF w (dstep V f E reg sig a (dF p s0))). rewrite Ep.
    eapply feq_trans; [exact (IH (p ++ [a]) Hpa Hw') |].
    rewrite <- Ep. destruct a as [e | j]; simpl.
    - change (rF (e :: evsF w) (nF (dF p s0))) with (rF (evsF w) (aF e (nF (dF p s0)))).
      apply (runF_ext _ _ _ _ _ _ _ _ _ HC). apply flush_ev_at; [exact It | apply Hx; exact Hp].
    - apply (runF_ext _ _ _ _ _ _ _ _ _ HC). apply (flush_prop _ _ _ _ _ _ _ _ _ HC); [exact It | exact Ha].
  Qed.

  Theorem dist_flush : forall s0, InvF s0 -> XUR s0 ->
    forall w, Forall okF w -> feqF (nF (dF w s0)) (rF (evsF w) (nF s0)).
  Proof. intros s0 Hi Hx w Hw. exact (flush_reach s0 Hi Hx w [] ltac:(constructor) Hw). Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* The failure witnesses: the runs whose flushes ARE the two sides of each condition.  *)
  (* ---------------------------------------------------------------------------------- *)

  (* "event at t" versus "flush, then event": same events, and their flushes at reg e are the
     right and left sides of XUat t e. *)
  Theorem dist_xu_runs : forall s0 p e, InvF s0 ->
    nF (dF (p ++ [DE e]) s0) (reg e) = f (reg e) (nF (dF p s0)) (sig e (dF p s0 (reg e))) /\
    nF (dF (p ++ map DP o ++ [DE e]) s0) (reg e) =
      f (reg e) (nF (dF p s0)) (sig e (f (reg e) (nF (dF p s0)) (dF p s0 (reg e)))).
  Proof.
    intros s0 p e Hi. set (t := dF p s0).
    assert (It : InvF t) by (apply drun_inv; exact Hi).
    split.
    - rewrite drun_app. change (dF [DE e] (dF p s0)) with (evF e t). apply N_ev_at. exact It.
    - rewrite drun_app, drun_app, drun_props. change (dF [DE e] (frF o (dF p s0))) with (evF e (frF o t)).
      assert (Ifr : InvF (frF o t)) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact It).
      assert (Fr : feqF (frF o t) (nF t))
        by (apply feq_sym; apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact It).
      assert (In_ : InvF (nF t)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact It).
      assert (Nn : feqF (nF (frF o t)) (nF t)).
      { eapply feq_trans; [apply (N_ext _ _ _ _ _ _ _ _ _ HC); exact Fr |].
        apply (N_self _ _ _ _ _ _ _ _ _ HC); [exact In_ | apply (N_cons _ _ _ _ _ _ _ _ _ HC); exact It]. }
      rewrite (N_ev_at e _ Ifr). rewrite (f_ext _ _ _ _ Nn). rewrite (Fr (reg e)).
      rewrite (N_at t (reg e) It (c_reg _ _ _ _ _ _ _ _ _ HC e)). reflexivity.
  Qed.

  Theorem dist_xu_diverge : forall s0 p e, InvF s0 -> Forall okF p -> ~ XUat (dF p s0) e ->
    Forall okF (p ++ [DE e]) /\ Forall okF (p ++ map DP o ++ [DE e]) /\
    evsF (p ++ [DE e]) = evsF (p ++ map DP o ++ [DE e]) /\
    nF (dF (p ++ [DE e]) s0) (reg e) <> nF (dF (p ++ map DP o ++ [DE e]) s0) (reg e).
  Proof.
    intros s0 p e Hi Hp Hn.
    split; [apply ok_app; [exact Hp | constructor; [exact Logic.I | constructor]] |].
    split; [apply ok_app; [exact Hp | apply ok_app; [exact ok_props | constructor; [exact Logic.I | constructor]]] |].
    split; [rewrite !evs_app, evs_props; reflexivity |].
    destruct (dist_xu_runs s0 p e Hi) as [A B]. rewrite A, B. intro H. apply Hn. symmetry. exact H.
  Qed.

  Theorem lcc_runs : forall s0 p e1 e2, InvF s0 -> reg e1 = reg e2 ->
    nF (dF (p ++ [DE e1; DE e2]) s0) (reg e1) =
    f (reg e1) (nF (dF p s0)) (sig e2 (sig e1 (dF p s0 (reg e1)))).
  Proof.
    intros s0 p e1 e2 Hi E12. set (t := dF p s0).
    assert (It : InvF t) by (apply drun_inv; exact Hi).
    rewrite drun_app. change (dF [DE e1; DE e2] (dF p s0)) with (evF e2 (evF e1 t)).
    assert (I1 : InvF (evF e1 t)) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact It).
    assert (I2 : InvF (evF e2 (evF e1 t))) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact I1).
    rewrite (N_at _ (reg e1) I2 (c_reg _ _ _ _ _ _ _ _ _ HC e1)).
    rewrite (f_N_ev e2 _ (reg e1) _ E12), (f_N_ev e1 t (reg e1) _ eq_refl).
    rewrite (evstep_at V E reg sig e2 _ (reg e1) E12), (evstep_at V E reg sig e1 t (reg e1) eq_refl).
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Necessity and sufficiency.                                                          *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem dist_xur_nec : forall s0, InvF s0 -> DistConv s0 -> XUR s0.
  Proof.
    intros s0 Hi Hd p e Hp. unfold XUat.
    destruct (dist_xu_runs s0 p e Hi) as [A B].
    assert (Ok1 : Forall okF (p ++ [DE e]))
      by (apply ok_app; [exact Hp | constructor; [exact Logic.I | constructor]]).
    assert (Ok2 : Forall okF (p ++ map DP o ++ [DE e]))
      by (apply ok_app; [exact Hp | apply ok_app; [exact ok_props | constructor; [exact Logic.I | constructor]]]).
    assert (Ev : evsF (p ++ [DE e]) = evsF (p ++ map DP o ++ [DE e]))
      by (rewrite !evs_app, evs_props; reflexivity).
    pose proof (Hd _ _ Ok1 Ok2 (eq_rect _ (fun l => tequiv IfedF (evsF (p ++ [DE e])) l)
                                   (teq_refl IfedF _) _ Ev) (reg e)) as H.
    rewrite A, B in H. symmetry. exact H.
  Qed.

  Theorem dist_lcc_nec : forall s0, InvF s0 -> DistConv s0 -> LCCR s0.
  Proof.
    intros s0 Hi Hd p e1 e2 Hp E12 Hab. unfold LCCat.
    assert (Ok : forall a b, Forall okF (p ++ [DE a; DE b]))
      by (intros; apply ok_app; [exact Hp | repeat constructor]).
    assert (Ht : tequiv IfedF (evsF (p ++ [DE e1; DE e2])) (evsF (p ++ [DE e2; DE e1]))).
    { rewrite !evs_app. apply (teq_swap IfedF (evsF p) e1 e2 []). right. exact Hab. }
    pose proof (Hd _ _ (Ok e1 e2) (Ok e2 e1) Ht (reg e1)) as H.
    pose proof (lcc_runs s0 p e1 e2 Hi E12) as A.
    pose proof (lcc_runs s0 p e2 e1 Hi (eq_sym E12)) as B. rewrite <- E12 in B.
    rewrite A, B in H. exact H.
  Qed.

  Lemma dist_tc : forall s0, InvF s0 -> DistConv s0 -> XUR s0 -> TC (nF s0).
  Proof.
    intros s0 Hi Hd Hx es1 es2 H.
    pose proof (dist_flush s0 Hi Hx (map DE es1) (ok_evs es1)) as A1. rewrite evs_evs in A1.
    pose proof (dist_flush s0 Hi Hx (map DE es2) (ok_evs es2)) as A2. rewrite evs_evs in A2.
    assert (Ht : tequiv IfedF (evsF (map DE es1)) (evsF (map DE es2))) by (rewrite !evs_evs; exact H).
    eapply feq_trans; [apply feq_sym; exact A1 |].
    eapply feq_trans; [exact (Hd _ _ (ok_evs es1) (ok_evs es2) Ht) | exact A2].
  Qed.

  Lemma dist_suff : forall s0, InvF s0 -> XUR s0 -> TC (nF s0) -> DistConv s0.
  Proof.
    intros s0 Hi Hx Ht w1 w2 H1 H2 Hq.
    eapply feq_trans; [exact (dist_flush s0 Hi Hx w1 H1) |].
    eapply feq_trans; [exact (Ht _ _ Hq) | apply feq_sym; exact (dist_flush s0 Hi Hx w2 H2)].
  Qed.

  (* Headline (FedMachine form): distributed convergence is reachable XU plus FedMachine
     convergence from the flushed start. *)
  Theorem dist_exact_tc : forall s0, InvF s0 -> (DistConv s0 <-> XUR s0 /\ TC (nF s0)).
  Proof.
    intros s0 Hi. split.
    - intros Hd. assert (Hx : XUR s0) by (apply dist_xur_nec; assumption).
      split; [exact Hx | apply dist_tc; assumption].
    - intros [Hx Ht]. apply dist_suff; assumption.
  Qed.

  (* The FedMachine state after events q from the flushed start is reached, up to feq, by the
     distributed run "events q, then a flush". *)
  Lemma reach_flush : forall s0, InvF s0 -> XUR s0 ->
    forall q, feqF (dF (map DE q ++ map DP o) s0) (rF q (nF s0)).
  Proof.
    intros s0 Hi Hx q. rewrite drun_app, drun_props.
    assert (Iq : InvF (dF (map DE q) s0)) by (apply drun_inv; exact Hi).
    eapply feq_trans; [apply feq_sym; apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact Iq |].
    pose proof (dist_flush s0 Hi Hx (map DE q) (ok_evs q)) as A. rewrite evs_evs in A. exact A.
  Qed.

  Lemma ok_reach : forall q l, Forall okF l -> Forall okF ((map DE q ++ map DP o) ++ l).
  Proof. intros q l Hl. apply ok_app; [apply ok_app; [apply ok_evs | exact ok_props] | exact Hl]. Qed.

  (* Reachable XU already contains the FedMachine's C1 at reachable witnesses. *)
  Theorem xur_c1r1 : forall s0, InvF s0 -> XUR s0 -> C1R1f (nF s0).
  Proof.
    intros s0 Hi Hx q e a Ne. unfold C1at.
    set (s := rF q (nF s0)). set (u := dF (map DE q ++ map DP o) s0).
    assert (Hu : feqF u s) by (apply reach_flush; assumption).
    pose proof (Hx ((map DE q ++ map DP o) ++ [DE a]) e
                  (ok_reach q [DE a] ltac:(repeat constructor))) as X.
    rewrite drun_app in X. change (dF [DE a] (dF (map DE q ++ map DP o) s0)) with (evF a u) in X.
    unfold XUat in X.
    assert (Na : feqF (nF (evF a u)) (aF a s)).
    { unfold applyF. apply (N_ext _ _ _ _ _ _ _ _ _ HC). apply (evstep_ext V E reg sig). exact Hu. }
    rewrite !(f_ext (reg e) _ _ _ Na) in X.
    rewrite (evstep_off V E reg sig a u (reg e) (fun H => Ne (eq_sym H))) in X.
    rewrite (Hu (reg e)) in X. exact X.
  Qed.

  (* Headline: the exact condition, in terms of the FedMachine's C2. *)
  Theorem dist_exact : forall s0, InvF s0 -> (DistConv s0 <-> XUR s0 /\ C2Rf (nF s0)).
  Proof.
    intros s0 Hi.
    assert (In_ : InvF (nF s0)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Cn : ConsF (nF s0)) by (apply (N_cons _ _ _ _ _ _ _ _ _ HC); exact Hi).
    rewrite (dist_exact_tc s0 Hi). split.
    - intros [Hx Ht]. split; [exact Hx |].
      exact (proj2 (proj1 (fed_exact _ _ _ _ _ _ _ _ _ _ HC (nF s0) In_ Cn) Ht)).
    - intros [Hx H2]. split; [exact Hx |].
      apply (proj2 (fed_exact _ _ _ _ _ _ _ _ _ _ HC (nF s0) In_ Cn)).
      split; [apply xur_c1r1; assumption | exact H2].
  Qed.

  Lemma xur_lcc_c2r : forall s0, InvF s0 -> XUR s0 -> LCCR s0 -> C2Rf (nF s0).
  Proof.
    intros s0 Hi Hx Hl q e1 e2 E12 Hab. unfold C2at.
    set (s := rF q (nF s0)). set (w := map DE q ++ map DP o). set (u := dF w s0).
    assert (Hu : feqF u s) by (apply reach_flush; assumption).
    assert (In_ : InvF (nF s0)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Is : InvF s) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact In_).
    assert (Cs : ConsF s)
      by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); [exact In_ | apply (N_cons _ _ _ _ _ _ _ _ _ HC); exact Hi]).
    assert (Nu : feqF (nF u) s).
    { eapply feq_trans; [apply (N_ext _ _ _ _ _ _ _ _ _ HC); exact Hu |].
      apply (N_self _ _ _ _ _ _ _ _ _ HC); assumption. }
    assert (Okw : forall a, Forall okF (w ++ [DE a])) by (intro; apply ok_reach; repeat constructor).
    pose proof (Hx (w ++ [DE e1]) e2 (Okw e1)) as A. rewrite drun_app in A.
    change (dF [DE e1] (dF w s0)) with (evF e1 u) in A. unfold XUat in A.
    rewrite <- E12 in A.
    rewrite !(f_N_ev e1 u (reg e1) _ eq_refl) in A. rewrite !(f_ext (reg e1) _ _ _ Nu) in A.
    rewrite (evstep_at V E reg sig e1 u (reg e1) eq_refl) in A. rewrite (Hu (reg e1)) in A.
    pose proof (Hx (w ++ [DE e2]) e1 (Okw e2)) as B. rewrite drun_app in B.
    change (dF [DE e2] (dF w s0)) with (evF e2 u) in B. unfold XUat in B.
    rewrite !(f_N_ev e2 u (reg e1) _ E12) in B. rewrite !(f_ext (reg e1) _ _ _ Nu) in B.
    rewrite (evstep_at V E reg sig e2 u (reg e1) E12) in B. rewrite (Hu (reg e1)) in B.
    assert (Ok0 : Forall okF w) by (unfold w; apply ok_app; [apply ok_evs | exact ok_props]).
    pose proof (Hl w e1 e2 Ok0 E12 Hab) as C.
    change (dF w s0) with u in C. unfold LCCat in C.
    rewrite !(f_ext (reg e1) _ _ _ Nu) in C. rewrite (Hu (reg e1)) in C.
    rewrite A, B. exact C.
  Qed.

  (* Headline: the exact condition, as the reachable forms of XU and of each registry's CC. *)
  Theorem dist_exact_local : forall s0, InvF s0 -> (DistConv s0 <-> XUR s0 /\ LCCR s0).
  Proof.
    intros s0 Hi. split.
    - intros Hd. split; [apply dist_xur_nec | apply dist_lcc_nec]; assumption.
    - intros [Hx Hl]. apply (proj2 (dist_exact s0 Hi)). split; [exact Hx |].
      apply xur_lcc_c2r; assumption.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* (a) XU is sufficient: the existing results as corollaries.                          *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma xu_xur : XU V f valid E reg sig -> forall s0, InvF s0 -> XUR s0.
  Proof.
    intros HX s0 Hi p e _. unfold XUat. apply HX.
    - apply (N_inv _ _ _ _ _ _ _ _ _ HC). apply drun_inv. exact Hi.
    - apply drun_inv. exact Hi.
  Qed.

  Theorem xu_exact_condition : XU V f valid E reg sig -> LocalCC V valid E reg sig I ->
    forall s0, InvF s0 -> XUR s0 /\ C2Rf (nF s0) /\ LCCR s0.
  Proof.
    intros HX HL s0 Hi.
    assert (Hx : XUR s0) by (apply xu_xur; assumption).
    assert (Hl : LCCR s0).
    { intros p e1 e2 _ E12 Hab. unfold LCCat. rewrite (HL e1 e2 _ E12 Hab); [reflexivity |].
      apply drun_inv; exact Hi. }
    split; [exact Hx |]. split; [apply xur_lcc_c2r; assumption | exact Hl].
  Qed.

  Theorem dist_interleavings_converge_recovered :
    XU V f valid E reg sig -> LocalCC V valid E reg sig I -> forall s0, InvF s0 -> DistConv s0.
  Proof.
    intros HX HL s0 Hi. destruct (xu_exact_condition HX HL s0 Hi) as [Hx [_ Hl]].
    apply (proj2 (dist_exact_local s0 Hi)). split; assumption.
  Qed.

  (* XU + C2 (gsm's ProjectionSafe XU with Build's C2) suffice: no LocalCC needed. *)
  Theorem dist_xu_c2_converge :
    XU V f valid E reg sig -> C2 V f valid E reg sig I -> forall s0, InvF s0 -> DistConv s0.
  Proof.
    intros HX H2 s0 Hi. apply (proj2 (dist_exact s0 Hi)). split; [apply xu_xur; assumption |].
    apply (static_c2_reach _ _ _ _ _ _ _ _ _ _ HC H2);
      [apply (N_inv _ _ _ _ _ _ _ _ _ HC) | apply (N_cons _ _ _ _ _ _ _ _ _ HC)]; exact Hi.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* (c) Distributed convergence implies FedMachine convergence.                         *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem dist_implies_fed_flush : forall s0, InvF s0 -> DistConv s0 ->
    TC (nF s0) /\ C1R1f (nF s0) /\ C2Rf (nF s0).
  Proof.
    intros s0 Hi Hd.
    assert (Hx : XUR s0) by (apply dist_xur_nec; assumption).
    assert (Ht : TC (nF s0)) by (apply dist_tc; assumption).
    split; [exact Ht |].
    apply (fed_exact _ _ _ _ _ _ _ _ _ _ HC (nF s0));
      [apply (N_inv _ _ _ _ _ _ _ _ _ HC) | apply (N_cons _ _ _ _ _ _ _ _ _ HC) | ]; assumption.
  Qed.

  Theorem dist_implies_fed : forall s0, InvF s0 -> ConsF s0 -> DistConv s0 ->
    TC s0 /\ C1R1f s0 /\ C2Rf s0.
  Proof.
    intros s0 Hi Hc Hd.
    assert (Ht : TC s0).
    { intros es1 es2 H.
      assert (Ns : feqF (nF s0) s0) by (apply (N_self _ _ _ _ _ _ _ _ _ HC); assumption).
      pose proof (proj1 (dist_implies_fed_flush s0 Hi Hd) es1 es2 H) as T.
      eapply feq_trans; [apply (runF_ext _ _ _ _ _ _ _ _ _ HC); apply feq_sym; exact Ns |].
      eapply feq_trans; [exact T |]. apply (runF_ext _ _ _ _ _ _ _ _ _ HC). exact Ns. }
    split; [exact Ht |]. apply (fed_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi Hc). exact Ht.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Every valid start; every consistent start; root sources.                            *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma C2at_feq : forall s s' e1 e2, feqF s s' -> C2atf s e1 e2 -> C2atf s' e1 e2.
  Proof.
    intros s s' e1 e2 H C. unfold C2at in *. rewrite !(f_ext (reg e1) s' s _ (feq_sym _ _ _ H)).
    rewrite <- (H (reg e1)). exact C.
  Qed.

  Lemma c2g_c2r : C2G -> forall s0, InvF s0 -> C2Rf (nF s0).
  Proof.
    intros H s0 Hi p e1 e2 E12 Hab.
    assert (In_ : InvF (nF s0)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    apply H; [apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact In_
             | apply (runF_cons _ _ _ _ _ _ _ _ _ HC); [exact In_ | apply (N_cons _ _ _ _ _ _ _ _ _ HC); exact Hi]
             | exact E12 | exact Hab].
  Qed.

  Lemma c2r_c2g_at : forall s e1 e2, InvF s -> ConsF s -> reg e1 = reg e2 -> I e1 e2 ->
    C2Rf (nF s) -> C2atf s e1 e2.
  Proof.
    intros s e1 e2 Hi Hc E12 Hab H.
    apply (C2at_feq (nF s)); [apply (N_self _ _ _ _ _ _ _ _ _ HC); assumption |].
    exact (H [] e1 e2 E12 Hab).
  Qed.

  Theorem dist_exact_global : (forall s0, InvF s0 -> DistConv s0) <-> XUG /\ C2G.
  Proof.
    split.
    - intros H. split.
      + intros s e Hs. exact (dist_xur_nec s Hs (H s Hs) [] e ltac:(constructor)).
      + intros s e1 e2 Hi Hc E12 Hab. apply c2r_c2g_at; try assumption.
        exact (proj2 (proj1 (dist_exact s Hi) (H s Hi))).
    - intros [Hx H2] s0 Hi. apply (proj2 (dist_exact s0 Hi)). split.
      + intros p e _. apply Hx. apply drun_inv. exact Hi.
      + apply c2g_c2r; assumption.
  Qed.

  Theorem dist_exact_consistent :
    (forall s0, InvF s0 -> ConsF s0 -> DistConv s0) <->
    (forall s0, InvF s0 -> ConsF s0 -> XUR s0) /\ C2G.
  Proof.
    split.
    - intros H. split.
      + intros s0 Hi Hc. apply dist_xur_nec; [exact Hi | apply H; assumption].
      + intros s e1 e2 Hi Hc E12 Hab. apply c2r_c2g_at; try assumption.
        exact (proj2 (proj1 (dist_exact s Hi) (H s Hi Hc))).
    - intros [Hx H2] s0 Hi Hc. apply (proj2 (dist_exact s0 Hi)). split.
      + apply Hx; assumption.
      + apply c2g_c2r; assumption.
  Qed.

  Lemma src_ne : forall e k, In k (src (reg e)) -> k <> reg e.
  Proof.
    intros e k Hk E'.
    destruct (split_at _ _ _ _ _ _ _ _ _ HC (reg e) (c_reg _ _ _ _ _ _ _ _ _ HC e))
      as [o1 [L [Ho [Hj Hs]]]].
    apply (Hs k Hk). rewrite E'. exact Hj.
  Qed.

  (* With root sources, the flushed sources of a target are its sources' own states. *)
  Lemma f_root_upd : RootSrc -> forall e z b x, InvF z -> valid (reg e) b ->
    f (reg e) (nF (upd V z (reg e) b)) x = f (reg e) z x.
  Proof.
    intros HR e z b x Hz Hb.
    assert (Iu : InvF (upd V z (reg e) b)).
    { intro k. unfold upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply Hz].
      apply Nat.eqb_eq in Ek. subst k. exact Hb. }
    apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk.
    assert (Ne : k <> reg e) by (apply src_ne; exact Hk).
    assert (Hn : nF (upd V z (reg e) b) k = upd V z (reg e) b k).
    { destruct (in_dec Nat.eq_dec k o) as [Ko | Ko].
      - rewrite (N_at _ k Iu Ko). apply (HR e k Hk).
      - apply N_out; assumption. }
    rewrite Hn. apply upd_neq. exact Ne.
  Qed.

  Theorem xug_iff_xu : RootSrc -> (XUG <-> XU V f valid E reg sig).
  Proof.
    intros HR. split.
    - intros H e z b Hz Hb.
      pose proof (H (upd V z (reg e) b) e) as X.
      assert (Iu : InvF (upd V z (reg e) b)).
      { intro k. unfold upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply Hz].
        apply Nat.eqb_eq in Ek. subst k. exact Hb. }
      specialize (X Iu). unfold XUat in X. rewrite !(f_root_upd HR e z b _ Hz Hb) in X.
      rewrite upd_eq in X. exact X.
    - intros H s e Hs. unfold XUat. apply H; [apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact Hs | apply Hs].
  Qed.

  Theorem c2g_iff_c2 : RootSrc -> (C2G <-> C2 V f valid E reg sig I).
  Proof.
    intros HR. split.
    - intros H e1 e2 z b E12 Hab Hz Hb Hcb.
      set (u := upd V z (reg e1) b).
      assert (Iu : InvF u).
      { intro k. unfold u, upd. destruct (Nat.eqb k (reg e1)) eqn:Ek; [| apply Hz].
        apply Nat.eqb_eq in Ek. subst k. exact Hb. }
      assert (Fz : forall x, f (reg e1) (nF u) x = f (reg e1) z x)
        by (intro; apply f_root_upd; assumption).
      assert (Su : nF u (reg e1) = b).
      { rewrite (N_at u (reg e1) Iu (c_reg _ _ _ _ _ _ _ _ _ HC e1)). rewrite Fz.
        unfold u. rewrite upd_eq. symmetry. exact Hcb. }
      pose proof (H (nF u) e1 e2 (N_inv _ _ _ _ _ _ _ _ _ HC u Iu)
                    (N_cons _ _ _ _ _ _ _ _ _ HC u Iu) E12 Hab) as C.
      unfold C2at in C. rewrite !Fz, Su in C. exact C.
    - intros H s e1 e2 Hi Hc E12 Hab. unfold C2at.
      apply H; [exact E12 | exact Hab | exact Hi | apply Hi |].
      apply Hc. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  (* Headline (every valid start, root sources): gsm's static XU + C2 check is exact. *)
  Theorem dist_global_exact_roots : RootSrc ->
    ((forall s0, InvF s0 -> DistConv s0) <-> XU V f valid E reg sig /\ C2 V f valid E reg sig I).
  Proof.
    intros HR. rewrite dist_exact_global, (xug_iff_xu HR), (c2g_iff_c2 HR). reflexivity.
  Qed.

  End WithCommon.
End DistExact.

(* ========================================================================================= *)
(* Non-vacuity: the supply chain satisfies every form of the exact condition.                *)
(* ========================================================================================= *)

Theorem supply_dist_exact : forall s0, Inv (bool * nat) sp_valid s0 ->
  XUR (bool * nat) sp_f sp_rho sev sp_reg sp_sig [0; 1] s0 /\
  C2R (bool * nat) sp_f sp_rho sev sp_reg sp_sig sp_I [0; 1]
      (N (bool * nat) sp_f sp_rho [0; 1] s0) /\
  LCCR (bool * nat) sp_f sp_rho sev sp_reg sp_sig sp_I [0; 1] s0 /\
  DistConv (bool * nat) sp_f sp_rho sev sp_reg sp_sig sp_I [0; 1] s0.
Proof.
  intros s0 Hi. destruct supply_instance as [HC [HX [HL _]]].
  destruct (xu_exact_condition _ _ _ _ _ _ _ _ _ _ HC HX HL s0 Hi) as [A [B C]].
  split; [exact A |]. split; [exact B |]. split; [exact C |].
  exact (dist_interleavings_converge_recovered _ _ _ _ _ _ _ _ _ _ HC HX HL s0 Hi).
Qed.

(* ========================================================================================= *)
(* (b) The exact condition is strictly weaker than XU: gsm's `levels` federation.            *)
(* Registry 0: (on, _), on <= 1; Flip sets on. Registry 1: (level, count), level <= 3,        *)
(* count <= 2; the morphism writes level := min on 1, so images are levels 0 and 1. Bump     *)
(* increments count only at level = 3, which no image produces and no event writes. XU fails  *)
(* at the valid stale state (3, 0); no run from a start whose level is not 3 reaches it.      *)
(* ========================================================================================= *)

Definition lv_valid (k : nat) (x : nat * nat) : Prop :=
  match k with 1 => fst x <= 3 /\ snd x <= 2 | _ => fst x <= 1 end.

Definition lv_f (k : nat) (z : nat -> nat * nat) (x : nat * nat) : nat * nat :=
  match k with 1 => (Nat.min (fst (z 0)) 1, snd x) | _ => x end.

Definition lv_rho (_ : nat) (x : nat * nat) : nat * nat := x.

Inductive lev : Type := Flip | Bump.

Definition lv_reg (e : lev) : nat := match e with Flip => 0 | Bump => 1 end.

Definition lv_sig (e : lev) (x : nat * nat) : nat * nat :=
  match e with
  | Flip => (1, snd x)
  | Bump => if Nat.eqb (fst x) 3 then (fst x, Nat.min (S (snd x)) 2) else x
  end.

Definition lv_I (_ _ : lev) : Prop := True.

(* A stale start: the target sits at the level no image produces. *)
Definition lv_stale (k : nat) : nat * nat := match k with 1 => (3, 0) | _ => (0, 0) end.

Lemma lv_common : Common (nat * nat) src2 lv_f lv_valid lv_rho lev lv_reg lv_sig [0; 1].
Proof.
  constructor.
  - intros [| [| j]] z1 z2 x H; simpl; try reflexivity.
    rewrite (H 0); [reflexivity | left; reflexivity].
  - exact topo2.
  - intros [| [| j]] z [a c] Hz Hx; simpl in *; try exact Hx.
    destruct Hx as [_ Hc]. split; [lia | exact Hc].
  - intros [| [| j]] z z' x _ _ _; reflexivity.
  - intros; reflexivity.
  - intros [] [a c] Hx; simpl in *; [lia |].
    destruct (Nat.eqb a 3); simpl; [split; lia | exact Hx].
  - intros []; simpl; tauto.
Qed.

Lemma lv_reach : forall w s0, fst (s0 1) <> 3 ->
  fst (drun (nat * nat) lv_f lev lv_reg lv_sig w s0 1) <> 3.
Proof.
  induction w as [| a w IH]; intros s0 H; [exact H |].
  simpl. apply IH. destruct a as [[] | j]; simpl.
  - unfold evstep, upd. simpl. exact H.
  - unfold evstep, upd. simpl. destruct (s0 1) as [l c]. simpl in *.
    destruct (Nat.eqb_spec l 3); [contradiction | exact H].
  - unfold fstep, upd. destruct (Nat.eqb 1 j) eqn:Ej; [| exact H].
    apply Nat.eqb_eq in Ej. subst j. simpl. lia.
Qed.

Lemma lv_xur : forall s0, fst (s0 1) <> 3 -> XUR (nat * nat) lv_f lv_rho lev lv_reg lv_sig [0; 1] s0.
Proof.
  intros s0 H p e _. pose proof (lv_reach p s0 H) as Ht.
  unfold XUat. set (t := drun (nat * nat) lv_f lev lv_reg lv_sig p s0) in *.
  set (n := N (nat * nat) lv_f lv_rho [0; 1] t).
  destruct e; [reflexivity |]. change (lv_reg Bump) with 1.
  destruct (t 1) as [l c]. simpl in Ht.
  assert (E1 : Nat.eqb (Nat.min (fst (n 0)) 1) 3 = false) by (apply Nat.eqb_neq; lia).
  assert (E2 : Nat.eqb l 3 = false) by (apply Nat.eqb_neq; exact Ht).
  cbn [lv_f lv_sig lv_reg fst snd]. rewrite E1, E2. reflexivity.
Qed.

Lemma lv_c2r : forall s, C2R (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] s.
Proof. intros s p [] [] E' _; simpl in E'; try discriminate; reflexivity. Qed.

Theorem levels_exact_not_xu :
  Common (nat * nat) src2 lv_f lv_valid lv_rho lev lv_reg lv_sig [0; 1] /\
  C1 (nat * nat) lv_f lv_valid lev lv_reg lv_sig /\
  C2 (nat * nat) lv_f lv_valid lev lv_reg lv_sig lv_I /\
  ~ XU (nat * nat) lv_f lv_valid lev lv_reg lv_sig /\
  RootSrc (nat * nat) src2 lv_f lev lv_reg /\
  (forall s0, Inv (nat * nat) lv_valid s0 -> fst (s0 1) <> 3 ->
     XUR (nat * nat) lv_f lv_rho lev lv_reg lv_sig [0; 1] s0 /\
     C2R (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] (N (nat * nat) lv_f lv_rho [0; 1] s0) /\
     DistConv (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] s0) /\
  (forall s0, Inv (nat * nat) lv_valid s0 -> Cons (nat * nat) lv_f [0; 1] s0 ->
     DistConv (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] s0) /\
  Inv (nat * nat) lv_valid lv_stale /\
  ~ DistConv (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] lv_stale.
Proof.
  pose proof lv_common as HC.
  assert (Good : forall s0, Inv (nat * nat) lv_valid s0 -> fst (s0 1) <> 3 ->
     XUR (nat * nat) lv_f lv_rho lev lv_reg lv_sig [0; 1] s0 /\
     C2R (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] (N (nat * nat) lv_f lv_rho [0; 1] s0) /\
     DistConv (nat * nat) lv_f lv_rho lev lv_reg lv_sig lv_I [0; 1] s0).
  { intros s0 Hi H. assert (Hx := lv_xur s0 H). assert (H2 := lv_c2r (N (nat * nat) lv_f lv_rho [0; 1] s0)).
    split; [exact Hx |]. split; [exact H2 |].
    apply (dist_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi). split; assumption. }
  split; [exact HC |].
  split.
  { intros e z z' [l c] _ _ _ Hb. destruct e; [reflexivity |]. simpl in Hb |- *.
    injection Hb as Hl. rewrite Hl.
    destruct (Nat.eqb_spec (Nat.min (fst (z' 0)) 1) 3) as [E' | _]; [lia |].
    destruct (Nat.eqb_spec (Nat.min (fst (z 0)) 1) 3) as [E' | _]; [lia | reflexivity]. }
  split; [intros [] [] z b E' _ _ _ _; simpl in E'; try discriminate; reflexivity |].
  split.
  { intro HX.
    pose proof (HX Bump (fun _ => (0, 0)) (3, 0)) as H.
    assert (Hz : Inv (nat * nat) lv_valid (fun _ => (0, 0))) by (intros [| [| k]]; simpl; lia).
    assert (Hb : lv_valid (lv_reg Bump) (3, 0)) by (simpl; lia).
    specialize (H Hz Hb). vm_compute in H. discriminate H. }
  split.
  { intros [] k Hk t x; simpl in Hk; [contradiction |]. destruct Hk as [<- | []]. reflexivity. }
  split; [exact Good |].
  split.
  { intros s0 Hi Hc. apply Good; [exact Hi |].
    pose proof (Hc 1 (or_intror (or_introl eq_refl))) as H1. simpl in H1.
    rewrite H1. simpl. lia. }
  split; [intros [| [| k]]; simpl; lia |].
  intro Hd.
  assert (Ok1 : Forall (okact lev [0; 1]) [DEv lev Bump]) by (repeat constructor).
  assert (Ok2 : Forall (okact lev [0; 1]) [DProp lev 1; DEv lev Bump])
    by (repeat constructor; simpl; tauto).
  pose proof (Hd _ _ Ok1 Ok2 (teq_refl _ [Bump]) 1) as H. vm_compute in H. discriminate H.
Qed.

(* ========================================================================================= *)
(* (c) The converse fails: FedMachine convergence does not imply distributed convergence.     *)
(* The federation of fed_grs_c1_c2_insufficient: target (shared, local), only image shared = *)
(* false, both events flip shared and add it into local. C1 and C2 hold, so every FedMachine  *)
(* order converges from every consistent start; but from the consistent start (false, false) *)
(* the runs G1; G2 and G1; propagate; G2 (the SAME event sequence) differ after the flush.    *)
(* ========================================================================================= *)

Definition gg_start (_ : nat) : bool * bool := (false, false).

Theorem dist_strictly_stronger_than_fed :
  Common (bool * bool) src2 (pf (bool * bool) bool bool snd pair src2 gg_G) gg_valid gg_rho gev gg_reg
    (gsig (bool * bool) gg_rho gev gg_reg gg_ap) [0; 1] /\
  (forall s0, Inv (bool * bool) gg_valid s0 ->
     Cons (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) [0; 1] s0 ->
     TraceConv (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho gev gg_reg
       (gsig (bool * bool) gg_rho gev gg_reg gg_ap) (Itot gev) [0; 1] s0) /\
  Inv (bool * bool) gg_valid gg_start /\
  Cons (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) [0; 1] gg_start /\
  ~ XUR (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho gev gg_reg
      (gsig (bool * bool) gg_rho gev gg_reg gg_ap) [0; 1] gg_start /\
  ~ DistConv (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho gev gg_reg
      (gsig (bool * bool) gg_rho gev gg_reg gg_ap) (Itot gev) [0; 1] gg_start /\
  N (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho [0; 1]
    (drun (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gev gg_reg
       (gsig (bool * bool) gg_rho gev gg_reg gg_ap) [DEv gev G1; DEv gev G2] gg_start) 1 = (false, true) /\
  N (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho [0; 1]
    (drun (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gev gg_reg
       (gsig (bool * bool) gg_rho gev gg_reg gg_ap) [DEv gev G1; DProp gev 1; DEv gev G2] gg_start) 1
    = (false, false).
Proof.
  pose proof gg_paper as HT. pose proof (tree_net _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT) as HP.
  assert (HC := paper_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg_vdec HP).
  assert (Hi : Inv (bool * bool) gg_valid gg_start) by (intro k; exact Logic.I).
  assert (Nx : ~ XUR (bool * bool) (pf (bool * bool) bool bool snd pair src2 gg_G) gg_rho gev gg_reg
                 (gsig (bool * bool) gg_rho gev gg_reg gg_ap) [0; 1] gg_start).
  { intro H. pose proof (H [DEv gev G1] G2 ltac:(repeat constructor)) as X.
    unfold XUat in X. vm_compute in X. discriminate X. }
  split; [exact HC |].
  split.
  { intros s0 Hs Hc es1 es2 Ht.
    exact (fed_interleavings_converge _ _ _ _ _ _ _ _ _ _ HC gg_c1 gg_c2 es1 es2 Ht s0 Hs Hc). }
  split; [exact Hi |].
  split; [intros j [<- | [<- | []]]; reflexivity |].
  split; [exact Nx |].
  split; [intro Hd; apply Nx; exact (dist_xur_nec _ _ _ _ _ _ _ _ _ _ HC gg_start Hi Hd) |].
  split; vm_compute; reflexivity.
Qed.
