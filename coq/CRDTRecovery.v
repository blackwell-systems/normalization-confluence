(* CRDTRecovery.v: strong eventual consistency (SEC) of CRDTs, a theorem from outside the
   repository, recovered with the framework kernels frozen. Axiom-free.

   The outside theorems (statements checked against the sources).
   - Shapiro, Preguica, Baquero, Zawirski, "Conflict-free Replicated Data Types", SSS 2011, LNCS
     6976, pp. 386-400; proofs in INRIA Research Report RR-7687 (July 2011, hal inria-00609399).
     Theorem 2 (RR-7687 Theorem 2.2, CmRDT): assuming causal delivery of updates and method
     termination, an op-based object whose concurrent updates commute (Definition 6: at every
     reachable replica state where both are enabled) is SEC. Theorem 1 (RR-7687 Theorem 2.1,
     CvRDT): assuming eventual delivery and termination, a state-based object with the monotonic
     semilattice property (Definition 4: states a join-semilattice, merge is the least upper
     bound, updates inflationary s <= s . u) is SEC. Strong convergence (Definition 3): replicas
     with equal causal histories have equivalent states. The state-based causal history
     (Definition 1) adds an update to the local history and unions the two histories at a merge.
   - Gomes, Kleppmann, Mulligan, Beresford, "Verifying strong eventual consistency in
     distributed systems", OOPSLA 2017 (PACMPL 1, Article 109), Section 4.3, theorem
     convergence: two lists of distinct operations, hb-consistent, with the same set, in which
     concurrent operations commute as Kleisli compositions of partial state transformers, have
     the same interpretation. hb is a strict partial order in their locale.

   Only strong convergence is recovered; eventual delivery and termination are liveness
   assumptions of Shapiro's theorems and are not modeled here.

   The kernels used, all unchanged:
     CanonicalExecution.StateDescent, CanonicalExecution.gact / grun (the governed step N o act),
     CanonicalExecution.normalization_descent,
     PresentedExecution.state_side_transfer (state descent enters through the semantics),
     PresentedExecution.local_exact_all (P1), PresentedExecution.cg_gen, cg_prefix, cg_peq,
     msem_eq_resp (the causal presentation), CanonicalInstances.causal_adequate (adequacy of
     that presentation), PresentedExecution.alo_exact_recovered (P1 on at-least-once delivery).

   1. Op-based (section OpBased). N := id. State descent is reflexivity (nid_state_descent), so
      the normalized raw semantics is the governed one (opsec_state_side, state_side_transfer).
      History descent is the causal presentation: OpSEC s0 <-> PInv (opsec_history_descent,
      causal_adequate and cg_peq); P1 (local_exact_all) reduces it to the seeds
      (opsec_seeds); the seeds are raw commutation of concurrent pairs at causally deliverable
      points (seeds_concurrent). Together opsec_exact: OpSEC s0 <-> ConcCommuteReach s0, and
      from every start opsec_global_exact (hb irreflexive): SEC from every start iff concurrent
      operations commute at every state. Shapiro's sufficient condition is shapiro_cmrdt_sec.
   2. Gomes et al.'s convergence theorem with their definitions (section Gomes): partial
      operations, Kleisli composition, hb-consistent lists, concurrent-ops-commute.
      gomes_convergence, through opsec_exact on option states.
   3. State-based (sections Payloads and Replicas). Shapiro's replica model: replicas,
      updates, binary merges, causal histories. cvrdt_sec. The kernel step is
      alo_exact_recovered on unary payload merges; the binary merge is reduced to unary ones
      by cv_invariant (semilattice laws, inflation, uniqueness of updates). See the leak note
      there.
   4. The N = id instance and strictness. causal_descent_exact: for any N with state descent,
      the repaired results of causal orders agree iff concurrent governed steps commute at
      causally deliverable points (normalization_descent, then opsec_exact);
      sec_is_nid_instance: with N = id this is op-based SEC word for word. crdt_sec_strict: the
      settrue / flip witness converges after repair for every hb, while its raw operations are
      not SEC once the two events are concurrent and admit no order making both inflationary.
   5. Non-vacuity: opsec_nonvacuous, gomes_nonvacuous, cvrdt_nonvacuous. *)

From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Trace NC.CanonicalExecution NC.PresentedExecution.
Require NC.CausalReplay NC.GovernanceConverse NC.CanonicalInstances NC.AtLeastOnceExact.
Require NC.CRDT NC.CRDTBoundary.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Op-based SEC from the layer A kernels with N = id                                         *)
(* ============================================================================================ *)

Section OpBased.
  Context {S E : Type}.
  Variable apply : E -> S -> S.
  Variable hb : E -> E -> Prop.

  Local Notation causal := (CausalReplay.causal hb).
  Local Notation concurrent := (CausalReplay.concurrent hb).

  (* The canonicalizer of a CRDT: the identity (no repair). *)
  Definition nid (s : S) : S := s.

  (* SEC at a start: delivery orders of the same events that respect causality agree. *)
  Definition OpSEC (s0 : S) : Prop :=
    forall o1 o2, causal o1 -> causal o2 -> Permutation o1 o2 ->
      runT apply o1 s0 = runT apply o2 s0.

  (* The exact condition: a concurrent pair commutes at every point after which it can be
     delivered in causal order. *)
  Definition ConcCommuteReach (s0 : S) : Prop :=
    forall p a b, concurrent a b -> causal (p ++ [a; b]) ->
      apply b (apply a (runT apply p s0)) = apply a (apply b (runT apply p s0)).

  (* State descent along N = id is reflexivity. *)
  Lemma nid_state_descent : StateDescent nid apply.
  Proof. intros e s. reflexivity. Qed.

  (* With N = id the governed step and run are the raw ones. *)
  Lemma grun_nid : forall t s, grun nid apply t s = runT apply t s.
  Proof. intros t s. reflexivity. Qed.

  (* The state side (kernel: state_side_transfer): the normalized raw semantics and the governed
     semantics pose the same invariance question for every presentation. *)
  Theorem opsec_state_side : forall s0 (Adm : list E -> Prop) Gen,
    PInv Adm Gen (fun t => nid (rawrun apply t s0)) eq <->
    PInv Adm Gen (fun t => grun nid apply t (nid s0)) eq.
  Proof.
    intros s0 Adm Gen. exact (state_side_transfer nid apply s0 nid_state_descent Adm Gen eq).
  Qed.

  Local Notation sem s0 := (msem (gact nid apply) (fun x => x) s0).

  (* History descent (kernel: causal_adequate, through cg_peq): SEC is invariance of the
     governed semantics under the causal presentation. *)
  Theorem opsec_history_descent : forall s0,
    OpSEC s0 <-> PInv causal (cg_gen hb) (sem s0) eq.
  Proof.
    intros s0. split.
    - intros H t t' Hq. apply (@cg_peq S E apply hb s0) in Hq.
      destruct (ac_adm' causal (CanonicalInstances.cswap hb) t t' Hq) as [Ht Ht'].
      exact (H t t' Ht Ht' (proj2 (CanonicalInstances.causal_adequate hb t t' Ht Ht') Hq)).
    - intros H o1 o2 H1 H2 P. apply (H o1 o2). apply (@cg_peq S E apply hb s0).
      exact (proj1 (CanonicalInstances.causal_adequate hb o1 o2 H1 H2) P).
  Qed.

  (* P1 (kernel: local_exact_all, with cg_prefix and msem_eq_resp). *)
  Theorem opsec_seeds : forall s0,
    PInv causal (cg_gen hb) (sem s0) eq <-> PSeedOK causal (cg_gen hb) (sem s0) eq.
  Proof.
    intros s0. apply local_exact_all; [exact (@eq_refl _) | exact (@eq_sym _) | exact (@eq_trans _)
                                      | exact (cg_prefix hb) |].
    intros t t' e _ _. apply msem_eq_resp.
  Qed.

  (* The seeds are raw commutation of concurrent pairs at causally deliverable points. *)
  Theorem seeds_concurrent : forall s0,
    PSeedOK causal (cg_gen hb) (sem s0) eq <-> ConcCommuteReach s0.
  Proof.
    intros s0. split.
    - intros H p a b Hab Hc.
      assert (Hc' : causal (p ++ [b; a]))
        by exact (GovernanceConverse.causal_swap hb p a b [] (proj1 (proj2 Hab)) Hc).
      pose proof (H p [a; b] [b; a]
                    (ex_intro _ a (ex_intro _ b (conj Hab (conj Hc (conj eq_refl eq_refl)))))
                    Hc Hc') as K.
      unfold msem in K. rewrite !runT_app in K. exact K.
    - intros H p u v (a & b & Hab & Hc & -> & ->) _ _. unfold msem. rewrite !runT_app.
      exact (H p a b Hab Hc).
  Qed.

  (* Op-based SEC, exact: SEC at s0 iff concurrent pairs commute at causally deliverable points. *)
  Theorem opsec_exact : forall s0, OpSEC s0 <-> ConcCommuteReach s0.
  Proof.
    intros s0. rewrite opsec_history_descent, opsec_seeds. apply seeds_concurrent.
  Qed.

  (* From every start: concurrent operations commute at every state. *)
  Theorem opsec_global_exact : (forall x, ~ hb x x) ->
    ((forall s0, OpSEC s0) <-> (forall a b s, concurrent a b -> apply a (apply b s) = apply b (apply a s))).
  Proof.
    intros Hirr. split.
    - intros H a b s Hab.
      assert (Hc : causal ([] ++ [a; b])).
      { destruct Hab as [Hne [Hab Hba]]. split.
        - constructor; [intros [E1 | []]; apply Hne; symmetry; exact E1
                      | constructor; [intros [] | constructor]].
        - intros x y Hxy Hx Hy. exfalso.
          destruct Hx as [<- | [<- | []]]; destruct Hy as [<- | [<- | []]];
            [exact (Hirr _ Hxy) | exact (Hab Hxy) | exact (Hba Hxy) | exact (Hirr _ Hxy)]. }
      symmetry. exact (proj1 (opsec_exact s) (H s) [] a b Hab Hc).
    - intros H s0. apply opsec_exact. intros p a b Hab _. symmetry. apply H. exact Hab.
  Qed.

  (* Shapiro's sufficient condition: concurrent updates commute at every state reached by a
     causal delivery. It implies the exact condition; the converse fails
     (GovernanceConverse.naive_causal_converse_fails). *)
  Definition ShapiroCommute (s0 : S) : Prop :=
    forall p a b, causal p -> concurrent a b ->
      apply b (apply a (runT apply p s0)) = apply a (apply b (runT apply p s0)).

  Theorem shapiro_cmrdt_sec : forall s0, ShapiroCommute s0 -> OpSEC s0.
  Proof.
    intros s0 H. apply opsec_exact. intros p a b Hab Hc. apply H; [| exact Hab].
    exact (GovernanceConverse.causal_prefix hb p [a; b] Hc).
  Qed.
End OpBased.

(* ============================================================================================ *)
(* 2. Gomes, Kleppmann, Mulligan, Beresford (OOPSLA 2017), theorem convergence                  *)
(* ============================================================================================ *)

(* Their definitions: interp gives partial state transformers, composed by the Kleisli arrow;
   apply_operations composes a list left to right from Some; hb-consistent appends an operation
   that happens before nothing already in the list; concurrency is neither hb direction; and
   concurrent_ops_commute asks the Kleisli compositions of concurrent pairs in the list to be
   equal (pointwise here, function equality there). *)
Section Gomes.
  Context {St Op : Type}.
  Variable hb : Op -> Op -> Prop.
  Variable interp : Op -> St -> option St.

  Definition kleisli (f g : St -> option St) : St -> option St :=
    fun x => match f x with Some y => g y | None => None end.

  Definition apply_operations (ops : list Op) : St -> option St :=
    fold_left kleisli (map interp ops) (@Some St).

  Inductive hb_consistent : list Op -> Prop :=
  | hbc_nil : hb_consistent []
  | hbc_snoc : forall xs y, hb_consistent xs -> (forall x, In x xs -> ~ hb y x) ->
      hb_consistent (xs ++ [y]).

  Definition gconcurrent (x y : Op) : Prop := ~ hb x y /\ ~ hb y x.

  Definition concurrent_ops_commute (xs : list Op) : Prop :=
    forall x y, In x xs -> In y xs -> gconcurrent x y ->
      forall s, kleisli (interp x) (interp y) s = kleisli (interp y) (interp x) s.

  (* The total step on option states that the kernels run: None absorbs. *)
  Definition ostep (x : Op) (o : option St) : option St :=
    match o with Some s => interp x s | None => None end.

  Lemma apply_operations_runT : forall ops s, apply_operations ops s = runT ostep ops (Some s).
  Proof.
    intros ops s. unfold apply_operations.
    assert (K : forall f, fold_left kleisli (map interp ops) f s = runT ostep ops (f s)).
    { induction ops as [| x ops IH]; intros f; [reflexivity |].
      change (map interp (x :: ops)) with (interp x :: map interp ops). rewrite runT_cons.
      cbn [fold_left]. rewrite IH. unfold kleisli, ostep. destruct (f s); reflexivity. }
    apply K.
  Qed.

  Lemma prec_snoc_l : forall (l : list Op) a b y,
    CausalReplay.prec a b l -> CausalReplay.prec a b (l ++ [y]).
  Proof.
    induction l as [| x l IH]; intros a b y H; [destruct H |]. simpl in *.
    destruct H as [[-> Hb] | H]; [left; split; [reflexivity | apply in_or_app; left; exact Hb]
                                | right; apply IH; exact H].
  Qed.

  Lemma prec_snoc_r : forall (l : list Op) a y, In a l -> CausalReplay.prec a y (l ++ [y]).
  Proof.
    induction l as [| x l IH]; intros a y H; [destruct H |]. simpl in *.
    destruct H as [-> | H]; [left; split; [reflexivity | apply in_or_app; right; left; reflexivity]
                            | right; apply IH; exact H].
  Qed.

  (* hb-consistent and distinct: hb-earlier operations come first. *)
  Lemma hbc_prec : forall xs, hb_consistent xs -> NoDup xs ->
    forall a b, hb a b -> a <> b -> In a xs -> In b xs -> CausalReplay.prec a b xs.
  Proof.
    intros xs H. induction H as [| xs y Hc IH Hy]; intros Hnd a b Hab Hne Ha Hb; [destruct Ha |].
    assert (Hnd' : NoDup xs) by exact (NoDup_app_remove_r _ _ Hnd).
    apply in_app_or in Ha. apply in_app_or in Hb.
    destruct Ha as [Ha | [<- | []]]; destruct Hb as [Hb | [<- | []]].
    - apply prec_snoc_l. exact (IH Hnd' a b Hab Hne Ha Hb).
    - apply prec_snoc_r. exact Ha.
    - exfalso. exact (Hy b Hb Hab).
    - exfalso. exact (Hne eq_refl).
  Qed.
End Gomes.

(* Generic list facts for the restriction to the operations of a history. *)
Lemma prec_in_l : forall {A : Type} (k i : A) o, CausalReplay.prec k i o -> In k o.
Proof.
  intros A k i o. induction o as [| x t IH]; simpl; [contradiction |].
  intros [[-> _] | H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma prec_map_inv : forall {A B : Type} (f : A -> B) l a b, NoDup (map f l) -> In a l -> In b l ->
  CausalReplay.prec (f a) (f b) (map f l) -> CausalReplay.prec a b l.
Proof.
  intros A B f l. induction l as [| c t IH]; intros a b Hnd Ha Hb H; [destruct Ha |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hc Hnd].
  simpl in H. destruct H as [[Ec Hfb] | H].
  - destruct Ha as [-> | Ha]; [| exfalso; apply Hc; rewrite Ec; apply in_map; exact Ha].
    destruct Hb as [-> | Hb]; [exfalso; apply Hc; exact Hfb |].
    left. split; [reflexivity | exact Hb].
  - right. destruct Ha as [<- | Ha]; [exfalso; apply Hc; exact (prec_in_l _ _ _ H) |].
    destruct Hb as [<- | Hb]; [exfalso; apply Hc; exact (CausalReplay.prec_in_r _ _ _ H) |].
    exact (IH a b Hnd Ha Hb H).
Qed.

Lemma attach : forall {A : Type} (P : A -> Prop) (l : list A), (forall x, In x l -> P x) ->
  exists l' : list (sig P), map (@proj1_sig A P) l' = l.
Proof.
  intros A P l. induction l as [| x l IH]; intros H; [exists []; reflexivity |].
  destruct IH as [l' E]; [intros y Hy; apply H; right; exact Hy |].
  exists (exist P x (H x (or_introl eq_refl)) :: l'). simpl. rewrite E. reflexivity.
Qed.

Lemma runT_map : forall {A B S : Type} (step : B -> S -> S) (f : A -> B) l s,
  runT step (map f l) s = runT (fun a => step (f a)) l s.
Proof.
  intros A B S step f l. induction l as [| x l IH]; intros s; [reflexivity |].
  change (map f (x :: l)) with (f x :: map f l). rewrite !runT_cons. apply IH.
Qed.

(* Gomes et al.'s theorem convergence (Section 4.3), through opsec_exact. The events are the
   operations of xs (a subtype), the states are option states (ostep), and hb is restricted to
   them. Their hypotheses, plus irreflexivity of hb (part of their strict partial order);
   transitivity of hb and concurrent_ops_commute ys are not used. *)
Theorem gomes_convergence : forall {St Op : Type} (hb : Op -> Op -> Prop)
  (interp : Op -> St -> option St), (forall x, ~ hb x x) ->
  forall xs ys, (forall x, In x xs <-> In x ys) ->
  concurrent_ops_commute hb interp xs -> concurrent_ops_commute hb interp ys ->
  NoDup xs -> NoDup ys -> hb_consistent hb xs -> hb_consistent hb ys ->
  forall s, apply_operations interp xs s = apply_operations interp ys s.
Proof.
  intros St Op hb interp Hirr xs ys Hset Hcx _ Hdx Hdy Hhx Hhy s.
  rewrite !apply_operations_runT.
  set (P := fun x => In x xs).
  set (pr := @proj1_sig Op P).
  set (hb' := fun a b : sig P => hb (pr a) (pr b)).
  pose proof (NoDup_Permutation Hdx Hdy Hset) as Hperm.
  destruct (attach P xs (fun x H => H)) as [l1 E1].
  rewrite <- E1 in Hperm. apply Permutation_sym in Hperm.
  destruct (Permutation_map_inv _ _ Hperm) as [l2 [E2 P12]].
  assert (Hne : forall a b, hb a b -> a <> b) by (intros a b H ->; exact (Hirr b H)).
  assert (Hcaus : forall l zs, map pr l = zs -> hb_consistent hb zs -> NoDup zs ->
            CausalReplay.causal hb' l).
  { intros l zs Ez Hh Hd. subst zs. split; [exact (NoDup_map_inv _ _ Hd) |].
    intros a b Hab Ha Hb. apply (prec_map_inv pr); [exact Hd | exact Ha | exact Hb |].
    apply (hbc_prec hb (map pr l) Hh Hd);
      [exact Hab | exact (Hne _ _ Hab) | apply in_map; exact Ha | apply in_map; exact Hb]. }
  assert (Hsec : OpSEC (fun a => ostep interp (pr a)) hb' (Some s)).
  { apply opsec_exact. intros p a b [_ [Hab Hba]] _.
    destruct (runT (fun a0 => ostep interp (pr a0)) p (Some s)) as [y |]; [| reflexivity].
    exact (Hcx (pr a) (pr b) (proj2_sig a) (proj2_sig b) (conj Hab Hba) y). }
  rewrite <- E1, E2, !runT_map.
  apply Hsec; [exact (Hcaus l1 xs E1 Hhx Hdx) | exact (Hcaus l2 ys (eq_sym E2) Hhy Hdy) | exact P12].
Qed.

(* ============================================================================================ *)
(* 3. State-based SEC (Shapiro Theorem 1, CvRDT)                                                *)
(* ============================================================================================ *)

(* The kernel step: unary merges of payloads. An event e merges a fixed payload pay e into the
   state (pmerge). Free at-least-once delivery of such events (any order, any duplication)
   converges iff they commute and are idempotent at reachable states: alo_exact_recovered
   (P1 on the at-least-once presentation), unchanged. A join-semilattice gives both. *)
Section Payloads.
  Context {S E : Type}.
  Variable join : S -> S -> S.
  Hypothesis join_comm : forall a b, join a b = join b a.
  Hypothesis join_assoc : forall a b c, join (join a b) c = join a (join b c).
  Hypothesis join_idem : forall a, join a a = a.
  Variable dec : forall x y : E, {x = y} + {x <> y}.

  Definition pmerge (pay : E -> S) (e : E) (s : S) : S := join s (pay e).

  (* The at-least-once kernel on payload merges, as an iff. *)
  Theorem merge_delivery_exact : forall (pay : E -> S) (Ev : E -> Prop) s0,
    AtLeastOnceExact.ALOConv (pmerge pay) Ev s0 <->
    AtLeastOnceExact.CommReach (pmerge pay) Ev s0 /\
    forall a, AtLeastOnceExact.IdemReach (pmerge pay) Ev s0 a.
  Proof. intros pay Ev s0. exact (alo_exact_recovered dec (pmerge pay) Ev s0). Qed.

  (* The semilattice laws discharge both clauses. *)
  Lemma join_aloconv : forall pay s0, AtLeastOnceExact.ALOConv (pmerge pay) (fun _ => True) s0.
  Proof.
    intros pay s0. apply merge_delivery_exact. split.
    - intros p a b _ _ _. unfold pmerge. rewrite !join_assoc, (join_comm (pay a)). reflexivity.
    - intros a u _ _. unfold pmerge. rewrite join_assoc, join_idem. reflexivity.
  Qed.

  (* Two delivery words with the same set of events reach the same state. *)
  Theorem payload_sec : forall pay s0 (d1 d2 : list E), (forall x, In x d1 <-> In x d2) ->
    runT (pmerge pay) d1 s0 = runT (pmerge pay) d2 s0.
  Proof.
    intros pay s0 d1 d2 H.
    pose proof (join_aloconv pay s0) as K.
    assert (F : forall d : list E, Forall (fun _ : E => True) d) by (intros d; apply Forall_forall; intros; exact I).
    rewrite (K d1 (nodup dec d1) (F d1) (NoDup_nodup dec d1) (fun x => nodup_In dec d1 x)).
    rewrite (K d2 (nodup dec d1) (F d2) (NoDup_nodup dec d1)); [reflexivity |].
    intros x. rewrite nodup_In. apply H.
  Qed.

  (* Semilattice facts used by the reduction of binary merges (CRDT-specific, no kernel). *)
  Lemma run_join : forall pay l x y,
    runT (pmerge pay) l (join x y) = join x (runT (pmerge pay) l y).
  Proof.
    intros pay l. induction l as [| e l IH]; intros x y; [reflexivity |].
    rewrite !runT_cons. change (pmerge pay e (join x y)) with (join (join x y) (pay e)).
    change (pmerge pay e y) with (join y (pay e)). rewrite join_assoc. apply IH.
  Qed.

  Lemma run_above : forall pay l s0, join s0 (runT (pmerge pay) l s0) = runT (pmerge pay) l s0.
  Proof. intros pay l s0. rewrite <- run_join, join_idem. reflexivity. Qed.

  Lemma run_merge : forall pay l1 l2 s0,
    join (runT (pmerge pay) l1 s0) (runT (pmerge pay) l2 s0) = runT (pmerge pay) (l1 ++ l2) s0.
  Proof.
    intros pay l1 l2 s0. rewrite runT_app, <- run_join.
    rewrite (join_comm _ s0), run_above. reflexivity.
  Qed.

  Lemma run_agree : forall pay pay' l s, (forall e, In e l -> pay e = pay' e) ->
    runT (pmerge pay) l s = runT (pmerge pay') l s.
  Proof.
    intros pay pay' l. induction l as [| e l IH]; intros s H; [reflexivity |].
    rewrite !runT_cons. change (pmerge pay e s) with (join s (pay e)).
    change (pmerge pay' e s) with (join s (pay' e)). rewrite (H e (or_introl eq_refl)).
    apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.
End Payloads.

(* Shapiro's state-based model (SSS 2011, Section 2.1 and Definition 1). Replicas R hold
   states; Upd i e runs update e at replica i (s := u e s); Mrg i j merges replica j's current
   state into replica i's (s_i := s_i join s_j). The causal history hist of a replica adds e at
   Upd i e and unions in the other history at Mrg i j. Updates are unique: an event is run as an
   update at most once (NoDup (upds w)). The payload log pay records the state each update
   produced at its source. Only hist and pay are bookkeeping; st is the replicated state.

   LEAK (reported, not repaired). The binary merge Mrg i j combines two replica states. The
   layer A kernels see words of events from one start, so Mrg is not a kernel event. It is
   reduced to unary payload merges by cv_invariant: every replica's state is the run of
   pmerge pay over its causal history from s0. That reduction uses only the semilattice laws,
   inflation of updates and uniqueness of updates, not any kernel; the kernel step is
   payload_sec. The smallest missing generic piece is a presentation whose executions are
   multi-replica configurations with a binary merge (histories combined by union), rather than
   words from one start. *)
Section Replicas.
  Context {S E R : Type}.
  Variable join : S -> S -> S.
  Hypothesis join_comm : forall a b, join a b = join b a.
  Hypothesis join_assoc : forall a b c, join (join a b) c = join a (join b c).
  Hypothesis join_idem : forall a, join a a = a.
  Variable decE : forall x y : E, {x = y} + {x <> y}.
  Variable decR : forall x y : R, {x = y} + {x <> y}.
  Variable u : E -> S -> S.
  (* Updates are inflationary: s <= u e s in the order of the semilattice (x <= y iff join x y = y). *)
  Hypothesis u_infl : forall e s, join s (u e s) = u e s.
  Variable s0 : S.

  Inductive lab : Type := Upd (i : R) (e : E) | Mrg (i j : R).

  Record cfg : Type := mkc { st : R -> S; hist : R -> list E; pay : E -> S }.

  Definition updR {A : Type} (f : R -> A) (i : R) (a : A) : R -> A :=
    fun k => if decR k i then a else f k.
  Definition updE (f : E -> S) (e : E) (a : S) : E -> S :=
    fun x => if decE x e then a else f x.

  Definition cstep (l : lab) (c : cfg) : cfg :=
    match l with
    | Upd i e => mkc (updR (st c) i (u e (st c i))) (updR (hist c) i (hist c i ++ [e]))
                     (updE (pay c) e (u e (st c i)))
    | Mrg i j => mkc (updR (st c) i (join (st c i) (st c j)))
                     (updR (hist c) i (hist c i ++ hist c j)) (pay c)
    end.

  Definition c0 : cfg := mkc (fun _ => s0) (fun _ => []) (fun _ => s0).

  Fixpoint upds (w : list lab) : list E :=
    match w with [] => [] | Upd _ e :: w' => e :: upds w' | Mrg _ _ :: w' => upds w' end.

  Lemma upds_app : forall w w', upds (w ++ w') = upds w ++ upds w'.
  Proof.
    induction w as [| [i e | i j] w IH]; intros w'; simpl; [reflexivity | rewrite IH; reflexivity | apply IH].
  Qed.

  Local Notation prun pay l := (runT (pmerge join pay) l s0).

  Definition CvInv (w : list lab) (c : cfg) : Prop :=
    (forall i, st c i = prun (pay c) (hist c i)) /\
    (forall i e, In e (hist c i) -> In e (upds w)).

  (* The reduction of binary merges to unary payload merges (CRDT-specific, no kernel). *)
  Lemma cv_invariant : forall w, NoDup (upds w) -> CvInv w (runT cstep w c0).
  Proof.
    induction w as [| l w IH] using rev_ind; intros Hnd.
    - split; [intros i; reflexivity | intros i e []].
    - rewrite upds_app in Hnd. destruct (IH (NoDup_app_remove_r _ _ Hnd)) as [Hst Hh].
      rewrite runT_app. change (runT cstep [l] (runT cstep w c0)) with (cstep l (runT cstep w c0)).
      set (c := runT cstep w c0) in *.
      destruct l as [i e | i j].
      + simpl in Hnd. assert (He : ~ In e (upds w)).
        { intros H. apply (NoDup_remove_2 (upds w) [] e Hnd). rewrite app_nil_r. exact H. }
        assert (Ag : forall k, prun (pay c) (hist c k) = prun (updE (pay c) e (u e (st c i))) (hist c k)).
        { intros k. apply run_agree. intros x Hx. unfold updE. destruct (decE x e) as [-> |]; [| reflexivity].
          exfalso. exact (He (Hh k e Hx)). }
        split.
        * intros k. simpl. unfold updR. destruct (decR k i) as [-> |]; [| rewrite <- Ag; apply Hst].
          rewrite runT_app. change (runT (pmerge join (updE (pay c) e (u e (st c i)))) [e] ?x)
            with (join x (updE (pay c) e (u e (st c i)) e)).
          rewrite <- Ag, <- Hst. unfold updE. destruct (decE e e) as [_ | N]; [| exfalso; exact (N eq_refl)].
          symmetry. apply u_infl.
        * intros k x. simpl. rewrite upds_app. simpl. unfold updR. destruct (decR k i) as [-> |].
          -- intros Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx | [<- | []]];
               [left; exact (Hh i x Hx) | right; left; reflexivity].
          -- intros Hx. apply in_or_app. left. exact (Hh k x Hx).
      + split.
        * intros k. simpl. unfold updR. destruct (decR k i) as [-> |]; [| apply Hst].
          rewrite !Hst. apply run_merge; assumption.
        * intros k x. simpl. rewrite upds_app, app_nil_r. unfold updR. destruct (decR k i) as [-> |].
          -- intros Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (Hh i x Hx) | exact (Hh j x Hx)].
          -- exact (Hh k x).
  Qed.

  (* Shapiro Theorem 1, strong convergence: replicas with the same causal history (as a set)
     have the same state, for every execution with unique updates. *)
  Theorem cvrdt_sec : forall w i j, NoDup (upds w) ->
    (forall e, In e (hist (runT cstep w c0) i) <-> In e (hist (runT cstep w c0) j)) ->
    st (runT cstep w c0) i = st (runT cstep w c0) j.
  Proof.
    intros w i j Hnd H. destruct (cv_invariant w Hnd) as [Hst _]. rewrite !Hst.
    apply (payload_sec join join_comm join_assoc join_idem decE). exact H.
  Qed.
End Replicas.

(* ============================================================================================ *)
(* 4. SEC as the N = id instance, and strictness on the same operations                         *)
(* ============================================================================================ *)

(* The main result under causal delivery, for any canonicalizer N with state descent: the
   repaired results N (rawrun o s0) of causal orders of the same events agree iff concurrent
   governed steps commute at causally deliverable points from N s0. Kernels:
   normalization_descent (state descent), then opsec_exact (history descent, P1). *)
Theorem causal_descent_exact : forall {S E : Type} (N : S -> S) (act : E -> S -> S)
  (hb : E -> E -> Prop) (s0 : S), StateDescent N act ->
  ((forall o1 o2, CausalReplay.causal hb o1 -> CausalReplay.causal hb o2 -> Permutation o1 o2 ->
      N (rawrun act o1 s0) = N (rawrun act o2 s0)) <->
   ConcCommuteReach (gact N act) hb (N s0)).
Proof.
  intros S E N act hb s0 HS. rewrite <- opsec_exact.
  assert (K : forall o, N (rawrun act o s0) = runT (gact N act) o (N s0))
    by (intros o; exact (normalization_descent N act HS o s0)).
  split; intros H o1 o2 H1 H2 P; [rewrite <- !K | rewrite !K]; exact (H o1 o2 H1 H2 P).
Qed.

(* With N = id the statement is op-based SEC and its exact condition, word for word. *)
Theorem sec_is_nid_instance : forall {S E : Type} (apply : E -> S -> S) (hb : E -> E -> Prop) s0,
  ((forall o1 o2, CausalReplay.causal hb o1 -> CausalReplay.causal hb o2 -> Permutation o1 o2 ->
      nid (rawrun apply o1 s0) = nid (rawrun apply o2 s0)) <-> OpSEC apply hb s0) /\
  (ConcCommuteReach (gact nid apply) hb (nid s0) <-> ConcCommuteReach apply hb s0).
Proof. intros S E apply hb s0. split; split; intros H; exact H. Qed.

(* The witness of CRDT.v and CRDTBoundary.v (raw settrue and flip, repair to false). *)
Definition wN : bool -> bool := CRDT.fixb.

Lemma wN_state_descent : StateDescent wN CRDTBoundary.wraw.
Proof. intros e s. reflexivity. Qed.

(* Strictness. With the non-identity repair wN, the repaired results of causal orders agree for
   every hb from every start. With N = id the same raw operations are not SEC from any start
   once WSet and WFlip are concurrent (hb irreflexive), and no partial order makes both raw
   operations inflationary, so they are not a CvRDT either (CRDTBoundary.witness_not_cvrdt_order). *)
Theorem crdt_sec_strict :
  (exists s, wN s <> s) /\
  (forall hb s0 o1 o2, CausalReplay.causal hb o1 -> CausalReplay.causal hb o2 ->
     Permutation o1 o2 ->
     wN (rawrun CRDTBoundary.wraw o1 s0) = wN (rawrun CRDTBoundary.wraw o2 s0)) /\
  (forall hb, (forall x, ~ hb x x) -> CausalReplay.concurrent hb CRDTBoundary.WSet CRDTBoundary.WFlip ->
     forall s0, ~ OpSEC CRDTBoundary.wraw hb s0) /\
  ~ (exists le : bool -> bool -> Prop,
       (forall s, le s s) /\ (forall a b, le a b -> le b a -> a = b) /\
       (forall a b c, le a b -> le b c -> le a c) /\
       (forall s, le s (CRDT.settrue s)) /\ (forall s, le s (CRDT.flip s))).
Proof.
  split; [exists true; discriminate |].
  split; [| split; [| exact CRDTBoundary.witness_not_cvrdt_order]].
  - intros hb s0. apply (causal_descent_exact wN CRDTBoundary.wraw hb s0 wN_state_descent).
    intros p a b _ _. reflexivity.
  - intros hb Hirr Hc s0 H. apply opsec_exact in H.
    assert (Hcaus : CausalReplay.causal hb ([] ++ [CRDTBoundary.WSet; CRDTBoundary.WFlip])).
    { destruct Hc as [Hne [H1 H2]]. split.
      - constructor; [intros [E1 | []]; apply Hne; symmetry; exact E1 | constructor; [intros [] | constructor]].
      - intros x y Hxy Hx Hy. exfalso.
        destruct Hx as [<- | [<- | []]]; destruct Hy as [<- | [<- | []]];
          [exact (Hirr _ Hxy) | exact (H1 Hxy) | exact (H2 Hxy) | exact (Hirr _ Hxy)]. }
    pose proof (H [] _ _ Hc Hcaus) as K. simpl in K.
    unfold CRDT.flip, CRDT.settrue in K. discriminate K.
Qed.

(* ============================================================================================ *)
(* 5. Non-vacuity                                                                               *)
(* ============================================================================================ *)

(* Op-based: a counter (every increment commutes), every hb, every start. *)
Theorem opsec_nonvacuous : forall (hb : nat -> nat -> Prop) s0,
  OpSEC (fun _ s => S s) hb s0 /\ ConcCommuteReach (fun _ s => S s) hb s0.
Proof.
  intros hb s0. assert (C : ConcCommuteReach (fun _ s => S s) hb s0) by (intros p a b _ _; reflexivity).
  split; [apply opsec_exact |]; exact C.
Qed.

(* Gomes et al.: every hypothesis holds on two concurrent additions in both orders. *)
Theorem gomes_nonvacuous :
  let hb := fun _ _ : nat => False in
  let interp := fun (x s : nat) => Some (x + s) in
  (forall x, ~ hb x x) /\ (forall x, In x [1; 2] <-> In x [2; 1]) /\
  concurrent_ops_commute hb interp [1; 2] /\ concurrent_ops_commute hb interp [2; 1] /\
  NoDup [1; 2] /\ NoDup [2; 1] /\ hb_consistent hb [1; 2] /\ hb_consistent hb [2; 1] /\
  forall s, apply_operations interp [1; 2] s = apply_operations interp [2; 1] s.
Proof.
  intros hb interp.
  assert (Cm : forall xs, concurrent_ops_commute hb interp xs).
  { intros xs x y _ _ _ s. unfold kleisli, interp. f_equal.
    rewrite PeanoNat.Nat.add_assoc, (PeanoNat.Nat.add_comm y x), <- PeanoNat.Nat.add_assoc. reflexivity. }
  assert (Hc : forall a b, hb_consistent hb [a; b]).
  { intros a b. change [a; b] with (([] ++ [a]) ++ [b]).
    apply hbc_snoc; [apply hbc_snoc; [constructor | intros _ []] | intros _ _ []]. }
  assert (Nd : forall a b : nat, a <> b -> NoDup [a; b]).
  { intros a b Hab. constructor; [intros [E1 | []]; exact (Hab (eq_sym E1)) | constructor; [intros [] | constructor]]. }
  split; [intros _ [] |].
  split; [intros x; simpl; tauto |].
  split; [apply Cm | split; [apply Cm |]].
  split; [apply Nd; discriminate | split; [apply Nd; discriminate |]].
  split; [apply Hc | split; [apply Hc |]].
  intros s. reflexivity.
Qed.

(* State-based: max on nat, two replicas, one update each, merges both ways. The histories are
   [1; 2] and [2; 1; 2] (the second merge delivers update 2 twice), the same set, and both
   states are 2. *)
Definition nv_w : list (@lab nat bool) := [Upd true 1; Upd false 2; Mrg true false; Mrg false true].

Definition nv_u (e s : nat) : nat := Nat.max s e.
Definition nv_c : cfg := runT (cstep Nat.max PeanoNat.Nat.eq_dec Bool.bool_dec nv_u) nv_w (c0 0).

Theorem cvrdt_nonvacuous :
  (forall a b, Nat.max a b = Nat.max b a) /\
  (forall a b c, Nat.max (Nat.max a b) c = Nat.max a (Nat.max b c)) /\
  (forall a, Nat.max a a = a) /\ (forall e s, Nat.max s (nv_u e s) = nv_u e s) /\
  NoDup (upds nv_w) /\ hist nv_c true = [1; 2] /\ hist nv_c false = [2; 1; 2] /\
  st nv_c true = 2 /\ st nv_c false = 2.
Proof.
  split; [exact PeanoNat.Nat.max_comm |].
  split; [intros a b c; symmetry; apply PeanoNat.Nat.max_assoc |].
  split; [exact PeanoNat.Nat.max_id |].
  split; [intros e s; unfold nv_u; rewrite PeanoNat.Nat.max_assoc, PeanoNat.Nat.max_id; reflexivity |].
  split; [constructor; [intros [E1 | []]; discriminate E1 | constructor; [intros [] | constructor]] |].
  repeat split; reflexivity.
Qed.
