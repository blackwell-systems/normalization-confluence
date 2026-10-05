(* CRDTBoundary.v: the boundary between the CRDT convergence regimes and normalization
   confluence, stated as one theorem, with the strictness witness of CRDT.v sharpened.
   Axiom-free.

   CRDT.v, CausalReplay.v, GovernanceConverse.v and CvRDTExact.v prove the pieces: the embedding
   of op-based and state-based CRDTs (cmrdt_SEC, cvrdt_SEC), the exact compensation-free
   conditions (causal_convergence_exact, merge_action_exact, cvrdt_exact_all), and a witness
   machine on bool (settrue, flip, compensation to false) that converges only through
   compensation. This file assembles them into a single boundary statement and replaces the
   weakest parts of the original witness argument with sharper theorems.

   Setting. An event e has a raw transition act e : S -> S; a normalization (compensation)
   normalize : S -> S; the governed step is CausalReplay.gstep act normalize e s =
   normalize (act e s). "Compensation-free" means normalize = id pointwise.

   The witness, sharpened (section Witness; events WSet and WFlip, raw transitions CRDT.settrue
   and CRDT.flip, compensation CRDT.fixb).
   - witness_ops_not_commute: the raw operations do not commute, at every state:
     flip (settrue s) = false and settrue (flip s) = true. The old witness_not_cmrdt quantified
     over all bool functions; this is the specific pair.
   - witness_not_cvrdt_order: there is no partial order on bool under which both raw operations
     are inflationary (s <= op s for all s). settrue false = true forces false <= true,
     flip true = false forces true <= false, antisymmetry gives true = false.
     witness_not_inflationary_antisym: the same with antisymmetry as the only hypothesis.
   - witness_not_cvrdt_exact: as merge actions of a compensation-free registry the raw operations
     are, from every start state, neither commutative nor idempotent at a reachable state, do not
     converge under unordered at-least-once delivery (MergeConv fails; flip is not idempotent),
     and have no semilattice representation on the reachable states (CvRDTOn fails).
   - witness_raw_not_causal: with no causal order between the two events, the raw operations do
     not converge under causal exactly-once delivery from any start state.
   - witness_governed_constant: the governed machine's state after any nonempty delivery is false
     (the normal form is constant), its governed steps commute and are idempotent everywhere,
     and they ARE a state-based CRDT on bool (CvRDTOn with the join andb, false as top). So the
     governed BEHAVIOR is trivially representable by a CRDT; the strictness claim is about the
     raw transition representation, not about observable behavior.

   The boundary (crdt_boundary).
   (a) Compensation-free, causal exactly-once delivery: for every irreflexive hb, causal
       convergence of the governed steps from every start iff concurrent raw operations commute
       at every state (causal_cmrdt act hb). Instance of causal_convergence_exact composed with
       compensation_free_exact.
   (b) Compensation-free, unordered at-least-once delivery: for every event range X and start
       s0, convergence under every order and duplication iff the raw actions are commutative and
       idempotent on the states reachable from s0 (merge_action_exact). With X finite (listed by
       xs) and state equality decidable, iff a join-semilattice representation of the raw actions
       on the reachable states (cvrdt_exact_all).
   (c) With compensation: the witness's governed steps converge under both delivery models from
       every start, on the same bool representation, while (a) and (b) fail for its raw
       operations (the compensation-free system built from them diverges from every start).
   Qualifier. (c) is strictness relative to a fixed transition representation: by
   witness_governed_constant the governed composite gstep act fixb is itself a CvRDT and a
   CmRDT on bool. The theorem says that no compensation-free system using the raw transitions
   settrue and flip satisfies the CRDT convergence conditions, not that the observable governed
   behavior escapes every CRDT.

   Non-vacuity (boundary_nonvacuous): the hypotheses of (a) and (b) hold for the witness raw
   operations (both sides false there) and for the constant action (both sides true there). *)

From Coq Require Import List Bool.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace.
Require NC.CRDT NC.CausalReplay NC.GovernanceConverse NC.CvRDTExact.
Import ListNotations.

(* ============================================================================================ *)
(* Compensation-free governed steps coincide with the raw transitions.                          *)
(* ============================================================================================ *)

Section CompensationFree.
  Context {S E : Type}.
  Variable act : E -> S -> S.
  Variable normalize : S -> S.
  Hypothesis Hid : forall s, normalize s = s.

  Local Notation gstep := (NC.CausalReplay.gstep act normalize).

  Lemma gstep_id : forall e s, gstep e s = act e s.
  Proof. intros e s. unfold NC.CausalReplay.gstep. apply Hid. Qed.

  Lemma runT_gstep_id : forall u s, runT gstep u s = runT act u s.
  Proof.
    induction u as [| e u IH]; intros s; [reflexivity |].
    rewrite !runT_cons, gstep_id. apply IH.
  Qed.

  Lemma mergeconv_gstep_id : forall X s0,
    NC.CvRDTExact.MergeConv gstep X s0 <-> NC.CvRDTExact.MergeConv act X s0.
  Proof.
    intros X s0. unfold NC.CvRDTExact.MergeConv. split; intros H d1 d2 H1 H2 Heq.
    - rewrite <- !runT_gstep_id. apply H; assumption.
    - rewrite !runT_gstep_id. apply H; assumption.
  Qed.

  (* (a) causal exactly-once delivery: exactly the op-based (CmRDT) commutativity regime. *)
  Theorem cf_causal_boundary : forall hb : E -> E -> Prop, (forall x, ~ hb x x) ->
    ((forall s0, NC.GovernanceConverse.CausalConv gstep hb s0) <->
     NC.CausalReplay.causal_cmrdt act hb).
  Proof.
    intros hb Hirr.
    rewrite (NC.GovernanceConverse.causal_convergence_exact gstep hb Hirr).
    exact (NC.CausalReplay.compensation_free_exact act hb normalize Hid).
  Qed.

  (* (b) unordered at-least-once delivery: exactly commutative-idempotent state evolution on the
     reachable states. *)
  Theorem cf_merge_boundary : forall (dec : forall a b : E, {a = b} + {a <> b}) X s0,
    NC.CvRDTExact.MergeConv gstep X s0 <->
    NC.CvRDTExact.ActComm act X s0 /\ NC.CvRDTExact.ActIdem act X s0.
  Proof.
    intros dec X s0. rewrite mergeconv_gstep_id. exact (NC.CvRDTExact.merge_action_exact dec act X s0).
  Qed.

  (* (b') with a finite event range and decidable state equality: exactly the CvRDT semilattice
     regime on the reachable states. *)
  Theorem cf_cvrdt_boundary : forall (dec : forall a b : E, {a = b} + {a <> b}) X xs,
    (forall e, X e <-> In e xs) -> (forall a b : S, {a = b} + {a <> b}) -> forall s0,
    NC.CvRDTExact.MergeConv gstep X s0 <-> NC.CvRDTExact.CvRDTOn act X s0.
  Proof.
    intros dec X xs Hxs Sdec s0. rewrite mergeconv_gstep_id.
    exact (proj2 (NC.CvRDTExact.cvrdt_exact_all dec act X xs Hxs Sdec s0)).
  Qed.
End CompensationFree.

(* ============================================================================================ *)
(* The witness of CRDT.v, sharpened.                                                            *)
(* ============================================================================================ *)

Section Witness.
  Inductive wev := WSet | WFlip.

  Definition wev_dec : forall a b : wev, {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* Raw transitions: CRDT.v's settrue and flip. *)
  Definition wraw (e : wev) : bool -> bool :=
    match e with WSet => NC.CRDT.settrue | WFlip => NC.CRDT.flip end.

  (* Governed steps: apply, then compensate with CRDT.v's fixb (reset to the valid state). *)
  Definition wgov : wev -> bool -> bool := NC.CausalReplay.gstep wraw NC.CRDT.fixb.

  (* Compensation-free system on the same raw transitions. *)
  Definition wfree : wev -> bool -> bool := NC.CausalReplay.gstep wraw (fun s => s).

  (* Both events are always in range, and neither happens before the other. *)
  Definition wX (_ : wev) : Prop := True.
  Definition whb (_ _ : wev) : Prop := False.

  Lemma wX_list : forall e, wX e <-> In e [WSet; WFlip].
  Proof. intros e. split; [intros _; destruct e; simpl; auto | intros _; exact I]. Qed.

  Lemma whb_irrefl : forall x, ~ whb x x.
  Proof. intros x []. Qed.

  Lemma w_concurrent : NC.CausalReplay.concurrent whb WFlip WSet.
  Proof. split; [discriminate | split; intros []]. Qed.

  (* The specific counterexample: the raw operations do not commute, at any state. *)
  Theorem witness_ops_not_commute :
    NC.CRDT.flip (NC.CRDT.settrue false) = false /\
    NC.CRDT.settrue (NC.CRDT.flip false) = true /\
    (forall s, NC.CRDT.flip (NC.CRDT.settrue s) <> NC.CRDT.settrue (NC.CRDT.flip s)).
  Proof.
    split; [reflexivity | split; [reflexivity |]].
    intros s. unfold NC.CRDT.flip, NC.CRDT.settrue. simpl. discriminate.
  Qed.

  (* No antisymmetric relation makes both raw operations inflationary. *)
  Theorem witness_not_inflationary_antisym :
    ~ exists le : bool -> bool -> Prop,
        (forall a b, le a b -> le b a -> a = b) /\
        (forall s, le s (NC.CRDT.settrue s)) /\
        (forall s, le s (NC.CRDT.flip s)).
  Proof.
    intros [le [Hanti [Hset Hflip]]].
    pose proof (Hset false) as H1. pose proof (Hflip true) as H2.
    unfold NC.CRDT.settrue in H1. unfold NC.CRDT.flip in H2. simpl in H2.
    discriminate (Hanti false true H1 H2).
  Qed.

  (* There is no partial order on bool under which both raw operations are inflationary: the
     raw operations are not monotone state evolution in any join-semilattice on bool. *)
  Theorem witness_not_cvrdt_order :
    ~ exists le : bool -> bool -> Prop,
        (forall s, le s s) /\
        (forall a b, le a b -> le b a -> a = b) /\
        (forall a b c, le a b -> le b c -> le a c) /\
        (forall s, le s (NC.CRDT.settrue s)) /\
        (forall s, le s (NC.CRDT.flip s)).
  Proof.
    intros [le [_ [Hanti [_ [Hset Hflip]]]]].
    apply witness_not_inflationary_antisym. exists le. auto.
  Qed.

  Lemma wraw_reach_init : forall s0, NC.CvRDTExact.Reach wraw wX s0 s0.
  Proof. intros s0. exists []. split; [constructor | reflexivity]. Qed.

  (* As merge actions of a compensation-free registry the raw operations are not a CvRDT, from
     every start state: not commutative, not idempotent (flip), no convergence under unordered
     at-least-once delivery, no semilattice representation on the reachable states. *)
  Theorem witness_not_cvrdt_exact : forall s0,
    ~ NC.CvRDTExact.ActComm wraw wX s0 /\
    ~ NC.CvRDTExact.ActIdem wraw wX s0 /\
    ~ NC.CvRDTExact.MergeConv wraw wX s0 /\
    ~ NC.CvRDTExact.CvRDTOn wraw wX s0.
  Proof.
    intros s0.
    assert (Hidem : ~ NC.CvRDTExact.ActIdem wraw wX s0).
    { intros H. specialize (H s0 WFlip (wraw_reach_init s0) I).
      destruct s0; simpl in H; unfold NC.CRDT.flip in H; simpl in H; discriminate H. }
    assert (Hconv : ~ NC.CvRDTExact.MergeConv wraw wX s0).
    { intros H. apply Hidem. exact (proj2 (proj1 (NC.CvRDTExact.merge_action_exact wev_dec wraw wX s0) H)). }
    split; [| split; [exact Hidem | split; [exact Hconv |]]].
    - intros H. specialize (H s0 WSet WFlip (wraw_reach_init s0) I I).
      simpl in H. unfold NC.CRDT.flip, NC.CRDT.settrue in H. simpl in H. discriminate H.
    - intros H. apply Hconv. exact (NC.CvRDTExact.cvrdt_on_conv wev_dec wraw wX s0 H).
  Qed.

  (* The concrete divergence under duplication: flip delivered once vs twice. *)
  Example witness_duplicate_diverges :
    runT wraw [WFlip] false <> runT wraw [WFlip; WFlip] false.
  Proof. simpl. unfold NC.CRDT.flip. simpl. discriminate. Qed.

  Lemma w_causal_pair : forall a b, a <> b -> NC.CausalReplay.causal whb [a; b].
  Proof.
    intros a b Hne. split.
    - constructor; [intros [E | []]; apply Hne; symmetry; exact E | constructor; [intros [] | constructor]].
    - intros x y [].
  Qed.

  (* Under causal exactly-once delivery (the two events concurrent) the raw operations diverge
     from every start: [WSet; WFlip] ends at false, [WFlip; WSet] at true. *)
  Theorem witness_raw_not_causal : forall s0,
    ~ NC.GovernanceConverse.CausalConv wraw whb s0.
  Proof.
    intros s0 H.
    specialize (H [WSet; WFlip] [WFlip; WSet] (w_causal_pair WSet WFlip ltac:(discriminate))
                  (w_causal_pair WFlip WSet ltac:(discriminate)) (perm_swap WFlip WSet [])).
    unfold NC.CausalReplay.run in H. simpl in H. unfold NC.CRDT.flip, NC.CRDT.settrue in H.
    simpl in H. discriminate H.
  Qed.

  (* The governed behavior is trivial: every nonempty delivery ends at false, the governed steps
     commute and are idempotent at every state, and they form a state-based CRDT on bool with the
     join andb (false is the top element). *)
  Lemma wgov_false : forall e s, wgov e s = false.
  Proof. reflexivity. Qed.

  Lemma wgov_run_false : forall e u s, runT wgov (e :: u) s = false.
  Proof.
    intros e u. induction u as [| x u IH] using rev_ind; intros s; [reflexivity |].
    rewrite app_comm_cons, runT_app. reflexivity.
  Qed.

  Theorem witness_governed_constant :
    (forall e u s, runT wgov (e :: u) s = false) /\
    (forall a b s, wgov a (wgov b s) = wgov b (wgov a s)) /\
    (forall a s, wgov a (wgov a s) = wgov a s) /\
    (forall s0, NC.CvRDTExact.CvRDTOn wgov wX s0).
  Proof.
    split; [exact wgov_run_false | split; [reflexivity | split; [reflexivity |]]].
    intros s0. exists andb. split; [split; [| split; [| split]] |].
    - intros s t Hs Ht. destruct (andb s t) eqn:E.
      + apply andb_true_iff in E. destruct E as [-> ->]. exact Hs.
      + exists [WSet]. split; [constructor; [exact I | constructor] | reflexivity].
    - intros s t _ _. apply andb_comm.
    - intros s t r _ _ _. symmetry. apply andb_assoc.
    - intros s _. apply andb_diag.
    - intros s e _ _. rewrite wgov_false, wgov_false. symmetry. apply andb_false_r.
  Qed.

  (* The governed machine converges under both delivery models, from every start. *)
  Theorem witness_governed_converges :
    (forall s0, NC.GovernanceConverse.CausalConv wgov whb s0) /\
    (forall s0, NC.CvRDTExact.MergeConv wgov wX s0).
  Proof.
    split.
    - apply (proj2 (NC.GovernanceConverse.causal_convergence_exact wgov whb whb_irrefl)).
      intros a b s _. reflexivity.
    - intros s0. apply (proj2 (NC.CvRDTExact.merge_action_exact wev_dec wgov wX s0)).
      split; [intros s x y _ _ _ | intros s x _ _]; reflexivity.
  Qed.
End Witness.

(* ============================================================================================ *)
(* The boundary theorem.                                                                        *)
(* ============================================================================================ *)

(* Remove compensation and the CRDT algebra is exactly the convergence condition that remains:
   (a) causal exactly-once delivery: CmRDT commutativity; (b) unordered at-least-once delivery:
   commutative-idempotent state evolution on reachable states, and with a finite event range and
   decidable state equality, a CvRDT semilattice on reachable states. Restore compensation and the
   class is strictly larger on the same transition representation (c). *)
Theorem crdt_boundary :
  (forall (S E : Type) (act : E -> S -> S) (normalize : S -> S),
     (forall s, normalize s = s) ->
     (* (a) *)
     (forall hb : E -> E -> Prop, (forall x, ~ hb x x) ->
        ((forall s0, NC.GovernanceConverse.CausalConv (NC.CausalReplay.gstep act normalize) hb s0)
         <-> NC.CausalReplay.causal_cmrdt act hb)) /\
     (* (b) *)
     (forall (dec : forall a b : E, {a = b} + {a <> b}) (X : E -> Prop) (s0 : S),
        NC.CvRDTExact.MergeConv (NC.CausalReplay.gstep act normalize) X s0 <->
        NC.CvRDTExact.ActComm act X s0 /\ NC.CvRDTExact.ActIdem act X s0) /\
     (* (b') *)
     (forall (dec : forall a b : E, {a = b} + {a <> b}) (X : E -> Prop) (xs : list E),
        (forall e, X e <-> In e xs) -> (forall a b : S, {a = b} + {a <> b}) -> forall s0,
        NC.CvRDTExact.MergeConv (NC.CausalReplay.gstep act normalize) X s0 <->
        NC.CvRDTExact.CvRDTOn act X s0)) /\
  (* (c) *)
  ((forall s0, NC.GovernanceConverse.CausalConv wgov whb s0) /\
   (forall s0, NC.CvRDTExact.MergeConv wgov wX s0) /\
   ~ NC.CausalReplay.causal_cmrdt wraw whb /\
   ~ (forall s0, NC.GovernanceConverse.CausalConv wfree whb s0) /\
   (forall s0, ~ (NC.CvRDTExact.ActComm wraw wX s0 /\ NC.CvRDTExact.ActIdem wraw wX s0)) /\
   (forall s0, ~ NC.CvRDTExact.MergeConv wfree wX s0) /\
   (forall s0, ~ NC.CvRDTExact.CvRDTOn wraw wX s0)).
Proof.
  split.
  - intros S E act normalize Hid. split; [| split].
    + exact (cf_causal_boundary act normalize Hid).
    + exact (cf_merge_boundary act normalize Hid).
    + exact (cf_cvrdt_boundary act normalize Hid).
  - destruct witness_governed_converges as [HC HM].
    assert (Hnc : ~ NC.CausalReplay.causal_cmrdt wraw whb).
    { intros H. specialize (H WFlip WSet false w_concurrent).
      simpl in H. unfold NC.CRDT.flip, NC.CRDT.settrue in H. simpl in H. discriminate H. }
    split; [exact HC | split; [exact HM | split; [exact Hnc | split; [| split; [| split]]]]].
    + intros H. apply Hnc.
      exact (proj1 (cf_causal_boundary wraw (fun s => s) (fun s => eq_refl) whb whb_irrefl) H).
    + intros s0 [HAC _]. exact (proj1 (witness_not_cvrdt_exact s0) HAC).
    + intros s0 H. apply (proj1 (proj2 (proj2 (witness_not_cvrdt_exact s0)))).
      exact (proj1 (mergeconv_gstep_id wraw (fun s => s) (fun s => eq_refl) wX s0) H).
    + intros s0. exact (proj2 (proj2 (proj2 (witness_not_cvrdt_exact s0)))).
Qed.

(* ============================================================================================ *)
(* Non-vacuity of the boundary's hypotheses.                                                    *)
(* ============================================================================================ *)

(* The constant action (the witness's governed step read as a raw transition): compensation-free,
   and it satisfies every CRDT condition. *)
Definition wconst (_ : wev) (_ : bool) : bool := false.

Theorem boundary_nonvacuous :
  (* the hypotheses of (a), (b), (b') hold for the witness's events, range and order *)
  (forall x, ~ whb x x) /\ (forall e, wX e <-> In e [WSet; WFlip]) /\
  inhabited (forall a b : wev, {a = b} + {a <> b}) /\
  inhabited (forall a b : bool, {a = b} + {a <> b}) /\
  (* with the raw witness operations, both sides of (a) and (b') are false *)
  ~ NC.CausalReplay.causal_cmrdt wraw whb /\ ~ NC.CvRDTExact.CvRDTOn wraw wX false /\
  (* with the constant action, both sides are true *)
  NC.CausalReplay.causal_cmrdt wconst whb /\
  (forall s0, NC.GovernanceConverse.CausalConv (NC.CausalReplay.gstep wconst (fun s => s)) whb s0) /\
  (forall s0, NC.CvRDTExact.CvRDTOn wconst wX s0) /\
  (forall s0, NC.CvRDTExact.MergeConv (NC.CausalReplay.gstep wconst (fun s => s)) wX s0).
Proof.
  destruct crdt_boundary as [HB [_ [_ [Hnc [_ [_ [_ Hcv]]]]]]].
  assert (Hcc : NC.CausalReplay.causal_cmrdt wconst whb) by (intros a b s _; reflexivity).
  assert (Hon : forall s0, NC.CvRDTExact.CvRDTOn wconst wX s0).
  { intros s0. destruct witness_governed_constant as [_ [_ [_ H]]]. exact (H s0). }
  split; [exact whb_irrefl | split; [exact wX_list | split; [exact (inhabits wev_dec) | split; [exact (inhabits bool_dec) |]]]].
  split; [exact Hnc | split; [exact (Hcv false) | split; [exact Hcc | split; [| split; [exact Hon |]]]]].
  - apply (proj2 (proj1 (HB bool wev wconst (fun s => s) (fun s => eq_refl)) whb whb_irrefl)). exact Hcc.
  - intros s0.
    apply (proj2 (proj2 (proj2 (HB bool wev wconst (fun s => s) (fun s => eq_refl))) wev_dec wX
                   [WSet; WFlip] wX_list bool_dec s0)).
    exact (Hon s0).
Qed.
