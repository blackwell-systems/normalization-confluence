(* RootSetEvents.v: the EXACT event-order condition under root-set coordination of a lossy
   (non-invertible) network, mechanized axiom-free. This closes the row "Event order under
   root-set coordination (non-invertible driving forest)" of REGIME-AUDIT section 12
   (LOSSY-NETWORKS.md P6).

   The gap. CoordinatedExact.v gives the exact event-order condition when values are driven along
   a spanning TREE of a group-labeled graph (invertible transports): interleavings converge iff
   the root's independent events commute at every root value its events can reach. RootSet.v
   drives values from a ROOT SET R along an outward spanning forest F with arbitrary (lossy)
   maps. This file puts the two together.

   The driving network of a forest (fsrc, ffun). Each vertex w attached by a forest edge
   (u, w, f) reads only its forest parent u and takes f (s u), ignoring its own value; a root
   keeps its own value; every other registry is untouched. Non-driving edges X (the edges of the
   graph outside F) never write: they are kept as constraints checked on the result, or
   coordinated away. Because a forest attaches each vertex once, every vertex has exactly one
   driver, so the network is acyclic and satisfies FederationEvents.Common (forest_common).
   FederationEventsConverse (acyclic_gc_iff, fed_exact, fed_exact_full) then applies unchanged.

   Setting of the main section: R a root list, F an outward spanning forest from R
   (RootSet.oforest R F), o a topological order of the driving network (FederationEvents.topoF)
   over exactly R ++ verts F, and local events (E, reg, sig) on those registries, with any
   declared same-registry independence J. Runs are FedMachine.Apply sequences (runF) with the
   identity normalizer; a start s0 is any morphism-consistent state (Cons) of the network, which
   is the same as a section of F (Cons_msection, msection_Cons).

   1. The network and its order.
      - forest_network_shape: roots keep their value, a forest edge (u, w, f) gives w the step
        x |-> f (s u), registries off R ++ verts F are untouched.
      - forest_order, forest_order_set: with R duplicate free, R followed by the forest's
        targets in order is a topological order over exactly R ++ verts F, so the hypothesis on
        o is always satisfiable.

   2. C1 and C2 on the forest, concretely.
      - forest_c1_static, forest_c1r1: C1 holds unconditionally (statically, and at every
        reachable witness). A driven target is overwritten by f (z u) on both sides; a root's
        repair is the identity, so both sides are sig e b.
      - forest_c2at_iff: C2 at a reachable witness s is trivial on driven registries, and on a
        root r it is exactly sig e2 (sig e1 (s r)) = sig e1 (sig e2 (s r)).
      - forest_c2_static_iff: static C2 holds iff every two J-independent events of every root
        commute at every value.

   3. The exact condition (forest_events_exact): for every consistent start s0,
        TraceConv s0  <->  for every root r in R, RootCC r J (s0 r)
      where CoordinatedExact.RootCC r J x0 says every two J-independent events of r commute at
      every value reachable from x0 by r's own events. The condition is a conjunction of one
      independent condition per root. Permutation form: forest_perm_exact. Uniform form
      (forest_events_exact_global, forest_global_iff_static): convergence from EVERY consistent
      start iff every root's independent events commute at every value, iff static C1 /\ C2.

   4. Different roots do not interact.
      - forest_root_run: the value of root r after a run is s0 r pushed through r's own events
        only (rrun of the filtered list).
      - forest_run_formula, forest_run_single_root: every vertex w of the network after a run
        is p w applied to the run of ONE root rho w (its driving root) on that root's own
        events. A vertex reached from two roots in the graph (two incoming edges from different
        trees) is still driven by one of them: the other edge is non-driving, it lies in X.
      - forest_runs_by_root: two runs that agree on each root's subsequence reach the same state;
        forest_cross_commute: events of different registries commute from every consistent
        state; forest_driven_noop: an event on a driven registry is overwritten (no effect).
      So there is no counterexample in which events of two roots fail to commute; the only
      cross-root coupling is through the kept constraints:
      - forest_runs_kept: every reached state is a section of F, and it is a section of F ++ X
        iff the run's root values (each root's own run) form a consistent root assignment in the
        sense of RootSet.root_set_criterion. Whether X holds at the result depends on the joint
        root values, but the result itself does not depend on the interleaving of different
        roots' events.

   5. The group case recovered (Section Recover). The driving network dfun of a spanning tree T
      from r (CoordinatedCycles, edges in either direction, driven against a morphism through
      the inverse) is the forest network of tforest r T, the outward forest from [r] with the
      maps tr g b (tforest_props, dfun_ffun, dsrc_fsrc). Since runF depends on the step function
      only pointwise (runF_fext), coordinated_events_exact_recovered re-derives
      CoordinatedExact.coordinated_events_exact as the case R = [r], and
      coordinated_events_exact_global_recovered its uniform form. recovered_klein instantiates
      it on CoordinatedExact's Klein tree.

   6. Non-vacuity and counterexamples, on a two-root lossy network over nat (the tw_ results):
        roots 0 and 1; forest F = [(0, 2, par); (1, 3, cap1)] with par x = x mod 2 and
        cap1 x = min x 1 (both lossy); non-driving edge X = [(1, 2, par)], so vertex 2 is
        reached from both roots. Events: Dbl (x |-> 2x) and Clamp (x |-> min x 5) on root 0,
        Inc on root 1, Poke (write 7) on the driven vertex 2.
      - tw_root_set: {0, 1} is a root set of F ++ X and neither root alone is; F is a spanning
        forest; vertex 2 is reachable from both roots.
      - tw_converges_at_zero: from every consistent start with root 0 at value 0, every
        permutation of events converges (Dbl and Clamp both fix 0).
      - tw_diverges_at_three: from a consistent start with root 0 at value 3, Dbl and Clamp do
        not commute (5 versus 6 at root 0, 1 versus 0 at the driven vertex 2).
      - tw_reachable_matters: at root value 1 Dbl and Clamp commute, yet from a start with root
        0 at 1 the runs Dbl Dbl Dbl Clamp and Dbl Dbl Clamp Dbl diverge (5 versus 8), because 4
        is reachable. The reachable-value qualifier of the exact condition is needed.
      - tw_not_global: so convergence fails from some consistent start; the uniform condition is
        strictly stronger than the per-start one (the fixed-start divergence versus convergence).
      - tw_cross_roots, tw_poke_noop, tw_vertex2: root 0 and root 1 events commute from every
        consistent start (even from the start where root 0's own events do not); Poke is
        overwritten; vertex 2 depends on root 0's events only.
      - tw_constraint: the cross-root constraint X holds from the zero start, fails after one Inc
        on root 1, and holds again after two: coupling through constraints, not through order.

   States are compared pointwise, so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.CohomologyGraph NC.CohomologyGeneral.
Require NC.Trace NC.FederationOrder NC.FederationEvents NC.FederationEventsConverse
  NC.CoordinatedCycles NC.CoordinatedExact NC.RootSet.
Import ListNotations.

(* ===================================================================== *)
(* The driving network of a forest. *)

Section Network.
  Context {V : Type}.

  (* The driver of w: Some (parent, map) if w is the target of a forest edge. The list is scanned
     from its last edge, so the snoc structure of RootSet.oforest is easy to follow. *)
  Fixpoint fruleR (l : list (@edge (V -> V))) (w : nat) : option (nat * (V -> V)) :=
    match l with
    | [] => None
    | (u, v, f) :: rest => if Nat.eq_dec w v then Some (u, f) else fruleR rest w
    end.

  Definition frule (F : list (@edge (V -> V))) (w : nat) : option (nat * (V -> V)) :=
    fruleR (rev F) w.

  Definition fsrc (F : list (@edge (V -> V))) (w : nat) : list nat :=
    match frule F w with Some (u, _) => [u] | None => [] end.

  Definition ffun (F : list (@edge (V -> V))) (w : nat) (s : nat -> V) (x : V) : V :=
    match frule F w with Some (u, f) => f (s u) | None => x end.

  Definition targets (F : list (@edge (V -> V))) : list nat :=
    map (fun x : @edge (V -> V) => let '(_, v, _) := x in v) F.

  Lemma frule_nil : forall w, frule [] w = None.
  Proof. reflexivity. Qed.

  Lemma frule_snoc : forall es u v f w,
    frule (es ++ [(u, v, f)]) w = if Nat.eq_dec w v then Some (u, f) else frule es w.
  Proof. intros. unfold frule. rewrite rev_app_distr. reflexivity. Qed.

  Lemma targets_snoc : forall es u v (f : V -> V), targets (es ++ [(u, v, f)]) = targets es ++ [v].
  Proof. intros. unfold targets. rewrite map_app. reflexivity. Qed.

  Lemma targets_in_verts : forall F w, In w (targets F) -> In w (verts F).
  Proof.
    induction F as [| [[u v] f] F IH]; intros w H; simpl in *; [exact H |].
    destruct H as [H | H]; [right; left; exact H | right; right; apply IH; exact H].
  Qed.

  Lemma in_lift : forall (R : list nat) (es l : list (@edge (V -> V))) w,
    In w (R ++ verts es) -> In w (R ++ verts (es ++ l)).
  Proof.
    intros R es l w H. rewrite verts_app. apply in_app_or in H. apply in_or_app.
    destruct H as [H | H]; [left; exact H | right; apply in_or_app; left; exact H].
  Qed.

  Lemma new_in : forall (R : list nat) (es : list (@edge (V -> V))) u v f,
    In v (R ++ verts (es ++ [(u, v, f)])).
  Proof.
    intros. apply in_or_app. right. rewrite verts_app. apply in_or_app. right. right. left.
    reflexivity.
  Qed.

  (* A driver is a forest edge; its parent is reached; a root is never driven. *)
  Lemma frule_some : forall R F, RootSet.oforest R F -> forall w u f, frule F w = Some (u, f) ->
    In (u, w, f) F /\ In u (R ++ verts F) /\ ~ In w R.
  Proof.
    intros R F HF. induction HF as [| es u0 v0 f0 HF IH Hu Hv]; intros w u f H.
    - rewrite frule_nil in H. discriminate.
    - rewrite frule_snoc in H. destruct (Nat.eq_dec w v0) as [-> | Hne].
      + injection H as Eu Ef. subst u f. split; [| split].
        * apply in_or_app. right. left. reflexivity.
        * apply in_lift. exact Hu.
        * intro Hr. apply Hv. apply in_or_app. left. exact Hr.
      + destruct (IH w u f H) as [Hin [Hp Hr]]. split; [| split].
        * apply in_or_app. left. exact Hin.
        * apply in_lift. exact Hp.
        * exact Hr.
  Qed.

  Lemma frule_in : forall R F, RootSet.oforest R F -> forall u v f, In (u, v, f) F ->
    frule F v = Some (u, f).
  Proof.
    intros R F HF. induction HF as [| es u0 v0 f0 HF IH Hu Hv]; intros u v f H; [destruct H |].
    rewrite frule_snoc. apply in_app_or in H. destruct H as [H | [H | []]].
    - destruct (Nat.eq_dec v v0) as [-> | Hne]; [| exact (IH u v f H)].
      exfalso. apply Hv. apply in_or_app. right. exact (proj2 (in_verts_edge es u v0 f H)).
    - injection H as Eu Ev Ef. subst.
      match goal with |- context [Nat.eq_dec ?a ?a] =>
        destruct (Nat.eq_dec a a) as [_ | C]; [reflexivity | contradiction] end.
  Qed.

  Lemma frule_root : forall R F, RootSet.oforest R F -> forall r, In r R -> frule F r = None.
  Proof.
    intros R F HF r Hr. destruct (frule F r) as [[u f] |] eqn:H; [| reflexivity].
    exfalso. exact (proj2 (proj2 (frule_some R F HF r u f H)) Hr).
  Qed.

  Lemma frule_driven : forall R F, RootSet.oforest R F -> forall w, In w (R ++ verts F) ->
    ~ In w R -> exists u f, frule F w = Some (u, f).
  Proof.
    intros R F HF. induction HF as [| es u0 v0 f0 HF IH Hu Hv]; intros w Hw Hr.
    - simpl in Hw. rewrite app_nil_r in Hw. contradiction.
    - rewrite frule_snoc. destruct (Nat.eq_dec w v0) as [-> | Hne]; [do 2 eexists; reflexivity |].
      destruct (RootSet.verts_snoc_set R es u0 v0 f0 w Hw) as [Hold | [-> | ->]].
      + exact (IH w Hold Hr).
      + exact (IH u0 Hu Hr).
      + contradiction.
  Qed.

  Lemma frule_off : forall R F, RootSet.oforest R F -> forall w, ~ In w (R ++ verts F) ->
    frule F w = None.
  Proof.
    intros R F HF w Hw. destruct (frule F w) as [[u f] |] eqn:H; [| reflexivity].
    exfalso. apply Hw. apply in_or_app. right.
    exact (proj2 (in_verts_edge F u w f (proj1 (frule_some R F HF w u f H)))).
  Qed.

  Lemma verts_in_targets : forall R F, RootSet.oforest R F -> forall w,
    In w (R ++ verts F) -> In w (R ++ targets F).
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv]; intros w Hw.
    - exact Hw.
    - rewrite targets_snoc, app_assoc. apply in_or_app.
      destruct (RootSet.verts_snoc_set R es u v f w Hw) as [Hold | [-> | ->]].
      + left. exact (IH w Hold).
      + left. exact (IH u Hu).
      + right. left. reflexivity.
  Qed.

  (* ----- topological orders of the forest network ----- *)

  Lemma topoF_ext : forall (src1 src2 : nat -> list nat) l,
    (forall w, In w l -> src1 w = src2 w) ->
    FederationEvents.topoF src1 l -> FederationEvents.topoF src2 l.
  Proof.
    intros src1 src2. induction l as [| a l IH]; intros He H; [exact I |].
    destruct H as [Ha [Hs Hl]]. split; [exact Ha | split].
    - intros k Hk. rewrite <- (He a (or_introl eq_refl)) in Hk. exact (Hs k Hk).
    - apply IH; [intros w Hw; apply He; right; exact Hw | exact Hl].
  Qed.

  Lemma topoF_nodup_nil : forall (src : nat -> list nat) l, NoDup l ->
    (forall w, In w l -> src w = []) -> FederationEvents.topoF src l.
  Proof.
    intros src l Hl. induction Hl as [| a l Ha Hl IH]; intros Hs; [exact I |].
    split; [exact Ha | split].
    - intros k Hk. rewrite (Hs a (or_introl eq_refl)) in Hk. destruct Hk.
    - apply IH. intros w Hw. apply Hs. right. exact Hw.
  Qed.

  Lemma topoF_snoc : forall (src : nat -> list nat) l v,
    FederationEvents.topoF src l -> ~ In v l -> ~ In v (src v) ->
    (forall a, In a l -> ~ In v (src a)) -> FederationEvents.topoF src (l ++ [v]).
  Proof.
    intros src l v. induction l as [| a l IH]; intros H Hv Hvv Ha.
    - simpl. split; [intros [] | split; [| exact I]].
      intros k Hk [E | []]. subst. exact (Hvv Hk).
    - destruct H as [Hal [Hs Hl]]. simpl. split; [| split].
      + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | [E | []]];
          [exact (Hal Hin) | subst; apply Hv; left; reflexivity].
      + intros k Hk [E | Hin]; [exact (Hs k Hk (or_introl E)) |].
        apply in_app_or in Hin. destruct Hin as [Hin | [E | []]];
          [exact (Hs k Hk (or_intror Hin)) | subst; exact (Ha a (or_introl eq_refl) Hk)].
      + apply IH; [exact Hl | intro Hin; apply Hv; right; exact Hin | exact Hvv |].
        intros b Hb. apply Ha. right. exact Hb.
  Qed.

  (* R followed by the forest's targets, in order, is a topological order. *)
  Theorem forest_order : forall R F, NoDup R -> RootSet.oforest R F ->
    FederationEvents.topoF (fsrc F) (R ++ targets F).
  Proof.
    intros R F HR HF. induction HF as [| es u v f HF IH Hu Hv].
    - simpl. rewrite app_nil_r. apply topoF_nodup_nil; [exact HR |].
      intros w _. reflexivity.
    - assert (Hold : forall w, In w (R ++ targets es) -> In w (R ++ verts es)).
      { intros w Hw. apply in_app_or in Hw. apply in_or_app.
        destruct Hw as [Hw | Hw]; [left; exact Hw | right; apply targets_in_verts; exact Hw]. }
      assert (Hsrc : forall w, In w (R ++ targets es) -> fsrc es w = fsrc (es ++ [(u, v, f)]) w).
      { intros w Hw. unfold fsrc. rewrite frule_snoc. destruct (Nat.eq_dec w v) as [-> | _];
          [exfalso; exact (Hv (Hold v Hw)) | reflexivity]. }
      rewrite targets_snoc, app_assoc. apply topoF_snoc.
      + apply (topoF_ext (fsrc es)); [exact Hsrc | exact IH].
      + intro H. exact (Hv (Hold v H)).
      + unfold fsrc. rewrite frule_snoc. destruct (Nat.eq_dec v v) as [_ | C]; [| contradiction].
        intros [E | []]. subst. exact (Hv Hu).
      + intros a Ha. rewrite <- (Hsrc a Ha). unfold fsrc.
        destruct (frule es a) as [[p g] |] eqn:Hr; [| intros []].
        intros [E | []]. subst p. apply Hv. exact (proj1 (proj2 (frule_some R es HF a v g Hr))).
  Qed.

  Theorem forest_order_set : forall R F, RootSet.oforest R F ->
    forall w, In w (R ++ targets F) <-> In w (R ++ verts F).
  Proof.
    intros R F HF w. split; [| apply verts_in_targets; exact HF].
    intro Hw. apply in_app_or in Hw. apply in_or_app.
    destruct Hw as [Hw | Hw]; [left; exact Hw | right; apply targets_in_verts; exact Hw].
  Qed.

  (* ----- the network satisfies Common ----- *)

  Lemma ffun_local : forall F i s1 s2 x, (forall k, In k (fsrc F i) -> s1 k = s2 k) ->
    ffun F i s1 x = ffun F i s2 x.
  Proof.
    intros F i s1 s2 x H. unfold ffun, fsrc in *.
    destruct (frule F i) as [[u f] |]; [rewrite (H u (or_introl eq_refl)) |]; reflexivity.
  Qed.

  Lemma forest_common : forall F o (E : Type) (reg : E -> nat) (sig : E -> V -> V),
    FederationEvents.topoF (fsrc F) o -> (forall ev, In (reg ev) o) ->
    FederationEvents.Common V (fsrc F) (ffun F) (fun _ _ => True) (fun _ x => x) E reg sig o.
  Proof.
    intros F o E reg sig Ho Hreg. constructor.
    - apply ffun_local.
    - exact Ho.
    - intros; exact I.
    - intros j z z' x _ _ _. unfold ffun. destruct (frule F j) as [[u f] |]; reflexivity.
    - intros; reflexivity.
    - intros; exact I.
    - exact Hreg.
  Qed.

  (* runF depends on the step function only pointwise. *)
  Lemma runF_fext : forall (f1 f2 : nat -> (nat -> V) -> V -> V),
    (forall j t x, f1 j t x = f2 j t x) ->
    forall rho E reg sig o es s,
      FederationEvents.runF V f1 rho E reg sig o es s = FederationEvents.runF V f2 rho E reg sig o es s.
  Proof.
    intros f1 f2 Hf rho E reg sig o.
    assert (Hfr : forall l t, FederationEvents.frun V f1 l t = FederationEvents.frun V f2 l t).
    { induction l as [| a l IH]; intro t; [reflexivity |].
      change (FederationEvents.frun V f1 (a :: l) t)
        with (FederationEvents.frun V f1 l (FederationEvents.fstep V f1 t a)).
      change (FederationEvents.frun V f2 (a :: l) t)
        with (FederationEvents.frun V f2 l (FederationEvents.fstep V f2 t a)).
      rewrite IH. unfold FederationEvents.fstep. rewrite Hf. reflexivity. }
    induction es as [| a es IH]; intro s; [reflexivity |].
    change (FederationEvents.runF V f1 rho E reg sig o (a :: es) s)
      with (FederationEvents.runF V f1 rho E reg sig o es (FederationEvents.applyF V f1 rho E reg sig o a s)).
    change (FederationEvents.runF V f2 rho E reg sig o (a :: es) s)
      with (FederationEvents.runF V f2 rho E reg sig o es (FederationEvents.applyF V f2 rho E reg sig o a s)).
    rewrite IH. unfold FederationEvents.applyF, FederationEvents.N. rewrite Hfr. reflexivity.
  Qed.
End Network.

(* ===================================================================== *)
(* Events under root-set coordination. *)

Section Events.
  Context {V : Type}.
  Variables (R : list nat) (F : list (@edge (V -> V))) (o : list nat).
  Hypothesis HF : RootSet.oforest R F.
  Hypothesis Ho : FederationEvents.topoF (fsrc F) o.
  Hypothesis Hset : forall w, In w o <-> In w (R ++ verts F).
  Variables (E : Type) (reg : E -> nat) (sig : E -> V -> V).
  Hypothesis Hreg : forall ev, In (reg ev) o.

  Local Notation FF := (ffun F).
  Local Notation idN := (fun (_ : nat) (x : V) => x).
  Local Notation rF := (FederationEvents.runF V FF idN E reg sig o).
  Local Notation aF := (FederationEvents.applyF V FF idN E reg sig o).
  Local Notation ConsD := (FederationEvents.Cons V FF o).
  Local Notation rrun := (CoordinatedExact.rrun E sig).
  Local Notation proj r p := (filter (fun ev => Nat.eqb (reg ev) r) p).

  Lemma HC : FederationEvents.Common V (fsrc F) FF (fun _ _ => True) idN E reg sig o.
  Proof. exact (forest_common F o E reg sig Ho Hreg). Qed.

  Lemma Inv_all : forall s, FederationEvents.Inv V (fun _ _ => True) s.
  Proof. intros s k. exact I. Qed.

  Lemma ffun_root : forall r s x, In r R -> FF r s x = x.
  Proof. intros r s x Hr. unfold ffun. rewrite (frule_root R F HF r Hr). reflexivity. Qed.

  Lemma in_o_root : forall r, In r R -> In r o.
  Proof. intros r Hr. apply Hset. apply in_or_app. left. exact Hr. Qed.

  Lemma reg_cases : forall ev, In (reg ev) R \/ exists u f, frule F (reg ev) = Some (u, f).
  Proof.
    intro ev. destruct (in_dec Nat.eq_dec (reg ev) R) as [Hr | Hr]; [left; exact Hr | right].
    exact (frule_driven R F HF (reg ev) (proj1 (Hset _) (Hreg ev)) Hr).
  Qed.

  (* ----- the shape of the network ----- *)

  Theorem forest_network_shape :
    (forall r s x, In r R -> FF r s x = x) /\
    (forall u w f s x, In (u, w, f) F -> FF w s x = f (s u)) /\
    (forall w s x, ~ In w (R ++ verts F) -> FF w s x = x).
  Proof.
    split; [exact ffun_root | split].
    - intros u w f s x H. unfold ffun. rewrite (frule_in R F HF u w f H). reflexivity.
    - intros w s x Hw. unfold ffun. rewrite (frule_off R F HF w Hw). reflexivity.
  Qed.

  (* Consistent states of the network are exactly the sections of the forest. *)
  Lemma Cons_msection : forall t, ConsD t -> msection t F.
  Proof.
    intros t Hc [[u v] f] Hx. unfold msat.
    assert (Hv : In v o).
    { apply Hset. apply in_or_app. right. exact (proj2 (in_verts_edge F u v f Hx)). }
    rewrite (Hc v Hv). unfold ffun. rewrite (frule_in R F HF u v f Hx). reflexivity.
  Qed.

  Lemma msection_Cons : forall t, msection t F -> ConsD t.
  Proof.
    intros t Hs j _. unfold ffun. destruct (frule F j) as [[u f] |] eqn:Hr; [| reflexivity].
    pose proof (Hs _ (proj1 (frule_some R F HF j u f Hr))) as H. unfold msat in H.
    symmetry. exact H.
  Qed.

  Theorem forest_cons_iff : forall t, ConsD t <-> msection t F.
  Proof. intro t. split; [apply Cons_msection | apply msection_Cons]. Qed.

  Lemma drive_Cons : forall a, ConsD (RootSet.drive F a).
  Proof. intro a. apply msection_Cons. exact (RootSet.out_forest_section R F HF a). Qed.

  (* ----- one step, at a root and off the network ----- *)

  Lemma applyF_root : forall r ev s, In r R ->
    aF ev s r = if Nat.eq_dec (reg ev) r then sig ev (s r) else s r.
  Proof.
    intros r ev s Hr. unfold FederationEvents.applyF, FederationEvents.N.
    rewrite (FederationEvents.frun_solves _ _ _ _ _ _ _ _ _ HC o _ Ho r (in_o_root r Hr)).
    rewrite (ffun_root r _ _ Hr). unfold FederationEvents.evstep.
    destruct (Nat.eq_dec (reg ev) r) as [Er | Er].
    - rewrite <- Er. apply FederationEvents.upd_eq.
    - apply FederationEvents.upd_neq. intro H. apply Er. symmetry. exact H.
  Qed.

  Lemma applyF_off : forall w ev s, ~ In w o -> aF ev s w = s w.
  Proof.
    intros w ev s Hw. unfold FederationEvents.applyF, FederationEvents.N.
    rewrite (FederationEvents.frun_out V FF o _ w Hw).
    apply FederationEvents.evstep_off. intro E'. subst. exact (Hw (Hreg ev)).
  Qed.

  Lemma run_off : forall w es s, ~ In w o -> rF es s w = s w.
  Proof.
    intros w es. induction es as [| a es IH]; intros s Hw; [reflexivity |].
    change (rF (a :: es) s) with (rF es (aF a s)). rewrite (IH _ Hw). exact (applyF_off w a s Hw).
  Qed.

  (* ----- the root values of a run ----- *)

  Theorem forest_root_run : forall r p s, In r R -> rF p s r = rrun (proj r p) (s r).
  Proof.
    intros r p. induction p as [| a p IH]; intros s Hr; [reflexivity |].
    change (rF (a :: p) s) with (rF p (aF a s)). rewrite (IH _ Hr), (applyF_root r a s Hr).
    cbn [filter]. destruct (Nat.eq_dec (reg a) r) as [Er | Er].
    - rewrite (proj2 (Nat.eqb_eq _ _) Er). reflexivity.
    - rewrite (proj2 (Nat.eqb_neq _ _) Er). reflexivity.
  Qed.

  Theorem forest_root_reach : forall r p s, In r R ->
    CoordinatedExact.RootReach r E reg sig (s r) (rF p s r).
  Proof.
    intros r p s Hr. exists (proj r p). split.
    - apply Forall_forall. intros x Hx. apply filter_In in Hx. apply Nat.eqb_eq. exact (proj2 Hx).
    - apply forest_root_run. exact Hr.
  Qed.

  Lemma filter_only : forall r q, Forall (fun ev => reg ev = r) q -> proj r q = q.
  Proof.
    intros r. induction q as [| a q IH]; intros H; [reflexivity |].
    inversion H as [| ? ? Ha Hq]. cbn [filter].
    rewrite (proj2 (Nat.eqb_eq _ _) Ha), (IH Hq). reflexivity.
  Qed.

  Lemma root_only_run : forall r q s, In r R -> Forall (fun ev => reg ev = r) q ->
    rF q s r = rrun q (s r).
  Proof. intros r q s Hr Hq. rewrite (forest_root_run r q s Hr), (filter_only r q Hq). reflexivity. Qed.

  (* ----- C1 and C2 on the forest ----- *)

  Theorem forest_c1_static : FederationEvents.C1 V FF (fun _ _ => True) E reg sig.
  Proof.
    intros ev z z' b _ _ _ _. unfold ffun.
    destruct (frule F (reg ev)) as [[u f] |]; reflexivity.
  Qed.

  Theorem forest_c1r1 : forall s0, FederationEventsConverse.C1R1 V FF idN E reg sig o s0.
  Proof.
    intros s0 p ev a _. unfold FederationEventsConverse.C1at, ffun.
    destruct (frule F (reg ev)) as [[u f] |]; reflexivity.
  Qed.

  Theorem forest_c2at_iff : forall s e1 e2, reg e1 = reg e2 ->
    (FederationEventsConverse.C2at V FF E reg sig s e1 e2 <->
     (In (reg e1) R -> sig e2 (sig e1 (s (reg e1))) = sig e1 (sig e2 (s (reg e1))))).
  Proof.
    intros s e1 e2 _. unfold FederationEventsConverse.C2at.
    destruct (reg_cases e1) as [Hr | [u [f Hs]]].
    - rewrite !(ffun_root (reg e1) _ _ Hr). split; intro H; [intros _; exact H | exact (H Hr)].
    - unfold ffun. rewrite Hs. split; [intros _ Hr | intros _; reflexivity].
      exfalso. rewrite (frule_root R F HF _ Hr) in Hs. discriminate.
  Qed.

  Theorem forest_c2_static_iff : forall J,
    FederationEvents.C2 V FF (fun _ _ => True) E reg sig J <->
    (forall e1 e2 x, In (reg e1) R -> reg e1 = reg e2 -> J e1 e2 ->
       sig e2 (sig e1 x) = sig e1 (sig e2 x)).
  Proof.
    intros J. split.
    - intros H e1 e2 x Hr E12 Hj.
      pose proof (H e1 e2 (fun _ => x) x E12 Hj (Inv_all _) I) as Hc.
      rewrite !(ffun_root (reg e1) _ _ Hr) in Hc. apply Hc. reflexivity.
    - intros H e1 e2 z b E12 Hj _ _ _.
      destruct (reg_cases e1) as [Hr | [u [f Hs]]].
      + rewrite !(ffun_root (reg e1) _ _ Hr). exact (H e1 e2 b Hr E12 Hj).
      + unfold ffun. rewrite Hs. reflexivity.
  Qed.

  (* ----- the exact theorem ----- *)

  Theorem forest_gc_iff : forall J s0,
    FederationEventsConverse.GCF V FF idN E reg sig J o s0 <->
    FederationEventsConverse.TraceConv V FF idN E reg sig J o s0.
  Proof.
    intros J s0. exact (FederationEventsConverse.acyclic_gc_iff V (fsrc F) FF _ idN E reg sig J o HC s0).
  Qed.

  Theorem forest_fed_exact : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv V FF idN E reg sig J o s0 <->
     FederationEventsConverse.C1R1 V FF idN E reg sig o s0 /\
     FederationEventsConverse.C2R V FF idN E reg sig J o s0).
  Proof.
    intros J s0 Hc.
    exact (FederationEventsConverse.fed_exact V (fsrc F) FF _ idN E reg sig J o HC s0 (Inv_all s0) Hc).
  Qed.

  Theorem forest_fed_exact_full : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv V FF idN E reg sig J o s0 <->
     FederationEventsConverse.C1R V FF idN E reg sig o s0 /\
     FederationEventsConverse.C2R V FF idN E reg sig J o s0).
  Proof.
    intros J s0 Hc.
    exact (FederationEventsConverse.fed_exact_full V (fsrc F) FF _ idN E reg sig J o HC s0
             (Inv_all s0) Hc).
  Qed.

  (* Headline: event interleavings converge from s0 iff, for every root r, the J-independent
     events of r commute at every value reachable from s0 r by r's own events. *)
  Theorem forest_events_exact : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv V FF idN E reg sig J o s0 <->
     forall r, In r R -> CoordinatedExact.RootCC r E reg sig J (s0 r)).
  Proof.
    intros J s0 Hc. rewrite (forest_fed_exact J s0 Hc). split.
    - intros [_ H2] r Hr x [q [Hq ->]] e1 e2 R1 R2 Hj.
      assert (E12 : reg e1 = reg e2) by (rewrite R1, R2; reflexivity).
      pose proof (proj1 (forest_c2at_iff _ e1 e2 E12) (H2 q e1 e2 E12 Hj)) as H.
      rewrite R1 in H. specialize (H Hr). rewrite (root_only_run r q s0 Hr Hq) in H. exact H.
    - intros H. split; [apply forest_c1r1 |]. intros p e1 e2 E12 Hj.
      apply (proj2 (forest_c2at_iff _ e1 e2 E12)). intros Hr.
      apply (H (reg e1) Hr); [apply forest_root_reach; exact Hr | reflexivity | |  exact Hj].
      symmetry. exact E12.
  Qed.

  (* With every pair declared independent: permutations converge iff every root's events
     commute at every value reachable by that root's events. *)
  Theorem forest_perm_exact : forall s0, ConsD s0 ->
    ((forall es1 es2, Permutation es1 es2 -> FederationEvents.feq V (rF es1 s0) (rF es2 s0)) <->
     forall r, In r R -> CoordinatedExact.RootCC r E reg sig (fun _ _ => True) (s0 r)).
  Proof.
    intros s0 Hc. rewrite <- (forest_events_exact (fun _ _ => True) s0 Hc). split.
    - intros H es1 es2 Ht. apply H. exact (Trace.tequiv_perm _ _ _ Ht).
    - intros H es1 es2 Hp. apply H.
      apply (Trace.perm_tequiv_total _ (fun _ => True)); [intros; right; exact I | exact Hp |].
      apply Forall_forall. intros. exact I.
  Qed.

  (* The uniform version: convergence from every consistent start iff every root's
     J-independent events commute at every value. *)
  Theorem forest_events_exact_global : forall J,
    (forall s0, ConsD s0 -> FederationEventsConverse.TraceConv V FF idN E reg sig J o s0) <->
    (forall e1 e2 x, In (reg e1) R -> reg e1 = reg e2 -> J e1 e2 ->
       sig e2 (sig e1 x) = sig e1 (sig e2 x)).
  Proof.
    intros J. split.
    - intros H e1 e2 x Hr E12 Hj.
      set (s := RootSet.drive F (fun _ => x)).
      pose proof (proj1 (forest_events_exact J s (drive_Cons _)) (H s (drive_Cons _)) (reg e1) Hr)
        as Hcc.
      assert (Hs : s (reg e1) = x) by exact (RootSet.drive_root R F HF _ (reg e1) Hr).
      rewrite Hs in Hcc. apply (Hcc x); [| reflexivity | symmetry; exact E12 | exact Hj].
      exists []. split; [constructor | reflexivity].
    - intros H s0 Hc. apply (forest_events_exact J s0 Hc).
      intros r Hr x _ e1 e2 R1 R2 Hj. apply H; [rewrite R1; exact Hr | rewrite R1, R2; reflexivity |
                                                exact Hj].
  Qed.

  (* So static C1 and C2 are exact for the uniform question on a forest. *)
  Theorem forest_global_iff_static : forall J,
    (forall s0, ConsD s0 -> FederationEventsConverse.TraceConv V FF idN E reg sig J o s0) <->
    FederationEvents.C1 V FF (fun _ _ => True) E reg sig /\
    FederationEvents.C2 V FF (fun _ _ => True) E reg sig J.
  Proof.
    intros J. rewrite forest_events_exact_global, forest_c2_static_iff. split.
    - intro H. split; [exact forest_c1_static | exact H].
    - intros [_ H]. exact H.
  Qed.

  (* ----- different roots do not interact ----- *)

  (* Two consistent states with the same root values agree on the whole network. *)
  Lemma forest_state_roots : forall t1 t2, ConsD t1 -> ConsD t2 ->
    (forall r, In r R -> t1 r = t2 r) -> forall w, In w o -> t1 w = t2 w.
  Proof.
    intros t1 t2 H1 H2 Hr w Hw.
    exact (RootSet.out_forest_unique R F HF t1 t2 (Cons_msection t1 H1) (Cons_msection t2 H2) Hr
             w (proj1 (Hset w) Hw)).
  Qed.

  (* A run is the forest drive of each root's own run. *)
  Theorem forest_run_formula : forall s0 es w, ConsD s0 -> In w o ->
    rF es s0 w = RootSet.drive F (fun r => rrun (proj r es) (s0 r)) w.
  Proof.
    intros s0 es w Hc Hw. apply forest_state_roots; [| apply drive_Cons | | exact Hw].
    - exact (FederationEvents.runF_cons _ _ _ _ _ _ _ _ _ HC es s0 (Inv_all s0) Hc).
    - intros r Hr. rewrite (RootSet.drive_root R F HF _ r Hr). exact (forest_root_run r es s0 Hr).
  Qed.

  (* Every vertex of the network depends on ONE root's events only: its driving root. *)
  Theorem forest_run_single_root :
    exists (rho : nat -> nat) (p : nat -> V -> V),
      forall w, In w o -> In (rho w) R /\
        forall s0 es, ConsD s0 -> rF es s0 w = p w (rrun (proj (rho w) es) (s0 (rho w))).
  Proof.
    destruct (RootSet.driving_paths R F HF) as [rho [p Hp]]. exists rho, p.
    intros w Hw. destruct (Hp w (proj1 (Hset w) Hw)) as [Hr Hd]. split; [exact Hr |].
    intros s0 es Hc. rewrite (forest_run_formula s0 es w Hc Hw). apply Hd.
  Qed.

  (* Runs that agree on every root's own subsequence reach the same state. *)
  Theorem forest_runs_by_root : forall s0 es1 es2, ConsD s0 ->
    (forall r, In r R -> proj r es1 = proj r es2) -> FederationEvents.feq V (rF es1 s0) (rF es2 s0).
  Proof.
    intros s0 es1 es2 Hc Hp k. destruct (in_dec Nat.eq_dec k o) as [Hk | Hk].
    - rewrite (forest_run_formula s0 es1 k Hc Hk), (forest_run_formula s0 es2 k Hc Hk).
      apply (RootSet.drive_ext R F HF); [| exact (proj1 (Hset k) Hk)].
      intros r Hr. rewrite (Hp r Hr). reflexivity.
    - rewrite (run_off k es1 s0 Hk), (run_off k es2 s0 Hk). reflexivity.
  Qed.

  (* Events of different registries commute from every consistent state. *)
  Theorem forest_cross_commute : forall s e1 e2, ConsD s -> reg e1 <> reg e2 ->
    FederationEvents.feq V (aF e2 (aF e1 s)) (aF e1 (aF e2 s)).
  Proof.
    intros s e1 e2 Hc Hne.
    change (FederationEvents.feq V (rF [e1; e2] s) (rF [e2; e1] s)).
    apply forest_runs_by_root; [exact Hc |]. intros r _. cbn [filter].
    destruct (Nat.eqb (reg e1) r) eqn:H1; destruct (Nat.eqb (reg e2) r) eqn:H2; try reflexivity.
    exfalso. apply Hne. apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. rewrite H1, H2. reflexivity.
  Qed.

  (* An event on a driven registry is overwritten. *)
  Theorem forest_driven_noop : forall s ev, ConsD s -> ~ In (reg ev) R ->
    FederationEvents.feq V (aF ev s) s.
  Proof.
    intros s ev Hc Hr. change (FederationEvents.feq V (rF [ev] s) (rF [] s)).
    apply forest_runs_by_root; [exact Hc |]. intros r Hr'. cbn [filter].
    destruct (Nat.eqb (reg ev) r) eqn:H; [| reflexivity].
    exfalso. apply Nat.eqb_eq in H. rewrite H in Hr. exact (Hr Hr').
  Qed.

  (* ----- kept constraints: the only cross-root coupling ----- *)

  Theorem forest_runs_kept : forall X, RootSet.spans (R ++ verts F) X ->
    forall s0 es, ConsD s0 ->
      msection (rF es s0) F /\
      (msection (rF es s0) (F ++ X) <->
       exists s, msection s (F ++ X) /\ forall r, In r R -> s r = rrun (proj r es) (s0 r)).
  Proof.
    intros X Hsp s0 es Hc.
    assert (Hs : msection (rF es s0) F)
      by exact (Cons_msection _ (FederationEvents.runF_cons _ _ _ _ _ _ _ _ _ HC es s0 (Inv_all s0) Hc)).
    split; [exact Hs |].
    pose proof (RootSet.root_set_criterion R F X (rF es s0) HF Hs Hsp) as Hcrit.
    rewrite msection_app. split.
    - intros [_ HX]. destruct (proj2 Hcrit HX) as [s [Hs' Hr]]. exists s. split; [exact Hs' |].
      intros r Hrr. rewrite (Hr r Hrr). exact (forest_root_run r es s0 Hrr).
    - intros [s [Hs' Hr]]. split; [exact Hs |]. intros x Hx. apply (proj1 Hcrit); [| exact Hx].
      exists s. split; [exact Hs' |].
      intros r Hrr. rewrite (Hr r Hrr). symmetry. exact (forest_root_run r es s0 Hrr).
  Qed.
End Events.

(* ===================================================================== *)
(* The group case of CoordinatedExact.v, recovered as R = [r]. *)

Section Recover.
  Context {G : Type}.
  Variables (op : G -> G -> G) (inv : G -> G).

  Local Notation trg g b := (CoordinatedCycles.tr op inv g b).

  (* The outward forest of a tree: an edge pointing toward the reached set is reversed and
     carries the inverse transport. *)
  Fixpoint tfR (r : nat) (l : list (@edge G)) : list (@edge (G -> G)) :=
    match l with
    | [] => []
    | (u, v, g) :: rest =>
        tfR r rest ++ [if in_dec Nat.eq_dec v (r :: verts (rev rest))
                       then (v, u, trg g true) else (u, v, trg g false)]
    end.

  Definition tforest (r : nat) (T : list (@edge G)) : list (@edge (G -> G)) := tfR r (rev T).

  Lemma tforest_snoc : forall r es u v g,
    tforest r (es ++ [(u, v, g)]) =
    tforest r es ++ [if in_dec Nat.eq_dec v (r :: verts es)
                     then (v, u, trg g true) else (u, v, trg g false)].
  Proof.
    intros. unfold tforest. rewrite rev_app_distr. simpl. rewrite rev_involutive. reflexivity.
  Qed.

  Lemma in_snoc_iff : forall (A B L1 L2 : list nat),
    (forall w, In w A <-> In w B) -> (forall w, In w L1 <-> In w L2) ->
    forall w, In w (A ++ L1) <-> In w (B ++ L2).
  Proof.
    intros A B L1 L2 H1 H2 w. rewrite !in_app_iff, (H1 w), (H2 w). tauto.
  Qed.

  Theorem tforest_props : forall r T, tree r T ->
    RootSet.oforest [r] (tforest r T) /\
    (forall w, In w ([r] ++ verts (tforest r T)) <-> In w (r :: verts T)) /\
    (forall w, frule (tforest r T) w =
       match CoordinatedCycles.rule r T w with
       | Some (p, g, b) => Some (p, trg g b)
       | None => None
       end).
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu].
    - split; [apply RootSet.f_nil | split; [intro w; simpl; tauto | intro w; reflexivity]].
    - destruct IH as [IHf [IHs IHr]]. rewrite tforest_snoc.
      destruct (in_dec Nat.eq_dec v (r :: verts es)) as [C | _]; [contradiction |].
      split; [| split].
      + apply RootSet.f_out; [exact IHf | apply IHs; exact Hu | rewrite IHs; exact Hv].
      + intro w. rewrite !verts_app. change ([r] ++ verts (tforest r es) ++ verts [(u, v, trg g false)])
          with (([r] ++ verts (tforest r es)) ++ [u; v]).
        change (r :: verts es ++ verts [(u, v, g)]) with ((r :: verts es) ++ [u; v]).
        apply in_snoc_iff; [exact IHs | tauto].
      + intro w. rewrite frule_snoc, (CoordinatedCycles.rule_out r es u v g w Hv).
        destruct (Nat.eq_dec w v); [reflexivity | apply IHr].
    - destruct IH as [IHf [IHs IHr]]. rewrite tforest_snoc.
      destruct (in_dec Nat.eq_dec v (r :: verts es)) as [_ | C]; [| contradiction].
      split; [| split].
      + apply RootSet.f_out; [exact IHf | apply IHs; exact Hv | rewrite IHs; exact Hu].
      + intro w. rewrite !verts_app. change ([r] ++ verts (tforest r es) ++ verts [(v, u, trg g true)])
          with (([r] ++ verts (tforest r es)) ++ [v; u]).
        change (r :: verts es ++ verts [(u, v, g)]) with ((r :: verts es) ++ [u; v]).
        apply in_snoc_iff; [exact IHs | intro x; simpl; tauto].
      + intro w. rewrite frule_snoc, (CoordinatedCycles.rule_in r es u v g w Hv).
        destruct (Nat.eq_dec w u); [reflexivity | apply IHr].
  Qed.

  Lemma dfun_ffun : forall r T, tree r T -> forall w s x,
    CoordinatedCycles.dfun op inv r T w s x = ffun (tforest r T) w s x.
  Proof.
    intros r T HT w s x. unfold CoordinatedCycles.dfun, ffun.
    rewrite (proj2 (proj2 (tforest_props r T HT)) w).
    destruct (CoordinatedCycles.rule r T w) as [[[p g] b] |]; reflexivity.
  Qed.

  Lemma dsrc_fsrc : forall r T, tree r T -> forall w,
    CoordinatedCycles.dsrc r T w = fsrc (tforest r T) w.
  Proof.
    intros r T HT w. unfold CoordinatedCycles.dsrc, fsrc.
    rewrite (proj2 (proj2 (tforest_props r T HT)) w).
    destruct (CoordinatedCycles.rule r T w) as [[[p g] b] |]; reflexivity.
  Qed.

  Section Inst.
    Variables (r : nat) (T : list (@edge G)) (o : list nat).
    Hypothesis HT : tree r T.
    Hypothesis Ho : FederationOrder.topo (CoordinatedCycles.dsrc r T) o.
    Hypothesis Hset : forall w, In w o <-> In w (r :: verts T).
    Variables (E : Type) (reg : E -> nat) (sig : E -> G -> G).
    Hypothesis Hreg : forall ev, In (reg ev) o.

    Local Notation D := (CoordinatedCycles.dfun op inv r T).
    Local Notation FT := (ffun (tforest r T)).
    Local Notation idN := (fun (_ : nat) (x : G) => x).

    Lemma rec_forest : RootSet.oforest [r] (tforest r T).
    Proof. exact (proj1 (tforest_props r T HT)). Qed.

    Lemma rec_order : FederationEvents.topoF (fsrc (tforest r T)) o.
    Proof.
      apply (topoF_ext (CoordinatedCycles.dsrc r T)); [intros w _; apply dsrc_fsrc; exact HT |].
      apply CoordinatedCycles.topo_topoF. exact Ho.
    Qed.

    Lemma rec_set : forall w, In w o <-> In w ([r] ++ verts (tforest r T)).
    Proof. intro w. rewrite (Hset w). symmetry. exact (proj1 (proj2 (tforest_props r T HT)) w). Qed.

    Lemma rec_cons : forall s, FederationEvents.Cons G D o s <-> FederationEvents.Cons G FT o s.
    Proof.
      intro s. split; intros H j Hj; [rewrite <- (dfun_ffun r T HT) | rewrite (dfun_ffun r T HT)];
        exact (H j Hj).
    Qed.

    Lemma rec_tc : forall J s,
      FederationEventsConverse.TraceConv G D idN E reg sig J o s <->
      FederationEventsConverse.TraceConv G FT idN E reg sig J o s.
    Proof.
      intros J s. unfold FederationEventsConverse.TraceConv.
      split; intros H es1 es2 Ht k; pose proof (H es1 es2 Ht k) as Hk;
        rewrite !(runF_fext D FT (dfun_ffun r T HT)) in *; exact Hk.
    Qed.

    (* CoordinatedExact.coordinated_events_exact, re-derived from forest_events_exact. *)
    Theorem coordinated_events_exact_recovered : forall J s0, FederationEvents.Cons G D o s0 ->
      (FederationEventsConverse.TraceConv G D idN E reg sig J o s0 <->
       CoordinatedExact.RootCC r E reg sig J (s0 r)).
    Proof.
      intros J s0 Hc. rewrite rec_tc.
      rewrite (forest_events_exact [r] (tforest r T) o rec_forest rec_order rec_set E reg sig Hreg J s0
                 (proj1 (rec_cons s0) Hc)).
      split; [intro H; exact (H r (or_introl eq_refl)) | intros H q [<- | []]; exact H].
    Qed.

    Theorem coordinated_events_exact_global_recovered : forall J,
      (forall s0, FederationEvents.Cons G D o s0 ->
         FederationEventsConverse.TraceConv G D idN E reg sig J o s0) <->
      (forall e1 e2 x, reg e1 = r -> reg e2 = r -> J e1 e2 -> sig e2 (sig e1 x) = sig e1 (sig e2 x)).
    Proof.
      intros J.
      transitivity (forall s0, FederationEvents.Cons G FT o s0 ->
                      FederationEventsConverse.TraceConv G FT idN E reg sig J o s0).
      { split; intros H s0 Hc; apply rec_tc; apply H; apply rec_cons; exact Hc. }
      rewrite (forest_events_exact_global [r] (tforest r T) o rec_forest rec_order rec_set E reg sig
                 Hreg J).
      split.
      - intros H e1 e2 x R1 R2 Hj. apply H; [rewrite R1; left; reflexivity | rewrite R1, R2; reflexivity |
                                              exact Hj].
      - intros H e1 e2 x [R1 | []] E12 Hj. apply H; [symmetry; exact R1 | rewrite <- E12; symmetry;
                                                       exact R1 | exact Hj].
    Qed.
  End Inst.
End Recover.

(* The recovered theorem on CoordinatedExact's Klein tree (non-vacuity of its hypotheses). *)
Theorem recovered_klein : forall J,
  FederationEventsConverse.TraceConv (bool * bool)
    (CoordinatedCycles.dfun CoordinatedExact.kop CoordinatedExact.kinv 0 CoordinatedExact.kT)
    (fun _ x => x) CoordinatedExact.kev CoordinatedExact.kreg CoordinatedExact.ksig J [0; 1]
    CoordinatedExact.kz <->
  CoordinatedExact.RootCC 0 CoordinatedExact.kev CoordinatedExact.kreg CoordinatedExact.ksig J
    (CoordinatedExact.kz 0).
Proof.
  intro J.
  apply (coordinated_events_exact_recovered CoordinatedExact.kop CoordinatedExact.kinv 0
           CoordinatedExact.kT [0; 1] CoordinatedExact.kT_tree CoordinatedExact.kT_order
           CoordinatedExact.kT_verts CoordinatedExact.kev CoordinatedExact.kreg CoordinatedExact.ksig
           CoordinatedExact.kreg_in J CoordinatedExact.kz).
  intros j [<- | [<- | []]]; reflexivity.
Qed.

(* ===================================================================== *)
(* A two-root lossy network over nat. *)

Definition par (x : nat) : nat := if Nat.even x then 0 else 1.
Definition cap1 (x : nat) : nat := Nat.min x 1.

Definition tw_R : list nat := [0; 1].
Definition tw_F : list (@edge (nat -> nat)) := [(0, 2, par); (1, 3, cap1)].
Definition tw_X : list (@edge (nat -> nat)) := [(1, 2, par)].
Definition tw_o : list nat := [0; 1; 2; 3].

Lemma tw_forest : RootSet.oforest tw_R tw_F.
Proof.
  change tw_F with (([] ++ [(0, 2, par)]) ++ [(1, 3, cap1)]).
  apply RootSet.f_out; [apply RootSet.f_out; [apply RootSet.f_nil | |] | |]; simpl; intuition congruence.
Qed.

Lemma tw_order : FederationEvents.topoF (fsrc tw_F) tw_o.
Proof.
  change tw_o with (tw_R ++ targets tw_F). apply forest_order; [| exact tw_forest].
  repeat constructor; simpl; intuition congruence.
Qed.

Lemma tw_set : forall w, In w tw_o <-> In w (tw_R ++ verts tw_F).
Proof. intro w. change tw_o with (tw_R ++ targets tw_F). apply forest_order_set. exact tw_forest. Qed.

Inductive twev : Type := TDbl | TClamp | TInc | TPoke.

Definition tw_reg (ev : twev) : nat :=
  match ev with TDbl | TClamp => 0 | TInc => 1 | TPoke => 2 end.

Definition tw_sig (ev : twev) (x : nat) : nat :=
  match ev with TDbl => x + x | TClamp => Nat.min x 5 | TInc => S x | TPoke => 7 end.

Lemma tw_reg_in : forall ev, In (tw_reg ev) tw_o.
Proof. intros []; simpl; auto. Qed.

Local Notation twD := (ffun tw_F).
Local Notation twRun := (FederationEvents.runF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o).
Local Notation twCons := (FederationEvents.Cons nat twD tw_o).

(* The consistent state with root values a0 and a1. *)
Definition tw_s (a0 a1 : nat) (k : nat) : nat :=
  match k with 0 => a0 | 1 => a1 | 2 => par a0 | 3 => cap1 a1 | _ => 0 end.

Lemma tw_s_cons : forall a0 a1, twCons (tw_s a0 a1).
Proof. intros a0 a1 j [<- | [<- | [<- | [<- | []]]]]; reflexivity. Qed.

Theorem tw_root_set :
  RootSet.spanning_forest tw_R (tw_F ++ tw_X) tw_F /\
  RootSet.root_set tw_R (tw_F ++ tw_X) /\
  ~ RootSet.root_set [0] (tw_F ++ tw_X) /\ ~ RootSet.root_set [1] (tw_F ++ tw_X) /\
  RootSet.reach (tw_F ++ tw_X) [0] 2 /\ RootSet.reach (tw_F ++ tw_X) [1] 2.
Proof.
  assert (Hsf : RootSet.spanning_forest tw_R (tw_F ++ tw_X) tw_F).
  { split; [exact tw_forest | split].
    - intros x Hx. apply in_or_app. left. exact Hx.
    - intros w Hw. simpl in Hw |- *. intuition. }
  split; [exact Hsf | split; [apply RootSet.root_set_iff_forest; exists tw_F; exact Hsf |]].
  split; [| split; [| split]].
  - intro H. assert (Hr : RootSet.reach (tw_F ++ tw_X) [0] 1) by (apply H; simpl; tauto).
    inversion Hr as [r Hin | u v f _ Hin]; subst.
    + simpl in Hin. intuition congruence.
    + simpl in Hin. destruct Hin as [Hin | [Hin | [Hin | []]]]; inversion Hin.
  - intro H. assert (Hr : RootSet.reach (tw_F ++ tw_X) [1] 0) by (apply H; simpl; tauto).
    inversion Hr as [r Hin | u v f _ Hin]; subst.
    + simpl in Hin. intuition congruence.
    + simpl in Hin. destruct Hin as [Hin | [Hin | [Hin | []]]]; inversion Hin.
  - apply (RootSet.reach_step _ _ 0 2 par); [apply RootSet.reach_root; left; reflexivity |].
    left. reflexivity.
  - apply (RootSet.reach_step _ _ 1 2 par); [apply RootSet.reach_root; left; reflexivity |].
    right. right. left. reflexivity.
Qed.

Lemma tw_root0_fixed : forall q, Forall (fun ev => tw_reg ev = 0) q ->
  CoordinatedExact.rrun twev tw_sig q 0 = 0.
Proof.
  induction q as [| a q IH]; intros H; [reflexivity |].
  inversion H as [| ? ? Ha Hq]; subst. destruct a; simpl in Ha; try discriminate;
    unfold CoordinatedExact.rrun in *; simpl; apply IH; exact Hq.
Qed.

(* From every consistent start with root 0 at value 0, every permutation converges. *)
Theorem tw_converges_at_zero : forall s0, twCons s0 -> s0 0 = 0 ->
  forall es1 es2, Permutation es1 es2 -> FederationEvents.feq nat (twRun es1 s0) (twRun es2 s0).
Proof.
  intros s0 Hc H0.
  apply (proj2 (forest_perm_exact tw_R tw_F tw_o tw_forest tw_order tw_set twev tw_reg tw_sig
                  tw_reg_in s0 Hc)).
  intros r [<- | [<- | []]] x [q [Hq ->]] e1 e2 R1 R2 _.
  - rewrite H0, (tw_root0_fixed q Hq).
    destruct e1, e2; simpl in R1, R2; try discriminate; reflexivity.
  - destruct e1, e2; simpl in R1, R2; try discriminate; reflexivity.
Qed.

(* From a consistent start with root 0 at value 3, Dbl and Clamp do not commute; the
   divergence reaches the driven vertex 2. *)
Theorem tw_diverges_at_three :
  twCons (tw_s 3 0) /\
  twRun [TDbl; TClamp] (tw_s 3 0) 0 = 5 /\ twRun [TClamp; TDbl] (tw_s 3 0) 0 = 6 /\
  twRun [TDbl; TClamp] (tw_s 3 0) 2 = 1 /\ twRun [TClamp; TDbl] (tw_s 3 0) 2 = 0 /\
  ~ CoordinatedExact.RootCC 0 twev tw_reg tw_sig (fun _ _ => True) (tw_s 3 0 0).
Proof.
  split; [apply tw_s_cons |]. split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  intro H. assert (Hx : CoordinatedExact.RootReach 0 twev tw_reg tw_sig 3 3)
    by (exists []; split; [constructor | reflexivity]).
  pose proof (H 3 Hx TDbl TClamp eq_refl eq_refl I) as Hd. discriminate Hd.
Qed.

(* Commuting at the start value is not enough: at 1 Dbl and Clamp commute, but 4 is reachable. *)
Theorem tw_reachable_matters :
  tw_sig TClamp (tw_sig TDbl 1) = tw_sig TDbl (tw_sig TClamp 1) /\
  twRun [TDbl; TDbl; TDbl; TClamp] (tw_s 1 0) 0 = 5 /\
  twRun [TDbl; TDbl; TClamp; TDbl] (tw_s 1 0) 0 = 8 /\
  ~ CoordinatedExact.RootCC 0 twev tw_reg tw_sig (fun _ _ => True) (tw_s 1 0 0).
Proof.
  split; [reflexivity |]. split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  intro H. assert (Hx : CoordinatedExact.RootReach 0 twev tw_reg tw_sig 1 4)
    by (exists [TDbl; TDbl]; split; [repeat constructor | reflexivity]).
  pose proof (H 4 Hx TDbl TClamp eq_refl eq_refl I) as Hd. discriminate Hd.
Qed.

(* So convergence holds from some consistent starts and fails from others. *)
Theorem tw_not_global :
  (forall a1 es1 es2, Permutation es1 es2 ->
     FederationEvents.feq nat (twRun es1 (tw_s 0 a1)) (twRun es2 (tw_s 0 a1))) /\
  ~ (forall s0, twCons s0 ->
       FederationEventsConverse.TraceConv nat twD (fun _ x => x) twev tw_reg tw_sig
         (fun _ _ => True) tw_o s0).
Proof.
  split.
  - intros a1. apply tw_converges_at_zero; [apply tw_s_cons | reflexivity].
  - intro H. pose proof (H (tw_s 3 0) (tw_s_cons 3 0) [TDbl; TClamp] [TClamp; TDbl]
                           (Trace.teq_swap _ [] TDbl TClamp [] (or_intror I)) 0) as Hd.
    revert Hd. vm_compute. discriminate.
Qed.

(* Events of the two roots commute from every consistent start, events on the driven vertex are
   overwritten, and vertex 2 (reached from both roots) depends on root 0's events only. *)
Theorem tw_cross_roots : forall s, twCons s -> forall e1 e2, tw_reg e1 <> tw_reg e2 ->
  FederationEvents.feq nat
    (FederationEvents.applyF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o e2
       (FederationEvents.applyF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o e1 s))
    (FederationEvents.applyF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o e1
       (FederationEvents.applyF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o e2 s)).
Proof.
  intros s Hc e1 e2 Hne.
  exact (forest_cross_commute tw_R tw_F tw_o tw_forest tw_order tw_set twev tw_reg tw_sig tw_reg_in
           s e1 e2 Hc Hne).
Qed.

Theorem tw_poke_noop : forall s, twCons s ->
  FederationEvents.feq nat (FederationEvents.applyF nat twD (fun _ x => x) twev tw_reg tw_sig tw_o TPoke s) s.
Proof.
  intros s Hc. apply (forest_driven_noop tw_R tw_F tw_o tw_forest tw_order tw_set twev tw_reg tw_sig
                        tw_reg_in s TPoke Hc).
  simpl. intuition congruence.
Qed.

Theorem tw_vertex2 : forall s0 es, twCons s0 ->
  twRun es s0 2 = par (CoordinatedExact.rrun twev tw_sig
                         (filter (fun ev => Nat.eqb (tw_reg ev) 0) es) (s0 0)).
Proof.
  intros s0 es Hc.
  rewrite (forest_run_formula tw_R tw_F tw_o tw_forest tw_order tw_set twev tw_reg tw_sig tw_reg_in
             s0 es 2 Hc (or_intror (or_intror (or_introl eq_refl)))).
  reflexivity.
Qed.

(* The cross-root constraint (1, 2, par) is a check on the joint root values. *)
Theorem tw_constraint :
  msection (twRun [] (tw_s 0 0)) (tw_F ++ tw_X) /\
  ~ msection (twRun [TInc] (tw_s 0 0)) (tw_F ++ tw_X) /\
  msection (twRun [TInc; TInc] (tw_s 0 0)) (tw_F ++ tw_X) /\
  msection (twRun [TInc; TPoke; TDbl; TInc] (tw_s 0 0)) (tw_F ++ tw_X).
Proof.
  split; [| split; [| split]].
  - intros x Hx. simpl in Hx. destruct Hx as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
  - intro H. pose proof (H (1, 2, par) (or_intror (or_intror (or_introl eq_refl)))) as Hd.
    revert Hd. vm_compute. discriminate.
  - intros x Hx. simpl in Hx. destruct Hx as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
  - intros x Hx. simpl in Hx. destruct Hx as [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
Qed.
