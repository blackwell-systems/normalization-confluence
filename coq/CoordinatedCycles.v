(* CoordinatedCycles.v: non-monotone cycles converge under a computed coordination, mechanized
   axiom-free. This is the soundness theorem for the holonomy-minimal plan of gsm's
   HOLONOMY-COORDINATION-DESIGN.md (Roadmap item 4).

   Model. The network is a group-labeled graph exactly as in CohomologyGraph.v: registries are
   nats, the shared fiber of every registry is the group G itself (the invertible fragment with
   the regular action; Z/2 = (bool, xor) covers gsm's copy and 1 - x loops), and an edge
   (u, v, g) is a morphism that transports the value at u to g * s(u) at v. A plan splits the
   edges of a connected component into three lists, relative to a designated authority root r:

     T  a spanning tree grown from r (CohomologyGraph.tree r T). Its edges DRIVE values.
     B  balanced non-tree edges. They are DEMOTED to checked constraints: they never write, and a
        state is accepted only if it satisfies them.
     C  coordinated non-tree edges. They are REMOVED from the federation: neither a writer nor a
        constraint inside it. Whatever the external coordinator does with them (serialize them
        through a single authority, or reject the writes they would make) happens outside the
        propagation graph, and the federation's normal form is not required to satisfy them.

   The driving network (dsrc, dfun) is computed from T: the root keeps its own value (it is the
   authority), and each other tree vertex w reads only its tree parent p and takes the transported
   value, g * s(p) when the tree edge points away from the root and g^-1 * s(p) when it points
   toward it (the second case is where invertibility is used to drive against a morphism's
   direction). Every other registry is untouched. This network is acyclic, so it is an acyclic
   federation in the sense of FederationOrder.v (topo, run) and FederationEvents.v (Common, topoF,
   frun, runF), and those results apply to it unchanged.

   Results.
   - drive_order_exists: the driving network has a topological order over exactly the tree's
     vertices (so a normal form exists).
   - drive_consistent: running any such order gives a state in which every tree registry equals
     its driven value, the root keeps the authority value, and off-tree registries are untouched
     (via FederationEvents.frun_solves, with the network shown to satisfy Common).
   - balanced_any_section: being balanced does not depend on which tree section is used (the
     right constant of tree_unique cancels), so "balanced" is a static property of the edge.
   - coordinated_sound (the soundness theorem): under a plan with T a spanning tree and every edge
     of B balanced, for every initial state and every topological order, the normal form
     satisfies every tree edge and every balanced constraint, keeps the authority value at the
     root, is the UNIQUE state satisfying T ++ B with that root value (tree_unique: the root fixes
     the constant), and every other topological order reaches the same state pointwise
     (FederationOrder.order_independent).
   - coordinated_unique_nf: the same as an existence-and-uniqueness statement.
   - coordination_needed (via unbalanced_blocks): keeping any unbalanced edge of C, as a writer
     or as a constraint, leaves no consistent state at all, so the normal form is lost.
   - plan_exact (via cycle_basis_criterion): with B balanced and C unbalanced, a set K of
     non-tree edges can be kept with a consistent state iff K avoids C. The coordinated set is
     exactly the unbalanced edges: no fewer, no more.
   - coordinated_events_converge: composed with FederationEvents.fed_permutations_converge, any
     two permutations of local events (on any tree registries) converge under the plan,
     provided the authority root's own events commute, and the result satisfies T ++ B. Events
     on non-root registries are overwritten by the drive, which is the design note's warning
     that a demoted edge no longer propagates a local write backward.

   Instances (every hypothesis discharged, over Z/2).
   - Copy-back loop (A -> B copy, B -> A copy): rooted at A, the back edge is balanced and kept
     as a constraint, zero edges coordinated: copyback_zero_coordination.
   - Negation loop (A -> B copy, B -> A 1 - x): rooted at A, the back edge is unbalanced, one edge
     coordinated, and keeping it destroys every consistent state: negation_one_coordinated.

   Corners where the naive statement is false (recorded as theorems).
   - copyback_without_authority: with no authority root (both edges kept as writers) the
     balanced copy-back loop has two consistent states and two propagation orders reach
     different ones. Trivial holonomy gives existence, not uniqueness.
   - root_choice_matters: the normal form is unique GIVEN the root, but depends on which
     registry is the root: rooted at A versus at B, the same initial state reaches (0, 0)
     versus (1, 1). The plan must report its root.
   - noninvertible_balance_not_static: with a non-invertible transport (B -> A constant 0),
     whether the back edge holds at the normal form depends on the authority value, so it is
     neither balanced nor unbalanced as a property of the cycle. Invertibility is needed.
   - nonfree_holonomy_counterexample: with bijections acting on a fiber that is not the group
     itself (a swap of {0, 1} acting on {0, 1, 2}), a non-identity holonomy still admits a
     consistent state (value 2), so unbalanced_blocks' "no consistent state at all" fails
     outside the regular action; the edge is still violated for some authority value (0), so it
     must still be coordinated for the plan to be sound for every root value.

   States are compared pointwise, so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.CohomologyGraph NC.FederationOrder NC.FederationEvents.
Import ListNotations.

(* ----- bridges between the two acyclic-federation files ----- *)

(* FederationOrder's topological orders are FederationEvents' topological orders. *)
Lemma topo_topoF :
  forall (src : nat -> list nat) o, FederationOrder.topo src o -> FederationEvents.topoF src o.
Proof.
  intros src o. induction o as [| a o IH]; intros [Hnd Hs]; simpl; [exact I |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd]. split; [exact Ha | split].
  - intros k Hk Hin. pose proof (Hs a k (or_introl eq_refl) Hk Hin) as Hp. simpl in Hp.
    destruct Hp as [[_ Hin'] | Hp]; apply Ha; [exact Hin' | exact (FederationOrder.prec_in_r _ _ _ Hp)].
  - apply IH. split; [exact Hnd |]. intros i k Hi Hk Hko.
    apply (FederationOrder.prec_tail a); [intro E; subst k; contradiction |].
    apply Hs; [right; exact Hi | exact Hk | right; exact Hko].
Qed.

(* FederationEvents' repair run is FederationOrder's run, pointwise. *)
Lemma frun_run :
  forall (V : Type) (src : nat -> list nat) (f : nat -> (nat -> V) -> V -> V),
    (forall i s1 s2 x, (forall k, In k (src i) -> s1 k = s2 k) -> f i s1 x = f i s2 x) ->
    forall l t k, FederationEvents.frun V f l t k = FederationOrder.run f l t k.
Proof.
  intros V src f Hloc l. induction l as [| a l IH]; intros t k; [reflexivity |].
  change (FederationEvents.frun V f (a :: l) t)
    with (FederationEvents.frun V f l (FederationEvents.fstep V f t a)).
  rewrite FederationOrder.run_cons, IH.
  apply (FederationOrder.run_ext src f Hloc). intro j.
  unfold FederationEvents.fstep, FederationEvents.upd, FederationOrder.step, FederationOrder.upd.
  destruct (Nat.eqb j a) eqn:E1; destruct (Nat.eq_dec j a) as [E2 | E2]; try reflexivity.
  - apply Nat.eqb_eq in E1. contradiction.
  - subst j. rewrite Nat.eqb_refl in E1. discriminate.
Qed.

Section Coordinated.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  (* ----- the driving network computed from the spanning tree ----- *)

  (* The driving rule of registry w: Some (parent, label, reversed) if w is attached to the tree
     by an edge (the fresh endpoint of that edge), None otherwise (the root, or off the tree).
     The list is scanned from its last edge, so freshness is checked against the prefix. *)
  Fixpoint ruleR (r : nat) (l : list (@edge G)) (w : nat) : option (nat * G * bool) :=
    match l with
    | [] => None
    | (u, v, g) :: rest =>
        if in_dec Nat.eq_dec v (r :: verts (rev rest))
        then (if Nat.eq_dec w u then Some (v, g, true) else ruleR r rest w)
        else (if Nat.eq_dec w v then Some (u, g, false) else ruleR r rest w)
    end.

  Definition rule (r : nat) (T : list (@edge G)) (w : nat) : option (nat * G * bool) :=
    ruleR r (rev T) w.

  (* Transport along a tree edge, against its direction when reversed. *)
  Definition tr (g : G) (b : bool) (x : G) : G := if b then op (inv g) x else op g x.

  (* The sources and the step of each registry in the driving network. *)
  Definition dsrc (r : nat) (T : list (@edge G)) (w : nat) : list nat :=
    match rule r T w with Some (p, _, _) => [p] | None => [] end.

  Definition dfun (r : nat) (T : list (@edge G)) (w : nat) (s : nat -> G) (x : G) : G :=
    match rule r T w with Some (p, g, b) => tr g b (s p) | None => x end.

  (* The normal form of the coordinated federation along a propagation order o. *)
  Definition drive (r : nat) (T : list (@edge G)) (o : list nat) (s0 : nat -> G) : nat -> G :=
    FederationOrder.run (dfun r T) o s0.

  (* The non-tree edges lie among the tree's vertices (the tree spans them). *)
  Definition spans (r : nat) (T X : list (@edge G)) : Prop :=
    forall u v g, In (u, v, g) X -> In u (r :: verts T) /\ In v (r :: verts T).

  Lemma rule_nil : forall r w, rule r [] w = None.
  Proof. reflexivity. Qed.

  Lemma rule_snoc :
    forall r es u v g w,
      rule r (es ++ [(u, v, g)]) w =
      if in_dec Nat.eq_dec v (r :: verts es)
      then (if Nat.eq_dec w u then Some (v, g, true) else rule r es w)
      else (if Nat.eq_dec w v then Some (u, g, false) else rule r es w).
  Proof. intros. unfold rule. rewrite rev_app_distr. simpl. rewrite rev_involutive. reflexivity. Qed.

  Lemma rule_out :
    forall r es u v g w, ~ In v (r :: verts es) ->
      rule r (es ++ [(u, v, g)]) w = if Nat.eq_dec w v then Some (u, g, false) else rule r es w.
  Proof.
    intros r es u v g w H. rewrite rule_snoc.
    destruct (in_dec Nat.eq_dec v (r :: verts es)); [contradiction | reflexivity].
  Qed.

  Lemma rule_in :
    forall r es u v g w, In v (r :: verts es) ->
      rule r (es ++ [(u, v, g)]) w = if Nat.eq_dec w u then Some (v, g, true) else rule r es w.
  Proof.
    intros r es u v g w H. rewrite rule_snoc.
    destruct (in_dec Nat.eq_dec v (r :: verts es)); [reflexivity | contradiction].
  Qed.

  Lemma verts_lift : forall (es l : list (@edge G)) w, In w (verts es) -> In w (verts (es ++ l)).
  Proof. intros es l w H. rewrite verts_app. apply in_or_app. left. exact H. Qed.

  (* A driven registry is a non-root tree vertex, and its parent is a tree vertex. *)
  Lemma rule_some :
    forall r T, tree r T -> forall w p g b, rule r T w = Some (p, g, b) ->
      In p (r :: verts T) /\ In w (verts T) /\ w <> r.
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu];
      intros w p h b H.
    - rewrite rule_nil in H. discriminate.
    - rewrite (rule_out r es u v g w Hv) in H. revert H.
      destruct (Nat.eq_dec w v) as [-> | Hne]; intro H.
      + injection H as Ep Eg Eb. subst p. split; [| split].
        * apply verts_snoc_intro. left. exact Hu.
        * rewrite verts_app. apply in_or_app. right. right. left. reflexivity.
        * intro E. apply Hv. left. symmetry. exact E.
      + destruct (IH w p h b H) as [Hp [Hw Hr]]. split; [| split].
        * apply verts_snoc_intro. left. exact Hp.
        * apply verts_lift. exact Hw.
        * exact Hr.
    - rewrite (rule_in r es u v g w Hv) in H. revert H.
      destruct (Nat.eq_dec w u) as [-> | Hne]; intro H.
      + injection H as Ep Eg Eb. subst p. split; [| split].
        * apply verts_snoc_intro. left. exact Hv.
        * rewrite verts_app. apply in_or_app. right. left. reflexivity.
        * intro E. apply Hu. left. symmetry. exact E.
      + destruct (IH w p h b H) as [Hp [Hw Hr]]. split; [| split].
        * apply verts_snoc_intro. left. exact Hp.
        * apply verts_lift. exact Hw.
        * exact Hr.
  Qed.

  (* The authority root is never driven. *)
  Lemma root_none : forall r T, tree r T -> rule r T r = None.
  Proof.
    intros r T HT. destruct (rule r T r) as [[[p g] b] |] eqn:H; [| reflexivity].
    exfalso. destruct (rule_some r T HT r p g b H) as [_ [_ Hr]]. apply Hr. reflexivity.
  Qed.

  (* Every non-root tree vertex is driven. *)
  Lemma driven :
    forall r T, tree r T -> forall w, In w (r :: verts T) -> w <> r ->
      exists p g b, rule r T w = Some (p, g, b).
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu];
      intros w Hw Hr.
    - simpl in Hw. destruct Hw as [E | []]. exfalso. apply Hr. symmetry. exact E.
    - rewrite (rule_out r es u v g w Hv).
      destruct (Nat.eq_dec w v) as [-> | Hne]; [do 3 eexists; reflexivity |].
      apply IH; [| exact Hr].
      destruct (verts_snoc r es u v g w Hw) as [Hold | [-> | ->]];
        [exact Hold | exact Hu | exfalso; apply Hne; reflexivity].
    - rewrite (rule_in r es u v g w Hv).
      destruct (Nat.eq_dec w u) as [-> | Hne]; [do 3 eexists; reflexivity |].
      apply IH; [| exact Hr].
      destruct (verts_snoc r es u v g w Hw) as [Hold | [-> | ->]];
        [exact Hold | exfalso; apply Hne; reflexivity | exact Hv].
  Qed.

  Lemma dfun_local :
    forall r T i s1 s2 x, (forall k, In k (dsrc r T i) -> s1 k = s2 k) ->
      dfun r T i s1 x = dfun r T i s2 x.
  Proof.
    intros r T i s1 s2 x H. unfold dfun, dsrc in *.
    destruct (rule r T i) as [[[p g] b] |]; [rewrite (H p (or_introl eq_refl)) |]; reflexivity.
  Qed.

  Lemma dfun_out_new :
    forall r es u v g t x, ~ In v (r :: verts es) -> dfun r (es ++ [(u, v, g)]) v t x = op g (t u).
  Proof.
    intros r es u v g t x H. unfold dfun. rewrite (rule_out r es u v g v H).
    destruct (Nat.eq_dec v v) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  Qed.

  Lemma dfun_out_old :
    forall r es u v g w t x, ~ In v (r :: verts es) -> w <> v ->
      dfun r (es ++ [(u, v, g)]) w t x = dfun r es w t x.
  Proof.
    intros r es u v g w t x H Hw. unfold dfun. rewrite (rule_out r es u v g w H).
    destruct (Nat.eq_dec w v); [contradiction | reflexivity].
  Qed.

  Lemma dsrc_out_new :
    forall r es u v g, ~ In v (r :: verts es) -> dsrc r (es ++ [(u, v, g)]) v = [u].
  Proof.
    intros r es u v g H. unfold dsrc. rewrite (rule_out r es u v g v H).
    destruct (Nat.eq_dec v v) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  Qed.

  Lemma dsrc_out_old :
    forall r es u v g w, ~ In v (r :: verts es) -> w <> v ->
      dsrc r (es ++ [(u, v, g)]) w = dsrc r es w.
  Proof.
    intros r es u v g w H Hw. unfold dsrc. rewrite (rule_out r es u v g w H).
    destruct (Nat.eq_dec w v); [contradiction | reflexivity].
  Qed.

  Lemma dfun_in_new :
    forall r es u v g t x, In v (r :: verts es) ->
      dfun r (es ++ [(u, v, g)]) u t x = op (inv g) (t v).
  Proof.
    intros r es u v g t x H. unfold dfun. rewrite (rule_in r es u v g u H).
    destruct (Nat.eq_dec u u) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  Qed.

  Lemma dfun_in_old :
    forall r es u v g w t x, In v (r :: verts es) -> w <> u ->
      dfun r (es ++ [(u, v, g)]) w t x = dfun r es w t x.
  Proof.
    intros r es u v g w t x H Hw. unfold dfun. rewrite (rule_in r es u v g w H).
    destruct (Nat.eq_dec w u); [contradiction | reflexivity].
  Qed.

  Lemma dsrc_in_new :
    forall r es u v g, In v (r :: verts es) -> dsrc r (es ++ [(u, v, g)]) u = [v].
  Proof.
    intros r es u v g H. unfold dsrc. rewrite (rule_in r es u v g u H).
    destruct (Nat.eq_dec u u) as [_ | n]; [reflexivity | exfalso; apply n; reflexivity].
  Qed.

  Lemma dsrc_in_old :
    forall r es u v g w, In v (r :: verts es) -> w <> u ->
      dsrc r (es ++ [(u, v, g)]) w = dsrc r es w.
  Proof.
    intros r es u v g w H Hw. unfold dsrc. rewrite (rule_in r es u v g w H).
    destruct (Nat.eq_dec w u); [contradiction | reflexivity].
  Qed.

  (* A state in which every tree registry equals its driven value is a section of the tree. *)
  Lemma cons_section :
    forall r T, tree r T ->
    forall t, (forall w, In w (r :: verts T) -> t w = dfun r T w t (t w)) -> is_section op t T.
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu]; intros t H.
    - intros x [].
    - apply section_app. split.
      + apply IH. intros w Hw.
        assert (Hwv : w <> v) by (intro E; subst; contradiction).
        rewrite <- (dfun_out_old r es u v g w t (t w) Hv Hwv).
        apply H. apply verts_snoc_intro. left. exact Hw.
      + intros x [<- | []]. unfold sat.
        pose proof (H v (verts_snoc_intro r es u v g v (or_intror (or_intror eq_refl)))) as E.
        rewrite (dfun_out_new r es u v g t (t v) Hv) in E. symmetry. exact E.
    - apply section_app. split.
      + apply IH. intros w Hw.
        assert (Hwu : w <> u) by (intro E; subst; contradiction).
        rewrite <- (dfun_in_old r es u v g w t (t w) Hv Hwu).
        apply H. apply verts_snoc_intro. left. exact Hw.
      + intros x [<- | []]. unfold sat.
        pose proof (H u (verts_snoc_intro r es u v g u (or_intror (or_introl eq_refl)))) as E.
        rewrite (dfun_in_new r es u v g t (t u) Hv) in E.
        rewrite E, assoc, inv_r, id_l. reflexivity.
  Qed.

  (* ----- the driving network is an acyclic federation ----- *)

  Lemma prec_snoc_new : forall o k v, In k o -> FederationOrder.prec k v (o ++ [v]).
  Proof.
    induction o as [| a o IH]; intros k v Hk; [destruct Hk |]. simpl.
    destruct Hk as [<- | Hk].
    - left. split; [reflexivity | apply in_or_app; right; left; reflexivity].
    - right. apply IH. exact Hk.
  Qed.

  Lemma prec_app_r :
    forall o l k i, FederationOrder.prec k i o -> FederationOrder.prec k i (o ++ l).
  Proof.
    induction o as [| a o IH]; intros l k i H; [destruct H |]. simpl in *.
    destruct H as [[E Hi] | H].
    - left. split; [exact E | apply in_or_app; left; exact Hi].
    - right. apply IH. exact H.
  Qed.

  (* A topological propagation order over exactly the tree's vertices exists. *)
  Theorem drive_order_exists :
    forall r T, tree r T ->
      exists o, FederationOrder.topo (dsrc r T) o /\ (forall w, In w o <-> In w (r :: verts T)).
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu].
    - exists [r]. split.
      + split; [constructor; [intros [] | constructor] |].
        intros i k _ Hk. unfold dsrc in Hk. rewrite rule_nil in Hk. destruct Hk.
      + intro w. simpl. tauto.
    - destruct IH as [o [[Hnd Hsrc] Hset]]. exists (o ++ [v]).
      assert (Hvo : ~ In v o) by (intro H; apply Hv; apply Hset; exact H).
      split; [split |].
      + apply (Permutation_NoDup (Permutation_cons_append o v)). constructor; assumption.
      + intros i k Hi Hk Hko. apply in_app_or in Hi. destruct Hi as [Hi | [<- | []]].
        * assert (Hiv : i <> v) by (intro E; subst; contradiction).
          rewrite (dsrc_out_old r es u v g i Hv Hiv) in Hk.
          assert (Hko' : In k o).
          { unfold dsrc in Hk. destruct (rule r es i) as [[[p h] b] |] eqn:Hr; [| destruct Hk].
            destruct Hk as [<- | []]. apply Hset. exact (proj1 (rule_some r es HT i p h b Hr)). }
          apply prec_app_r. apply Hsrc; assumption.
        * rewrite (dsrc_out_new r es u v g Hv) in Hk. destruct Hk as [<- | []].
          apply prec_snoc_new. apply Hset. exact Hu.
      + intro w. split; intro H.
        * apply in_app_or in H. apply verts_snoc_intro.
          destruct H as [H | [<- | []]]; [left; apply Hset; exact H | right; right; reflexivity].
        * apply in_or_app. destruct (verts_snoc r es u v g w H) as [H' | [-> | ->]];
            [left; apply Hset; exact H' | left; apply Hset; exact Hu | right; left; reflexivity].
    - destruct IH as [o [[Hnd Hsrc] Hset]]. exists (o ++ [u]).
      assert (Huo : ~ In u o) by (intro H; apply Hu; apply Hset; exact H).
      split; [split |].
      + apply (Permutation_NoDup (Permutation_cons_append o u)). constructor; assumption.
      + intros i k Hi Hk Hko. apply in_app_or in Hi. destruct Hi as [Hi | [<- | []]].
        * assert (Hiu : i <> u) by (intro E; subst; contradiction).
          rewrite (dsrc_in_old r es u v g i Hv Hiu) in Hk.
          assert (Hko' : In k o).
          { unfold dsrc in Hk. destruct (rule r es i) as [[[p h] b] |] eqn:Hr; [| destruct Hk].
            destruct Hk as [<- | []]. apply Hset. exact (proj1 (rule_some r es HT i p h b Hr)). }
          apply prec_app_r. apply Hsrc; assumption.
        * rewrite (dsrc_in_new r es u v g Hv) in Hk. destruct Hk as [<- | []].
          apply prec_snoc_new. apply Hset. exact Hv.
      + intro w. split; intro H.
        * apply in_app_or in H. apply verts_snoc_intro.
          destruct H as [H | [<- | []]]; [left; apply Hset; exact H | right; left; reflexivity].
        * apply in_or_app. destruct (verts_snoc r es u v g w H) as [H' | [-> | ->]];
            [left; apply Hset; exact H' | right; left; reflexivity | left; apply Hset; exact Hv].
  Qed.

  (* The plan's network satisfies FederationEvents' per-registry conditions (Common), with no
     validity constraint (the fiber is the whole group) and the identity normalizer. *)
  Lemma drive_common :
    forall r T o (E : Type) (reg : E -> nat) (sig : E -> G -> G),
      FederationOrder.topo (dsrc r T) o -> (forall ev, In (reg ev) o) ->
      FederationEvents.Common G (dsrc r T) (dfun r T) (fun _ _ => True) (fun _ x => x)
        E reg sig o.
  Proof.
    intros r T o E reg sig Ho Hreg. constructor.
    - apply dfun_local.
    - apply topo_topoF. exact Ho.
    - intros; exact I.
    - intros j z z' x _ _ _. unfold dfun. destruct (rule r T j) as [[[p g] b] |]; reflexivity.
    - intros; reflexivity.
    - intros; exact I.
    - exact Hreg.
  Qed.

  (* Running any topological order: every tree registry equals its driven value, the root keeps
     the authority value, and registries off the tree are untouched. *)
  Theorem drive_consistent :
    forall r T o s0, tree r T -> FederationOrder.topo (dsrc r T) o ->
      (forall w, In w o <-> In w (r :: verts T)) ->
      (forall w, In w (r :: verts T) -> drive r T o s0 w = dfun r T w (drive r T o s0) (drive r T o s0 w)) /\
      drive r T o s0 r = s0 r /\
      (forall w, ~ In w (r :: verts T) -> drive r T o s0 w = s0 w).
  Proof.
    intros r T o s0 HT Ho Hset.
    pose proof (drive_common r T o Empty_set (fun x => match x with end)
                  (fun x => match x with end) Ho (fun x => match x with end)) as HC.
    assert (Hfr : forall k, FederationEvents.frun G (dfun r T) o s0 k = drive r T o s0 k)
      by (intro k; unfold drive; apply (frun_run G (dsrc r T)); apply dfun_local).
    assert (Hsolve : forall j, In j o -> drive r T o s0 j = dfun r T j (drive r T o s0) (s0 j)).
    { intros j Hj. rewrite <- (Hfr j).
      rewrite (FederationEvents.frun_solves _ _ _ _ _ _ _ _ _ HC o s0 (topo_topoF _ _ Ho) j Hj).
      apply dfun_local. intros k _. apply Hfr. }
    split; [| split].
    - intros w Hw. destruct (rule r T w) as [[[p g] b] |] eqn:Hr.
      + rewrite (Hsolve w (proj2 (Hset w) Hw)) at 1. unfold dfun. rewrite Hr. reflexivity.
      + unfold dfun at 1. rewrite Hr. reflexivity.
    - rewrite (Hsolve r (proj2 (Hset r) (or_introl eq_refl))). unfold dfun.
      rewrite (root_none r T HT). reflexivity.
    - intros w Hw. rewrite <- (Hfr w). apply FederationEvents.frun_out.
      intro H. apply Hw. apply Hset. exact H.
  Qed.

  (* ----- balance is a static property of the edge (needs the group laws) ----- *)

  Lemma balanced_any_section :
    forall r T sT s u v g, tree r T -> is_section op sT T -> is_section op s T ->
      In u (r :: verts T) -> In v (r :: verts T) -> sat op sT (u, v, g) -> sat op s (u, v, g).
  Proof.
    intros r T sT s u v g HT HsT Hs Hu Hv Hb. unfold sat in *.
    rewrite (tree_unique op e inv assoc id_l inv_r inv_l r T HT sT s HsT Hs u Hu).
    rewrite (tree_unique op e inv assoc id_l inv_r inv_l r T HT sT s HsT Hs v Hv).
    rewrite assoc, Hb. reflexivity.
  Qed.

  (* Any state driven along the tree satisfies every balanced constraint. *)
  Lemma kept_section :
    forall r T B sT, tree r T -> is_section op sT T -> spans r T B ->
      (forall x, In x B -> sat op sT x) ->
      forall t, (forall w, In w (r :: verts T) -> t w = dfun r T w t (t w)) ->
      is_section op t (T ++ B).
  Proof.
    intros r T B sT HT HsT Hsp Hbal t Ht.
    assert (HtT : is_section op t T) by exact (cons_section r T HT t Ht).
    apply section_app. split; [exact HtT |].
    intros [[u v] g] Hx. destruct (Hsp u v g Hx) as [Hu Hv].
    exact (balanced_any_section r T sT t u v g HT HsT HtT Hu Hv (Hbal _ Hx)).
  Qed.

  (* ----- the soundness theorem ----- *)

  Theorem coordinated_sound :
    forall r T B sT, tree r T -> is_section op sT T -> spans r T B ->
      (forall x, In x B -> sat op sT x) ->
      forall o s0, FederationOrder.topo (dsrc r T) o -> (forall w, In w o <-> In w (r :: verts T)) ->
      is_section op (drive r T o s0) (T ++ B) /\
      drive r T o s0 r = s0 r /\
      (forall w, ~ In w (r :: verts T) -> drive r T o s0 w = s0 w) /\
      (forall t, is_section op t (T ++ B) -> t r = s0 r ->
         forall w, In w (r :: verts T) -> t w = drive r T o s0 w) /\
      (forall o', FederationOrder.topo (dsrc r T) o' -> (forall w, In w o' <-> In w (r :: verts T)) ->
         FederationOrder.seq (drive r T o' s0) (drive r T o s0)).
  Proof.
    intros r T B sT HT HsT Hsp Hbal o s0 Ho Hset.
    destruct (drive_consistent r T o s0 HT Ho Hset) as [Hc [Hroot Hoff]].
    assert (HnT : is_section op (drive r T o s0) T) by exact (cons_section r T HT _ Hc).
    split; [exact (kept_section r T B sT HT HsT Hsp Hbal _ Hc) |].
    split; [exact Hroot |]. split; [exact Hoff |]. split.
    - intros t Ht Htr w Hw.
      destruct (proj1 (section_app op t T B) Ht) as [HtT _].
      rewrite (tree_unique op e inv assoc id_l inv_r inv_l r T HT _ t HnT HtT w Hw).
      rewrite Htr, <- Hroot, inv_l, id_r. reflexivity.
    - intros o' Ho' Hset' k. unfold drive.
      apply (FederationOrder.order_independent (dsrc r T) (dfun r T) (dfun_local r T)
               o' o s0 Ho' Ho).
      apply NoDup_Permutation; [exact (proj1 Ho') | exact (proj1 Ho) |].
      intro w. rewrite Hset', Hset. reflexivity.
  Qed.

  (* Existence and uniqueness: for every authority value there is exactly one consistent state of
     the kept network T ++ B on the tree, and every propagation order reaches it. *)
  Theorem coordinated_unique_nf :
    forall r T B sT, tree r T -> is_section op sT T -> spans r T B ->
      (forall x, In x B -> sat op sT x) ->
      forall s0, exists nf,
        is_section op nf (T ++ B) /\ nf r = s0 r /\
        (forall w, ~ In w (r :: verts T) -> nf w = s0 w) /\
        (forall t, is_section op t (T ++ B) -> t r = s0 r ->
           forall w, In w (r :: verts T) -> t w = nf w) /\
        (forall o, FederationOrder.topo (dsrc r T) o -> (forall w, In w o <-> In w (r :: verts T)) ->
           FederationOrder.seq (drive r T o s0) nf).
  Proof.
    intros r T B sT HT HsT Hsp Hbal s0.
    destruct (drive_order_exists r T HT) as [o [Ho Hset]].
    exists (drive r T o s0). exact (coordinated_sound r T B sT HT HsT Hsp Hbal o s0 Ho Hset).
  Qed.

  (* ----- the coordinated set is needed, and exactly ----- *)

  (* Keeping an unbalanced edge, as a writer or as a constraint, leaves no consistent state. *)
  Theorem coordination_needed :
    forall r T B C sT x, tree r T -> is_section op sT T -> spans r T (B ++ C) ->
      In x C -> ~ sat op sT x -> forall t, ~ is_section op t (T ++ B ++ [x]).
  Proof.
    intros r T B C sT x HT HsT Hsp Hx Hnot t Ht.
    assert (Hsp' : spans r T (B ++ [x])).
    { intros u v g H. apply in_app_or in H. destruct H as [H | [-> | []]].
      - apply (Hsp u v g). apply in_or_app. left. exact H.
      - apply (Hsp u v g). apply in_or_app. right. exact Hx. }
    apply (unbalanced_blocks op e inv assoc id_l id_r inv_r inv_l r T (B ++ [x]) sT x
             HT HsT Hsp'); [apply in_or_app; right; left; reflexivity | exact Hnot |].
    exists t. exact Ht.
  Qed.

  (* Exactness: a set of non-tree edges can be kept consistently iff it avoids the coordinated
     (unbalanced) set. *)
  Theorem plan_exact :
    forall r T B C sT, tree r T -> is_section op sT T -> spans r T (B ++ C) ->
      (forall x, In x B -> sat op sT x) -> (forall x, In x C -> ~ sat op sT x) ->
      forall K, incl K (B ++ C) ->
        (has_section op (T ++ K) <-> forall x, In x K -> ~ In x C).
  Proof.
    intros r T B C sT HT HsT Hsp Hbal Hunb K Hincl.
    assert (HspK : spans r T K) by (intros u v g H; apply (Hsp u v g); apply Hincl; exact H).
    rewrite (cycle_basis_criterion op e inv assoc id_l id_r inv_r inv_l r T K sT HT HsT HspK).
    split.
    - intros Hall x Hx HC. exact (Hunb x HC (Hall x Hx)).
    - intros Hno x Hx. destruct (in_app_or _ _ _ (Hincl x Hx)) as [HB | HC].
      + exact (Hbal x HB).
      + exfalso. exact (Hno x Hx HC).
  Qed.

  (* ----- event interleavings under the plan (FederationEvents) ----- *)

  Theorem coordinated_events_converge :
    forall r T B sT o (E : Type) (reg : E -> nat) (sig : E -> G -> G),
      tree r T -> is_section op sT T -> spans r T B -> (forall x, In x B -> sat op sT x) ->
      FederationOrder.topo (dsrc r T) o -> (forall w, In w o <-> In w (r :: verts T)) ->
      (forall ev, In (reg ev) o) ->
      (forall e1 e2 x, reg e1 = r -> reg e2 = r -> sig e1 (sig e2 x) = sig e2 (sig e1 x)) ->
      forall es1 es2, Permutation es1 es2 ->
      forall s, FederationEvents.Cons G (dfun r T) o s ->
        FederationEvents.feq G
          (FederationEvents.runF G (dfun r T) (fun _ x => x) E reg sig o es1 s)
          (FederationEvents.runF G (dfun r T) (fun _ x => x) E reg sig o es2 s) /\
        is_section op (FederationEvents.runF G (dfun r T) (fun _ x => x) E reg sig o es1 s) (T ++ B).
  Proof.
    intros r T B sT o E reg sig HT HsT Hsp Hbal Ho Hset Hreg Hcc es1 es2 Hp s Hcons.
    pose proof (drive_common r T o E reg sig Ho Hreg) as HC.
    assert (H1 : FederationEvents.C1 G (dfun r T) (fun _ _ => True) E reg sig).
    { intros ev z z' b _ _ _ _. unfold dfun.
      destruct (rule r T (reg ev)) as [[[p g] bb] |]; reflexivity. }
    assert (H2 : FederationEvents.C2 G (dfun r T) (fun _ _ => True) E reg sig (fun _ _ => True)).
    { intros e1 e2 z b Hrg _ _ _ _. unfold dfun.
      destruct (rule r T (reg e1)) as [[[p g] bb] |] eqn:Hr; [reflexivity |].
      destruct (Nat.eq_dec (reg e1) r) as [R1 | R1].
      - apply Hcc; [rewrite <- Hrg; exact R1 | exact R1].
      - destruct (driven r T HT (reg e1) (proj1 (Hset _) (Hreg e1)) R1) as [p [g [bb Hs]]].
        rewrite Hs in Hr. discriminate. }
    split.
    - apply (FederationEvents.fed_permutations_converge G (dsrc r T) (dfun r T) _ _ E reg sig
               (fun _ _ => True) o HC H1 H2); [intros; exact I | exact Hp | intro k; exact I | exact Hcons].
    - apply (kept_section r T B sT HT HsT Hsp Hbal). intros w Hw.
      apply (FederationEvents.runF_cons _ _ _ _ _ _ _ _ _ HC es1 s (fun _ => I) Hcons).
      apply Hset. exact Hw.
  Qed.
End Coordinated.

(* ============================================================
   Instances over Z/2 = (bool, xor), the group of CohomologyGraph.v's non-vacuity section. They
   are gsm's two 2-cycles (diagnose_test.go): registry 0 is A, registry 1 is B, values 0/1 are
   false/true, a copy is the label false and the map 1 - x is the label true. Axiom-free.
   ============================================================ *)

(* The spanning tree of both loops: A -> B copy, rooted at A (and, reversed, at B). *)
Definition cc_T : list (@edge bool) := [] ++ [(0, 1, false)].

Lemma cc_tree0 : tree 0 cc_T.
Proof. unfold cc_T. apply t_out; [apply t_nil | left; reflexivity | simpl; intuition congruence]. Qed.

Lemma cc_tree1 : tree 1 cc_T.
Proof. unfold cc_T. apply t_in; [apply t_nil | left; reflexivity | simpl; intuition congruence]. Qed.

Lemma cc_section : is_section xorb sT0 cc_T.
Proof. unfold cc_T. intros [[u v] g] H. simpl in H. destruct H as [H | []]. injection H as Eu Ev Eg. subst. reflexivity. Qed.

Lemma cc_spans : forall X, (forall u v g, In (u, v, g) X -> u <= 1 /\ v <= 1) -> spans 0 cc_T X.
Proof.
  intros X H u v g Hx. destruct (H u v g Hx) as [Hu Hv]. simpl.
  split; [destruct u as [| [| u]] | destruct v as [| [| v]]]; simpl; auto; exfalso; lia.
Qed.

Lemma cc_order0 : FederationOrder.topo (dsrc 0 cc_T) [0; 1].
Proof.
  split; [repeat constructor; simpl; intuition congruence |].
  intros i k Hi Hk Hko. simpl in Hi.
  destruct Hi as [<- | [<- | []]]; cbv in Hk; [destruct Hk | destruct Hk as [<- | []]; simpl; auto].
Qed.

Lemma cc_order0_verts : forall w, In w [0; 1] <-> In w (0 :: verts cc_T).
Proof. intro w. simpl. tauto. Qed.

(* ----- the copy-back loop: balanced, accepted with zero coordination ----- *)

Definition cb_B : list (@edge bool) := [(1, 0, false)].   (* B -> A copy, demoted to a check *)
Definition cb_C : list (@edge bool) := [].                (* nothing coordinated *)

Lemma cb_balanced : forall x, In x cb_B -> sat xorb sT0 x.
Proof. intros x [<- | []]. reflexivity. Qed.

Theorem copyback_zero_coordination :
  forall s0 : nat -> bool, exists nf,
    is_section xorb nf (cc_T ++ cb_B ++ cb_C) /\ nf 0 = s0 0 /\ nf 1 = s0 0 /\
    (forall t, is_section xorb t (cc_T ++ cb_B) -> t 0 = s0 0 -> t 0 = nf 0 /\ t 1 = nf 1) /\
    (forall o, FederationOrder.topo (dsrc 0 cc_T) o -> (forall w, In w o <-> In w (0 :: verts cc_T)) ->
       FederationOrder.seq (drive xorb (fun a => a) 0 cc_T o s0) nf).
Proof.
  intro s0.
  assert (Hsp : spans 0 cc_T cb_B).
  { apply cc_spans. intros u v g [H | []]. injection H as Eu Ev Eg. subst. lia. }
  destruct (coordinated_unique_nf xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r
              xor_inv_l 0 cc_T cb_B sT0 cc_tree0 cc_section Hsp cb_balanced s0)
    as [nf [Hs [Hr [_ [Hu Ho]]]]].
  assert (Hc : is_section xorb (fun _ => s0 0) (cc_T ++ cb_B)).
  { intros [[u v] g] H. simpl in H. destruct H as [H | [H | []]];
      injection H as Eu Ev Eg; subst; reflexivity. }
  exists nf. split; [unfold cb_C; rewrite app_nil_r; exact Hs |]. split; [exact Hr |]. split.
  - symmetry. exact (Hu _ Hc eq_refl 1 (or_intror (or_intror (or_introl eq_refl)))).
  - split; [| exact Ho]. intros t Ht Ht0. split.
    + exact (Hu t Ht Ht0 0 (or_introl eq_refl)).
    + exact (Hu t Ht Ht0 1 (or_intror (or_intror (or_introl eq_refl)))).
Qed.

(* ----- the negation loop: unbalanced, one edge coordinated ----- *)

Definition neg_B : list (@edge bool) := [].                (* nothing kept as a check *)
Definition neg_C : list (@edge bool) := [(1, 0, true)].    (* B -> A 1 - x, coordinated *)

Lemma neg_unbalanced : forall x, In x neg_C -> ~ sat xorb sT0 x.
Proof. intros x [<- | []]. unfold sat, sT0. simpl. discriminate. Qed.

Theorem negation_one_coordinated :
  (forall s0 : nat -> bool, exists nf,
     is_section xorb nf (cc_T ++ neg_B) /\ nf 0 = s0 0 /\ nf 1 = s0 0 /\
     (forall t, is_section xorb t (cc_T ++ neg_B) -> t 0 = s0 0 -> t 0 = nf 0 /\ t 1 = nf 1) /\
     (forall o, FederationOrder.topo (dsrc 0 cc_T) o -> (forall w, In w o <-> In w (0 :: verts cc_T)) ->
        FederationOrder.seq (drive xorb (fun a => a) 0 cc_T o s0) nf)) /\
  (forall t : nat -> bool, ~ is_section xorb t (cc_T ++ neg_B ++ neg_C)).
Proof.
  assert (Hsp : spans 0 cc_T (neg_B ++ neg_C)).
  { apply cc_spans. intros u v g [H | []]. injection H as Eu Ev Eg. subst. lia. }
  split.
  - intro s0.
    destruct (coordinated_unique_nf xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r
                xor_inv_l 0 cc_T neg_B sT0 cc_tree0 cc_section
                (fun u v g H => match H with end) (fun x H => match H with end) s0)
      as [nf [Hs [Hr [_ [Hu Ho]]]]].
    assert (Hc : is_section xorb (fun _ => s0 0) (cc_T ++ neg_B)).
    { intros [[u v] g] H. simpl in H. destruct H as [H | []].
      injection H as Eu Ev Eg. subst. reflexivity. }
    exists nf. split; [exact Hs |]. split; [exact Hr |]. split.
    + symmetry. exact (Hu _ Hc eq_refl 1 (or_intror (or_intror (or_introl eq_refl)))).
    + split; [| exact Ho]. intros t Ht Ht0. split.
      * exact (Hu t Ht Ht0 0 (or_introl eq_refl)).
      * exact (Hu t Ht Ht0 1 (or_intror (or_intror (or_introl eq_refl)))).
  - intro t.
    exact (coordination_needed xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r
             xor_inv_l 0 cc_T neg_B neg_C sT0 (1, 0, true) cc_tree0 cc_section Hsp
             (or_introl eq_refl) (neg_unbalanced _ (or_introl eq_refl)) t).
Qed.

(* ============================================================
   Corners where the naive statement fails.
   ============================================================ *)

(* No authority: the copy-back loop with both edges as writers (a cyclic network, so no
   topological order exists) has two consistent states, and two propagation orders reach
   different ones from the same initial state A = 0, B = 1. *)
Definition cc_wsrc (i : nat) : list nat := match i with 0 => [1] | 1 => [0] | _ => [] end.
Definition cc_wf (i : nat) (s : nat -> bool) (x : bool) : bool :=
  match i with 0 => s 1 | 1 => s 0 | _ => x end.
Definition cc_s0 (k : nat) : bool := match k with 0 => false | _ => true end.

Theorem copyback_without_authority :
  FederationOrder.run cc_wf [0; 1] cc_s0 0 = true /\
  FederationOrder.run cc_wf [1; 0] cc_s0 0 = false /\
  is_section xorb (FederationOrder.run cc_wf [0; 1] cc_s0) (cc_T ++ cb_B) /\
  is_section xorb (FederationOrder.run cc_wf [1; 0] cc_s0) (cc_T ++ cb_B).
Proof.
  split; [reflexivity | split; [reflexivity |]].
  split; intros [[u v] g] H; simpl in H; destruct H as [H | [H | []]];
    injection H as Eu Ev Eg; subst; reflexivity.
Qed.

(* The root matters: the same edges and the same initial state, rooted at A versus at B, reach
   A = B = 0 versus A = B = 1. Both are consistent with the whole loop. *)
Lemma cc_order1 : FederationOrder.topo (dsrc 1 cc_T) [1; 0].
Proof.
  split; [repeat constructor; simpl; intuition congruence |].
  intros i k Hi Hk Hko. simpl in Hi.
  destruct Hi as [<- | [<- | []]]; cbv in Hk; [destruct Hk | destruct Hk as [<- | []]; simpl; auto].
Qed.

Theorem root_choice_matters :
  drive xorb (fun a => a) 0 cc_T [0; 1] cc_s0 0 = false /\
  drive xorb (fun a => a) 0 cc_T [0; 1] cc_s0 1 = false /\
  drive xorb (fun a => a) 1 cc_T [1; 0] cc_s0 0 = true /\
  drive xorb (fun a => a) 1 cc_T [1; 0] cc_s0 1 = true /\
  is_section xorb (drive xorb (fun a => a) 0 cc_T [0; 1] cc_s0) (cc_T ++ cb_B) /\
  is_section xorb (drive xorb (fun a => a) 1 cc_T [1; 0] cc_s0) (cc_T ++ cb_B).
Proof.
  repeat split; try reflexivity;
    intros [[u v] g] H; simpl in H; destruct H as [H | [H | []]];
    injection H as Eu Ev Eg; subst; reflexivity.
Qed.

(* A forward copy network A -> B over any fiber (B reads A, A is the authority), used by the two
   counterexamples below. It is acyclic, with topological order [0; 1]. *)
Definition cc_fsrc (i : nat) : list nat := match i with 1 => [0] | _ => [] end.
Definition cc_ff {V : Type} (i : nat) (s : nat -> V) (x : V) : V :=
  match i with 1 => s 0 | _ => x end.

Lemma cc_forder : FederationOrder.topo cc_fsrc [0; 1].
Proof.
  split; [repeat constructor; simpl; intuition congruence |].
  intros i k Hi Hk Hko. simpl in Hi.
  destruct Hi as [<- | [<- | []]]; simpl in Hk; [destruct Hk | destruct Hk as [<- | []]; simpl; auto].
Qed.

(* Invertibility is needed: with B -> A the constant 0 (not a bijection), the tree-driven normal
   form satisfies the back edge from the authority value 0 and violates it from 1, so whether the
   edge must be coordinated depends on the authority value, not on the cycle. Contrast
   balanced_any_section, where the group laws make it a property of the edge. *)
Definition cc_const0 (_ : bool) : bool := false.

Theorem noninvertible_balance_not_static :
  FederationOrder.topo cc_fsrc [0; 1] /\
  FederationOrder.run cc_ff [0; 1] (fun _ => false) 0
    = cc_const0 (FederationOrder.run cc_ff [0; 1] (fun _ => false) 1) /\
  FederationOrder.run cc_ff [0; 1] (fun _ => true) 0
    <> cc_const0 (FederationOrder.run cc_ff [0; 1] (fun _ => true) 1).
Proof. split; [exact cc_forder | split; [reflexivity | discriminate]]. Qed.

(* The regular action is needed for "no consistent state at all": the bijection of {0, 1, 2}
   swapping 0 and 1 is a non-identity holonomy for the loop A -> B copy, B -> A swap, yet the
   normal form from the authority value 2 satisfies the back edge. From the authority value 0 it
   is violated, so a plan sound for every root value must still coordinate the edge. *)
Definition cc_swap (x : nat) : nat := match x with 0 => 1 | 1 => 0 | n => n end.

Theorem nonfree_holonomy_counterexample :
  (forall x, cc_swap (cc_swap x) = x) /\ cc_swap 0 <> 0 /\
  FederationOrder.run cc_ff [0; 1] (fun _ => 2) 0
    = cc_swap (FederationOrder.run cc_ff [0; 1] (fun _ => 2) 1) /\
  FederationOrder.run cc_ff [0; 1] (fun _ => 0) 0
    <> cc_swap (FederationOrder.run cc_ff [0; 1] (fun _ => 0) 1).
Proof.
  split; [intros [| [| x]]; reflexivity |].
  split; [discriminate | split; [reflexivity | discriminate]].
Qed.
