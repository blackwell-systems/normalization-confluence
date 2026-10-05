(* SignedCycles.v: the invertible-versus-lossy separation, stated on walks, and the finite
   switching (Harary balance) theorem it gives at Z/2. Axiom-free.

   Setting (reading A for groups, as in CohomologyGraph.v): a network is a list of edges (u, v, g)
   labeled by a group G acting on itself by left translation (the regular action); a section is
   s with g (s u) = s v on every edge. A WALK may traverse an edge backward, contributing the
   inverse label (walk); a DIRECTED path uses edges forward only (dpath). The label of a walk
   u -> ... -> w that first crosses g and then h is h g (the transport is applied in order).

   Results.
     section_transport     (the lemma) a section transports along every walk: the walk's label
                           maps s u to s w.
     holonomy_free_section a network whose closed walks all have trivial label has a section. Any
                           finite edge list; no spanning-tree hypothesis (the tree is grown in the
                           proof, edge by edge, one component at a time).
     invertible_merge_is_holonomy
                           (1) two directed paths u -> v with different composite labels h1, h2
                           close (with the second one reversed) into a closed walk at u whose
                           holonomy h2^-1 h1 is not the identity, and no section exists;
                           (2) a section exists iff every closed walk has trivial holonomy, iff
                           walk labels depend only on the endpoints (path independence), iff the
                           labeling is a coboundary (section_iff_coboundary).
     fundamental_cycles_holonomy
                           with a spanning tree T plus extra edges X: every extra edge balanced
                           against the tree's section (cycle_basis_criterion) iff every closed
                           walk of T ++ X has trivial holonomy.
     obstruction_loop_vs_merge
                           (a) invertible: every tree (no undirected cycle) has a section and no
                           non-trivial holonomy (tree_has_section); (b) lossy: the C22 shape is a
                           tree with no section, although each of its two edges alone has one: two
                           directed paths merge at vertex 2 with images that disagree, and no loop
                           is involved (c22_cycle_basis_fails, c22_no_section_recovered, c22_lmin).
   Signed graphs (Z/2 labels under xorb; label true is a negative edge, false a positive one).
     harary_balance        a switching o : nat -> bool exists (every edge (u, v, b) has
                           b = xorb (o u) (o v), so flipping the orders at the vertices with o = true
                           makes every edge positive) iff no closed walk carries an odd number of
                           negative edges (no negative undirected cycle). This is Harary's balance
                           theorem for finite signed graphs, proved here (not cited), as the Z/2
                           instance of holonomy_free_section.
     balanced_dicycles_positive, balanced_no_positive_acyclic
                           in a balanced signed graph every directed cycle is positive; so balance
                           together with "no positive directed cycle" (the sign condition of
                           Thomas's first rule) leaves no directed cycle at all.
   Non-vacuity: z2_triangle_* (an unbalanced Z/2 triangle: holonomy true, no section, two directed
   paths 0 -> 2 with labels true and false) and z2_square_balanced. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.RootSet NC.LossyMinimum.
Import ListNotations.

Section Walks.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  (* Walks: an edge may be crossed forward (label g) or backward (label g^-1). *)
  Inductive walk (es : list (@edge G)) : nat -> nat -> G -> Prop :=
  | w_nil : forall u, walk es u u e
  | w_fwd : forall u v w g h, In (u, v, g) es -> walk es v w h -> walk es u w (op h g)
  | w_bwd : forall u v w g h, In (v, u, g) es -> walk es v w h -> walk es u w (op h (inv g)).

  (* Directed paths: forward edges only. *)
  Inductive dpath (es : list (@edge G)) : nat -> nat -> G -> Prop :=
  | d_nil : forall u, dpath es u u e
  | d_fwd : forall u v w g h, In (u, v, g) es -> dpath es v w h -> dpath es u w (op h g).

  (* Every closed walk has trivial holonomy. *)
  Definition holonomy_free (es : list (@edge G)) : Prop := forall u h, walk es u u h -> h = e.

  (* Walk labels depend only on the endpoints. *)
  Definition path_independent (es : list (@edge G)) : Prop :=
    forall u v h1 h2, walk es u v h1 -> walk es u v h2 -> h1 = h2.

  (* ----- group facts ----- *)

  Lemma sc_inv_unique : forall a b, op a b = e -> b = inv a.
  Proof.
    intros a b H. rewrite <- (id_l b), <- (inv_l a), <- assoc, H, id_r. reflexivity.
  Qed.

  Lemma sc_inv_e : inv e = e.
  Proof. symmetry. apply sc_inv_unique. apply id_l. Qed.

  Lemma sc_inv_op : forall a b, inv (op a b) = op (inv b) (inv a).
  Proof.
    intros a b. symmetry. apply sc_inv_unique.
    rewrite assoc, <- (assoc a b (inv b)), inv_r, id_r. apply inv_r.
  Qed.

  Lemma sc_inv_inv : forall a, inv (inv a) = a.
  Proof. intros a. symmetry. apply sc_inv_unique. apply inv_l. Qed.

  Lemma sc_rcancel : forall a b c, op a c = op b c -> a = b.
  Proof.
    intros a b c H.
    rewrite <- (id_r a), <- (id_r b), <- (inv_r c), !assoc, H. reflexivity.
  Qed.

  (* ----- walks ----- *)

  Lemma dpath_walk : forall es u v h, dpath es u v h -> walk es u v h.
  Proof.
    intros es u v h H. induction H as [u | u v w g h Hin _ IH]; [apply w_nil |].
    apply w_fwd with v; assumption.
  Qed.

  Lemma walk_edge : forall es u v g, In (u, v, g) es -> walk es u v g.
  Proof.
    intros es u v g Hin. rewrite <- (id_l g). apply w_fwd with v; [exact Hin | apply w_nil].
  Qed.

  Lemma walk_edge_back : forall es u v g, In (u, v, g) es -> walk es v u (inv g).
  Proof.
    intros es u v g Hin. rewrite <- (id_l (inv g)). apply w_bwd with u; [exact Hin | apply w_nil].
  Qed.

  Lemma walk_app : forall es u v a, walk es u v a -> forall w b, walk es v w b -> walk es u w (op b a).
  Proof.
    intros es u v a H. induction H as [u | u v x g h Hin _ IH | u v x g h Hin _ IH]; intros w b Hb.
    - rewrite id_r. exact Hb.
    - rewrite assoc. apply w_fwd with v; [exact Hin | apply IH; exact Hb].
    - rewrite assoc. apply w_bwd with v; [exact Hin | apply IH; exact Hb].
  Qed.

  Lemma walk_rev : forall es u v h, walk es u v h -> walk es v u (inv h).
  Proof.
    intros es u v h H. induction H as [u | u v w g h Hin _ IH | u v w g h Hin _ IH].
    - rewrite sc_inv_e. apply w_nil.
    - rewrite sc_inv_op. apply (walk_app es w v (inv h) IH u (inv g)).
      apply walk_edge_back. exact Hin.
    - rewrite sc_inv_op, sc_inv_inv. apply (walk_app es w v (inv h) IH u g).
      apply walk_edge. exact Hin.
  Qed.

  (* THE LEMMA: a section transports along every walk. *)
  Lemma section_transport :
    forall es s, is_section op s es -> forall u v h, walk es u v h -> op h (s u) = s v.
  Proof.
    intros es s Hs u v h H. induction H as [u | u v w g h Hin _ IH | u v w g h Hin _ IH].
    - apply id_l.
    - pose proof (Hs _ Hin) as E. unfold sat in E. rewrite <- assoc, E. exact IH.
    - pose proof (Hs _ Hin) as E. unfold sat in E.
      rewrite <- assoc, <- E, (assoc (inv g) g (s v)), inv_l, id_l. exact IH.
  Qed.

  Theorem section_holonomy_free : forall es, has_section op es -> holonomy_free es.
  Proof.
    intros es [s Hs] u h H. apply (sc_rcancel h e (s u)). rewrite id_l.
    exact (section_transport es s Hs u u h H).
  Qed.

  Lemma holonomy_free_path_independent : forall es, holonomy_free es <-> path_independent es.
  Proof.
    intros es. split.
    - intros Hf u v h1 h2 H1 H2.
      pose proof (Hf u _ (walk_app es u v h1 H1 u (inv h2) (walk_rev es u v h2 H2))) as E.
      rewrite (sc_inv_unique _ _ E), sc_inv_inv. reflexivity.
    - intros Hp u h H. exact (Hp u u h e H (w_nil es u)).
  Qed.

  (* ----- growing a section: the converse, on any finite edge list ----- *)

  (* s is consistent on W: it transports along every walk between two vertices of W. *)
  Definition WInv (es : list (@edge G)) (W : list nat) (s : nat -> G) : Prop :=
    forall u v h, In u W -> In v W -> walk es u v h -> op h (s u) = s v.

  Definition WClosed (es : list (@edge G)) (W : list nat) : Prop :=
    forall u v g, In (u, v, g) es -> (In u W <-> In v W).

  Lemma walk_closed : forall es W, WClosed es W -> forall a b h, walk es a b h -> (In a W <-> In b W).
  Proof.
    intros es W Hc a b h H. induction H as [u | u v w g h Hin _ IH | u v w g h Hin _ IH].
    - tauto.
    - pose proof (Hc u v g Hin). tauto.
    - pose proof (Hc v u g Hin). tauto.
  Qed.

  Lemma crossing_or_closed2 : forall W es,
    (exists u v g, In (u, v, g) es /\ ((In u W /\ ~ In v W) \/ (In v W /\ ~ In u W))) \/
    WClosed es W.
  Proof.
    intros W es. induction es as [| [[u v] g] es IH].
    - right. intros a b c [].
    - destruct IH as [[a [b [c [Hin H]]]] | Hc].
      + left. exists a, b, c. split; [right; exact Hin | exact H].
      + destruct (in_dec Nat.eq_dec u W) as [Hu | Hu]; destruct (in_dec Nat.eq_dec v W) as [Hv | Hv].
        * right. intros a b c [E | Hin]; [injection E as -> -> ->; tauto | exact (Hc a b c Hin)].
        * left. exists u, v, g. split; [left; reflexivity | left; split; assumption].
        * left. exists u, v, g. split; [left; reflexivity | right; split; assumption].
        * right. intros a b c [E | Hin]; [injection E as -> -> ->; tauto | exact (Hc a b c Hin)].
  Qed.

  Lemma outside_or_covered : forall (l W : list nat),
    (exists b, In b l /\ ~ In b W) \/ (forall b, In b l -> In b W).
  Proof.
    intros l W. induction l as [| x l IH].
    - right. intros b [].
    - destruct (in_dec Nat.eq_dec x W) as [Hx | Hx].
      + destruct IH as [[b [Hb Hn]] | Hc].
        * left. exists b. split; [right; exact Hb | exact Hn].
        * right. intros b [<- | Hb]; [exact Hx | exact (Hc b Hb)].
      + left. exists x. split; [left; reflexivity | exact Hx].
  Qed.

  Definition sc_out (W : list nat) (w : nat) : bool := if in_dec Nat.eq_dec w W then false else true.

  Lemma sc_measure : forall l W b, In b l -> ~ In b W ->
    length (filter (sc_out (b :: W)) l) < length (filter (sc_out W) l).
  Proof.
    intros l W b Hb Hn. apply (rs_filter_lt nat _ _ l) with (y := b).
    - intros x _ Hx. unfold sc_out in *.
      destruct (in_dec Nat.eq_dec x (b :: W)) as [H1 | H1]; [discriminate |].
      destruct (in_dec Nat.eq_dec x W) as [H2 | H2]; [exfalso; apply H1; right; exact H2 | reflexivity].
    - exact Hb.
    - unfold sc_out. destruct (in_dec Nat.eq_dec b W); [contradiction | reflexivity].
    - unfold sc_out. destruct (in_dec Nat.eq_dec b (b :: W)) as [_ | H]; [reflexivity |].
      exfalso. apply H. left. reflexivity.
  Qed.

  (* Attach b to W through a walk a -> b with label g0. *)
  Lemma attach_step : forall es W s a b g0,
    holonomy_free es -> WInv es W s -> In a W -> ~ In b W -> walk es a b g0 ->
    WInv es (b :: W) (upd s b (op g0 (s a))).
  Proof.
    intros es W s a b g0 Hf HI Ha Hb Hab u v h Hu Hv H.
    assert (Na : a <> b) by (intro E; subst; contradiction).
    destruct Hu as [Eu | Hu]; destruct Hv as [Ev | Hv].
    - subst u v. rewrite (Hf b h H). apply id_l.
    - subst u. assert (Nv : v <> b) by (intro E; subst; contradiction).
      rewrite upd_same, (upd_other s b _ v Nv).
      rewrite assoc. apply (HI a v (op h g0) Ha Hv). exact (walk_app es a b g0 Hab v h H).
    - subst v. assert (Nu : u <> b) by (intro E; subst; contradiction).
      rewrite upd_same, (upd_other s b _ u Nu).
      pose proof (HI u a (op (inv g0) h) Hu Ha (walk_app es u b h H a (inv g0) (walk_rev es a b g0 Hab)))
        as E.
      rewrite <- E, !assoc, inv_r, id_l. reflexivity.
    - assert (Nu : u <> b) by (intro E; subst; contradiction).
      assert (Nv : v <> b) by (intro E; subst; contradiction).
      rewrite (upd_other s b _ u Nu), (upd_other s b _ v Nv). exact (HI u v h Hu Hv H).
  Qed.

  (* Start a new component at b (no edge crosses W). *)
  Lemma isolated_step : forall es W s b,
    holonomy_free es -> WInv es W s -> WClosed es W -> ~ In b W -> WInv es (b :: W) (upd s b e).
  Proof.
    intros es W s b Hf HI Hc Hb u v h Hu Hv H.
    pose proof (walk_closed es W Hc u v h H) as Hio.
    destruct Hu as [Eu | Hu]; destruct Hv as [Ev | Hv].
    - subst u v. rewrite (Hf b h H). apply id_l.
    - subst u. exfalso. apply Hb. apply Hio. exact Hv.
    - subst v. exfalso. apply Hb. apply Hio. exact Hu.
    - assert (Nu : u <> b) by (intro E; subst; contradiction).
      assert (Nv : v <> b) by (intro E; subst; contradiction).
      rewrite (upd_other s b _ u Nu), (upd_other s b _ v Nv). exact (HI u v h Hu Hv H).
  Qed.

  Lemma grow_section : forall es, holonomy_free es -> forall n W s, WInv es W s ->
    length (filter (sc_out W) (verts es)) <= n ->
    exists W' s', WInv es W' s' /\ forall w, In w (verts es) -> In w W'.
  Proof.
    intros es Hf n. induction n as [| n IH]; intros W s HI Hn.
    - destruct (outside_or_covered (verts es) W) as [[b [Hb Hnb]] | Hcov].
      + pose proof (sc_measure (verts es) W b Hb Hnb). lia.
      + exists W, s. split; assumption.
    - destruct (crossing_or_closed2 W es) as [[u [v [g [Hin [[Hu Hv] | [Hv Hu]]]]]] | Hc].
      + apply (IH (v :: W) (upd s v (op g (s u)))).
        * exact (attach_step es W s u v g Hf HI Hu Hv (walk_edge es u v g Hin)).
        * pose proof (sc_measure (verts es) W v (proj2 (in_verts_edge es u v g Hin)) Hv). lia.
      + apply (IH (u :: W) (upd s u (op (inv g) (s v)))).
        * exact (attach_step es W s v u (inv g) Hf HI Hv Hu (walk_edge_back es u v g Hin)).
        * pose proof (sc_measure (verts es) W u (proj1 (in_verts_edge es u v g Hin)) Hu). lia.
      + destruct (outside_or_covered (verts es) W) as [[b [Hb Hnb]] | Hcov].
        * apply (IH (b :: W) (upd s b e)).
          -- exact (isolated_step es W s b Hf HI Hc Hnb).
          -- pose proof (sc_measure (verts es) W b Hb Hnb). lia.
        * exists W, s. split; assumption.
  Qed.

  Theorem holonomy_free_section : forall es, holonomy_free es -> has_section op es.
  Proof.
    intros es Hf.
    destruct (grow_section es Hf _ [] (fun _ => e) (fun u v h Hu => match Hu with end) (le_n _))
      as [W [s [HI Hcov]]].
    exists s. intros [[u v] g] Hin. unfold sat.
    destruct (in_verts_edge es u v g Hin) as [Hu Hv].
    exact (HI u v g (Hcov u Hu) (Hcov v Hv) (walk_edge es u v g Hin)).
  Qed.

  (* ----- the theorem ----- *)

  Theorem invertible_merge_is_holonomy : forall es,
    (forall u v h1 h2, dpath es u v h1 -> dpath es u v h2 -> h1 <> h2 ->
       walk es u u (op (inv h2) h1) /\ op (inv h2) h1 <> e /\ ~ has_section op es) /\
    (has_section op es <-> holonomy_free es) /\
    (has_section op es <-> path_independent es) /\
    (coboundary op inv es <-> holonomy_free es).
  Proof.
    intros es.
    assert (Hiff : has_section op es <-> holonomy_free es)
      by (split; [apply section_holonomy_free | apply holonomy_free_section]).
    split; [| split; [exact Hiff | split]].
    - intros u v h1 h2 P1 P2 Ne.
      assert (W : walk es u u (op (inv h2) h1)).
      { exact (walk_app es u v h1 (dpath_walk es u v h1 P1) u (inv h2)
                 (walk_rev es u v h2 (dpath_walk es u v h2 P2))). }
      assert (Nt : op (inv h2) h1 <> e).
      { intro E. apply Ne. rewrite (sc_inv_unique _ _ E), sc_inv_inv. reflexivity. }
      split; [exact W | split; [exact Nt |]].
      intro Hs. apply Nt. exact (section_holonomy_free es Hs u _ W).
    - rewrite Hiff. apply holonomy_free_path_independent.
    - rewrite <- (section_iff_coboundary op e inv assoc id_r inv_r inv_l). exact Hiff.
  Qed.

  (* Tie to cycle_basis_criterion: per fundamental cycle. *)
  Corollary fundamental_cycles_holonomy :
    forall r T X sT, tree r T -> is_section op sT T ->
      (forall u v g, In (u, v, g) X -> In u (r :: verts T) /\ In v (r :: verts T)) ->
      ((forall x, In x X -> sat op sT x) <-> holonomy_free (T ++ X)).
  Proof.
    intros r T X sT HT HsT Hsp.
    rewrite <- (cycle_basis_criterion op e inv assoc id_l id_r inv_r inv_l r T X sT HT HsT Hsp).
    split; [apply section_holonomy_free | apply holonomy_free_section].
  Qed.
End Walks.

(* ============================================================================================ *)
(* The separation: loops (invertible) versus merges (lossy).                                    *)
(* ============================================================================================ *)

Theorem obstruction_loop_vs_merge :
  (forall (G : Type) (op : G -> G -> G) (e : G) (inv : G -> G),
     (forall a b c, op a (op b c) = op (op a b) c) ->
     (forall a, op e a = a) -> (forall a, op a e = a) ->
     (forall a, op a (inv a) = e) -> (forall a, op (inv a) a = e) ->
     forall r es, tree r es -> has_section op es /\ holonomy_free op e inv es) /\
  (tree 2 c22_es /\
   ~ (exists s : nat -> bool, msection s c22_es) /\
   (exists s : nat -> bool, msection s [(0, 2, fun _ : bool => false)]) /\
   (exists s : nat -> bool, msection s [(1, 2, fun _ : bool => true)]) /\
   is_lmin c22_es 1).
Proof.
  split.
  - intros G op e inv assoc id_l id_r inv_r inv_l r es HT.
    pose proof (tree_has_section op e inv assoc id_l inv_r r es HT) as Hs.
    split; [exact Hs | exact (section_holonomy_free op e inv assoc id_l id_r inv_r inv_l es Hs)].
  - split; [exact (proj1 c22_cycle_basis_fails) |].
    split; [exact c22_no_section_recovered |].
    split; [exists (fun _ => false); intros x [<- | []]; reflexivity |].
    split; [exists (fun _ => true); intros x [<- | []]; reflexivity |].
    exact (proj2 c22_lmin).
Qed.

(* ============================================================================================ *)
(* Signed graphs: Z/2 under xorb. Label true = negative edge, false = positive edge.            *)
(* ============================================================================================ *)

Lemma z2_assoc : forall a b c, xorb a (xorb b c) = xorb (xorb a b) c.
Proof. intros [] [] []; reflexivity. Qed.
Lemma z2_id_l : forall a, xorb false a = a. Proof. intros []; reflexivity. Qed.
Lemma z2_id_r : forall a, xorb a false = a. Proof. intros []; reflexivity. Qed.
Lemma z2_inv : forall a, xorb a ((fun x : bool => x) a) = false. Proof. intros []; reflexivity. Qed.

Definition swalk (sg : list (@edge bool)) : nat -> nat -> bool -> Prop :=
  walk xorb false (fun x => x) sg.
Definition sdpath (sg : list (@edge bool)) : nat -> nat -> bool -> Prop :=
  dpath xorb false sg.

(* A switching: flipping the vertices with o = true makes every edge positive. *)
Definition Switching (sg : list (@edge bool)) (o : nat -> bool) : Prop :=
  forall u v b, In (u, v, b) sg -> b = xorb (o u) (o v).

Lemma switching_section : forall sg o, Switching sg o <-> is_section xorb o sg.
Proof.
  intros sg o. split.
  - intros H [[u v] b] Hin. unfold sat. rewrite (H u v b Hin). destruct (o u), (o v); reflexivity.
  - intros H u v b Hin. pose proof (H _ Hin) as E. unfold sat in E. rewrite <- E.
    destruct b, (o u); reflexivity.
Qed.

(* Harary's balance theorem, finite case, proved: a switching to all-positive exists iff no closed
   walk carries an odd number of negative edges. *)
Theorem harary_balance : forall sg,
  (exists o, Switching sg o) <-> (forall u h, swalk sg u u h -> h = false).
Proof.
  intros sg.
  pose proof (invertible_merge_is_holonomy xorb false (fun x => x) z2_assoc z2_id_l z2_id_r z2_inv
                z2_inv sg) as (_ & H & _).
  unfold has_section in H. unfold holonomy_free in H. rewrite <- H.
  split; intros [o Ho]; exists o; apply switching_section; exact Ho.
Qed.

(* In a balanced signed graph every directed cycle is positive. *)
Theorem balanced_dicycles_positive : forall sg o, Switching sg o ->
  forall u v g h, In (u, v, g) sg -> sdpath sg v u h -> xorb h g = false.
Proof.
  intros sg o Ho u v g h Hin P.
  apply (section_holonomy_free xorb false (fun x => x) z2_assoc z2_id_l z2_id_r z2_inv z2_inv sg
           (ex_intro _ o (proj1 (switching_section sg o) Ho)) u).
  apply (w_fwd xorb false (fun x => x) sg u v u g h Hin).
  exact (dpath_walk xorb false (fun x => x) sg v u h P).
Qed.

(* Balance plus Thomas's sign condition "no positive directed cycle" leaves no directed cycle. *)
Corollary balanced_no_positive_acyclic : forall sg o, Switching sg o ->
  (forall u v g h, In (u, v, g) sg -> sdpath sg v u h -> xorb h g = true) ->
  forall u v g h, In (u, v, g) sg -> ~ sdpath sg v u h.
Proof.
  intros sg o Ho Hneg u v g h Hin P.
  pose proof (balanced_dicycles_positive sg o Ho u v g h Hin P) as E1.
  rewrite (Hneg u v g h Hin P) in E1. discriminate E1.
Qed.

(* ----- non-vacuity ----- *)

(* An unbalanced triangle: 0 -> 1 positive, 1 -> 2 positive, 0 -> 2 negative. The two directed
   paths 0 -> 2 have labels false and true, so the closed walk has holonomy true. *)
Definition z2_tri : list (@edge bool) := [(0, 1, false); (1, 2, false); (0, 2, true)].

Theorem z2_triangle_merge :
  sdpath z2_tri 0 2 false /\ sdpath z2_tri 0 2 true /\
  swalk z2_tri 0 0 true /\ ~ (exists o, Switching z2_tri o).
Proof.
  assert (P1 : sdpath z2_tri 0 2 false).
  { change false with (xorb (xorb false false) false).
    apply (d_fwd xorb false z2_tri 0 1 2 false (xorb false false)); [simpl; tauto |].
    apply (d_fwd xorb false z2_tri 1 2 2 false false); [simpl; tauto | apply d_nil]. }
  assert (P2 : sdpath z2_tri 0 2 true).
  { change true with (xorb false true).
    apply (d_fwd xorb false z2_tri 0 2 2 true false); [simpl; tauto | apply d_nil]. }
  destruct (proj1 (invertible_merge_is_holonomy xorb false (fun x => x) z2_assoc z2_id_l z2_id_r
                     z2_inv z2_inv z2_tri) 0 2 true false P2 P1 ltac:(discriminate))
    as [W [_ Hn]].
  split; [exact P1 | split; [exact P2 | split; [exact W |]]].
  intros [o Ho]. apply Hn. exists o. apply switching_section. exact Ho.
Qed.

(* A balanced 4-cycle with two negative edges: switching o = (0, 1, 1, 0) on 0, 1, 2, 3. *)
Definition z2_square : list (@edge bool) := [(0, 1, true); (1, 2, false); (2, 3, true); (3, 0, false)].

Theorem z2_square_balanced :
  Switching z2_square (fun v => match v with 1 | 2 => true | _ => false end) /\
  forall u h, swalk z2_square u u h -> h = false.
Proof.
  assert (H : Switching z2_square (fun v => match v with 1 | 2 => true | _ => false end)).
  { intros u v b Hin. simpl in Hin.
    destruct Hin as [E | [E | [E | [E | []]]]]; injection E as <- <- <-; reflexivity. }
  split; [exact H | apply harary_balance; exists (fun v => match v with 1 | 2 => true | _ => false end); exact H].
Qed.
