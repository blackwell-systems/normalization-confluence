(* RootSet.v: the root-set criterion for lossy networks in the constraint reading, mechanized
   axiom-free. This closes the row "general graph (no out-arborescence, several cycles): none
   mechanized; none known" of REGIME-AUDIT section 12 for reading A of LOSSY-NETWORKS.md, and is
   open problem P1 of that note.

   Setting (reading A, CohomologyGeneral.v). A network is a list G of edges (u, v, f) with
   f : V -> V an arbitrary (lossy) map on one fiber V; a state s : nat -> V is a section when
   f (s u) = s v on every edge (msection s G). CohomologyGeneral.v decides sections when ONE
   vertex reaches all others (out_tree_section, out_tree_unique, rooted_criterion). Here the root
   is replaced by a ROOT SET R: a list of vertices such that every vertex of G is reachable from
   some root (root_set R G). A minimum root set is one representative per source strongly
   connected component of G (David, JAIR 1995, Appendix A.1); any superset is also a root set.

   Driving. An outward spanning forest F from R (oforest R F) is grown edge by edge, each edge
   attaching one fresh vertex to the already reached set R ++ verts F, so every vertex has
   exactly one driving path from exactly one root. drive F a is the state obtained from root
   values a by pushing them along F (fold_left of upd). spanning_forest R G F additionally asks
   F to be a subgraph of G that covers every vertex of G.

     root_set_iff_forest        R is a root set of G iff G has an outward spanning forest from R
     out_forest_section         the driven state is a section of the forest, for EVERY root
                                assignment, and keeps the root values (drive_root)
     out_forest_unique          sections of the forest agreeing on R agree on every reached vertex
     root_set_criterion         fixed root values: a section of F ++ X with the root values of a
                                forest section sF exists iff sF satisfies every non-driving edge
                                (the multi-root rooted_criterion)
     root_set_exists            a section of F ++ X exists iff SOME root assignment drives a state
                                satisfying every non-driving edge
     driving_paths              each reached vertex w is driven by one root rho w through one
                                path composite p w: drive F a w = p w (a (rho w))
     root_set_agreement         the criterion in agreement form: for every non-driving edge
                                (u, w, f), f (p u (a (rho u))) = p w (a (rho w))
     root_set_criterion_graph   for any root set and spanning forest of G:
                                (exists s, msection s G) <-> exists a, msection (drive F a) G
     root_set_criterion_values  the same with the root values fixed
     root_set_bijection         sections and consistent root assignments correspond: a section is
                                the driven state of its own root values, the driven state keeps
                                its root values, and root values determine the section
     root_set_count             with a finite enumeration of V: the list of consistent root
                                tuples (a filter of the product of root domains) and the list of
                                sections restricted to the network's vertices are both duplicate
                                free, the second is exactly the sections, and they have the same
                                length; so #sections = #consistent root assignments
     root_set_decide            existence is a search over the product of root domains

   Agreement form. The non-driving edges are of two kinds: an edge from the tree of root r_i into
   the tree of root r_j (i <> j) says the root values agree at the vertex where the trees meet
   (two driving paths into one vertex); an edge inside one tree (or a back edge into a root) is
   the single-root condition of rooted_criterion. root_set_criterion checks both kinds at once.

   Single root. otree_oforest: an otree from r is an oforest from [r]; rooted_criterion_recovered
   and out_tree_section_recovered re-derive CohomologyGeneral's theorems as the case R = [r].

   Instances.
     diamond_*        one root, two parallel lossy paths 0 -> 1 -> 3 and 0 -> 2 -> 3 over tri that
                      disagree at every root value: no section, zero consistent root values
     c22_*            c22_cycle_basis_fails's shape: two roots 0, 1 with constant maps into 2: no
                      section, zero consistent root tuples (recovers the no-section half)
     two_*            two roots collapsing into one vertex over tri: 5 of the 9 root tuples are
                      consistent and the network has exactly 5 sections
     scc_*            a root set containing a strongly connected component {0, 1} (with a lossy
                      back edge) and a second root 2: exactly 1 of 4 root tuples is consistent;
                      neither {0, 1} alone nor {2} alone is a root set

   Optimality (cited, not mechanized). Deciding whether a section exists is NP-complete in general
   (LOSSY-NETWORKS.md section 3.2, a reduction from 3-SAT; consistent with Cooper, Cohen and
   Jeavons 1994 as reported by David 1995). So the search over the product of root domains is
   not avoidable in general unless P = NP. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral.
Import ListNotations.

(* ===================================================================== *)
(* Small list facts (stated locally so the file builds on Coq 8.18 to Rocq 9.3). *)

Lemma rs_nodup_app :
  forall (A : Type) (a b : list A),
    NoDup a -> NoDup b -> (forall z, In z a -> ~ In z b) -> NoDup (a ++ b).
Proof.
  intros A a b Ha. induction Ha as [| x a Hx Ha IH]; intros Hb Hd; simpl; [exact Hb |].
  constructor.
  - intro H. apply in_app_or in H. destruct H as [H | H]; [exact (Hx H) |].
    exact (Hd x (or_introl eq_refl) H).
  - apply IH; [exact Hb |]. intros z Hz. exact (Hd z (or_intror Hz)).
Qed.

Lemma rs_nodup_flat_map :
  forall (A B : Type) (g : A -> list B) (l : list A),
    NoDup l -> (forall x, In x l -> NoDup (g x)) ->
    (forall x y z, In x l -> In y l -> In z (g x) -> In z (g y) -> x = y) ->
    NoDup (flat_map g l).
Proof.
  intros A B g l Hl. induction Hl as [| x l Hx Hl IH]; intros Hg Hd; simpl; [constructor |].
  apply rs_nodup_app.
  - apply Hg. left. reflexivity.
  - apply IH; [intros y Hy; apply Hg; right; exact Hy |].
    intros a b z Ha Hb Hza Hzb. apply (Hd a b z (or_intror Ha) (or_intror Hb) Hza Hzb).
  - intros z Hz Hin. apply in_flat_map in Hin. destruct Hin as [y [Hy Hzy]].
    assert (E : x = y) by exact (Hd x y z (or_introl eq_refl) (or_intror Hy) Hz Hzy).
    subst. exact (Hx Hy).
Qed.

Lemma rs_nodup_filter :
  forall (A : Type) (p : A -> bool) (l : list A), NoDup l -> NoDup (filter p l).
Proof.
  intros A p l Hl. induction Hl as [| x l Hx Hl IH]; simpl; [constructor |].
  destruct (p x); [| exact IH]. constructor; [| exact IH].
  intro H. apply filter_In in H. exact (Hx (proj1 H)).
Qed.

Lemma rs_filter_le :
  forall (A : Type) (p q : A -> bool) (l : list A),
    (forall x, In x l -> q x = true -> p x = true) -> length (filter q l) <= length (filter p l).
Proof.
  intros A p q l. induction l as [| x l IH]; intro H; simpl; [lia |].
  assert (H' : forall y, In y l -> q y = true -> p y = true) by (intros y Hy; apply H; right; exact Hy).
  specialize (IH H'). destruct (q x) eqn:Eq.
  - rewrite (H x (or_introl eq_refl) Eq). simpl. lia.
  - destruct (p x); simpl; lia.
Qed.

Lemma rs_filter_lt :
  forall (A : Type) (p q : A -> bool) (l : list A),
    (forall x, In x l -> q x = true -> p x = true) ->
    forall y, In y l -> p y = true -> q y = false ->
    length (filter q l) < length (filter p l).
Proof.
  intros A p q l. induction l as [| x l IH]; intros H y Hy Hp Hq; [destruct Hy |].
  assert (H' : forall z, In z l -> q z = true -> p z = true) by (intros z Hz; apply H; right; exact Hz).
  simpl. destruct Hy as [<- | Hy].
  - rewrite Hp, Hq. simpl. pose proof (rs_filter_le A p q l H'). lia.
  - specialize (IH H' y Hy Hp Hq). destruct (q x) eqn:Eq.
    + rewrite (H x (or_introl eq_refl) Eq). simpl. lia.
    + destruct (p x); simpl; lia.
Qed.

Lemma rs_map_app_prefix :
  forall (A B : Type) (f g : A -> B) (R L : list A),
    map f (R ++ L) = map g (R ++ L) -> map f R = map g R.
Proof.
  intros A B f g R L. induction R as [| x R IH]; simpl; intro H; [reflexivity |].
  injection H as E1 E2. rewrite E1, (IH E2). reflexivity.
Qed.

(* ===================================================================== *)
(* Forests, driving, and the criterion. *)

Section RootSet.
  Context {V : Type}.

  (* An outward spanning forest from the root list R: each edge attaches one fresh vertex to the
     already reached set R ++ verts es, pointing away from it. *)
  Inductive oforest (R : list nat) : list (@edge (V -> V)) -> Prop :=
  | f_nil : oforest R []
  | f_out : forall es u v f,
      oforest R es -> In u (R ++ verts es) -> ~ In v (R ++ verts es) ->
      oforest R (es ++ [(u, v, f)]).

  (* Driving root values along a forest. *)
  Definition dstep (s : nat -> V) (x : @edge (V -> V)) : nat -> V :=
    let '(u, v, f) := x in upd s v (f (s u)).

  Definition drive (F : list (@edge (V -> V))) (a : nat -> V) : nat -> V := fold_left dstep F a.

  Lemma drive_snoc :
    forall es u v f a, drive (es ++ [(u, v, f)]) a = upd (drive es a) v (f (drive es a u)).
  Proof. intros es u v f a. unfold drive. rewrite fold_left_app. reflexivity. Qed.

  Lemma verts_snoc_set :
    forall (R : list nat) es u v (f : V -> V) w, In w (R ++ verts (es ++ [(u, v, f)])) ->
      In w (R ++ verts es) \/ w = u \/ w = v.
  Proof.
    intros R es u v f w Hw. rewrite verts_app in Hw. simpl in Hw.
    apply in_app_or in Hw. destruct Hw as [Hw | Hw]; [left; apply in_or_app; left; exact Hw |].
    apply in_app_or in Hw. destruct Hw as [Hw | Hw]; [left; apply in_or_app; right; exact Hw |].
    destruct Hw as [Hw | [Hw | []]]; right; [left | right]; symmetry; exact Hw.
  Qed.

  (* The driven state keeps the root values. *)
  Theorem drive_root : forall R F, oforest R F -> forall a r, In r R -> drive F a r = a r.
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv]; intros a r Hr; [reflexivity |].
    rewrite drive_snoc, upd_other; [exact (IH a r Hr) |].
    intro E. subst. apply Hv. apply in_or_app. left. exact Hr.
  Qed.

  (* Driving along a forest: every root assignment gives a section of the forest. *)
  Theorem out_forest_section : forall R F, oforest R F -> forall a, msection (drive F a) F.
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv]; intro a; [intros x [] |].
    rewrite drive_snoc. apply msection_app. split.
    - apply msection_upd_fresh; [apply IH |]. intro H. apply Hv. apply in_or_app. right. exact H.
    - intros x [<- | []]. unfold msat. rewrite upd_same, upd_other; [reflexivity |].
      intro E. subst. exact (Hv Hu).
  Qed.

  (* ... and sections of the forest are determined by their root values. *)
  Theorem out_forest_unique :
    forall R F, oforest R F ->
    forall s t, msection s F -> msection t F -> (forall r, In r R -> s r = t r) ->
    forall w, In w (R ++ verts F) -> s w = t w.
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv]; intros s t Hs Ht Hr w Hw.
    - simpl in Hw. rewrite app_nil_r in Hw. exact (Hr w Hw).
    - destruct (proj1 (msection_app _ _ _) Hs) as [Hs1 Hsx].
      destruct (proj1 (msection_app _ _ _) Ht) as [Ht1 Htx].
      pose proof (Hsx (u, v, f) (or_introl eq_refl)) as Es.
      pose proof (Htx (u, v, f) (or_introl eq_refl)) as Et.
      unfold msat in Es, Et.
      destruct (verts_snoc_set R es u v f w Hw) as [Hold | [-> | ->]].
      + exact (IH s t Hs1 Ht1 Hr w Hold).
      + exact (IH s t Hs1 Ht1 Hr u Hu).
      + rewrite <- Es, <- Et. f_equal. exact (IH s t Hs1 Ht1 Hr u Hu).
  Qed.

  Corollary section_driven :
    forall R F, oforest R F -> forall s, msection s F ->
      forall w, In w (R ++ verts F) -> drive F s w = s w.
  Proof.
    intros R F HF s Hs w Hw.
    apply (out_forest_unique R F HF (drive F s) s (out_forest_section R F HF s) Hs); [| exact Hw].
    intros r Hr. exact (drive_root R F HF s r Hr).
  Qed.

  Corollary drive_ext :
    forall R F, oforest R F -> forall a b, (forall r, In r R -> a r = b r) ->
      forall w, In w (R ++ verts F) -> drive F a w = drive F b w.
  Proof.
    intros R F HF a b Hab w Hw.
    apply (out_forest_unique R F HF _ _ (out_forest_section R F HF a)
             (out_forest_section R F HF b)); [| exact Hw].
    intros r Hr. rewrite (drive_root R F HF a r Hr), (drive_root R F HF b r Hr). exact (Hab r Hr).
  Qed.

  Definition spans (W : list nat) (X : list (@edge (V -> V))) : Prop :=
    forall u v f, In (u, v, f) X -> In u W /\ In v W.

  (* The root-set criterion with the root values fixed: with an outward spanning forest F from R
     and non-driving edges X among its vertices, F ++ X has a section with the root values of a
     forest section sF iff sF satisfies every non-driving edge. *)
  Theorem root_set_criterion :
    forall R F X sF, oforest R F -> msection sF F -> spans (R ++ verts F) X ->
      ((exists s, msection s (F ++ X) /\ forall r, In r R -> s r = sF r) <->
       forall x, In x X -> msat sF x).
  Proof.
    intros R F X sF HF HsF Hsp. split.
    - intros [s [Hs Hr]] [[u v] f] Hx.
      destruct (proj1 (msection_app _ _ _) Hs) as [HsF' HsX].
      pose proof (HsX _ Hx) as E. unfold msat in E |- *.
      destruct (Hsp u v f Hx) as [Hu Hv].
      assert (Hr' : forall r, In r R -> sF r = s r) by (intros r H; symmetry; exact (Hr r H)).
      rewrite (out_forest_unique R F HF sF s HsF HsF' Hr' u Hu),
              (out_forest_unique R F HF sF s HsF HsF' Hr' v Hv).
      exact E.
    - intro Hbal. exists sF. split; [| reflexivity]. apply msection_app. split; [exact HsF |].
      intros x Hx. exact (Hbal x Hx).
  Qed.

  (* The same, stated with a root assignment a and its driven state. *)
  Corollary root_set_criterion_driven :
    forall R F X, oforest R F -> spans (R ++ verts F) X -> forall a,
      ((exists s, msection s (F ++ X) /\ forall r, In r R -> s r = a r) <->
       forall x, In x X -> msat (drive F a) x).
  Proof.
    intros R F X HF Hsp a.
    rewrite <- (root_set_criterion R F X (drive F a) HF (out_forest_section R F HF a) Hsp).
    split; intros [s [Hs Hr]]; exists s; split; try exact Hs; intros r H;
      rewrite (Hr r H); [symmetry |]; exact (drive_root R F HF a r H).
  Qed.

  (* Existence: a section exists iff some root assignment drives a state satisfying every
     non-driving edge. *)
  Theorem root_set_exists :
    forall R F X, oforest R F -> spans (R ++ verts F) X ->
      ((exists s, msection s (F ++ X)) <-> exists a, forall x, In x X -> msat (drive F a) x).
  Proof.
    intros R F X HF Hsp. split.
    - intros [s Hs]. exists s.
      apply (proj1 (root_set_criterion_driven R F X HF Hsp s)). exists s. split; [exact Hs |].
      intros r _. reflexivity.
    - intros [a Ha]. destruct (proj2 (root_set_criterion_driven R F X HF Hsp a) Ha) as [s [Hs _]].
      exists s. exact Hs.
  Qed.

  (* Every reached vertex w is driven by exactly one root rho w through one path composite p w. *)
  Theorem driving_paths :
    forall R F, oforest R F ->
      exists (rho : nat -> nat) (p : nat -> V -> V),
        forall w, In w (R ++ verts F) -> In (rho w) R /\ forall a, drive F a w = p w (a (rho w)).
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv].
    - exists (fun w => w), (fun _ x => x). intros w Hw. simpl in Hw. rewrite app_nil_r in Hw.
      split; [exact Hw | reflexivity].
    - destruct IH as [rho [p Hp]].
      exists (fun w => if Nat.eq_dec w v then rho u else rho w),
             (fun w => if Nat.eq_dec w v then (fun x => f (p u x)) else p w).
      intros w Hw. destruct (Nat.eq_dec w v) as [-> | Hne].
      + split; [exact (proj1 (Hp u Hu)) |]. intro a.
        rewrite drive_snoc, upd_same, (proj2 (Hp u Hu) a). reflexivity.
      + assert (Hold : In w (R ++ verts es)).
        { destruct (verts_snoc_set R es u v f w Hw) as [H | [-> | ->]];
            [exact H | exact Hu | contradiction]. }
        split; [exact (proj1 (Hp w Hold)) |]. intro a.
        rewrite drive_snoc, upd_other; [exact (proj2 (Hp w Hold) a) | exact Hne].
  Qed.

  (* The agreement form: a section exists iff some root values make, for every non-driving edge
     (u, w, f), the value pushed from u's root through u's path and f equal the value driven
     from w's root through w's path. When the two roots differ this is agreement of two roots
     at a vertex reached from both (the join reading, LOSSY-NETWORKS.md section 3.3). *)
  Theorem root_set_agreement :
    forall R F X, oforest R F -> spans (R ++ verts F) X ->
      exists (rho : nat -> nat) (p : nat -> V -> V),
        (forall w, In w (R ++ verts F) -> In (rho w) R /\ forall a, drive F a w = p w (a (rho w))) /\
        ((exists s, msection s (F ++ X)) <->
         exists a, forall u w f, In (u, w, f) X -> f (p u (a (rho u))) = p w (a (rho w))).
  Proof.
    intros R F X HF Hsp. destruct (driving_paths R F HF) as [rho [p Hp]].
    exists rho, p. split; [exact Hp |]. rewrite (root_set_exists R F X HF Hsp).
    split; intros [a Ha]; exists a.
    - intros u w f Hx. destruct (Hsp u w f Hx) as [Hu Hw]. pose proof (Ha _ Hx) as E.
      unfold msat in E. rewrite (proj2 (Hp u Hu) a), (proj2 (Hp w Hw) a) in E. exact E.
    - intros [[u w] f] Hx. destruct (Hsp u w f Hx) as [Hu Hw]. unfold msat.
      rewrite (proj2 (Hp u Hu) a), (proj2 (Hp w Hw) a). exact (Ha u w f Hx).
  Qed.

  (* ----- root sets of a graph ----- *)

  Inductive reach (G : list (@edge (V -> V))) (R : list nat) : nat -> Prop :=
  | reach_root : forall r, In r R -> reach G R r
  | reach_step : forall u v f, reach G R u -> In (u, v, f) G -> reach G R v.

  (* R is a root set of G: every vertex of G is reachable from some root. *)
  Definition root_set (R : list nat) (G : list (@edge (V -> V))) : Prop :=
    forall w, In w (verts G) -> reach G R w.

  Definition spanning_forest (R : list nat) (G F : list (@edge (V -> V))) : Prop :=
    oforest R F /\ incl F G /\ forall w, In w (verts G) -> In w (R ++ verts F).

  Definition closed (G : list (@edge (V -> V))) (W : list nat) : Prop :=
    forall u v f, In (u, v, f) G -> In u W -> In v W.

  Lemma closed_reach :
    forall G R W, closed G W -> (forall r, In r R -> In r W) -> forall w, reach G R w -> In w W.
  Proof.
    intros G R W Hc HR w H. induction H as [r Hr | u v f H IH Hin]; [exact (HR r Hr) |].
    exact (Hc u v f Hin IH).
  Qed.

  Lemma forest_reach :
    forall R F, oforest R F -> forall G, incl F G -> forall w, In w (R ++ verts F) -> reach G R w.
  Proof.
    intros R F HF. induction HF as [| es u v f HF IH Hu Hv]; intros G Hi w Hw.
    - simpl in Hw. rewrite app_nil_r in Hw. apply reach_root. exact Hw.
    - assert (Hi' : incl es G) by (intros x Hx; apply Hi; apply in_or_app; left; exact Hx).
      destruct (verts_snoc_set R es u v f w Hw) as [Hold | [-> | ->]].
      + exact (IH G Hi' w Hold).
      + exact (IH G Hi' u Hu).
      + apply (reach_step G R u v f (IH G Hi' u Hu)). apply Hi. apply in_or_app. right. left.
        reflexivity.
  Qed.

  Lemma crossing_or_closed :
    forall (W : list nat) (G : list (@edge (V -> V))),
      (exists u v f, In (u, v, f) G /\ In u W /\ ~ In v W) \/ closed G W.
  Proof.
    intros W G. induction G as [| [[u v] f] G IH].
    - right. intros a b g [].
    - destruct (in_dec Nat.eq_dec u W) as [Hu | Hu]; [destruct (in_dec Nat.eq_dec v W) as [Hv | Hv] |].
      + destruct IH as [[a [b [g [Hin [Ha Hb]]]]] | Hc].
        * left. exists a, b, g. split; [right; exact Hin | split; assumption].
        * right. intros a b g [E | Hin] Ha; [injection E as -> -> ->; exact Hv |].
          exact (Hc a b g Hin Ha).
      + left. exists u, v, f. split; [left; reflexivity | split; assumption].
      + destruct IH as [[a [b [g [Hin [Ha Hb]]]]] | Hc].
        * left. exists a, b, g. split; [right; exact Hin | split; assumption].
        * right. intros a b g [E | Hin] Ha; [injection E as -> -> ->; contradiction |].
          exact (Hc a b g Hin Ha).
  Qed.

  Definition outside (W : list nat) (w : nat) : bool :=
    if in_dec Nat.eq_dec w W then false else true.

  Lemma grow :
    forall R G n F, oforest R F -> incl F G ->
      length (filter (outside (R ++ verts F)) (verts G)) <= n ->
      exists F', oforest R F' /\ incl F' G /\ closed G (R ++ verts F').
  Proof.
    intros R G n. induction n as [| n IH]; intros F HF Hi Hn;
      (destruct (crossing_or_closed (R ++ verts F) G) as [[u [v [f [Hin [Hu Hv]]]]] | Hc];
       [| exists F; split; [exact HF | split; [exact Hi | exact Hc]]]).
    - (* a crossing edge would strictly decrease a measure that is already 0 *)
      set (F2 := F ++ [(u, v, f)]).
      assert (Hlt : length (filter (outside (R ++ verts F2)) (verts G)) <
                    length (filter (outside (R ++ verts F)) (verts G))).
      { apply (rs_filter_lt nat _ _ (verts G)) with (y := v).
        - intros x _ Hx. unfold outside in *.
          destruct (in_dec Nat.eq_dec x (R ++ verts F)) as [H1 | H1]; [| reflexivity].
          destruct (in_dec Nat.eq_dec x (R ++ verts F2)) as [H2 | H2]; [discriminate |].
          exfalso. apply H2. unfold F2. rewrite verts_app. rewrite app_assoc.
          apply in_or_app. left. exact H1.
        - exact (proj2 (in_verts_edge G u v f Hin)).
        - unfold outside. destruct (in_dec Nat.eq_dec v (R ++ verts F)); [contradiction | reflexivity].
        - unfold outside. destruct (in_dec Nat.eq_dec v (R ++ verts F2)) as [_ | H]; [reflexivity |].
          exfalso. apply H. unfold F2. rewrite verts_app. simpl. apply in_or_app. right.
          apply in_or_app. right. right. left. reflexivity. }
      lia.
    - set (F2 := F ++ [(u, v, f)]).
      assert (HF2 : oforest R F2) by (apply f_out; assumption).
      assert (Hi2 : incl F2 G).
      { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | [<- | []]]; [apply Hi; exact Hx | exact Hin]. }
      apply (IH F2 HF2 Hi2).
      assert (Hlt : length (filter (outside (R ++ verts F2)) (verts G)) <
                    length (filter (outside (R ++ verts F)) (verts G))).
      { apply (rs_filter_lt nat _ _ (verts G)) with (y := v).
        - intros x _ Hx. unfold outside in *.
          destruct (in_dec Nat.eq_dec x (R ++ verts F)) as [H1 | H1]; [| reflexivity].
          destruct (in_dec Nat.eq_dec x (R ++ verts F2)) as [H2 | H2]; [discriminate |].
          exfalso. apply H2. unfold F2. rewrite verts_app. rewrite app_assoc.
          apply in_or_app. left. exact H1.
        - exact (proj2 (in_verts_edge G u v f Hin)).
        - unfold outside. destruct (in_dec Nat.eq_dec v (R ++ verts F)); [contradiction | reflexivity].
        - unfold outside. destruct (in_dec Nat.eq_dec v (R ++ verts F2)) as [_ | H]; [reflexivity |].
          exfalso. apply H. unfold F2. rewrite verts_app. simpl. apply in_or_app. right.
          apply in_or_app. right. right. left. reflexivity. }
      lia.
  Qed.

  (* Root sets are exactly the vertex lists that carry an outward spanning forest. *)
  Theorem root_set_iff_forest :
    forall R G, root_set R G <-> exists F, spanning_forest R G F.
  Proof.
    intros R G. split.
    - intro HR.
      destruct (grow R G _ [] (f_nil R) (fun x (H : In x []) => match H with end) (le_n _))
        as [F [HF [Hi Hc]]].
      exists F. split; [exact HF | split; [exact Hi |]].
      intros w Hw. apply (closed_reach G R _ Hc); [| exact (HR w Hw)].
      intros r Hr. apply in_or_app. left. exact Hr.
    - intros [F [HF [Hi Hcov]]] w Hw. exact (forest_reach R F HF G Hi w (Hcov w Hw)).
  Qed.

  Lemma spanning_spans :
    forall R G F, spanning_forest R G F -> spans (R ++ verts F) G.
  Proof.
    intros R G F [_ [_ Hcov]] u v f Hin.
    destruct (in_verts_edge G u v f Hin) as [Hu Hv]. split; apply Hcov; assumption.
  Qed.

  Lemma msection_sub :
    forall (s : nat -> V) (F G : list (@edge (V -> V))), incl F G -> (msection s G <-> msection s (F ++ G)).
  Proof.
    intros s F G Hi. rewrite msection_app. split; [| tauto].
    intro H. split; [| exact H]. intros x Hx. exact (H x (Hi x Hx)).
  Qed.

  (* The root-set criterion on a graph: for a root set R and a spanning forest F of G from R,
     G has a section iff some root assignment drives a state satisfying every edge of G. *)
  Theorem root_set_criterion_graph :
    forall R G F, spanning_forest R G F ->
      ((exists s, msection s G) <-> exists a, msection (drive F a) G).
  Proof.
    intros R G F Hsf. pose proof Hsf as [HF [Hi Hcov]].
    pose proof (root_set_exists R F G HF (spanning_spans R G F Hsf)) as H.
    split.
    - intros [s Hs]. destruct (proj1 H (ex_intro _ s (proj1 (msection_sub s F G Hi) Hs))) as [a Ha].
      exists a. exact Ha.
    - intros [a Ha]. exists (drive F a). exact Ha.
  Qed.

  Theorem root_set_criterion_values :
    forall R G F, spanning_forest R G F -> forall a,
      ((exists s, msection s G /\ forall r, In r R -> s r = a r) <-> msection (drive F a) G).
  Proof.
    intros R G F Hsf a. pose proof Hsf as [HF [Hi Hcov]].
    pose proof (root_set_criterion_driven R F G HF (spanning_spans R G F Hsf) a) as H.
    split.
    - intros [s [Hs Hr]].
      exact (proj1 H (ex_intro _ s (conj (proj1 (msection_sub s F G Hi) Hs) Hr))).
    - intro Ha. exists (drive F a). split; [exact Ha |]. exact (drive_root R F HF a).
  Qed.

  (* Sections correspond to consistent root assignments: a section is the driven state of its own
     root values; the driven state of a root assignment keeps it; and two sections with the same
     root values agree on every vertex of the network. *)
  Theorem root_set_bijection :
    forall R G F, spanning_forest R G F ->
      (forall s, msection s G -> msection (drive F s) G /\
                                 forall w, In w (R ++ verts F) -> drive F s w = s w) /\
      (forall a r, In r R -> drive F a r = a r) /\
      (forall s t, msection s G -> msection t G -> (forall r, In r R -> s r = t r) ->
                   forall w, In w (R ++ verts F) -> s w = t w).
  Proof.
    intros R G F Hsf. pose proof Hsf as [HF [Hi Hcov]].
    split; [| split].
    - intros s Hs. split.
      + apply (proj1 (root_set_criterion_values R G F Hsf s)). exists s. split; [exact Hs |].
        intros r _. reflexivity.
      + apply (section_driven R F HF s). intros x Hx. exact (Hs x (Hi x Hx)).
    - exact (drive_root R F HF).
    - intros s t Hs Ht Hr. apply (out_forest_unique R F HF s t); [| | exact Hr];
        intros x Hx; [exact (Hs x (Hi x Hx)) | exact (Ht x (Hi x Hx))].
  Qed.

  (* ----- counting: a search over the product of root domains ----- *)

  Section Count.
    Variable Vdec : forall x y : V, {x = y} + {x <> y}.
    Variable v0 : V.

    Definition msat_b (s : nat -> V) (x : @edge (V -> V)) : bool :=
      let '(u, v, f) := x in if Vdec (f (s u)) (s v) then true else false.

    Definition msection_b (s : nat -> V) (es : list (@edge (V -> V))) : bool :=
      forallb (msat_b s) es.

    Lemma msection_b_spec : forall s es, msection_b s es = true <-> msection s es.
    Proof.
      intros s es. unfold msection_b, msection. rewrite forallb_forall. split.
      - intros H [[u v] f] Hx. specialize (H _ Hx). unfold msat_b in H. unfold msat.
        destruct (Vdec (f (s u)) (s v)); [assumption | discriminate].
      - intros H [[u v] f] Hx. specialize (H _ Hx). unfold msat in H. unfold msat_b.
        destruct (Vdec (f (s u)) (s v)); [reflexivity | contradiction].
    Qed.

    (* A root tuple, read as a root assignment (earlier occurrences win; v0 off the roots). *)
    Fixpoint assign (R : list nat) (a : list V) : nat -> V :=
      match R, a with
      | r :: R', x :: a' => upd (assign R' a') r x
      | _, _ => fun _ => v0
      end.

    Lemma assign_map : forall R (s : nat -> V) r, In r R -> assign R (map s R) r = s r.
    Proof.
      induction R as [| q R IH]; intros s r Hr; [destruct Hr |]. simpl.
      destruct (Nat.eq_dec r q) as [-> | Hne]; [apply upd_same |].
      rewrite upd_other; [| exact Hne]. apply IH. destruct Hr as [E | H]; [congruence | exact H].
    Qed.

    Lemma map_assign : forall R a, NoDup R -> length a = length R -> map (assign R a) R = a.
    Proof.
      induction R as [| q R IH]; intros a Hnd Hl; destruct a as [| x a]; simpl in *;
        try reflexivity; try discriminate.
      inversion Hnd as [| q' R' Hq Hnd']. subst.
      rewrite upd_same. f_equal. rewrite <- (IH a Hnd' (eq_add_S _ _ Hl)) at 2.
      apply map_ext_in. intros w Hw. apply upd_other. intro E. subst. exact (Hq Hw).
    Qed.

    (* All k-tuples over l. *)
    Fixpoint tuples (l : list V) (k : nat) : list (list V) :=
      match k with
      | 0 => [[]]
      | S k => flat_map (fun x => map (cons x) (tuples l k)) l
      end.

    Lemma tuples_spec :
      forall l k t, In t (tuples l k) <-> length t = k /\ forall x, In x t -> In x l.
    Proof.
      intros l k. induction k as [| k IH]; intro t; simpl.
      - split.
        + intros [<- | []]. split; [reflexivity | intros x []].
        + intros [Hl _]. destruct t; [left; reflexivity | discriminate].
      - rewrite in_flat_map. split.
        + intros [x [Hx Ht]]. apply in_map_iff in Ht. destruct Ht as [t' [<- Ht']].
          apply IH in Ht'. destruct Ht' as [Hl Hin]. simpl. split; [rewrite Hl; reflexivity |].
          intros y [<- | Hy]; [exact Hx | exact (Hin y Hy)].
        + intros [Hl Hin]. destruct t as [| x t]; [discriminate |].
          exists x. split; [apply Hin; left; reflexivity |]. apply in_map.
          apply IH. split; [simpl in Hl; lia |]. intros y Hy. apply Hin. right. exact Hy.
    Qed.

    Lemma tuples_nodup : forall l k, NoDup l -> NoDup (tuples l k).
    Proof.
      intros l k Hl. induction k as [| k IH]; simpl; [constructor; [intros [] | constructor] |].
      apply rs_nodup_flat_map; [exact Hl | |].
      - intros x _. apply nodup_map_inj; [exact IH |]. intros a b _ _ E. injection E. tauto.
      - intros x y z _ _ Hx Hy. apply in_map_iff in Hx, Hy.
        destruct Hx as [a [<- _]]. destruct Hy as [b [E _]]. injection E as E1 _. symmetry. exact E1.
    Qed.

    (* The consistent root tuples, and the network's sections listed through them. *)
    Definition rs_ok (R : list nat) (G F : list (@edge (V -> V))) (a : list V) : bool :=
      msection_b (drive F (assign R a)) G.

    Definition consistent_roots (lv : list V) (R : list nat) (G F : list (@edge (V -> V))) :
      list (list V) := filter (rs_ok R G F) (tuples lv (length R)).

    Definition sections_on (lv : list V) (R : list nat) (G F : list (@edge (V -> V))) :
      list (list V) :=
      map (fun a => map (drive F (assign R a)) (R ++ verts F)) (consistent_roots lv R G F).

    (* Counting: with V enumerated by lv (no duplicates), the consistent root tuples are a
       duplicate-free list; the sections, recorded on the network's vertices R ++ verts F, are a
       duplicate-free list containing exactly the restrictions of sections of G; and the two have
       the same length. So #sections = #consistent root assignments. *)
    Theorem root_set_count :
      forall lv R G F, spanning_forest R G F -> NoDup R -> NoDup lv -> (forall x, In x lv) ->
        NoDup (consistent_roots lv R G F) /\
        (forall a, In a (consistent_roots lv R G F) <->
                   length a = length R /\ msection (drive F (assign R a)) G) /\
        NoDup (sections_on lv R G F) /\
        (forall s, msection s G -> In (map s (R ++ verts F)) (sections_on lv R G F)) /\
        (forall t, In t (sections_on lv R G F) ->
                   exists s, msection s G /\ map s (R ++ verts F) = t) /\
        length (sections_on lv R G F) = length (consistent_roots lv R G F).
    Proof.
      intros lv R G F Hsf HR Hlv Hfull.
      pose proof Hsf as [HF [Hi Hcov]].
      assert (Hin : forall a, In a (consistent_roots lv R G F) <->
                    length a = length R /\ msection (drive F (assign R a)) G).
      { intro a. unfold consistent_roots, rs_ok. rewrite filter_In, tuples_spec, msection_b_spec.
        split; [tauto |]. intros [Hl Hs]. split; [split; [exact Hl | intros x _; apply Hfull] | exact Hs]. }
      split; [| split; [exact Hin | split; [| split; [| split]]]].
      - apply rs_nodup_filter. apply tuples_nodup. exact Hlv.
      - apply nodup_map_inj; [apply rs_nodup_filter; apply tuples_nodup; exact Hlv |].
        intros a b Ha Hb Eab. apply Hin in Ha, Hb.
        apply rs_map_app_prefix in Eab.
        rewrite <- (map_assign R a HR (proj1 Ha)), <- (map_assign R b HR (proj1 Hb)).
        rewrite <- (map_ext_in _ _ R (drive_root R F HF (assign R a))),
                <- (map_ext_in _ _ R (drive_root R F HF (assign R b))).
        exact Eab.
      - intros s Hs. unfold sections_on. apply in_map_iff. exists (map s R). split.
        + apply map_ext_in. intros w Hw.
          rewrite (drive_ext R F HF (assign R (map s R)) s (assign_map R s) w Hw).
          apply (section_driven R F HF s); [intros x Hx; exact (Hs x (Hi x Hx)) | exact Hw].
        + apply Hin. split; [apply cg_len_map |].
          apply (proj1 (root_set_criterion_values R G F Hsf _)). exists s. split; [exact Hs |].
          intros r Hr. symmetry. exact (assign_map R s r Hr).
      - intros t Ht. unfold sections_on in Ht. apply in_map_iff in Ht. destruct Ht as [a [<- Ha]].
        apply Hin in Ha. exists (drive F (assign R a)). split; [exact (proj2 Ha) | reflexivity].
      - unfold sections_on. apply cg_len_map.
    Qed.

    (* Existence is a search over the product of root domains. *)
    Theorem root_set_decide :
      forall lv R G F, spanning_forest R G F -> (forall x, In x lv) ->
        ((exists s, msection s G) <-> existsb (rs_ok R G F) (tuples lv (length R)) = true).
    Proof.
      intros lv R G F Hsf Hfull. pose proof Hsf as [HF [Hi Hcov]].
      rewrite existsb_exists. split.
      - intros [s Hs]. exists (map s R). split.
        + apply tuples_spec. split; [apply cg_len_map | intros x _; apply Hfull].
        + unfold rs_ok. apply msection_b_spec.
          apply (proj1 (root_set_criterion_values R G F Hsf _)). exists s. split; [exact Hs |].
          intros r Hr. symmetry. exact (assign_map R s r Hr).
      - intros [a [_ Ha]]. exists (drive F (assign R a)). apply msection_b_spec. exact Ha.
    Qed.
  End Count.

  (* ----- the single-root case ----- *)

  Lemma otree_oforest : forall r (T : list (@edge (V -> V))), otree r T <-> oforest [r] T.
  Proof.
    intros r T. split; intro H.
    - induction H as [| es u v f H IH Hu Hv]; [apply f_nil | apply f_out; assumption].
    - induction H as [| es u v f H IH Hu Hv]; [apply o_nil | apply o_out; assumption].
  Qed.

  (* CohomologyGeneral.rooted_criterion, re-derived as the case R = [r]. *)
  Theorem rooted_criterion_recovered :
    forall r (T X : list (@edge (V -> V))) (sT : nat -> V), otree r T -> msection sT T ->
      (forall u v f, In (u, v, f) X -> In u (r :: verts T) /\ In v (r :: verts T)) ->
      ((exists s, msection s (T ++ X) /\ s r = sT r) <-> forall x, In x X -> msat sT x).
  Proof.
    intros r T X sT HT HsT Hsp.
    rewrite <- (root_set_criterion [r] T X sT (proj1 (otree_oforest r T) HT) HsT Hsp).
    split; intros [s [Hs Hr]]; exists s; split; try exact Hs.
    - intros q [<- | []]. exact Hr.
    - exact (Hr r (or_introl eq_refl)).
  Qed.

  Theorem out_tree_section_recovered :
    forall r (T : list (@edge (V -> V))), otree r T -> forall x0 : V, exists s, msection s T /\ s r = x0.
  Proof.
    intros r T HT x0. pose proof (proj1 (otree_oforest r T) HT) as HF.
    exists (drive T (fun _ => x0)). split; [exact (out_forest_section [r] T HF _) |].
    exact (drive_root [r] T HF _ r (or_introl eq_refl)).
  Qed.

  Theorem out_tree_unique_recovered :
    forall r (T : list (@edge (V -> V))), otree r T ->
    forall s t : nat -> V, msection s T -> msection t T -> s r = t r ->
    forall w, In w (r :: verts T) -> s w = t w.
  Proof.
    intros r T HT s t Hs Ht Hr w Hw.
    apply (out_forest_unique [r] T (proj1 (otree_oforest r T) HT) s t Hs Ht); [| exact Hw].
    intros q [<- | []]. exact Hr.
  Qed.
End RootSet.

(* ===================================================================== *)
(* Instances. *)

Lemma bool_full : forall x : bool, In x [true; false].
Proof. intros []; simpl; auto. Qed.

Lemma bool_nodup : NoDup [true; false].
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma tri_nodup : NoDup tri_all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

(* (1) The diamond: one root 0 and two parallel paths 0 -> 1 -> 3 (copies) and 0 -> 2 -> 3, the
   second through the lossy map dia_h (t0 |-> t1, t1 |-> t0, t2 |-> t0). The paths disagree at
   vertex 3 for every root value, so there is no section. *)
Definition dia_h (x : tri) : tri := match x with t0 => t1 | _ => t0 end.

Definition dia_G : list (@edge (tri -> tri)) :=
  [(0, 1, fun x => x); (0, 2, dia_h); (1, 3, fun x => x); (2, 3, fun x => x)].
Definition dia_F : list (@edge (tri -> tri)) :=
  (([] ++ [(0, 1, fun x => x)]) ++ [(0, 2, dia_h)]) ++ [(1, 3, fun x => x)].

Theorem diamond_forest : spanning_forest [0] dia_G dia_F.
Proof.
  split; [| split].
  - unfold dia_F. repeat apply f_out; try apply f_nil; simpl; intuition lia.
  - intros x Hx. unfold dia_F in Hx. simpl in Hx. unfold dia_G. simpl. tauto.
  - intros w Hw. simpl in Hw. simpl. intuition.
Qed.

Theorem diamond_not_injective : dia_h t1 = dia_h t2.
Proof. reflexivity. Qed.

Theorem diamond_no_consistent_root : forall a : nat -> tri, ~ msection (drive dia_F a) dia_G.
Proof.
  intros a H. pose proof (H (2, 3, fun x => x) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as E.
  unfold msat in E. cbn in E. destruct (a 0); discriminate E.
Qed.

Theorem diamond_no_section : ~ exists s : nat -> tri, msection s dia_G.
Proof.
  rewrite (root_set_criterion_graph [0] dia_G dia_F diamond_forest).
  intros [a Ha]. exact (diamond_no_consistent_root a Ha).
Qed.

Theorem diamond_count :
  length (consistent_roots tri_eq_dec t0 tri_all [0] dia_G dia_F) = 0.
Proof. vm_compute. reflexivity. Qed.

(* (2) c22_cycle_basis_fails's shape: roots 0 and 1, constant maps false and true into 2. *)
Definition c22_F : list (@edge (bool -> bool)) := [] ++ [(0, 2, fun _ => false)].

Theorem c22_forest : spanning_forest [0; 1] c22_es c22_F.
Proof.
  split; [| split].
  - unfold c22_F. apply f_out; [apply f_nil | simpl; auto | simpl; intuition lia].
  - intros x [<- | []]. left. reflexivity.
  - intros w Hw. simpl in Hw. simpl. intuition.
Qed.

Theorem c22_root_set : root_set [0; 1] c22_es /\ ~ root_set [0] c22_es /\ ~ root_set [1] c22_es.
Proof.
  split; [| split].
  - apply root_set_iff_forest. exists c22_F. exact c22_forest.
  - intro H. assert (Hc : closed c22_es [0; 2]).
    { intros u v f Hin Hu. simpl in Hin. destruct Hin as [E | [E | []]];
        injection E as Eu Ev _; subst; simpl in *; intuition lia. }
    pose proof (closed_reach c22_es [0] [0; 2] Hc (fun r H => match H with
      | or_introl E => or_introl E | or_intror F => match F with end end) 1 (H 1 ltac:(simpl; auto)))
      as H1. simpl in H1. intuition lia.
  - intro H. assert (Hc : closed c22_es [1; 2]).
    { intros u v f Hin Hu. simpl in Hin. destruct Hin as [E | [E | []]];
        injection E as Eu Ev _; subst; simpl in *; intuition lia. }
    pose proof (closed_reach c22_es [1] [1; 2] Hc (fun r H => match H with
      | or_introl E => or_introl E | or_intror F => match F with end end) 0 (H 0 ltac:(simpl; auto)))
      as H0. simpl in H0. intuition lia.
Qed.

Theorem c22_no_consistent_root : forall a : nat -> bool, ~ msection (drive c22_F a) c22_es.
Proof.
  intros a H. pose proof (H (1, 2, fun _ => true) (or_intror (or_introl eq_refl))) as E.
  unfold msat in E. cbn in E. discriminate E.
Qed.

Theorem c22_no_section_recovered : ~ exists s : nat -> bool, msection s c22_es.
Proof.
  rewrite (root_set_criterion_graph [0; 1] c22_es c22_F c22_forest).
  intros [a Ha]. exact (c22_no_consistent_root a Ha).
Qed.

Theorem c22_count :
  length (consistent_roots bool_dec false [true; false] [0; 1] c22_es c22_F) = 0.
Proof. vm_compute. reflexivity. Qed.

(* (3) Two roots 0 and 1 collapsing into vertex 2 over tri with the lossy map two_c
   (t0, t1 |-> t0, t2 |-> t2): sections exist, and there are exactly 5 of them, one per
   consistent root tuple (4 with both roots in {t0, t1}, and (t2, t2)). *)
Definition two_c (x : tri) : tri := match x with t2 => t2 | _ => t0 end.

Definition two_G : list (@edge (tri -> tri)) := [(0, 2, two_c); (1, 2, two_c)].
Definition two_F : list (@edge (tri -> tri)) := [] ++ [(0, 2, two_c)].

Theorem two_forest : spanning_forest [0; 1] two_G two_F.
Proof.
  split; [| split].
  - unfold two_F. apply f_out; [apply f_nil | simpl; auto | simpl; intuition lia].
  - intros x [<- | []]. left. reflexivity.
  - intros w Hw. simpl in Hw. simpl. intuition.
Qed.

Theorem two_has_section : exists s : nat -> tri, msection s two_G.
Proof.
  apply (root_set_criterion_graph [0; 1] two_G two_F two_forest).
  exists (fun _ => t2). intros x Hx. simpl in Hx.
  destruct Hx as [<- | [<- | []]]; reflexivity.
Qed.

Theorem two_count :
  length (consistent_roots tri_eq_dec t0 tri_all [0; 1] two_G two_F) = 5 /\
  length (sections_on tri_eq_dec t0 tri_all [0; 1] two_G two_F) = 5.
Proof. split; vm_compute; reflexivity. Qed.

Theorem two_count_is_sections :
  NoDup (sections_on tri_eq_dec t0 tri_all [0; 1] two_G two_F) /\
  (forall s, msection s two_G ->
     In (map s [0; 1; 0; 2]) (sections_on tri_eq_dec t0 tri_all [0; 1] two_G two_F)) /\
  length (sections_on tri_eq_dec t0 tri_all [0; 1] two_G two_F) = 5.
Proof.
  destruct (root_set_count tri_eq_dec t0 tri_all [0; 1] two_G two_F two_forest
              ltac:(repeat constructor; simpl; intuition lia) tri_nodup tri_full)
    as [_ [_ [Hnd [Hall [_ _]]]]].
  split; [exact Hnd | split; [exact Hall | vm_compute; reflexivity]].
Qed.

(* (4) A root set containing a strongly connected component: 0 -> 1 (copy) and 1 -> 0 (constant
   true) form a source component {0, 1}; 2 is a second source; 1 -> 3 (copy) and 2 -> 3
   (negation) meet at 3. Root set [0; 2]: exactly one of the four root tuples is consistent,
   (true, false), the back edge forcing 0 to true and the meeting at 3 forcing 2 to false. *)
Definition scc_G : list (@edge (bool -> bool)) :=
  [(0, 1, fun x => x); (1, 0, fun _ => true); (1, 3, fun x => x); (2, 3, negb)].
Definition scc_F : list (@edge (bool -> bool)) :=
  ([] ++ [(0, 1, fun x => x)]) ++ [(1, 3, fun x => x)].

Theorem scc_forest : spanning_forest [0; 2] scc_G scc_F.
Proof.
  split; [| split].
  - unfold scc_F. repeat apply f_out; try apply f_nil; simpl; intuition lia.
  - intros x Hx. unfold scc_F in Hx. simpl in Hx. unfold scc_G. simpl. tauto.
  - intros w Hw. simpl in Hw. simpl. intuition.
Qed.

Theorem scc_component :
  reach scc_G [0] 1 /\ reach scc_G [1] 0 /\
  ~ root_set [0] scc_G /\ ~ root_set [2] scc_G /\ root_set [0; 2] scc_G.
Proof.
  split; [| split; [| split; [| split]]].
  - apply (reach_step scc_G [0] 0 1 (fun x => x)); [apply reach_root; left; reflexivity | left; reflexivity].
  - apply (reach_step scc_G [1] 1 0 (fun _ => true)); [apply reach_root; left; reflexivity |].
    right. left. reflexivity.
  - intro H. assert (Hc : closed scc_G [0; 1; 3]).
    { intros u v f Hin Hu. simpl in Hin. destruct Hin as [E | [E | [E | [E | []]]]];
        injection E as Eu Ev _; subst; simpl in *; intuition lia. }
    pose proof (closed_reach scc_G [0] [0; 1; 3] Hc (fun r H => match H with
      | or_introl E => or_introl E | or_intror F => match F with end end) 2 (H 2 ltac:(simpl; tauto)))
      as H2. simpl in H2. intuition lia.
  - intro H. assert (Hc : closed scc_G [2; 3]).
    { intros u v f Hin Hu. simpl in Hin. destruct Hin as [E | [E | [E | [E | []]]]];
        injection E as Eu Ev _; subst; simpl in *; intuition lia. }
    pose proof (closed_reach scc_G [2] [2; 3] Hc (fun r H => match H with
      | or_introl E => or_introl E | or_intror F => match F with end end) 0 (H 0 ltac:(simpl; tauto)))
      as H0. simpl in H0. intuition lia.
  - apply root_set_iff_forest. exists scc_F. exact scc_forest.
Qed.

Theorem scc_consistent_roots :
  consistent_roots bool_dec false [true; false] [0; 2] scc_G scc_F = [[true; false]].
Proof. vm_compute. reflexivity. Qed.

Theorem scc_unique_section :
  (exists s : nat -> bool, msection s scc_G /\ s 0 = true /\ s 2 = false) /\
  forall s t : nat -> bool, msection s scc_G -> msection t scc_G ->
    forall w, In w [0; 2; 0; 1; 1; 3] -> s w = t w.
Proof.
  split.
  - destruct (proj2 (root_set_criterion_values [0; 2] scc_G scc_F scc_forest
                       (fun n => if Nat.eqb n 2 then false else true)))
      as [s [Hs Hr]].
    + intros x Hx. simpl in Hx. destruct Hx as [<- | [<- | [<- | [<- | []]]]]; reflexivity.
    + exists s. split; [exact Hs |]. split; [exact (Hr 0 (or_introl eq_refl)) |].
      exact (Hr 2 (or_intror (or_introl eq_refl))).
  - intros s t Hs Ht w Hw.
    destruct (root_set_bijection [0; 2] scc_G scc_F scc_forest) as [_ [_ Hu]].
    apply (Hu s t Hs Ht); [| exact Hw].
    assert (Root : forall q : nat -> bool, msection q scc_G -> q 0 = true /\ q 2 = false).
    { intros q Hq.
      pose proof (Hq (1, 0, fun _ => true) (or_intror (or_introl eq_refl))) as E1.
      pose proof (Hq (0, 1, fun x => x) (or_introl eq_refl)) as E0.
      pose proof (Hq (1, 3, fun x => x) (or_intror (or_intror (or_introl eq_refl)))) as E3.
      pose proof (Hq (2, 3, negb) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as E4.
      unfold msat in E0, E1, E3, E4. split; [congruence |].
      destruct (q 2); simpl in E4; congruence. }
    destruct (Root s Hs) as [Hs0 Hs2]. destruct (Root t Ht) as [Ht0 Ht2].
    intros r [<- | [<- | []]]; congruence.
Qed.
