(* RootlessNetworks.v: rootless propagation on an ARBITRARY finite invertible network, mechanized
   axiom-free. RootlessCycles.v settles one coherently oriented cycle (rootless_nf_exists_iff,
   rootless_unique_iff, rootless_unique_normal_form_iff) and records two corners: a self-loop is
   unique, and a registry with no incoming edge acts as a de facto root
   (rootless_orientation_matters). This file closes the general case of REGIME-AUDIT section 11
   (gap 2): several cycles, mixed orientation, sources feeding cycles, any finite edge list.

   Model. Exactly RootlessCycles.v: the fiber of every registry is the group G (the regular
   action), every edge (u, v, g) is a writer, firing it overwrites the target, s(v) := g * s(u)
   (fire1), a schedule is any finite list of edges of the network (fire), and a consistent state is
   a section (is_section, the fixed points of every writer). Nothing is assumed about the shape of
   the edge list.

   Graph notions (all on the directed edge list es, with verts es its registries).
   - reach es r w: a directed path r -> ... -> w (r upstream of w; reflexive).
   - linked es x y: x and y lie in the same weakly connected component (paths in either direction).
   - co_rooted es: every two linked registries have a common upstream registry. Equivalently
     (co_rooted_iff_roots) every weakly connected component has a registry upstream of all of it:
     its condensation has a single source component.
   - de_facto_root es r: no edge into r from another registry (only self-loops, if any), so r is
     never overwritten by anyone else. root_cover es: every component contains one.
   - authority_cover es: every component contains a de facto root upstream of all of it, that is,
     an authority root in the sense of CoordinatedCycles.v (authority_cover_iff: this is exactly
     co_rooted together with root_cover).

   Results (any group, any finite network).
   - net_reachable_iff / net_reachable_fair_iff (the reachable set, exactly): for a section sigma
     and an initial state t0, some schedule (equivalently some fair schedule) drives t0 to sigma
     on every registry iff every registry has an upstream registry, possibly itself, at which
     sigma and t0 already agree. net_nf_from_iff: a consistent state is reachable from t0 iff such
     a sigma exists. The key fact is net_origin: relative to any section, firing an edge copies
     the offset sigma(u)^-1 t(u) from u to v, so every value is an initial value transported from
     upstream.
   - net_nf_exists_iff (existence from every start): every initial state reaches a consistent
     state by a fair schedule iff the labeling is a coboundary (has_section, so H^1 = 0 on the
     whole underlying graph) and (co_rooted or |G| = 1).
   - net_unique_iff / net_unique_fair_iff (uniqueness): any two schedules (equivalently any two
     fair schedules) that reach consistent states from the same start reach the same one iff
     (has_section -> root_cover or |G| = 1). The free choice lives exactly in the components
     without a de facto root: the source components of their condensations are nontrivial.
   - net_unique_normal_form_iff (both): a unique normal form from every start, reached by a fair
     schedule, iff has_section and (authority_cover or |G| = 1). So a rootless network has a
     unique normal form exactly when each component already is an authority-rooted (coordinated)
     network in the sense of CoordinatedCycles.v, or the group is trivial.
   - The nontrivial-group forms (net_nf_exists_iff_nontrivial, net_unique_iff_nontrivial,
     net_unique_normal_form_iff_nontrivial) drop the "or |G| = 1" disjunct.
   - net_strong_iff (strongly connected networks with an edge between distinct registries):
     existence from every start iff has_section, and uniqueness iff (has_section -> |G| = 1).

   Recovered as corollaries (statements identical to RootlessCycles.v): cycle_nf_exists_recovered
   (rootless_nf_exists_iff), cycle_unique_recovered (rootless_unique_iff),
   cycle_unique_general_recovered (rootless_unique_iff_general),
   cycle_unique_normal_form_recovered (rootless_unique_normal_form_iff); the two corners
   selfloop_recovered (the self-loop registry is a de facto root) and
   orientation_matters_recovered (registry 0 of tri_mixed is an authority root), and the Z/2
   copy-back loop as an instance of the cycle corollary (copyback_recovered_net).

   Boundary cases and counterexamples (Z/2, all proved).
   - rootless_figure_eight: two coherently oriented cycles sharing a registry; every start
     reaches a consistent state, not unique.
   - rootless_mixed_square: the undirected 4-cycle 0 -> 1 <- 2 -> 3 <- 0 (mixed orientation,
     two sources): a coboundary with a unique normal form whenever one is reached, yet some start
     reaches no consistent state. So "coboundary implies existence from every start", true on one
     coherent cycle, is false on networks; the extra condition is co_rooted.
   - rootless_source_feeds_cycle: a source feeding the 2-cycle 1 <-> 2; a unique normal form from
     every start although the network contains a coherently oriented cycle and |G| = 2. So the
     single-cycle uniqueness iff (unique iff |G| = 1) does not extend to networks containing a
     cycle.
   - rootless_cycle_feeds_cycle: the 2-cycle 0 <-> 1 feeding the 2-cycle 2 <-> 3: existence from
     every start, not unique (only the source component of the condensation is free).
   - rootless_global_holonomy: the triangle 0 -> 1 -> 2 with 0 -> 2 labeled by the flip has an
     authority root and no directed cycle (every strongly connected component is a single
     registry), yet no consistent state: the existence obstruction is H^1 of the whole
     underlying graph, not holonomy inside strongly connected components.

   States are compared pointwise, so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.RootlessCycles.
Import ListNotations.

(* ============================================================
   Finite combinatorics on edge lists (no group structure).
   ============================================================ *)

Section Graphs.
  Context {G : Type}.

  Inductive reach (es : list (@edge G)) (r : nat) : nat -> Prop :=
  | reach_refl : reach es r r
  | reach_step : forall u v g, reach es r u -> In (u, v, g) es -> reach es r v.

  Lemma reach_edge : forall es u v g, In (u, v, g) es -> reach es u v.
  Proof. intros es u v g H. exact (reach_step es u u v g (reach_refl es u) H). Qed.

  Lemma reach_trans : forall es x y z, reach es x y -> reach es y z -> reach es x z.
  Proof.
    intros es x y z H1 H2. induction H2 as [| u v g H2 IH Hin]; [exact H1 |].
    exact (reach_step es x u v g IH Hin).
  Qed.

  Lemma reach_incl : forall es es' x y, incl es es' -> reach es x y -> reach es' x y.
  Proof.
    intros es es' x y Hi H. induction H as [| u v g H IH Hin]; [apply reach_refl |].
    exact (reach_step es' x u v g IH (Hi _ Hin)).
  Qed.

  Definition rev_edges (es : list (@edge G)) : list (@edge G) :=
    map (fun x : @edge G => let '(u, v, g) := x in (v, u, g)) es.

  Lemma in_rev_edges : forall es u v g, In (u, v, g) (rev_edges es) <-> In (v, u, g) es.
  Proof.
    intros es u v g. unfold rev_edges. rewrite in_map_iff. split.
    - intros [[[a b] h] [E H]]. simpl in E. injection E as E1 E2 E3. subst. exact H.
    - intro H. exists (v, u, g). split; [reflexivity | exact H].
  Qed.

  Lemma reach_rev : forall es x y, reach (rev_edges es) x y -> reach es y x.
  Proof.
    intros es x y H. induction H as [| u v g H IH Hin]; [apply reach_refl |].
    rewrite in_rev_edges in Hin. exact (reach_trans es v u x (reach_edge es v u g Hin) IH).
  Qed.

  Lemma reach_rev' : forall es x y, reach es y x -> reach (rev_edges es) x y.
  Proof.
    intros es x y H. induction H as [| u v g H IH Hin]; [apply reach_refl |].
    apply (reach_trans (rev_edges es) v u y); [| exact IH].
    apply (reach_edge (rev_edges es) v u g). rewrite in_rev_edges. exact Hin.
  Qed.

  (* Weak connectivity: paths that may use edges in either direction. *)
  Definition linked (es : list (@edge G)) (x y : nat) : Prop := reach (es ++ rev_edges es) x y.

  Lemma linked_refl : forall es x, linked es x x.
  Proof. intros es x. apply reach_refl. Qed.

  Lemma linked_of_reach : forall es x y, reach es x y -> linked es x y.
  Proof. intros es x y H. apply (reach_incl es); [apply incl_appl, incl_refl | exact H]. Qed.

  Lemma linked_trans : forall es x y z, linked es x y -> linked es y z -> linked es x z.
  Proof. intros es x y z. apply reach_trans. Qed.

  Lemma linked_sym : forall es x y, linked es x y -> linked es y x.
  Proof.
    intros es x y H. apply reach_rev' in H. apply (reach_incl (rev_edges (es ++ rev_edges es)));
      [| exact H].
    intros [[u v] g] Hin. rewrite in_rev_edges in Hin. apply in_app_or in Hin.
    apply in_or_app. destruct Hin as [Hin | Hin].
    - right. rewrite in_rev_edges. exact Hin.
    - left. rewrite in_rev_edges in Hin. exact Hin.
  Qed.

  Lemma linked_edge_fwd :
    forall es x u v g, In (u, v, g) es -> linked es x u -> linked es x v.
  Proof.
    intros es x u v g Hin H. apply (reach_step _ x u v g H). apply in_or_app. left. exact Hin.
  Qed.

  Lemma linked_edge_bwd :
    forall es x u v g, In (u, v, g) es -> linked es x v -> linked es x u.
  Proof.
    intros es x u v g Hin H. apply (reach_step _ x v u g H). apply in_or_app. right.
    rewrite in_rev_edges. exact Hin.
  Qed.

  Lemma linked_verts :
    forall es x y, linked es x y -> x = y \/ (In x (verts es) /\ In y (verts es)).
  Proof.
    intros es x y H. induction H as [| u v g H IH Hin]; [left; reflexivity |].
    assert (Huv : In u (verts es) /\ In v (verts es)).
    { apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      - exact (in_verts_edge es u v g Hin).
      - rewrite in_rev_edges in Hin. destruct (in_verts_edge es v u g Hin) as [A B]. split; assumption. }
    right. destruct IH as [<- | [Hx _]]; split; try exact (proj1 Huv); try exact Hx; exact (proj2 Huv).
  Qed.

  (* ----- decision helpers on lists ----- *)

  Lemma list_split :
    forall {A : Type} (P Q : A -> Prop) (l : list A),
      (forall x, In x l -> P x \/ Q x) -> (forall x, In x l -> P x) \/ (exists x, In x l /\ Q x).
  Proof.
    intros A P Q l. induction l as [| a l IH]; intro H; [left; intros x [] |].
    destruct (H a (or_introl eq_refl)) as [Pa | Qa];
      [| right; exists a; split; [left; reflexivity | exact Qa]].
    destruct IH as [Hall | [x [Hx Qx]]]; [intros x Hx; apply H; right; exact Hx | |].
    - left. intros x [<- | Hx]; [exact Pa | exact (Hall x Hx)].
    - right. exists x. split; [right; exact Hx | exact Qx].
  Qed.

  Lemma filter_prop :
    forall {A : Type} (P : A -> Prop) (l : list A), (forall x, P x \/ ~ P x) ->
      exists l', forall x, In x l' <-> In x l /\ ~ P x.
  Proof.
    intros A P l Hd. induction l as [| a l IH].
    - exists []. intro x. simpl. split; [intros [] | intros [[] _]].
    - destruct IH as [l' Hl']. destruct (Hd a) as [Pa | Na].
      + exists l'. intro x. rewrite Hl'. simpl. split.
        * intros [Hx Hn]. split; [right; exact Hx | exact Hn].
        * intros [[<- | Hx] Hn]; [contradiction | split; assumption].
      + exists (a :: l'). intro x. simpl. rewrite Hl'. split.
        * intros [<- | [Hx Hn]]; [split; [left; reflexivity | exact Na] |
                                   split; [right; exact Hx | exact Hn]].
        * intros [[<- | Hx] Hn]; [left; reflexivity | right; split; assumption].
  Qed.

  (* ----- a termination measure: registries of es outside a list ----- *)

  Definition memb (S : list nat) (w : nat) : bool := if in_dec Nat.eq_dec w S then true else false.

  Lemma memb_spec : forall S w, memb S w = true <-> In w S.
  Proof. intros S w. unfold memb. destruct (in_dec Nat.eq_dec w S); split; congruence. Qed.

  Definition outside (S l : list nat) : nat := length (filter (fun w => negb (memb S w)) l).

  Lemma filter_le :
    forall (f g : nat -> bool) l, (forall y, f y = true -> g y = true) ->
      length (filter f l) <= length (filter g l).
  Proof.
    intros f g l H. induction l as [| a l IH]; simpl; [lia |].
    destruct (f a) eqn:Ef; [rewrite (H a Ef); simpl; lia |].
    destruct (g a); simpl; lia.
  Qed.

  Lemma filter_lt :
    forall (f g : nat -> bool) l x, (forall y, f y = true -> g y = true) -> In x l ->
      f x = false -> g x = true -> length (filter f l) < length (filter g l).
  Proof.
    intros f g l x H Hx Ef Eg. induction l as [| a l IH]; [destruct Hx |].
    destruct Hx as [-> | Hx].
    - simpl. rewrite Ef, Eg. simpl. pose proof (filter_le f g l H). lia.
    - simpl. specialize (IH Hx). destruct (f a) eqn:Fa; [rewrite (H a Fa); simpl; lia |].
      destruct (g a); simpl; lia.
  Qed.

  Lemma outside_lt :
    forall v S l, In v l -> ~ In v S -> outside (v :: S) l < outside S l.
  Proof.
    intros v S l Hv HS. unfold outside. apply (filter_lt _ _ l v).
    - intros y Hy. destruct (memb S y) eqn:E; [| reflexivity].
      apply memb_spec in E. assert (E' : memb (v :: S) y = true) by (apply memb_spec; right; exact E).
      rewrite E' in Hy. discriminate.
    - exact Hv.
    - assert (E : memb (v :: S) v = true) by (apply memb_spec; left; reflexivity). rewrite E.
      reflexivity.
    - destruct (memb S v) eqn:E; [apply memb_spec in E; contradiction | reflexivity].
  Qed.

  Lemma cross_or_closed :
    forall (es : list (@edge G)) S,
      (exists u v g, In (u, v, g) es /\ In u S /\ ~ In v S) \/
      (forall u v g, In (u, v, g) es -> In u S -> In v S).
  Proof.
    intros es S. induction es as [| [[u v] g] es IH]; [right; intros u v g [] |].
    destruct (in_dec Nat.eq_dec u S) as [Hu | Hu]; [destruct (in_dec Nat.eq_dec v S) as [Hv | Hv] |].
    - destruct IH as [[a [b [h [Hin [Ha Hb]]]]] | Hc].
      + left. exists a, b, h. split; [right; exact Hin | split; assumption].
      + right. intros a b h [E | Hin] Ha; [injection E as <- <- <-; exact Hv | exact (Hc a b h Hin Ha)].
    - left. exists u, v, g. split; [left; reflexivity | split; assumption].
    - destruct IH as [[a [b [h [Hin [Ha Hb]]]]] | Hc].
      + left. exists a, b, h. split; [right; exact Hin | split; assumption].
      + right. intros a b h [E | Hin] Ha;
          [injection E as <- <- <-; contradiction | exact (Hc a b h Hin Ha)].
  Qed.

  Lemma closed_reach :
    forall (es : list (@edge G)) S, (forall u v g, In (u, v, g) es -> In u S -> In v S) ->
      forall r w, reach es r w -> In r S -> In w S.
  Proof.
    intros es S Hc r w H Hr. induction H as [| u v g H IH Hin]; [exact Hr |].
    exact (Hc u v g Hin IH).
  Qed.

  (* The registries reachable from a finite list form a finite list: reachability is decidable. *)
  Lemma closure :
    forall (es : list (@edge G)) S, exists T, forall w, In w T <-> exists r, In r S /\ reach es r w.
  Proof.
    intro es.
    assert (Closed : forall S, (forall u v g, In (u, v, g) es -> In u S -> In v S) ->
              exists T, forall w, In w T <-> exists r, In r S /\ reach es r w).
    { intros S Hc. exists S. intro w. split.
      - intro H. exists w. split; [exact H | apply reach_refl].
      - intros [r [Hr Hw]]. exact (closed_reach es S Hc r w Hw Hr). }
    assert (Main : forall n S, outside S (verts es) <= n ->
              exists T, forall w, In w T <-> exists r, In r S /\ reach es r w).
    { induction n as [| n IH]; intros S Hn;
        destruct (cross_or_closed es S) as [[u [v [g [Hin [Hu Hv]]]]] | Hc];
        try exact (Closed S Hc);
        pose proof (outside_lt v S (verts es) (proj2 (in_verts_edge es u v g Hin)) Hv) as Hlt;
        [lia |].
      destruct (IH (v :: S)) as [T HT]; [lia |].
      exists T. intro w. rewrite HT. split.
      - intros [r [[<- | Hr] Hw]].
        + exists u. split; [exact Hu | exact (reach_trans es u v w (reach_edge es u v g Hin) Hw)].
        + exists r. split; [exact Hr | exact Hw].
      - intros [r [Hr Hw]]. exists r. split; [right; exact Hr | exact Hw]. }
    intro S. exact (Main _ S (le_n _)).
  Qed.

  Lemma reach_dec : forall (es : list (@edge G)) x y, reach es x y \/ ~ reach es x y.
  Proof.
    intros es x y. destruct (closure es [x]) as [T HT].
    destruct (in_dec Nat.eq_dec y T) as [Hy | Hy].
    - left. destruct (proj1 (HT y) Hy) as [r [[<- | []] Hr]]. exact Hr.
    - right. intro H. apply Hy. apply HT. exists x. split; [left; reflexivity | exact H].
  Qed.

  Lemma anc_list : forall (es : list (@edge G)) x, exists A, forall r, In r A <-> reach es r x.
  Proof.
    intros es x. destruct (closure (rev_edges es) [x]) as [T HT]. exists T. intro r. rewrite HT.
    split.
    - intros [y [[<- | []] Hy]]. exact (reach_rev es x r Hy).
    - intro H. exists x. split; [left; reflexivity | exact (reach_rev' es x r H)].
  Qed.

  Lemma comp_list : forall (es : list (@edge G)) x, exists K, forall w, In w K <-> linked es x w.
  Proof.
    intros es x. destruct (closure (es ++ rev_edges es) [x]) as [T HT]. exists T. intro w.
    rewrite HT. split.
    - intros [y [[<- | []] Hy]]. exact Hy.
    - intro H. exists x. split; [left; reflexivity | exact H].
  Qed.

  (* ----- the structural conditions ----- *)

  (* Every two weakly linked registries have a common upstream registry. *)
  Definition co_rooted (es : list (@edge G)) : Prop :=
    forall x y, linked es x y -> exists r, reach es r x /\ reach es r y.

  (* No edge into r from another registry. *)
  Definition de_facto_root (es : list (@edge G)) (r : nat) : Prop :=
    forall u g, In (u, r, g) es -> u = r.

  (* Every weakly connected component contains a de facto root. *)
  Definition root_cover (es : list (@edge G)) : Prop :=
    forall x, In x (verts es) -> exists r, linked es x r /\ de_facto_root es r.

  (* Every weakly connected component contains a de facto root upstream of all of it. *)
  Definition authority_cover (es : list (@edge G)) : Prop :=
    forall x, In x (verts es) -> exists r, de_facto_root es r /\ forall y, linked es x y -> reach es r y.

  Definition strongly_connected (es : list (@edge G)) : Prop :=
    forall x y, In x (verts es) -> In y (verts es) -> reach es x y.

  Lemma common_dec :
    forall (es : list (@edge G)) x y,
      (exists r, reach es r x /\ reach es r y) \/ ~ (exists r, reach es r x /\ reach es r y).
  Proof.
    intros es x y. destruct (anc_list es x) as [A HA].
    destruct (list_split (fun r => ~ reach es r y) (fun r => reach es r y) A
                (fun r _ => match reach_dec es r y with
                            | or_introl H => or_intror H | or_intror H => or_introl H end))
      as [Hn | [r [Hr Hry]]].
    - right. intros [r [Hrx Hry]]. exact (Hn r (proj2 (HA r) Hrx) Hry).
    - left. exists r. split; [apply HA; exact Hr | exact Hry].
  Qed.

  Lemma co_rooted_or_witness :
    forall (es : list (@edge G)),
      co_rooted es \/ exists x y, linked es x y /\ ~ (exists r, reach es r x /\ reach es r y).
  Proof.
    intro es.
    assert (Hx : forall x, In x (verts es) ->
                   (forall y, linked es x y -> exists r, reach es r x /\ reach es r y) \/
                   (exists y, linked es x y /\ ~ (exists r, reach es r x /\ reach es r y))).
    { intros x _. destruct (comp_list es x) as [K HK].
      destruct (list_split (fun y => exists r, reach es r x /\ reach es r y)
                  (fun y => ~ (exists r, reach es r x /\ reach es r y)) K
                  (fun y _ => common_dec es x y)) as [Hall | [y [Hy Hn]]].
      - left. intros y Hy. apply Hall. apply HK. exact Hy.
      - right. exists y. split; [apply HK; exact Hy | exact Hn]. }
    destruct (list_split _ _ (verts es) Hx) as [Hall | [x [_ [y [Hxy Hn]]]]].
    - left. intros x y Hxy. destruct (linked_verts es x y Hxy) as [<- | [Hxv _]].
      + exists x. split; apply reach_refl.
      + exact (Hall x Hxv y Hxy).
    - right. exists x, y. split; assumption.
  Qed.

  Lemma dfr_or_proper :
    forall (es : list (@edge G)) r, de_facto_root es r \/ exists u g, In (u, r, g) es /\ u <> r.
  Proof.
    intros es r. induction es as [| [[u v] g] es IH]; [left; intros u g [] |].
    destruct IH as [Hd | [u' [g' [Hin Hne]]]];
      [| right; exists u', g'; split; [right; exact Hin | exact Hne]].
    destruct (Nat.eq_dec v r) as [-> | Hvr].
    - destruct (Nat.eq_dec u r) as [-> | Hur].
      + left. intros a h [E | Hin]; [congruence | exact (Hd a h Hin)].
      + right. exists u, g. split; [left; reflexivity | exact Hur].
    - left. intros a h [E | Hin]; [congruence | exact (Hd a h Hin)].
  Qed.

  Lemma root_cover_or_witness :
    forall (es : list (@edge G)),
      root_cover es \/
      exists x, In x (verts es) /\ forall y, linked es x y -> exists u g, In (u, y, g) es /\ u <> y.
  Proof.
    intro es.
    assert (Hx : forall x, In x (verts es) ->
                   (exists r, linked es x r /\ de_facto_root es r) \/
                   (forall y, linked es x y -> exists u g, In (u, y, g) es /\ u <> y)).
    { intros x _. destruct (comp_list es x) as [K HK].
      destruct (list_split (fun y => exists u g, In (u, y, g) es /\ u <> y)
                  (fun y => de_facto_root es y) K
                  (fun y _ => match dfr_or_proper es y with
                              | or_introl H => or_intror H | or_intror H => or_introl H end))
        as [Hall | [r [Hr Hroot]]].
      - right. intros y Hy. apply Hall. apply HK. exact Hy.
      - left. exists r. split; [apply HK; exact Hr | exact Hroot]. }
    destruct (list_split _ _ (verts es) Hx) as [Hall | [x [Hxv Hw]]].
    - left. exact Hall.
    - right. exists x. split; assumption.
  Qed.

  Lemma reach_to_dfr : forall (es : list (@edge G)) z w, reach es z w -> de_facto_root es w -> z = w.
  Proof.
    intros es z w H. induction H as [| u v g H IH Hin]; intro Hr; [reflexivity |].
    pose proof (Hr u g Hin) as E. subst u. exact (IH Hr).
  Qed.

  (* Every two-sided component has a registry upstream of all of it, given co_rooted. *)
  Lemma co_rooted_root :
    forall (es : list (@edge G)), co_rooted es ->
      forall x, exists r, linked es x r /\ forall y, linked es x y -> reach es r y.
  Proof.
    intros es Hc x. destruct (comp_list es x) as [K HK].
    assert (L : forall L, (forall y, In y L -> linked es x y) ->
                  exists r, linked es x r /\ forall y, In y L -> reach es r y).
    { induction L as [| y L IH]; intro HL.
      - exists x. split; [apply linked_refl | intros y []].
      - destruct IH as [r [Hxr Hr]]; [intros z Hz; apply HL; right; exact Hz |].
        destruct (Hc r y) as [z [Hzr Hzy]].
        + apply (linked_trans es r x y); [apply linked_sym; exact Hxr | apply HL; left; reflexivity].
        + exists z. split.
          * apply (linked_trans es x r z Hxr). apply linked_sym. apply linked_of_reach. exact Hzr.
          * intros w [<- | Hw]; [exact Hzy | exact (reach_trans es z r w Hzr (Hr w Hw))]. }
    destruct (L K (fun y Hy => proj1 (HK y) Hy)) as [r [Hxr Hr]].
    exists r. split; [exact Hxr |]. intros y Hy. apply Hr. apply HK. exact Hy.
  Qed.

  (* co_rooted says exactly that every weakly connected component has a registry upstream of all of
     it (its condensation has a single source component). *)
  Theorem co_rooted_iff_roots :
    forall (es : list (@edge G)),
      co_rooted es <-> forall x, exists r, forall y, linked es x y -> reach es r y.
  Proof.
    intro es. split.
    - intros Hc x. destruct (co_rooted_root es Hc x) as [r [_ Hr]]. exists r. exact Hr.
    - intros H x y Hxy. destruct (H x) as [r Hr]. exists r.
      split; [apply Hr; apply linked_refl | exact (Hr y Hxy)].
  Qed.

  Theorem authority_cover_iff :
    forall (es : list (@edge G)), authority_cover es <-> co_rooted es /\ root_cover es.
  Proof.
    intro es. split.
    - intro Ha. split.
      + intros x y Hxy. destruct (linked_verts es x y Hxy) as [<- | [Hx _]].
        * exists x. split; apply reach_refl.
        * destruct (Ha x Hx) as [r [_ Hr]]. exists r.
          split; [apply Hr; apply linked_refl | exact (Hr y Hxy)].
      + intros x Hx. destruct (Ha x Hx) as [r [Hroot Hr]]. exists r. split; [| exact Hroot].
        apply linked_sym. apply linked_of_reach. apply Hr. apply linked_refl.
    - intros [Hc Hrc] x Hx. destruct (Hrc x Hx) as [r [Hxr Hroot]]. exists r.
      split; [exact Hroot |]. intros y Hy.
      destruct (Hc r y) as [z [Hzr Hzy]].
      + apply (linked_trans es r x y); [apply linked_sym; exact Hxr | exact Hy].
      + rewrite <- (reach_to_dfr es z r Hzr Hroot). exact Hzy.
  Qed.

  (* Structural sufficient conditions, used by the instances. *)
  Lemma co_rooted_of_root :
    forall (es : list (@edge G)) r, (forall y, In y (verts es) -> reach es r y) -> co_rooted es.
  Proof.
    intros es r Hr x y Hxy. destruct (linked_verts es x y Hxy) as [<- | [Hx Hy]].
    - exists x. split; apply reach_refl.
    - exists r. split; [exact (Hr x Hx) | exact (Hr y Hy)].
  Qed.

  Lemma authority_of_root :
    forall (es : list (@edge G)) r, de_facto_root es r ->
      (forall y, In y (verts es) -> reach es r y) -> authority_cover es.
  Proof.
    intros es r Hroot Hr x Hx. exists r. split; [exact Hroot |]. intros y Hy.
    destruct (linked_verts es x y Hy) as [<- | [_ Hy']]; [exact (Hr x Hx) | exact (Hr y Hy')].
  Qed.

  Lemma proper_in :
    forall (es : list (@edge G)) x y, reach es x y -> x <> y ->
      exists u g, In (u, y, g) es /\ u <> y.
  Proof.
    intros es x y H. induction H as [| u v g H IH Hin]; intro Hne; [contradiction Hne; reflexivity |].
    destruct (Nat.eq_dec u v) as [-> | Huv]; [exact (IH Hne) | exists u, g; split; assumption].
  Qed.

  Lemma sc_co_rooted : forall (es : list (@edge G)), strongly_connected es -> co_rooted es.
  Proof.
    intros es Hsc x y Hxy. destruct (linked_verts es x y Hxy) as [<- | [Hx Hy]].
    - exists x. split; apply reach_refl.
    - exists x. split; [apply reach_refl | exact (Hsc x y Hx Hy)].
  Qed.

  Lemma sc_not_root_cover :
    forall (es : list (@edge G)), strongly_connected es ->
      forall u v g, In (u, v, g) es -> u <> v -> ~ root_cover es.
  Proof.
    intros es Hsc u v g Hin Huv Hrc. destruct (in_verts_edge es u v g Hin) as [Hu Hv].
    destruct (Hrc u Hu) as [r [Hur Hroot]].
    assert (Hr : In r (verts es)) by (destruct (linked_verts es u r Hur) as [<- | [_ H]]; assumption).
    destruct (Nat.eq_dec u r) as [<- | Hne].
    - destruct (proper_in es v u (Hsc v u Hv Hu) (fun E => Huv (eq_sym E)))
        as [u' [g' [Hin' Hne']]].
      exact (Hne' (Hroot u' g' Hin')).
    - destruct (proper_in es u r (Hsc u r Hu Hr) Hne) as [u' [g' [Hin' Hne']]].
      exact (Hne' (Hroot u' g' Hin')).
  Qed.

  (* A minimal dominating subset of a finite list: every element of L is downstream of X, and no
     element of X is downstream of another. *)
  Lemma min_dom :
    forall (es : list (@edge G)) L, exists X,
      incl X L /\ (forall v, In v L -> exists r, In r X /\ reach es r v) /\
      (forall w r, In w X -> In r X -> r <> w -> ~ reach es r w).
  Proof.
    intro es. induction L as [| v L IH].
    - exists []. split; [intros x [] |]. split; [intros v [] | intros w r []].
    - destruct IH as [X [HXL [Hdom Hind]]].
      destruct (list_split (fun r => ~ reach es r v) (fun r => reach es r v) X
                  (fun r _ => match reach_dec es r v with
                              | or_introl H => or_intror H | or_intror H => or_introl H end))
        as [Hnone | [r0 [Hr0 Hr0v]]].
      + destruct (filter_prop (fun w => reach es v w) X (fun w => reach_dec es v w)) as [Xf HXf].
        exists (v :: Xf). split; [| split].
        * intros w [<- | Hw]; [left; reflexivity | right; exact (HXL w (proj1 (proj1 (HXf w) Hw)))].
        * intros u [<- | Hu].
          -- exists v. split; [left; reflexivity | apply reach_refl].
          -- destruct (Hdom u Hu) as [r [Hr Hru]]. destruct (reach_dec es v r) as [Hvr | Hvr].
             ++ exists v. split; [left; reflexivity | exact (reach_trans es v r u Hvr Hru)].
             ++ exists r. split; [right; apply HXf; split; assumption | exact Hru].
        * intros w r [<- | Hw] [<- | Hr] Hne.
          -- contradiction Hne. reflexivity.
          -- exact (Hnone r (proj1 (proj1 (HXf r) Hr))).
          -- exact (proj2 (proj1 (HXf w) Hw)).
          -- exact (Hind w r (proj1 (proj1 (HXf w) Hw)) (proj1 (proj1 (HXf r) Hr)) Hne).
      + exists X. split; [intros w Hw; right; exact (HXL w Hw) |]. split; [| exact Hind].
        intros u [<- | Hu]; [exists r0; split; assumption | exact (Hdom u Hu)].
  Qed.

  (* Seeds: one upstream witness per registry of a list, collected into a list. *)
  Lemma seeds :
    forall (es : list (@edge G)) (P : nat -> Prop) L,
      (forall w, In w L -> exists r, reach es r w /\ P r) ->
      exists S, (forall r, In r S -> P r) /\ forall w, In w L -> exists r, In r S /\ reach es r w.
  Proof.
    intros es P L. induction L as [| a L IH]; intro H.
    - exists []. split; [intros r [] | intros w []].
    - destruct (H a (or_introl eq_refl)) as [r [Hr Pr]].
      destruct IH as [S [HS HL]]; [intros w Hw; apply H; right; exact Hw |].
      exists (r :: S). split.
      + intros r' [<- | Hr']; [exact Pr | exact (HS r' Hr')].
      + intros w [<- | Hw]; [exists r; split; [left; reflexivity | exact Hr] |].
        destruct (HL w Hw) as [r' [Hr' Hw']]. exists r'. split; [right; exact Hr' | exact Hw'].
  Qed.

  Lemma reach_mono :
    forall (es : list (@edge G)), (forall u v g, In (u, v, g) es -> u < v) ->
      forall x y, reach es x y -> x <= y.
  Proof.
    intros es Hm x y H. induction H as [| u v g H IH Hin]; [lia |].
    pose proof (Hm u v g Hin). lia.
  Qed.
End Graphs.

(* ============================================================
   Rootless propagation on any network.
   ============================================================ *)

Section Networks.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  (* ----- small group facts ----- *)

  Lemma lcancel : forall g a b, op g a = op g b -> a = b.
  Proof using assoc id_l inv_l.
    intros g a b H.
    transitivity (op (inv g) (op g a)); [rewrite assoc, inv_l, id_l; reflexivity |].
    rewrite H, assoc, inv_l, id_l. reflexivity.
  Qed.

  Lemma rcancel : forall a b c, op a c = op b c -> a = b.
  Proof using assoc id_r inv_r.
    intros a b c H.
    transitivity (op (op a c) (inv c)); [rewrite <- assoc, inv_r, id_r; reflexivity |].
    rewrite H, <- assoc, inv_r, id_r. reflexivity.
  Qed.

  Lemma tr_back : forall a b, op a (op (inv a) b) = b.
  Proof using assoc id_l inv_r. intros a b. rewrite assoc, inv_r, id_l. reflexivity. Qed.

  Lemma off_edge : forall g a b x, op g a = b -> op (inv b) (op g x) = op (inv a) x.
  Proof using assoc id_l inv_r inv_l.
    intros g a b x H.
    assert (Hx : op g x = op b (op (inv a) x)).
    { rewrite <- H, <- assoc, tr_back. reflexivity. }
    rewrite Hx, assoc, inv_l, id_l. reflexivity.
  Qed.

  Lemma off_e : forall a b, op (inv a) b = e -> b = a.
  Proof using assoc id_l id_r inv_r.
    intros a b H. rewrite <- (tr_back a b), H, id_r. reflexivity.
  Qed.

  (* ----- sections ----- *)

  Lemma section_verts :
    forall es s t, is_section op s es -> (forall w, In w (verts es) -> t w = s w) ->
      is_section op t es.
  Proof.
    intros es s t Hs Ht [[u v] g] Hin. destruct (in_verts_edge es u v g Hin) as [Hu Hv].
    unfold sat. rewrite (Ht u Hu), (Ht v Hv). exact (Hs _ Hin).
  Qed.

  Lemma translate_section :
    forall es s c, is_section op s es -> is_section op (fun w => op (s w) c) es.
  Proof using assoc.
    intros es s c Hs [[u v] g] Hin. unfold sat. rewrite assoc.
    pose proof (Hs _ Hin) as E. unfold sat in E. rewrite E. reflexivity.
  Qed.

  Lemma piece_section :
    forall es s K a b, is_section op s es ->
      (forall u v g, In (u, v, g) es -> (In u K <-> In v K)) ->
      is_section op (fun w => if in_dec Nat.eq_dec w K then op (s w) b else op (s w) a) es.
  Proof using assoc.
    intros es s K a b Hs HK [[u v] g] Hin. unfold sat.
    pose proof (Hs _ Hin) as E. unfold sat in E. pose proof (HK u v g Hin) as Huv.
    destruct (in_dec Nat.eq_dec u K) as [Hu | Hu]; destruct (in_dec Nat.eq_dec v K) as [Hv | Hv].
    - rewrite assoc, E. reflexivity.
    - exfalso. exact (Hv (proj1 Huv Hu)).
    - exfalso. exact (Hu (proj2 Huv Hv)).
    - rewrite assoc, E. reflexivity.
  Qed.

  (* Two sections on one weakly connected component differ by one right constant. *)
  Lemma linked_shift :
    forall es s sg c x y, is_section op s es -> is_section op sg es ->
      sg x = op (s x) c -> linked es x y -> sg y = op (s y) c.
  Proof using assoc id_l inv_l.
    intros es s sg c x y Hs Hsg Hx H. induction H as [| u v g H IH Hin]; [exact Hx |].
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - pose proof (Hs _ Hin) as E1. pose proof (Hsg _ Hin) as E2. unfold sat in E1, E2.
      rewrite <- E1, <- E2, IH, assoc. reflexivity.
    - rewrite in_rev_edges in Hin.
      pose proof (Hs _ Hin) as E1. pose proof (Hsg _ Hin) as E2. unfold sat in E1, E2.
      apply (lcancel g). rewrite E2, IH, <- E1, assoc. reflexivity.
  Qed.

  (* ----- schedules ----- *)

  Lemma stable_from :
    forall es s p t, is_section op s es -> incl p es -> (forall k, t k = s k) ->
      forall k, fire op p t k = s k.
  Proof.
    intros es s p. induction p as [| x p IH]; intros t Hs Hp Ht k; [exact (Ht k) |].
    rewrite fire_cons. apply IH; [exact Hs | intros y Hy; apply Hp; right; exact Hy |].
    intro z. destruct x as [[u v] g]. rewrite fire1_eq.
    destruct (Nat.eq_dec z v) as [-> | _]; [| exact (Ht z)].
    rewrite (Ht u). exact (Hs _ (Hp _ (or_introl eq_refl))).
  Qed.

  Lemma extend_fair :
    forall es p t, incl p es -> is_section op (fire op p t) es ->
      incl (p ++ es) es /\ incl es (p ++ es) /\
      (forall k, fire op (p ++ es) t k = fire op p t k) /\ is_section op (fire op (p ++ es) t) es.
  Proof.
    intros es p t Hp Hs.
    assert (E : forall k, fire op (p ++ es) t k = fire op p t k).
    { intro k. rewrite fire_app. apply (stable_from es); [exact Hs | apply incl_refl | reflexivity]. }
    split; [intros x Hx; apply in_app_or in Hx; destruct Hx; [apply Hp |]; assumption |].
    split; [apply incl_appr, incl_refl |]. split; [exact E |].
    apply (section_verts es (fire op p t)); [exact Hs | intros w _; apply E].
  Qed.

  Lemma untargeted :
    forall es p t w, ~ In w (verts es) -> incl p es -> fire op p t w = t w.
  Proof.
    intros es p t w Hw Hp. apply fire_untargeted. intros u v g Hin E. subst v.
    exact (Hw (proj2 (in_verts_edge es u w g (Hp _ Hin)))).
  Qed.

  (* A registry that is never overwritten by another registry keeps its value, once self-loops
     carry the identity (which every section forces). *)
  Lemma dfr_stable :
    forall es r, de_facto_root es r -> (forall g, In (r, r, g) es -> g = e) ->
      forall p, incl p es -> forall t, fire op p t r = t r.
  Proof using id_l.
    intros es r Hroot Hloop p. induction p as [| x p IH]; intros Hp t; [reflexivity |].
    rewrite fire_cons, IH by (intros y Hy; apply Hp; right; exact Hy).
    destruct x as [[u v] g]. rewrite fire1_eq.
    destruct (Nat.eq_dec r v) as [-> | _]; [| reflexivity].
    pose proof (Hp _ (or_introl eq_refl)) as Hin. pose proof (Hroot u g Hin) as Eu. subst u.
    rewrite (Hloop g Hin), id_l. reflexivity.
  Qed.

  Lemma selfloop_e : forall es s r g, is_section op s es -> In (r, r, g) es -> g = e.
  Proof using assoc id_l id_r inv_r.
    intros es s r g Hs Hin. pose proof (Hs _ Hin) as E. unfold sat in E.
    apply (rcancel g e (s r)). rewrite id_l. exact E.
  Qed.

  (* ----- flooding from a seed list ----- *)

  Lemma flood :
    forall es sg, is_section op sg es -> forall S t, (forall r, In r S -> t r = sg r) ->
      exists p, incl p es /\
        (forall w, (exists r, In r S /\ reach es r w) -> fire op p t w = sg w) /\
        (forall w, fire op p t w = t w \/ exists r, In r S /\ reach es r w).
  Proof.
    intros es sg Hsg.
    assert (Closed : forall S t, (forall u v g, In (u, v, g) es -> In u S -> In v S) ->
              (forall r, In r S -> t r = sg r) ->
              exists p, incl p es /\
                (forall w, (exists r, In r S /\ reach es r w) -> fire op p t w = sg w) /\
                (forall w, fire op p t w = t w \/ exists r, In r S /\ reach es r w)).
    { intros S t Hc Ht. exists []. split; [intros x [] |]. split.
      - intros w [r [Hr Hw]]. exact (Ht w (closed_reach es S Hc r w Hw Hr)).
      - intro w. left. reflexivity. }
    assert (Main : forall n S t, outside S (verts es) <= n -> (forall r, In r S -> t r = sg r) ->
              exists p, incl p es /\
                (forall w, (exists r, In r S /\ reach es r w) -> fire op p t w = sg w) /\
                (forall w, fire op p t w = t w \/ exists r, In r S /\ reach es r w)).
    { induction n as [| n IH]; intros S t Hn Ht;
        destruct (cross_or_closed es S) as [[u [v [g [Hin [Hu Hv]]]]] | Hc];
        try exact (Closed S t Hc Ht);
        pose proof (outside_lt v S (verts es) (proj2 (in_verts_edge es u v g Hin)) Hv) as Hlt;
        [lia |].
      assert (Ht' : forall r, In r (v :: S) -> fire1 op t (u, v, g) r = sg r).
      { intros r Hr. rewrite fire1_eq. destruct (Nat.eq_dec r v) as [-> | Hne].
        - rewrite (Ht u Hu). exact (Hsg _ Hin).
        - destruct Hr as [<- | Hr]; [contradiction Hne; reflexivity | exact (Ht r Hr)]. }
      destruct (IH (v :: S) (fire1 op t (u, v, g))) as [p [Hp [H1 H2]]]; [lia | exact Ht' |].
      exists ((u, v, g) :: p).
      split; [intros x [<- | Hx]; [exact Hin | exact (Hp x Hx)] |]. split.
      - intros w [r [Hr Hw]]. rewrite fire_cons. apply H1. exists r. split; [right; exact Hr | exact Hw].
      - intro w. rewrite fire_cons. destruct (H2 w) as [E | [r [[<- | Hr] Hw]]].
        + rewrite E, fire1_eq. destruct (Nat.eq_dec w v) as [-> | _]; [| left; reflexivity].
          right. exists u. split; [exact Hu | exact (reach_edge es u v g Hin)].
        + right. exists u. split; [exact Hu | exact (reach_trans es u v w (reach_edge es u v g Hin) Hw)].
        + right. exists r. split; assumption. }
    intros S t Ht. exact (Main _ S t (le_n _) Ht).
  Qed.

  (* ----- the reachable set, exactly ----- *)

  (* Relative to a section sg, the offset sg(w)^-1 t(w) only ever moves downstream, unchanged:
     every value is an initial value transported along a path. *)
  Theorem net_origin :
    forall es sg, is_section op sg es -> forall p, incl p es -> forall t w,
      exists r, reach es r w /\ op (inv (sg r)) (t r) = op (inv (sg w)) (fire op p t w).
  Proof using assoc id_l inv_r inv_l.
    intros es sg Hsg p. induction p as [| x p IH]; intros Hp t w.
    - exists w. split; [apply reach_refl | reflexivity].
    - destruct (IH (fun y Hy => Hp y (or_intror Hy)) (fire1 op t x) w) as [r [Hr E]].
      rewrite fire_cons, <- E. destruct x as [[u v] g].
      pose proof (Hp _ (or_introl eq_refl)) as Hin. rewrite fire1_eq.
      destruct (Nat.eq_dec r v) as [-> | Hne].
      + exists u. split; [exact (reach_trans es u v w (reach_edge es u v g Hin) Hr) |].
        symmetry. apply off_edge. exact (Hsg _ Hin).
      + exists r. split; [exact Hr | reflexivity].
  Qed.

  Theorem net_reachable_iff :
    forall es sg t0, is_section op sg es ->
      ((exists p, incl p es /\ forall w, In w (verts es) -> fire op p t0 w = sg w) <->
       (forall w, In w (verts es) -> exists r, reach es r w /\ sg r = t0 r)).
  Proof using assoc id_l id_r inv_r inv_l.
    intros es sg t0 Hsg. split.
    - intros [p [Hp Ew]] w Hw. destruct (net_origin es sg Hsg p Hp t0 w) as [r [Hr E]].
      exists r. split; [exact Hr |]. rewrite (Ew w Hw), inv_l in E. symmetry. exact (off_e _ _ E).
    - intro H. destruct (seeds es (fun r => sg r = t0 r) (verts es) H) as [S [HS Hcov]].
      destruct (flood es sg Hsg S t0 (fun r Hr => eq_sym (HS r Hr))) as [p [Hp [H1 _]]].
      exists p. split; [exact Hp |]. intros w Hw. apply H1. exact (Hcov w Hw).
  Qed.

  Theorem net_reachable_fair_iff :
    forall es sg t0, is_section op sg es ->
      ((exists p, incl p es /\ incl es p /\ forall w, In w (verts es) -> fire op p t0 w = sg w) <->
       (forall w, In w (verts es) -> exists r, reach es r w /\ sg r = t0 r)).
  Proof using assoc id_l id_r inv_r inv_l.
    intros es sg t0 Hsg. rewrite <- (net_reachable_iff es sg t0 Hsg). split.
    - intros [p [Hp [_ E]]]. exists p. split; assumption.
    - intros [p [Hp E]].
      destruct (extend_fair es p t0 Hp (section_verts es sg _ Hsg E)) as [A [B [C _]]].
      exists (p ++ es). split; [exact A | split; [exact B |]].
      intros w Hw. rewrite C. exact (E w Hw).
  Qed.

  (* A consistent state is reachable from t0 (by a fair schedule) iff some section agrees with t0
     somewhere upstream of every registry. *)
  Theorem net_nf_from_iff :
    forall es t0,
      (exists p, incl p es /\ incl es p /\ is_section op (fire op p t0) es) <->
      (exists sg, is_section op sg es /\
                  forall w, In w (verts es) -> exists r, reach es r w /\ sg r = t0 r).
  Proof using assoc id_l id_r inv_r inv_l.
    intros es t0. split.
    - intros [p [Hp [_ Hs]]]. exists (fire op p t0). split; [exact Hs |].
      apply (net_reachable_iff es (fire op p t0) t0 Hs). exists p. split; [exact Hp | reflexivity].
    - intros [sg [Hsg H]].
      destruct (proj2 (net_reachable_fair_iff es sg t0 Hsg) H) as [p [Hp [Hf E]]].
      exists p. split; [exact Hp | split; [exact Hf |]].
      exact (section_verts es sg _ Hsg E).
  Qed.

  (* ----- existence from every start ----- *)

  Lemma inclosed_stable :
    forall es s a (X : nat -> Prop), is_section op s es ->
      (forall u v g, In (u, v, g) es -> X v -> X u) ->
      forall p, incl p es -> forall t, (forall w, X w -> t w = op (s w) a) ->
      forall w, X w -> fire op p t w = op (s w) a.
  Proof using assoc.
    intros es s a X Hs HX p. induction p as [| x p IH]; intros Hp t Ht w Hw; [exact (Ht w Hw) |].
    rewrite fire_cons. apply IH; [intros y Hy; apply Hp; right; exact Hy | | exact Hw].
    intros z Hz. destruct x as [[u v] g]. pose proof (Hp _ (or_introl eq_refl)) as Hin.
    rewrite fire1_eq. destruct (Nat.eq_dec z v) as [-> | _]; [| exact (Ht z Hz)].
    rewrite (Ht u (HX u v g Hin Hz)), assoc. pose proof (Hs _ Hin) as E. unfold sat in E.
    rewrite E. reflexivity.
  Qed.

  Theorem net_reach_all :
    forall es, has_section op es -> co_rooted es ->
      forall t0, exists p, incl p es /\ is_section op (fire op p t0) es.
  Proof using assoc id_l inv_r.
    intros es [s Hs] Hc.
    assert (Main : forall L t, exists p, incl p es /\
                     forall u v g, In (u, v, g) es -> (exists x, In x L /\ linked es x u) ->
                       sat op (fire op p t) (u, v, g)).
    { induction L as [| x L IH]; intro t.
      - exists []. split; [intros y [] | intros u v g _ [x [[] _]]].
      - destruct (IH t) as [p1 [Hp1 H1]].
        destruct (co_rooted_root es Hc x) as [r [Hxr Hr]].
        set (sg := fun w => op (s w) (op (inv (s r)) (fire op p1 t r))).
        assert (Hsg : is_section op sg es) by (apply translate_section; exact Hs).
        destruct (flood es sg Hsg [r] (fire op p1 t)) as [p2 [Hp2 [F1 F2]]].
        { intros r' [<- | []]. unfold sg. rewrite tr_back. reflexivity. }
        exists (p1 ++ p2).
        split; [intros y Hy; apply in_app_or in Hy; destruct Hy; [apply Hp1 | apply Hp2]; assumption |].
        assert (Rx : forall w, reach es r w -> linked es x w)
          by (intros w Hw; exact (linked_trans es x r w Hxr (linked_of_reach es r w Hw))).
        assert (Fx : forall w, linked es x w -> fire op p2 (fire op p1 t) w = sg w)
          by (intros w Hw; apply F1; exists r; split; [left; reflexivity | exact (Hr w Hw)]).
        assert (Fs : forall w, fire op p2 (fire op p1 t) w = fire op p1 t w \/ linked es x w).
        { intro w. destruct (F2 w) as [E | [r' [[<- | []] Hw]]]; [left; exact E | right; exact (Rx w Hw)]. }
        assert (Case : forall u v g, In (u, v, g) es -> linked es x u ->
                         sat op (fire op p2 (fire op p1 t)) (u, v, g)).
        { intros u v g Hin Hu. unfold sat.
          rewrite (Fx u Hu), (Fx v (linked_edge_fwd es x u v g Hin Hu)). exact (Hsg _ Hin). }
        intros u v g Hin [x' [[<- | Hx'] Hu]]; rewrite fire_app; [apply Case; assumption |].
        destruct (Fs u) as [Eu | Hu']; [| apply Case; assumption].
        destruct (Fs v) as [Ev | Hv']; [| apply Case; [exact Hin | exact (linked_edge_bwd es x u v g Hin Hv')]].
        unfold sat. rewrite Eu, Ev. exact (H1 u v g Hin (ex_intro _ x' (conj Hx' Hu))). }
    intro t0. destruct (Main (verts es) t0) as [p [Hp H]]. exists p. split; [exact Hp |].
    intros [[u v] g] Hin. apply H; [exact Hin |]. exists u.
    split; [exact (proj1 (in_verts_edge es u v g Hin)) | apply linked_refl].
  Qed.

  (* Existence from every start: a coboundary, and every component has a registry upstream of all
     of it, or the group is trivial. *)
  Theorem net_nf_exists_iff :
    forall es,
      (forall t0, exists p, incl p es /\ incl es p /\ is_section op (fire op p t0) es) <->
      has_section op es /\ (co_rooted es \/ @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intro es. split.
    - intro H. destruct (H (fun _ => e)) as [p [_ [_ Hp]]].
      assert (Hs : has_section op es) by (eexists; exact Hp).
      split; [exact Hs |]. destruct Hs as [s Hs].
      destruct (co_rooted_or_witness es) as [Hc | [x [y [Hxy Hno]]]]; [left; exact Hc | right].
      intros a b.
      destruct (anc_list es x) as [A HA]. destruct (anc_list es y) as [B HB].
      set (t0 := fun w => if in_dec Nat.eq_dec w A then op (s w) a else op (s w) b).
      destruct (H t0) as [q [Hq [_ Sq]]].
      assert (Ex : fire op q t0 x = op (s x) a).
      { apply (inclosed_stable es s a (fun w => In w A) Hs); [| exact Hq | | apply HA, reach_refl].
        - intros u v g Hin Hv. apply HA. apply HA in Hv.
          exact (reach_trans es u v x (reach_edge es u v g Hin) Hv).
        - intros w Hw. unfold t0. destruct (in_dec Nat.eq_dec w A); [reflexivity | contradiction]. }
      assert (Ey : fire op q t0 y = op (s y) b).
      { apply (inclosed_stable es s b (fun w => In w B) Hs); [| exact Hq | | apply HB, reach_refl].
        - intros u v g Hin Hv. apply HB. apply HB in Hv.
          exact (reach_trans es u v y (reach_edge es u v g Hin) Hv).
        - intros w Hw. unfold t0. destruct (in_dec Nat.eq_dec w A) as [HwA | _]; [| reflexivity].
          exfalso. apply Hno. exists w. split; [apply HA; exact HwA | apply HB; exact Hw]. }
      pose proof (linked_shift es s (fire op q t0) a x y Hs Sq Ex Hxy) as Ey'.
      rewrite Ey in Ey'. exact (eq_sym (lcancel _ _ _ Ey')).
    - intros [Hs [Hc | Ht]] t0.
      + destruct (net_reach_all es Hs Hc t0) as [p [Hp Sp]].
        destruct (extend_fair es p t0 Hp Sp) as [A [B [_ D]]].
        exists (p ++ es). split; [exact A | split; [exact B | exact D]].
      + exists es. split; [apply incl_refl | split; [apply incl_refl |]].
        intros [[u v] g] _. apply Ht.
  Qed.

  Corollary net_nf_exists_iff_nontrivial :
    forall a b : G, a <> b -> forall es,
      (forall t0, exists p, incl p es /\ incl es p /\ is_section op (fire op p t0) es) <->
      has_section op es /\ co_rooted es.
  Proof using assoc id_l id_r inv_r inv_l.
    intros a b Hab es. rewrite net_nf_exists_iff. split.
    - intros [Hs [Hc | Ht]]; [split; assumption | exfalso; exact (Hab (Ht a b))].
    - intros [Hs Hc]. split; [exact Hs | left; exact Hc].
  Qed.

  (* ----- uniqueness ----- *)

  Theorem unique_fair_iff : forall es, unique_nf_fair op es <-> unique_nf op es.
  Proof.
    intro es. split.
    - intros Hf t0 p1 p2 H1 H2 S1 S2 k.
      destruct (extend_fair es p1 t0 H1 S1) as [A1 [B1 [C1 D1]]].
      destruct (extend_fair es p2 t0 H2 S2) as [A2 [B2 [C2 D2]]].
      rewrite <- (C1 k), <- (C2 k). exact (Hf t0 (p1 ++ es) (p2 ++ es) A1 A2 B1 B2 D1 D2 k).
    - intros Hu t0 p1 p2 H1 H2 _ _ S1 S2. exact (Hu t0 p1 p2 H1 H2 S1 S2).
  Qed.

  Theorem net_unique_sufficient : forall es, root_cover es -> unique_nf op es.
  Proof using assoc id_l id_r inv_r inv_l.
    intros es Hr t0 p1 p2 H1 H2 S1 S2 k.
    destruct (in_dec Nat.eq_dec k (verts es)) as [Hk | Hk].
    - destruct (Hr k Hk) as [r [Hkr Hroot]].
      assert (Hloop : forall g, In (r, r, g) es -> g = e)
        by (intros g Hin; exact (selfloop_e es _ r g S1 Hin)).
      pose proof (dfr_stable es r Hroot Hloop p1 H1 t0) as R1.
      pose proof (dfr_stable es r Hroot Hloop p2 H2 t0) as R2.
      assert (E : fire op p2 t0 k = op (fire op p1 t0 k) e).
      { apply (linked_shift es (fire op p1 t0) (fire op p2 t0) e r k S1 S2);
          [rewrite R1, R2, id_r; reflexivity | apply linked_sym; exact Hkr]. }
      rewrite id_r in E. symmetry. exact E.
    - rewrite (untargeted es p1 t0 k Hk H1), (untargeted es p2 t0 k Hk H2). reflexivity.
  Qed.

  (* Uniqueness: the reachable consistent state is unique from every start iff (a consistent
     state exists ->) every component contains a de facto root, or the group is trivial. *)
  Theorem net_unique_iff :
    forall es, unique_nf op es <-> (has_section op es -> root_cover es \/ @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intro es. split.
    - intros Hu [s Hs].
      destruct (root_cover_or_witness es) as [Hr | [x [Hx Hprop]]]; [left; exact Hr | right].
      intros a b.
      destruct (comp_list es x) as [K HK].
      destruct (min_dom es K) as [X [HXK [HXdom HXind]]].
      set (t0 := fun w => if in_dec Nat.eq_dec w X then op (s w) b else op (s w) a).
      set (sg1 := fun w => op (s w) a).
      set (sg2 := fun w => if in_dec Nat.eq_dec w K then op (s w) b else op (s w) a).
      assert (S1 : is_section op sg1 es) by (apply translate_section; exact Hs).
      assert (S2 : is_section op sg2 es).
      { apply piece_section; [exact Hs |]. intros u v g Hin. rewrite !HK. split.
        - apply (linked_edge_fwd es x u v g Hin).
        - apply (linked_edge_bwd es x u v g Hin). }
      assert (A1 : forall w, In w (verts es) -> exists r, reach es r w /\ sg1 r = t0 r).
      { intros w Hw. unfold sg1, t0. destruct (in_dec Nat.eq_dec w X) as [HwX | HwX].
        - destruct (Hprop w (proj1 (HK w) (HXK w HwX))) as [u [g [Hin Hne]]].
          exists u. split; [exact (reach_edge es u w g Hin) |].
          destruct (in_dec Nat.eq_dec u X) as [HuX | HuX]; [| reflexivity].
          exfalso. exact (HXind w u HwX HuX Hne (reach_edge es u w g Hin)).
        - exists w. split; [apply reach_refl |].
          destruct (in_dec Nat.eq_dec w X); [contradiction | reflexivity]. }
      assert (A2 : forall w, In w (verts es) -> exists r, reach es r w /\ sg2 r = t0 r).
      { intros w Hw. unfold sg2, t0. destruct (in_dec Nat.eq_dec w K) as [HwK | HwK].
        - destruct (HXdom w HwK) as [r [HrX Hrw]]. exists r. split; [exact Hrw |].
          destruct (in_dec Nat.eq_dec r K) as [_ | HrK]; [| exfalso; exact (HrK (HXK r HrX))].
          destruct (in_dec Nat.eq_dec r X); [reflexivity | contradiction].
        - exists w. split; [apply reach_refl |].
          destruct (in_dec Nat.eq_dec w K); [contradiction |].
          destruct (in_dec Nat.eq_dec w X) as [HwX | _]; [exfalso; exact (HwK (HXK w HwX)) | reflexivity]. }
      destruct (proj2 (net_reachable_iff es sg1 t0 S1) A1) as [p1 [Hp1 E1]].
      destruct (proj2 (net_reachable_iff es sg2 t0 S2) A2) as [p2 [Hp2 E2]].
      pose proof (Hu t0 p1 p2 Hp1 Hp2 (section_verts es sg1 _ S1 E1)
                    (section_verts es sg2 _ S2 E2) x) as Ex.
      rewrite (E1 x Hx), (E2 x Hx) in Ex. unfold sg1, sg2 in Ex.
      destruct (in_dec Nat.eq_dec x K) as [_ | HxK];
        [| exfalso; apply HxK; apply HK; apply linked_refl].
      exact (lcancel _ _ _ Ex).
    - intros H t0 p1 p2 H1 H2 S1 S2.
      destruct (H (ex_intro _ (fire op p1 t0) S1)) as [Hr | Ht].
      + exact (net_unique_sufficient es Hr t0 p1 p2 H1 H2 S1 S2).
      + intro k. apply Ht.
  Qed.

  Corollary net_unique_fair_iff :
    forall es, unique_nf_fair op es <-> (has_section op es -> root_cover es \/ @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intro es. rewrite unique_fair_iff. apply net_unique_iff.
  Qed.

  Corollary net_unique_iff_nontrivial :
    forall a b : G, a <> b -> forall es, has_section op es ->
      (unique_nf op es <-> root_cover es) /\ (unique_nf_fair op es <-> root_cover es).
  Proof using assoc id_l id_r inv_r inv_l.
    intros a b Hab es Hs.
    assert (U : unique_nf op es <-> root_cover es).
    { rewrite net_unique_iff. split.
      - intro H. destruct (H Hs) as [Hr | Ht]; [exact Hr | exfalso; exact (Hab (Ht a b))].
      - intros Hr _. left. exact Hr. }
    split; [exact U | rewrite unique_fair_iff; exact U].
  Qed.

  (* ----- existence and uniqueness together ----- *)

  Theorem net_unique_normal_form_iff :
    forall es,
      (forall t0, exists p,
          incl p es /\ incl es p /\ is_section op (fire op p t0) es /\
          (forall q, incl q es -> is_section op (fire op q t0) es ->
             peq (fire op q t0) (fire op p t0)))
      <-> has_section op es /\ (authority_cover es \/ @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intro es. split.
    - intro H.
      assert (E : forall t0, exists p, incl p es /\ incl es p /\ is_section op (fire op p t0) es).
      { intro t0. destruct (H t0) as [p [A [B [C _]]]]. exists p. split; [exact A | split; assumption]. }
      destruct (proj1 (net_nf_exists_iff es) E) as [Hs Hct].
      assert (U : unique_nf op es).
      { intros t0 p1 p2 H1 H2 S1 S2 k. destruct (H t0) as [p [_ [_ [_ Hu]]]].
        rewrite (Hu p1 H1 S1 k), (Hu p2 H2 S2 k). reflexivity. }
      split; [exact Hs |].
      destruct (proj1 (net_unique_iff es) U Hs) as [Hr | Ht]; [| right; exact Ht].
      destruct Hct as [Hc | Ht]; [| right; exact Ht].
      left. apply authority_cover_iff. split; assumption.
    - intros [Hs [Ha | Ht]] t0.
      + apply authority_cover_iff in Ha. destruct Ha as [Hc Hr].
        destruct (proj2 (net_nf_exists_iff es) (conj Hs (or_introl Hc)) t0) as [p [Hp [Hf Sp]]].
        exists p. split; [exact Hp | split; [exact Hf | split; [exact Sp |]]].
        intros q Hq Sq k. exact (net_unique_sufficient es Hr t0 q p Hq Hp Sq Sp k).
      + exists es. split; [apply incl_refl | split; [apply incl_refl | split]].
        * intros [[u v] g] _. apply Ht.
        * intros q _ _ k. apply Ht.
  Qed.

  Corollary net_unique_normal_form_iff_nontrivial :
    forall a b : G, a <> b -> forall es,
      (forall t0, exists p,
          incl p es /\ incl es p /\ is_section op (fire op p t0) es /\
          (forall q, incl q es -> is_section op (fire op q t0) es ->
             peq (fire op q t0) (fire op p t0)))
      <-> has_section op es /\ authority_cover es.
  Proof using assoc id_l id_r inv_r inv_l.
    intros a b Hab es. rewrite net_unique_normal_form_iff. split.
    - intros [Hs [Ha | Ht]]; [split; assumption | exfalso; exact (Hab (Ht a b))].
    - intros [Hs Ha]. split; [exact Hs | left; exact Ha].
  Qed.

  (* ----- strongly connected networks ----- *)

  Theorem net_strong_iff :
    forall es, strongly_connected es -> (exists u v g, In (u, v, g) es /\ u <> v) ->
      ((forall t0, exists p, incl p es /\ incl es p /\ is_section op (fire op p t0) es) <->
       has_section op es) /\
      (unique_nf op es <-> (has_section op es -> @trivial_group G)) /\
      (unique_nf_fair op es <-> (has_section op es -> @trivial_group G)).
  Proof using assoc id_l id_r inv_r inv_l.
    intros es Hsc [u [v [g [Hin Huv]]]].
    pose proof (sc_not_root_cover es Hsc u v g Hin Huv) as Hnr.
    assert (U : unique_nf op es <-> (has_section op es -> @trivial_group G)).
    { rewrite net_unique_iff. split; intros H Hs.
      - destruct (H Hs) as [Hr | Ht]; [contradiction | exact Ht].
      - right. exact (H Hs). }
    split; [| split; [exact U | rewrite unique_fair_iff; exact U]].
    rewrite net_nf_exists_iff. split; [intros [Hs _]; exact Hs |].
    intro Hs. split; [exact Hs | left; exact (sc_co_rooted es Hsc)].
  Qed.

  (* ----- the single coherently oriented cycle, recovered ----- *)

  Lemma path_in :
    forall (gs : list G) j k, k < length gs -> exists g, In (j + k, S (j + k), g) (pathE j gs).
  Proof.
    induction gs as [| g gs IH]; intros j k Hk; simpl in Hk; [lia |].
    destruct k as [| k].
    - exists g. rewrite Nat.add_0_r. left. reflexivity.
    - destruct (IH (S j) k) as [g' H]; [lia |]. exists g'. right.
      replace (j + S k) with (S j + k) by lia. exact H.
  Qed.

  Lemma cyc_reach_up :
    forall (gs : list G) gc d k, k + d <= length gs -> reach (cycE gs gc) k (k + d).
  Proof.
    intros gs gc d. induction d as [| d IH]; intros k Hk; [rewrite Nat.add_0_r; apply reach_refl |].
    destruct (path_in gs 0 (k + d)) as [g Hg]; [lia |]. simpl in Hg.
    replace (k + S d) with (S (k + d)) by lia.
    apply (reach_step (cycE gs gc) k (k + d) (S (k + d)) g); [apply IH; lia |].
    apply path_incl. exact Hg.
  Qed.

  Lemma cyc_sc : forall (gs : list G) gc, strongly_connected (cycE gs gc).
  Proof.
    intros gs gc x y Hx Hy. apply cyc_verts in Hx. apply cyc_verts in Hy.
    assert (Hxn : reach (cycE gs gc) x (length gs)).
    { replace (length gs) with (x + (length gs - x)) by lia. apply cyc_reach_up. lia. }
    assert (Hx0 : reach (cycE gs gc) x 0)
      by exact (reach_step (cycE gs gc) x (length gs) 0 gc Hxn (closing_in gs gc)).
    exact (reach_trans _ x 0 y Hx0 (cyc_reach_up gs gc y 0 Hy)).
  Qed.

  Lemma cyc_proper : forall (gs : list G) gc, 1 <= length gs -> exists u v g, In (u, v, g) (cycE gs gc) /\ u <> v.
  Proof.
    intros gs gc Hn. destruct (path_in gs 0 0) as [g Hg]; [lia |]. simpl in Hg.
    exists 0, 1, g. split; [apply path_incl; exact Hg | discriminate].
  Qed.

  Corollary cycle_nf_exists_recovered :
    forall gs gc,
      (forall t0, exists p, incl p (cycE gs gc) /\ incl (cycE gs gc) p /\
                            is_section op (fire op p t0) (cycE gs gc)) <->
      op gc (hol op gs e) = e.
  Proof using assoc id_l id_r inv_r inv_l.
    intros gs gc. rewrite net_nf_exists_iff.
    rewrite <- (rootless_section_iff_holonomy op e inv assoc id_l id_r inv_r gs gc). split.
    - intros [H _]. exact H.
    - intro H. split; [exact H | left; exact (sc_co_rooted _ (cyc_sc gs gc))].
  Qed.

  Corollary cycle_unique_recovered :
    forall gs gc, 1 <= length gs -> op gc (hol op gs e) = e ->
      (unique_nf op (cycE gs gc) <-> @trivial_group G) /\
      (unique_nf_fair op (cycE gs gc) <-> @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intros gs gc Hn Hh.
    apply (rootless_section_iff_holonomy op e inv assoc id_l id_r inv_r) in Hh.
    destruct (net_strong_iff _ (cyc_sc gs gc) (cyc_proper gs gc Hn)) as [_ [U F]].
    rewrite U, F. split; split; intro H; try exact (H Hh); intros _; exact H.
  Qed.

  Corollary cycle_unique_general_recovered :
    forall gs gc, 1 <= length gs ->
      (unique_nf op (cycE gs gc) <-> (op gc (hol op gs e) = e -> @trivial_group G)) /\
      (unique_nf_fair op (cycE gs gc) <-> (op gc (hol op gs e) = e -> @trivial_group G)).
  Proof using assoc id_l id_r inv_r inv_l.
    intros gs gc Hn.
    destruct (net_strong_iff _ (cyc_sc gs gc) (cyc_proper gs gc Hn)) as [_ [U F]].
    rewrite U, F, (rootless_section_iff_holonomy op e inv assoc id_l id_r inv_r gs gc).
    split; reflexivity.
  Qed.

  Corollary cycle_unique_normal_form_recovered :
    forall gs gc, 1 <= length gs ->
      ((forall t0, exists p,
          incl p (cycE gs gc) /\ incl (cycE gs gc) p /\
          is_section op (fire op p t0) (cycE gs gc) /\
          (forall q, incl q (cycE gs gc) -> is_section op (fire op q t0) (cycE gs gc) ->
             peq (fire op q t0) (fire op p t0)))
       <-> @trivial_group G).
  Proof using assoc id_l id_r inv_r inv_l.
    intros gs gc Hn. rewrite net_unique_normal_form_iff. split.
    - intros [_ [Ha | Ht]]; [| exact Ht]. exfalso.
      destruct (cyc_proper gs gc Hn) as [u [v [g [Hin Huv]]]].
      apply (sc_not_root_cover _ (cyc_sc gs gc) u v g Hin Huv).
      exact (proj2 (proj1 (authority_cover_iff _) Ha)).
    - intro Ht. split; [exists (fun _ => e); intros [[u v] g] _; apply Ht | right; exact Ht].
  Qed.
End Networks.

(* ============================================================
   Instances, boundary cases and counterexamples over Z/2 = (bool, xor).
   ============================================================ *)

Ltac in_list := simpl; repeat (first [left; reflexivity | right]).

Lemma all_false_section :
  forall es : list (@edge bool), (forall u v g, In (u, v, g) es -> g = false) ->
    has_section xorb es.
Proof.
  intros es H. exists (fun _ => false). intros [[u v] g] Hin. unfold sat.
  rewrite (H u v g Hin). reflexivity.
Qed.

(* ----- two coherently oriented cycles sharing a registry ----- *)

Definition fig8 : list (@edge bool) := [(0, 1, false); (1, 0, false); (0, 2, false); (2, 0, false)].

Lemma fig8_sc : strongly_connected fig8.
Proof.
  assert (V : forall x, In x (verts fig8) -> x = 0 \/ x = 1 \/ x = 2).
  { intros x Hx. simpl in Hx. lia. }
  assert (To0 : forall x, In x (verts fig8) -> reach fig8 x 0).
  { intros x Hx. destruct (V x Hx) as [-> | [-> | ->]];
      [apply reach_refl | apply (reach_edge _ _ _ false); in_list | apply (reach_edge _ _ _ false); in_list]. }
  assert (From0 : forall x, In x (verts fig8) -> reach fig8 0 x).
  { intros x Hx. destruct (V x Hx) as [-> | [-> | ->]];
      [apply reach_refl | apply (reach_edge _ _ _ false); in_list | apply (reach_edge _ _ _ false); in_list]. }
  intros x y Hx Hy. exact (reach_trans _ x 0 y (To0 x Hx) (From0 y Hy)).
Qed.

Theorem rootless_figure_eight :
  strongly_connected fig8 /\ has_section xorb fig8 /\
  (forall t0, exists p, incl p fig8 /\ incl fig8 p /\ is_section xorb (fire xorb p t0) fig8) /\
  ~ unique_nf xorb fig8 /\ ~ unique_nf_fair xorb fig8.
Proof.
  assert (Hs : has_section xorb fig8).
  { apply all_false_section. intros u v g H. simpl in H.
    destruct H as [H | [H | [H | [H | []]]]]; injection H as _ _ <-; reflexivity. }
  assert (Hp : exists u v g, In (u, v, g) fig8 /\ u <> v)
    by (exists 0, 1, false; split; [in_list | discriminate]).
  destruct (net_strong_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l fig8
              fig8_sc Hp) as [E [U F]].
  split; [exact fig8_sc |]. split; [exact Hs |]. split; [apply E; exact Hs |].
  split; intro H; [pose proof (proj1 U H Hs true false) as B | pose proof (proj1 F H Hs true false) as B];
    discriminate B.
Qed.

(* ----- mixed orientation: 0 -> 1 <- 2 -> 3 <- 0 ----- *)

Definition sq : list (@edge bool) := [(0, 1, false); (2, 1, false); (2, 3, false); (0, 3, false)].

Lemma sq_dfr0 : de_facto_root sq 0.
Proof. intros u g H. simpl in H. destruct H as [H | [H | [H | [H | []]]]]; discriminate H. Qed.

Lemma sq_dfr2 : de_facto_root sq 2.
Proof. intros u g H. simpl in H. destruct H as [H | [H | [H | [H | []]]]]; discriminate H. Qed.

Lemma sq_linked02 : linked sq 0 2.
Proof.
  apply (linked_edge_bwd sq 0 2 1 false); [in_list |].
  apply linked_of_reach. apply (reach_edge _ _ _ false). in_list.
Qed.

Theorem rootless_mixed_square :
  has_section xorb sq /\ root_cover sq /\ unique_nf xorb sq /\ ~ co_rooted sq /\
  ~ (forall t0, exists p, incl p sq /\ is_section xorb (fire xorb p t0) sq).
Proof.
  assert (Hs : has_section xorb sq).
  { apply all_false_section. intros u v g H. simpl in H.
    destruct H as [H | [H | [H | [H | []]]]]; injection H as _ _ <-; reflexivity. }
  assert (Hrc : root_cover sq).
  { intros x Hx. exists 0. split; [| exact sq_dfr0]. apply linked_sym.
    simpl in Hx. destruct Hx as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
      try apply linked_refl; try exact sq_linked02;
      apply linked_of_reach; apply (reach_edge _ _ _ false); in_list. }
  split; [exact Hs |]. split; [exact Hrc |].
  split; [exact (net_unique_sufficient xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r
                   xor_inv_l sq Hrc) |].
  split.
  - intro Hc. destruct (Hc 0 2 sq_linked02) as [r [H0 H2]].
    pose proof (reach_to_dfr sq r 0 H0 sq_dfr0). pose proof (reach_to_dfr sq r 2 H2 sq_dfr2).
    congruence.
  - intro H. set (t0 := fun w => if Nat.eq_dec w 0 then true else false).
    destruct (H t0) as [p [Hp Sp]].
    assert (Hno : forall r g, In (r, r, g) sq -> g = false).
    { intros r g Hin. simpl in Hin. destruct Hin as [E | [E | [E | [E | []]]]]; congruence. }
    pose proof (dfr_stable xorb false xor_id_l sq 0 sq_dfr0 (Hno 0) p Hp t0) as R0.
    pose proof (dfr_stable xorb false xor_id_l sq 2 sq_dfr2 (Hno 2) p Hp t0) as R2.
    pose proof (Sp (0, 1, false) ltac:(in_list)) as E1.
    pose proof (Sp (2, 1, false) ltac:(in_list)) as E2.
    unfold sat in E1, E2. rewrite R0 in E1. rewrite R2 in E2. unfold t0 in E1, E2. simpl in E1, E2. congruence.
Qed.

(* ----- a source feeding a coherently oriented cycle ----- *)

Definition sfc : list (@edge bool) := [(0, 1, false); (1, 2, false); (2, 1, false)].

Theorem rootless_source_feeds_cycle :
  In (1, 2, false) sfc /\ In (2, 1, false) sfc /\ authority_cover sfc /\ ~ @trivial_group bool /\
  (forall t0, exists p,
     incl p sfc /\ incl sfc p /\ is_section xorb (fire xorb p t0) sfc /\
     (forall q, incl q sfc -> is_section xorb (fire xorb q t0) sfc ->
        peq (fire xorb q t0) (fire xorb p t0))).
Proof.
  assert (Ha : authority_cover sfc).
  { apply (authority_of_root sfc 0).
    - intros u g H. simpl in H. destruct H as [H | [H | [H | []]]]; discriminate H.
    - intros y Hy. assert (Hr01 : reach sfc 0 1) by (apply (reach_edge _ _ _ false); in_list).
      simpl in Hy. assert (y = 0 \/ y = 1 \/ y = 2) as [-> | [-> | ->]] by lia;
        [apply reach_refl | exact Hr01 |].
      apply (reach_step sfc 0 1 2 false Hr01). in_list. }
  split; [in_list |]. split; [in_list |]. split; [exact Ha |].
  split; [intro H; discriminate (H true false) |].
  apply (net_unique_normal_form_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l).
  split; [| left; exact Ha].
  apply all_false_section. intros u v g H. simpl in H.
  destruct H as [H | [H | [H | []]]]; injection H as _ _ <-; reflexivity.
Qed.

(* ----- a cycle feeding a cycle: 0 <-> 1 -> 2 <-> 3 ----- *)

Definition cfc : list (@edge bool) :=
  [(0, 1, false); (1, 0, false); (1, 2, false); (2, 3, false); (3, 2, false)].

Theorem rootless_cycle_feeds_cycle :
  co_rooted cfc /\ ~ root_cover cfc /\
  (forall t0, exists p, incl p cfc /\ incl cfc p /\ is_section xorb (fire xorb p t0) cfc) /\
  ~ unique_nf xorb cfc /\ ~ unique_nf_fair xorb cfc.
Proof.
  assert (Hs : has_section xorb cfc).
  { apply all_false_section. intros u v g H. simpl in H.
    destruct H as [H | [H | [H | [H | [H | []]]]]]; injection H as _ _ <-; reflexivity. }
  assert (Hc : co_rooted cfc).
  { apply (co_rooted_of_root cfc 0). intros y Hy.
    assert (R1 : reach cfc 0 1) by (apply (reach_edge _ _ _ false); in_list).
    assert (R2 : reach cfc 0 2) by (apply (reach_step cfc 0 1 2 false R1); in_list).
    assert (R3 : reach cfc 0 3) by (apply (reach_step cfc 0 2 3 false R2); in_list).
    simpl in Hy. assert (y = 0 \/ y = 1 \/ y = 2 \/ y = 3) as [-> | [-> | [-> | ->]]] by lia;
      [apply reach_refl | exact R1 | exact R2 | exact R3]. }
  assert (Hnr : ~ root_cover cfc).
  { intro H. destruct (H 0 ltac:(in_list)) as [r [H0r Hr]].
    assert (Hv : r = 0 \/ r = 1 \/ r = 2 \/ r = 3).
    { destruct (linked_verts cfc 0 r H0r) as [<- | [_ Hv]]; [lia | simpl in Hv; lia]. }
    destruct Hv as [-> | [-> | [-> | ->]]].
    - discriminate (Hr 1 false ltac:(in_list)).
    - discriminate (Hr 0 false ltac:(in_list)).
    - discriminate (Hr 1 false ltac:(in_list)).
    - discriminate (Hr 2 false ltac:(in_list)). }
  pose proof (net_unique_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l cfc) as U.
  pose proof (net_unique_fair_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l cfc) as F.
  split; [exact Hc |]. split; [exact Hnr |].
  split; [apply (net_nf_exists_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l);
          split; [exact Hs | left; exact Hc] |].
  split; intro H; [destruct (proj1 U H Hs) as [Hr | Ht] | destruct (proj1 F H Hs) as [Hr | Ht]];
    try exact (Hnr Hr); discriminate (Ht true false).
Qed.

(* ----- mixed orientation with a flip: rooted, acyclic, yet no consistent state ----- *)

Definition tri_flip : list (@edge bool) := [(0, 1, false); (1, 2, false); (0, 2, true)].

Theorem rootless_global_holonomy :
  authority_cover tri_flip /\
  (forall x y, reach tri_flip x y -> reach tri_flip y x -> x = y) /\
  ~ has_section xorb tri_flip /\
  (forall t0 p, ~ is_section xorb (fire xorb p t0) tri_flip).
Proof.
  assert (Hno : ~ has_section xorb tri_flip).
  { intros [s Hs].
    pose proof (Hs (0, 1, false) ltac:(in_list)) as E1.
    pose proof (Hs (1, 2, false) ltac:(in_list)) as E2.
    pose proof (Hs (0, 2, true) ltac:(in_list)) as E3.
    unfold sat in E1, E2, E3. rewrite <- E2, <- E1 in E3.
    destruct (s 0); discriminate E3. }
  split.
  - apply (authority_of_root tri_flip 0).
    + intros u g H. simpl in H. destruct H as [H | [H | [H | []]]]; discriminate H.
    + intros y Hy. simpl in Hy. assert (y = 0 \/ y = 1 \/ y = 2) as [-> | [-> | ->]] by lia;
        [apply reach_refl | apply (reach_edge _ _ _ false); in_list |
         apply (reach_edge _ _ _ true); in_list].
  - split; [| split; [exact Hno | intros t0 p H; apply Hno; eexists; exact H]].
    assert (Hm : forall u v g, In (u, v, g) tri_flip -> u < v).
    { intros u v g H. simpl in H.
      destruct H as [H | [H | [H | []]]]; injection H as <- <- _; lia. }
    intros x y H1 H2. pose proof (reach_mono tri_flip Hm x y H1).
    pose proof (reach_mono tri_flip Hm y x H2). lia.
Qed.

(* ----- the two corners of RootlessCycles.v, explained ----- *)

(* The self-loop registry has no incoming edge from another registry: a de facto root. *)
Theorem selfloop_recovered :
  cycE [] false = [(0, 0, false)] /\ root_cover (cycE [] false) /\ unique_nf xorb (cycE [] false).
Proof.
  assert (Hrc : root_cover (cycE [] false)).
  { intros x Hx. exists 0. split.
    - simpl in Hx. destruct Hx as [<- | [<- | []]]; apply linked_refl.
    - intros u g [H | []]. injection H as <- _. reflexivity. }
  split; [reflexivity |]. split; [exact Hrc |].
  exact (net_unique_sufficient xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l _ Hrc).
Qed.

(* The mixed triangle of rootless_orientation_matters has an authority root, registry 0. *)
Theorem orientation_matters_recovered :
  authority_cover tri_mixed /\ unique_nf xorb tri_mixed /\
  (forall t0, exists p, incl p tri_mixed /\ incl tri_mixed p /\
                        is_section xorb (fire xorb p t0) tri_mixed).
Proof.
  assert (Ha : authority_cover tri_mixed).
  { apply (authority_of_root tri_mixed 0).
    - intros u g H. simpl in H. destruct H as [H | [H | [H | []]]]; discriminate H.
    - intros y Hy. simpl in Hy. assert (y = 0 \/ y = 1 \/ y = 2) as [-> | [-> | ->]] by lia;
        [apply reach_refl | |]; apply (reach_edge _ _ _ false); in_list. }
  assert (Hs : has_section xorb tri_mixed).
  { apply all_false_section. intros u v g H. simpl in H.
    destruct H as [H | [H | [H | []]]]; injection H as _ _ <-; reflexivity. }
  destruct (proj1 (authority_cover_iff tri_mixed) Ha) as [Hc Hr].
  split; [exact Ha |]. split.
  - exact (net_unique_sufficient xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l _ Hr).
  - apply (net_nf_exists_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l).
    split; [exact Hs | left; exact Hc].
Qed.

(* Non-vacuity of the cycle corollaries' hypotheses: the Z/2 copy-back loop of RootlessCycles.v
   (one path edge, trivial holonomy) is not unique, now as an instance of cycle_unique_recovered. *)
Theorem copyback_recovered_net :
  1 <= length cb_gs /\ xorb cb_gc (hol xorb cb_gs false) = false /\
  ~ unique_nf xorb (cycE cb_gs cb_gc) /\ ~ unique_nf_fair xorb (cycE cb_gs cb_gc).
Proof.
  destruct (cycle_unique_recovered xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
              cb_gs cb_gc (le_n 1) eq_refl) as [[U _] [F _]].
  split; [apply le_n |]. split; [reflexivity |].
  split; intro H; [discriminate (U H true false) | discriminate (F H true false)].
Qed.
