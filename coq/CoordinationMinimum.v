(* CoordinationMinimum.v: minimum coordination on invertible networks tied to the authority-root plan
   model, mechanized axiom-free (gap 10 of REGIME-AUDIT.md).

   Setting: a group-labeled graph (the regular action), as in CohomologyGraph.v. CoordinatedCycles.v
   fixes a spanning tree T grown from an authority root r and coordinates exactly the non-tree edges
   that are unbalanced against T (plan_exact). CohomologyGeneral.v defines a feasible coordination
   as a deletion set whose residual has a section, and bounds its minimum from below. Nothing linked
   the two. This file does.

   Definitions.
     plan Es r T X        T is a tree grown from r, Es is T ++ X up to order (so T is a sub-multiset
                          of the network), and T spans the non-tree edges X. Having a plan rooted at r is
                          how connectivity of the network (with r a vertex) is stated.
     coord r T X          the plan's coordinated set: the non-tree edges unbalanced against T,
                          tested against the computed tree section tsec r T (balance is static,
                          balanced_any_section, so plan_cost_any_section: any tree section gives the
                          same count).
     plan_cost r T X      the size of coord r T X.
     feasibleM Es F       F is a sub-multiset of Es (Es is K ++ F up to order) whose removal leaves a
                          network K with a global section. CohomologyGeneral.feasible deletes by
                          membership; the two agree on duplicate-free networks (feasibleM_feasible,
                          feasible_feasibleM).

   Main results (any group, decidable equality on labels).
     plan_coord_feasible  for every plan, the coordinated set is feasible: its residual T ++ kept has
                          the tree section (keep_balanced_suffices); plan_coord_exact restates
                          plan_exact for the computed split (a set of non-tree edges can be kept iff
                          it avoids coord).
     feasible_plan        conversely, for every feasible F there is a plan rooted at the same r with
                          plan_cost <= |F|. The residual K = Es - F may be disconnected: the tree is
                          grown from r, through edges of K first; when no edge of K leaves the grown
                          part, an edge of F is taken and the section of K is multiplied on the right
                          by one constant on everything not yet reached (gauge freedom), which keeps
                          every K edge satisfied because none of them crosses. So tree edges in F are
                          harmless and only non-tree edges of F can be coordinated.
     plan_min_exact       hence, for a connected network and every k:
                            (exists a plan rooted at r with plan_cost <= k)
                              <-> (exists a feasible F with |F| <= k).
                          The minimum over rooted spanning trees of the plan's cost is the minimum
                          feasible coordination, the group feedback edge set number, for every root.
     plan_min_root_independent  so the optimum is the same for every authority root.
     plan_min_lower_iff   the same for lower bounds (every plan costs >= k iff every feasible set has
                          size >= k).
     plan_min_attained    a minimum feasible F yields a plan whose cost is |F| and which is optimal
                          among all plans.
     plan_min_exact_set   the same iff with CohomologyGeneral.feasible, for a duplicate-free network.
     plan_cost_ge_disjoint  edge_disjoint_lower_bound recovered for every plan.
     section_decide       relative to a tree, a section of T ++ X exists iff the computed tree section
                          satisfies every edge of X (a decision procedure; cycle_basis_criterion).

   The hypotheses are needed.
     plan_min_connected_needed  two disjoint edges: the empty set is feasible, but no plan exists for
                          any root, so the tree form of the iff fails. Per connected component the
                          theorem applies as stated.
     plan_min_nodup_needed  a duplicated network: membership deletion of one edge is feasible, yet
                          every plan costs 2 (one deleted entry removes two copies).

   Complexity. maxcut_reduction mechanizes the reduction from Max-Cut: a graph H becomes the Z/2
   network signed H with every edge labeled by the flip, of the same size (signed_size); a feasible
   coordination of size |F| exists with |F| + k <= |H| iff H has a cut with at least k edges.
   maxcut_plan_reduction is the same for plans when the network is connected. NP-hardness of the
   minimum (already for Z/2, and for the plan model) then follows from the NP-completeness of Max-Cut
   (Karp 1972), which is cited, not mechanized; membership in NP is the plan itself (section_decide
   checks it). maxcut_triangle is the non-vacuity instance.

   Instances (every hypothesis discharged).
     negation_plan_min    gsm's negation 2-cycle over Z/2: cost 1, the minimum.
     bowtie_plan_min      two Z/2 triangles sharing a vertex: cost 2, the minimum (bowtie_min_two).
     pendant_tree_uses_F  a negation loop with a pendant edge: the feasible set that also deletes the
                          pendant edge leaves a disconnected residual, and every spanning tree uses
                          that deleted edge.
     s3_tree_choice       an S_3 network (four paths from 0 to 1 with holonomies id, rho, rho, tau):
                          the plan of a bad tree costs 3, the plan of a good tree costs 2, and 2 is
                          the minimum over every plan and every feasible set; the abelian image
                          (sign into Z/2) needs only 1, so the S_3 minimum is strictly above it.

   Every theorem is closed under the global context. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.CohomologyGraph NC.CoordinatedCycles NC.CohomologyGeneral.
Import ListNotations.

(* ===================================================================== *)
(* Local list facts (stated here so the file builds on Coq 8.18 to Rocq 9.3). *)

Lemma cm_filter_app :
  forall (A : Type) (p : A -> bool) l l', filter p (l ++ l') = filter p l ++ filter p l'.
Proof.
  intros A p l l'. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite IH. destruct (p a); reflexivity.
Qed.

Lemma cm_len_app : forall (A : Type) (l l' : list A), length (l ++ l') = length l + length l'.
Proof. intros A l l'. induction l as [| a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cm_filter_perm_len :
  forall (A : Type) (p : A -> bool) l l', Permutation l l' -> length (filter p l) = length (filter p l').
Proof.
  intros A p l l' H. induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
  - reflexivity.
  - destruct (p x); simpl; lia.
  - destruct (p x), (p y); simpl; reflexivity.
  - lia.
Qed.

Lemma cm_filter_len_le : forall (A : Type) (p : A -> bool) l, length (filter p l) <= length l.
Proof. intros A p l. induction l as [| a l IH]; simpl; [lia | destruct (p a); simpl; lia]. Qed.

Lemma cm_filter_mono :
  forall (A : Type) (p q : A -> bool) l, (forall x, In x l -> p x = true -> q x = true) ->
    length (filter p l) <= length (filter q l).
Proof.
  intros A p q l H. induction l as [| a l IH]; simpl; [lia |].
  assert (IH' : length (filter p l) <= length (filter q l))
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (p a) eqn:Ep.
  - rewrite (H a (or_introl eq_refl) Ep). simpl. lia.
  - destruct (q a); simpl; lia.
Qed.

Lemma cm_filter_none :
  forall (A : Type) (p : A -> bool) l, (forall x, In x l -> p x = false) -> length (filter p l) = 0.
Proof.
  intros A p l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma cm_filter_all :
  forall (A : Type) (p : A -> bool) l, (forall x, In x l -> p x = true) -> length (filter p l) = length l.
Proof.
  intros A p l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)). simpl. rewrite IH; [reflexivity |].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma cm_filter_ext_in :
  forall (A : Type) (p q : A -> bool) l, (forall x, In x l -> p x = q x) -> filter p l = filter q l.
Proof.
  intros A p q l H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity |]. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma cm_perm_partition :
  forall (A : Type) (p : A -> bool) l, Permutation l (filter p l ++ filter (fun x => negb (p x)) l).
Proof.
  intros A p l. induction l as [| a l IH]; simpl; [constructor |].
  destruct (p a); simpl.
  - apply perm_skip. exact IH.
  - apply Permutation_cons_app. exact IH.
Qed.

Lemma cm_nodup_filter :
  forall (A : Type) (p : A -> bool) l, NoDup l -> NoDup (filter p l).
Proof.
  intros A p l H. induction H as [| a l Ha H IH]; simpl; [constructor |].
  destruct (p a); [| exact IH]. constructor; [| exact IH].
  intro Hin. apply filter_In in Hin. apply Ha. exact (proj1 Hin).
Qed.

(* ===================================================================== *)
(* Vertex sets: crossing edges and the number of target vertices not yet reached. *)

Definition cross {G : Type} (V : list nat) (x : @edge G) : Prop :=
  let '(u, v, _) := x in (In u V /\ ~ In v V) \/ (In v V /\ ~ In u V).

Lemma cross_dec_list :
  forall {G : Type} (V : list nat) (l : list (@edge G)),
    {y | In y l /\ cross V y} + {forall y, In y l -> ~ cross V y}.
Proof.
  intros G V l. induction l as [| [[u v] g] l IH].
  - right. intros y [].
  - destruct (in_dec Nat.eq_dec u V) as [Hu | Hu]; destruct (in_dec Nat.eq_dec v V) as [Hv | Hv].
    + destruct IH as [[y [Hy Hc]] | Hno].
      * left. exists y. split; [right; exact Hy | exact Hc].
      * right. intros y [<- | Hy]; [| exact (Hno y Hy)]. simpl. intros [[_ H] | [_ H]]; contradiction.
    + left. exists (u, v, g). split; [left; reflexivity |]. simpl. left. split; assumption.
    + left. exists (u, v, g). split; [left; reflexivity |]. simpl. right. split; assumption.
    + destruct IH as [[y [Hy Hc]] | Hno].
      * left. exists y. split; [right; exact Hy | exact Hc].
      * right. intros y [<- | Hy]; [| exact (Hno y Hy)]. simpl. intros [[H _] | [H _]]; contradiction.
Qed.

(* A tree grown from r inside V reaches every vertex of a spanning tree T0, or some edge of T0
   leaves V: this is how connectivity is used. *)
Lemma tree_cross :
  forall {G : Type} r (T0 : list (@edge G)), tree r T0 ->
    forall V, In r V -> forall z, In z (r :: verts T0) -> ~ In z V ->
      exists y, In y T0 /\ cross V y.
Proof.
  intros G r T0 HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu];
    intros V Hr z Hz HzV.
  - simpl in Hz. destruct Hz as [<- | []]. contradiction.
  - destruct (verts_snoc r es u v g z Hz) as [Hold | [-> | ->]].
    + destruct (IH V Hr z Hold HzV) as [y [Hy Hc]].
      exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
    + destruct (IH V Hr u Hu HzV) as [y [Hy Hc]].
      exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
    + destruct (in_dec Nat.eq_dec u V) as [HuV | HuV].
      * exists (u, v, g). split; [apply in_or_app; right; left; reflexivity |].
        simpl. left. split; assumption.
      * destruct (IH V Hr u Hu HuV) as [y [Hy Hc]].
        exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
  - destruct (verts_snoc r es u v g z Hz) as [Hold | [-> | ->]].
    + destruct (IH V Hr z Hold HzV) as [y [Hy Hc]].
      exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
    + destruct (in_dec Nat.eq_dec v V) as [HvV | HvV].
      * exists (u, v, g). split; [apply in_or_app; right; left; reflexivity |].
        simpl. right. split; assumption.
      * destruct (IH V Hr v Hv HvV) as [y [Hy Hc]].
        exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
    + destruct (IH V Hr v Hv HzV) as [y [Hy Hc]].
      exists y. split; [apply in_or_app; left; exact Hy | exact Hc].
Qed.

Definition outside (V L : list nat) : nat :=
  length (filter (fun z => if in_dec Nat.eq_dec z V then false else true) L).

Lemma outside_lt :
  forall V V' L w, incl V V' -> In w L -> ~ In w V -> In w V' -> outside V' L < outside V L.
Proof.
  intros V V' L w Hinc. unfold outside.
  assert (Hle : forall M,
             length (filter (fun z => if in_dec Nat.eq_dec z V' then false else true) M) <=
             length (filter (fun z => if in_dec Nat.eq_dec z V then false else true) M)).
  { intro M. induction M as [| b M IHM]; simpl; [lia |].
    destruct (in_dec Nat.eq_dec b V') as [H1 | H1]; destruct (in_dec Nat.eq_dec b V) as [H2 | H2];
      simpl; try lia.
    exfalso. apply H1. apply Hinc. exact H2. }
  induction L as [| a L IH]; intros Hw HwV HwV'; [destruct Hw |]. simpl.
  destruct Hw as [Ea | Hw].
  - subst a.
    destruct (in_dec Nat.eq_dec w V') as [_ | H]; [| contradiction].
    destruct (in_dec Nat.eq_dec w V) as [H | _]; [contradiction |]. simpl. specialize (Hle L). lia.
  - specialize (IH Hw HwV HwV').
    destruct (in_dec Nat.eq_dec a V') as [H1 | H1]; destruct (in_dec Nat.eq_dec a V) as [H2 | H2];
      simpl; try lia.
    exfalso. apply H1. apply Hinc. exact H2.
Qed.

Lemma outside_le : forall V L, outside V L <= length L.
Proof. intros V L. apply cm_filter_len_le. Qed.

(* ===================================================================== *)
(* Plans, feasible sets and checkers (no group laws needed).            *)

Section Checkers.
  Context {G : Type}.
  Variable op : G -> G -> G.
  Hypothesis G_eq_dec : forall a b : G, {a = b} + {a <> b}.
  Set Default Proof Using "All".

  Definition ed_dec : forall x y : @edge G, {x = y} + {x <> y}.
  Proof using G_eq_dec.
    intros [[a b] c] [[a' b'] c'].
    destruct (Nat.eq_dec a a') as [Ea | Ha]; [| right; congruence].
    destruct (Nat.eq_dec b b') as [Eb | Hb]; [| right; congruence].
    destruct (G_eq_dec c c') as [Ec | Hc]; [left; subst; reflexivity | right; congruence].
  Defined.

  (* ----- balance as a boolean ----- *)

  Definition balb (s : nat -> G) (x : @edge G) : bool :=
    let '(u, v, g) := x in if G_eq_dec (op g (s u)) (s v) then true else false.

  Lemma balb_true : forall s x, balb s x = true <-> sat op s x.
  Proof.
    intros s [[u v] g]. unfold balb, sat.
    destruct (G_eq_dec (op g (s u)) (s v)) as [E | E]; split; intro H;
      [exact E | reflexivity | discriminate H | contradiction].
  Qed.

  Lemma balb_false : forall s x, balb s x = false <-> ~ sat op s x.
  Proof.
    intros s x. split.
    - intros H Hs. apply balb_true in Hs. rewrite Hs in H. discriminate H.
    - intro H. destruct (balb s x) eqn:E; [| reflexivity]. exfalso. apply H. apply balb_true. exact E.
  Qed.

  (* ----- plans, their coordinated set and cost ----- *)

  Definition plan (Es : list (@edge G)) (r : nat) (T X : list (@edge G)) : Prop :=
    tree r T /\ Permutation Es (T ++ X) /\ spans r T X.

  (* Removing the sub-multiset F of Es leaves a network K with a global section. *)
  Definition feasibleM (Es F : list (@edge G)) : Prop :=
    exists K, Permutation Es (K ++ F) /\ has_section op K.

  Lemma perm_incl :
    forall (Es A B : list (@edge G)), Permutation Es (A ++ B) -> incl A Es /\ incl B Es.
  Proof.
    intros Es A B H. split; intros x Hx; apply (Permutation_in x (Permutation_sym H));
      apply in_or_app; [left | right]; exact Hx.
  Qed.

  (* Every endpoint of the network is a vertex of a plan's tree. *)
  Lemma plan_covers :
    forall Es r T X, plan Es r T X ->
      forall u v g, In (u, v, g) Es -> In u (r :: verts T) /\ In v (r :: verts T).
  Proof.
    intros Es r T X [HT [HP Hsp]] u v g Hin.
    apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - destruct (in_verts_edge T u v g Hin) as [Hu Hv]. split; right; assumption.
    - exact (Hsp u v g Hin).
  Qed.

  (* ----- CohomologyGeneral.feasible (deletion by membership) ----- *)

  Lemma feasibleM_feasible : forall Es F, feasibleM Es F -> feasible op Es F.
  Proof.
    intros Es F [K [HP [s Hs]]]. exists s. intros x Hx Hnx. apply Hs.
    apply (Permutation_in _ HP) in Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx];
      [exact Hx | contradiction].
  Qed.

  Lemma feasible_feasibleM :
    forall Es D, NoDup Es -> feasible op Es D -> exists F, feasibleM Es F /\ length F <= length D.
  Proof.
    intros Es D Hnd [s Hs].
    pose (notD := fun x : @edge G => if in_dec ed_dec x D then false else true).
    exists (filter (fun x => negb (notD x)) Es). split.
    - exists (filter notD Es). split; [apply cm_perm_partition |].
      exists s. intros x Hx. apply filter_In in Hx. destruct Hx as [Hx Hn]. apply (Hs x Hx).
      unfold notD in Hn. destruct (in_dec ed_dec x D); [discriminate Hn | assumption].
    - apply NoDup_incl_length; [apply cm_nodup_filter; exact Hnd |].
      intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hn]. unfold notD in Hn.
      destruct (in_dec ed_dec x D); [assumption | discriminate Hn].
  Qed.

  Lemma feasibleM_nil : forall Es, feasibleM Es [] -> has_section op Es.
  Proof.
    intros Es [K [HP [s Hs]]]. exists s. intros x Hx. apply Hs.
    rewrite app_nil_r in HP. exact (Permutation_in _ HP Hx).
  Qed.

  (* ----- boolean checkers for concrete instances ----- *)

  Definition inb (z : nat) (l : list nat) : bool := if in_dec Nat.eq_dec z l then true else false.

  Fixpoint treebR (r : nat) (l : list (@edge G)) : bool :=
    match l with
    | [] => true
    | (u, v, _) :: rest =>
        treebR r rest &&
        ((inb u (r :: verts (rev rest)) && negb (inb v (r :: verts (rev rest)))) ||
         (inb v (r :: verts (rev rest)) && negb (inb u (r :: verts (rev rest)))))
    end.

  Definition treeb (r : nat) (T : list (@edge G)) : bool := treebR r (rev T).

  Lemma treeb_sound : forall T r, treeb r T = true -> tree r T.
  Proof.
    intro T. induction T as [| x T IH] using rev_ind; intros r H; [apply t_nil |].
    destruct x as [[u v] g]. unfold treeb in H. rewrite rev_app_distr in H. simpl in H.
    rewrite rev_involutive in H. apply andb_prop in H. destruct H as [H1 H2].
    pose proof (IH r H1) as HT. unfold inb in H2.
    destruct (in_dec Nat.eq_dec u (r :: verts T)) as [Hu | Hu];
      destruct (in_dec Nat.eq_dec v (r :: verts T)) as [Hv | Hv]; simpl in H2; try discriminate H2.
    - apply t_out; assumption.
    - apply t_in; assumption.
  Qed.

  Definition spansb (r : nat) (T X : list (@edge G)) : bool :=
    forallb (fun x => let '(u, v, _) := x in inb u (r :: verts T) && inb v (r :: verts T)) X.

  Lemma spansb_sound : forall r T X, spansb r T X = true -> spans r T X.
  Proof.
    intros r T X H u v g Hx. unfold spansb in H. rewrite forallb_forall in H.
    specialize (H _ Hx). simpl in H. apply andb_prop in H. destruct H as [H1 H2]. unfold inb in *.
    destruct (in_dec Nat.eq_dec u (r :: verts T)); [| discriminate H1].
    destruct (in_dec Nat.eq_dec v (r :: verts T)); [| discriminate H2].
    split; assumption.
  Qed.

  Fixpoint rem1 (x : @edge G) (l : list (@edge G)) : option (list (@edge G)) :=
    match l with
    | [] => None
    | y :: t => if ed_dec x y then Some t else option_map (cons y) (rem1 x t)
    end.

  Lemma rem1_perm : forall x l l', rem1 x l = Some l' -> Permutation l (x :: l').
  Proof.
    intros x l. induction l as [| y t IH]; intros l' H; simpl in H; [discriminate H |].
    destruct (ed_dec x y) as [-> | Hne].
    - injection H as <-. apply Permutation_refl.
    - destruct (rem1 x t) as [t' |] eqn:E; simpl in H; [| discriminate H].
      injection H as <-. apply (Permutation_trans (perm_skip y (IH t' eq_refl))). apply perm_swap.
  Qed.

  Fixpoint permb (l l' : list (@edge G)) : bool :=
    match l with
    | [] => match l' with [] => true | _ => false end
    | x :: t => match rem1 x l' with Some l'' => permb t l'' | None => false end
    end.

  Lemma permb_sound : forall l l', permb l l' = true -> Permutation l l'.
  Proof.
    intro l. induction l as [| x t IH]; intros l' H; simpl in H.
    - destruct l'; [constructor | discriminate H].
    - destruct (rem1 x l') as [l'' |] eqn:E; [| discriminate H].
      apply Permutation_sym. apply (Permutation_trans (rem1_perm x l' l'' E)).
      apply perm_skip. apply Permutation_sym. apply IH. exact H.
  Qed.

  Definition planb (Es : list (@edge G)) (r : nat) (T X : list (@edge G)) : bool :=
    treeb r T && spansb r T X && permb Es (T ++ X).

  Lemma planb_sound : forall Es r T X, planb Es r T X = true -> plan Es r T X.
  Proof.
    intros Es r T X H. unfold planb in H. apply andb_prop in H. destruct H as [H H3].
    apply andb_prop in H. destruct H as [H1 H2].
    split; [exact (treeb_sound T r H1) | split; [exact (permb_sound _ _ H3) | exact (spansb_sound r T X H2)]].
  Qed.

  Lemma section_check : forall s es, forallb (balb s) es = true -> is_section op s es.
  Proof.
    intros s es H x Hx. rewrite forallb_forall in H. apply balb_true. exact (H x Hx).
  Qed.
End Checkers.

(* ===================================================================== *)
(* The plan model and feasible coordination, for any group.              *)

Section PlanMin.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.
  Hypothesis G_eq_dec : forall a b : G, {a = b} + {a <> b}.
  Set Default Proof Using "All".

  (* ----- the computed tree section ----- *)

  (* Grown along the tree from its last edge backward, as CoordinatedCycles.ruleR: each edge sets
     its fresh endpoint from the other one, the root keeps the identity. *)
  Fixpoint tsecR (r : nat) (l : list (@edge G)) : nat -> G :=
    match l with
    | [] => fun _ => e
    | (u, v, g) :: rest =>
        if in_dec Nat.eq_dec v (r :: verts (rev rest))
        then upd (tsecR r rest) u (op (inv g) (tsecR r rest v))
        else upd (tsecR r rest) v (op g (tsecR r rest u))
    end.

  Definition tsec (r : nat) (T : list (@edge G)) : nat -> G := tsecR r (rev T).

  Lemma tsec_snoc :
    forall r es u v g,
      tsec r (es ++ [(u, v, g)]) =
      if in_dec Nat.eq_dec v (r :: verts es)
      then upd (tsec r es) u (op (inv g) (tsec r es v))
      else upd (tsec r es) v (op g (tsec r es u)).
  Proof. intros. unfold tsec. rewrite rev_app_distr. simpl. rewrite rev_involutive. reflexivity. Qed.

  Lemma tsec_section : forall r T, tree r T -> is_section op (tsec r T) T.
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu].
    - intros x [].
    - rewrite tsec_snoc. destruct (in_dec Nat.eq_dec v (r :: verts es)) as [H | _]; [contradiction |].
      apply section_app. split.
      + apply section_upd_fresh; [exact IH |]. intro H. apply Hv. right. exact H.
      + intros x [<- | []]. unfold sat.
        rewrite upd_same, upd_other; [reflexivity |].
        intro E. subst. apply Hv. exact Hu.
    - rewrite tsec_snoc. destruct (in_dec Nat.eq_dec v (r :: verts es)) as [_ | H]; [| contradiction].
      apply section_app. split.
      + apply section_upd_fresh; [exact IH |]. intro H. apply Hu. right. exact H.
      + intros x [<- | []]. unfold sat.
        rewrite upd_same, upd_other; [| intro E; subst; apply Hu; exact Hv].
        rewrite assoc, inv_r, id_l. reflexivity.
  Qed.

  Definition coord (r : nat) (T X : list (@edge G)) : list (@edge G) :=
    filter (fun x => negb ((balb op G_eq_dec) (tsec r T) x)) X.

  Definition kept (r : nat) (T X : list (@edge G)) : list (@edge G) :=
    filter ((balb op G_eq_dec) (tsec r T)) X.

  Definition plan_cost (r : nat) (T X : list (@edge G)) : nat := length (coord r T X).

  Lemma coord_unbalanced :
    forall r T X x, In x (coord r T X) -> In x X /\ ~ sat op (tsec r T) x.
  Proof.
    intros r T X x H. unfold coord in H. apply filter_In in H. destruct H as [Hx Hb].
    split; [exact Hx |]. apply (balb_false op G_eq_dec). destruct ((balb op G_eq_dec) (tsec r T) x); [discriminate Hb | reflexivity].
  Qed.

  Lemma kept_balanced :
    forall r T X x, In x (kept r T X) -> In x X /\ sat op (tsec r T) x.
  Proof.
    intros r T X x H. unfold kept in H. apply filter_In in H. destruct H as [Hx Hb].
    split; [exact Hx | apply (balb_true op G_eq_dec); exact Hb].
  Qed.

  (* The cost does not depend on which tree section is used (balance is static). *)
  Theorem plan_cost_any_section :
    forall Es r T X s, plan Es r T X -> is_section op s T ->
      plan_cost r T X = length (filter (fun x => negb ((balb op G_eq_dec) s x)) X).
  Proof.
    intros Es r T X s [HT [_ Hsp]] Hs. unfold plan_cost, coord. f_equal.
    apply cm_filter_ext_in. intros [[u v] g] Hx. destruct (Hsp u v g Hx) as [Hu Hv].
    pose proof (tsec_section r T HT) as Ht.
    destruct ((balb op G_eq_dec) (tsec r T) (u, v, g)) eqn:E1; destruct ((balb op G_eq_dec) s (u, v, g)) eqn:E2;
      try reflexivity; exfalso.
    - apply (balb_true op G_eq_dec) in E1. apply (balb_false op G_eq_dec) in E2. apply E2.
      exact (balanced_any_section op e inv assoc id_l inv_r inv_l r T _ s u v g HT Ht Hs Hu Hv E1).
    - apply (balb_true op G_eq_dec) in E2. apply (balb_false op G_eq_dec) in E1. apply E1.
      exact (balanced_any_section op e inv assoc id_l inv_r inv_l r T s _ u v g HT Hs Ht Hu Hv E2).
  Qed.

  (* The plan's cost is at most the number of non-tree edges (the first Betti number). *)
  Theorem plan_cost_le_betti : forall r T X, plan_cost r T X <= length X.
  Proof. intros r T X. apply cm_filter_len_le. Qed.

  (* ----- direction 1: every plan's coordinated set is feasible, and exactly needed ----- *)

  Theorem plan_coord_feasible :
    forall Es r T X, plan Es r T X ->
      feasibleM op Es (coord r T X) /\ has_section op (T ++ kept r T X) /\
      Permutation Es ((T ++ kept r T X) ++ coord r T X).
  Proof.
    intros Es r T X [HT [HP Hsp]].
    assert (Hperm : Permutation Es ((T ++ kept r T X) ++ coord r T X)).
    { rewrite <- app_assoc. apply (Permutation_trans HP). apply Permutation_app_head.
      unfold kept, coord. apply cm_perm_partition. }
    assert (Hsec : has_section op (T ++ kept r T X)).
    { apply (keep_balanced_suffices op T (kept r T X) (tsec r T) (tsec_section r T HT)).
      intros x Hx. exact (proj2 (kept_balanced r T X x Hx)). }
    split; [exists (T ++ kept r T X); split; assumption | split; assumption].
  Qed.

  (* plan_exact for the computed split: a set of non-tree edges can be kept with a section iff it
     avoids the coordinated set. *)
  Theorem plan_coord_exact :
    forall Es r T X, plan Es r T X ->
      forall K, incl K X -> (has_section op (T ++ K) <-> forall x, In x K -> ~ In x (coord r T X)).
  Proof.
    intros Es r T X [HT [HP Hsp]] K HK.
    apply (plan_exact op e inv assoc id_l id_r inv_r inv_l r T (kept r T X) (coord r T X) (tsec r T)
             HT (tsec_section r T HT)).
    - intros u v g H. apply in_app_or in H. apply (Hsp u v g).
      destruct H as [H | H]; [exact (proj1 (kept_balanced r T X _ H)) | exact (proj1 (coord_unbalanced r T X _ H))].
    - intros x Hx. exact (proj2 (kept_balanced r T X x Hx)).
    - intros x Hx. exact (proj2 (coord_unbalanced r T X x Hx)).
    - intros x Hx. apply in_or_app. pose proof (HK x Hx) as HxX.
      destruct ((balb op G_eq_dec) (tsec r T) x) eqn:E.
      + left. unfold kept. apply filter_In. split; assumption.
      + right. unfold coord. apply filter_In. split; [exact HxX | rewrite E; reflexivity].
  Qed.

  (* Deciding a section relative to a tree: the computed tree section satisfies every extra edge. *)
  Theorem section_decide :
    forall r T X, tree r T -> spans r T X ->
      (has_section op (T ++ X) <-> forallb ((balb op G_eq_dec) (tsec r T)) X = true).
  Proof.
    intros r T X HT Hsp.
    rewrite (cycle_basis_criterion op e inv assoc id_l id_r inv_r inv_l r T X (tsec r T) HT
               (tsec_section r T HT) Hsp).
    rewrite forallb_forall. split; intros H x Hx; apply (balb_true op G_eq_dec); apply H; exact Hx.
  Qed.

  (* ----- direction 2: from a feasible set to a plan, by gauge freedom ----- *)

  (* Multiply a state on the right by one constant outside V. *)
  Definition resc (t : nat -> G) (V : list nat) (c : G) : nat -> G :=
    fun z => if in_dec Nat.eq_dec z V then t z else op (t z) c.

  Lemma resc_section :
    forall t V c es, is_section op t es -> (forall y, In y es -> ~ cross V y) ->
      is_section op (resc t V c) es.
  Proof.
    intros t V c es Ht Hn [[u v] g] Hin. pose proof (Ht _ Hin) as E. pose proof (Hn _ Hin) as Hc.
    unfold sat in *. unfold resc. simpl in Hc.
    destruct (in_dec Nat.eq_dec u V) as [Hu | Hu]; destruct (in_dec Nat.eq_dec v V) as [Hv | Hv].
    - exact E.
    - exfalso. apply Hc. left. split; assumption.
    - exfalso. apply Hc. right. split; assumption.
    - rewrite assoc, E. reflexivity.
  Qed.

  Lemma tree_no_cross :
    forall r (T : list (@edge G)) y, In y T -> ~ cross (r :: verts T) y.
  Proof.
    intros r T [[u v] g] Hy. destruct (in_verts_edge T u v g Hy) as [Hu Hv].
    simpl. intros [[_ H] | [_ H]]; apply H; right; assumption.
  Qed.

  (* One step: attach a crossing edge of the network to the tree. *)
  Lemma attach :
    forall (Es : list (@edge G)) L r (T X : list (@edge G)) y,
      (forall u v g, In (u, v, g) Es -> In u L /\ In v L) ->
      tree r T -> Permutation Es (T ++ X) -> In y Es -> cross (r :: verts T) y ->
      exists X1, Permutation Es ((T ++ [y]) ++ X1) /\ tree r (T ++ [y]) /\
                 outside (r :: verts (T ++ [y])) L < outside (r :: verts T) L.
  Proof.
    intros Es L r T X [[u v] g] Hcov HT HP Hy Hc.
    assert (HyX : In (u, v, g) X).
    { apply (Permutation_in _ HP) in Hy. apply in_app_or in Hy. destruct Hy as [Hy | Hy]; [| exact Hy].
      exfalso. exact (tree_no_cross r T _ Hy Hc). }
    destruct (in_split _ _ HyX) as [X1 [X2 EX]]. subst X.
    exists (X1 ++ X2). split; [| split].
    - apply (Permutation_trans HP). rewrite <- app_assoc. apply Permutation_app_head.
      simpl. apply Permutation_sym. apply Permutation_middle.
    - simpl in Hc. destruct Hc as [[Hu Hv] | [Hv Hu]]; [apply t_out | apply t_in]; assumption.
    - destruct (Hcov u v g Hy) as [HuL HvL].
      assert (Hinc : incl (r :: verts T) (r :: verts (T ++ [(u, v, g)])))
        by (intros w Hw; apply verts_snoc_intro; left; exact Hw).
      simpl in Hc. destruct Hc as [[Hu Hv] | [Hv Hu]].
      + apply (outside_lt _ _ L v Hinc HvL Hv). apply verts_snoc_intro. right. right. reflexivity.
      + apply (outside_lt _ _ L u Hinc HuL Hu). apply verts_snoc_intro. right. left. reflexivity.
  Qed.

  (* Grow a spanning tree from r preferring edges of K, keeping a section of T ++ K. *)
  Lemma grow :
    forall (Es K : list (@edge G)) L r (T0 : list (@edge G)),
      tree r T0 -> incl T0 Es -> incl K Es ->
      (forall u v g, In (u, v, g) Es -> In u L /\ In v L) ->
      (forall z, In z L -> In z (r :: verts T0)) ->
      forall n (T X : list (@edge G)), tree r T -> Permutation Es (T ++ X) -> has_section op (T ++ K) ->
        outside (r :: verts T) L < n ->
        exists T' X', tree r T' /\ Permutation Es (T' ++ X') /\ has_section op (T' ++ K) /\
                      (forall z, In z L -> In z (r :: verts T')).
  Proof.
    intros Es K L r T0 HT0 HT0E HKE Hcov HL0 n.
    induction n as [| n IH]; intros T X HT HP [t Ht] Hn; [lia |].
    destruct (proj1 (section_app op t T K) Ht) as [HtT HtK].
    destruct (cross_dec_list (r :: verts T) K) as [[y [HyK Hc]] | HnoK].
    - (* an edge of K leaves the tree: attach it, the section is unchanged *)
      destruct (attach Es L r T X y Hcov HT HP (HKE y HyK) Hc) as [X1 [HP1 [HT1 Hlt]]].
      apply (IH (T ++ [y]) X1 HT1 HP1); [| lia].
      exists t. apply section_app. split; [apply section_app; split | exact HtK].
      + exact HtT.
      + intros x [<- | []]. exact (HtK y HyK).
    - destruct (cross_dec_list (r :: verts T) Es) as [[y [HyE Hc]] | HnoE].
      + (* only edges of F leave: attach one, rescaling everything not yet reached *)
        destruct (attach Es L r T X y Hcov HT HP HyE Hc) as [X1 [HP1 [HT1 Hlt]]].
        apply (IH (T ++ [y]) X1 HT1 HP1); [| lia].
        assert (Hnc : forall c, is_section op (resc t (r :: verts T) c) (T ++ K)).
        { intro c. apply resc_section; [exact Ht |].
          intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx];
            [exact (tree_no_cross r T x Hx) | exact (HnoK x Hx)]. }
        destruct y as [[u v] g]. simpl in Hc. destruct Hc as [[Hu Hv] | [Hv Hu]].
        * exists (resc t (r :: verts T) (op (inv (t v)) (op g (t u)))).
          destruct (proj1 (section_app _ _ _ _) (Hnc (op (inv (t v)) (op g (t u))))) as [H1 H2].
          apply section_app. split; [apply section_app; split | exact H2]; [exact H1 |].
          intros x [<- | []]. unfold sat, resc.
          destruct (in_dec Nat.eq_dec u (r :: verts T)) as [_ | H]; [| contradiction].
          destruct (in_dec Nat.eq_dec v (r :: verts T)) as [H | _]; [contradiction |].
          rewrite assoc, inv_r, id_l. reflexivity.
        * exists (resc t (r :: verts T) (op (inv (t u)) (op (inv g) (t v)))).
          destruct (proj1 (section_app _ _ _ _) (Hnc (op (inv (t u)) (op (inv g) (t v))))) as [H1 H2].
          apply section_app. split; [apply section_app; split | exact H2]; [exact H1 |].
          intros x [<- | []]. unfold sat, resc.
          destruct (in_dec Nat.eq_dec u (r :: verts T)) as [H | _]; [contradiction |].
          destruct (in_dec Nat.eq_dec v (r :: verts T)) as [_ | H]; [| contradiction].
          rewrite (assoc (t u)), inv_r, id_l, assoc, inv_r, id_l. reflexivity.
      + (* nothing leaves: the tree already spans *)
        exists T, X. split; [exact HT | split; [exact HP | split; [exists t; exact Ht |]]].
        intros z Hz. destruct (in_dec Nat.eq_dec z (r :: verts T)) as [H | H]; [exact H |].
        exfalso. destruct (tree_cross r T0 HT0 (r :: verts T) (or_introl eq_refl) z (HL0 z Hz) H)
          as [y [Hy Hc]].
        exact (HnoE y (HT0E y Hy) Hc).
  Qed.

  (* The converse direction: every feasible coordination is matched by a plan, rooted at the same
     authority, whose coordinated set is no larger. No connectivity of the residual is assumed. *)
  Theorem feasible_plan :
    forall Es r T0 X0 F, plan Es r T0 X0 -> feasibleM op Es F ->
      exists T X, plan Es r T X /\ plan_cost r T X <= length F.
  Proof.
    intros Es r T0 X0 F Hpl [K [HPK HsK]].
    destruct Hpl as [HT0 [HP0 Hsp0]].
    pose proof ((plan_covers op G_eq_dec) Es r T0 X0 (conj HT0 (conj HP0 Hsp0))) as Hcov.
    destruct ((perm_incl op G_eq_dec) _ _ _ HP0) as [HT0E _]. destruct ((perm_incl op G_eq_dec) _ _ _ HPK) as [HKE _].
    destruct (grow Es K (r :: verts T0) r T0 HT0 HT0E HKE Hcov (fun z H => H)
                (S (length (r :: verts T0))) [] Es (t_nil r) (Permutation_refl Es) HsK)
      as [T [X [HT [HP [[t Ht] Hspan]]]]].
    { pose proof (outside_le (r :: @verts G []) (r :: verts T0)). lia. }
    destruct (proj1 (section_app op t T K) Ht) as [HtT HtK].
    assert (Hsp : spans r T X).
    { intros u v g Hx. apply ((perm_incl op G_eq_dec) _ _ _ HP) in Hx. destruct (Hcov u v g Hx) as [Hu Hv].
      split; apply Hspan; assumption. }
    exists T, X. split; [split; [exact HT | split; [exact HP | exact Hsp]] |].
    pose (notK := fun x : @edge G => if in_dec (ed_dec G_eq_dec) x K then false else true).
    assert (H1 : plan_cost r T X <= length (filter notK X)).
    { unfold plan_cost, coord. apply cm_filter_mono. intros [[u v] g] Hx Hb. unfold notK.
      destruct (in_dec (ed_dec G_eq_dec) (u, v, g) K) as [HK | _]; [| reflexivity].
      exfalso. destruct (Hsp u v g Hx) as [Hu Hv].
      pose proof (balanced_any_section op e inv assoc id_l inv_r inv_l r T t (tsec r T) u v g HT HtT
                    (tsec_section r T HT) Hu Hv (HtK _ HK)) as Hs.
      apply (balb_true op G_eq_dec) in Hs. rewrite Hs in Hb. discriminate Hb. }
    assert (H2 : length (filter notK X) <= length (filter notK Es)).
    { rewrite (cm_filter_perm_len _ notK _ _ HP), cm_filter_app, cm_len_app. lia. }
    assert (H3 : length (filter notK Es) <= length F).
    { rewrite (cm_filter_perm_len _ notK _ _ HPK), cm_filter_app, cm_len_app.
      rewrite (cm_filter_none _ notK K); [simpl; apply cm_filter_len_le |].
      intros x Hx. unfold notK. destruct (in_dec (ed_dec G_eq_dec) x K); [reflexivity | contradiction]. }
    lia.
  Qed.

  (* ----- the minimum ----- *)

  (* For a connected network (some plan rooted at r exists) and every k: some plan rooted at r
     coordinates at most k edges iff some feasible coordination deletes at most k edges. So the
     minimum over rooted spanning trees of the plan cost is the minimum feasible coordination (the
     group feedback edge set number), for every authority root. *)
  Theorem plan_min_exact :
    forall Es r, (exists T0 X0, plan Es r T0 X0) ->
      forall k, (exists T X, plan Es r T X /\ plan_cost r T X <= k) <->
                (exists F, feasibleM op Es F /\ length F <= k).
  Proof.
    intros Es r [T0 [X0 H0]] k. split.
    - intros [T [X [Hp Hc]]]. exists (coord r T X).
      split; [exact (proj1 (plan_coord_feasible Es r T X Hp)) | exact Hc].
    - intros [F [HF Hk]]. destruct (feasible_plan Es r T0 X0 F H0 HF) as [T [X [Hp Hc]]].
      exists T, X. split; [exact Hp | lia].
  Qed.

  (* The optimum does not depend on the authority root: any two roots of a connected network admit
     plans of the same minimum cost (the root still matters for the normal form,
     CoordinatedCycles.root_choice_matters, but not for how much must be coordinated). *)
  Theorem plan_min_root_independent :
    forall Es r r', (exists T0 X0, plan Es r T0 X0) -> (exists T1 X1, plan Es r' T1 X1) ->
      forall k, (exists T X, plan Es r T X /\ plan_cost r T X <= k) <->
                (exists T X, plan Es r' T X /\ plan_cost r' T X <= k).
  Proof.
    intros Es r r' H H' k. rewrite (plan_min_exact Es r H k), (plan_min_exact Es r' H' k).
    reflexivity.
  Qed.

  (* Lower bounds transfer both ways. *)
  Theorem plan_min_lower_iff :
    forall Es r, (exists T0 X0, plan Es r T0 X0) ->
      forall k, (forall T X, plan Es r T X -> k <= plan_cost r T X) <->
                (forall F, feasibleM op Es F -> k <= length F).
  Proof.
    intros Es r [T0 [X0 H0]] k. split.
    - intros H F HF. destruct (feasible_plan Es r T0 X0 F H0 HF) as [T [X [Hp Hc]]].
      specialize (H T X Hp). lia.
    - intros H T X Hp. apply H. exact (proj1 (plan_coord_feasible Es r T X Hp)).
  Qed.

  (* A minimum feasible coordination is attained by a plan, which is optimal among all plans. *)
  Theorem plan_min_attained :
    forall Es r T0 X0 F, plan Es r T0 X0 -> feasibleM op Es F ->
      (forall F', feasibleM op Es F' -> length F <= length F') ->
      exists T X, plan Es r T X /\ plan_cost r T X = length F /\ feasibleM op Es (coord r T X) /\
                  (forall T' X', plan Es r T' X' -> plan_cost r T X <= plan_cost r T' X').
  Proof.
    intros Es r T0 X0 F H0 HF Hmin.
    destruct (feasible_plan Es r T0 X0 F H0 HF) as [T [X [Hp Hc]]].
    pose proof (proj1 (plan_coord_feasible Es r T X Hp)) as Hfe.
    pose proof (Hmin _ Hfe) as Hge. unfold plan_cost in Hc, Hge.
    exists T, X. split; [exact Hp |]. split; [unfold plan_cost; lia |]. split; [exact Hfe |].
    intros T' X' Hp'. pose proof (Hmin _ (proj1 (plan_coord_feasible Es r T' X' Hp'))) as H'.
    unfold plan_cost in *. lia.
  Qed.

  (* On a duplicate-free connected network the same iff holds with CohomologyGeneral.feasible. *)
  Theorem plan_min_exact_set :
    forall Es r, NoDup Es -> (exists T0 X0, plan Es r T0 X0) ->
      forall k, (exists T X, plan Es r T X /\ plan_cost r T X <= k) <->
                (exists D, feasible op Es D /\ length D <= k).
  Proof.
    intros Es r Hnd Hc k. rewrite (plan_min_exact Es r Hc k). split.
    - intros [F [HF Hk]]. exists F. split; [exact ((feasibleM_feasible op G_eq_dec) Es F HF) | exact Hk].
    - intros [D [HD Hk]]. destruct ((feasible_feasibleM op G_eq_dec) Es D Hnd HD) as [F [HF Hl]].
      exists F. split; [exact HF | lia].
  Qed.

  (* edge_disjoint_lower_bound recovered for every plan: k edge-disjoint obstructing cycles force
     every plan to coordinate at least k edges, whatever the tree and root. *)
  Theorem plan_cost_ge_disjoint :
    forall Es Cs, edge_disjoint Cs ->
      (forall C, In C Cs -> incl C Es /\ ~ has_section op C) ->
      forall r T X, plan Es r T X -> length Cs <= plan_cost r T X.
  Proof.
    intros Es Cs Hd HC r T X Hp. unfold plan_cost.
    apply (edge_disjoint_lower_bound op (ed_dec G_eq_dec) Es Cs Hd HC).
    apply (feasibleM_feasible op G_eq_dec). exact (proj1 (plan_coord_feasible Es r T X Hp)).
  Qed.

End PlanMin.

(* ===================================================================== *)
(* The hypotheses are needed.                                              *)

(* Connectivity: two disjoint edges. Deleting nothing is feasible, but no tree rooted anywhere spans
   both edges, so no plan exists and the tree form of plan_min_exact fails for k = 0. *)
Definition disc_es : list (@edge bool) := [(0, 1, false); (2, 3, false)].

Theorem plan_min_connected_needed :
  feasibleM xorb disc_es [] /\
  (forall r T X, ~ plan disc_es r T X) /\
  ~ (forall r k, (exists T X, plan disc_es r T X /\ plan_cost xorb false (fun a => a) bool_dec r T X <= k) <->
                  (exists F, feasibleM xorb disc_es F /\ length F <= k)).
Proof.
  assert (Hf : feasibleM xorb disc_es []).
  { exists disc_es. split; [rewrite app_nil_r; apply Permutation_refl |].
    exists (fun _ => false). intros x Hx. simpl in Hx.
    destruct Hx as [<- | [<- | []]]; reflexivity. }
  assert (Hno : forall r T X, ~ plan disc_es r T X).
  { intros r T X Hp. pose proof (plan_covers xorb bool_dec disc_es r T X Hp) as Hcov.
    destruct Hp as [HT [HP _]].
    destruct (tree_vertex_count r T HT) as [vs [Hnd [Hin Hlen]]].
    assert (Hl : length T <= 2).
    { apply Permutation_length in HP. rewrite cm_len_app in HP. simpl in HP. lia. }
    assert (Hinc : incl [0; 1; 2; 3] vs).
    { intros z Hz. apply Hin. simpl in Hz.
      destruct Hz as [<- | [<- | [<- | [<- | []]]]].
      - exact (proj1 (Hcov 0 1 false (or_introl eq_refl))).
      - exact (proj2 (Hcov 0 1 false (or_introl eq_refl))).
      - exact (proj1 (Hcov 2 3 false (or_intror (or_introl eq_refl)))).
      - exact (proj2 (Hcov 2 3 false (or_intror (or_introl eq_refl)))). }
    assert (H4 : length [0; 1; 2; 3] <= length vs).
    { apply NoDup_incl_length; [| exact Hinc].
      repeat constructor; simpl; intuition discriminate. }
    simpl in H4. lia. }
  split; [exact Hf | split; [exact Hno |]].
  intro H. destruct (proj2 (H 0 0) (ex_intro _ [] (conj Hf (le_n 0)))) as [T [X [Hp _]]].
  exact (Hno 0 T X Hp).
Qed.

(* Duplicate-freeness for deletion by membership: two copies each of the flip and the identity
   between 0 and 1. Deleting the flip (one list entry, both copies) is feasible, yet every plan
   coordinates at least two edges, because every feasible sub-multiset has two entries. *)
Definition dup_x : @edge bool := (0, 1, true).
Definition dup_y : @edge bool := (0, 1, false).
Definition dup_es : list (@edge bool) := [dup_y; dup_x; dup_x; dup_y].

Lemma dup_no_section : forall K, In dup_x K -> In dup_y K -> ~ has_section xorb K.
Proof.
  intros K Hx Hy [s Hs]. pose proof (Hs _ Hx) as E1. pose proof (Hs _ Hy) as E2.
  unfold sat, dup_x, dup_y in E1, E2. destruct (s 0), (s 1); simpl in *; discriminate.
Qed.

Lemma dup_feasibleM_ge2 : forall F, feasibleM xorb dup_es F -> 2 <= length F.
Proof.
  intros F [K [HP Hs]].
  destruct F as [| z [| z' F]]; [| | simpl; lia]; exfalso.
  - rewrite app_nil_r in HP.
    apply (dup_no_section K); [| | exact Hs]; apply (Permutation_in _ HP); simpl; auto.
  - assert (Hz : In z dup_es)
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; left; reflexivity).
    assert (HP' : Permutation (z :: K) dup_es)
      by (apply (Permutation_trans (Permutation_cons_append K z)); apply Permutation_sym; exact HP).
    simpl in Hz. destruct Hz as [<- | [<- | [<- | [<- | []]]]].
    + pose proof (@Permutation_cons_app_inv _ K [] [dup_x; dup_x; dup_y] _ HP') as HK.
      apply (dup_no_section K); [| | exact Hs]; apply (Permutation_in _ (Permutation_sym HK)); simpl; auto.
    + pose proof (@Permutation_cons_app_inv _ K [dup_y] [dup_x; dup_y] _ HP') as HK.
      apply (dup_no_section K); [| | exact Hs]; apply (Permutation_in _ (Permutation_sym HK)); simpl; auto.
    + pose proof (@Permutation_cons_app_inv _ K [dup_y] [dup_x; dup_y] _ HP') as HK.
      apply (dup_no_section K); [| | exact Hs]; apply (Permutation_in _ (Permutation_sym HK)); simpl; auto.
    + pose proof (@Permutation_cons_app_inv _ K [] [dup_x; dup_x; dup_y] _ HP') as HK.
      apply (dup_no_section K); [| | exact Hs]; apply (Permutation_in _ (Permutation_sym HK)); simpl; auto.
Qed.

Theorem plan_min_nodup_needed :
  ~ NoDup dup_es /\
  plan dup_es 0 [dup_y] [dup_x; dup_x; dup_y] /\
  feasible xorb dup_es [dup_x] /\
  (forall T X, plan dup_es 0 T X -> 2 <= plan_cost xorb false (fun a => a) bool_dec 0 T X) /\
  ~ (forall k, (exists T X, plan dup_es 0 T X /\ plan_cost xorb false (fun a => a) bool_dec 0 T X <= k) <->
               (exists D, feasible xorb dup_es D /\ length D <= k)).
Proof.
  assert (Hp : plan dup_es 0 [dup_y] [dup_x; dup_x; dup_y])
    by (apply (planb_sound xorb bool_dec); vm_compute; reflexivity).
  assert (Hlow : forall T X, plan dup_es 0 T X -> 2 <= plan_cost xorb false (fun a => a) bool_dec 0 T X).
  { apply (plan_min_lower_iff xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
             bool_dec dup_es 0 (ex_intro _ _ (ex_intro _ _ Hp)) 2).
    exact dup_feasibleM_ge2. }
  assert (Hf : feasible xorb dup_es [dup_x]).
  { exists (fun _ => false). intros x Hx Hnx. simpl in Hx.
    destruct Hx as [<- | [<- | [<- | [<- | []]]]]; try reflexivity; exfalso; apply Hnx; left; reflexivity. }
  split; [| split; [exact Hp | split; [exact Hf | split; [exact Hlow |]]]].
  - intro H. inversion H as [| a l Ha Hl]. apply Ha. right. right. left. reflexivity.
  - intro H. destruct (proj2 (H 1) (ex_intro _ [dup_x] (conj Hf (le_n 1)))) as [T [X [Hp' Hc]]].
    specialize (Hlow T X Hp'). lia.
Qed.

(* ===================================================================== *)
(* Complexity: the Max-Cut reduction (Z/2, every edge the flip).          *)

Definition cut_count (s : nat -> bool) (H : list (nat * nat)) : nat :=
  length (filter (fun p => xorb (s (fst p)) (s (snd p))) H).

Definition signed (H : list (nat * nat)) : list (@edge bool) := map (fun p => (fst p, snd p, true)) H.

Definition cutE (s : nat -> bool) (x : @edge bool) : bool := let '(u, v, _) := x in xorb (s u) (s v).

Lemma cut_count_signed : forall s H, cut_count s H = length (filter (cutE s) (signed H)).
Proof.
  intros s H. unfold cut_count, signed. induction H as [| [u v] H IH]; simpl; [reflexivity |].
  destruct (xorb (s u) (s v)); simpl; rewrite IH; reflexivity.
Qed.

Lemma signed_true : forall H u v g, In (u, v, g) (signed H) -> g = true.
Proof.
  intros H u v g Hin. unfold signed in Hin. apply in_map_iff in Hin.
  destruct Hin as [[a b] [E _]]. simpl in E. injection E as _ _ Eg. symmetry. exact Eg.
Qed.

(* Size: the reduction keeps the vertices and the number of edges. *)
Theorem signed_size :
  forall H, length (signed H) = length H /\ (forall u v g, In (u, v, g) (signed H) -> g = true) /\
            (forall u v, In (u, v) H <-> In (u, v, true) (signed H)).
Proof.
  intro H. split; [apply cg_len_map |]. split; [exact (signed_true H) |].
  intros u v. unfold signed. split.
  - intro Hin. apply (in_map (fun p => (fst p, snd p, true))) in Hin. exact Hin.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[a b] [E Hab]]. simpl in E.
    injection E as Ea Eb. subst. exact Hab.
Qed.

(* Correctness: a coordination deleting |F| edges with |F| + k <= |H| exists iff H has a cut of at
   least k edges. So the minimum coordination of signed H is |H| minus the maximum cut. *)
Theorem maxcut_reduction :
  forall H k, (exists F, feasibleM xorb (signed H) F /\ length F + k <= length H) <->
              (exists s, k <= cut_count s H).
Proof.
  intros H k. split.
  - intros [F [[K [HP [s Hs]]] Hk]]. exists s.
    pose proof (Permutation_length HP) as Hl. rewrite cm_len_app in Hl. unfold signed in Hl.
    rewrite cg_len_map in Hl.
    rewrite cut_count_signed, (cm_filter_perm_len _ (cutE s) _ _ HP), cm_filter_app, cm_len_app.
    rewrite (cm_filter_all _ (cutE s) K); [lia |].
    intros [[u v] g] Hx. pose proof (Hs _ Hx) as E. unfold sat in E. simpl.
    assert (Hg : g = true).
    { apply (signed_true H u v g). apply (Permutation_in _ (Permutation_sym HP)).
      apply in_or_app. left. exact Hx. }
    subst g. destruct (s u), (s v); simpl in *; congruence.
  - intros [s Hk]. exists (filter (fun x => negb (cutE s x)) (signed H)). split.
    + exists (filter (cutE s) (signed H)). split; [apply cm_perm_partition |].
      exists s. intros [[u v] g] Hx. apply filter_In in Hx. destruct Hx as [Hx Hc].
      rewrite (signed_true H u v g Hx). unfold sat. simpl in Hc.
      destruct (s u), (s v); simpl in *; congruence.
    + pose proof (Permutation_length (cm_perm_partition _ (cutE s) (signed H))) as Hl.
      rewrite cm_len_app in Hl. rewrite cut_count_signed in Hk. unfold signed in Hl at 1.
      rewrite cg_len_map in Hl. lia.
Qed.

(* The same for the plan model, when signed H is connected. *)
Theorem maxcut_plan_reduction :
  forall H r, (exists T0 X0, plan (signed H) r T0 X0) ->
    forall k, (exists T X, plan (signed H) r T X /\
                           plan_cost xorb false (fun a => a) bool_dec r T X + k <= length H) <->
              (exists s, k <= cut_count s H).
Proof.
  intros H r [T0 [X0 H0]] k. rewrite <- maxcut_reduction. split.
  - intros [T [X [Hp Hc]]]. exists (coord xorb false (fun a => a) bool_dec r T X).
    split; [exact (proj1 (plan_coord_feasible xorb false (fun a => a) xor_assoc xor_id_l xor_id_r
                            xor_inv_r xor_inv_l bool_dec _ r T X Hp)) | exact Hc].
  - intros [F [HF Hk]].
    destruct (feasible_plan xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
                bool_dec _ r T0 X0 F H0 HF) as [T [X [Hp Hc]]].
    exists T, X. split; [exact Hp | lia].
Qed.

(* Non-vacuity: the triangle has maximum cut 2, so its signed network (an odd cycle of flips)
   needs exactly one coordinated edge, and a plan attains it. *)
Definition tri_H : list (nat * nat) := [(0, 1); (1, 2); (2, 0)].

Theorem maxcut_triangle :
  (exists s, 2 <= cut_count s tri_H) /\ ~ (exists s, 3 <= cut_count s tri_H) /\
  (exists F, feasibleM xorb (signed tri_H) F /\ length F = 1) /\
  ~ (exists F, feasibleM xorb (signed tri_H) F /\ length F = 0) /\
  plan (signed tri_H) 0 [(0, 1, true); (1, 2, true)] [(2, 0, true)] /\
  plan_cost xorb false (fun a => a) bool_dec 0 [(0, 1, true); (1, 2, true)] [(2, 0, true)] = 1.
Proof.
  assert (Hcut2 : exists s, 2 <= cut_count s tri_H)
    by (exists (fun z => match z with 1 => true | _ => false end); vm_compute; lia).
  assert (Hno3 : ~ (exists s, 3 <= cut_count s tri_H)).
  { intros [s Hs]. unfold cut_count, tri_H in Hs. simpl in Hs.
    destruct (s 0), (s 1), (s 2); simpl in Hs; lia. }
  split; [exact Hcut2 | split; [exact Hno3 | split; [| split]]].
  - destruct (proj2 (maxcut_reduction tri_H 2) Hcut2) as [F [HF Hl]].
    assert (Hge : 1 <= length F).
    { destruct F as [| z F]; [| simpl; lia]. exfalso. apply Hno3.
      apply (proj1 (maxcut_reduction tri_H 3)). exists []. split; [exact HF | simpl; lia]. }
    exists F. split; [exact HF | simpl in Hl; lia].
  - intros [F [HF Hl]]. apply Hno3. apply (proj1 (maxcut_reduction tri_H 3)).
    exists F. split; [exact HF | simpl; lia].
  - split; [apply (planb_sound xorb bool_dec); vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* ===================================================================== *)
(* Instances over Z/2.                                                     *)

(* gsm's negation 2-cycle (CoordinatedCycles.v), rooted at A: the plan coordinates one edge, the
   minimum over every plan and every feasible set. *)
Definition neg_es : list (@edge bool) := cc_T ++ neg_C.

Theorem negation_plan_min :
  plan neg_es 0 cc_T neg_C /\
  plan_cost xorb false (fun a => a) bool_dec 0 cc_T neg_C = 1 /\
  (forall T X, plan neg_es 0 T X -> 1 <= plan_cost xorb false (fun a => a) bool_dec 0 T X) /\
  (forall F, feasibleM xorb neg_es F -> 1 <= length F).
Proof.
  assert (Hp : plan neg_es 0 cc_T neg_C) by (apply (planb_sound xorb bool_dec); vm_compute; reflexivity).
  assert (HF : forall F, feasibleM xorb neg_es F -> 1 <= length F).
  { intros [| z F] HF; [| simpl; lia]. exfalso.
    destruct (feasibleM_nil xorb bool_dec neg_es HF) as [s Hs].
    pose proof (Hs (0, 1, false) (or_introl eq_refl)) as E1.
    pose proof (Hs (1, 0, true) (or_intror (or_introl eq_refl))) as E2.
    unfold sat in E1, E2. destruct (s 0), (s 1); simpl in *; discriminate. }
  split; [exact Hp | split; [vm_compute; reflexivity | split; [| exact HF]]].
  apply (plan_min_lower_iff xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
           bool_dec neg_es 0 (ex_intro _ _ (ex_intro _ _ Hp)) 1). exact HF.
Qed.

(* The bowtie (CohomologyGeneral.v): two Z/2 triangles sharing vertex 0. The plan coordinates two
   edges, the minimum (bowtie_min_two), and every plan coordinates at least two. *)
Definition bow_es : list (@edge bool) := bow_T ++ bow_X.

Theorem bowtie_plan_min :
  plan bow_es 0 bow_T bow_X /\
  plan_cost xorb false (fun a => a) bool_dec 0 bow_T bow_X = 2 /\
  (forall T X, plan bow_es 0 T X -> 2 <= plan_cost xorb false (fun a => a) bool_dec 0 T X) /\
  (forall F, feasibleM xorb bow_es F -> 2 <= length F).
Proof.
  assert (Hp : plan bow_es 0 bow_T bow_X) by (apply (planb_sound xorb bool_dec); vm_compute; reflexivity).
  assert (HF : forall F, feasibleM xorb bow_es F -> 2 <= length F).
  { intros F HF. apply (proj2 bowtie_min_two). exact (feasibleM_feasible xorb bool_dec bow_es F HF). }
  split; [exact Hp | split; [vm_compute; reflexivity | split; [| exact HF]]].
  apply (plan_min_lower_iff xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
           bool_dec bow_es 0 (ex_intro _ _ (ex_intro _ _ Hp)) 2). exact HF.
Qed.

(* A disconnected residual: the negation loop with a pendant edge 1 -> 2. Deleting the negation
   edge and the pendant edge is feasible and leaves vertex 2 isolated; every spanning tree uses the
   deleted pendant edge, so the tree must be allowed to contain edges of F (feasible_plan does). *)
Definition pend_es : list (@edge bool) := [(0, 1, false); (1, 0, true); (1, 2, false)].
Definition pend_F : list (@edge bool) := [(1, 0, true); (1, 2, false)].

Theorem pendant_tree_uses_F :
  feasibleM xorb pend_es pend_F /\
  ~ In 2 (verts [(0, 1, false)]) /\
  (exists T X, plan pend_es 0 T X /\ plan_cost xorb false (fun a => a) bool_dec 0 T X <= length pend_F) /\
  (forall T X, plan pend_es 0 T X -> In (1, 2, false) T).
Proof.
  assert (HF : feasibleM xorb pend_es pend_F).
  { exists [(0, 1, false)]. split; [apply (permb_sound xorb bool_dec); vm_compute; reflexivity |].
    exists (fun _ => false). apply (section_check xorb bool_dec). vm_compute. reflexivity. }
  assert (Hp : plan pend_es 0 [(0, 1, false); (1, 2, false)] [(1, 0, true)])
    by (apply (planb_sound xorb bool_dec); vm_compute; reflexivity).
  split; [exact HF | split; [simpl; intuition discriminate | split]].
  - exact (feasible_plan xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
             bool_dec pend_es 0 _ _ pend_F Hp HF).
  - intros T X HpT. pose proof (plan_covers xorb bool_dec pend_es 0 T X HpT 1 2 false) as H2.
    destruct H2 as [_ H2]; [right; right; left; reflexivity |].
    destruct H2 as [E | H2]; [discriminate E |].
    destruct (in_verts_exists T 2 H2) as [u [v [g [Hin Hw]]]].
    destruct HpT as [_ [HP _]].
    assert (Hin' : In (u, v, g) pend_es)
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
    simpl in Hin'. destruct Hin' as [E | [E | [E | []]]]; injection E as Eu Ev Eg; subst;
      [destruct Hw as [Hw | Hw]; discriminate Hw | destruct Hw as [Hw | Hw]; discriminate Hw | exact Hin].
Qed.

(* ===================================================================== *)
(* The S_3 instance: the tree choice matters.                              *)

(* S_3 as permutations of {0, 1, 2}, given by their images; s3op is composition (apply the right
   argument first), a left action on itself (the regular action). *)
Inductive s3 : Type := s3i | s3r | s3r2 | s3a | s3b | s3c.

Definition s3_img (x : s3) : nat * nat * nat :=
  match x with
  | s3i => (0, 1, 2) | s3r => (1, 2, 0) | s3r2 => (2, 0, 1)
  | s3a => (1, 0, 2) | s3b => (0, 2, 1) | s3c => (2, 1, 0)
  end.

Definition s3_of (p : nat * nat * nat) : s3 :=
  match p with
  | (0, 1, 2) => s3i | (1, 2, 0) => s3r | (2, 0, 1) => s3r2
  | (1, 0, 2) => s3a | (0, 2, 1) => s3b | _ => s3c
  end.

Definition s3_ap (p : nat * nat * nat) (i : nat) : nat :=
  let '(x, y, z) := p in match i with 0 => x | 1 => y | _ => z end.

Definition s3op (x y : s3) : s3 :=
  s3_of (s3_ap (s3_img x) (s3_ap (s3_img y) 0),
         s3_ap (s3_img x) (s3_ap (s3_img y) 1),
         s3_ap (s3_img x) (s3_ap (s3_img y) 2)).

Definition s3inv (x : s3) : s3 := match x with s3r => s3r2 | s3r2 => s3r | y => y end.

Lemma s3_assoc : forall a b c, s3op a (s3op b c) = s3op (s3op a b) c.
Proof. destruct a, b, c; reflexivity. Qed.
Lemma s3_id_l : forall a, s3op s3i a = a. Proof. destruct a; reflexivity. Qed.
Lemma s3_id_r : forall a, s3op a s3i = a. Proof. destruct a; reflexivity. Qed.
Lemma s3_inv_r : forall a, s3op a (s3inv a) = s3i. Proof. destruct a; reflexivity. Qed.
Lemma s3_inv_l : forall a, s3op (s3inv a) a = s3i. Proof. destruct a; reflexivity. Qed.

Definition s3_eq_dec : forall x y : s3, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Lemma s3_not_comm : s3op s3r s3a <> s3op s3a s3r.
Proof. discriminate. Qed.

(* Four paths from 0 to 1: directly (id), through 2 (rho), through 3 (rho), through 4 (tau). *)
Definition s3_T1 : list (@edge s3) := [(0, 1, s3i); (0, 2, s3r); (0, 3, s3r); (0, 4, s3a)].
Definition s3_X1 : list (@edge s3) := [(2, 1, s3i); (3, 1, s3i); (4, 1, s3i)].
Definition s3_es : list (@edge s3) := s3_T1 ++ s3_X1.
Definition s3_T2 : list (@edge s3) := [(0, 2, s3r); (2, 1, s3i); (0, 3, s3r); (0, 4, s3a)].
Definition s3_X2 : list (@edge s3) := [(0, 1, s3i); (3, 1, s3i); (4, 1, s3i)].

(* Two edge-disjoint obstructing cycles: id against rho, and rho against tau. *)
Definition s3_C1 : list (@edge s3) := [(0, 1, s3i); (0, 2, s3r); (2, 1, s3i)].
Definition s3_C2 : list (@edge s3) := [(0, 3, s3r); (3, 1, s3i); (0, 4, s3a); (4, 1, s3i)].

Lemma s3_cycle_no_section :
  forall C, In C [s3_C1; s3_C2] -> incl C s3_es /\ ~ has_section s3op C.
Proof.
  intros C [<- | [<- | []]]; split.
  - intros x Hx. simpl in Hx |- *. intuition.
  - intro H.
    assert (Hd : has_section s3op ([(0, 1, s3i); (0, 2, s3r)] ++ [(2, 1, s3i)])) by exact H.
    rewrite (section_decide s3op s3i s3inv s3_assoc s3_id_l s3_id_r s3_inv_r s3_inv_l s3_eq_dec 0)
      in Hd; [vm_compute in Hd; discriminate Hd | |].
    + apply (treeb_sound s3op s3_eq_dec). vm_compute. reflexivity.
    + apply (spansb_sound s3op s3_eq_dec). vm_compute. reflexivity.
  - intros x Hx. simpl in Hx |- *. intuition.
  - intro H.
    assert (Hd : has_section s3op ([(0, 3, s3r); (3, 1, s3i); (0, 4, s3a)] ++ [(4, 1, s3i)])) by exact H.
    rewrite (section_decide s3op s3i s3inv s3_assoc s3_id_l s3_id_r s3_inv_r s3_inv_l s3_eq_dec 0)
      in Hd; [vm_compute in Hd; discriminate Hd | |].
    + apply (treeb_sound s3op s3_eq_dec). vm_compute. reflexivity.
    + apply (spansb_sound s3op s3_eq_dec). vm_compute. reflexivity.
Qed.

Lemma s3_disjoint : edge_disjoint [s3_C1; s3_C2].
Proof.
  split; [| split; [intros C' x [] | exact I]].
  intros C' x [<- | []] Hx Hx'. simpl in Hx, Hx'.
  destruct Hx as [<- | [<- | [<- | []]]];
    destruct Hx' as [E | [E | [E | [E | []]]]]; discriminate E.
Qed.

(* The sign homomorphism onto Z/2 = S_3^ab, and the abelian image of the network. *)
Definition s3_sign (x : s3) : bool := match x with s3i | s3r | s3r2 => false | _ => true end.

Lemma s3_sign_hom : forall a b, s3_sign (s3op a b) = xorb (s3_sign a) (s3_sign b).
Proof. destruct a, b; reflexivity. Qed.

(* The plan of the bad tree (through the direct edge) coordinates 3 edges, the plan of the good
   tree (through vertex 2) coordinates 2, and 2 is the minimum over every plan and every feasible
   set. The abelian image needs only one deletion. *)
Theorem s3_tree_choice :
  plan s3_es 0 s3_T1 s3_X1 /\
  plan_cost s3op s3i s3inv s3_eq_dec 0 s3_T1 s3_X1 = 3 /\
  plan s3_es 0 s3_T2 s3_X2 /\
  plan_cost s3op s3i s3inv s3_eq_dec 0 s3_T2 s3_X2 = 2 /\
  (forall F, feasibleM s3op s3_es F -> 2 <= length F) /\
  (forall T X, plan s3_es 0 T X -> 2 <= plan_cost s3op s3i s3inv s3_eq_dec 0 T X) /\
  feasibleM s3op s3_es (coord s3op s3i s3inv s3_eq_dec 0 s3_T2 s3_X2) /\
  feasibleM xorb (map (pushE s3_sign) s3_es) [(0, 4, true)].
Proof.
  assert (Hp1 : plan s3_es 0 s3_T1 s3_X1)
    by (apply (planb_sound s3op s3_eq_dec); vm_compute; reflexivity).
  assert (Hp2 : plan s3_es 0 s3_T2 s3_X2)
    by (apply (planb_sound s3op s3_eq_dec); vm_compute; reflexivity).
  assert (HF : forall F, feasibleM s3op s3_es F -> 2 <= length F).
  { intros F HF.
    apply (edge_disjoint_lower_bound s3op (ed_dec s3_eq_dec) s3_es [s3_C1; s3_C2] s3_disjoint
             s3_cycle_no_section).
    exact (feasibleM_feasible s3op s3_eq_dec s3_es F HF). }
  split; [exact Hp1 | split; [vm_compute; reflexivity |]].
  split; [exact Hp2 | split; [vm_compute; reflexivity |]].
  split; [exact HF | split].
  - apply (plan_min_lower_iff s3op s3i s3inv s3_assoc s3_id_l s3_id_r s3_inv_r s3_inv_l s3_eq_dec
             s3_es 0 (ex_intro _ _ (ex_intro _ _ Hp1)) 2). exact HF.
  - split; [exact (proj1 (plan_coord_feasible s3op s3i s3inv s3_assoc s3_id_l s3_id_r s3_inv_r s3_inv_l
                            s3_eq_dec s3_es 0 s3_T2 s3_X2 Hp2)) |].
    exists [(0, 1, false); (0, 2, false); (0, 3, false); (2, 1, false); (3, 1, false); (4, 1, false)].
    split; [apply (permb_sound xorb bool_dec); vm_compute; reflexivity |].
    exists (fun _ => false). apply (section_check xorb bool_dec). vm_compute. reflexivity.
Qed.
