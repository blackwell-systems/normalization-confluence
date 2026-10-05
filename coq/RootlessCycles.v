(* RootlessCycles.v: rootless propagation on invertible cycles, mechanized axiom-free. This closes
   the "no authority root" row of REGIME-AUDIT section 11: CoordinatedCycles.v proves the exact
   condition for coordination-free convergence GIVEN an authority root (coordinated_unique_nf,
   root_choice_matters), and records one instance without a root (copyback_without_authority).
   Here that instance becomes an exact theorem.

   Model (rootless propagation). The network is a group-labeled graph exactly as in
   CohomologyGraph.v: the fiber of every registry is the group G itself (the regular action), and
   an edge (u, v, g) transports the value at u to g * s(u) at v. With no designated root, EVERY
   edge is a writer: firing (u, v, g) overwrites the target, s(v) := g * s(u), and changes nothing
   else (fire1). A schedule is any finite list of edges of the network, fired left to right
   (fire). Its normal form, when it has one, is a consistent state, that is a fixed point of every
   writer; fixed_iff_section shows these are exactly the sections (H^0). A schedule is fair when
   it fires every edge at least once (incl es p); since a section is fixed by every writer
   (fire_section_stable), any continuation of a schedule that has reached a section stays there,
   so the reachable sections are exactly the limits of fair infinite schedules, and the statements
   below are about the SET of reachable fixed points.

   The cycle. A directed (coherently oriented) cycle on the registries 0 .. n:
     path edges (i, i + 1, g_i) for i < n, then the closing edge (n, 0, g_c)     (cycE gs g_c)
   with holonomy hol = g_c * g_(n-1) * ... * g_0. Coherent orientation is what "rootless" means
   here: a vertex with no incoming edge is never written, so it is a de facto root
   (rootless_orientation_matters below).

   Results (any group, n >= 1, that is at least two registries).
   - rootless_section_iff_holonomy: a consistent state exists iff the holonomy is trivial
     (and iff the labeling is a coboundary, rootless_section_iff_coboundary).
   - rootless_reaches_section: if a consistent state exists, then from EVERY initial state the
     single round that fires the path and then the closing edge reaches one. So
     rootless_nf_exists_iff: "every initial state reaches a consistent state" iff trivial
     holonomy.
   - rootless_two_orders: for every section s and every group element c, from the initial state
     s with registry 0 shifted to s(0) * c, the two rounds "closing edge first" and "closing edge
     last" (both permutations of the edge list, so both fair) reach s and s * c, both
     consistent, and every continuation keeps them there.
   - rootless_not_unique: hence, with trivial holonomy and c <> e, two fair orders reach distinct
     consistent states.
   - rootless_unique_iff (the exact statement): with trivial holonomy, the reachable consistent
     state is unique from every initial state iff |G| = 1, for arbitrary schedules and for fair
     ones alike. rootless_unique_iff_general drops the holonomy hypothesis:
     unique iff (a consistent state exists -> |G| = 1); with nontrivial holonomy uniqueness holds
     vacuously because nothing is reachable.
   - rootless_unique_normal_form_iff: "from every initial state there is exactly one reachable
     consistent state, and some fair round reaches it" iff |G| = 1. Since |G| = 1 forces trivial
     holonomy, this is the single iff "a rootless invertible cycle has a unique normal form iff
     the group is trivial".

   Corners (proved as theorems).
   - rootless_selfloop_unique: the bound n >= 1 is needed. A self-loop (n = 0) with identity
     label over Z/2 has a unique normal form (every state is already consistent and no write
     changes anything) although |G| = 2.
   - rootless_orientation_matters: coherent orientation is needed. The triangle 0 -> 1, 1 -> 2,
     0 -> 2 of copies over Z/2 is a cycle of the underlying graph with trivial holonomy, yet the
     normal form is unique: registry 0 has no incoming edge and acts as the authority root.

   Instances (every hypothesis discharged).
   - Z/2 copy-back (A -> B copy, B -> A copy, CoordinatedCycles.v's loop): not unique
     (rootless_copyback_not_unique), and copyback_without_authority is recovered from
     rootless_two_orders (copyback_without_authority_recovered, through a bridge to
     FederationOrder.run: firing each registry's single in-edge is that registry's step).
   - An S_3-labeled triangle (labels a, b and (b a)^-1, with a b <> b a) with trivial holonomy:
     consistent states exist from every initial state, and they are not unique
     (rootless_s3_not_unique).
   - The trivial group on a triangle: unique normal form from every initial state
     (rootless_trivial_unique).
   - The Z/2 negation loop: nontrivial holonomy, no initial state reaches a consistent state
     (rootless_negation_no_nf), so the existence iff fires both ways.

   States are compared pointwise (peq), so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.CohomologyGraph NC.CoordinatedCycles.
Require NC.FederationOrder NC.Cohomology.
Import ListNotations.

Section Rootless.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  (* ----- rootless propagation on any graph ----- *)

  (* Firing the edge (u, v, g): the target v is overwritten with g * s(u). *)
  Definition fire1 (t : nat -> G) (x : @edge G) : nat -> G :=
    let '(u, v, g) := x in fun z => if Nat.eq_dec z v then op g (t u) else t z.

  (* A schedule: a list of edges fired left to right. *)
  Definition fire (p : list (@edge G)) (t : nat -> G) : nat -> G := fold_left fire1 p t.

  Definition peq (s t : nat -> G) : Prop := forall k, s k = t k.

  Definition trivial_group : Prop := forall a b : G, a = b.

  (* Every two schedules of es that reach consistent states from the same initial state reach the
     same one. *)
  Definition unique_nf (es : list (@edge G)) : Prop :=
    forall t0 p1 p2, incl p1 es -> incl p2 es ->
      is_section op (fire p1 t0) es -> is_section op (fire p2 t0) es ->
      peq (fire p1 t0) (fire p2 t0).

  (* The same, restricted to fair schedules (every edge fired at least once). *)
  Definition unique_nf_fair (es : list (@edge G)) : Prop :=
    forall t0 p1 p2, incl p1 es -> incl p2 es -> incl es p1 -> incl es p2 ->
      is_section op (fire p1 t0) es -> is_section op (fire p2 t0) es ->
      peq (fire p1 t0) (fire p2 t0).

  Lemma fire_cons : forall x p t, fire (x :: p) t = fire p (fire1 t x).
  Proof. reflexivity. Qed.

  Lemma fire_one : forall x t, fire [x] t = fire1 t x.
  Proof. reflexivity. Qed.

  Lemma fire1_eq :
    forall t u v g z, fire1 t (u, v, g) z = if Nat.eq_dec z v then op g (t u) else t z.
  Proof. reflexivity. Qed.

  Lemma fire_app : forall p q t, fire (p ++ q) t = fire q (fire p t).
  Proof. intros p q t. unfold fire. apply fold_left_app. Qed.

  Lemma fire1_ext : forall x s t, peq s t -> peq (fire1 s x) (fire1 t x).
  Proof.
    intros [[u v] g] s t H k. simpl.
    destruct (Nat.eq_dec k v); rewrite ?H; reflexivity.
  Qed.

  Lemma fire_ext : forall p s t, peq s t -> peq (fire p s) (fire p t).
  Proof.
    induction p as [| x p IH]; intros s t H; [exact H |].
    rewrite !fire_cons. apply IH. apply fire1_ext. exact H.
  Qed.

  Lemma section_peq : forall es s t, peq s t -> is_section op s es -> is_section op t es.
  Proof.
    intros es s t H Hs [[u v] g] Hin. pose proof (Hs _ Hin) as E. unfold sat in *.
    rewrite <- !H. exact E.
  Qed.

  Lemma fire1_section : forall s x, sat op s x -> peq (fire1 s x) s.
  Proof.
    intros s [[u v] g] H k. unfold sat in H. simpl.
    destruct (Nat.eq_dec k v) as [-> | _]; [exact H | reflexivity].
  Qed.

  (* The normal forms of rootless propagation (fixed points of every writer) are exactly the
     sections. *)
  Theorem fixed_iff_section :
    forall es t, (forall x, In x es -> peq (fire1 t x) t) <-> is_section op t es.
  Proof.
    intros es t. split.
    - intros H [[u v] g] Hin. pose proof (H _ Hin v) as E. simpl in E.
      destruct (Nat.eq_dec v v) as [_ | n]; [exact E | exfalso; apply n; reflexivity].
    - intros H x Hx. apply fire1_section. exact (H x Hx).
  Qed.

  (* A section is stable under every continuation: what a schedule reaches, every fair extension
     of it keeps. *)
  Theorem fire_section_stable :
    forall es s p, is_section op s es -> incl p es -> peq (fire p s) s.
  Proof.
    intros es s p Hs. revert s Hs. induction p as [| x p IH]; intros s Hs Hp k; [reflexivity |].
    rewrite fire_cons.
    transitivity (fire p s k).
    - apply fire_ext. apply fire1_section. apply Hs. apply Hp. left. reflexivity.
    - apply IH; [exact Hs |]. intros y Hy. apply Hp. right. exact Hy.
  Qed.

  (* Over the trivial group every schedule's result is consistent and all agree, on any graph. *)
  Lemma trivial_all_section : trivial_group -> forall es t, is_section op t es.
  Proof. intros Ht es t [[u v] g] _. apply Ht. Qed.

  Lemma trivial_unique : trivial_group -> forall es, unique_nf es.
  Proof. intros Ht es t0 p1 p2 _ _ _ _ k. apply Ht. Qed.

  (* Section shifted by a right constant (the regular action commutes with right translation). *)
  Lemma section_shift :
    forall es s c t, is_section op s es ->
      (forall w, In w (verts es) -> t w = op (s w) c) -> is_section op t es.
  Proof.
    intros es s c t Hs Ht [[u v] g] Hin.
    destruct (in_verts_edge es u v g Hin) as [Hu Hv]. unfold sat.
    rewrite (Ht u Hu), (Ht v Hv), assoc. pose proof (Hs _ Hin) as E. unfold sat in E.
    rewrite E. reflexivity.
  Qed.

  (* ----- the directed cycle ----- *)

  Fixpoint pathE (k : nat) (gs : list G) : list (@edge G) :=
    match gs with
    | [] => []
    | g :: gs' => (k, S k, g) :: pathE (S k) gs'
    end.

  Definition closing (gs : list G) (gc : G) : @edge G := (length gs, 0, gc).

  (* Path edges (i, i + 1, g_i) for i < n = length gs, then the closing edge (n, 0, gc). *)
  Definition cycE (gs : list G) (gc : G) : list (@edge G) := pathE 0 gs ++ [closing gs gc].

  (* The order that fires the closing edge first and then the path. *)
  Definition order_back (gs : list G) (gc : G) : list (@edge G) := closing gs gc :: pathE 0 gs.

  (* hol gs x = g_(n-1) * ... * g_0 * x. *)
  Definition hstep (acc g : G) : G := op g acc.
  Definition hol (gs : list G) (x : G) : G := fold_left hstep gs x.

  Lemma hol_e : forall gs x, hol gs x = op (hol gs e) x.
  Proof.
    unfold hol. induction gs as [| g gs IH]; intro x; simpl; [rewrite id_l; reflexivity |].
    rewrite (IH (hstep x g)), (IH (hstep e g)). unfold hstep. rewrite id_r, assoc. reflexivity.
  Qed.

  Lemma path_out :
    forall gs k t w, w <= k \/ k + length gs < w -> fire (pathE k gs) t w = t w.
  Proof.
    induction gs as [| g gs IH]; intros k t w Hw; [reflexivity |].
    simpl pathE. rewrite fire_cons. simpl in Hw. rewrite IH by lia. rewrite fire1_eq.
    destruct (Nat.eq_dec w (S k)); [lia | reflexivity].
  Qed.

  Lemma path_end : forall gs k t, fire (pathE k gs) t (k + length gs) = hol gs (t k).
  Proof.
    induction gs as [| g gs IH]; intros k t.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - simpl pathE. rewrite fire_cons. replace (k + length (g :: gs)) with (S k + length gs)
        by (simpl; lia).
      rewrite IH. rewrite fire1_eq. destruct (Nat.eq_dec (S k) (S k)) as [_ | Hne]; [| contradiction].
      reflexivity.
  Qed.

  (* Firing a path always makes it consistent (a path has no cycle). *)
  Lemma path_section : forall gs k t, is_section op (fire (pathE k gs) t) (pathE k gs).
  Proof.
    induction gs as [| g gs IH]; intros k t x Hx; [destruct Hx |].
    simpl pathE in *. rewrite fire_cons. destruct Hx as [<- | Hx].
    - unfold sat. rewrite !path_out by lia. rewrite !fire1_eq.
      destruct (Nat.eq_dec k (S k)); [lia |].
      destruct (Nat.eq_dec (S k) (S k)) as [_ | Hne]; [reflexivity | contradiction].
    - apply IH. exact Hx.
  Qed.

  Lemma section_path_end :
    forall gs k s, is_section op s (pathE k gs) -> s (k + length gs) = hol gs (s k).
  Proof.
    induction gs as [| g gs IH]; intros k s Hs.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - replace (k + length (g :: gs)) with (S k + length gs) by (simpl; lia).
      rewrite IH by (intros x Hx; apply Hs; right; exact Hx).
      pose proof (Hs (k, S k, g) (or_introl eq_refl)) as E. unfold sat in E.
      rewrite <- E. reflexivity.
  Qed.

  (* Firing a path from a state that agrees with s * c at its start yields s * c along it. *)
  Lemma path_shift :
    forall gs k s c t, is_section op s (pathE k gs) -> t k = op (s k) c ->
      forall w, k <= w <= k + length gs -> fire (pathE k gs) t w = op (s w) c.
  Proof.
    induction gs as [| g gs IH]; intros k s c t Hs Ht w Hw.
    - simpl in Hw. assert (w = k) by lia. subst. exact Ht.
    - simpl pathE. rewrite fire_cons. destruct (Nat.eq_dec w k) as [-> | Hne].
      + rewrite path_out by lia. rewrite fire1_eq. destruct (Nat.eq_dec k (S k)); [lia | exact Ht].
      + apply (IH (S k) s c).
        * intros x Hx. apply Hs. right. exact Hx.
        * rewrite fire1_eq. destruct (Nat.eq_dec (S k) (S k)) as [_ | Hss]; [| contradiction].
          pose proof (Hs (k, S k, g) (or_introl eq_refl)) as E. unfold sat in E.
          rewrite Ht, assoc, E. reflexivity.
        * simpl in Hw. lia.
  Qed.

  Lemma path_verts : forall gs k w, In w (verts (pathE k gs)) -> k <= w <= k + length gs.
  Proof.
    induction gs as [| g gs IH]; intros k w H; simpl in H; [contradiction |].
    destruct H as [<- | [<- | H]]; simpl; [lia | lia |]. apply IH in H. lia.
  Qed.

  Lemma cyc_verts : forall gs gc w, In w (verts (cycE gs gc)) -> w <= length gs.
  Proof.
    intros gs gc w H. unfold cycE in H. rewrite verts_app in H. apply in_app_or in H.
    destruct H as [H | H].
    - apply path_verts in H. lia.
    - simpl in H. destruct H as [<- | [<- | []]]; lia.
  Qed.

  Lemma path_incl : forall gs gc, incl (pathE 0 gs) (cycE gs gc).
  Proof. intros gs gc x Hx. apply in_or_app. left. exact Hx. Qed.

  Lemma closing_in : forall gs gc, In (closing gs gc) (cycE gs gc).
  Proof. intros gs gc. apply in_or_app. right. left. reflexivity. Qed.

  Lemma cyc_split :
    forall gs gc s, is_section op s (cycE gs gc) ->
      is_section op s (pathE 0 gs) /\ op gc (s (length gs)) = s 0.
  Proof.
    intros gs gc s Hs. destruct (proj1 (section_app op s _ _) Hs) as [Hp Hc].
    split; [exact Hp |]. exact (Hc _ (or_introl eq_refl)).
  Qed.

  (* ----- existence: trivial holonomy ----- *)

  Theorem rootless_section_iff_holonomy :
    forall gs gc, has_section op (cycE gs gc) <-> op gc (hol gs e) = e.
  Proof.
    intros gs gc. split.
    - intros [s Hs]. destruct (cyc_split gs gc s Hs) as [Hp Hc].
      pose proof (section_path_end gs 0 s Hp) as Hn. simpl in Hn.
      rewrite Hn, hol_e, assoc in Hc.
      apply (right_cancel op e inv assoc id_r inv_r _ _ (s 0)). rewrite id_l. exact Hc.
    - intro H. exists (fire (pathE 0 gs) (fun _ => e)). apply section_app. split.
      + apply path_section.
      + intros x [<- | []]. unfold closing, sat.
        pose proof (path_end gs 0 (fun _ => e)) as Hn. simpl in Hn. rewrite Hn.
        rewrite (path_out gs 0 (fun _ => e) 0) by lia. exact H.
  Qed.

  Corollary rootless_section_iff_coboundary :
    forall gs gc, coboundary op inv (cycE gs gc) <-> op gc (hol gs e) = e.
  Proof.
    intros gs gc. rewrite <- (section_iff_coboundary op e inv assoc id_r inv_r inv_l).
    apply rootless_section_iff_holonomy.
  Qed.

  (* With a consistent state, the round "path, then closing edge" reaches one from EVERY initial
     state: the right-translate of any section by s(0)^-1 * t0(0). *)
  Theorem rootless_reaches_section :
    forall gs gc, has_section op (cycE gs gc) ->
      forall t0, is_section op (fire (cycE gs gc) t0) (cycE gs gc) /\
                 peq (fire (cycE gs gc) t0) (fire (pathE 0 gs) t0).
  Proof.
    intros gs gc [s Hs] t0.
    destruct (cyc_split gs gc s Hs) as [Hp _].
    set (c := op (inv (s 0)) (t0 0)).
    assert (Hshift : forall w, w <= length gs -> fire (pathE 0 gs) t0 w = op (s w) c).
    { intros w Hw. apply (path_shift gs 0 s c t0 Hp); [| simpl; lia].
      unfold c. rewrite assoc, inv_r, id_l. reflexivity. }
    assert (Hsec : is_section op (fire (pathE 0 gs) t0) (cycE gs gc)).
    { apply (section_shift _ s c _ Hs). intros w Hw. apply Hshift. exact (cyc_verts gs gc w Hw). }
    assert (Hstab : peq (fire (cycE gs gc) t0) (fire (pathE 0 gs) t0)).
    { intro k. unfold cycE. rewrite fire_app.
      apply (fire_section_stable (cycE gs gc)); [exact Hsec |].
      intros x [<- | []]. apply closing_in. }
    split; [| exact Hstab].
    apply (section_peq _ (fire (pathE 0 gs) t0)); [| exact Hsec].
    intro k. symmetry. apply Hstab.
  Qed.

  (* "Every initial state reaches a consistent state" iff the holonomy is trivial. *)
  Theorem rootless_nf_exists_iff :
    forall gs gc,
      (forall t0, exists p, incl p (cycE gs gc) /\ incl (cycE gs gc) p /\
                            is_section op (fire p t0) (cycE gs gc)) <->
      op gc (hol gs e) = e.
  Proof.
    intros gs gc. rewrite <- rootless_section_iff_holonomy. split.
    - intro H. destruct (H (fun _ => e)) as [p [_ [_ Hs]]]. eexists. exact Hs.
    - intros Hs t0. exists (cycE gs gc). split; [apply incl_refl | split; [apply incl_refl |]].
      exact (proj1 (rootless_reaches_section gs gc Hs t0)).
  Qed.

  (* ----- non-uniqueness: two fair orders ----- *)

  (* The initial state s with registry 0 shifted to s(0) * c. *)
  Definition perturb (s : nat -> G) (c : G) : nat -> G :=
    fun z => if Nat.eq_dec z 0 then op (s 0) c else s z.

  Theorem rootless_two_orders :
    forall gs gc s c, 1 <= length gs -> is_section op s (cycE gs gc) ->
      Permutation (order_back gs gc) (cycE gs gc) /\
      peq (fire (order_back gs gc) (perturb s c)) s /\
      (forall w, w <= length gs -> fire (cycE gs gc) (perturb s c) w = op (s w) c) /\
      is_section op (fire (order_back gs gc) (perturb s c)) (cycE gs gc) /\
      is_section op (fire (cycE gs gc) (perturb s c)) (cycE gs gc).
  Proof.
    intros gs gc s c Hn Hs.
    destruct (cyc_split gs gc s Hs) as [Hp Hc].
    assert (Hback : peq (fire (order_back gs gc) (perturb s c)) s).
    { intro k. unfold order_back. rewrite fire_cons.
      transitivity (fire (pathE 0 gs) s k).
      - apply fire_ext. intro z. unfold closing. rewrite fire1_eq. unfold perturb.
        destruct (Nat.eq_dec z 0) as [-> | Hz].
        + destruct (Nat.eq_dec (length gs) 0); [lia | exact Hc].
        + reflexivity.
      - apply (fire_section_stable (cycE gs gc)); [exact Hs | apply path_incl]. }
    assert (Hfwd : forall w, w <= length gs -> fire (cycE gs gc) (perturb s c) w = op (s w) c).
    { assert (Hpath : forall w, w <= length gs ->
                        fire (pathE 0 gs) (perturb s c) w = op (s w) c).
      { intros w Hw. apply (path_shift gs 0 s c _ Hp); [| simpl; lia].
        unfold perturb. destruct (Nat.eq_dec 0 0) as [_ | Hne]; [reflexivity | contradiction]. }
      intros w Hw. unfold cycE. rewrite fire_app, fire_one. unfold closing. rewrite fire1_eq.
      destruct (Nat.eq_dec w 0) as [-> | Hw0]; [| apply Hpath; exact Hw].
      rewrite (Hpath (length gs) (le_n _)), assoc, Hc. reflexivity. }
    split; [apply Permutation_cons_append |].
    split; [exact Hback |]. split; [exact Hfwd |]. split.
    - apply (section_peq _ s); [intro k; symmetry; apply Hback | exact Hs].
    - apply (section_shift _ s c _ Hs). intros w Hw. apply Hfwd. exact (cyc_verts gs gc w Hw).
  Qed.

  Lemma shift_eq_e : forall x c, x = op x c -> c = e.
  Proof.
    intros x c H. transitivity (op (inv x) (op x c)).
    - rewrite assoc, inv_l, id_l. reflexivity.
    - rewrite <- H. apply inv_l.
  Qed.

  (* Trivial holonomy and a non-identity element: two fair orders from one initial state reach
     distinct consistent states, and every continuation keeps each where it is. *)
  Theorem rootless_not_unique :
    forall gs gc, 1 <= length gs -> has_section op (cycE gs gc) ->
      forall c, c <> e ->
      exists t0 p1 p2,
        Permutation p1 (cycE gs gc) /\ Permutation p2 (cycE gs gc) /\
        is_section op (fire p1 t0) (cycE gs gc) /\ is_section op (fire p2 t0) (cycE gs gc) /\
        fire p1 t0 0 <> fire p2 t0 0 /\
        (forall q, incl q (cycE gs gc) -> peq (fire (p1 ++ q) t0) (fire p1 t0)) /\
        (forall q, incl q (cycE gs gc) -> peq (fire (p2 ++ q) t0) (fire p2 t0)).
  Proof.
    intros gs gc Hn [s Hs] c Hc.
    destruct (rootless_two_orders gs gc s c Hn Hs) as [Hperm [Hback [Hfwd [S1 S2]]]].
    exists (perturb s c), (order_back gs gc), (cycE gs gc).
    split; [exact Hperm |]. split; [apply Permutation_refl |].
    split; [exact S1 |]. split; [exact S2 |]. split; [| split].
    - rewrite Hback, (Hfwd 0) by lia. intro E. exact (Hc (shift_eq_e _ _ E)).
    - intros q Hq k. rewrite fire_app. apply (fire_section_stable _ _ q S1 Hq).
    - intros q Hq k. rewrite fire_app. apply (fire_section_stable _ _ q S2 Hq).
  Qed.

  Lemma fair_unique_trivial :
    forall gs gc, 1 <= length gs -> has_section op (cycE gs gc) ->
      unique_nf_fair (cycE gs gc) -> trivial_group.
  Proof.
    intros gs gc Hn [s Hs] Hu a b.
    set (c := op (inv a) b).
    destruct (rootless_two_orders gs gc s c Hn Hs) as [Hperm [Hback [Hfwd [S1 S2]]]].
    assert (Hfair : incl (cycE gs gc) (order_back gs gc)).
    { intros x Hx. apply (Permutation_in x (Permutation_sym Hperm)). exact Hx. }
    pose proof (Hu (perturb s c) (order_back gs gc) (cycE gs gc)
                  (fun x Hx => Permutation_in x Hperm Hx) (incl_refl _)
                  Hfair (incl_refl _) S1 S2 0) as E.
    rewrite Hback, (Hfwd 0) in E by lia.
    pose proof (shift_eq_e _ _ E) as Hce. unfold c in Hce.
    transitivity (op a (op (inv a) b)).
    - rewrite Hce, id_r. reflexivity.
    - rewrite assoc, inv_r, id_l. reflexivity.
  Qed.

  (* The exact statement. With trivial holonomy (a consistent state exists), rootless
     propagation has a unique reachable consistent state from every initial state iff |G| = 1,
     whether all schedules or only fair ones are considered. *)
  Theorem rootless_unique_iff :
    forall gs gc, 1 <= length gs -> op gc (hol gs e) = e ->
      (unique_nf (cycE gs gc) <-> trivial_group) /\
      (unique_nf_fair (cycE gs gc) <-> trivial_group).
  Proof.
    intros gs gc Hn Hh. apply rootless_section_iff_holonomy in Hh.
    assert (A : unique_nf_fair (cycE gs gc) -> trivial_group)
      by exact (fair_unique_trivial gs gc Hn Hh).
    assert (B : unique_nf (cycE gs gc) -> unique_nf_fair (cycE gs gc))
      by (intros Hu t0 p1 p2 H1 H2 _ _; exact (Hu t0 p1 p2 H1 H2)).
    split; split.
    - intro H. exact (A (B H)).
    - intro H. exact (trivial_unique H _).
    - exact A.
    - intro H. exact (B (trivial_unique H _)).
  Qed.

  (* Without the holonomy hypothesis: unique iff (a consistent state exists -> |G| = 1). With
     nontrivial holonomy nothing consistent is reachable and uniqueness is vacuous. *)
  Theorem rootless_unique_iff_general :
    forall gs gc, 1 <= length gs ->
      (unique_nf (cycE gs gc) <-> (op gc (hol gs e) = e -> trivial_group)) /\
      (unique_nf_fair (cycE gs gc) <-> (op gc (hol gs e) = e -> trivial_group)).
  Proof.
    intros gs gc Hn. split; split.
    - intros Hu Hh. exact (proj1 (proj1 (rootless_unique_iff gs gc Hn Hh)) Hu).
    - intros H t0 p1 p2 H1 H2 S1 S2.
      assert (Hh : op gc (hol gs e) = e)
        by (apply rootless_section_iff_holonomy; exists (fire p1 t0); exact S1).
      exact (trivial_unique (H Hh) _ t0 p1 p2 H1 H2 S1 S2).
    - intros Hu Hh. exact (proj1 (proj2 (rootless_unique_iff gs gc Hn Hh)) Hu).
    - intros H t0 p1 p2 H1 H2 _ _ S1 S2.
      assert (Hh : op gc (hol gs e) = e)
        by (apply rootless_section_iff_holonomy; exists (fire p1 t0); exact S1).
      exact (trivial_unique (H Hh) _ t0 p1 p2 H1 H2 S1 S2).
  Qed.

  (* Existence and uniqueness together: from every initial state some fair round reaches a
     consistent state and every schedule that reaches one reaches the same, iff |G| = 1. *)
  Theorem rootless_unique_normal_form_iff :
    forall gs gc, 1 <= length gs ->
      ((forall t0, exists p,
          incl p (cycE gs gc) /\ incl (cycE gs gc) p /\
          is_section op (fire p t0) (cycE gs gc) /\
          (forall q, incl q (cycE gs gc) -> is_section op (fire q t0) (cycE gs gc) ->
             peq (fire q t0) (fire p t0)))
       <-> trivial_group).
  Proof.
    intros gs gc Hn. split.
    - intro H.
      assert (Hh : op gc (hol gs e) = e).
      { apply rootless_section_iff_holonomy.
        destruct (H (fun _ => e)) as [p [_ [_ [Hs _]]]]. eexists. exact Hs. }
      apply (proj1 (proj1 (rootless_unique_iff gs gc Hn Hh))).
      intros t0 p1 p2 H1 H2 S1 S2 k. destruct (H t0) as [p [_ [_ [_ Hu]]]].
      rewrite (Hu p1 H1 S1 k), (Hu p2 H2 S2 k). reflexivity.
    - intros Ht t0. exists (cycE gs gc).
      split; [apply incl_refl | split; [apply incl_refl | split]].
      + apply trivial_all_section. exact Ht.
      + intros q _ _ k. apply Ht.
  Qed.
End Rootless.

(* ============================================================
   Instances and corners. Z/2 is (bool, xor) with the group laws of CohomologyGraph.v.
   ============================================================ *)

Definition xinv (a : bool) : bool := a.

(* ----- Z/2 copy-back: A -> B copy, B -> A copy ----- *)

Definition cb_gs : list bool := [false].
Definition cb_gc : bool := false.

Lemma cb_cycE : cycE cb_gs cb_gc = cc_T ++ cb_B.
Proof. reflexivity. Qed.

Lemma cb_holonomy : xorb cb_gc (hol xorb cb_gs false) = false.
Proof. reflexivity. Qed.

Theorem rootless_copyback_not_unique :
  has_section xorb (cycE cb_gs cb_gc) /\
  ~ unique_nf xorb (cycE cb_gs cb_gc) /\ ~ unique_nf_fair xorb (cycE cb_gs cb_gc).
Proof.
  destruct (rootless_unique_iff xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
              cb_gs cb_gc (le_n 1) cb_holonomy) as [[U _] [F _]].
  split; [exact (proj2 (rootless_section_iff_holonomy xorb false xinv xor_assoc xor_id_l
                          xor_id_r xor_inv_r cb_gs cb_gc) cb_holonomy) |].
  split; intro H; [pose proof (U H true false) as E | pose proof (F H true false) as E];
    discriminate E.
Qed.

(* Bridge: in the copy-back loop each registry has one in-edge, and FederationOrder.run of the
   registry writers cc_wf is firing those in-edges. Registry 0's in-edge is the closing edge. *)
Lemma cb_bridge_01 :
  forall t k, FederationOrder.run cc_wf [0; 1] t k = fire xorb (order_back cb_gs cb_gc) t k.
Proof. intros t [| [| k]]; reflexivity. Qed.

Lemma cb_bridge_10 :
  forall t k, FederationOrder.run cc_wf [1; 0] t k = fire xorb (cycE cb_gs cb_gc) t k.
Proof. intros t [| [| k]]; reflexivity. Qed.

(* copyback_without_authority as an instance of rootless_two_orders: section s = (true, true),
   shift c = true, so the initial state is cc_s0 = (false, true). *)
Theorem copyback_without_authority_recovered :
  FederationOrder.run cc_wf [0; 1] cc_s0 0 = true /\
  FederationOrder.run cc_wf [1; 0] cc_s0 0 = false /\
  is_section xorb (FederationOrder.run cc_wf [0; 1] cc_s0) (cc_T ++ cb_B) /\
  is_section xorb (FederationOrder.run cc_wf [1; 0] cc_s0) (cc_T ++ cb_B).
Proof.
  set (s := fun _ : nat => true).
  assert (Hs : is_section xorb s (cycE cb_gs cb_gc)).
  { intros [[u v] g] H. simpl in H. destruct H as [H | [H | []]];
      injection H as Eu Ev Eg; subst; reflexivity. }
  destruct (rootless_two_orders xorb xor_assoc
              cb_gs cb_gc s true (le_n 1) Hs) as [_ [Hback [Hfwd [S1 S2]]]].
  assert (Hp : peq (perturb xorb s true) cc_s0) by (intros [| k]; reflexivity).
  assert (R1 : peq (FederationOrder.run cc_wf [0; 1] cc_s0)
                   (fire xorb (order_back cb_gs cb_gc) (perturb xorb s true))).
  { intro k. rewrite cb_bridge_01. symmetry. apply fire_ext. exact Hp. }
  assert (R2 : peq (FederationOrder.run cc_wf [1; 0] cc_s0)
                   (fire xorb (cycE cb_gs cb_gc) (perturb xorb s true))).
  { intro k. rewrite cb_bridge_10. symmetry. apply fire_ext. exact Hp. }
  rewrite <- cb_cycE.
  split; [rewrite R1, Hback; reflexivity |].
  split; [rewrite R2, (Hfwd 0) by (simpl; lia); reflexivity |].
  split.
  - apply (section_peq xorb _ _ _ (fun k => eq_sym (R1 k)) S1).
  - apply (section_peq xorb _ _ _ (fun k => eq_sym (R2 k)) S2).
Qed.

(* ----- Z/2 negation loop: nontrivial holonomy, no normal form from any state ----- *)

Theorem rootless_negation_no_nf :
  xorb true (hol xorb [false] false) <> false /\
  forall t0 p, ~ is_section xorb (fire xorb p t0) (cycE [false] true).
Proof.
  split; [discriminate |]. intros t0 p H.
  assert (Hh : xorb true (hol xorb [false] false) = false).
  { apply (rootless_section_iff_holonomy xorb false xinv xor_assoc xor_id_l xor_id_r xor_inv_r).
    eexists. exact H. }
  discriminate Hh.
Qed.

(* ----- the trivial group ----- *)

Definition uop (_ _ : unit) : unit := tt.

Lemma unit_trivial : @trivial_group unit.
Proof. intros [] []. reflexivity. Qed.

(* A triangle over the trivial group: unique normal form from every initial state. *)
Theorem rootless_trivial_unique :
  forall t0 : nat -> unit, exists p,
    incl p (cycE [tt; tt] tt) /\ incl (cycE [tt; tt] tt) p /\
    is_section uop (fire uop p t0) (cycE [tt; tt] tt) /\
    (forall q, incl q (cycE [tt; tt] tt) -> is_section uop (fire uop q t0) (cycE [tt; tt] tt) ->
       peq (fire uop q t0) (fire uop p t0)).
Proof.
  apply (proj2 (rootless_unique_normal_form_iff uop tt (fun _ => tt)
                  (fun _ _ _ => eq_refl) (fun 'tt => eq_refl) (fun 'tt => eq_refl)
                  (fun _ => eq_refl) (fun _ => eq_refl) [tt; tt] tt (le_S _ _ (le_n 1)))).
  exact unit_trivial.
Qed.

(* ----- S_3: a non-abelian cycle with trivial holonomy ----- *)

(* The six elements, named by their image triples (CohomologyMin.v's all_perms). The product is
   the composition S3Sep.comp of Cohomology.v, read back through the triples. *)
Inductive S3 : Type := P012 | P120 | P201 | P102 | P021 | P210.

Definition s3_to (x : S3) : NC.Cohomology.S3Sep.perm :=
  match x with
  | P012 => (0, 1, 2) | P120 => (1, 2, 0) | P201 => (2, 0, 1)
  | P102 => (1, 0, 2) | P021 => (0, 2, 1) | P210 => (2, 1, 0)
  end.

Definition s3_of (p : NC.Cohomology.S3Sep.perm) : S3 :=
  match p with
  | (0, 1, 2) => P012 | (1, 2, 0) => P120 | (2, 0, 1) => P201
  | (1, 0, 2) => P102 | (0, 2, 1) => P021 | (2, 1, 0) => P210
  | _ => P012
  end.

Definition s3op (x y : S3) : S3 := s3_of (NC.Cohomology.S3Sep.comp (s3_to x) (s3_to y)).

Definition s3inv (x : S3) : S3 :=
  match x with P120 => P201 | P201 => P120 | y => y end.

Lemma s3_assoc : forall a b c, s3op a (s3op b c) = s3op (s3op a b) c.
Proof. intros [] [] []; reflexivity. Qed.
Lemma s3_id_l : forall a, s3op P012 a = a. Proof. intros []; reflexivity. Qed.
Lemma s3_id_r : forall a, s3op a P012 = a. Proof. intros []; reflexivity. Qed.
Lemma s3_inv_r : forall a, s3op a (s3inv a) = P012. Proof. intros []; reflexivity. Qed.
Lemma s3_inv_l : forall a, s3op (s3inv a) a = P012. Proof. intros []; reflexivity. Qed.

(* a = (0 1 2) and b = (0 1), as in Cohomology.v; the closing label is (b a)^-1. *)
Definition s3_gs : list S3 := [P120; P102].
Definition s3_gc : S3 := s3inv (s3op P102 P120).

Theorem rootless_s3_not_unique :
  s3op P120 P102 <> s3op P102 P120 /\
  s3op s3_gc (hol s3op s3_gs P012) = P012 /\
  (forall t0, is_section s3op (fire s3op (cycE s3_gs s3_gc) t0) (cycE s3_gs s3_gc)) /\
  ~ unique_nf s3op (cycE s3_gs s3_gc) /\ ~ unique_nf_fair s3op (cycE s3_gs s3_gc).
Proof.
  assert (Hh : s3op s3_gc (hol s3op s3_gs P012) = P012) by reflexivity.
  destruct (rootless_unique_iff s3op P012 s3inv s3_assoc s3_id_l s3_id_r s3_inv_r s3_inv_l
              s3_gs s3_gc (le_S _ _ (le_n 1)) Hh) as [[U _] [F _]].
  split; [discriminate |]. split; [exact Hh |]. split.
  - intro t0. apply (rootless_reaches_section s3op P012 s3inv s3_assoc s3_id_l s3_inv_r).
    exact (proj2 (rootless_section_iff_holonomy s3op P012 s3inv s3_assoc s3_id_l s3_id_r s3_inv_r
                    s3_gs s3_gc) Hh).
  - split; intro H; [pose proof (U H P012 P120) as E | pose proof (F H P012 P120) as E];
      discriminate E.
Qed.

(* ----- corner: a self-loop (n = 0) has a unique normal form over Z/2 ----- *)

Theorem rootless_selfloop_unique :
  cycE [] false = [(0, 0, false)] /\
  has_section xorb (cycE [] false) /\ unique_nf xorb (cycE [] false) /\
  ~ @trivial_group bool.
Proof.
  assert (Hall : forall t, is_section xorb t (cycE [] false)).
  { intros t [[u v] g] [H | []]. injection H as Eu Ev Eg. subst. reflexivity. }
  split; [reflexivity |]. split; [exists (fun _ => false); apply Hall |]. split.
  - intros t0 p1 p2 H1 H2 _ _ k.
    rewrite (fire_section_stable xorb _ t0 p1 (Hall t0) H1 k),
            (fire_section_stable xorb _ t0 p2 (Hall t0) H2 k).
    reflexivity.
  - intro H. discriminate (H true false).
Qed.

(* ----- corner: orientation. A cycle of the underlying graph that is not coherently oriented
   has a registry with no incoming edge, which acts as the authority root. ----- *)

Definition tri_mixed : list (@edge bool) := [(0, 1, false); (1, 2, false); (0, 2, false)].

Lemma fire_untargeted :
  forall {G : Type} (op : G -> G -> G) p t w,
    (forall u v g, In (u, v, g) p -> v <> w) -> fire op p t w = t w.
Proof.
  intros G op p. induction p as [| [[u v] g] p IH]; intros t w H; [reflexivity |].
  rewrite fire_cons. rewrite IH by (intros a b c Hin; apply (H a b c); right; exact Hin).
  rewrite fire1_eq. destruct (Nat.eq_dec w v) as [-> | _]; [| reflexivity].
  exfalso. exact (H u v g (or_introl eq_refl) eq_refl).
Qed.

Theorem rootless_orientation_matters :
  has_section xorb tri_mixed /\ unique_nf xorb tri_mixed /\ ~ @trivial_group bool.
Proof.
  split; [exists (fun _ => false); intros [[u v] g] H; simpl in H;
          destruct H as [H | [H | [H | []]]]; injection H as Eu Ev Eg; subst; reflexivity |].
  split; [| intro H; discriminate (H true false)].
  assert (Hno : forall p, incl p tri_mixed -> forall w, w <> 1 -> w <> 2 ->
                  forall t, fire xorb p t w = t w).
  { intros p Hp w H1 H2 t. apply fire_untargeted. intros u v g Hin E. subst v.
    pose proof (Hp _ Hin) as Hin'. simpl in Hin'.
    destruct Hin' as [H | [H | [H | []]]]; injection H as Eu Ev Eg; subst; contradiction. }
  assert (Hval : forall p t0, incl p tri_mixed -> is_section xorb (fire xorb p t0) tri_mixed ->
                   forall w, fire xorb p t0 w = if Nat.eq_dec w 1 then t0 0
                                                else if Nat.eq_dec w 2 then t0 0 else t0 w).
  { intros p t0 Hp Hs w.
    assert (H0 : fire xorb p t0 0 = t0 0) by (apply (Hno p Hp 0); discriminate).
    assert (E01 : fire xorb p t0 1 = t0 0).
    { rewrite <- H0. symmetry. exact (Hs (0, 1, false) (or_introl eq_refl)). }
    assert (E12 : fire xorb p t0 2 = t0 0).
    { rewrite <- E01. symmetry. exact (Hs (1, 2, false) (or_intror (or_introl eq_refl))). }
    destruct (Nat.eq_dec w 1) as [-> | N1]; [exact E01 |].
    destruct (Nat.eq_dec w 2) as [-> | N2]; [exact E12 |].
    exact (Hno p Hp w N1 N2 t0). }
  intros t0 p1 p2 H1 H2 S1 S2 k. rewrite (Hval p1 t0 H1 S1 k), (Hval p2 t0 H2 S2 k). reflexivity.
Qed.
