(* CohomologyGeneral.v: the general-map content of the companion paper's cohomology sections
   (categorical paper, sections 6 to 8), mechanized axiom-free. Work package WP9 of PAPER-MAP.md.

   Cohomology.v, CohomologyGraph.v, CohomologyMin.v and CoordinatedCycles.v cover the invertible
   fragment (group-labeled graphs). This file covers what the paper states for GENERAL transport
   maps, fixes the statements that are false or imprecise as written, and records each
   counterexample as a theorem.

   Paper label to Coq theorem map (row IDs from PAPER-MAP.md):

   C9  thm:obstruction ("a global section around a cycle exists iff the loop composite has a
       reachable fixed point"). The paper never defines "reachable". Here: x0 REACHES A FIXED
       POINT under g when some iterate g^n(x0) is fixed by g (reaches_fixed).
         thm_obstruction_general         sections of a cycle exist iff the loop composite has a
                                         fixed point (any fiber, any maps)
         sections_are_fixed_points       restriction to vertex 0 is a bijection from sections onto
                                         Fix(g): the witness lives on the shared fiber alone
         reaches_fixed_iff_section       a fixed point is reachable from x0 iff some section has
                                         its vertex-0 value on the forward orbit of x0
         thm_obstruction_reachable       the paper's statement with "reachable" read as
                                         "reachable from some seed"
         diagnose_bounded                on a finite fiber with decidable equality, x0 reaches a
                                         fixed point iff g^N(x0) is fixed, N = |fiber| (what gsm's
                                         DiagnoseCycle computes)
         diagnose_orbit_witness          on a finite fiber the orbit repeats within N steps
         diagnose_dichotomy              the diagnostic's two outcomes, exactly
   C15 section 7, "a non-convergent result is definitive" (FALSE AS STATED).
         c15_definitive_claim_false      counterexample: swap of {0,1} with 2 fixed, seed 0
         c15_seed_settles / c15_seed_orbits / c15_tri_section
         c15_exact_refuter               corrected: no section iff NO seed reaches a fixed point
         c15_free_definitive             corrected: one seed is definitive when g's fixed points
                                         are all-or-nothing (a free action)
         c15_injective_reaches_iff_fixed for an invertible composite, a seed reaches a fixed point
                                         iff it is already fixed
         c15_regular_definitive          the regular action (translation by the holonomy): one
                                         seed is definitive, and it reaches iff h = e
         c15_convergent_result_sound    "converges" proves a section exists
         c15_convergent_result_not_global  but not that every seed settles
   C16 prop:minimal (coordination-free SEC iff H^1 = 0), with the qualifiers.
         prop_minimal_qualified_iff      regular action plus an authority root: the labeling is a
                                         coboundary iff, for every authority value, the
                                         uncoordinated network has a unique consistent state
                                         reached by every propagation order
         prop_minimal_qualifiers_needed  without the regular action a non-coboundary still has a
                                         section; without an authority root two orders disagree
                                         (reuses nonfree_holonomy_counterexample and
                                         copyback_without_authority)
   C19 section 8, edge-disjoint obstructions ("one hit per cycle, any G").
         edge_disjoint_lower_bound       k pairwise edge-disjoint cycles with no section force
                                         every feasible coordination to delete at least k edges
                                         (any labels, no group laws used)
         edge_disjoint_min               with a spanning tree whose unbalanced edges number k,
                                         the minimum is exactly k
         bowtie_min_two                  non-vacuity: two Z/2 triangles sharing a vertex
   C20 section 8, min_G >= min_{G^ab}, general form.
         section_pushforward             a section pushes forward along any homomorphism
         feasible_pushforward            so does every feasible coordination
         min_G_ge_min_image              any lower bound on the image's minimum bounds min_G
                                         (G^ab is the image under the abelianization)
         klein_min_ge_1                  non-vacuity: Klein group onto Z/2
   C22 section 8, non-invertible case ("a cycle basis still suffices") (FALSE AS STATED).
         c22_cycle_basis_fails           a tree (empty cycle basis) with constant maps into one
                                         vertex has no section; deleting one edge restores one
         out_tree_section, out_tree_unique, rooted_criterion, rooted_coordination_suffices
                                         corrected: when every tree edge points away from an
                                         authority root, the tree carries a unique section per
                                         root value, and the whole graph has a section with that
                                         root value iff the driven state satisfies every non-tree
                                         edge (a fixed-point condition on the root value)
         c22_rooted_instance             non-vacuity: balance depends on the root value
   C13 section 6, "the obstruction vanishes in exactly two ways" (IMPRECISE).
         c13_two_ways_not_exhaustive     a cyclic, non-monotone loop with a section (two
                                         negations), and one with non-trivial holonomy and a
                                         non-monotone composite that still has a section

   Every theorem is closed under the global context. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Cohomology NC.CohomologyGraph NC.CoordinatedCycles.
Require NC.FederationOrder.
Import ListNotations.

(* ===================================================================== *)
(* Small nat and list facts (stated locally so the file builds on Coq 8.18 to Rocq 9.3). *)

Lemma cg_len_map : forall (A B : Type) (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f l. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cg_len_seq : forall n a, length (seq a n) = n.
Proof. induction n as [| n IH]; intro a; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma bounded_ex_dec :
  forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) ->
  forall N, {exists n, n <= N /\ P n} + {forall n, n <= N -> ~ P n}.
Proof.
  intros P Pd N. induction N as [| N IH].
  - destruct (Pd 0) as [H | H].
    + left. exists 0. split; [lia | exact H].
    + right. intros n Hn Hp. assert (n = 0) by lia. subst. contradiction.
  - destruct IH as [Hex | Hno].
    + left. destruct Hex as [n [Hn Hp]]. exists n. split; [lia | exact Hp].
    + destruct (Pd (S N)) as [H | H].
      * left. exists (S N). split; [lia | exact H].
      * right. intros n Hn Hp. destruct (Nat.eq_dec n (S N)) as [-> | Hne]; [contradiction |].
        apply (Hno n); [lia | exact Hp].
Qed.

Lemma least_witness :
  forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) ->
  forall k, P k -> exists m, m <= k /\ P m /\ forall j, j < m -> ~ P j.
Proof.
  intros P Pd.
  assert (Gen : forall n k, k <= n -> P k -> exists m, m <= k /\ P m /\ forall j, j < m -> ~ P j).
  { induction n as [| n IH]; intros k Hk Hp.
    - exists k. split; [lia |]. split; [exact Hp |]. intros j Hj. lia.
    - destruct (le_lt_dec k n) as [Hle | Hlt]; [exact (IH k Hle Hp) |].
      destruct (bounded_ex_dec P Pd n) as [[k' [Hk' Hp']] | Hno].
      + destruct (IH k' Hk' Hp') as [m [Hm [Hpm Hmin]]].
        exists m. split; [lia | split; assumption].
      + exists k. split; [lia |]. split; [exact Hp |]. intros j Hj. apply Hno. lia. }
  intros k Hk. exact (Gen k k (le_n k) Hk).
Qed.

(* Pigeonhole: a map injective on [0, N] into a list needs at least N + 1 entries. *)
Lemma inj_bound :
  forall (A : Type) (f : nat -> A) (l : list A) N,
    (forall a b, a <= N -> b <= N -> f a = f b -> a = b) ->
    (forall k, k <= N -> In (f k) l) -> S N <= length l.
Proof.
  intros A f l N Hinj Hin.
  assert (Hnd : NoDup (map f (seq 0 (S N)))).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    intros a b Ha Hb. apply in_seq in Ha. apply in_seq in Hb. apply Hinj; lia. }
  assert (Hinc : incl (map f (seq 0 (S N))) l).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [k [<- Hk]]. apply in_seq in Hk.
    apply Hin. lia. }
  assert (Hlen : length (map f (seq 0 (S N))) <= length l) by (apply NoDup_incl_length; assumption).
  rewrite cg_len_map, cg_len_seq in Hlen. exact Hlen.
Qed.

(* ===================================================================== *)
(* C9: the obstruction theorem for general maps around one cycle.         *)

Section GeneralCycle.
  Context {V : Type}.

  (* A global section around the directed cycle with edge maps fs = [f_0; ...; f_{n-1}]: values
     s 0, ..., s n at the cycle's vertices with s (i+1) = f_i (s i), closing up as s n = s 0. *)
  Definition cycle_section (fs : list (V -> V)) (s : nat -> V) : Prop :=
    (forall i, i < length fs -> s (S i) = nth i fs (fun x => x) (s i)) /\ s (length fs) = s 0.

  (* The partial composite along the first k edges. *)
  Definition pre (fs : list (V -> V)) (k : nat) (x : V) : V := loop_composite (firstn k fs) x.

  Lemma loop_cons : forall f fs (x : V), loop_composite (f :: fs) x = loop_composite fs (f x).
  Proof. reflexivity. Qed.

  Lemma pre_succ :
    forall fs i x, i < length fs -> pre fs (S i) x = nth i fs (fun y => y) (pre fs i x).
  Proof.
    unfold pre. induction fs as [| f fs IH]; intros i x H; simpl in H; [lia |].
    destruct i as [| i]; [reflexivity |].
    change (firstn (S (S i)) (f :: fs)) with (f :: firstn (S i) fs).
    change (firstn (S i) (f :: fs)) with (f :: firstn i fs).
    rewrite !loop_cons. apply IH. lia.
  Qed.

  Lemma pre_all : forall fs x, pre fs (length fs) x = loop_composite fs x.
  Proof. intros fs x. unfold pre. rewrite firstn_all. reflexivity. Qed.

  Lemma section_pre :
    forall fs s, cycle_section fs s -> forall i, i <= length fs -> s i = pre fs i (s 0).
  Proof.
    intros fs s [Hs _] i. induction i as [| i IH]; intro Hi; [reflexivity |].
    rewrite (Hs i) by lia. rewrite pre_succ by lia. rewrite IH by lia. reflexivity.
  Qed.

  Lemma section_fixed : forall fs s, cycle_section fs s -> loop_composite fs (s 0) = s 0.
  Proof.
    intros fs s H. rewrite <- pre_all, <- (section_pre fs s H (length fs)) by lia.
    exact (proj2 H).
  Qed.

  Lemma section_of_fixed :
    forall fs x, loop_composite fs x = x -> cycle_section fs (fun i => pre fs i x).
  Proof.
    intros fs x Hx. split.
    - intros i Hi. apply pre_succ. exact Hi.
    - rewrite pre_all. exact Hx.
  Qed.

  (* C9, the general-map version: a section of a cycle exists iff the loop composite has a fixed
     point. No invertibility, no finiteness. *)
  Theorem thm_obstruction_general :
    forall fs, (exists s, cycle_section fs s) <-> Cohomology.has_section fs.
  Proof.
    intro fs. split.
    - intros [s Hs]. exists (s 0). exact (section_fixed fs s Hs).
    - intros [x Hx]. exists (fun i => pre fs i x). exact (section_of_fixed fs x Hx).
  Qed.

  (* The witness lives on the shared fiber: restricting a section to vertex 0 is a bijection from
     sections (on the cycle's vertices 0..n) onto the fixed points of the loop composite. *)
  Theorem sections_are_fixed_points :
    forall fs,
      (forall s, cycle_section fs s -> loop_composite fs (s 0) = s 0) /\
      (forall x, loop_composite fs x = x -> exists s, cycle_section fs s /\ s 0 = x) /\
      (forall s t, cycle_section fs s -> cycle_section fs t -> s 0 = t 0 ->
         forall i, i <= length fs -> s i = t i).
  Proof.
    intro fs. split; [exact (section_fixed fs) |]. split.
    - intros x Hx. exists (fun i => pre fs i x). split; [exact (section_of_fixed fs x Hx) |].
      reflexivity.
    - intros s t Hs Ht E i Hi.
      rewrite (section_pre fs s Hs i Hi), (section_pre fs t Ht i Hi), E. reflexivity.
  Qed.

  (* ----- reachable fixed points ----- *)

  Fixpoint orbit (g : V -> V) (n : nat) (x : V) : V :=
    match n with
    | 0 => x
    | S k => g (orbit g k x)
    end.

  (* "x0 reaches a fixed point under g": some iterate g^n(x0) is fixed. This is the precise sense
     of "reachable fixed point" in thm:obstruction, and what DiagnoseCycle tests from its seed. *)
  Definition reaches_fixed (g : V -> V) (x0 : V) : Prop :=
    exists n, g (orbit g n x0) = orbit g n x0.

  Lemma orbit_stable :
    forall g x0 n, g (orbit g n x0) = orbit g n x0 ->
      forall m, n <= m -> orbit g m x0 = orbit g n x0.
  Proof.
    intros g x0 n Hn m Hm. induction m as [| m IH].
    - assert (n = 0) by lia. subst. reflexivity.
    - destruct (Nat.eq_dec n (S m)) as [<- | Hne]; [reflexivity |].
      simpl. rewrite IH by lia. exact Hn.
  Qed.

  Lemma orbit_ext :
    forall g h, (forall x, g x = h x) -> forall n x, orbit g n x = orbit h n x.
  Proof.
    intros g h E n x. induction n as [| n IH]; [reflexivity |]. simpl. rewrite IH. apply E.
  Qed.

  (* A fixed point is reachable from x0 exactly when some section has its vertex-0 value on the
     forward orbit of x0. *)
  Theorem reaches_fixed_iff_section :
    forall fs x0,
      reaches_fixed (loop_composite fs) x0 <->
      exists s, cycle_section fs s /\ exists n, s 0 = orbit (loop_composite fs) n x0.
  Proof.
    intros fs x0. split.
    - intros [n Hn]. exists (fun i => pre fs i (orbit (loop_composite fs) n x0)).
      split; [exact (section_of_fixed fs _ Hn) |]. exists n. reflexivity.
    - intros [s [Hs [n Hn]]]. exists n. rewrite <- Hn. exact (section_fixed fs s Hs).
  Qed.

  (* thm:obstruction with "reachable" made precise: a section exists iff from SOME seed the
     iteration of the loop composite reaches a fixed point. *)
  Theorem thm_obstruction_reachable :
    forall fs, (exists s, cycle_section fs s) <-> exists x0, reaches_fixed (loop_composite fs) x0.
  Proof.
    intro fs. split.
    - intros [s Hs]. exists (s 0). exists 0. exact (section_fixed fs s Hs).
    - intros [x0 Hr]. apply reaches_fixed_iff_section in Hr. destruct Hr as [s [Hs _]].
      exists s. exact Hs.
  Qed.

  (* ----- the bounded diagnostic on a finite fiber (gsm's DiagnoseCycle) ----- *)

  Section Finite.
    Hypothesis eq_dec : forall x y : V, {x = y} + {x <> y}.
    Variable l : list V.
    Hypothesis l_full : forall x, In x l.

    (* Iterating |fiber| times decides reachability from the seed. *)
    Theorem diagnose_bounded :
      forall g x0, reaches_fixed g x0 <-> g (orbit g (length l) x0) = orbit g (length l) x0.
    Proof.
      intros g x0. split; [| intro H; exists (length l); exact H].
      intros [n Hn].
      pose (P := fun k => g (orbit g k x0) = orbit g k x0).
      assert (Pd : forall k, {P k} + {~ P k}) by (intro k; apply eq_dec).
      destruct (least_witness P Pd n Hn) as [m [_ [Hm Hmin]]].
      assert (Hlt : forall a b, a < b -> b <= m -> orbit g a x0 = orbit g b x0 -> False).
      { intros a b Hab Hb E.
        assert (Eshift : forall k, orbit g (a + k) x0 = orbit g (b + k) x0).
        { induction k as [| k IH]; [rewrite !Nat.add_0_r; exact E |].
          rewrite !Nat.add_succ_r. simpl. rewrite IH. reflexivity. }
        apply (Hmin (a + (m - b))); [lia |]. unfold P. rewrite Eshift.
        replace (b + (m - b)) with m by lia. exact Hm. }
      assert (Hinj : forall a b, a <= m -> b <= m -> orbit g a x0 = orbit g b x0 -> a = b).
      { intros a b Ha Hb E. destruct (lt_eq_lt_dec a b) as [[H | H] | H].
        - exfalso. exact (Hlt a b H Hb E).
        - exact H.
        - exfalso. exact (Hlt b a H Ha (eq_sym E)). }
      assert (Hbound : S m <= length l)
        by (apply (inj_bound V (fun k => orbit g k x0) l m Hinj); intros; apply l_full).
      unfold P in Hm. rewrite (orbit_stable g x0 m Hm (length l)) by lia. exact Hm.
    Qed.

    (* The orbit repeats within |fiber| steps. *)
    Theorem diagnose_orbit_witness :
      forall g x0, exists i j, i < j <= length l /\ orbit g i x0 = orbit g j x0.
    Proof.
      intros g x0.
      assert (Qd : forall i, {exists j, j <= length l /\ (i < j /\ orbit g i x0 = orbit g j x0)} +
                             {~ exists j, j <= length l /\ (i < j /\ orbit g i x0 = orbit g j x0)}).
      { intro i. destruct (bounded_ex_dec (fun j => i < j /\ orbit g i x0 = orbit g j x0)
                             (fun j => match lt_dec i j with
                                       | left H1 =>
                                           match eq_dec (orbit g i x0) (orbit g j x0) with
                                           | left H2 => left (conj H1 H2)
                                           | right H2 => right (fun H => H2 (proj2 H))
                                           end
                                       | right H1 => right (fun H => H1 (proj1 H))
                                       end) (length l)) as [H | H].
        - left. exact H.
        - right. intros [j [Hj Hp]]. exact (H j Hj Hp). }
      destruct (bounded_ex_dec _ Qd (length l)) as [[i [Hi [j [Hj [Hij E]]]]] | Hno].
      - exists i, j. split; [split; [exact Hij | exact Hj] | exact E].
      - exfalso.
        assert (Hb : S (length l) <= length l); [| lia].
        apply (inj_bound V (fun k => orbit g k x0) l (length l)); [| intros; apply l_full].
        intros a b Ha Hb E. destruct (lt_eq_lt_dec a b) as [[H | H] | H].
        + exfalso. apply (Hno a Ha). exists b. split; [exact Hb | split; [exact H | exact E]].
        + exact H.
        + exfalso. apply (Hno b Hb). exists a. split; [exact Ha | split; [exact H | symmetry; exact E]].
    Qed.

    (* The diagnostic's two outcomes, exactly: either the seed settles (and iterating |fiber|
       times lands on the fixed point), or no iterate is ever fixed and the orbit repeats within
       |fiber| steps. *)
    Theorem diagnose_dichotomy :
      forall g x0,
        (reaches_fixed g x0 /\ g (orbit g (length l) x0) = orbit g (length l) x0) \/
        (~ reaches_fixed g x0 /\ (forall k, g (orbit g k x0) <> orbit g k x0) /\
         exists i j, i < j <= length l /\ orbit g i x0 = orbit g j x0).
    Proof.
      intros g x0.
      destruct (eq_dec (g (orbit g (length l) x0)) (orbit g (length l) x0)) as [H | H].
      - left. split; [exists (length l); exact H | exact H].
      - right. assert (Hn : ~ reaches_fixed g x0) by (intro R; apply H; apply diagnose_bounded; exact R).
        split; [exact Hn | split].
        + intros k Hk. apply Hn. exists k. exact Hk.
        + apply diagnose_orbit_witness.
    Qed.
  End Finite.

  (* ===================================================================== *)
  (* C15: reading the diagnostic's result, corrected forms.               *)

  (* Exact form: a cycle has no section iff NO seed reaches a fixed point. *)
  Theorem c15_exact_refuter :
    forall fs, ~ Cohomology.has_section fs <-> forall x0, ~ reaches_fixed (loop_composite fs) x0.
  Proof.
    intro fs. rewrite <- thm_obstruction_general, thm_obstruction_reachable. split.
    - intros H x0 Hr. apply H. exists x0. exact Hr.
    - intros H [x0 Hr]. exact (H x0 Hr).
  Qed.

  (* One seed is definitive when the fixed points of g are all-or-nothing (a free action). *)
  Theorem c15_free_definitive :
    forall g : V -> V, (forall x y, g x = x -> g y = y) ->
      forall x0, ~ reaches_fixed g x0 -> ~ exists x, g x = x.
  Proof.
    intros g Hfree x0 Hn [x Hx]. apply Hn. exists 0. exact (Hfree x x0 Hx).
  Qed.

  (* For an invertible (injective) composite, a seed reaches a fixed point iff it is fixed: the
     diagnostic from seed x0 only tests whether x0 itself is a fixed point. *)
  Theorem c15_injective_reaches_iff_fixed :
    forall g : V -> V, (forall x y, g x = g y -> x = y) ->
      forall x0, reaches_fixed g x0 <-> g x0 = x0.
  Proof.
    intros g Hinj x0. split; [| intro H; exists 0; exact H].
    intros [n Hn]. induction n as [| n IH]; [exact Hn |].
    apply IH. apply Hinj. exact Hn.
  Qed.

  (* "Converges" is sound for existence: a seed that settles exhibits a section. *)
  Theorem c15_convergent_result_sound :
    forall fs x0, reaches_fixed (loop_composite fs) x0 -> exists s, cycle_section fs s.
  Proof.
    intros fs x0 Hr. apply thm_obstruction_reachable. exists x0. exact Hr.
  Qed.
End GeneralCycle.

(* The regular action: the loop composite is translation by the holonomy h in a group. Then one
   seed is definitive, from any seed: it reaches a fixed point iff h = e iff a fixed point exists. *)
Section RegularDiagnostic.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.

  Theorem c15_regular_definitive :
    forall h x0,
      (reaches_fixed (op h) x0 <-> h = e) /\
      (~ reaches_fixed (op h) x0 <-> ~ exists x, op h x = x).
  Proof.
    intros h x0.
    assert (Hr : reaches_fixed (op h) x0 <-> h = e).
    { split.
      - intros [n Hn]. apply (fixed_point_iff_trivial_holonomy op e inv assoc id_l id_r inv_r h).
        exists (orbit (op h) n x0). exact Hn.
      - intros ->. exists 0. apply id_l. }
    split; [exact Hr |].
    rewrite Hr, <- (fixed_point_iff_trivial_holonomy op e inv assoc id_l id_r inv_r h).
    tauto.
  Qed.

  Theorem c15_regular_is_free : forall h x y, op h x = x -> op h y = y.
  Proof.
    intros h x y Hx.
    assert (He : h = e)
      by (apply (fixed_point_iff_trivial_holonomy op e inv assoc id_l id_r inv_r h); exists x; exact Hx).
    rewrite He. apply id_l.
  Qed.
End RegularDiagnostic.

(* ----- C15 counterexample on a finite fiber ----- *)

(* The fiber {t0, t1, t2}; the loop A -> B copy, B -> A swapping t0 and t1 (t2 fixed). The same
   loop as CoordinatedCycles.nonfree_holonomy_counterexample, on a finite type so that the
   finite-fiber diagnostic applies. *)
Inductive tri : Type := t0 | t1 | t2.

Definition tri_swap (x : tri) : tri := match x with t0 => t1 | t1 => t0 | t2 => t2 end.

Definition tri_eq_dec : forall x y : tri, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition tri_all : list tri := [t0; t1; t2].

Lemma tri_full : forall x, In x tri_all.
Proof. intros []; simpl; auto. Qed.

Definition swap_loop : list (tri -> tri) := [fun x => x; tri_swap].

Lemma swap_loop_g : forall x, loop_composite swap_loop x = tri_swap x.
Proof. reflexivity. Qed.

Lemma tri_orbit01 : forall n, orbit tri_swap n t0 = t0 \/ orbit tri_swap n t0 = t1.
Proof.
  induction n as [| n IH]; [left; reflexivity |].
  simpl. destruct IH as [-> | ->]; [right | left]; reflexivity.
Qed.

Theorem c15_seed_orbits : ~ reaches_fixed (loop_composite swap_loop) t0.
Proof.
  intros [n Hn]. rewrite (orbit_ext _ tri_swap swap_loop_g n t0), swap_loop_g in Hn.
  destruct (tri_orbit01 n) as [E | E]; rewrite E in Hn; discriminate Hn.
Qed.

Theorem c15_seed_settles : reaches_fixed (loop_composite swap_loop) t2.
Proof. exists 0. reflexivity. Qed.

Theorem c15_tri_section : exists s, cycle_section swap_loop s.
Proof. apply thm_obstruction_general. exists t2. reflexivity. Qed.

(* The paper's claim "a non-convergent result is definitive: an orbit exists, so the cycle cannot
   converge", as a statement about every loop and seed, is false. *)
Theorem c15_definitive_claim_false :
  ~ (forall (V : Type) (fs : list (V -> V)) (x0 : V),
       ~ reaches_fixed (loop_composite fs) x0 -> ~ Cohomology.has_section fs).
Proof.
  intro H. apply (H tri swap_loop t0 c15_seed_orbits). exists t2. reflexivity.
Qed.

(* A convergent result from one seed does not show every seed settles (the paper's caveat,
   which is correct); and the finite diagnostic lands in each branch of diagnose_dichotomy. *)
Theorem c15_convergent_result_not_global :
  reaches_fixed (loop_composite swap_loop) t2 /\ ~ reaches_fixed (loop_composite swap_loop) t0 /\
  (forall x y, tri_swap x = tri_swap y -> x = y) /\ tri_swap t0 <> t0 /\
  (exists i j, i < j <= length tri_all /\
     orbit (loop_composite swap_loop) i t0 = orbit (loop_composite swap_loop) j t0).
Proof.
  split; [exact c15_seed_settles |]. split; [exact c15_seed_orbits |].
  split; [intros [] []; simpl; congruence |]. split; [discriminate |].
  exact (diagnose_orbit_witness tri_eq_dec tri_all tri_full _ t0).
Qed.

(* ===================================================================== *)
(* C16: prop:minimal with its qualifiers.                                  *)

Section MinimalQualified.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  (* Regular action (the fiber is G itself) and an authority root r: the labeling T ++ X is a
     coboundary (H^1 = 0) iff the coordination-free implementation (no edge coordinated: the tree
     drives from the root, every non-tree edge is kept as a checked constraint) has, for every
     authority value, a consistent state that is the unique one with that root value and that
     every propagation order reaches. *)
  Theorem prop_minimal_qualified_iff :
    forall r T X sT, tree r T -> is_section op sT T -> spans r T X ->
      (coboundary op inv (T ++ X) <->
       forall s0 : nat -> G, exists nf,
         is_section op nf (T ++ X) /\ nf r = s0 r /\
         (forall t, is_section op t (T ++ X) -> t r = s0 r ->
            forall w, In w (r :: verts T) -> t w = nf w) /\
         (forall o, FederationOrder.topo (dsrc r T) o ->
            (forall w, In w o <-> In w (r :: verts T)) ->
            FederationOrder.seq (drive op inv r T o s0) nf)).
  Proof.
    intros r T X sT HT HsT Hsp. split.
    - intro Hcob.
      assert (Hbal : forall x, In x X -> sat op sT x).
      { apply (proj1 (cycle_basis_criterion op e inv assoc id_l id_r inv_r inv_l r T X sT HT HsT Hsp)).
        apply (proj2 (section_iff_coboundary op e inv assoc id_r inv_r inv_l _)). exact Hcob. }
      intro s0.
      destruct (coordinated_unique_nf op e inv assoc id_l id_r inv_r inv_l r T X sT HT HsT Hsp Hbal s0)
        as [nf [H1 [H2 [_ [H4 H5]]]]].
      exists nf. split; [exact H1 |]. split; [exact H2 |]. split; [exact H4 | exact H5].
    - intro Hall. destruct (Hall (fun _ => e)) as [nf [Hs _]].
      apply (proj1 (section_iff_coboundary op e inv assoc id_r inv_r inv_l _)). exists nf. exact Hs.
  Qed.
End MinimalQualified.

(* The qualifiers are needed.
   (1) Regular action: Z/2 acting on {t0, t1, t2} by the swap (not a torsor). The 2-cycle labeled
       (identity, swap) is NOT a coboundary in Z/2 (H^1 <> 0), yet the action has a global
       section (t2 at both vertices). Also nonfree_holonomy_counterexample (CoordinatedCycles.v).
   (2) Authority root: copyback_without_authority (CoordinatedCycles.v): with trivial holonomy and
       both edges as writers, two propagation orders reach different consistent states, so the
       implementation is not strongly eventually consistent. *)
Definition z2_act (b : bool) (x : tri) : tri := if b then tri_swap x else x.

Theorem prop_minimal_qualifiers_needed :
  (~ coboundary xorb (fun a => a) [(0, 1, false); (1, 0, true)] /\
   exists s : nat -> tri, z2_act false (s 0) = s 1 /\ z2_act true (s 1) = s 0) /\
  ((forall x, cc_swap (cc_swap x) = x) /\ cc_swap 0 <> 0 /\
   FederationOrder.run cc_ff [0; 1] (fun _ => 2) 0
     = cc_swap (FederationOrder.run cc_ff [0; 1] (fun _ => 2) 1) /\
   FederationOrder.run cc_ff [0; 1] (fun _ => 0) 0
     <> cc_swap (FederationOrder.run cc_ff [0; 1] (fun _ => 0) 1)) /\
  (FederationOrder.run cc_wf [0; 1] cc_s0 0 = true /\
   FederationOrder.run cc_wf [1; 0] cc_s0 0 = false /\
   is_section xorb (FederationOrder.run cc_wf [0; 1] cc_s0) (cc_T ++ cb_B) /\
   is_section xorb (FederationOrder.run cc_wf [1; 0] cc_s0) (cc_T ++ cb_B)).
Proof.
  split; [| split; [exact nonfree_holonomy_counterexample | exact copyback_without_authority]].
  split.
  - intros [h Hh].
    pose proof (Hh 0 1 false (or_introl eq_refl)) as E1.
    pose proof (Hh 1 0 true (or_intror (or_introl eq_refl))) as E2.
    destruct (h 0), (h 1); simpl in E1, E2; discriminate.
  - exists (fun _ => t2). split; reflexivity.
Qed.

(* ===================================================================== *)
(* C19 and C20: coordinations as edge deletions.                          *)

Section Coordination.
  Context {G : Type}.
  Variable op : G -> G -> G.

  (* A coordination deletes the edges in D; s is a section of the residual network when it
     satisfies every edge of Es outside D. No group laws are used in this section. *)
  Definition rsec (Es D : list (@edge G)) (s : nat -> G) : Prop :=
    forall x, In x Es -> ~ In x D -> sat op s x.

  Definition feasible (Es D : list (@edge G)) : Prop := exists s, rsec Es D s.

  (* Pairwise edge-disjointness of a list of cycles (each given by its edge list). *)
  Fixpoint edge_disjoint (Cs : list (list (@edge G))) : Prop :=
    match Cs with
    | [] => True
    | C :: Cs' => (forall C' x, In C' Cs' -> In x C -> ~ In x C') /\ edge_disjoint Cs'
    end.

  Hypothesis edge_eq_dec : forall x y : @edge G, {x = y} + {x <> y}.

  Lemma meets_dec :
    forall (C D : list (@edge G)), {exists x, In x C /\ In x D} + {forall x, In x C -> ~ In x D}.
  Proof.
    intros C D. induction C as [| y C IH].
    - right. intros x [].
    - destruct (in_dec edge_eq_dec y D) as [Hy | Hy].
      + left. exists y. split; [left; reflexivity | exact Hy].
      + destruct IH as [Hex | Hno].
        * left. destruct Hex as [x [Hx HxD]]. exists x. split; [right; exact Hx | exact HxD].
        * right. intros x [<- | Hx]; [exact Hy | exact (Hno x Hx)].
  Qed.

  (* Every feasible coordination hits every cycle that has no section of its own. *)
  Lemma must_hit :
    forall Es D s C, rsec Es D s -> incl C Es -> ~ CohomologyGraph.has_section op C ->
      exists x, In x C /\ In x D.
  Proof.
    intros Es D s C Hs Hinc Hno. destruct (meets_dec C D) as [H | Hmiss]; [exact H |].
    exfalso. apply Hno. exists s. intros x Hx. apply Hs; [apply Hinc; exact Hx | exact (Hmiss x Hx)].
  Qed.

  Lemma choose_hits :
    forall (D : list (@edge G)) (Cs : list (list (@edge G))), (forall C, In C Cs -> exists x, In x C /\ In x D) ->
      exists ds, length ds = length Cs /\ incl ds D /\ Forall2 (fun x C => In x C) ds Cs.
  Proof.
    intros D Cs. induction Cs as [| C Cs IH]; intro H.
    - exists []. split; [reflexivity | split; [intros x [] | constructor]].
    - destruct (H C (or_introl eq_refl)) as [x [HxC HxD]].
      destruct IH as [ds [Hl [Hi Hf]]]; [intros C' HC'; apply H; right; exact HC' |].
      exists (x :: ds). split; [simpl; rewrite Hl; reflexivity |]. split.
      + intros y [<- | Hy]; [exact HxD | exact (Hi y Hy)].
      + constructor; assumption.
  Qed.

  Lemma forall2_in :
    forall (ds : list (@edge G)) (Cs : list (list (@edge G))) y, Forall2 (fun x C => In x C) ds Cs -> In y ds -> exists C, In C Cs /\ In y C.
  Proof.
    intros ds Cs y Hf. induction Hf as [| x C ds Cs Hx Hf IH]; intro Hy; [destruct Hy |].
    destruct Hy as [<- | Hy].
    - exists C. split; [left; reflexivity | exact Hx].
    - destruct (IH Hy) as [C' [HC' Hy']]. exists C'. split; [right; exact HC' | exact Hy'].
  Qed.

  Lemma hits_nodup :
    forall (ds : list (@edge G)) (Cs : list (list (@edge G))), Forall2 (fun x C => In x C) ds Cs -> edge_disjoint Cs -> NoDup ds.
  Proof.
    intros ds Cs Hf. induction Hf as [| x C ds Cs Hx Hf IH]; intro Hd; [constructor |].
    destruct Hd as [Hd Hd']. constructor; [| exact (IH Hd')].
    intro Hin. destruct (forall2_in ds Cs x Hf Hin) as [C' [HC' HxC']].
    exact (Hd C' x HC' Hx HxC').
  Qed.

  (* C19, lower bound: k pairwise edge-disjoint cycles, none of which has a section on its own,
     force every feasible coordination to delete at least k edges. *)
  Theorem edge_disjoint_lower_bound :
    forall Es Cs, edge_disjoint Cs ->
      (forall C, In C Cs -> incl C Es /\ ~ CohomologyGraph.has_section op C) ->
      forall D, feasible Es D -> length Cs <= length D.
  Proof.
    intros Es Cs Hd HC D [s Hs].
    destruct (choose_hits D Cs) as [ds [Hl [Hi Hf]]].
    { intros C HinC. destruct (HC C HinC) as [Hinc Hno]. exact (must_hit Es D s C Hs Hinc Hno). }
    rewrite <- Hl. apply NoDup_incl_length; [exact (hits_nodup ds Cs Hf Hd) | exact Hi].
  Qed.

  (* C19, exact minimum: if some spanning tree T has balanced extra edges B and k unbalanced
     extra edges Xs, and the network contains k pairwise edge-disjoint obstructing cycles, then
     coordinating Xs is feasible and no coordination with fewer than k edges is. *)
  Theorem edge_disjoint_min :
    forall T B Xs Cs sT, is_section op sT T -> (forall x, In x B -> sat op sT x) ->
      edge_disjoint Cs ->
      (forall C, In C Cs -> incl C (T ++ B ++ Xs) /\ ~ CohomologyGraph.has_section op C) ->
      length Cs = length Xs ->
      feasible (T ++ B ++ Xs) Xs /\ (forall D, feasible (T ++ B ++ Xs) D -> length Xs <= length D).
  Proof.
    intros T B Xs Cs sT HsT Hbal Hd HC Hl. split.
    - exists sT. intros x Hx Hnx. apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (HsT x Hx) |].
      apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (Hbal x Hx) | contradiction].
    - intros D HD. rewrite <- Hl. exact (edge_disjoint_lower_bound _ Cs Hd HC D HD).
  Qed.
End Coordination.

(* Non-vacuity of C19: the bowtie, two Z/2 triangles 0-1-2 and 0-3-4 sharing vertex 0, each
   closed by a flip. Spanning tree 0 -> 1 -> 2, 0 -> 3 -> 4; minimum coordination exactly 2. *)
Definition bow_T : list (@edge bool) := [(0, 1, false); (1, 2, false); (0, 3, false); (3, 4, false)].
Definition bow_X : list (@edge bool) := [(2, 0, true); (4, 0, true)].
Definition bow_C1 : list (@edge bool) := [(0, 1, false); (1, 2, false); (2, 0, true)].
Definition bow_C2 : list (@edge bool) := [(0, 3, false); (3, 4, false); (4, 0, true)].

Lemma bool_edge_eq_dec : forall x y : @edge bool, {x = y} + {x <> y}.
Proof.
  intros [[a b] c] [[a' b'] c'].
  destruct (Nat.eq_dec a a') as [-> | Ha]; [| right; congruence].
  destruct (Nat.eq_dec b b') as [-> | Hb]; [| right; congruence].
  destruct (bool_dec c c') as [-> | Hc]; [left; reflexivity | right; congruence].
Qed.

Theorem bowtie_min_two :
  feasible xorb (bow_T ++ [] ++ bow_X) bow_X /\
  (forall D, feasible xorb (bow_T ++ [] ++ bow_X) D -> 2 <= length D).
Proof.
  assert (HsT : is_section xorb sT0 bow_T).
  { intros [[u v] g] H. simpl in H.
    destruct H as [H | [H | [H | [H | []]]]]; injection H as Eu Ev Eg; subst; reflexivity. }
  assert (Hno : forall a b,
             ~ CohomologyGraph.has_section xorb [(0, a, false); (a, b, false); (b, 0, true)]).
  { intros a b [s Hs].
    pose proof (Hs _ (or_introl eq_refl)) as E1.
    pose proof (Hs _ (or_intror (or_introl eq_refl))) as E2.
    pose proof (Hs _ (or_intror (or_intror (or_introl eq_refl)))) as E3.
    unfold sat in E1, E2, E3. simpl in E1, E2, E3.
    destruct (s 0), (s a), (s b); simpl in *; congruence. }
  destruct (edge_disjoint_min xorb bool_edge_eq_dec bow_T [] bow_X [bow_C1; bow_C2] sT0 HsT
              (fun x H => match H with end)) as [Hf Hmin].
  - split; [| split; [intros C' x [] | exact I]].
    intros C' x [<- | []] Hx Hx'. simpl in Hx, Hx'.
    destruct Hx as [<- | [<- | [<- | []]]]; destruct Hx' as [H | [H | [H | []]]]; discriminate H.
  - intros C [<- | [<- | []]]; split.
    + intros x Hx. simpl in Hx |- *. tauto.
    + exact (Hno 1 2).
    + intros x Hx. simpl in Hx |- *. tauto.
    + exact (Hno 3 4).
  - reflexivity.
  - split; [exact Hf | exact Hmin].
Qed.

(* ----- C20: pushforward along any homomorphism ----- *)

Section Pushforward.
  Context {G H : Type}.
  Variables (opG : G -> G -> G) (opH : H -> H -> H) (phi : G -> H).
  Hypothesis hom : forall a b, phi (opG a b) = opH (phi a) (phi b).

  Definition pushE (x : @edge G) : @edge H := let '(u, v, g) := x in (u, v, phi g).

  Lemma sat_push : forall s x, sat opG s x -> sat opH (fun w => phi (s w)) (pushE x).
  Proof. intros s [[u v] g] Hs. unfold sat in *. simpl. rewrite <- hom, Hs. reflexivity. Qed.

  Theorem section_pushforward :
    forall s es, is_section opG s es -> is_section opH (fun w => phi (s w)) (map pushE es).
  Proof.
    intros s es Hs y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- Hx]].
    apply sat_push. exact (Hs x Hx).
  Qed.

  Theorem feasible_pushforward :
    forall Es D, feasible opG Es D -> feasible opH (map pushE Es) (map pushE D).
  Proof.
    intros Es D [s Hs]. exists (fun w => phi (s w)). intros y Hy Hny.
    apply in_map_iff in Hy. destruct Hy as [x [<- Hx]].
    apply sat_push. apply Hs; [exact Hx |]. intro HxD. apply Hny. apply in_map. exact HxD.
  Qed.

  (* min_G >= min_H for every homomorphic image H (in particular G^ab): every lower bound on the
     size of a feasible coordination of the image network bounds the original from below. *)
  Theorem min_G_ge_min_image :
    forall Es k, (forall D', feasible opH (map pushE Es) D' -> k <= length D') ->
      forall D, feasible opG Es D -> k <= length D.
  Proof.
    intros Es k Hk D HD. rewrite <- (cg_len_map _ _ pushE D). apply Hk.
    exact (feasible_pushforward Es D HD).
  Qed.
End Pushforward.

(* Non-vacuity of C20: the Klein group Z/2 x Z/2 onto Z/2 by the first coordinate. A triangle
   whose closing edge carries (true, false) needs at least one coordinated edge, because its
   image does. *)
Definition kop (a b : bool * bool) : bool * bool := (xorb (fst a) (fst b), xorb (snd a) (snd b)).

Lemma klein_hom : forall a b, fst (kop a b) = xorb (fst a) (fst b).
Proof. reflexivity. Qed.

Definition klein_tri : list (@edge (bool * bool)) :=
  [(0, 1, (false, true)); (1, 2, (false, false)); (2, 0, (true, false))].

Theorem klein_min_ge_1 : forall D, feasible kop klein_tri D -> 1 <= length D.
Proof.
  apply (min_G_ge_min_image kop xorb fst klein_hom klein_tri 1).
  intros [| d D'] [s Hs]; [| simpl; lia]. exfalso.
  pose proof (Hs _ (or_introl eq_refl) (fun H => H)) as E1.
  pose proof (Hs _ (or_intror (or_introl eq_refl)) (fun H => H)) as E2.
  pose proof (Hs _ (or_intror (or_intror (or_introl eq_refl))) (fun H => H)) as E3.
  unfold sat in E1, E2, E3. simpl in E1, E2, E3.
  destruct (s 0), (s 1), (s 2); simpl in *; congruence.
Qed.

(* ===================================================================== *)
(* C22: the non-invertible case.                                          *)

Section NonInvertible.
  Context {V : Type}.

  (* Edges carry arbitrary transport maps V -> V (the edge type of CohomologyGraph.v with labels
     in V -> V); s satisfies (u, v, f) when f (s u) = s v. *)
  Definition msat (s : nat -> V) (x : @edge (V -> V)) : Prop :=
    let '(u, v, f) := x in f (s u) = s v.

  Definition msection (s : nat -> V) (es : list (@edge (V -> V))) : Prop :=
    forall x, In x es -> msat s x.

  (* A root-oriented tree: every edge points away from the authority root r. *)
  Inductive otree (r : nat) : list (@edge (V -> V)) -> Prop :=
  | o_nil : otree r []
  | o_out : forall es u v f,
      otree r es -> In u (r :: verts es) -> ~ In v (r :: verts es) ->
      otree r (es ++ [(u, v, f)]).

  Lemma otree_tree : forall r es, otree r es -> tree r es.
  Proof.
    intros r es H. induction H as [| es u v f H IH Hu Hv]; [apply t_nil |].
    apply t_out; assumption.
  Qed.

  Lemma msection_app :
    forall s a b, msection s (a ++ b) <-> msection s a /\ msection s b.
  Proof.
    intros s a b. unfold msection. split.
    - intro H. split; intros x Hx; apply H; apply in_or_app; [left | right]; exact Hx.
    - intros [Ha Hb] x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx];
        [apply Ha | apply Hb]; exact Hx.
  Qed.

  Lemma msection_upd_fresh :
    forall s es w x, msection s es -> ~ In w (verts es) -> msection (upd s w x) es.
  Proof.
    intros s es w x Hs Hw [[a b] f] Hin.
    destruct (in_verts_edge es a b f Hin) as [Ha Hb].
    assert (Na : a <> w) by (intro E; subst; contradiction).
    assert (Nb : b <> w) by (intro E; subst; contradiction).
    pose proof (Hs _ Hin) as E. unfold msat in *.
    rewrite (upd_other s w x a Na), (upd_other s w x b Nb). exact E.
  Qed.

  (* Driving along a root-oriented tree: for every authority value there is a section. *)
  Theorem out_tree_section : forall r T, otree r T -> forall x0, exists s, msection s T /\ s r = x0.
  Proof.
    intros r T HT. induction HT as [| es u v f HT IH Hu Hv]; intro x0.
    - exists (fun _ => x0). split; [intros x [] | reflexivity].
    - destruct (IH x0) as [s [Hs Hr]]. exists (upd s v (f (s u))). split.
      + apply msection_app. split.
        * apply msection_upd_fresh; [exact Hs |]. intro H. apply Hv. right. exact H.
        * intros x [<- | []]. unfold msat.
          rewrite upd_same, upd_other; [reflexivity |].
          intro E. subst. apply Hv. exact Hu.
      + rewrite upd_other; [exact Hr |]. intro E. subst. apply Hv. left. reflexivity.
  Qed.

  (* ... and it is unique given the root value. *)
  Theorem out_tree_unique :
    forall r T, otree r T ->
    forall s t, msection s T -> msection t T -> s r = t r ->
    forall w, In w (r :: verts T) -> s w = t w.
  Proof.
    intros r T HT. induction HT as [| es u v f HT IH Hu Hv]; intros s t Hs Ht Hr w Hw.
    - simpl in Hw. destruct Hw as [<- | []]. exact Hr.
    - destruct (proj1 (msection_app _ _ _) Hs) as [Hs1 Hsx].
      destruct (proj1 (msection_app _ _ _) Ht) as [Ht1 Htx].
      pose proof (Hsx (u, v, f) (or_introl eq_refl)) as Es.
      pose proof (Htx (u, v, f) (or_introl eq_refl)) as Et.
      unfold msat in Es, Et.
      destruct (verts_snoc r es u v f w Hw) as [Hold | [-> | ->]].
      + exact (IH s t Hs1 Ht1 Hr w Hold).
      + exact (IH s t Hs1 Ht1 Hr u Hu).
      + rewrite <- Es, <- Et. f_equal. exact (IH s t Hs1 Ht1 Hr u Hu).
  Qed.

  (* The corrected "cycle basis suffices", in fixed-point form: with a root-oriented spanning
     tree T and extra edges X among its vertices, the whole graph has a section with root value
     sT r iff the tree-driven state sT satisfies every extra edge. *)
  Theorem rooted_criterion :
    forall r T X sT, otree r T -> msection sT T ->
      (forall u v f, In (u, v, f) X -> In u (r :: verts T) /\ In v (r :: verts T)) ->
      ((exists s, msection s (T ++ X) /\ s r = sT r) <-> forall x, In x X -> msat sT x).
  Proof.
    intros r T X sT HT HsT Hsp. split.
    - intros [s [Hs Hr]] [[u v] f] Hx.
      destruct (proj1 (msection_app _ _ _) Hs) as [HsT' HsX].
      pose proof (HsX _ Hx) as E. unfold msat in E |- *.
      destruct (Hsp u v f Hx) as [Hu Hv].
      rewrite (out_tree_unique r T HT sT s HsT HsT' (eq_sym Hr) u Hu),
              (out_tree_unique r T HT sT s HsT HsT' (eq_sym Hr) v Hv).
      exact E.
    - intro Hbal. exists sT. split; [| reflexivity]. apply msection_app. split; [exact HsT |].
      intros x Hx. exact (Hbal x Hx).
  Qed.

  (* Coordinating (deleting) every non-tree edge always leaves a section, for every authority
     value, when the tree is root-oriented. *)
  Theorem rooted_coordination_suffices :
    forall r T, otree r T -> forall X x0,
      exists s, s r = x0 /\ forall x, In x (T ++ X) -> ~ In x X -> msat s x.
  Proof.
    intros r T HT X x0. destruct (out_tree_section r T HT x0) as [s [Hs Hr]].
    exists s. split; [exact Hr |]. intros x Hx Hnx.
    apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (Hs x Hx) | contradiction].
  Qed.
End NonInvertible.

(* The counterexample: a tree (so its cycle basis is empty) whose two edges point INTO vertex 2,
   with constant maps 0 and 1. It has no section, so "a cycle basis suffices" fails, and the
   minimum coordination is 1 although the graph has no cycle at all. *)
Definition c22_es : list (@edge (bool -> bool)) :=
  ([] ++ [(0, 2, fun _ => false)]) ++ [(1, 2, fun _ => true)].

Theorem c22_cycle_basis_fails :
  tree 2 c22_es /\
  ~ (exists s, msection s c22_es) /\
  (exists s, msection s [(0, 2, fun _ : bool => false)]).
Proof.
  split; [| split].
  - unfold c22_es. apply t_in; [apply t_in; [apply t_nil | left; reflexivity | simpl; intuition congruence] | |].
    + simpl. left. reflexivity.
    + simpl. intuition congruence.
  - intros [s Hs].
    pose proof (Hs _ (or_introl eq_refl)) as E1.
    pose proof (Hs _ (or_intror (or_introl eq_refl))) as E2.
    unfold msat in E1, E2. rewrite <- E1 in E2. discriminate E2.
  - exists (fun _ => false). intros x [<- | []]. reflexivity.
Qed.

(* Non-vacuity of the corrected form: tree 0 -> 1 (copy), extra edge 1 -> 0 (constant false).
   The section exists with root value false and not with root value true. *)
Definition c22_T : list (@edge (bool -> bool)) := [] ++ [(0, 1, fun x => x)].
Definition c22_X : list (@edge (bool -> bool)) := [(1, 0, fun _ => false)].

Theorem c22_rooted_instance :
  otree 0 c22_T /\
  (exists s, msection s (c22_T ++ c22_X) /\ s 0 = false) /\
  ~ (exists s, msection s (c22_T ++ c22_X) /\ s 0 = true).
Proof.
  assert (HT : otree 0 c22_T).
  { unfold c22_T. apply o_out; [apply o_nil | left; reflexivity | simpl; intuition congruence]. }
  assert (Hsp : forall u v f, In (u, v, f) c22_X -> In u (0 :: verts c22_T) /\ In v (0 :: verts c22_T)).
  { intros u v f [H | []]. injection H as Eu Ev Ef. subst. simpl. auto. }
  assert (Hsec : forall b : bool, msection (fun _ => b) c22_T).
  { intros b x [<- | []]. reflexivity. }
  split; [exact HT | split].
  - apply (proj2 (rooted_criterion 0 c22_T c22_X (fun _ => false) HT (Hsec false) Hsp)).
    intros x [<- | []]. reflexivity.
  - intro H.
    pose proof (proj1 (rooted_criterion 0 c22_T c22_X (fun _ => true) HT (Hsec true) Hsp) H) as H'.
    specialize (H' _ (or_introl eq_refl)). discriminate H'.
Qed.

(* ===================================================================== *)
(* C13: "the obstruction vanishes in exactly two ways" is not exhaustive. *)

(* (1) A cyclic loop with trivial holonomy whose edges are not monotone: two negations on bool.
   (2) A cyclic loop with NON-trivial holonomy and a non-monotone composite that still has a
       section: copy then swap on {0, 1, 2, ...}, fixed point 2.
   Neither is acyclic (each is a cycle) and neither is in the monotone regime. *)
Theorem c13_two_ways_not_exhaustive :
  (exists s, cycle_section [negb; negb] s) /\
  ~ (forall x y, Bool.le x y -> Bool.le (negb x) (negb y)) /\
  (exists s, cycle_section [fun x => x; cc_swap] s) /\
  cc_swap 0 <> 0 /\
  ~ (forall x y, x <= y -> loop_composite [fun x => x; cc_swap] x <= loop_composite [fun x => x; cc_swap] y).
Proof.
  split; [apply thm_obstruction_general; exists false; reflexivity |].
  split; [intro H; specialize (H false true I); simpl in H; discriminate H |].
  split; [apply thm_obstruction_general; exists 2; reflexivity |].
  split; [discriminate |].
  intro H. specialize (H 0 1 (le_S _ _ (le_n 0))). simpl in H. lia.
Qed.
