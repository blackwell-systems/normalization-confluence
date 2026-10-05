(* CohomologyNerve.v: H^1 of the nerve as a 2-COMPLEX (a graph plus 2-cells whose boundary
   holonomies must be trivial), mechanized axiom-free. CohomologyGraph.v classifies H^1 on the
   1-skeleton (H1_classification: classes are the non-tree labels up to simultaneous conjugation;
   betti_number: |E| - |V| + 1 generators). Here the triangles of the nerve are added as 2-cells.

   Model.
   - A 2-cell is a closed walk (base vertex, list of steps), each step an edge index with an
     orientation (forward, or backward = the inverse label). The nerve's triangles are the length-3
     cells; the theory holds for any closed walk, and every instance below uses triangles except one
     square boundary, used to show a dependent relation.
   - hol L w: the holonomy of the walk w under the labeling L (the composite transport).
   - cocycle L C: every 2-cell of C has trivial holonomy under L (the 2-cocycle condition). On the
     graph (C = []) every labeling is a cocycle.
   - Gauge and cohomologous are CohomologyGraph.v's (the gauge group is the same 0-cochains).

   Results.
   1. Non-abelian classification, for a fixed spanning tree T with extra edges X
      (nerve_H1_classification): relabel the tree by the identity (triv T); then
      (a) triv T ++ X' is a cocycle iff the assignment X' of the generators (the non-tree edges)
          satisfies every relation word gen_word |T| w (the cell's walk with its tree steps erased,
          relations_in_generators);
      (b) every cocycle of the complex is cohomologous to such a triv T ++ X';
      (c) two of them are cohomologous iff the assignments are simultaneously conjugate;
      (d) simultaneous conjugation preserves the relations.
      So H^1(K; G) is in bijection with Hom(<X | relation words>, G) modulo conjugation, the
      presented group being the fundamental group of the 2-complex. For non-abelian G there is no
      rank: the classification replaces it. For abelian G the conjugation is trivial and classes are
      exactly the relation-satisfying assignments (nerve_H1_abelian).
   2. Counting over Z/2 (nerve_H1_Z2_count): the classes are counted by an explicit list of
      representatives of length 2^(b - rank), where b = |X| = |E| - |V| + 1 and rank is the number
      of relations not implied by the ones after them in the list (rel_rank; it depends only on the solution set,
      rel_rank_solution_set, so not on the order of the cells). So dim H^1 = b - rank. With no cells
      the count is 2^b with betti_number's b (nerve_Z2_no_cells); the count is 2^b iff the rank is 0
      iff the cells impose no relation on the generators (nerve_Z2_full_iff); adding a cell never
      raises it (nerve_Z2_cell_lowers).
   3. Sections (nerve_section_iff_coboundary): a section exists iff the labeling is a coboundary iff
      it is cohomologous to the identity labeling, with no reference to the cells, and a labeling
      with a section is a cocycle of every complex. So the cells change the count of classes, never
      the existence question.
   4. Non-vacuity: the hollow triangle (rank 0, two classes), the filled triangle (rank 1, one class:
      the flip class of the graph is killed), and the square with a diagonal (0, 1 or 2 filled
      triangles: 4, 2, 1 classes; adding the square boundary as a third cell keeps rank 2). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph.
Import ListNotations.

(* ================================================================
   Combinatorial data, independent of the group.
   ================================================================ *)

(* A step traverses edge i forward (true) or backward (false). *)
Definition step : Type := (nat * bool)%type.

(* A 2-cell: a base vertex and a closed walk from it. *)
Definition cell : Type := (nat * list step)%type.

(* Walks on an unlabeled graph (a list of endpoint pairs). *)
Inductive walk (S : list (nat * nat)) : nat -> list step -> nat -> Prop :=
| w_nil : forall a, walk S a [] a
| w_fwd : forall a b c i w,
    nth_error S i = Some (a, b) -> walk S b w c -> walk S a ((i, true) :: w) c
| w_bwd : forall a b c i w,
    nth_error S i = Some (b, a) -> walk S b w c -> walk S a ((i, false) :: w) c.

Definition wf_cells (S : list (nat * nat)) (C : list cell) : Prop :=
  forall c, In c C -> walk S (fst c) (snd c) (fst c).

(* A cell's walk rewritten in the generators: tree steps (index < n) are erased, and the non-tree
   edge n + k becomes generator k. *)
Fixpoint gen_word (n : nat) (w : list step) : list step :=
  match w with
  | [] => []
  | (i, o) :: w' => if n <=? i then (i - n, o) :: gen_word n w' else gen_word n w'
  end.

Lemma nth_error_map_ :
  forall (A B : Type) (f : A -> B) (l : list A) i,
    nth_error (map f l) i = option_map f (nth_error l i).
Proof. intros A B f l. induction l as [| x l IH]; intro i; destruct i; simpl; auto. Qed.

Lemma len_map_ : forall (A B : Type) (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f l. induction l; simpl; auto. Qed.

Lemma len_app_ : forall (A : Type) (a b : list A), length (a ++ b) = length a + length b.
Proof. intros A a b. induction a; simpl; auto. Qed.

(* ================================================================
   The group-labeled 2-complex.
   ================================================================ *)

Section Nerve.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  Definition shape (L : list (@edge G)) : list (nat * nat) :=
    map (fun x => let '(u, v, _) := x in (u, v)) L.

  (* The identity labeling on the same edges. *)
  Definition triv (L : list (@edge G)) : list (@edge G) :=
    map (fun x => let '(u, v, _) := x in (u, v, e)) L.

  Definition lab_of (L : list (@edge G)) (s : step) : G :=
    match nth_error L (fst s) with
    | Some (_, _, g) => if snd s then g else inv g
    | None => e
    end.

  (* Holonomy of a walk: the composite transport, later steps on the left. *)
  Fixpoint hol (L : list (@edge G)) (w : list step) : G :=
    match w with
    | [] => e
    | s :: w' => op (hol L w') (lab_of L s)
    end.

  (* The 2-cocycle condition: every 2-cell has trivial holonomy. *)
  Definition cocycle (L : list (@edge G)) (C : list cell) : Prop :=
    forall c, In c C -> hol L (snd c) = e.

  (* The relation words, evaluated on an assignment X of the generators. *)
  Definition rels_hold (n : nat) (X : list (@edge G)) (C : list cell) : Prop :=
    forall c, In c C -> hol X (gen_word n (snd c)) = e.

  (* Extra edges spanned by the tree (as in H1_classification). *)
  Definition spanned (r : nat) (T X : list (@edge G)) : Prop :=
    forall u v g, In (u, v, g) X -> In u (r :: verts T) /\ In v (r :: verts T).

  (* ----- group algebra ----- *)

  Lemma inv_e : inv e = e.
  Proof. rewrite <- (id_l (inv e)). apply inv_r. Qed.

  Lemma inv_inv_ : forall a, inv (inv a) = a.
  Proof. exact (inv_inv op e inv assoc id_l id_r inv_l). Qed.

  Lemma inv_op : forall a b, inv (op a b) = op (inv b) (inv a).
  Proof.
    intros a b.
    transitivity (op (inv (op a b)) (op (op a b) (op (inv b) (inv a)))).
    - replace (op (op a b) (op (inv b) (inv a))) with e; [rewrite id_r; reflexivity |].
      rewrite <- assoc, (assoc b), inv_r, id_l, inv_r. reflexivity.
    - rewrite assoc, inv_l, id_l. reflexivity.
  Qed.

  Lemma conj_e : forall c x, op c (op x (inv c)) = e -> x = e.
  Proof.
    intros c x H.
    transitivity (op (inv c) (op (op c (op x (inv c))) c)).
    - rewrite <- !assoc, inv_l, id_r, !assoc, inv_l, id_l. reflexivity.
    - rewrite H, id_l, inv_l. reflexivity.
  Qed.

  Lemma conj_id : forall c, op c (op e (inv c)) = e.
  Proof. intro c. rewrite id_l. apply inv_r. Qed.

  (* ----- shapes ----- *)

  Lemma shape_app : forall a b, shape (a ++ b) = shape a ++ shape b.
  Proof. intros a b. apply map_app. Qed.

  Lemma shape_gauge : forall h L, shape (gauge op inv h L) = shape L.
  Proof. intros h L. induction L as [| [[u v] g] L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma shape_triv : forall L, shape (triv L) = shape L.
  Proof. intro L. induction L as [| [[u v] g] L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma length_shape : forall L, length (shape L) = length L.
  Proof. intro L. apply len_map_. Qed.

  Lemma length_triv : forall L, length (triv L) = length L.
  Proof. intro L. apply len_map_. Qed.

  Lemma triv_shape : forall A B, shape A = shape B -> triv A = triv B.
  Proof.
    induction A as [| [[u v] g] A IH]; intros [| [[u' v'] g'] B] H; simpl in *;
      try discriminate; [reflexivity |].
    injection H as Eu Ev HB. subst. rewrite (IH B HB). reflexivity.
  Qed.

  Lemma verts_shape : forall A B, shape A = shape B -> verts A = verts B.
  Proof.
    induction A as [| [[u v] g] A IH]; intros [| [[u' v'] g'] B] H; simpl in *;
      try discriminate; [reflexivity |].
    injection H as Eu Ev HB. subst. rewrite (IH B HB). reflexivity.
  Qed.

  Lemma idlab_triv : forall L, idlab e (triv L).
  Proof.
    intros L u v g H. unfold triv in H. apply in_map_iff in H.
    destruct H as [[[a b] h] [E _]]. injection E as _ _ Eg. symmetry. exact Eg.
  Qed.

  Lemma idlab_eq_triv : forall L, idlab e L -> L = triv L.
  Proof.
    induction L as [| [[u v] g] L IH]; intro H; simpl; [reflexivity |].
    rewrite (H u v g (or_introl eq_refl)) at 1. f_equal.
    apply IH. intros a b c Hin. exact (H a b c (or_intror Hin)).
  Qed.

  Lemma shape_split :
    forall L A B, shape L = A ++ B ->
      exists L1 L2, L = L1 ++ L2 /\ shape L1 = A /\ shape L2 = B.
  Proof.
    induction L as [| x L IH]; intros A B H.
    - destruct A; [| discriminate]. destruct B; [| discriminate].
      exists [], []. auto.
    - destruct A as [| p A].
      + exists [], (x :: L). auto.
      + destruct x as [[u v] g]. simpl in H. injection H as Ep H'.
        destruct (IH A B H') as [L1 [L2 [E [E1 E2]]]].
        exists ((u, v, g) :: L1), L2. subst. simpl. auto.
  Qed.

  Lemma shape_single :
    forall L u v, shape L = [(u, v)] -> exists g, L = [(u, v, g)].
  Proof.
    intros [| [[a b] g] [| y L]] u v H; simpl in H; try discriminate.
    injection H as -> ->. exists g. reflexivity.
  Qed.

  (* The tree property depends only on the endpoints. *)
  Lemma tree_shape : forall r T, tree r T -> forall T', shape T' = shape T -> tree r T'.
  Proof.
    intros r T HT. induction HT as [| es u v g HT IH Hu Hv | es u v g HT IH Hv Hu];
      intros T' E.
    - destruct T'; [apply t_nil | discriminate].
    - rewrite shape_app in E. simpl in E.
      destruct (shape_split T' (shape es) [(u, v)] E) as [L1 [L2 [-> [E1 E2]]]].
      destruct (shape_single L2 u v E2) as [g' ->].
      rewrite <- (verts_shape L1 es E1) in Hu, Hv.
      apply t_out; [apply IH; exact E1 | exact Hu | exact Hv].
    - rewrite shape_app in E. simpl in E.
      destruct (shape_split T' (shape es) [(u, v)] E) as [L1 [L2 [-> [E1 E2]]]].
      destruct (shape_single L2 u v E2) as [g' ->].
      rewrite <- (verts_shape L1 es E1) in Hu, Hv.
      apply t_in; [apply IH; exact E1 | exact Hv | exact Hu].
  Qed.

  Lemma in_shape : forall L u v g, In (u, v, g) L -> In (u, v) (shape L).
  Proof.
    intros L u v g H. unfold shape. apply in_map_iff. exists (u, v, g). auto.
  Qed.

  Lemma in_shape_inv : forall L u v, In (u, v) (shape L) -> exists g, In (u, v, g) L.
  Proof.
    intros L u v H. unfold shape in H. apply in_map_iff in H.
    destruct H as [[[a b] g] [E Hin]]. injection E as -> ->. exists g. exact Hin.
  Qed.

  Lemma spanned_shape :
    forall r T T' X X', spanned r T X -> shape T' = shape T -> shape X' = shape X ->
      spanned r T' X'.
  Proof.
    intros r T T' X X' H ET EX u v g Hin.
    rewrite (verts_shape T' T ET).
    pose proof (in_shape X' u v g Hin) as Hs. rewrite EX in Hs.
    destruct (in_shape_inv X u v Hs) as [g0 H0]. exact (H u v g0 H0).
  Qed.

  (* ----- gauge transformations ----- *)

  Lemma gauge_comp :
    forall h1 h2 L,
      gauge op inv h2 (gauge op inv h1 L) = gauge op inv (fun w => op (h2 w) (h1 w)) L.
  Proof.
    intros h1 h2 L. induction L as [| [[u v] g] L IH]; simpl; [reflexivity |].
    rewrite IH. f_equal. f_equal. rewrite inv_op, !assoc. reflexivity.
  Qed.

  Lemma gauge_unit : forall L, gauge op inv (fun _ => e) L = L.
  Proof.
    intro L. induction L as [| [[u v] g] L IH]; simpl; [reflexivity |].
    rewrite IH, inv_e, id_l, id_r. reflexivity.
  Qed.

  (* Cohomology is an equivalence relation. *)
  Lemma cohom_refl : forall L, cohomologous op inv L L.
  Proof. intro L. exists (fun _ => e). symmetry. apply gauge_unit. Qed.

  Lemma cohom_sym : forall L1 L2, cohomologous op inv L1 L2 -> cohomologous op inv L2 L1.
  Proof.
    intros L1 L2 [h ->]. exists (fun w => inv (h w)). rewrite gauge_comp.
    transitivity (gauge op inv (fun _ => e) L1); [symmetry; apply gauge_unit |].
    unfold gauge. apply map_ext. intros [[u v] g]. rewrite !inv_l. reflexivity.
  Qed.

  Lemma cohom_trans :
    forall L1 L2 L3, cohomologous op inv L1 L2 -> cohomologous op inv L2 L3 ->
      cohomologous op inv L1 L3.
  Proof.
    intros L1 L2 L3 [h1 ->] [h2 ->]. exists (fun w => op (h2 w) (h1 w)). apply gauge_comp.
  Qed.

  (* ----- holonomy of walks ----- *)

  Lemma nth_shape :
    forall L i a b, nth_error (shape L) i = Some (a, b) ->
      exists g, nth_error L i = Some (a, b, g).
  Proof.
    induction L as [| [[u v] g] L IH]; intros [| i] a b H; simpl in H; try discriminate.
    - injection H as -> ->. exists g. reflexivity.
    - exact (IH i a b H).
  Qed.

  Lemma lab_gauge :
    forall h L i u v g, nth_error L i = Some (u, v, g) ->
      nth_error (gauge op inv h L) i = Some (u, v, op (h v) (op g (inv (h u)))).
  Proof.
    intros h L i u v g H. unfold gauge. rewrite nth_error_map_, H. reflexivity.
  Qed.

  Lemma gauge_none :
    forall h L i, nth_error L i = None -> nth_error (gauge op inv h L) i = None.
  Proof.
    intro h. induction L as [| x L IH]; intros [| i] H; simpl in *; try discriminate;
      try reflexivity. apply IH. exact H.
  Qed.

  (* Gauge covariance: a gauge conjugates the holonomy of a walk a -> b by its end values. *)
  Theorem hol_gauge :
    forall h L a w b, walk (shape L) a w b ->
      hol (gauge op inv h L) w = op (h b) (op (hol L w) (inv (h a))).
  Proof.
    intros h L a w b Hw. induction Hw as [a | a b c i w Hi Hw IH | a b c i w Hi Hw IH].
    - simpl. symmetry. apply conj_id.
    - destruct (nth_shape L i a b Hi) as [g Hg]. simpl. unfold lab_of. simpl.
      rewrite (lab_gauge h L i a b g Hg), Hg, IH.
      rewrite <- !assoc. f_equal. f_equal. rewrite (assoc (inv (h b))), inv_l, id_l. reflexivity.
    - destruct (nth_shape L i b a Hi) as [g Hg]. simpl. unfold lab_of. simpl.
      rewrite (lab_gauge h L i b a g Hg), Hg, IH.
      rewrite !inv_op, inv_inv_.
      rewrite <- !assoc. f_equal. f_equal. rewrite (assoc (inv (h b))), inv_l, id_l. reflexivity.
  Qed.

  (* The cocycle condition is gauge invariant, so it is a property of a cohomology class. *)
  Theorem cocycle_gauge :
    forall h L C, wf_cells (shape L) C -> (cocycle L C <-> cocycle (gauge op inv h L) C).
  Proof.
    intros h L C Hwf. split; intros H c Hc.
    - rewrite (hol_gauge h L _ _ _ (Hwf c Hc)), (H c Hc). apply conj_id.
    - apply (conj_e (h (fst c))). rewrite <- (hol_gauge h L _ _ _ (Hwf c Hc)). exact (H c Hc).
  Qed.

  (* Along a walk, a section transports exactly as the holonomy does. *)
  Lemma hol_section :
    forall s L a w b, is_section op s L -> walk (shape L) a w b ->
      hol L w = op (s b) (inv (s a)).
  Proof.
    intros s L a w b Hs Hw. induction Hw as [a | a b c i w Hi Hw IH | a b c i w Hi Hw IH].
    - simpl. symmetry. apply inv_r.
    - destruct (nth_shape L i a b Hi) as [g Hg]. simpl. unfold lab_of. simpl. rewrite Hg, IH.
      pose proof (Hs _ (nth_error_In L i Hg)) as E. unfold sat in E.
      rewrite <- E, inv_op, <- !assoc, inv_l, id_r. reflexivity.
    - destruct (nth_shape L i b a Hi) as [g Hg]. simpl. unfold lab_of. simpl. rewrite Hg, IH.
      pose proof (Hs _ (nth_error_In L i Hg)) as E. unfold sat in E.
      rewrite <- E, inv_op, <- !assoc. reflexivity.
  Qed.

  Lemma section_cocycle :
    forall L C, wf_cells (shape L) C -> has_section op L -> cocycle L C.
  Proof.
    intros L C Hwf [s Hs] c Hc. rewrite (hol_section s L _ _ _ Hs (Hwf c Hc)). apply inv_r.
  Qed.

  Lemma coboundary_iff_gauge_triv :
    forall L, coboundary op inv L <-> exists h, L = gauge op inv h (triv L).
  Proof.
    intro L. split.
    - intros [h Hh]. exists h. unfold gauge, triv. rewrite map_map.
      transitivity (map (fun x : @edge G => x) L); [symmetry; apply map_id |].
      apply map_ext_in. intros [[u v] g] Hin. rewrite (Hh u v g Hin), id_l. reflexivity.
    - intros [h E]. exists h. intros u v g Hin. rewrite E in Hin.
      unfold gauge, triv in Hin. rewrite map_map in Hin. apply in_map_iff in Hin.
      destruct Hin as [[[a b] k] [Ex _]]. injection Ex as -> -> <-. rewrite id_l. reflexivity.
  Qed.

  (* Point 4: sections are decided on the graph. A section exists iff the labeling is a coboundary
     iff it is cohomologous to the identity labeling; none of this mentions the cells, and a labeling
     with a section is a cocycle of every complex on its graph. *)
  Theorem nerve_section_iff_coboundary :
    forall L C, wf_cells (shape L) C ->
      (has_section op L <-> coboundary op inv L) /\
      (has_section op L <-> cohomologous op inv (triv L) L) /\
      (has_section op L -> cocycle L C).
  Proof.
    intros L C Hwf.
    pose proof (section_iff_coboundary op e inv assoc id_r inv_r inv_l L) as HS.
    split; [exact HS | split].
    - rewrite HS, coboundary_iff_gauge_triv. split; intros [h E]; exists h; exact E.
    - apply section_cocycle. exact Hwf.
  Qed.

  (* ----- relations rewritten in the generators ----- *)

  (* On a labeling that is the identity on the tree, a walk's holonomy is its relation word
     evaluated on the non-tree labels. *)
  Theorem hol_tree_fixed :
    forall T X w, idlab e T -> hol (T ++ X) w = hol X (gen_word (length T) w).
  Proof.
    intros T X w Hid. induction w as [| [i o] w IH]; [reflexivity |].
    simpl. destruct (Nat.leb_spec (length T) i) as [Hle | Hlt].
    - simpl. rewrite IH. unfold lab_of. simpl. rewrite (nth_error_app2 T X Hle). reflexivity.
    - rewrite IH. unfold lab_of. simpl. rewrite (nth_error_app1 T X Hlt).
      destruct (nth_error T i) as [[[u v] g] |] eqn:Hn; [| apply id_r].
      rewrite (Hid u v g (nth_error_In T i Hn)). destruct o; [| rewrite inv_e]; apply id_r.
  Qed.

  Theorem relations_in_generators :
    forall T X C, idlab e T -> (cocycle (T ++ X) C <-> rels_hold (length T) X C).
  Proof.
    intros T X C Hid. unfold cocycle, rels_hold. split; intros H c Hc;
      [rewrite <- (hol_tree_fixed T X _ Hid) | rewrite (hol_tree_fixed T X _ Hid)]; exact (H c Hc).
  Qed.

  (* Simultaneous conjugation conjugates every word. *)
  Lemma hol_gauge_const :
    forall c X w, hol (gauge op inv (fun _ => c) X) w = op c (op (hol X w) (inv c)).
  Proof.
    intros c X w. induction w as [| [i o] w IH]; simpl; [symmetry; apply conj_id |].
    rewrite IH. unfold lab_of. simpl.
    destruct (nth_error X i) as [[[u v] g] |] eqn:Hn.
    - rewrite (lab_gauge (fun _ => c) X i u v g Hn). destruct o.
      + rewrite <- !assoc. f_equal. f_equal. rewrite (assoc (inv c)), inv_l, id_l. reflexivity.
      + rewrite !inv_op, inv_inv_, <- !assoc. f_equal. f_equal.
        rewrite (assoc (inv c)), inv_l, id_l. reflexivity.
    - rewrite (gauge_none (fun _ => c) X i Hn), id_r, id_r. reflexivity.
  Qed.

  Lemma rels_hold_conj :
    forall n X C c, rels_hold n X C -> rels_hold n (gauge op inv (fun _ => c) X) C.
  Proof.
    intros n X C c H d Hd. rewrite hol_gauge_const, (H d Hd). apply conj_id.
  Qed.

  (* ----- the classification ----- *)

  (* H^1 of the 2-complex, for a fixed spanning tree T of its graph T ++ X:
     (a) assignments of the generators satisfying the relation words are exactly the tree-fixed
         cocycles;
     (b) every cocycle of the complex is cohomologous to one of them;
     (c) two of them are cohomologous iff they are simultaneously conjugate;
     (d) simultaneous conjugation preserves the relations.
     So H^1(K; G) = Hom(<X | relation words>, G) / conjugation. *)
  Theorem nerve_H1_classification :
    forall r T X C,
      tree r T -> spanned r T X -> wf_cells (shape (T ++ X)) C ->
      (forall X', rels_hold (length T) X' C <-> cocycle (triv T ++ X') C) /\
      (forall L, shape L = shape (T ++ X) -> cocycle L C ->
         exists X', shape X' = shape X /\ rels_hold (length T) X' C /\
                    cohomologous op inv L (triv T ++ X')) /\
      (forall X1 X2, shape X1 = shape X ->
         (cohomologous op inv (triv T ++ X1) (triv T ++ X2)
          <-> exists c, X2 = gauge op inv (fun _ => c) X1)) /\
      (forall X1 c, rels_hold (length T) X1 C ->
         rels_hold (length T) (gauge op inv (fun _ => c) X1) C).
  Proof.
    intros r T X C HT Hsp Hwf. split; [| split; [| split]].
    - intro X'. rewrite (relations_in_generators (triv T) X' C (idlab_triv T)), length_triv.
      reflexivity.
    - intros L EL HL. rewrite shape_app in EL.
      destruct (shape_split L (shape T) (shape X) EL) as [LT [LX [-> [ET EX]]]].
      pose proof (tree_shape r T HT LT ET) as HLT.
      destruct (gauge_fix op e inv assoc id_l id_r inv_r inv_l r LT HLT) as [h Hh].
      assert (Hwf' : wf_cells (shape (LT ++ LX)) C)
        by (rewrite shape_app, ET, EX, <- shape_app; exact Hwf).
      pose proof (proj1 (cocycle_gauge h _ C Hwf') HL) as Hc.
      rewrite gauge_app in Hc.
      assert (Eg : gauge op inv h LT = triv T).
      { rewrite (idlab_eq_triv _ Hh). apply triv_shape. rewrite shape_gauge. exact ET. }
      rewrite Eg in Hc.
      exists (gauge op inv h LX). split; [| split].
      + rewrite shape_gauge. exact EX.
      + rewrite <- (length_triv T). apply relations_in_generators; [apply idlab_triv | exact Hc].
      + exists h. rewrite gauge_app, Eg. reflexivity.
    - intros X1 X2 E1.
      apply (H1_classification op e inv assoc id_l id_r inv_r inv_l r (triv T) X1 X2).
      + apply (tree_shape r T HT). apply shape_triv.
      + apply idlab_triv.
      + apply (spanned_shape r T (triv T) X X1 Hsp (shape_triv T) E1).
    - intros X1 c H. apply rels_hold_conj. exact H.
  Qed.

  (* Abelian coefficients: simultaneous conjugation is trivial, so the classes are exactly the
     relation-satisfying assignments, Hom(<X | relations>^ab, G). *)
  Theorem nerve_H1_abelian :
    (forall a b, op a b = op b a) ->
    forall r T X, tree r T -> spanned r T X ->
    forall X1 X2, shape X1 = shape X ->
      (cohomologous op inv (triv T ++ X1) (triv T ++ X2) <-> X1 = X2).
  Proof.
    intros Hcomm r T X HT Hsp X1 X2 E1.
    rewrite (H1_classification op e inv assoc id_l id_r inv_r inv_l r (triv T) X1 X2
               (tree_shape r T HT _ (shape_triv T)) (idlab_triv T)
               (spanned_shape r T (triv T) X X1 Hsp (shape_triv T) E1)).
    assert (Hc : forall c, gauge op inv (fun _ => c) X1 = X1).
    { intro c. transitivity (map (fun x : @edge G => x) X1); [| apply map_id].
      unfold gauge. apply map_ext. intros [[u v] g].
      rewrite (Hcomm g (inv c)), assoc, inv_r, id_l. reflexivity. }
    split.
    - intros [c ->]. symmetry. apply Hc.
    - intros <-. exists e. symmetry. apply Hc.
  Qed.
End Nerve.

(* ================================================================
   Counting over Z/2: linear relations on bool^m, their rank, and the solution count.
   ================================================================ *)

Fixpoint allvecs (m : nat) : list (list bool) :=
  match m with
  | 0 => [[]]
  | S m' => map (cons false) (allvecs m') ++ map (cons true) (allvecs m')
  end.

(* The common kernel of a list of functionals, as an explicit list. *)
Fixpoint ker (m : nat) (F : list (list bool -> bool)) : list (list bool) :=
  match F with
  | [] => allvecs m
  | f :: F' => filter (fun a => negb (f a)) (ker m F')
  end.

(* The rank: the number of relations not implied by the later ones in the list (a relation adds
   one exactly when it is nonzero somewhere on the common kernel of the rest). *)
Fixpoint rel_rank (m : nat) (F : list (list bool -> bool)) : nat :=
  match F with
  | [] => 0
  | f :: F' => (if existsb f (ker m F') then 1 else 0) + rel_rank m F'
  end.

Fixpoint vxor (a b : list bool) : list bool :=
  match a, b with
  | x :: a', y :: b' => xorb x y :: vxor a' b'
  | _, _ => []
  end.

Definition linear (m : nat) (f : list bool -> bool) : Prop :=
  forall a b, length a = m -> length b = m -> f (vxor a b) = xorb (f a) (f b).

Lemma nodup_app_disj :
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1. induction H1 as [| x l1 Hx H1 IH]; intros H2 Hd; simpl; [exact H2 |].
  constructor.
  - intro H. apply in_app_or in H. destruct H as [H | H]; [exact (Hx H) |].
    exact (Hd x (or_introl eq_refl) H).
  - apply IH; [exact H2 |]. intros y Hy. apply Hd. right. exact Hy.
Qed.

Lemma nodup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hl. induction Hl as [| x l Hx Hl IH]; simpl; constructor.
  - intro H. apply in_map_iff in H. destruct H as [y [Ey Hy]].
    assert (y = x) by (apply Hinj; [right; exact Hy | left; reflexivity | exact Ey]).
    subst. exact (Hx Hy).
  - apply IH. intros a b Ha Hb. apply Hinj; right; assumption.
Qed.

Lemma nodup_filter_ :
  forall (A : Type) (p : A -> bool) (l : list A), NoDup l -> NoDup (filter p l).
Proof.
  intros A p l H. induction H as [| x l Hx H IH]; simpl; [constructor |].
  destruct (p x); [| exact IH]. constructor; [| exact IH].
  intro Hin. apply filter_In in Hin. exact (Hx (proj1 Hin)).
Qed.

Lemma filter_all_ :
  forall (A : Type) (p : A -> bool) (l : list A), (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  intros A p l. induction l as [| x l IH]; intro H; simpl; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity |]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma filter_le_ : forall (A : Type) (p : A -> bool) (l : list A), length (filter p l) <= length l.
Proof. intros A p l. induction l as [| x l IH]; simpl; [lia |]. destruct (p x); simpl; lia. Qed.

Lemma filter_full_ :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (filter p l) = length l -> forall x, In x l -> p x = true.
Proof.
  intros A p l. induction l as [| y l IH]; intros H x Hx; [contradiction |].
  simpl in H. destruct (p y) eqn:Hy.
  - simpl in H. destruct Hx as [<- | Hx]; [exact Hy |]. apply IH; [lia | exact Hx].
  - pose proof (filter_le_ A p l). lia.
Qed.

Lemma filter_split_ :
  forall (A : Type) (p : A -> bool) (l : list A),
    length (filter (fun x => negb (p x)) l) + length (filter p l) = length l.
Proof.
  intros A p l. induction l as [| x l IH]; simpl; [reflexivity |].
  destruct (p x); simpl; lia.
Qed.

Lemma in_allvecs : forall m a, In a (allvecs m) <-> length a = m.
Proof.
  induction m as [| m IH]; intro a; simpl.
  - split; [intros [<- | []]; reflexivity |]. intro H. destruct a; [left; reflexivity | discriminate].
  - rewrite in_app_iff, !in_map_iff. split.
    + intros [[x [<- Hx]] | [x [<- Hx]]]; simpl; f_equal; apply IH; exact Hx.
    + intro H. destruct a as [| b a]; [discriminate |]. injection H as H.
      destruct b; [right | left]; exists a; split; try reflexivity; apply IH; exact H.
Qed.

Lemma nodup_allvecs : forall m, NoDup (allvecs m).
Proof.
  induction m as [| m IH]; simpl.
  - constructor; [intros [] | constructor].
  - apply nodup_app_disj.
    + apply nodup_map_inj; [intros x y _ _ E; injection E; auto | exact IH].
    + apply nodup_map_inj; [intros x y _ _ E; injection E; auto | exact IH].
    + intros x H1 H2. apply in_map_iff in H1, H2.
      destruct H1 as [y1 [<- _]]. destruct H2 as [y2 [E _]]. discriminate E.
Qed.

Lemma length_allvecs : forall m, length (allvecs m) = 2 ^ m.
Proof.
  induction m as [| m IH]; simpl; [reflexivity |].
  rewrite len_app_, !len_map_, IH. lia.
Qed.

Lemma in_ker :
  forall m F a, In a (ker m F) <-> length a = m /\ (forall f, In f F -> f a = false).
Proof.
  intros m F a. induction F as [| f F IH]; simpl.
  - rewrite in_allvecs. split; [intro H; split; [exact H | intros f []] | intros [H _]; exact H].
  - rewrite filter_In, IH. split.
    + intros [[Hl Hf] Hn]. split; [exact Hl |]. intros g [<- | Hg]; [| exact (Hf g Hg)].
      destruct (f a); [discriminate | reflexivity].
    + intros [Hl Hf]. split; [split; [exact Hl |] |].
      * intros g Hg. apply Hf. right. exact Hg.
      * rewrite (Hf f (or_introl eq_refl)). reflexivity.
Qed.

Lemma nodup_ker : forall m F, NoDup (ker m F).
Proof.
  intros m F. induction F as [| f F IH]; simpl; [apply nodup_allvecs | apply nodup_filter_; exact IH].
Qed.

Lemma vxor_len : forall a b, length a = length b -> length (vxor a b) = length a.
Proof.
  induction a as [| x a IH]; intros [| y b] H; simpl in *; try discriminate; [reflexivity |].
  rewrite IH; [reflexivity | lia].
Qed.

Lemma vxor_cancel : forall a w, length a = length w -> vxor (vxor a w) w = a.
Proof.
  induction a as [| x a IH]; intros [| y w] H; simpl in *; try discriminate; [reflexivity |].
  rewrite IH by lia. f_equal. destruct x, y; reflexivity.
Qed.

Lemma vxor_self : forall a, vxor a a = repeat false (length a).
Proof. induction a as [| x a IH]; simpl; [reflexivity |]. rewrite IH, xorb_nilpotent. reflexivity. Qed.

Lemma linear_zero : forall m f, linear m f -> f (repeat false m) = false.
Proof.
  intros m f Hf. pose proof (Hf (repeat false m) (repeat false m) (repeat_length _ _)
                               (repeat_length _ _)) as H.
  rewrite vxor_self, repeat_length, xorb_nilpotent in H. exact H.
Qed.

(* A functional that is nonzero somewhere on a subspace is zero on exactly half of it. *)
Lemma ker_halves :
  forall m F f w,
    (forall g, In g F -> linear m g) -> linear m f ->
    In w (ker m F) -> f w = true ->
    2 * length (filter (fun a => negb (f a)) (ker m F)) = length (ker m F).
Proof.
  intros m F f w HF Hf Hw Hfw.
  set (K := ker m F).
  set (P0 := filter (fun a => negb (f a)) K). set (P1 := filter f K).
  pose proof (filter_split_ _ f K) as Hsplit. fold P0 P1 in Hsplit.
  destruct (proj1 (in_ker m F w) Hw) as [Hlw Hzw].
  assert (Hclos : forall a, In a K -> In (vxor a w) K /\ f (vxor a w) = xorb (f a) true).
  { intros a Ha. destruct (proj1 (in_ker m F a) Ha) as [Hla Hza]. split.
    - apply in_ker. split; [rewrite vxor_len; lia |].
      intros g Hg. rewrite (HF g Hg a w Hla Hlw), (Hza g Hg), (Hzw g Hg). reflexivity.
    - rewrite (Hf a w Hla Hlw), Hfw. reflexivity. }
  assert (Hinj : forall l, (forall x, In x l -> In x K) ->
            forall x y, In x l -> In y l -> vxor x w = vxor y w -> x = y).
  { intros l Hl x y Hx Hy E.
    destruct (proj1 (in_ker m F x) (Hl x Hx)) as [Hlx _].
    destruct (proj1 (in_ker m F y) (Hl y Hy)) as [Hly _].
    rewrite <- (vxor_cancel x w), <- (vxor_cancel y w), E by lia. reflexivity. }
  assert (H01 : length P0 <= length P1).
  { rewrite <- (len_map_ _ _ (fun a => vxor a w) P0).
    apply NoDup_incl_length.
    - apply nodup_map_inj; [| apply nodup_filter_, nodup_ker].
      apply Hinj. intros x Hx. apply filter_In in Hx. exact (proj1 Hx).
    - intros y Hy. apply in_map_iff in Hy. destruct Hy as [a [<- Ha]].
      apply filter_In in Ha. destruct Ha as [Ha Hfa].
      destruct (Hclos a Ha) as [Hin Hv]. apply filter_In. split; [exact Hin |].
      rewrite Hv. destruct (f a); [discriminate | reflexivity]. }
  assert (H10 : length P1 <= length P0).
  { rewrite <- (len_map_ _ _ (fun a => vxor a w) P1).
    apply NoDup_incl_length.
    - apply nodup_map_inj; [| apply nodup_filter_, nodup_ker].
      apply Hinj. intros x Hx. apply filter_In in Hx. exact (proj1 Hx).
    - intros y Hy. apply in_map_iff in Hy. destruct Hy as [a [<- Ha]].
      apply filter_In in Ha. destruct Ha as [Ha Hfa].
      destruct (Hclos a Ha) as [Hin Hv]. apply filter_In. split; [exact Hin |].
      rewrite Hv, Hfa. reflexivity. }
  lia.
Qed.

(* The solution count: |ker| * 2^rank = 2^m. *)
Theorem ker_count :
  forall m F, (forall f, In f F -> linear m f) ->
    length (ker m F) * 2 ^ rel_rank m F = 2 ^ m.
Proof.
  intros m F. induction F as [| f F IH]; intro HF; simpl.
  - rewrite length_allvecs. lia.
  - assert (HF' : forall g, In g F -> linear m g) by (intros g Hg; apply HF; right; exact Hg).
    destruct (existsb f (ker m F)) eqn:Hex.
    + apply existsb_exists in Hex. destruct Hex as [w [Hw Hfw]].
      pose proof (ker_halves m F f w HF' (HF f (or_introl eq_refl)) Hw Hfw) as Hh.
      rewrite <- (IH HF'), <- Hh. simpl. lia.
    + rewrite filter_all_; [simpl; exact (IH HF') |].
      intros a Ha. destruct (f a) eqn:Hfa; [| reflexivity].
      exfalso. assert (existsb f (ker m F) = true) by (apply existsb_exists; exists a; auto).
      congruence.
Qed.

Lemma pow2_le_inj : forall a b, 2 ^ a <= 2 ^ b -> a <= b.
Proof.
  intros a b H. destruct (Nat.le_gt_cases a b) as [Hle | Hgt]; [exact Hle |].
  pose proof (Nat.pow_lt_mono_r 2 b a ltac:(lia) Hgt). lia.
Qed.

Lemma zero_in_ker :
  forall m F, (forall f, In f F -> linear m f) -> In (repeat false m) (ker m F).
Proof.
  intros m F HF. apply in_ker. split; [apply repeat_length |].
  intros f Hf. apply linear_zero. exact (HF f Hf).
Qed.

Theorem rel_rank_le :
  forall m F, (forall f, In f F -> linear m f) -> rel_rank m F <= m /\ rel_rank m F <= length F.
Proof.
  intros m F HF. split.
  - apply pow2_le_inj. rewrite <- (ker_count m F HF).
    destruct (ker m F) eqn:Hk.
    + exfalso. pose proof (zero_in_ker m F HF) as H. rewrite Hk in H. exact H.
    + simpl. lia.
  - clear HF. induction F as [| f F IH]; simpl; [lia |]. destruct (existsb f (ker m F)); lia.
Qed.

(* dim H^1 = m - rank, as a count. *)
Theorem ker_count_pow :
  forall m F, (forall f, In f F -> linear m f) ->
    length (ker m F) = 2 ^ (m - rel_rank m F).
Proof.
  intros m F HF. pose proof (ker_count m F HF) as H.
  destruct (rel_rank_le m F HF) as [Hle _].
  assert (E : 2 ^ m = 2 ^ (m - rel_rank m F) * 2 ^ rel_rank m F)
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite E in H.
  apply (Nat.mul_cancel_r _ _ (2 ^ rel_rank m F)); [| exact H].
  apply Nat.pow_nonzero. lia.
Qed.

(* The rank depends only on the solution set: it is the rank of the relations, not of the list. *)
Theorem rel_rank_solution_set :
  forall m F F',
    (forall f, In f F -> linear m f) -> (forall f, In f F' -> linear m f) ->
    (forall a, length a = m -> ((forall f, In f F -> f a = false) <-> (forall f, In f F' -> f a = false))) ->
    rel_rank m F = rel_rank m F'.
Proof.
  intros m F F' HF HF' Hs.
  assert (Hin : forall a, In a (ker m F) <-> In a (ker m F')).
  { intro a. rewrite !in_ker. split; intros [Hl H]; split; try exact Hl; apply (Hs a Hl); exact H. }
  assert (Hlen : length (ker m F) = length (ker m F')).
  { apply Nat.le_antisymm; apply NoDup_incl_length; try apply nodup_ker; intros a Ha; apply Hin;
      exact Ha. }
  rewrite (ker_count_pow m F HF), (ker_count_pow m F' HF') in Hlen.
  destruct (rel_rank_le m F HF) as [H1 _]. destruct (rel_rank_le m F' HF') as [H2 _].
  assert (m - rel_rank m F = m - rel_rank m F').
  { apply Nat.le_antisymm; apply pow2_le_inj; lia. }
  lia.
Qed.

Theorem rel_rank_zero_iff :
  forall m F, (forall f, In f F -> linear m f) ->
    (rel_rank m F = 0 <-> forall f a, In f F -> length a = m -> f a = false).
Proof.
  intros m F HF. split.
  - intros H0 f a Hf Ha.
    assert (Hfull : length (ker m F) = length (allvecs m))
      by (rewrite (ker_count_pow m F HF), H0, length_allvecs, Nat.sub_0_r; reflexivity).
    assert (Hall : forall F0, (forall g, In g F0 -> In g F) ->
              length (ker m F0) = length (allvecs m) ->
              forall b, In b (allvecs m) -> In b (ker m F0)).
    { clear f a Hf Ha. induction F0 as [| g F0 IH]; intros Hsub HL b Hb; [exact Hb |].
      simpl in HL |- *.
      assert (HL0 : length (ker m F0) = length (allvecs m)).
      { apply Nat.le_antisymm.
        - apply NoDup_incl_length; [apply nodup_ker |]. intros x Hx.
          apply in_allvecs. exact (proj1 (proj1 (in_ker m F0 x) Hx)).
        - rewrite <- HL. apply filter_le_. }
      pose proof (IH (fun h Hh => Hsub h (or_intror Hh)) HL0 b Hb) as Hk.
      apply filter_In. split; [exact Hk |].
      rewrite <- HL0 in HL. exact (filter_full_ _ _ _ HL b Hk). }
    pose proof (Hall F (fun g Hg => Hg) Hfull a (proj2 (in_allvecs m a) Ha)) as Hk.
    exact (proj2 (proj1 (in_ker m F a) Hk) f Hf).
  - intro Hz. clear HF. induction F as [| f F IH]; simpl; [reflexivity |].
    rewrite IH by (intros g a Hg Ha; apply Hz; [right |]; assumption).
    destruct (existsb f (ker m F)) eqn:Hex; [| reflexivity].
    apply existsb_exists in Hex. destruct Hex as [a [Ha Hfa]].
    rewrite (Hz f a (or_introl eq_refl) (proj1 (proj1 (in_ker m F a) Ha))) in Hfa. discriminate.
Qed.

(* ================================================================
   Z/2 labelings of the 2-complex.
   ================================================================ *)

(* The non-tree edges Xs labeled by the vector a. *)
Fixpoint assign (Xs : list (nat * nat)) (a : list bool) : list (@edge bool) :=
  match Xs, a with
  | (u, v) :: Xs', g :: a' => (u, v, g) :: assign Xs' a'
  | _, _ => []
  end.

Definition labels (X : list (@edge bool)) : list bool := map (fun x => let '(_, _, g) := x in g) X.

Definition zhol (L : list (@edge bool)) (w : list step) : bool := hol xorb false (fun x => x) L w.

(* The relation of cell c, as a functional on generator vectors. *)
Definition rel_fun (n : nat) (Xs : list (nat * nat)) (c : cell) : list bool -> bool :=
  fun a => zhol (assign Xs a) (gen_word n (snd c)).

Definition rel_funs (n : nat) (Xs : list (nat * nat)) (C : list cell) := map (rel_fun n Xs) C.

(* The representatives of H^1 and the rank of the relations, for tree T, extra edges Xs, cells C. *)
Definition Z2reps (T : list (@edge bool)) (Xs : list (nat * nat)) (C : list cell) :=
  ker (length Xs) (rel_funs (length T) Xs C).

Definition Z2rank (T : list (@edge bool)) (Xs : list (nat * nat)) (C : list cell) :=
  rel_rank (length Xs) (rel_funs (length T) Xs C).

Lemma shape_assign : forall Xs a, length a = length Xs -> shape (assign Xs a) = Xs.
Proof.
  induction Xs as [| [u v] Xs IH]; intros [| g a] H; simpl in *; try discriminate; [reflexivity |].
  rewrite IH by lia. reflexivity.
Qed.

Lemma labels_assign : forall Xs a, length a = length Xs -> labels (assign Xs a) = a.
Proof.
  induction Xs as [| [u v] Xs IH]; intros [| g a] H; simpl in *; try discriminate; [reflexivity |].
  rewrite IH by lia. reflexivity.
Qed.

Lemma assign_labels : forall X, assign (shape X) (labels X) = X.
Proof. induction X as [| [[u v] g] X IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma length_labels : forall X, length (labels X) = length X.
Proof. intro X. apply len_map_. Qed.

Fixpoint wsum (a : list bool) (w : list step) : bool :=
  match w with
  | [] => false
  | (i, _) :: w' => xorb (wsum a w') (nth i a false)
  end.

Lemma lab_assign :
  forall Xs a s, length a = length Xs -> lab_of false (fun x => x) (assign Xs a) s = nth (fst s) a false.
Proof.
  intros Xs a [i o]. unfold lab_of. simpl. revert a i.
  induction Xs as [| [u v] Xs IH]; intros [| g a] i H; simpl in *; try discriminate.
  - destruct i; reflexivity.
  - destruct i as [| i]; simpl; [destruct o; reflexivity |]. apply IH. lia.
Qed.

Lemma zhol_assign : forall Xs a w, length a = length Xs -> zhol (assign Xs a) w = wsum a w.
Proof.
  intros Xs a w H. unfold zhol. induction w as [| [i o] w IH]; simpl; [reflexivity |].
  rewrite IH, (lab_assign Xs a (i, o) H). reflexivity.
Qed.

Lemma nth_vxor :
  forall a b i, length a = length b -> nth i (vxor a b) false = xorb (nth i a false) (nth i b false).
Proof.
  induction a as [| x a IH]; intros [| y b] i H; simpl in *; try discriminate.
  - destruct i; reflexivity.
  - destruct i; [reflexivity | apply IH; lia].
Qed.

Lemma rel_fun_linear : forall n Xs c, linear (length Xs) (rel_fun n Xs c).
Proof.
  intros n Xs c a b Ha Hb. unfold rel_fun.
  rewrite !zhol_assign; [| lia | lia | rewrite vxor_len; lia].
  induction (gen_word n (snd c)) as [| [i o] w IH]; simpl; [reflexivity |].
  rewrite IH, nth_vxor by lia.
  destruct (wsum a w), (wsum b w), (nth i a false), (nth i b false); reflexivity.
Qed.

Lemma rel_funs_linear : forall n Xs C f, In f (rel_funs n Xs C) -> linear (length Xs) f.
Proof.
  intros n Xs C f H. unfold rel_funs in H. apply in_map_iff in H.
  destruct H as [c [<- _]]. apply rel_fun_linear.
Qed.

  Lemma z2_rels_iff :
    forall T Xs C a, length a = length Xs ->
      (cocycle xorb false (fun x => x) (triv false T ++ assign Xs a) C
       <-> forall f, In f (rel_funs (length T) Xs C) -> f a = false).
  Proof.
    intros T Xs C a Ha.
    rewrite (relations_in_generators xorb false (fun x => x) xor_id_l xor_id_r xor_inv_r
               (triv false T) (assign Xs a) C (idlab_triv false T)), length_triv.
    unfold rels_hold, rel_funs. split.
    - intros H f Hf. apply in_map_iff in Hf. destruct Hf as [c [<- Hc]]. exact (H c Hc).
    - intros H c Hc. apply (H (rel_fun (length T) Xs c)). apply in_map_iff. exists c. auto.
  Qed.

(* The counting theorem over Z/2. For a spanning tree T (rooted at r) of the graph T ++ Xs and
   2-cells C (closed walks): the list Z2reps of generator vectors has no duplicates and length
   2^(|Xs| - rank) with rank <= |Xs| and rank <= |C|; its members are exactly the vectors whose
   tree-fixed labeling is a cocycle; every cocycle of the complex is cohomologous to the labeling of
   some member; and distinct members are not cohomologous. So H^1(K; Z/2) has exactly
   2^(|Xs| - rank) elements, |Xs| = |E| - |V| + 1, and dim H^1 = (|E| - |V| + 1) - rank. *)
Theorem nerve_H1_Z2_count :
  forall r T Xs C,
    tree r T ->
    (forall u v, In (u, v) Xs -> In u (r :: verts T) /\ In v (r :: verts T)) ->
    wf_cells (shape T ++ Xs) C ->
    NoDup (Z2reps T Xs C) /\
    length (Z2reps T Xs C) = 2 ^ (length Xs - Z2rank T Xs C) /\
    Z2rank T Xs C <= length Xs /\ Z2rank T Xs C <= length C /\
    (forall a, In a (Z2reps T Xs C)
               <-> length a = length Xs
                   /\ cocycle xorb false (fun x => x) (triv false T ++ assign Xs a) C) /\
    (forall L, shape L = shape T ++ Xs -> cocycle xorb false (fun x => x) L C ->
       exists a, In a (Z2reps T Xs C)
                 /\ cohomologous xorb (fun x => x) L (triv false T ++ assign Xs a)) /\
    (forall a1 a2, In a1 (Z2reps T Xs C) -> In a2 (Z2reps T Xs C) ->
       cohomologous xorb (fun x => x) (triv false T ++ assign Xs a1) (triv false T ++ assign Xs a2) ->
       a1 = a2).
Proof.
  intros r T Xs C HT Hsp Hwf.
  set (X0 := assign Xs (repeat false (length Xs))).
  assert (EX0 : shape X0 = Xs) by (apply shape_assign; apply repeat_length).
  assert (Hsp0 : spanned r T X0).
  { intros u v g Hin. apply Hsp. rewrite <- EX0. exact (in_shape X0 u v g Hin). }
  assert (Hwf0 : wf_cells (shape (T ++ X0)) C) by (rewrite shape_app, EX0; exact Hwf).
  destruct (nerve_H1_classification xorb false (fun x => x) xor_assoc xor_id_l xor_id_r xor_inv_r
              xor_inv_l r T X0 C HT Hsp0 Hwf0) as [_ [Hsurj [_ _]]].
  pose proof (rel_funs_linear (length T) Xs C) as Hlin.
  destruct (rel_rank_le _ _ Hlin) as [Hr1 Hr2].
  unfold Z2reps, Z2rank. split; [apply nodup_ker | split; [| split; [| split; [| split; [| split]]]]].
  - apply ker_count_pow. exact Hlin.
  - exact Hr1.
  - unfold rel_funs in Hr2. rewrite len_map_ in Hr2. exact Hr2.
  - intro a. rewrite in_ker. split.
    + intros [Ha H]. split; [exact Ha |]. apply z2_rels_iff; assumption.
    + intros [Ha H]. split; [exact Ha |]. apply (z2_rels_iff T Xs C a Ha). exact H.
  - intros L EL HL. rewrite <- EX0, <- shape_app in EL.
    destruct (Hsurj L EL HL) as [X' [EX' [Hrel Hco]]].
    rewrite EX0 in EX'.
    assert (Hla : length (labels X') = length Xs)
      by (rewrite <- EX', length_labels, length_shape; reflexivity).
    exists (labels X'). rewrite <- EX', assign_labels. rewrite EX'. split; [| exact Hco].
    apply in_ker. split; [exact Hla |]. apply (z2_rels_iff T Xs C _ Hla).
    rewrite <- EX', assign_labels.
    apply (relations_in_generators xorb false (fun x => x) xor_id_l xor_id_r xor_inv_r (triv false T) X' C
             (idlab_triv false T)). rewrite length_triv. exact Hrel.
  - intros a1 a2 H1 H2 Hco.
    destruct (proj1 (in_ker _ _ a1) H1) as [Ha1 _]. destruct (proj1 (in_ker _ _ a2) H2) as [Ha2 _].
    assert (E1 : shape (assign Xs a1) = shape X0) by (rewrite EX0; apply shape_assign; exact Ha1).
    pose proof (proj1 (nerve_H1_abelian xorb false (fun x => x) xor_assoc xor_id_l xor_id_r
                         xor_inv_r xor_inv_l xorb_comm r T X0 HT Hsp0
                         (assign Xs a1) (assign Xs a2) E1) Hco) as E.
    rewrite <- (labels_assign Xs a1 Ha1), <- (labels_assign Xs a2 Ha2), E. reflexivity.
Qed.

(* Recovering betti_number: with no 2-cells the rank is 0 and the count is 2^b, where
   b + |V| = |E| + 1. *)
Corollary nerve_Z2_no_cells :
  forall r T Xs,
    tree r T ->
    (forall u v, In (u, v) Xs -> In u (r :: verts T) /\ In v (r :: verts T)) ->
    Z2rank T Xs [] = 0 /\ length (Z2reps T Xs []) = 2 ^ length Xs /\
    exists vs, NoDup vs /\
      (forall w, In w vs <-> In w (r :: verts (T ++ assign Xs (repeat false (length Xs))))) /\
      length Xs + length vs = length (T ++ assign Xs (repeat false (length Xs))) + 1.
Proof.
  intros r T Xs HT Hsp.
  set (X0 := assign Xs (repeat false (length Xs))).
  assert (EX0 : shape X0 = Xs) by (apply shape_assign; apply repeat_length).
  split; [reflexivity | split].
  - unfold Z2reps. simpl. apply length_allvecs.
  - assert (Hsp0 : forall u v g, In (u, v, g) X0 -> In u (r :: verts T) /\ In v (r :: verts T)).
    { intros u v g Hin. apply Hsp. rewrite <- EX0. exact (in_shape X0 u v g Hin). }
    destruct (betti_number r T X0 HT Hsp0) as [vs [Hnd [Hin Hlen]]].
    exists vs. split; [exact Hnd | split; [exact Hin |]].
    assert (E0 : length X0 = length Xs) by (rewrite <- (length_shape X0), EX0; reflexivity).
    rewrite <- E0. exact Hlen.
Qed.

(* Equality with the graph count holds exactly when the cells impose no relation. *)
Corollary nerve_Z2_full_iff :
  forall T Xs C,
    (length (Z2reps T Xs C) = 2 ^ length Xs <-> Z2rank T Xs C = 0) /\
    (Z2rank T Xs C = 0 <->
       forall a, length a = length Xs -> cocycle xorb false (fun x => x) (triv false T ++ assign Xs a) C).
Proof.
  intros T Xs C. pose proof (rel_funs_linear (length T) Xs C) as Hlin.
  destruct (rel_rank_le _ _ Hlin) as [Hr1 _].
  unfold Z2reps, Z2rank in *. split.
  - rewrite (ker_count_pow _ _ Hlin). split; intro H; [| rewrite H, Nat.sub_0_r; reflexivity].
    assert (length Xs - rel_rank (length Xs) (rel_funs (length T) Xs C) = length Xs)
      by (apply Nat.le_antisymm; [lia | apply pow2_le_inj; lia]).
    lia.
  - rewrite (rel_rank_zero_iff _ _ Hlin). split.
    + intros H a Ha. apply (z2_rels_iff T Xs C a Ha). intros f Hf. exact (H f a Hf Ha).
    + intros H f a Hf Ha. exact (proj1 (z2_rels_iff T Xs C a Ha) (H a Ha) f Hf).
Qed.

(* Adding a 2-cell never raises the count of classes. *)
Corollary nerve_Z2_cell_lowers :
  forall T Xs C c, length (Z2reps T Xs (c :: C)) <= length (Z2reps T Xs C).
Proof. intros T Xs C c. unfold Z2reps. simpl. apply filter_le_. Qed.

(* ================================================================
   Non-vacuity.
   ================================================================ *)

(* --- The triangle 0 -> 1 -> 2 (tree triT from CohomologyGraph.v), closing edge 2 -> 0. --- *)

Definition triXs : list (nat * nat) := [(2, 0)].

(* The filled triangle: the 2-cell 0 -> 1 -> 2 -> 0. *)
Definition triCell : cell := (0, [(0, true); (1, true); (2, true)]).

Lemma tri_span :
  forall u v, In (u, v) triXs -> In u (0 :: verts triT) /\ In v (0 :: verts triT).
Proof. intros u v [H | []]. injection H as <- <-. simpl. auto 10. Qed.

Lemma tri_wf : wf_cells (shape triT ++ triXs) [triCell].
Proof.
  intros c [<- | []]. simpl.
  apply (w_fwd _ 0 1); [reflexivity |]. apply (w_fwd _ 1 2); [reflexivity |].
  apply (w_fwd _ 2 0); [reflexivity |]. apply w_nil.
Qed.

Lemma tri_wf_hollow : wf_cells (shape triT ++ triXs) [].
Proof. intros c []. Qed.

(* Hollow triangle: no relation, rank 0, two classes (H^1 = Z/2). *)
Example hollow_triangle : Z2rank triT triXs [] = 0 /\ Z2reps triT triXs [] = [[false]; [true]].
Proof. split; reflexivity. Qed.

(* Filled triangle: one independent relation, rank 1, one class (H^1 = 0). *)
Example filled_triangle : Z2rank triT triXs [triCell] = 1 /\ Z2reps triT triXs [triCell] = [[false]].
Proof. split; reflexivity. Qed.

(* The flip labeling: a nontrivial class on the graph (tri_flip_not_cohomologous_to_identity) that
   the filled triangle kills, since it is not a cocycle of the complex. *)
Example triangle_kills_flip :
  ~ cohomologous xorb (fun a => a) (triT ++ [(2, 0, true)]) (triT ++ [(2, 0, false)]) /\
  cocycle xorb false (fun x => x) (triT ++ [(2, 0, true)]) [] /\
  ~ cocycle xorb false (fun x => x) (triT ++ [(2, 0, true)]) [triCell].
Proof.
  split; [exact tri_flip_not_cohomologous_to_identity | split].
  - intros c [].
  - intro H. specialize (H triCell (or_introl eq_refl)). discriminate H.
Qed.

(* On the filled triangle every cocycle has a section: the class count 1 at work, through the
   general theorem (every hypothesis discharged). *)
Example filled_cocycle_has_section :
  forall L, shape L = [(0, 1); (1, 2); (2, 0)] ->
    cocycle xorb false (fun x => x) L [triCell] -> has_section xorb L.
Proof.
  intros L EL HL.
  destruct (nerve_H1_Z2_count 0 triT triXs [triCell] triT_tree tri_span tri_wf)
    as [_ [_ [_ [_ [_ [Hsurj _]]]]]].
  destruct (Hsurj L EL HL) as [a [Ha Hco]].
  change (Z2reps triT triXs [triCell]) with [[false]] in Ha.
  destruct Ha as [<- | []].
  apply (nerve_section_iff_coboundary xorb false (fun x => x) xor_assoc xor_id_l xor_id_r
           xor_inv_r xor_inv_l L [] (fun c H => match H with end)).
  replace (triv false L) with (triv false triT ++ assign triXs [false]).
  - exact (cohom_sym xorb false (fun x => x) xor_assoc xor_id_l xor_id_r xor_inv_r xor_inv_l
             _ _ Hco).
  - symmetry. rewrite (triv_shape false L (triT ++ assign triXs [false])); [reflexivity |].
    rewrite EL. reflexivity.
Qed.

(* --- The square 0 - 1 - 2 - 3 - 0 with the diagonal 0 -> 2. --- *)

(* Tree 0 -> 1 -> 2 -> 3 (edges 0, 1, 2); extra edges 3 -> 0 (edge 3) and 0 -> 2 (edge 4). *)
Definition sqT : list (@edge bool) := (([] ++ [(0, 1, false)]) ++ [(1, 2, false)]) ++ [(2, 3, false)].
Definition sqXs : list (nat * nat) := [(3, 0); (0, 2)].

(* Triangle 0 -> 1 -> 2 -> 0 (the diagonal traversed backward) and triangle 0 -> 2 -> 3 -> 0. *)
Definition sqA : cell := (0, [(0, true); (1, true); (4, false)]).
Definition sqB : cell := (0, [(4, true); (2, true); (3, true)]).
(* The square boundary 0 -> 1 -> 2 -> 3 -> 0: a 2-cell whose relation is implied by sqA and sqB. *)
Definition sqO : cell := (0, [(0, true); (1, true); (2, true); (3, true)]).

Lemma sqT_tree : tree 0 sqT.
Proof.
  unfold sqT. apply t_out.
  - apply t_out.
    + apply t_out; [apply t_nil | simpl; auto | simpl; intuition congruence].
    + simpl. auto 10.
    + simpl. intuition congruence.
  - simpl. auto 10.
  - simpl. intuition congruence.
Qed.

Lemma sq_span :
  forall u v, In (u, v) sqXs -> In u (0 :: verts sqT) /\ In v (0 :: verts sqT).
Proof. intros u v [H | [H | []]]; injection H as <- <-; simpl; auto 10. Qed.

Lemma sq_wf : wf_cells (shape sqT ++ sqXs) [sqA; sqB; sqO].
Proof.
  intros c [<- | [<- | [<- | []]]]; simpl.
  - apply (w_fwd _ 0 1); [reflexivity |]. apply (w_fwd _ 1 2); [reflexivity |].
    apply (w_bwd _ 2 0); [reflexivity |]. apply w_nil.
  - apply (w_fwd _ 0 2); [reflexivity |]. apply (w_fwd _ 2 3); [reflexivity |].
    apply (w_fwd _ 3 0); [reflexivity |]. apply w_nil.
  - apply (w_fwd _ 0 1); [reflexivity |]. apply (w_fwd _ 1 2); [reflexivity |].
    apply (w_fwd _ 2 3); [reflexivity |]. apply (w_fwd _ 3 0); [reflexivity |]. apply w_nil.
Qed.

(* No cells: b = 5 - 4 + 1 = 2, four classes. *)
Example square_hollow : Z2rank sqT sqXs [] = 0 /\ length (Z2reps sqT sqXs []) = 4.
Proof. split; reflexivity. Qed.

(* One filled triangle: rank 1, two classes. *)
Example square_one_triangle : Z2rank sqT sqXs [sqA] = 1 /\ length (Z2reps sqT sqXs [sqA]) = 2.
Proof. split; reflexivity. Qed.

(* Both triangles filled (a disk): rank 2, one class. *)
Example square_two_triangles :
  Z2rank sqT sqXs [sqA; sqB] = 2 /\ Z2reps sqT sqXs [sqA; sqB] = [[false; false]].
Proof. split; reflexivity. Qed.

(* Adding the square boundary as a third cell: its relation is implied, so the rank stays 2 with
   three cells (the rank counts independent relations, not cells). *)
Example square_dependent_cell :
  Z2rank sqT sqXs [sqO; sqA; sqB] = 2 /\ length (Z2reps sqT sqXs [sqO; sqA; sqB]) = 1.
Proof. split; reflexivity. Qed.

(* The general theorem's hypotheses hold on every instance. *)
Example nerve_instances_wf :
  (exists l, l = Z2reps triT triXs [triCell] /\
     NoDup l /\ length l = 2 ^ (length triXs - Z2rank triT triXs [triCell])) /\
  (exists l, l = Z2reps sqT sqXs [sqA; sqB; sqO] /\
     NoDup l /\ length l = 2 ^ (length sqXs - Z2rank sqT sqXs [sqA; sqB; sqO])).
Proof.
  split; eexists; split; try reflexivity.
  - destruct (nerve_H1_Z2_count 0 triT triXs [triCell] triT_tree tri_span tri_wf) as [H1 [H2 _]].
    split; assumption.
  - destruct (nerve_H1_Z2_count 0 sqT sqXs [sqA; sqB; sqO] sqT_tree sq_span sq_wf) as [H1 [H2 _]].
    split; assumption.
Qed.
