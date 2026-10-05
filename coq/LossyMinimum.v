(* LossyMinimum.v: minimum coordination for non-invertible (lossy) networks, mechanized
   axiom-free. This closes gap 11 of REGIME-AUDIT.md ("Optimization: minimum coordination" in
   section 12, "none known") as far as an exact characterization, a decision procedure, hardness
   and the link to the invertible case go.

   Setting: reading A of LOSSY-NETWORKS.md, as in CohomologyGeneral.v, RootSet.v and
   LossyHardness.v. A network is a list G of edges (u, v, f) with f : V -> V an arbitrary map on one
   fiber V; a state s is a section when f (s u) = s v on every edge (msection s G).

   Coordination sets. A coordination deletes edges, identified by POSITION in G (so parallel copies
   of one edge are distinct edges, and no equality on maps is needed): F is a coordination set of G
   when it is a duplicate-free list of positions below |G| (cset G F); the residual network
   resid G F keeps the edges whose position is not in F. F is feasible (lfeasible G F) when the
   residual has a section, and k is the minimum coordination (is_lmin G k) when some feasible
   coordination set has k positions and every feasible one has at least k.

   Exact characterization (part 1, through RootSet.v).
     lfeasible_root_set       for ANY root set R and spanning forest Fr of the residual: F is
                              feasible iff some root assignment a drives a state satisfying every
                              residual edge (root_set_criterion_graph on the residual)
     lfeasible_iff_root_set   F is feasible iff the residual has a root set, a spanning forest and
                              a root assignment whose driven state satisfies every residual edge
                              (a root set always exists: trivial_forest)
     lmin_root_set            k is the minimum iff k is the least |F| with that property
     lmin_unique              the minimum is unique
   Decision procedure (finite fiber, enumerated by lv, decidable equality).
     sec_b_spec               sec_b decides whether a network has a section (search over one value
                              per vertex)
     lfeasible_decide_forest  with a spanning forest of the residual: feasibility is the search over
                              the product of the root domains (root_set_decide)
     lmin_le_b_spec           lmin_le_b G k = true iff a feasible coordination set of size <= k
                              exists (search over the subsets of positions)
     lmin_b_correct           lmin_b G is the minimum; lmin_decide: is_lmin G k <-> lmin_b G = k;
                              lmin_exists: the minimum exists
   Hardness (part 3).
     lmin_zero_iff_section    the minimum is 0 iff the network has a section
     lmin_zero_iff_sat        through the 3-SAT network of LossyHardness.v: the minimum of net f is
                              0 iff f is satisfiable (net_section_iff_sat)
     net_lmin_dichotomy       the minimum of net f is 0 if f is satisfiable and 1 otherwise
                              (deleting the pinning self-loop always suffices, no_pin_trivial)
     lmin_reduction           the reduction packaged: linear size (net_size), minimum 0 iff
                              satisfiable, minimum 1 iff unsatisfiable
   So deciding "minimum <= k" is NP-hard already for k = 0, and telling minimum 0 from minimum 1
   is NP-hard (no multiplicative approximation of the minimum is efficient unless P = NP), by the
   standard argument from these correctness and size theorems.
   Membership in NP.
     min_le_np_certificate    a feasible coordination set of size <= k exists iff some certificate
                              (F, t), F a list of positions and t one value per residual vertex,
                              passes the checker min_cert_ok (a length test, a duplicate test, a
                              range test, and one equality test per residual edge)
     min_cert_size            an accepted certificate has |F| <= min k |G| and |t| <= 2 |G|
     lmin_le_np               the same stated for the minimum: m <= k iff a certificate passes
   Invertible case (part 4).
     lift                     a group-labeled network as a lossy one under the regular action
                              (g acts by x |-> g x)
     lossy_min_is_gfes        on lifted networks, the lossy minimum is exactly the group feedback
                              edge set minimum: the least number of deleted edges leaving a
                              coboundary labeling (H^1 = 0 on the residual, section_iff_coboundary)
     lift_cycle_basis         per fundamental cycle: with the residual a spanning tree plus extra
                              edges, F is feasible iff every extra edge is balanced
                              (cycle_basis_criterion)
     group_tree_lmin_zero     a group-labeled tree (no cycle) has minimum 0
     group_lmin_le_nontree    with a spanning tree T and extra edges X, the minimum is at most |X|
     lossy_lmin_le_nontree    the lossy analogue needs an OUTWARD forest (rooted_coordination_suffices)
   The lossy minimum is not cycle-based.
     c22_lmin                 the C22 shape (two constant maps false and true into one vertex) has
                              minimum 1, although it is a tree (no cycle at all)
     lossy_min_exceeds_cycle_bounds
                              every lower bound on the lossy minimum that sees only cycles (takes
                              the same value on every tree as on the empty network) is 0 on C22,
                              strictly below its minimum 1; the group case has minimum 0 on every
                              tree (group_tree_lmin_zero)
   Non-vacuity.
     c22_*, diamond_lmin, two_lmin, scc_lmin, tri_lmin (a Z/2 triangle: 1 = gfes minimum),
     bow_lmin (the bowtie: 2 = gfes minimum, matching bowtie_min_two), fsat_lmin (0),
     funsat_lmin (1). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.RootSet NC.LossyHardness.
Import ListNotations.

(* ===================================================================== *)
(* Residual networks: deleting edges by position. *)

Definition memb (i : nat) (F : list nat) : bool := if in_dec Nat.eq_dec i F then true else false.

Lemma memb_spec : forall i F, memb i F = true <-> In i F.
Proof.
  intros i F. unfold memb. destruct (in_dec Nat.eq_dec i F); split; intro H;
    [exact i0 | reflexivity | discriminate | contradiction].
Qed.

Section Resid.
  Context {A : Type}.

  Fixpoint resid_from (i : nat) (G : list A) (F : list nat) : list A :=
    match G with
    | [] => []
    | x :: G' => if memb i F then resid_from (S i) G' F else x :: resid_from (S i) G' F
    end.

  (* The residual network: the edges of G whose position is not in F. *)
  Definition resid (G : list A) (F : list nat) : list A := resid_from 0 G F.

  (* A coordination set: duplicate-free positions of G. *)
  Definition cset (G : list A) (F : list nat) : Prop := NoDup F /\ forall i, In i F -> i < length G.

  Lemma resid_from_ext :
    forall G i F F', (forall j, In j F <-> In j F') -> resid_from i G F = resid_from i G F'.
  Proof.
    induction G as [| x G IH]; intros i F F' H; simpl; [reflexivity |].
    assert (E : memb i F = memb i F').
    { destruct (memb i F) eqn:E1, (memb i F') eqn:E2; try reflexivity.
      - apply memb_spec in E1. apply H in E1. apply memb_spec in E1. congruence.
      - apply memb_spec in E2. apply H in E2. apply memb_spec in E2. congruence. }
    rewrite E, (IH (S i) F F' H). reflexivity.
  Qed.

  Lemma resid_from_none :
    forall G i F, (forall j, In j F -> j < i \/ i + length G <= j) -> resid_from i G F = G.
  Proof.
    induction G as [| x G IH]; intros i F H; simpl; [reflexivity |].
    destruct (memb i F) eqn:E.
    - apply memb_spec in E. destruct (H i E); simpl in *; lia.
    - f_equal. apply IH. intros j Hj. destruct (H j Hj); simpl in *; lia.
  Qed.

  Lemma resid_from_all :
    forall G i F, (forall j, i <= j < i + length G -> In j F) -> resid_from i G F = [].
  Proof.
    induction G as [| x G IH]; intros i F H; simpl; [reflexivity |].
    replace (memb i F) with true by (symmetry; apply memb_spec; apply H; simpl; lia).
    apply IH. intros j Hj. apply H. simpl. lia.
  Qed.

  Lemma resid_from_app :
    forall G H i F, resid_from i (G ++ H) F = resid_from i G F ++ resid_from (i + length G) H F.
  Proof.
    induction G as [| x G IH]; intros H i F; simpl.
    - rewrite Nat.add_0_r. reflexivity.
    - rewrite IH. replace (S i + length G) with (i + S (length G)) by lia.
      destruct (memb i F); reflexivity.
  Qed.

  Lemma resid_from_incl : forall G i F x, In x (resid_from i G F) -> In x G.
  Proof.
    induction G as [| y G IH]; intros i F x Hx; simpl in *; [exact Hx |].
    destruct (memb i F); [right; exact (IH _ _ _ Hx) |].
    destruct Hx as [<- | Hx]; [left; reflexivity | right; exact (IH _ _ _ Hx)].
  Qed.

  Lemma resid_from_length : forall G i F, length (resid_from i G F) <= length G.
  Proof.
    induction G as [| y G IH]; intros i F; simpl; [lia |].
    destruct (memb i F); simpl; specialize (IH (S i) F); lia.
  Qed.

  Lemma resid_nil : forall G, resid G [] = G.
  Proof. intro G. apply resid_from_none. intros j []. Qed.

  Lemma resid_all : forall G, resid G (seq 0 (length G)) = [].
  Proof. intro G. apply resid_from_all. intros j Hj. apply in_seq. lia. Qed.

  Lemma cset_all : forall G, cset G (seq 0 (length G)).
  Proof.
    intro G. split; [apply seq_NoDup |]. intros i Hi. apply in_seq in Hi. lia.
  Qed.

  Lemma cset_nil : forall G, cset G [].
  Proof. intro G. split; [constructor | intros i []]. Qed.
End Resid.

Lemma resid_from_map :
  forall (A B : Type) (h : A -> B) G i F, resid_from i (map h G) F = map h (resid_from i G F).
Proof.
  intros A B h. induction G as [| x G IH]; intros i F; simpl; [reflexivity |].
  destruct (memb i F); simpl; rewrite IH; reflexivity.
Qed.

Lemma cset_map :
  forall (A B : Type) (h : A -> B) G F, cset (map h G) F <-> cset G F.
Proof. intros A B h G F. unfold cset. rewrite map_length. tauto. Qed.

(* ===================================================================== *)
(* Feasibility and the minimum. *)

Section Lossy.
  Context {V : Type}.

  Definition lfeasible (G : list (@edge (V -> V))) (F : list nat) : Prop :=
    exists s, msection s (resid G F).

  (* k is the minimum coordination of G. *)
  Definition is_lmin (G : list (@edge (V -> V))) (k : nat) : Prop :=
    (exists F, cset G F /\ length F = k /\ lfeasible G F) /\
    (forall F, cset G F -> lfeasible G F -> k <= length F).

  Theorem lmin_unique : forall G k k', is_lmin G k -> is_lmin G k' -> k = k'.
  Proof.
    intros G k k' [[F [HF [Hl Hf]]] Hk] [[F' [HF' [Hl' Hf']]] Hk'].
    pose proof (Hk F' HF' Hf'). pose proof (Hk' F HF Hf). lia.
  Qed.

  (* The minimum is 0 iff the network already has a section. *)
  Theorem lmin_zero_iff_section : forall G, is_lmin G 0 <-> exists s, msection s G.
  Proof.
    intro G. split.
    - intros [[F [_ [Hl [s Hs]]]] _]. destruct F; [| discriminate].
      exists s. rewrite resid_nil in Hs. exact Hs.
    - intros [s Hs]. split; [| intros; lia].
      exists []. split; [apply cset_nil | split; [reflexivity |]].
      exists s. rewrite resid_nil. exact Hs.
  Qed.

  (* The decision problem "minimum <= k" is the existence of a small feasible coordination set. *)
  Theorem lmin_le_iff :
    forall G m, is_lmin G m ->
      forall k, m <= k <-> exists F, cset G F /\ length F <= k /\ lfeasible G F.
  Proof.
    intros G m [[F [HF [Hl Hf]]] Hm] k. split.
    - intro H. exists F. split; [exact HF | split; [lia | exact Hf]].
    - intros [F' [HF' [Hl' Hf']]]. pose proof (Hm F' HF' Hf'). lia.
  Qed.

  (* Deleting every edge is feasible (the fiber is inhabited). *)
  Theorem delete_all_feasible : forall (v0 : V) G, lfeasible G (seq 0 (length G)).
  Proof. intros v0 G. exists (fun _ => v0). rewrite resid_all. intros x []. Qed.

  Theorem lmin_le_length : forall (v0 : V) G k, is_lmin G k -> k <= length G.
  Proof.
    intros v0 G k [_ Hk]. rewrite <- (seq_length (length G) 0).
    exact (Hk _ (cset_all G) (delete_all_feasible v0 G)).
  Qed.

  (* ----- the exact characterization through the root-set criterion ----- *)

  (* For any root set R of the residual and any spanning forest Fr from R: F is feasible iff some
     root assignment drives a state satisfying every residual edge. *)
  Theorem lfeasible_root_set :
    forall G F R Fr, spanning_forest R (resid G F) Fr ->
      (lfeasible G F <-> exists a, msection (drive Fr a) (resid G F)).
  Proof. intros G F R Fr Hsf. exact (root_set_criterion_graph R (resid G F) Fr Hsf). Qed.

  (* Every network has a root set: all of its vertices, with the empty forest. *)
  Theorem trivial_forest : forall es : list (@edge (V -> V)), spanning_forest (verts es) es [].
  Proof.
    intro es. split; [apply f_nil | split; [intros x [] |]].
    intros w Hw. apply in_or_app. left. exact Hw.
  Qed.

  Definition root_set_ok (es : list (@edge (V -> V))) : Prop :=
    exists R Fr a, spanning_forest R es Fr /\ msection (drive Fr a) es.

  Theorem lfeasible_iff_root_set : forall G F, lfeasible G F <-> root_set_ok (resid G F).
  Proof.
    intros G F. split.
    - intro H. exists (verts (resid G F)), [].
      destruct (proj1 (lfeasible_root_set G F _ _ (trivial_forest (resid G F))) H) as [a Ha].
      exists a. split; [apply trivial_forest | exact Ha].
    - intros [R [Fr [a [Hsf Ha]]]]. exact (proj2 (lfeasible_root_set G F R Fr Hsf) (ex_intro _ a Ha)).
  Qed.

  (* The minimum is the least |F| whose residual satisfies the root-set criterion. *)
  Theorem lmin_root_set :
    forall G k, is_lmin G k <->
      ((exists F, cset G F /\ length F = k /\ root_set_ok (resid G F)) /\
       (forall F, cset G F -> root_set_ok (resid G F) -> k <= length F)).
  Proof.
    intros G k. unfold is_lmin. split; intros [[F [HF [Hl Hf]]] Hk]; split.
    - exists F. split; [exact HF | split; [exact Hl | apply lfeasible_iff_root_set; exact Hf]].
    - intros F' HF' Hf'. apply Hk; [exact HF' | apply lfeasible_iff_root_set; exact Hf'].
    - exists F. split; [exact HF | split; [exact Hl | apply lfeasible_iff_root_set; exact Hf]].
    - intros F' HF' Hf'. apply Hk; [exact HF' | apply lfeasible_iff_root_set; exact Hf'].
  Qed.

  (* A residual that is itself an outward forest is feasible. *)
  Theorem forest_residual_feasible :
    forall (v0 : V) G F R, oforest R (resid G F) -> lfeasible G F.
  Proof.
    intros v0 G F R HF. exists (drive (resid G F) (fun _ => v0)). exact (out_forest_section R _ HF _).
  Qed.

  (* Lossy analogue of "coordinate the non-tree edges": with an OUTWARD forest T followed by
     extra edges X, the minimum is at most |X|. *)
  Theorem lossy_lmin_le_nontree :
    forall (v0 : V) R T X k, oforest R T -> is_lmin (T ++ X) k -> k <= length X.
  Proof.
    intros v0 R T X k HT [_ Hk].
    set (F := seq (length T) (length X)).
    assert (HR : resid (T ++ X) F = T).
    { unfold resid. rewrite resid_from_app, (resid_from_all X (0 + length T) F), app_nil_r.
      - apply resid_from_none. intros j Hj. apply in_seq in Hj. lia.
      - intros j Hj. apply in_seq. lia. }
    assert (HF : cset (T ++ X) F).
    { split; [apply seq_NoDup |]. intros i Hi. apply in_seq in Hi. rewrite app_length. lia. }
    pose proof (Hk F HF (forest_residual_feasible v0 _ F R ltac:(rewrite HR; exact HT))) as H.
    unfold F in H. rewrite seq_length in H. exact H.
  Qed.
End Lossy.

(* ===================================================================== *)
(* Subsets of positions, and a least-witness search. *)

Fixpoint subsets (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: l' => map (cons x) (subsets l') ++ subsets l'
  end.

Lemma filter_subsets : forall p l, In (filter p l) (subsets l).
Proof.
  intros p. induction l as [| x l IH]; simpl; [left; reflexivity |].
  apply in_or_app. destruct (p x); [left; apply in_map; exact IH | right; exact IH].
Qed.

Lemma subsets_spec : forall l S, In S (subsets l) -> incl S l /\ (NoDup l -> NoDup S).
Proof.
  induction l as [| x l IH]; intros S HS; simpl in HS.
  - destruct HS as [<- | []]. split; [intros y [] | intros _; constructor].
  - apply in_app_or in HS. destruct HS as [HS | HS].
    + apply in_map_iff in HS. destruct HS as [S' [<- HS']]. destruct (IH S' HS') as [Hi Hn].
      split.
      * intros y [<- | Hy]; [left; reflexivity | right; exact (Hi y Hy)].
      * intro Hnd. inversion Hnd as [| x' l' Hx Hnd']. subst.
        constructor; [intro H; exact (Hx (Hi x H)) | exact (Hn Hnd')].
    + destruct (IH S HS) as [Hi Hn]. split.
      * intros y Hy. right. exact (Hi y Hy).
      * intro Hnd. inversion Hnd. exact (Hn ltac:(assumption)).
Qed.

Fixpoint least_from (p : nat -> bool) (k fuel : nat) : nat :=
  match fuel with
  | 0 => k
  | S n => if p k then k else least_from p (S k) n
  end.

Lemma least_from_spec :
  forall p fuel k, p (k + fuel) = true ->
    p (least_from p k fuel) = true /\ k <= least_from p k fuel /\
    forall j, k <= j < least_from p k fuel -> p j = false.
Proof.
  intros p. induction fuel as [| n IH]; intros k H; simpl.
  - rewrite Nat.add_0_r in H. split; [exact H | split; [lia | intros; lia]].
  - destruct (p k) eqn:E; [split; [exact E | split; [lia | intros; lia]] |].
    replace (k + S n) with (S k + n) in H by lia. destruct (IH (S k) H) as [H1 [H2 H3]].
    split; [exact H1 | split; [lia |]]. intros j Hj.
    destruct (Nat.eq_dec j k) as [-> | Hne]; [exact E |]. apply H3. lia.
Qed.

Lemma nodup_same_length :
  forall (l l' : list nat), NoDup l -> NoDup l' -> (forall x, In x l <-> In x l') ->
    length l = length l'.
Proof.
  intros l l' H H' E.
  pose proof (NoDup_incl_length H (fun x Hx => proj1 (E x) Hx)).
  pose proof (NoDup_incl_length H' (fun x Hx => proj2 (E x) Hx)). lia.
Qed.

(* ===================================================================== *)
(* The decision procedure on a finite fiber. *)

Section Decide.
  Context {V : Type}.
  Variable Vdec : forall x y : V, {x = y} + {x <> y}.
  Variable v0 : V.
  Variable lv : list V.
  Hypothesis lv_full : forall x, In x lv.

  (* Section existence: a search over one value per vertex (the trivial root set). *)
  Definition sec_b (es : list (@edge (V -> V))) : bool :=
    existsb (fun t => msection_b Vdec (assign v0 (nodup Nat.eq_dec (verts es)) t) es)
            (tuples lv (length (nodup Nat.eq_dec (verts es)))).

  Theorem sec_b_spec : forall es, sec_b es = true <-> exists s, msection s es.
  Proof.
    intro es. rewrite (np_certificate V Vdec v0 lv es lv_full). unfold sec_b.
    rewrite existsb_exists. reflexivity.
  Qed.

  (* With a spanning forest of the residual, feasibility is the search over the product of the
     root domains of RootSet.root_set_decide. *)
  Theorem lfeasible_decide_forest :
    forall G F R Fr, spanning_forest R (resid G F) Fr ->
      (lfeasible G F <-> existsb (rs_ok Vdec v0 R (resid G F) Fr) (tuples lv (length R)) = true).
  Proof. intros G F R Fr Hsf. exact (root_set_decide Vdec v0 lv R (resid G F) Fr Hsf lv_full). Qed.

  (* "minimum <= k", by search over the subsets of positions. *)
  Definition lmin_le_b (G : list (@edge (V -> V))) (k : nat) : bool :=
    existsb (fun S => Nat.leb (length S) k && sec_b (resid G S)) (subsets (seq 0 (length G))).

  Theorem lmin_le_b_spec :
    forall G k, lmin_le_b G k = true <-> exists F, cset G F /\ length F <= k /\ lfeasible G F.
  Proof.
    intros G k. unfold lmin_le_b. rewrite existsb_exists. split.
    - intros [S [HS Hb]]. apply andb_true_iff in Hb. destruct Hb as [Hl Hs].
      destruct (subsets_spec _ S HS) as [Hi Hn]. exists S. split; [split |].
      + exact (Hn (seq_NoDup _ _)).
      + intros i Hin. apply Hi in Hin. apply in_seq in Hin. lia.
      + split; [apply Nat.leb_le; exact Hl | apply sec_b_spec; exact Hs].
    - intros [F [[Hnd Hb] [Hl Hf]]].
      set (S := filter (fun i => memb i F) (seq 0 (length G))).
      assert (E : forall j, In j S <-> In j F).
      { intro j. unfold S. rewrite filter_In, memb_spec, in_seq. split; [tauto |].
        intro H. split; [split; [lia | simpl; exact (Hb j H)] | exact H]. }
      exists S. split; [apply filter_subsets |]. apply andb_true_iff. split.
      + apply Nat.leb_le. rewrite (nodup_same_length S F); [exact Hl | | exact Hnd | exact E].
        apply rs_nodup_filter. apply seq_NoDup.
      + apply sec_b_spec. unfold resid. rewrite (resid_from_ext G 0 S F E). exact Hf.
  Qed.

  (* The minimum, computed. *)
  Definition lmin_b (G : list (@edge (V -> V))) : nat := least_from (lmin_le_b G) 0 (length G).

  Theorem lmin_b_correct : forall G, is_lmin G (lmin_b G).
  Proof.
    intro G.
    assert (Htop : lmin_le_b G (0 + length G) = true).
    { apply lmin_le_b_spec. exists (seq 0 (length G)).
      split; [apply cset_all | split; [rewrite seq_length; lia | exact (delete_all_feasible v0 G)]]. }
    destruct (least_from_spec (lmin_le_b G) (length G) 0 Htop) as [H1 [_ H3]].
    fold (lmin_b G) in H1, H3.
    apply lmin_le_b_spec in H1. destruct H1 as [F [HF [Hl Hf]]].
    assert (Low : forall F', cset G F' -> lfeasible G F' -> lmin_b G <= length F').
    { intros F' HF' Hf'. destruct (Nat.le_gt_cases (lmin_b G) (length F')) as [H | H]; [exact H |].
      exfalso. assert (Hp : lmin_le_b G (length F') = true).
      { apply lmin_le_b_spec. exists F'. split; [exact HF' | split; [lia | exact Hf']]. }
      rewrite (H3 (length F') ltac:(lia)) in Hp. discriminate. }
    split; [| exact Low].
    exists F. split; [exact HF | split; [| exact Hf]].
    pose proof (Low F HF Hf). lia.
  Qed.

  Theorem lmin_decide : forall G k, is_lmin G k <-> lmin_b G = k.
  Proof.
    intros G k. split.
    - intro H. exact (lmin_unique G _ _ (lmin_b_correct G) H).
    - intros <-. exact (lmin_b_correct G).
  Qed.

  Theorem lmin_exists : forall G : list (@edge (V -> V)), exists k, is_lmin G k.
  Proof. intro G. exists (lmin_b G). exact (lmin_b_correct G). Qed.

  (* ----- membership in NP: a certificate is a coordination set plus one value per vertex ----- *)

  Fixpoint nodup_b (l : list nat) : bool :=
    match l with
    | [] => true
    | x :: l' => negb (memb x l') && nodup_b l'
    end.

  Lemma nodup_b_spec : forall l, nodup_b l = true <-> NoDup l.
  Proof.
    induction l as [| x l IH]; simpl; [split; [constructor | reflexivity] |].
    rewrite andb_true_iff, IH, negb_true_iff. split.
    - intros [Hx Hn]. constructor; [| exact Hn]. intro H. apply memb_spec in H. congruence.
    - intro H. inversion H as [| x' l' Hx Hn]. subst. split; [| exact Hn].
      destruct (memb x l) eqn:E; [apply memb_spec in E; contradiction | reflexivity].
  Qed.

  Definition cset_b (G : list (@edge (V -> V))) (F : list nat) : bool :=
    nodup_b F && forallb (fun i => Nat.ltb i (length G)) F.

  Lemma cset_b_spec : forall G F, cset_b G F = true <-> cset G F.
  Proof.
    intros G F. unfold cset_b, cset. rewrite andb_true_iff, nodup_b_spec, forallb_forall.
    split; intros [H1 H2]; split; try exact H1; intros i Hi; apply Nat.ltb_lt; exact (H2 i Hi).
  Qed.

  Definition rverts (G : list (@edge (V -> V))) (F : list nat) : list nat :=
    nodup Nat.eq_dec (verts (resid G F)).

  (* The checker: a length test, a duplicate test, a range test, and one equality test per
     residual edge. *)
  Definition min_cert_ok (G : list (@edge (V -> V))) (k : nat) (F : list nat) (t : list V) : bool :=
    Nat.leb (length F) k && cset_b G F && msection_b Vdec (assign v0 (rverts G F) t) (resid G F).

  Theorem min_le_np_certificate :
    forall G k,
      (exists F, cset G F /\ length F <= k /\ lfeasible G F) <->
      exists F t, In t (tuples lv (length (rverts G F))) /\ min_cert_ok G k F t = true.
  Proof.
    intros G k. split.
    - intros [F [HF [Hl Hf]]].
      destruct (proj1 (np_certificate V Vdec v0 lv (resid G F) lv_full) Hf) as [t [Ht Hok]].
      exists F, t. split; [exact Ht |]. unfold min_cert_ok.
      rewrite (proj2 (Nat.leb_le _ _) Hl), (proj2 (cset_b_spec G F) HF). exact Hok.
    - intros [F [t [_ Hok]]]. unfold min_cert_ok in Hok.
      apply andb_true_iff in Hok. destruct Hok as [Hok Hs]. apply andb_true_iff in Hok.
      destruct Hok as [Hl HF]. exists F. split; [apply cset_b_spec; exact HF |].
      split; [apply Nat.leb_le; exact Hl |].
      exists (assign v0 (rverts G F) t). apply (msection_b_spec Vdec). exact Hs.
  Qed.

  Lemma verts_length : forall (es : list (@edge (V -> V))), length (verts es) = 2 * length es.
  Proof. induction es as [| [[u v] f] es IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

  Lemma nodup_length_le : forall (l : list nat), length (nodup Nat.eq_dec l) <= length l.
  Proof.
    intro l. apply NoDup_incl_length; [apply NoDup_nodup |]. intros x Hx.
    exact (proj1 (nodup_In Nat.eq_dec l x) Hx).
  Qed.

  (* The certificate is small: |F| <= k, |F| <= |G|, and t has at most 2 |G| entries. *)
  Theorem min_cert_size :
    forall G k F t, min_cert_ok G k F t = true -> In t (tuples lv (length (rverts G F))) ->
      length F <= k /\ length F <= length G /\ length t <= 2 * length G.
  Proof.
    intros G k F t Hok Ht. unfold min_cert_ok in Hok.
    apply andb_true_iff in Hok. destruct Hok as [Hok _]. apply andb_true_iff in Hok.
    destruct Hok as [Hl HF]. apply Nat.leb_le in Hl. apply cset_b_spec in HF.
    destruct HF as [Hnd Hb]. split; [exact Hl | split].
    - rewrite <- (seq_length (length G) 0). apply NoDup_incl_length; [exact Hnd |].
      intros i Hi. apply in_seq. split; [lia | simpl; exact (Hb i Hi)].
    - apply tuples_spec in Ht. destruct Ht as [Ht _]. rewrite Ht. unfold rverts.
      pose proof (nodup_length_le (verts (resid G F))) as H1. rewrite verts_length in H1.
      pose proof (resid_from_length G 0 F) as H2. unfold resid in *. lia.
  Qed.

  (* The same, for the minimum itself: m <= k iff some certificate passes. *)
  Theorem lmin_le_np :
    forall G m k, is_lmin G m ->
      (m <= k <-> exists F t, In t (tuples lv (length (rverts G F))) /\ min_cert_ok G k F t = true).
  Proof.
    intros G m k Hm. rewrite (lmin_le_iff G m Hm k). apply min_le_np_certificate.
  Qed.
End Decide.

(* ===================================================================== *)
(* Hardness: the 3-SAT networks of LossyHardness.v. *)

(* The minimum of net f is 0 iff f is satisfiable. *)
Theorem lmin_zero_iff_sat : forall f, is_lmin (net f) 0 <-> satisfiable f.
Proof. intro f. rewrite lmin_zero_iff_section. apply net_section_iff_sat. Qed.

Theorem min_le_zero_iff_sat :
  forall f, (exists F, cset (net f) F /\ length F <= 0 /\ lfeasible (net f) F) <-> satisfiable f.
Proof.
  intro f. rewrite <- net_section_iff_sat. split.
  - intros [F [_ [Hl [s Hs]]]]. destruct F; [| simpl in Hl; lia].
    exists s. rewrite resid_nil in Hs. exact Hs.
  - intros [s Hs]. exists []. split; [apply cset_nil | split; [simpl; lia |]].
    exists s. rewrite resid_nil. exact Hs.
Qed.

(* Deleting the pinning self-loop (position 0) always leaves a section. *)
Theorem net_unpinned : forall f, resid (net f) [0] = cedges 0 f.
Proof.
  intro f. unfold resid, net. simpl. apply resid_from_none. intros j [<- | []]. left. lia.
Qed.

Theorem net_one_suffices : forall f, cset (net f) [0] /\ lfeasible (net f) [0].
Proof.
  intro f. split.
  - split; [repeat constructor; intros [] |]. intros i [<- | []]. simpl. lia.
  - exists (fun v => if Nat.eqb v zv then 1 else poison). rewrite net_unpinned. apply no_pin_trivial.
Qed.

Theorem net_lmin_dichotomy :
  forall f, (satisfiable f -> is_lmin (net f) 0) /\ (~ satisfiable f -> is_lmin (net f) 1).
Proof.
  intro f. split; [apply lmin_zero_iff_sat |].
  intro Hu. split.
  - exists [0]. destruct (net_one_suffices f) as [H1 H2]. split; [exact H1 | split; [reflexivity | exact H2]].
  - intros F HF [s Hs]. destruct F as [| i F]; [| simpl; lia].
    exfalso. apply Hu. apply net_section_iff_sat. exists s. rewrite resid_nil in Hs. exact Hs.
Qed.

(* The reduction, packaged: linear size, minimum 0 iff satisfiable, minimum 1 iff unsatisfiable. *)
Theorem lmin_reduction :
  forall f,
    length (net f) = 6 * length f + 1 /\
    (is_lmin (net f) 0 <-> satisfiable f) /\
    (is_lmin (net f) 1 <-> ~ satisfiable f).
Proof.
  intro f. split; [exact (proj1 (net_size f)) |]. split; [apply lmin_zero_iff_sat |]. split.
  - intros H1 Hs. pose proof (lmin_unique _ _ _ H1 (proj1 (net_lmin_dichotomy f) Hs)). discriminate.
  - exact (proj2 (net_lmin_dichotomy f)).
Qed.

(* ===================================================================== *)
(* The invertible case: group labels under the regular action. *)

Section Group.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  Definition lift_edge (x : @edge G) : @edge (G -> G) := let '(u, v, g) := x in (u, v, op g).

  (* A group-labeled network as a lossy one: g acts by left translation. *)
  Definition lift (Es : list (@edge G)) : list (@edge (G -> G)) := map lift_edge Es.

  Lemma msection_lift : forall s Es, msection s (lift Es) <-> is_section op s Es.
  Proof.
    intros s Es. unfold msection, is_section, lift. split.
    - intros H [[u v] g] Hx. exact (H _ (in_map lift_edge _ _ Hx)).
    - intros H x Hx. apply in_map_iff in Hx. destruct Hx as [[[u v] g] [<- Hy]]. exact (H _ Hy).
  Qed.

  Lemma resid_lift : forall Es F, resid (lift Es) F = lift (resid Es F).
  Proof. intros Es F. apply resid_from_map. Qed.

  (* A group feedback edge set: deleting it leaves a coboundary labeling (H^1 = 0). *)
  Definition gfes (Es : list (@edge G)) (F : list nat) : Prop :=
    cset Es F /\ coboundary op inv (resid Es F).

  Definition is_gfes_min (Es : list (@edge G)) (k : nat) : Prop :=
    (exists F, gfes Es F /\ length F = k) /\ (forall F, gfes Es F -> k <= length F).

  Theorem lfeasible_lift_iff :
    forall Es F, lfeasible (lift Es) F <-> coboundary op inv (resid Es F).
  Proof.
    intros Es F. rewrite <- (section_iff_coboundary op e inv assoc id_r inv_r inv_l).
    unfold lfeasible, has_section. rewrite resid_lift.
    split; intros [s Hs]; exists s; apply msection_lift; exact Hs.
  Qed.

  (* On group-labeled networks, the lossy minimum IS the group feedback edge set minimum. *)
  Theorem lossy_min_is_gfes : forall Es k, is_lmin (lift Es) k <-> is_gfes_min Es k.
  Proof.
    intros Es k.
    assert (E : forall F, (cset (lift Es) F /\ lfeasible (lift Es) F) <-> gfes Es F).
    { intro F. unfold gfes, lift. rewrite cset_map. fold (lift Es). rewrite lfeasible_lift_iff.
      reflexivity. }
    unfold is_lmin, is_gfes_min. split; intros [[F [H1 H2]] Hk]; split.
    - exists F. destruct H2 as [Hl Hf]. split; [apply E; split; assumption | exact Hl].
    - intros F' HF'. apply E in HF'. destruct HF' as [HF' Hf']. exact (Hk F' HF' Hf').
    - exists F. apply E in H1. destruct H1 as [HF Hf]. split; [exact HF | split; assumption].
    - intros F' HF' Hf'. apply Hk. apply E. split; assumption.
  Qed.

  (* Per fundamental cycle (cycle_basis_criterion): when the residual is a spanning tree T plus
     extra edges X, F is feasible iff every extra edge is balanced against the tree's section. *)
  Theorem lift_cycle_basis :
    forall Es F r T X sT,
      resid Es F = T ++ X -> tree r T -> is_section op sT T ->
      (forall u v g, In (u, v, g) X -> In u (r :: verts T) /\ In v (r :: verts T)) ->
      (lfeasible (lift Es) F <-> forall x, In x X -> sat op sT x).
  Proof.
    intros Es F r T X sT HR HT HsT Hsp.
    rewrite <- (cycle_basis_criterion op e inv assoc id_l id_r inv_r inv_l r T X sT HT HsT Hsp).
    unfold lfeasible, has_section. rewrite resid_lift, HR.
    split; intros [s Hs]; exists s; apply msection_lift; exact Hs.
  Qed.

  (* A group-labeled tree (no cycle) has minimum 0. *)
  Theorem group_tree_lmin_zero : forall r Es, tree r Es -> is_lmin (lift Es) 0.
  Proof.
    intros r Es HT. apply lmin_zero_iff_section.
    destruct (tree_has_section op e inv assoc id_l inv_r r Es HT) as [s Hs].
    exists s. apply msection_lift. exact Hs.
  Qed.

  (* With a spanning tree T followed by extra edges X, the minimum is at most |X| (the cycle rank
     when T spans). *)
  Theorem group_lmin_le_nontree :
    forall r T X k, tree r T -> is_lmin (lift (T ++ X)) k -> k <= length X.
  Proof.
    intros r T X k HT [_ Hk].
    set (F := seq (length T) (length X)).
    assert (HR : resid (T ++ X) F = T).
    { unfold resid. rewrite resid_from_app, (resid_from_all X (0 + length T) F), app_nil_r.
      - apply resid_from_none. intros j Hj. apply in_seq in Hj. lia.
      - intros j Hj. apply in_seq. lia. }
    assert (HF : cset (lift (T ++ X)) F).
    { apply cset_map. split; [apply seq_NoDup |]. intros i Hi. apply in_seq in Hi.
      rewrite app_length. lia. }
    assert (Hf : lfeasible (lift (T ++ X)) F).
    { destruct (tree_has_section op e inv assoc id_l inv_r r T HT) as [s Hs].
      exists s. rewrite resid_lift, HR. apply msection_lift. exact Hs. }
    pose proof (Hk F HF Hf) as H. unfold F in H. rewrite seq_length in H. exact H.
  Qed.
End Group.

(* ===================================================================== *)
(* The lossy minimum is not cycle-based: the C22 shape. *)

Theorem c22_lmin_b : lmin_b bool_dec false [true; false] c22_es = 1.
Proof. vm_compute. reflexivity. Qed.

(* Two constant maps false and true into vertex 2: minimum 1, on a tree. *)
Theorem c22_lmin : tree 2 c22_es /\ is_lmin c22_es 1.
Proof.
  split; [exact (proj1 c22_cycle_basis_fails) |].
  apply (lmin_decide bool_dec false [true; false] bool_full). exact c22_lmin_b.
Qed.

(* A lower bound on the lossy minimum that sees only cycles takes the same value on a tree as on
   the empty network; every such bound is 0 on C22, whose minimum is 1. *)
Theorem lossy_min_exceeds_cycle_bounds :
  forall L : list (@edge (bool -> bool)) -> nat,
    (forall G k, is_lmin G k -> L G <= k) ->
    (forall r G, tree r G -> L G = L []) ->
    L c22_es = 0 /\ is_lmin c22_es 1 /\ L c22_es < 1.
Proof.
  intros L Hlb Htree.
  assert (H0 : L [] <= 0).
  { apply Hlb. apply lmin_zero_iff_section. exists (fun _ => false). intros x []. }
  assert (Hc : L c22_es = 0) by (rewrite (Htree 2 c22_es (proj1 c22_cycle_basis_fails)); lia).
  split; [exact Hc | split; [exact (proj2 c22_lmin) | lia]].
Qed.

(* The hypotheses are satisfiable (the zero bound), so the theorem is not vacuous. *)
Theorem cycle_bounds_nonvacuous :
  (forall G k, is_lmin G k -> (fun _ : list (@edge (bool -> bool)) => 0) G <= k) /\
  (forall r (G : list (@edge (bool -> bool))), tree r G ->
     (fun _ : list (@edge (bool -> bool)) => 0) G = (fun _ : list (@edge (bool -> bool)) => 0) []).
Proof. split; intros; [lia | reflexivity]. Qed.

(* The invertible contrast: under the regular action, a tree has minimum 0. The C22 tree shape
   relabeled by Z/2 (both edges the identity) has minimum 0. *)
Definition c22_group : list (@edge bool) := ([] ++ [(0, 2, false)]) ++ [(1, 2, false)].

Theorem c22_group_lmin : tree 2 c22_group /\ is_lmin (lift xorb c22_group) 0.
Proof.
  assert (HT : tree 2 c22_group).
  { unfold c22_group. apply t_in; [apply t_in; [apply t_nil | left; reflexivity | simpl; intuition congruence] | |].
    - simpl. left. reflexivity.
    - simpl. intuition congruence. }
  split; [exact HT |].
  exact (group_tree_lmin_zero xorb false (fun x => x) xor_assoc xor_id_l xor_inv_r
           2 c22_group HT).
Qed.

(* ===================================================================== *)
(* Further instances. *)

(* The diamond of RootSet.v: no section, one deletion suffices. *)
Theorem diamond_lmin : is_lmin dia_G 1.
Proof. apply (lmin_decide tri_eq_dec t0 tri_all tri_full). vm_compute. reflexivity. Qed.

(* Two roots collapsing into one vertex: sections exist, minimum 0. *)
Theorem two_lmin : is_lmin two_G 0.
Proof. apply (lmin_decide tri_eq_dec t0 tri_all tri_full). vm_compute. reflexivity. Qed.

(* A root set containing a strongly connected component: minimum 0. *)
Theorem scc_lmin : is_lmin scc_G 0.
Proof. apply (lmin_decide bool_dec false [true; false] bool_full). vm_compute. reflexivity. Qed.

(* A Z/2 triangle closed by a flip: lossy minimum 1 = group feedback edge set minimum. *)
Definition ztri : list (@edge bool) := [(0, 1, false); (1, 2, false); (2, 0, true)].

Theorem tri_lmin : is_lmin (lift xorb ztri) 1 /\ is_gfes_min xorb (fun x => x) ztri 1.
Proof.
  assert (H : is_lmin (lift xorb ztri) 1).
  { apply (lmin_decide bool_dec false [true; false] bool_full). vm_compute. reflexivity. }
  split; [exact H |].
  exact (proj1 (lossy_min_is_gfes xorb false (fun x => x) xor_assoc xor_id_r xor_inv_r xor_inv_l
                  ztri 1) H).
Qed.

(* The bowtie of CohomologyGeneral.v: lossy minimum 2 = group feedback edge set minimum,
   matching bowtie_min_two. *)
Theorem bow_lmin : is_lmin (lift xorb (bow_T ++ bow_X)) 2 /\
                   is_gfes_min xorb (fun x => x) (bow_T ++ bow_X) 2.
Proof.
  assert (H : is_lmin (lift xorb (bow_T ++ bow_X)) 2).
  { apply (lmin_decide bool_dec false [true; false] bool_full). vm_compute. reflexivity. }
  split; [exact H |].
  exact (proj1 (lossy_min_is_gfes xorb false (fun x => x) xor_assoc xor_id_r xor_inv_r xor_inv_l
                  _ 2) H).
Qed.

(* 3-SAT instances: the satisfiable clause has minimum 0, the unsatisfiable formula minimum 1. *)
Theorem fsat_lmin : is_lmin (net fsat) 0.
Proof. apply lmin_zero_iff_sat. exact fsat_satisfiable. Qed.

Theorem funsat_lmin : is_lmin (net funsat) 1.
Proof. apply (proj2 (net_lmin_dichotomy funsat)). exact funsat_unsatisfiable. Qed.

(* The NP checker accepts a certificate for C22 with k = 1: delete position 1. *)
Theorem c22_certificate :
  min_cert_ok bool_dec false c22_es 1 [1] [false; false; false] = true /\
  min_cert_ok bool_dec false c22_es 0 [] [false; false; false] = false.
Proof. split; vm_compute; reflexivity. Qed.
