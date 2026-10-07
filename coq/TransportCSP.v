(* TransportCSP.v: static consistency of transport networks as a finite-domain constraint
   satisfaction problem, and the regime cells this correspondence predicts. Axiom-free.

   The development has three layers: an execution algebra (events, traces, merges), a constraint
   algebra (which states are consistent), and dynamics (whether runs settle). Existence of a
   section of a transport network is a question of the second layer. This file makes the
   correspondence between that question and the constraint satisfaction problem CSP(Gamma)
   precise, so that the polymorphism classification of CSP (cited, never mechanized) reads
   directly as a classification of section existence per fixed transport family.

   Part 1, the bridge.
     rgraph f, rpin c         the graph {(x, f x)} of a transport map, and the unary relation {c}
     gamma F cs               the template Gamma_F: the graphs of the maps in F and the pins in cs
     csp_of G P               the CSP instance of a network G (edges labeled by maps) with pinned
                              vertices P, a list of (vertex, value)
     section_iff_csp          G has a section agreeing with P iff csp_of G P is satisfiable, and
                              csp_of G P is an instance over gamma F cs when G is labeled by F and
                              P's values lie in cs (reading A, msection)
     hsection_iff_csp         the same for merge networks (reading B's resolver merges): a
                              k-ary merge map g is the (k+1)-ary relation hgraph k g;
                              msection_as_hsection recovers reading A as the case k = 1
     pol_iff_commute          an operation p : list D -> D of arity k preserves rgraph f iff
                              f (p xs) = p (map f xs) for every xs of length k
     pol_pin_iff              p preserves rpin c iff p (repeat c k) = c
     pol_gamma_iff            Pol(Gamma_F) is exactly the set of operations commuting with every
                              f in F and fixing every pinned value (the centralizer of F)
     pol_solutions            polymorphisms map k solutions of any instance over Gamma to a
                              solution; section_closure is the network form
     group_maltsev            for a group acting on itself by left translation, the Mal'tsev
                              operation x y^-1 z commutes with every translation and satisfies
                              m(x, x, y) = y = m(y, x, x); group_section_as_msection reads the
                              group-labeled networks of CohomologyGraph.v as translation networks
     hard_family              the 26 maps used by LossyHardness.v's reduction: filt, pin, and the
                              24 projections sprj n1 n2 n3 p (8 sign patterns, 3 positions);
                              prj_signs: prj c p depends on c only through its signs;
                              net_in_hard_family: every edge of net f is labeled by hard_family;
                              hard_family_csp: section existence for this one fixed family is
                              equivalent to 3-SAT on every formula, by net_section_iff_sat

   Part 2, predicted cells.
     mono_min_commute, mono_max_commute, mono_median_commute
                              a monotone map on a chain commutes with min, max and median
     chain_pol                min and max (semilattice operations) and median (a majority
                              operation) are polymorphisms of gamma F cs for every family F of
                              monotone maps on the chain nat and every pin list cs
     ac_exact                 monotone transports on the finite chain {0..N} with pinned
                              vertices: arc consistency (a simultaneous revise iterated to a
                              fixed point, at most |vs| (N + 1) passes, ac_run_some) decides
                              existence of a section with values in {0..N}: ac_decide = true iff
                              one exists; the witness is the minimum of each arc-consistent
                              domain (ac_min_section)
     diamond_join_fails       the diamond 0 < a, b < 1 with f (0) = f (a) = f (b) = 0, f (1) = 1:
                              f is monotone and does not commute with join (it does commute with
                              meet: diamond_meet_ok); diamond_g_fails gives a monotone map that
                              commutes with neither, so the chain hypothesis matters
     median_family            a non-chain family with a majority polymorphism: on bool * bool, the
                              coordinate swap, the lossy projection (x, y) |-> (x, x) and the
                              negation of the first coordinate commute with the coordinatewise
                              median (a majority operation); median_family_not_lattice: the
                              lattice meet and join are not polymorphisms of it

   Cited, not mechanized: the CSP dichotomy (Bulatov 2017; Zhuk 2017, 2020), Mal'tsev
   tractability (Bulatov and Dalmau 2006), the polymorphism (Galois) connection and closure
   properties (Jeavons, Cohen and Gyssens 1997; Jeavons 1998), bounded width of majority templates
   (Jeavons, Cohen and Cooper 1998; Feder and Vardi 1998). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.RootSet NC.LossyHardness.
Import ListNotations.

(* ===================================================================== *)
(* Small list facts. *)

Lemma tc_map_nth_seq :
  forall (A : Type) (d : A) (l : list A), map (fun i => nth i l d) (seq 0 (length l)) = l.
Proof.
  intros A d l. induction l as [| x l IH]; [reflexivity |].
  simpl. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma tc_map_const_seq :
  forall (A : Type) (c : A) (a k : nat), map (fun _ => c) (seq a k) = repeat c k.
Proof. intros A c a k. revert a. induction k as [| k IH]; intro a; simpl; [| rewrite IH]; reflexivity. Qed.

(* ===================================================================== *)
(* Part 1: the bridge. *)

Section CSP.
  Context {D : Type}.

  (* A relation has an arity n and a predicate on tuples (lists); a constraint applies one to a
     scope of vertices. *)
  Definition rel : Type := (nat * (list D -> Prop))%type.
  Definition constraint : Type := (list nat * rel)%type.

  Definition csat (s : nat -> D) (c : constraint) : Prop := snd (snd c) (map s (fst c)).

  Definition solution (s : nat -> D) (I : list constraint) : Prop := forall c, In c I -> csat s c.

  Definition csp_sat (I : list constraint) : Prop := exists s, solution s I.

  (* I is an instance of CSP(Gamma): every constraint uses a relation of Gamma, with a scope of
     the relation's arity. *)
  Definition over (Gamma : list rel) (I : list constraint) : Prop :=
    forall c, In c I -> In (snd c) Gamma /\ length (fst c) = fst (snd c).

  (* The graph of a transport map and the unary pin relation. *)
  Definition rgraph (f : D -> D) : rel :=
    (2, fun t => match t with [x; y] => f x = y | _ => False end).

  Definition rpin (c : D) : rel := (1, fun t => t = [c]).

  Definition gamma (F : list (D -> D)) (cs : list D) : list rel := map rgraph F ++ map rpin cs.

  Definition econ (x : @edge (D -> D)) : constraint :=
    let '(u, v, f) := x in ([u; v], rgraph f).

  Definition pcon (x : nat * D) : constraint := ([fst x], rpin (snd x)).

  Definition csp_of (G : list (@edge (D -> D))) (P : list (nat * D)) : list constraint :=
    map econ G ++ map pcon P.

  Definition pinned (s : nat -> D) (P : list (nat * D)) : Prop := forall r c, In (r, c) P -> s r = c.

  Definition labeled (F : list (D -> D)) (G : list (@edge (D -> D))) : Prop :=
    forall u v f, In (u, v, f) G -> In f F.

  Lemma csat_econ : forall s x, csat s (econ x) <-> msat s x.
  Proof. intros s [[u v] f]. reflexivity. Qed.

  Lemma csat_pcon : forall s r c, csat s (pcon (r, c)) <-> s r = c.
  Proof.
    intros s r c. unfold csat, pcon. simpl. split; [intro H; injection H; tauto | intros ->; reflexivity].
  Qed.

  (* The bridge, reading A: sections agreeing with the pins are the solutions of csp_of G P. *)
  Theorem section_solution :
    forall G P s, (msection s G /\ pinned s P) <-> solution s (csp_of G P).
  Proof.
    intros G P s. unfold solution, csp_of. split.
    - intros [Hs Hp] c Hc. apply in_app_or in Hc. destruct Hc as [Hc | Hc]; apply in_map_iff in Hc;
        destruct Hc as [[[u v] f] [<- Hx]] || destruct Hc as [[r a] [<- Hx]].
      + apply csat_econ. exact (Hs _ Hx).
      + apply csat_pcon. exact (Hp r a Hx).
    - intro H. split.
      + intros x Hx. apply csat_econ. apply H. apply in_or_app. left. apply in_map. exact Hx.
      + intros r a Hx. apply csat_pcon. apply H. apply in_or_app. right. apply in_map. exact Hx.
  Qed.

  Theorem section_iff_csp :
    forall F cs G P, labeled F G -> (forall r c, In (r, c) P -> In c cs) ->
      ((exists s, msection s G /\ pinned s P) <-> csp_sat (csp_of G P)) /\
      over (gamma F cs) (csp_of G P).
  Proof.
    intros F cs G P HF Hcs. split.
    - split; intros [s Hs]; exists s; apply section_solution; exact Hs.
    - intros c Hc. unfold csp_of in Hc. apply in_app_or in Hc. unfold gamma.
      destruct Hc as [Hc | Hc]; apply in_map_iff in Hc.
      + destruct Hc as [[[u v] f] [<- Hx]]. simpl. split; [| reflexivity].
        apply in_or_app. left. apply in_map. exact (HF u v f Hx).
      + destruct Hc as [[r a] [<- Hx]]. simpl. split; [| reflexivity].
        apply in_or_app. right. apply in_map. exact (Hcs r a Hx).
  Qed.

  (* Without pins: plain section existence. *)
  Corollary section_iff_csp_nopin :
    forall G, (exists s, msection s G) <-> csp_sat (csp_of G []).
  Proof.
    intro G. split.
    - intros [s Hs]. exists s. apply section_solution. split; [exact Hs | intros r c []].
    - intros [s Hs]. exists s. exact (proj1 (proj2 (section_solution G [] s) Hs)).
  Qed.
End CSP.

(* ----- Reading B: merges as (k+1)-ary relations ----- *)

Section Merges.
  Context {D : Type}.

  (* A merge edge (us, v, g): the vertex v holds the merge g of the values at us. *)
  Definition hedge : Type := (list nat * nat * (list D -> D))%type.

  Definition hsat (s : nat -> D) (x : hedge) : Prop :=
    let '(us, v, g) := x in g (map s us) = s v.

  Definition hsection (s : nat -> D) (H : list hedge) : Prop := forall x, In x H -> hsat s x.

  (* The graph of a k-ary merge map: a relation of arity k + 1. *)
  Definition hgraph (k : nat) (g : list D -> D) : @rel D :=
    (S k, fun t => exists xs y, t = xs ++ [y] /\ length xs = k /\ g xs = y).

  Definition hcon (x : hedge) : @constraint D :=
    let '(us, v, g) := x in (us ++ [v], hgraph (length us) g).

  Lemma csat_hcon : forall s x, csat s (hcon x) <-> hsat s x.
  Proof.
    intros s [[us v] g]. unfold csat, hcon, hsat. simpl. rewrite map_app. simpl. split.
    - intros [xs [y [E [Hl Hg]]]]. apply app_inj_tail in E. destruct E as [E1 E2].
      rewrite E1, E2. exact Hg.
    - intro Hg. exists (map s us), (s v). split; [reflexivity |]. split; [apply map_length | exact Hg].
  Qed.

  Theorem hsection_iff_csp :
    forall H s, hsection s H <-> solution s (map hcon H).
  Proof.
    intros H s. split.
    - intros Hs c Hc. apply in_map_iff in Hc. destruct Hc as [x [<- Hx]]. apply csat_hcon. exact (Hs x Hx).
    - intros Hs x Hx. apply csat_hcon. apply Hs. apply in_map. exact Hx.
  Qed.

  Theorem hsection_over :
    forall H, over (map (fun x => let '(us, _, g) := x in hgraph (length us) g) H) (map hcon H).
  Proof.
    intros H c Hc. apply in_map_iff in Hc. destruct Hc as [[[us v] g] [<- Hx]]. simpl. split.
    - apply (in_map (fun x : hedge => let '(us0, _, g0) := x in hgraph (length us0) g0) H _ Hx).
    - rewrite app_length. simpl. lia.
  Qed.

  (* Reading A is the case k = 1 (d0 only fills the unused non-singleton case). *)
  Definition lift (d0 : D) (x : @edge (D -> D)) : hedge :=
    let '(u, v, f) := x in ([u], v, fun l => f (hd d0 l)).

  Theorem msection_as_hsection :
    forall d0 G s, msection s G <-> hsection s (map (lift d0) G).
  Proof.
    intros d0 G s. split.
    - intros Hs x Hx. apply in_map_iff in Hx. destruct Hx as [[[u v] f] [<- Hx]]. exact (Hs _ Hx).
    - intros Hs [[u v] f] Hx. exact (Hs _ (in_map (lift d0) G _ Hx)).
  Qed.
End Merges.

(* ----- Polymorphisms ----- *)

Section Pol.
  Context {D : Type}.

  (* p : list D -> D, read as a k-ary operation, preserves the n-ary relation R when, for every
     k x n matrix M (row i is M i 0, ..., M i (n - 1)) whose k rows are tuples of R, the tuple of
     p applied to each column is a tuple of R. *)
  Definition col (k : nat) (M : nat -> nat -> D) (j : nat) : list D := map (fun i => M i j) (seq 0 k).
  Definition row (n : nat) (M : nat -> nat -> D) (i : nat) : list D := map (fun j => M i j) (seq 0 n).

  Definition preserves (k : nat) (p : list D -> D) (R : @rel D) : Prop :=
    forall M : nat -> nat -> D, (forall i, i < k -> snd R (row (fst R) M i)) ->
      snd R (map (fun j => p (col k M j)) (seq 0 (fst R))).

  Definition pol (k : nat) (p : list D -> D) (Gamma : list (@rel D)) : Prop :=
    forall R, In R Gamma -> preserves k p R.

  Definition commutes (k : nat) (p : list D -> D) (f : D -> D) : Prop :=
    forall xs, length xs = k -> f (p xs) = p (map f xs).

  (* A k-ary operation preserves the graph of f iff it commutes with f. *)
  Theorem pol_iff_commute : forall k p f, preserves k p (rgraph f) <-> commutes k p f.
  Proof.
    intros k p f. split.
    - intros H xs Hl. set (d := p []).
      set (M := fun i j => if Nat.eqb j 0 then nth i xs d else f (nth i xs d)).
      assert (Hrow : forall i, i < k -> snd (rgraph f) (row (fst (rgraph f)) M i)).
      { intros i _. reflexivity. }
      pose proof (H M Hrow) as E. simpl in E. unfold col, M in E. simpl in E.
      rewrite <- Hl in E. rewrite tc_map_nth_seq in E.
      rewrite <- (tc_map_nth_seq D d xs) at 2. rewrite map_map. exact E.
    - intros H M Hrow. simpl.
      assert (E : col k M 1 = map f (col k M 0)).
      { unfold col. rewrite map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi.
        pose proof (Hrow i (proj2 Hi)) as Ei. simpl in Ei. symmetry. exact Ei. }
      rewrite E. apply H. unfold col. rewrite map_length, seq_length. reflexivity.
  Qed.

  (* ... and preserves the pin {c} iff it fixes c. *)
  Theorem pol_pin_iff : forall k p c, preserves k p (rpin c) <-> p (repeat c k) = c.
  Proof.
    intros k p c. split.
    - intro H. pose proof (H (fun _ _ => c) (fun i _ => eq_refl)) as E. simpl in E.
      injection E as E. unfold col in E. rewrite tc_map_const_seq in E. exact E.
    - intros H M Hrow. simpl. f_equal. transitivity (p (repeat c k)); [| exact H]. f_equal. unfold col.
      rewrite <- (tc_map_const_seq D c 0 k). apply map_ext_in. intros i Hi. apply in_seq in Hi.
      pose proof (Hrow i (proj2 Hi)) as Ei. simpl in Ei. injection Ei as Ei. exact Ei.
  Qed.

  (* Pol(Gamma_F) is the centralizer of F, restricted to operations fixing the pinned values. *)
  Theorem pol_gamma_iff :
    forall k p F cs, pol k p (gamma F cs) <->
      (forall f, In f F -> commutes k p f) /\ (forall c, In c cs -> p (repeat c k) = c).
  Proof.
    intros k p F cs. unfold pol, gamma. split.
    - intro H. split.
      + intros f Hf. apply pol_iff_commute. apply H. apply in_or_app. left. apply in_map. exact Hf.
      + intros c Hc. apply pol_pin_iff. apply H. apply in_or_app. right. apply in_map. exact Hc.
    - intros [HF Hc] R HR. apply in_app_or in HR. destruct HR as [HR | HR]; apply in_map_iff in HR;
        destruct HR as [x [<- Hx]].
      + apply pol_iff_commute. exact (HF x Hx).
      + apply pol_pin_iff. exact (Hc x Hx).
  Qed.

  (* Polymorphisms map k solutions to a solution (the closure property). *)
  Theorem pol_solutions :
    forall k p Gamma I, pol k p Gamma -> over Gamma I ->
      forall S : nat -> nat -> D, (forall i, i < k -> solution (S i) I) ->
      solution (fun w => p (map (fun i => S i w) (seq 0 k))) I.
  Proof.
    intros k p Gamma I Hp Hov S HS [sc R] Hc. destruct (Hov _ Hc) as [HR Hlen]. simpl in HR, Hlen.
    set (M := fun i j => S i (nth j sc 0)).
    assert (Hrow : forall i, i < k -> snd R (row (fst R) M i)).
    { intros i Hi. pose proof (HS i Hi _ Hc) as E. unfold csat in E. simpl in E.
      unfold row, M. rewrite <- Hlen. rewrite <- (map_map (fun j => nth j sc 0) (S i)).
      rewrite tc_map_nth_seq. exact E. }
    pose proof (Hp R HR M Hrow) as E. unfold csat. simpl.
    rewrite <- Hlen in E. rewrite <- (tc_map_nth_seq nat 0 sc) at 1. rewrite map_map. exact E.
  Qed.

  (* The network form: an operation commuting with every edge map sends k sections to a section. *)
  Theorem section_closure :
    forall k p (G : list (@edge (D -> D))) (S : nat -> nat -> D),
      (forall u v f, In (u, v, f) G -> commutes k p f) ->
      (forall i, i < k -> msection (S i) G) ->
      msection (fun w => p (map (fun i => S i w) (seq 0 k))) G.
  Proof.
    intros k p G S Hc HS [[u v] f] Hx. unfold msat.
    rewrite (Hc u v f Hx) by (rewrite map_length, seq_length; reflexivity).
    f_equal. rewrite map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi.
    exact (HS i (proj2 Hi) _ Hx).
  Qed.
End Pol.

(* ----- Groups: the Mal'tsev operation ----- *)

Section GroupMaltsev.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis id_r  : forall a, op a e = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  Definition maltsev (l : list G) : G :=
    match l with [x; y; z] => op x (op (inv y) z) | _ => e end.

  Lemma inv_op : forall a b, inv (op a b) = op (inv b) (inv a).
  Proof.
    intros a b.
    transitivity (op (inv (op a b)) (op (op a b) (op (inv b) (inv a)))).
    - rewrite <- (assoc a b), (assoc b (inv b)), inv_r, id_l, inv_r, id_r. reflexivity.
    - rewrite assoc, inv_l, id_l. reflexivity.
  Qed.

  (* x y^-1 z commutes with every left translation and is a Mal'tsev operation. *)
  Theorem group_maltsev :
    (forall g, commutes 3 maltsev (op g)) /\
    (forall x y, maltsev [x; x; y] = y /\ maltsev [y; x; x] = y).
  Proof.
    split.
    - intros g [| x [| y [| z [| w l]]]] Hl; simpl in Hl; try discriminate. simpl.
      rewrite inv_op. rewrite <- (assoc (inv y) (inv g) (op g z)), (assoc (inv g) g z), inv_l, id_l.
      rewrite <- (assoc g x). reflexivity.
    - intros x y. simpl. split.
      + rewrite assoc, inv_r, id_l. reflexivity.
      + rewrite inv_l, id_r. reflexivity.
  Qed.

  (* So the Mal'tsev operation is a polymorphism of every template of translations and pins. *)
  Corollary group_pol :
    forall (gs : list G) (cs : list G), pol 3 maltsev (gamma (map op gs) cs).
  Proof.
    intros gs cs. apply pol_gamma_iff. split.
    - intros f Hf. apply in_map_iff in Hf. destruct Hf as [g [<- _]]. exact (proj1 group_maltsev g).
    - intros c _. simpl. rewrite inv_l, id_r. reflexivity.
  Qed.

  (* The group-labeled networks of CohomologyGraph.v are translation networks. *)
  Definition tr (x : @edge G) : @edge (G -> G) := let '(u, v, g) := x in (u, v, op g).

  Theorem group_section_as_msection :
    forall s es, is_section op s es <-> msection s (map tr es).
  Proof.
    intros s es. split.
    - intros Hs x Hx. apply in_map_iff in Hx. destruct Hx as [[[u v] g] [<- Hx]]. exact (Hs _ Hx).
    - intros Hs [[u v] g] Hx. exact (Hs _ (in_map tr es _ Hx)).
  Qed.
End GroupMaltsev.

(* ----- The reduction of LossyHardness.v uses one fixed finite family ----- *)

(* The projection for a clause with sign pattern (n1, n2, n3), at position p. *)
Definition sprj (n1 n2 n3 : bool) (p : nat) : nat -> nat := prj ((0, n1), (0, n2), (0, n3)) p.

(* prj c p depends on c only through its sign pattern. *)
Theorem prj_signs :
  forall x1 n1 x2 n2 x3 n3 p, prj ((x1, n1), (x2, n2), (x3, n3)) p = sprj n1 n2 n3 p.
Proof. reflexivity. Qed.

Corollary prj_signs_eq :
  forall (c c' : clause) p,
    snd (fst (fst c)) = snd (fst (fst c')) -> snd (snd (fst c)) = snd (snd (fst c')) ->
    snd (snd c) = snd (snd c') -> prj c p = prj c' p.
Proof.
  intros [[[x1 n1] [x2 n2]] [x3 n3]] [[[y1 m1] [y2 m2]] [y3 m3]] p E1 E2 E3. simpl in *.
  subst. rewrite !prj_signs. reflexivity.
Qed.

Definition bools : list bool := [true; false].

(* The 26 maps: filt, pin and the 24 projections. *)
Definition hard_family : list (nat -> nat) :=
  filt :: pin :: flat_map (fun n1 => flat_map (fun n2 => flat_map (fun n3 =>
    map (sprj n1 n2 n3) [0; 1; 2]) bools) bools) bools.

Lemma hard_family_length : length hard_family = 26.
Proof. reflexivity. Qed.

Lemma sprj_in : forall n1 n2 n3 p, p < 3 -> In (sprj n1 n2 n3 p) hard_family.
Proof.
  intros n1 n2 n3 p Hp. right. right.
  apply in_flat_map. exists n1. split; [destruct n1; simpl; auto |].
  apply in_flat_map. exists n2. split; [destruct n2; simpl; auto |].
  apply in_flat_map. exists n3. split; [destruct n3; simpl; auto |].
  apply in_map. destruct p as [| [| [| p]]]; simpl; auto. lia.
Qed.

Lemma prj_in : forall c p, p < 3 -> In (prj c p) hard_family.
Proof. intros [[[x1 n1] [x2 n2]] [x3 n3]] p Hp. rewrite prj_signs. apply sprj_in. exact Hp. Qed.

(* Every edge of the reduction's network is labeled by the fixed family. *)
Theorem net_in_hard_family : forall f, labeled hard_family (net f).
Proof.
  intros f u v g Hx. destruct Hx as [E | Hx].
  - injection E as _ _ <-. right. left. reflexivity.
  - destruct (cedges_in f 0 _ Hx) as [k [c [_ Hk]]]. simpl in Hk.
    destruct Hk as [E | [E | [E | [E | [E | [E | []]]]]]]; injection E as _ _ <-;
      first [apply prj_in; lia | left; reflexivity].
Qed.

(* Section existence for the one fixed family hard_family (no pins beyond the pin map) is 3-SAT
   on every formula: CSP(gamma hard_family []) restricted to the networks net f, by the existing
   reduction (net_section_iff_sat, linear size by net_size). *)
Theorem hard_family_csp :
  forall f,
    labeled hard_family (net f) /\
    over (gamma hard_family []) (csp_of (net f) []) /\
    ((exists s, msection s (net f)) <-> satisfiable f) /\
    (csp_sat (csp_of (net f) []) <-> satisfiable f) /\
    length (net f) = 6 * length f + 1.
Proof.
  intro f. split; [exact (net_in_hard_family f) |].
  split; [exact (proj2 (section_iff_csp hard_family [] (net f) [] (net_in_hard_family f)
                          (fun r c H => match H with end))) |].
  split; [exact (net_section_iff_sat f) |].
  split; [rewrite <- section_iff_csp_nopin; exact (net_section_iff_sat f) |].
  exact (proj1 (net_size f)).
Qed.

(* ===================================================================== *)
(* Part 2: predicted cells. *)

(* ----- Chains: monotone maps commute with min, max and median ----- *)

Definition mono (f : nat -> nat) : Prop := forall x y, x <= y -> f x <= f y.

Definition min2 (l : list nat) : nat := match l with [x; y] => Nat.min x y | _ => 0 end.
Definition max2 (l : list nat) : nat := match l with [x; y] => Nat.max x y | _ => 0 end.
Definition med (x y z : nat) : nat := Nat.max (Nat.min x y) (Nat.min (Nat.max x y) z).
Definition med3 (l : list nat) : nat := match l with [x; y; z] => med x y z | _ => 0 end.

Theorem mono_min_commute : forall f, mono f -> forall x y, f (Nat.min x y) = Nat.min (f x) (f y).
Proof.
  intros f Hf x y. destruct (Nat.le_ge_cases x y) as [H | H].
  - rewrite (Nat.min_l x y H), (Nat.min_l _ _ (Hf _ _ H)). reflexivity.
  - rewrite (Nat.min_r x y H), (Nat.min_r _ _ (Hf _ _ H)). reflexivity.
Qed.

Theorem mono_max_commute : forall f, mono f -> forall x y, f (Nat.max x y) = Nat.max (f x) (f y).
Proof.
  intros f Hf x y. destruct (Nat.le_ge_cases x y) as [H | H].
  - rewrite (Nat.max_r x y H), (Nat.max_r _ _ (Hf _ _ H)). reflexivity.
  - rewrite (Nat.max_l x y H), (Nat.max_l _ _ (Hf _ _ H)). reflexivity.
Qed.

Theorem mono_median_commute : forall f, mono f -> forall x y z, f (med x y z) = med (f x) (f y) (f z).
Proof.
  intros f Hf x y z. unfold med.
  rewrite (mono_max_commute f Hf), !(mono_min_commute f Hf), (mono_max_commute f Hf). reflexivity.
Qed.

(* The median is a majority operation. *)
Theorem med_majority : forall x y, med x x y = x /\ med x y x = x /\ med y x x = x.
Proof. intros x y. unfold med. repeat split; lia. Qed.

(* For every family of monotone maps on the chain and every pin list, min and max (semilattice
   operations) and the median (a majority operation) are polymorphisms of Gamma_F. *)
Theorem chain_pol :
  forall F cs, (forall f, In f F -> mono f) ->
    pol 2 min2 (gamma F cs) /\ pol 2 max2 (gamma F cs) /\ pol 3 med3 (gamma F cs).
Proof.
  intros F cs HF. split; [| split]; apply pol_gamma_iff; split;
    try (intros c _; simpl; unfold med; lia);
    intros f Hf xs Hl; pose proof (HF f Hf) as Hm.
  - destruct xs as [| x [| y [| w l]]]; simpl in Hl; try discriminate. apply mono_min_commute. exact Hm.
  - destruct xs as [| x [| y [| w l]]]; simpl in Hl; try discriminate. apply mono_max_commute. exact Hm.
  - destruct xs as [| x [| y [| z [| w l]]]]; simpl in Hl; try discriminate. apply mono_median_commute. exact Hm.
Qed.

(* So min of two sections is a section, and so is max, for monotone networks. *)
Corollary chain_min_section :
  forall (G : list (@edge (nat -> nat))) s t, (forall u v f, In (u, v, f) G -> mono f) ->
    msection s G -> msection t G ->
    msection (fun w => Nat.min (s w) (t w)) G /\ msection (fun w => Nat.max (s w) (t w)) G.
Proof.
  intros G s t HG Hs Ht. split; intros [[u v] f] Hx; unfold msat;
    [rewrite (mono_min_commute f (HG u v f Hx)) | rewrite (mono_max_commute f (HG u v f Hx))];
    rewrite (Hs _ Hx), (Ht _ Hx); reflexivity.
Qed.

(* The reduction's family is not monotone, and min is not one of its polymorphisms. *)
Theorem hard_family_min_fails :
  sprj false false false 2 0 = 8 /\ sprj false false false 2 1 = 1 /\
  ~ mono (sprj false false false 2) /\ ~ pol 2 min2 (gamma hard_family []).
Proof.
  split; [reflexivity |]. split; [reflexivity |]. split.
  - intro H. pose proof (H 0 1 ltac:(lia)) as E. vm_compute in E. lia.
  - intro H. apply pol_gamma_iff in H. destruct H as [H _].
    pose proof (H _ (sprj_in false false false 2 ltac:(lia)) [0; 1] eq_refl) as E.
    vm_compute in E. discriminate E.
Qed.

(* ----- Off the chain: the diamond ----- *)

Inductive dia : Type := dz | da | db | du.

Definition dle (x y : dia) : bool :=
  match x, y with
  | dz, _ | _, du => true
  | da, da | db, db => true
  | _, _ => false
  end.

Definition djoin (x y : dia) : dia :=
  match x, y with
  | dz, z | z, dz => z
  | da, da => da
  | db, db => db
  | _, _ => du
  end.

Definition dmeet (x y : dia) : dia :=
  match x, y with
  | du, z | z, du => z
  | da, da => da
  | db, db => db
  | _, _ => dz
  end.

Definition dmono (f : dia -> dia) : Prop := forall x y, dle x y = true -> dle (f x) (f y) = true.

Definition djoin2 (l : list dia) : dia := match l with [x; y] => djoin x y | _ => dz end.
Definition dmeet2 (l : list dia) : dia := match l with [x; y] => dmeet x y | _ => dz end.

(* The lossy map f (0) = f (a) = f (b) = 0, f (1) = 1. *)
Definition dfl (x : dia) : dia := match x with du => du | _ => dz end.

Theorem diamond_join_fails :
  dmono dfl /\ dfl (djoin da db) <> djoin (dfl da) (dfl db) /\ ~ pol 2 djoin2 (gamma [dfl] []).
Proof.
  split; [intros [] [] H; try discriminate; reflexivity |]. split; [discriminate |].
  intro H. apply pol_gamma_iff in H. destruct H as [H _].
  pose proof (H dfl (or_introl eq_refl) [da; db] eq_refl) as E. discriminate E.
Qed.

(* It does commute with meet, so this family keeps a semilattice polymorphism. *)
Theorem diamond_meet_ok : forall x y, dfl (dmeet x y) = dmeet (dfl x) (dfl y).
Proof. intros [] []; reflexivity. Qed.

(* A monotone map on the diamond commuting with neither join nor meet: a, b |-> a. *)
Definition dg (x : dia) : dia := match x with dz => dz | du => du | _ => da end.

Theorem diamond_g_fails :
  dmono dg /\ dg (djoin da db) <> djoin (dg da) (dg db) /\ dg (dmeet da db) <> dmeet (dg da) (dg db) /\
  ~ pol 2 djoin2 (gamma [dg] []) /\ ~ pol 2 dmeet2 (gamma [dg] []).
Proof.
  split; [intros [] [] H; try discriminate; reflexivity |].
  split; [discriminate |]. split; [discriminate |]. split; intro H; apply pol_gamma_iff in H;
    destruct H as [H _]; pose proof (H dg (or_introl eq_refl) [da; db] eq_refl) as E; discriminate E.
Qed.

(* ----- A non-chain family with a majority polymorphism ----- *)

Definition bmed (x y z : bool) : bool := (x && y) || (y && z) || (x && z).

Definition pmed (l : list (bool * bool)) : bool * bool :=
  match l with
  | [(x1, x2); (y1, y2); (z1, z2)] => (bmed x1 y1 z1, bmed x2 y2 z2)
  | _ => (false, false)
  end.

Definition pmeet2 (l : list (bool * bool)) : bool * bool :=
  match l with [(x1, x2); (y1, y2)] => (x1 && y1, x2 && y2) | _ => (false, false) end.
Definition pjoin2 (l : list (bool * bool)) : bool * bool :=
  match l with [(x1, x2); (y1, y2)] => (x1 || y1, x2 || y2) | _ => (false, false) end.

Definition pswap (x : bool * bool) : bool * bool := (snd x, fst x).
Definition pfst (x : bool * bool) : bool * bool := (fst x, fst x).
Definition pneg (x : bool * bool) : bool * bool := (negb (fst x), snd x).

Definition median_fam : list (bool * bool -> bool * bool) := [pswap; pfst; pneg].
Definition all_pairs : list (bool * bool) := [(false, false); (false, true); (true, false); (true, true)].

(* The coordinatewise median is a majority polymorphism of the family with every pin. *)
Theorem median_family :
  (forall x y, pmed [x; x; y] = x /\ pmed [x; y; x] = x /\ pmed [y; x; x] = x) /\
  pol 3 pmed (gamma median_fam all_pairs) /\ pfst (true, false) = pfst (true, true).
Proof.
  split; [intros [[] []] [[] []]; repeat split; reflexivity |]. split; [| reflexivity].
  apply pol_gamma_iff. split.
  - intros f Hf xs Hl. destruct xs as [| x [| y [| z [| w l]]]]; simpl in Hl; try discriminate.
    destruct x as [[] []], y as [[] []], z as [[] []];
      destruct Hf as [<- | [<- | [<- | []]]]; reflexivity.
  - intros [[] []] _; reflexivity.
Qed.

Theorem median_family_not_lattice :
  ~ pol 2 pmeet2 (gamma median_fam []) /\ ~ pol 2 pjoin2 (gamma median_fam []).
Proof.
  split; intro H; apply pol_gamma_iff in H; destruct H as [H _];
    pose proof (H pneg (or_intror (or_intror (or_introl eq_refl))) [(false, false); (true, false)] eq_refl)
      as E; discriminate E.
Qed.

(* ----- Monotone transports on a finite chain: arc consistency decides existence ----- *)

Lemma tc_filter_le : forall (A : Type) (p : A -> bool) l, length (filter p l) <= length l.
Proof. intros A p l. induction l as [| x l IH]; simpl; [lia |]. destruct (p x); simpl; lia. Qed.

Lemma tc_filter_eq :
  forall (A : Type) (p : A -> bool) l, length (filter p l) = length l -> forall a, In a l -> p a = true.
Proof.
  intros A p l. induction l as [| x l IH]; intros Hl a Ha; [destruct Ha |]. simpl in Hl.
  pose proof (tc_filter_le A p l) as Hle.
  destruct (p x) eqn:Ex; simpl in Hl; [| lia].
  destruct Ha as [<- | Ha]; [exact Ex | apply IH; [lia | exact Ha]].
Qed.

Definition msum (g : nat -> nat) (l : list nat) : nat := fold_right (fun w acc => g w + acc) 0 l.

Lemma msum_ext : forall g h l, (forall w, g w = h w) -> msum g l = msum h l.
Proof. intros g h l H. induction l as [| w l IH]; simpl; [reflexivity | rewrite H, IH; reflexivity]. Qed.

Lemma msum_lt :
  forall g h l, (forall w, In w l -> g w <= h w) -> (exists w, In w l /\ g w < h w) -> msum g l < msum h l.
Proof.
  intros g h l. induction l as [| x l IH]; intros Hle [w [Hw Hlt]]; [destruct Hw |]. simpl.
  assert (Hle' : forall w, In w l -> g w <= h w) by (intros y Hy; apply Hle; right; exact Hy).
  assert (Hs : msum g l <= msum h l).
  { clear IH Hw Hlt. induction l as [| y l IHl]; simpl; [lia |].
    pose proof (Hle' y (or_introl eq_refl)). pose proof (Hle x (or_introl eq_refl)).
    assert (msum g l <= msum h l); [| lia]. apply IHl.
    - intros z [<- | Hz]; [apply Hle; left; reflexivity | apply Hle; right; right; exact Hz].
    - intros z Hz. apply Hle'. right. exact Hz. }
  destruct Hw as [<- | Hw]; [lia |]. pose proof (IH Hle' (ex_intro _ w (conj Hw Hlt))).
  pose proof (Hle x (or_introl eq_refl)). lia.
Qed.

Lemma msum_bound : forall g l b, (forall w, g w <= b) -> msum g l <= length l * b.
Proof. intros g l b H. induction l as [| w l IH]; simpl; [lia |]. pose proof (H w). lia. Qed.

Fixpoint lmin (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: l' => Nat.min x (lmin l')
  end.

Lemma lmin_in : forall l, l <> [] -> In (lmin l) l.
Proof.
  induction l as [| x l IH]; intro H; [contradiction |]. destruct l as [| y l]; [left; reflexivity |].
  change (In (Nat.min x (lmin (y :: l))) (x :: y :: l)).
  destruct (Nat.le_ge_cases x (lmin (y :: l))) as [E | E].
  - rewrite Nat.min_l by exact E. left. reflexivity.
  - rewrite Nat.min_r by exact E. right. apply IH. discriminate.
Qed.

Lemma lmin_le : forall l x, In x l -> lmin l <= x.
Proof.
  induction l as [| y l IH]; intros x Hx; [destruct Hx |]. destruct l as [| z l].
  - destruct Hx as [<- | []]. simpl. lia.
  - change (Nat.min y (lmin (z :: l)) <= x). destruct Hx as [<- | Hx]; [lia |].
    pose proof (IH x Hx). lia.
Qed.

Definition memb (x : nat) (l : list nat) : bool := existsb (Nat.eqb x) l.

Lemma memb_spec : forall x l, memb x l = true <-> In x l.
Proof.
  intros x l. unfold memb. rewrite existsb_exists. split.
  - intros [y [Hy E]]. apply Nat.eqb_eq in E. subst. exact Hy.
  - intro H. exists x. split; [exact H | apply Nat.eqb_refl].
Qed.

(* Monotone on the chain {0..N}. *)
Definition mono_on (N : nat) (f : nat -> nat) : Prop := forall x y, x <= y -> y <= N -> f x <= f y.

Section ArcConsistency.
  Variable N : nat.
  Variable G : list (@edge (nat -> nat)).
  Variable P : list (nat * nat).

  (* A section over the finite chain {0..N} agreeing with the pins. *)
  Definition chain_section (s : nat -> nat) : Prop :=
    (forall w, s w <= N) /\ msection s G /\ pinned s P.

  Definition vs : list nat := verts G ++ map fst P.

  (* a keeps a successor in d v along every out-edge, and a predecessor in d u along every
     in-edge (arc consistency for functional constraints). *)
  Definition out_ok (d : nat -> list nat) (w a : nat) : bool :=
    forallb (fun x => let '(u, v, f) := x in if Nat.eqb u w then memb (f a) (d v) else true) G.

  Definition in_ok (d : nat -> list nat) (w a : nat) : bool :=
    forallb (fun x => let '(u, v, f) := x in
                      if Nat.eqb v w then existsb (fun b => Nat.eqb (f b) a) (d u) else true) G.

  Definition pin_ok (w a : nat) : bool :=
    forallb (fun x => if Nat.eqb (fst x) w then Nat.eqb a (snd x) else true) P.

  Definition init (w : nat) : list nat := filter (pin_ok w) (seq 0 (S N)).

  (* One simultaneous revise of every domain. *)
  Definition revise (d : nat -> list nat) (w : nat) : list nat :=
    filter (fun a => out_ok d w a && in_ok d w a) (d w).

  (* Tabulate the new domains on vs once per pass. *)
  Definition tab (l : list nat) (d : nat -> list nat) : nat -> list nat :=
    let t := map (fun x => (x, d x)) l in
    fun w => match find (fun q => Nat.eqb (fst q) w) t with Some q => snd q | None => d w end.

  Lemma tab_spec : forall l d w, tab l d w = d w.
  Proof.
    intros l d w. unfold tab. induction l as [| x l IH]; simpl; [reflexivity |].
    destruct (Nat.eqb x w) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | exact IH].
  Qed.

  Definition nxt (d : nat -> list nat) : nat -> list nat := tab vs (revise d).

  Definition measure (d : nat -> list nat) : nat := msum (fun w => length (d w)) vs.

  Definition stable (d : nat -> list nat) : bool :=
    forallb (fun w => Nat.eqb (length (revise d w)) (length (d w))) vs.

  Fixpoint run (fuel : nat) (d : nat -> list nat) : option (nat -> list nat) :=
    match fuel with
    | 0 => None
    | S k => if stable d then Some d else run k (nxt d)
    end.

  Definition ac_domains : option (nat -> list nat) := run (S (measure init)) init.

  Definition nonempty (l : list nat) : bool := match l with [] => false | _ => true end.

  Definition ac_decide : bool :=
    match ac_domains with Some d => forallb (fun w => nonempty (d w)) vs | None => false end.

  (* ----- the procedure terminates within measure init + 1 passes ----- *)

  Lemma nxt_spec : forall d w, nxt d w = revise d w.
  Proof. intros d w. apply tab_spec. Qed.

  Lemma measure_nxt : forall d, stable d = false -> measure (nxt d) < measure d.
  Proof.
    intros d Hs. unfold measure. rewrite (msum_ext _ (fun w => length (revise d w)) vs)
      by (intro w; rewrite nxt_spec; reflexivity).
    apply msum_lt.
    - intros w _. apply tc_filter_le.
    - unfold stable in Hs. apply not_true_iff_false in Hs. rewrite forallb_forall in Hs.
      destruct (existsb (fun w => negb (Nat.eqb (length (revise d w)) (length (d w)))) vs) eqn:E.
      + apply existsb_exists in E. destruct E as [w [Hw E]]. exists w. split; [exact Hw |].
        apply negb_true_iff, Nat.eqb_neq in E. pose proof (tc_filter_le _ (fun a => out_ok d w a && in_ok d w a) (d w)).
        unfold revise in *. lia.
      + exfalso. apply Hs. intros w Hw. destruct (Nat.eqb (length (revise d w)) (length (d w))) eqn:F;
          [reflexivity |]. assert (H : existsb (fun w => negb (Nat.eqb (length (revise d w)) (length (d w)))) vs = true)
          by (apply existsb_exists; exists w; rewrite F; split; [exact Hw | reflexivity]).
        congruence.
  Qed.

  Theorem ac_run_some : forall fuel d, measure d < fuel -> exists d', run fuel d = Some d'.
  Proof.
    induction fuel as [| k IH]; intros d Hd; [lia |]. simpl.
    destruct (stable d) eqn:Hs; [exists d; reflexivity |].
    apply IH. pose proof (measure_nxt d Hs). lia.
  Qed.

  (* The pass bound: at most |vs| (N + 1) + 1 passes. *)
  Theorem ac_pass_bound : measure init <= length vs * S N.
  Proof.
    apply msum_bound. intro w. unfold init. pose proof (tc_filter_le _ (pin_ok w) (seq 0 (S N))).
    rewrite seq_length in H. exact H.
  Qed.

  (* ----- soundness of pruning ----- *)

  Lemma sol_ok :
    forall s d, chain_section s -> (forall w, In (s w) (d w)) ->
      forall w, out_ok d w (s w) = true /\ in_ok d w (s w) = true.
  Proof.
    intros s d [_ [Hs _]] Hd w. split; apply forallb_forall; intros [[u v] f] Hx;
      pose proof (Hs _ Hx) as E; unfold msat in E.
    - destruct (Nat.eqb u w) eqn:Eu; [| reflexivity]. apply Nat.eqb_eq in Eu. subst u.
      apply memb_spec. rewrite E. apply Hd.
    - destruct (Nat.eqb v w) eqn:Ev; [| reflexivity]. apply Nat.eqb_eq in Ev. subst v.
      apply existsb_exists. exists (s u). split; [apply Hd | apply Nat.eqb_eq; exact E].
  Qed.

  Lemma run_spec :
    forall fuel d d', run fuel d = Some d' ->
      stable d' = true /\ (forall w a, In a (d' w) -> In a (d w)) /\
      (forall s, chain_section s -> (forall w, In (s w) (d w)) -> forall w, In (s w) (d' w)).
  Proof.
    induction fuel as [| k IH]; intros d d' H; [discriminate |]. simpl in H.
    destruct (stable d) eqn:Hs.
    - injection H as <-. split; [exact Hs | split; [tauto | tauto]].
    - destruct (IH (nxt d) d' H) as [H1 [H2 H3]]. split; [exact H1 |]. split.
      + intros w a Ha. apply H2 in Ha. rewrite nxt_spec in Ha. unfold revise in Ha.
        apply filter_In in Ha. exact (proj1 Ha).
      + intros s Hsol Hd. apply (H3 s Hsol). intro w. rewrite nxt_spec. unfold revise.
        apply filter_In. split; [apply Hd |]. destruct (sol_ok s d Hsol Hd w) as [-> ->]. reflexivity.
  Qed.

  Lemma stable_spec :
    forall d, stable d = true -> forall w, In w vs -> forall a, In a (d w) ->
      out_ok d w a = true /\ in_ok d w a = true.
  Proof.
    intros d Hs w Hw a Ha. unfold stable in Hs. rewrite forallb_forall in Hs.
    pose proof (Hs w Hw) as E. apply Nat.eqb_eq in E.
    pose proof (tc_filter_eq _ _ _ E a Ha) as F. apply andb_true_iff in F. exact F.
  Qed.

  (* ----- the minimum of arc-consistent domains is a section ----- *)

  Theorem ac_min_section :
    (forall u v f, In (u, v, f) G -> mono_on N f) ->
    forall d, stable d = true -> (forall w a, In a (d w) -> In a (init w)) ->
      (forall w, In w vs -> d w <> []) -> chain_section (fun w => lmin (d w)).
  Proof.
    intros Hmono d Hst Hsub Hne.
    assert (Hrng : forall w a, In a (d w) -> a <= N).
    { intros w a Ha. apply Hsub in Ha. unfold init in Ha. apply filter_In in Ha. destruct Ha as [Ha _].
      apply in_seq in Ha. lia. }
    assert (Hvu : forall u v f, In (u, v, f) G -> In u vs /\ In v vs).
    { intros u v f Hx. destruct (in_verts_edge G u v f Hx) as [Hu Hv].
      split; apply in_or_app; left; assumption. }
    split; [| split].
    - intro w. destruct (d w) as [| a l] eqn:E; [simpl; lia |].
      apply (Hrng w). rewrite E. apply lmin_in. discriminate.
    - intros [[u v] f] Hx. unfold msat. destruct (Hvu u v f Hx) as [Hu Hv].
      pose proof (lmin_in (d u) (Hne u Hu)) as Ha0. pose proof (lmin_in (d v) (Hne v Hv)) as Hb0.
      set (a0 := lmin (d u)) in *. set (b0 := lmin (d v)) in *.
      assert (H1 : b0 <= f a0).
      { destruct (stable_spec d Hst u Hu a0 Ha0) as [Ho _]. unfold out_ok in Ho.
        rewrite forallb_forall in Ho. pose proof (Ho _ Hx) as E. simpl in E.
        rewrite Nat.eqb_refl in E. apply memb_spec in E. apply lmin_le. exact E. }
      assert (H2 : f a0 <= b0).
      { destruct (stable_spec d Hst v Hv b0 Hb0) as [_ Hi]. unfold in_ok in Hi.
        rewrite forallb_forall in Hi. pose proof (Hi _ Hx) as E. simpl in E.
        rewrite Nat.eqb_refl in E. apply existsb_exists in E. destruct E as [b [Hb E]].
        apply Nat.eqb_eq in E. rewrite <- E. apply (Hmono u v f Hx).
        - apply lmin_le. exact Hb.
        - exact (Hrng u b Hb). }
      lia.
    - intros r c Hrc.
      assert (Hr : In r vs) by (apply in_or_app; right; apply (in_map fst P (r, c)); exact Hrc).
      pose proof (lmin_in (d r) (Hne r Hr)) as Hm. apply Hsub in Hm. unfold init in Hm.
      apply filter_In in Hm. destruct Hm as [_ Hp]. unfold pin_ok in Hp.
      rewrite forallb_forall in Hp. pose proof (Hp _ Hrc) as E. simpl in E.
      rewrite Nat.eqb_refl in E. apply Nat.eqb_eq. exact E.
  Qed.

  (* ----- exactness ----- *)

  Theorem ac_exact :
    (forall u v f, In (u, v, f) G -> mono_on N f) ->
    (ac_decide = true <-> exists s, chain_section s).
  Proof.
    intro Hmono. destruct (ac_run_some (S (measure init)) init (le_n _)) as [d Hd].
    destruct (run_spec _ _ _ Hd) as [Hst [Hsub Hpres]].
    unfold ac_decide, ac_domains. rewrite Hd. split.
    - intro H. exists (fun w => lmin (d w)). apply (ac_min_section Hmono d Hst Hsub).
      intros w Hw E. rewrite forallb_forall in H. pose proof (H w Hw) as F. rewrite E in F. discriminate.
    - intros [s Hs]. apply forallb_forall. intros w Hw.
      assert (Hin : forall w, In (s w) (init w)).
      { intro x. unfold init. apply filter_In. split.
        - apply in_seq. pose proof (proj1 Hs x). lia.
        - unfold pin_ok. apply forallb_forall. intros [r c] Hrc. simpl.
          destruct (Nat.eqb r x) eqn:E; [| reflexivity]. apply Nat.eqb_eq in E. subst r.
          apply Nat.eqb_eq. exact (proj2 (proj2 Hs) x c Hrc). }
      pose proof (Hpres s Hs Hin w) as E. destruct (d w); [destruct E | reflexivity].
  Qed.
End ArcConsistency.

(* Per family: every network labeled by a family of monotone maps on {0..N} is decided by arc
   consistency. *)
Corollary ac_family :
  forall N (F : list (nat -> nat)) G P, (forall f, In f F -> mono_on N f) -> labeled F G ->
    (ac_decide N G P = true <-> exists s, chain_section N G P s).
Proof.
  intros N F G P HF HG. apply ac_exact. intros u v f Hx. exact (HF f (HG u v f Hx)).
Qed.

(* ----- Instances ----- *)

Definition capS (x : nat) : nat := Nat.min (S x) 3.
Definition dec1 (x : nat) : nat := x - 1.
Definition ident (x : nat) : nat := x.
Definition const3 (_ : nat) : nat := 3.

Definition mono_fam : list (nat -> nat) := [capS; dec1; ident; const3].

Lemma mono_fam_mono : forall f, In f mono_fam -> mono_on 3 f /\ mono f.
Proof.
  intros f Hf. destruct Hf as [<- | [<- | [<- | [<- | []]]]]; split; intros x y Hxy;
    unfold capS, dec1, ident, const3; lia.
Qed.

(* (1) A path, a lossy decrement and a parallel copy, with vertex 0 pinned to 1: a section. *)
Definition ex1_G : list (@edge (nat -> nat)) := [(0, 1, capS); (1, 2, dec1); (0, 2, ident)].
Definition ex1_P : list (nat * nat) := [(0, 1)].

Theorem ac_ex1 :
  labeled mono_fam ex1_G /\ ac_decide 3 ex1_G ex1_P = true /\ exists s, chain_section 3 ex1_G ex1_P s.
Proof.
  assert (HL : labeled mono_fam ex1_G).
  { intros u v f Hx. destruct Hx as [E | [E | [E | []]]]; injection E as _ _ <-; simpl; tauto. }
  assert (H : ac_decide 3 ex1_G ex1_P = true) by (vm_compute; reflexivity).
  split; [exact HL |]. split; [exact H |].
  apply (ac_family 3 mono_fam ex1_G ex1_P (fun f Hf => proj1 (mono_fam_mono f Hf)) HL). exact H.
Qed.

(* (2) Two paths merging at vertex 2 that disagree: no section. *)
Definition ex2_G : list (@edge (nat -> nat)) := [(0, 2, dec1); (1, 2, const3)].

Theorem ac_ex2 :
  labeled mono_fam ex2_G /\ ac_decide 3 ex2_G ex1_P = false /\ ~ exists s, chain_section 3 ex2_G ex1_P s.
Proof.
  assert (HL : labeled mono_fam ex2_G).
  { intros u v f Hx. destruct Hx as [E | [E | []]]; injection E as _ _ <-; simpl; tauto. }
  assert (H : ac_decide 3 ex2_G ex1_P = false) by (vm_compute; reflexivity).
  split; [exact HL |]. split; [exact H |]. intro Hs.
  apply (ac_family 3 mono_fam ex2_G ex1_P (fun f Hf => proj1 (mono_fam_mono f Hf)) HL) in Hs.
  congruence.
Qed.

(* (3) A lossy 2-cycle with no pins: the only section is 3 everywhere, and the arc-consistent
   domains are exactly {3}. *)
Definition ex3_G : list (@edge (nat -> nat)) := [(0, 1, capS); (1, 0, capS)].

Theorem ac_ex3 :
  ac_decide 3 ex3_G [] = true /\
  (forall d, ac_domains 3 ex3_G [] = Some d -> d 0 = [3] /\ d 1 = [3]) /\
  forall s, chain_section 3 ex3_G [] s -> s 0 = 3 /\ s 1 = 3.
Proof.
  split; [vm_compute; reflexivity |]. split.
  - intros d Hd. vm_compute in Hd. injection Hd as <-. split; vm_compute; reflexivity.
  - intros s [Hb [Hs _]]. pose proof (Hs _ (or_introl eq_refl)) as E1.
    pose proof (Hs _ (or_intror (or_introl eq_refl))) as E2. unfold msat, capS in E1, E2.
    pose proof (Hb 0). pose proof (Hb 1). lia.
Qed.

(* Monotonicity is needed: the negation x |-> 1 - x on {0, 1} around a triangle is arc
   consistent with full domains, yet has no section. *)
Definition flip (x : nat) : nat := 1 - x.
Definition tri3_G : list (@edge (nat -> nat)) := [(0, 1, flip); (1, 2, flip); (2, 0, flip)].

Theorem ac_needs_mono :
  ~ mono_on 1 flip /\ ac_decide 1 tri3_G [] = true /\ ~ exists s, chain_section 1 tri3_G [] s.
Proof.
  split; [intro H; pose proof (H 0 1 ltac:(lia) ltac:(lia)) as E; unfold flip in E; simpl in E; lia |].
  split; [vm_compute; reflexivity |].
  intros [s [Hb [Hs _]]].
  pose proof (Hs _ (or_introl eq_refl)) as E1.
  pose proof (Hs _ (or_intror (or_introl eq_refl))) as E2.
  pose proof (Hs _ (or_intror (or_intror (or_introl eq_refl)))) as E3.
  unfold msat, flip in E1, E2, E3. pose proof (Hb 0). pose proof (Hb 1). pose proof (Hb 2). lia.
Qed.

(* Sections of the bridge, non-vacuity: the C22 tree of CohomologyGeneral.v as a CSP instance with
   no solution, and the two-root network of RootSet.v as one with a solution. *)
Theorem bridge_instances :
  ~ csp_sat (csp_of c22_es []) /\ csp_sat (csp_of two_G []).
Proof.
  split.
  - rewrite <- section_iff_csp_nopin. exact c22_no_section_recovered.
  - rewrite <- section_iff_csp_nopin. exact two_has_section.
Qed.
