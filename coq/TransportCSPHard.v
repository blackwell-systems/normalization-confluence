(* TransportCSPHard.v: the predicted hard cell of TransportCSP.v. Monotone transports on the
   diamond (the Boolean lattice 2 x 2) give an NP-complete section problem, and the algebra
   predicts it: the template has only projections as polymorphisms. Axiom-free.

   The diamond dia = {dz < da, db < du} of TransportCSP.v is the lattice of two flags:
   dz = (0, 0), da = (1, 0), db = (0, 1), du = (1, 1) (bit1, bit2, mkd). The family dfam has six
   monotone maps, each reading one flag, the AND or the OR of the two flags, or a constant, and
   writing the result into both flags:
     dp1, dp2     x |-> (x1, x1), x |-> (x2, x2)
     dfl, dor     x |-> (x1 && x2, x1 && x2) (the lossy map of diamond_join_fails),
                  x |-> (x1 || x2, x1 || x2)
     dc0, dc1     the constants dz and du (a constant self-loop pins a vertex)

   Part 1, the reduction (3-SAT, as in LossyHardness.v, to section existence for dfam).
     dnet f               per variable x: a hidden vertex T_x with dfl T_x = 0 and dor T_x = 1, so
                          T_x is da or db, and its two flags give P_x (x) and N_x (not x); per
                          clause l0 or l1 or l2: a hidden W with dp1 W = l0, dp2 W = l1, a vertex
                          Q = dor W, and a hidden R with dp1 R = Q, dp2 R = l2, dor R = 1
     dnet_iff_sat         (exists s, msection s (dnet f)) <-> satisfiable f          [exact]
     dnet_size            |dnet f| = 18 |f| + 2
     dnet_mono            every map of dnet f is monotone (dmono), and dnet f is labeled by dfam
     dnet_np_certificate  membership in NP: a section exists iff a tuple of one value per vertex
                          passes the edge-by-edge checker (np_certificate of LossyHardness.v)
     diamond_hard_csp     the CSP form: csp_of (dnet f) [] is an instance of CSP(gamma dfam [])
                          satisfiable iff f is satisfiable, of linear size

   Part 2, the algebra (the prediction, mechanized for this family).
     pol_dfam_iff         for every arity k, an operation is a polymorphism of gamma dfam [] iff
                          it is a projection; pol_dfam_pins_iff: the same with every pin
     dfam_no_siggers      so no 4-ary Siggers polymorphism s (a, r, e, a) = s (r, a, r, e), no
                          majority, no Mal'tsev, no binary commutative polymorphism
     dfam_lattice_fails   join, meet and the lattice median are not polymorphisms (witnesses)
     dfam_minimal         each of the six maps is needed: without dfl, join is a polymorphism;
                          without dor, meet is; without dc0 (dc1) the constant du (dz) state is a
                          section of every network
     pol_superfamily_proj the same for every family containing dfam (all monotone maps of the
                          diamond, say) and any pins
     semilattice_pol      the tractable side: for any idempotent binary operation j, every
                          family of j-homomorphisms (with any pins) has j as a polymorphism;
                          joinhom_pol and meethom_pol read it on the diamond

   Instances: dnet_fsat, dnet_fsat_check (a satisfiable clause: a section, checked by computation),
   dnet_funsat (the unsatisfiable 8-clause formula: no section), dnet_needs_pins (without the two
   pins the all-dz state is a section of every network).

   Cited, not mechanized: the CSP dichotomy (Bulatov 2017; Zhuk 2017, 2020), under which a template
   with no Taylor polymorphism is NP-complete (Bulatov, Jeavons and Krokhin 2005); the Siggers term
   (Siggers 2010; the 4-ary form, Kearnes, Markovic and McKenzie 2014); semilattice templates are
   tractable (Jeavons, Cohen and Gyssens 1997). The hardness of dfam is proved here directly by
   the reduction, so the dichotomy is only needed to read the polymorphism side as a prediction. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.RootSet NC.LossyHardness NC.TransportCSP.
Import ListNotations.

(* ===================================================================== *)
(* The diamond as two flags. *)

Definition bit1 (v : dia) : bool := match v with da | du => true | _ => false end.
Definition bit2 (v : dia) : bool := match v with db | du => true | _ => false end.

Definition mkd (x y : bool) : dia :=
  match x, y with
  | false, false => dz
  | true, false => da
  | false, true => db
  | true, true => du
  end.

(* A flag broadcast into both flags. *)
Definition bv (b : bool) : dia := if b then du else dz.

Lemma mkd_bits : forall v, mkd (bit1 v) (bit2 v) = v.
Proof. intros []; reflexivity. Qed.

Lemma bit1_mkd : forall x y, bit1 (mkd x y) = x.
Proof. intros [] []; reflexivity. Qed.

Lemma bit2_mkd : forall x y, bit2 (mkd x y) = y.
Proof. intros [] []; reflexivity. Qed.

Lemma bit1_bv : forall b, bit1 (bv b) = b.
Proof. intros []; reflexivity. Qed.

Lemma bit2_bv : forall b, bit2 (bv b) = b.
Proof. intros []; reflexivity. Qed.

Lemma bv_inj : forall b c, bv b = bv c -> b = c.
Proof. intros [] [] H; try discriminate; reflexivity. Qed.

Definition dia_eq_dec : forall x y : dia, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition dall : list dia := [dz; da; db; du].

Lemma dall_spec : forall x, In x dall.
Proof. intros []; simpl; tauto. Qed.

(* ===================================================================== *)
(* The family. *)

Definition dp1 (v : dia) : dia := bv (bit1 v).
Definition dp2 (v : dia) : dia := bv (bit2 v).
Definition dor (v : dia) : dia := bv (bit1 v || bit2 v).
Definition dc0 (_ : dia) : dia := dz.
Definition dc1 (_ : dia) : dia := du.

Lemma dfl_bits : forall v, dfl v = bv (bit1 v && bit2 v).
Proof. intros []; reflexivity. Qed.

Definition dfam : list (dia -> dia) := [dp1; dp2; dfl; dor; dc0; dc1].

Theorem dfam_mono : forall g, In g dfam -> dmono g.
Proof.
  intros g Hg. destruct Hg as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    intros [] [] H; try discriminate; reflexivity.
Qed.

(* Each map broadcasts: its values lie in the chain {dz, du}. *)
Lemma dfam_broadcast : forall g, In g dfam -> forall v, g v = bv (bit1 (g v)).
Proof.
  intros g Hg v. destruct Hg as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; destruct v; reflexivity.
Qed.

(* ===================================================================== *)
(* Part 1: the reduction. *)

(* Vertices: 0 is pinned to dz, 1 to du; variable i owns 6 i + 2 (T), 6 i + 3 (P), 6 i + 4 (N);
   clause j owns 6 j + 5 (W), 6 j + 6 (Q), 6 j + 7 (R). *)
Definition hz : nat := 0.
Definition ho : nat := 1.
Definition hT (i : nat) : nat := S (S (6 * i)).
Definition hP (i : nat) : nat := S (S (6 * i + 1)).
Definition hN (i : nat) : nat := S (S (6 * i + 2)).
Definition hW (j : nat) : nat := S (S (6 * j + 3)).
Definition hQ (j : nat) : nat := S (S (6 * j + 4)).
Definition hR (j : nat) : nat := S (S (6 * j + 5)).

(* The vertex of a literal: P x for x, N x for not x. *)
Definition hl (l : lit) : nat := if snd l then hN (fst l) else hP (fst l).

Definition var_edges (i : nat) : list (@edge (dia -> dia)) :=
  [(hT i, hP i, dp1); (hT i, hN i, dp2); (hT i, hz, dfl); (hT i, ho, dor)].

Definition lit0 (c : clause) : lit := fst (fst c).
Definition lit1 (c : clause) : lit := snd (fst c).
Definition lit2 (c : clause) : lit := snd c.

Definition dclause_edges (j : nat) (c : clause) : list (@edge (dia -> dia)) :=
  var_edges (fst (lit0 c)) ++ var_edges (fst (lit1 c)) ++ var_edges (fst (lit2 c)) ++
  [(hW j, hl (lit0 c), dp1); (hW j, hl (lit1 c), dp2); (hW j, hQ j, dor);
   (hR j, hQ j, dp1); (hR j, hl (lit2 c), dp2); (hR j, ho, dor)].

Fixpoint dcedges (j : nat) (f : cnf) : list (@edge (dia -> dia)) :=
  match f with
  | [] => []
  | c :: f' => dclause_edges j c ++ dcedges (S j) f'
  end.

Definition dnet (f : cnf) : list (@edge (dia -> dia)) := (hz, hz, dc0) :: (ho, ho, dc1) :: dcedges 0 f.

Lemma dcedges_in :
  forall g j x, In x (dcedges j g) -> exists k c, nth_error g k = Some c /\ In x (dclause_edges (j + k) c).
Proof.
  induction g as [| c g IH]; intros j x Hx; [simpl in Hx; contradiction |].
  change (In x (dclause_edges j c ++ dcedges (S j) g)) in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - exists 0, c. rewrite Nat.add_0_r. auto.
  - destruct (IH (S j) x Hx) as [k [c' [Hk Hx']]]. exists (S k), c'. split; [exact Hk |].
    replace (j + S k) with (S j + k) by lia. exact Hx'.
Qed.

Lemma dcedges_has :
  forall g j k c, nth_error g k = Some c -> incl (dclause_edges (j + k) c) (dcedges j g).
Proof.
  induction g as [| c0 g IH]; intros j k c Hk x Hx; destruct k as [| k]; simpl in Hk;
    try discriminate.
  - injection Hk as E. subst c. change (In x (dclause_edges j c0 ++ dcedges (S j) g)).
    apply in_or_app. left. rewrite Nat.add_0_r in Hx. exact Hx.
  - change (In x (dclause_edges j c0 ++ dcedges (S j) g)). apply in_or_app. right.
    apply (IH (S j) k c Hk). replace (S j + k) with (j + S k) by lia. exact Hx.
Qed.

(* ----- the state of an assignment ----- *)

Lemma div6 : forall i r, r < 6 -> (6 * i + r) / 6 = i /\ (6 * i + r) mod 6 = r.
Proof.
  intros i r Hr. split.
  - symmetry. apply (Nat.div_unique _ 6 i r); lia.
  - symmetry. apply (Nat.mod_unique _ 6 i r); lia.
Qed.

Definition dstate (f : cnf) (a : nat -> bool) (v : nat) : dia :=
  match v with
  | 0 => dz
  | 1 => du
  | S (S w) =>
      let i := w / 6 in
      let cl := match nth_error f i with
                | Some c => (lit_val a (lit0 c), lit_val a (lit1 c), lit_val a (lit2 c))
                | None => (false, false, false)
                end in
      let '(y0, y1, y2) := cl in
      match w mod 6 with
      | 0 => mkd (a i) (negb (a i))
      | 1 => bv (a i)
      | 2 => bv (negb (a i))
      | 3 => mkd y0 y1
      | 4 => bv (y0 || y1)
      | _ => mkd (y0 || y1) y2
      end
  end.

Lemma dstate_T : forall f a i, dstate f a (hT i) = mkd (a i) (negb (a i)).
Proof.
  intros f a i. unfold hT, dstate. rewrite <- (Nat.add_0_r (6 * i)).
  destruct (div6 i 0 ltac:(lia)) as [-> ->]. destruct (nth_error f i) as [[[? ?] ?] |]; reflexivity.
Qed.

Lemma dstate_P : forall f a i, dstate f a (hP i) = bv (a i).
Proof.
  intros f a i. unfold hP, dstate. destruct (div6 i 1 ltac:(lia)) as [-> ->].
  destruct (nth_error f i) as [[[? ?] ?] |]; reflexivity.
Qed.

Lemma dstate_N : forall f a i, dstate f a (hN i) = bv (negb (a i)).
Proof.
  intros f a i. unfold hN, dstate. destruct (div6 i 2 ltac:(lia)) as [-> ->].
  destruct (nth_error f i) as [[[? ?] ?] |]; reflexivity.
Qed.

Lemma dstate_l : forall f a l, dstate f a (hl l) = bv (lit_val a l).
Proof.
  intros f a [x n]. unfold hl, lit_val. simpl. destruct n.
  - rewrite dstate_N. destruct (a x); reflexivity.
  - rewrite dstate_P. destruct (a x); reflexivity.
Qed.

Lemma dstate_W :
  forall f a j c, nth_error f j = Some c -> dstate f a (hW j) = mkd (lit_val a (lit0 c)) (lit_val a (lit1 c)).
Proof.
  intros f a j c Hj. unfold hW, dstate. destruct (div6 j 3 ltac:(lia)) as [-> ->]. rewrite Hj. reflexivity.
Qed.

Lemma dstate_Q :
  forall f a j c, nth_error f j = Some c -> dstate f a (hQ j) = bv (lit_val a (lit0 c) || lit_val a (lit1 c)).
Proof.
  intros f a j c Hj. unfold hQ, dstate. destruct (div6 j 4 ltac:(lia)) as [-> ->]. rewrite Hj. reflexivity.
Qed.

Lemma dstate_R :
  forall f a j c, nth_error f j = Some c ->
    dstate f a (hR j) = mkd (lit_val a (lit0 c) || lit_val a (lit1 c)) (lit_val a (lit2 c)).
Proof.
  intros f a j c Hj. unfold hR, dstate. destruct (div6 j 5 ltac:(lia)) as [-> ->]. rewrite Hj. reflexivity.
Qed.

Lemma clause_val_lits :
  forall a c, clause_val a c = lit_val a (lit0 c) || lit_val a (lit1 c) || lit_val a (lit2 c).
Proof. intros a [[l0 l1] l2]. reflexivity. Qed.

(* ----- correctness ----- *)

Lemma var_edges_ok : forall f a i x, In x (var_edges i) -> msat (dstate f a) x.
Proof.
  intros f a i x Hx. destruct Hx as [<- | [<- | [<- | [<- | []]]]]; unfold msat;
    rewrite ?dstate_T, ?dstate_P, ?dstate_N; destruct (a i); reflexivity.
Qed.

Theorem dsection_of_sat : forall f a, satisfies a f -> msection (dstate f a) (dnet f).
Proof.
  intros f a Ha x Hx. destruct Hx as [<- | [<- | Hx]]; [reflexivity | reflexivity |].
  destruct (dcedges_in f 0 x Hx) as [k [c [Hk Hxk]]]. change (0 + k) with k in Hxk.
  unfold dclause_edges, var_edges in Hxk. cbn [app In] in Hxk.
  pose proof (Ha c (nth_error_In f k Hk)) as Hc. rewrite clause_val_lits in Hc.
  repeat (destruct Hxk as [<- | Hxk]; [| ]); [.. | destruct Hxk];
    unfold msat; rewrite ?dstate_T, ?dstate_P, ?dstate_N,
       ?(dstate_W f a k c Hk), ?(dstate_Q f a k c Hk), ?(dstate_R f a k c Hk), ?dstate_l;
    unfold dp1, dp2, dor; rewrite ?bit1_mkd, ?bit2_mkd;
    try (destruct (a _); reflexivity); try reflexivity.
  rewrite Hc. reflexivity.
Qed.

(* The two local facts behind the converse. *)
Lemma var_core : forall t, dfl t = dz -> dor t = du -> t = mkd (bit1 t) (negb (bit1 t)).
Proof. intros [] H1 H2; try discriminate; reflexivity. Qed.

Lemma clause_core :
  forall w r y0 y1 y2, dor r = du -> dp1 r = dor w -> dp2 r = bv y2 -> dp1 w = bv y0 -> dp2 w = bv y1 ->
    y0 || y1 || y2 = true.
Proof. intros [] [] [] [] [] H1 H2 H3 H4 H5; try discriminate; reflexivity. Qed.

Definition dassign (s : nat -> dia) (i : nat) : bool := bit1 (s (hT i)).

Lemma dsection_clause :
  forall f s k c, msection s (dnet f) -> nth_error f k = Some c ->
    (forall l, In l [lit0 c; lit1 c; lit2 c] -> s (hl l) = bv (lit_val (dassign s) l)) /\
    clause_val (dassign s) c = true.
Proof.
  intros f s k c Hs Hk.
  assert (Hin : forall x, In x (dclause_edges k c) -> msat s x).
  { intros x Hx. apply Hs. right. right. exact (dcedges_has f 0 k c Hk x Hx). }
  assert (Hz : s hz = dz) by (symmetry; exact (Hs _ (or_introl eq_refl))).
  assert (Ho : s ho = du) by (symmetry; exact (Hs _ (or_intror (or_introl eq_refl)))).
  assert (Hvar : forall i, incl (var_edges i) (dclause_edges k c) ->
                   s (hP i) = bv (dassign s i) /\ s (hN i) = bv (negb (dassign s i))).
  { intros i Hi.
    assert (E1 : dp1 (s (hT i)) = s (hP i)) by (apply (Hin (_, _, dp1)); apply Hi; simpl; tauto).
    assert (E2 : dp2 (s (hT i)) = s (hN i)) by (apply (Hin (_, _, dp2)); apply Hi; simpl; tauto).
    assert (E3 : dfl (s (hT i)) = s hz) by (apply (Hin (_, _, dfl)); apply Hi; simpl; tauto).
    assert (E4 : dor (s (hT i)) = s ho) by (apply (Hin (_, _, dor)); apply Hi; simpl; tauto).
    rewrite Hz in E3. rewrite Ho in E4. pose proof (var_core _ E3 E4) as Et.
    unfold dassign. rewrite <- E1, <- E2, Et. unfold dp1, dp2. rewrite bit1_mkd, bit2_mkd. auto. }
  assert (Hl : forall l, In l [lit0 c; lit1 c; lit2 c] -> s (hl l) = bv (lit_val (dassign s) l)).
  { intros l Hl'.
    assert (Hi : incl (var_edges (fst l)) (dclause_edges k c)).
    { intros x Hx. unfold dclause_edges. destruct Hl' as [<- | [<- | [<- | []]]];
        repeat (apply in_or_app; (left; exact Hx) || right). }
    destruct (Hvar _ Hi) as [HP HN]. destruct l as [x n]. unfold hl, lit_val. cbn [fst snd] in *.
    destruct n; [rewrite HN | rewrite HP]; destruct (dassign s x); reflexivity. }
  split; [exact Hl |].
  assert (F1 : dor (s (hR k)) = s ho) by (apply (Hin (_, _, dor)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  assert (F2 : dp1 (s (hR k)) = s (hQ k)) by (apply (Hin (_, _, dp1)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  assert (F3 : dp2 (s (hR k)) = s (hl (lit2 c))) by (apply (Hin (_, _, dp2)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  assert (F4 : dor (s (hW k)) = s (hQ k)) by (apply (Hin (_, _, dor)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  assert (F5 : dp1 (s (hW k)) = s (hl (lit0 c))) by (apply (Hin (_, _, dp1)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  assert (F6 : dp2 (s (hW k)) = s (hl (lit1 c))) by (apply (Hin (_, _, dp2)); unfold dclause_edges; rewrite !in_app_iff; simpl; tauto).
  rewrite clause_val_lits. apply (clause_core (s (hW k)) (s (hR k))).
  - rewrite F1. exact Ho.
  - rewrite F2, F4. reflexivity.
  - rewrite F3. apply Hl. simpl. tauto.
  - rewrite F5. apply Hl. simpl. tauto.
  - rewrite F6. apply Hl. simpl. tauto.
Qed.

Theorem dsat_of_section : forall f s, msection s (dnet f) -> satisfies (dassign s) f.
Proof.
  intros f s Hs c Hc. destruct (In_nth_error f c Hc) as [k Hk].
  exact (proj2 (dsection_clause f s k c Hs Hk)).
Qed.

(* The reduction is correct. *)
Theorem dnet_iff_sat : forall f, (exists s, msection s (dnet f)) <-> satisfiable f.
Proof.
  intro f. split.
  - intros [s Hs]. exists (dassign s). exact (dsat_of_section f s Hs).
  - intros [a Ha]. exists (dstate f a). exact (dsection_of_sat f a Ha).
Qed.

(* ----- size, labels, membership in NP ----- *)

Lemma dcedges_length : forall g j, length (dcedges j g) = 18 * length g.
Proof.
  induction g as [| c g IH]; intro j; [reflexivity |].
  change (length (dclause_edges j c ++ dcedges (S j) g) = 18 * S (length g)).
  rewrite app_length, IH. unfold dclause_edges. rewrite !app_length. simpl. lia.
Qed.

(* The network is linear in the formula: 18 edges per clause and the two pins. *)
Theorem dnet_size : forall f, length (dnet f) = 18 * length f + 2.
Proof. intro f. unfold dnet. simpl. rewrite dcedges_length. lia. Qed.

(* Every edge of dnet f is labeled by dfam, so by a monotone map of the diamond. *)
Theorem dnet_labeled : forall f, labeled dfam (dnet f).
Proof.
  intros f u v g Hx. destruct Hx as [E | [E | Hx]];
    [injection E as _ _ <-; simpl; tauto | injection E as _ _ <-; simpl; tauto |].
  destruct (dcedges_in f 0 _ Hx) as [k [c [_ Hk]]]. change (0 + k) with k in Hk.
  unfold dclause_edges, var_edges in Hk. cbn [app In] in Hk.
  repeat (destruct Hk as [E | Hk]; [injection E as _ _ <-; simpl; tauto |]). destruct Hk.
Qed.

Theorem dnet_mono : forall f u v g, In (u, v, g) (dnet f) -> dmono g.
Proof. intros f u v g Hx. apply dfam_mono. exact (dnet_labeled f u v g Hx). Qed.

(* Membership in NP: one value of the diamond per vertex, checked edge by edge. *)
Theorem dnet_np_certificate :
  forall f, (exists s, msection s (dnet f)) <->
    exists t, In t (tuples dall (length (nodup Nat.eq_dec (verts (dnet f))))) /\
              msection_b dia_eq_dec (assign dz (nodup Nat.eq_dec (verts (dnet f))) t) (dnet f) = true.
Proof. intro f. exact (np_certificate dia dia_eq_dec dz dall (dnet f) dall_spec). Qed.

(* The CSP form: the fixed template gamma dfam [] (no pins beyond dc0 and dc1) carries 3-SAT. *)
Theorem diamond_hard_csp :
  forall f,
    labeled dfam (dnet f) /\
    over (gamma dfam []) (csp_of (dnet f) []) /\
    ((exists s, msection s (dnet f)) <-> satisfiable f) /\
    (csp_sat (csp_of (dnet f) []) <-> satisfiable f) /\
    length (dnet f) = 18 * length f + 2.
Proof.
  intro f. split; [exact (dnet_labeled f) |].
  split; [exact (proj2 (section_iff_csp dfam [] (dnet f) [] (dnet_labeled f)
                          (fun r c H => match H with end))) |].
  split; [exact (dnet_iff_sat f) |].
  split; [rewrite <- section_iff_csp_nopin; exact (dnet_iff_sat f) |].
  exact (dnet_size f).
Qed.

(* Every monotone family on the diamond containing dfam is NP-hard by the same networks; in
   particular all monotone self-maps of the diamond. *)
Corollary mono_family_hard :
  forall F : list (dia -> dia), incl dfam F ->
    forall f, labeled F (dnet f) /\ ((exists s, msection s (dnet f)) <-> satisfiable f).
Proof.
  intros F HF f. split; [intros u v g Hx; exact (HF g (dnet_labeled f u v g Hx)) | exact (dnet_iff_sat f)].
Qed.

(* ===================================================================== *)
(* Part 2: the algebra. Every polymorphism of gamma dfam [] is a projection. *)

Lemma nth_map_seq :
  forall (A : Type) (F : nat -> A) k j d, j < k -> nth j (map F (seq 0 k)) d = F j.
Proof.
  intros A F k j d Hj. rewrite nth_indep with (d' := F 0) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(* A lattice homomorphism from the Boolean functions on {0..k-1} to bool that keeps 0 and 1 is
   a coordinate. *)
Theorem bool_hom_proj :
  forall (k : nat) (sg : (nat -> bool) -> bool),
    (forall g h, (forall j, j < k -> g j = h j) -> sg g = sg h) ->
    (forall g h, sg (fun j => g j && h j) = sg g && sg h) ->
    (forall g h, sg (fun j => g j || h j) = sg g || sg h) ->
    sg (fun _ => false) = false -> sg (fun _ => true) = true ->
    exists i, i < k /\ forall g, sg g = g i.
Proof.
  intros k sg Hext Hand Hor H0 H1.
  assert (Hat : forall g m, sg (fun j => g m && Nat.eqb j m) = g m && sg (fun j => Nat.eqb j m)).
  { intros g m. destruct (g m); [reflexivity | exact H0]. }
  assert (Hsum : forall g m,
            sg (fun j => Nat.ltb j m && g j) = existsb (fun j => g j && sg (fun x => Nat.eqb x j)) (seq 0 m)).
  { intros g m. induction m as [| m IH].
    - transitivity (sg (fun _ => false)); [| exact H0]. apply Hext. intros j _. destruct j; reflexivity.
    - rewrite seq_S, existsb_app. simpl. rewrite orb_false_r, <- IH, <- Hat, <- Hor.
      apply Hext. intros j _.
      destruct (Nat.ltb_spec j (S m)), (Nat.ltb_spec j m), (Nat.eqb_spec j m); subst; try lia;
        repeat match goal with |- context [g ?x] => destruct (g x) end; reflexivity. }
  assert (Hall : forall g, sg g = existsb (fun j => g j && sg (fun x => Nat.eqb x j)) (seq 0 k)).
  { intro g. rewrite <- Hsum. apply Hext. intros j Hj.
    destruct (Nat.ltb_spec j k); [reflexivity | lia]. }
  pose proof (Hall (fun _ => true)) as E. rewrite H1 in E. symmetry in E.
  apply existsb_exists in E. destruct E as [i [Hi Ei]]. apply in_seq in Hi. simpl in Ei.
  exists i. split; [lia |]. intro g. destruct (g i) eqn:Gi.
  - rewrite Hall. apply existsb_exists. exists i. split; [apply in_seq; lia | rewrite Gi, Ei; reflexivity].
  - assert (Z : sg (fun j => g j && Nat.eqb j i) = false).
    { transitivity (sg (fun _ => false)); [| exact H0]. apply Hext. intros j _.
      destruct (Nat.eqb_spec j i); [subst j; rewrite Gi; reflexivity | destruct (g j); reflexivity]. }
    rewrite Hand, Ei, andb_true_r in Z. exact Z.
Qed.

Section DfamPol.
  Variable k : nat.
  Variable p : list dia -> dia.
  Hypothesis Hp : pol k p (gamma dfam []).

  Let cm : forall g, In g dfam -> forall xs, length xs = k -> g (p xs) = p (map g xs).
  Proof. intros g Hg. exact (proj1 (proj1 (pol_gamma_iff k p dfam []) Hp) g Hg). Qed.

  (* A Boolean tuple, broadcast into the chain {dz, du}, and p read on such tuples. *)
  Definition btup (g : nat -> bool) : list dia := map (fun j => bv (g j)) (seq 0 k).
  Definition sig (g : nat -> bool) : bool := bit1 (p (btup g)).

  Lemma btup_length : forall g, length (btup g) = k.
  Proof. intro g. unfold btup. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma sig_ext : forall g h, (forall j, j < k -> g j = h j) -> sig g = sig h.
  Proof.
    intros g h H. unfold sig, btup. f_equal. f_equal. apply map_ext_in. intros j Hj.
    apply in_seq in Hj. rewrite H by lia. reflexivity.
  Qed.

  Lemma p_btup : forall g, p (btup g) = bv (sig g).
  Proof.
    intro g. transitivity (dp1 (p (btup g))); [| reflexivity].
    rewrite (cm dp1 ltac:(simpl; tauto) _ (btup_length g)). f_equal. unfold btup. rewrite map_map.
    apply map_ext. intro j. unfold dp1. rewrite bit1_bv. reflexivity.
  Qed.

  Lemma tup_bits :
    forall (rd : dia -> bool) (gm : dia -> dia), In gm dfam -> (forall v, gm v = bv (rd v)) ->
      forall xs, length xs = k -> rd (p xs) = sig (fun j => rd (nth j xs dz)).
  Proof.
    intros rd gm Hg Hgm xs Hl. apply bv_inj. rewrite <- Hgm, (cm gm Hg xs Hl), <- p_btup.
    f_equal. rewrite <- (tc_map_nth_seq dia dz xs) at 1. rewrite map_map, Hl. unfold btup.
    apply map_ext. intro j. apply Hgm.
  Qed.

  Lemma sig_bit1 : forall xs, length xs = k -> bit1 (p xs) = sig (fun j => bit1 (nth j xs dz)).
  Proof. apply (tup_bits bit1 dp1); [simpl; tauto | reflexivity]. Qed.

  Lemma sig_bit2 : forall xs, length xs = k -> bit2 (p xs) = sig (fun j => bit2 (nth j xs dz)).
  Proof. apply (tup_bits bit2 dp2); [simpl; tauto | reflexivity]. Qed.

  Definition pair_tup (g h : nat -> bool) : list dia := map (fun j => mkd (g j) (h j)) (seq 0 k).

  Lemma pair_tup_length : forall g h, length (pair_tup g h) = k.
  Proof. intros g h. unfold pair_tup. rewrite map_length, seq_length. reflexivity. Qed.

  Lemma pair_bits :
    forall g h, sig (fun j => bit1 (nth j (pair_tup g h) dz)) = sig g /\
                sig (fun j => bit2 (nth j (pair_tup g h) dz)) = sig h.
  Proof.
    intros g h. split; apply sig_ext; intros j Hj; unfold pair_tup; rewrite nth_map_seq by exact Hj;
      [apply bit1_mkd | apply bit2_mkd].
  Qed.

  Lemma sig_comb :
    forall (gm : dia -> dia) (op : bool -> bool -> bool), In gm dfam ->
      (forall v, gm v = bv (op (bit1 v) (bit2 v))) ->
      forall g h, sig (fun j => op (g j) (h j)) = op (sig g) (sig h).
  Proof.
    intros gm op Hg Hgm g h. apply bv_inj. rewrite <- p_btup.
    destruct (pair_bits g h) as [E1 E2].
    rewrite <- E1, <- E2, <- sig_bit1, <- sig_bit2 by apply pair_tup_length.
    rewrite <- Hgm, (cm gm Hg _ (pair_tup_length g h)). f_equal. unfold pair_tup, btup. rewrite map_map.
    apply map_ext. intro j. rewrite Hgm, bit1_mkd, bit2_mkd. reflexivity.
  Qed.

  Lemma sig_const :
    forall (gm : dia -> dia) (b : bool), In gm dfam -> (forall v, gm v = bv b) -> sig (fun _ => b) = b.
  Proof.
    intros gm b Hg Hgm. unfold sig. transitivity (bit1 (bv b)); [| apply bit1_bv]. f_equal.
    transitivity (p (map gm (btup (fun _ => b)))).
    - f_equal. unfold btup. rewrite map_map. apply map_ext. intro j. symmetry. apply Hgm.
    - rewrite <- (cm gm Hg _ (btup_length _)). apply Hgm.
  Qed.

  Theorem dfam_pol_proj : exists i, i < k /\ forall xs, length xs = k -> p xs = nth i xs dz.
  Proof.
    destruct (bool_hom_proj k sig sig_ext
                (sig_comb dfl andb ltac:(simpl; tauto) dfl_bits)
                (sig_comb dor orb ltac:(simpl; tauto) (fun v => eq_refl))
                (sig_const dc0 false ltac:(simpl; tauto) (fun v => eq_refl))
                (sig_const dc1 true ltac:(simpl; tauto) (fun v => eq_refl))) as [i [Hi Hs]].
    exists i. split; [exact Hi |]. intros xs Hl.
    rewrite <- (mkd_bits (p xs)), sig_bit1, sig_bit2, !Hs by exact Hl. apply mkd_bits.
  Qed.
End DfamPol.

(* Projections are polymorphisms of every template of graphs of maps and pins. *)
Lemma proj_pol :
  forall (D : Type) (d : D) k i (F : list (D -> D)) cs, i < k ->
    pol k (fun xs => nth i xs d) (gamma F cs).
Proof.
  intros D d k i F cs Hi. apply pol_gamma_iff. split.
  - intros g _ xs Hl. rewrite (nth_indep (map g xs) d (g d)) by (rewrite map_length; lia).
    rewrite map_nth. reflexivity.
  - intros c _. assert (H : In (nth i (repeat c k) d) (repeat c k)) by (apply nth_In; rewrite repeat_length; lia).
    apply repeat_spec in H. exact H.
Qed.

(* The exact algebraic statement: for every arity, Pol(gamma dfam []) is the clone of projections. *)
Theorem pol_dfam_iff :
  forall k p, pol k p (gamma dfam []) <-> exists i, i < k /\ forall xs, length xs = k -> p xs = nth i xs dz.
Proof.
  intros k p. split; [apply dfam_pol_proj |].
  intros [i [Hi Hp]] R HR. intros M HM.
  assert (E : forall j, j < fst R -> p (col k M j) = nth i (col k M j) dz).
  { intros j _. apply Hp. unfold col. rewrite map_length, seq_length. reflexivity. }
  rewrite (map_ext_in _ (fun j => nth i (col k M j) dz)) by (intros j Hj; apply in_seq in Hj; apply E; lia).
  exact (proj_pol dia dz k i dfam [] Hi R HR M HM).
Qed.

(* The same with every value pinned. *)
Theorem pol_dfam_pins_iff :
  forall k p, pol k p (gamma dfam dall) <-> exists i, i < k /\ forall xs, length xs = k -> p xs = nth i xs dz.
Proof.
  intros k p. split.
  - intro H. apply pol_dfam_iff. apply pol_gamma_iff. split; [| intros c []].
    exact (proj1 (proj1 (pol_gamma_iff k p dfam dall) H)).
  - intros [i [Hi Hp]] R HR M HM.
    rewrite (map_ext_in _ (fun j => nth i (col k M j) dz)) by
      (intros j Hj; apply Hp; unfold col; rewrite map_length, seq_length; reflexivity).
    exact (proj_pol dia dz k i dfam dall Hi R HR M HM).
Qed.

(* Any family containing dfam (for instance all monotone self-maps of the diamond), with any pins,
   has only projections as polymorphisms. *)
Corollary pol_superfamily_proj :
  forall (F : list (dia -> dia)) cs k p, incl dfam F -> pol k p (gamma F cs) ->
    exists i, i < k /\ forall xs, length xs = k -> p xs = nth i xs dz.
Proof.
  intros F cs k p HF H. apply pol_dfam_iff. apply pol_gamma_iff. split; [| intros c []].
  intros g Hg. exact (proj1 (proj1 (pol_gamma_iff k p F cs) H) g (HF g Hg)).
Qed.

(* ----- consequences: no Taylor-type polymorphism ----- *)

Theorem dfam_no_siggers :
  forall p, pol 4 p (gamma dfam []) -> ~ (forall x y z, p [x; y; z; x] = p [y; x; y; z]).
Proof.
  intros p Hp H. destruct (dfam_pol_proj 4 p Hp) as [i [Hi Hpi]].
  pose proof (H dz du da) as E. rewrite !Hpi in E by reflexivity.
  destruct i as [| [| [| [| i]]]]; try lia; discriminate E.
Qed.

Theorem dfam_no_majority :
  forall p, pol 3 p (gamma dfam []) -> ~ (forall x y, p [x; x; y] = x /\ p [x; y; x] = x /\ p [y; x; x] = x).
Proof.
  intros p Hp H. destruct (dfam_pol_proj 3 p Hp) as [i [Hi Hpi]].
  destruct (H dz du) as [E1 [E2 E3]]. rewrite Hpi in E1, E2, E3 by reflexivity.
  destruct i as [| [| [| i]]]; try lia; discriminate.
Qed.

Theorem dfam_no_maltsev :
  forall p, pol 3 p (gamma dfam []) -> ~ (forall x y, p [x; x; y] = y /\ p [y; x; x] = y).
Proof.
  intros p Hp H. destruct (dfam_pol_proj 3 p Hp) as [i [Hi Hpi]].
  destruct (H dz du) as [E1 E2]. rewrite Hpi in E1, E2 by reflexivity.
  destruct i as [| [| [| i]]]; try lia; discriminate.
Qed.

Theorem dfam_no_commutative :
  forall p, pol 2 p (gamma dfam []) -> ~ (forall x y, p [x; y] = p [y; x]).
Proof.
  intros p Hp H. destruct (dfam_pol_proj 2 p Hp) as [i [Hi Hpi]].
  pose proof (H dz du) as E. rewrite !Hpi in E by reflexivity.
  destruct i as [| [| i]]; try lia; discriminate.
Qed.

(* The lattice operations, explicitly: join fails at dfl, meet at dor, the median at dor. *)
Definition dmed (x y z : dia) : dia := djoin (djoin (dmeet x y) (dmeet y z)) (dmeet x z).
Definition dmed3 (l : list dia) : dia := match l with [x; y; z] => dmed x y z | _ => dz end.

Theorem dfam_lattice_fails :
  (forall x y, dmed x x y = x /\ dmed x y x = x /\ dmed y x x = x) /\
  dfl (djoin da db) <> djoin (dfl da) (dfl db) /\
  dor (dmeet da db) <> dmeet (dor da) (dor db) /\
  dor (dmed da db dz) <> dmed (dor da) (dor db) (dor dz) /\
  ~ pol 2 djoin2 (gamma dfam []) /\ ~ pol 2 dmeet2 (gamma dfam []) /\ ~ pol 3 dmed3 (gamma dfam []).
Proof.
  split; [intros [] []; repeat split; reflexivity |].
  split; [discriminate |]. split; [discriminate |]. split; [discriminate |].
  split; [| split]; intro H; apply pol_gamma_iff in H; destruct H as [H _].
  - pose proof (H dfl ltac:(simpl; tauto) [da; db] eq_refl) as E. discriminate E.
  - pose proof (H dor ltac:(simpl; tauto) [da; db] eq_refl) as E. discriminate E.
  - pose proof (H dor ltac:(simpl; tauto) [da; db; dz] eq_refl) as E. discriminate E.
Qed.

(* ----- the tractable side: homomorphisms of an idempotent operation ----- *)

Section Semilattice.
  Context {L : Type}.
  Variable j : L -> L -> L.
  Variable d : L.
  Hypothesis j_idem : forall x, j x x = x.

  Definition j2 (l : list L) : L := match l with [x; y] => j x y | _ => d end.

  (* If every map of F preserves j, then j is a polymorphism of gamma F cs for every pin list:
     a semilattice polymorphism when j is a semilattice operation. *)
  Theorem semilattice_pol :
    forall (F : list (L -> L)) cs, (forall f, In f F -> forall x y, f (j x y) = j (f x) (f y)) ->
      pol 2 j2 (gamma F cs).
  Proof.
    intros F cs HF. apply pol_gamma_iff. split.
    - intros f Hf xs Hl. destruct xs as [| x [| y [| w l]]]; simpl in Hl; try discriminate.
      exact (HF f Hf x y).
    - intros c _. simpl. apply j_idem.
  Qed.
End Semilattice.

Theorem joinhom_pol :
  forall (F : list (dia -> dia)) cs, (forall f, In f F -> forall x y, f (djoin x y) = djoin (f x) (f y)) ->
    pol 2 djoin2 (gamma F cs).
Proof. intros F cs HF. exact (semilattice_pol djoin dz (fun x => match x with dz | da | db | du => eq_refl end) F cs HF). Qed.

Theorem meethom_pol :
  forall (F : list (dia -> dia)) cs, (forall f, In f F -> forall x y, f (dmeet x y) = dmeet (f x) (f y)) ->
    pol 2 dmeet2 (gamma F cs).
Proof. intros F cs HF. exact (semilattice_pol dmeet dz (fun x => match x with dz | da | db | du => eq_refl end) F cs HF). Qed.

(* Every map of dfam is needed for the hardness. *)
Theorem dfam_minimal :
  pol 2 djoin2 (gamma [dp1; dp2; dor; dc0; dc1] dall) /\
  pol 2 dmeet2 (gamma [dp1; dp2; dfl; dc0; dc1] dall) /\
  (forall G, labeled [dp1; dp2; dfl; dor; dc1] G -> msection (fun _ => du) G) /\
  (forall G, labeled [dp1; dp2; dfl; dor; dc0] G -> msection (fun _ => dz) G).
Proof.
  split; [| split; [| split]].
  - apply joinhom_pol. intros f Hf x y.
    destruct Hf as [<- | [<- | [<- | [<- | [<- | []]]]]]; destruct x, y; reflexivity.
  - apply meethom_pol. intros f Hf x y.
    destruct Hf as [<- | [<- | [<- | [<- | [<- | []]]]]]; destruct x, y; reflexivity.
  - intros G HG [[u v] f] Hx. unfold msat.
    destruct (HG u v f Hx) as [<- | [<- | [<- | [<- | [<- | []]]]]]; reflexivity.
  - intros G HG [[u v] f] Hx. unfold msat.
    destruct (HG u v f Hx) as [<- | [<- | [<- | [<- | [<- | []]]]]]; reflexivity.
Qed.

(* ----- instances ----- *)

(* The satisfiable clause x0 or x1 or x2: a section, built from the all-true assignment. *)
Theorem dnet_fsat : exists s, msection s (dnet fsat).
Proof. apply dnet_iff_sat. exact fsat_satisfiable. Qed.

Theorem dnet_fsat_check :
  msection_b dia_eq_dec (dstate fsat (fun _ => true)) (dnet fsat) = true.
Proof. vm_compute. reflexivity. Qed.

(* The unsatisfiable 8-clause formula on x0, x1, x2: no section. *)
Theorem dnet_funsat : ~ exists s, msection s (dnet funsat).
Proof. rewrite dnet_iff_sat. exact funsat_unsatisfiable. Qed.

(* The pins are needed: without the two constant self-loops, the all-dz state is a section of the
   network of every formula. *)
Definition dnet_nopin (f : cnf) : list (@edge (dia -> dia)) := dcedges 0 f.

Theorem dnet_needs_pins : forall f, msection (fun _ => dz) (dnet_nopin f).
Proof.
  intros f [[u v] g] Hx. unfold msat. destruct (dcedges_in f 0 _ Hx) as [k [c [_ Hk]]].
  change (0 + k) with k in Hk. unfold dclause_edges, var_edges in Hk. cbn [app In] in Hk.
  repeat (destruct Hk as [E | Hk]; [injection E as _ _ <-; reflexivity |]). destruct Hk.
Qed.
