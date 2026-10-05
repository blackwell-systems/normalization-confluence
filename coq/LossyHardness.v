(* LossyHardness.v: the 3-SAT reduction behind "existence of a section of a lossy network is
   NP-complete" (LOSSY-NETWORKS.md section 3.2), mechanized axiom-free.

   Setting: reading A of LOSSY-NETWORKS.md, as in CohomologyGeneral.v. A network is a list of edges
   (u, v, f) with f : V -> V an arbitrary (possibly lossy) map on ONE shared fiber V; a state s is a
   section when f (s u) = s v on every edge (msection s es). Here V = nat, and every map of the
   constructed network is a 9-entry table on {0..8} (codes 0..7, poison 8), constant above 8.

   What is mechanized: the CORRECTNESS of the reduction and its SIZE BOUND, not complexity theory.
   NP-completeness then follows by the standard argument: membership (a section restricted to the
   network's vertices is a certificate of one value per vertex, checked by one table lookup per
   edge: np_certificate), and hardness (the construction below is linear in the formula,
   net_size, and preserves satisfiability, net_section_iff_sat).

   The construction (net f), for a 3-CNF f with clauses C_0..C_{m-1} over variables x_i:
     clause vertex  cv j = 2j + 2   value: a 3-bit code of an assignment to C_j's three literals
     variable vertex xv i = 2i + 1  value: 0 or 1
     filter vertex  zv = 0          pinned to 0 by a constant self-loop (zv, zv, fun _ => 0)
     projection edge (cv j, xv x, prj C_j k) for the k-th literal x of C_j: a code satisfying C_j
       goes to its k-th bit, anything else to the poison value 8
     filter edge    (xv x, zv, filt) for each occurrence: 0, 1 |-> 0, everything else |-> 1
   The filter gadget is how typed fibers ({0, 1} for variables, the 7 satisfying codes for a clause)
   are fitted into msection's single fiber.

   Main results.
     net_section_iff_sat     (exists s, msection s (net f)) <-> satisfiable f        [exact]
     section_of_sat          a satisfying assignment a gives the section state_of f a
     sat_of_section          a section s gives the satisfying assignment assign_of s
     net_bijection           sections, up to equality on the network's vertices, correspond
                             one to one to satisfying assignments, up to equality on the occurring
                             variables (the reduction is parsimonious)
     net_count               the same as a count: the section tuples on the network's vertices
                             and the satisfying bit vectors on the occurring variables are
                             duplicate-free lists of equal length
     net_size                |net f| = 6 |f| + 1 edges, and the vertex list nverts f, of length
                             4 |f| + 1, contains every vertex of the network
     net_tables              every map is a 9-entry table: it maps {0..8} into {0..8} and is
                             constant on n >= 8
     np_certificate          for any network over a fiber with decidable equality: a section
                             exists iff some tuple of one value per vertex passes the edge-by-edge
                             checker msection_b
     np_certificate_net      the same for net f, with the values drawn from {0..8}
   The gadget is necessary (counterexamples to the reduction without it).
     no_filter_trivial       without the filter edges, the constant poison state is a section for
                             EVERY formula
     no_pin_trivial          with the filter edges but without the pinning self-loop, the state
                             poison everywhere and 1 at the filter vertex is a section for every
                             formula
   Non-vacuity.
     fsat_* / funsat_*       one satisfiable clause (7 satisfying assignments, 7 sections, both
                             counted by computation) and the unsatisfiable 8-clause formula on
                             x0, x1, x2 (no section; the gadget-free variants have one)

   Imports msection_b, tuples and assign from RootSet.v. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.RootSet.
Import ListNotations.

(* ===================================================================== *)
(* 3-CNF formulas. *)

(* A literal is a variable and a negation flag; a clause has exactly three literals. *)
Definition lit : Type := (nat * bool)%type.
Definition clause : Type := (lit * lit * lit)%type.
Definition cnf : Type := list clause.

Definition lit_val (a : nat -> bool) (l : lit) : bool := xorb (a (fst l)) (snd l).

Definition clause_val (a : nat -> bool) (c : clause) : bool :=
  let '(l1, l2, l3) := c in lit_val a l1 || lit_val a l2 || lit_val a l3.

Definition satisfies (a : nat -> bool) (f : cnf) : Prop := forall c, In c f -> clause_val a c = true.

Definition satisfiable (f : cnf) : Prop := exists a, satisfies a f.

Definition sat_check (a : nat -> bool) (f : cnf) : bool := forallb (clause_val a) f.

Theorem sat_check_spec : forall a f, sat_check a f = true <-> satisfies a f.
Proof. intros a f. unfold sat_check, satisfies. apply forallb_forall. Qed.

(* The variable of the p-th literal (p = 0, 1, 2) and the variables occurring in f, one entry per
   occurrence. *)
Definition cvar (c : clause) (p : nat) : nat :=
  let '((x1, _), (x2, _), (x3, _)) := c in
  match p with 0 => x1 | 1 => x2 | _ => x3 end.

Definition occ (f : cnf) : list nat := flat_map (fun c => [cvar c 0; cvar c 1; cvar c 2]) f.

(* A clause read on three bits (the values of its three variables). *)
Definition cbits (c : clause) (y1 y2 y3 : bool) : bool :=
  let '((_, n1), (_, n2), (_, n3)) := c in xorb y1 n1 || xorb y2 n2 || xorb y3 n3.

Lemma clause_val_cbits :
  forall a c, clause_val a c = cbits c (a (cvar c 0)) (a (cvar c 1)) (a (cvar c 2)).
Proof. intros a [[[x1 n1] [x2 n2]] [x3 n3]]. reflexivity. Qed.

Lemma cvar_occ : forall f c p, In c f -> p < 3 -> In (cvar c p) (occ f).
Proof.
  intros f c p Hc Hp. unfold occ. apply in_flat_map. exists c. split; [exact Hc |].
  destruct p as [| [| [| p]]]; simpl; auto.
Qed.

Lemma occ_cvar : forall f i, In i (occ f) -> exists c p, In c f /\ p < 3 /\ i = cvar c p.
Proof.
  intros f i Hi. unfold occ in Hi. apply in_flat_map in Hi. destruct Hi as [c [Hc Hi]].
  exists c. simpl in Hi. destruct Hi as [E | [E | [E | []]]].
  - exists 0. split; [exact Hc | split; [lia | symmetry; exact E]].
  - exists 1. split; [exact Hc | split; [lia | symmetry; exact E]].
  - exists 2. split; [exact Hc | split; [lia | symmetry; exact E]].
Qed.

(* A clause's value depends only on its variables. *)
Lemma satisfies_ext :
  forall f a b, (forall i, In i (occ f) -> a i = b i) -> satisfies a f -> satisfies b f.
Proof.
  intros f a b Hab Ha c Hc. rewrite clause_val_cbits. specialize (Ha c Hc).
  rewrite clause_val_cbits in Ha.
  rewrite <- !Hab by (apply cvar_occ; [exact Hc | lia]). exact Ha.
Qed.

(* ===================================================================== *)
(* Codes: the shared fiber is nat; 0..7 are 3-bit codes, 8 is poison. *)

Definition bn (b : bool) : nat := if b then 1 else 0.

Definition poison : nat := 8.

Definition code3 (y1 y2 y3 : bool) : nat := 4 * bn y1 + 2 * bn y2 + bn y3.

Definition bit (p n : nat) : bool :=
  match p with
  | 0 => Nat.odd (Nat.div2 (Nat.div2 n))
  | 1 => Nat.odd (Nat.div2 n)
  | _ => Nat.odd n
  end.

Lemma bit_code :
  forall y1 y2 y3,
    bit 0 (code3 y1 y2 y3) = y1 /\ bit 1 (code3 y1 y2 y3) = y2 /\ bit 2 (code3 y1 y2 y3) = y3 /\
    code3 y1 y2 y3 < 8.
Proof. intros [] [] []; repeat split; (reflexivity || (unfold code3, bn; simpl; lia)). Qed.

Lemma code_bits : forall n, n < 8 -> code3 (bit 0 n) (bit 1 n) (bit 2 n) = n.
Proof. intros n Hn. do 8 (destruct n as [| n]; [reflexivity |]). lia. Qed.

Lemma bn_le : forall b, bn b <= 1.
Proof. intros []; simpl; lia. Qed.

Lemma bn_eqb : forall b, Nat.eqb (bn b) 1 = b.
Proof. intros []; reflexivity. Qed.

Lemma eqb_bn : forall m, m <= 1 -> bn (Nat.eqb m 1) = m.
Proof. intros [| [| m]] H; [reflexivity | reflexivity | lia]. Qed.

(* The codes that satisfy a clause. *)
Definition code_ok (c : clause) (n : nat) : bool :=
  Nat.ltb n 8 && cbits c (bit 0 n) (bit 1 n) (bit 2 n).

Lemma code_ok_spec :
  forall c n, code_ok c n = true <-> n < 8 /\ cbits c (bit 0 n) (bit 1 n) (bit 2 n) = true.
Proof. intros c n. unfold code_ok. rewrite andb_true_iff, Nat.ltb_lt. tauto. Qed.

(* The three kinds of maps. *)
Definition prj (c : clause) (p : nat) (n : nat) : nat :=
  if code_ok c n then bn (bit p n) else poison.

Definition filt (n : nat) : nat := if Nat.leb n 1 then 0 else 1.

Definition pin (_ : nat) : nat := 0.

Lemma prj_code :
  forall c p y1 y2 y3, p < 3 -> cbits c y1 y2 y3 = true ->
    prj c p (code3 y1 y2 y3) = bn (match p with 0 => y1 | 1 => y2 | _ => y3 end).
Proof.
  intros c p y1 y2 y3 Hp Hc. destruct (bit_code y1 y2 y3) as [E1 [E2 [E3 L]]].
  unfold prj. replace (code_ok c (code3 y1 y2 y3)) with true.
  - destruct p as [| [| [| p]]]; [rewrite E1 | rewrite E2 | rewrite E3 | lia]; reflexivity.
  - symmetry. apply code_ok_spec. rewrite E1, E2, E3. auto.
Qed.

Lemma prj_inv : forall c p n m, prj c p n = m -> m <= 1 -> code_ok c n = true /\ bn (bit p n) = m.
Proof.
  intros c p n m E Hm. unfold prj in E. destruct (code_ok c n); [auto | unfold poison in E; lia].
Qed.

Lemma filt_zero : forall n, filt n = 0 -> n <= 1.
Proof. intros n. unfold filt. destruct (Nat.leb n 1) eqn:E; [apply Nat.leb_le in E; lia | discriminate]. Qed.

(* ===================================================================== *)
(* The network. *)

Definition zv : nat := 0.
Definition xv (i : nat) : nat := S (2 * i).
Definition cv (j : nat) : nat := S (S (2 * j)).

Definition clause_edges (j : nat) (c : clause) : list (@edge (nat -> nat)) :=
  [(cv j, xv (cvar c 0), prj c 0); (cv j, xv (cvar c 1), prj c 1); (cv j, xv (cvar c 2), prj c 2);
   (xv (cvar c 0), zv, filt); (xv (cvar c 1), zv, filt); (xv (cvar c 2), zv, filt)].

Fixpoint cedges (j : nat) (f : cnf) : list (@edge (nat -> nat)) :=
  match f with
  | [] => []
  | c :: f' => clause_edges j c ++ cedges (S j) f'
  end.

Definition net (f : cnf) : list (@edge (nat -> nat)) := (zv, zv, pin) :: cedges 0 f.

(* The network's vertices: the filter, one per clause, one per occurrence. *)
Definition nverts (f : cnf) : list nat := zv :: map cv (seq 0 (length f)) ++ map xv (occ f).

Lemma cedges_in :
  forall g j x, In x (cedges j g) -> exists k c, nth_error g k = Some c /\ In x (clause_edges (j + k) c).
Proof.
  induction g as [| c g IH]; intros j x Hx; [simpl in Hx; contradiction |].
  change (In x (clause_edges j c ++ cedges (S j) g)) in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - exists 0, c. rewrite Nat.add_0_r. auto.
  - destruct (IH (S j) x Hx) as [k [c' [Hk Hx']]]. exists (S k), c'. split; [exact Hk |].
    replace (j + S k) with (S j + k) by lia. exact Hx'.
Qed.

Lemma cedges_has :
  forall g j k c, nth_error g k = Some c -> incl (clause_edges (j + k) c) (cedges j g).
Proof.
  induction g as [| c0 g IH]; intros j k c Hk x Hx; destruct k as [| k]; simpl in Hk;
    try discriminate.
  - injection Hk as E. subst c. change (In x (clause_edges j c0 ++ cedges (S j) g)).
    apply in_or_app. left. rewrite Nat.add_0_r in Hx. exact Hx.
  - change (In x (clause_edges j c0 ++ cedges (S j) g)). apply in_or_app. right. apply (IH (S j) k c Hk).
    replace (S j + k) with (j + S k) by lia. exact Hx.
Qed.

(* ----- the state of an assignment ----- *)

Definition ccode (a : nat -> bool) (c : clause) : nat :=
  code3 (a (cvar c 0)) (a (cvar c 1)) (a (cvar c 2)).

Definition state_of (f : cnf) (a : nat -> bool) (v : nat) : nat :=
  match v with
  | 0 => 0
  | S w =>
      if Nat.even w then bn (a (Nat.div2 w))
      else match nth_error f (Nat.div2 w) with Some c => ccode a c | None => 0 end
  end.

Definition assign_of (s : nat -> nat) (i : nat) : bool := Nat.eqb (s (xv i)) 1.

Lemma even_double : forall i, Nat.even (2 * i) = true /\ Nat.div2 (2 * i) = i.
Proof.
  induction i as [| i IH]; [split; reflexivity |].
  replace (2 * S i) with (S (S (2 * i))) by lia.
  change (Nat.even (2 * i) = true /\ S (Nat.div2 (2 * i)) = S i).
  destruct IH as [E D]. rewrite E, D. auto.
Qed.

Lemma odd_double : forall j, Nat.even (S (2 * j)) = false /\ Nat.div2 (S (2 * j)) = j.
Proof.
  induction j as [| j IH]; [split; reflexivity |].
  replace (S (2 * S j)) with (S (S (S (2 * j)))) by lia.
  change (Nat.even (S (2 * j)) = false /\ S (Nat.div2 (S (2 * j))) = S j).
  destruct IH as [E D]. rewrite E, D. auto.
Qed.

Lemma state_z : forall f a, state_of f a zv = 0.
Proof. reflexivity. Qed.

Lemma state_x : forall f a i, state_of f a (xv i) = bn (a i).
Proof.
  intros f a i. unfold xv, state_of. destruct (even_double i) as [E D]. rewrite E, D. reflexivity.
Qed.

Lemma state_c : forall f a j c, nth_error f j = Some c -> state_of f a (cv j) = ccode a c.
Proof.
  intros f a j c Hj. unfold cv, state_of. destruct (odd_double j) as [E D]. rewrite E, D, Hj.
  reflexivity.
Qed.

Lemma assign_state : forall f a i, assign_of (state_of f a) i = a i.
Proof. intros f a i. unfold assign_of. rewrite state_x. apply bn_eqb. Qed.

(* ===================================================================== *)
(* Correctness. *)

Theorem section_of_sat : forall f a, satisfies a f -> msection (state_of f a) (net f).
Proof.
  intros f a Ha x Hx. destruct Hx as [<- | Hx]; [reflexivity |].
  destruct (cedges_in f 0 x Hx) as [k [c [Hk Hxk]]]. simpl in Hxk.
  pose proof (Ha c (nth_error_In f k Hk)) as Hc. rewrite clause_val_cbits in Hc.
  unfold msat. destruct Hxk as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    rewrite ?state_c with (c := c) by exact Hk; rewrite ?state_x; unfold ccode;
    try (rewrite prj_code by (exact Hc || lia); reflexivity);
    unfold filt; rewrite (proj2 (Nat.leb_le _ _) (bn_le _)); reflexivity.
Qed.

(* What a section says about one clause: the filter vertex is 0, the clause value is a satisfying
   code, and each of the clause's variables holds the matching bit. *)
Lemma section_clause :
  forall f s k c, msection s (net f) -> nth_error f k = Some c ->
    s zv = 0 /\ code_ok c (s (cv k)) = true /\
    forall p, p < 3 -> s (xv (cvar c p)) = bn (bit p (s (cv k))).
Proof.
  intros f s k c Hs Hk.
  assert (Hin : forall x, In x (clause_edges k c) -> msat s x).
  { intros x Hx. apply Hs. right. exact (cedges_has f 0 k c Hk x Hx). }
  assert (Hz : s zv = 0) by (symmetry; exact (Hs _ (or_introl eq_refl))).
  assert (Hp : forall p, p < 3 ->
            code_ok c (s (cv k)) = true /\ bn (bit p (s (cv k))) = s (xv (cvar c p))).
  { intros p Hp. assert (Hf : s (xv (cvar c p)) <= 1).
    { apply filt_zero. rewrite <- Hz.
      destruct p as [| [| [| p]]]; [| | | lia]; apply (Hin (_, _, filt)); simpl; tauto. }
    apply (prj_inv c p); [| exact Hf].
    destruct p as [| [| [| p]]]; [| | | lia]; apply (Hin (_, _, prj c _)); simpl; tauto. }
  split; [exact Hz |]. split; [exact (proj1 (Hp 0 ltac:(lia))) |].
  intros p Hp'. symmetry. exact (proj2 (Hp p Hp')).
Qed.

Theorem sat_of_section : forall f s, msection s (net f) -> satisfies (assign_of s) f.
Proof.
  intros f s Hs c Hc. destruct (In_nth_error f c Hc) as [k Hk].
  destruct (section_clause f s k c Hs Hk) as [_ [Hok Hv]].
  apply code_ok_spec in Hok. rewrite clause_val_cbits. unfold assign_of.
  rewrite !Hv by lia. rewrite !bn_eqb. exact (proj2 Hok).
Qed.

(* The reduction is correct: the network has a section iff the formula is satisfiable. *)
Theorem net_section_iff_sat : forall f, (exists s, msection s (net f)) <-> satisfiable f.
Proof.
  intro f. split.
  - intros [s Hs]. exists (assign_of s). exact (sat_of_section f s Hs).
  - intros [a Ha]. exists (state_of f a). exact (section_of_sat f a Ha).
Qed.

(* ===================================================================== *)
(* Parsimony: sections correspond one to one to satisfying assignments. *)

Lemma section_values :
  forall f s, msection s (net f) -> forall v, In v (nverts f) -> state_of f (assign_of s) v = s v.
Proof.
  intros f s Hs v Hv. destruct Hv as [<- | Hv].
  - rewrite state_z. exact (Hs _ (or_introl eq_refl)).
  - apply in_app_or in Hv. destruct Hv as [Hv | Hv]; apply in_map_iff in Hv;
      destruct Hv as [w [<- Hw]].
    + apply in_seq in Hw. destruct (nth_error f w) as [c |] eqn:Hk;
        [| apply nth_error_None in Hk; lia].
      destruct (section_clause f s w c Hs Hk) as [_ [Hok Hval]].
      apply code_ok_spec in Hok. rewrite (state_c f _ w c Hk). unfold ccode, assign_of.
      rewrite !Hval by lia. rewrite !bn_eqb. apply code_bits. exact (proj1 Hok).
    + destruct (occ_cvar f w Hw) as [c [p [Hc [Hp ->]]]].
      destruct (In_nth_error f c Hc) as [k Hk].
      destruct (section_clause f s k c Hs Hk) as [_ [_ Hval]].
      rewrite state_x. unfold assign_of. apply eqb_bn. rewrite (Hval p Hp). apply bn_le.
Qed.

Lemma state_of_ext :
  forall f a b, (forall i, In i (occ f) -> a i = b i) ->
    forall v, In v (nverts f) -> state_of f a v = state_of f b v.
Proof.
  intros f a b Hab v Hv. destruct Hv as [<- | Hv]; [reflexivity |].
  apply in_app_or in Hv. destruct Hv as [Hv | Hv]; apply in_map_iff in Hv;
    destruct Hv as [w [<- Hw]].
  - apply in_seq in Hw. destruct (nth_error f w) as [c |] eqn:Hk; [| apply nth_error_None in Hk; lia].
    rewrite !(state_c f _ w c Hk). unfold ccode.
    rewrite !Hab by (apply cvar_occ; [exact (nth_error_In f w Hk) | lia]). reflexivity.
  - rewrite !state_x. rewrite (Hab w Hw). reflexivity.
Qed.

(* Sections modulo agreement on the network's vertices, and satisfying assignments modulo
   agreement on the occurring variables, are in bijection: assign_of and state_of map each class
   into the other, are well defined on classes, and are mutually inverse. *)
Theorem net_bijection :
  forall f,
    (forall a, satisfies a f -> msection (state_of f a) (net f)) /\
    (forall s, msection s (net f) -> satisfies (assign_of s) f) /\
    (forall a i, assign_of (state_of f a) i = a i) /\
    (forall s, msection s (net f) -> forall v, In v (nverts f) -> state_of f (assign_of s) v = s v) /\
    (forall a b, (forall i, In i (occ f) -> a i = b i) ->
       forall v, In v (nverts f) -> state_of f a v = state_of f b v) /\
    (forall s t, (forall v, In v (nverts f) -> s v = t v) ->
       forall i, In i (occ f) -> assign_of s i = assign_of t i).
Proof.
  intro f. split; [exact (section_of_sat f) |]. split; [exact (sat_of_section f) |].
  split; [exact (assign_state f) |]. split; [exact (section_values f) |].
  split; [exact (state_of_ext f) |].
  intros s t Hst i Hi. unfold assign_of. rewrite Hst; [reflexivity |].
  right. apply in_or_app. right. apply in_map. exact Hi.
Qed.

(* Two sections that induce the same assignment on the occurring variables agree on the network;
   two satisfying assignments that induce the same state on the network agree on the occurring
   variables. *)
Corollary sections_determined :
  forall f s t, msection s (net f) -> msection t (net f) ->
    (forall i, In i (occ f) -> assign_of s i = assign_of t i) ->
    forall v, In v (nverts f) -> s v = t v.
Proof.
  intros f s t Hs Ht H v Hv.
  rewrite <- (section_values f s Hs v Hv), <- (section_values f t Ht v Hv).
  exact (state_of_ext f _ _ H v Hv).
Qed.

Corollary assignments_determined :
  forall f a b, (forall v, In v (nverts f) -> state_of f a v = state_of f b v) ->
    forall i, In i (occ f) -> a i = b i.
Proof.
  intros f a b H i Hi. rewrite <- (assign_state f a i), <- (assign_state f b i).
  apply (proj2 (proj2 (proj2 (proj2 (proj2 (net_bijection f)))))); [exact H | exact Hi].
Qed.

(* ===================================================================== *)
(* Size. *)

Lemma cedges_length : forall g j, length (cedges j g) = 6 * length g.
Proof.
  induction g as [| c g IH]; intro j; [reflexivity |].
  change (length (clause_edges j c ++ cedges (S j) g) = 6 * S (length g)).
  rewrite app_length, IH. simpl. lia.
Qed.

Lemma occ_length : forall f, length (occ f) = 3 * length f.
Proof.
  induction f as [| c f IH]; simpl; [reflexivity |]. unfold occ in *. simpl. rewrite IH. lia.
Qed.

Lemma cedges_verts :
  forall g j v, In v (verts (cedges j g)) ->
    v = zv \/ (exists k, k < length g /\ v = cv (j + k)) \/ In v (map xv (occ g)).
Proof.
  induction g as [| c g IH]; intros j v Hv; [simpl in Hv; contradiction |].
  change (In v (verts (clause_edges j c ++ cedges (S j) g))) in Hv.
  change (occ (c :: g)) with ([cvar c 0; cvar c 1; cvar c 2] ++ occ g). rewrite map_app.
  rewrite verts_app in Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv].
  - simpl in Hv.
    repeat (destruct Hv as [<- | Hv];
            [first [left; reflexivity
                   | right; left; exists 0; split; [simpl; lia | rewrite Nat.add_0_r; reflexivity]
                   | right; right; apply in_or_app; left; simpl; tauto] |]).
    contradiction.
  - destruct (IH (S j) v Hv) as [Hz | [[k [Hk ->]] | Hx]]; [left; exact Hz | |].
    + right. left. exists (S k). split; [simpl; lia |]. f_equal. lia.
    + right. right. apply in_or_app. right. exact Hx.
Qed.

(* The network is linear in the formula: 6m + 1 edges, at most 4m + 1 vertices (m clauses). *)
Theorem net_size :
  forall f, length (net f) = 6 * length f + 1 /\ length (nverts f) = 4 * length f + 1 /\
            incl (verts (net f)) (nverts f).
Proof.
  intro f. split; [| split].
  - unfold net. simpl. rewrite cedges_length. lia.
  - unfold nverts. simpl. rewrite app_length, !map_length, seq_length, occ_length. lia.
  - intros v Hv. unfold net in Hv. simpl in Hv.
    destruct Hv as [<- | [<- | Hv]]; [left; reflexivity | left; reflexivity |].
    destruct (cedges_verts f 0 v Hv) as [-> | [[k [Hk ->]] | Hx]]; [left; reflexivity | |].
    + right. apply in_or_app. left. apply in_map. apply in_seq. lia.
    + right. apply in_or_app. right. exact Hx.
Qed.

(* Every map of the network is a table on the 9 values {0..8}: it maps {0..8} into {0..8} and is
   constant from 8 on. *)
Theorem net_tables :
  forall f u v g, In (u, v, g) (net f) ->
    (forall n, n <= 8 -> g n <= 8) /\ (forall n, 8 <= n -> g n = g 8).
Proof.
  intros f u v g Hx. destruct Hx as [E | Hx].
  - injection E as _ _ <-. unfold pin. split; intros; lia.
  - destruct (cedges_in f 0 _ Hx) as [k [c [_ Hk]]]. simpl in Hk.
    assert (Hp : forall p, (forall n, n <= 8 -> prj c p n <= 8) /\
                           (forall n, 8 <= n -> prj c p n = prj c p 8)).
    { intro p. split.
      - intros n _. unfold prj, poison. destruct (code_ok c n); [pose proof (bn_le (bit p n)); lia | lia].
      - intros n Hn. unfold prj. replace (code_ok c n) with false; [replace (code_ok c 8) with false; [reflexivity |] |].
        + symmetry. apply not_true_iff_false. intro H. apply code_ok_spec in H. lia.
        + symmetry. apply not_true_iff_false. intro H. apply code_ok_spec in H. lia. }
    assert (Hf : (forall n, n <= 8 -> filt n <= 8) /\ (forall n, 8 <= n -> filt n = filt 8)).
    { unfold filt. split; intros n Hn; destruct (Nat.leb n 1) eqn:E; try reflexivity; try lia.
      apply Nat.leb_le in E. lia. }
    destruct Hk as [E | [E | [E | [E | [E | [E | []]]]]]]; injection E as _ _ <-;
      first [exact (Hp _) | exact Hf].
Qed.

(* ===================================================================== *)
(* Membership in NP: a section is certified by one value per vertex, checked edge by edge. *)

(* A section only depends on the network's vertices. *)
Lemma msection_ext :
  forall (V : Type) (es : list (@edge (V -> V))) (s t : nat -> V),
    (forall v, In v (verts es) -> s v = t v) -> msection s es -> msection t es.
Proof.
  intros V es s t Hst Hs [[u v] g] Hx. pose proof (Hs _ Hx) as E. unfold msat in *.
  destruct (in_verts_edge es u v g Hx) as [Hu Hv]. rewrite <- (Hst u Hu), <- (Hst v Hv). exact E.
Qed.

(* For any network over a fiber with decidable equality, listed by lv: a section exists iff some
   tuple of values on the vertices (duplicates removed), drawn from lv, passes msection_b, which
   performs one equality test per edge. *)
Theorem np_certificate :
  forall (V : Type) (Vdec : forall x y : V, {x = y} + {x <> y}) (v0 : V) (lv : list V)
         (es : list (@edge (V -> V))),
    (forall x, In x lv) ->
    ((exists s, msection s es) <->
     exists t, In t (tuples lv (length (nodup Nat.eq_dec (verts es)))) /\
               msection_b Vdec (assign v0 (nodup Nat.eq_dec (verts es)) t) es = true).
Proof.
  intros V Vdec v0 lv es Hlv. set (R := nodup Nat.eq_dec (verts es)). split.
  - intros [s Hs]. exists (map s R). split.
    + apply tuples_spec. split; [apply map_length | intros x _; apply Hlv].
    + apply msection_b_spec. apply (msection_ext V es s); [| exact Hs].
      intros v Hv. symmetry. apply assign_map. apply nodup_In. exact Hv.
  - intros [t [_ Ht]]. exists (assign v0 R t). apply msection_b_spec in Ht. exact Ht.
Qed.

Definition vals9 : list nat := seq 0 9.

Definition nv (f : cnf) : list nat := nodup Nat.eq_dec (nverts f).
Definition lo (f : cnf) : list nat := nodup Nat.eq_dec (occ f).

(* The certificate for net f: one value in {0..8} per vertex of nverts f. *)
Definition cert_ok (f : cnf) (t : list nat) : bool :=
  msection_b Nat.eq_dec (assign 0 (nv f) t) (net f).

Lemma state_of_range : forall f a v, In v (nverts f) -> state_of f a v < 8.
Proof.
  intros f a v Hv. destruct Hv as [<- | Hv]; [simpl; lia |].
  apply in_app_or in Hv. destruct Hv as [Hv | Hv]; apply in_map_iff in Hv; destruct Hv as [w [<- Hw]].
  - apply in_seq in Hw. destruct (nth_error f w) as [c |] eqn:Hk; [| apply nth_error_None in Hk; lia].
    rewrite (state_c f a w c Hk). unfold ccode. apply bit_code.
  - rewrite state_x. pose proof (bn_le (a w)). lia.
Qed.

Lemma cert_section :
  forall f s, msection s (net f) <-> msection (assign 0 (nv f) (map s (nv f))) (net f).
Proof.
  intros f s. pose proof (proj2 (proj2 (net_size f))) as Hincl.
  assert (Hag : forall v, In v (verts (net f)) -> assign 0 (nv f) (map s (nv f)) v = s v).
  { intros v Hv. apply assign_map. apply nodup_In. exact (Hincl v Hv). }
  split; apply msection_ext; intros v Hv; [symmetry |]; exact (Hag v Hv).
Qed.

Theorem np_certificate_net :
  forall f, (exists s, msection s (net f)) <->
            exists t, In t (tuples vals9 (length (nv f))) /\ cert_ok f t = true.
Proof.
  intro f. split.
  - intros [s Hs]. exists (map (state_of f (assign_of s)) (nv f)). split.
    + apply tuples_spec. split; [apply map_length |]. intros x Hx. apply in_map_iff in Hx.
      destruct Hx as [v [<- Hv]]. apply nodup_In in Hv. apply in_seq.
      pose proof (state_of_range f (assign_of s) v Hv). lia.
    + unfold cert_ok. apply msection_b_spec. apply (proj1 (cert_section f _)).
      apply section_of_sat. exact (sat_of_section f s Hs).
  - intros [t [_ Ht]]. exists (assign 0 (nv f) t). apply msection_b_spec in Ht. exact Ht.
Qed.

(* ===================================================================== *)
(* Counting: #sections = #satisfying assignments. *)

(* The sections, recorded on the network's vertices (values in {0..8}), and the satisfying
   assignments, recorded on the occurring variables. *)
Definition section_tuples (f : cnf) : list (list nat) :=
  filter (cert_ok f) (tuples vals9 (length (nv f))).

Definition sat_tuples (f : cnf) : list (list bool) :=
  filter (fun bs => sat_check (assign false (lo f) bs) f) (tuples [true; false] (length (lo f))).

Lemma vals9_nodup : NoDup vals9.
Proof. apply seq_NoDup. Qed.

Lemma bools_nodup : NoDup [true; false].
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma map_eq_in :
  forall (A B : Type) (h1 h2 : A -> B) (l : list A) x, map h1 l = map h2 l -> In x l -> h1 x = h2 x.
Proof.
  intros A B h1 h2 l x. induction l as [| y l IH]; simpl; intros E Hx; [contradiction |].
  injection E as E1 E2. destruct Hx as [<- | Hx]; [exact E1 | exact (IH E2 Hx)].
Qed.

Theorem net_count :
  forall f,
    NoDup (section_tuples f) /\ NoDup (sat_tuples f) /\
    (forall t, In t (section_tuples f) <-> exists s, msection s (net f) /\ map s (nv f) = t) /\
    (forall bs, In bs (sat_tuples f) <-> exists a, satisfies a f /\ map a (lo f) = bs) /\
    length (section_tuples f) = length (sat_tuples f).
Proof.
  intro f.
  assert (Hnv : NoDup (nv f)) by apply NoDup_nodup.
  assert (Hlo : NoDup (lo f)) by apply NoDup_nodup.
  assert (HS : NoDup (section_tuples f))
    by (apply rs_nodup_filter; apply tuples_nodup; exact vals9_nodup).
  assert (HA : NoDup (sat_tuples f))
    by (apply rs_nodup_filter; apply tuples_nodup; exact bools_nodup).
  (* membership in the sections list *)
  assert (MS : forall t, In t (section_tuples f) <-> exists s, msection s (net f) /\ map s (nv f) = t).
  { intro t. unfold section_tuples, cert_ok. rewrite filter_In, tuples_spec, msection_b_spec. split.
    - intros [[Hl _] Hs]. exists (assign 0 (nv f) t). split; [exact Hs |].
      apply map_assign; [exact Hnv | exact Hl].
    - intros [s [Hs <-]]. split; [split |].
      + apply map_length.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as [v [<- Hv]].
        apply nodup_In in Hv. apply in_seq. rewrite <- (section_values f s Hs v Hv).
        pose proof (state_of_range f (assign_of s) v Hv). lia.
      + apply (proj1 (cert_section f s)). exact Hs. }
  (* membership in the assignments list *)
  assert (MA : forall bs, In bs (sat_tuples f) <-> exists a, satisfies a f /\ map a (lo f) = bs).
  { intro bs. unfold sat_tuples. rewrite filter_In, tuples_spec, sat_check_spec. split.
    - intros [[Hl _] Ha]. exists (assign false (lo f) bs). split; [exact Ha |].
      apply map_assign; [exact Hlo | exact Hl].
    - intros [a [Ha <-]]. split; [split |].
      + apply map_length.
      + intros [] _; simpl; auto.
      + apply (satisfies_ext f a); [| exact Ha]. intros i Hi. symmetry. apply assign_map.
        apply nodup_In. exact Hi. }
  split; [exact HS |]. split; [exact HA |]. split; [exact MS |]. split; [exact MA |].
  (* the bijection, as a map from assignments to sections *)
  set (g := fun bs => map (state_of f (assign false (lo f) bs)) (nv f)).
  assert (Hag : forall a bs, map a (lo f) = bs -> forall i, In i (occ f) -> assign false (lo f) bs i = a i).
  { intros a bs <- i Hi. apply assign_map. apply nodup_In. exact Hi. }
  assert (Hinj : NoDup (map g (sat_tuples f))).
  { apply nodup_map_inj; [exact HA |]. intros b1 b2 H1 H2 E.
    apply MA in H1, H2. destruct H1 as [a1 [_ <-]]. destruct H2 as [a2 [_ <-]].
    apply map_ext_in. intros i Hi. apply nodup_In in Hi.
    rewrite <- (Hag a1 _ eq_refl i Hi), <- (Hag a2 _ eq_refl i Hi).
    apply (assignments_determined f); [| exact Hi]. intros v Hv.
    assert (Ev : In v (nv f)) by (apply nodup_In; exact Hv).
    unfold g in E. exact (map_eq_in _ _ _ _ (nv f) v E Ev). }
  assert (Hto : incl (map g (sat_tuples f)) (section_tuples f)).
  { intros t Ht. apply in_map_iff in Ht. destruct Ht as [bs [<- Hbs]].
    apply MA in Hbs. destruct Hbs as [a [Ha Ebs]]. apply MS.
    exists (state_of f (assign false (lo f) bs)). split; [| reflexivity].
    apply section_of_sat. apply (satisfies_ext f a); [| exact Ha].
    intros i Hi. symmetry. exact (Hag a bs Ebs i Hi). }
  assert (Hfrom : incl (section_tuples f) (map g (sat_tuples f))).
  { intros t Ht. apply MS in Ht. destruct Ht as [s [Hs <-]]. apply in_map_iff.
    exists (map (assign_of s) (lo f)). split.
    - unfold g. apply map_ext_in. intros v Hv. apply nodup_In in Hv.
      rewrite <- (section_values f s Hs v Hv). apply state_of_ext; [| exact Hv].
      exact (Hag (assign_of s) _ eq_refl).
    - apply MA. exists (assign_of s). split; [exact (sat_of_section f s Hs) | reflexivity]. }
  pose proof (NoDup_incl_length Hinj Hto). pose proof (NoDup_incl_length HS Hfrom).
  rewrite map_length in *. lia.
Qed.

(* ===================================================================== *)
(* The gadget is necessary. *)

(* The reduction without the filter edges and the pin: projection edges only. *)
Definition proj_edges (j : nat) (c : clause) : list (@edge (nat -> nat)) :=
  [(cv j, xv (cvar c 0), prj c 0); (cv j, xv (cvar c 1), prj c 1); (cv j, xv (cvar c 2), prj c 2)].

Fixpoint pedges (j : nat) (f : cnf) : list (@edge (nat -> nat)) :=
  match f with [] => [] | c :: f' => proj_edges j c ++ pedges (S j) f' end.

Lemma prj_poison : forall c p, prj c p poison = poison.
Proof.
  intros c p. unfold prj. replace (code_ok c poison) with false; [reflexivity |].
  symmetry. apply not_true_iff_false. intro H. apply code_ok_spec in H. unfold poison in H. lia.
Qed.

Lemma pedges_in :
  forall g j x, In x (pedges j g) -> exists k c, In x (proj_edges k c).
Proof.
  induction g as [| c g IH]; intros j x Hx; [simpl in Hx; contradiction |].
  change (In x (proj_edges j c ++ pedges (S j) g)) in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exists j, c; exact Hx | exact (IH _ _ Hx)].
Qed.

(* Without the filter, every formula's network has a section: poison everywhere. *)
Theorem no_filter_trivial : forall f, msection (fun _ => poison) (pedges 0 f).
Proof.
  intros f x Hx. destruct (pedges_in f 0 x Hx) as [k [c Hk]]. simpl in Hk.
  destruct Hk as [<- | [<- | [<- | []]]]; apply prj_poison.
Qed.

(* With the filter edges but without the pin, every formula's network has a section: poison
   everywhere and 1 at the filter vertex. *)
Theorem no_pin_trivial :
  forall f, msection (fun v => if Nat.eqb v zv then 1 else poison) (cedges 0 f).
Proof.
  intros f x Hx. destruct (cedges_in f 0 x Hx) as [k [c [_ Hk]]]. simpl in Hk.
  destruct Hk as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; unfold msat, xv, cv, zv; simpl;
    first [apply prj_poison | reflexivity].
Qed.

(* ===================================================================== *)
(* Instances. *)

(* One clause x0 \/ x1 \/ x2: satisfiable, 7 satisfying assignments, 7 sections. *)
Definition fsat : cnf := [((0, false), (1, false), (2, false))].

Theorem fsat_satisfiable : satisfiable fsat.
Proof. exists (fun _ => true). intros c [<- | []]. reflexivity. Qed.

Theorem fsat_has_section : exists s, msection s (net fsat).
Proof. apply net_section_iff_sat. exact fsat_satisfiable. Qed.

Theorem fsat_check : cert_ok fsat (map (state_of fsat (fun _ => true)) (nv fsat)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fsat_count : length (sat_tuples fsat) = 7 /\ length (section_tuples fsat) = 7.
Proof. split; vm_compute; reflexivity. Qed.

(* All 8 sign patterns on x0, x1, x2: unsatisfiable, so no section; the gadget-free variants of
   its network have one. *)
Definition funsat : cnf :=
  [((0, false), (1, false), (2, false)); ((0, false), (1, false), (2, true));
   ((0, false), (1, true), (2, false));  ((0, false), (1, true), (2, true));
   ((0, true), (1, false), (2, false));  ((0, true), (1, false), (2, true));
   ((0, true), (1, true), (2, false));   ((0, true), (1, true), (2, true))].

Theorem funsat_unsatisfiable : ~ satisfiable funsat.
Proof.
  intros [a Ha]. unfold satisfies in Ha.
  destruct (a 0) eqn:E0, (a 1) eqn:E1, (a 2) eqn:E2;
    [ specialize (Ha _ (nth_error_In funsat 7 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 6 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 5 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 4 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 3 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 2 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 1 eq_refl))
    | specialize (Ha _ (nth_error_In funsat 0 eq_refl)) ];
    simpl in Ha; unfold lit_val in Ha; simpl in Ha; rewrite E0, E1, E2 in Ha; discriminate.
Qed.

Theorem funsat_no_section : ~ exists s, msection s (net funsat).
Proof. rewrite net_section_iff_sat. exact funsat_unsatisfiable. Qed.

Theorem funsat_count : length (sat_tuples funsat) = 0 /\ length (section_tuples funsat) = 0.
Proof.
  assert (H : length (sat_tuples funsat) = 0) by (vm_compute; reflexivity).
  split; [exact H |]. rewrite (proj2 (proj2 (proj2 (proj2 (net_count funsat))))). exact H.
Qed.

Theorem funsat_gadget_needed :
  (exists s, msection s (pedges 0 funsat)) /\ (exists s, msection s (cedges 0 funsat)).
Proof.
  split; [exists (fun _ => poison); apply no_filter_trivial |].
  exists (fun v => if Nat.eqb v zv then 1 else poison). apply no_pin_trivial.
Qed.
