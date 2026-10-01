(* CohomologyMin.v: the graph-level minimum-coordination counts for the S_3 separating instance,
   mechanized axiom-free. Cohomology.v machine-checks the finite crux facts of the theta-graph
   separation (each single-edge deletion leaves a non-trivial holonomy; the sign of a is even,
   of b odd) and leaves the graph-level wrapping (min_G = 2, min_{G^ab} = 1) at the paper level.
   This file closes that wrapping.

   The objects are stated directly, not through a checker:
   - The theta graph: two vertices 0 and 1, three parallel edges e1, e2, e3 from 0 to 1, labeled
     by the S_3 elements id, a = (0 1 2), b = (0 1) (the spanning edge e1 gauged to the identity),
     matching the labeling of Cohomology.v and CATEGORICAL-STRUCTURE.md section 10.3.
   - A coordination deletes edges; the kept edges are the constraints still in force.
   - A global section (H^0 non-empty) is a pair of fiber values s0, s1 in S_3, the S_3-torsor,
     such that every kept edge transports s0 to s1. That is the gluing condition itself.
   - The abelianized problem replaces each label by its sign in Z/2 = S_3^ab, acting on the fiber
     bool by xor; sign is proven to be a homomorphism, so this is the true abelian image.

   Results:
   - min_G = 2: every coordination leaving a section deletes at least two edges, and deleting two
     (keeping only the spanning edge) leaves one.
   - min_{G^ab} = 1: every abelian section needs at least one deletion, and deleting e3 (the odd
     edge b) suffices, since the remaining labels id and a are both even.
   - Functoriality: any S_3 section maps to an abelian section, so on any edge set the abelian
     minimum never exceeds the non-abelian one (non-commutativity raises the floor, never lowers it).
   - Hence the strict separation 1 = min_{G^ab} < min_G = 2.

   Sections are decided by finite enumeration of the torsor, and each decider is proven equivalent
   to the Prop it decides, so every theorem is about sections, not about the decider. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Import NC.Cohomology.
Import S3Sep.

(* ===== The fiber: S_3 as a finite type of image-triples ===== *)

Definition peqb (p q : perm) : bool :=
  let '(x1, y1, z1) := p in
  let '(x2, y2, z2) := q in
  Nat.eqb x1 x2 && Nat.eqb y1 y2 && Nat.eqb z1 z2.

Lemma peqb_eq : forall p q, peqb p q = true <-> p = q.
Proof.
  intros [[x1 y1] z1] [[x2 y2] z2]. unfold peqb. split.
  - intro H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Nat.eqb_eq in H3.
    subst. reflexivity.
  - intro H. injection H as E1 E2 E3. subst. rewrite !Nat.eqb_refl. reflexivity.
Qed.

(* The six elements of S_3. *)
Definition all_perms : list perm :=
  [(0, 1, 2); (1, 2, 0); (2, 0, 1); (1, 0, 2); (0, 2, 1); (2, 1, 0)].

Lemma in_perms_b : forall p, existsb (peqb p) all_perms = true -> In p all_perms.
Proof.
  intros p H. apply (proj1 (existsb_exists _ _)) in H as [q [Hq E]].
  apply peqb_eq in E. subst. exact Hq.
Qed.

(* ===== The theta graph ===== *)

(* Edge labels: e1 (the spanning edge) = id, e2 = a, e3 = b. *)
Definition label (i : nat) : perm :=
  match i with
  | 1 => idp
  | 2 => a
  | _ => b
  end.

Lemma label_in : forall i, In (label i) all_perms.
Proof. intro i. apply in_perms_b. destruct i as [|[|[|i]]]; reflexivity. Qed.

(* A coordination is given by which of e1, e2, e3 are kept. *)
Definition kept (k1 k2 k3 : bool) : list nat :=
  (if k1 then [1] else []) ++ (if k2 then [2] else []) ++ (if k3 then [3] else []).

Definition deleted (k1 k2 k3 : bool) : nat :=
  (if k1 then 0 else 1) + (if k2 then 0 else 1) + (if k3 then 0 else 1).

(* ===== Non-abelian sections (H^0 over the S_3 torsor) ===== *)

Definition has_section (es : list nat) : Prop :=
  exists s0 s1, In s0 all_perms /\ In s1 all_perms /\
    forall e, In e es -> comp (label e) s0 = s1.

Definition sectionb (es : list nat) : bool :=
  existsb (fun s0 =>
    existsb (fun s1 =>
      forallb (fun e => peqb (comp (label e) s0) s1) es)
    all_perms)
  all_perms.

Lemma sectionb_iff : forall es, sectionb es = true <-> has_section es.
Proof.
  intro es. unfold sectionb, has_section. split.
  - intro H. apply (proj1 (existsb_exists _ _)) in H as [s0 [Hs0 H]]. cbv beta in H.
    apply (proj1 (existsb_exists _ _)) in H as [s1 [Hs1 H]]. cbv beta in H.
    generalize (proj1 (forallb_forall _ _) H); clear H; intro H.
    exists s0, s1. split; [exact Hs0 |]. split; [exact Hs1 |].
    intros e He. apply peqb_eq. apply H. exact He.
  - intros (s0 & s1 & Hs0 & Hs1 & H).
    apply (proj2 (existsb_exists _ _)). exists s0. split; [exact Hs0 |]. cbv beta.
    apply (proj2 (existsb_exists _ _)). exists s1. split; [exact Hs1 |]. cbv beta.
    apply (proj2 (forallb_forall _ _)). intros e He. apply peqb_eq. apply H. exact He.
Qed.

(* ===== Abelianized sections (sign in Z/2, acting on bool by xor) ===== *)

Definition sign (p : perm) : bool := negb (even_perm p).

(* sign is a homomorphism S_3 -> Z/2, so it is the abelianization map. Checked over all pairs. *)
Lemma sign_hom :
  forall p q, In p all_perms -> In q all_perms ->
    sign (comp p q) = xorb (sign p) (sign q).
Proof.
  assert (H : forallb (fun p => forallb (fun q =>
                Bool.eqb (sign (comp p q)) (xorb (sign p) (sign q))) all_perms) all_perms = true)
    by (vm_compute; reflexivity).
  intros p q Hp Hq.
  pose proof (proj1 (forallb_forall _ _) H p Hp) as H1. cbv beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 q Hq) as H2.
  apply Bool.eqb_prop in H2. exact H2.
Qed.

Definition has_section_ab (es : list nat) : Prop :=
  exists s0 s1 : bool, forall e, In e es -> xorb (sign (label e)) s0 = s1.

Definition sectionb_ab (es : list nat) : bool :=
  existsb (fun s0 =>
    existsb (fun s1 =>
      forallb (fun e => Bool.eqb (xorb (sign (label e)) s0) s1) es)
    [false; true])
  [false; true].

Lemma bool_in : forall x : bool, In x [false; true].
Proof. destruct x; simpl; auto. Qed.

Lemma sectionb_ab_iff : forall es, sectionb_ab es = true <-> has_section_ab es.
Proof.
  intro es. unfold sectionb_ab, has_section_ab. split.
  - intro H. apply (proj1 (existsb_exists _ _)) in H as [s0 [_ H]]. cbv beta in H.
    apply (proj1 (existsb_exists _ _)) in H as [s1 [_ H]]. cbv beta in H.
    generalize (proj1 (forallb_forall _ _) H); clear H; intro H.
    exists s0, s1. intros e He. apply Bool.eqb_prop. apply H. exact He.
  - intros (s0 & s1 & H).
    apply (proj2 (existsb_exists _ _)). exists s0. split; [apply bool_in |]. cbv beta.
    apply (proj2 (existsb_exists _ _)). exists s1. split; [apply bool_in |]. cbv beta.
    apply (proj2 (forallb_forall _ _)). intros e He. rewrite (H e He). apply Bool.eqb_reflx.
Qed.

(* ===== Functoriality: an S_3 section induces an abelian section ===== *)

Theorem section_G_implies_ab : forall es, has_section es -> has_section_ab es.
Proof.
  intros es (s0 & s1 & Hs0 & Hs1 & H).
  exists (sign s0), (sign s1). intros e He.
  rewrite <- (H e He). rewrite (sign_hom (label e) s0 (label_in e) Hs0). reflexivity.
Qed.

(* ===== min_G = 2 ===== *)

Theorem min_G_lower :
  forall k1 k2 k3, has_section (kept k1 k2 k3) -> 2 <= deleted k1 k2 k3.
Proof.
  intros k1 k2 k3 H.
  destruct k1, k2, k3; unfold deleted; simpl; try lia;
    exfalso; apply (proj2 (sectionb_iff _)) in H; vm_compute in H; discriminate H.
Qed.

Theorem min_G_attained : has_section (kept true false false) /\ deleted true false false = 2.
Proof. split; [apply (proj1 (sectionb_iff _)); vm_compute; reflexivity | reflexivity]. Qed.

(* ===== min_{G^ab} = 1 ===== *)

Theorem min_ab_lower :
  forall k1 k2 k3, has_section_ab (kept k1 k2 k3) -> 1 <= deleted k1 k2 k3.
Proof.
  intros k1 k2 k3 H.
  destruct k1, k2, k3; unfold deleted; simpl; try lia;
    exfalso; apply (proj2 (sectionb_ab_iff _)) in H; vm_compute in H; discriminate H.
Qed.

Theorem min_ab_attained : has_section_ab (kept true true false) /\ deleted true true false = 1.
Proof. split; [apply (proj1 (sectionb_ab_iff _)); vm_compute; reflexivity | reflexivity]. Qed.

(* ===== The strict separation: 1 = min_{G^ab} < min_G = 2 ===== *)

Theorem theta_separation :
  (forall k1 k2 k3, has_section (kept k1 k2 k3) -> 2 <= deleted k1 k2 k3) /\
  has_section (kept true false false) /\
  (forall k1 k2 k3, has_section_ab (kept k1 k2 k3) -> 1 <= deleted k1 k2 k3) /\
  has_section_ab (kept true true false) /\
  ~ has_section (kept true true false).
Proof.
  split; [exact min_G_lower |].
  split; [exact (proj1 min_G_attained) |].
  split; [exact min_ab_lower |].
  split; [exact (proj1 min_ab_attained) |].
  intro H. apply min_G_lower in H. unfold deleted in H. simpl in H. lia.
Qed.
