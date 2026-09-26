(* Categorical.v: the structural core of the companion paper's federation-as-limit account,
   mechanized at the paper's level of abstraction. The normalizer is an abstract idempotent
   endomap, exactly as Governance.v treats the registry operators abstractly.

   This mechanizes:
   - Lemma 0 (a registry's valid set is the fixed-point set = the image of its idempotent
     normalizer, and that set is the equalizer of id and the normalizer), and
   - the abstract skeleton of Theorem 1 (an idempotent normalizer is a retraction onto that set:
     it lands in the set and fixes it, so it splits the inclusion of the set into the state space).

   Everything is axiom-free. The concrete instance at the end (clamp-to-cap, a genuinely
   collapsing normalizer, mirroring compensation) discharges the idempotence hypothesis with no
   hypotheses of its own, so the results are not vacuous. *)

Section IdempotentRetraction.
  Context {A : Type} (rho : A -> A).
  Hypothesis idem : forall x, rho (rho x) = rho x.

  (* The valid set two ways: fixed points of the normalizer, and its image. *)
  Definition Fixed (x : A) : Prop := rho x = x.
  Definition InImage (x : A) : Prop := exists y, rho y = x.

  (* Lemma 0, part 1: image = fixed points. The forward direction is exactly idempotence. *)
  Lemma image_iff_fixed : forall x, InImage x <-> Fixed x.
  Proof.
    intro x. split.
    - intros [y Hy]. unfold Fixed. rewrite <- Hy. apply idem.
    - intro Hx. exists x. exact Hx.
  Qed.

  (* Lemma 0, part 2: the fixed-point set is the equalizer of id and rho. In Set the equalizer of
     (id, rho) has carrier {x | id x = rho x}; that predicate is Fixed up to symmetry, so the
     fixed-point set IS the equalizer carrier (a limit). *)
  Lemma fixed_is_equalizer : forall x, Fixed x <-> (fun z => z) x = rho x.
  Proof. intro x. unfold Fixed. split; intro H; symmetry; exact H. Qed.

  (* Theorem 1 (abstract skeleton): rho is a retraction onto Fixed.
     (a) rho lands in the fixed set (idempotence); (b) rho fixes the fixed set (definitional).
     Together rho splits the inclusion Fixed -> A, i.e. it is a retraction onto its image, which
     by image_iff_fixed is the limit L = Fixed. *)
  Lemma retract_into_fixed : forall x, Fixed (rho x).
  Proof. intro x. unfold Fixed. apply idem. Qed.

  Lemma retract_fixes_fixed : forall x, Fixed x -> rho x = x.
  Proof. intros x H. exact H. Qed.

  (* Equalizer universal property, axiom-free fragment. Any fork u : Z -> A that already lands in
     Fixed factors through the inclusion, and the factoring A-map is u itself. Full uniqueness into
     the subset type {x | Fixed x} needs proof irrelevance of Fixed (available when A has decidable
     equality, e.g. gsm's finite state types); the computational content, that the mediator's
     underlying values are forced, is axiom-free and stated here. *)
  Section Universal.
    Context {Z : Type} (u : Z -> A).
    Hypothesis u_fixed : forall z, Fixed (u z).

    Lemma mediator_lands_in_fixed : forall z, Fixed (u z).
    Proof. exact u_fixed. Qed.

    Lemma mediator_values_unique :
      forall m : Z -> A,
        (forall z, m z = u z) -> forall z, rho (m z) = m z.
    Proof. intros m Hm z. rewrite Hm. apply u_fixed. Qed.
  End Universal.
End IdempotentRetraction.

(* Non-vacuity: a concrete idempotent normalizer that genuinely collapses (clamp to a cap at 3,
   the shape of a real compensation), so the section's hypothesis is satisfiable and the results
   are about something. Its fixed set is exactly {n | n <= 3}. *)
From Coq Require Import Arith.PeanoNat.

Definition clamp3 (n : nat) : nat := Nat.min n 3.

Lemma clamp3_idem : forall n, clamp3 (clamp3 n) = clamp3 n.
Proof.
  intro n. unfold clamp3.
  apply Nat.min_l. apply Nat.le_min_r.
Qed.

Lemma clamp3_fixed_iff : forall n, Fixed clamp3 n <-> n <= 3.
Proof.
  intro n. unfold Fixed, clamp3. split.
  - intro H. rewrite <- H. apply Nat.le_min_r.
  - intro H. apply Nat.min_l. exact H.
Qed.

(* The abstract retraction results instantiate at clamp3 with no remaining hypotheses: clamp3 is a
   retraction onto {n | n <= 3}. *)
Definition clamp3_retracts_into : forall n, Fixed clamp3 (clamp3 n) :=
  retract_into_fixed clamp3 clamp3_idem.

Definition clamp3_image_iff_fixed : forall x, InImage clamp3 x <-> Fixed clamp3 x :=
  image_iff_fixed clamp3 clamp3_idem.

(* --------------------------------------------------------------------------- *)
(* Proposition 1: the federated consistent set is an equalizer, hence a finite  *)
(* limit in Set. Mechanized at the paper's abstraction level: the targets are a *)
(* finite list, and a target's current shared component and its resolver value  *)
(* are abstract maps sh, res : St -> T -> Sh. The consistent set L_F is the set  *)
(* of federated states where every target's shared component equals its         *)
(* resolver value; the two parallel maps sharedOf, resolvedOf send a state to    *)
(* the tuple (modeled as a list over the targets) of shared components and of    *)
(* resolver values. L_F = eq(sharedOf, resolvedOf). Modeling the product over    *)
(* targets as a list keeps the equalizer characterization axiom-free, with no    *)
(* functional extensionality. *)

From Coq Require Import Lists.List.
Import ListNotations.

(* Pointwise agreement over a finite index list is exactly equality of the two
   list-valued maps: the equalizer of a product is the conjunction of the
   component equalizers. Both directions are structural, axiom-free. *)
Lemma pointwise_to_map {A B : Type} (f h : A -> B) (l : list A) :
  (forall x, In x l -> f x = h x) -> map f l = map h l.
Proof.
  induction l as [|a l IH]; simpl; intro H.
  - reflexivity.
  - f_equal.
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma map_to_pointwise {A B : Type} (f h : A -> B) (l : list A) :
  map f l = map h l -> forall x, In x l -> f x = h x.
Proof.
  induction l as [|a l IH]; simpl; intro Heq.
  - intros x [].
  - injection Heq as Hhd Htl. intros x Hin.
    destruct Hin as [Hx|Hx].
    + rewrite <- Hx. exact Hhd.
    + apply IH; [exact Htl | exact Hx].
Qed.

Section FederatedEqualizer.
  Context {St T Sh : Type}.
  Variable targets : list T.       (* the federation's targets (finite) *)
  Variable sh  : St -> T -> Sh.    (* a target's current shared component *)
  Variable res : St -> T -> Sh.    (* the resolver value from that target's sources *)

  (* The two parallel maps into the product over targets (modeled as a list). *)
  Definition sharedOf   (s : St) : list Sh := map (sh s) targets.
  Definition resolvedOf (s : St) : list Sh := map (res s) targets.

  (* L_F: every target's shared component already equals its resolver value. *)
  Definition Consistent (s : St) : Prop :=
    forall B, In B targets -> sh s B = res s B.

  (* The equalizer of the two maps. *)
  Definition Equalizer (s : St) : Prop := sharedOf s = resolvedOf s.

  (* Proposition 1: the consistent set is exactly the equalizer, so the federated
     normal forms are a finite limit in Set (an equalizer of a product, each factor
     itself the equalizer of Lemma 0). *)
  Theorem consistent_iff_equalizer : forall s, Consistent s <-> Equalizer s.
  Proof.
    intro s. unfold Consistent, Equalizer, sharedOf, resolvedOf. split.
    - apply pointwise_to_map.
    - apply map_to_pointwise.
  Qed.
End FederatedEqualizer.

(* Non-vacuity: a two-target instance where consistency is a genuine constraint
   (the state must be 0), so Proposition 1 is not about an empty or trivial
   equalizer. *)
Example ex_consistent_zero :
  Consistent (true :: false :: nil) (fun (s : nat) (_ : bool) => s) (fun _ _ => 0) 0.
Proof. intros B _. reflexivity. Qed.

Example ex_inconsistent_one :
  ~ Consistent (true :: false :: nil) (fun (s : nat) (_ : bool) => s) (fun _ _ => 0) 1.
Proof. intro H. specialize (H true (or_introl eq_refl)). discriminate H. Qed.

(* --------------------------------------------------------------------------- *)
(* Theorem 1 (federation retraction), the operator half. The Corollary of the   *)
(* note: any operator that is SOUND (its image lands in a consistent set L) and  *)
(* COMPLETE (it fixes L) is the idempotent retraction onto L, with image and     *)
(* fixed-point set both equal to L. The federated normalizer rho_F is an         *)
(* instance once Lemma A (soundness) and Lemma B (completeness) are discharged   *)
(* for it, which is done concretely below. *)

Section RetractionOntoConsistent.
  Context {A : Type} (rho : A -> A) (L : A -> Prop).
  Hypothesis sound    : forall s, L (rho s).           (* Lemma A: im rho subset L *)
  Hypothesis complete : forall s, L s -> rho s = s.    (* Lemma B: L subset Fix rho *)

  Theorem rhoL_idempotent : forall s, rho (rho s) = rho s.
  Proof. intro s. apply complete. apply sound. Qed.

  Theorem rhoL_image_iff_L : forall x, (exists y, rho y = x) <-> L x.
  Proof.
    intro x. split.
    - intros [y Hy]. rewrite <- Hy. apply sound.
    - intro Hx. exists x. apply complete. exact Hx.
  Qed.

  Theorem rhoL_L_iff_fixed : forall x, L x <-> rho x = x.
  Proof.
    intro x. split.
    - apply complete.
    - intro H. rewrite <- H. apply sound.
  Qed.
End RetractionOntoConsistent.

(* A concrete federated operator: a root A with local normalizer normA and a target B whose shared
   component is fixed by a morphism phi from A's normal form. M1 is modeled by taking the morphism
   image to be B-normal, so B's local normalizer is the identity on it (no separate normB needed).
   rho_F normalizes A, then sets B to phi of A's normal form. It discharges Lemma A and Lemma B and
   so instantiates the retraction Corollary: rho_F is the idempotent retraction onto its consistent
   set L2. *)
Section FederatedOperator.
  Context {V : Type}.
  Variable normA : V -> V.
  Hypothesis normA_idem : forall a, normA (normA a) = normA a.
  Variable phi : V -> V.

  Definition rhoF (p : V * V) : V * V :=
    let a' := normA (fst p) in (a', phi a').

  Definition L2 (p : V * V) : Prop :=
    normA (fst p) = fst p /\ snd p = phi (fst p).

  Lemma rhoF_sound : forall p, L2 (rhoF p).
  Proof. intro p. unfold L2, rhoF. simpl. split; [apply normA_idem | reflexivity]. Qed.

  Lemma rhoF_complete : forall p, L2 p -> rhoF p = p.
  Proof.
    intros [a b] H. unfold L2 in H. simpl in H. destruct H as [Ha Hb].
    unfold rhoF. simpl. rewrite Ha. rewrite <- Hb. reflexivity.
  Qed.

  Theorem rhoF_retraction : forall p, rhoF (rhoF p) = rhoF p.
  Proof. exact (rhoL_idempotent rhoF L2 rhoF_sound rhoF_complete). Qed.

  Theorem rhoF_image_iff_L2 : forall p, (exists q, rhoF q = p) <-> L2 p.
  Proof. exact (rhoL_image_iff_L rhoF L2 rhoF_sound rhoF_complete). Qed.
End FederatedOperator.

(* Order-independence, commutation core (the local step of Lemma C): updates to two independent
   registry components commute. Two incomparable registries have disjoint reads and writes, so
   processing them in either order gives the same result. The full result, that ALL topological
   orders agree, additionally uses the classical fact that linear extensions of a finite poset are
   connected by adjacent transpositions of incomparable elements; that connectivity is not
   mechanized here, so order-independence over general DAGs remains paper-level. *)
Definition updL {A B : Type} (fa : A -> A) (p : A * B) : A * B := (fa (fst p), snd p).
Definition updR {A B : Type} (fb : B -> B) (p : A * B) : A * B := (fst p, fb (snd p)).

Lemma updates_commute {A B : Type} (fa : A -> A) (fb : B -> B) (p : A * B) :
  updL fa (updR fb p) = updR fb (updL fa p).
Proof. destruct p as [a b]. reflexivity. Qed.

(* --------------------------------------------------------------------------- *)
(* Theorem 1 for a GENERAL acyclic federation: rho_F as a left-to-right fold     *)
(* over a topological order. The federated state is a positional list (position  *)
(* i is registry i, with sources before targets). Processing position i replaces *)
(* its value with stepAt applied to the already-finalized prefix and the current *)
(* value; stepAt models "read finalized sources, overwrite shared component,      *)
(* apply local normalizer". rho_F is the idempotent retraction onto the           *)
(* consistent set L_F: every position is already fixed by its step given its      *)
(* prefix. Soundness (Lemma A) needs stepAt idempotent given a fixed prefix (the  *)
(* local M1 + idempotence content); completeness (Lemma B) needs only the         *)
(* definition of L_F. This upgrades the two-registry instance above to every      *)
(* acyclic federation. *)

(* Splitting a snoc: l ++ [y] = p ++ z :: sfx puts the split either inside l or at
   the appended element y. A structural fact, axiom-free, needed for soundness. *)
Lemma app_split_snoc {A : Type} :
  forall (l : list A) (y : A) (p : list A) (z : A) (sfx : list A),
    l ++ (y :: nil) = p ++ z :: sfx ->
    (exists sfx', l = p ++ z :: sfx' /\ sfx = sfx' ++ (y :: nil)) \/
    (p = l /\ z = y /\ sfx = nil).
Proof.
  intros l y p. revert l. induction p as [|b p' IHp]; intros l z sfx H; simpl in H.
  - destruct l as [|a l']; simpl in H.
    + injection H as Hz Hs. right. split; [reflexivity | split; [symmetry; exact Hz | symmetry; exact Hs]].
    + injection H as Ha Hrest. left. exists l'. split.
      * rewrite Ha. reflexivity.
      * symmetry; exact Hrest.
  - destruct l as [|a l']; simpl in H.
    + injection H as Hb Hnil. exfalso. exact (app_cons_not_nil p' sfx z Hnil).
    + injection H as Hab Hrest. specialize (IHp l' z sfx Hrest).
      destruct IHp as [[sfx' [Hl' Hsfx]] | [Hp' [Hz Hsfx]]].
      * left. exists sfx'. split; [rewrite Hab, Hl'; reflexivity | exact Hsfx].
      * right. split; [rewrite Hab, Hp'; reflexivity | split; [exact Hz | exact Hsfx]].
Qed.

Section GeneralFederatedFold.
  Context {V : Type}.
  Variable stepAt : list V -> V -> V.   (* finalized prefix -> current value -> finalized value *)

  Fixpoint rhoF_from (done todo : list V) : list V :=
    match todo with
    | nil => done
    | x :: rest => rhoF_from (done ++ (stepAt done x :: nil)) rest
    end.

  Definition rhoFold (s : list V) : list V := rhoF_from nil s.

  (* L_F: every position is a fixed point of its step given its prefix. *)
  Definition ConsistentList (l : list V) : Prop :=
    forall p x sfx, l = p ++ x :: sfx -> stepAt p x = x.

  (* Lemma B (completeness): a consistent state is fixed. Uses only the definition. *)
  Lemma rhoFold_complete_gen :
    forall todo done, ConsistentList (done ++ todo) -> rhoF_from done todo = done ++ todo.
  Proof.
    induction todo as [|x rest IH]; intros done H; simpl.
    - rewrite app_nil_r. reflexivity.
    - assert (Hx : stepAt done x = x) by (apply (H done x rest); reflexivity).
      rewrite Hx.
      assert (Hcons : ConsistentList ((done ++ x :: nil) ++ rest)).
      { rewrite <- app_assoc. simpl. exact H. }
      rewrite (IH (done ++ x :: nil) Hcons).
      rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma rhoFold_complete : forall s, ConsistentList s -> rhoFold s = s.
  Proof.
    intros s H. unfold rhoFold. apply (rhoFold_complete_gen s nil). simpl. exact H.
  Qed.

  Hypothesis stepAt_idem : forall p x, stepAt p (stepAt p x) = stepAt p x.

  (* Extending a consistent finalized prefix by one processed element stays consistent. *)
  Lemma consistent_snoc :
    forall done x, ConsistentList done -> ConsistentList (done ++ (stepAt done x :: nil)).
  Proof.
    intros done x Hdone p z sfx Hsplit.
    apply app_split_snoc in Hsplit.
    destruct Hsplit as [[sfx' [Hdone_eq Hsfx]] | [Hp [Hz Hsfx]]].
    - apply (Hdone p z sfx'). exact Hdone_eq.
    - rewrite Hp, Hz. apply stepAt_idem.
  Qed.

  Lemma rhoF_from_consistent :
    forall todo done, ConsistentList done -> ConsistentList (rhoF_from done todo).
  Proof.
    induction todo as [|x rest IH]; intros done Hdone; simpl.
    - exact Hdone.
    - apply IH. apply consistent_snoc. exact Hdone.
  Qed.

  (* Lemma A (soundness): rho_F lands in the consistent set. *)
  Lemma rhoFold_sound : forall s, ConsistentList (rhoFold s).
  Proof.
    intro s. unfold rhoFold. apply rhoF_from_consistent.
    intros p x sfx H. destruct p; simpl in H; discriminate H.
  Qed.

  (* Theorem 1 for the general acyclic operator: rho_F is the idempotent retraction
     onto its consistent set, with image and fixed set both L_F. *)
  Theorem rhoFold_retraction : forall s, rhoFold (rhoFold s) = rhoFold s.
  Proof. exact (rhoL_idempotent rhoFold ConsistentList rhoFold_sound rhoFold_complete). Qed.

  Theorem rhoFold_image_iff_consistent :
    forall x, (exists y, rhoFold y = x) <-> ConsistentList x.
  Proof. exact (rhoL_image_iff_L rhoFold ConsistentList rhoFold_sound rhoFold_complete). Qed.
End GeneralFederatedFold.

(* Non-vacuity: a concrete fold (each position reset to 0, a genuinely collapsing step) computes,
   and its consistent set is the all-zero states. *)
Example ex_rhoFold_zeros :
  rhoFold (fun (_ : list nat) (_ : nat) => 0) (1 :: 2 :: nil) = 0 :: 0 :: nil.
Proof. reflexivity. Qed.

(* --------------------------------------------------------------------------- *)
(* Theorem 2 (compositionality), operator level. The flat normalization of a     *)
(* federation split along a topological cut J ++ K equals the staged one:         *)
(* finalize the upstream block J, then continue with K on top of that finalized   *)
(* block. So an upstream sub-federation collapses to its finalized block and the   *)
(* combined normalizer factors as (normalize J) then (normalize K). This is the    *)
(* fold-append law for rho_F, axiom-free. *)

Section Compositionality.
  Context {V : Type}.
  Variable stepAt : list V -> V -> V.

  Lemma rhoF_from_app :
    forall js ks done,
      rhoF_from stepAt done (js ++ ks) =
      rhoF_from stepAt (rhoF_from stepAt done js) ks.
  Proof.
    induction js as [|x js' IH]; intros ks done; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  (* Theorem 2: normalizing the whole federation equals normalizing the upstream
     block J, then federating K on top of the collapsed (finalized) J. *)
  Theorem rhoFold_compositional :
    forall js ks,
      rhoFold stepAt (js ++ ks) = rhoF_from stepAt (rhoFold stepAt js) ks.
  Proof. intros js ks. unfold rhoFold. apply rhoF_from_app. Qed.
End Compositionality.

(* Non-vacuity: the flat and staged computations agree and both compute. *)
Example ex_compositional_zeros :
  rhoFold (fun (_ : list nat) (_ : nat) => 0) ((1 :: 2 :: nil) ++ (3 :: nil)) =
  rhoF_from (fun (_ : list nat) (_ : nat) => 0)
            (rhoFold (fun (_ : list nat) (_ : nat) => 0) (1 :: 2 :: nil)) (3 :: nil).
Proof. reflexivity. Qed.
