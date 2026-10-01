(* FederationOrder.v: the federated normalizer is independent of the topological order, mechanized
   axiom-free for ARBITRARY acyclic federations.

   Categorical.v mechanizes the local step of this result (updates_commute: two independent
   registries commute) and leaves the full statement at the paper level, because the paper's proof
   lifts the local step to all topological orders through the classical fact that linear extensions
   of a finite poset are connected by adjacent transpositions of incomparable elements. This file
   proves the full statement without assuming that fact.

   Model. Registries are indexed by nat. A state assigns each registry its current value. Registry i
   has a source list src i and a step f i that reads the state only through its sources (f_local)
   and the registry's own current value. Processing i overwrites i's value with f i applied to the
   current state; running an order processes registries left to right. An order is topological
   when it has no duplicates and every source of a registry that occurs in the order occurs earlier.

   Theorem (order_independent). Any two topological orders of the same registries produce the same
   final state, from any initial state.

   Proof idea. Induct on the first registry a of one order. In the other order, every registry
   placed before a is independent of a: a cannot read it (a is first in a topological order, so it
   has no in-order sources) and it cannot read a (it precedes a in a topological order). So a can
   be bubbled to the front by adjacent commutations, and the tails are again topological orders of
   the same registries. States are compared pointwise, so no functional extensionality is used. *)

From Coq Require Import List Arith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Section Order.
  Context {V : Type}.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.

  (* A registry's step reads the state only through its sources. *)
  Hypothesis f_local :
    forall i s1 s2 x, (forall k, In k (src i) -> s1 k = s2 k) -> f i s1 x = f i s2 x.

  Definition upd (s : nat -> V) (w : nat) (x : V) : nat -> V :=
    fun z => if Nat.eq_dec z w then x else s z.

  Definition step (s : nat -> V) (i : nat) : nat -> V := upd s i (f i s (s i)).

  Definition run (o : list nat) (s : nat -> V) : nat -> V := fold_left step o s.

  Definition seq (s t : nat -> V) : Prop := forall k, s k = t k.

  Lemma run_cons : forall i o s, run (i :: o) s = run o (step s i).
  Proof. reflexivity. Qed.

  Lemma step_other : forall s i k, k <> i -> step s i k = s k.
  Proof. intros s i k H. unfold step, upd. destruct (Nat.eq_dec k i); [contradiction | reflexivity]. Qed.

  Lemma step_self : forall s i, step s i i = f i s (s i).
  Proof. intros s i. unfold step, upd. destruct (Nat.eq_dec i i); [reflexivity | contradiction]. Qed.

  Lemma step_ext : forall s t i, seq s t -> seq (step s i) (step t i).
  Proof.
    intros s t i H k. unfold step, upd. destruct (Nat.eq_dec k i) as [-> | _]; [| apply H].
    rewrite (H i). apply f_local. intros k _. apply H.
  Qed.

  Lemma run_ext : forall o s t, seq s t -> seq (run o s) (run o t).
  Proof.
    induction o as [| i o IH]; intros s t H; [exact H |].
    rewrite !run_cons. apply IH. apply step_ext. exact H.
  Qed.

  (* Processing i does not change what j reads, when i is not a source of j. *)
  Lemma f_after : forall s i j x, ~ In i (src j) -> f j (step s i) x = f j s x.
  Proof.
    intros s i j x H. apply f_local. intros k Hk. apply step_other.
    intro E. subst. contradiction.
  Qed.

  (* Two independent registries commute. *)
  Lemma step_comm :
    forall s i j, i <> j -> ~ In i (src j) -> ~ In j (src i) ->
      seq (step (step s i) j) (step (step s j) i).
  Proof.
    intros s i j Hij Hi Hj k.
    assert (Hji : j <> i) by (intro E; apply Hij; symmetry; exact E).
    destruct (Nat.eq_dec k j) as [-> | Hkj].
    - rewrite step_self, (step_other s i j Hji), (f_after s i j (s j) Hi).
      rewrite (step_other (step s j) i j Hji), step_self. reflexivity.
    - destruct (Nat.eq_dec k i) as [-> | Hki].
      + rewrite (step_other (step s i) j i Hij), step_self.
        rewrite step_self, (step_other s j i Hij), (f_after s j i (s i) Hj). reflexivity.
      + rewrite (step_other _ j k Hkj), (step_other _ i k Hki).
        rewrite (step_other _ i k Hki), (step_other _ j k Hkj). reflexivity.
  Qed.

  (* ----- topological orders ----- *)

  (* prec k i o: k occurs strictly before i in o. *)
  Fixpoint prec (k i : nat) (o : list nat) : Prop :=
    match o with
    | [] => False
    | x :: t => (x = k /\ In i t) \/ prec k i t
    end.

  Definition topo (o : list nat) : Prop :=
    NoDup o /\ forall i k, In i o -> In k (src i) -> In k o -> prec k i o.

  Lemma prec_in_r : forall k i o, prec k i o -> In i o.
  Proof.
    induction o as [| x t IH]; simpl; [contradiction |].
    intros [[_ H] | H]; right; [exact H | apply IH; exact H].
  Qed.

  Lemma prec_tail : forall a t k i, k <> a -> prec k i (a :: t) -> prec k i t.
  Proof. intros a t k i Hk H. simpl in H. destruct H as [[E _] | H]; [congruence | exact H]. Qed.

  Lemma prec_remove :
    forall l a r k i, k <> a -> i <> a -> prec k i (l ++ a :: r) -> prec k i (l ++ r).
  Proof.
    induction l as [| x l IH]; intros a r k i Hk Hi H; simpl in *.
    - destruct H as [[E _] | H]; [congruence | exact H].
    - destruct H as [[E Hin] | H].
      + left. split; [exact E |]. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [Hin | [Hin | Hin]]; [left; exact Hin | congruence | right; exact Hin].
      + right. exact (IH a r k i Hk Hi H).
  Qed.

  (* In a duplicate-free order, a cannot precede something placed before it. *)
  Lemma prec_before_contra :
    forall l a r b, NoDup (l ++ a :: r) -> In b l -> prec a b (l ++ a :: r) -> False.
  Proof.
    induction l as [| x l IH]; intros a r b Hnd Hb H; [destruct Hb |].
    simpl in Hnd, H. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hx Hnd'].
    destruct H as [[E _] | H].
    - subst x. apply Hx. apply in_or_app. right. left. reflexivity.
    - destruct Hb as [E | Hb].
      + subst x. apply Hx. exact (prec_in_r _ _ _ H).
      + exact (IH a r b Hnd' Hb H).
  Qed.

  Lemma in_insert : forall (l r : list nat) a x, In x (l ++ r) -> In x (l ++ a :: r).
  Proof.
    intros l r a x H. apply in_app_or in H. apply in_or_app.
    destruct H as [H | H]; [left; exact H | right; right; exact H].
  Qed.

  (* ----- bubbling one registry to the front ----- *)

  Lemma bubble :
    forall l a r s,
      (forall b, In b l -> b <> a /\ ~ In a (src b) /\ ~ In b (src a)) ->
      seq (run (l ++ a :: r) s) (run (a :: l ++ r) s).
  Proof.
    induction l as [| b l IH]; intros a r s H.
    - intro k. reflexivity.
    - destruct (H b (or_introl eq_refl)) as [Hba [Hab Hb]].
      change (seq (run (b :: (l ++ a :: r)) s) (run (a :: b :: (l ++ r)) s)).
      rewrite !run_cons. intro k.
      transitivity (run (a :: l ++ r) (step s b) k).
      + apply (IH a r (step s b)). intros b' Hb'. apply H. right. exact Hb'.
      + rewrite run_cons. apply run_ext. exact (step_comm s b a Hba Hb Hab).
  Qed.

  (* ----- the theorem ----- *)

  Theorem order_independent :
    forall o1 o2 s, topo o1 -> topo o2 -> Permutation o1 o2 -> seq (run o1 s) (run o2 s).
  Proof.
    induction o1 as [| a o1 IH]; intros o2 s [Hnd1 Ht1] [Hnd2 Ht2] HP.
    - apply Permutation_nil in HP. subst. intro k. reflexivity.
    - assert (Ha2 : In a o2) by (apply (Permutation_in a HP); left; reflexivity).
      apply in_split in Ha2. destruct Ha2 as [l [r E]]. subst o2.
      assert (Hnd1' := Hnd1). apply NoDup_cons_iff in Hnd1'. destruct Hnd1' as [Ha1 Hnd1t].
      assert (Har : ~ In a (l ++ r)) by (apply NoDup_remove_2; exact Hnd2).
      (* every registry before a in o2 is independent of a *)
      assert (Hbub : forall b, In b l -> b <> a /\ ~ In a (src b) /\ ~ In b (src a)).
      { intros b Hb.
        assert (Hbo1 : In b (a :: o1)).
        { apply (Permutation_in b (Permutation_sym HP)). apply in_or_app. left. exact Hb. }
        split; [| split].
        - intro Eb. subst b. apply Har. apply in_or_app. left. exact Hb.
        - intro Hsrc. apply (prec_before_contra l a r b Hnd2 Hb).
          apply Ht2; [apply in_or_app; left; exact Hb | exact Hsrc |
                      apply in_or_app; right; left; reflexivity].
        - intro Hsrc. pose proof (Ht1 a b (or_introl eq_refl) Hsrc Hbo1) as Hp.
          simpl in Hp. destruct Hp as [[Eab Hin] | Hp].
          + apply Ha1. exact Hin.
          + apply Ha1. exact (prec_in_r _ _ _ Hp). }
      (* the tails are topological orders of the same registries *)
      assert (Hto1 : topo o1).
      { split; [exact Hnd1t |]. intros i k Hi Hk Hko.
        apply (prec_tail a); [intro Ek; subst k; contradiction |].
        apply Ht1; [right; exact Hi | exact Hk | right; exact Hko]. }
      assert (Hto2 : topo (l ++ r)).
      { split; [exact (NoDup_remove_1 l r a Hnd2) |]. intros i k Hi Hk Hko.
        apply (prec_remove l a r k i).
        - intro Ek. subst k. contradiction.
        - intro Ei. subst i. contradiction.
        - apply Ht2; [apply in_insert; exact Hi | exact Hk | apply in_insert; exact Hko]. }
      assert (HP' : Permutation o1 (l ++ r)) by (exact (Permutation_cons_app_inv _ _ HP)).
      intro k.
      transitivity (run (a :: l ++ r) s k).
      + rewrite !run_cons. exact (IH (l ++ r) (step s a) Hto1 Hto2 HP' k).
      + symmetry. exact (bubble l a r s Hbub k).
  Qed.
End Order.

(* ============================================================
   Non-vacuity: three registries, where registry 2 reads registries 0 and 1. Both [0; 1; 2] and
   [1; 0; 2] are topological orders, every hypothesis is discharged, and the theorem says they
   agree; the instance also computes the common result. Axiom-free.
   ============================================================ *)

Definition ex_src (i : nat) : list nat := match i with 2 => [0; 1] | _ => [] end.

Definition ex_f (i : nat) (s : nat -> nat) (x : nat) : nat :=
  match i with 0 => 5 | 1 => 7 | 2 => s 0 + s 1 | _ => x end.

Lemma ex_f_local :
  forall i s1 s2 x, (forall k, In k (ex_src i) -> s1 k = s2 k) -> ex_f i s1 x = ex_f i s2 x.
Proof.
  intros i s1 s2 x H. destruct i as [| [| [| i]]]; simpl; try reflexivity.
  rewrite (H 0 (or_introl eq_refl)), (H 1 (or_intror (or_introl eq_refl))). reflexivity.
Qed.

Lemma ex_topo_012 : topo ex_src [0; 1; 2].
Proof.
  split.
  - repeat constructor; simpl; intuition congruence.
  - intros i k Hi Hk Hko. simpl in Hi.
    destruct Hi as [<- | [<- | [<- | []]]]; simpl in Hk; try contradiction.
    destruct Hk as [<- | [<- | []]]; simpl; intuition.
Qed.

Lemma ex_topo_102 : topo ex_src [1; 0; 2].
Proof.
  split.
  - repeat constructor; simpl; intuition congruence.
  - intros i k Hi Hk Hko. simpl in Hi.
    destruct Hi as [<- | [<- | [<- | []]]]; simpl in Hk; try contradiction.
    destruct Hk as [<- | [<- | []]]; simpl; intuition.
Qed.

Example ex_orders_agree :
  forall k, run ex_f [0; 1; 2] (fun _ => 0) k = run ex_f [1; 0; 2] (fun _ => 0) k.
Proof.
  exact (order_independent ex_src ex_f ex_f_local [0; 1; 2] [1; 0; 2] (fun _ => 0)
           ex_topo_012 ex_topo_102 (perm_swap 1 0 [2])).
Qed.

Example ex_result : run ex_f [1; 0; 2] (fun _ => 0) 2 = 12.
Proof. reflexivity. Qed.
