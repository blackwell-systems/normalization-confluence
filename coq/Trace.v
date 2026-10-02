(* Trace equivalence: convergence for DECLARED independent pairs.

   gsm's Build checks Compensation Commutativity only for the event pairs a
   registry declares independent (Registry.Independent), or for every pair when it
   declares none. Checker.run_perm_invariant needs EVERY pair to commute, which is
   too strong for a machine that declares pairs: its guarantee is about event
   sequences that differ only by reordering declared-independent events.

   tequiv I is that relation: the equivalence closure of swapping two ADJACENT
   events a, b with I a b (Mazurkiewicz trace equivalence). The theorem
   run_tequiv says: if every step lands in a set V, V is inside a domain D, and
   every I-pair commutes on D, then trace-equivalent sequences reach the same state
   from any start in D. When I relates every pair of events, tequiv is exactly
   Permutation (perm_tequiv_total), so run_perm_invariant is the special case.
   Axiom-free. *)

From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Section Trace.
  Context {S E : Type}.
  Variable step : E -> S -> S.

  Definition runT (es : list E) (s : S) : S :=
    fold_left (fun st e => step e st) es s.

  Lemma runT_cons : forall e es s, runT (e :: es) s = runT es (step e s).
  Proof. reflexivity. Qed.

  Lemma runT_app : forall l r s, runT (l ++ r) s = runT r (runT l s).
  Proof. intros l r s. unfold runT. apply fold_left_app. Qed.

  (* I: the declared independence relation; Ev: the events in range. *)
  Variable I : E -> E -> Prop.

  Inductive tequiv : list E -> list E -> Prop :=
  | teq_refl  : forall l, tequiv l l
  | teq_swap  : forall l a b r, I a b -> tequiv (l ++ a :: b :: r) (l ++ b :: a :: r)
  | teq_sym   : forall l1 l2, tequiv l1 l2 -> tequiv l2 l1
  | teq_trans : forall l1 l2 l3, tequiv l1 l2 -> tequiv l2 l3 -> tequiv l1 l3.

  Lemma tequiv_perm : forall l1 l2, tequiv l1 l2 -> Permutation l1 l2.
  Proof.
    intros l1 l2 H. induction H.
    - apply Permutation_refl.
    - apply Permutation_app_head. apply perm_swap.
    - apply Permutation_sym. exact IHtequiv.
    - eapply Permutation_trans; eassumption.
  Qed.

  Lemma tequiv_cons : forall x l1 l2, tequiv l1 l2 -> tequiv (x :: l1) (x :: l2).
  Proof.
    intros x l1 l2 H. induction H.
    - apply teq_refl.
    - change (x :: l ++ a :: b :: r) with ((x :: l) ++ a :: b :: r).
      change (x :: l ++ b :: a :: r) with ((x :: l) ++ b :: a :: r).
      apply teq_swap. exact H.
    - apply teq_sym. exact IHtequiv.
    - eapply teq_trans; eassumption.
  Qed.

  Variable Ev : E -> Prop.
  Variable V D : S -> Prop.

  Hypothesis V_D : forall s, V s -> D s.
  Hypothesis step_V : forall e s, Ev e -> D s -> V (step e s).
  Hypothesis step_comm : forall a b s, Ev a -> Ev b -> I a b -> D s ->
    step a (step b s) = step b (step a s).

  Lemma runT_D : forall l s, Forall Ev l -> D s -> D (runT l s).
  Proof.
    induction l as [| e l IH]; intros s Hl Hs; [exact Hs |].
    inversion Hl; subst. rewrite runT_cons. apply IH; [assumption |].
    apply V_D. apply step_V; assumption.
  Qed.

  (* Order independence up to declared-independent reordering. *)
  Theorem run_tequiv :
    forall es1 es2, tequiv es1 es2 -> Forall Ev es1 ->
    forall s, D s -> runT es1 s = runT es2 s.
  Proof.
    intros es1 es2 H. induction H as [ l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H12 IH12 H23 IH23 ];
      intros Hev s Hs.
    - reflexivity.
    - rewrite !runT_app.
      apply Forall_app in Hev. destruct Hev as [Hl Hr].
      inversion Hr as [| ? ? Ha Hr']; subst. inversion Hr' as [| ? ? Hb _]; subst.
      pose proof (runT_D l s Hl Hs) as HD.
      rewrite !runT_cons. rewrite (step_comm a b (runT l s) Ha Hb Hab HD). reflexivity.
    - symmetry. apply IH; [| exact Hs].
      apply (Permutation_Forall (tequiv_perm _ _ (teq_sym _ _ H))). exact Hev.
    - rewrite (IH12 Hev s Hs). apply IH23; [| exact Hs].
      apply (Permutation_Forall (tequiv_perm _ _ H12)). exact Hev.
  Qed.

  (* When I relates every pair of in-range events, trace equivalence is just
     Permutation: the all-pairs guarantee is the special case. *)
  Theorem perm_tequiv_total :
    (forall a b, Ev a -> Ev b -> I a b) ->
    forall es1 es2, Permutation es1 es2 -> Forall Ev es1 -> tequiv es1 es2.
  Proof.
    intros Htot es1 es2 Hp. induction Hp as [ | x l1 l2 Hp IH | x y l | l1 l2 l3 Hp1 IH1 Hp2 IH2 ];
      intros Hev.
    - apply teq_refl.
    - inversion Hev; subst. apply tequiv_cons. apply IH. assumption.
    - inversion Hev as [| ? ? Hy Hev']; subst. inversion Hev' as [| ? ? Hx _]; subst.
      apply (teq_swap [] y x l). apply Htot; assumption.
    - eapply teq_trans; [apply IH1; exact Hev |].
      apply IH2. apply (Permutation_Forall Hp1). exact Hev.
  Qed.
End Trace.
