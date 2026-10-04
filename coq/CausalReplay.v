(* CausalReplay.v: normalization confluence under CAUSAL delivery, mechanized axiom-free.

   The base theorem (Governance.v) and the CRDT development (CRDT.v) require compensation
   commutativity for EVERY pair of events, so every replay order must agree. Real replicated
   systems only promise causal delivery: an event is applied after the events it depends on, and
   only CONCURRENT events (neither happened before the other) may arrive in either order. This file
   proves convergence under that weaker requirement and uses it to settle the exact relationship
   with op-based CRDTs as the literature defines them.

   Setting. A governed step applies an event and normalizes (this is what gsm runs: a step table
   entry is "apply, then repair to validity"). Events carry a happens-before relation hb. Two
   events are concurrent when they are distinct and neither happens before the other. A delivery
   order respects causality when it has no duplicates and every hb-earlier event in it comes first.

   Results.
   - causal_convergence: if governed steps commute for every CONCURRENT pair, any two causally
     consistent orders of the same events reach the same state. Causally ordered pairs never need
     to commute.
   - causal_cmrdt_SEC: standard op-based CRDTs (concurrent operations commute, causal delivery)
     converge, as an instance.
   - compensation_free_exact: for a compensation-free system (normalization is the identity), the
     causal convergence condition holds IFF the system is a causal op-based CRDT. With the
     embedding, this makes the compensation-free fragment EXACTLY the op-based CRDTs.
   - witness_causal_not_cmrdt: a governed system that converges causally but is not a CRDT
     (strictness).
   - witness_beyond_all_pairs: a system whose operations do NOT all commute, which the all-pairs
     theorem cannot cover, but which converges under causal delivery (the new reach).

   - causal_tequiv: any two causally consistent orders of the same events are trace-equivalent
     under concurrency, which connects causal delivery to Trace.v's run_tequiv (the theorem behind
     gsm's declared Independent pairs).

   The ordering argument bubbles the first event of one order to the front of the other, the same
   technique as FederationOrder.v, so the connectivity of linear extensions is never assumed. *)

From Coq Require Import List Arith.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace.
Import ListNotations.

(* ----- orders and causality, generic in the event type ----- *)

Section Orders.
  Context {E : Type}.

  (* prec k i o: k occurs strictly before i in o. *)
  Fixpoint prec (k i : E) (o : list E) : Prop :=
    match o with
    | [] => False
    | x :: t => (x = k /\ In i t) \/ prec k i t
    end.

  Lemma prec_in_r : forall k i o, prec k i o -> In i o.
  Proof.
    induction o as [| x t IH]; simpl; [contradiction |].
    intros [[_ H] | H]; right; [exact H | apply IH; exact H].
  Qed.

  Lemma prec_tail : forall a t k i, k <> a -> prec k i (a :: t) -> prec k i t.
  Proof. intros a t k i Hk H. simpl in H. destruct H as [[Ea _] | H]; [congruence | exact H]. Qed.

  Lemma prec_remove :
    forall l a r k i, k <> a -> i <> a -> prec k i (l ++ a :: r) -> prec k i (l ++ r).
  Proof.
    induction l as [| x l IH]; intros a r k i Hk Hi H; simpl in *.
    - destruct H as [[Ea _] | H]; [congruence | exact H].
    - destruct H as [[Ex Hin] | H].
      + left. split; [exact Ex |]. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [Hin | [Hin | Hin]]; [left; exact Hin | congruence | right; exact Hin].
      + right. exact (IH a r k i Hk Hi H).
  Qed.

  Lemma prec_before_contra :
    forall l a r b, NoDup (l ++ a :: r) -> In b l -> prec a b (l ++ a :: r) -> False.
  Proof.
    induction l as [| x l IH]; intros a r b Hnd Hb H; [destruct Hb |].
    simpl in Hnd, H. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hx Hnd'].
    destruct H as [[Ex _] | H].
    - subst x. apply Hx. apply in_or_app. right. left. reflexivity.
    - destruct Hb as [Ex | Hb].
      + subst x. apply Hx. exact (prec_in_r _ _ _ H).
      + exact (IH a r b Hnd' Hb H).
  Qed.

  Lemma in_insert : forall (l r : list E) a x, In x (l ++ r) -> In x (l ++ a :: r).
  Proof.
    intros l r a x H. apply in_app_or in H. apply in_or_app.
    destruct H as [H | H]; [left; exact H | right; right; exact H].
  Qed.

  Variable hb : E -> E -> Prop.   (* happens-before *)

  Definition concurrent (a b : E) : Prop := a <> b /\ ~ hb a b /\ ~ hb b a.

  Lemma concurrent_sym : forall a b, concurrent a b -> concurrent b a.
  Proof. intros a b [Hne [H1 H2]]. split; [intro E1; apply Hne; symmetry; exact E1 | split; assumption]. Qed.

  (* A causally consistent delivery order: no duplicates, and causes come before effects. *)
  Definition causal (o : list E) : Prop :=
    NoDup o /\ forall a b, hb a b -> In a o -> In b o -> prec a b o.

  (* ----- bridge to Trace.v: causal delivery yields trace-equivalent sequences ----- *)

  (* An event can be swapped to the front past events concurrent with it. *)
  Lemma tequiv_bubble :
    forall l a r, (forall b, In b l -> concurrent b a) ->
      tequiv concurrent (l ++ a :: r) (a :: l ++ r).
  Proof.
    induction l as [| b l IH]; intros a r H; simpl; [apply teq_refl |].
    apply teq_trans with (l2 := b :: a :: l ++ r).
    - apply tequiv_cons. apply IH. intros b' Hb'. apply H. right. exact Hb'.
    - apply (teq_swap concurrent [] b a (l ++ r)). apply H. left. reflexivity.
  Qed.

  (* Any two causally consistent orders of the same events are trace-equivalent, where the
     independence relation is concurrency. This is the step Trace.v leaves to the caller: with it,
     Trace.run_tequiv applies to every pair of replicas that deliver causally. Proved by bubbling,
     so the connectivity of linear extensions is never assumed. *)
  Theorem causal_tequiv :
    forall o1 o2, causal o1 -> causal o2 -> Permutation o1 o2 -> tequiv concurrent o1 o2.
  Proof.
    induction o1 as [| a o1 IH]; intros o2 [Hnd1 Hc1] [Hnd2 Hc2] HP.
    - apply Permutation_nil in HP. subst. apply teq_refl.
    - assert (Ha2 : In a o2) by (apply (Permutation_in a HP); left; reflexivity).
      apply in_split in Ha2. destruct Ha2 as [l [r E2]]. subst o2.
      assert (Hnd1' := Hnd1). apply NoDup_cons_iff in Hnd1'. destruct Hnd1' as [Ha1 Hnd1t].
      assert (Har : ~ In a (l ++ r)) by (apply NoDup_remove_2; exact Hnd2).
      assert (Hbub : forall b, In b l -> concurrent b a).
      { intros b Hb.
        assert (Hbo1 : In b (a :: o1)).
        { apply (Permutation_in b (Permutation_sym HP)). apply in_or_app. left. exact Hb. }
        split; [| split].
        - intro Eb. subst b. apply Har. apply in_or_app. left. exact Hb.
        - intro Hba. pose proof (Hc1 b a Hba Hbo1 (or_introl eq_refl)) as Hp.
          simpl in Hp. destruct Hp as [[Eab Hin] | Hp].
          + apply Ha1. exact Hin.
          + apply Ha1. exact (prec_in_r _ _ _ Hp).
        - intro Hab. apply (prec_before_contra l a r b Hnd2 Hb).
          apply Hc2; [exact Hab | apply in_or_app; right; left; reflexivity |
                      apply in_or_app; left; exact Hb]. }
      assert (Hco1 : causal o1).
      { split; [exact Hnd1t |]. intros x y Hxy Hx Hy.
        apply (prec_tail a); [intro Ex; subst x; contradiction |].
        apply Hc1; [exact Hxy | right; exact Hx | right; exact Hy]. }
      assert (Hco2 : causal (l ++ r)).
      { split; [exact (NoDup_remove_1 l r a Hnd2) |]. intros x y Hxy Hx Hy.
        apply (prec_remove l a r x y).
        - intro Ex. subst x. contradiction.
        - intro Ey. subst y. contradiction.
        - apply Hc2; [exact Hxy | apply in_insert; exact Hx | apply in_insert; exact Hy]. }
      assert (HP' : Permutation o1 (l ++ r)) by (exact (Permutation_cons_app_inv _ _ HP)).
      apply teq_trans with (l2 := a :: l ++ r).
      + apply tequiv_cons. exact (IH (l ++ r) Hco1 Hco2 HP').
      + apply teq_sym. exact (tequiv_bubble l a r Hbub).
  Qed.
End Orders.

Arguments concurrent {E} hb a b.
Arguments causal {E} hb o.

(* ----- convergence under causal delivery ----- *)

Section CausalConvergence.
  Context {S E : Type}.
  Variable step : E -> S -> S.          (* governed step: apply, then normalize *)
  Variable hb : E -> E -> Prop.

  (* Compensation commutativity, required ONLY for concurrent pairs. *)
  Hypothesis cc_concurrent :
    forall a b s, concurrent hb a b -> step a (step b s) = step b (step a s).

  Definition run (es : list E) (s : S) : S := fold_left (fun st e => step e st) es s.

  Lemma run_cons : forall e es s, run (e :: es) s = run es (step e s).
  Proof. reflexivity. Qed.

  (* Bubble an event to the front past events concurrent with it. *)
  Lemma bubble :
    forall l a r s, (forall b, In b l -> concurrent hb b a) ->
      run (l ++ a :: r) s = run (a :: l ++ r) s.
  Proof.
    induction l as [| b l IH]; intros a r s H; [reflexivity |].
    change (run (b :: (l ++ a :: r)) s = run (a :: b :: (l ++ r)) s).
    rewrite !run_cons.
    rewrite (IH a r (step b s) (fun b' Hb' => H b' (or_intror Hb'))), run_cons.
    rewrite (cc_concurrent a b s (concurrent_sym hb b a (H b (or_introl eq_refl)))).
    reflexivity.
  Qed.

  Theorem causal_convergence :
    forall o1 o2 s, causal hb o1 -> causal hb o2 -> Permutation o1 o2 -> run o1 s = run o2 s.
  Proof.
    induction o1 as [| a o1 IH]; intros o2 s [Hnd1 Hc1] [Hnd2 Hc2] HP.
    - apply Permutation_nil in HP. subst. reflexivity.
    - assert (Ha2 : In a o2) by (apply (Permutation_in a HP); left; reflexivity).
      apply in_split in Ha2. destruct Ha2 as [l [r E2]]. subst o2.
      assert (Hnd1' := Hnd1). apply NoDup_cons_iff in Hnd1'. destruct Hnd1' as [Ha1 Hnd1t].
      assert (Har : ~ In a (l ++ r)) by (apply NoDup_remove_2; exact Hnd2).
      (* every event delivered before a in o2 is concurrent with a *)
      assert (Hbub : forall b, In b l -> concurrent hb b a).
      { intros b Hb.
        assert (Hbo1 : In b (a :: o1)).
        { apply (Permutation_in b (Permutation_sym HP)). apply in_or_app. left. exact Hb. }
        split; [| split].
        - intro Eb. subst b. apply Har. apply in_or_app. left. exact Hb.
        - intro Hba. pose proof (Hc1 b a Hba Hbo1 (or_introl eq_refl)) as Hp.
          simpl in Hp. destruct Hp as [[Eab Hin] | Hp].
          + apply Ha1. exact Hin.
          + apply Ha1. exact (prec_in_r _ _ _ Hp).
        - intro Hab. apply (prec_before_contra l a r b Hnd2 Hb).
          apply Hc2; [exact Hab | apply in_or_app; right; left; reflexivity |
                      apply in_or_app; left; exact Hb]. }
      assert (Hco1 : causal hb o1).
      { split; [exact Hnd1t |]. intros x y Hxy Hx Hy.
        apply (prec_tail a); [intro Ex; subst x; contradiction |].
        apply Hc1; [exact Hxy | right; exact Hx | right; exact Hy]. }
      assert (Hco2 : causal hb (l ++ r)).
      { split; [exact (NoDup_remove_1 l r a Hnd2) |]. intros x y Hxy Hx Hy.
        apply (prec_remove l a r x y).
        - intro Ex. subst x. contradiction.
        - intro Ey. subst y. contradiction.
        - apply Hc2; [exact Hxy | apply in_insert; exact Hx | apply in_insert; exact Hy]. }
      assert (HP' : Permutation o1 (l ++ r)) by (exact (Permutation_cons_app_inv _ _ HP)).
      rewrite (bubble l a r s Hbub), !run_cons.
      exact (IH (l ++ r) (step a s) Hco1 Hco2 HP').
  Qed.
End CausalConvergence.

(* ----- op-based CRDTs: the instance, and the exact correspondence ----- *)

Section CausalCRDT.
  Context {S Op : Type}.
  Variable apply : Op -> S -> S.
  Variable hb : Op -> Op -> Prop.

  (* The standard op-based CRDT condition: CONCURRENT operations commute (delivery is causal). *)
  Definition causal_cmrdt : Prop :=
    forall a b s, concurrent hb a b -> apply a (apply b s) = apply b (apply a s).

  (* Strong eventual consistency for op-based CRDTs under causal delivery. *)
  Theorem causal_cmrdt_SEC :
    causal_cmrdt ->
    forall o1 o2 s, causal hb o1 -> causal hb o2 -> Permutation o1 o2 ->
      run apply o1 s = run apply o2 s.
  Proof. intros H. exact (causal_convergence apply hb H). Qed.

  (* A governed system: apply an operation, then normalize. *)
  Variable normalize : S -> S.
  Definition gstep (o : Op) (s : S) : S := normalize (apply o s).

  (* Exactness: when the system is compensation-free (normalization is the identity), the causal
     convergence condition on governed steps is EQUIVALENT to being an op-based CRDT. Forward is the
     converse of the embedding; backward is the embedding. *)
  Theorem compensation_free_exact :
    (forall s, normalize s = s) ->
    ((forall a b s, concurrent hb a b -> gstep a (gstep b s) = gstep b (gstep a s))
     <-> causal_cmrdt).
  Proof.
    intros Hid. unfold gstep, causal_cmrdt. split; intros H a b s Hc.
    - specialize (H a b s Hc). rewrite !Hid in H. exact H.
    - rewrite !Hid. exact (H a b s Hc).
  Qed.
End CausalCRDT.

Arguments causal_cmrdt {S Op} apply hb.

(* ============================================================
   Witnesses. Axiom-free.
   ============================================================ *)

(* Strictness: a governed system that converges under causal delivery but is not an op-based CRDT.
   The state is one boolean, only false is valid, and compensation resets to false. The raw
   operations (set-true, flip) do not commute, so with no causal order between them they are a
   concurrent pair that a CRDT would require to commute; the governed steps still agree. *)
Definition w_settrue (_ : bool) : bool := true.
Definition w_flip (s : bool) : bool := negb s.
Definition w_apply (o : bool -> bool) (s : bool) : bool := o s.
Definition w_norm (_ : bool) : bool := false.
Definition w_hb (_ _ : bool -> bool) : Prop := False.

Lemma w_ops_distinct : w_flip <> w_settrue.
Proof. intro E. pose proof (f_equal (fun f => f true) E) as H. simpl in H. discriminate H. Qed.

Theorem witness_causal_converges :
  forall a b s, concurrent w_hb a b ->
    gstep w_apply w_norm a (gstep w_apply w_norm b s) = gstep w_apply w_norm b (gstep w_apply w_norm a s).
Proof. intros. reflexivity. Qed.

Theorem witness_causal_not_cmrdt : ~ causal_cmrdt w_apply w_hb.
Proof.
  intro H. specialize (H w_flip w_settrue false).
  assert (Hc : concurrent w_hb w_flip w_settrue)
    by (split; [exact w_ops_distinct | split; intros []]).
  specialize (H Hc). unfold w_apply, w_flip, w_settrue in H. simpl in H. discriminate H.
Qed.

(* New reach: operations that do NOT all commute, so the all-pairs theorem does not apply, but that
   converge under causal delivery. A flag that is added and later removed (remove is causally after
   add), plus a counter increment concurrent with both. *)
Inductive rop := Add | Remove | Inc.

Definition r_apply (o : rop) (s : bool * nat) : bool * nat :=
  match o with
  | Add => (true, snd s)
  | Remove => (false, snd s)
  | Inc => (fst s, S (snd s))
  end.

Definition r_hb (a b : rop) : Prop := a = Add /\ b = Remove.

Lemma r_cmrdt : causal_cmrdt r_apply r_hb.
Proof.
  intros a b s [Hne [Hab Hba]].
  destruct a, b; try reflexivity; try (exfalso; apply Hne; reflexivity).
  - exfalso. apply Hab. split; reflexivity.
  - exfalso. apply Hba. split; reflexivity.
Qed.

Theorem witness_beyond_all_pairs :
  (~ forall a b s, r_apply a (r_apply b s) = r_apply b (r_apply a s)) /\
  (forall o1 o2 s, causal r_hb o1 -> causal r_hb o2 -> Permutation o1 o2 ->
     run r_apply o1 s = run r_apply o2 s).
Proof.
  split.
  - intro H. specialize (H Add Remove (false, 0)). simpl in H. discriminate H.
  - exact (causal_cmrdt_SEC r_apply r_hb r_cmrdt).
Qed.

(* The instance computes: two causally consistent orders reach the same state. *)
Example witness_orders_agree :
  run r_apply [Add; Inc; Remove] (false, 0) = run r_apply [Inc; Add; Remove] (false, 0).
Proof. reflexivity. Qed.
