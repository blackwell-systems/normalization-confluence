(* A verified checker that operates on the RULES (the combinator AST), not on
   gsm's pre-computed output tables.

   With closure-free rules (gsm's combinator vocabulary), a machine is DATA: each
   invariant is a predicate + a repair transform, each event is a transform, all
   built from a fixed expression grammar. This file models that grammar in Coq,
   computes each event's step function by EVALUATING the AST (apply the event, then
   normalize by iterated repair), and proves: if the AST-derived step functions map
   valid states to valid states and pairwise commute on valid states, then the
   machine converges (any order of the same events from a valid state yields the
   same state). Extracted, this checker recomputes convergence straight from the
   rules, so it does not have to trust gsm to have computed its tables correctly.

   State is a valuation (list of per-variable values in raw 0..domain-1 space; the
   min=0 case, which gsm's exporter targets). Axiom-free; reuses run_perm_invariant
   from Checker.v for the order-independence conclusion. *)

Require Import NC.Checker.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Import ListNotations.

(* ===== the combinator grammar as data ===== *)

Inductive expr :=
| EVar (i : nat)
| ELit (n : nat)
| EAdd (a b : expr)
| ESub (a b : expr).

Inductive pred :=
| PLe (a b : expr)
| PLt (a b : expr)
| PEq (a b : expr)
| PAnd (ps : list pred)
| POr (ps : list pred)
| PNot (p : pred).

Definition assign : Type := (nat * expr)%type. (* variable index := expr *)
Definition transform : Type := list assign.

(* An event carries a guard (a precondition) and an effect. An unguarded event uses
   a guard that is always true (PAnd []). A guarded event is a no-op when its guard
   is false, matching gsm's DeclEventGuarded. *)
Definition gevent : Type := (pred * transform)%type.

(* A machine: per-variable domain size and logical minimum (values live in
   min .. min+domain-1; the state stores the raw 0..domain-1 offset), invariants
   (predicate + repair), and guarded events. *)
Record machine := {
  doms : list nat;                     (* doms[i] = domain size of variable i *)
  mins : list nat;                     (* mins[i] = logical minimum of variable i *)
  invs : list (pred * transform);
  evs  : list gevent
}.

(* ===== valuation state + evaluation (matches gsm readVal/writeVal, raw space) ===== *)

Definition valn := list nat.

Fixpoint rd (i : nat) (s : valn) {struct s} : nat :=
  match s with
  | [] => 0
  | x :: t => match i with 0 => x | S i' => rd i' t end
  end.

Fixpoint wr (i v : nat) (s : valn) {struct s} : valn :=
  match s with
  | [] => []
  | x :: t => match i with 0 => v :: t | S i' => x :: wr i' v t end
  end.

(* A variable reads in LOGICAL space: min[i] + the raw stored offset. *)
Fixpoint evalE (mins : list nat) (s : valn) (e : expr) : nat :=
  match e with
  | EVar i => nth i mins 0 + rd i s
  | ELit n => n
  | EAdd a b => evalE mins s a + evalE mins s b
  | ESub a b => evalE mins s a - evalE mins s b   (* nat subtraction (truncates at 0) *)
  end.

Fixpoint evalP (mins : list nat) (s : valn) (p : pred) : bool :=
  match p with
  | PLe a b => Nat.leb (evalE mins s a) (evalE mins s b)
  | PLt a b => Nat.ltb (evalE mins s a) (evalE mins s b)
  | PEq a b => Nat.eqb (evalE mins s a) (evalE mins s b)
  | PAnd ps => forallb (evalP mins s) ps
  | POr ps => existsb (evalP mins s) ps
  | PNot p => negb (evalP mins s p)
  end.

(* Writing takes a LOGICAL value, stores the raw offset value-min, clamped into
   0..doms[i]-1 (so the state stays in range), like gsm's SetInt. *)
Definition setClamped (m : machine) (i v : nat) (s : valn) : valn :=
  wr i (Nat.min (v - nth i (mins m) 0) (nth i (doms m) 1 - 1)) s.

Fixpoint applyT (m : machine) (t : transform) (s : valn) : valn :=
  match t with
  | [] => s
  | (i, e) :: rest => applyT m rest (setClamped m i (evalE (mins m) s e) s)
  end.

Definition allValid (m : machine) (s : valn) : bool :=
  forallb (fun inv => evalP (mins m) s (fst inv)) (invs m).

(* One repair step: fire the first violated invariant's repair. *)
Definition repair1 (m : machine) (s : valn) : valn :=
  match find (fun inv => negb (evalP (mins m) s (fst inv))) (invs m) with
  | Some inv => applyT m (snd inv) s
  | None => s
  end.

(* Normalize by iterated repair, bounded by fuel. *)
Fixpoint normalize (m : machine) (fuel : nat) (s : valn) : valn :=
  match fuel with
  | 0 => s
  | S f => if allValid m s then s else normalize m f (repair1 m s)
  end.

Definition fuelOf (m : machine) : nat := fold_left Nat.mul (doms m) 1.

(* The step function of a guarded event: if the guard holds, apply the effect then
   normalize; otherwise the event is a no-op. *)
Definition stepAst (m : machine) (ge : gevent) (s : valn) : valn :=
  if evalP (mins m) s (fst ge)
  then normalize m (fuelOf m) (applyT m (snd ge) s)
  else s.

Fixpoint valeqb (a b : valn) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => andb (Nat.eqb x y) (valeqb xs ys)
  | _, _ => false
  end.

Lemma valeqb_eq : forall a b, valeqb a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; intros [| y ys] H; simpl in H; try discriminate; try reflexivity.
  apply andb_prop in H. destruct H as [Hxy Hxs].
  apply Nat.eqb_eq in Hxy. subst y. f_equal. apply IH; exact Hxs.
Qed.

(* ===== the checker ===== *)

(* Enumerate the valuation box: all assignments of each variable over its domain. *)
Fixpoint box (ds : list nat) : list valn :=
  match ds with
  | [] => [ [] ]
  | d :: rest => flat_map (fun v => map (cons v) (box rest)) (seq 0 d)
  end.

(* check: on every VALID valuation in the box, every event-step lands on a valid
   valuation (so normalization actually completed) and every ordered pair of
   event-steps commutes. *)
Definition stepCheckOne (m : machine) (v : valn) : bool :=
  forallb (fun e1 =>
    andb (allValid m (stepAst m e1 v))
      (forallb (fun e2 =>
        valeqb
          (stepAst m e2 (stepAst m e1 v))
          (stepAst m e1 (stepAst m e2 v)))
        (evs m)))
    (evs m).

Definition check (m : machine) : bool :=
  forallb (fun v => if allValid m v then stepCheckOne m v else true) (box (doms m)).

(* ===== soundness ===== *)

(* If the check passes, then on every valid valuation in the box, each event-step
   lands on a valid valuation (normalization completed) and every ordered pair of
   event-steps commutes. These are the two facts that, via run_perm_invariant
   (Checker.v), make the machine converge: applying the same events in any order
   from such a state yields the same state. *)

Lemma check_here :
  forall m, check m = true ->
  forall v, In v (box (doms m)) -> allValid m v = true -> stepCheckOne m v = true.
Proof.
  intros m Hchk v Hv Hval. unfold check in Hchk.
  rewrite forallb_forall in Hchk. specialize (Hchk v Hv).
  rewrite Hval in Hchk. exact Hchk.
Qed.

Theorem check_sound_preserves_valid :
  forall m, check m = true ->
  forall v, In v (box (doms m)) -> allValid m v = true ->
  forall e, In e (evs m) -> allValid m (stepAst m e v) = true.
Proof.
  intros m Hchk v Hv Hval e He.
  pose proof (check_here m Hchk v Hv Hval) as H.
  unfold stepCheckOne in H. rewrite forallb_forall in H.
  specialize (H e He). apply andb_prop in H. destruct H as [Hpv _]. exact Hpv.
Qed.

Theorem check_sound_commute :
  forall m, check m = true ->
  forall v, In v (box (doms m)) -> allValid m v = true ->
  forall e1 e2, In e1 (evs m) -> In e2 (evs m) ->
    stepAst m e2 (stepAst m e1 v) = stepAst m e1 (stepAst m e2 v).
Proof.
  intros m Hchk v Hv Hval e1 e2 He1 He2.
  pose proof (check_here m Hchk v Hv Hval) as H.
  unfold stepCheckOne in H. rewrite forallb_forall in H.
  specialize (H e1 He1). apply andb_prop in H. destruct H as [_ Hcomm].
  rewrite forallb_forall in Hcomm. specialize (Hcomm e2 He2).
  apply valeqb_eq in Hcomm. exact Hcomm.
Qed.

(* ===== convergence: the two checked facts give order-independence ===== *)

(* To lift the pairwise commutation (a one-step fact) to whole event sequences we
   need that an event-step keeps the state inside the enumerated valuation box, so
   commutation keeps applying along a run. A valuation is in the box exactly when it
   has one entry per variable, each within that variable's domain. *)

Definition inRange (ds : list nat) (v : valn) : Prop :=
  length v = length ds /\ forall j, j < length ds -> nth j v 0 < nth j ds 0.

Lemma box_length : forall ds v, In v (box ds) -> length v = length ds.
Proof.
  induction ds as [| d rest IH]; intros v Hin; simpl in Hin.
  - destruct Hin as [<- | []]. reflexivity.
  - apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
    apply in_map_iff in Hin. destruct Hin as [w [Heq Hw]]. subst v.
    simpl. f_equal. apply IH; exact Hw.
Qed.

Lemma box_range : forall ds v, In v (box ds) ->
  forall j, j < length ds -> nth j v 0 < nth j ds 0.
Proof.
  induction ds as [| d rest IH]; intros v Hin j Hj; simpl in *.
  - lia.
  - apply in_flat_map in Hin. destruct Hin as [x [Hx Hin]].
    apply in_seq in Hx. apply in_map_iff in Hin. destruct Hin as [w [Heq Hw]]. subst v.
    destruct j as [| j']; simpl.
    + lia.
    + apply IH; [exact Hw | lia].
Qed.

Lemma box_intro : forall ds v,
  length v = length ds ->
  (forall j, j < length ds -> nth j v 0 < nth j ds 0) ->
  In v (box ds).
Proof.
  induction ds as [| d rest IH]; intros v Hlen Hr; simpl.
  - destruct v; simpl in Hlen; [left; reflexivity | discriminate].
  - destruct v as [| x w]; simpl in Hlen; [discriminate | ].
    apply in_flat_map. exists x. split.
    + apply in_seq. split; [lia | ]. specialize (Hr 0 ltac:(simpl; lia)). simpl in Hr. lia.
    + apply in_map_iff. exists w. split; [reflexivity | ].
      apply IH; [lia | ]. intros j Hj. specialize (Hr (S j) ltac:(simpl; lia)). simpl in Hr. exact Hr.
Qed.

Lemma box_iff : forall ds v, In v (box ds) <-> inRange ds v.
Proof.
  intros ds v. split.
  - intro Hin. split; [apply box_length; exact Hin | apply box_range; exact Hin].
  - intros [Hlen Hr]. apply box_intro; assumption.
Qed.

(* wr writes one position; it preserves length and only changes that position. *)
Lemma wr_length : forall s x i, length (wr i x s) = length s.
Proof.
  induction s as [| a t IH]; intros x i; destruct i as [| i']; simpl;
    try reflexivity; try (rewrite IH); reflexivity.
Qed.

Lemma wr_nth_neq : forall s j i x, j <> i -> nth j (wr i x s) 0 = nth j s 0.
Proof.
  induction s as [| a t IH]; intros j i x Hne.
  - destruct i; reflexivity.
  - destruct i as [| i']; destruct j as [| j']; simpl.
    + lia.
    + reflexivity.
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma wr_nth_eq : forall s i x, i < length s -> nth i (wr i x s) 0 = x.
Proof.
  induction s as [| a t IH]; intros i x Hlt; simpl in Hlt.
  - lia.
  - destruct i as [| i']; simpl; [reflexivity | apply IH; lia].
Qed.

Lemma setClamped_pres : forall m i v s,
  inRange (doms m) s -> inRange (doms m) (setClamped m i v s).
Proof.
  intros m i v s [Hlen Hr]. unfold setClamped. split.
  - rewrite wr_length. exact Hlen.
  - intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne].
    + assert (Hi : i < length s) by (rewrite Hlen; exact Hj).
      assert (Hd : nth i (doms m) 1 = nth i (doms m) 0) by (apply nth_indep; exact Hj).
      rewrite wr_nth_eq by exact Hi.
      specialize (Hr i Hj). rewrite Hd. lia.
    + rewrite wr_nth_neq by exact Hne. apply Hr; exact Hj.
Qed.

Lemma applyT_pres : forall m t s,
  inRange (doms m) s -> inRange (doms m) (applyT m t s).
Proof.
  intros m t. induction t as [| [i e] rest IH]; intros s Hin; simpl.
  - exact Hin.
  - apply IH. apply setClamped_pres. exact Hin.
Qed.

Lemma repair1_pres : forall m s,
  inRange (doms m) s -> inRange (doms m) (repair1 m s).
Proof.
  intros m s Hin. unfold repair1.
  destruct (find (fun inv => negb (evalP (mins m) s (fst inv))) (invs m)) as [inv | ].
  - apply applyT_pres. exact Hin.
  - exact Hin.
Qed.

Lemma normalize_pres : forall m fuel s,
  inRange (doms m) s -> inRange (doms m) (normalize m fuel s).
Proof.
  intros m fuel. induction fuel as [| f IH]; intros s Hin; simpl.
  - exact Hin.
  - destruct (allValid m s); [exact Hin | apply IH; apply repair1_pres; exact Hin].
Qed.

Lemma stepAst_pres : forall m e s,
  inRange (doms m) s -> inRange (doms m) (stepAst m e s).
Proof.
  intros m e s Hin. unfold stepAst.
  destruct (evalP (mins m) s (fst e)).
  - apply normalize_pres. apply applyT_pres. exact Hin.
  - exact Hin.
Qed.

Lemma stepAst_in_box : forall m e v,
  In v (box (doms m)) -> In (stepAst m e v) (box (doms m)).
Proof.
  intros m e v Hin. apply box_iff. apply stepAst_pres. apply box_iff. exact Hin.
Qed.

Section AstConverge.
  Variable m : machine.
  Hypothesis Hchk : check m = true.

  (* The invariant an event-step preserves: still in the box, still valid. *)
  Definition good (v : valn) : Prop := In v (box (doms m)) /\ allValid m v = true.

  Lemma step_good : forall e v, In e (evs m) -> good v -> good (stepAst m e v).
  Proof.
    intros e v He [Hbox Hval]. split.
    - apply stepAst_in_box. exact Hbox.
    - apply (check_sound_preserves_valid m Hchk v Hbox Hval e He).
  Qed.

  (* Apply a sequence of events left to right (the AST analogue of Checker.run). *)
  Definition runAst (es : list gevent) (v : valn) : valn :=
    fold_left (fun s e => stepAst m e s) es v.

  Lemma runAst_cons : forall e es v, runAst (e :: es) v = runAst es (stepAst m e v).
  Proof. reflexivity. Qed.

  (* Order-independence on valid states: same events in any order, same result. The
     argument mirrors Checker.run_perm_invariant, but carries `good` because our
     commutation is guaranteed only on valid box states (check_sound_commute). *)
  Lemma run_good_perm :
    forall es1 es2, Permutation es1 es2 ->
    (forall e, In e es1 -> In e (evs m)) ->
    forall v, good v -> runAst es1 v = runAst es2 v.
  Proof.
    intros es1 es2 Hperm.
    induction Hperm as
      [ | e l1 l2 Hp IH | e1 e2 l | l1 l2 l3 Hp1 IH1 Hp2 IH2 ]; intros Hev v Hgood.
    - reflexivity.
    - rewrite !runAst_cons. apply IH.
      + intros x Hx. apply Hev. right; exact Hx.
      + apply step_good; [apply Hev; left; reflexivity | exact Hgood].
    - rewrite !runAst_cons.
      assert (He1 : In e1 (evs m)) by (apply Hev; right; left; reflexivity).
      assert (He2 : In e2 (evs m)) by (apply Hev; left; reflexivity).
      destruct Hgood as [Hbox Hval].
      rewrite (check_sound_commute m Hchk v Hbox Hval e2 e1 He2 He1).
      reflexivity.
    - assert (Hev2 : forall x, In x l2 -> In x (evs m)).
      { intros x Hx. apply Hev. apply Permutation_in with (l := l2); [apply Permutation_sym; exact Hp1 | exact Hx]. }
      rewrite (IH1 Hev v Hgood). apply IH2; [exact Hev2 | exact Hgood].
  Qed.

  (* Capstone: if the AST checker passes, then from any valid valuation, applying
     the same multiset of events in any two orders yields the same valuation. The
     verifier for this fact is machine-checked and runs on the rules themselves. *)
  Theorem check_sound_converges :
    forall v, In v (box (doms m)) -> allValid m v = true ->
    forall es1 es2, Permutation es1 es2 ->
      (forall e, In e es1 -> In e (evs m)) ->
      runAst es1 v = runAst es2 v.
  Proof.
    intros v Hbox Hval es1 es2 Hperm Hev.
    apply run_good_perm; [exact Hperm | exact Hev | split; assumption].
  Qed.
End AstConverge.

(* ===== the compensation-free fragment: CRDTs =====

   A machine is compensation-free when no in-domain valuation ever needs repair:
   every valuation in the box already satisfies every invariant, so normalization
   is the identity and no compensation ever fires. This is exactly the fragment
   CRDT.v characterizes as the CRDTs (operations preserve every invariant, so there
   is nothing to compensate). The predicate is decidable and extracted, so the CRDT
   classification is CERTIFIED from the rules, not asserted by the producer. It is
   the AST analogue of gsm's "max repair depth = 0". *)
Definition compensationFree (m : machine) : bool :=
  forallb (allValid m) (box (doms m)).

Lemma compensationFree_valid :
  forall m, compensationFree m = true ->
  forall v, In v (box (doms m)) -> allValid m v = true.
Proof.
  intros m Hcf v Hv. unfold compensationFree in Hcf.
  rewrite forallb_forall in Hcf. apply Hcf. exact Hv.
Qed.

Lemma normalize_valid_id :
  forall m fuel s, allValid m s = true -> normalize m fuel s = s.
Proof.
  intros m fuel s Hval.
  destruct fuel as [| f]; simpl; [reflexivity | rewrite Hval; reflexivity].
Qed.

(* Under compensation-freeness, an event-step never repairs: it is exactly the
   guarded effect, with no normalization interposed. This is the defining behavior
   of a CRDT operation (mutate directly; there is nothing to compensate), so a
   machine the checker calls compensation-free provably belongs to the CRDT
   fragment. *)
Theorem compensationFree_step_no_repair :
  forall m, compensationFree m = true ->
  forall e v, In v (box (doms m)) ->
    stepAst m e v = (if evalP (mins m) v (fst e) then applyT m (snd e) v else v).
Proof.
  intros m Hcf e v Hv. unfold stepAst.
  destruct (evalP (mins m) v (fst e)); [| reflexivity].
  apply normalize_valid_id.
  apply compensationFree_valid; [exact Hcf |].
  apply box_iff. apply applyT_pres. apply box_iff. exact Hv.
Qed.
