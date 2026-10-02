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

   State is a valuation (list of per-variable values in raw 0..domain-1 space).
   Expressions evaluate in LOGICAL space over the integers Z, with gsm's signed Go
   semantics: a variable reads as min + raw, Add/Sub are signed, comparisons are
   signed, and a write stores the clamped raw offset. Two gsm behaviours are not
   modelled; `check` refuses every machine where they could matter:
   - Go's `int` wraps (at 2^31 on 32-bit platforms). check_no_overflow: on a
     certified machine every subexpression stays within 32-bit range on every
     valuation the checker sees, so Go never wraps and Z is exactly gsm's
     arithmetic.
   - A gsm Bool write stores (value <> 0), not a clamp. The format carries no
     variable kinds, so check_binary_writes_exact covers every two-valued
     variable with minimum 0: on a certified machine every write to one stores
     exactly (value <> 0), which is both the clamp and the Bool write.
   Axiom-free; reuses run_perm_invariant from Checker.v for the order-independence
   conclusion. *)

Require Import NC.Checker.
Require Import NC.Trace.
Require Import NC.TableCheck.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import ZArith.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Lia.
Import ListNotations.

(* ===== the combinator grammar as data ===== *)

Inductive expr :=
| EVar (i : nat)
| ELit (n : Z)
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
  mins : list Z;                       (* mins[i] = logical minimum of variable i *)
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

(* A variable reads in LOGICAL space: min[i] + the raw stored offset. Arithmetic
   is signed, as in gsm's binE.eval over Go int (see check_no_overflow for why no
   wraparound needs modelling). *)
Fixpoint evalE (mins : list Z) (s : valn) (e : expr) : Z :=
  match e with
  | EVar i => (nth i mins 0%Z + Z.of_nat (rd i s))%Z
  | ELit n => n
  | EAdd a b => (evalE mins s a + evalE mins s b)%Z
  | ESub a b => (evalE mins s a - evalE mins s b)%Z
  end.

Fixpoint evalP (mins : list Z) (s : valn) (p : pred) : bool :=
  match p with
  | PLe a b => Z.leb (evalE mins s a) (evalE mins s b)
  | PLt a b => Z.ltb (evalE mins s a) (evalE mins s b)
  | PEq a b => Z.eqb (evalE mins s a) (evalE mins s b)
  | PAnd ps => forallb (evalP mins s) ps
  | POr ps => existsb (evalP mins s) ps
  | PNot p => negb (evalP mins s p)
  end.

(* Writing takes a LOGICAL value and stores the raw offset value-min, clamped into
   0..doms[i]-1 (so the state stays in range), like gsm's SetInt (clamp into
   min..max, store val-min) and its enum write (clamp into 0..domain-1). Z.to_nat
   sends a value below the minimum to raw 0, which is the lower clamp. *)
(* Init.Nat.min, which ExtrOcamlNatInt maps to OCaml's min; PeanoNat's Nat.min is
   an unmapped copy that extracts as unary recursion. *)
Definition setClamped (m : machine) (i : nat) (v : Z) (s : valn) : valn :=
  wr i (Init.Nat.min (Z.to_nat (v - nth i (mins m) 0%Z)) (nth i (doms m) 1 - 1)) s.

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

(* Init.Nat.mul, which ExtrOcamlNatInt maps to OCaml's ( * ); PeanoNat's Nat.mul is an
   unmapped copy that extracts as unary recursion. *)
Definition fuelOf (m : machine) : nat := fold_left Init.Nat.mul (doms m) 1.

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

(* ===== the bounded-arithmetic fragment =====

   gsm evaluates expressions in Go `int`. Rather than model Go's platform-dependent
   wraparound, the checker only certifies machines where no wraparound can occur:
   bnd over-approximates |value| of an expression on every valuation in the box,
   and `bounded` requires bnd <= 2^31-1 for every expression the rules contain.
   Since a subexpression's bound is at most its parent's, every intermediate value
   Go computes is in 32-bit range too (check_no_overflow). *)
Definition maxAbs : Z := 2147483647%Z.

Definition varBound (m : machine) (i : nat) : Z :=
  Z.max (Z.abs (nth i (mins m) 0%Z)) (Z.abs (nth i (mins m) 0%Z + Z.of_nat (nth i (doms m) 0) - 1)).

Fixpoint bnd (m : machine) (e : expr) : Z :=
  match e with
  | EVar i => varBound m i
  | ELit n => Z.abs n
  | EAdd a b | ESub a b => (bnd m a + bnd m b)%Z
  end.

(* The expressions a predicate, transform, and machine contain. *)
Fixpoint exprsP (p : pred) : list expr :=
  match p with
  | PLe a b | PLt a b | PEq a b => [a; b]
  | PAnd ps | POr ps => flat_map exprsP ps
  | PNot q => exprsP q
  end.

Definition exprsT (t : transform) : list expr := map snd t.

Definition exprsM (m : machine) : list expr :=
  flat_map (fun inv => exprsP (fst inv) ++ exprsT (snd inv)) (invs m) ++
  flat_map (fun ge => exprsP (fst ge) ++ exprsT (snd ge)) (evs m).

(* Every subexpression of e, e included. *)
Fixpoint subexprs (e : expr) : list expr :=
  e :: match e with
       | EVar _ | ELit _ => []
       | EAdd a b | ESub a b => subexprs a ++ subexprs b
       end.

Definition bounded (m : machine) : bool :=
  forallb (fun e => Z.leb (bnd m e) maxAbs) (exprsM m).

(* ===== writes to two-valued variables =====

   gsm's Bool write stores (value <> 0); the model clamps. The two agree exactly
   when the value is not negative. lo/hi bound an expression's value by interval
   arithmetic, and signSafe requires lo >= 0 for every write to a two-valued
   variable with minimum 0 (every Bool is one; Int 0..1 and two-value Enums are
   too, and are held to the same rule because the format does not say which). *)
Fixpoint lo (m : machine) (e : expr) : Z :=
  match e with
  | EVar i => nth i (mins m) 0%Z
  | ELit n => n
  | EAdd a b => (lo m a + lo m b)%Z
  | ESub a b => (lo m a - hi m b)%Z
  end
with hi (m : machine) (e : expr) : Z :=
  match e with
  | EVar i => (nth i (mins m) 0%Z + Z.of_nat (nth i (doms m) 1%nat) - 1)%Z
  | ELit n => n
  | EAdd a b => (hi m a + hi m b)%Z
  | ESub a b => (hi m a - lo m b)%Z
  end.

Definition binaryVar (m : machine) (i : nat) : bool :=
  andb (Nat.eqb (nth i (doms m) 0) 2) (Z.eqb (nth i (mins m) 0%Z) 0).

Definition signSafeT (m : machine) (t : transform) : bool :=
  forallb (fun a => implb (binaryVar m (fst a)) (Z.leb 0 (lo m (snd a)))) t.

Definition transformsM (m : machine) : list transform :=
  map snd (invs m) ++ map snd (evs m).

Definition signSafe (m : machine) : bool :=
  forallb (signSafeT m) (transformsM m).

Definition check (m : machine) : bool :=
  andb (andb (bounded m) (signSafe m))
    (forallb (fun v => if allValid m v then stepCheckOne m v else true) (box (doms m))).

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
  apply andb_prop in Hchk. destruct Hchk as [_ Hchk].
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

(* ===== certified machines never overflow Go's int =====

   gsm evaluates every expression in Go `int` (32 bits on 32-bit platforms). If
   the checker passes, every subexpression of every expression in the rules has
   |value| <= 2^31-1 on every valuation in the box, which contains every state
   gsm's Build enumerates and every intermediate state of a repair or an event.
   So no Go evaluation of these rules wraps, on any platform, and the Z semantics
   above is exactly what gsm computes. *)

Lemma rd_nth : forall s i, rd i s = nth i s 0.
Proof.
  induction s as [| x t IH]; intros i; destruct i as [| i']; simpl; try reflexivity.
  apply IH.
Qed.

Lemma bnd_nonneg : forall m e, (0 <= bnd m e)%Z.
Proof. intros m e. induction e; simpl; unfold varBound; lia. Qed.

Lemma evalE_bnd : forall m v e,
  In v (box (doms m)) -> (Z.abs (evalE (mins m) v e) <= bnd m e)%Z.
Proof.
  intros m v e Hv.
  induction e as [i | n | a IHa b IHb | a IHa b IHb]; simpl.
  - unfold varBound. rewrite rd_nth.
    destruct (Nat.lt_ge_cases i (length (doms m))) as [Hi | Hi].
    + pose proof (box_range _ _ Hv i Hi) as Hr. lia.
    + rewrite (nth_overflow v 0) by (rewrite (box_length _ _ Hv); exact Hi). lia.
  - lia.
  - lia.
  - lia.
Qed.

Lemma subexprs_bnd : forall m e e', In e' (subexprs e) -> (bnd m e' <= bnd m e)%Z.
Proof.
  intros m e. induction e as [i | n | a IHa b IHb | a IHa b IHb]; intros e' Hin; simpl in Hin.
  - destruct Hin as [<- | []]. lia.
  - destruct Hin as [<- | []]. lia.
  - destruct Hin as [<- | Hin]; [lia |]. simpl.
    pose proof (bnd_nonneg m a). pose proof (bnd_nonneg m b).
    apply in_app_or in Hin. destruct Hin as [Hs | Hs];
      [specialize (IHa e' Hs) | specialize (IHb e' Hs)]; lia.
  - destruct Hin as [<- | Hin]; [lia |]. simpl.
    pose proof (bnd_nonneg m a). pose proof (bnd_nonneg m b).
    apply in_app_or in Hin. destruct Hin as [Hs | Hs];
      [specialize (IHa e' Hs) | specialize (IHb e' Hs)]; lia.
Qed.

Theorem check_no_overflow :
  forall m, check m = true ->
  forall e, In e (exprsM m) ->
  forall e', In e' (subexprs e) ->
  forall v, In v (box (doms m)) ->
    (Z.abs (evalE (mins m) v e') <= maxAbs)%Z.
Proof.
  intros m Hchk e He e' Hsub v Hv.
  unfold check in Hchk. apply andb_prop in Hchk. destruct Hchk as [Hb _].
  apply andb_prop in Hb. destruct Hb as [Hb _].
  unfold bounded in Hb. rewrite forallb_forall in Hb.
  specialize (Hb e He). apply Z.leb_le in Hb.
  pose proof (evalE_bnd m v e' Hv). pose proof (subexprs_bnd m e e' Hsub). lia.
Qed.

(* ===== certified machines write Bools exactly as gsm does ===== *)

Lemma evalE_range : forall m v e,
  In v (box (doms m)) -> (lo m e <= evalE (mins m) v e <= hi m e)%Z.
Proof.
  intros m v e Hv.
  induction e as [i | n | a IHa b IHb | a IHa b IHb]; simpl.
  - rewrite rd_nth.
    destruct (Nat.lt_ge_cases i (length (doms m))) as [Hi | Hi].
    + pose proof (box_range _ _ Hv i Hi) as Hr.
      assert (Hd : nth i (doms m) 1 = nth i (doms m) 0) by (apply nth_indep; exact Hi).
      rewrite Hd. lia.
    + rewrite (nth_overflow v 0) by (rewrite (box_length _ _ Hv); exact Hi).
      rewrite (nth_overflow (doms m) 1) by exact Hi. lia.
  - lia.
  - lia.
  - lia.
Qed.

(* The clamp into a two-valued, minimum-0 variable stores exactly gsm's Bool value
   (value <> 0) whenever the value is not negative. *)
Lemma clamp_binary_is_bool : forall v : Z,
  (0 <= v)%Z -> Nat.min (Z.to_nat (v - 0)) (2 - 1) = (if Z.eqb v 0 then 0 else 1).
Proof.
  intros v Hv. destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity | lia].
Qed.

Theorem check_binary_writes_exact :
  forall m, check m = true ->
  forall t, In t (transformsM m) ->
  forall i e, In (i, e) t -> nth i (doms m) 0 = 2 -> nth i (mins m) 0%Z = 0%Z ->
  forall v s, In v (box (doms m)) ->
    setClamped m i (evalE (mins m) v e) s =
    wr i (if Z.eqb (evalE (mins m) v e) 0 then 0 else 1) s.
Proof.
  intros m Hchk t Ht i e Hin Hd Hm v s Hv.
  unfold check in Hchk. apply andb_prop in Hchk. destruct Hchk as [Hb _].
  apply andb_prop in Hb. destruct Hb as [_ Hs].
  unfold signSafe in Hs. rewrite forallb_forall in Hs. specialize (Hs t Ht).
  unfold signSafeT in Hs. rewrite forallb_forall in Hs. specialize (Hs (i, e) Hin).
  simpl in Hs. unfold binaryVar in Hs. rewrite Hd, Hm in Hs. simpl in Hs.
  apply Z.leb_le in Hs.
  pose proof (evalE_range m v e Hv) as [Hlo _].
  unfold setClamped. rewrite Hm.
  assert (Hd1 : nth i (doms m) 1 = 2).
  { destruct (Nat.lt_ge_cases i (length (doms m))) as [Hi | Hi].
    - rewrite <- Hd. apply nth_indep. exact Hi.
    - rewrite (nth_overflow (doms m) 0) in Hd by exact Hi. discriminate. }
  rewrite Hd1. f_equal. apply clamp_binary_is_bool. lia.
Qed.

(* ===== the rules oracle aligned with gsm's Build =====

   `check` above decides a property that differs from Build's in three ways, each
   measured by gsm's differential test:
   - Repair termination. Build requires repair to terminate from EVERY state in
     the box (computeNormalForms runs it from every encoding); check only required
     it from the states an event reaches from a valid state. Every theorem of the
     convergence meta-theory assumes the stronger form (Governance.wfc and
     Gsm.repair_terminates quantify over all states), the runtime's
     Machine.Normalize applies it to any state, and THEORY.md section 5.1 defines
     WFC over the whole state space. So the oracle takes Build's side: `wfc`.
   - Declared pairs. Build checks only the pairs declared independent, or every
     pair when none is declared. checkBuild takes the declared pairs as an input
     (None: every pair), and its guarantee is stated for sequences that differ by
     reordering declared-independent events (Trace.tequiv).
   - Domain. Build checks commutation on the valid states plus the zero state
     Machine.NewState returns, valid or not; check used the valid states only.
     The zero state brings a second alignment: gsm's step normalizes even when
     the guard is false (its step table holds NF(s) there, and the lazy runtime
     does the same), where stepAst returns s unchanged. The two agree on valid
     states (stepG_valid_eq), so only an invalid zero state can tell them apart,
     and stepG is gsm's step.
   The arithmetic fragment (bounded, signSafe) is unchanged. *)

Local Open Scope bool_scope.

Definition stepG (m : machine) (ge : gevent) (s : valn) : valn :=
  normalize m (fuelOf m) (if evalP (mins m) s (fst ge) then applyT m (snd ge) s else s).

Definition noEvent : gevent := (PAnd [], []).
Definition evAt (m : machine) (e : nat) : gevent := nth e (evs m) noEvent.
Definition stepI (m : machine) (e : nat) (s : valn) : valn := stepG m (evAt m e) s.

Definition zeroV (m : machine) : valn := repeat 0 (length (doms m)).
Definition inDA (m : machine) (v : valn) : bool := allValid m v || valeqb v (zeroV m).

(* Build's WFC: repair reaches a valid state from every state in the box. The
   fuel is the box size, which is enough: repair is deterministic, so a run that
   has not reached a valid state after that many steps has repeated a state and
   cycles forever (Build fails the same machines, on a repeat or on a run longer
   than the state count). *)
Definition wfc (m : machine) : bool :=
  forallb (fun v => allValid m (normalize m (fuelOf m) v)) (box (doms m)).

Definition pairsA (m : machine) (P : option (list (nat * nat))) : list (nat * nat) :=
  match P with None => allPairs (length (evs m)) | Some l => l end.

Definition indepA (m : machine) (P : option (list (nat * nat))) (a b : nat) : Prop :=
  match P with
  | None => a < length (evs m) /\ b < length (evs m)
  | Some l => In (a, b) l \/ In (b, a) l
  end.

Definition pairsOkA (m : machine) (P : option (list (nat * nat))) : bool :=
  forallb (fun p => ltn (fst p) (length (evs m)) && ltn (snd p) (length (evs m))) (pairsA m P).

Definition ccA (m : machine) (P : option (list (nat * nat))) : bool :=
  forallb (fun v => implb (inDA m v)
    (forallb (fun p => valeqb (stepI m (fst p) (stepI m (snd p) v))
                              (stepI m (snd p) (stepI m (fst p) v)))
       (pairsA m P)))
    (box (doms m)).

Definition checkBuild (m : machine) (P : option (list (nat * nat))) : bool :=
  bounded m && signSafe m && pairsOkA m P && wfc m && ccA m P.

(* gsm's step and stepAst agree on valid states. *)
Lemma stepG_valid_eq : forall m ge v, allValid m v = true -> stepG m ge v = stepAst m ge v.
Proof.
  intros m ge v Hv. unfold stepG, stepAst.
  destruct (evalP (mins m) v (fst ge)); [reflexivity |].
  apply normalize_valid_id. exact Hv.
Qed.

Lemma stepG_pres : forall m ge s, inRange (doms m) s -> inRange (doms m) (stepG m ge s).
Proof.
  intros m ge s Hs. unfold stepG. apply normalize_pres.
  destruct (evalP (mins m) s (fst ge)); [apply applyT_pres |]; exact Hs.
Qed.

(* ===== repair termination ===== *)

Definition rstepA (m : machine) (t s : valn) : Prop := allValid m s = false /\ t = repair1 m s.

Lemma normalize_valid_acc : forall m f s,
  allValid m (normalize m f s) = true -> Acc (rstepA m) s.
Proof.
  intros m f. induction f as [| f IH]; intros s H; simpl in H.
  - constructor. intros t [Hf _]. congruence.
  - destruct (allValid m s) eqn:Hv.
    + constructor. intros t [Hf _]. congruence.
    + specialize (IH _ H). constructor. intros t [_ ->]. exact IH.
Qed.

Fixpoint depthF (m : machine) (f : nat) (s : valn) : nat :=
  match f with
  | 0 => 0
  | S f' => if allValid m s then 0 else S (depthF m f' (repair1 m s))
  end.

Lemma depthF_stable : forall m f s, allValid m (normalize m f s) = true ->
  forall g, f <= g -> depthF m g s = depthF m f s.
Proof.
  intros m f. induction f as [| f IH]; intros s H g Hg; simpl in H.
  - destruct g; simpl; [reflexivity | rewrite H; reflexivity].
  - destruct g as [| g]; [lia |]. simpl.
    destruct (allValid m s) eqn:Hv; [reflexivity |].
    f_equal. apply IH; [exact H | lia].
Qed.

(* The repair-depth potential: what Governance.wfc and Gsm.wfc_decreases assume. *)
Definition phiA (m : machine) (s : valn) : nat := depthF m (fuelOf m) s.

Section CheckBuild.
  Variable m : machine.
  Variable P : option (list (nat * nat)).
  Hypothesis Hchk : checkBuild m P = true.

  Lemma checkBuild_parts :
    bounded m = true /\ signSafe m = true /\ pairsOkA m P = true /\ wfc m = true /\ ccA m P = true.
  Proof.
    pose proof Hchk as H. unfold checkBuild in H.
    repeat rewrite Bool.andb_true_iff in H. tauto.
  Qed.

  Theorem checkBuild_pairs_in_range :
    forall a b, In (a, b) (pairsA m P) -> a < length (evs m) /\ b < length (evs m).
  Proof.
    intros a b Hin. destruct checkBuild_parts as [_ [_ [Hp _]]].
    unfold pairsOkA in Hp. rewrite forallb_forall in Hp. specialize (Hp (a, b) Hin).
    simpl in Hp. apply Bool.andb_true_iff in Hp. destruct Hp as [Ha Hb].
    apply ltn_spec in Ha. apply ltn_spec in Hb. split; assumption.
  Qed.

  Theorem checkBuild_normalize_valid :
    forall v, In v (box (doms m)) -> allValid m (normalize m (fuelOf m) v) = true.
  Proof.
    intros v Hv. destruct checkBuild_parts as [_ [_ [_ [Hw _]]]].
    unfold wfc in Hw. rewrite forallb_forall in Hw. apply Hw, Hv.
  Qed.

  (* WFC, as the meta-theory states it: no infinite compensation sequence starts
     anywhere in the box. *)
  Theorem checkBuild_wfc_terminates : forall v, In v (box (doms m)) -> Acc (rstepA m) v.
  Proof.
    intros v Hv. apply (normalize_valid_acc m (fuelOf m)). apply checkBuild_normalize_valid, Hv.
  Qed.

  (* ... and with the potential the meta-theory's wfc hypothesis asks for: every
     repair of an invalid state in the box strictly decreases the repair depth. *)
  Theorem checkBuild_wfc_potential :
    forall v, In v (box (doms m)) -> allValid m v = false -> phiA m (repair1 m v) < phiA m v.
  Proof.
    intros v Hv Hinv. pose proof (checkBuild_normalize_valid v Hv) as Hn.
    unfold phiA. destruct (fuelOf m) as [| F] eqn:HF.
    - simpl in Hn. congruence.
    - simpl in Hn. rewrite Hinv in Hn.
      rewrite (depthF_stable m F (repair1 m v) Hn (S F)) by lia.
      change (depthF m (S F) v) with (if allValid m v then 0 else S (depthF m F (repair1 m v))).
      rewrite Hinv. lia.
  Qed.

  (* Machine.Apply lands on a valid state from every state in the box. *)
  Theorem checkBuild_step_valid :
    forall e v, In v (box (doms m)) -> allValid m (stepI m e v) = true.
  Proof.
    intros e v Hv. unfold stepI, stepG. apply checkBuild_normalize_valid.
    apply box_iff. destruct (evalP (mins m) v (fst (evAt m e))); [apply applyT_pres |];
      apply box_iff; exact Hv.
  Qed.

  Lemma stepI_in_box : forall e v, In v (box (doms m)) -> In (stepI m e v) (box (doms m)).
  Proof. intros e v Hv. apply box_iff. apply stepG_pres. apply box_iff. exact Hv. Qed.

  Lemma ccA_listed : forall a b v, In (a, b) (pairsA m P) ->
    In v (box (doms m)) -> inDA m v = true ->
    stepI m a (stepI m b v) = stepI m b (stepI m a v).
  Proof.
    intros a b v Hin Hv HD. destruct checkBuild_parts as [_ [_ [_ [_ Hc]]]].
    unfold ccA in Hc. rewrite forallb_forall in Hc. specialize (Hc v Hv).
    rewrite HD in Hc. simpl in Hc. rewrite forallb_forall in Hc.
    apply valeqb_eq. exact (Hc (a, b) Hin).
  Qed.

  (* CC on Build's domain, for every declared-independent pair. *)
  Theorem checkBuild_commute :
    forall a b v, indepA m P a b -> In v (box (doms m)) -> inDA m v = true ->
    stepI m a (stepI m b v) = stepI m b (stepI m a v).
  Proof.
    intros a b v Hab Hv HD.
    pose proof (fun a b H => ccA_listed a b v H Hv HD) as Hc.
    unfold indepA in Hab. unfold pairsA in Hc. destruct P as [l |].
    - destruct Hab as [Hab | Hba]; [apply Hc, Hab | symmetry; apply Hc, Hba].
    - destruct Hab as [Ha Hb].
      destruct (Nat.lt_trichotomy a b) as [Hlt | [-> | Hgt]].
      + apply Hc, allPairs_in; assumption.
      + reflexivity.
      + symmetry. apply Hc, allPairs_in; assumption.
  Qed.

  (* The runtime guarantee, from the rules: from a valid state or the zero state,
     event sequences that differ only by reordering declared-independent events
     reach the same state. *)
  Theorem checkBuild_converges :
    forall es1 es2, tequiv (indepA m P) es1 es2 -> Forall (fun e => e < length (evs m)) es1 ->
    forall v, In v (box (doms m)) -> inDA m v = true -> runT (stepI m) es1 v = runT (stepI m) es2 v.
  Proof.
    intros es1 es2 Hte Hev v Hv HD.
    apply (run_tequiv (stepI m) (indepA m P) (fun e => e < length (evs m))
             (fun s => In s (box (doms m)) /\ allValid m s = true)
             (fun s => In s (box (doms m)) /\ inDA m s = true)); try assumption.
    - intros s [Hb Hs]. split; [exact Hb |]. unfold inDA. rewrite Hs. reflexivity.
    - intros e s _ [Hb _]. split; [apply stepI_in_box, Hb | apply checkBuild_step_valid, Hb].
    - intros a b s _ _ Hab [Hb Hs]. apply checkBuild_commute; assumption.
    - split; assumption.
  Qed.

  Theorem checkBuild_converges_all :
    P = None ->
    forall es1 es2, Permutation es1 es2 -> Forall (fun e => e < length (evs m)) es1 ->
    forall v, In v (box (doms m)) -> inDA m v = true -> runT (stepI m) es1 v = runT (stepI m) es2 v.
  Proof.
    intros HP es1 es2 Hp Hev v Hv HD. apply checkBuild_converges; [| exact Hev | exact Hv | exact HD].
    apply (perm_tequiv_total (indepA m P) (fun e => e < length (evs m))); [| exact Hp | exact Hev].
    intros a b Ha Hb. unfold indepA. rewrite HP. split; assumption.
  Qed.

  (* The fragment guarantees carry over unchanged. *)
  Theorem checkBuild_no_overflow :
    forall e, In e (exprsM m) -> forall e', In e' (subexprs e) ->
    forall v, In v (box (doms m)) -> (Z.abs (evalE (mins m) v e') <= maxAbs)%Z.
  Proof.
    intros e He e' Hsub v Hv. destruct checkBuild_parts as [Hb _].
    unfold bounded in Hb. rewrite forallb_forall in Hb.
    specialize (Hb e He). apply Z.leb_le in Hb.
    pose proof (evalE_bnd m v e' Hv). pose proof (subexprs_bnd m e e' Hsub). lia.
  Qed.

  Theorem checkBuild_binary_writes_exact :
    forall t, In t (transformsM m) ->
    forall i e, In (i, e) t -> nth i (doms m) 0 = 2 -> nth i (mins m) 0%Z = 0%Z ->
    forall v s, In v (box (doms m)) ->
      setClamped m i (evalE (mins m) v e) s =
      wr i (if Z.eqb (evalE (mins m) v e) 0 then 0 else 1) s.
  Proof.
    intros t Ht i e Hin Hd Hm v s Hv. destruct checkBuild_parts as [_ [Hs _]].
    unfold signSafe in Hs. rewrite forallb_forall in Hs. specialize (Hs t Ht).
    unfold signSafeT in Hs. rewrite forallb_forall in Hs. specialize (Hs (i, e) Hin).
    simpl in Hs. unfold binaryVar in Hs. rewrite Hd, Hm in Hs. simpl in Hs.
    apply Z.leb_le in Hs.
    pose proof (evalE_range m v e Hv) as [Hlo _].
    unfold setClamped. rewrite Hm.
    assert (Hd1 : nth i (doms m) 1 = 2).
    { destruct (Nat.lt_ge_cases i (length (doms m))) as [Hi | Hi].
      - rewrite <- Hd. apply nth_indep. exact Hi.
      - rewrite (nth_overflow (doms m) 0) in Hd by exact Hi. discriminate. }
    rewrite Hd1. f_equal. apply clamp_binary_is_bool. lia.
  Qed.
End CheckBuild.
