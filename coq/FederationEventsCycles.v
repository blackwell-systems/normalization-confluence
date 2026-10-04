(* FederationEventsCycles.v: event-interleaving convergence for MONOTONE CYCLIC federations,
   mechanized axiom-free.

   FederationEvents.v handles acyclic federations only: its per-edge conditions C1 and C2 are
   stated against a topological order, and its proofs solve the repair equations source-first.
   On a cycle a target's local state feeds back into its own sources, the repair equations have
   several solutions (bottom_matters below: a non-least fixed point exists), and no per-edge
   condition is meaningful. This file proves the result that does hold.

   Model (faithful to gsm's FedMachine.normalizeCyclic, federation_machine.go, and to the
   visited-states verification of federation_monotone.go on fix/monotone-cycles-visited-states).
   A federated state is a pair (l, h): l the local (non-shared) parts of every component, h the
   values of every shared (morphism-controlled) variable.
     - rho1 : phase 1, every component's own normalizer (Machine.Normalize).
     - F l  : the synchronous repair operator on shared values for fixed locals l (F_L).
     - u l j: the repair of target j alone (one coordinate update of F l; m.repair(out, j)).
     - ts   : the order in which normalizeCyclic sweeps the targets (component index order).
     - le, bot, rank, height: the finite lattice of shared-value assignments, ordered
              componentwise, with bottom "all raw 0" and a rank bounded by height (the sum of
              raw values in gsm).
   Hypotheses are exactly those of Chaotic.v (u_incr, u_sound, all_fixed) plus monotonicity of
   the coordinate updates (u_mono) and "a fixed point of F is fixed by every u" (u_fixed); they
   follow from F_L monotone for coordinate updates, which is what verifyMonotoneVisited checks
   over every state the iteration visits (valid locals with ANY shared values).
     Ncyc t = (l, kleene l K bot) with l the locals of rho1 t: reset every shared variable to
              bottom, then sweep the targets until a sweep changes nothing (the "changed" test),
              at most K rounds (kleeneCap). Modeling notes: gsm stops after a sweep that changed
              nothing; kleene tests stability first, which returns the same state. gsm panics at
              the cap; here K > height makes the cap unreachable (proved, not assumed), and gsm's
              monotoneChainBound (2 + the sum of the shared domains) exceeds the height (the sum
              of domain - 1).
     A governed event step is step e = Ncyc o (ev e): FedMachine.Apply (component Apply, then
     Normalize). ev is an arbitrary function on federated states, so events may read shared
     values (feedback).

   Results.
     cyc_N_lfp / cyc_N_unique : Ncyc t is the least fixed point of F (locals of rho1 t), and the
        only one: the normal form is a well-defined function, whatever the sweep order
        (cyc_sweep_order_independent). Chaotic.v covers arbitrary fair asynchronous schedules.
     cyc_N_idem : Ncyc is idempotent (given that phase 1 fixes valid states and the least fixed
        point is valid, which gsm checks at Build and at run time).
     THE GLOBAL CONDITION. GC s0: for every state s reachable from s0 by governed steps and every
        federated-independent pair a, b (different registries, or declared independent on one
        registry), step a (step b s) = step b (step a s); that is, the two events commute AFTER
        FULL RE-NORMALIZATION, on reachable federated states.
     gc_iff / cyc_events_converge_iff : GC s0 holds iff every two trace-equivalent event
        sequences reach the same state from s0. Sufficiency is Trace.run_tequiv with domain
        "reachable from s0"; necessity takes the one-swap pair at the failing state. So GC is
        not merely sufficient: it is the exact condition, for cycles and (FederationEventsConverse
        acyclic_gc_iff) for the acyclic machine alike. gc_image is the variant over N's whole
        image (every normalized state), which is what a check without a fixed start can verify.
     cyc_instance : non-vacuity. A two-registry CYCLE (A's shared flag is fed by B, B's by A)
        whose repair is monotone on a finite lattice, with local raise/clear events on both
        registries: every hypothesis is discharged, the least fixed point is computed, and every
        pair of trace-equivalent sequences converges from every start.
     bottom_matters : on that cycle, with both alarms clear, "both shared flags set" is a fixed
        point of the repair, but Ncyc returns the least one (both clear). The acyclic argument
        (unique solution of the repair equations) is unavailable on a cycle.
     cyc_counterexample : the same cycle with an event LatchA that copies A's shared flag (fed by
        B) into A's local alarm. GC fails at the start, and LatchA;RaiseB and RaiseB;LatchA
        (one allowed swap apart) end in different federated states.

   Relation to the acyclic theory (FederationEventsConverse.v): there the same global condition
   (GCF) is equivalent to convergence, implied by static C1 + C2, and equivalent to C1 + C2
   restricted to reachable witnesses. On a cycle there is no per-edge reduction; the global
   condition is checked on reachable normal forms. Non-monotone cycles remain excluded by
   design: their repair has no unique least fixed point reached from bottom, so there is no
   normal form for events to commute after; gsm routes them to coordination. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.Federation.
Import ListNotations.

(* ======================================================================================= *)
(* Part 1. The global condition, for any federated normalizer.                              *)
(* ======================================================================================= *)

Section Global.
  Variable S E : Type.
  Variable Nf : S -> S.          (* the federated normalizer *)
  Variable ev : E -> S -> S.     (* the local event step (component Apply) *)
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.   (* declared independence within a registry *)

  Definition gstep (e : E) (s : S) : S := Nf (ev e s).
  Definition grun (es : list E) (s : S) : S := runT gstep es s.
  Definition Ifd (a b : E) : Prop := reg a <> reg b \/ I a b.

  (* The global condition: independent events commute after full re-normalization, at every
     state reachable from s0. *)
  Definition GC (s0 : S) : Prop :=
    forall p a b, Ifd a b -> gstep a (gstep b (grun p s0)) = gstep b (gstep a (grun p s0)).

  Definition Converges (s0 : S) : Prop :=
    forall es1 es2, tequiv Ifd es1 es2 -> grun es1 s0 = grun es2 s0.

  Lemma grun_snoc : forall p e s, grun (p ++ [e]) s = gstep e (grun p s).
  Proof. intros. unfold grun. rewrite runT_app. reflexivity. Qed.

  Theorem gc_sufficient : forall s0, GC s0 -> Converges s0.
  Proof.
    intros s0 Hg es1 es2 H.
    set (D := fun s => exists p, s = grun p s0).
    apply (run_tequiv gstep Ifd (fun _ => True) D D).
    - auto.
    - intros e s _ [p ->]. exists (p ++ [e]). symmetry. apply grun_snoc.
    - intros a b s _ _ Hab [p ->]. apply Hg. exact Hab.
    - exact H.
    - apply Forall_forall. auto.
    - exists []. reflexivity.
  Qed.

  Theorem gc_necessary : forall s0, Converges s0 -> GC s0.
  Proof.
    intros s0 Hc p a b Hab.
    pose proof (Hc _ _ (teq_swap Ifd p a b [] Hab)) as H.
    unfold grun in H. rewrite !runT_app in H. symmetry. exact H.
  Qed.

  Theorem gc_iff : forall s0, GC s0 <-> Converges s0.
  Proof. intros s0. split; [apply gc_sufficient | apply gc_necessary]. Qed.

  (* Variant without a fixed start: commutation on the whole image of the normalizer gives
     convergence from every normalized state. *)
  Lemma grun_image : forall p t, exists t', grun p (Nf t) = Nf t' \/ (p = [] /\ t' = t).
  Proof.
    induction p as [| e p IH]; intros t.
    - exists t. right. split; reflexivity.
    - destruct (IH (ev e (Nf t))) as [t' [H | [-> ->]]].
      + exists t'. left. exact H.
      + exists (ev e (Nf t)). left. reflexivity.
  Qed.

  Theorem gc_image :
    (forall t a b, Ifd a b -> gstep a (gstep b (Nf t)) = gstep b (gstep a (Nf t))) ->
    forall t, Converges (Nf t).
  Proof.
    intros H t. apply gc_sufficient. intros p a b Hab.
    destruct (grun_image p t) as [t' [E' | [-> _]]].
    - rewrite E'. apply H. exact Hab.
    - apply H. exact Hab.
  Qed.
End Global.

(* ======================================================================================= *)
(* Part 2. gsm's cyclic normalizer: Kleene sweeps from bottom over visited states.          *)
(* ======================================================================================= *)

Section Cyclic.
  Variables Loc Sh : Type.
  Variable le : Sh -> Sh -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable bot : Sh.
  Hypothesis bot_least : forall x, le bot x.
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, le x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.

  Variable F : Loc -> Sh -> Sh.               (* synchronous repair, locals fixed *)
  Variable u : Loc -> nat -> Sh -> Sh.        (* repair of one target *)

  Definition sound (l : Loc) (x : Sh) : Prop := le x (F l x).
  Hypothesis u_incr : forall l j x, sound l x -> le x (u l j x).
  Hypothesis u_sound : forall l j x, sound l x -> sound l (u l j x).
  Hypothesis u_mono : forall l j x y, le x y -> le (u l j x) (u l j y).
  Hypothesis u_fixed : forall l j x, F l x = x -> u l j x = x.

  (* A sweep order covers the targets when "no target changes" means "F-fixed". *)
  Definition Cover (js : list nat) : Prop :=
    forall l x, (forall j, In j js -> u l j x = x) -> F l x = x.

  Variable rho1 : Loc * Sh -> Loc * Sh.       (* phase 1 *)
  Variable K : nat.                            (* kleeneCap *)
  Hypothesis K_big : height < K.

  Fixpoint sweep (l : Loc) (js : list nat) (x : Sh) : Sh :=
    match js with [] => x | j :: r => sweep l r (u l j x) end.

  Definition stable_dec (l : Loc) (js : list nat) (x : Sh) :
    {forall j, In j js -> u l j x = x} + {exists j, In j js /\ u l j x <> x}.
  Proof.
    induction js as [| a js IH].
    - left. intros j [].
    - destruct (sh_eq_dec (u l a x) x) as [Ea | Na].
      + destruct IH as [Hs | Hn].
        * left. intros j [<- | Hj]; [exact Ea | apply Hs; exact Hj].
        * right. destruct Hn as [j [Hj Hn]]. exists j. split; [right; exact Hj | exact Hn].
      + right. exists a. split; [left; reflexivity | exact Na].
  Defined.

  Fixpoint kleene (l : Loc) (js : list nat) (n : nat) (x : Sh) : Sh :=
    match n with
    | 0 => x
    | S n' => if stable_dec l js x then x else kleene l js n' (sweep l js x)
    end.

  (* gsm's FedMachine.Normalize on a cyclic network, sweeping in the order js. *)
  Definition Ncyc_with (js : list nat) (t : Loc * Sh) : Loc * Sh :=
    (fst (rho1 t), kleene (fst (rho1 t)) js K bot).

  Lemma rank_mono : forall x y, le x y -> rank x <= rank y.
  Proof.
    intros x y H. destruct (sh_eq_dec x y) as [-> | Ne]; [lia |].
    apply Nat.lt_le_incl. apply rank_strict; assumption.
  Qed.

  (* The iteration invariant: below its image, below every fixed point. *)
  Definition Pinv (l : Loc) (x : Sh) : Prop := sound l x /\ forall p, F l p = p -> le x p.

  Lemma Pinv_bot : forall l, Pinv l bot.
  Proof. intros l. split; [apply bot_least | intros; apply bot_least]. Qed.

  Lemma u_Pinv : forall l j x, Pinv l x -> Pinv l (u l j x).
  Proof.
    intros l j x [Hs Hb]. split; [apply u_sound; exact Hs |].
    intros p Hp. rewrite <- (u_fixed l j p Hp). apply u_mono. apply Hb. exact Hp.
  Qed.

  Lemma sweep_props : forall l js x, Pinv l x -> Pinv l (sweep l js x) /\ le x (sweep l js x).
  Proof.
    intros l js. induction js as [| a js IH]; intros x Hx; [split; [exact Hx | apply le_refl] |].
    simpl. destruct (IH (u l a x) (u_Pinv l a x Hx)) as [P L]. split; [exact P |].
    eapply le_trans; [apply u_incr; exact (proj1 Hx) | exact L].
  Qed.

  Lemma sweep_strict : forall l js x, Pinv l x -> (exists j, In j js /\ u l j x <> x) ->
    rank x < rank (sweep l js x).
  Proof.
    intros l js. induction js as [| a js IH]; intros x Hx [j [Hj Hn]]; [destruct Hj |].
    simpl. destruct (sh_eq_dec (u l a x) x) as [Ea | Na].
    - rewrite Ea. apply IH; [exact Hx |].
      destruct Hj as [<- | Hj]; [contradiction | exists j; split; assumption].
    - assert (R1 : rank x < rank (u l a x)).
      { apply rank_strict; [apply u_incr; exact (proj1 Hx) | intro H; apply Na; symmetry; exact H]. }
      pose proof (rank_mono _ _ (proj2 (sweep_props l js (u l a x) (u_Pinv l a x Hx)))). lia.
  Qed.

  Lemma kleene_spec : forall l js n x, Pinv l x -> height < rank x + n ->
    Pinv l (kleene l js n x) /\ forall j, In j js -> u l j (kleene l js n x) = kleene l js n x.
  Proof.
    intros l js n. induction n as [| n IH]; intros x Hx Hr.
    - pose proof (rank_bound x). lia.
    - simpl. destruct (stable_dec l js x) as [Hs | Hn]; [split; assumption |].
      apply IH; [apply (proj1 (sweep_props l js x Hx)) |].
      pose proof (sweep_strict l js x Hx Hn). lia.
  Qed.

  (* Headline: the cyclic normal form is the least fixed point of the repair, for any covering
     sweep order. *)
  Theorem cyc_N_lfp : forall js, Cover js -> forall t,
    fst (Ncyc_with js t) = fst (rho1 t) /\ is_lfp le (F (fst (rho1 t))) (snd (Ncyc_with js t)).
  Proof.
    intros js Hcov t. split; [reflexivity |]. simpl.
    destruct (kleene_spec (fst (rho1 t)) js K bot (Pinv_bot _)) as [[_ Hb] Hf];
      [pose proof (rank_bound bot); lia |].
    split.
    - unfold fixed_point. apply Hcov. exact Hf.
    - intros x Hx. apply Hb. exact Hx.
  Qed.

  Theorem cyc_N_unique : forall js, Cover js -> forall t m,
    is_lfp le (F (fst (rho1 t))) m -> Ncyc_with js t = (fst (rho1 t), m).
  Proof.
    intros js Hcov t m Hm. destruct (cyc_N_lfp js Hcov t) as [_ H].
    unfold Ncyc_with. f_equal. exact (lfp_unique le le_antisym _ _ _ H Hm).
  Qed.

  Theorem cyc_sweep_order_independent : forall js1 js2, Cover js1 -> Cover js2 ->
    forall t, Ncyc_with js1 t = Ncyc_with js2 t.
  Proof.
    intros js1 js2 H1 H2 t. destruct (cyc_N_lfp js2 H2 t) as [_ H].
    rewrite (cyc_N_unique js1 H1 t _ H). reflexivity.
  Qed.

  (* Idempotence: phase 1 fixes valid states, and the least fixed point is valid (gsm checks
     every image valid at Build, and panics on an invalid fixed point at run time). *)
  Variable Valid : Loc * Sh -> Prop.
  Hypothesis rho1_valid : forall s, Valid s -> rho1 s = s.
  Hypothesis lfp_valid : forall t m, is_lfp le (F (fst (rho1 t))) m -> Valid (fst (rho1 t), m).

  Theorem cyc_N_idem : forall js, Cover js -> forall t,
    Ncyc_with js (Ncyc_with js t) = Ncyc_with js t.
  Proof.
    intros js Hcov t.
    assert (Hv : Valid (Ncyc_with js t))
      by (unfold Ncyc_with; apply lfp_valid; exact (proj2 (cyc_N_lfp js Hcov t))).
    unfold Ncyc_with at 1. rewrite (rho1_valid _ Hv). reflexivity.
  Qed.

  (* Headline: governed event steps step e = Ncyc o (ev e) on a monotone cyclic federation
     converge on all trace-equivalent sequences from s0 exactly when the global condition
     holds from s0. *)
  Theorem cyc_events_converge_iff :
    forall js (E : Type) (ev : E -> Loc * Sh -> Loc * Sh) (reg : E -> nat) (I : E -> E -> Prop) s0,
      Cover js ->
      (GC (Loc * Sh) E (Ncyc_with js) ev reg I s0 <->
       Converges (Loc * Sh) E (Ncyc_with js) ev reg I s0).
  Proof. intros. apply gc_iff. Qed.
End Cyclic.

(* ======================================================================================= *)
(* Part 3. A concrete monotone CYCLE: two registries, each one's shared flag fed by the other. *)
(* Locals (la, lb): each registry's own alarm. Shared (sa, sb): sa is A's copy of whether an *)
(* alarm is up, fed by B (lb || sb); sb is B's copy, fed by A (la || sa). A -> B -> A.       *)
(* ======================================================================================= *)

Definition B2 : Type := (bool * bool)%type.

Definition cle (x y : B2) : Prop := implb (fst x) (fst y) = true /\ implb (snd x) (snd y) = true.
Definition cbot : B2 := (false, false).
Definition crank (x : B2) : nat := (if fst x then 1 else 0) + (if snd x then 1 else 0).

Definition ceq_dec : forall x y : B2, {x = y} + {x <> y}.
Proof. decide equality; apply bool_dec. Defined.

Definition cF (l : B2) (x : B2) : B2 := (snd l || snd x, fst l || fst x).

Definition cu (l : B2) (j : nat) (x : B2) : B2 :=
  match j with
  | 0 => (fst (cF l x), snd x)
  | 1 => (fst x, snd (cF l x))
  | _ => x
  end.

Definition cts : list nat := [0; 1].
Definition crho1 (s : B2 * B2) : B2 * B2 := s.
Definition cValid (_ : B2 * B2) : Prop := True.

Definition cN : B2 * B2 -> B2 * B2 := Ncyc_with B2 B2 cbot ceq_dec cu crho1 3 cts.

Ltac bf := repeat match goal with
  | x : B2 |- _ => destruct x
  | x : B2 * B2 |- _ => destruct x
  | b : bool |- _ => destruct b
  end.

Lemma cle_refl : forall x, cle x x. Proof. intros; bf; split; reflexivity. Qed.
Lemma cle_trans : forall x y z, cle x y -> cle y z -> cle x z.
Proof. intros x y z; bf; unfold cle; simpl; intuition congruence. Qed.
Lemma cle_antisym : forall x y, cle x y -> cle y x -> x = y.
Proof. intros x y; bf; unfold cle; simpl; intuition congruence. Qed.
Lemma cbot_least : forall x, cle cbot x. Proof. intros; bf; split; reflexivity. Qed.
Lemma crank_strict : forall x y, cle x y -> x <> y -> crank x < crank y.
Proof. intros x y; bf; unfold cle, crank; simpl; intuition (try congruence; try lia). Qed.
Lemma crank_bound : forall x, crank x <= 2. Proof. intros; bf; unfold crank; simpl; lia. Qed.

Lemma cu_incr : forall l j x, sound B2 B2 cle cF l x -> cle x (cu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, cu, cF; simpl; intuition. Qed.
Lemma cu_sound : forall l j x, sound B2 B2 cle cF l x -> sound B2 B2 cle cF l (cu l j x).
Proof. intros l [| [| j]] x; bf; unfold sound, cle, cu, cF; simpl; intuition. Qed.
Lemma cu_mono : forall l j x y, cle x y -> cle (cu l j x) (cu l j y).
Proof. intros l [| [| j]] x y; bf; unfold cle, cu, cF; simpl; intuition. Qed.
Lemma cu_fixed : forall l j x, cF l x = x -> cu l j x = x.
Proof. intros l [| [| j]] x; bf; unfold cu, cF; simpl; intro H; congruence. Qed.
Lemma cts_cover : Cover B2 B2 cF cu cts.
Proof.
  intros l x H. pose proof (H 0 (or_introl eq_refl)) as H0.
  pose proof (H 1 (or_intror (or_introl eq_refl))) as H1.
  revert H0 H1. bf; unfold cu, cF; simpl; intros H0 H1; congruence.
Qed.

Lemma cN_lfp : forall t, fst (cN t) = fst t /\ is_lfp cle (cF (fst t)) (snd (cN t)).
Proof.
  apply (cyc_N_lfp B2 B2 cle cle_refl cle_trans cbot cbot_least crank crank_strict 2 crank_bound
           ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed crho1 3 ltac:(lia) cts cts_cover).
Qed.

Lemma cN_idem : forall t, cN (cN t) = cN t.
Proof.
  apply (cyc_N_idem B2 B2 cle cle_refl cle_trans cbot cbot_least crank crank_strict 2
           crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed crho1 3 ltac:(lia) cValid).
  - intros; reflexivity.
  - intros; exact I.
  - exact cts_cover.
Qed.

(* Positive alphabet: raise and clear each registry's own alarm. *)
Inductive pev : Type := RaiseA | ClearA | RaiseB | ClearB.

Definition preg (e : pev) : nat := match e with RaiseA | ClearA => 0 | _ => 1 end.

Definition pstep (e : pev) (s : B2 * B2) : B2 * B2 :=
  match e, s with
  | RaiseA, ((_, lb), h) => ((true, lb), h)
  | ClearA, ((_, lb), h) => ((false, lb), h)
  | RaiseB, ((la, _), h) => ((la, true), h)
  | ClearB, ((la, _), h) => ((la, false), h)
  end.

Definition pI (_ _ : pev) : Prop := False.

(* Non-vacuity: every hypothesis of the cyclic development is discharged on a cycle (A feeds B, B feeds A),
   the normal form is the least fixed point (computed), and every pair of trace-equivalent
   event sequences converges from every start. *)
Theorem cyc_instance :
  (forall t, is_lfp cle (cF (fst t)) (snd (cN t))) /\
  (forall t m, is_lfp cle (cF (fst t)) m -> cN t = (fst t, m)) /\
  (forall t, cN (cN t) = cN t) /\
  cN ((true, false), (false, false)) = ((true, false), (true, true)) /\
  (forall s0, GC (B2 * B2) pev cN pstep preg pI s0) /\
  (forall s0, Converges (B2 * B2) pev cN pstep preg pI s0).
Proof.
  assert (Hg : forall s0, GC (B2 * B2) pev cN pstep preg pI s0).
  { intros s0 p a b Hab. set (s := grun _ _ cN pstep p s0). clearbody s.
    destruct Hab as [Ne | []].
    destruct a, b; simpl in Ne; try (exfalso; apply Ne; reflexivity);
      bf; reflexivity. }
  split; [intro t; apply (proj2 (cN_lfp t)) |].
  split.
  { intros t m Hm.
    exact (cyc_N_unique B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank crank_strict 2
             crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed crho1 3 ltac:(lia) cts
             cts_cover t m Hm). }
  split; [exact cN_idem |].
  split; [reflexivity |].
  split; [exact Hg |].
  intro s0. apply gc_sufficient. apply Hg.
Qed.

(* On the cycle the least fixed point is not the only one: with both alarms clear, "both shared
   flags set" also satisfies every repair equation. Ncyc returns the least one. *)
Theorem bottom_matters :
  cF (false, false) (true, true) = (true, true) /\
  cN ((false, false), (true, true)) = ((false, false), (false, false)).
Proof. split; reflexivity. Qed.

(* Counterexample: LatchA copies A's shared flag (fed by B) into A's local alarm. *)
Inductive xev : Type := LatchA | RaiseB'.

Definition xreg (e : xev) : nat := match e with LatchA => 0 | RaiseB' => 1 end.

Definition xstep (e : xev) (s : B2 * B2) : B2 * B2 :=
  match e, s with
  | LatchA, ((la, lb), (sa, sb)) => ((la || sa, lb), (sa, sb))
  | RaiseB', ((la, _), h) => ((la, true), h)
  end.

Definition xI (_ _ : xev) : Prop := False.

Definition xs0 : B2 * B2 := ((false, false), (false, false)).

Theorem cyc_counterexample :
  (forall t, is_lfp cle (cF (fst t)) (snd (cN t))) /\
  tequiv (Ifd xev xreg xI) [LatchA; RaiseB'] [RaiseB'; LatchA] /\
  grun (B2 * B2) xev cN xstep [LatchA; RaiseB'] xs0 = ((false, true), (true, true)) /\
  grun (B2 * B2) xev cN xstep [RaiseB'; LatchA] xs0 = ((true, true), (true, true)) /\
  ~ GC (B2 * B2) xev cN xstep xreg xI xs0 /\
  ~ Converges (B2 * B2) xev cN xstep xreg xI xs0.
Proof.
  assert (Ht : tequiv (Ifd xev xreg xI) [LatchA; RaiseB'] [RaiseB'; LatchA]).
  { apply (teq_swap _ [] LatchA RaiseB' []). left. discriminate. }
  assert (Hn : ~ Converges (B2 * B2) xev cN xstep xreg xI xs0).
  { intro H. pose proof (H _ _ Ht) as Hd. discriminate Hd. }
  split; [intro t; apply (proj2 (cN_lfp t)) |].
  split; [exact Ht |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| exact Hn].
  intro H. apply Hn. apply gc_sufficient. exact H.
Qed.
