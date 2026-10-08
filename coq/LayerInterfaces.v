(* LayerInterfaces.v: the interfaces between the three layers of the framework (A, the execution
   algebra, PresentedExecution.v; B, the constraint algebra, TransportCSP.v; C, settlement
   dynamics as fair recurrence, CanonicalRecurrence.v). Axiom-free. A, B and C are used as they
   are; nothing in them is changed to make an interface fit.

   The objection under test: "A, B and C are three unrelated classical theories stapled
   together." Three interface hypotheses were attacked; each result below is an exact statement,
   a counterexample, or both. Docs: coq/docs/interfaces.md.

   Part 1. Descent (the elementary shape, stated once). For N : X -> X and a predicate P:
     DescendsOn P N e  := forall x, P x -> N (e (N x)) = N (e x)
     RespectsOn P N e  := e respects the kernel of N on P
     FactorsOn P N e   := N o e factors through N on P
     CommutesOn P N e  := N (e x) = e (N x) on P (strict commutation)
     descends_iff_respects, descends_iff_factors: the three are equivalent when P is closed under
       N and N is idempotent on P. This is the textbook condition for an operation to be
       compatible with an equivalence (a congruence, in universal algebra); the content of each
       instance is the choice of N and P and the exactness of the condition there.
     commutes_descends: strict commutation implies descent. descends_word: descent of every step
       gives descent of every word.
   Part 2. Transition-level instances (one definition, three uses of N):
     state_descent_is_descends, state_descent_respects_recovered: A's state descent S
       (CanonicalExecution.StateDescent) is DescendsOn everywhere, event by event.
     cc2_is_descends: CC2 in its all-events form, N := rho_star (state_descent_iff_cc2).
     xu_is_descends, xu_iff_respects: FederationEvents.XU is DescendsOn on valid states with
       N := f (reg e) z, equivalently sig e respects the kernel of the repair (sig descends to the
       quotient by N). c1_is_descends, c1_iff_respects: C1 is the same on consistent states.
     candidate_is_commutes, candidate_implies_xu: Candidate is CommutesOn; strict naturality
       implies canonicalized naturality under Common.
     strict_not_necessary: on the supply federation XU holds, Candidate fails, and every
       reordering converges (FederationEvents.supply_instance, supply_converges).
   Part 3. The scale hierarchy. Finite histories: history_from_descent,
     path_history_from_descent (descent of every event makes history descent of the raw runs
     after N the same question as history descent of the governed runs; state_side_transfer).
     descent_not_history, history_not_descent: the two levels are independent.
     Infinite histories (layer C): C's N is an observation X -> C, and CanonSettles asks the
     trajectory N (x_t) to be eventually constant; it uses N only through the fiber of the target
     (canon_settles_fiber). trajectory_quotient, canon_settles_quotient_invariant: under
     transition-level descent (ObsRespects) the N-trajectory, hence canonical settlement, depends
     only on the N-image of the dynamics. trajectory_needs_descent: without descent it does not,
     and canonical settlement holds or fails independently of descent.
   Part 4. A-C, Newman as the bridge.
     newman_bridge: SN R c0 -> NFDec -> (PeaksJoin <-> CR) /\ (CR <-> UNF); cr_peaks, cr_unf: the
       converse directions need no termination.
     LStep: the moving steps of a layer-C system; nf_iff_stable: its normal forms are the
       settled states.
     fair_starves: under fair raw settlement (C2), every reachable moving loop starves a label
       (a label of js, never named by the loop, that moves every loop state).
     sn_iff_no_loop (finite X), fair_sn_exact: under C2, SN <-> no reachable starved loop.
     fair_newman: under C2 and no starved loop, local joinability <-> confluence <-> unique
       normal forms.
     four_point_fair_not_confluent: every peak joins, C2 holds, an unfair infinite run exists (its
       loop starves label 0), and confluence and unique normal forms fail; no canonical target
       settles. drop_starved_confluent: a starved loop with confluence (the condition is exact
       for termination, not for confluence). or_fair_newman: non-vacuity.
   Part 5. B-C, the fixed points are the B-solutions.
     erep_fixed_iff, edge_fixed_iff_section, edge_fixed_iff_csp, edge_fixed_exists_iff_csp:
       reading A, s is fixed by every edge repair iff it is a section iff a CSP solution.
     rupd_fixed_iff, rupd_fixed_iff_csp: reading B, the same for resolver repairs
       (SignedResolver.rupd) and merge networks (hsection_iff_csp).
     no_solution_no_settlement, singleton_iff_solution, canon_needs_solutions,
       settled_canon_exact, ghost_refutes, multistable: the same facts in C's vocabulary.
     flip2_unique_solution_livelock, negation_no_solution, no_solution_canon_settles,
       copyback_multistable, copyback_ghost_solution: the instances and the leak.
   Part 6. A-B, strict naturality on sections.
     natural_maps_sections, preserves_exact, square_necessary, natural_iff_edgewise,
       uniform_natural_is_unary_pol; natural_converse_fails and selfloop_square_not_necessary are
       the counterexamples to the naive converse. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.DistributedCycles NC.CohomologyGraph NC.CohomologyGeneral.
Require Import NC.CanonicalExecution NC.PresentedExecution NC.TransportCSP NC.SignedResolver.
Require Import NC.DistributedCyclesExact NC.CanonicalRecurrence.
Require NC.FederationEvents NC.GovernanceConverse NC.GovernanceWFConverse NC.RhoStar.
Import ListNotations.

(* ============================================================================================ *)
(* Part 1. Descent along an idempotent map, relativized to a predicate.                         *)
(* ============================================================================================ *)

Section Descent.
  Context {X : Type}.
  Variable P : X -> Prop.
  Variable N : X -> X.

  (* e descends along N on P: its canonical outcome is the same from x and from N x. *)
  Definition DescendsOn (e : X -> X) : Prop := forall x, P x -> N (e (N x)) = N (e x).
  (* e respects the kernel of N on P. *)
  Definition RespectsOn (e : X -> X) : Prop :=
    forall x y, P x -> P y -> N x = N y -> N (e x) = N (e y).
  (* N o e factors through N on P. *)
  Definition FactorsOn (e : X -> X) : Prop := exists g : X -> X, forall x, P x -> N (e x) = g (N x).
  (* Strict commutation on P. *)
  Definition CommutesOn (e : X -> X) : Prop := forall x, P x -> N (e x) = e (N x).

  Definition NClosed : Prop := forall x, P x -> P (N x).
  Definition NIdem : Prop := forall x, P x -> N (N x) = N x.

  Theorem descends_iff_respects : NClosed -> NIdem ->
    forall e, DescendsOn e <-> RespectsOn e.
  Proof.
    intros Hc Hi e. split.
    - intros H x y Px Py E. rewrite <- (H x Px), <- (H y Py), E. reflexivity.
    - intros H x Px. apply H; [apply Hc; exact Px | exact Px | apply Hi; exact Px].
  Qed.

  Theorem descends_iff_factors : NClosed -> NIdem ->
    forall e, DescendsOn e <-> FactorsOn e.
  Proof.
    intros Hc Hi e. split.
    - intros H. exists (fun y => N (e y)). intros x Px. symmetry. apply H. exact Px.
    - intros [g Hg] x Px. rewrite (Hg _ (Hc x Px)), (Hi x Px). symmetry. apply Hg. exact Px.
  Qed.

  (* Strict commutation implies descent; the converse fails (strict_not_necessary, below). *)
  Theorem commutes_descends : NClosed -> NIdem -> forall e, CommutesOn e -> DescendsOn e.
  Proof.
    intros Hc Hi e H x Px. rewrite (H _ (Hc x Px)), (Hi x Px). symmetry. apply H. exact Px.
  Qed.

  (* Descent composes along words: the finite-history consequence of transition-level descent. *)
  Definition wapply (w : list (X -> X)) (x : X) : X := fold_left (fun y e => e y) w x.

  Lemma wapply_snoc : forall w e x, wapply (w ++ [e]) x = e (wapply w x).
  Proof. intros w e x. unfold wapply. rewrite fold_left_app. reflexivity. Qed.

  Lemma wapply_closed : forall w, (forall e, In e w -> forall x, P x -> P (e x)) ->
    forall x, P x -> P (wapply w x).
  Proof.
    induction w as [| e w IH] using List.rev_ind; intros Hw x Px; [exact Px |].
    rewrite wapply_snoc. apply Hw; [apply in_or_app; right; left; reflexivity |].
    apply IH; [intros e' He'; apply Hw; apply in_or_app; left; exact He' | exact Px].
  Qed.

  Theorem descends_word : NClosed -> NIdem ->
    forall w, (forall e, In e w -> DescendsOn e /\ forall x, P x -> P (e x)) ->
    forall x, P x -> N (wapply w (N x)) = N (wapply w x).
  Proof.
    intros Hc Hi w. induction w as [| e w IH] using List.rev_ind; intros Hw x Px; [apply Hi; exact Px |].
    assert (He : DescendsOn e) by (apply Hw; apply in_or_app; right; left; reflexivity).
    assert (Hw' : forall e', In e' w -> DescendsOn e' /\ forall x, P x -> P (e' x))
      by (intros e' H'; apply Hw; apply in_or_app; left; exact H').
    assert (Cl : forall e', In e' w -> forall x, P x -> P (e' x)) by (intros e' H'; apply Hw'; exact H').
    rewrite !wapply_snoc.
    rewrite <- (He (wapply w (N x))) by (apply wapply_closed; [exact Cl | apply Hc; exact Px]).
    rewrite (IH Hw' x Px). apply He. apply wapply_closed; [exact Cl | exact Px].
  Qed.
End Descent.

(* ============================================================================================ *)
(* Part 2. Transition-level instances: state descent (S, CC2), C1 and XU, and Candidate.        *)
(* ============================================================================================ *)

(* A's state descent (CanonicalExecution.StateDescent) is DescendsOn with P everywhere true, one
   event at a time; state_descent_iff_respects_canon is descends_iff_respects at that instance. *)
Theorem state_descent_is_descends : forall {X Ev : Type} (N : X -> X) (act : Ev -> X -> X),
  StateDescent N act <-> forall e, DescendsOn (fun _ => True) N (act e).
Proof.
  intros X Ev N act. split.
  - intros H e x _. symmetry. apply H.
  - intros H e s. symmetry. apply (H e s I).
Qed.

Theorem state_descent_respects_recovered : forall {X Ev : Type} (N : X -> X) (act : Ev -> X -> X),
  (forall x, N (N x) = N x) ->
  (StateDescent N act <-> forall e, RespectsOn (fun _ => True) N (act e)).
Proof.
  intros X Ev N act Hi. rewrite state_descent_is_descends. split; intros H e.
  - apply (proj1 (descends_iff_respects _ N (fun x _ => I) (fun x _ => Hi x) (act e))). apply H.
  - apply (proj2 (descends_iff_respects _ N (fun x _ => I) (fun x _ => Hi x) (act e))). apply H.
Qed.

(* CC2 in its all-events form (state_descent_iff_cc2) is DescendsOn for N := rho_star. *)
Theorem cc2_is_descends :
  forall {State Event : Type} (apply : Event -> State -> State) (rho : State -> State)
    (valid : State -> Prop) (valid_dec : forall s, {valid s} + {~ valid s}) (Phi : State -> nat),
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  ((forall e, DescendsOn (fun _ => True) (RhoStar.rho_star rho valid valid_dec Phi) (apply e)) <->
   (forall s e, ~ valid s ->
      RhoStar.rho_star rho valid valid_dec Phi (apply e s) =
      RhoStar.rho_star rho valid valid_dec Phi (apply e (rho s)))).
Proof.
  intros State Event apply rho valid valid_dec Phi wfc.
  rewrite <- state_descent_is_descends. apply state_descent_iff_cc2. exact wfc.
Qed.

(* The federation (FederationEvents.v). N := f (reg e) z, the repair of the event's registry
   from valid source states z; idempotent on valid states by c_absorb, closed by c_m1. *)
Section Federation.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable o : list nat.
  Hypothesis HC : FederationEvents.Common V src f valid rho E reg sig o.

  Definition Inv := FederationEvents.Inv V valid.

  (* The states C1 quantifies over: valid and consistent (some valid image fixes them). *)
  Definition ConsAt (j : nat) (b : V) : Prop :=
    valid j b /\ exists z', Inv z' /\ b = f j z' b.

  Lemma fed_closed : forall j z, Inv z -> NClosed (valid j) (f j z).
  Proof. intros j z Hz b Hb. apply (FederationEvents.c_m1 _ _ _ _ _ _ _ _ _ HC); assumption. Qed.

  Lemma fed_idem : forall j z, Inv z -> NIdem (valid j) (f j z).
  Proof. intros j z Hz b Hb. apply (FederationEvents.c_absorb _ _ _ _ _ _ _ _ _ HC); assumption. Qed.

  Lemma cons_closed : forall j z, Inv z -> NClosed (ConsAt j) (f j z).
  Proof.
    intros j z Hz b [Hb _]. split; [apply fed_closed; assumption |].
    exists z. split; [exact Hz | symmetry; apply fed_idem; assumption].
  Qed.

  Lemma cons_idem : forall j z, Inv z -> NIdem (ConsAt j) (f j z).
  Proof. intros j z Hz b [Hb _]. apply fed_idem; assumption. Qed.

  (* XU is descent of every event step along its registry's repair, on valid states. *)
  Theorem xu_is_descends :
    FederationEvents.XU V f valid E reg sig <->
    forall e z, Inv z -> DescendsOn (valid (reg e)) (f (reg e) z) (sig e).
  Proof.
    split.
    - intros H e z Hz b Hb. apply H; assumption.
    - intros H e z b Hz Hb. apply H; assumption.
  Qed.

  (* ... equivalently, sig e respects the kernel of the repair on valid states: sig descends to
     the quotient of the valid states by f (reg e) z. *)
  Theorem xu_iff_respects :
    FederationEvents.XU V f valid E reg sig <->
    forall e z, Inv z -> RespectsOn (valid (reg e)) (f (reg e) z) (sig e).
  Proof.
    rewrite xu_is_descends. split; intros H e z Hz.
    - apply (proj1 (descends_iff_respects _ _ (fed_closed _ z Hz) (fed_idem _ z Hz) _)). apply H. exact Hz.
    - apply (proj2 (descends_iff_respects _ _ (fed_closed _ z Hz) (fed_idem _ z Hz) _)). apply H. exact Hz.
  Qed.

  (* C1 is the same descent on the consistent states only. *)
  Theorem c1_is_descends :
    FederationEvents.C1 V f valid E reg sig <->
    forall e z, Inv z -> DescendsOn (ConsAt (reg e)) (f (reg e) z) (sig e).
  Proof.
    split.
    - intros H e z Hz b [Hb [z' [Hz' E']]]. exact (H e z z' b Hz Hz' Hb E').
    - intros H e z z' b Hz Hz' Hb E'. apply (H e z Hz). split; [exact Hb | exists z'; tauto].
  Qed.

  Theorem c1_iff_respects :
    FederationEvents.C1 V f valid E reg sig <->
    forall e z, Inv z -> RespectsOn (ConsAt (reg e)) (f (reg e) z) (sig e).
  Proof.
    rewrite c1_is_descends. split; intros H e z Hz.
    - apply (proj1 (descends_iff_respects _ _ (cons_closed _ z Hz) (cons_idem _ z Hz) _)). apply H. exact Hz.
    - apply (proj2 (descends_iff_respects _ _ (cons_closed _ z Hz) (cons_idem _ z Hz) _)). apply H. exact Hz.
  Qed.

  (* Candidate is strict commutation, and strict commutation implies descent: Candidate -> XU. *)
  Theorem candidate_is_commutes :
    FederationEvents.Candidate V f valid E reg sig <->
    forall e z, Inv z -> CommutesOn (valid (reg e)) (f (reg e) z) (sig e).
  Proof.
    split.
    - intros H e z Hz b Hb. apply H; assumption.
    - intros H e z b Hz Hb. apply H; assumption.
  Qed.

  Theorem candidate_implies_xu :
    FederationEvents.Candidate V f valid E reg sig -> FederationEvents.XU V f valid E reg sig.
  Proof.
    intros Hc. apply xu_is_descends. intros e z Hz.
    apply (commutes_descends _ _ (fed_closed _ z Hz) (fed_idem _ z Hz)).
    apply candidate_is_commutes; assumption.
  Qed.
End Federation.

(* Strict naturality is unnecessarily strong: on the supply federation XU (descent) holds,
   Candidate (strict commutation) fails, and every reordering of events converges. *)
Theorem strict_not_necessary :
  FederationEvents.Common (bool * nat) FederationEvents.src2 FederationEvents.sp_f
    FederationEvents.sp_valid FederationEvents.sp_rho FederationEvents.sev FederationEvents.sp_reg
    FederationEvents.sp_sig [0; 1] /\
  (forall e z, Inv (bool * nat) FederationEvents.sp_valid z ->
     DescendsOn (FederationEvents.sp_valid (FederationEvents.sp_reg e))
       (FederationEvents.sp_f (FederationEvents.sp_reg e) z) (FederationEvents.sp_sig e)) /\
  ~ (forall e z, Inv (bool * nat) FederationEvents.sp_valid z ->
     CommutesOn (FederationEvents.sp_valid (FederationEvents.sp_reg e))
       (FederationEvents.sp_f (FederationEvents.sp_reg e) z) (FederationEvents.sp_sig e)) /\
  (forall es1 es2 s, Permutation es1 es2 ->
    FederationEvents.Inv (bool * nat) FederationEvents.sp_valid s ->
    FederationEvents.Cons (bool * nat) FederationEvents.sp_f [0; 1] s ->
    FederationEvents.feq (bool * nat)
      (FederationEvents.runF (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho
         FederationEvents.sev FederationEvents.sp_reg FederationEvents.sp_sig [0; 1] es1 s)
      (FederationEvents.runF (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho
         FederationEvents.sev FederationEvents.sp_reg FederationEvents.sp_sig [0; 1] es2 s)).
Proof.
  destruct FederationEvents.supply_instance as (Hc & Hx & _ & _ & _ & Hn).
  split; [exact Hc |]. split; [apply xu_is_descends; exact Hx |].
  split; [| exact FederationEvents.supply_converges].
  intro H. apply Hn. apply candidate_is_commutes. exact H.
Qed.

(* ============================================================================================ *)
(* Part 3. The scale hierarchy. Transition level (Parts 1, 2), finite histories (history        *)
(* descent), infinite histories (trajectories eventually constant in the quotient, layer C).    *)
(* ============================================================================================ *)

(* Finite histories. Transition-level descent of every event turns a history-descent question
   about the raw runs, read after N, into the same question about the governed runs from N s0
   (normalization_descent; state_side_transfer is the path-system form). *)
Theorem history_from_descent : forall {X Ev : Type} (N : X -> X) (act : Ev -> X -> X),
  (forall e, DescendsOn (fun _ => True) N (act e)) ->
  forall (EqH : list Ev -> list Ev -> Prop) s0,
    (forall h k, EqH h k -> N (rawrun act h s0) = N (rawrun act k s0)) <->
    (forall h k, EqH h k -> grun N act h (N s0) = grun N act k (N s0)).
Proof.
  intros X Ev N act HD EqH s0. apply state_descent_is_descends in HD.
  assert (K : forall w, N (rawrun act w s0) = grun N act w (N s0))
    by (intro w; apply normalization_descent; exact HD).
  split; intros H h k E; [rewrite <- !K | rewrite !K]; apply H; exact E.
Qed.

Theorem path_history_from_descent : forall {X Ev : Type} (N : X -> X) (act : Ev -> X -> X) (s0 : X),
  (forall e, DescendsOn (fun _ => True) N (act e)) ->
  forall (Adm : list Ev -> Prop) Gen (eqv : X -> X -> Prop),
    PInv Adm Gen (fun t => N (rawrun act t s0)) eqv <->
    PInv Adm Gen (fun t => grun N act t (N s0)) eqv.
Proof.
  intros X Ev N act s0 HD. apply state_side_transfer. apply state_descent_is_descends. exact HD.
Qed.

(* The two levels are independent. Descent without history descent: with N the identity every
   map descends, and two events that do not commute separate a reordering. *)
Definition hact (b : bool) (x : nat) : nat := if b then S x else 0.

Theorem descent_not_history :
  (forall b, DescendsOn (fun _ => True) (fun x : nat => x) (hact b)) /\
  Permutation [true; false] [false; true] /\
  rawrun hact [true; false] 0 <> rawrun hact [false; true] 0.
Proof.
  split; [intros b x _; reflexivity |]. split; [apply perm_swap |]. simpl. discriminate.
Qed.

(* History descent without descent: one event, so every reordering is the identity and history
   descent over Permutation holds, while the event does not respect N's kernel (N 1 = N 0). *)
Definition hN (x : nat) : nat := if Nat.leb x 1 then 0 else x.

Theorem history_not_descent :
  (forall x, hN (hN x) = hN x) /\
  (forall h k : list unit, Permutation h k -> forall s, hN (rawrun (fun _ => S) h s) = hN (rawrun (fun _ => S) k s)) /\
  ~ DescendsOn (fun _ => True) hN S.
Proof.
  split.
  { intro x. unfold hN. destruct (Nat.leb x 1) eqn:E; [reflexivity |]. rewrite E. reflexivity. }
  split.
  { intros h k Hp s. assert (L : length h = length k) by (apply Permutation_length; exact Hp).
    assert (Hu : forall l : list unit, l = repeat tt (length l))
      by (induction l as [| [] l IH]; [reflexivity | simpl; f_equal; exact IH]).
    rewrite (Hu h), (Hu k), L. reflexivity. }
  intro H. specialize (H 1 I). discriminate H.
Qed.

(* Infinite histories: layer C. C's N : X -> C is an observation and CanonSettles asks that the
   trajectory n |-> N (x_n) be eventually constant at c; it reads N only through the fiber of c. *)
Section Trajectory.
  Variable X : Type.
  Variable js : list nat.
  Variable C : Type.
  Variable N : X -> C.

  Theorem canon_settles_fiber : forall (u : nat -> X -> X) (C' : Type) (N' : X -> C') c c' s0,
    (forall x, N x = c <-> N' x = c') ->
    (CanonSettles X js u C N s0 c <-> CanonSettles X js u C' N' s0 c').
  Proof.
    intros u C' N' c c' s0 H. split; intros Hs sg Hf; destruct (Hs sg Hf) as [M HM]; exists M;
      intros n Hn; apply H; exact (HM n Hn).
  Qed.

  (* Transition-level descent for an observation: each step respects the kernel of N. *)
  Definition ObsRespects (u : nat -> X -> X) : Prop :=
    forall j x y, In j js -> N x = N y -> N (u j x) = N (u j y).

  (* Under descent, the N-trajectory depends only on the N-image of the dynamics and the start:
     it is a trajectory of the quotient dynamics. *)
  Theorem trajectory_quotient : forall u u',
    ObsRespects u -> (forall j x, In j js -> N (u' j x) = N (u j x)) ->
    forall sg, (forall n, In (sg n) js) -> forall s0 s0', N s0' = N s0 ->
    forall n, N (prs X u' sg n s0') = N (prs X u sg n s0).
  Proof.
    intros u u' Hr Ha sg Hsg s0 s0' E n. induction n as [| n IH]; [exact E |].
    cbn [prs]. rewrite (Ha _ _ (Hsg n)). apply Hr; [apply Hsg | exact IH].
  Qed.

  Theorem canon_settles_quotient_invariant : forall u u',
    ObsRespects u -> (forall j x, In j js -> N (u' j x) = N (u j x)) ->
    forall s0 s0' c, N s0' = N s0 ->
    (CanonSettles X js u C N s0 c <-> CanonSettles X js u' C N s0' c).
  Proof.
    intros u u' Hr Ha s0 s0' c E.
    assert (K : forall sg, Fair js sg -> forall n, N (prs X u' sg n s0') = N (prs X u sg n s0))
      by (intros sg [Hin _]; apply trajectory_quotient; assumption).
    split; intros Hs sg Hf; destruct (Hs sg Hf) as [M HM]; exists M; intros n Hn;
      unfold Fiber in *; [rewrite K | rewrite <- K]; auto.
  Qed.
End Trajectory.

(* Without descent the invariance fails: u and u' agree after N at every state, u settles in
   the fiber true from ta, u' leaves it for good. u does not respect N (N ta = N tb, but u keeps
   ta in the fiber and sends tb out of it). And C-settlement needs no descent: u' violates it
   too and still settles canonically, at false. *)
Inductive T3 : Type := ta | tb | tz.
Definition t3N (x : T3) : bool := match x with tz => false | _ => true end.
Definition t3u (_ : nat) (x : T3) : T3 := match x with ta => ta | _ => tz end.
Definition t3u' (_ : nat) (x : T3) : T3 := match x with ta => tb | _ => tz end.

Lemma t3u_ta : forall sg n, prs T3 t3u sg n ta = ta.
Proof. intros sg n. induction n as [| n IH]; [reflexivity |]. cbn [prs]. rewrite IH. reflexivity. Qed.

Lemma t3u'_late : forall sg n, 2 <= n -> prs T3 t3u' sg n ta = tz.
Proof.
  intros sg n Hn. induction n as [| n IH]; [lia |].
  destruct (Nat.eq_dec n 1) as [-> | Ne]; [reflexivity |]. cbn [prs]. rewrite IH by lia. reflexivity.
Qed.

Lemma t3_fair : Fair [0] (fun _ => 0).
Proof. split; [intro n; left; reflexivity | intros j n [<- | []]; exists n; split; [lia | reflexivity]]. Qed.

Theorem trajectory_needs_descent :
  (forall j x, t3N (t3u' j x) = t3N (t3u j x)) /\
  ~ ObsRespects T3 [0] bool t3N t3u /\
  CanonSettles T3 [0] t3u bool t3N ta true /\
  ~ CanonSettles T3 [0] t3u' bool t3N ta true /\
  ~ ObsRespects T3 [0] bool t3N t3u' /\
  CanonSettles T3 [0] t3u' bool t3N ta false.
Proof.
  split; [intros j []; reflexivity |].
  split; [intro H; specialize (H 0 ta tb (or_introl eq_refl) eq_refl); discriminate H |].
  split; [intros sg _; exists 0; intros n _; unfold Fiber; rewrite t3u_ta; reflexivity |].
  split.
  { intro H. destruct (H (fun _ => 0) t3_fair) as [M HM]. specialize (HM (M + 2) ltac:(lia)).
    unfold Fiber in HM. rewrite t3u'_late in HM by lia. discriminate HM. }
  split; [intro H; specialize (H 0 ta tb (or_introl eq_refl) eq_refl); discriminate H |].
  intros sg _. exists 2. intros n Hn. unfold Fiber. rewrite t3u'_late by exact Hn. reflexivity.
Qed.

(* ============================================================================================ *)
(* Part 4. A-C: Newman as the bridge, and what fair settlement can and cannot replace.          *)
(* ============================================================================================ *)

Section Bridge.
  Context {A : Type}.
  Variable R : A -> A -> Prop.
  Variable c0 : A.

  (* Unique normal forms below every reachable configuration. *)
  Definition UNF : Prop := forall x n1 n2, Reach R c0 x ->
    star R x n1 -> normal_form R n1 -> star R x n2 -> normal_form R n2 -> n1 = n2.
  (* Normality is decidable at reachable configurations. *)
  Definition NFDec : Prop := forall x, Reach R c0 x -> normal_form R x \/ exists y, R x y.

  Lemma sn_reach_nf : SN R c0 -> NFDec -> forall x, Reach R c0 x -> exists n, star R x n /\ normal_form R n.
  Proof.
    intros Hsn Hd x Hx. pose proof (GovernanceWFConverse.SN_star_closed R c0 x Hx Hsn) as Hacc.
    induction Hacc as [x _ IH].
    destruct (Hd x Hx) as [Nf | [y Hy]]; [exists x; split; [apply star_refl | exact Nf] |].
    destruct (IH y Hy) as [n [Sn Nn]]; [eapply star_trans; [exact Hx | apply star_one; exact Hy] |].
    exists n. split; [eapply star_step; [exact Hy | exact Sn] | exact Nn].
  Qed.

  (* The converse direction needs no termination: confluence joins every reachable peak. *)
  Theorem cr_peaks : CR R c0 -> PeaksJoin R c0.
  Proof.
    intros H x y z Hx Hy Hz. apply H; eapply star_trans; try exact Hx; apply star_one; assumption.
  Qed.

  Theorem cr_unf : CR R c0 -> UNF.
  Proof.
    intros H x n1 n2 Hx S1 N1 S2 N2.
    destruct (H n1 n2 (star_trans _ _ _ _ Hx S1) (star_trans _ _ _ _ Hx S2)) as [w [A1 A2]].
    rewrite (star_from_nf R n1 w N1 A1), (star_from_nf R n2 w N2 A2). reflexivity.
  Qed.

  (* Newman as the bridge: under termination, local joinability (at reachable peaks),
     confluence and unique normal forms coincide. *)
  Theorem newman_bridge : SN R c0 -> NFDec ->
    (PeaksJoin R c0 <-> CR R c0) /\ (CR R c0 <-> UNF).
  Proof.
    intros Hsn Hd. split; [split; [apply (proj2 (peak_exact R c0 Hsn)) | apply cr_peaks] |].
    split; [apply cr_unf |]. intros H y z Hy Hz.
    destruct (sn_reach_nf Hsn Hd y Hy) as [ny [Sy Ny]]. destruct (sn_reach_nf Hsn Hd z Hz) as [nz [Sz Nz]].
    exists ny. split; [exact Sy |]. rewrite (H c0 ny nz (star_refl R c0) (star_trans _ _ _ _ Hy Sy) Ny
                                                 (star_trans _ _ _ _ Hz Sz) Nz). exact Sz.
  Qed.
End Bridge.

(* Strong normalization excludes cycles (any relation). *)
Lemma sn_no_cycle : forall {A : Type} (R : A -> A -> Prop) x, SN R x ->
  forall y, R x y -> star R y x -> False.
Proof.
  intros A R x H. induction H as [x _ IH]. intros y Rxy Syx. destruct Syx as [x | y z x Ryz Szx].
  - exact (IH x Rxy x Rxy (star_refl R x)).
  - exact (IH y Rxy z Ryz (star_trans _ _ _ _ Szx (star_one R _ _ Rxy))).
Qed.

(* The labeled reduction of a layer-C system: a real (moving) step of some label. Its normal forms
   are exactly the settled states. *)
Section Labeled.
  Variable X : Type.
  Variable X_eq_dec : forall x y : X, {x = y} + {x <> y}.
  Variable js : list nat.
  Variable u : nat -> X -> X.

  Definition LStep (x y : X) : Prop := exists j, In j js /\ u j x = y /\ y <> x.

  Theorem nf_iff_stable : forall x, normal_form LStep x <-> Stable X u js x.
  Proof.
    intros x. split.
    - intros H j Hj. destruct (X_eq_dec (u j x) x) as [E | E]; [exact E |].
      exfalso. apply H. exists (u j x), j. tauto.
    - intros H [y [j [Hj [E Ne]]]]. apply Ne. rewrite <- E. apply H. exact Hj.
  Qed.

  Lemma lstep_dec : forall x, normal_form LStep x \/ exists y, LStep x y.
  Proof.
    intros x.
    assert (H : forall l, (forall j, In j l -> u j x = x) \/ exists j, In j l /\ u j x <> x).
    { induction l as [| a l [IH | [j [Hj Nj]]]].
      - left. intros j [].
      - destruct (X_eq_dec (u a x) x) as [E | E].
        + left. intros j [<- | Hj]; [exact E | exact (IH j Hj)].
        + right. exists a. split; [left; reflexivity | exact E].
      - right. exists j. split; [right; exact Hj | exact Nj]. }
    destruct (H js) as [Hs | [j [Hj Nj]]].
    - left. apply nf_iff_stable. exact Hs.
    - right. exists (u j x), j. tauto.
  Qed.

  Lemma wrun_star : forall w x, Path js w -> star LStep x (wrun X u w x).
  Proof.
    induction w as [| a w IH]; intros x Hw; [apply star_refl |]. inversion Hw as [| ? ? Ha Hw']; subst.
    change (wrun X u (a :: w) x) with (wrun X u w (u a x)).
    destruct (X_eq_dec (u a x) x) as [E | E].
    - rewrite E. apply IH. exact Hw'.
    - eapply star_step; [exists a; split; [exact Ha | split; [reflexivity | exact E]] | apply IH; exact Hw'].
  Qed.

  Lemma star_word : forall x y, star LStep x y -> exists w, Path js w /\ wrun X u w x = y.
  Proof.
    intros x y S. induction S as [x | x y z [j [Hj [E _]]] _ [w [Hw Ew]]]; [exists []; split; [constructor | reflexivity] |].
    exists (j :: w). split; [constructor; assumption |]. simpl. rewrite E. exact Ew.
  Qed.

  (* A moving loop at x: a nonempty js-word returning x to x whose every step moves. *)
  Definition ystate (x : X) (q : list nat) (k : nat) : X := wrun X u (firstn k q) x.
  Definition MLoop (x : X) (q : list nat) : Prop :=
    q <> [] /\ Path js q /\ wrun X u q x = x /\
    forall k, k < length q -> u (nth k q 0) (ystate x q k) <> ystate x q k.
  (* A label of js that the loop never names although it moves every loop state: a reduction
     that is enabled at every step and hidden forever (a weak-fairness violation). *)
  Definition Starved (x : X) (q : list nat) (j : nat) : Prop :=
    In j js /\ ~ In j q /\ forall k, k < length q -> u j (ystate x q k) <> ystate x q k.
  Definition StarvedLoop (s0 : X) : Prop :=
    exists p q j, Path js p /\ MLoop (wrun X u p s0) q /\ Starved (wrun X u p s0) q j.
  Definition LoopFrom (s0 : X) : Prop :=
    exists p q, Path js p /\ MLoop (wrun X u p s0) q.

  Lemma mloop_cycle : forall x q, MLoop x q -> exists y, LStep x y /\ star LStep y x.
  Proof.
    intros x [| a q] (Hq & Hp & Eq & Hm); [congruence |]. inversion Hp as [| ? ? Ha Hp']; subst.
    exists (u a x). split.
    - exists a. split; [exact Ha | split; [reflexivity | exact (Hm 0 ltac:(simpl; lia))]].
    - change (wrun X u (a :: q) x) with (wrun X u q (u a x)) in Eq. rewrite <- Eq at 2.
      apply wrun_star. exact Hp'.
  Qed.

  (* Fairness can insert a label only where it is idle: ins puts every label that fixes the
     current state in front of each step, which changes no state. *)
  Definition fixers (x : X) : list nat := filter (fun j => if X_eq_dec (u j x) x then true else false) js.

  Fixpoint ins (x : X) (w : list nat) : list nat :=
    match w with [] => [] | a :: r => fixers x ++ a :: ins (u a x) r end.

  Lemma fixers_spec : forall x j, In j (fixers x) <-> In j js /\ u j x = x.
  Proof.
    intros x j. unfold fixers. rewrite filter_In.
    destruct (X_eq_dec (u j x) x) as [E | E]; split; intros [H1 H2]; split; try assumption; congruence.
  Qed.

  Lemma wrun_fixed : forall l x, (forall j, In j l -> u j x = x) -> wrun X u l x = x.
  Proof.
    induction l as [| a l IH]; intros x H; [reflexivity |]. change (wrun X u l (u a x) = x).
    rewrite (H a (or_introl eq_refl)). apply IH. intros j Hj. apply H. right. exact Hj.
  Qed.

  Lemma wrun_ins : forall w x, wrun X u (ins x w) x = wrun X u w x.
  Proof.
    induction w as [| a w IH]; intros x; [reflexivity |]. simpl ins.
    rewrite wrun_app, (wrun_fixed (fixers x) x) by (intros j Hj; apply fixers_spec; exact Hj).
    change (wrun X u (ins (u a x) w) (u a x) = wrun X u w (u a x)). apply IH.
  Qed.

  Lemma path_ins : forall w x, Path js w -> Path js (ins x w).
  Proof.
    induction w as [| a w IH]; intros x Hw; [constructor |]. inversion Hw as [| ? ? Ha Hw']; subst.
    simpl. apply Forall_app. split.
    - apply Forall_forall. intros j Hj. apply fixers_spec in Hj. tauto.
    - constructor; [exact Ha | apply IH; exact Hw'].
  Qed.

  Lemma in_ins_orig : forall w x j, In j w -> In j (ins x w).
  Proof.
    induction w as [| a w IH]; intros x j Hj; [destruct Hj |]. simpl. apply in_or_app. right.
    destruct Hj as [<- | Hj]; [left; reflexivity | right; apply IH; exact Hj].
  Qed.

  Lemma in_ins_fixer : forall w x k j, k < length w -> In j js ->
    u j (ystate x w k) = ystate x w k -> In j (ins x w).
  Proof.
    induction w as [| a w IH]; intros x k j Hk Hj E; [simpl in Hk; lia |]. simpl. apply in_or_app.
    destruct k as [| k].
    - left. apply fixers_spec. split; [exact Hj | exact E].
    - right. right. apply (IH (u a x) k j); [simpl in Hk; lia | exact Hj | exact E].
  Qed.

  Lemma bsearch : forall (Q : nat -> Prop), (forall k, Q k \/ ~ Q k) ->
    forall n, (exists k, k < n /\ Q k) \/ (forall k, k < n -> ~ Q k).
  Proof.
    intros Q Hd n. induction n as [| n [[k [Hk Qk]] | IH]].
    - right. intros k Hk. lia.
    - left. exists k. split; [lia | exact Qk].
    - destruct (Hd n) as [Qn | Qn].
      + left. exists n. split; [lia | exact Qn].
      + right. intros k Hk. destruct (Nat.eq_dec k n) as [-> | Ne]; [exact Qn | apply IH; lia].
  Qed.

  (* Under fair raw settlement (C2), every reachable moving loop starves some label: an infinite
     reduction survives fairness only by hiding a reduction that is enabled at every step. *)
  Theorem fair_starves : forall s0, FairSettles X js u (Stable X u js) s0 ->
    forall p q, Path js p -> MLoop (wrun X u p s0) q -> exists j, Starved (wrun X u p s0) q j.
  Proof.
    intros s0 Hfs p q Hp HL. set (x := wrun X u p s0) in *.
    assert (D : forall l, (forall j, In j l -> In j q \/ exists k, k < length q /\ u j (ystate x q k) = ystate x q k) \/
                          (exists j, In j l /\ ~ In j q /\ forall k, k < length q -> u j (ystate x q k) <> ystate x q k)).
    { induction l as [| a l [IH | [j [Hj Hs]]]].
      - left. intros j [].
      - destruct (in_dec Nat.eq_dec a q) as [Ia | Ia].
        + left. intros j [<- | Hj]; [left; exact Ia | exact (IH j Hj)].
        + destruct (bsearch (fun k => u a (ystate x q k) = ystate x q k)
                      (fun k => match X_eq_dec (u a (ystate x q k)) (ystate x q k) with
                                | left E => or_introl E | right E => or_intror E end) (length q))
            as [Hk | Hk].
          * left. intros j [<- | Hj]; [right; exact Hk | exact (IH j Hj)].
          * right. exists a. split; [left; reflexivity | split; [exact Ia | exact Hk]].
      - right. exists j. split; [right; exact Hj | exact Hs]. }
    destruct (D js) as [Hall | [j [Hj Hs]]]; [| exists j; split; [exact Hj | exact Hs]].
    exfalso. destruct HL as (Hq & Hpq & Eq & Hm).
    assert (Hne : ins x q <> []) by (destruct q as [| a q]; [congruence | simpl; destruct (fixers x); discriminate]).
    assert (HF : FairLasso X js u s0 x p (ins x q)).
    { split; [exact Hp | split; [reflexivity | split; [exact Hne | split; [apply path_ins; exact Hpq |]]]].
      split; [rewrite wrun_ins; exact Eq |]. intros j Hj. destruct (Hall j Hj) as [Iq | [k [Hk Ek]]].
      - apply in_ins_orig. exact Iq.
      - apply (in_ins_fixer q x k j Hk Hj Ek). }
    assert (NS : ~ Stable X u js x).
    { intro S. destruct q as [| a q']; [congruence |]. apply (Hm 0 ltac:(simpl; lia)). apply S.
      inversion Hpq; subst. assumption. }
    apply (proj1 (bad_lasso_refutes X js u (Stable X u js) s0
                    (ex_intro _ x (ex_intro _ p (ex_intro _ (ins x q) (ex_intro _ x
                       (conj HF (conj (onloop_base X u x _ Hne) NS))))))) Hfs).
  Qed.

  Theorem sn_no_loop : forall s0, SN LStep s0 -> ~ LoopFrom s0.
  Proof.
    intros s0 Hsn (p & q & Hp & HL). destruct (mloop_cycle _ q HL) as [y [Hxy Hyx]].
    apply (sn_no_cycle LStep (wrun X u p s0)
             (GovernanceWFConverse.SN_star_closed LStep s0 _ (wrun_star p s0 Hp) Hsn) y Hxy Hyx).
  Qed.

  Section Fin.
    Variable xs : list X.
    Hypothesis xs_full : forall x, In x xs.

    Definition Chain (f : nat -> X) (n : nat) : Prop := forall i, i < n -> LStep (f i) (f (S i)).

    Lemma acc_bound : forall n x, (forall f, f 0 = x -> ~ Chain f n) -> SN LStep x.
    Proof.
      induction n as [| n IH]; intros x H.
      - exfalso. apply (H (fun _ => x) eq_refl). intros i Hi. lia.
      - constructor. intros y Hxy. apply IH. intros g Eg Hg.
        apply (H (fun i => match i with 0 => x | S i => g i end) eq_refl).
        intros [| i] Hi; [rewrite <- Eg in Hxy; exact Hxy | apply Hg; lia].
    Qed.

    Lemma chain_reach : forall s0 f n, f 0 = s0 -> Chain f n -> forall i, i <= n -> Reach LStep s0 (f i).
    Proof.
      intros s0 f n E Hc i. induction i as [| i IH]; intros Hi; [rewrite E; apply star_refl |].
      eapply star_trans; [apply IH; lia | apply star_one; apply Hc; lia].
    Qed.

    Lemma chain_word : forall f n a, Chain f n -> forall d, a + d <= n ->
      exists w, length w = d /\ Path js w /\ wrun X u w (f a) = f (a + d) /\
        forall k, k < length w -> u (nth k w 0) (ystate (f a) w k) <> ystate (f a) w k.
    Proof.
      intros f n a Hc d. induction d as [| d IH]; intros Hd.
      - exists []. rewrite Nat.add_0_r. split; [reflexivity | split; [constructor | split; [reflexivity |]]].
        intros k Hk. simpl in Hk. lia.
      - destruct (IH ltac:(lia)) as (w & Lw & Pw & Ew & Mw).
        destruct (Hc (a + d) ltac:(lia)) as [j [Hj [Ej Nj]]].
        exists (w ++ [j]). rewrite app_length. simpl. split; [lia |].
        split; [apply Forall_app; split; [exact Pw | constructor; [exact Hj | constructor]] |].
        split; [rewrite wrun_app, Ew; simpl; rewrite Ej; f_equal; lia |].
        intros k Hk. unfold ystate. rewrite firstn_app.
        destruct (Nat.eq_dec k (length w)) as [-> | Ne].
        + rewrite firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r, Ew.
          rewrite app_nth2 by lia. rewrite Nat.sub_diag. simpl. rewrite Ej.
          replace (a + S d) with (S (a + d)) by lia. exact Nj.
        + replace (k - length w) with 0 by lia. simpl. rewrite app_nil_r.
          rewrite app_nth1 by lia. apply Mw. lia.
    Qed.

    (* On a finite state space, termination from s0 is the absence of a reachable moving loop. *)
    Theorem sn_iff_no_loop : forall s0, SN LStep s0 <-> ~ LoopFrom s0.
    Proof.
      intros s0. split; [apply sn_no_loop |]. intros Hn.
      apply (acc_bound (length xs)). intros f Ef Hc.
      destruct (pigeon_aux X X_eq_dec (length xs) xs f (le_n _) (fun i _ => xs_full (f i)))
        as (a & b & Hab & E).
      destruct (star_word s0 (f a) (chain_reach s0 f _ Ef Hc a ltac:(lia))) as [p [Hp Ep]].
      destruct (chain_word f _ a Hc (b - a) ltac:(lia)) as (w & Lw & Pw & Ew & Mw).
      apply Hn. exists p, w. split; [exact Hp |]. rewrite Ep.
      split; [intro Z; rewrite Z in Lw; simpl in Lw; lia |]. split; [exact Pw |].
      split; [rewrite Ew; replace (a + (b - a)) with b by lia; symmetry; exact E | exact Mw].
    Qed.

    (* What fair settlement can replace: under C2, termination is exactly the absence of a
       reachable starved loop. *)
    Theorem fair_sn_exact : forall s0, FairSettles X js u (Stable X u js) s0 ->
      (SN LStep s0 <-> ~ StarvedLoop s0).
    Proof.
      intros s0 Hfs. rewrite sn_iff_no_loop. split.
      - intros Hn (p & q & j & Hp & HL & _). apply Hn. exists p, q. tauto.
      - intros Hn (p & q & Hp & HL). destruct (fair_starves s0 Hfs p q Hp HL) as [j Hj].
        apply Hn. exists p, q, j. tauto.
    Qed.

    Theorem fair_newman : forall s0, FairSettles X js u (Stable X u js) s0 -> ~ StarvedLoop s0 ->
      (PeaksJoin LStep s0 <-> CR LStep s0) /\ (CR LStep s0 <-> UNF LStep s0).
    Proof.
      intros s0 Hfs Hn. apply newman_bridge; [apply (fair_sn_exact s0 Hfs); exact Hn |].
      intros x _. apply lstep_dec.
    Qed.
  End Fin.
End Labeled.

(* ----- Part 4b. Instances of the A-C bridge ----- *)

(* The counterexample: the standard four-point system showing that Newman's lemma needs
   termination (for example Klop, "Term rewriting systems from Church-Rosser to Knuth-Bendix
   and beyond," ICALP 1990, LNCS 443, Figure 3), in layer C's form. Label 0 sends kb to ka and
   kc to kd; label 1 swaps kb and kc. Every peak joins, every fair run settles (C2), yet the
   system is not confluent: from kb both ka and kd are normal forms. The infinite run kb, kc, kb,
   ... under label 1 alone is unfair, and its loop starves label 0, which moves both loop
   states. *)
Inductive K4 : Type := ka | kb | kc | kd.
Definition k4_eq_dec : forall x y : K4, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition ku (j : nat) (x : K4) : K4 :=
  match j, x with 0, kb => ka | 0, kc => kd | 1, kb => kc | 1, kc => kb | _, _ => x end.
Definition kjs : list nat := [0; 1].
Definition KStep := LStep K4 kjs ku.

Lemma kstep : forall j x, In j kjs -> ku j x <> x -> KStep x (ku j x).
Proof. intros j x Hj Ne. exists j. tauto. Qed.

Lemma kc_ka : star KStep kc ka.
Proof.
  eapply star_step; [apply (kstep 1 kc); [simpl; tauto | discriminate] |].
  eapply star_step; [apply (kstep 0 kb); [simpl; tauto | discriminate] | apply star_refl].
Qed.

Lemma kb_kd : star KStep kb kd.
Proof.
  eapply star_step; [apply (kstep 1 kb); [simpl; tauto | discriminate] |].
  eapply star_step; [apply (kstep 0 kc); [simpl; tauto | discriminate] | apply star_refl].
Qed.

Lemma k_nf_a : normal_form KStep ka.
Proof. apply (nf_iff_stable K4 k4_eq_dec). intros j [<- | [<- | []]]; reflexivity. Qed.

Lemma k_nf_d : normal_form KStep kd.
Proof. apply (nf_iff_stable K4 k4_eq_dec). intros j [<- | [<- | []]]; reflexivity. Qed.

Lemma k_lc : forall x y z, KStep x y -> KStep x z -> joinable KStep y z.
Proof.
  intros x y z [j1 [H1 [<- _]]] [j2 [H2 [<- _]]].
  destruct H1 as [<- | [<- | []]]; destruct H2 as [<- | [<- | []]]; destruct x; simpl;
    try (exists ka; split; [apply star_refl | exact kc_ka]);
    try (exists ka; split; [exact kc_ka | apply star_refl]);
    try (exists kd; split; [apply star_refl | exact kb_kd]);
    try (exists kd; split; [exact kb_kd | apply star_refl]);
    eexists; split; apply star_refl.
Qed.

Lemma k_fair_settles : forall s0, FairSettles K4 kjs ku (Stable K4 ku kjs) s0.
Proof.
  intros s0. apply C2_reach. intros sg [_ Hinf]. destruct (Hinf 0 0 (or_introl eq_refl)) as [m [_ Em]].
  exists (S m). cbn [prs]. rewrite Em. intros j [<- | [<- | []]]; destruct (prs K4 ku sg m s0); reflexivity.
Qed.

Lemma k_ones : forall n, prs K4 ku (fun _ => 1) n kb = if Nat.even n then kb else kc.
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [prs]. rewrite IH, Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even n); reflexivity.
Qed.

Theorem four_point_fair_not_confluent :
  (forall x y z, KStep x y -> KStep x z -> joinable KStep y z) /\
  FairSettles K4 kjs ku (Stable K4 ku kjs) kb /\
  MLoop K4 kjs ku kb [1; 1] /\ Starved K4 kjs ku kb [1; 1] 0 /\ StarvedLoop K4 kjs ku kb /\
  (forall n, KStep (prs K4 ku (fun _ => 1) n kb) (prs K4 ku (fun _ => 1) (S n) kb)) /\
  ~ Fair kjs (fun _ => 1) /\
  ~ SN KStep kb /\
  star KStep kb ka /\ star KStep kb kd /\ normal_form KStep ka /\ normal_form KStep kd /\ ka <> kd /\
  ~ CR KStep kb /\ ~ UNF KStep kb /\
  (forall c, ~ CanonSettles K4 kjs ku K4 (fun x => x) kb c).
Proof.
  assert (HL : MLoop K4 kjs ku kb [1; 1]).
  { split; [discriminate | split; [repeat constructor; simpl; tauto | split; [reflexivity |]]].
    intros [| [| k]] Hk; simpl in Hk; [discriminate | discriminate | lia]. }
  assert (HS : Starved K4 kjs ku kb [1; 1] 0).
  { split; [left; reflexivity | split; [simpl; intuition discriminate |]].
    intros [| [| k]] Hk; simpl in Hk; [discriminate | discriminate | lia]. }
  assert (Sa : star KStep kb ka) by (eapply star_step; [apply (kstep 0 kb); [simpl; tauto | discriminate] | apply star_refl]).
  assert (NCR : ~ CR KStep kb).
  { intro H. destruct (H ka kd Sa kb_kd) as [w [A1 A2]].
    rewrite <- (star_from_nf KStep ka w k_nf_a A1) in A2.
    discriminate (star_from_nf KStep kd ka k_nf_d A2). }
  split; [exact k_lc |]. split; [apply k_fair_settles |]. split; [exact HL |]. split; [exact HS |].
  split; [exists [], [1; 1], 0; split; [constructor | split; [exact HL | exact HS]] |].
  split.
  { intro n. rewrite !k_ones, Nat.even_succ, <- Nat.negb_even. destruct (Nat.even n); simpl.
    - apply (kstep 1 kb); [simpl; tauto | discriminate].
    - apply (kstep 1 kc); [simpl; tauto | discriminate]. }
  split.
  { intros [_ H]. destruct (H 0 0 (or_introl eq_refl)) as [m [_ Em]]. discriminate Em. }
  split.
  { intro H. apply (sn_no_cycle KStep kb H kc); [apply (kstep 1 kb); [simpl; tauto | discriminate] |].
    apply star_one. apply (kstep 1 kc); [simpl; tauto | discriminate]. }
  split; [exact Sa |]. split; [exact kb_kd |]. split; [exact k_nf_a |]. split; [exact k_nf_d |].
  split; [discriminate |]. split; [exact NCR |].
  split; [intro H; discriminate (H kb ka kd (star_refl _ kb) Sa k_nf_a kb_kd k_nf_d) |].
  intros c H. refine (proj1 (bad_lasso_refutes K4 kjs ku (Fiber K4 K4 (fun x => x) c) kb _) H).
  destruct (k4_eq_dec c ka) as [-> | Ne].
  - exists kd, [1; 0], [0; 1], kd. split.
    + split; [repeat constructor; simpl; tauto | split; [reflexivity | split; [discriminate |]]].
      split; [repeat constructor; simpl; tauto | split; [reflexivity | intros j Hj; exact Hj]].
    + split; [apply onloop_base; discriminate | unfold Fiber; discriminate].
  - exists ka, [0], [0; 1], ka. split.
    + split; [repeat constructor; simpl; tauto | split; [reflexivity | split; [discriminate |]]].
      split; [repeat constructor; simpl; tauto | split; [reflexivity | intros j Hj; exact Hj]].
    + split; [apply onloop_base; discriminate | unfold Fiber; intro E; exact (Ne (eq_sym E))].
Qed.

(* The starved loop is necessary for non-termination, not for non-confluence: in the drop
   network (CanonicalRecurrence.fud: label 0 swaps fa and fb, label 1 drops every value to fz)
   the loop fa, fb, fa under label 0 starves label 1, every fair run settles, and the system is
   still confluent, because fz is the only normal form and every state reaches it. *)
Definition DStep := LStep Fl fjs2 fud.

Lemma drop_to_fz : forall x, star DStep x fz.
Proof.
  intros x. assert (P : Path fjs2 [1]) by (repeat constructor; simpl; tauto).
  exact (wrun_star Fl fl_eq_dec fjs2 fud [1] x P).
Qed.

Theorem drop_starved_confluent :
  FairSettles Fl fjs2 fud (Stable Fl fud fjs2) fa /\
  StarvedLoop Fl fjs2 fud fa /\ ~ SN DStep fa /\
  PeaksJoin DStep fa /\ CR DStep fa /\ UNF DStep fa.
Proof.
  assert (CRa : CR DStep fa).
  { intros y z _ _. exists fz. split; apply drop_to_fz. }
  split.
  { apply C2_reach. intros sg [_ Hinf]. destruct (Hinf 1 0 (or_intror (or_introl eq_refl))) as [m [_ Em]].
    exists (S m). cbn [prs]. rewrite Em. intros j [<- | [<- | []]]; reflexivity. }
  assert (HS : StarvedLoop Fl fjs2 fud fa).
  { exists [], [0; 0], 1. split; [constructor |]. split.
    - split; [discriminate | split; [repeat constructor; simpl; tauto | split; [reflexivity |]]].
      intros [| [| k]] Hk; simpl in Hk; [discriminate | discriminate | lia].
    - split; [right; left; reflexivity | split; [simpl; intuition discriminate |]].
      intros [| [| k]] Hk; simpl in Hk; [discriminate | discriminate | lia]. }
  split; [exact HS |]. split.
  { intro H. apply (sn_no_loop Fl fl_eq_dec fjs2 fud fa H).
    destruct HS as (p & q & _ & Hp & HL & _). exists p, q. tauto. }
  split; [apply cr_peaks; exact CRa |]. split; [exact CRa | apply cr_unf; exact CRa].
Qed.

(* Non-vacuity of fair_newman: two flags, label 0 raises the first, label 1 the second. Every
   fair run settles at (true, true), there is no moving loop, every peak joins, and the theorem
   yields confluence and unique normal forms. *)
Definition orU (j : nat) (x : bool * bool) : bool * bool :=
  match j with 0 => (true, snd x) | 1 => (fst x, true) | _ => x end.
Definition OStep := LStep (bool * bool) js2 orU.
Definition bb_eq_dec : forall x y : bool * bool, {x = y} + {x <> y}.
Proof. decide equality; apply bool_dec. Defined.

Lemma or_fst : forall w x, Path js2 w -> fst x = true -> fst (wrun (bool * bool) orU w x) = true.
Proof.
  induction w as [| a w IH]; intros x Hw Hx; [exact Hx |]. inversion Hw as [| ? ? Ha Hw']; subst.
  apply IH; [exact Hw' |]. destruct Ha as [<- | [<- | []]]; simpl; [reflexivity | exact Hx].
Qed.

Lemma or_snd : forall w x, Path js2 w -> snd x = true -> snd (wrun (bool * bool) orU w x) = true.
Proof.
  induction w as [| a w IH]; intros x Hw Hx; [exact Hx |]. inversion Hw as [| ? ? Ha Hw']; subst.
  apply IH; [exact Hw' |]. destruct Ha as [<- | [<- | []]]; simpl; [exact Hx | reflexivity].
Qed.

Lemma or_prs : forall sg x n m, (forall i, In (sg i) js2) -> n <= m ->
  prs (bool * bool) orU sg m x = wrun (bool * bool) orU (seg sg n (m - n)) (prs (bool * bool) orU sg n x).
Proof.
  intros sg x n m _ Hnm. replace m with (n + (m - n)) at 1 by lia. apply prs_seg.
Qed.

Theorem or_fair_newman :
  FairSettles (bool * bool) js2 orU (Stable (bool * bool) orU js2) (false, false) /\
  ~ StarvedLoop (bool * bool) js2 orU (false, false) /\
  PeaksJoin OStep (false, false) /\ CR OStep (false, false) /\ UNF OStep (false, false).
Proof.
  assert (HF : FairSettles (bool * bool) js2 orU (Stable (bool * bool) orU js2) (false, false)).
  { apply C2_reach. intros sg Hf. destruct Hf as [Hin Hinf].
    destruct (Hinf 0 0 (or_introl eq_refl)) as [m0 [_ E0]].
    destruct (Hinf 1 0 (or_intror (or_introl eq_refl))) as [m1 [_ E1]].
    exists (S (Nat.max m0 m1)). set (M := S (Nat.max m0 m1)).
    assert (P : forall n k, Path js2 (seg sg n k)) by (intros n k; apply seg_path; split; assumption).
    assert (A : fst (prs (bool * bool) orU sg M (false, false)) = true).
    { rewrite (or_prs sg _ (S m0) M Hin) by lia. apply or_fst; [apply P |]. cbn [prs]. rewrite E0. reflexivity. }
    assert (B : snd (prs (bool * bool) orU sg M (false, false)) = true).
    { rewrite (or_prs sg _ (S m1) M Hin) by lia. apply or_snd; [apply P |]. cbn [prs]. rewrite E1. reflexivity. }
    destruct (prs (bool * bool) orU sg M (false, false)) as [a b]. simpl in A, B. subst.
    intros j [<- | [<- | []]]; reflexivity. }
  assert (NL : ~ StarvedLoop (bool * bool) js2 orU (false, false)).
  { intros (p & q & j & _ & (Hq & Hp & Eq & Hm) & _). set (x := wrun (bool * bool) orU p (false, false)) in *.
    destruct q as [| a q]; [congruence |]. inversion Hp as [| ? ? Ha Hp']; subst.
    pose proof (Hm 0 ltac:(simpl; lia)) as M0. simpl in M0. change (wrun _ orU (a :: q) x) with (wrun _ orU q (orU a x)) in Eq.
    destruct x as [x1 x2]. destruct Ha as [<- | [<- | []]]; simpl in M0.
    - destruct x1; [exfalso; apply M0; reflexivity |]. pose proof (or_fst q (orU 0 (false, x2)) Hp' eq_refl) as F. rewrite Eq in F. discriminate F.
    - destruct x2; [exfalso; apply M0; reflexivity |]. pose proof (or_snd q (orU 1 (x1, false)) Hp' eq_refl) as F. rewrite Eq in F. discriminate F. }
  destruct (fair_newman (bool * bool) bb_eq_dec js2 orU
              [(false, false); (false, true); (true, false); (true, true)]
              ltac:(intros [[] []]; simpl; tauto) (false, false) HF NL) as [E1 E2].
  assert (T : forall x, star OStep x (true, true)).
  { intros x. assert (P : Path js2 [0; 1]) by (repeat constructor; simpl; tauto).
    pose proof (wrun_star (bool * bool) bb_eq_dec js2 orU [0; 1] x P) as S. destruct x as [a b]. exact S. }
  assert (PJ : PeaksJoin OStep (false, false)) by (intros x y z _ _ _; exists (true, true); split; apply T).
  split; [exact HF |]. split; [exact NL |]. split; [exact PJ |].
  split; [apply (proj1 E1); exact PJ | apply (proj1 E2); apply (proj1 E1); exact PJ].
Qed.

(* ============================================================================================ *)
(* Part 5. B-C: the fixed points of the repair dynamics are the B-solutions.                    *)
(* ============================================================================================ *)

(* A store: get and set on the vertices vs, with the two lens laws used below. *)
Section Store.
  Variables D Sh : Type.
  Variable get : nat -> Sh -> D.
  Variable set : nat -> D -> Sh -> Sh.
  Variable vs : list nat.
  Hypothesis get_set : forall v d s, In v vs -> get v (set v d s) = d.
  Hypothesis set_get : forall v s, In v vs -> set v (get v s) s = s.

  Definition val (s : Sh) : nat -> D := fun w => get w s.

  (* Reading A: the edge repair U_(a,b,f)(s) = s[b := f (s_a)]. *)
  Definition erep (x : @edge (D -> D)) (s : Sh) : Sh := let '(a, b, f) := x in set b (f (get a s)) s.

  Theorem erep_fixed_iff : forall a b f s, In b vs -> (erep (a, b, f) s = s <-> f (get a s) = get b s).
  Proof.
    intros a b f s Hb. simpl. split.
    - intro E. rewrite <- (get_set b (f (get a s)) s Hb), E. reflexivity.
    - intro E. rewrite E. apply set_get. exact Hb.
  Qed.

  (* The repair dynamics of a network G: label j repairs the j-th edge. *)
  Definition eU (G : list (@edge (D -> D))) (j : nat) (s : Sh) : Sh :=
    match nth_error G j with Some x => erep x s | None => s end.
  Definition ejs (G : list (@edge (D -> D))) : list nat := seq 0 (length G).
  Definition TargetsIn (G : list (@edge (D -> D))) : Prop := forall a b f, In (a, b, f) G -> In b vs.
  Definition EndsIn (G : list (@edge (D -> D))) : Prop := forall a b f, In (a, b, f) G -> In a vs /\ In b vs.

  Theorem edge_fixed_iff_section : forall G s, TargetsIn G ->
    (Stable Sh (eU G) (ejs G) s <-> msection (val s) G).
  Proof.
    intros G s HT. split.
    - intros H [[a b] f] Hx. destruct (In_nth_error G _ Hx) as [j Ej].
      assert (Hj : In j (ejs G)) by (apply in_seq; split; [lia | apply nth_error_Some; congruence]).
      pose proof (H j Hj) as E. unfold eU in E. rewrite Ej in E.
      apply (erep_fixed_iff a b f s (HT a b f Hx)) in E. exact E.
    - intros H j Hj. unfold eU. destruct (nth_error G j) as [[[a b] f] |] eqn:Ej; [| reflexivity].
      pose proof (nth_error_In G j Ej) as Hx. apply (erep_fixed_iff a b f s (HT a b f Hx)). exact (H _ Hx).
  Qed.

  (* ... and so (section_iff_csp) the solutions of the network's CSP. *)
  Theorem edge_fixed_iff_csp : forall G s, TargetsIn G ->
    (Stable Sh (eU G) (ejs G) s <-> solution (val s) (csp_of G [])).
  Proof.
    intros G s HT. rewrite edge_fixed_iff_section by exact HT. rewrite <- section_solution. split.
    - intro H. split; [exact H | intros r c []].
    - intros [H _]. exact H.
  Qed.

  Definition Realize : Prop := forall a : nat -> D, exists s, forall w, In w vs -> get w s = a w.

  Theorem edge_fixed_exists_iff_csp : forall G, EndsIn G -> Realize ->
    ((exists s, Stable Sh (eU G) (ejs G) s) <-> csp_sat (csp_of G [])).
  Proof.
    intros G HE HR. assert (HT : TargetsIn G) by (intros a b f Hx; apply (HE a b f Hx)). split.
    - intros [s Hs]. exists (val s). apply edge_fixed_iff_csp; assumption.
    - intros [a Ha]. destruct (HR a) as [s Hs]. exists s. apply edge_fixed_iff_section; [exact HT |].
      apply section_solution in Ha. destruct Ha as [Ha _]. intros [[u v] f] Hx.
      destruct (HE u v f Hx) as [Hu Hv]. unfold msat, val. rewrite (Hs u Hu), (Hs v Hv). exact (Ha _ Hx).
  Qed.

  (* Reading B: the resolver repair U_j(s) = s[j := F_j(s)] (SignedResolver.rupd). *)
  Theorem rupd_fixed_iff : forall (js : list nat) (Fv : nat -> Sh -> D) s, incl js vs ->
    (Stable Sh (rupd D Sh js set Fv) js s <-> forall j, In j js -> Fv j s = get j s).
  Proof.
    intros js Fv s Hv. split.
    - intros H j Hj. pose proof (H j Hj) as E. unfold rupd in E. destruct (in_dec Nat.eq_dec j js); [| contradiction].
      rewrite <- (get_set j (Fv j s) s (Hv j Hj)), E. reflexivity.
    - intros H j Hj. unfold rupd. destruct (in_dec Nat.eq_dec j js); [| reflexivity].
      rewrite (H j Hj). apply set_get. apply Hv. exact Hj.
  Qed.

  (* When F_j reads its in-neighbors us j through a merge g j, the fixed points are the sections of
     the merge network, and so (hsection_iff_csp) the solutions of its CSP. *)
  Definition mnet (js : list nat) (us : nat -> list nat) (g : nat -> list D -> D) : list (@hedge D) :=
    map (fun j => (us j, j, g j)) js.

  Theorem rupd_fixed_iff_csp : forall js (Fv : nat -> Sh -> D) us g s, incl js vs ->
    (forall j s, In j js -> Fv j s = g j (map (fun w => get w s) (us j))) ->
    (Stable Sh (rupd D Sh js set Fv) js s <-> hsection (val s) (mnet js us g)) /\
    (hsection (val s) (mnet js us g) <-> solution (val s) (map hcon (mnet js us g))).
  Proof.
    intros js Fv us g s Hv HF. split; [| apply hsection_iff_csp].
    rewrite rupd_fixed_iff by exact Hv. split.
    - intros H x Hx. unfold mnet in Hx. apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
      simpl. unfold val. rewrite <- (HF j s Hj). apply H. exact Hj.
    - intros H j Hj. rewrite (HF j s Hj).
      exact (H (us j, j, g j) (in_map (fun j => (us j, j, g j)) js j Hj)).
  Qed.
End Store.

(* Settlement in C's vocabulary, for any dynamics: what the B-solutions (the settled states,
   Stable) decide about C1 and C2, and what they do not. *)
Section Settle.
  Variable X : Type.
  Variable js : list nat.
  Variable u : nat -> X -> X.

  Lemma path_js : Path js js.
  Proof. apply Forall_forall. intros j Hj. exact Hj. Qed.

  (* No B-solution: no fair run settles (no physical settlement), from any start. *)
  Theorem no_solution_no_settlement : js <> [] -> (forall x, ~ Stable X u js x) ->
    forall s0, ~ FairSettles X js u (Stable X u js) s0.
  Proof.
    intros Hne Hn s0 H. destruct (H (lsg [] js) (lasso_fair js [] js (Forall_nil _) path_js Hne (fun j Hj => Hj)))
      as [M HM]. exact (Hn _ (HM M (le_n M))).
  Qed.

  (* The singleton fair recurrent classes (C2's settled loops) are exactly the reachable
     B-solutions. *)
  Theorem singleton_iff_solution : js <> [] -> forall s0 p, Path js p ->
    ((exists q, FairLasso X js u s0 (wrun X u p s0) p q /\
                forall y, OnLoop X u (wrun X u p s0) q y -> y = wrun X u p s0) <->
     Stable X u js (wrun X u p s0)).
  Proof.
    intros Hne s0 p Hp. set (x := wrun X u p s0). split.
    - intros [q [(_ & _ & Hq & Pq & Eq & Hall) Hy]] j Hj. destruct (In_nth q j 0 (Hall j Hj)) as [k [Hk Ek]].
      assert (Yk : wrun X u (firstn k q) x = x) by (apply Hy; exists k; split; [exact Hk | reflexivity]).
      assert (Yk1 : wrun X u (firstn (S k) q) x = x).
      { destruct (Nat.eq_dec (S k) (length q)) as [E | E].
        - rewrite E, firstn_all. exact Eq.
        - apply Hy. exists (S k). split; [lia | reflexivity]. }
      rewrite firstn_snoc, wrun_app, Yk, Ek in Yk1 by exact Hk. exact Yk1.
    - intros Hs. exists js. split.
      + split; [exact Hp | split; [reflexivity | split; [exact Hne | split; [exact path_js |]]]].
        split; [apply (settled_wrun X js u); [exact Hs | exact path_js] | intros j Hj; exact Hj].
      + intros y [k [_ <-]]. apply (settled_wrun X js u); [exact Hs | apply path_firstn; exact path_js].
  Qed.

  Section Canon.
    Variable C : Type.
    Variable N : X -> C.

    (* Canonical settlement at c forces every reachable B-solution into the fiber of c. *)
    Theorem canon_needs_solutions : js <> [] -> forall s0 c, CanonSettles X js u C N s0 c ->
      forall p, Path js p -> Stable X u js (wrun X u p s0) -> N (wrun X u p s0) = c.
    Proof.
      intros Hne s0 c H p Hp Hs.
      destruct (proj2 (singleton_iff_solution Hne s0 p Hp) Hs) as [q [HL Hy]].
      destruct (H (lsg p q) (match HL with conj Pp (conj _ (conj Hq (conj Pq (conj _ Ha)))) =>
                                lasso_fair js p q Pp Pq Hq Ha end)) as [M HM].
      destruct (lasso_visits X js u s0 _ p q _ HL (onloop_base X u _ q (proj1 (proj2 (proj2 HL)))) M)
        as [n [Hn En]].
      unfold Fiber in HM. rewrite <- En. exact (HM n Hn).
    Qed.

    (* Under fair raw settlement (C2), canonical settlement (C1) is exactly: every reachable
       B-solution lies in the fiber of c. A ghost is a reachable B-solution outside it. *)
    Theorem settled_canon_exact : js <> [] -> forall s0 c, FairSettles X js u (Stable X u js) s0 ->
      (CanonSettles X js u C N s0 c <->
       forall p, Path js p -> Stable X u js (wrun X u p s0) -> N (wrun X u p s0) = c).
    Proof.
      intros Hne s0 c Hfs. split; [apply canon_needs_solutions; exact Hne |].
      intros H sg Hf. destruct (Hfs sg Hf) as [M HM]. exists M. intros n Hn. unfold Fiber.
      assert (E : prs X u sg n s0 = wrun X u (seg sg 0 n) s0) by exact (prs_seg X u sg s0 0 n).
      rewrite E. apply H; [apply seg_path; exact Hf |]. rewrite <- E. apply HM. exact Hn.
    Qed.

    Definition Ghost (s0 : X) (c : C) : Prop :=
      exists p, Path js p /\ Stable X u js (wrun X u p s0) /\ N (wrun X u p s0) <> c.

    Theorem ghost_refutes : js <> [] -> forall s0 c, Ghost s0 c -> ~ CanonSettles X js u C N s0 c.
    Proof. intros Hne s0 c [p [Hp [Hs Hn]]] H. exact (Hn (canon_needs_solutions Hne s0 c H p Hp Hs)). Qed.

    (* Several reachable B-solutions with different canonical images: no target settles. *)
    Theorem multistable : js <> [] -> forall s0 p1 p2, Path js p1 -> Path js p2 ->
      Stable X u js (wrun X u p1 s0) -> Stable X u js (wrun X u p2 s0) ->
      N (wrun X u p1 s0) <> N (wrun X u p2 s0) -> forall c, ~ CanonSettles X js u C N s0 c.
    Proof.
      intros Hne s0 p1 p2 H1 H2 S1 S2 Nd c H. apply Nd.
      rewrite (canon_needs_solutions Hne s0 c H p1 H1 S1), (canon_needs_solutions Hne s0 c H p2 H2 S2).
      reflexivity.
    Qed.
  End Canon.
End Settle.

(* ----- Part 5b. Instances of the B-C interface ----- *)

(* flip2 (DistributedCyclesExact.flip2_fair_livelock) is a reading-A network on a one-vertex
   store: two self-loop edges at vertex 0, the swap and the drop of fa to fz. Its repair dynamics
   is fu2 tt label by label; its unique section (B-solution) is fz; and the fair lasso fa -0-> fb
   -1-> fb -0-> fa refutes settlement. A unique B-solution does not give C-settlement. *)
Definition get1 (_ : nat) (s : Fl) : Fl := s.
Definition set1 (_ : nat) (d : Fl) (_ : Fl) : Fl := d.
Definition fdrop (x : Fl) : Fl := match x with fa => fz | _ => x end.
Definition flipG : list (@edge (Fl -> Fl)) := [(0, 0, fsw); (0, 0, fdrop)].
Definition flipU := eU Fl Fl get1 set1 flipG.

Theorem flip2_unique_solution_livelock :
  (forall j x, flipU j x = fu2 tt j x) /\ ejs Fl flipG = fjs2 /\
  (forall s, msection (val Fl Fl get1 s) flipG <-> s = fz) /\
  (forall s, Stable Fl flipU fjs2 s <-> s = fz) /\
  BadLasso Fl fjs2 flipU (Stable Fl flipU fjs2) fa /\
  ~ FairSettles Fl fjs2 flipU (Stable Fl flipU fjs2) fa.
Proof.
  assert (Sec : forall s, msection (val Fl Fl get1 s) flipG <-> s = fz).
  { intros s. split.
    - intro H. pose proof (H _ (or_introl eq_refl)) as E. destruct s; [reflexivity | discriminate E | discriminate E].
    - intros -> x [<- | [<- | []]]; reflexivity. }
  assert (St : forall s, Stable Fl flipU fjs2 s <-> s = fz).
  { intros s. rewrite <- Sec. apply (edge_fixed_iff_section Fl Fl get1 set1 [0]).
    - intros v d s' _. reflexivity.
    - intros v s' _. reflexivity.
    - intros a b f [E | [E | []]]; injection E as <- <- <-; left; reflexivity. }
  assert (B : BadLasso Fl fjs2 flipU (Stable Fl flipU fjs2) fa).
  { exists fa, [], [0; 1; 0], fa. split.
    - split; [constructor | split; [reflexivity | split; [discriminate |]]].
      split; [repeat constructor; simpl; tauto | split; [reflexivity |]].
      intros j [<- | [<- | []]]; simpl; tauto.
    - split; [apply onloop_base; discriminate | intro H; apply St in H; discriminate H]. }
  split; [intros [| [| [| j]]] []; reflexivity |]. split; [reflexivity |]. split; [exact Sec |].
  split; [exact St |]. split; [exact B | exact (proj1 (bad_lasso_refutes _ _ _ _ _ B))].
Qed.

(* The negation cycle x0 := not x1, x1 := x0 (SignedResolver.neg_F) as a reading-B merge
   network: no B-solution, hence (no_solution_no_settlement) no fair run settles from any start. *)
Definition negus (j : nat) : list nat := match j with 0 => [1] | _ => [0] end.
Definition negg (j : nat) (l : list bool) : bool := match j with 0 => negb (hd false l) | _ => hd false l end.

Lemma set2_get2 : forall v s, In v js2 -> set2 v (get2 v s) s = s.
Proof. intros v [a b] [<- | [<- | []]]; reflexivity. Qed.

Theorem negation_no_solution :
  (forall s, ~ solution (val bool SS2 get2 s) (map hcon (mnet bool js2 negus negg))) /\
  (forall s, ~ Stable SS2 (rupd2 neg_F) js2 s) /\
  (forall s0, ~ FairSettles SS2 js2 (rupd2 neg_F) (Stable SS2 (rupd2 neg_F) js2) s0).
Proof.
  assert (HF : forall j s, In j js2 -> neg_F j s = negg j (map (fun w => get2 w s) (negus j)))
    by (intros j s [<- | [<- | []]]; reflexivity).
  assert (NS : forall s, ~ Stable SS2 (rupd2 neg_F) js2 s).
  { intros [a b] H. apply (proj1 (proj1 (rupd_fixed_iff_csp bool SS2 get2 set2 js2
                                           get2_set_eq set2_get2 js2 neg_F negus negg (a, b)
                                           (fun j Hj => Hj) HF))) in H.
    pose proof (H _ (or_introl eq_refl)) as E0. pose proof (H _ (or_intror (or_introl eq_refl))) as E1.
    unfold val in E0, E1. destruct a, b; simpl in E0, E1; discriminate. }
  split.
  { intros s Hs. apply (NS s).
    destruct (rupd_fixed_iff_csp bool SS2 get2 set2 js2 get2_set_eq set2_get2
                js2 neg_F negus negg s (fun j Hj => Hj) HF) as [E1 E2].
    apply E1. apply E2. exact Hs. }
  split; [exact NS |]. apply no_solution_no_settlement; [discriminate | exact NS].
Qed.

(* The leak on the canonical side: no B-solution does not refute canonical settlement. The
   oscillation of CanonicalRecurrence.semantic_oscillation has no settled state, raw settlement
   fails, and canonical settlement at true holds. *)
Theorem no_solution_canon_settles :
  (forall x, ~ Stable Osc osc_u osc_js x) /\
  ~ FairSettles Osc osc_js osc_u (Stable Osc osc_u osc_js) oz /\
  CanonSettles Osc osc_js osc_u bool osc_N oz true.
Proof.
  assert (NS : forall x, ~ Stable Osc osc_u osc_js x)
    by (intros x H; specialize (H 0 (or_introl eq_refl)); destruct x; discriminate H).
  split; [exact NS |]. split; [apply no_solution_no_settlement; [discriminate | exact NS] |].
  destruct semantic_oscillation as (_ & _ & _ & _ & _ & _ & _ & H). exact H.
Qed.

(* Several B-solutions: the copy-back cycle x0 := x1, x1 := x0 from (false, true) reaches the two
   solutions (true, true) and (false, false); multistable refutes every canonical target. *)
Theorem copyback_multistable :
  Stable SS2 (rupd2 cb_F) js2 (wrun SS2 (rupd2 cb_F) [0] (false, true)) /\
  Stable SS2 (rupd2 cb_F) js2 (wrun SS2 (rupd2 cb_F) [1] (false, true)) /\
  wrun SS2 (rupd2 cb_F) [0] (false, true) <> wrun SS2 (rupd2 cb_F) [1] (false, true) /\
  forall c, ~ CanonSettles SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (false, true) c.
Proof.
  assert (S1 : Stable SS2 (rupd2 cb_F) js2 (wrun SS2 (rupd2 cb_F) [0] (false, true)))
    by (intros j _; apply cb_tt_fixed).
  assert (S2 : Stable SS2 (rupd2 cb_F) js2 (wrun SS2 (rupd2 cb_F) [1] (false, true)))
    by (intros j _; apply cb_ff_fixed).
  assert (P0 : Path js2 [0]) by (repeat constructor; simpl; tauto).
  assert (P1 : Path js2 [1]) by (repeat constructor; simpl; tauto).
  split; [exact S1 | split; [exact S2 | split; [discriminate |]]].
  apply (multistable SS2 js2 (rupd2 cb_F) SS2 (fun s => s) ltac:(discriminate) (false, true) [0] [1] P0 P1 S1 S2).
  discriminate.
Qed.

(* A ghost: from (true, true) the copy-back cycle is settled (C2 holds) at a B-solution that is
   not the designated canonical one, slfp = (false, false); settled_canon_exact reads C1's
   failure off that one reachable solution. *)
Theorem copyback_ghost_solution :
  FairSettles SS2 js2 (rupd2 cb_F) (Stable SS2 (rupd2 cb_F) js2) (true, true) /\
  Ghost SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse) /\
  ~ CanonSettles SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse).
Proof.
  assert (G : Ghost SS2 js2 (rupd2 cb_F) SS2 (fun s => s) (true, true) (slfp2 cb_F ofalse)).
  { exists []. split; [constructor | split; [intros j _; apply cb_tt_fixed |]].
    simpl. rewrite (proj1 (proj2 (proj2 (proj2 copyback_ghost)))). discriminate. }
  split.
  { apply C2_reach. intros sg _. exists 0. intros j _. apply cb_tt_fixed. }
  split; [exact G | exact (ghost_refutes SS2 js2 (rupd2 cb_F) SS2 (fun s => s) ltac:(discriminate) _ _ G)].
Qed.

(* ============================================================================================ *)
(* Part 6. A-B, strict: natural families of event maps act on sections.                         *)
(* ============================================================================================ *)

Section Natural.
  Context {D : Type}.

  (* A per-vertex family e_v commuting with every edge map: f o e_a = e_b o f on (a, b, f). *)
  Definition NatSq (G : list (@edge (D -> D))) (e : nat -> D -> D) : Prop :=
    forall a b f, In (a, b, f) G -> forall x, f (e a x) = e b (f x).
  Definition PreservesSections (G : list (@edge (D -> D))) (e : nat -> D -> D) : Prop :=
    forall s, msection s G -> msection (fun w => e w (s w)) G.

  Theorem natural_maps_sections : forall G e, NatSq G e -> PreservesSections G e.
  Proof. intros G e H s Hs [[a b] f] Hx. simpl. rewrite (H a b f Hx), (Hs _ Hx). reflexivity. Qed.

  (* The exact condition for one network: the squares commute on the values sections take. *)
  Theorem preserves_exact : forall G e, PreservesSections G e <->
    forall s, msection s G -> forall a b f, In (a, b, f) G -> f (e a (s a)) = e b (f (s a)).
  Proof.
    intros G e. split.
    - intros H s Hs a b f Hx. pose proof (H s Hs _ Hx) as E. simpl in E. rewrite E, (Hs _ Hx). reflexivity.
    - intros H s Hs [[a b] f] Hx. simpl. rewrite (H s Hs a b f Hx), (Hs _ Hx). reflexivity.
  Qed.

  (* The converse: a square is necessary once the edge stands alone, if it is not a self-loop. *)
  Theorem square_necessary : forall a b f e, a <> b -> PreservesSections [(a, b, f)] e ->
    forall x, f (e a x) = e b (f x).
  Proof.
    intros a b f e Hab H x.
    set (s := fun w => if Nat.eqb w b then f x else x).
    assert (Sa : s a = x) by (unfold s; apply Nat.eqb_neq in Hab; rewrite Hab; reflexivity).
    assert (Sb : s b = f x) by (unfold s; rewrite Nat.eqb_refl; reflexivity).
    assert (Hs : msection s [(a, b, f)]) by (intros y [<- | []]; simpl; rewrite Sa, Sb; reflexivity).
    pose proof (H s Hs _ (or_introl eq_refl)) as E. simpl in E. rewrite Sa, Sb in E. exact E.
  Qed.

  Theorem natural_iff_edgewise : forall G e, (forall a b f, In (a, b, f) G -> a <> b) ->
    (NatSq G e <-> forall a b f, In (a, b, f) G -> PreservesSections [(a, b, f)] e).
  Proof.
    intros G e Hl. split.
    - intros H a b f Hx. apply natural_maps_sections. intros a' b' f' [E | []] x.
      injection E as <- <- <-. apply H. exact Hx.
    - intros H a b f Hx. apply square_necessary; [apply (Hl a b f Hx) | apply H; exact Hx].
  Qed.

  (* The uniform case e_v = p is a unary polymorphism (pol_iff_commute with k = 1). *)
  Theorem uniform_natural_is_unary_pol : forall (d0 : D) G (p : D -> D),
    NatSq G (fun _ => p) <-> forall a b f, In (a, b, f) G -> preserves 1 (fun l => p (hd d0 l)) (rgraph f).
  Proof.
    intros d0 G p. split.
    - intros H a b f Hx. apply pol_iff_commute. intros [| x [| y l]] Hl; try discriminate Hl.
      simpl. apply H with (a := a) (b := b). exact Hx.
    - intros H a b f Hx x. pose proof (proj1 (pol_iff_commute 1 _ f) (H a b f Hx) [x] eq_refl) as E.
      exact E.
  Qed.
End Natural.

(* The naive converse fails on a fixed network: the squares need hold only on section values.
   On bool, the pin edge 2 -> 0 (constant false) forces s 0 = false; e_0 = (fun _ => false) and
   e_1 = id preserve every section, but the square of the edge 0 -> 1 (identity) fails at true. *)
Definition ncG : list (@edge (bool -> bool)) := [(0, 1, fun x => x); (2, 0, fun _ => false)].
Definition ncE (v : nat) : bool -> bool := match v with 0 => fun _ => false | _ => fun x => x end.

Theorem natural_converse_fails :
  PreservesSections ncG ncE /\ ~ NatSq ncG ncE /\ msection (fun _ => false) ncG.
Proof.
  split.
  { intros s Hs [[a b] f] [E | [E | []]]; injection E as <- <- <-; simpl.
    - pose proof (Hs _ (or_intror (or_introl eq_refl))) as E2. simpl in E2.
      pose proof (Hs _ (or_introl eq_refl)) as E1. simpl in E1. rewrite <- E1, <- E2. reflexivity.
    - reflexivity. }
  split.
  { intro H. pose proof (H 0 1 (fun x => x) (or_introl eq_refl) true) as E. discriminate E. }
  intros [[a b] f] [E | [E | []]]; injection E as <- <- <-; reflexivity.
Qed.

(* And the self-loop exception: a self-loop with no section (negation) is preserved by every
   family, including one whose square fails. *)
Theorem selfloop_square_not_necessary :
  PreservesSections [(0, 0, negb)] (fun _ _ => true) /\ ~ NatSq [(0, 0, negb)] (fun _ _ => true).
Proof.
  split.
  - intros s Hs. exfalso. pose proof (Hs _ (or_introl eq_refl)) as E. simpl in E. destruct (s 0); discriminate E.
  - intro H. pose proof (H 0 0 negb (or_introl eq_refl) true) as E. discriminate E.
Qed.
