(* CanonicalLocality.v: the P layer of the canonical-execution experiment, interaction locality.
   Validated, scoped to acyclic composition; on cycles, soundness only. Axiom-free.

   CanonicalExecution.v isolates three layers, E (effective canonicalization), S (state descent)
   and H (history descent), for one canonicalizer on one state space. Criterion D of
   CanonicalInstances.v (FederationEventsConverse.fed_exact) was PARTIAL: the history layer went
   through the kernel, but splitting the GLOBAL swap condition (independent events commute after
   the full federated canonicalizer at reachable states, GCF) into the per-registry C1 and C2
   shapes used the model's own locality lemma (gc_iff_reach). This file states that split as a
   kernel theorem with the topology kept OUT of it, and makes the acyclic federation one instance.

   1. Factorization through a composition boundary (section Factorization). There are three kinds
      of ambiguity, each with an "exposed" predicate (the ones a run can reach) and a "resolved"
      predicate: global ambiguities g (for instance an independent pair at a reachable state,
      resolved when it commutes), local ambiguities l (inside one component) and interface
      ambiguities i (across the boundary). A decomposition DL, DJ lists the local and interface
      ambiguities a global one is made of.
        LCExposed  : a component of an exposed global ambiguity is exposed.
        LCSound    : an exposed global ambiguity whose components are all resolved is resolved.
        LC         : LCExposed /\ LCSound (locality completeness).
        Realizable : every exposed local (interface) ambiguity is forced by some exposed global
                     ambiguity: there is an exposed g whose resolution implies its resolution.
        Reflects   : the resolution of an exposed g implies the resolution of its components.
      - factor_sound   : LC -> LocalRes -> InterfaceRes -> GlobalRes.
      - factor_complete: Realizable -> GlobalRes -> LocalRes /\ InterfaceRes.
      - factor_exact   : LC -> Realizable -> (GlobalRes <-> LocalRes /\ InterfaceRes).
      - factor_pointwise: LCSound -> Reflects -> for exposed g, RG g <-> its components resolve.
      - reflects_realizable: Reflects plus "every exposed local or interface ambiguity is a
        component of an exposed global one" (Covered) gives Realizable.
      Each hypothesis is needed: factor_needs_sound (LCExposed, Realizable, LocalRes and
      InterfaceRes hold, GlobalRes fails), factor_needs_exposed (LCSound, Realizable, LocalRes
      and InterfaceRes hold, GlobalRes fails) and factor_needs_realizable (LC and GlobalRes hold,
      LocalRes fails).
      The theorem is thin by design: LCSound is the backward direction stated per global
      ambiguity and Realizable the forward direction stated per local or interface ambiguity, so
      all of factor_exact's content is in its premises. In an instance, both carry model content
      (for the federation, pair_commute and pair_commute_nec).

   2. The acyclic federation (section FedFactor), Common (FederationEvents.v) and a valid
      consistent start s0. Global ambiguities: an independent pair (a, b) at a reachable state s,
      resolved when applyF commutes (GCF). Local ambiguities (the H shape): a declared-independent
      pair on one registry j at a reachable s, resolved when the local governed run of the
      overwrite canonicalizer N_{j,s} := f j s commutes on the pair,
        grun (f j s) sig [a; b] (s j) = grun (f j s) sig [b; a] (s j)       (C2at, kernel grun).
      Interface ambiguities (the S shape): an event e on j and an event a on another registry at
      a reachable s, resolved when e's action descends along the local canonicalizer of the
      changed source environment,
        StateDescentAt (f j (applyF a s)) sig e (s j)                     (C1at, kernel S).
      LCSound is FederationEventsConverse.pair_commute and Reflects is pair_commute_nec: the
      locality and topological-solving argument (solve_unique, frun_solves, the upL lemmas) is
      exactly the proof of LC for this instance (fed_lc_sound, fed_reflects).
      Corollaries:
      - gc_iff_reach_P (= FederationEventsConverse.gc_iff_reach): GCF s0 <-> C1R1 s0 /\ C2R s0,
        that is GlobalH <-> InterfaceS /\ LocalH.
      - reach_commute_iff_P (= reach_commute_iff), from factor_pointwise.
      - fed_exact_P (= fed_exact, criterion D): TraceConv s0 <-> C1R1 s0 /\ C2R s0, by the kernel
        history layer (history_descent_exact over adjacent swaps) and then gc_iff_reach_P.
      - fed_exact_full_P (= fed_exact_full): the same with C1R (any number of intervening
        events); the multi-event move is the model's conv_c1_runs.
      - fed_gc_sites: the per-site form, GCF s0 <-> for every registry j, local history descent
        at j and state descent at j's exposed stale witnesses, stated in kernel vocabulary.
      - fed_factor_supply: non-vacuity on the supply chain of FederationEvents.v.

   3. Acyclicity is needed for LC (cyclic_lc_fails). A two-registry cycle 0 <-> 1 whose
      morphisms copy the other registry: every field of Common holds except the topological
      order; at every reachable state every local and interface ambiguity is resolved (C1R1 and
      C2R hold), yet two declared-independent events of registry 1 diverge after one swap
      (GCF fails). cyclic_lc_fails states that much; cyclic_lc_sound_fails states the step to
      LC: with the decomposition of section FedFactor, LCExposed and both component resolutions
      hold and LCSound, hence LC, fails. On a cycle the local canonicalizer of registry 1 reads
      registry 0, which reads registry 1: the event's own write comes back through its sources.

   4. The cyclic instance (cyc_factor_sound). On the monotone-cycle model of
      FederationEventsCyclesCheck.v (normal form (l, Lsh l)), FederationEventsCyclesCheck.commute_nf
      proves LCSound for the decomposition whose local ambiguities are the C2cyc witnesses and
      whose interface ambiguities are the C1cyc witnesses, every global ambiguity decomposing into
      all of them (a static decomposition, not a pointwise one). So factor_sound gives, from
      C1cyc and C2cyc, commutation of every independent pair at every normal form
      (cyc_factor_sound), hence GC from every normal form (cyc_factor_sound_gc): the soundness
      half only. Realizability of the
      static witnesses is not proved (and FederationEventsConverse.naive_converse_fails shows the
      static witnesses are not realizable in general).

   5. Shared hypothesis with state gluing. Common's c_local (a repair reads only its sources) is
      SheafGluing.R1 for the repair read at any fixed target values: common_r1 is the direction
      from Common, c_local_iff_r1 the equivalence with c_local alone. That is the one hypothesis
      the two P halves are proved to share here; SheafGluing's Refines (every constraint inside
      one cover member) has no counterpart in factor_exact, where the constraints that cross the
      boundary become interface ambiguities instead. fed_state_and_interaction states the two
      halves side by side on one acyclic federation (a conjunction, not a combined descent
      theorem). *)

Require Import NC.CanonicalExecution NC.Trace.
Require NC.FederationEvents NC.FederationEventsConverse NC.CanonicalInstances.
Require NC.FederationEventsCycles NC.FederationEventsCyclesCheck NC.SheafGluing.
From Coq Require Import List Arith Bool.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Factorization of global obligations through a composition boundary                       *)
(* ============================================================================================ *)

Section Factorization.
  Context {G L J : Type}.
  Variable GAmb : G -> Prop.      (* exposed global ambiguities *)
  Variable RG : G -> Prop.        (* resolved global ambiguities *)
  Variable LAmb : L -> Prop.      (* exposed local ambiguities (inside one component) *)
  Variable RL : L -> Prop.
  Variable JAmb : J -> Prop.      (* exposed interface ambiguities (across the boundary) *)
  Variable RJ : J -> Prop.
  Variable DL : G -> L -> Prop.   (* the local ambiguities a global one decomposes into *)
  Variable DJ : G -> J -> Prop.   (* the interface ambiguities a global one decomposes into *)

  Definition GlobalRes : Prop := forall g, GAmb g -> RG g.
  Definition LocalRes : Prop := forall l, LAmb l -> RL l.
  Definition InterfaceRes : Prop := forall i, JAmb i -> RJ i.
  Definition Components (g : G) : Prop :=
    (forall l, DL g l -> RL l) /\ (forall i, DJ g i -> RJ i).

  Definition LCExposed : Prop :=
    forall g, GAmb g -> (forall l, DL g l -> LAmb l) /\ (forall i, DJ g i -> JAmb i).
  Definition LCSound : Prop := forall g, GAmb g -> Components g -> RG g.
  Definition LC : Prop := LCExposed /\ LCSound.
  Definition Realizable : Prop :=
    (forall l, LAmb l -> exists g, GAmb g /\ (RG g -> RL l)) /\
    (forall i, JAmb i -> exists g, GAmb g /\ (RG g -> RJ i)).
  Definition Reflects : Prop := forall g, GAmb g -> RG g -> Components g.
  Definition Covered : Prop :=
    (forall l, LAmb l -> exists g, GAmb g /\ DL g l) /\
    (forall i, JAmb i -> exists g, GAmb g /\ DJ g i).

  Lemma reflects_realizable : Reflects -> Covered -> Realizable.
  Proof.
    intros HR [HL HJ]. split.
    - intros l Hl. destruct (HL l Hl) as [g [Hg Hd]]. exists g. split; [exact Hg |].
      intros Hr. exact (proj1 (HR g Hg Hr) l Hd).
    - intros i Hi. destruct (HJ i Hi) as [g [Hg Hd]]. exists g. split; [exact Hg |].
      intros Hr. exact (proj2 (HR g Hg Hr) i Hd).
  Qed.

  Theorem factor_pointwise : LCSound -> Reflects ->
    forall g, GAmb g -> (RG g <-> Components g).
  Proof. intros HS HR g Hg. split; [apply HR; exact Hg | apply HS; exact Hg]. Qed.

  Theorem factor_sound : LC -> LocalRes -> InterfaceRes -> GlobalRes.
  Proof.
    intros [HE HS] HL HJ g Hg. destruct (HE g Hg) as [EL EJ].
    apply HS; [exact Hg |]. split.
    - intros l Hl. apply HL. apply EL. exact Hl.
    - intros i Hi. apply HJ. apply EJ. exact Hi.
  Qed.

  Theorem factor_complete : Realizable -> GlobalRes -> LocalRes /\ InterfaceRes.
  Proof.
    intros [RLz RJz] HG. split.
    - intros l Hl. destruct (RLz l Hl) as [g [Hg H]]. apply H. apply HG. exact Hg.
    - intros i Hi. destruct (RJz i Hi) as [g [Hg H]]. apply H. apply HG. exact Hg.
  Qed.

  (* The headline: under LC and realizability, global resolution is exactly local and
     interface resolution. *)
  Theorem factor_exact : LC -> Realizable -> (GlobalRes <-> LocalRes /\ InterfaceRes).
  Proof.
    intros Hlc Hr. split; [apply factor_complete; exact Hr |].
    intros [HL HJ]. apply factor_sound; assumption.
  Qed.
End Factorization.

(* Each hypothesis is needed. Without LCSound: everything else holds and the global
   ambiguity is unresolved. *)
Theorem factor_needs_sound :
  LCExposed (fun _ : unit => True) (fun _ : unit => True) (fun _ : unit => True)
    (fun _ _ => True) (fun _ _ => True) /\
  Realizable (fun _ : unit => True) (fun _ => False) (fun _ : unit => True) (fun _ => True)
    (fun _ : unit => True) (fun _ => True) /\
  LocalRes (fun _ : unit => True) (fun _ => True) /\
  InterfaceRes (fun _ : unit => True) (fun _ => True) /\
  ~ LCSound (fun _ : unit => True) (fun _ => False) (fun _ : unit => True) (fun _ : unit => True)
      (fun _ _ => True) (fun _ _ => True) /\
  ~ GlobalRes (fun _ : unit => True) (fun _ => False).
Proof.
  split; [intros g _; split; intros; exact I |].
  split; [split; intros x _; exists tt; split; [exact I | | exact I | ]; intros _; exact I |].
  split; [intros l _; exact I |]. split; [intros i _; exact I |].
  split.
  - intros H. apply (H tt I). split; intros; exact I.
  - intros H. exact (H tt I).
Qed.

(* Without Realizable: LC and global resolution hold, and a local ambiguity no global one
   reaches is unresolved (the abstract shape of FederationEventsConverse.naive_converse_fails). *)
Theorem factor_needs_realizable :
  LC (fun _ : unit => True) (fun _ => True) (fun _ : unit => True) (fun _ => False)
    (fun _ : unit => True) (fun _ => True) (fun _ _ => False) (fun _ _ => False) /\
  GlobalRes (fun _ : unit => True) (fun _ => True) /\
  ~ LocalRes (fun _ : unit => True) (fun _ => False) /\
  ~ Realizable (fun _ : unit => True) (fun _ => True) (fun _ : unit => True) (fun _ => False)
      (fun _ : unit => True) (fun _ => True).
Proof.
  split; [split; [intros g _; split; intros _ [] | intros g _ _; exact I] |].
  split; [intros g _; exact I |].
  split; [intros H; exact (H tt I) |].
  intros [H _]. destruct (H tt I) as [g [_ Hg]]. exact (Hg I).
Qed.

(* Without LCExposed: a global ambiguity whose components are never exposed. LCSound and
   Realizable hold, LocalRes and InterfaceRes hold vacuously, and GlobalRes fails. With
   factor_needs_sound and factor_needs_realizable, each of the three premises of factor_exact
   (LCExposed and LCSound, which make up LC, and Realizable) is needed. *)
Theorem factor_needs_exposed :
  LCSound (fun _ : unit => True) (fun _ => False) (fun _ : unit => False) (fun _ : unit => False)
    (fun _ _ => True) (fun _ _ => True) /\
  Realizable (fun _ : unit => True) (fun _ => False) (fun _ : unit => False) (fun _ => False)
    (fun _ : unit => False) (fun _ => False) /\
  LocalRes (fun _ : unit => False) (fun _ => False) /\
  InterfaceRes (fun _ : unit => False) (fun _ => False) /\
  ~ LCExposed (fun _ : unit => True) (fun _ : unit => False) (fun _ : unit => False)
      (fun _ _ => True) (fun _ _ => True) /\
  ~ GlobalRes (fun _ : unit => True) (fun _ => False).
Proof.
  split; [intros g _ [HL _]; exact (HL tt I) |].
  split; [split; intros x Hx; destruct Hx |].
  split; [intros l Hl; destruct Hl |]. split; [intros i Hi; destruct Hi |].
  split; [intros H; destruct (H tt I) as [HL _]; exact (HL tt I) |].
  intros H. exact (H tt I).
Qed.

(* ============================================================================================ *)
(* 2. The acyclic federation: LC is the locality and topological-solving argument              *)
(* ============================================================================================ *)

Section FedFactor.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  Variable o : list nat.
  Hypothesis HC : FederationEvents.Common V src f valid rho E reg sig o.
  Variable s0 : nat -> V.
  Hypothesis Hi0 : FederationEvents.Inv V valid s0.
  Hypothesis Hc0 : FederationEvents.Cons V f o s0.

  Local Notation feqF := (FederationEvents.feq V).
  Local Notation InvF := (FederationEvents.Inv V valid).
  Local Notation ConsF := (FederationEvents.Cons V f o).
  Local Notation IfedF := (FederationEvents.Ifed E reg I).
  Local Notation rF := (FederationEvents.runF V f rho E reg sig o).
  Local Notation aF := (FederationEvents.applyF V f rho E reg sig o).

  (* An ambiguity: a state and two events. *)
  Definition Amb : Type := ((nat -> V) * E * E)%type.

  Definition FReach (s : nat -> V) : Prop := exists p, s = rF p s0.

  (* Global: an independent pair at a reachable state; resolved when it commutes after the
     federated canonicalizer. *)
  Definition fGAmb (g : Amb) : Prop := let '(s, a, b) := g in FReach s /\ IfedF a b.
  Definition fRG (g : Amb) : Prop :=
    let '(s, a, b) := g in feqF (aF b (aF a s)) (aF a (aF b s)).
  (* Local (H shape): a declared-independent pair on one registry; resolved when the local
     governed run of the overwrite canonicalizer f j s commutes on it. *)
  Definition fLAmb (l : Amb) : Prop :=
    let '(s, a, b) := l in FReach s /\ reg a = reg b /\ I a b.
  Definition fRL (l : Amb) : Prop :=
    let '(s, a, b) := l in
    grun (f (reg a) s) sig [a; b] (s (reg a)) = grun (f (reg a) s) sig [b; a] (s (reg a)).
  (* Interface (S shape): an event e and an event a on another registry; resolved when e's
     action descends along the local canonicalizer of the source environment a changed. *)
  Definition fJAmb (i : Amb) : Prop := let '(s, e, a) := i in FReach s /\ reg a <> reg e.
  Definition fRJ (i : Amb) : Prop :=
    let '(s, e, a) := i in StateDescentAt (f (reg e) (aF a s)) sig e (s (reg e)).
  (* The decomposition: a same-registry pair is its own local ambiguity; a cross-registry pair
     is the two interface ambiguities, one per direction. *)
  Definition fDL (g : Amb) (l : Amb) : Prop := let '(s, a, b) := g in reg a = reg b /\ l = g.
  Definition fDJ (g : Amb) (i : Amb) : Prop :=
    let '(s, a, b) := g in reg a <> reg b /\ (i = (s, a, b) \/ i = (s, b, a)).

  Lemma freach_ok : forall s, FReach s -> InvF s /\ ConsF s.
  Proof.
    intros s [p ->]. split.
    - apply (FederationEvents.runF_inv _ _ _ _ _ _ _ _ _ HC). exact Hi0.
    - apply (FederationEvents.runF_cons _ _ _ _ _ _ _ _ _ HC); assumption.
  Qed.

  Lemma fed_lc_exposed : LCExposed fGAmb fLAmb fJAmb fDL fDJ.
  Proof.
    intros [[s a] b] [Hr Hab]. split.
    - intros l [E12 ->]. split; [exact Hr |]. split; [exact E12 |].
      destruct Hab as [Ne | H]; [contradiction | exact H].
    - intros i [Ne [-> | ->]]; split; try exact Hr.
      + intro E'. apply Ne. symmetry. exact E'.
      + exact Ne.
  Qed.

  (* LC for the federation is the model's locality lemma pair_commute. *)
  Lemma fed_lc_sound : LCSound fGAmb fRG fRL fRJ fDL fDJ.
  Proof.
    intros [[s a] b] [Hr _] [HL HJ]. destruct (freach_ok s Hr) as [Hi Hc].
    apply (FederationEventsConverse.pair_commute _ _ _ _ _ _ _ _ _ HC s a b Hi Hc).
    - intros Ne. split.
      + symmetry. exact (HJ (s, a, b) (conj Ne (or_introl eq_refl))).
      + symmetry. exact (HJ (s, b, a) (conj Ne (or_intror eq_refl))).
    - intros E12. exact (HL (s, a, b) (conj E12 eq_refl)).
  Qed.

  Lemma fed_reflects : Reflects fGAmb fRG fRL fRJ fDL fDJ.
  Proof.
    intros [[s a] b] [Hr _] Hg. destruct (freach_ok s Hr) as [Hi Hc].
    destruct (FederationEventsConverse.pair_commute_nec _ _ _ _ _ _ _ _ _ HC s a b Hi Hc Hg)
      as [H1 H2]. split.
    - intros l [E12 ->]. exact (H2 E12).
    - intros i [Ne [-> | ->]]; symmetry; [exact (proj1 (H1 Ne)) | exact (proj2 (H1 Ne))].
  Qed.

  Lemma fed_covered : Covered fGAmb fLAmb fJAmb fDL fDJ.
  Proof.
    split.
    - intros [[s a] b] [Hr [E12 Hab]]. exists (s, a, b). split.
      + split; [exact Hr | right; exact Hab].
      + split; [exact E12 | reflexivity].
    - intros [[s e] a] [Hr Ne]. exists (s, e, a). split.
      + split; [exact Hr | left; intro E'; apply Ne; symmetry; exact E'].
      + split; [intro E'; apply Ne; symmetry; exact E' | left; reflexivity].
  Qed.

  Lemma fed_lc : LC fGAmb fRG fLAmb fRL fJAmb fRJ fDL fDJ.
  Proof. split; [exact fed_lc_exposed | exact fed_lc_sound]. Qed.

  Lemma fed_realizable : Realizable fGAmb fRG fLAmb fRL fJAmb fRJ.
  Proof. apply (reflects_realizable _ _ _ _ _ _ fDL fDJ); [exact fed_reflects | exact fed_covered]. Qed.

  (* The three obligations are the published ones, read in kernel vocabulary. *)
  Lemma fed_global : FederationEventsConverse.GCF V f rho E reg sig I o s0 <-> GlobalRes fGAmb fRG.
  Proof.
    split.
    - intros H [[s a] b] [[p ->] Hab]. exact (H p a b Hab).
    - intros H p a b Hab. exact (H (rF p s0, a, b) (conj (ex_intro _ p eq_refl) Hab)).
  Qed.

  Lemma fed_interface : FederationEventsConverse.C1R1 V f rho E reg sig o s0 <-> InterfaceRes fJAmb fRJ.
  Proof.
    split.
    - intros H [[s e] a] [[p ->] Ne]. symmetry. exact (H p e a Ne).
    - intros H p e a Ne. symmetry. exact (H (rF p s0, e, a) (conj (ex_intro _ p eq_refl) Ne)).
  Qed.

  Lemma fed_local : FederationEventsConverse.C2R V f rho E reg sig I o s0 <-> LocalRes fLAmb fRL.
  Proof.
    split.
    - intros H [[s a] b] [[p ->] [E12 Hab]]. exact (H p a b E12 Hab).
    - intros H p a b E12 Hab.
      exact (H (rF p s0, a, b) (conj (ex_intro _ p eq_refl) (conj E12 Hab))).
  Qed.

  (* gc_iff_reach as a corollary: GlobalH <-> InterfaceS /\ LocalH. *)
  Theorem gc_iff_reach_P :
    FederationEventsConverse.GCF V f rho E reg sig I o s0 <->
    FederationEventsConverse.C1R1 V f rho E reg sig o s0 /\
    FederationEventsConverse.C2R V f rho E reg sig I o s0.
  Proof.
    rewrite fed_global, fed_interface, fed_local, (factor_exact _ _ _ _ _ _ _ _ fed_lc fed_realizable).
    tauto.
  Qed.

  (* Criterion D: fed_exact. The kernel history layer turns trace convergence into commutation at
     each reachable adjacent swap; the P layer splits that into C1R1 and C2R. *)
  Theorem fed_exact_P :
    FederationEventsConverse.TraceConv V f rho E reg sig I o s0 <->
    FederationEventsConverse.C1R1 V f rho E reg sig o s0 /\
    FederationEventsConverse.C2R V f rho E reg sig I o s0.
  Proof.
    rewrite <- gc_iff_reach_P, <- (CanonicalInstances.fed_gen_iff _ _ _ _ _ _ _ _ _ _ HC),
      <- (history_descent_exact (fun _ : list E => True) (CanonicalInstances.fswap E reg I)
            (tequiv IfedF) (fun es => rF es s0) feqF
            (fun y k => eq_refl) (fun y z H k => eq_sym (H k))
            (fun x y z H1 H2 k => eq_trans (H1 k) (H2 k)) (CanonicalInstances.fed_adequate E reg I)).
    split; [intros H t u _ _; exact (H t u) | intros H es1 es2; exact (H es1 es2 Logic.I Logic.I)].
  Qed.

  (* fed_exact_full: any number of intervening events (the move past w is conv_c1_runs). *)
  Theorem fed_exact_full_P :
    FederationEventsConverse.TraceConv V f rho E reg sig I o s0 <->
    FederationEventsConverse.C1R V f rho E reg sig o s0 /\
    FederationEventsConverse.C2R V f rho E reg sig I o s0.
  Proof.
    rewrite fed_exact_P. split.
    - intros H. split; [| exact (proj2 H)].
      intros p e w Hw.
      pose proof (proj2 (fed_exact_P) H _ _
        (FederationEventsConverse.tequiv_app_l E reg I p _ _
          (FederationEventsConverse.tequiv_move E reg I e w Hw)) (reg e)) as Eq.
      rewrite (FederationEvents.runF_app _ _ _ _ _ _ _ p (e :: w)),
        (FederationEvents.runF_app _ _ _ _ _ _ _ p (w ++ [e])) in Eq.
      destruct (freach_ok (rF p s0) (ex_intro _ p eq_refl)) as [Hi Hc].
      destruct (FederationEventsConverse.conv_c1_runs _ _ _ _ _ _ _ _ _ HC (rF p s0) e w Hi Hc Hw)
        as [A B].
      rewrite <- A, <- B. symmetry. exact Eq.
    - intros [H1 H2]. split; [| exact H2].
      intros p e a Ne. apply (H1 p e [a]). constructor; [exact Ne | constructor].
  Qed.

  (* The per-site form in kernel vocabulary: global history descent iff, at every registry j,
     local history descent of the governed run of f j s and state descent of j's events along
     f j (applyF a s) at the stale witnesses exposed by an event a on another registry. *)
  Theorem fed_gc_sites :
    FederationEventsConverse.GCF V f rho E reg sig I o s0 <->
    forall j,
      (forall p a b, reg a = j -> reg b = j -> I a b ->
         grun (f j (rF p s0)) sig [a; b] (rF p s0 j) = grun (f j (rF p s0)) sig [b; a] (rF p s0 j)) /\
      (forall p e a, reg e = j -> reg a <> j ->
         StateDescentAt (f j (aF a (rF p s0))) sig e (rF p s0 j)).
  Proof.
    rewrite gc_iff_reach_P. split.
    - intros [H1 H2] j. split.
      + intros p a b <- Eb Hab. exact (H2 p a b (eq_sym Eb) Hab).
      + intros p e a <- Ne. symmetry. exact (H1 p e a Ne).
    - intros H. split.
      + intros p e a Ne. symmetry. exact (proj2 (H (reg e)) p e a eq_refl Ne).
      + intros p a b E12 Hab. exact (proj1 (H (reg a)) p a b eq_refl (eq_sym E12) Hab).
  Qed.
End FedFactor.

(* reach_commute_iff as a corollary of factor_pointwise, at any valid consistent state and for
   any two events (independence plays no role pointwise: take I := everything). *)
Theorem reach_commute_iff_P :
  forall V src f valid rho E reg sig o,
  FederationEvents.Common V src f valid rho E reg sig o ->
  forall s e1 e2, FederationEvents.Inv V valid s -> FederationEvents.Cons V f o s ->
  (FederationEvents.feq V (FederationEvents.applyF V f rho E reg sig o e2
                             (FederationEvents.applyF V f rho E reg sig o e1 s))
                          (FederationEvents.applyF V f rho E reg sig o e1
                             (FederationEvents.applyF V f rho E reg sig o e2 s)) <->
   (reg e1 <> reg e2 -> FederationEventsConverse.C1at V f rho E reg sig o s e1 e2 /\
                        FederationEventsConverse.C1at V f rho E reg sig o s e2 e1) /\
   (reg e1 = reg e2 -> FederationEventsConverse.C2at V f E reg sig s e1 e2)).
Proof.
  intros V src f valid rho E reg sig o HC s e1 e2 Hi Hc.
  set (Iall := fun _ _ : E => True).
  assert (Hg : fGAmb V f rho E reg sig Iall o s (s, e1, e2))
    by (split; [exists []; reflexivity | right; exact Logic.I]).
  rewrite (factor_pointwise _ _ _ _ _ _
             (fed_lc_sound V src f valid rho E reg sig Iall o HC s Hi Hc)
             (fed_reflects V src f valid rho E reg sig Iall o HC s Hi Hc) _ Hg).
  split.
  - intros [HL HJ]. split.
    + intros Ne. split; symmetry.
      * exact (HJ (s, e1, e2) (conj Ne (or_introl eq_refl))).
      * exact (HJ (s, e2, e1) (conj Ne (or_intror eq_refl))).
    + intros E12. exact (HL (s, e1, e2) (conj E12 eq_refl)).
  - intros [H1 H2]. split.
    + intros l [E12 ->]. exact (H2 E12).
    + intros i [Ne [-> | ->]]; symmetry; [exact (proj1 (H1 Ne)) | exact (proj2 (H1 Ne))].
Qed.

(* Non-vacuity of the federation instance: the supply chain of FederationEvents.v satisfies LC
   and Realizable, and all three resolutions hold, from every valid consistent start. *)
Theorem fed_factor_supply : forall s0,
  FederationEvents.Inv (bool * nat) FederationEvents.sp_valid s0 ->
  FederationEvents.Cons (bool * nat) FederationEvents.sp_f [0; 1] s0 ->
  let FG := fGAmb (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho FederationEvents.sev
              FederationEvents.sp_reg FederationEvents.sp_sig FederationEvents.sp_I [0; 1] s0 in
  let FL := fLAmb (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho FederationEvents.sev
              FederationEvents.sp_reg FederationEvents.sp_sig FederationEvents.sp_I [0; 1] s0 in
  let FJ := fJAmb (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho FederationEvents.sev
              FederationEvents.sp_reg FederationEvents.sp_sig [0; 1] s0 in
  let RG := fRG (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho FederationEvents.sev
              FederationEvents.sp_reg FederationEvents.sp_sig [0; 1] in
  let RL := fRL (bool * nat) FederationEvents.sp_f FederationEvents.sev FederationEvents.sp_reg
              FederationEvents.sp_sig in
  let RJ := fRJ (bool * nat) FederationEvents.sp_f FederationEvents.sp_rho FederationEvents.sev
              FederationEvents.sp_reg FederationEvents.sp_sig [0; 1] in
  LC FG RG FL RL FJ RJ (fDL (bool * nat) FederationEvents.sev FederationEvents.sp_reg)
     (fDJ (bool * nat) FederationEvents.sev FederationEvents.sp_reg) /\
  Realizable FG RG FL RL FJ RJ /\
  GlobalRes FG RG /\ LocalRes FL RL /\ InterfaceRes FJ RJ.
Proof.
  intros s0 Hi Hc FG FL FJ RG RL RJ.
  pose proof FederationEvents.sp_common as HC.
  destruct FederationEvents.supply_instance as [_ [_ [_ [H1 [H2 _]]]]].
  assert (Hg : GlobalRes FG RG).
  { apply (proj1 (fed_global _ _ _ _ _ _ _ _ s0)).
    apply (FederationEventsConverse.static_c1_c2_gc _ _ _ _ _ _ _ _ _ _ HC H1 H2 s0 Hi Hc). }
  split; [exact (fed_lc _ _ _ _ _ _ _ _ _ _ HC s0 Hi Hc) |].
  split; [exact (fed_realizable _ _ _ _ _ _ _ _ _ _ HC s0 Hi Hc) |].
  split; [exact Hg |].
  apply (factor_complete _ _ _ _ _ _ (fed_realizable _ _ _ _ _ _ _ _ _ _ HC s0 Hi Hc) Hg).
Qed.

(* ============================================================================================ *)
(* 3. Acyclicity is needed for LC: a two-registry cycle                                         *)
(* ============================================================================================ *)

(* Registry 0 reads 1 and registry 1 reads 0; each morphism copies the other registry's value. *)
Definition cy_src (k : nat) : list nat := match k with 0 => [1] | 1 => [0] | _ => [] end.
Definition cy_f (k : nat) (z : nat -> bool) (x : bool) : bool :=
  match k with 0 => z 1 | 1 => z 0 | _ => x end.
Definition cy_valid (_ : nat) (_ : bool) : Prop := True.
Definition cy_rho (_ : nat) (x : bool) : bool := x.
Inductive cyev : Type := CyNeg | CyOn.
Definition cy_reg (_ : cyev) : nat := 1.
Definition cy_sig (e : cyev) (x : bool) : bool := match e with CyNeg => negb x | CyOn => true end.
Definition cy_I (_ _ : cyev) : Prop := True.
Definition cy_s0 (_ : nat) : bool := false.

Theorem cyclic_lc_fails :
  (* every field of Common except the topological order *)
  (forall j z1 z2 x, (forall k, In k (cy_src j) -> z1 k = z2 k) -> cy_f j z1 x = cy_f j z2 x) /\
  ~ FederationEvents.topoF cy_src [0; 1] /\
  (forall j z x, FederationEvents.Inv bool cy_valid z -> cy_valid j x -> cy_valid j (cy_f j z x)) /\
  (forall j z z' x, FederationEvents.Inv bool cy_valid z -> FederationEvents.Inv bool cy_valid z' ->
     cy_valid j x -> cy_f j z (cy_f j z' x) = cy_f j z x) /\
  (forall j x, cy_valid j x -> cy_rho j x = x) /\
  (forall e x, cy_valid (cy_reg e) x -> cy_valid (cy_reg e) (cy_sig e x)) /\
  (forall e, In (cy_reg e) [0; 1]) /\
  FederationEvents.Inv bool cy_valid cy_s0 /\ FederationEvents.Cons bool cy_f [0; 1] cy_s0 /\
  (* every exposed interface and local ambiguity is resolved *)
  FederationEventsConverse.C1R1 bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] cy_s0 /\
  FederationEventsConverse.C2R bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0 /\
  (* and the global one is not: one swap of two declared-independent events diverges *)
  FederationEvents.runF bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] [CyNeg; CyOn] cy_s0 1 = true /\
  FederationEvents.runF bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] [CyOn; CyNeg] cy_s0 1 = false /\
  ~ FederationEventsConverse.GCF bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0.
Proof.
  split.
  { intros [| [| j]] z1 z2 x H; simpl; try reflexivity; apply H; left; reflexivity. }
  split. { simpl. intros [_ [Hs _]]. apply (Hs 1); [left; reflexivity | right; left; reflexivity]. }
  split. { intros. exact Logic.I. }
  split. { intros [| [| j]] z z' x _ _ _; reflexivity. }
  split. { intros. reflexivity. }
  split. { intros. exact Logic.I. }
  split. { intros e. right. left. reflexivity. }
  split. { intros k. exact Logic.I. }
  split. { intros j [<- | [<- | []]]; reflexivity. }
  split. { intros p e a Ne. exfalso. apply Ne. reflexivity. }
  split. { intros p e1 e2 _ _. reflexivity. }
  split; [reflexivity |]. split; [reflexivity |].
  intros H. pose proof (H [] CyNeg CyOn (or_intror Logic.I) 1) as D. discriminate D.
Qed.

(* The name cyclic_lc_fails is about LC, but its statement is about C1R1, C2R and GCF; the step
   "so LCSound fails" was prose. Here it is stated: on the cycle, with the decomposition of
   section FedFactor, LCSound (hence LC) fails at the global ambiguity (cy_s0, CyNeg, CyOn), while
   LCExposed and both component resolutions hold. *)
Theorem cyclic_lc_sound_fails :
  LCExposed (fGAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
    (fLAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
    (fJAmb bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] cy_s0) (fDL bool cyev cy_reg) (fDJ bool cyev cy_reg) /\
  LocalRes (fLAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0) (fRL bool cy_f cyev cy_reg cy_sig) /\
  InterfaceRes (fJAmb bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] cy_s0) (fRJ bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) /\
  ~ LCSound (fGAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
      (fRG bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) (fRL bool cy_f cyev cy_reg cy_sig)
      (fRJ bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) (fDL bool cyev cy_reg) (fDJ bool cyev cy_reg) /\
  ~ LC (fGAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
      (fRG bool cy_f cy_rho cyev cy_reg cy_sig [0; 1])
      (fLAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0) (fRL bool cy_f cyev cy_reg cy_sig)
      (fJAmb bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] cy_s0)
      (fRJ bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) (fDL bool cyev cy_reg) (fDJ bool cyev cy_reg).
Proof.
  destruct cyclic_lc_fails as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _ & _ & Hg).
  assert (HL : LocalRes (fLAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
                 (fRL bool cy_f cyev cy_reg cy_sig))
    by exact (proj1 (fed_local _ _ _ _ _ _ _ _ _) H2).
  assert (HJ : InterfaceRes (fJAmb bool cy_f cy_rho cyev cy_reg cy_sig [0; 1] cy_s0)
                 (fRJ bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]))
    by exact (proj1 (fed_interface _ _ _ _ _ _ _ _) H1).
  assert (HS : ~ LCSound (fGAmb bool cy_f cy_rho cyev cy_reg cy_sig cy_I [0; 1] cy_s0)
      (fRG bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) (fRL bool cy_f cyev cy_reg cy_sig)
      (fRJ bool cy_f cy_rho cyev cy_reg cy_sig [0; 1]) (fDL bool cyev cy_reg) (fDJ bool cyev cy_reg)).
  { intros H. apply Hg. apply (proj2 (fed_global _ _ _ _ _ _ _ _ _)).
    apply (factor_sound _ _ _ _ _ _ _ _ (conj (fed_lc_exposed _ _ _ _ _ _ _ _ _) H) HL HJ). }
  split; [exact (fed_lc_exposed _ _ _ _ _ _ _ _ _) |].
  split; [exact HL |]. split; [exact HJ |]. split; [exact HS |].
  intros [_ H]. exact (HS H).
Qed.

(* ============================================================================================ *)
(* 4. The cyclic instance: soundness of the static decomposition (FederationEventsCyclesCheck) *)
(* ============================================================================================ *)

Section CycFactor.
  Variables Loc Sh Lc Hc Rg : Type.
  Variable rg_eq_dec : forall a b : Rg, {a = b} + {a <> b}.
  Variable enc : Rg -> nat.
  Variable lget : Rg -> Loc -> Lc.
  Variable lset : Rg -> Lc -> Loc -> Loc.
  Hypothesis lget_lset_eq : forall j x l, lget j (lset j x l) = x.
  Hypothesis lget_lset_neq : forall j k x l, k <> j -> lget k (lset j x l) = lget k l.
  Hypothesis l_ext : forall l l', (forall k, lget k l = lget k l') -> l = l'.
  Variable sget : Rg -> Sh -> Hc.
  Variable sset : Rg -> Hc -> Sh -> Sh.
  Hypothesis sget_sset_eq : forall j x h, sget j (sset j x h) = x.
  Hypothesis sget_sset_neq : forall j k x h, k <> j -> sget k (sset j x h) = sget k h.
  Variable cvalid : Rg -> Lc * Hc -> Prop.
  Variable E : Type.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.
  Variable I : E -> E -> Prop.
  Hypothesis sig_valid : forall e x, cvalid (reg e) x -> cvalid (reg e) (sig e x).
  Variable rho1 : Loc * Sh -> Loc * Sh.
  Variable Lsh : Loc -> Sh.
  Hypothesis rho1_valid : forall s, FederationEventsCyclesCheck.FValid Loc Sh Lc Hc Rg lget sget cvalid s ->
    rho1 s = s.
  Hypothesis nf_valid : forall t, FederationEventsCyclesCheck.FValid Loc Sh Lc Hc Rg lget sget cvalid
    (FederationEventsCyclesCheck.Nr Loc Sh rho1 Lsh t).
  Variable Hs : Rg -> Hc -> Prop.
  Hypothesis Hs_nf : forall t k, Hs k (sget k (snd (FederationEventsCyclesCheck.Nr Loc Sh rho1 Lsh t))).

  Local Notation Nr := (FederationEventsCyclesCheck.Nr Loc Sh rho1 Lsh).
  Local Notation gs := (FederationEventsCycles.gstep (Loc * Sh) E Nr
                          (FederationEventsCyclesCheck.cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig)).
  Local Notation nreg := (FederationEventsCyclesCheck.nreg Rg enc E reg).

  (* Global: an independent pair at a normal form. Local: a C2cyc witness. Interface: a C1cyc
     witness (the shared part of j is an image, from a source environment). *)
  Definition cGAmb (g : (Loc * Sh) * E * E) : Prop :=
    let '(s, a, b) := g in (exists t, s = Nr t) /\ FederationEventsCycles.Ifd E nreg I a b.
  Definition cRG (g : (Loc * Sh) * E * E) : Prop :=
    let '(s, a, b) := g in gs a (gs b s) = gs b (gs a s).
  Definition cLAmb (l : E * E * Lc * Hc) : Prop :=
    let '(a, b, x, h) := l in reg a = reg b /\ I a b /\ cvalid (reg a) (x, h) /\ Hs (reg a) h.
  Definition cRL (l : E * E * Lc * Hc) : Prop :=
    let '(a, b, x, h) := l in fst (sig a (fst (sig b (x, h)), h)) = fst (sig b (fst (sig a (x, h)), h)).
  Definition cJAmb (i : E * Lc * Hc * Hc) : Prop :=
    let '(e, x, h, h') := i in cvalid (reg e) (x, h) /\ Hs (reg e) h /\ Hs (reg e) h'.
  Definition cRJ (i : E * Lc * Hc * Hc) : Prop :=
    let '(e, x, h, h') := i in fst (sig e (x, h')) = fst (sig e (x, h)).

  (* The static decomposition: every exposed witness is a component of every global ambiguity. *)
  Theorem cyc_lc : LC cGAmb cRG cLAmb cRL cJAmb cRJ (fun _ l => cLAmb l) (fun _ i => cJAmb i).
  Proof.
    split; [intros g _; split; intros; assumption |].
    intros [[s a] b] [[t ->] Hab] [HL HJ].
    apply (FederationEventsCyclesCheck.commute_nf Loc Sh Lc Hc Rg rg_eq_dec enc lget lset
             lget_lset_eq lget_lset_neq l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg sig I
             sig_valid rho1 Lsh rho1_valid nf_valid Hs Hs_nf); [| | exact Hab].
    - intros e x h h' H1 H2 H3. exact (HJ (e, x, h, h') (conj H1 (conj H2 H3))).
    - intros a' b' x h H1 H2 H3 H4. exact (HL (a', b', x, h) (conj H1 (conj H2 (conj H3 H4)))).
  Qed.

  (* GC on the image of the normalizer from C1cyc and C2cyc, as factor_sound. *)
  Theorem cyc_factor_sound :
    FederationEventsCyclesCheck.C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    FederationEventsCyclesCheck.C2cyc Lc Hc Rg cvalid E reg sig I Hs ->
    GlobalRes cGAmb cRG.
  Proof.
    intros H1 H2. apply (factor_sound _ _ _ _ _ _ _ _ cyc_lc).
    - intros [[[a b] x] h] [E12 [Hab [Hv Hh]]]. exact (H2 a b x h E12 Hab Hv Hh).
    - intros [[[e x] h] h'] [Hv [Hh Hh']]. exact (H1 e x h h' Hv Hh Hh').
  Qed.

  (* cyc_factor_sound's conclusion is commutation of every independent pair at every normal form
     Nr t. The docs read it as "GC on the image of the normalizer"; this is that reading, stated:
     GC (FederationEventsCycles.GC, for the governed step Nr o cev) from every normal form. *)
  Lemma cyc_grun_nf : forall p t, exists t', FederationEventsCycles.grun (Loc * Sh) E Nr
    (FederationEventsCyclesCheck.cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig) p (Nr t) = Nr t'.
  Proof.
    induction p as [| e p IH]; intros t; [exists t; reflexivity |].
    exact (IH (FederationEventsCyclesCheck.cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig e (Nr t))).
  Qed.

  Theorem cyc_factor_sound_gc :
    FederationEventsCyclesCheck.C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    FederationEventsCyclesCheck.C2cyc Lc Hc Rg cvalid E reg sig I Hs ->
    forall t, FederationEventsCycles.GC (Loc * Sh) E Nr
      (FederationEventsCyclesCheck.cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig) nreg I (Nr t).
  Proof.
    intros H1 H2 t p a b Hab. destruct (cyc_grun_nf p t) as [t' ->].
    exact (cyc_factor_sound H1 H2 (Nr t', a, b) (conj (ex_intro _ t' eq_refl) Hab)).
  Qed.
End CycFactor.

(* ============================================================================================ *)
(* 5. The hypothesis shared with state gluing                                                   *)
(* ============================================================================================ *)

(* c_local (a repair reads only its sources) is SheafGluing's R1 for the repair read at any
   fixed target values. *)
Theorem common_r1 : forall V src f valid rho E reg sig o,
  FederationEvents.Common V src f valid rho E reg sig o ->
  forall y : nat -> V, SheafGluing.R1 src (fun B s => f B s (y B)).
Proof.
  intros V src f valid rho E reg sig o HC y B s t H.
  exact (FederationEvents.c_local _ _ _ _ _ _ _ _ _ HC B s t (y B) H).
Qed.

(* common_r1 is one direction from all of Common. The identification the docs state ("c_local is
   R1 for the repair read at any fixed target values") is this equivalence, with c_local alone. *)
Theorem c_local_iff_r1 : forall (V : Type) (src : nat -> list nat) (f : nat -> (nat -> V) -> V -> V),
  (forall j z1 z2 x, (forall k, In k (src j) -> z1 k = z2 k) -> f j z1 x = f j z2 x) <->
  (forall y : nat -> V, SheafGluing.R1 src (fun B s => f B s (y B))).
Proof.
  intros V src f. split.
  - intros H y B s t Hst. exact (H B s t (y B) Hst).
  - intros H j z1 z2 x Hz. exact (H (fun _ => x) j z1 z2 Hz).
Qed.

(* The two P halves side by side on one acyclic federation: a conjunction, not a combined
   descent theorem. Under Common and a valid consistent start, the repair read at any fixed
   target values glues on every refining cover (SheafGluing.gluing, through common_r1), and trace
   convergence is exactly interface state descent plus local history descent (fed_exact_P). *)
Theorem fed_state_and_interaction : forall V src f valid rho E reg sig I o,
  FederationEvents.Common V src f valid rho E reg sig o ->
  forall s0, FederationEvents.Inv V valid s0 -> FederationEvents.Cons V f o s0 ->
  (forall (y : nat -> V) (rho' : nat -> V -> V) (get : nat -> V -> V) (C : list (list nat)),
     SheafGluing.Refines src C -> SheafGluing.GluesFor src rho' get (fun B s => f B s (y B)) C) /\
  (FederationEventsConverse.TraceConv V f rho E reg sig I o s0 <->
   FederationEventsConverse.C1R1 V f rho E reg sig o s0 /\ FederationEventsConverse.C2R V f rho E reg sig I o s0).
Proof.
  intros V src f valid rho E reg sig I o HC s0 Hi Hc. split.
  - intros y rho' get C Hr fam d Hcov Hcomp Hl. subst C.
    exact (proj1 (SheafGluing.gluing src rho' get _ (common_r1 V src f valid rho E reg sig o HC y)
                    fam d Hcomp Hl Hr)).
  - exact (fed_exact_P V src f valid rho E reg sig I o HC s0 Hi Hc).
Qed.
