(* FederationEvents.v: convergence for EVENT INTERLEAVINGS ACROSS REGISTRIES in an acyclic
   federation, mechanized axiom-free.

   The gap. Federation.v, FederationOrder.v, Categorical.v and Chaotic.v establish that the
   federated normalizer is well defined and independent of the order in which it visits
   registries. None of them says what happens when LOCAL EVENTS on a target registry interleave
   with changes propagated from its sources. They can diverge: a target event that reads a
   variable the morphism overwrites (a "shared" variable) sees a different value depending on
   whether a source event was propagated first. Every per-registry condition (each registry
   convergent, M1, acyclic authority) can hold and the federation still reaches two different
   states (audit_counterexample below: sold = 0 versus sold = 1).

   Model (faithful to gsm's FedMachine; federation.go, federation_machine.go).
   Registries are indexed by nat; a federated state t : nat -> V gives every registry its state.
     - valid j x       : x satisfies registry j's invariants.
     - rho j           : registry j's normalizer (gsm Machine.Normalize, phase 1 of rho_Fed).
     - f j t x         : morphism repair of registry j (phase 2): overwrite the shared component of
                         x with the image computed from the sources src j of j in t. For a single
                         source this is the morphism Map; for a multi-source target it is the
                         Resolver; for a source registry it is the identity. It reads t only
                         through src j (c_local), preserves validity (c_m1: M1 / R2), and a later
                         overwrite absorbs an earlier one (c_absorb: follows from gsm's
                         well-formedness "Map writes only Shared()" plus source-determinacy R1).
     - sig e           : the component step of event e on registry reg e (gsm Machine.Apply: the
                         event then the component normalizer, so it maps valid states to valid
                         states, c_sig).
     - o               : the registries in a topological order (topoF: no registry reads a later
                         or equal one). Acyclic federations only; cyclic (AllowMonotoneCycles)
                         networks are out of scope here.
   N t  = phase 1 (rho on every component) then phase 2 (repair every registry in order o):
          FedMachine.Normalize.
   applyF e t = N (t with component reg e replaced by sig e (t (reg e))): FedMachine.Apply.
   runF       = a sequence of FedMachine.Apply calls over the combined event alphabet.

   The condition. Write ow_z x := f j z x (overwrite with the image of source states z), and call
   x CONSISTENT when x = ow_z' x for some valid source states z' (its shared part is an image).
     C1 (cross-registry CC, the form gsm checks): for every event e of j, all valid source states
        z and z', and every valid consistent b (b = ow_z' b):
          ow_z (sig e (ow_z b)) = ow_z (sig e b).
        In gsm terms: ow(rho_B(e(ow(b, v'))), v') = ow(rho_B(e(b)), v') for every image v' and
        every valid b whose shared part is an image. The final overwrite is on BOTH sides, so a
        target event that only writes a shared variable passes.
     C2 (repaired CC): for declared-independent events e1, e2 of the same registry j, valid
        source states z and valid b consistent with z:
          ow_z (sig e2 (ow_z (sig e1 b))) = ow_z (sig e1 (ow_z (sig e2 b))).
        This is CC of the steps "event then repair". For a source registry (f = identity) it is
        exactly the registry's own CC. For a target it is NOT implied by the target's own CC plus
        C1: c2_counterexample exhibits a target whose two events commute locally, C1 holds, and
        the federation still diverges, because the repair between the two events erases what
        the first event wrote into a shared variable.

   Results.
     fed_events_commute / fed_interleavings_converge / fed_permutations_converge (machine model):
        under Common + C1 + C2, from any valid consistent state (any FedMachine state), two
        FedMachine.Apply sequences over the combined alphabet that differ by swapping events of
        different registries, or declared-independent events of one registry, reach the same
        federated state. With every same-registry pair declared, any permutation does.
     propagation_flush / dist_interleavings_converge (distributed model, explicit propagation
        steps as in Component + SharedProjection + MergeProjection): a run is any word of local
        events and propagation steps; after propagation completes (N), the result equals the
        FedMachine run of its events, so all interleavings agree. This needs the stronger XU
        (C1 for EVERY valid b, not only consistent ones) plus each registry's own CC, because a
        node may apply events to a state whose shared part a local event has just overwritten.
        xu_implies_c1_c2 shows XU + local CC implies C1 + C2.
     audit_counterexample : Common, C2, local CC hold; C1 fails; two interleavings diverge.
     c2_counterexample    : Common, C1, local CC hold; C2 fails; two interleavings diverge.
     supply_instance / supply_converges : a concrete federation discharging every hypothesis of
        both models (non-vacuity), whose target event writes a shared variable, so the stronger
        commute-without-repair form (Candidate) fails there although the federation converges.

   States are compared pointwise (feq), so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace.
Import ListNotations.

Section Fed.
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

  Definition upd (t : nat -> V) (w : nat) (x : V) : nat -> V :=
    fun k => if Nat.eqb k w then x else t k.

  Definition feq (t u : nat -> V) : Prop := forall k, t k = u k.

  Definition Inv (t : nat -> V) : Prop := forall k, valid k (t k).

  (* Topological order: no registry reads itself or a registry placed after it. *)
  Fixpoint topoF (l : list nat) : Prop :=
    match l with
    | [] => True
    | a :: r => ~ In a r /\ (forall k, In k (src a) -> ~ In k (a :: r)) /\ topoF r
    end.

  (* The per-registry conditions gsm already checks (or that hold by construction). *)
  Record Common : Prop := {
    c_local : forall j z1 z2 x, (forall k, In k (src j) -> z1 k = z2 k) -> f j z1 x = f j z2 x;
    c_topo : topoF o;
    c_m1 : forall j z x, Inv z -> valid j x -> valid j (f j z x);
    c_absorb : forall j z z' x, Inv z -> Inv z' -> valid j x -> f j z (f j z' x) = f j z x;
    c_rho : forall j x, valid j x -> rho j x = x;
    c_sig : forall e x, valid (reg e) x -> valid (reg e) (sig e x);
    c_reg : forall e, In (reg e) o
  }.

  (* C1: cross-registry CC, quantified over consistent target states (the gsm check). *)
  Definition C1 : Prop :=
    forall e z z' b, Inv z -> Inv z' -> valid (reg e) b -> b = f (reg e) z' b ->
      f (reg e) z (sig e (f (reg e) z b)) = f (reg e) z (sig e b).

  (* C2: CC of "event then repair" for declared-independent events of one registry. *)
  Definition C2 : Prop :=
    forall e1 e2 z b, reg e1 = reg e2 -> I e1 e2 -> Inv z -> valid (reg e1) b ->
      b = f (reg e1) z b ->
      f (reg e1) z (sig e2 (f (reg e1) z (sig e1 b))) =
      f (reg e1) z (sig e1 (f (reg e1) z (sig e2 b))).

  (* XU: C1 for every valid target state (needed when propagation is a separate step). *)
  Definition XU : Prop :=
    forall e z b, Inv z -> valid (reg e) b ->
      f (reg e) z (sig e (f (reg e) z b)) = f (reg e) z (sig e b).

  (* Each registry's own CC on its declared pairs (what gsm's component Build checks). *)
  Definition LocalCC : Prop :=
    forall e1 e2 x, reg e1 = reg e2 -> I e1 e2 -> valid (reg e1) x ->
      sig e1 (sig e2 x) = sig e2 (sig e1 x).

  (* The first-draft condition: the event commutes with re-projection without a final repair. *)
  Definition Candidate : Prop :=
    forall e z b, Inv z -> valid (reg e) b ->
      f (reg e) z (sig e b) = sig e (f (reg e) z b).

  (* Federated independence: different registries, or declared independent. *)
  Definition Ifed (e1 e2 : E) : Prop := reg e1 <> reg e2 \/ I e1 e2.

  Definition fstep (t : nat -> V) (j : nat) : nat -> V := upd t j (f j t (t j)).
  Definition frun (l : list nat) (t : nat -> V) : nat -> V := fold_left fstep l t.
  Definition N (t : nat -> V) : nat -> V := frun o (fun k => rho k (t k)).
  Definition evstep (e : E) (t : nat -> V) : nat -> V := upd t (reg e) (sig e (t (reg e))).
  Definition applyF (e : E) (t : nat -> V) : nat -> V := N (evstep e t).
  Definition runF (es : list E) (t : nat -> V) : nat -> V :=
    fold_left (fun st e => applyF e st) es t.

  (* Morphism-consistent: every registry's shared component is its sources' image. *)
  Definition Cons (t : nat -> V) : Prop := forall j, In j o -> t j = f j t (t j).

  Section Core.
  Hypothesis HC : Common.

  Lemma upd_eq : forall t w x, upd t w x w = x.
  Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma upd_neq : forall t w x k, k <> w -> upd t w x k = t k.
  Proof. intros t w x k H. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

  Lemma feq_sym : forall t u, feq t u -> feq u t.
  Proof. intros t u H k. symmetry. apply H. Qed.

  Lemma feq_trans : forall t u w, feq t u -> feq u w -> feq t w.
  Proof. intros t u w H1 H2 k. rewrite H1. apply H2. Qed.

  Lemma fstep_eq : forall t a, fstep t a a = f a t (t a).
  Proof. intros. apply upd_eq. Qed.

  Lemma fstep_neq : forall t a k, k <> a -> fstep t a k = t k.
  Proof. intros. apply upd_neq. assumption. Qed.

  Lemma evstep_at : forall e t j, j = reg e -> evstep e t j = sig e (t j).
  Proof. intros e t j ->. apply upd_eq. Qed.

  Lemma evstep_off : forall e t j, j <> reg e -> evstep e t j = t j.
  Proof. intros. apply upd_neq. assumption. Qed.

  Lemma frun_out : forall l t k, ~ In k l -> frun l t k = t k.
  Proof.
    induction l as [| a l IH]; intros t k H; [reflexivity |].
    simpl in H. change (frun (a :: l) t) with (frun l (fstep t a)).
    rewrite IH by tauto. apply fstep_neq. intro E'. apply H. left. symmetry. exact E'.
  Qed.

  Lemma frun_solves :
    forall l t, topoF l -> forall j, In j l -> frun l t j = f j (frun l t) (t j).
  Proof.
    induction l as [| a l IH]; intros t Ht j Hj; [destruct Hj |].
    destruct Ht as [Ha [Hs Hr]].
    change (frun (a :: l) t) with (frun l (fstep t a)).
    destruct (Nat.eq_dec j a) as [-> | Hne].
    - rewrite (frun_out l _ a Ha), fstep_eq. apply (c_local HC).
      intros k Hk. specialize (Hs k Hk).
      rewrite frun_out by (intro H'; apply Hs; right; exact H').
      symmetry. apply fstep_neq. intro E'. apply Hs. left. symmetry. exact E'.
    - destruct Hj as [E' | Hj]; [congruence |].
      rewrite (IH (fstep t a) Hr j Hj). rewrite fstep_neq by exact Hne. reflexivity.
  Qed.

  Lemma fstep_ext : forall t u a, feq t u -> feq (fstep t a) (fstep u a).
  Proof.
    intros t u a H k. unfold fstep, upd. destruct (Nat.eqb k a); [| apply H].
    rewrite (H a). apply (c_local HC). intros. apply H.
  Qed.

  Lemma frun_ext : forall l t u, feq t u -> feq (frun l t) (frun l u).
  Proof.
    induction l as [| a l IH]; intros t u H; [exact H |].
    apply IH. apply fstep_ext. exact H.
  Qed.

  Lemma fstep_inv : forall t a, Inv t -> Inv (fstep t a).
  Proof.
    intros t a H k. unfold fstep, upd. destruct (Nat.eqb k a) eqn:Ek; [| apply H].
    apply Nat.eqb_eq in Ek. subst k. apply (c_m1 HC); [exact H | apply H].
  Qed.

  Lemma frun_inv : forall l t, Inv t -> Inv (frun l t).
  Proof.
    induction l as [| a l IH]; intros t H; [exact H |].
    apply IH. apply fstep_inv. exact H.
  Qed.

  (* Uniqueness of the solution of the repair equations along a topological order. *)
  Lemma solve_unique :
    forall l z1 z2 u1 u2, topoF l ->
      (forall k, ~ In k l -> z1 k = z2 k) ->
      (forall j, In j l -> z1 j = f j z1 (u1 j)) ->
      (forall j, In j l -> z2 j = f j z2 (u2 j)) ->
      (forall j, In j l -> f j z1 (u1 j) = f j z1 (u2 j)) ->
      feq z1 z2.
  Proof.
    induction l as [| a l IH]; intros z1 z2 u1 u2 Ht Hout H1 H2 H12.
    - intro k. apply Hout. intros [].
    - destruct Ht as [Ha [Hs Hr]].
      assert (Ea : z1 a = z2 a).
      { rewrite (H1 a (or_introl eq_refl)), (H2 a (or_introl eq_refl)).
        rewrite (H12 a (or_introl eq_refl)). apply (c_local HC).
        intros k Hk. apply Hout. apply Hs. exact Hk. }
      apply (IH z1 z2 u1 u2 Hr).
      + intros k Hk. destruct (Nat.eq_dec k a) as [-> | Hne]; [exact Ea |].
        apply Hout. intros [E' | E']; [congruence | contradiction].
      + intros j Hj. apply H1. right. exact Hj.
      + intros j Hj. apply H2. right. exact Hj.
      + intros j Hj. apply H12. right. exact Hj.
  Qed.

  Lemma rho_phase : forall t, Inv t -> feq (fun k => rho k (t k)) t.
  Proof. intros t H k. apply (c_rho HC). apply H. Qed.

  Lemma N_frun : forall t, Inv t -> feq (N t) (frun o t).
  Proof. intros t H. unfold N. apply frun_ext. apply rho_phase. exact H. Qed.

  Lemma N_ext : forall t u, feq t u -> feq (N t) (N u).
  Proof. intros t u H. unfold N. apply frun_ext. intro k. rewrite H. reflexivity. Qed.

  Lemma N_inv : forall t, Inv t -> Inv (N t).
  Proof.
    intros t H. unfold N. apply frun_inv. intro k. rewrite (c_rho HC); apply H.
  Qed.

  Lemma evstep_inv : forall e t, Inv t -> Inv (evstep e t).
  Proof.
    intros e t H k. unfold evstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply H].
    apply Nat.eqb_eq in Ek. subst k. apply (c_sig HC). apply H.
  Qed.

  Lemma evstep_ext : forall e t u, feq t u -> feq (evstep e t) (evstep e u).
  Proof.
    intros e t u H k. unfold evstep, upd. destruct (Nat.eqb k (reg e)); [rewrite H; reflexivity | apply H].
  Qed.

  Lemma applyF_ext : forall e t u, feq t u -> feq (applyF e t) (applyF e u).
  Proof. intros. unfold applyF. apply N_ext. apply evstep_ext. assumption. Qed.

  Lemma applyF_inv : forall e t, Inv t -> Inv (applyF e t).
  Proof. intros. unfold applyF. apply N_inv. apply evstep_inv. assumption. Qed.

  (* The federated normal form satisfies every morphism invariant. *)
  Lemma N_cons : forall t, Inv t -> Cons (N t).
  Proof.
    intros t H j Hj.
    assert (Hp : Inv (fun k => rho k (t k))) by (intro k; rewrite (c_rho HC); apply H).
    assert (Hs : N t j = f j (N t) (rho j (t j))).
    { unfold N. exact (frun_solves o (fun k => rho k (t k)) (c_topo HC) j Hj). }
    rewrite Hs at 2. rewrite (c_absorb HC); [exact Hs | apply N_inv; exact H | apply N_inv; exact H | apply Hp].
  Qed.

  Lemma applyF_cons : forall e t, Inv t -> Cons (applyF e t).
  Proof. intros. unfold applyF. apply N_cons. apply evstep_inv. assumption. Qed.

  Lemma runF_ext : forall es t u, feq t u -> feq (runF es t) (runF es u).
  Proof.
    induction es as [| e es IH]; intros t u H; [exact H |].
    apply IH. apply applyF_ext. exact H.
  Qed.

  Lemma runF_inv : forall es t, Inv t -> Inv (runF es t).
  Proof.
    induction es as [| e es IH]; intros t H; [exact H |].
    apply IH. apply applyF_inv. exact H.
  Qed.

  Lemma runF_cons : forall es t, Inv t -> Cons t -> Cons (runF es t).
  Proof.
    induction es as [| e es IH]; intros t H Hc; [exact Hc |].
    apply IH; [apply applyF_inv | apply applyF_cons]; exact H.
  Qed.

  Lemma runF_app : forall l r t, runF (l ++ r) t = runF r (runF l t).
  Proof. intros. unfold runF. apply fold_left_app. Qed.

  Lemma runF_two : forall a b r t, runF (a :: b :: r) t = runF r (applyF b (applyF a t)).
  Proof. reflexivity. Qed.

  End Core.

  (* ------------------------------------------------------------------------------------- *)
  (* The machine model: FedMachine.Apply sequences, under C1 + C2.                          *)
  (* ------------------------------------------------------------------------------------- *)
  Section Machine.
  Hypothesis HC : Common.
  Hypothesis H1 : C1.
  Hypothesis H2 : C2.

  (* An image produced from any valid source states can be replaced by the current one. *)
  Lemma c1_shift :
    forall e j z z' y, j = reg e -> Inv z -> Inv z' -> valid j y ->
      f j z (sig e (f j z' y)) = f j z (sig e (f j z y)).
  Proof.
    intros e j z z' y -> Hz Hz' Hy.
    assert (Hb : f (reg e) z' y = f (reg e) z' (f (reg e) z' y)).
    { symmetry. apply (c_absorb HC); assumption. }
    pose proof (H1 e z z' (f (reg e) z' y) Hz Hz' ((c_m1 HC) _ _ _ Hz' Hy) Hb) as Hc.
    rewrite (c_absorb HC) in Hc by assumption. symmetry. exact Hc.
  Qed.

  Lemma c1_cons :
    forall e j z z' w x, j = reg e -> Inv z -> Inv z' -> Inv w -> valid j x -> x = f j w x ->
      f j z (sig e (f j z' x)) = f j z (sig e x).
  Proof.
    intros e j z z' w x Hj Hz Hz' Hw Hx Hcx.
    rewrite (c1_shift e j z z' x Hj Hz Hz' Hx). subst j. apply (H1 e z w x); assumption.
  Qed.

  (* Headline 1: two federated events commute from any valid consistent state, when they are
     on different registries or declared independent. *)
  Theorem fed_events_commute :
    forall s e1 e2, Inv s -> Cons s -> Ifed e1 e2 ->
      feq (applyF e2 (applyF e1 s)) (applyF e1 (applyF e2 s)).
  Proof.
    intros s e1 e2 Hs Hcs Hi.
    pose proof (c_topo HC) as Ht.
    set (z1 := frun o (evstep e1 s)). set (z2 := frun o (evstep e2 s)).
    set (z12 := frun o (evstep e2 z1)). set (z21 := frun o (evstep e1 z2)).
    assert (I1 : Inv z1) by (apply frun_inv, evstep_inv; assumption).
    assert (I2 : Inv z2) by (apply frun_inv, evstep_inv; assumption).
    assert (I12 : Inv z12) by (apply frun_inv, evstep_inv; assumption).
    assert (I21 : Inv z21) by (apply frun_inv, evstep_inv; assumption).
    assert (A1 : feq (applyF e1 s) z1) by (apply N_frun, evstep_inv; assumption).
    assert (A2 : feq (applyF e2 s) z2) by (apply N_frun, evstep_inv; assumption).
    assert (A12 : feq (applyF e2 (applyF e1 s)) z12).
    { eapply feq_trans; [apply applyF_ext; [exact HC | exact A1] |].
      apply N_frun; [exact HC |]. apply evstep_inv; assumption. }
    assert (A21 : feq (applyF e1 (applyF e2 s)) z21).
    { eapply feq_trans; [apply applyF_ext; [exact HC | exact A2] |].
      apply N_frun; [exact HC |]. apply evstep_inv; assumption. }
    eapply feq_trans; [exact A12 |]. eapply feq_trans; [| apply feq_sym; exact A21].
    pose proof (c_reg HC e1) as R1. pose proof (c_reg HC e2) as R2.
    assert (S1 : forall j, In j o -> z1 j = f j z1 (evstep e1 s j))
      by (intros; apply frun_solves; assumption).
    assert (S2 : forall j, In j o -> z2 j = f j z2 (evstep e2 s j))
      by (intros; apply frun_solves; assumption).
    apply (solve_unique HC o z12 z21 (evstep e2 z1) (evstep e1 z2) Ht).
    - intros k Hk. unfold z12, z21. rewrite !frun_out by assumption.
      rewrite !evstep_off by (intro E'; subst; contradiction).
      unfold z1, z2. rewrite !frun_out by assumption.
      rewrite !evstep_off by (intro E'; subst; contradiction). reflexivity.
    - intros. apply frun_solves; assumption.
    - intros. apply frun_solves; assumption.
    - intros j Hj. pose proof (Hcs j Hj) as Hx. pose proof (Hs j) as Vx.
      destruct (Nat.eq_dec j (reg e1)) as [J1 | J1]; destruct (Nat.eq_dec j (reg e2)) as [J2 | J2].
      + (* the same registry: C2 *)
        assert (Iab : I e1 e2) by (destruct Hi as [Hn | Hab]; [congruence | exact Hab]).
        rewrite (evstep_at e2 z1 j J2), (evstep_at e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_at e1 s j J1), (evstep_at e2 s j J2).
        assert (V1 : valid j (sig e1 (s j))) by (rewrite J1; apply (c_sig HC); rewrite <- J1; exact Vx).
        assert (V2 : valid j (sig e2 (s j))) by (rewrite J2; apply (c_sig HC); rewrite <- J2; exact Vx).
        rewrite (c1_shift e2 j z12 z1 _ J2 I12 I1 V1).
        rewrite (c1_shift e1 j z12 z2 _ J1 I12 I2 V2).
        rewrite <- (c1_cons e1 j z12 z12 s (s j) J1 I12 I12 Hs Vx Hx).
        rewrite <- (c1_cons e2 j z12 z12 s (s j) J2 I12 I12 Hs Vx Hx).
        subst j.
        apply (H2 e1 e2 z12 (f (reg e1) z12 (s (reg e1)))); [assumption | assumption | assumption | |].
        * apply (c_m1 HC); assumption.
        * symmetry. apply (c_absorb HC); assumption.
      + (* j is e1's registry only *)
        rewrite (evstep_off e2 z1 j J2), (evstep_at e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_at e1 s j J1), (evstep_off e2 s j J2).
        assert (V1 : valid j (sig e1 (s j))) by (rewrite J1; apply (c_sig HC); rewrite <- J1; exact Vx).
        rewrite (c_absorb HC) by assumption.
        symmetry. apply (c1_cons e1 j z12 z2 s (s j) J1 I12 I2 Hs Vx Hx).
      + (* j is e2's registry only *)
        rewrite (evstep_at e2 z1 j J2), (evstep_off e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_off e1 s j J1), (evstep_at e2 s j J2).
        assert (V2 : valid j (sig e2 (s j))) by (rewrite J2; apply (c_sig HC); rewrite <- J2; exact Vx).
        rewrite (c_absorb HC j z12 z2) by assumption.
        apply (c1_cons e2 j z12 z1 s (s j) J2 I12 I1 Hs Vx Hx).
      + (* neither: both sides are re-projections of the same state *)
        rewrite (evstep_off e2 z1 j J2), (evstep_off e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_off e1 s j J1), (evstep_off e2 s j J2).
        rewrite !(c_absorb HC) by assumption. reflexivity.
  Qed.

  (* Headline 2: interleavings that differ by swapping federated-independent events converge. *)
  Theorem fed_interleavings_converge :
    forall es1 es2, tequiv Ifed es1 es2 ->
      forall s, Inv s -> Cons s -> feq (runF es1 s) (runF es2 s).
  Proof.
    intros es1 es2 H. induction H as [ l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H12 IH12 H23 IH23 ];
      intros s Hs Hc.
    - intro k. reflexivity.
    - rewrite !runF_app, !runF_two. apply runF_ext; [exact HC |].
      apply fed_events_commute; [apply runF_inv | apply runF_cons | ]; assumption.
    - apply feq_sym. apply IH; assumption.
    - eapply feq_trans; [apply IH12 | apply IH23]; assumption.
  Qed.

  (* Headline 3: with every same-registry pair declared, every permutation converges. *)
  Theorem fed_permutations_converge :
    (forall e1 e2, reg e1 = reg e2 -> I e1 e2) ->
    forall es1 es2, Permutation es1 es2 ->
      forall s, Inv s -> Cons s -> feq (runF es1 s) (runF es2 s).
  Proof.
    intros Htot es1 es2 Hp. apply fed_interleavings_converge.
    apply (perm_tequiv_total Ifed (fun _ => True)); [| exact Hp |].
    - intros a b _ _. destruct (Nat.eq_dec (reg a) (reg b)) as [E' | Ne];
        [right; apply Htot; exact E' | left; exact Ne].
    - apply Forall_forall. intros. trivial.
  Qed.

  End Machine.

  (* ------------------------------------------------------------------------------------- *)
  (* The distributed model: local events and propagation steps interleave freely.           *)
  (* ------------------------------------------------------------------------------------- *)
  Inductive act : Type :=
  | DEv : E -> act          (* a local event on its registry, no propagation *)
  | DProp : nat -> act.     (* registry j merges the projection of its sources' current states *)

  Definition dstep (a : act) (t : nat -> V) : nat -> V :=
    match a with DEv e => evstep e t | DProp j => fstep t j end.

  Fixpoint drun (w : list act) (t : nat -> V) : nat -> V :=
    match w with [] => t | a :: w' => drun w' (dstep a t) end.

  Fixpoint evs (w : list act) : list E :=
    match w with
    | [] => []
    | DEv e :: w' => e :: evs w'
    | DProp _ :: w' => evs w'
    end.

  Definition okact (a : act) : Prop := match a with DEv _ => True | DProp j => In j o end.

  Section Distributed.
  Hypothesis HC : Common.
  Hypothesis HX : XU.
  Hypothesis HL : LocalCC.

  Theorem xu_implies_c1_c2 : C1 /\ C2.
  Proof.
    split.
    - intros e z z' b Hz _ Hb _. apply HX; assumption.
    - intros e1 e2 z b E12 Iab Hz Hb _.
      assert (Hb2 : valid (reg e2) b) by (rewrite <- E12; exact Hb).
      assert (L : f (reg e1) z (sig e2 (f (reg e1) z (sig e1 b))) = f (reg e1) z (sig e2 (sig e1 b))).
      { rewrite E12. apply HX; [exact Hz |]. rewrite <- E12. apply (c_sig HC). exact Hb. }
      assert (R : f (reg e1) z (sig e1 (f (reg e1) z (sig e2 b))) = f (reg e1) z (sig e1 (sig e2 b))).
      { apply HX; [exact Hz |]. rewrite E12. apply (c_sig HC). exact Hb2. }
      rewrite L, R, (HL e1 e2 b E12 Iab Hb). reflexivity.
  Qed.

  Lemma xu_strong :
    forall e z z' y, Inv z -> Inv z' -> valid (reg e) y ->
      f (reg e) z (sig e (f (reg e) z' y)) = f (reg e) z (sig e y).
  Proof.
    intros e z z' y Hz Hz' Hy.
    assert (Hc1 : C1) by (intros e' w w' b Hw _ Hb _; apply HX; assumption).
    rewrite (c1_shift HC Hc1 e (reg e) z z' y eq_refl Hz Hz' Hy).
    apply HX; assumption.
  Qed.

  Lemma flush_ev : forall e t, Inv t -> feq (N (evstep e t)) (applyF e (N t)).
  Proof.
    intros e t Ht.
    pose proof (c_topo HC) as To. pose proof (c_reg HC e) as Re.
    set (n := frun o t).
    assert (In_ : Inv n) by (apply frun_inv; assumption).
    eapply feq_trans; [apply N_frun; [exact HC | apply evstep_inv; assumption] |].
    unfold applyF. eapply feq_trans; [| apply feq_sym, N_ext, evstep_ext, N_frun; assumption].
    eapply feq_trans; [| apply feq_sym, N_frun; [exact HC | apply evstep_inv; assumption]].
    assert (Iz : Inv (frun o (evstep e t))) by (apply frun_inv, evstep_inv; assumption).
    apply (solve_unique HC o _ _ (evstep e t) (evstep e n) To).
    - intros k Hk. rewrite !frun_out by assumption.
      rewrite !evstep_off by (intro E'; subst; contradiction).
      unfold n. rewrite frun_out by assumption. reflexivity.
    - intros. apply frun_solves; assumption.
    - intros. apply frun_solves; assumption.
    - intros j Hj.
      assert (Hn : n j = f j n (t j)) by (exact (frun_solves HC o t To j Hj)).
      destruct (Nat.eq_dec j (reg e)) as [J | Ne].
      + rewrite !(evstep_at e _ j J). rewrite Hn. rewrite J.
        symmetry. apply xu_strong; [exact Iz | exact In_ | apply Ht].
      + rewrite !(evstep_off e _ j Ne). rewrite Hn.
        symmetry. apply (c_absorb HC); [exact Iz | exact In_ | apply Ht].
  Qed.

  Lemma flush_prop : forall j t, Inv t -> In j o -> feq (N (fstep t j)) (N t).
  Proof.
    intros j t Ht Hj. pose proof (c_topo HC) as To.
    eapply feq_trans; [apply N_frun; [exact HC | apply fstep_inv; assumption] |].
    eapply feq_trans; [| apply feq_sym, N_frun; assumption].
    assert (Iz : Inv (frun o (fstep t j))) by (apply frun_inv, fstep_inv; assumption).
    apply (solve_unique HC o _ _ (fstep t j) t To).
    - intros k Hk. rewrite !frun_out by assumption.
      apply fstep_neq. intro E'. subst. contradiction.
    - intros. apply frun_solves; assumption.
    - intros. apply frun_solves; assumption.
    - intros k Hk. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite fstep_eq. apply (c_absorb HC); [exact Iz | exact Ht | apply Ht].
      + rewrite fstep_neq by exact Ne. reflexivity.
  Qed.

  Lemma dstep_inv : forall a t, Inv t -> Inv (dstep a t).
  Proof. intros [e | j] t H; [apply evstep_inv | apply fstep_inv]; assumption. Qed.

  (* Headline 4: once propagation completes, an interleaving of events and propagation steps
     yields exactly the FedMachine run of its events. *)
  Theorem propagation_flush :
    forall w s, Inv s -> Forall okact w -> feq (N (drun w s)) (runF (evs w) (N s)).
  Proof.
    induction w as [| a w IH]; intros s Hs Hw.
    - intro k. reflexivity.
    - inversion Hw as [| ? ? Ha Hw']; subst. simpl.
      eapply feq_trans; [apply IH; [apply dstep_inv | ]; assumption |].
      destruct a as [e | j]; simpl.
      + apply runF_ext; [exact HC |]. apply flush_ev. exact Hs.
      + apply runF_ext; [exact HC |]. apply flush_prop; assumption.
  Qed.

  (* Headline 5: all interleavings of events and propagation steps converge once propagation
     completes, whenever their event sequences are federated-trace-equivalent. *)
  Theorem dist_interleavings_converge :
    forall w1 w2 s, Inv s -> Forall okact w1 -> Forall okact w2 ->
      tequiv Ifed (evs w1) (evs w2) -> feq (N (drun w1 s)) (N (drun w2 s)).
  Proof.
    intros w1 w2 s Hs Hw1 Hw2 Ht.
    destruct xu_implies_c1_c2 as [Hc1 Hc2].
    eapply feq_trans; [apply propagation_flush; assumption |].
    eapply feq_trans; [| apply feq_sym, propagation_flush; assumption].
    apply (fed_interleavings_converge HC Hc1 Hc2 _ _ Ht);
      [apply N_inv | apply N_cons]; assumption.
  Qed.

  End Distributed.
End Fed.

(* ========================================================================================= *)
(* Concrete instances. Registry 0 is the source, registry 1 the target, o = [0; 1].          *)
(* ========================================================================================= *)

Definition src2 (k : nat) : list nat := match k with 1 => [0] | _ => [] end.

Lemma topo2 : topoF src2 [0; 1].
Proof.
  simpl. repeat split.
  - intros [H | []]. discriminate.
  - intros k [].
  - intros [].
  - intros k [<- | []] [H | []]. discriminate.
Qed.

(* ----- the supply chain: a manufacturer recall drives the supplier's listed flag ----- *)
(* State = (flag, count). Registry 0: (recalled, _). Registry 1: (listed_ok, sold), sold <= 3. *)

Definition sp_valid (k : nat) (x : bool * nat) : Prop :=
  match k with 1 => snd x <= 3 | _ => True end.

Definition sp_f (k : nat) (z : nat -> bool * nat) (x : bool * nat) : bool * nat :=
  match k with 1 => (negb (fst (z 0)), snd x) | _ => x end.

Definition sp_rho (k : nat) (x : bool * nat) : bool * nat :=
  match k with 1 => (fst x, Nat.min (snd x) 3) | _ => x end.

Lemma sp_common_parts :
  forall (Ev : Type) (rg : Ev -> nat) (sg : Ev -> bool * nat -> bool * nat),
    (forall e x, sp_valid (rg e) x -> sp_valid (rg e) (sg e x)) ->
    (forall e, In (rg e) [0; 1]) ->
    Common (bool * nat) src2 sp_f sp_valid sp_rho Ev rg sg [0; 1].
Proof.
  intros Ev rg sg Hsg Hrg. constructor.
  - intros [| [| j]] z1 z2 x H; simpl; try reflexivity.
    rewrite (H 0); [reflexivity | left; reflexivity].
  - exact topo2.
  - intros [| [| j]] z x _ Hx; simpl in *; trivial.
  - intros [| [| j]] z z' x _ _ _; reflexivity.
  - intros [| [| j]] [b n] Hx; simpl in *; try reflexivity. rewrite Nat.min_l by exact Hx. reflexivity.
  - exact Hsg.
  - exact Hrg.
Qed.

Inductive sev : Type := Recall | Sell | Unlist.

Definition sp_reg (e : sev) : nat := match e with Recall => 0 | _ => 1 end.

(* Sell is unguarded (it reads only local state); Unlist WRITES the shared flag, which the
   morphism repair then overwrites: the authority argument of FedMachine.Apply. *)
Definition sp_sig (e : sev) (x : bool * nat) : bool * nat :=
  match e with
  | Recall => (true, snd x)
  | Sell => (fst x, Nat.min (S (snd x)) 3)
  | Unlist => (false, snd x)
  end.

Definition sp_I (_ _ : sev) : Prop := True.

Lemma sp_common : Common (bool * nat) src2 sp_f sp_valid sp_rho sev sp_reg sp_sig [0; 1].
Proof.
  apply sp_common_parts.
  - intros [] [b n] H; simpl in *; trivial; lia.
  - intros []; simpl; tauto.
Qed.

Theorem supply_instance :
  Common (bool * nat) src2 sp_f sp_valid sp_rho sev sp_reg sp_sig [0; 1] /\
  XU (bool * nat) sp_f sp_valid sev sp_reg sp_sig /\
  LocalCC (bool * nat) sp_valid sev sp_reg sp_sig sp_I /\
  C1 (bool * nat) sp_f sp_valid sev sp_reg sp_sig /\
  C2 (bool * nat) sp_f sp_valid sev sp_reg sp_sig sp_I /\
  ~ Candidate (bool * nat) sp_f sp_valid sev sp_reg sp_sig.
Proof.
  assert (Hx : XU (bool * nat) sp_f sp_valid sev sp_reg sp_sig)
    by (intros [] z [b n] _ _; reflexivity).
  assert (Hl : LocalCC (bool * nat) sp_valid sev sp_reg sp_sig sp_I)
    by (intros [] [] [b n] E' _ _; simpl in E'; try discriminate; reflexivity).
  destruct (xu_implies_c1_c2 _ _ _ _ _ _ _ _ _ _ sp_common Hx Hl) as [Hc1 Hc2].
  split; [exact sp_common |]. split; [exact Hx |]. split; [exact Hl |].
  split; [exact Hc1 |]. split; [exact Hc2 |].
  intro Hc.
  assert (Hz : Inv (bool * nat) sp_valid (fun _ => (false, 0)))
    by (intros [| [| k]]; simpl; lia).
  assert (Hb : sp_valid (sp_reg Unlist) (true, 0)) by (simpl; lia).
  pose proof (Hc Unlist (fun _ => (false, 0)) (true, 0) Hz Hb) as Hd.
  simpl in Hd. discriminate Hd.
Qed.

(* Non-vacuity: the general theorem applies to the instance; every reordering converges. *)
Theorem supply_converges :
  forall es1 es2 s, Permutation es1 es2 ->
    Inv (bool * nat) sp_valid s -> Cons (bool * nat) sp_f [0; 1] s ->
    feq (bool * nat) (runF (bool * nat) sp_f sp_rho sev sp_reg sp_sig [0; 1] es1 s)
                     (runF (bool * nat) sp_f sp_rho sev sp_reg sp_sig [0; 1] es2 s).
Proof.
  intros es1 es2 s Hp Hs Hc.
  destruct supply_instance as [Hcm [_ [_ [Hc1 [Hc2 _]]]]].
  apply (fed_permutations_converge _ _ _ _ _ _ _ _ sp_I _ Hcm Hc1 Hc2);
    [intros; exact I | exact Hp | exact Hs | exact Hc].
Qed.

(* ----- necessity of C1: the audit's counterexample (a target event reads a shared flag) ----- *)

Inductive cev : Type := CRecall | CSell.

Definition ce_reg (e : cev) : nat := match e with CRecall => 0 | CSell => 1 end.

Definition ce_sig (e : cev) (x : bool * nat) : bool * nat :=
  match e with
  | CRecall => (true, snd x)
  | CSell => if fst x then (fst x, Nat.min (S (snd x)) 3) else x
  end.

Definition ce_I (_ _ : cev) : Prop := True.

Definition ce_s0 (k : nat) : bool * nat := match k with 1 => (true, 0) | _ => (false, 0) end.

Theorem audit_counterexample :
  Common (bool * nat) src2 sp_f sp_valid sp_rho cev ce_reg ce_sig [0; 1] /\
  C2 (bool * nat) sp_f sp_valid cev ce_reg ce_sig ce_I /\
  LocalCC (bool * nat) sp_valid cev ce_reg ce_sig ce_I /\
  ~ C1 (bool * nat) sp_f sp_valid cev ce_reg ce_sig /\
  Inv (bool * nat) sp_valid ce_s0 /\ Cons (bool * nat) sp_f [0; 1] ce_s0 /\
  runF (bool * nat) sp_f sp_rho cev ce_reg ce_sig [0; 1] [CRecall; CSell] ce_s0 1 = (false, 0) /\
  runF (bool * nat) sp_f sp_rho cev ce_reg ce_sig [0; 1] [CSell; CRecall] ce_s0 1 = (false, 1).
Proof.
  split.
  { apply sp_common_parts.
    - intros [] [[] n] H; simpl in *; trivial; lia.
    - intros []; simpl; tauto. }
  split. { intros [] [] z b E' _ _ _ _; simpl in E'; try discriminate; reflexivity. }
  split. { intros [] [] x E' _ _; simpl in E'; try discriminate; reflexivity. }
  split.
  { intro Hc.
    assert (Hz : Inv (bool * nat) sp_valid (fun _ => (true, 0)))
      by (intros [| [| k]]; simpl; lia).
    assert (Hz' : Inv (bool * nat) sp_valid (fun _ => (false, 0)))
      by (intros [| [| k]]; simpl; lia).
    assert (Hb : sp_valid (ce_reg CSell) (true, 0)) by (simpl; lia).
    pose proof (Hc CSell (fun _ => (true, 0)) (fun _ => (false, 0)) (true, 0) Hz Hz' Hb eq_refl)
      as Hd.
    simpl in Hd. discriminate Hd. }
  split. { intros [| [| k]]; simpl; lia. }
  split. { intros j [<- | [<- | []]]; reflexivity. }
  split; reflexivity.
Qed.

(* ----- necessity of C2: C1 and each registry's own CC hold, yet the federation diverges ----- *)
(* State = ((slot_a, slot_b), audit). Registry 1's slot_a is shared; the source's invariant
   keeps its own slot_a closed, so the only image is slot_a = false (C1 is then immediate).
   Swap exchanges the two slots; Audit records slot_a xor slot_b. They commute on registry 1
   alone (xor is symmetric), but in the federation the repair between them erases what Swap
   moved into the shared slot, so the audit bit depends on the order. *)

Definition cw_valid (k : nat) (x : bool * bool * bool) : Prop :=
  match k with 0 => fst (fst x) = false | _ => True end.

Definition cw_f (k : nat) (z : nat -> bool * bool * bool) (x : bool * bool * bool) :
  bool * bool * bool :=
  match k with 1 => ((fst (fst (z 0)), snd (fst x)), snd x) | _ => x end.

Definition cw_rho (_ : nat) (x : bool * bool * bool) : bool * bool * bool := x.

Inductive wev : Type := Swap | Audit.

Definition cw_reg (_ : wev) : nat := 1.

Definition cw_sig (e : wev) (x : bool * bool * bool) : bool * bool * bool :=
  match e, x with
  | Swap, ((a, b), c) => ((b, a), c)
  | Audit, ((a, b), _) => ((a, b), xorb a b)
  end.

Definition cw_I (_ _ : wev) : Prop := True.

Definition cw_s0 (k : nat) : bool * bool * bool :=
  match k with 1 => ((false, true), false) | _ => ((false, false), false) end.

Theorem c2_counterexample :
  Common (bool * bool * bool) src2 cw_f cw_valid cw_rho wev cw_reg cw_sig [0; 1] /\
  C1 (bool * bool * bool) cw_f cw_valid wev cw_reg cw_sig /\
  LocalCC (bool * bool * bool) cw_valid wev cw_reg cw_sig cw_I /\
  ~ C2 (bool * bool * bool) cw_f cw_valid wev cw_reg cw_sig cw_I /\
  Inv (bool * bool * bool) cw_valid cw_s0 /\ Cons (bool * bool * bool) cw_f [0; 1] cw_s0 /\
  runF (bool * bool * bool) cw_f cw_rho wev cw_reg cw_sig [0; 1] [Audit; Swap] cw_s0 1
    = ((false, false), true) /\
  runF (bool * bool * bool) cw_f cw_rho wev cw_reg cw_sig [0; 1] [Swap; Audit] cw_s0 1
    = ((false, false), false).
Proof.
  split.
  { constructor.
    - intros [| [| j]] z1 z2 x H; simpl; try reflexivity.
      rewrite (H 0); [reflexivity | left; reflexivity].
    - exact topo2.
    - intros [| [| j]] z x _ Hx; simpl in *; trivial.
    - intros [| [| j]] z z' x _ _ _; reflexivity.
    - intros. reflexivity.
    - intros. simpl. trivial.
    - intros e. simpl. tauto. }
  split.
  { intros e z z' [[a b] c] Hz Hz' _ Hb. simpl in *.
    pose proof (Hz 0) as H0. pose proof (Hz' 0) as H0'. simpl in H0, H0'.
    rewrite H0' in Hb. injection Hb as Ha. subst a. rewrite H0. reflexivity. }
  split. { intros [] [] [[a b] c] _ _ _; simpl; try reflexivity; destruct a, b; reflexivity. }
  split.
  { intro Hc.
    assert (Hz : Inv (bool * bool * bool) cw_valid (fun _ => ((false, false), false)))
      by (intros [| [| k]]; simpl; trivial).
    pose proof (Hc Audit Swap (fun _ => ((false, false), false)) ((false, true), false)
                   eq_refl Logic.I Hz Logic.I eq_refl) as Hd.
    simpl in Hd. discriminate Hd. }
  split. { intros [| [| k]]; simpl; trivial. }
  split. { intros j [<- | [<- | []]]; reflexivity. }
  split; reflexivity.
Qed.
