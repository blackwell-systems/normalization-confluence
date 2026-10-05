(* The verification calculus for CC (Base paper, section "Verification Calculus for CC",
   label sec:calculus), mechanized: per-invariant repairs, footprints, repair locality,
   the two preparatory lemmas, the footprint theorem (refuted as stated, then corrected),
   the "Practical import" remark, pattern 1 of section 8.2 ("compensation to a canonical
   state"), and product lifting.

   Paper-label map (PAPER-MAP.md rows B31, B33, B35 to B38, B40):
     def:footprint, def:perinv, def:decomp, def:repair-locality (B33)
                              IsFootprint, PerInv, Decomposable, RepairLocal
     lem:repair-commute (B35)  base_lem_repair_commute                       (exact)
     lem:repair-idempotent (B36)
                              base_lem_repair_idempotent                    (exact)
     thm:footprint-cc1 (B37)  base_thm_footprint_cc1_refuted                (k = 0)
                              base_thm_footprint_cc1_raw_refuted            (raw events commute)
                              corrected: calc_footprint_cc1_valid_iff, calc_footprint_cc1_valid,
                              calc_footprint_cc1_iff, calc_footprint_cc1,
                              calc_fp_absorb_iff_sa, calc_cc2_strong_absorption,
                              calc_cc1_iff_commute_under_cc2,
                              calc_components_cc1_valid, calc_components_cc1_iff
                              each hypothesis needed: calc_valid_needs_commute,
                              calc_valid_needs_disjoint, calc_valid_needs_repair_local,
                              calc_all_needs_commute, calc_all_needs_absorb,
                              calc_all_needs_repair_local
                              non-vacuity: calc_clamp_instance, calc_order_cc1
     remark "Practical import" (B38)
                              base_rem_practical_import_refuted (footprints overlap),
                              calc_order_credit_repair_commute (the true half),
                              calc_order_cc1 (CC1 holds anyway, by the corrected theorem)
     8.2 pattern 1 (B31)      base_pattern1_cc1_refuted, base_pattern1_cc2_refuted;
                              corrected: calc_canonical_cc2_iff, calc_canonical_pattern;
                              non-vacuity calc_canonical_instance
     def:product, thm:product (B39, B40)
                              base_thm_product (WFC, rho*, CC1, CC2 lift),
                              base_thm_product_decomposable (repairs, footprints, locality lift);
                              non-vacuity calc_product_instance

   Setting. A registry has states St, a finite list `all` of invariant indices (the paper's
   1..k), invariants psi i : St -> bool, validity V = the conjunction of psi i over `all`
   (validD), a compensation step rho fixing valid states (Fixes) and decreasing a measure
   on invalid ones (WFC), and N = rho* (IsRhoStar: N s is an iterate of rho from s and is
   valid; since rho fixes valid states this is the paper's "least m" iterate). CC1 is
   stated at a state (CC1_at) as in the paper's Notation subsection.

   No axioms, no admits. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* ============================================================
   1. Registries, rho*, CC1, CC2, strong absorption
   ============================================================ *)

Fixpoint iter {St : Type} (n : nat) (f : St -> St) (x : St) : St :=
  match n with
  | 0 => x
  | Datatypes.S n' => iter n' f (f x)
  end.

Definition Fixes {St} (valid : St -> bool) (rho : St -> St) : Prop :=
  forall s, valid s = true -> rho s = s.

Definition WFC {St} (valid : St -> bool) (rho : St -> St) (Phi : St -> nat) : Prop :=
  forall s, valid s = false -> Phi (rho s) < Phi s.

Definition IsRhoStar {St} (valid : St -> bool) (rho N : St -> St) : Prop :=
  forall s, exists m, N s = iter m rho s /\ valid (N s) = true.

(* def:registry plus WFC plus def:rhostar. *)
Definition IsRegistry {St} (valid : St -> bool) (rho : St -> St) (Phi : St -> nat)
  (N : St -> St) : Prop :=
  Fixes valid rho /\ WFC valid rho Phi /\ IsRhoStar valid rho N.

Definition CC1_at {St E} (N : St -> St) (A : E -> St -> St) (e1 e2 : E) (s : St) : Prop :=
  N (A e2 (N (A e1 s))) = N (A e1 (N (A e2 s))).

Definition CC2_ev {St E} (valid : St -> bool) (rho N : St -> St) (A : E -> St -> St)
  (e : E) : Prop :=
  forall s, valid s = false -> N (A e s) = N (A e (rho s)).

(* Strong absorption for one event (the hypothesis of thm:strong-absorption). *)
Definition SA_ev {St E} (N : St -> St) (A : E -> St -> St) (e : E) : Prop :=
  forall s, N (A e s) = N (A e (N s)).

Lemma iter_add : forall {St} a b (f : St -> St) x, iter (a + b) f x = iter b f (iter a f x).
Proof. intros St a. induction a as [|a IH]; intros b f x; simpl; [reflexivity|apply IH]. Qed.

Lemma iter_fixed : forall {St} valid (rho : St -> St) n x,
  Fixes valid rho -> valid x = true -> iter n rho x = x.
Proof.
  intros St valid rho n. induction n as [|n IH]; intros x Hf Hv; simpl; [reflexivity|].
  rewrite (Hf x Hv). apply IH; assumption.
Qed.

Lemma iter_valid_unique : forall {St} valid (rho : St -> St) a b x,
  Fixes valid rho -> valid (iter a rho x) = true -> valid (iter b rho x) = true ->
  iter a rho x = iter b rho x.
Proof.
  intros St valid rho a b x Hf Ha Hb.
  destruct (Nat.le_ge_cases a b) as [H|H].
  - replace b with (a + (b - a)) by lia. rewrite iter_add.
    symmetry. apply (iter_fixed valid); assumption.
  - replace a with (b + (a - b)) by lia. rewrite iter_add.
    apply (iter_fixed valid); assumption.
Qed.

Lemma rho_star_fix : forall {St} valid (rho N : St -> St) s,
  Fixes valid rho -> IsRhoStar valid rho N -> valid s = true -> N s = s.
Proof.
  intros St valid rho N s Hf Hr Hv. destruct (Hr s) as [m [Hm _]].
  rewrite Hm. apply (iter_fixed valid); assumption.
Qed.

Lemma rho_star_rho : forall {St} valid (rho N : St -> St) s,
  Fixes valid rho -> IsRhoStar valid rho N -> N (rho s) = N s.
Proof.
  intros St valid rho N s Hf Hr.
  destruct (Hr s) as [m [Hm Hv]]. destruct (Hr (rho s)) as [m' [Hm' Hv']].
  rewrite Hm, Hm'. rewrite Hm in Hv. rewrite Hm' in Hv'.
  change (iter m' rho (rho s)) with (iter (Datatypes.S m') rho s) in *.
  apply (iter_valid_unique valid); assumption.
Qed.

Lemma rho_star_idem : forall {St} valid (rho N : St -> St) s,
  Fixes valid rho -> IsRhoStar valid rho N -> N (N s) = N s.
Proof.
  intros St valid rho N s Hf Hr. destruct (Hr s) as [m [_ Hv]].
  apply (rho_star_fix valid rho); assumption.
Qed.

Lemma rho_star_iter : forall {St} valid (rho N : St -> St) n s,
  Fixes valid rho -> IsRhoStar valid rho N -> N (iter n rho s) = N s.
Proof.
  intros St valid rho N n. induction n as [|n IH]; intros s Hf Hr; simpl; [reflexivity|].
  rewrite IH by assumption. apply (rho_star_rho valid); assumption.
Qed.

(* CC2 (for every invalid state) implies strong absorption, for N = rho*. *)
Theorem calc_cc2_strong_absorption : forall {St E} valid (rho N : St -> St)
  (A : E -> St -> St) e,
  Fixes valid rho -> IsRhoStar valid rho N -> CC2_ev valid rho N A e -> SA_ev N A e.
Proof.
  intros St E valid rho N A e Hf Hr Hcc2 s.
  destruct (Hr s) as [m [Hm _]]. rewrite Hm. clear Hm.
  revert s. induction m as [|m IH]; intros s; simpl; [reflexivity|].
  destruct (valid s) eqn:Hv.
  - rewrite (Hf s Hv). apply IH.
  - rewrite (Hcc2 s Hv). apply IH.
Qed.

(* Under strong absorption of both events, CC1 at s is exactly normalized commutation. *)
Theorem calc_cc1_iff_commute_of_sa : forall {St E} (N : St -> St) (A : E -> St -> St) e1 e2 s,
  SA_ev N A e1 -> SA_ev N A e2 ->
  (CC1_at N A e1 e2 s <-> N (A e2 (A e1 s)) = N (A e1 (A e2 s))).
Proof.
  intros St E N A e1 e2 s H1 H2. unfold CC1_at.
  rewrite <- (H2 (A e1 s)), <- (H1 (A e2 s)). tauto.
Qed.

(* Corrected footprint theorem, form 0: for a registry satisfying CC2 (which convergence
   needs anyway), CC1 for a pair holds at s iff the two events commute up to N at s.
   Footprints play no role. *)
Theorem calc_cc1_iff_commute_under_cc2 : forall {St E} valid (rho N : St -> St)
  (A : E -> St -> St) e1 e2 s,
  Fixes valid rho -> IsRhoStar valid rho N ->
  CC2_ev valid rho N A e1 -> CC2_ev valid rho N A e2 ->
  (CC1_at N A e1 e2 s <-> N (A e2 (A e1 s)) = N (A e1 (A e2 s))).
Proof.
  intros. apply calc_cc1_iff_commute_of_sa;
    eapply calc_cc2_strong_absorption; eassumption.
Qed.

(* ============================================================
   2. The calculus definitions (B33)
   ============================================================ *)

Definition validD {St I} (all : list I) (psi : I -> St -> bool) (s : St) : bool :=
  forallb (fun i => psi i s) all.

(* R_J = r_{j1} o r_{j2} o ... o r_{jn} for J = [j1; ...; jn]. *)
Fixpoint R {St I} (J : list I) (r : I -> St -> St) (s : St) : St :=
  match J with
  | [] => s
  | i :: J' => r i (R J' r s)
  end.

(* def:perinv: (R1) targeted fix, (R2) no-op on satisfied, (R3) mutual commutativity. *)
Definition PerInv {St I} (all : list I) (psi : I -> St -> bool) (r : I -> St -> St) : Prop :=
  (forall i s, In i all -> psi i s = false -> psi i (r i s) = true) /\
  (forall i s, In i all -> psi i s = true -> r i s = s) /\
  (forall i j s, In i all -> In j all -> r i (r j s) = r j (r i s)).

(* def:decomp: N = r_1 o ... o r_k. *)
Definition Decomposable {St I} (all : list I) (r : I -> St -> St) (N : St -> St) : Prop :=
  forall s, N s = R all r s.

(* def:footprint, for one event (F e i = true means i is in F(e)). *)
Definition IsFootprint {St I E} (all : list I) (psi : I -> St -> bool) (A : E -> St -> St)
  (F : E -> I -> bool) (e : E) : Prop :=
  forall i s, In i all -> F e i = false -> psi i (A e s) = psi i s.

(* def:repair-locality. *)
Definition RepairLocal {St I E} (all : list I) (r : I -> St -> St) (A : E -> St -> St)
  (F : E -> I -> bool) (e : E) : Prop :=
  forall i s, In i all -> F e i = false -> r i (A e s) = A e (r i s).

(* (H1) of thm:footprint-cc1. *)
Definition DisjointFP {I E} (all : list I) (F : E -> I -> bool) (e1 e2 : E) : Prop :=
  forall i, In i all -> F e1 i = true -> F e2 i = false.

(* The added hypothesis of the corrected theorem: e absorbs the repairs of its own
   footprint up to N. A per-event check involving only the repairs in F(e). *)
Definition FPAbsorb {St I E} (all : list I) (r : I -> St -> St) (N : St -> St)
  (A : E -> St -> St) (F : E -> I -> bool) (e : E) : Prop :=
  forall s, N (A e (R (filter (F e) all) r s)) = N (A e s).

(* ============================================================
   3. Lemmas of the calculus
   ============================================================ *)

Lemma R_app : forall {St I} (J1 J2 : list I) (r : I -> St -> St) s,
  R (J1 ++ J2) r s = R J1 r (R J2 r s).
Proof. intros St I J1. induction J1 as [|i J1 IH]; intros; simpl; [reflexivity|]. now rewrite IH. Qed.

(* lem:repair-commute (B35), exact. *)
Theorem base_lem_repair_commute : forall {St I E} (all : list I) (r : I -> St -> St)
  (A : E -> St -> St) (F : E -> I -> bool) e (J : list I) s,
  RepairLocal all r A F e ->
  incl J all -> (forall i, In i J -> F e i = false) ->
  R J r (A e s) = A e (R J r s).
Proof.
  intros St I E all r A F e J s Hloc. induction J as [|i J IH]; intros Hincl Hdis; simpl.
  - reflexivity.
  - rewrite IH.
    + apply Hloc; [apply Hincl; left; reflexivity | apply Hdis; left; reflexivity].
    + intros x Hx. apply Hincl. right. exact Hx.
    + intros x Hx. apply Hdis. right. exact Hx.
Qed.

Section PerInvLemmas.
  Context {St I : Type}.
  Variable all : list I.
  Variable psi : I -> St -> bool.
  Variable r : I -> St -> St.
  Hypothesis Hpi : PerInv all psi r.

  Lemma r1 : forall i s, In i all -> psi i s = false -> psi i (r i s) = true.
  Proof. apply Hpi. Qed.
  Lemma r2 : forall i s, In i all -> psi i s = true -> r i s = s.
  Proof. apply Hpi. Qed.
  Lemma r3 : forall i j s, In i all -> In j all -> r i (r j s) = r j (r i s).
  Proof. apply Hpi. Qed.

  Lemma r_sat : forall i s, In i all -> psi i (r i s) = true.
  Proof.
    intros i s Hi. destruct (psi i s) eqn:E.
    - rewrite (r2 i s Hi E). exact E.
    - apply r1; assumption.
  Qed.

  Lemma r_fixed_psi : forall i s, In i all -> r i s = s -> psi i s = true.
  Proof. intros i s Hi H. rewrite <- H. apply r_sat. exact Hi. Qed.

  Lemma r_pres : forall i j s, In i all -> In j all -> psi i s = true -> psi i (r j s) = true.
  Proof.
    intros i j s Hi Hj H. apply r_fixed_psi; [exact Hi|].
    rewrite r3 by assumption. rewrite (r2 i s Hi H). reflexivity.
  Qed.

  Lemma R_pres : forall J i s, incl J all -> In i all -> psi i s = true -> psi i (R J r s) = true.
  Proof.
    intros J. induction J as [|j J IH]; intros i s Hincl Hi H; simpl; [exact H|].
    apply r_pres; [exact Hi | apply Hincl; left; reflexivity |].
    apply IH; [intros x Hx; apply Hincl; right; exact Hx | exact Hi | exact H].
  Qed.

  Lemma R_sat : forall J i s, incl J all -> In i J -> psi i (R J r s) = true.
  Proof.
    intros J. induction J as [|j J IH]; intros i s Hincl Hin; [destruct Hin|].
    simpl. destruct Hin as [<-|Hin].
    - apply r_sat. apply Hincl. left. reflexivity.
    - apply r_pres; [apply Hincl; right; exact Hin | apply Hincl; left; reflexivity |].
      apply IH; [intros x Hx; apply Hincl; right; exact Hx | exact Hin].
  Qed.

  Lemma R_fix : forall J s, incl J all -> (forall i, In i J -> psi i s = true) -> R J r s = s.
  Proof.
    intros J. induction J as [|j J IH]; intros s Hincl H; simpl; [reflexivity|].
    rewrite IH.
    - apply r2; [apply Hincl; left; reflexivity | apply H; left; reflexivity].
    - intros x Hx. apply Hincl. right. exact Hx.
    - intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma r_R_comm : forall i J s, In i all -> incl J all -> r i (R J r s) = R J r (r i s).
  Proof.
    intros i J. induction J as [|j J IH]; intros s Hi Hincl; simpl; [reflexivity|].
    rewrite r3 by (assumption || (apply Hincl; left; reflexivity)).
    rewrite IH; [reflexivity | exact Hi | intros x Hx; apply Hincl; right; exact Hx].
  Qed.

  Lemma R_R_comm : forall J1 J2 s, incl J1 all -> incl J2 all ->
    R J1 r (R J2 r s) = R J2 r (R J1 r s).
  Proof.
    intros J1. induction J1 as [|i J1 IH]; intros J2 s H1 H2; simpl; [reflexivity|].
    rewrite IH by (assumption || (intros x Hx; apply H1; right; exact Hx)).
    apply r_R_comm; [apply H1; left; reflexivity | exact H2].
  Qed.

  Lemma R_split : forall (f : I -> bool) J s, incl J all ->
    R J r s = R (filter f J) r (R (filter (fun i => negb (f i)) J) r s).
  Proof.
    intros f J. induction J as [|i J IH]; intros s Hincl; simpl; [reflexivity|].
    assert (HJ : incl J all) by (intros x Hx; apply Hincl; right; exact Hx).
    assert (Hi : In i all) by (apply Hincl; left; reflexivity).
    destruct (f i); simpl; rewrite IH by exact HJ; [reflexivity|].
    apply r_R_comm; [exact Hi|].
    intros x Hx. apply filter_In in Hx. apply HJ. apply Hx.
  Qed.

  Variable N : St -> St.
  Hypothesis Hdec : Decomposable all r N.

  Lemma N_valid : forall s, validD all psi (N s) = true.
  Proof.
    intros s. unfold validD. apply forallb_forall. intros i Hi.
    rewrite Hdec. apply R_sat; [apply incl_refl | exact Hi].
  Qed.

  Lemma N_fix : forall s, validD all psi s = true -> N s = s.
  Proof.
    intros s Hv. rewrite Hdec. apply R_fix; [apply incl_refl|].
    intros i Hi. unfold validD in Hv. rewrite forallb_forall in Hv. apply Hv. exact Hi.
  Qed.

  Lemma N_R : forall J s, incl J all -> N (R J r s) = N s.
  Proof.
    intros J s HJ. rewrite !Hdec. rewrite R_R_comm by (assumption || apply incl_refl).
    apply R_fix; [exact HJ|]. intros i Hi. apply R_sat; [apply incl_refl | apply HJ, Hi].
  Qed.

  Lemma N_idem : forall s, N (N s) = N s.
  Proof. intros s. apply N_fix. apply N_valid. Qed.

  (* Normalizing before e reduces to repairing e's own footprint. *)
  Lemma N_A_N : forall {E} (A : E -> St -> St) (F : E -> I -> bool) e s,
    RepairLocal all r A F e ->
    N (A e (N s)) = N (A e (R (filter (F e) all) r s)).
  Proof.
    intros E A F e s Hloc.
    rewrite (Hdec s), (R_split (F e) all s (incl_refl _)).
    rewrite R_R_comm by (intros x Hx; apply filter_In in Hx; apply Hx).
    rewrite <- (base_lem_repair_commute all r A F e).
    - apply N_R. intros x Hx; apply filter_In in Hx; apply Hx.
    - exact Hloc.
    - intros x Hx; apply filter_In in Hx; apply Hx.
    - intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx].
      destruct (F e x); [discriminate | reflexivity].
  Qed.
End PerInvLemmas.

(* lem:repair-idempotent (B36), exact: R_J fixes J-valid states and is idempotent. *)
Theorem base_lem_repair_idempotent : forall {St I} (all : list I) (psi : I -> St -> bool)
  (r : I -> St -> St) (J : list I),
  PerInv all psi r -> incl J all ->
  (forall s, (forall i, In i J -> psi i s = true) -> R J r s = s) /\
  (forall s, R J r (R J r s) = R J r s).
Proof.
  intros St I all psi r J Hpi HJ. split.
  - intros s H. apply (R_fix all psi r Hpi); assumption.
  - intros s. apply (R_fix all psi r Hpi); [exact HJ|].
    intros i Hi. apply (R_sat all psi r Hpi); assumption.
Qed.

(* The paper's Notation (i) to (iii) hold for a decomposable normalizer. *)
Theorem calc_decomp_normalizer : forall {St I} (all : list I) (psi : I -> St -> bool)
  (r : I -> St -> St) N,
  PerInv all psi r -> Decomposable all r N ->
  (forall s, validD all psi (N s) = true) /\
  (forall s, validD all psi s = true -> N s = s) /\
  (forall s, N (N s) = N s).
Proof.
  intros. split; [|split].
  - apply (N_valid all psi r); assumption.
  - apply (N_fix all psi r); assumption.
  - apply (N_idem all psi r); assumption.
Qed.

(* ============================================================
   4. thm:footprint-cc1 (B37) as stated, and its refutation
   ============================================================ *)

(* The paper's statement, verbatim: WFC (with rho fixing valid states and N = rho* ),
   N decomposable via per-invariant repairs, F a footprint, e1 and e2 independent
   (distinct), (H1) disjoint footprints, (H2) repair locality; conclusion CC1. *)
Definition paper_footprint_cc1 : Prop :=
  forall (St I E : Type) (all : list I) (psi : I -> St -> bool) (r : I -> St -> St)
    (rho : St -> St) (Phi : St -> nat) (N : St -> St) (A : E -> St -> St)
    (F : E -> I -> bool) (e1 e2 : E),
    IsRegistry (validD all psi) rho Phi N ->
    PerInv all psi r -> Decomposable all r N ->
    IsFootprint all psi A F e1 -> IsFootprint all psi A F e2 ->
    e1 <> e2 ->
    DisjointFP all F e1 e2 ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    forall s, CC1_at N A e1 e2 s.

(* The same, with the extra hypothesis that the raw events commute. *)
Definition paper_footprint_cc1_raw : Prop :=
  forall (St I E : Type) (all : list I) (psi : I -> St -> bool) (r : I -> St -> St)
    (rho : St -> St) (Phi : St -> nat) (N : St -> St) (A : E -> St -> St)
    (F : E -> I -> bool) (e1 e2 : E),
    IsRegistry (validD all psi) rho Phi N ->
    PerInv all psi r -> Decomposable all r N ->
    IsFootprint all psi A F e1 -> IsFootprint all psi A F e2 ->
    e1 <> e2 ->
    DisjointFP all F e1 e2 ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    (forall s, A e1 (A e2 s) = A e2 (A e1 s)) ->
    forall s, CC1_at N A e1 e2 s.

(* Counterexample 1: k = 0. No invariants, every state valid, repair is the identity,
   footprints are empty, repair locality is vacuous; x := 1 and x := 2 do not commute. *)
Definition k0_all : list unit := [].
Definition k0_psi (_ : unit) (_ : nat) : bool := true.
Definition k0_r (_ : unit) (s : nat) : nat := s.
Definition k0_A (b : bool) (_ : nat) : nat := if b then 1 else 2.
Definition k0_F (_ : bool) (_ : unit) : bool := false.

Lemma k0_hyps :
  IsRegistry (validD k0_all k0_psi) (fun s => s) (fun _ => 0) (fun s => s) /\
  PerInv k0_all k0_psi k0_r /\ Decomposable k0_all k0_r (fun s => s) /\
  IsFootprint k0_all k0_psi k0_A k0_F true /\ IsFootprint k0_all k0_psi k0_A k0_F false /\
  DisjointFP k0_all k0_F true false /\
  RepairLocal k0_all k0_r k0_A k0_F true /\ RepairLocal k0_all k0_r k0_A k0_F false /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F true /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F false.
Proof.
  repeat split; try (intros; simpl in *; tauto); try (intros ? ?; reflexivity).
  - intros s H. discriminate.
  - intros s. exists 0. split; reflexivity.
Qed.

Lemma k0_not_cc1 : ~ CC1_at (fun s : nat => s) k0_A true false 0.
Proof. unfold CC1_at, k0_A. discriminate. Qed.

Theorem base_thm_footprint_cc1_refuted : ~ paper_footprint_cc1.
Proof.
  intros H. destruct k0_hyps as (Hreg & Hpi & Hdec & Hf1 & Hf2 & Hdj & Hl1 & Hl2 & _ & _).
  apply k0_not_cc1.
  exact (H nat unit bool k0_all k0_psi k0_r (fun s => s) (fun _ => 0) (fun s => s) k0_A k0_F
           true false Hreg Hpi Hdec Hf1 Hf2 ltac:(discriminate) Hdj Hl1 Hl2 0).
Qed.

(* Counterexample 2: states {0,1,2,3}, psi1 = psi2 = (s >= 2), r1 = r2 = (0,1 -> 2),
   a = (0,0,2,3) with footprint {} and repair-local, b = (0,0,3,0) with footprint {1,2}.
   The raw events commute; at 0 the two sides of CC1 are 3 and 2. *)
Inductive Q4 : Type := q0 | q1 | q2 | q3.
Inductive Q5 : Type := z0 | z1 | z2 | z3 | zx.
Inductive Stage : Type := pending | approved | held.
Inductive Bal : Type := b0 | b1 | b2 | b3.

(* Case analysis over the finite types of the instances below. *)
Ltac fin_destr :=
  repeat match goal with
  | x : Q4 |- _ => destruct x
  | x : Q5 |- _ => destruct x
  | x : unit |- _ => destruct x
  | x : bool |- _ => destruct x
  | x : Stage |- _ => destruct x
  | x : Bal |- _ => destruct x
  | x : prod _ _ |- _ => destruct x
  end.
Ltac fin :=
  unfold IsFootprint, RepairLocal, DisjointFP, FPAbsorb, Decomposable, Fixes, WFC, CC1_at,
    CC2_ev, SA_ev;
  intros; fin_destr; cbn in *; try discriminate; try reflexivity; try lia.

Definition q_hi (s : Q4) : bool := match s with q2 | q3 => true | _ => false end.
Definition q_rep (s : Q4) : Q4 := match s with q0 | q1 => q2 | x => x end.
Definition q_a (s : Q4) : Q4 := match s with q0 | q1 => q0 | q2 => q2 | q3 => q3 end.
Definition q_b (s : Q4) : Q4 := match s with q0 | q1 => q0 | q2 => q3 | q3 => q0 end.
Definition q_Phi (s : Q4) : nat := if q_hi s then 0 else 1.

Definition c2_all : list bool := [true; false].
Definition c2_psi (_ : bool) (s : Q4) : bool := q_hi s.
Definition c2_r (_ : bool) (s : Q4) : Q4 := q_rep s.
Definition c2_A (e : bool) : Q4 -> Q4 := if e then q_a else q_b.
Definition c2_F (e : bool) (_ : bool) : bool := negb e.

Lemma q_registry : IsRegistry q_hi q_rep q_Phi q_rep.
Proof.
  split; [|split].
  - intros [] H; try discriminate; reflexivity.
  - intros [] H; try discriminate; cbv; lia.
  - intros s. exists (if q_hi s then 0 else 1). destruct s; split; reflexivity.
Qed.

Lemma c2_valid : forall s, validD c2_all c2_psi s = q_hi s.
Proof. intros []; reflexivity. Qed.

Lemma c2_registry : IsRegistry (validD c2_all c2_psi) q_rep q_Phi q_rep.
Proof.
  destruct q_registry as (H1 & H2 & H3). split; [|split].
  - intros s H. rewrite c2_valid in H. auto.
  - intros s H. rewrite c2_valid in H. auto.
  - intros s. destruct (H3 s) as [m [Hm Hv]]. exists m. rewrite c2_valid. auto.
Qed.

Lemma c2_perinv : PerInv c2_all c2_psi c2_r.
Proof.
  unfold PerInv, c2_psi, c2_r. repeat split.
  - intros _ [] _ H; try discriminate; reflexivity.
  - intros _ [] _ H; try discriminate; reflexivity.
Qed.

Lemma c2_decomp : Decomposable c2_all c2_r q_rep.
Proof. intros []; reflexivity. Qed.

Lemma c2_hyps :
  IsFootprint c2_all c2_psi c2_A c2_F true /\ IsFootprint c2_all c2_psi c2_A c2_F false /\
  DisjointFP c2_all c2_F true false /\
  RepairLocal c2_all c2_r c2_A c2_F true /\ RepairLocal c2_all c2_r c2_A c2_F false /\
  (forall s, c2_A true (c2_A false s) = c2_A false (c2_A true s)).
Proof.
  unfold IsFootprint, DisjointFP, RepairLocal, c2_F, c2_A, c2_psi, c2_r.
  repeat split.
  - intros i [] _ _; reflexivity.
  - intros i s _ H; discriminate.
  - intros i _ H; discriminate.
  - intros i [] _ _; reflexivity.
  - intros i s _ H; discriminate.
  - intros []; reflexivity.
Qed.

Lemma c2_not_cc1 : ~ CC1_at q_rep c2_A true false q0.
Proof. unfold CC1_at. cbv. discriminate. Qed.

Theorem base_thm_footprint_cc1_raw_refuted : ~ paper_footprint_cc1_raw.
Proof.
  intros H. destruct c2_hyps as (Hf1 & Hf2 & Hdj & Hl1 & Hl2 & Hc).
  apply c2_not_cc1.
  exact (H Q4 bool bool c2_all c2_psi c2_r q_rep q_Phi q_rep c2_A c2_F true false
           c2_registry c2_perinv c2_decomp Hf1 Hf2 ltac:(discriminate) Hdj Hl1 Hl2 Hc q0).
Qed.

(* ============================================================
   5. The corrected footprint theorem
   ============================================================ *)

Section Corrected.
  Context {St I E : Type}.
  Variable all : list I.
  Variable psi : I -> St -> bool.
  Variable r : I -> St -> St.
  Variable N : St -> St.
  Variable A : E -> St -> St.
  Variable F : E -> I -> bool.

  Lemma disj_in : forall e1 e2, DisjointFP all F e1 e2 ->
    forall i, In i (filter (F e2) all) -> F e1 i = false.
  Proof.
    intros e1 e2 Hdj i Hi. apply filter_In in Hi. destruct Hi as [Hi H2].
    destruct (F e1 i) eqn:H1; [|reflexivity].
    rewrite (Hdj i Hi H1) in H2. discriminate.
  Qed.

  Lemma disj_in' : forall e1 e2, DisjointFP all F e1 e2 ->
    forall i, In i (filter (F e1) all) -> F e2 i = false.
  Proof.
    intros e1 e2 Hdj i Hi. apply filter_In in Hi. destruct Hi as [Hi H1].
    apply (Hdj i Hi H1).
  Qed.

  Lemma filter_incl : forall f, incl (filter f all) all.
  Proof. intros f x Hx. apply filter_In in Hx. apply Hx. Qed.

  (* Exact form at every state under (H1) and (H2): CC1 at s iff the events commute up
     to N after the other event's footprint repairs. *)
  Theorem calc_footprint_cc1_iff : forall e1 e2 s,
    PerInv all psi r -> Decomposable all r N ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    DisjointFP all F e1 e2 ->
    (CC1_at N A e1 e2 s <->
     N (A e2 (A e1 (R (filter (F e2) all) r s))) =
     N (A e1 (A e2 (R (filter (F e1) all) r s)))).
  Proof.
    intros e1 e2 s Hpi Hdec Hl1 Hl2 Hdj. unfold CC1_at.
    rewrite (N_A_N all psi r Hpi N Hdec A F e2 (A e1 s) Hl2).
    rewrite (N_A_N all psi r Hpi N Hdec A F e1 (A e2 s) Hl1).
    rewrite (base_lem_repair_commute all r A F e1 (filter (F e2) all) s Hl1
               (filter_incl _) (disj_in e1 e2 Hdj)).
    rewrite (base_lem_repair_commute all r A F e2 (filter (F e1) all) s Hl2
               (filter_incl _) (disj_in' e1 e2 Hdj)).
    tauto.
  Qed.

  (* Corrected form at valid states (the form gsm checks): under (H1) and (H2), CC1 at a
     valid s is exactly normalized commutation at s. *)
  Theorem calc_footprint_cc1_valid_iff : forall e1 e2 s,
    PerInv all psi r -> Decomposable all r N ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    DisjointFP all F e1 e2 ->
    validD all psi s = true ->
    (CC1_at N A e1 e2 s <-> N (A e2 (A e1 s)) = N (A e1 (A e2 s))).
  Proof.
    intros e1 e2 s Hpi Hdec Hl1 Hl2 Hdj Hv.
    rewrite (calc_footprint_cc1_iff e1 e2 s Hpi Hdec Hl1 Hl2 Hdj).
    assert (Hs : forall J, incl J all -> R J r s = s).
    { intros J HJ. apply (R_fix all psi r Hpi); [exact HJ|].
      intros i Hi. unfold validD in Hv. rewrite forallb_forall in Hv. apply Hv, HJ, Hi. }
    rewrite !Hs by apply filter_incl. tauto.
  Qed.

  Theorem calc_footprint_cc1_valid : forall e1 e2 s,
    PerInv all psi r -> Decomposable all r N ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    DisjointFP all F e1 e2 ->
    N (A e2 (A e1 s)) = N (A e1 (A e2 s)) ->
    validD all psi s = true ->
    CC1_at N A e1 e2 s.
  Proof.
    intros. apply (calc_footprint_cc1_valid_iff e1 e2 s); assumption.
  Qed.

  (* Footprint absorption is strong absorption, for a repair-local event. *)
  Theorem calc_fp_absorb_iff_sa : forall e,
    PerInv all psi r -> Decomposable all r N -> RepairLocal all r A F e ->
    (FPAbsorb all r N A F e <-> SA_ev N A e).
  Proof.
    intros e Hpi Hdec Hl. split.
    - intros H s. rewrite (N_A_N all psi r Hpi N Hdec A F e s Hl). symmetry. apply H.
    - intros H s. rewrite (H (R _ r s)), (N_R all psi r Hpi N Hdec _ _ (filter_incl _)).
      symmetry. apply H.
  Qed.

  (* Corrected form at every state (the paper's CC1): repair locality, footprint
     absorption and normalized commutation give CC1. Disjointness is not needed. *)
  Theorem calc_footprint_cc1 : forall e1 e2 s,
    PerInv all psi r -> Decomposable all r N ->
    RepairLocal all r A F e1 -> RepairLocal all r A F e2 ->
    FPAbsorb all r N A F e1 -> FPAbsorb all r N A F e2 ->
    N (A e2 (A e1 s)) = N (A e1 (A e2 s)) ->
    CC1_at N A e1 e2 s.
  Proof.
    intros e1 e2 s Hpi Hdec Hl1 Hl2 Ha1 Ha2 Hc.
    apply (calc_cc1_iff_commute_of_sa N A e1 e2 s);
      [apply (calc_fp_absorb_iff_sa e1) | apply (calc_fp_absorb_iff_sa e2) | ]; assumption.
  Qed.
End Corrected.

(* ---- Each hypothesis of the corrected theorems is needed ---- *)

(* Valid-state form without normalized commutation: k = 0, every state valid. *)
Theorem calc_valid_needs_commute :
  PerInv k0_all k0_psi k0_r /\ Decomposable k0_all k0_r (fun s => s) /\
  RepairLocal k0_all k0_r k0_A k0_F true /\ RepairLocal k0_all k0_r k0_A k0_F false /\
  DisjointFP k0_all k0_F true false /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F true /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F false /\
  validD k0_all k0_psi 0 = true /\
  ~ CC1_at (fun s : nat => s) k0_A true false 0.
Proof.
  destruct k0_hyps as (_ & Hpi & Hdec & _ & _ & Hdj & Hl1 & Hl2 & Ha1 & Ha2).
  repeat split; try assumption; try (intros ?; reflexivity). exact k0_not_cc1.
Qed.

(* Valid-state form without disjoint footprints: one invariant (s <> 1), repair 1 -> 0,
   e1 = +1 mod 4, e2 = +2 mod 4; both footprints are {1}; raw events commute. *)
Definition m_psi (_ : unit) (s : Q4) : bool := match s with q1 => false | _ => true end.
Definition m_r (_ : unit) (s : Q4) : Q4 := match s with q1 => q0 | x => x end.
Definition m_inc (s : Q4) : Q4 := match s with q0 => q1 | q1 => q2 | q2 => q3 | q3 => q0 end.
Definition m_A (e : bool) (s : Q4) : Q4 := if e then m_inc s else m_inc (m_inc s).
Definition m_F (_ : bool) (_ : unit) : bool := true.
Definition m_all : list unit := [tt].
Definition m_N (s : Q4) : Q4 := m_r tt s.

Theorem calc_valid_needs_disjoint :
  IsRegistry (validD m_all m_psi) m_N (fun s => if m_psi tt s then 0 else 1) m_N /\
  PerInv m_all m_psi m_r /\ Decomposable m_all m_r m_N /\
  IsFootprint m_all m_psi m_A m_F true /\ IsFootprint m_all m_psi m_A m_F false /\
  RepairLocal m_all m_r m_A m_F true /\ RepairLocal m_all m_r m_A m_F false /\
  (forall s, m_A true (m_A false s) = m_A false (m_A true s)) /\
  ~ DisjointFP m_all m_F true false /\
  validD m_all m_psi q0 = true /\
  ~ CC1_at m_N m_A true false q0.
Proof.
  unfold IsRegistry, Fixes, WFC, IsRhoStar, PerInv, Decomposable, IsFootprint,
    RepairLocal, DisjointFP, CC1_at.
  repeat split; try solve [fin].
  all: try solve [intros s; exists (if m_psi tt s then 0 else 1); destruct s; split; reflexivity].
  all: try solve [intros H; specialize (H tt (or_introl eq_refl) eq_refl); discriminate].
  all: cbv; discriminate.
Qed.

(* Valid-state form without repair locality: one invariant (x = false), repair
   (true, y) -> (false, y + 1); e1 sets x := true (footprint {1}); e2 sets y := 0
   (footprint {}), preserves the invariant and commutes with e1, but not with the repair.
   At the valid state (false, 0) the two sides of CC1 are (false, 0) and (false, 1). *)
Definition l_psi (_ : unit) (s : bool * nat) : bool := negb (fst s).
Definition l_r (_ : unit) (s : bool * nat) : bool * nat :=
  if fst s then (false, Datatypes.S (snd s)) else s.
Definition l_A (e : bool) (s : bool * nat) : bool * nat :=
  if e then (true, snd s) else (fst s, 0).
Definition l_F (e : bool) (_ : unit) : bool := e.
Definition l_all : list unit := [tt].
Definition l_N (s : bool * nat) : bool * nat := l_r tt s.

Theorem calc_valid_needs_repair_local :
  IsRegistry (validD l_all l_psi) l_N (fun s => if fst s then 1 else 0) l_N /\
  PerInv l_all l_psi l_r /\ Decomposable l_all l_r l_N /\
  IsFootprint l_all l_psi l_A l_F true /\ IsFootprint l_all l_psi l_A l_F false /\
  DisjointFP l_all l_F true false /\
  RepairLocal l_all l_r l_A l_F true /\ ~ RepairLocal l_all l_r l_A l_F false /\
  (forall s, l_A true (l_A false s) = l_A false (l_A true s)) /\
  validD l_all l_psi (false, 0) = true /\
  ~ CC1_at l_N l_A true false (false, 0).
Proof.
  unfold IsRegistry, Fixes, WFC, IsRhoStar, PerInv, Decomposable, IsFootprint,
    RepairLocal, DisjointFP, CC1_at.
  repeat split; try solve [fin].
  all: try solve [intros [x y]; exists (if x then 1 else 0); destruct x; split; reflexivity].
  all: try solve [intros H; specialize (H tt (true, 0) (or_introl eq_refl) eq_refl); discriminate].
  all: cbv; discriminate.
Qed.

(* All-states form without normalized commutation: k = 0 again (footprint absorption and
   repair locality hold trivially). *)
Theorem calc_all_needs_commute :
  PerInv k0_all k0_psi k0_r /\ Decomposable k0_all k0_r (fun s => s) /\
  RepairLocal k0_all k0_r k0_A k0_F true /\ RepairLocal k0_all k0_r k0_A k0_F false /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F true /\
  FPAbsorb k0_all k0_r (fun s => s) k0_A k0_F false /\
  ~ CC1_at (fun s : nat => s) k0_A true false 0.
Proof.
  destruct calc_valid_needs_commute as (H1 & H2 & H3 & H4 & _ & H6 & H7 & _ & H9).
  repeat split; assumption.
Qed.

(* All-states form without footprint absorption: counterexample 2 (raw events commute,
   footprints disjoint, both events repair-local), and b fails footprint absorption. *)
Theorem calc_all_needs_absorb :
  PerInv c2_all c2_psi c2_r /\ Decomposable c2_all c2_r q_rep /\
  RepairLocal c2_all c2_r c2_A c2_F true /\ RepairLocal c2_all c2_r c2_A c2_F false /\
  DisjointFP c2_all c2_F true false /\
  FPAbsorb c2_all c2_r q_rep c2_A c2_F true /\ ~ FPAbsorb c2_all c2_r q_rep c2_A c2_F false /\
  (forall s, c2_A true (c2_A false s) = c2_A false (c2_A true s)) /\
  ~ CC1_at q_rep c2_A true false q0.
Proof.
  destruct c2_hyps as (_ & _ & Hdj & Hl1 & Hl2 & Hc).
  split; [exact c2_perinv|]. split; [exact c2_decomp|].
  split; [exact Hl1|]. split; [exact Hl2|]. split; [exact Hdj|].
  split; [intros []; reflexivity|]. split.
  - intros H. specialize (H q0). cbv in H. discriminate.
  - split; [exact Hc | exact c2_not_cc1].
Qed.

(* All-states form without repair locality: one invariant (s >= 2), a = identity,
   b swaps 2 and 3; both footprints empty (so footprint absorption is trivial). *)
Definition w_b (s : Q4) : Q4 := match s with q2 => q3 | q3 => q2 | x => x end.
Definition w_A (e : bool) : Q4 -> Q4 := if e then (fun s => s) else w_b.
Definition w_F (_ : bool) (_ : unit) : bool := false.
Definition w_all : list unit := [tt].
Definition w_psi (_ : unit) (s : Q4) : bool := q_hi s.
Definition w_r (_ : unit) (s : Q4) : Q4 := q_rep s.

Theorem calc_all_needs_repair_local :
  PerInv w_all w_psi w_r /\ Decomposable w_all w_r q_rep /\
  IsFootprint w_all w_psi w_A w_F true /\ IsFootprint w_all w_psi w_A w_F false /\
  DisjointFP w_all w_F true false /\
  RepairLocal w_all w_r w_A w_F true /\ ~ RepairLocal w_all w_r w_A w_F false /\
  FPAbsorb w_all w_r q_rep w_A w_F true /\ FPAbsorb w_all w_r q_rep w_A w_F false /\
  (forall s, w_A true (w_A false s) = w_A false (w_A true s)) /\
  ~ CC1_at q_rep w_A true false q0.
Proof.
  unfold PerInv, Decomposable, IsFootprint, RepairLocal, DisjointFP, FPAbsorb, CC1_at.
  repeat split; try solve [fin].
  all: try solve [intros H; specialize (H tt q0 (or_introl eq_refl) eq_refl); discriminate].
  all: cbv; discriminate.
Qed.

(* ---- Non-vacuity: two clamped counters, disjoint footprints ---- *)

Definition cl_all : list bool := [true; false].
Definition cl_psi (i : bool) (s : nat * nat) : bool :=
  if i then fst s <=? 2 else snd s <=? 2.
Definition cl_r (i : bool) (s : nat * nat) : nat * nat :=
  if i then (Nat.min (fst s) 2, snd s) else (fst s, Nat.min (snd s) 2).
Definition cl_N (s : nat * nat) : nat * nat := (Nat.min (fst s) 2, Nat.min (snd s) 2).
Definition cl_A (e : bool) (s : nat * nat) : nat * nat :=
  if e then (Datatypes.S (fst s), snd s) else (fst s, Datatypes.S (snd s)).
Definition cl_F (e i : bool) : bool := Bool.eqb e i.
Definition cl_Phi (s : nat * nat) : nat := (fst s - 2) + (snd s - 2).

Lemma leb_min : forall x, (x <=? 2) = true -> Nat.min x 2 = x.
Proof. intros x H. apply Nat.leb_le in H. lia. Qed.

Theorem calc_clamp_instance :
  IsRegistry (validD cl_all cl_psi) cl_N cl_Phi cl_N /\
  PerInv cl_all cl_psi cl_r /\ Decomposable cl_all cl_r cl_N /\
  IsFootprint cl_all cl_psi cl_A cl_F true /\ IsFootprint cl_all cl_psi cl_A cl_F false /\
  DisjointFP cl_all cl_F true false /\
  RepairLocal cl_all cl_r cl_A cl_F true /\ RepairLocal cl_all cl_r cl_A cl_F false /\
  FPAbsorb cl_all cl_r cl_N cl_A cl_F true /\ FPAbsorb cl_all cl_r cl_N cl_A cl_F false /\
  (forall s, cl_A true (cl_A false s) = cl_A false (cl_A true s)) /\
  (forall s, CC1_at cl_N cl_A true false s) /\
  CC1_at cl_N cl_A true false (5, 0) /\ validD cl_all cl_psi (5, 0) = false.
Proof.
  assert (Hval : forall x y, validD cl_all cl_psi (x, y) = (x <=? 2) && (y <=? 2)).
  { intros x y. unfold validD; simpl. rewrite andb_true_r. reflexivity. }
  assert (Hreg : IsRegistry (validD cl_all cl_psi) cl_N cl_Phi cl_N).
  { split; [|split].
    - intros [x y] H. rewrite Hval in H. apply andb_true_iff in H. destruct H as [Hx Hy].
      unfold cl_N; simpl. rewrite (leb_min x Hx), (leb_min y Hy). reflexivity.
    - intros [x y] H. rewrite Hval in H. unfold cl_Phi, cl_N; simpl.
      destruct (Nat.leb_spec x 2), (Nat.leb_spec y 2); simpl in H; try discriminate; lia.
    - intros [x y]. exists 1. split; [reflexivity|].
      unfold cl_N. cbn [fst snd]. rewrite Hval.
      apply andb_true_iff. split; apply Nat.leb_le; lia. }
  assert (Hpi : PerInv cl_all cl_psi cl_r).
  { repeat split.
    - intros [] [x y] _ H; simpl in *; apply Nat.leb_le; lia.
    - intros [] [x y] _ H; simpl in *; [rewrite (leb_min x H) | rewrite (leb_min y H)];
        reflexivity.
    - intros [] [] [x y] _ _; simpl; try reflexivity; f_equal; lia. }
  assert (Hdec : Decomposable cl_all cl_r cl_N) by (intros [x y]; reflexivity).
  assert (Hl1 : RepairLocal cl_all cl_r cl_A cl_F true)
    by (intros [] [x y] _ H; try discriminate; reflexivity).
  assert (Hl2 : RepairLocal cl_all cl_r cl_A cl_F false)
    by (intros [] [x y] _ H; try discriminate; reflexivity).
  assert (Ha1 : FPAbsorb cl_all cl_r cl_N cl_A cl_F true)
    by (intros [x y]; unfold cl_N; simpl; f_equal; lia).
  assert (Ha2 : FPAbsorb cl_all cl_r cl_N cl_A cl_F false)
    by (intros [x y]; unfold cl_N; simpl; f_equal; lia).
  assert (Hc : forall s, cl_A true (cl_A false s) = cl_A false (cl_A true s))
    by (intros [x y]; reflexivity).
  assert (Hcc : forall s, CC1_at cl_N cl_A true false s).
  { intros s. apply (calc_footprint_cc1 cl_all cl_psi cl_r cl_N cl_A cl_F); try assumption.
    rewrite Hc. reflexivity. }
  split; [exact Hreg|]. split; [exact Hpi|]. split; [exact Hdec|].
  repeat split; try assumption; try solve [fin]; apply Hcc.
Qed.

(* ---- gsm form: events acting on disjoint components of a product state ----
   A machine whose state splits as S1 * S2, whose normalizer acts componentwise
   (N1 on S1, N2 on S2), with e1 touching only S1 and e2 only S2. This is what gsm's
   footprint components give (an event reads and writes only its component; repairs of a
   component read and write only it). *)

Section Components.
  Context {S1 S2 : Type}.
  Variable v1 : S1 -> bool.
  Variable v2 : S2 -> bool.
  Variable N1 : S1 -> S1.
  Variable N2 : S2 -> S2.
  Variable f : S1 -> S1.
  Variable g : S2 -> S2.

  Definition cN (s : S1 * S2) : S1 * S2 := (N1 (fst s), N2 (snd s)).
  Definition cA (e : bool) (s : S1 * S2) : S1 * S2 :=
    if e then (f (fst s), snd s) else (fst s, g (snd s)).

  (* At every state: CC1 iff each event absorbs normalization in its own component. *)
  Theorem calc_components_cc1_iff : forall s1 s2,
    (forall x, N1 (N1 x) = N1 x) -> (forall y, N2 (N2 y) = N2 y) ->
    (CC1_at cN cA true false (s1, s2) <->
     N1 (f s1) = N1 (f (N1 s1)) /\ N2 (g (N2 s2)) = N2 (g s2)).
  Proof.
    intros s1 s2 H1 H2. unfold CC1_at, cN, cA; simpl. rewrite H1, H2.
    split.
    - intros H. injection H as Ha Hb. split; assumption.
    - intros [Ha Hb]. rewrite Ha, Hb. reflexivity.
  Qed.

  (* At valid states: CC1 always holds. *)
  Theorem calc_components_cc1_valid : forall s1 s2,
    (forall x, N1 (N1 x) = N1 x) -> (forall y, N2 (N2 y) = N2 y) ->
    (forall x, v1 x = true -> N1 x = x) -> (forall y, v2 y = true -> N2 y = y) ->
    v1 s1 = true -> v2 s2 = true ->
    CC1_at cN cA true false (s1, s2).
  Proof.
    intros s1 s2 H1 H2 F1 F2 V1 V2. apply calc_components_cc1_iff; try assumption.
    rewrite (F1 s1 V1), (F2 s2 V2). split; reflexivity.
  Qed.
End Components.

(* ============================================================
   6. Remark "Practical import" (B38): the order-fulfillment registry
   ============================================================ *)

Definition ge2 (b : Bal) : bool := match b with b2 | b3 => true | _ => false end.
Definition binc (b : Bal) : Bal := match b with b0 => b1 | b1 => b2 | _ => b3 end.

Definition o_psi (_ : unit) (s : Stage * Bal) : bool :=
  match fst s with approved => ge2 (snd s) | _ => true end.
Definition o_rho (s : Stage * Bal) : Stage * Bal :=
  match s with
  | (approved, b) => if ge2 b then s else (held, b)
  | _ => s
  end.
Definition o_r (_ : unit) (s : Stage * Bal) : Stage * Bal := o_rho s.
Definition o_credit (s : Stage * Bal) : Stage * Bal :=
  match s with
  | (held, b) => if ge2 (binc b) then (approved, binc b) else (held, binc b)
  | (st, b) => (st, binc b)
  end.
Definition o_approve (s : Stage * Bal) : Stage * Bal := (approved, snd s).
(* Events: true = approve, false = credit. *)
Definition o_A (e : bool) : Stage * Bal -> Stage * Bal := if e then o_approve else o_credit.
Definition o_all : list unit := [tt].
Definition o_Phi (s : Stage * Bal) : nat := if o_psi tt s then 0 else 1.
Definition o_valid := validD o_all o_psi.

Lemma o_registry : IsRegistry o_valid o_rho o_Phi o_rho.
Proof.
  split; [|split].
  - intros [[] []] H; try discriminate; reflexivity.
  - intros [[] []] H; try discriminate; cbv; lia.
  - intros s. exists (if o_psi tt s then 0 else 1). destruct s as [[] []]; split; reflexivity.
Qed.

Lemma o_perinv : PerInv o_all o_psi o_r.
Proof. repeat split; fin. Qed.

Lemma o_decomp : Decomposable o_all o_r o_rho.
Proof. intros [[] []]; reflexivity. Qed.

(* Every footprint of approve and of credit contains the single invariant, so no footprint
   assignment makes them disjoint: the remark's claim is false as stated. *)
Theorem base_rem_practical_import_refuted : forall F : bool -> unit -> bool,
  IsFootprint o_all o_psi o_A F true -> IsFootprint o_all o_psi o_A F false ->
  F true tt = true /\ F false tt = true /\ ~ DisjointFP o_all F true false.
Proof.
  intros F Ha Hc.
  assert (HA : F true tt = true).
  { destruct (F true tt) eqn:E; [reflexivity|].
    specialize (Ha tt (pending, b0) (or_introl eq_refl) E). discriminate. }
  assert (HC : F false tt = true).
  { destruct (F false tt) eqn:E; [reflexivity|].
    specialize (Hc tt (approved, b1) (or_introl eq_refl) E). discriminate. }
  split; [exact HA|]. split; [exact HC|].
  intros H. rewrite (H tt (or_introl eq_refl) HA) in HC. discriminate.
Qed.

(* The true half of the remark: the held-state repair commutes with credit. *)
Theorem calc_order_credit_repair_commute : forall s, o_rho (o_credit s) = o_credit (o_rho s).
Proof. intros [[] []]; reflexivity. Qed.

(* CC1 nonetheless holds for (approve, credit) at every state, by the corrected theorem
   (calc_footprint_cc1 needs no disjointness): both events absorb their footprint repairs,
   and they commute. Also CC2 holds for both events. *)
Theorem calc_order_cc1 :
  (forall s, CC1_at o_rho o_A true false s) /\
  CC2_ev o_valid o_rho o_rho o_A true /\ CC2_ev o_valid o_rho o_rho o_A false.
Proof.
  split; [|split].
  - intros s. apply (calc_footprint_cc1 o_all o_psi o_r o_rho o_A (fun _ _ => true));
      try (exact o_perinv || exact o_decomp); fin.
  - fin.
  - fin.
Qed.

(* ============================================================
   7. Section 8.2, pattern 1 (B31): compensation to a canonical state
   ============================================================ *)

(* "If rho*(s) = bot for every invalid s, both CC1 and CC2 hold." *)
Definition paper_canonical_cc1 : Prop :=
  forall (St E : Type) (valid : St -> bool) (rho : St -> St) (Phi : St -> nat) (N : St -> St)
    (A : E -> St -> St) (bot : St),
    IsRegistry valid rho Phi N -> valid bot = true ->
    (forall s, valid s = false -> N s = bot) ->
    forall e1 e2 s, e1 <> e2 -> CC1_at N A e1 e2 s.

Definition paper_canonical_cc2 : Prop :=
  forall (St E : Type) (valid : St -> bool) (rho : St -> St) (Phi : St -> nat) (N : St -> St)
    (A : E -> St -> St) (bot : St),
    IsRegistry valid rho Phi N -> valid bot = true ->
    (forall s, valid s = false -> N s = bot) ->
    forall e, CC2_ev valid rho N A e.

(* States {0,1,2,3}, 3 invalid, reset to 0. *)
Definition p_valid (s : Q4) : bool := match s with q3 => false | _ => true end.
Definition p_rho (s : Q4) : Q4 := match s with q3 => q0 | x => x end.
Definition p_Phi (s : Q4) : nat := if p_valid s then 0 else 1.

Lemma p_registry : IsRegistry p_valid p_rho p_Phi p_rho.
Proof.
  split; [|split].
  - intros [] H; try discriminate; reflexivity.
  - intros [] H; try discriminate; cbv; lia.
  - intros s. exists (if p_valid s then 0 else 1). destruct s; split; reflexivity.
Qed.

Lemma p_canonical : forall s, p_valid s = false -> p_rho s = q0.
Proof. intros [] H; try discriminate; reflexivity. Qed.

(* Two valid-to-valid events that do not commute (x := 1, x := 2) violate CC1. *)
Theorem base_pattern1_cc1_refuted : ~ paper_canonical_cc1.
Proof.
  intros H.
  specialize (H Q4 bool p_valid p_rho p_Phi p_rho (fun e _ => if e then q1 else q2) q0
                p_registry eq_refl p_canonical true false q0 ltac:(discriminate)).
  cbv in H. discriminate.
Qed.

(* An event sending the invalid state 3 to 1 but the reset state 0 to 2 violates CC2. *)
Theorem base_pattern1_cc2_refuted : ~ paper_canonical_cc2.
Proof.
  intros H.
  specialize (H Q4 unit p_valid p_rho p_Phi p_rho
                (fun _ s => match s with q3 => q1 | q0 => q2 | x => x end) q0
                p_registry eq_refl p_canonical tt q3 eq_refl).
  cbv in H. discriminate.
Qed.

(* Corrected pattern 1. With canonical compensation, CC2 for e is exactly the reset check
   N(A_e s) = N(A_e bot) on invalid s; and given CC2, CC1 for a pair is exactly normalized
   commutation. *)
Theorem calc_canonical_cc2_iff : forall {St E} (valid : St -> bool) (rho N : St -> St)
  (A : E -> St -> St) (bot : St) e,
  Fixes valid rho -> IsRhoStar valid rho N ->
  (forall s, valid s = false -> N s = bot) ->
  (CC2_ev valid rho N A e <-> forall s, valid s = false -> N (A e s) = N (A e bot)).
Proof.
  intros St E valid rho N A bot e Hf Hr Hcan. split.
  - intros H s Hv. rewrite (calc_cc2_strong_absorption valid rho N A e Hf Hr H s).
    rewrite (Hcan s Hv). reflexivity.
  - intros H s Hv. rewrite (H s Hv).
    destruct (valid (rho s)) eqn:Hv'.
    + assert (Heq : rho s = bot).
      { rewrite <- (Hcan s Hv). rewrite <- (rho_star_rho valid rho N s Hf Hr).
        symmetry. apply (rho_star_fix valid rho); assumption. }
      rewrite Heq. reflexivity.
    + symmetry. apply H. exact Hv'.
Qed.

Theorem calc_canonical_pattern : forall {St E} (valid : St -> bool) (rho N : St -> St)
  (A : E -> St -> St) (bot : St) e1 e2,
  Fixes valid rho -> IsRhoStar valid rho N ->
  (forall s, valid s = false -> N s = bot) ->
  (forall s, valid s = false -> N (A e1 s) = N (A e1 bot)) ->
  (forall s, valid s = false -> N (A e2 s) = N (A e2 bot)) ->
  CC2_ev valid rho N A e1 /\ CC2_ev valid rho N A e2 /\
  (forall s, CC1_at N A e1 e2 s <-> N (A e2 (A e1 s)) = N (A e1 (A e2 s))).
Proof.
  intros St E valid rho N A bot e1 e2 Hf Hr Hcan H1 H2.
  assert (C1 : CC2_ev valid rho N A e1) by (apply (calc_canonical_cc2_iff valid rho N A bot); assumption).
  assert (C2 : CC2_ev valid rho N A e2) by (apply (calc_canonical_cc2_iff valid rho N A bot); assumption).
  split; [exact C1|]. split; [exact C2|].
  intros s. apply (calc_cc1_iff_commute_under_cc2 valid rho N A); assumption.
Qed.

(* Non-vacuity: a mod-4 counter with a corrupt state reset to 0; events add 1 and add 2
   after treating the corrupt state as 0. *)
Definition z_valid (s : Q5) : bool := match s with zx => false | _ => true end.
Definition z_rho (s : Q5) : Q5 := match s with zx => z0 | x => x end.
Definition z_inc (s : Q5) : Q5 :=
  match s with z0 | zx => z1 | z1 => z2 | z2 => z3 | z3 => z0 end.
Definition z_A (e : bool) (s : Q5) : Q5 := if e then z_inc s else z_inc (z_inc (z_rho s)).

Theorem calc_canonical_instance :
  IsRegistry z_valid z_rho (fun s => if z_valid s then 0 else 1) z_rho /\
  (forall s, z_valid s = false -> z_rho s = z0) /\
  (forall e, CC2_ev z_valid z_rho z_rho z_A e) /\
  (forall s, CC1_at z_rho z_A true false s).
Proof.
  assert (Hreg : IsRegistry z_valid z_rho (fun s => if z_valid s then 0 else 1) z_rho).
  { split; [|split].
    - intros [] H; try discriminate; reflexivity.
    - intros [] H; try discriminate; cbv; lia.
    - intros s. exists (if z_valid s then 0 else 1). destruct s; split; reflexivity. }
  destruct Hreg as (Hf & Hw & Hr).
  assert (Hcan : forall s, z_valid s = false -> z_rho s = z0)
    by (intros [] H; try discriminate; reflexivity).
  assert (Hreset : forall e s, z_valid s = false -> z_rho (z_A e s) = z_rho (z_A e z0))
    by (intros [] [] H; try discriminate; reflexivity).
  split; [split; [exact Hf | split; assumption]|]. split; [exact Hcan|].
  split.
  - intros e. apply (calc_canonical_cc2_iff z_valid z_rho z_rho z_A z0 e Hf Hr Hcan).
    apply Hreset.
  - intros s. destruct (calc_canonical_pattern z_valid z_rho z_rho z_A z0 true false
                          Hf Hr Hcan (Hreset true) (Hreset false)) as (_ & _ & H).
    apply H. destruct s; reflexivity.
Qed.

(* ============================================================
   8. Product composition (B39, B40)
   ============================================================ *)

Section Product.
  Context {S1 S2 E1 E2 : Type}.
  Variable v1 : S1 -> bool.
  Variable v2 : S2 -> bool.
  Variable rho1 : S1 -> S1.
  Variable rho2 : S2 -> S2.
  Variable Phi1 : S1 -> nat.
  Variable Phi2 : S2 -> nat.
  Variable N1 : S1 -> S1.
  Variable N2 : S2 -> S2.
  Variable A1 : E1 -> S1 -> S1.
  Variable A2 : E2 -> S2 -> S2.

  (* def:product. *)
  Definition pv (s : S1 * S2) : bool := v1 (fst s) && v2 (snd s).
  Definition prho (s : S1 * S2) : S1 * S2 := (rho1 (fst s), rho2 (snd s)).
  Definition pPhi (s : S1 * S2) : nat := Phi1 (fst s) + Phi2 (snd s).
  Definition pN (s : S1 * S2) : S1 * S2 := (N1 (fst s), N2 (snd s)).
  Definition pA (e : E1 * E2) (s : S1 * S2) : S1 * S2 :=
    (A1 (fst e) (fst s), A2 (snd e) (snd s)).

  Lemma iter_pair : forall n s1 s2,
    iter n prho (s1, s2) = (iter n rho1 s1, iter n rho2 s2).
  Proof. intros n. induction n as [|n IH]; intros; simpl; [reflexivity|]. apply IH. Qed.

  (* thm:product, WFC and CC part. CC1 for a product pair holds at (s1, s2) when it holds
     componentwise (and conversely); CC2 lifts. *)
  Theorem base_thm_product :
    IsRegistry v1 rho1 Phi1 N1 -> IsRegistry v2 rho2 Phi2 N2 ->
    IsRegistry pv prho pPhi pN /\
    (forall a1 a2 b1 b2 s1 s2,
        CC1_at pN pA (a1, b1) (a2, b2) (s1, s2) <->
        CC1_at N1 A1 a1 a2 s1 /\ CC1_at N2 A2 b1 b2 s2) /\
    (forall a b, CC2_ev v1 rho1 N1 A1 a -> CC2_ev v2 rho2 N2 A2 b ->
                 CC2_ev pv prho pN pA (a, b)).
  Proof.
    intros (F1 & W1 & R1) (F2 & W2 & R2). split; [split; [|split]|split].
    - intros [s1 s2] H. unfold pv in H; simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2]. unfold prho; simpl. rewrite (F1 s1 H1), (F2 s2 H2). reflexivity.
    - intros [s1 s2] H. unfold pv in H; simpl in H. unfold pPhi, prho; simpl.
      destruct (v1 s1) eqn:H1, (v2 s2) eqn:H2; simpl in H; try discriminate.
      + rewrite (F1 s1 H1). specialize (W2 s2 H2). lia.
      + rewrite (F2 s2 H2). specialize (W1 s1 H1). lia.
      + specialize (W1 s1 H1). specialize (W2 s2 H2). lia.
    - intros [s1 s2]. destruct (R1 s1) as [m1 [Hm1 Hv1]]. destruct (R2 s2) as [m2 [Hm2 Hv2]].
      exists (m1 + m2). unfold pN, pv; simpl. rewrite Hv1, Hv2. split; [|reflexivity].
      rewrite iter_pair. f_equal.
      + rewrite iter_add, <- Hm1. symmetry. apply (iter_fixed v1); assumption.
      + rewrite Nat.add_comm, iter_add, <- Hm2. symmetry. apply (iter_fixed v2); assumption.
    - intros a1 a2 b1 b2 s1 s2. unfold CC1_at, pN, pA; simpl. split.
      + intros H. injection H as Ha Hb. split; assumption.
      + intros [Ha Hb]. rewrite Ha, Hb. reflexivity.
    - intros a b C1 C2 [s1 s2] H. unfold pv in H; simpl in H. unfold pN, pA, prho; simpl.
      f_equal.
      + destruct (v1 s1) eqn:H1; [rewrite (F1 s1 H1); reflexivity | apply C1, H1].
      + destruct (v2 s2) eqn:H2; [rewrite (F2 s2 H2); reflexivity | apply C2, H2].
  Qed.

  (* thm:product, decomposability part: per-invariant repairs, footprints (composed by
     union, inl F1 + inr F2) and repair locality lift to the product. *)
  Context {I1 I2 : Type}.
  Variable all1 : list I1.
  Variable all2 : list I2.
  Variable psi1 : I1 -> S1 -> bool.
  Variable psi2 : I2 -> S2 -> bool.
  Variable r1 : I1 -> S1 -> S1.
  Variable r2 : I2 -> S2 -> S2.
  Variable F1 : E1 -> I1 -> bool.
  Variable F2 : E2 -> I2 -> bool.

  Definition pall : list (I1 + I2) := map inl all1 ++ map inr all2.
  Definition ppsi (i : I1 + I2) (s : S1 * S2) : bool :=
    match i with inl i1 => psi1 i1 (fst s) | inr i2 => psi2 i2 (snd s) end.
  Definition pr (i : I1 + I2) (s : S1 * S2) : S1 * S2 :=
    match i with inl i1 => (r1 i1 (fst s), snd s) | inr i2 => (fst s, r2 i2 (snd s)) end.
  Definition pF (e : E1 * E2) (i : I1 + I2) : bool :=
    match i with inl i1 => F1 (fst e) i1 | inr i2 => F2 (snd e) i2 end.

  Lemma in_pall_l : forall i, In (inl i) pall -> In i all1.
  Proof.
    intros i H. apply in_app_or in H. destruct H as [H|H]; apply in_map_iff in H;
      destruct H as [x [Hx Hin]]; [injection Hx as ->; exact Hin | discriminate].
  Qed.

  Lemma in_pall_r : forall i, In (inr i) pall -> In i all2.
  Proof.
    intros i H. apply in_app_or in H. destruct H as [H|H]; apply in_map_iff in H;
      destruct H as [x [Hx Hin]]; [discriminate | injection Hx as ->; exact Hin].
  Qed.

  Lemma fb_app : forall {X} (f : X -> bool) l1 l2,
    forallb f (l1 ++ l2) = forallb f l1 && forallb f l2.
  Proof.
    intros X f l1. induction l1 as [|x l IH]; intros; simpl; [reflexivity|].
    rewrite IH. apply andb_assoc.
  Qed.

  Lemma fb_map : forall {X Y} (f : Y -> bool) (g : X -> Y) l,
    forallb f (map g l) = forallb (fun x => f (g x)) l.
  Proof. intros X Y f g l. induction l as [|x l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Lemma R_inl : forall J s1 s2, R (map inl J) pr (s1, s2) = (R J r1 s1, s2).
  Proof. intros J. induction J as [|i J IH]; intros; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Lemma R_inr : forall J s1 s2, R (map inr J) pr (s1, s2) = (s1, R J r2 s2).
  Proof. intros J. induction J as [|i J IH]; intros; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Theorem base_thm_product_decomposable :
    PerInv all1 psi1 r1 -> PerInv all2 psi2 r2 ->
    Decomposable all1 r1 N1 -> Decomposable all2 r2 N2 ->
    PerInv pall ppsi pr /\ Decomposable pall pr pN /\
    (forall s, validD pall ppsi s = validD all1 psi1 (fst s) && validD all2 psi2 (snd s)) /\
    (forall a b, IsFootprint all1 psi1 A1 F1 a -> IsFootprint all2 psi2 A2 F2 b ->
                 IsFootprint pall ppsi pA pF (a, b)) /\
    (forall a b, RepairLocal all1 r1 A1 F1 a -> RepairLocal all2 r2 A2 F2 b ->
                 RepairLocal pall pr pA pF (a, b)) /\
    (forall a1 b1 a2 b2, DisjointFP all1 F1 a1 a2 -> DisjointFP all2 F2 b1 b2 ->
                 DisjointFP pall pF (a1, b1) (a2, b2)).
  Proof.
    intros (P1 & P2 & P3) (Q1 & Q2 & Q3) D1 D2. split; [|split; [|split; [|split; [|split]]]].
    - split; [|split].
      + intros [i|i] [s1 s2] Hi H; simpl in *.
        * apply P1; [apply in_pall_l, Hi | exact H].
        * apply Q1; [apply in_pall_r, Hi | exact H].
      + intros [i|i] [s1 s2] Hi H; simpl in *.
        * rewrite (P2 i s1 (in_pall_l i Hi) H). reflexivity.
        * rewrite (Q2 i s2 (in_pall_r i Hi) H). reflexivity.
      + intros [i|i] [j|j] [s1 s2] Hi Hj; simpl; try reflexivity.
        * rewrite (P3 i j s1 (in_pall_l i Hi) (in_pall_l j Hj)). reflexivity.
        * rewrite (Q3 i j s2 (in_pall_r i Hi) (in_pall_r j Hj)). reflexivity.
    - intros [s1 s2]. unfold pall. rewrite R_app, R_inr, R_inl. unfold pN; simpl.
      rewrite D1, D2. reflexivity.
    - intros [s1 s2]. unfold validD, pall. rewrite fb_app, !fb_map. reflexivity.
    - intros a b H1 H2 [i|i] [s1 s2] Hi H; simpl in *.
      + apply H1; [apply in_pall_l, Hi | exact H].
      + apply H2; [apply in_pall_r, Hi | exact H].
    - intros a b H1 H2 [i|i] [s1 s2] Hi H; unfold pA, pr; simpl in *.
      + rewrite (H1 i s1 (in_pall_l i Hi) H). reflexivity.
      + rewrite (H2 i s2 (in_pall_r i Hi) H). reflexivity.
    - intros a1 b1 a2 b2 H1 H2 [i|i] Hi H; simpl in *.
      + apply H1; [apply in_pall_l, Hi | exact H].
      + apply H2; [apply in_pall_r, Hi | exact H].
  Qed.
End Product.

(* Non-vacuity for product lifting: two order-fulfillment registries side by side. *)
Theorem calc_product_instance :
  IsRegistry (pv o_valid o_valid) (prho o_rho o_rho) (pPhi o_Phi o_Phi) (pN o_rho o_rho) /\
  (forall s, CC1_at (pN o_rho o_rho) (pA o_A o_A) (true, false) (false, true) s) /\
  (forall e, CC2_ev (pv o_valid o_valid) (prho o_rho o_rho) (pN o_rho o_rho) (pA o_A o_A) e).
Proof.
  destruct calc_order_cc1 as (Hcc1 & Ha & Hc).
  assert (Hcc1' : forall s, CC1_at o_rho o_A false true s).
  { intros s. unfold CC1_at. symmetry. apply Hcc1. }
  destruct (base_thm_product o_valid o_valid o_rho o_rho o_Phi o_Phi o_rho o_rho o_A o_A
              o_registry o_registry) as (Hreg & H1 & H2).
  split; [exact Hreg|]. split.
  - intros [s1 s2]. apply H1. split; [apply Hcc1 | apply Hcc1'].
  - intros [[|] [|]]; apply H2; assumption.
Qed.

(* Non-vacuity for the components form: two order-fulfillment registries side by side,
   approve acting on the first, credit on the second. CC1 holds at every valid state, and
   at the invalid state ((approved, b0), (approved, b0)) the absorption condition holds too. *)
Theorem calc_components_instance :
  (forall s1 s2, o_valid s1 = true -> o_valid s2 = true ->
     CC1_at (cN o_rho o_rho) (cA o_approve o_credit) true false (s1, s2)) /\
  CC1_at (cN o_rho o_rho) (cA o_approve o_credit) true false ((approved, b0), (approved, b0)).
Proof.
  assert (Hi : forall x, o_rho (o_rho x) = o_rho x) by fin.
  assert (Hf : forall x, o_valid x = true -> o_rho x = x) by fin.
  split.
  - intros s1 s2 V1 V2.
    apply (calc_components_cc1_valid o_valid o_valid); assumption.
  - apply (calc_components_cc1_iff o_rho o_rho o_approve o_credit); try assumption.
    split; reflexivity.
Qed.
