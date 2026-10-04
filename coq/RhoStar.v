(* RhoStar.v: iterated compensation rho* constructed from WFC, and the base facts that rest on it
   (ROADMAP item 7, work package WP1 of coq/PAPER-MAP.md), mechanized axiom-free.

   Governance.v, GovernanceCausal.v, GovernanceWF.v and GovernanceConverse.v take rho* as an
   abstract parameter with the hypotheses rho_star_reach (and, in GovernanceConverse.v,
   rho_star_valid). The paper (Base, Def. "Iterated Compensation") instead DEFINES rho* from rho:
   rho*(s) = rho^m(s) for the least m with V(rho^m(s)), which exists by WFC. This file constructs
   that operator and proves its specification, so the headline theorems hold with rho* defined
   rather than assumed: every rho* hypothesis is discharged.

   Paper map (label -> Coq theorem):
     Base def:rhostar           base_def_rhostar, base_def_rhostar_least_unique,
                                rho_star_canonical (independent of the measure)
     Base sec:calculus (i)-(iii) rho_star_valid, rho_star_fix, rho_star_idem
     Cat sec. 3 (C23)           cat_bg_rho_idempotent, cat_bg_valid_from_any_state,
                                cat_bg_lemma_zero; counterexample to the unqualified
                                "valid set non-empty": cat_bg_nonempty_needs_a_state
     Base rem:absorption (B15)  base_rem_absorption, base_rem_absorption_enabled
     Base thm:strong-absorption base_thm_strong_absorption, and the converse
     (B34)                      strong_absorption_iff_cc2
     Base lem:termination (B18) base_lem_termination_bound (all-pairs GRS),
                                causal_lem_termination_bound (causal GRS)
     Base lem:finite-implies-ubc base_lem_finite_implies_ubc
     (B8)
     Base def:config (B10)      deps_enabled_after_remove, deps_enabled_after_comp (Governance.v),
                                deps_causal_enabled_after_remove, deps_causal_enabled_after_comp
                                (GovernanceCausal.v), deps_coenabled_independent
     Base thm:complexity (B29)  base_thm_complexity_per_event, base_thm_complexity_comp_total,
                                rho_star_steps_le_measure
     Base cor:unique-nf with rho* constructed and deps-based enabledness:
                                paper_governance_confluent, paper_governance_unique_normal_forms,
                                paper_causal_governance_confluent,
                                paper_causal_governance_unique_normal_forms
     Headline theorems with rho* constructed (no rho* hypothesis):
                                wfc_governance_confluent, wfc_governance_unique_normal_forms,
                                wfc_causal_governance_confluent,
                                wfc_causal_governance_unique_normal_forms,
                                wfc_governance_wf_confluent, wfc_causal_governance_wf_confluent,
                                wfc_cc_exact_from
   Non-vacuity: the four-level saturating counter (lv_* below) discharges every hypothesis set, and
   the unbounded withdrawal registry of GovernanceWF.v gets its rho* constructed (zw_rho_star_built).

   The construction needs V decidable (the paper's V_R is Boolean-valued) and nothing else beyond
   determinism of rho (rho is a function). *)

Require Import NC.Newman NC.Governance NC.GovernanceCausal NC.GovernanceWF NC.GovernanceConverse
  NC.Categorical.
From Coq Require Import List.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import Wellfounded.Inverse_Image.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
Import ListNotations.

(* ============================================================================================ *)
(* 1. The compensation chain, relationally                                                        *)
(* ============================================================================================ *)

Section Chain.
  Context {State : Type}.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.

  (* crel s t: iterating rho from s, stopping at the first valid state, ends at t. *)
  Inductive crel : State -> State -> Prop :=
  | crel_done : forall s, valid s -> crel s s
  | crel_more : forall s t, ~ valid s -> crel (rho s) t -> crel s t.

  (* rho^m, unfolded on the inside: iterN (S m) s = iterN m (rho s). *)
  Fixpoint iterN (m : nat) (s : State) : State :=
    match m with
    | 0 => s
    | S m' => iterN m' (rho s)
    end.

  Lemma crel_valid : forall s t, crel s t -> valid t.
  Proof. intros s t H. induction H; assumption. Qed.

  Lemma crel_fun : forall s t1 t2, crel s t1 -> crel s t2 -> t1 = t2.
  Proof.
    intros s t1 t2 H1. revert t2. induction H1 as [s V | s t Hn H IH]; intros t2 H2.
    - inversion H2; subst; [reflexivity | contradiction].
    - inversion H2; subst; [contradiction | apply IH; assumption].
  Qed.

  Lemma crel_fix : forall s t, valid s -> crel s t -> t = s.
  Proof. intros s t V H. apply (crel_fun s); [exact H | constructor; exact V]. Qed.

  Lemma crel_rho : forall s t, ~ valid s -> crel s t -> crel (rho s) t.
  Proof. intros s t Hn H. inversion H; subst; [contradiction | assumption]. Qed.

  Lemma crel_self : forall s t, crel s t -> crel t t.
  Proof. intros s t H. constructor. eapply crel_valid; exact H. Qed.

  (* The relational chain is exactly "rho^m for the least m reaching validity". *)
  Lemma crel_iter : forall s t, crel s t ->
    exists m, t = iterN m s /\ valid (iterN m s) /\ (forall k, k < m -> ~ valid (iterN k s)).
  Proof.
    intros s t H. induction H as [s V | s t Hn H [m [E [V L]]]].
    - exists 0. split; [reflexivity |]. split; [exact V |]. intros k Hk. lia.
    - exists (S m). simpl. split; [exact E |]. split; [exact V |].
      intros [| k] Hk; simpl; [exact Hn |]. apply L. lia.
  Qed.

  Lemma iter_crel : forall m s,
    valid (iterN m s) -> (forall k, k < m -> ~ valid (iterN k s)) -> crel s (iterN m s).
  Proof.
    induction m as [| m IH]; intros s V L; simpl in *.
    - constructor. exact V.
    - constructor 2.
      + exact (L 0 ltac:(lia)).
      + apply IH; [exact V |]. intros k Hk. exact (L (S k) ltac:(lia)).
  Qed.

  Lemma least_unique : forall s m1 m2,
    valid (iterN m1 s) -> (forall k, k < m1 -> ~ valid (iterN k s)) ->
    valid (iterN m2 s) -> (forall k, k < m2 -> ~ valid (iterN k s)) -> m1 = m2.
  Proof.
    intros s m1 m2 V1 L1 V2 L2.
    assert (T : m1 < m2 \/ m1 = m2 \/ m2 < m1) by lia. destruct T as [H | [H | H]].
    - exfalso. exact (L2 m1 H V1).
    - exact H.
    - exfalso. exact (L1 m2 H V2).
  Qed.

  (* Reachability by compensation steps, in both rewrite systems. *)
  Section Reach.
    Context {Event : Type}.
    Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
    Variable apply : Event -> State -> State.
    Variable enabled : Event -> State -> list Event -> Prop.

    Lemma crel_reach_gov : forall s t B, crel s t ->
      star (Governance.step event_eq_dec apply rho valid enabled) (s, B) (t, B).
    Proof.
      intros s t B H. induction H as [s V | s t Hn H IH].
      - apply star_refl.
      - eapply star_step; [apply Governance.st_comp; exact Hn | exact IH].
    Qed.

    Lemma crel_reach_causal : forall s t B, crel s t ->
      star (GovernanceCausal.step event_eq_dec apply rho valid enabled) (s, B) (t, B).
    Proof.
      intros s t B H. induction H as [s V | s t Hn H IH].
      - apply star_refl.
      - eapply star_step; [apply GovernanceCausal.st_comp; exact Hn | exact IH].
    Qed.
  End Reach.
End Chain.

(* ============================================================================================ *)
(* 2. Construction under WFC over any well-founded order (GovernanceWF.v's setting)              *)
(* ============================================================================================ *)

Section ConstructWF.
  Context {State : Type}.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s).

  Definition crel_exists : forall s, { t | crel rho valid s t }.
  Proof.
    refine (well_founded_induction_type
              (wf_inverse_image State P ltP Phi wf_ltP)
              (fun s => { t | crel rho valid s t }) _).
    intros s IH. destruct (valid_dec s) as [V | Hn].
    - exists s. constructor. exact V.
    - destruct (IH (rho s) (wfc_wf s Hn)) as [t Ht]. exists t. constructor 2; assumption.
  Defined.

  Definition rho_star_wf (s : State) : State := proj1_sig (crel_exists s).

  Lemma rho_star_wf_crel : forall s, crel rho valid s (rho_star_wf s).
  Proof. intro s. unfold rho_star_wf. destruct (crel_exists s) as [t Ht]. exact Ht. Qed.
End ConstructWF.

(* ============================================================================================ *)
(* 3. Construction under WFC with a nat measure (the paper's Axiom WFC): computable by fuel       *)
(* ============================================================================================ *)

Section ConstructNat.
  Context {State : Type}.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable Phi : State -> nat.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.

  Fixpoint comp_fuel (n : nat) (s : State) : State :=
    match n with
    | 0 => s
    | S n' => if valid_dec s then s else comp_fuel n' (rho s)
    end.

  (* rho*: at most Phi s compensation steps are ever needed. *)
  Definition rho_star (s : State) : State := comp_fuel (Phi s) s.

  Lemma comp_fuel_crel : forall n s, Phi s <= n -> crel rho valid s (comp_fuel n s).
  Proof.
    induction n as [| n IH]; intros s Hle; simpl.
    - destruct (valid_dec s) as [V | Hn].
      + constructor. exact V.
      + exfalso. pose proof (wfc s Hn). lia.
    - destruct (valid_dec s) as [V | Hn].
      + constructor. exact V.
      + constructor 2; [exact Hn |]. apply IH. pose proof (wfc s Hn). lia.
  Qed.

  Lemma rho_star_crel : forall s, crel rho valid s (rho_star s).
  Proof. intro s. apply comp_fuel_crel. lia. Qed.

  (* Base def:rhostar, exactly: rho*(s) = rho^m(s) for the least m with V(rho^m(s)); such an m
     exists (WFC) and is unique. *)
  Theorem base_def_rhostar : forall s, exists m,
    rho_star s = iterN rho m s /\ valid (iterN rho m s) /\
    (forall k, k < m -> ~ valid (iterN rho k s)).
  Proof. intro s. apply crel_iter. apply rho_star_crel. Qed.

  Theorem base_def_rhostar_least_unique : forall s m,
    valid (iterN rho m s) -> (forall k, k < m -> ~ valid (iterN rho k s)) ->
    rho_star s = iterN rho m s.
  Proof.
    intros s m V L. destruct (base_def_rhostar s) as [m' [E [V' L']]].
    rewrite E. f_equal. apply (least_unique rho valid s); assumption.
  Qed.

  (* Base sec:calculus, Notation (i), (ii), (iii). *)
  Theorem rho_star_valid : forall s, valid (rho_star s).
  Proof. intro s. eapply crel_valid. apply rho_star_crel. Qed.

  Theorem rho_star_fix : forall s, valid s -> rho_star s = s.
  Proof. intros s V. apply (crel_fix rho valid s); [exact V | apply rho_star_crel]. Qed.

  Theorem rho_star_idem : forall s, rho_star (rho_star s) = rho_star s.
  Proof. intro s. apply rho_star_fix. apply rho_star_valid. Qed.

  (* rho(s) lies on the compensation chain of an invalid s (used by thm:strong-absorption). *)
  Theorem rho_star_rho : forall s, ~ valid s -> rho_star (rho s) = rho_star s.
  Proof.
    intros s Hn. apply (crel_fun rho valid (rho s)); [apply rho_star_crel |].
    apply crel_rho; [exact Hn | apply rho_star_crel].
  Qed.

  (* The number of compensation steps rho* takes is at most the measure (B29's per-event bound). *)
  Theorem rho_star_steps_le_measure : forall s m,
    rho_star s = iterN rho m s -> valid (iterN rho m s) ->
    (forall k, k < m -> ~ valid (iterN rho k s)) -> m <= Phi s.
  Proof.
    intros s m _ _ L. revert s L. induction m as [| m IH]; intros s L; [lia |].
    pose proof (L 0 ltac:(lia)) as Hn. simpl in Hn. pose proof (wfc s Hn).
    assert (m <= Phi (rho s)); [| lia].
    apply IH. intros k Hk. exact (L (S k) ltac:(lia)).
  Qed.
End ConstructNat.

(* rho* depends only on rho and V: any two WFC measures (nat or any well-founded order) give the
   same operator, so "the" rho* of the paper is well-defined. *)
Theorem rho_star_canonical :
  forall {State : Type} (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s}) (Phi : State -> nat)
    (P : Type) (ltP : P -> P -> Prop) (wf_ltP : well_founded ltP) (Psi : State -> P)
    (wfc : forall s, ~ valid s -> Phi (rho s) < Phi s)
    (wfc_wf : forall s, ~ valid s -> ltP (Psi (rho s)) (Psi s)),
  forall s, rho_star rho valid valid_dec Phi s = rho_star_wf rho valid valid_dec P ltP wf_ltP Psi wfc_wf s.
Proof.
  intros State rho valid vd Phi P ltP W Psi wfc wfcw s.
  apply (crel_fun rho valid s); [apply rho_star_crel; exact wfc | apply rho_star_wf_crel].
Qed.

Theorem rho_star_wf_valid :
  forall {State : Type} (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s})
    (P : Type) (ltP : P -> P -> Prop) (wf_ltP : well_founded ltP) (Phi : State -> P)
    (wfc_wf : forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s)),
  forall s, valid (rho_star_wf rho valid valid_dec P ltP wf_ltP Phi wfc_wf s).
Proof. intros. eapply crel_valid. apply rho_star_wf_crel. Qed.

Theorem rho_star_wf_idem :
  forall {State : Type} (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s})
    (P : Type) (ltP : P -> P -> Prop) (wf_ltP : well_founded ltP) (Phi : State -> P)
    (wfc_wf : forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s)),
  let N := rho_star_wf rho valid valid_dec P ltP wf_ltP Phi wfc_wf in
  forall s, N (N s) = N s.
Proof.
  intros State rho valid vd P ltP W Phi wfc N s. unfold N.
  apply (crel_fix rho valid); [eapply crel_valid; apply rho_star_wf_crel | apply rho_star_wf_crel].
Qed.

(* ============================================================================================ *)
(* 4. Cat sec. 3 background (C23): WFC makes the normalizer idempotent, its valid set reached     *)
(*    from any state; Lemma 0 then applies with the idempotence hypothesis discharged            *)
(* ============================================================================================ *)

Section CatBackground.
  Context {State : Type}.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable Phi : State -> nat.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.

  Local Notation N := (rho_star rho valid valid_dec Phi).

  Theorem cat_bg_rho_idempotent : forall s, N (N s) = N s.
  Proof. exact (rho_star_idem rho valid valid_dec Phi wfc). Qed.

  (* "Compensation reaches a valid state from any state." *)
  Theorem cat_bg_valid_from_any_state : forall s : State, exists v, valid v /\ N s = v.
  Proof. intro s. exists (N s). split; [apply rho_star_valid; exact wfc | reflexivity]. Qed.

  (* Cat Lemma 0 for the constructed normalizer: valid set = image = fixed points, with the
     idempotence hypothesis of Categorical.v discharged by WFC. *)
  Theorem cat_bg_lemma_zero : forall x,
    (valid x <-> Fixed N x) /\ (InImage N x <-> Fixed N x).
  Proof.
    intro x. split.
    - unfold Fixed. split.
      + apply rho_star_fix. exact wfc.
      + intro E. rewrite <- E. apply rho_star_valid. exact wfc.
    - apply image_iff_fixed. exact cat_bg_rho_idempotent.
  Qed.
End CatBackground.

(* The unqualified "its valid set is non-empty" needs the state space to be non-empty: the empty
   registry satisfies WFC (vacuously) and has an empty valid set. The corrected statement is
   cat_bg_valid_from_any_state (non-empty as soon as there is a state). *)
Theorem cat_bg_nonempty_needs_a_state :
  let rho := fun s : Empty_set => s in
  let valid := fun _ : Empty_set => True in
  let Phi := fun _ : Empty_set => 0 in
  (forall s, ~ valid s -> Phi (rho s) < Phi s) /\ ~ (exists v, valid v).
Proof. simpl. split; [intros [] | intros [[] _]]. Qed.

(* ============================================================================================ *)
(* 5. Compensation absorption (Base rem:absorption) and strong absorption (thm:strong-absorption) *)
(* ============================================================================================ *)

Section Absorption.
  Context {State Event : Type}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable Phi : State -> nat.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.

  Local Notation N := (rho_star rho valid valid_dec Phi).

  (* Base rem:absorption: CC2 generalizes from one compensation step to rho*. *)
  Theorem base_rem_absorption :
    (forall s e, ~ valid s -> N (apply e s) = N (apply e (rho s))) ->
    forall s e, N (apply e s) = N (apply e (N s)).
  Proof.
    intros cc2 s e.
    assert (G : forall t, crel rho valid s t -> N (apply e s) = N (apply e t)).
    { intros t H. induction H as [s V | s t Hn H IH]; [reflexivity |].
      rewrite (cc2 s e Hn). exact IH. }
    apply G. apply rho_star_crel. exact wfc.
  Qed.

  (* The same with CC2 required only for enabled events (the paper's Axiom CC2), given that
     compensation preserves enabledness (Governance.v's enabled_after_comp). *)
  Theorem base_rem_absorption_enabled :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall s B e, enabled e s B -> enabled e (rho s) B) ->
    (forall s B e, enabled e s B -> ~ valid s -> N (apply e s) = N (apply e (rho s))) ->
    forall s B e, enabled e s B -> N (apply e s) = N (apply e (N s)).
  Proof.
    intros enabled eac cc2 s B e Hen.
    assert (G : forall s t, crel rho valid s t -> enabled e s B -> N (apply e s) = N (apply e t)).
    { clear s Hen. intros s t H. induction H as [s V | s t Hn H IH]; intros Hs; [reflexivity |].
      rewrite (cc2 s B e Hs Hn). apply IH. apply eac. exact Hs. }
    apply G; [apply rho_star_crel; exact wfc | exact Hen].
  Qed.

  (* Base thm:strong-absorption, exactly: strong absorption implies CC2. *)
  Theorem base_thm_strong_absorption :
    (forall e s, N (apply e s) = N (apply e (N s))) ->
    forall s e, ~ valid s -> N (apply e s) = N (apply e (rho s)).
  Proof.
    intros SA s e Hn. rewrite (SA e s), (SA e (rho s)).
    rewrite (rho_star_rho rho valid valid_dec Phi wfc s Hn). reflexivity.
  Qed.

  (* Together: under WFC, CC2 and strong absorption are equivalent. *)
  Theorem strong_absorption_iff_cc2 :
    (forall e s, N (apply e s) = N (apply e (N s))) <->
    (forall s e, ~ valid s -> N (apply e s) = N (apply e (rho s))).
  Proof.
    split.
    - apply base_thm_strong_absorption.
    - intros cc2 e s. apply base_rem_absorption. exact cc2.
  Qed.
End Absorption.

(* ============================================================================================ *)
(* 6. Step bounds under UBC (Base lem:termination, thm:complexity)                               *)
(* ============================================================================================ *)

(* n-step closure. *)
Inductive nstar {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| ns_refl : forall x, nstar R 0 x x
| ns_step : forall n x y z, R x y -> nstar R n y z -> nstar R (S n) x z.

Lemma star_nstar : forall {A} (R : A -> A -> Prop) x y, star R x y -> exists n, nstar R n x y.
Proof.
  intros A R x y H. induction H as [x | x y z Rxy _ [n IH]].
  - exists 0. constructor.
  - exists (S n). econstructor; eassumption.
Qed.

Section Bounds.
  Context {State Event : Type}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Variable Phi   : State -> nat.
  Variable rm    : Event -> list Event -> list Event.
  Variable R : State * list Event -> State * list Event -> Prop.

  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.
  Hypothesis rm_length : forall e B, In e B -> length (rm e B) < length B.
  (* R is a governance rewrite relation: each step applies a buffered event or compensates. *)
  Hypothesis R_shape : forall s B d, R (s, B) d ->
    (exists e, In e B /\ d = (apply e s, rm e B)) \/ (~ valid s /\ d = (rho s, B)).

  Variable M : nat.
  Hypothesis ubc : forall s, Phi s <= M.   (* Axiom UBC *)

  (* Runs counting apply steps (a) and compensation steps (k) separately. *)
  Inductive runc : nat -> nat -> State * list Event -> State * list Event -> Prop :=
  | rc_refl : forall c, runc 0 0 c c
  | rc_apply : forall a k s B e d, In e B -> runc a k (apply e s, rm e B) d ->
      runc (S a) k (s, B) d
  | rc_comp : forall a k s B d, ~ valid s -> runc a k (rho s, B) d ->
      runc a (S k) (s, B) d.

  Lemma nstar_runc : forall n c d, nstar R n c d -> exists a k, a + k = n /\ runc a k c d.
  Proof.
    intros n c d H. induction H as [c | n [s B] y z Rxy _ [a [k [E IH]]]].
    - exists 0, 0. split; [reflexivity | constructor].
    - destruct (R_shape s B y Rxy) as [[e [Hin ->]] | [Hn ->]].
      + exists (S a), k. split; [lia | econstructor; eassumption].
      + exists a, (S k). split; [lia | econstructor; eassumption].
  Qed.

  (* The invariant: a <= |B| and k <= Phi(s) + a * M. *)
  Lemma runc_bound : forall a k s B d, runc a k (s, B) d ->
    a <= length B /\ k <= Phi s + a * M.
  Proof.
    intros a k s B d H. remember (s, B) as c eqn:Ec. revert s B Ec.
    induction H as [c | a k s' B' e d Hin _ IH | a k s' B' d Hn _ IH]; intros s B Ec.
    - split; lia.
    - injection Ec as -> ->. destruct (IH _ _ eq_refl) as [Ha Hk].
      pose proof (rm_length e B Hin). pose proof (ubc (apply e s)). simpl. split; lia.
    - injection Ec as -> ->. destruct (IH _ _ eq_refl) as [Ha Hk].
      pose proof (wfc s Hn). split; lia.
  Qed.

  (* Base lem:termination, the uniform bound: every reduction sequence from (s, E) has at most
     |E| + (|E| + 1) * M steps. *)
  Theorem termination_bound : forall s E n d, nstar R n (s, E) d ->
    n <= length E + (length E + 1) * M.
  Proof.
    intros s E n d H. destruct (nstar_runc n _ _ H) as [a [k [<- Hr]]].
    destruct (runc_bound a k s E d Hr) as [Ha Hk]. pose proof (ubc s). nia.
  Qed.

  (* Base thm:complexity, model level: at most M compensation steps per applied event, plus at most
     M before the first one, so compensation over n applied events costs at most (n + 1) * M. *)
  Theorem comp_total_bound : forall a k s E d, runc a k (s, E) d ->
    a <= length E /\ k <= (a + 1) * M.
  Proof.
    intros a k s E d H. destruct (runc_bound a k s E d H) as [Ha Hk].
    pose proof (ubc s). split; lia.
  Qed.

  (* Per event: after an event is applied, the compensation that follows it (a run of compensation
     steps only) takes at most M steps. *)
  Theorem comp_per_event_bound : forall e s B k d, runc 0 k (apply e s, B) d -> k <= M.
  Proof.
    intros e s B k d H. destruct (runc_bound 0 k _ _ d H) as [_ Hk].
    pose proof (ubc (apply e s)). lia.
  Qed.
End Bounds.

Section ConcreteBounds.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Variable Phi   : State -> nat.
  Variable enabled : Event -> State -> list Event -> Prop.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.
  Variable M : nat.
  Hypothesis ubc : forall s, Phi s <= M.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).
  Local Notation cstep := (GovernanceCausal.step event_eq_dec apply rho valid enabled).

  Lemma gstep_shape : forall s B d, gstep (s, B) d ->
    (exists e, In e B /\ d = (apply e s, Governance.remove1 event_eq_dec e B)) \/
    (~ valid s /\ d = (rho s, B)).
  Proof.
    intros s B d H. inversion H; subst; [left; eexists; split; eauto | right; split; auto].
  Qed.

  Lemma cstep_shape : forall s B d, cstep (s, B) d ->
    (exists e, In e B /\ d = (apply e s, GovernanceCausal.remove1 event_eq_dec e B)) \/
    (~ valid s /\ d = (rho s, B)).
  Proof.
    intros s B d H. inversion H; subst; [left; eexists; split; eauto | right; split; auto].
  Qed.

  (* Base lem:termination (step bound), for the all-pairs GRS of Governance.v. *)
  Theorem base_lem_termination_bound : forall s E n d, nstar gstep n (s, E) d ->
    n <= length E + (length E + 1) * M.
  Proof.
    apply (termination_bound apply rho valid Phi (Governance.remove1 event_eq_dec) gstep wfc
             (Governance.remove1_length_in event_eq_dec) gstep_shape M ubc).
  Qed.

  (* The same bound for the causal GRS of GovernanceCausal.v. *)
  Theorem causal_lem_termination_bound : forall s E n d, nstar cstep n (s, E) d ->
    n <= length E + (length E + 1) * M.
  Proof.
    apply (termination_bound apply rho valid Phi (GovernanceCausal.remove1 event_eq_dec) cstep wfc
             (GovernanceCausal.remove1_length_in event_eq_dec) cstep_shape M ubc).
  Qed.

  (* Base thm:complexity (model-level part): every reduction from (s, E) is a run of a applies and
     k compensations with a <= |E| and k <= (a + 1) * M: compensation is O(1) per event. *)
  Theorem base_thm_complexity_comp_total : forall s E n d, nstar gstep n (s, E) d ->
    exists a k, a + k = n /\ a <= length E /\ k <= (a + 1) * M.
  Proof.
    intros s E n d H.
    destruct (nstar_runc apply rho valid (Governance.remove1 event_eq_dec) gstep gstep_shape n _ _ H)
      as [a [k [E' Hr]]].
    exists a, k. split; [exact E' |].
    exact (comp_total_bound apply rho valid Phi (Governance.remove1 event_eq_dec) wfc
             (Governance.remove1_length_in event_eq_dec) M ubc a k s E d Hr).
  Qed.

  (* Base thm:complexity, per event: the compensation after one event is at most M steps. *)
  Theorem base_thm_complexity_per_event : forall e s B k d,
    runc apply rho valid (Governance.remove1 event_eq_dec) 0 k (apply e s, B) d -> k <= M.
  Proof.
    exact (comp_per_event_bound apply rho valid Phi (Governance.remove1 event_eq_dec) wfc
             (Governance.remove1_length_in event_eq_dec) M ubc).
  Qed.
End ConcreteBounds.

(* ============================================================================================ *)
(* 7. Finite state spaces imply UBC (Base lem:finite-implies-ubc)                                *)
(* ============================================================================================ *)

Fixpoint maxl (l : list nat) : nat :=
  match l with [] => 0 | x :: xs => Nat.max x (maxl xs) end.

Lemma maxl_ge : forall l x, In x l -> x <= maxl l.
Proof. induction l as [| y l IH]; intros x Hin; simpl in *; [contradiction |]. destruct Hin; subst; [lia |]. specialize (IH x H). lia. Qed.

Lemma maxl_in : forall l, l <> [] -> In (maxl l) l.
Proof.
  induction l as [| y l IH]; intros Hne; [contradiction |]. simpl.
  destruct l as [| z l']; [simpl; left; lia |].
  assert (Hi : In (maxl (z :: l')) (z :: l')) by (apply IH; discriminate).
  assert (Hc : Nat.max y (maxl (z :: l')) = maxl (z :: l') \/ Nat.max y (maxl (z :: l')) = y) by lia.
  destruct Hc as [-> | ->]; [right; exact Hi | left; reflexivity].
Qed.

(* With Sigma finite (listed by l) and WFC, UBC holds with M = max Phi; the maximum is attained
   as soon as Sigma has a state. *)
Theorem base_lem_finite_implies_ubc :
  forall {State : Type} (rho : State -> State) (valid : State -> Prop) (Phi : State -> nat)
    (l : list State),
  (forall s, In s l) ->
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  exists M, (forall s, Phi s <= M) /\ (forall s0 : State, exists s, Phi s = M).
Proof.
  intros State rho valid Phi l Hl _. exists (maxl (map Phi l)). split.
  - intro s. apply maxl_ge. apply in_map. apply Hl.
  - intro s0. assert (Hne : map Phi l <> []).
    { intro E. pose proof (Hl s0) as H. apply (in_map Phi) in H. rewrite E in H. contradiction. }
    destruct (proj1 (in_map_iff _ _ _) (maxl_in _ Hne)) as [s [Hs _]]. exists s. exact Hs.
Qed.

(* ============================================================================================ *)
(* 8. Deps-based enabledness (Base def:config) discharges the enabledness hypotheses             *)
(* ============================================================================================ *)

(* Base def:config: e in B is enabled iff deps(e) and B are disjoint. *)
Definition deps_enabled {State Event : Type} (deps : Event -> list Event)
  (e : Event) (_ : State) (B : list Event) : Prop :=
  In e B /\ forall d, In d (deps e) -> ~ In d B.

Section Deps.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable deps : Event -> list Event.

  Lemma g_in_remove1_neq : forall e x l, In x l -> x <> e ->
    In x (Governance.remove1 event_eq_dec e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |]. simpl.
    destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma g_in_remove1_sub : forall e x l, In x (Governance.remove1 event_eq_dec e l) -> In x l.
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin; [destruct Hin |]. simpl in Hin.
    destruct (event_eq_dec y e); [right; exact Hin |].
    destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; exact Hin].
  Qed.

  Lemma c_in_remove1_neq : forall e x l, In x l -> x <> e ->
    In x (GovernanceCausal.remove1 event_eq_dec e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |]. simpl.
    destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma c_in_remove1_sub : forall e x l, In x (GovernanceCausal.remove1 event_eq_dec e l) -> In x l.
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin; [destruct Hin |]. simpl in Hin.
    destruct (event_eq_dec y e); [right; exact Hin |].
    destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; exact Hin].
  Qed.

  (* Governance.v's enabled_after_remove, for deps-based enabledness and ANY normalizer. *)
  Theorem deps_enabled_after_remove :
    forall (apply : Event -> State -> State) (N : State -> State) sigma B e1 e2,
      deps_enabled deps e1 sigma B -> deps_enabled deps e2 sigma B -> e1 <> e2 ->
      In e2 (Governance.remove1 event_eq_dec e1 B) /\
      deps_enabled deps e2 (N (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B).
  Proof.
    intros apply N sigma B e1 e2 _ [Hin2 D2] Hne.
    assert (H : In e2 (Governance.remove1 event_eq_dec e1 B))
      by (apply g_in_remove1_neq; [exact Hin2 | intro E; apply Hne; symmetry; exact E]).
    split; [exact H |]. split; [exact H |].
    intros d Hd Hr. exact (D2 d Hd (g_in_remove1_sub _ _ _ Hr)).
  Qed.

  Theorem deps_enabled_after_comp :
    forall (rho : State -> State) sigma B e,
      deps_enabled deps e sigma B -> deps_enabled deps e (rho sigma) B.
  Proof. intros rho sigma B e H. exact H. Qed.

  Theorem deps_causal_enabled_after_remove :
    forall (apply : Event -> State -> State) (N : State -> State) sigma B e1 e2,
      deps_enabled deps e1 sigma B -> deps_enabled deps e2 sigma B -> e1 <> e2 ->
      In e2 (GovernanceCausal.remove1 event_eq_dec e1 B) /\
      deps_enabled deps e2 (N (apply e1 sigma)) (GovernanceCausal.remove1 event_eq_dec e1 B).
  Proof.
    intros apply N sigma B e1 e2 _ [Hin2 D2] Hne.
    assert (H : In e2 (GovernanceCausal.remove1 event_eq_dec e1 B))
      by (apply c_in_remove1_neq; [exact Hin2 | intro E; apply Hne; symmetry; exact E]).
    split; [exact H |]. split; [exact H |].
    intros d Hd Hr. exact (D2 d Hd (c_in_remove1_sub _ _ _ Hr)).
  Qed.

  Theorem deps_causal_enabled_after_comp :
    forall (rho : State -> State) sigma B e,
      deps_enabled deps e sigma B -> deps_enabled deps e (rho sigma) B.
  Proof. intros rho sigma B e H. exact H. Qed.

  (* Two events enabled together are causally independent (neither is a dependency of the other),
     so CC1 on co-enabled pairs is CC1 on the paper's "causally independent and simultaneously
     enabled" pairs. *)
  Theorem deps_coenabled_independent : forall (sigma : State) B e1 e2,
    deps_enabled deps e1 sigma B -> deps_enabled deps e2 sigma B ->
    ~ In e1 (deps e2) /\ ~ In e2 (deps e1).
  Proof.
    intros sigma B e1 e2 [H1 D1] [H2 D2]. split.
    - intro H. exact (D2 e1 H H1).
    - intro H. exact (D1 e2 H H2).
  Qed.
End Deps.

(* ============================================================================================ *)
(* 9. Headline theorems with rho* constructed: the rho* hypotheses are gone                      *)
(* ============================================================================================ *)

Section Headline.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable Phi : State -> nat.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.   (* Axiom WFC *)

  Local Notation N := (rho_star rho valid valid_dec Phi).

  Lemma rs_reach_gov : forall enabled s B,
    star (Governance.step event_eq_dec apply rho valid enabled) (s, B) (N s, B).
  Proof. intros. apply crel_reach_gov. apply rho_star_crel. exact wfc. Qed.

  Lemma rs_reach_causal : forall enabled s B,
    star (GovernanceCausal.step event_eq_dec apply rho valid enabled) (s, B) (N s, B).
  Proof. intros. apply crel_reach_causal. apply rho_star_crel. exact wfc. Qed.

  (* Governance.v's governance_confluent and governance_unique_normal_forms, with rho* the
     constructed operator: hypotheses are WFC, CC1, CC2 and the enabledness facts only. *)
  Theorem wfc_governance_confluent :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma e1 e2, N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (Governance.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    confluent (Governance.step event_eq_dec apply rho valid enabled).
  Proof.
    intros enabled cc1 cc2 ear eac.
    exact (Governance.governance_confluent event_eq_dec apply rho N valid Phi enabled wfc
             (rs_reach_gov enabled) cc1 cc2 ear eac).
  Qed.

  Theorem wfc_governance_unique_normal_forms :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma e1 e2, N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (Governance.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    forall c n1 n2,
      star (Governance.step event_eq_dec apply rho valid enabled) c n1 ->
      normal_form (Governance.step event_eq_dec apply rho valid enabled) n1 ->
      star (Governance.step event_eq_dec apply rho valid enabled) c n2 ->
      normal_form (Governance.step event_eq_dec apply rho valid enabled) n2 -> n1 = n2.
  Proof.
    intros enabled cc1 cc2 ear eac c n1 n2 S1 N1 S2 N2.
    eapply unique_normal_forms; try eassumption. apply wfc_governance_confluent; assumption.
  Qed.

  Theorem wfc_causal_governance_confluent :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (GovernanceCausal.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (GovernanceCausal.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    confluent (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Proof.
    intros enabled cc1 cc2 ear eac.
    exact (GovernanceCausal.causal_governance_confluent event_eq_dec apply rho N valid Phi enabled
             wfc (rs_reach_causal enabled) cc1 cc2 ear eac).
  Qed.

  Theorem wfc_causal_governance_unique_normal_forms :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (GovernanceCausal.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (GovernanceCausal.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    forall c n1 n2,
      star (GovernanceCausal.step event_eq_dec apply rho valid enabled) c n1 ->
      normal_form (GovernanceCausal.step event_eq_dec apply rho valid enabled) n1 ->
      star (GovernanceCausal.step event_eq_dec apply rho valid enabled) c n2 ->
      normal_form (GovernanceCausal.step event_eq_dec apply rho valid enabled) n2 -> n1 = n2.
  Proof.
    intros enabled cc1 cc2 ear eac c n1 n2 S1 N1 S2 N2.
    eapply unique_normal_forms; try eassumption. apply wfc_causal_governance_confluent; assumption.
  Qed.

  (* Base cor:unique-nf in the paper's own terms: rho* is Def. "Iterated Compensation", enabledness
     is Def. "Configuration" (deps disjoint from the buffer), CC1 is required only for distinct,
     causally independent, simultaneously enabled events. Hypotheses: WFC, CC1, CC2. *)
  Theorem paper_causal_governance_confluent :
    forall deps : Event -> list Event,
    (forall sigma B e1 e2,
       deps_enabled deps e1 sigma B -> deps_enabled deps e2 sigma B -> e1 <> e2 ->
       ~ In e1 (deps e2) -> ~ In e2 (deps e1) ->
       N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    confluent (GovernanceCausal.step event_eq_dec apply rho valid (deps_enabled deps)).
  Proof.
    intros deps cc1 cc2. apply wfc_causal_governance_confluent.
    - intros sigma B e1 e2 H1 H2 Hne.
      destruct (deps_coenabled_independent deps sigma B e1 e2 H1 H2) as [I1 I2].
      apply (cc1 sigma B); assumption.
    - exact cc2.
    - intros sigma B e1 e2 H1 H2 Hne.
      exact (deps_causal_enabled_after_remove event_eq_dec deps apply N sigma B e1 e2 H1 H2 Hne).
    - exact (deps_causal_enabled_after_comp deps rho).
  Qed.

  Theorem paper_causal_governance_unique_normal_forms :
    forall deps : Event -> list Event,
    (forall sigma B e1 e2,
       deps_enabled deps e1 sigma B -> deps_enabled deps e2 sigma B -> e1 <> e2 ->
       ~ In e1 (deps e2) -> ~ In e2 (deps e1) ->
       N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    forall c n1 n2,
      star (GovernanceCausal.step event_eq_dec apply rho valid (deps_enabled deps)) c n1 ->
      normal_form (GovernanceCausal.step event_eq_dec apply rho valid (deps_enabled deps)) n1 ->
      star (GovernanceCausal.step event_eq_dec apply rho valid (deps_enabled deps)) c n2 ->
      normal_form (GovernanceCausal.step event_eq_dec apply rho valid (deps_enabled deps)) n2 ->
      n1 = n2.
  Proof.
    intros deps cc1 cc2 c n1 n2 S1 N1 S2 N2.
    eapply unique_normal_forms; try eassumption. apply paper_causal_governance_confluent; assumption.
  Qed.

  (* The all-pairs CC1 system (Governance.v) with deps-based enabledness. *)
  Theorem paper_governance_confluent :
    forall deps : Event -> list Event,
    (forall sigma e1 e2, N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    confluent (Governance.step event_eq_dec apply rho valid (deps_enabled deps)).
  Proof.
    intros deps cc1 cc2. apply wfc_governance_confluent; try assumption.
    - intros sigma B e1 e2 H1 H2 Hne.
      exact (deps_enabled_after_remove event_eq_dec deps apply N sigma B e1 e2 H1 H2 Hne).
    - exact (deps_enabled_after_comp deps rho).
  Qed.

  Theorem paper_governance_unique_normal_forms :
    forall deps : Event -> list Event,
    (forall sigma e1 e2, N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    forall c n1 n2,
      star (Governance.step event_eq_dec apply rho valid (deps_enabled deps)) c n1 ->
      normal_form (Governance.step event_eq_dec apply rho valid (deps_enabled deps)) n1 ->
      star (Governance.step event_eq_dec apply rho valid (deps_enabled deps)) c n2 ->
      normal_form (Governance.step event_eq_dec apply rho valid (deps_enabled deps)) n2 ->
      n1 = n2.
  Proof.
    intros deps cc1 cc2 c n1 n2 S1 N1 S2 N2.
    eapply unique_normal_forms; try eassumption. apply paper_governance_confluent; assumption.
  Qed.

  (* GovernanceConverse.v's cc_exact_from with rho* constructed: both rho_star_reach and
     rho_star_valid are discharged. *)
  Theorem wfc_cc_exact_from : forall s0,
    (forall B, UN (Governance.step event_eq_dec apply rho valid free_enabled) (s0, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        N (apply e sigma) = N (apply e (rho sigma)))).
  Proof.
    exact (cc_exact_from event_eq_dec apply rho N valid Phi wfc (rs_reach_gov free_enabled)
             (rho_star_valid rho valid valid_dec Phi wfc)).
  Qed.
End Headline.

(* GovernanceWF.v's theorems (WFC over any well-founded order) with rho* constructed. *)
Section HeadlineWF.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s).

  Local Notation N := (rho_star_wf rho valid valid_dec P ltP wf_ltP Phi wfc_wf).

  Theorem wfc_governance_wf_confluent :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma e1 e2, N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (Governance.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (Governance.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    confluent (Governance.step event_eq_dec apply rho valid enabled).
  Proof.
    intros enabled cc1 cc2 ear eac.
    apply (governance_wf_confluent event_eq_dec apply rho N valid enabled P ltP wf_ltP Phi wfc_wf);
      try assumption.
    intros s B. apply crel_reach_gov. apply rho_star_wf_crel.
  Qed.

  Theorem wfc_causal_governance_wf_confluent :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) ->
    (forall sigma e, ~ valid sigma -> N (apply e sigma) = N (apply e (rho sigma))) ->
    (forall sigma B e1 e2, enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       In e2 (GovernanceCausal.remove1 event_eq_dec e1 B) /\
       enabled e2 (N (apply e1 sigma)) (GovernanceCausal.remove1 event_eq_dec e1 B)) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    confluent (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Proof.
    intros enabled cc1 cc2 ear eac.
    apply (causal_governance_wf_confluent event_eq_dec apply rho N valid enabled P ltP wf_ltP Phi
             wfc_wf); try assumption.
    intros s B. apply crel_reach_causal. apply rho_star_wf_crel.
  Qed.
End HeadlineWF.

(* ============================================================================================ *)
(* 10. Non-vacuity                                                                              *)
(* ============================================================================================ *)

(* A four-level saturating counter. States L0..L3; L3 (overflow) is invalid and repairs to L2.
   Events are nat amounts added with saturation at L3. WFC with Phi(L3) = 1, else 0; UBC with
   M = 1; finite; rho* caps at L2. Every hypothesis set of this file is discharged for it, with
   deps-based enabledness for an arbitrary dependency map. *)
Inductive lv := L0 | L1 | L2 | L3.

Definition lv_toN (s : lv) : nat := match s with L0 => 0 | L1 => 1 | L2 => 2 | L3 => 3 end.
Definition lv_ofN (n : nat) : lv :=
  match n with 0 => L0 | 1 => L1 | 2 => L2 | _ => L3 end.
Definition lv_apply (n : nat) (s : lv) : lv := lv_ofN (lv_toN s + n).
Definition lv_rho (s : lv) : lv := match s with L3 => L2 | x => x end.
Definition lv_valid (s : lv) : Prop := s <> L3.
Definition lv_valid_dec (s : lv) : {lv_valid s} + {~ lv_valid s}.
Proof.
  destruct s; [left; discriminate | left; discriminate | left; discriminate |].
  right. intro H. apply H. reflexivity.
Defined.
Definition lv_Phi (s : lv) : nat := match s with L3 => 1 | _ => 0 end.

Lemma lv_wfc : forall s, ~ lv_valid s -> lv_Phi (lv_rho s) < lv_Phi s.
Proof. intros [] H; simpl; try lia; exfalso; apply H; discriminate. Qed.

Lemma lv_finite : forall s, In s [L0; L1; L2; L3].
Proof. intros []; simpl; tauto. Qed.

Theorem lv_ubc : exists M, (forall s, lv_Phi s <= M) /\ (forall s0 : lv, exists s, lv_Phi s = M).
Proof. exact (base_lem_finite_implies_ubc lv_rho lv_valid lv_Phi _ lv_finite lv_wfc). Qed.

Lemma lv_Phi_le_1 : forall s, lv_Phi s <= 1.
Proof. intros []; simpl; lia. Qed.

Local Notation lvN := (rho_star lv_rho lv_valid lv_valid_dec lv_Phi).

Lemma lv_N_ofN : forall n, lvN (lv_ofN n) = lv_ofN (Nat.min n 2).
Proof. intros [| [| [| n]]]; reflexivity. Qed.

Lemma lv_toN_ofN_min : forall n, lv_toN (lv_ofN (Nat.min n 2)) = Nat.min n 2.
Proof. intros [| [| [| n]]]; reflexivity. Qed.

Lemma lv_N_apply : forall n s, lvN (lv_apply n s) = lv_ofN (Nat.min (lv_toN s + n) 2).
Proof. intros n s. unfold lv_apply. apply lv_N_ofN. Qed.

Lemma lv_cc1 : forall s e1 e2,
  lvN (lv_apply e2 (lvN (lv_apply e1 s))) = lvN (lv_apply e1 (lvN (lv_apply e2 s))).
Proof.
  intros s e1 e2. rewrite !lv_N_apply, !lv_toN_ofN_min. f_equal. lia.
Qed.

Lemma lv_cc2 : forall s e, ~ lv_valid s -> lvN (lv_apply e s) = lvN (lv_apply e (lv_rho s)).
Proof.
  intros [] e H; try (exfalso; apply H; discriminate).
  rewrite !lv_N_apply. f_equal. simpl lv_toN. lia.
Qed.

(* Strong absorption holds for the instance (so base_thm_strong_absorption's premise is met). *)
Theorem lv_strong_absorption : forall e s, lvN (lv_apply e s) = lvN (lv_apply e (lvN s)).
Proof.
  intros e s. apply (base_rem_absorption lv_apply lv_rho lv_valid lv_valid_dec lv_Phi lv_wfc).
  exact lv_cc2.
Qed.

Theorem lv_rho_star_caps : forall s, lvN s = lv_ofN (Nat.min (lv_toN s) 2).
Proof. intros []; reflexivity. Qed.

(* Base cor:unique-nf in the paper's terms, discharged: deps-based enabledness (any deps map),
   constructed rho*, WFC, CC1, CC2. *)
Theorem lv_paper_confluent : forall deps : nat -> list nat,
  confluent (GovernanceCausal.step Nat.eq_dec lv_apply lv_rho lv_valid (deps_enabled deps)).
Proof.
  intro deps. apply (paper_causal_governance_confluent Nat.eq_dec lv_apply lv_rho lv_valid
                       lv_valid_dec lv_Phi lv_wfc deps).
  - intros sigma B e1 e2 _ _ _ _ _. apply lv_cc1.
  - exact lv_cc2.
Qed.

Theorem lv_paper_governance_confluent : forall deps : nat -> list nat,
  confluent (Governance.step Nat.eq_dec lv_apply lv_rho lv_valid (deps_enabled deps)).
Proof.
  intro deps. exact (paper_governance_confluent Nat.eq_dec lv_apply lv_rho lv_valid lv_valid_dec
                       lv_Phi lv_wfc deps lv_cc1 lv_cc2).
Qed.

(* The UBC step bound instantiated (M = 1): every reduction from (s, E) has <= |E| + (|E|+1) steps. *)
Theorem lv_termination_bound : forall deps s E n d,
  nstar (Governance.step Nat.eq_dec lv_apply lv_rho lv_valid (deps_enabled deps)) n (s, E) d ->
  n <= length E + (length E + 1) * 1.
Proof.
  intros deps. exact (base_lem_termination_bound Nat.eq_dec lv_apply lv_rho lv_valid lv_Phi
                        (deps_enabled deps) lv_wfc 1 lv_Phi_le_1).
Qed.

(* The bound is attained: from (L3, [1]) the run compensate, apply 1, compensate has
   3 = |E| + (|E| + 1) * M steps. *)
Theorem lv_termination_bound_tight :
  nstar (Governance.step Nat.eq_dec lv_apply lv_rho lv_valid (deps_enabled (fun _ => [])))
    3 (L3, [1]) (L2, []).
Proof.
  eapply ns_step; [apply Governance.st_comp; intro H; apply H; reflexivity |]. simpl.
  eapply ns_step.
  { apply (Governance.st_apply Nat.eq_dec lv_apply lv_rho lv_valid (deps_enabled (fun _ => []))
             L2 [1] 1); [left; reflexivity | split; [left; reflexivity | intros d []]]. }
  simpl. eapply ns_step; [apply Governance.st_comp; intro H; apply H; reflexivity |].
  apply ns_refl.
Qed.

(* Base def:rhostar for the instance: m = 1 compensation step from L3. *)
Theorem lv_def_rhostar : lvN L3 = iterN lv_rho 1 L3 /\ lv_valid (iterN lv_rho 1 L3) /\
                         ~ lv_valid (iterN lv_rho 0 L3).
Proof.
  split; [reflexivity |]. split; [simpl; discriminate |]. simpl. intro H. apply H. reflexivity.
Qed.

(* The unbounded withdrawal registry of GovernanceWF.v (State = Z, potential in Z under Zwf 0):
   its rho* is now constructed, equals the hand-written zw_rho_star, and its confluence follows
   with no rho* hypothesis. *)
From Coq Require Import ZArith Zwf.
Open Scope Z_scope.

Definition zw_valid_dec (s : Z) : {zw_valid s} + {~ zw_valid s} := Z_le_dec 0 s.

Lemma zw_crel : forall s, crel zw_rho zw_valid s (zw_rho_star s).
Proof.
  assert (H : forall (n : nat) s, Z.to_nat (- s) = n -> crel zw_rho zw_valid s (zw_rho_star s)).
  { induction n as [| n IH]; intros s Hn; unfold zw_rho_star.
    - replace (Z.max s 0) with s by lia. constructor. unfold zw_valid. lia.
    - destruct (Z_le_gt_dec 0 s) as [Hv | Hinv].
      + replace (Z.max s 0) with s by lia. constructor. exact Hv.
      + constructor 2; [unfold zw_valid; lia |].
        replace (Z.max s 0) with (Z.max (zw_rho s) 0) by (unfold zw_rho; lia).
        apply IH. unfold zw_rho. lia. }
  intros s. apply (H (Z.to_nat (- s))). reflexivity.
Qed.

Theorem zw_rho_star_built : forall s,
  rho_star_wf zw_rho zw_valid zw_valid_dec Z (Zwf 0) (Zwf_well_founded 0) zw_Phi zw_wfc s
  = zw_rho_star s.
Proof.
  intro s. apply (crel_fun zw_rho zw_valid s); [apply rho_star_wf_crel | apply zw_crel].
Qed.

Theorem zw_confluent_built :
  confluent (Governance.step Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).
Proof.
  apply (wfc_governance_wf_confluent Nat.eq_dec zw_apply zw_rho zw_valid zw_valid_dec Z (Zwf 0)
           (Zwf_well_founded 0) zw_Phi zw_wfc zw_enabled); rewrite ?zw_rho_star_built.
  - intros. rewrite !zw_rho_star_built. apply zw_cc1.
  - intros. rewrite !zw_rho_star_built. apply zw_cc2. assumption.
  - intros. rewrite !zw_rho_star_built. apply zw_enabled_after_remove; assumption.
  - exact zw_enabled_after_comp.
Qed.

Close Scope Z_scope.
