(* PaperInstances.v: the concrete examples of the papers, mechanized exactly as given (ROADMAP
   item 7, work package WP2 of coq/PAPER-MAP.md). Axiom-free.

   Every example is stated on the paper's own data (states, invariants, compensation, events,
   morphisms) and every property the paper claims for it is a theorem here. Where the paper's
   text is wrong, the wrong claim is refuted by a theorem and the corrected claim is proved.

   Map from paper rows (PAPER-MAP.md) to theorems.

   B17, Base section 4 "Worked Example: Order Fulfillment" (Fed restates it):
     of_registry          rho fixes valid states and decreases Phi on invalid ones (Def. Registry),
                          WFC, UBC with M = 1, the only invalid states are (approved, 0), (approved, 1)
     of_valid_paper       the decided invariant is the paper's psi(s, b) = (s = approved -> b >= 2)
     of_rho_star_iterated rho* = rho is the iterated compensation of Def. "Iterated Compensation"
     of_cc1, of_cc2       CC1 for every pair of events at all 12 states, CC2 at every invalid state
     of_paper_traces      the two CC1 traces (from (pending, 0) and (pending, 1)) and the CC2 trace
     of_unique_normal_forms  every configuration has a unique normal form (Convergence Theorem)
     of_processors        P1 (approve, credit, credit) and P2 (credit, credit, approve) are runs of
                          the rewrite system ending in ((approved, 2), []), and every normal form
                          from the paper's stream is ((approved, 2), [])
     naive_registry       the naive revert rho(approved, b) = (pending, b) satisfies WFC and UBC
     naive_cc2_fails      it violates CC2 at (approved, 1) with credit (not stated in the paper)
     naive_paper_witness_fails  REFUTES the paper's witness: at (pending, 0) both orders of CC1 give
                          (pending, 1), so CC1 holds there
     naive_cc1_fails      the corrected witness: at (pending, 1) the two sides are (pending, 2) and
                          (approved, 2); hence the naive registry violates CC1 (the claim survives)
     naive_stream_diverges  the paper's own stream <approve, credit, credit> reaches the two normal
                          forms ((pending, 2), []) and ((approved, 2), []) under the naive revert

   B25, Base Thm. "Unbounded Compensation Depth Without UBC" (thm:necessity):
     ri_registry          R_infinity on Z: rho fixes 0, WFC with Phi = |s|, apply(e_n, 0) = -n
     ri_rho_star_iterated rho* = const 0 is the iterated compensation
     ri_depth             a reduction from (0, [e_n]) to normal form with exactly n compensation steps
     thm_necessity        for every M some reduction from (0, E) has more than M compensation steps
     ri_depth_exact       EVERY reduction from (0, [e_n]) to a normal form has exactly n of them
     ri_no_ubc            no WFC measure for R_infinity is bounded (UBC fails for every measure)
   B26, the remark "What Fails" after thm:necessity:
     ri_cc_any_extension  CC1 (all pairs, all states) and CC2 hold for EVERY total extension of
                          apply(e_n, -) (the paper defines it only at 0; rho* is constant)
     ri_what_fails        WFC, CC1, CC2 and unique normal forms hold, UBC fails

   B27, Base Prop. "Disagreement Without CC" (prop:cc-necessary):
     four_registry        rho fixes A, B; WFC; UBC with M = 1; rho* = rho is the iterated compensation
     four_paths           the paper's two paths: normal forms B (e1 first) and A (e2 first)
     prop_cc_necessary    two runs of the rewrite system from (A, [e1; e2]) reach the distinct valid
                          normal forms (B, []) and (A, []); CC1 fails at A

   F13, Fed Prop. "Necessity of Acyclicity" (prop:cycle-necessary):
     cycle_paper_trace    the paper's four repairs (0,0) -> (0,1) -> (1,1) -> (1,0) -> (0,0)
     prop_cycle_necessary components valid everywhere (WFC, CC vacuous), both morphisms satisfy M1,
                          federated compensation is deterministic, no state is federally valid,
                          and compensation never terminates from any state

   F14, Fed Prop. "Necessity of M1" (prop:m1-necessary):
     m1_paper_trace       (0,0) -> (0,1) -> (0,0) by morphism repair then local compensation
     prop_m1_necessary    acyclic, component WFC, M1 fails, no federally valid state, compensation
                          never terminates (it oscillates)
     m1_single_round_fails  one application of rho_Fed (phase 1, then phase 2) from (0,0) returns a
                          state that is not federally valid: Lemma "Single-Round Termination" needs M1

   F21, Fed remark "Necessity of the resolution conditions":
     r2_necessary         a two-source resolver satisfying R1 and violating R2 oscillates forever
     r1_necessary         a resolver violating R1 (reading the target's local component) and
                          satisfying R2, on an acyclic network with component WFC: the shared
                          normal form depends on how local compensation and resolution interleave

   F32, Fed section 6.x "Example: Manufacturer-Supplier Federation":
     ms_instance          Common (M1, locality, absorption, topological order), C1, C2, each
                          registry's own CC, the paper's M1 and the supplier's WFC
     ms_paper_traces      the paper's two traces, state by state
     ms_converges         every reordering of any event list converges (fed_permutations_converge)

   Conventions. Two-element sets {0, 1} of the federated examples are encoded as bool (0 = false,
   1 = true). Event buffers are lists (Governance.v); events have no causal dependencies in every
   example here (the papers give none), so enabledness is free_enabled (e is enabled iff e is in
   the buffer), which is the paper's deps-based enabledness with empty deps. *)

Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.FederationEvents NC.Trace.
From Coq Require Import List Arith Lia ZArith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.
Local Open Scope bool_scope.

(* ============================================================================================ *)
(* Shared tools                                                                                 *)
(* ============================================================================================ *)

Fixpoint iter {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with 0 => x | S k => f (iter f k x) end.

Lemma iter_S_inner : forall {A} (f : A -> A) n x, iter f (S n) x = iter f n (f x).
Proof.
  intros A f n. induction n as [| n IH]; intros x; [reflexivity |].
  change (iter f (S (S n)) x) with (f (iter f (S n) x)). rewrite IH. reflexivity.
Qed.

(* Def. "Iterated Compensation": rs s = rho^m s for the least m with V(rho^m s). *)
Definition IsRhoStar {S : Type} (rho : S -> S) (valid : S -> Prop) (rs : S -> S) : Prop :=
  forall s, exists m, valid (iter rho m s) /\ (forall k, k < m -> ~ valid (iter rho k s)) /\
                      rs s = iter rho m s.

(* If rho fixes valid states and one step of rho always reaches validity, then rho* = rho. *)
Lemma rho_star_one_step : forall {S : Type} (rho : S -> S) (valid : S -> Prop),
  (forall s, valid s \/ ~ valid s) ->
  (forall s, valid s -> rho s = s) -> (forall s, valid (rho s)) -> IsRhoStar rho valid rho.
Proof.
  intros S rho valid Hdec Hfix Hone s. destruct (Hdec s) as [Hv | Hn].
  - exists 0. split; [exact Hv |]. split; [intros k Hk; lia |]. simpl. apply Hfix. exact Hv.
  - exists 1. split; [apply Hone |]. split; [| reflexivity].
    intros k Hk. assert (k = 0) by lia. subst k. exact Hn.
Qed.

(* A relation in which every element has a successor has no terminating element: compensation
   never terminates. *)
Lemma no_SN_of_total : forall {A : Type} (R : A -> A -> Prop),
  (forall x, exists y, R x y) -> forall x, ~ SN R x.
Proof.
  intros A R Ht x H. unfold SN in H. induction H as [x _ IH].
  destruct (Ht x) as [y Hy]. exact (IH y Hy).
Qed.

(* Reduction sequences with their number of compensation steps (Thm. "Unbounded Compensation
   Depth" counts them). *)
Section Counted.
  Context {State Event : Type}.
  Variable eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho : State -> State.
  Variable valid : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.

  Inductive cred : State * list Event -> State * list Event -> nat -> Prop :=
  | cr_refl : forall c, cred c c 0
  | cr_apply : forall s B e d k, In e B -> enabled e s B ->
      cred (apply e s, remove1 eq_dec e B) d k -> cred (s, B) d k
  | cr_comp : forall s B d k, ~ valid s -> cred (rho s, B) d k -> cred (s, B) d (S k).

  Lemma cred_star : forall c d k, cred c d k -> star (step eq_dec apply rho valid enabled) c d.
  Proof.
    intros c d k H. induction H as [c | s B e d k Hin Hen _ IH | s B d k Hinv _ IH].
    - apply star_refl.
    - eapply star_step; [apply st_apply; eassumption | exact IH].
    - eapply star_step; [apply st_comp; exact Hinv | exact IH].
  Qed.

  (* Every reduction sequence has a compensation count. *)
  Lemma star_cred : forall c d, star (step eq_dec apply rho valid enabled) c d -> exists k, cred c d k.
  Proof.
    intros c d H. induction H as [c | c y d Hs _ [k IH]]; [exists 0; apply cr_refl |].
    destruct Hs as [s B e Hin Hen | s B Hinv].
    - exists k. eapply cr_apply; eassumption.
    - exists (S k). apply cr_comp; assumption.
  Qed.
End Counted.

(* ============================================================================================ *)
(* B17. Order fulfillment (Base section 4).                                                     *)
(* ============================================================================================ *)

Inductive stage : Type := Pending | Approved | Held.
Inductive bal : Type := B0 | B1 | B2 | B3.

Definition bnat (b : bal) : nat := match b with B0 => 0 | B1 => 1 | B2 => 2 | B3 => 3 end.

(* min(b + 1, 3) *)
Definition bsucc (b : bal) : bal := match b with B0 => B1 | B1 => B2 | B2 => B3 | B3 => B3 end.

Lemma bsucc_nat : forall b, bnat (bsucc b) = Nat.min (bnat b + 1) 3.
Proof. intros []; reflexivity. Qed.

Definition low (b : bal) : bool := match b with B0 | B1 => true | _ => false end.

Lemma low_nat : forall b, low b = true <-> bnat b < 2.
Proof. intros []; simpl; split; intro H; try reflexivity; try discriminate; lia. Qed.

Definition of_state : Type := (stage * bal)%type.

Definition is_approved (s : stage) : bool := match s with Approved => true | _ => false end.
Definition is_held (s : stage) : bool := match s with Held => true | _ => false end.

(* psi(s, b) = (s = approved -> b >= 2), decided. *)
Definition of_validb (x : of_state) : bool := negb (is_approved (fst x) && low (snd x)).
Definition of_valid (x : of_state) : Prop := of_validb x = true.

Lemma of_valid_paper : forall s b, of_valid (s, b) <-> (s = Approved -> 2 <= bnat b).
Proof.
  intros s b; destruct s, b; unfold of_valid; simpl; split; intro H;
    first [ reflexivity | discriminate | (intros E; discriminate E) | (intros _; lia)
          | (exfalso; specialize (H eq_refl); lia) ].
Qed.

(* rho(approved, b) = (held, b) for b < 2; identity elsewhere. *)
Definition of_rho (x : of_state) : of_state :=
  match x with (Approved, b) => if low b then (Held, b) else x | _ => x end.

Definition of_rho_star : of_state -> of_state := of_rho.

Definition of_Phi (x : of_state) : nat := if is_approved (fst x) && low (snd x) then 1 else 0.

Inductive oev : Type := Credit | Approve.

Definition oev_eq_dec : forall a b : oev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition of_apply (e : oev) (x : of_state) : of_state :=
  match e with
  | Credit => let b' := bsucc (snd x) in
              if is_held (fst x) && negb (low b') then (Approved, b') else (fst x, b')
  | Approve => (Approved, snd x)
  end.

Definition of_gov (e : oev) (x : of_state) : of_state := of_rho_star (of_apply e x).

Definition of_step := step oev_eq_dec of_apply of_rho of_valid free_enabled.

Theorem of_registry :
  (forall x, of_valid x -> of_rho x = x) /\
  (forall x, ~ of_valid x -> of_Phi (of_rho x) < of_Phi x) /\
  (forall x, of_Phi x <= 1) /\
  (forall x, ~ of_valid x <-> x = (Approved, B0) \/ x = (Approved, B1)).
Proof.
  unfold of_valid. split; [| split; [| split]].
  - intros [[] []] H; simpl in *; try reflexivity; discriminate.
  - intros [[] []] H; compute in *; try (exfalso; apply H; reflexivity); lia.
  - intros [[] []]; compute; lia.
  - intros [[] []]; simpl; split; intro H;
      try (left; reflexivity); try (right; reflexivity);
      try (exfalso; apply H; reflexivity);
      try (destruct H as [E | E]; discriminate E);
      discriminate.
Qed.

Lemma of_valid_dec : forall x, of_valid x \/ ~ of_valid x.
Proof. intros x. unfold of_valid. destruct (of_validb x); [left | right]; congruence. Qed.

Theorem of_rho_star_iterated : IsRhoStar of_rho of_valid of_rho_star.
Proof.
  apply rho_star_one_step.
  - exact of_valid_dec.
  - exact (proj1 of_registry).
  - intros [[] []]; reflexivity.
Qed.

Lemma of_rho_star_valid : forall x, of_valid (of_rho_star x).
Proof. intros [[] []]; reflexivity. Qed.

Lemma of_rho_star_reach : forall x B, star of_step (x, B) (of_rho_star x, B).
Proof.
  intros x B. unfold of_rho_star. destruct (of_valid_dec x) as [Hv | Hn].
  - rewrite (proj1 of_registry x Hv). apply star_refl.
  - apply star_one. apply st_comp. exact Hn.
Qed.

(* CC1 for EVERY pair of events at EVERY one of the 12 states (the paper checks valid states). *)
Theorem of_cc1 : forall x e1 e2, of_gov e2 (of_gov e1 x) = of_gov e1 (of_gov e2 x).
Proof. intros [[] []] [] []; reflexivity. Qed.

Theorem of_cc2 : forall x e, ~ of_valid x -> of_gov e x = of_gov e (of_rho x).
Proof. intros [[] []] [] H; try reflexivity; exfalso; apply H; reflexivity. Qed.

(* The paper's displayed traces, state by state. *)
Theorem of_paper_traces :
  (* CC1 from (pending, 0), path 1 and path 2 *)
  (of_apply Approve (Pending, B0) = (Approved, B0) /\ of_rho_star (Approved, B0) = (Held, B0) /\
   of_apply Credit (Held, B0) = (Held, B1) /\
   of_apply Credit (Pending, B0) = (Pending, B1) /\ of_apply Approve (Pending, B1) = (Approved, B1) /\
   of_rho_star (Approved, B1) = (Held, B1) /\
   of_gov Credit (of_gov Approve (Pending, B0)) = (Held, B1) /\
   of_gov Approve (of_gov Credit (Pending, B0)) = (Held, B1)) /\
  (* CC1 from (pending, 1) *)
  (of_apply Credit (Held, B1) = (Approved, B2) /\ of_apply Credit (Pending, B1) = (Pending, B2) /\
   of_apply Approve (Pending, B2) = (Approved, B2) /\
   of_gov Credit (of_gov Approve (Pending, B1)) = (Approved, B2) /\
   of_gov Approve (of_gov Credit (Pending, B1)) = (Approved, B2)) /\
  (* CC2 from (approved, 0) with credit *)
  (of_rho_star (of_apply Credit (Approved, B0)) = (Held, B1) /\
   of_rho (Approved, B0) = (Held, B0) /\
   of_rho_star (of_apply Credit (of_rho (Approved, B0))) = (Held, B1)).
Proof. repeat split. Qed.

(* Convergence Theorem on the example: every configuration has a unique normal form. *)
Theorem of_unique_normal_forms : forall x B, UN of_step (x, B).
Proof.
  apply (proj2 (cc_exact_global oev_eq_dec of_apply of_rho of_rho_star of_valid of_Phi
                  (proj1 (proj2 of_registry)) of_rho_star_reach of_rho_star_valid)).
  split; [exact of_cc1 | exact of_cc2].
Qed.

Ltac app_step e := eapply star_step; [apply (st_apply _ _ _ _ _ _ _ e); simpl; tauto | cbn].
Ltac comp_step := eapply star_step; [apply st_comp; unfold of_valid; simpl; discriminate | cbn].

Definition of_stream : list oev := [Approve; Credit; Credit].

(* Processors P1 (approve, credit, credit) and P2 (credit, credit, approve), as runs of the
   governance rewrite system; both end in the normal form ((approved, 2), []), and so does every
   run of the paper's stream. *)
Theorem of_processors :
  star of_step ((Pending, B0), of_stream) ((Approved, B2), []) /\
  star of_step ((Pending, B0), of_stream) ((Approved, B2), []) /\
  normal_form of_step ((Approved, B2), []) /\
  (fold_left (fun x e => of_gov e x) [Approve; Credit; Credit] (Pending, B0) = (Approved, B2)) /\
  (fold_left (fun x e => of_gov e x) [Credit; Credit; Approve] (Pending, B0) = (Approved, B2)) /\
  (forall n, star of_step ((Pending, B0), of_stream) n -> normal_form of_step n ->
     n = ((Approved, B2), [])).
Proof.
  assert (P1 : star of_step ((Pending, B0), of_stream) ((Approved, B2), [])).
  { unfold of_stream.
    app_step Approve. comp_step. app_step Credit. app_step Credit. apply star_refl. }
  assert (P2 : star of_step ((Pending, B0), of_stream) ((Approved, B2), [])).
  { unfold of_stream.
    app_step Credit. app_step Credit. app_step Approve. apply star_refl. }
  assert (NF : normal_form of_step ((Approved, B2), [])).
  { apply nf_valid_empty. reflexivity. }
  split; [exact P1 |]. split; [exact P2 |]. split; [exact NF |].
  split; [reflexivity |]. split; [reflexivity |].
  intros n Sn Nn. exact (of_unique_normal_forms _ _ n _ Sn Nn P1 NF).
Qed.

(* ----- the naive revert rho(approved, b) = (pending, b) ----- *)

Definition nv_rho (x : of_state) : of_state :=
  match x with (Approved, b) => if low b then (Pending, b) else x | _ => x end.

Definition nv_gov (e : oev) (x : of_state) : of_state := nv_rho (of_apply e x).

Definition nv_step := step oev_eq_dec of_apply nv_rho of_valid free_enabled.

Theorem naive_registry :
  (forall x, of_valid x -> nv_rho x = x) /\
  (forall x, ~ of_valid x -> of_Phi (nv_rho x) < of_Phi x) /\
  (forall x, of_Phi x <= 1) /\
  IsRhoStar nv_rho of_valid nv_rho.
Proof.
  unfold of_valid. split; [| split; [| split]].
  - intros [[] []] H; simpl in *; try reflexivity; discriminate.
  - intros [[] []] H; compute in *; try (exfalso; apply H; reflexivity); lia.
  - intros [[] []]; compute; lia.
  - apply rho_star_one_step.
    + exact of_valid_dec.
    + intros [[] []] H; unfold of_valid in H; simpl in *; try reflexivity; discriminate.
    + intros [[] []]; reflexivity.
Qed.

(* The naive revert also violates CC2: at (approved, 1), credit then repair gives (approved, 2),
   repair then credit gives (pending, 2). *)
Theorem naive_cc2_fails :
  ~ of_valid (Approved, B1) /\
  nv_gov Credit (Approved, B1) = (Approved, B2) /\
  nv_gov Credit (nv_rho (Approved, B1)) = (Pending, B2).
Proof. split; [discriminate | split; reflexivity]. Qed.

(* The paper's witness is wrong: at (pending, 0) the naive revert satisfies CC1. *)
Theorem naive_paper_witness_fails :
  nv_gov Credit (nv_gov Approve (Pending, B0)) = (Pending, B1) /\
  nv_gov Approve (nv_gov Credit (Pending, B0)) = (Pending, B1).
Proof. split; reflexivity. Qed.

(* The corrected witness: (pending, 1). The claim "the naive revert violates CC1" holds. *)
Theorem naive_cc1_fails :
  nv_gov Credit (nv_gov Approve (Pending, B1)) = (Pending, B2) /\
  nv_gov Approve (nv_gov Credit (Pending, B1)) = (Approved, B2) /\
  ~ (forall x e1 e2, nv_gov e2 (nv_gov e1 x) = nv_gov e1 (nv_gov e2 x)).
Proof.
  split; [reflexivity |]. split; [reflexivity |].
  intro H. specialize (H (Pending, B1) Approve Credit). discriminate H.
Qed.

(* Stronger: the paper's own stream diverges under the naive revert. *)
Theorem naive_stream_diverges :
  star nv_step ((Pending, B0), of_stream) ((Pending, B2), []) /\
  star nv_step ((Pending, B0), of_stream) ((Approved, B2), []) /\
  normal_form nv_step ((Pending, B2), []) /\ normal_form nv_step ((Approved, B2), []) /\
  ((Pending, B2), @nil oev) <> ((Approved, B2), []).
Proof.
  split.
  { unfold of_stream. app_step Approve. comp_step. app_step Credit. app_step Credit.
    apply star_refl. }
  split.
  { unfold of_stream. app_step Credit. app_step Credit. app_step Approve. apply star_refl. }
  split; [apply nf_valid_empty; reflexivity |].
  split; [apply nf_valid_empty; reflexivity |].
  discriminate.
Qed.

(* ============================================================================================ *)
(* B25, B26. R_infinity: unbounded compensation depth. Base thm:necessity and the remark after  *)
(* it ("What Fails").                                                                           *)
(* ============================================================================================ *)

Section RInfinity.
  Local Open Scope Z_scope.

  Definition ri_valid (s : Z) : Prop := s = 0.

  (* rho moves toward 0 (and fixes the valid state 0, as Def. Registry requires). *)
  Definition ri_rho (s : Z) : Z := if s <? 0 then s + 1 else if 0 <? s then s - 1 else s.

  (* The paper defines apply(e_n, -) only at 0, apply(e_n, 0) = -n. Any total extension works for
     every result below (ri_cc_any_extension); this one shifts by -n. *)
  Definition ri_apply (n : nat) (s : Z) : Z := s - Z.of_nat n.

  Definition ri_rho_star (_ : Z) : Z := 0.

  Definition ri_Phi (s : Z) : nat := Z.to_nat (Z.abs s).

  Definition ri_step := step Nat.eq_dec ri_apply ri_rho ri_valid free_enabled.
  Definition ri_cred := cred Nat.eq_dec ri_apply ri_rho ri_valid free_enabled.

  Lemma ri_Phi_rho : forall s, s <> 0 -> ri_Phi (ri_rho s) = Nat.pred (ri_Phi s).
  Proof.
    intros s H. unfold ri_Phi, ri_rho.
    destruct (Z.ltb_spec s 0); [| destruct (Z.ltb_spec 0 s)]; lia.
  Qed.

  Lemma ri_Phi_zero : forall s, ri_Phi s = 0%nat <-> s = 0.
  Proof. intros s. unfold ri_Phi. lia. Qed.

  Theorem ri_registry :
    (forall s, ri_valid s -> ri_rho s = s) /\
    (forall s, ~ ri_valid s -> (ri_Phi (ri_rho s) < ri_Phi s)%nat) /\
    (forall n, ri_apply n 0 = - Z.of_nat n).
  Proof.
    split; [| split].
    - intros s H. unfold ri_valid in H. subst s. reflexivity.
    - intros s H. unfold ri_valid in H. rewrite (ri_Phi_rho s H).
      assert (ri_Phi s <> 0%nat) by (rewrite ri_Phi_zero; exact H). lia.
    - intros n. unfold ri_apply. lia.
  Qed.

  Lemma ri_valid_dec : forall s, ri_valid s \/ ~ ri_valid s.
  Proof. intros s. unfold ri_valid. lia. Qed.

  Theorem ri_rho_star_iterated : IsRhoStar ri_rho ri_valid ri_rho_star.
  Proof.
    assert (H : forall m s, ri_Phi s = m ->
              ri_valid (iter ri_rho m s) /\ forall k, (k < m)%nat -> ~ ri_valid (iter ri_rho k s)).
    { induction m as [| m IH]; intros s Hs.
      - split; [apply ri_Phi_zero; exact Hs | intros k Hk; lia].
      - assert (Hn : s <> 0) by (intro E; subst s; discriminate Hs).
        assert (Hr : ri_Phi (ri_rho s) = m) by (rewrite (ri_Phi_rho s Hn); lia).
        destruct (IH (ri_rho s) Hr) as [Hv Hk].
        split; [rewrite iter_S_inner; exact Hv |].
        intros [| k] Hlt; [exact Hn |]. rewrite iter_S_inner. apply Hk. lia. }
    intros s. exists (ri_Phi s). destruct (H (ri_Phi s) s eq_refl) as [Hv Hk].
    split; [exact Hv |]. split; [exact Hk |]. unfold ri_valid in Hv. rewrite Hv. reflexivity.
  Qed.

  Lemma ri_rho_star_reach : forall s B, star ri_step (s, B) (ri_rho_star s, B).
  Proof.
    assert (H : forall m s B, ri_Phi s = m -> star ri_step (s, B) (0, B)).
    { induction m as [| m IH]; intros s B Hs.
      - apply ri_Phi_zero in Hs. subst s. apply star_refl.
      - assert (Hn : s <> 0) by (intro E; subst s; discriminate Hs).
        eapply star_step; [apply st_comp; exact Hn |].
        apply IH. rewrite (ri_Phi_rho s Hn). lia. }
    intros s B. exact (H _ s B eq_refl).
  Qed.

  Lemma ri_rm : forall n, remove1 Nat.eq_dec n [n] = [].
  Proof. intros n. simpl. destruct (Nat.eq_dec n n) as [_ | N]; [reflexivity | contradiction]. Qed.

  Lemma ri_chain : forall n, ri_cred (- Z.of_nat n, []) (0, []) n.
  Proof.
    induction n as [| n IH]; [apply cr_refl |].
    apply cr_comp; [unfold ri_valid; lia |].
    replace (ri_rho (- Z.of_nat (S n))) with (- Z.of_nat n) by (unfold ri_rho;
      destruct (Z.ltb_spec (- Z.of_nat (S n)) 0); [lia | lia]).
    exact IH.
  Qed.

  (* A reduction from (0, [e_n]) to normal form with exactly n compensation steps. *)
  Theorem ri_depth : forall n, ri_cred (0, [n]) (0, []) n /\ normal_form ri_step (0, []).
  Proof.
    intros n. split.
    - eapply cr_apply; [left; reflexivity | left; reflexivity |].
      rewrite ri_rm. replace (ri_apply n 0) with (- Z.of_nat n) by (unfold ri_apply; lia).
      apply ri_chain.
    - apply nf_valid_empty. reflexivity.
  Qed.

  (* thm:necessity, exactly: for every M there is a finite event set E and a reduction sequence
     from (sigma_0, E) = (0, E), ending in a normal form, with more than M compensation steps. *)
  Theorem thm_necessity : forall M : nat,
    exists E d k, ri_cred (0, E) d k /\ normal_form ri_step d /\ (M < k)%nat.
  Proof.
    intros M. exists [S M], (0, []), (S M). destruct (ri_depth (S M)) as [H1 H2].
    split; [exact H1 |]. split; [exact H2 | lia].
  Qed.

  Lemma ri_nf_valid : forall s B, normal_form ri_step (s, B) -> ri_valid s.
  Proof.
    intros s B H. destruct (ri_valid_dec s) as [Hv | Hn]; [exact Hv |].
    exfalso. apply H. eexists. apply st_comp. exact Hn.
  Qed.

  Lemma ri_tail : forall c d k, ri_cred c d k -> snd c = [] -> normal_form ri_step d ->
    k = ri_Phi (fst c).
  Proof.
    intros c d k H. induction H as [c | s B e d k Hin _ _ _ | s B d k Hinv _ IH];
      intros Hb Hnf; simpl in *.
    - destruct c as [s B]. simpl. apply ri_nf_valid in Hnf. unfold ri_valid in Hnf.
      subst s. reflexivity.
    - subst B. destruct Hin.
    - rewrite (IH Hb Hnf). rewrite (ri_Phi_rho s Hinv).
      assert (ri_Phi s <> 0%nat) by (rewrite ri_Phi_zero; exact Hinv). lia.
  Qed.

  (* Stronger than the paper: EVERY reduction from (0, [e_n]) to a normal form has exactly n
     compensation steps. *)
  Theorem ri_depth_exact : forall n d k, ri_cred (0, [n]) d k -> normal_form ri_step d -> k = n.
  Proof.
    intros n d k H Hnf. inversion H as [c E1 E2 E3 | s B e d' k' Hin Hen Hr E1 E2 E3 |
                                         s B d' k' Hinv Hr E1 E2 E3]; subst.
    - exfalso. apply Hnf. eexists. apply (st_apply _ _ _ _ _ _ _ n); left; reflexivity.
    - destruct Hin as [<- | []]. rewrite ri_rm in Hr.
      rewrite (ri_tail _ _ _ Hr eq_refl Hnf). simpl. unfold ri_apply, ri_Phi. lia.
    - exfalso. apply Hinv. reflexivity.
  Qed.

  (* UBC fails for EVERY WFC measure, not only for |s|. *)
  Definition ri_UBC : Prop :=
    exists (Phi : Z -> nat) (M : nat),
      (forall s, ~ ri_valid s -> (Phi (ri_rho s) < Phi s)%nat) /\ forall s, (Phi s <= M)%nat.

  Theorem ri_no_ubc : ~ ri_UBC.
  Proof.
    intros [Phi [M [Hw Hb]]].
    assert (H : forall n, (n <= Phi (- Z.of_nat n))%nat).
    { induction n as [| n IH]; [lia |].
      assert (Hn : ~ ri_valid (- Z.of_nat (S n))) by (unfold ri_valid; lia).
      pose proof (Hw _ Hn) as Hlt.
      replace (ri_rho (- Z.of_nat (S n))) with (- Z.of_nat n) in Hlt by (unfold ri_rho;
        destruct (Z.ltb_spec (- Z.of_nat (S n)) 0); [lia | lia]).
      lia. }
    specialize (H (S M)). specialize (Hb (- Z.of_nat (S M))). lia.
  Qed.

  (* B26: CC holds for EVERY total extension app of apply(e_n, -), at every state and for every
     pair of events (not only the one-event sets of the proof), because rho* is constant 0. *)
  Theorem ri_cc_any_extension : forall app : nat -> Z -> Z,
    (forall s e1 e2, ri_rho_star (app e2 (ri_rho_star (app e1 s))) =
                     ri_rho_star (app e1 (ri_rho_star (app e2 s)))) /\
    (forall s e, ~ ri_valid s -> ri_rho_star (app e s) = ri_rho_star (app e (ri_rho s))).
  Proof. intros app. split; reflexivity. Qed.

  (* The remark "What Fails": WFC, CC1, CC2 and unique normal forms hold; UBC fails. *)
  Theorem ri_what_fails :
    (forall s, ~ ri_valid s -> (ri_Phi (ri_rho s) < ri_Phi s)%nat) /\
    (forall s e1 e2, ri_rho_star (ri_apply e2 (ri_rho_star (ri_apply e1 s))) =
                     ri_rho_star (ri_apply e1 (ri_rho_star (ri_apply e2 s)))) /\
    (forall s e, ~ ri_valid s -> ri_rho_star (ri_apply e s) = ri_rho_star (ri_apply e (ri_rho s))) /\
    (forall s B, UN ri_step (s, B)) /\
    ~ ri_UBC.
  Proof.
    destruct (ri_cc_any_extension ri_apply) as [H1 H2].
    split; [exact (proj1 (proj2 ri_registry)) |].
    split; [exact H1 |]. split; [exact H2 |]. split; [| exact ri_no_ubc].
    apply (proj2 (cc_exact_global Nat.eq_dec ri_apply ri_rho ri_rho_star ri_valid ri_Phi
                    (proj1 (proj2 ri_registry)) ri_rho_star_reach (fun _ => eq_refl))).
    split; assumption.
  Qed.
End RInfinity.

(* ============================================================================================ *)
(* B27. The four-state CC counterexample (Base Prop. "Disagreement Without CC").                 *)
(* ============================================================================================ *)

Inductive four : Type := sA | sB | sC | sD.

Definition four_validb (x : four) : bool := match x with sA | sB => true | _ => false end.
Definition four_valid (x : four) : Prop := four_validb x = true.
Definition four_rho (x : four) : four := match x with sC => sA | sD => sB | _ => x end.
Definition four_Phi (x : four) : nat := match x with sC | sD => 1 | _ => 0 end.

Inductive fev : Type := ev1 | ev2.

Definition fev_eq_dec : forall a b : fev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* The paper's table: e1 = (C, C, C, D), e2 = (D, C, C, D) on (A, B, C, D). *)
Definition four_apply (e : fev) (x : four) : four :=
  match e, x with
  | ev1, sD => sD | ev1, _ => sC
  | ev2, sA => sD | ev2, sD => sD | ev2, _ => sC
  end.

Definition four_gov (e : fev) (x : four) : four := four_rho (four_apply e x).

Definition four_step := step fev_eq_dec four_apply four_rho four_valid free_enabled.

Theorem four_registry :
  (forall x, four_valid x -> four_rho x = x) /\
  (forall x, ~ four_valid x -> four_Phi (four_rho x) < four_Phi x) /\
  (forall x, four_Phi x <= 1) /\
  IsRhoStar four_rho four_valid four_rho.
Proof.
  unfold four_valid. split; [| split; [| split]].
  - intros [] H; simpl in *; try reflexivity; discriminate.
  - intros [] H; simpl in *; try (exfalso; apply H; reflexivity); lia.
  - intros []; simpl; lia.
  - apply rho_star_one_step.
    + intros x. destruct (four_validb x); [left | right]; congruence.
    + intros [] H; simpl in *; try reflexivity; discriminate.
    + intros []; reflexivity.
Qed.

(* The paper's two paths, state by state. *)
Theorem four_paths :
  four_apply ev1 sA = sC /\ four_rho sC = sA /\ four_apply ev2 sA = sD /\ four_rho sD = sB /\
  four_gov ev2 (four_gov ev1 sA) = sB /\
  four_apply ev1 sB = sC /\ four_gov ev1 (four_gov ev2 sA) = sA.
Proof. repeat split. Qed.

Ltac fapp e := eapply star_step; [apply (st_apply _ _ _ _ _ _ _ e); simpl; tauto | cbn].
Ltac fcomp := eapply star_step; [apply st_comp; unfold four_valid; simpl; discriminate | cbn].

Theorem prop_cc_necessary :
  star four_step (sA, [ev1; ev2]) (sB, []) /\ star four_step (sA, [ev1; ev2]) (sA, []) /\
  normal_form four_step (sB, []) /\ normal_form four_step (sA, []) /\
  four_valid sB /\ four_valid sA /\ sB <> sA /\
  four_gov ev2 (four_gov ev1 sA) <> four_gov ev1 (four_gov ev2 sA).
Proof.
  split. { fapp ev1. fcomp. fapp ev2. fcomp. apply star_refl. }
  split. { fapp ev2. fcomp. fapp ev1. fcomp. apply star_refl. }
  split; [apply nf_valid_empty; reflexivity |].
  split; [apply nf_valid_empty; reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; discriminate.
Qed.

(* ============================================================================================ *)
(* F13. The cyclic network (Fed Prop. "Necessity of Acyclicity").                               *)
(* R_A = R_B: {0, 1}, all valid, trivial compensation; phi_AB = flip, phi_BA = id.              *)
(* ============================================================================================ *)

Definition cyc_validA (_ : bool) : Prop := True.
Definition cyc_validB (_ : bool) : Prop := True.
Definition cyc_rhoA (x : bool) : bool := x.
Definition cyc_rhoB (x : bool) : bool := x.
Definition phiAB (a : bool) : bool := negb a.   (* flip: 1 - x *)
Definition phiBA (b : bool) : bool := b.        (* identity *)

(* Federated compensation: local compensation of an invalid component, or morphism repair of a
   violated morphism invariant (Def. "Federated Normalization Operator", repair steps). *)
Inductive cyc_rep : bool * bool -> bool * bool -> Prop :=
| cyc_locA : forall a b, ~ cyc_validA a -> cyc_rep (a, b) (cyc_rhoA a, b)
| cyc_locB : forall a b, ~ cyc_validB b -> cyc_rep (a, b) (a, cyc_rhoB b)
| cyc_rAB : forall a b, phiAB a <> b -> cyc_rep (a, b) (a, phiAB a)
| cyc_rBA : forall a b, phiBA b <> a -> cyc_rep (a, b) (phiBA b, b).

Definition cyc_fed_valid (x : bool * bool) : Prop :=
  cyc_validA (fst x) /\ cyc_validB (snd x) /\ phiAB (fst x) = snd x /\ phiBA (snd x) = fst x.

(* The paper's trace, with 0 = false and 1 = true. *)
Theorem cycle_paper_trace :
  cyc_rep (false, false) (false, true) /\ cyc_rep (false, true) (true, true) /\
  cyc_rep (true, true) (true, false) /\ cyc_rep (true, false) (false, false).
Proof.
  split; [apply (cyc_rAB false false); discriminate |].
  split; [apply (cyc_rBA false true); discriminate |].
  split; [apply (cyc_rAB true true); discriminate |].
  apply (cyc_rBA true false); discriminate.
Qed.

Lemma cyc_succ : forall x, exists y, cyc_rep x y.
Proof.
  intros [[] []].
  - exists (true, false). apply cyc_rAB. discriminate.
  - exists (false, false). apply cyc_rBA. discriminate.
  - exists (true, true). apply cyc_rBA. discriminate.
  - exists (false, true). apply cyc_rAB. discriminate.
Qed.

Theorem prop_cycle_necessary :
  (* components: every state valid, rho fixes valid states, WFC vacuous (measure 0) *)
  (forall x, cyc_validA x /\ cyc_rhoA x = x) /\ (forall x, cyc_validB x /\ cyc_rhoB x = x) /\
  (* M1 for both morphisms (total morphisms: the overwrite is the image) *)
  (forall a b, cyc_validA a -> cyc_validB b -> cyc_validB (phiAB a)) /\
  (forall b a, cyc_validB b -> cyc_validA a -> cyc_validA (phiBA b)) /\
  (* federated compensation is deterministic: the paper's cycle is the only behavior *)
  (forall x y z, cyc_rep x y -> cyc_rep x z -> y = z) /\
  (* no federally valid state, and compensation never terminates *)
  (forall x, ~ cyc_fed_valid x) /\
  (forall x, ~ SN cyc_rep x).
Proof.
  split; [intros; split; [exact I | reflexivity] |].
  split; [intros; split; [exact I | reflexivity] |].
  split; [intros; exact I |]. split; [intros; exact I |].
  split.
  { intros x y z H1 H2.
    destruct H1 as [a b H | a b H | a b H | a b H]; try (exfalso; apply H; exact I);
    inversion H2 as [a' b' H' | a' b' H' | a' b' H' | a' b' H']; subst;
      try (exfalso; apply H'; exact I); try reflexivity;
      destruct a, b; unfold phiAB, phiBA in *; simpl in *; congruence. }
  split.
  { intros [a b] [_ [_ [H1 H2]]]. unfold phiAB, phiBA in *; simpl in *. destruct a, b; simpl in *; congruence. }
  apply no_SN_of_total. exact cyc_succ.
Qed.

(* ============================================================================================ *)
(* F14. The M1 counterexample (Fed Prop. "Necessity of M1").                                    *)
(* R_A: {0}, trivial. R_B: {0, 1}, V_B(0), not V_B(1), rho_B(1) = 0. Total phi_AB(0) = 1.       *)
(* ============================================================================================ *)

Definition m1_validB (b : bool) : Prop := b = false.
Definition m1_rhoB (_ : bool) : bool := false.
Definition m1_PhiB (b : bool) : nat := if b then 1 else 0.
Definition m1_phi (_ : unit) : bool := true.

(* R_A's only state is valid, so its local compensation never fires; it is omitted. *)
Inductive m1_rep : unit * bool -> unit * bool -> Prop :=
| m1_morph : forall a b, m1_phi a <> b -> m1_rep (a, b) (a, m1_phi a)
| m1_locB : forall a b, ~ m1_validB b -> m1_rep (a, b) (a, m1_rhoB b).

Definition m1_fed_valid (x : unit * bool) : Prop := m1_validB (snd x) /\ m1_phi (fst x) = snd x.

(* One application of rho_Fed: phase 1 normalizes B locally, phase 2 repairs the edge. *)
Definition m1_rho_fed (x : unit * bool) : unit * bool :=
  let b1 := if snd x then m1_rhoB (snd x) else snd x in
  (fst x, if Bool.eqb (m1_phi (fst x)) b1 then b1 else m1_phi (fst x)).

Theorem m1_paper_trace :
  m1_rep (tt, false) (tt, true) /\ m1_rep (tt, true) (tt, false) /\ m1_rep (tt, false) (tt, true).
Proof.
  split; [apply (m1_morph tt false); discriminate |].
  split; [apply (m1_locB tt true); discriminate | apply (m1_morph tt false); discriminate].
Qed.

Lemma m1_succ : forall x, exists y, m1_rep x y.
Proof.
  intros [[] []].
  - exists (tt, false). apply m1_locB. discriminate.
  - exists (tt, true). apply m1_morph. discriminate.
Qed.

Theorem prop_m1_necessary :
  (* component B: rho fixes valid states, WFC *)
  (forall b, m1_validB b -> m1_rhoB b = b) /\
  (forall b, ~ m1_validB b -> m1_PhiB (m1_rhoB b) < m1_PhiB b) /\
  (* M1 fails *)
  ~ (forall a b, m1_validB b -> m1_validB (m1_phi a)) /\
  (* deterministic oscillation: no federally valid state, never terminates *)
  (forall x y z, m1_rep x y -> m1_rep x z -> y = z) /\
  (forall x, ~ m1_fed_valid x) /\
  (forall x, ~ SN m1_rep x).
Proof.
  split; [intros b H; unfold m1_validB in H; subst; reflexivity |].
  split; [intros [] H; simpl; [lia | exfalso; apply H; reflexivity] |].
  split; [intro H; specialize (H tt false eq_refl); discriminate H |].
  split.
  { intros x y z H1 H2.
    destruct H1 as [a b H | a b H]; inversion H2 as [a' b' H' | a' b' H']; subst; try reflexivity;
      destruct a, b; unfold m1_phi, m1_validB, m1_rhoB in *; congruence. }
  split; [intros [a b] [H1 H2]; unfold m1_validB, m1_phi in *; simpl in *; congruence |].
  apply no_SN_of_total. exact m1_succ.
Qed.

(* Lemma "Single-Round Termination" needs M1: one application of rho_Fed from the federally
   invalid (0, 0) returns (0, 1), which is not federally valid. *)
Theorem m1_single_round_fails :
  ~ m1_fed_valid (tt, false) /\ m1_rho_fed (tt, false) = (tt, true) /\ ~ m1_fed_valid (tt, true).
Proof.
  split; [intros [_ H]; discriminate H |]. split; [reflexivity |].
  intros [H _]. discriminate H.
Qed.

(* ============================================================================================ *)
(* F21. Necessity of the resolution conditions (Fed remark after thm:resolved-convergence).     *)
(* Resolvers are given as functions of the source states AND the target      *)
(* state, so that R1 (source determinacy) is a property, not a typing accident.                 *)
(* ============================================================================================ *)

(* R2: a resolver mapping valid sources to a shared value that violates V_B oscillates.
   Sources A1, A2: {0}, trivial. Target B: {0, 1} as in F14. Gamma(a1, a2, b) = 1. *)
Definition r2_gamma (_ _ : unit) (_ : bool) : bool := true.

Inductive r2_rep : unit * unit * bool -> unit * unit * bool -> Prop :=
| r2_res : forall a1 a2 b, r2_gamma a1 a2 b <> b -> r2_rep (a1, a2, b) (a1, a2, r2_gamma a1 a2 b)
| r2_locB : forall a1 a2 b, ~ m1_validB b -> r2_rep (a1, a2, b) (a1, a2, m1_rhoB b).

Definition r2_fed_valid (x : unit * unit * bool) : Prop :=
  match x with (a1, a2, b) => m1_validB b /\ r2_gamma a1 a2 b = b end.

Lemma r2_succ : forall x, exists y, r2_rep x y.
Proof.
  intros [[[] []] []].
  - exists (tt, tt, false). apply r2_locB. discriminate.
  - exists (tt, tt, true). apply r2_res. discriminate.
Qed.

Theorem r2_necessary :
  (* R1 holds: Gamma does not read the target *)
  (forall a1 a2 b b', r2_gamma a1 a2 b = r2_gamma a1 a2 b') /\
  (* R2 fails *)
  ~ (forall a1 a2 b, m1_validB b -> m1_validB (r2_gamma a1 a2 b)) /\
  (* resolution repair and local compensation oscillate *)
  r2_rep (tt, tt, false) (tt, tt, true) /\ r2_rep (tt, tt, true) (tt, tt, false) /\
  (forall x, ~ r2_fed_valid x) /\
  (forall x, ~ SN r2_rep x).
Proof.
  split; [reflexivity |].
  split; [intro H; specialize (H tt tt false eq_refl); discriminate H |].
  split; [apply r2_res; discriminate |].
  split; [apply r2_locB; discriminate |].
  split; [intros [[a1 a2] b] [H1 H2]; unfold m1_validB, r2_gamma in *; congruence |].
  apply no_SN_of_total. exact r2_succ.
Qed.

(* R1: a resolver that reads the target's local component, with R2 holding, on an acyclic
   network with component WFC: the shared normal form depends on the interleaving of local
   compensation and resolution repair. Target B: (sh, loc) in {0,1}^2, the only invalid state is
   (1, 0), rho_B(1, 0) = (1, 1). Gamma(a1, a2, (sh, loc)) = loc. *)
Definition r1_validb (x : bool * bool) : bool := negb (fst x && negb (snd x)).
Definition r1_valid (x : bool * bool) : Prop := r1_validb x = true.
Definition r1_rho (x : bool * bool) : bool * bool := if r1_validb x then x else (fst x, true).
Definition r1_Phi (x : bool * bool) : nat := if r1_validb x then 0 else 1.
Definition r1_gamma (_ _ : unit) (x : bool * bool) : bool := snd x.

Inductive r1_rep : unit * unit * (bool * bool) -> unit * unit * (bool * bool) -> Prop :=
| r1_res : forall a1 a2 x, r1_gamma a1 a2 x <> fst x ->
    r1_rep (a1, a2, x) (a1, a2, (r1_gamma a1 a2 x, snd x))
| r1_locB : forall a1 a2 x, ~ r1_valid x -> r1_rep (a1, a2, x) (a1, a2, r1_rho x).

Definition r1_fed_valid (y : unit * unit * (bool * bool)) : Prop :=
  match y with (a1, a2, x) => r1_valid x /\ r1_gamma a1 a2 x = fst x end.

Lemma r1_nf : forall y, r1_fed_valid y -> normal_form r1_rep y.
Proof.
  intros [[a1 a2] x] [Hv Hg] [z H]. inversion H; subst; [congruence | contradiction].
Qed.

Theorem r1_necessary :
  (* R1 fails: Gamma reads the target's local component *)
  ~ (forall a1 a2 x x', r1_gamma a1 a2 x = r1_gamma a1 a2 x') /\
  (* R2 holds: overwriting a valid target's shared component with Gamma keeps it valid *)
  (forall a1 a2 x, r1_valid x -> r1_valid (r1_gamma a1 a2 x, snd x)) /\
  (* component B: rho fixes valid states, WFC *)
  (forall x, r1_valid x -> r1_rho x = x) /\
  (forall x, ~ r1_valid x -> r1_Phi (r1_rho x) < r1_Phi x) /\
  (* from (1, 0): two federally valid normal forms with different shared components *)
  r1_rep (tt, tt, (true, false)) (tt, tt, (true, true)) /\
  r1_rep (tt, tt, (true, false)) (tt, tt, (false, false)) /\
  normal_form r1_rep (tt, tt, (true, true)) /\ normal_form r1_rep (tt, tt, (false, false)) /\
  r1_fed_valid (tt, tt, (true, true)) /\ r1_fed_valid (tt, tt, (false, false)).
Proof.
  split; [intro H; specialize (H tt tt (true, true) (true, false)); discriminate H |].
  split; [intros a1 a2 [[] []] H; reflexivity |].
  split; [intros x H; unfold r1_rho, r1_valid in *; rewrite H; reflexivity |].
  split; [intros x H; unfold r1_Phi, r1_rho, r1_valid in *; destruct (r1_validb x) eqn:E;
          [exfalso; apply H; reflexivity |]; destruct x as [s l]; unfold r1_validb in *; simpl in *;
          destruct s, l; simpl in *; try discriminate; lia |].
  assert (V1 : r1_fed_valid (tt, tt, (true, true))) by (split; reflexivity).
  assert (V2 : r1_fed_valid (tt, tt, (false, false))) by (split; reflexivity).
  split; [apply (r1_locB tt tt (true, false)); discriminate |].
  split; [apply (r1_res tt tt (true, false)); discriminate |].
  split; [apply r1_nf; exact V1 |]. split; [apply r1_nf; exact V2 |].
  split; assumption.
Qed.

(* ============================================================================================ *)
(* F32. The manufacturer-supplier federation (Fed section 6.x), in FederationEvents.v's model.  *)
(* Registry 0 is the manufacturer R_M, registry 1 the supplier R_S, o = [0; 1].                 *)
(* ============================================================================================ *)

Inductive ms : Type := Draft | Active | Suspended | Idle | Listed | Stale | Err.

Definition ms_validb (k : nat) (x : ms) : bool :=
  match k, x with
  | 0, (Draft | Active | Suspended) => true
  | 0, _ => false
  | 1, (Idle | Listed | Stale) => true
  | 1, _ => false
  | _, _ => true
  end.
Definition ms_valid (k : nat) (x : ms) : Prop := ms_validb k x = true.

(* The total morphism phi: draft -> idle, active -> listed, suspended -> stale. *)
Definition ms_phi (x : ms) : ms :=
  match x with Draft => Idle | Active => Listed | Suspended => Stale | _ => Idle end.

Definition ms_f (k : nat) (z : nat -> ms) (x : ms) : ms :=
  match k with 1 => ms_phi (z 0) | _ => x end.

Definition ms_rho (k : nat) (x : ms) : ms :=
  match k, x with 1, Err => Idle | _, _ => x end.

Definition ms_PhiS (x : ms) : nat := match x with Err => 1 | _ => 0 end.

(* The common value type ms carries both registries' states; Sigma_S is this part of it. *)
Definition ms_inS (x : ms) : bool := match x with Idle | Listed | Stale | Err => true | _ => false end.

Inductive msev : Type := Pub | Exp.

Definition ms_reg (e : msev) : nat := match e with Pub => 0 | Exp => 1 end.

Definition ms_raw (e : msev) (x : ms) : ms :=
  match e, x with Pub, Draft => Active | Pub, _ => x | Exp, _ => Stale end.

(* FedMachine.Apply's component step: the event, then the component normalizer. *)
Definition ms_sig (e : msev) (x : ms) : ms := ms_rho (ms_reg e) (ms_raw e x).

Definition ms_I (_ _ : msev) : Prop := True.

Definition ms_s0 (k : nat) : ms := match k with 0 => Draft | _ => Idle end.

Theorem ms_instance :
  Common ms src2 ms_f ms_valid ms_rho msev ms_reg ms_sig [0; 1] /\
  C1 ms ms_f ms_valid msev ms_reg ms_sig /\
  C2 ms ms_f ms_valid msev ms_reg ms_sig ms_I /\
  LocalCC ms ms_valid msev ms_reg ms_sig ms_I /\
  (* the paper's M1: every image of a valid manufacturer state is a valid supplier state *)
  (forall a b, ms_valid 0 a -> ms_valid 1 b -> ms_valid 1 (ms_phi a)) /\
  (* the supplier: rho_S fixes valid states, WFC *)
  (forall x, ms_valid 1 x -> ms_rho 1 x = x) /\
  (forall x, ms_inS x = true -> ~ ms_valid 1 x -> ms_PhiS (ms_rho 1 x) < ms_PhiS x) /\
  (* the start state is valid and morphism-consistent *)
  Inv ms ms_valid ms_s0 /\ Cons ms ms_f [0; 1] ms_s0.
Proof.
  unfold ms_valid. split.
  { constructor.
    - intros [| [| j]] z1 z2 x H; simpl; try reflexivity.
      rewrite (H 0); [reflexivity | left; reflexivity].
    - exact topo2.
    - intros [| [| j]] z x Hz Hx; simpl in *; trivial.
      pose proof (Hz 0) as H0. unfold ms_valid in H0. destruct (z 0); simpl in *; congruence.
    - intros [| [| j]] z z' x _ _ _; reflexivity.
    - intros [| [| j]] x Hx; [reflexivity | destruct x; simpl in *; congruence | reflexivity].
    - intros [] x Hx; destruct x; simpl in *; congruence.
    - intros []; simpl; tauto. }
  split. { intros [] z z' b _ _ _ _; reflexivity. }
  split. { intros [] [] z b E' _ _ _ _; simpl in E'; try discriminate; reflexivity. }
  split. { intros [] [] x E' _ _; simpl in E'; try discriminate; reflexivity. }
  split. { intros [] b Ha _; simpl in *; congruence. }
  split. { intros [] H; simpl in *; congruence. }
  split. { intros [] HS H; compute in *; try (exfalso; apply H; reflexivity); try discriminate; lia. }
  split. { intros [| [| k]]; reflexivity. }
  intros j [<- | [<- | []]]; reflexivity.
Qed.

Definition ms_ev := evstep ms msev ms_reg ms_sig.
Definition ms_applyF := applyF ms ms_f ms_rho msev ms_reg ms_sig [0; 1].
Definition ms_runF := runF ms ms_f ms_rho msev ms_reg ms_sig [0; 1].

(* The paper's two traces, as (manufacturer, supplier) pairs. *)
Theorem ms_paper_traces :
  (* Order 1: e_pub first *)
  (ms_ev Pub ms_s0 0, ms_ev Pub ms_s0 1) = (Active, Idle) /\
  (ms_applyF Pub ms_s0 0, ms_applyF Pub ms_s0 1) = (Active, Listed) /\
  (ms_ev Exp (ms_applyF Pub ms_s0) 0, ms_ev Exp (ms_applyF Pub ms_s0) 1) = (Active, Stale) /\
  (ms_runF [Pub; Exp] ms_s0 0, ms_runF [Pub; Exp] ms_s0 1) = (Active, Listed) /\
  (* Order 2: e_exp first *)
  (ms_ev Exp ms_s0 0, ms_ev Exp ms_s0 1) = (Draft, Stale) /\
  (ms_applyF Exp ms_s0 0, ms_applyF Exp ms_s0 1) = (Draft, Idle) /\
  (ms_ev Pub (ms_applyF Exp ms_s0) 0, ms_ev Pub (ms_applyF Exp ms_s0) 1) = (Active, Idle) /\
  (ms_runF [Exp; Pub] ms_s0 0, ms_runF [Exp; Pub] ms_s0 1) = (Active, Listed).
Proof. repeat split. Qed.

(* Every reordering of any event list converges, from every valid consistent state. *)
Theorem ms_converges :
  forall es1 es2 s, Permutation es1 es2 ->
    Inv ms ms_valid s -> Cons ms ms_f [0; 1] s -> feq ms (ms_runF es1 s) (ms_runF es2 s).
Proof.
  intros es1 es2 s Hp Hs Hc.
  destruct ms_instance as [Hcm [Hc1 [Hc2 _]]].
  apply (fed_permutations_converge _ _ _ _ _ _ _ _ ms_I _ Hcm Hc1 Hc2);
    [intros; exact I | exact Hp | exact Hs | exact Hc].
Qed.
