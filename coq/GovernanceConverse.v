(* GovernanceConverse.v: the converse of the single-registry Convergence Theorem and of causal
   convergence, in the strongest form that is true. Axiom-free.

   Governance.v and GovernanceCausal.v prove that WFC and CC (CC1, CC2) are SUFFICIENT for unique
   normal forms; CausalReplay.v proves that commutation of governed steps on concurrent pairs is
   sufficient for causal convergence. This file proves the matching converses and records exactly
   where the naive converse fails.

   Single registry (the Governance Rewrite System of Governance.v, reused verbatim).
   Write gov e s := rho_star (apply e s) for the governed step (apply, then repair).
   - newman_on: Newman's Lemma localized to a step-closed set of configurations, so CC only has to
     hold where a run can actually be.
   - jc_exact: for ANY enabledness (free, causal, guarded) and any start c0, the system is
     confluent from c0 IFF the joinability condition JC c0 holds: at every configuration reachable
     from c0, the governed successors of every critical pair are joinable. JC is CC "modulo the
     remaining buffer"; CC1/CC2 are the special case where the join is an equality.
   - cc_reach_unique_normal_forms: CC1 (co-enabled pairs) and CC2 on the states reachable from s0
     give unique normal forms from every configuration over a reachable state. This generalizes
     Governance.v and GovernanceCausal.v (CC needed only on reachable states).
   - cc1_runs, cc2_runs, cc1_fail_diverge, cc2_fail_diverge: under free delivery (every buffered
     event may fire) and canonical repair (rho_star returns a valid state), the two sides of CC1 at
     sigma are the normal forms of two runs from (sigma, [e1; e2]), and the two sides of CC2 at an
     invalid sigma are the normal forms of two runs from (sigma, [e]). A failure is a divergence.
   - reach_run, cc1_fail_diverge_from, cc2_fail_diverge_from: every reachable state is reached by a
     run from s0 (a word w delivered first), so a CC failure at a state reachable from s0 is a
     divergence of two event orders from (s0, w ++ [e1; e2]) (CC1) or (s0, w ++ [e]) (CC2).
   - cc_exact_from (the headline): free delivery, canonical repair, WFC. Every event buffer
     delivered from s0 has a unique normal form IFF CC1 and CC2 hold on the states reachable from
     s0. cc_exact: the same for every configuration over a reachable state. cc_exact_global: the
     same with every state reachable.
   Counterexamples to the naive converse:
   - rho_star_qualifier: with rho_star only a reduct (Governance.v's hypothesis rho_star_reach,
     which the identity satisfies), CC1 can fail while every configuration has a unique normal
     form. The converse needs rho_star to repair to validity.
   - masked_cc1: under causal enabledness, CC1 can fail for a co-enabled pair at a reachable
     configuration while every run from the start reaches the same normal form: a later reset
     event, enabled only after the pair, erases the difference. The exact condition there is JC,
     not CC1.

   Causal delivery (the run model of CausalReplay.v).
   - CCR s0: governed steps of a concurrent pair a, b commute at every state run p s0 after which
     the pair can be delivered (p ++ [a; b] is causally consistent).
   - ccr_convergence, ccr_diverge, causal_exact: causal convergence from s0 IFF CCR s0. A pair that
     can arrive in both orders after p and does not commute there gives two causally consistent
     permutations p ++ [a; b] and p ++ [b; a] that reach different states.
   - causal_convergence_exact: with hb irreflexive, causal convergence from every start IFF governed
     steps commute on every concurrent pair at every state. This is the converse of
     CausalReplay.causal_convergence; irreflexivity is needed (an event with hb a a never appears
     in a causal order, so its pairs never need to commute).
   - naive_causal_converse_fails: a concurrent pair that does not commute at a state reached by a
     causally consistent run, yet causal convergence holds: every run reaching that state contains
     an event causally after the pair. Reachability alone is not enough; the pair must be
     deliverable after the prefix. *)

Require Import NC.Newman NC.Governance NC.Trace NC.CausalReplay.
From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* ============================================================================================ *)
(* Newman's Lemma on a step-closed subset.                                                      *)
(* ============================================================================================ *)

Section ARSOn.
  Context {A : Type}.
  Variable R : A -> A -> Prop.
  Variable P : A -> Prop.
  Hypothesis P_closed : forall x y, P x -> R x y -> P y.

  Definition Ron (x y : A) : Prop := R x y /\ P x.

  Lemma star_closed : forall x y, P x -> star R x y -> P y.
  Proof.
    intros x y Hx S. induction S as [x | x y0 z Rxy _ IH]; [exact Hx |].
    apply IH. exact (P_closed x y0 Hx Rxy).
  Qed.

  Lemma star_Ron : forall x y, P x -> star R x y -> star Ron x y.
  Proof.
    intros x y Hx S. induction S as [x | x y0 z Rxy _ IH]; [apply star_refl |].
    eapply star_step; [split; [exact Rxy | exact Hx] |].
    apply IH. exact (P_closed x y0 Hx Rxy).
  Qed.

  Lemma star_of_Ron : forall x y, star Ron x y -> star R x y.
  Proof.
    intros x y S. induction S as [x | x y0 z [Rxy _] _ IH]; [apply star_refl |].
    eapply star_step; [exact Rxy | exact IH].
  Qed.

  Lemma SN_Ron : forall x, SN R x -> SN Ron x.
  Proof.
    intros x H. induction H as [x _ IH]. constructor. intros y [Rxy _]. apply IH. exact Rxy.
  Qed.

  (* Local confluence and termination only on P give confluence on P. *)
  Theorem newman_on :
    (forall x y z, P x -> R x y -> R x z -> joinable R y z) ->
    (forall x, P x -> SN R x) ->
    forall x, P x -> CR R x.
  Proof.
    intros LC HSN x Hx y z Sy Sz.
    assert (LC' : locally_confluent Ron).
    { intros u v w [Ruv Pu] [Ruw _].
      destruct (LC u v w Pu Ruv Ruw) as [m [Svm Swm]]. exists m. split.
      - apply star_Ron; [exact (P_closed u v Pu Ruv) | exact Svm].
      - apply star_Ron; [exact (P_closed u w Pu Ruw) | exact Swm]. }
    destruct (newman Ron LC' x (SN_Ron x (HSN x Hx)) y z (star_Ron x y Hx Sy) (star_Ron x z Hx Sz))
      as [m [Sym Szm]].
    exists m. split; apply star_of_Ron; assumption.
  Qed.
End ARSOn.

(* Unique normal forms from one point. *)
Definition UN {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
  forall n1 n2, star R x n1 -> normal_form R n1 -> star R x n2 -> normal_form R n2 -> n1 = n2.

Lemma CR_UN : forall {A : Type} (R : A -> A -> Prop) x, CR R x -> UN R x.
Proof.
  intros A R x H n1 n2 S1 N1 S2 N2. destruct (H n1 n2 S1 S2) as [w [A1 A2]].
  rewrite (star_from_nf R n1 w N1 A1), (star_from_nf R n2 w N2 A2). reflexivity.
Qed.

(* ============================================================================================ *)
(* Single registry: the exact joinability condition, and CC on reachable states.                *)
(* ============================================================================================ *)

Section Converse.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable Phi      : State -> nat.
  Variable enabled  : Event -> State -> list Event -> Prop.

  Local Notation gstep := (step event_eq_dec apply rho valid enabled).
  Local Notation rm := (remove1 event_eq_dec).

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star gstep (sigma, B) (rho_star sigma, B).
  Hypothesis enabled_after_comp : forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  (* States reachable from s0 by applying events and compensating invalid states. *)
  Inductive reach (s0 : State) : State -> Prop :=
  | r_init : reach s0 s0
  | r_apply : forall e s, reach s0 s -> reach s0 (apply e s)
  | r_comp : forall s, reach s0 s -> ~ valid s -> reach s0 (rho s).

  Lemma reach_step : forall s0 c d, reach s0 (fst c) -> gstep c d -> reach s0 (fst d).
  Proof.
    intros s0 c d Hc H. destruct H as [s B e _ _ | s B Hinv]; simpl in *.
    - apply r_apply. exact Hc.
    - apply r_comp; assumption.
  Qed.

  (* JC c0: at every configuration reachable from c0, the governed successors of each critical
     pair are joinable (CC1 and CC2 up to the rest of the run). *)
  Definition JC (c0 : State * list Event) : Prop :=
    forall sigma B, star gstep c0 (sigma, B) ->
      (forall e1 e2, In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
         joinable gstep (rho_star (apply e1 sigma), rm e1 B) (rho_star (apply e2 sigma), rm e2 B)) /\
      (forall e, ~ valid sigma -> In e B -> enabled e sigma B ->
         joinable gstep (rho_star (apply e sigma), rm e B) (rho_star (apply e (rho sigma)), rm e B)).

  Lemma apply_norm : forall sigma B e, In e B -> enabled e sigma B ->
    star gstep (apply e sigma, rm e B) (rho_star (apply e sigma), rm e B).
  Proof. intros. apply rho_star_reach. Qed.

  Lemma join_back : forall x x' y y', star gstep x x' -> star gstep y y' ->
    joinable gstep x' y' -> joinable gstep x y.
  Proof.
    intros x x' y y' Sx Sy [w [A1 A2]]. exists w.
    split; eapply star_trans; eassumption.
  Qed.

  (* Exactness, for any enabledness: confluence from c0 iff JC c0. *)
  Theorem jc_exact : forall c0, CR gstep c0 <-> JC c0.
  Proof.
    intros c0. split.
    - intros H sigma B Hr. split.
      + intros e1 e2 Hin1 Hin2 Hen1 Hen2 _. apply H.
        * eapply star_trans; [exact Hr |]. apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach);
            assumption.
        * eapply star_trans; [exact Hr |]. apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach);
            assumption.
      + intros e Hinv Hin Hen. apply H.
        * eapply star_trans; [exact Hr |]. apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach);
            assumption.
        * eapply star_trans; [exact Hr |]. eapply star_step; [apply st_comp; exact Hinv |].
          apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach);
            [exact Hin | apply enabled_after_comp; exact Hen].
    - intros HJ. apply (newman_on gstep (fun c => star gstep c0 c)).
      + intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
      + intros [sigma B] X1 X2 Hr H1 H2.
        destruct (HJ sigma B Hr) as [J1 J2].
        inversion H1 as [s1 B1 e1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst.
        * inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- destruct (event_eq_dec e1 e2) as [-> | Hne].
             ++ exists (apply e2 sigma, rm e2 B). split; apply star_refl.
             ++ apply (join_back _ _ _ _ (apply_norm sigma B e1 Hin1 Hen1)
                                         (apply_norm sigma B e2 Hin2 Hen2)).
                apply J1; assumption.
          -- apply (join_back _ _ _ _ (apply_norm sigma B e1 Hin1 Hen1)
                      (star_step _ _ _ _ (st_apply _ _ _ _ _ _ _ _ Hin1 (enabled_after_comp _ _ _ Hen1))
                         (rho_star_reach _ _))).
             apply J2; assumption.
        * inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- apply (join_back _ _ _ _
                      (star_step _ _ _ _ (st_apply _ _ _ _ _ _ _ _ Hin2 (enabled_after_comp _ _ _ Hen2))
                         (rho_star_reach _ _))
                      (apply_norm sigma B e2 Hin2 Hen2)).
             destruct (J2 e2 Hinv1 Hin2 Hen2) as [w [A1 A2]]. exists w. split; assumption.
          -- exists (rho sigma, B). split; apply star_refl.
      + intros x _. exact (terminating event_eq_dec apply rho valid Phi enabled wfc x).
      + apply star_refl.
  Qed.

  Corollary jc_unique_normal_forms : forall c0, JC c0 -> UN gstep c0.
  Proof. intros c0 H. apply CR_UN. apply jc_exact. exact H. Qed.

  (* CC1 (co-enabled pairs) and CC2 on the states reachable from s0 imply JC. *)
  Hypothesis enabled_after_remove :
    forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (rm e1 B) /\ enabled e2 (rho_star (apply e1 sigma)) (rm e1 B).

  Definition CC1_on (s0 : State) : Prop :=
    forall sigma B e1 e2, reach s0 sigma ->
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma))) = rho_star (apply e1 (rho_star (apply e2 sigma))).

  Definition CC2_on (s0 : State) : Prop :=
    forall sigma e, reach s0 sigma -> ~ valid sigma ->
      rho_star (apply e sigma) = rho_star (apply e (rho sigma)).

  Theorem cc_reach_jc : forall s0 c0, CC1_on s0 -> CC2_on s0 -> reach s0 (fst c0) -> JC c0.
  Proof.
    intros s0 c0 H1 H2 Hc0 sigma B Hr.
    assert (Hs : reach s0 sigma).
    { exact (star_closed gstep (fun c => reach s0 (fst c)) (reach_step s0) c0 (sigma, B) Hc0 Hr). }
    split.
    - intros e1 e2 Hin1 Hin2 Hen1 Hen2 Hne.
      destruct (enabled_after_remove sigma B e1 e2 Hen1 Hen2 Hne) as [Hin2' Hen2'].
      destruct (enabled_after_remove sigma B e2 e1 Hen2 Hen1 (fun E => Hne (eq_sym E))) as [Hin1' Hen1'].
      exists (rho_star (apply e2 (rho_star (apply e1 sigma))), rm e2 (rm e1 B)). split.
      + apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach); assumption.
      + rewrite (H1 sigma B e1 e2 Hs Hen1 Hen2 Hne), remove1_comm.
        apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach); assumption.
    - intros e Hinv _ _. rewrite (H2 sigma e Hs Hinv).
      exists (rho_star (apply e (rho sigma)), rm e B). split; apply star_refl.
  Qed.

  (* Governance.v and GovernanceCausal.v with CC required only on reachable states. *)
  Theorem cc_reach_unique_normal_forms :
    forall s0, CC1_on s0 -> CC2_on s0 -> forall sigma B, reach s0 sigma -> UN gstep (sigma, B).
  Proof.
    intros s0 H1 H2 sigma B Hs. apply jc_unique_normal_forms.
    apply (cc_reach_jc s0); assumption.
  Qed.
End Converse.

(* ============================================================================================ *)
(* Free delivery: CC on reachable states is EXACTLY unique normal forms.                        *)
(* ============================================================================================ *)

Section FreeExact.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable Phi      : State -> nat.

  (* Free delivery: every buffered event may fire. *)
  Definition free_enabled (e : Event) (_ : State) (B : list Event) : Prop := In e B.

  Local Notation fstep := (step event_eq_dec apply rho valid free_enabled).
  Local Notation rm := (remove1 event_eq_dec).
  Local Notation gov e s := (rho_star (apply e s)).

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star fstep (sigma, B) (rho_star sigma, B).
  (* Canonical repair: rho_star repairs to validity (Def. "Iterated Compensation"). *)
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  Lemma rm_head : forall e l, rm e (e :: l) = l.
  Proof. intros e l. simpl. destruct (event_eq_dec e e) as [_ | N]; [reflexivity | contradiction]. Qed.

  Lemma rm_skip : forall e x l, x <> e -> rm e (x :: l) = x :: rm e l.
  Proof. intros e x l H. simpl. destruct (event_eq_dec x e) as [E | _]; [contradiction | reflexivity]. Qed.

  Lemma in_rm : forall e x l, In x l -> x <> e -> In x (rm e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |].
    simpl. destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma nf_valid_empty : forall t, valid t -> normal_form fstep (t, []).
  Proof.
    intros t Hv [y H]. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst.
    - destruct Hin.
    - apply Hinv. exact Hv.
  Qed.

  Lemma gov_run : forall sigma B e, In e B -> star fstep (sigma, B) (gov e sigma, rm e B).
  Proof. intros. apply (apply_then_normalize _ _ _ _ _ _ rho_star_reach); assumption. Qed.

  (* The two sides of CC1 at sigma are the normal forms of two runs from (sigma, [e1; e2]). *)
  Theorem cc1_runs : forall sigma e1 e2, e1 <> e2 ->
    star fstep (sigma, [e1; e2]) (gov e2 (gov e1 sigma), []) /\
    star fstep (sigma, [e1; e2]) (gov e1 (gov e2 sigma), []) /\
    normal_form fstep (gov e2 (gov e1 sigma), []) /\
    normal_form fstep (gov e1 (gov e2 sigma), []).
  Proof.
    intros sigma e1 e2 Hne. split; [| split; [| split]].
    - eapply star_trans; [apply (gov_run sigma [e1; e2] e1); left; reflexivity |].
      rewrite rm_head. pose proof (gov_run (gov e1 sigma) [e2] e2 (or_introl eq_refl)) as H.
      rewrite rm_head in H. exact H.
    - eapply star_trans; [apply (gov_run sigma [e1; e2] e2); right; left; reflexivity |].
      rewrite (rm_skip e2 e1 [e2] Hne), rm_head.
      pose proof (gov_run (gov e2 sigma) [e1] e1 (or_introl eq_refl)) as H.
      rewrite rm_head in H. exact H.
    - apply nf_valid_empty. apply rho_star_valid.
    - apply nf_valid_empty. apply rho_star_valid.
  Qed.

  (* The two sides of CC2 at an invalid sigma are the normal forms of two runs from (sigma, [e]). *)
  Theorem cc2_runs : forall sigma e, ~ valid sigma ->
    star fstep (sigma, [e]) (gov e sigma, []) /\
    star fstep (sigma, [e]) (gov e (rho sigma), []) /\
    normal_form fstep (gov e sigma, []) /\
    normal_form fstep (gov e (rho sigma), []).
  Proof.
    intros sigma e Hinv. split; [| split; [| split]].
    - pose proof (gov_run sigma [e] e (or_introl eq_refl)) as H. rewrite rm_head in H. exact H.
    - eapply star_step; [apply st_comp; exact Hinv |].
      pose proof (gov_run (rho sigma) [e] e (or_introl eq_refl)) as H. rewrite rm_head in H. exact H.
    - apply nf_valid_empty. apply rho_star_valid.
    - apply nf_valid_empty. apply rho_star_valid.
  Qed.

  (* A CC1 failure is a divergence: two event orders, two distinct normal forms. *)
  Theorem cc1_fail_diverge : forall sigma e1 e2,
    gov e2 (gov e1 sigma) <> gov e1 (gov e2 sigma) ->
    exists n1 n2, star fstep (sigma, [e1; e2]) n1 /\ normal_form fstep n1 /\
                  star fstep (sigma, [e1; e2]) n2 /\ normal_form fstep n2 /\ n1 <> n2.
  Proof.
    intros sigma e1 e2 Hne.
    assert (Hd : e1 <> e2) by (intro E; subst; apply Hne; reflexivity).
    destruct (cc1_runs sigma e1 e2 Hd) as [S1 [S2 [N1 N2]]].
    exists (gov e2 (gov e1 sigma), []), (gov e1 (gov e2 sigma), []).
    repeat split; try assumption. intro E. injection E. exact Hne.
  Qed.

  (* A CC2 failure is a divergence: repair-then-apply and apply-then-repair disagree. *)
  Theorem cc2_fail_diverge : forall sigma e, ~ valid sigma ->
    gov e sigma <> gov e (rho sigma) ->
    exists n1 n2, star fstep (sigma, [e]) n1 /\ normal_form fstep n1 /\
                  star fstep (sigma, [e]) n2 /\ normal_form fstep n2 /\ n1 <> n2.
  Proof.
    intros sigma e Hinv Hne. destruct (cc2_runs sigma e Hinv) as [S1 [S2 [N1 N2]]].
    exists (gov e sigma, []), (gov e (rho sigma), []).
    repeat split; try assumption. intro E. injection E. exact Hne.
  Qed.

  (* The exact characterization, relative to a start state s0. *)
  Theorem cc_exact : forall s0,
    (forall sigma B, reach apply rho valid s0 sigma -> UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        gov e sigma = gov e (rho sigma))).
  Proof.
    intros s0. split.
    - intros H. split.
      + intros sigma e1 e2 Hs. destruct (event_eq_dec e1 e2) as [-> | Hd]; [reflexivity |].
        destruct (cc1_runs sigma e1 e2 Hd) as [S1 [S2 [N1 N2]]].
        pose proof (H sigma [e1; e2] Hs _ _ S1 N1 S2 N2) as E. injection E. auto.
      + intros sigma e Hs Hinv. destruct (cc2_runs sigma e Hinv) as [S1 [S2 [N1 N2]]].
        pose proof (H sigma [e] Hs _ _ S1 N1 S2 N2) as E. injection E. auto.
    - intros [H1 H2] sigma B Hs.
      assert (Har : forall s B e1 e2, free_enabled e1 s B -> free_enabled e2 s B -> e1 <> e2 ->
                  In e2 (rm e1 B) /\ free_enabled e2 (rho_star (apply e1 s)) (rm e1 B)).
      { intros s B' e1 e2 _ H2' Hne. unfold free_enabled.
        assert (Hi : In e2 (rm e1 B')) by (apply in_rm; [exact H2' | intro E; apply Hne; symmetry; exact E]).
        split; exact Hi. }
      apply (cc_reach_unique_normal_forms event_eq_dec apply rho rho_star valid Phi free_enabled
               wfc rho_star_reach (fun _ _ _ H => H) Har s0); [| | exact Hs].
      + intros s B' e1 e2 Hs' _ _ _. apply H1. exact Hs'.
      + intros s e Hs' Hinv. apply H2; assumption.
  Qed.

  (* Every reachable state is reached by a run from s0: a word w of events, delivered first. *)
  Lemma reach_run : forall s0 sigma, reach apply rho valid s0 sigma ->
    exists w, forall B, star fstep (s0, w ++ B) (sigma, B).
  Proof.
    intros s0 sigma H. induction H as [| e s _ [w IH] | s _ [w IH] Hinv].
    - exists []. intros B. apply star_refl.
    - exists (w ++ [e]). intros B. rewrite <- app_assoc. simpl.
      eapply star_trans; [apply IH |]. apply star_one.
      pose proof (st_apply event_eq_dec apply rho valid free_enabled s (e :: B) e
                    (or_introl eq_refl) (or_introl eq_refl)) as St.
      rewrite rm_head in St. exact St.
    - exists w. intros B. eapply star_trans; [apply IH |]. apply star_one. apply st_comp. exact Hinv.
  Qed.

  (* The converse from the start state: a CC1 failure at a state reachable from s0 is a divergence
     of two event orders from (s0, w ++ [e1; e2]). *)
  Theorem cc1_fail_diverge_from : forall s0 sigma e1 e2, reach apply rho valid s0 sigma ->
    gov e2 (gov e1 sigma) <> gov e1 (gov e2 sigma) ->
    exists w n1 n2, star fstep (s0, w ++ [e1; e2]) n1 /\ normal_form fstep n1 /\
                    star fstep (s0, w ++ [e1; e2]) n2 /\ normal_form fstep n2 /\ n1 <> n2.
  Proof.
    intros s0 sigma e1 e2 Hs Hne. destruct (reach_run s0 sigma Hs) as [w Hw].
    destruct (cc1_fail_diverge sigma e1 e2 Hne) as [n1 [n2 [S1 [N1 [S2 [N2 D]]]]]].
    exists w, n1, n2. split; [exact (star_trans _ _ _ _ (Hw _) S1) |].
    split; [exact N1 |]. split; [exact (star_trans _ _ _ _ (Hw _) S2) |]. split; assumption.
  Qed.

  Theorem cc2_fail_diverge_from : forall s0 sigma e, reach apply rho valid s0 sigma ->
    ~ valid sigma -> gov e sigma <> gov e (rho sigma) ->
    exists w n1 n2, star fstep (s0, w ++ [e]) n1 /\ normal_form fstep n1 /\
                    star fstep (s0, w ++ [e]) n2 /\ normal_form fstep n2 /\ n1 <> n2.
  Proof.
    intros s0 sigma e Hs Hinv Hne. destruct (reach_run s0 sigma Hs) as [w Hw].
    destruct (cc2_fail_diverge sigma e Hinv Hne) as [n1 [n2 [S1 [N1 [S2 [N2 D]]]]]].
    exists w, n1, n2. split; [exact (star_trans _ _ _ _ (Hw _) S1) |].
    split; [exact N1 |]. split; [exact (star_trans _ _ _ _ (Hw _) S2) |]. split; assumption.
  Qed.

  (* The headline form: every event buffer delivered from s0 has a unique normal form IFF CC1 and
     CC2 hold on the states reachable from s0. *)
  Theorem cc_exact_from : forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        gov e sigma = gov e (rho sigma))).
  Proof.
    intros s0. split.
    - intros H. split.
      + intros sigma e1 e2 Hs. destruct (event_eq_dec e1 e2) as [-> | Hd]; [reflexivity |].
        destruct (reach_run s0 sigma Hs) as [w Hw].
        destruct (cc1_runs sigma e1 e2 Hd) as [S1 [S2 [N1 N2]]].
        pose proof (H (w ++ [e1; e2]) _ _ (star_trans _ _ _ _ (Hw _) S1) N1
                                          (star_trans _ _ _ _ (Hw _) S2) N2) as E.
        injection E. auto.
      + intros sigma e Hs Hinv. destruct (reach_run s0 sigma Hs) as [w Hw].
        destruct (cc2_runs sigma e Hinv) as [S1 [S2 [N1 N2]]].
        pose proof (H (w ++ [e]) _ _ (star_trans _ _ _ _ (Hw _) S1) N1
                                     (star_trans _ _ _ _ (Hw _) S2) N2) as E.
        injection E. auto.
    - intros HC B. apply (proj2 (cc_exact s0) HC). apply r_init.
  Qed.

  (* Every state reachable: CC everywhere is exactly unique normal forms everywhere. *)
  Corollary cc_exact_global :
    (forall sigma B, UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma))).
  Proof.
    split.
    - intros H. split.
      + intros sigma e1 e2.
        apply (proj1 (proj1 (cc_exact sigma) (fun s B _ => H s B)) sigma e1 e2 (r_init _ _ _ _)).
      + intros sigma e Hinv.
        apply (proj2 (proj1 (cc_exact sigma) (fun s B _ => H s B)) sigma e (r_init _ _ _ _) Hinv).
    - intros [H1 H2] sigma B.
      apply (proj2 (cc_exact sigma)); [| apply r_init].
      split; [intros s e1 e2 _; apply H1 | intros s e _ Hinv; apply H2; exact Hinv].
  Qed.
End FreeExact.

(* ============================================================================================ *)
(* Counterexample 1: the converse needs rho_star to repair to validity.                         *)
(* ============================================================================================ *)

(* One boolean, only false is valid, compensation resets to false. Events: true sets the flag,
   false flips it. With the canonical repair (constantly false) CC holds and every configuration
   has a unique normal form. The identity also satisfies Governance.v's hypothesis on rho_star
   (it is a reduct, by zero steps), and with it CC1 fails: the raw events do not commute. *)

Definition q_apply (e s : bool) : bool := if e then true else negb s.
Definition q_rho (_ : bool) : bool := false.
Definition q_valid (s : bool) : Prop := s = false.
Definition q_Phi (s : bool) : nat := if s then 1 else 0.

Definition q_step :=
  step (State:=bool) (Event:=bool) Bool.bool_dec q_apply q_rho q_valid (free_enabled (State:=bool)).

Lemma q_wfc : forall s, ~ q_valid s -> q_Phi (q_rho s) < q_Phi s.
Proof. intros [|] H; [simpl; lia | exfalso; apply H; reflexivity]. Qed.

Lemma q_reach_canonical : forall s B, star q_step (s, B) (q_rho s, B).
Proof.
  intros [|] B.
  - eapply star_step; [apply st_comp; discriminate | apply star_refl].
  - apply star_refl.
Qed.

Theorem rho_star_qualifier :
  (forall s B, star q_step (s, B) (s, B)) /\
  ~ (forall s e1 e2, q_apply e2 (q_apply e1 s) = q_apply e1 (q_apply e2 s)) /\
  (forall s B, UN q_step (s, B)).
Proof.
  split; [intros; apply star_refl | split].
  - intro H. specialize (H false true false). discriminate H.
  - apply (proj2 (cc_exact_global Bool.bool_dec q_apply q_rho q_rho q_valid q_Phi
                    q_wfc q_reach_canonical (fun _ => eq_refl))).
    split; reflexivity.
Qed.

(* ============================================================================================ *)
(* Counterexample 2: under causal enabledness a CC1 failure can be masked by the future.        *)
(* ============================================================================================ *)

(* A register set to 1 by M1, to 2 by M2, reset to 0 by MR; MR is enabled only once M1 and M2 have
   left the buffer (it is causally after both). No compensation. M1 and M2 are enabled together at
   the start and do not commute (CC1 fails there), yet every run from the start ends in (0, []). *)

Inductive mev := M1 | M2 | MR.

Definition mev_eq_dec : forall a b : mev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition m_apply (e : mev) (_ : nat) : nat := match e with M1 => 1 | M2 => 2 | MR => 0 end.
Definition m_rho (s : nat) : nat := s.
Definition m_valid (_ : nat) : Prop := True.
Definition m_enabled (e : mev) (_ : nat) (B : list mev) : Prop :=
  e = MR -> ~ In M1 B /\ ~ In M2 B.

Definition m_step := step (State:=nat) mev_eq_dec m_apply m_rho m_valid m_enabled.
Definition m_start : nat * list mev := (0, [M1; M2; MR]).

Definition m_inv (c : nat * list mev) : Prop :=
  c = (0, []) \/ exists l, snd c = l ++ [MR] /\ ~ In MR l.

Lemma m_rm_app : forall e l r, In e l ->
  remove1 mev_eq_dec e (l ++ r) = remove1 mev_eq_dec e l ++ r.
Proof.
  intros e l r. induction l as [| x l IH]; intros H; [destruct H |].
  simpl. destruct (mev_eq_dec x e) as [-> | Hx]; [reflexivity |].
  destruct H as [-> | H]; [contradiction |]. simpl. rewrite (IH H). reflexivity.
Qed.

Lemma m_in_rm : forall e x l, In x (remove1 mev_eq_dec e l) -> In x l.
Proof.
  intros e x l. induction l as [| y l IH]; simpl; [auto |].
  destruct (mev_eq_dec y e); simpl; [auto | intros [H | H]; auto].
Qed.

Lemma m_only_mr : forall l, ~ In MR l -> ~ In M1 l -> ~ In M2 l -> l = [].
Proof.
  intros [| x l] H0 H1 H2; [reflexivity |].
  exfalso. destruct x; [apply H1 | apply H2 | apply H0]; left; reflexivity.
Qed.

Lemma m_inv_step : forall c d, m_inv c -> m_step c d -> m_inv d.
Proof.
  intros c d Hc H. destruct H as [s B e Hin Hen | s B Hinv]; [| exfalso; apply Hinv; exact I].
  destruct Hc as [E | [l [EB Hl]]]; simpl in *.
  - injection E as _ EB. subst B. destruct Hin.
  - subst B. destruct (mev_eq_dec e MR) as [-> | Hne].
    + destruct (Hen eq_refl) as [N1 N2].
      assert (El : l = []).
      { apply m_only_mr; [exact Hl | intro H; apply N1 | intro H; apply N2];
          apply in_or_app; left; exact H. }
      subst l. left. simpl. destruct (mev_eq_dec MR MR) as [_ | N]; [reflexivity | contradiction].
    + right. apply in_app_or in Hin. destruct Hin as [Hin | [E | []]]; [| congruence].
      exists (remove1 mev_eq_dec e l). simpl. split.
      * apply m_rm_app. exact Hin.
      * intro H. apply Hl. exact (m_in_rm e MR l H).
Qed.

Lemma m_inv_nf : forall c, m_inv c -> normal_form m_step c -> c = (0, []).
Proof.
  intros [s B] Hc Hnf. destruct Hc as [E | [l [EB Hl]]]; [exact E |].
  simpl in EB. subst B. exfalso. apply Hnf.
  destruct l as [| x l].
  - eexists. apply st_apply; [left; reflexivity |].
    intros _. split; intros [H | []]; discriminate H.
  - eexists. apply (st_apply _ _ _ _ _ s _ x); [left; reflexivity |].
    intros Ex. exfalso. subst x. apply Hl. left. reflexivity.
Qed.

Theorem masked_cc1 :
  (* M1 and M2 are distinct and enabled together at the start, *)
  m_enabled M1 0 [M1; M2; MR] /\ m_enabled M2 0 [M1; M2; MR] /\ M1 <> M2 /\
  (* CC1 fails for them there (rho_star is the identity: no compensation), *)
  m_apply M2 (m_apply M1 0) <> m_apply M1 (m_apply M2 0) /\
  (* yet every run from the start reaches the same normal form. *)
  UN m_step m_start /\
  (forall n, star m_step m_start n -> normal_form m_step n -> n = (0, [])).
Proof.
  assert (All : forall n, star m_step m_start n -> normal_form m_step n -> n = (0, [])).
  { intros n S N. apply m_inv_nf; [| exact N].
    apply (star_closed m_step m_inv m_inv_step m_start n); [| exact S].
    right. exists [M1; M2]. split; [reflexivity |]. intros [H | [H | []]]; discriminate H. }
  split; [intro H; discriminate H |]. split; [intro H; discriminate H |].
  split; [discriminate |]. split; [discriminate |]. split; [| exact All].
  intros n1 n2 S1 N1 S2 N2. rewrite (All n1 S1 N1), (All n2 S2 N2). reflexivity.
Qed.

(* ============================================================================================ *)
(* Causal delivery: the exact condition.                                                        *)
(* ============================================================================================ *)

Section CausalOrders.
  Context {E : Type}.
  Variable hb : E -> E -> Prop.

  Lemma prec_in_l : forall (k i : E) o, prec k i o -> In k o.
  Proof.
    intros k i o. induction o as [| x t IH]; simpl; [contradiction |].
    intros [[-> _] | H]; [left; reflexivity | right; apply IH; exact H].
  Qed.

  (* A prefix of a causally consistent order is causally consistent. *)
  Lemma causal_prefix : forall l r, causal hb (l ++ r) -> causal hb l.
  Proof.
    intros l r [Hnd Hc]. split; [exact (NoDup_app_remove_r _ _ Hnd) |].
    intros x y Hxy Hx Hy. pose proof (Hc x y Hxy (in_or_app _ _ _ (or_introl Hx))
                                           (in_or_app _ _ _ (or_introl Hy))) as H.
    clear Hc Hxy. induction l as [| z l IH]; [destruct Hx |].
    simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hz Hnd].
    simpl in H. destruct H as [[Ezx Hyin] | H].
    - subst z. destruct Hy as [Ey | Hy].
      + subst y. contradiction.
      + left. split; [reflexivity | exact Hy].
    - right. destruct Hx as [Ex | Hx].
      + subst z. exfalso. apply Hz. exact (prec_in_l _ _ _ H).
      + destruct Hy as [Ey | Hy].
        * subst z. exfalso. apply Hz. exact (prec_in_r _ _ _ H).
        * exact (IH Hnd Hx Hy H).
  Qed.

  Lemma prec_swap : forall (Y : list E) (b a : E) W x y, ~ (x = b /\ y = a) ->
    prec x y (Y ++ b :: a :: W) -> prec x y (Y ++ a :: b :: W).
  Proof.
    induction Y as [| z Y IH]; intros b a W x y Hn H; simpl in *.
    - destruct H as [[Eb [Ey | Hy]] | [[Ea Hy] | H]].
      + exfalso. apply Hn. split; [symmetry; exact Eb | symmetry; exact Ey].
      + right. left. split; [exact Eb | exact Hy].
      + left. split; [exact Ea | right; exact Hy].
      + right. right. exact H.
    - destruct H as [[Ez Hy] | H].
      + left. split; [exact Ez |]. apply in_app_or in Hy. apply in_or_app.
        destruct Hy as [Hy | [Hy | [Hy | Hy]]];
          [left; exact Hy | right; right; left; exact Hy | right; left; exact Hy
          | right; right; right; exact Hy].
      + right. exact (IH b a W x y Hn H).
  Qed.

  (* Swapping an adjacent pair that is not causally ordered keeps an order causally consistent. *)
  Lemma causal_swap : forall Y b a W, ~ hb b a ->
    causal hb (Y ++ b :: a :: W) -> causal hb (Y ++ a :: b :: W).
  Proof.
    intros Y b a W Hba [Hnd Hc].
    assert (HP : Permutation (Y ++ b :: a :: W) (Y ++ a :: b :: W))
      by (apply Permutation_app_head; apply perm_swap).
    split; [exact (Permutation_NoDup HP Hnd) |].
    intros x y Hxy Hx Hy. apply prec_swap.
    - intros [-> ->]. exact (Hba Hxy).
    - apply Hc; [exact Hxy | apply (Permutation_in _ (Permutation_sym HP)); exact Hx
                | apply (Permutation_in _ (Permutation_sym HP)); exact Hy].
  Qed.

  Lemma tequiv_causal : forall o1 o2, tequiv (concurrent hb) o1 o2 ->
    (causal hb o1 <-> causal hb o2).
  Proof.
    intros o1 o2 H. induction H as [l | l a b r Hab | l1 l2 _ IH | l1 l2 l3 _ IH1 _ IH2].
    - reflexivity.
    - destruct Hab as [_ [Hab Hba]]. split; apply causal_swap; assumption.
    - symmetry. exact IH.
    - rewrite IH1. exact IH2.
  Qed.
End CausalOrders.

Section CausalExact.
  Context {S E : Type}.
  Variable step : E -> S -> S.     (* governed step: apply, then normalize *)
  Variable hb : E -> E -> Prop.

  Local Notation run := (run step).

  Lemma run_app : forall l r s, run (l ++ r) s = run r (run l s).
  Proof. intros. unfold CausalReplay.run. apply fold_left_app. Qed.

  (* Causal convergence from s0. *)
  Definition CausalConv (s0 : S) : Prop :=
    forall o1 o2, causal hb o1 -> causal hb o2 -> Permutation o1 o2 -> run o1 s0 = run o2 s0.

  (* The exact condition: a concurrent pair commutes at every state after which it can be
     delivered in causal order. *)
  Definition CCR (s0 : S) : Prop :=
    forall p a b, concurrent hb a b -> causal hb (p ++ [a; b]) ->
      step b (step a (run p s0)) = step a (step b (run p s0)).

  Lemma ccr_tequiv : forall s0, CCR s0 ->
    forall o1 o2, tequiv (concurrent hb) o1 o2 -> causal hb o1 -> run o1 s0 = run o2 s0.
  Proof.
    intros s0 HC o1 o2 H. induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2];
      intros Hc.
    - reflexivity.
    - rewrite !run_app. rewrite !run_cons.
      rewrite (HC l a b Hab); [reflexivity |].
      apply (causal_prefix hb _ r). rewrite <- app_assoc. exact Hc.
    - symmetry. apply IH. apply (proj2 (tequiv_causal hb l1 l2 H)). exact Hc.
    - rewrite (IH1 Hc). apply IH2. apply (proj1 (tequiv_causal hb l1 l2 H1)). exact Hc.
  Qed.

  Theorem ccr_convergence : forall s0, CCR s0 -> CausalConv s0.
  Proof.
    intros s0 HC o1 o2 H1 H2 HP. apply (ccr_tequiv s0 HC); [| exact H1].
    apply causal_tequiv; assumption.
  Qed.

  (* A concurrent pair that can be delivered after p, and does not commute there, gives two
     causally consistent permutations that reach different states. *)
  Theorem ccr_diverge : forall s0 p a b, concurrent hb a b -> causal hb (p ++ [a; b]) ->
    step b (step a (run p s0)) <> step a (step b (run p s0)) ->
    causal hb (p ++ [b; a]) /\ Permutation (p ++ [a; b]) (p ++ [b; a]) /\
    run (p ++ [a; b]) s0 <> run (p ++ [b; a]) s0.
  Proof.
    intros s0 p a b [_ [Hab _]] Hc Hne. split; [| split].
    - apply causal_swap; assumption.
    - apply Permutation_app_head. apply perm_swap.
    - rewrite !run_app. exact Hne.
  Qed.

  Theorem causal_exact : forall s0, CausalConv s0 <-> CCR s0.
  Proof.
    intros s0. split; [| apply ccr_convergence].
    intros H p a b Hab Hc.
    assert (Hc' : causal hb (p ++ [b; a])) by (apply causal_swap; [apply Hab | exact Hc]).
    pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hc Hc'
                  (Permutation_app_head p (perm_swap b a []))) as Eq.
    rewrite !run_app in Eq. exact Eq.
  Qed.

  (* The converse of CausalReplay.causal_convergence. *)
  Theorem causal_convergence_exact : (forall x, ~ hb x x) ->
    ((forall s0, CausalConv s0) <->
     (forall a b s, concurrent hb a b -> step a (step b s) = step b (step a s))).
  Proof.
    intros Hirr. split.
    - intros H a b s Hab.
      assert (Hc : causal hb [a; b]).
      { destruct Hab as [Hne [Hab Hba]]. split.
        - constructor; [intros [Eq | []]; apply Hne; symmetry; exact Eq | constructor; [intros [] | constructor]].
        - intros x y Hxy [-> | [-> | []]] [-> | [-> | []]].
          + exfalso. exact (Hirr _ Hxy).
          + left. split; [reflexivity | left; reflexivity].
          + exfalso. exact (Hba Hxy).
          + exfalso. exact (Hirr _ Hxy). }
      symmetry. exact (proj1 (causal_exact s) (H s) [] a b Hab Hc).
    - intros H s0 o1 o2. exact (causal_convergence step hb H o1 o2 s0).
  Qed.
End CausalExact.

(* Counterexample: reachability of the non-commuting state is not enough. NA and NB are
   concurrent and do not commute at state 1, which the causally consistent run [NC] reaches from 0.
   But NC is causally after both NA and NB, so neither can be delivered after it, and every causally
   consistent order converges from 0. *)

Inductive nev := NA | NB | NC.

Definition n_step (e : nev) (s : nat) : nat :=
  match e with
  | NA => if Nat.eqb s 1 then 2 else s
  | NB => if Nat.eqb s 1 then 3 else s
  | NC => 1
  end.

Definition n_hb (x y : nev) : Prop := (x = NA \/ x = NB) /\ y = NC.

Lemma n_ccr : CCR n_step n_hb 0.
Proof.
  intros p a b [Hne [Hab Hba]] [Hnd Hc].
  assert (Hp : p = []).
  { destruct p as [| x p]; [reflexivity | exfalso].
    assert (Hx : In x (x :: p)) by (left; reflexivity).
    assert (Ha : ~ In a (x :: p)).
    { intro H. apply (NoDup_remove_2 (x :: p) [b] a Hnd). apply in_or_app. left. exact H. }
    assert (Hb : ~ In b (x :: p)).
    { intro H. assert (Hnd' : NoDup ((x :: p) ++ [b] ++ [])).
      { apply (NoDup_remove_1 (x :: p) [b] a) in Hnd. exact Hnd. }
      apply (NoDup_remove_2 (x :: p) [] b Hnd'). apply in_or_app. left. exact H. }
    destruct a, b; try (apply Hne; reflexivity);
      try (apply Hab; split; [auto | reflexivity]); try (apply Hba; split; [auto | reflexivity]).
    - (* a = NA, b = NB: x must be NC, which is causally after NA *)
      destruct x; try (apply Ha; left; reflexivity); try (apply Hb; left; reflexivity).
      apply (prec_before_contra (NC :: p) NA [NB] NC Hnd Hx).
      apply Hc; [split; [left; reflexivity | reflexivity] | apply in_or_app; right; left; reflexivity
                | apply in_or_app; left; exact Hx].
    - destruct x; try (apply Ha; left; reflexivity); try (apply Hb; left; reflexivity).
      apply (prec_before_contra (NC :: p) NB [NA] NC Hnd Hx).
      apply Hc; [split; [right; reflexivity | reflexivity] | apply in_or_app; right; left; reflexivity
                | apply in_or_app; left; exact Hx]. }
  subst p. destruct a, b; try reflexivity; exfalso;
    first [ apply Hne; reflexivity | apply Hab; split; [auto | reflexivity]
          | apply Hba; split; [auto | reflexivity] ].
Qed.

Theorem naive_causal_converse_fails :
  concurrent n_hb NA NB /\
  causal n_hb [NC] /\ run n_step [NC] 0 = 1 /\
  n_step NA (n_step NB 1) <> n_step NB (n_step NA 1) /\
  ~ causal n_hb [NC; NA; NB] /\
  CausalConv n_step n_hb 0.
Proof.
  split; [| split; [| split; [| split; [| split]]]].
  - split; [discriminate | split; intros [_ H]; discriminate H].
  - split; [constructor; [intros [] | constructor] |].
    intros x y [Hx0 ->] Hx _. destruct Hx as [<- | []]. exfalso. destruct Hx0 as [H | H]; discriminate H.
  - reflexivity.
  - simpl. discriminate.
  - intros [_ Hc]. assert (H : prec NA NC [NC; NA; NB]).
    { apply Hc; [split; [left; reflexivity | reflexivity] | right; left; reflexivity | left; reflexivity]. }
    simpl in H. destruct H as [[E _] | [[_ [E | []]] | [[E _] | []]]]; discriminate E.
  - apply ccr_convergence. exact n_ccr.
Qed.
