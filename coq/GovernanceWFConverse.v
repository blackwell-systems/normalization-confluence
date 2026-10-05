(* GovernanceWFConverse.v: the exact converses of the single-registry Convergence Theorem
   (GovernanceConverse.v: jc_exact, cc_exact_from; RhoStar.v: wfc_cc_exact_from) lifted from a
   nat-valued potential to WFC over ANY well-founded order (GovernanceWF.v's setting), including
   lexicographic products and the potential-free form "compensation is well-founded".
   Axiom-free.

   GovernanceConverse.v states every exact converse with Phi : State -> nat. The proofs use the
   potential only for termination (Newman's Lemma needs SN). This file isolates that use.

   Termination, exactly.
   - comp_rel s' s := ~ V s /\ s' = rho s (one compensation step, as a relation on states).
   - terminating_iff_comp_wf: the Governance Rewrite System terminates from every configuration
     IFF comp_rel is well-founded (for any enabledness).
   - comp_wf_iff_wfc: comp_rel is well-founded IFF WFC holds for SOME potential into SOME
     well-founded order. So "any well-founded potential" is exactly termination.
   - comp_wf_nat_potential: with V decidable, a well-founded comp_rel already has a nat potential
     (the number of compensation steps to validity). The lift to well-founded orders therefore adds
     generality only where V is not decidable; elsewhere it removes the obligation to find a
     nat-valued measure (an ordinal or lexicographic one is accepted as is).
   - canonical_comp_wf: canonical repair (rho* is a reduct of compensation steps AND valid) forces
     comp_rel to be well-founded. WFC is a consequence of canonical repair, not an extra hypothesis.

   The exact converses.
   - sn_jc_exact: any enabledness, any start c0 from which the system terminates: confluence from
     c0 IFF JC c0 (GovernanceConverse.JC). Termination is required only from c0.
   - wf_jc_exact (any well-founded potential), lex_jc_exact (lexicographic product),
     comp_wf_jc_exact (potential-free), canonical_jc_exact (canonical repair, no potential at all).
   - canonical_cc_exact_from: free delivery and canonical repair, NO termination hypothesis:
     every event buffer delivered from s0 has a unique normal form IFF CC1 and CC2 hold on the
     states reachable from s0.
   - wf_cc_exact_from: the same, stated with a potential into any well-founded order (the form of
     GovernanceWF.v). By canonical_comp_wf the potential is not used by the proof.
   - wf_cc_exact_from_built, wf_jc_exact_built: rho* constructed by RhoStar.rho_star_wf from the
     well-founded potential (no rho* hypothesis); comp_wf_cc_exact_from_built,
     comp_wf_jc_exact_built: rho* constructed from a well-founded comp_rel (no potential).
   - Corollaries recovering the nat statements, argument for argument (checked by unification):
     jc_exact_from_wf (GovernanceConverse.jc_exact), cc_exact_from_from_wf
     (GovernanceConverse.cc_exact_from), wfc_cc_exact_from_from_wf (RhoStar.wfc_cc_exact_from).

   Non-vacuity.
   - The Z-valued withdrawal registry of GovernanceWF.v (the zw_ definitions, potential in Z under Zwf 0):
     zw_unique_from (rho* given), zw_unique_from_built (rho* constructed from the Z potential),
     zw_comp_wf and zw_unique_from_comp_wf (potential-free), zw_jc (JC at every configuration).
   - A lexicographic escalation queue (the qe_ definitions): state (escalated, routine) in nat * nat, an
     escalated item repairs into two routine items, routine items over a cap of 3 drain one at a
     time; potential = the state itself under lex2 lt lt. With arrival events CC1 and CC2 hold and
     every buffer has a unique normal form (qe_unique_from); adding a "clear routine" event breaks
     CC1 at the start state, and the iff turns that into a failure of unique normal forms
     (qr_cc1_fails, qr_not_unique). *)

Require Import NC.Newman NC.Governance NC.GovernanceWF NC.GovernanceConverse NC.RhoStar.
From Coq Require Import List Arith Lia.
From Coq Require Import Wellfounded.Inverse_Image.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Termination of the Governance Rewrite System, exactly                                     *)
(* ============================================================================================ *)

Lemma SN_star_closed : forall {A : Type} (R : A -> A -> Prop) x y,
  star R x y -> SN R x -> SN R y.
Proof.
  intros A R x y S. induction S as [x | x y z Rxy _ IH]; intros H; [exact H |].
  apply IH. unfold SN in *. destruct H as [H]. apply H. exact Rxy.
Qed.

Section Termination.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply   : Event -> State -> State.
  Variable rho     : State -> State.
  Variable valid   : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).

  (* One compensation step, as a relation on states (smaller state on the left). *)
  Definition comp_rel (s' s : State) : Prop := ~ valid s /\ s' = rho s.

  Lemma comp_rel_wfc : forall s, ~ valid s -> comp_rel (rho s) s.
  Proof. intros s H. split; [exact H | reflexivity]. Qed.

  (* WFC into any well-founded order gives termination from every configuration. *)
  Theorem wf_terminating :
    forall (P : Type) (ltP : P -> P -> Prop), well_founded ltP ->
    forall Phi : State -> P, (forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s)) ->
    forall c, SN gstep c.
  Proof.
    intros P ltP W Phi H.
    apply (SN_of_lex_decrease P ltP W Phi gstep).
    exact (wf_step_decreases event_eq_dec apply rho valid enabled P ltP Phi H).
  Qed.

  Theorem comp_wf_terminating : well_founded comp_rel -> forall c, SN gstep c.
  Proof. intros W. exact (wf_terminating State comp_rel W (fun s => s) comp_rel_wfc). Qed.

  Theorem terminating_comp_wf : (forall c, SN gstep c) -> well_founded comp_rel.
  Proof.
    intros H s.
    assert (G : forall c, SN gstep c -> forall s B, c = (s, B) -> Acc comp_rel s).
    { intros c Hc. unfold SN in Hc. induction Hc as [c _ IH]. intros s0 B ->.
      constructor. intros s' [Hinv ->].
      assert (St : gstep (s0, B) (rho s0, B)) by (apply Governance.st_comp; exact Hinv).
      exact (IH (rho s0, B) St (rho s0) B eq_refl). }
    exact (G (s, []) (H (s, [])) s [] eq_refl).
  Qed.

  (* Termination from every configuration IFF compensation is well-founded. *)
  Theorem terminating_iff_comp_wf : (forall c, SN gstep c) <-> well_founded comp_rel.
  Proof. split; [exact terminating_comp_wf | exact comp_wf_terminating]. Qed.

  (* Compensation is well-founded IFF WFC holds for some potential into some well-founded order. *)
  Theorem comp_wf_iff_wfc :
    well_founded comp_rel <->
    exists (P : Type) (ltP : P -> P -> Prop) (Phi : State -> P),
      well_founded ltP /\ (forall s, ~ valid s -> ltP (Phi (rho s)) (Phi s)).
  Proof.
    split.
    - intros W. exists State, comp_rel, (fun s => s). split; [exact W | exact comp_rel_wfc].
    - intros [P [ltP [Phi [W H]]]] s.
      pose proof (wf_inverse_image State P ltP Phi W s) as A.
      induction A as [s _ IH]. constructor. intros s' [Hinv ->].
      apply IH. apply H. exact Hinv.
  Qed.

  (* With V decidable, a well-founded comp_rel has a nat potential: the number of compensation
     steps to validity. *)
  Inductive steps_to_valid : State -> nat -> Prop :=
  | stv_done : forall s, valid s -> steps_to_valid s 0
  | stv_more : forall s n, ~ valid s -> steps_to_valid (rho s) n -> steps_to_valid s (S n).

  Lemma steps_to_valid_fun : forall s n m, steps_to_valid s n -> steps_to_valid s m -> n = m.
  Proof.
    intros s n m H. revert m. induction H as [s V | s n Hn _ IH]; intros m H'.
    - inversion H'; subst; [reflexivity | contradiction].
    - inversion H'; subst; [contradiction |]. f_equal. apply IH. assumption.
  Qed.

  Theorem comp_wf_nat_potential :
    (forall s, {valid s} + {~ valid s}) -> well_founded comp_rel ->
    exists Phi : State -> nat, forall s, ~ valid s -> Phi (rho s) < Phi s.
  Proof.
    intros vd W.
    assert (F : forall s, { n | steps_to_valid s n }).
    { apply (well_founded_induction_type W). intros s IH. destruct (vd s) as [V | Hn].
      - exists 0. constructor. exact V.
      - destruct (IH (rho s) (comp_rel_wfc s Hn)) as [n Hs]. exists (S n). constructor; assumption. }
    exists (fun s => proj1_sig (F s)). intros s Hn.
    destruct (F s) as [n Hs]. destruct (F (rho s)) as [m Hm]. simpl.
    inversion Hs as [s' V | s' n' _ Hr]; subst; [contradiction |].
    rewrite (steps_to_valid_fun (rho s) m n' Hm Hr). lia.
  Qed.

  (* Canonical repair forces termination: if every state reaches a valid state by compensation
     steps (with an empty buffer), compensation is well-founded. *)
  Lemma comp_acc_of_run : forall c d, star gstep c d -> valid (fst d) -> snd c = [] ->
    Acc comp_rel (fst c).
  Proof.
    intros c d S. induction S as [x | x y z Rxy _ IH]; intros Vd Ec.
    - constructor. intros s' [Hinv _]. contradiction.
    - destruct x as [s B]. simpl in Ec. subst B.
      inversion Rxy as [s1 B1 e Hin _ E1 E2 | s1 B1 Hinv E1 E2]; subst; [destruct Hin |].
      constructor. intros s' [_ ->]. exact (IH Vd eq_refl).
  Qed.

  Theorem canonical_comp_wf :
    (forall s, exists t, valid t /\ star gstep (s, []) (t, [])) -> well_founded comp_rel.
  Proof.
    intros H s. destruct (H s) as [t [V S]]. exact (comp_acc_of_run (s, []) (t, []) S V eq_refl).
  Qed.
End Termination.

(* ============================================================================================ *)
(* 2. The exact joinability condition under termination from c0, for any enabledness           *)
(* ============================================================================================ *)

Section JCExact.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (Governance.remove1 event_eq_dec).

  Hypothesis rho_star_reach : forall sigma B, star gstep (sigma, B) (rho_star sigma, B).
  Hypothesis enabled_after_comp : forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  Lemma jc_apply_norm : forall sigma B e, In e B -> enabled e sigma B ->
    star gstep (sigma, B) (rho_star (apply e sigma), rm e B).
  Proof.
    intros. apply (Governance.apply_then_normalize event_eq_dec apply rho rho_star valid enabled
                     rho_star_reach); assumption.
  Qed.

  Lemma jc_join_back : forall x x' y y', star gstep x x' -> star gstep y y' ->
    joinable gstep x' y' -> joinable gstep x y.
  Proof.
    intros x x' y y' Sx Sy [w [A1 A2]]. exists w. split; eapply star_trans; eassumption.
  Qed.

  (* Exactness with termination required only from c0. *)
  Theorem sn_jc_exact : forall c0, SN gstep c0 ->
    (CR gstep c0 <-> JC event_eq_dec apply rho rho_star valid enabled c0).
  Proof.
    intros c0 Hsn. split.
    - intros H sigma B Hr. split.
      + intros e1 e2 Hin1 Hin2 Hen1 Hen2 _. apply H.
        * eapply star_trans; [exact Hr |]. apply jc_apply_norm; assumption.
        * eapply star_trans; [exact Hr |]. apply jc_apply_norm; assumption.
      + intros e Hinv Hin Hen. apply H.
        * eapply star_trans; [exact Hr |]. apply jc_apply_norm; assumption.
        * eapply star_trans; [exact Hr |]. eapply star_step; [apply Governance.st_comp; exact Hinv |].
          apply jc_apply_norm; [exact Hin | apply enabled_after_comp; exact Hen].
    - intros HJ. apply (newman_on gstep (fun c => star gstep c0 c)).
      + intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
      + intros [sigma B] X1 X2 Hr H1 H2.
        destruct (HJ sigma B Hr) as [J1 J2].
        inversion H1 as [s1 B1 e1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst.
        * inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- destruct (event_eq_dec e1 e2) as [-> | Hne].
             ++ exists (apply e2 sigma, rm e2 B). split; apply star_refl.
             ++ apply (jc_join_back _ _ _ _ (rho_star_reach _ _) (rho_star_reach _ _)).
                apply J1; assumption.
          -- apply (jc_join_back _ _ _ _ (rho_star_reach _ _)
                      (jc_apply_norm _ _ _ Hin1 (enabled_after_comp _ _ _ Hen1))).
             apply J2; assumption.
        * inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
          -- apply (jc_join_back _ _ _ _
                      (jc_apply_norm _ _ _ Hin2 (enabled_after_comp _ _ _ Hen2))
                      (rho_star_reach _ _)).
             destruct (J2 e2 Hinv1 Hin2 Hen2) as [w [A1 A2]]. exists w. split; assumption.
          -- exists (rho sigma, B). split; apply star_refl.
      + intros x Hx. exact (SN_star_closed gstep c0 x Hx Hsn).
      + apply star_refl.
  Qed.

  (* WFC over any well-founded order. *)
  Theorem wf_jc_exact :
    forall (P : Type) (ltP : P -> P -> Prop), well_founded ltP ->
    forall Phi : State -> P, (forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma)) ->
    forall c0, CR gstep c0 <-> JC event_eq_dec apply rho rho_star valid enabled c0.
  Proof.
    intros P ltP W Phi H c0. apply sn_jc_exact.
    exact (wf_terminating event_eq_dec apply rho valid enabled P ltP W Phi H c0).
  Qed.

  (* A potential into a lexicographic product of two well-founded orders. *)
  Corollary lex_jc_exact :
    forall (P1 P2 : Type) (lt1 : P1 -> P1 -> Prop) (lt2 : P2 -> P2 -> Prop)
           (Phi : State -> P1 * P2),
    well_founded lt1 -> well_founded lt2 ->
    (forall sigma, ~ valid sigma -> lex2 lt1 lt2 (Phi (rho sigma)) (Phi sigma)) ->
    forall c0, CR gstep c0 <-> JC event_eq_dec apply rho rho_star valid enabled c0.
  Proof.
    intros P1 P2 lt1 lt2 Phi W1 W2 H.
    exact (wf_jc_exact (P1 * P2) (lex2 lt1 lt2) (wf_lex2 lt1 lt2 W1 W2) Phi H).
  Qed.

  (* No potential: compensation itself is well-founded. *)
  Corollary comp_wf_jc_exact : well_founded (comp_rel rho valid) ->
    forall c0, CR gstep c0 <-> JC event_eq_dec apply rho rho_star valid enabled c0.
  Proof.
    intros W c0. apply sn_jc_exact.
    exact (comp_wf_terminating event_eq_dec apply rho valid enabled W c0).
  Qed.

  (* No potential and no termination hypothesis: canonical repair alone. *)
  Corollary canonical_jc_exact : (forall sigma, valid (rho_star sigma)) ->
    forall c0, CR gstep c0 <-> JC event_eq_dec apply rho rho_star valid enabled c0.
  Proof.
    intros V. apply comp_wf_jc_exact.
    apply (canonical_comp_wf event_eq_dec apply rho valid enabled).
    intros s. exists (rho_star s). split; [apply V | apply rho_star_reach].
  Qed.
End JCExact.

(* GovernanceConverse.v's nat-valued jc_exact, recovered with P = nat, ltP = lt. *)
Corollary jc_exact_from_wf :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho rho_star : State -> State) (valid : State -> Prop)
    (Phi : State -> nat) (enabled : Event -> State -> list Event -> Prop),
  (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
  (forall sigma B, star (Governance.step event_eq_dec apply rho valid enabled)
                        (sigma, B) (rho_star sigma, B)) ->
  (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
  forall c0 : Governance.Config,
  CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
  JC event_eq_dec apply rho rho_star valid enabled c0.
Proof.
  intros State Event dec apply rho rho_star valid Phi enabled wfc reach eac.
  exact (wf_jc_exact dec apply rho rho_star valid enabled reach eac nat lt lt_wf Phi wfc).
Qed.

(* ============================================================================================ *)
(* 3. Free delivery: CC on reachable states is exactly unique normal forms                       *)
(* ============================================================================================ *)

Section FreeWF.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.

  Local Notation fstep := (Governance.step event_eq_dec apply rho valid free_enabled).
  Local Notation rm := (Governance.remove1 event_eq_dec).
  Local Notation gov e s := (rho_star (apply e s)).

  (* Canonical repair (Def. "Iterated Compensation"): rho* is reached by compensation steps and is
     valid. *)
  Hypothesis rho_star_reach : forall sigma B, star fstep (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  Lemma rm_keep : forall e x l, In x l -> x <> e -> In x (rm e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |].
    simpl. destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  (* Canonical repair makes compensation well-founded: WFC is implied, not assumed. *)
  Theorem canonical_free_comp_wf : well_founded (comp_rel rho valid).
  Proof.
    apply (canonical_comp_wf event_eq_dec apply rho valid free_enabled).
    intros s. exists (rho_star s). split; [apply rho_star_valid | apply rho_star_reach].
  Qed.

  (* The headline, with no termination hypothesis: every event buffer delivered from s0 has a
     unique normal form IFF CC1 and CC2 hold on the states reachable from s0. *)
  Theorem canonical_cc_exact_from : forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        gov e sigma = gov e (rho sigma))).
  Proof.
    intros s0. split.
    - intros H. split.
      + intros sigma e1 e2 Hs. destruct (event_eq_dec e1 e2) as [-> | Hd]; [reflexivity |].
        destruct (reach_run event_eq_dec apply rho valid s0 sigma Hs) as [w Hw].
        destruct (cc1_runs event_eq_dec apply rho rho_star valid rho_star_reach rho_star_valid
                    sigma e1 e2 Hd) as [S1 [S2 [N1 N2]]].
        pose proof (H (w ++ [e1; e2]) _ _ (star_trans _ _ _ _ (Hw _) S1) N1
                                          (star_trans _ _ _ _ (Hw _) S2) N2) as E.
        injection E. auto.
      + intros sigma e Hs Hinv.
        destruct (reach_run event_eq_dec apply rho valid s0 sigma Hs) as [w Hw].
        destruct (cc2_runs event_eq_dec apply rho rho_star valid rho_star_reach rho_star_valid
                    sigma e Hinv) as [S1 [S2 [N1 N2]]].
        pose proof (H (w ++ [e]) _ _ (star_trans _ _ _ _ (Hw _) S1) N1
                                     (star_trans _ _ _ _ (Hw _) S2) N2) as E.
        injection E. auto.
    - intros [H1 H2] B. apply CR_UN.
      apply (proj2 (canonical_jc_exact event_eq_dec apply rho rho_star valid free_enabled
                      rho_star_reach (fun _ _ _ H => H) rho_star_valid (s0, B))).
      assert (Har : forall s B' e1 e2, free_enabled e1 s B' -> free_enabled e2 s B' -> e1 <> e2 ->
                  In e2 (rm e1 B') /\ free_enabled e2 (rho_star (apply e1 s)) (rm e1 B')).
      { intros s B' e1 e2 _ H2' Hne. unfold free_enabled.
        assert (Hi : In e2 (rm e1 B'))
          by (apply rm_keep; [exact H2' | intro E; apply Hne; symmetry; exact E]).
        split; exact Hi. }
      apply (cc_reach_jc event_eq_dec apply rho rho_star valid free_enabled rho_star_reach Har s0).
      + intros s B' e1 e2 Hs' _ _ _. apply H1. exact Hs'.
      + intros s e Hs' Hinv. apply H2; assumption.
      + apply r_init.
  Qed.

  (* The requested form: WFC over any well-founded order (GovernanceWF.v's setting). The potential
     is accepted but not needed: canonical_free_comp_wf derives termination from canonical repair. *)
  Theorem wf_cc_exact_from :
    forall (P : Type) (ltP : P -> P -> Prop), well_founded ltP ->
    forall Phi : State -> P, (forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma)) ->
    forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        gov e sigma = gov e (rho sigma))).
  Proof. intros P ltP W Phi H. exact canonical_cc_exact_from. Qed.
End FreeWF.

(* GovernanceConverse.v's nat-valued cc_exact_from, recovered. *)
Corollary cc_exact_from_from_wf :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho rho_star : State -> State) (valid : State -> Prop)
    (Phi : State -> nat),
  (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
  (forall sigma B, star (Governance.step event_eq_dec apply rho valid free_enabled)
                        (sigma, B) (rho_star sigma, B)) ->
  (forall sigma, valid (rho_star sigma)) ->
  forall s0,
  (forall B, UN (Governance.step event_eq_dec apply rho valid free_enabled) (s0, B)) <->
  ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
      rho_star (apply e2 (rho_star (apply e1 sigma))) =
      rho_star (apply e1 (rho_star (apply e2 sigma)))) /\
   (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
      rho_star (apply e sigma) = rho_star (apply e (rho sigma)))).
Proof.
  intros State Event dec apply rho rho_star valid Phi wfc reach V.
  exact (wf_cc_exact_from dec apply rho rho_star valid reach V nat lt lt_wf Phi wfc).
Qed.

(* ============================================================================================ *)
(* 4. rho* constructed (RhoStar.rho_star_wf): no rho* hypothesis                                 *)
(* ============================================================================================ *)

Section Built.
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
  Local Notation fstep := (Governance.step event_eq_dec apply rho valid free_enabled).

  Lemma built_reach : forall (enabled : Event -> State -> list Event -> Prop) s B,
    star (Governance.step event_eq_dec apply rho valid enabled) (s, B) (N s, B).
  Proof. intros. apply crel_reach_gov. apply rho_star_wf_crel. Qed.

  (* Free delivery, rho* built from any well-founded potential. *)
  Theorem wf_cc_exact_from_built : forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
        N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) /\
     (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
        N (apply e sigma) = N (apply e (rho sigma)))).
  Proof.
    exact (canonical_cc_exact_from event_eq_dec apply rho N valid (built_reach free_enabled)
             (rho_star_wf_valid rho valid valid_dec P ltP wf_ltP Phi wfc_wf)).
  Qed.

  (* Any enabledness, rho* built from any well-founded potential. *)
  Theorem wf_jc_exact_built :
    forall enabled : Event -> State -> list Event -> Prop,
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    forall c0, CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
               JC event_eq_dec apply rho N valid enabled c0.
  Proof.
    intros enabled eac.
    exact (wf_jc_exact event_eq_dec apply rho N valid enabled (built_reach enabled) eac
             P ltP wf_ltP Phi wfc_wf).
  Qed.
End Built.

(* rho* built with no potential: compensation itself is well-founded (P = State, Phi = id). *)
Definition rho_star_comp {State : Type} (rho : State -> State) (valid : State -> Prop)
  (valid_dec : forall s, {valid s} + {~ valid s}) (W : well_founded (comp_rel rho valid)) :
  State -> State :=
  rho_star_wf rho valid valid_dec State (comp_rel rho valid) W (fun s => s) (comp_rel_wfc rho valid).

Theorem comp_wf_cc_exact_from_built :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s}) (W : well_founded (comp_rel rho valid)),
  let N := rho_star_comp rho valid valid_dec W in
  forall s0,
  (forall B, UN (Governance.step event_eq_dec apply rho valid free_enabled) (s0, B)) <->
  ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
      N (apply e2 (N (apply e1 sigma))) = N (apply e1 (N (apply e2 sigma)))) /\
   (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
      N (apply e sigma) = N (apply e (rho sigma)))).
Proof.
  intros State Event dec apply rho valid vd W N.
  exact (wf_cc_exact_from_built dec apply rho valid vd State (comp_rel rho valid) W (fun s => s)
           (comp_rel_wfc rho valid)).
Qed.

Theorem comp_wf_jc_exact_built :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s}) (W : well_founded (comp_rel rho valid))
    (enabled : Event -> State -> list Event -> Prop),
  (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
  forall c0, CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
             JC event_eq_dec apply rho (rho_star_comp rho valid valid_dec W) valid enabled c0.
Proof.
  intros State Event dec apply rho valid vd W enabled eac.
  exact (wf_jc_exact_built dec apply rho valid vd State (comp_rel rho valid) W (fun s => s)
           (comp_rel_wfc rho valid) enabled eac).
Qed.

(* RhoStar.v's nat-valued wfc_cc_exact_from (rho* by fuel), recovered from canonical_cc_exact_from. *)
Corollary wfc_cc_exact_from_from_wf :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s}) (Phi : State -> nat),
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  forall s0,
  (forall B, UN (Governance.step event_eq_dec apply rho valid free_enabled) (s0, B)) <->
  ((forall sigma e1 e2, reach apply rho valid s0 sigma ->
      rho_star rho valid valid_dec Phi (apply e2 (rho_star rho valid valid_dec Phi (apply e1 sigma))) =
      rho_star rho valid valid_dec Phi (apply e1 (rho_star rho valid valid_dec Phi (apply e2 sigma)))) /\
   (forall sigma e, reach apply rho valid s0 sigma -> ~ valid sigma ->
      rho_star rho valid valid_dec Phi (apply e sigma) =
      rho_star rho valid valid_dec Phi (apply e (rho sigma)))).
Proof.
  intros State Event dec apply rho valid vd Phi wfc.
  exact (canonical_cc_exact_from dec apply rho (rho_star rho valid vd Phi) valid
           (rs_reach_gov dec apply rho valid vd Phi wfc free_enabled)
           (rho_star_valid rho valid vd Phi wfc)).
Qed.

(* The recovered statements are the original statements (the types unify syntactically). *)
Goal True.
Proof.
  let t1 := type of @GovernanceConverse.jc_exact in
  let t2 := type of @jc_exact_from_wf in unify t1 t2.
  let t1 := type of @GovernanceConverse.cc_exact_from in
  let t2 := type of @cc_exact_from_from_wf in unify t1 t2.
  let t1 := type of @RhoStar.wfc_cc_exact_from in
  let t2 := type of @wfc_cc_exact_from_from_wf in unify t1 t2.
  exact I.
Qed.

(* ============================================================================================ *)
(* 5. Non-vacuity: the Z-valued withdrawal registry (GovernanceWF.v)                             *)
(* ============================================================================================ *)

From Coq Require Import ZArith Zwf.
Open Scope Z_scope.

Local Notation zw_fstep :=
  (Governance.step Nat.eq_dec zw_apply zw_rho zw_valid (free_enabled (State:=Z) (Event:=nat))).

(* zw_enabled is free delivery. *)
Lemma zw_free_reach : forall s B, star zw_fstep (s, B) (zw_rho_star s, B).
Proof. exact zw_rho_star_reach. Qed.

Lemma zw_canonical : forall s, zw_valid (zw_rho_star s).
Proof. intro s. unfold zw_valid, zw_rho_star. lia. Qed.

(* wf_cc_exact_from with the Z potential under Zwf 0: unique normal forms from every start. *)
Theorem zw_unique_from : forall s0 B, UN zw_fstep (s0, B).
Proof.
  intros s0. apply (proj2 (wf_cc_exact_from Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid
                             zw_free_reach zw_canonical Z (Zwf 0) (Zwf_well_founded 0) zw_Phi
                             zw_wfc s0)).
  split; intros; [apply zw_cc1 | apply zw_cc2; assumption].
Qed.

(* The same with rho* constructed from the Z potential (no rho* hypothesis). *)
Theorem zw_unique_from_built : forall s0 B, UN zw_fstep (s0, B).
Proof.
  intros s0. apply (proj2 (wf_cc_exact_from_built Nat.eq_dec zw_apply zw_rho zw_valid zw_valid_dec
                             Z (Zwf 0) (Zwf_well_founded 0) zw_Phi zw_wfc s0)).
  split; intros; rewrite !zw_rho_star_built; [apply zw_cc1 | apply zw_cc2; assumption].
Qed.

(* Potential-free: compensation on Z is well-founded, and rho* built from it is zw_rho_star. *)
Theorem zw_comp_wf : well_founded (comp_rel zw_rho zw_valid).
Proof.
  apply (proj2 (comp_wf_iff_wfc zw_rho zw_valid)).
  exists Z, (Zwf 0), zw_Phi. split; [apply Zwf_well_founded | exact zw_wfc].
Qed.

Lemma zw_rho_star_comp : forall s, rho_star_comp zw_rho zw_valid zw_valid_dec zw_comp_wf s = zw_rho_star s.
Proof. intro s. apply (crel_fun zw_rho zw_valid s); [apply rho_star_wf_crel | apply zw_crel]. Qed.

Theorem zw_unique_from_comp_wf : forall s0 B, UN zw_fstep (s0, B).
Proof.
  intros s0. apply (proj2 (comp_wf_cc_exact_from_built Nat.eq_dec zw_apply zw_rho zw_valid
                             zw_valid_dec zw_comp_wf s0)).
  simpl. split; intros; rewrite !zw_rho_star_comp; [apply zw_cc1 | apply zw_cc2; assumption].
Qed.

(* wf_jc_exact: JC holds at every configuration of the Z registry. *)
Theorem zw_jc : forall c0,
  JC Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled c0.
Proof.
  intros c0. apply (proj1 (wf_jc_exact Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled
                             zw_rho_star_reach zw_enabled_after_comp Z (Zwf 0) (Zwf_well_founded 0)
                             zw_Phi zw_wfc c0)).
  apply zw_confluent.
Qed.

Close Scope Z_scope.

(* ============================================================================================ *)
(* 6. Non-vacuity: a lexicographic escalation queue                                              *)
(* ============================================================================================ *)

(* State (h, l): h escalated items, l routine items. Valid: no escalated item and at most 3 routine
   items. Repair: an escalated item becomes two routine items; with none escalated, one routine
   item drains. The potential is the state itself under lex2 lt lt. *)

Definition qe_valid (s : nat * nat) : Prop := fst s = 0 /\ snd s <= 3.

Definition qe_valid_dec (s : nat * nat) : {qe_valid s} + {~ qe_valid s}.
Proof.
  destruct s as [h l]. unfold qe_valid; simpl.
  destruct (Nat.eq_dec h 0) as [Hh | Hh].
  - destruct (le_dec l 3) as [Hl | Hl]; [left; split; assumption | right; intros [_ H]; contradiction].
  - right. intros [H _]. contradiction.
Defined.

Definition qe_rho (s : nat * nat) : nat * nat :=
  match s with
  | (S h, l) => (h, l + 2)
  | (0, l) => (0, l - 1)
  end.

Definition qe_Phi (s : nat * nat) : nat * nat := s.

Lemma qe_wf : well_founded (lex2 lt lt).
Proof. exact (wf_lex2 lt lt lt_wf lt_wf). Qed.

Lemma qe_inv0 : forall l, ~ qe_valid (0, l) -> 3 < l.
Proof.
  intros l H. destruct (le_dec l 3) as [Hl | Hl]; [| lia].
  exfalso. apply H. split; [reflexivity | exact Hl].
Qed.

Lemma qe_wfc : forall s, ~ qe_valid s -> lex2 lt lt (qe_Phi (qe_rho s)) (qe_Phi s).
Proof.
  intros [[| h] l] H; unfold qe_Phi, lex2; simpl.
  - right. split; [reflexivity |]. pose proof (qe_inv0 l H). lia.
  - left. lia.
Qed.

(* The closed form of rho*: escalations become routine items, then the routine queue caps at 3. *)
Definition qe_rs (s : nat * nat) : nat * nat := (0, Nat.min (snd s + 2 * fst s) 3).

Lemma qe_min_le : forall x, x <= 3 -> Nat.min x 3 = x.
Proof. intros. apply Nat.min_l. exact H. Qed.

Lemma qe_min_ge : forall x, 3 <= x -> Nat.min x 3 = 3.
Proof. intros. apply Nat.min_r. exact H. Qed.

Lemma qe_min_case : forall x, (x <= 3 /\ Nat.min x 3 = x) \/ (3 <= x /\ Nat.min x 3 = 3).
Proof.
  intros x. destruct (le_dec x 3) as [H | H].
  - left. split; [exact H | apply qe_min_le; exact H].
  - right. split; [lia | apply qe_min_ge; lia].
Qed.

Lemma qe_crel0 : forall l, crel qe_rho qe_valid (0, l) (0, Nat.min l 3).
Proof.
  induction l as [| l IH].
  - constructor. split; simpl; lia.
  - destruct (le_dec (S l) 3) as [Hl | Hl].
    + rewrite (qe_min_le (S l) Hl). constructor. split; [reflexivity | exact Hl].
    + assert (E : Nat.min (S l) 3 = Nat.min l 3)
        by (rewrite (qe_min_ge (S l)), (qe_min_ge l); lia).
      rewrite E. constructor 2.
      * intros [_ H]. simpl in H. lia.
      * assert (R : qe_rho (0, S l) = (0, l)) by (simpl; f_equal; lia).
        rewrite R. exact IH.
Qed.

Lemma qe_crel : forall s, crel qe_rho qe_valid s (qe_rs s).
Proof.
  intros [h l]. revert l. induction h as [| h IH]; intros l; unfold qe_rs; cbn [fst snd].
  - rewrite Nat.mul_0_r, Nat.add_0_r. apply qe_crel0.
  - constructor 2.
    + intros [H _]. discriminate H.
    + cbn [qe_rho]. replace (l + 2 * S h) with (l + 2 + 2 * h) by lia. exact (IH (l + 2)).
Qed.

Local Notation qeN := (rho_star_wf qe_rho qe_valid qe_valid_dec (nat * nat) (lex2 lt lt) qe_wf
                         qe_Phi qe_wfc).

(* The constructed rho* (from the lexicographic potential) is the closed form. *)
Theorem qe_built : forall s, qeN s = qe_rs s.
Proof. intro s. apply (crel_fun qe_rho qe_valid s); [apply rho_star_wf_crel | apply qe_crel]. Qed.

(* Arrival events: n escalated items arrive. *)
Definition qe_apply (n : nat) (s : nat * nat) : nat * nat := (fst s + n, snd s).

Local Notation qe_fstep :=
  (Governance.step Nat.eq_dec qe_apply qe_rho qe_valid (free_enabled (State:=nat * nat) (Event:=nat))).

Lemma qe_gov : forall n s, qe_rs (qe_apply n s) = (0, Nat.min (snd s + 2 * fst s + 2 * n) 3).
Proof. intros n [h l]. unfold qe_rs, qe_apply; simpl. f_equal. f_equal. lia. Qed.

Lemma qe_min_min : forall x y, Nat.min (Nat.min x 3 + y) 3 = Nat.min (x + y) 3.
Proof.
  intros x y. destruct (qe_min_case x) as [[H E] | [H E]]; rewrite E; [reflexivity |].
  rewrite (qe_min_ge (3 + y)), (qe_min_ge (x + y)); lia.
Qed.

Lemma qe_cc1 : forall s e1 e2,
  qe_rs (qe_apply e2 (qe_rs (qe_apply e1 s))) = qe_rs (qe_apply e1 (qe_rs (qe_apply e2 s))).
Proof.
  intros s e1 e2. rewrite !qe_gov. cbn [fst snd].
  rewrite !Nat.mul_0_r, !Nat.add_0_r, !qe_min_min. f_equal. f_equal. lia.
Qed.

Lemma qe_cc2 : forall s e, ~ qe_valid s -> qe_rs (qe_apply e s) = qe_rs (qe_apply e (qe_rho s)).
Proof.
  intros [[| h] l] e H; rewrite !qe_gov; cbn [fst snd qe_rho]; rewrite ?Nat.mul_0_r, ?Nat.add_0_r.
  - pose proof (qe_inv0 l H). rewrite (qe_min_ge (l + 2 * e)), (qe_min_ge (l - 1 + 2 * e)); [reflexivity | lia | lia].
  - f_equal. f_equal. lia.
Qed.

(* wf_cc_exact_from_built with a lexicographic potential: unique normal forms from every start. *)
Theorem qe_unique_from : forall s0 B, UN qe_fstep (s0, B).
Proof.
  intros s0. apply (proj2 (wf_cc_exact_from_built Nat.eq_dec qe_apply qe_rho qe_valid qe_valid_dec
                             (nat * nat) (lex2 lt lt) qe_wf qe_Phi qe_wfc s0)).
  split; intros; rewrite !qe_built; [apply qe_cc1 | apply qe_cc2; assumption].
Qed.

(* The converse direction bites: add a "clear the routine queue" event (None). CC1 fails at the
   start state (0, 0) for an arrival and a clear, so by the iff some buffer from (0, 0) has two
   distinct normal forms. *)
Definition qr_eq_dec : forall a b : option nat, {a = b} + {a <> b}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition qr_apply (e : option nat) (s : nat * nat) : nat * nat :=
  match e with
  | None => (fst s, 0)
  | Some n => (fst s + n, snd s)
  end.

Local Notation qr_fstep :=
  (Governance.step qr_eq_dec qr_apply qe_rho qe_valid
     (free_enabled (State:=nat * nat) (Event:=option nat))).

Theorem qr_cc1_fails :
  qeN (qr_apply None (qeN (qr_apply (Some 1) (0, 0)))) = (0, 0) /\
  qeN (qr_apply (Some 1) (qeN (qr_apply None (0, 0)))) = (0, 2).
Proof. rewrite !qe_built. split; reflexivity. Qed.

Theorem qr_not_unique : ~ (forall B, UN qr_fstep ((0, 0), B)).
Proof.
  intro H.
  destruct (proj1 (wf_cc_exact_from_built qr_eq_dec qr_apply qe_rho qe_valid qe_valid_dec
                     (nat * nat) (lex2 lt lt) qe_wf qe_Phi qe_wfc (0, 0)) H) as [H1 _].
  pose proof (H1 (0, 0) (Some 1) None (r_init _ _ _ _)) as E.
  destruct qr_cc1_fails as [A1 A2]. rewrite A1, A2 in E. discriminate E.
Qed.
