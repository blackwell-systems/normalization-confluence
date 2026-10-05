(* EnabledAfterComp.v: the exact confluence condition for the single-registry Governance Rewrite
   System when a compensation step may disable (or enable) a buffered event. Axiom-free.

   GovernanceConverse.jc_exact and GovernanceWFConverse.sn_jc_exact characterize confluence from c0
   by JC c0, under the hypothesis enabled_after_comp: a compensation step never disables a buffered
   event that was enabled. That hypothesis is what lets the event/compensation critical pair at an
   invalid sigma be closed by firing the event after the compensation; JC therefore compares the
   apply side with rho* (apply e (rho sigma)). When compensation can disable e, that configuration
   need not be reachable, and the critical pair has to be joined as it stands.

   The general system. The critical pairs of the rewrite system at a configuration (sigma, B) are:
   - event/event: two distinct events e1, e2, both in B and enabled at (sigma, B);
   - event/compensation: sigma invalid, e in B enabled at (sigma, B). Its successors are
     (apply e sigma, B - e) and (rho sigma, B). Whether e is still enabled at (rho sigma, B) does
     not change the peak, only how it can be closed.
   - compensation/compensation: identical successors.
   An event that compensation ENABLES (disabled at sigma, enabled at rho sigma) creates no peak at
   (sigma, B): it is not a step from there. It contributes only later steps, which the condition
   below already quantifies over, because it ranges over every configuration reachable from c0.

   Main results.
   - JCg c0 (the extended joinability condition, JC'): at every configuration reachable from c0,
     the event/event pairs are joinable after repair (as in JC), and for every event e enabled at
     an invalid sigma, (rho* (apply e sigma), B - e) is joinable with (rho sigma, B) itself.
   - jcg_exact: for ANY enabledness and any c0 from which the system terminates,
     confluence from c0 IFF JCg c0 (Newman localized: newman_on). No enabled_after_comp.
   - jcg_iff_critical, cr_iff_critical: JCg c0 is exactly joinability of every critical pair at
     every configuration reachable from c0 (local confluence on the reachable part).
   - JCsplit c0: JCg with the event/compensation clause split by whether compensation disables e:
     if e stays enabled at (rho sigma, B), JC's own clause; if it is disabled, the join with
     (rho sigma, B). jcsplit_exact: under termination from c0 and decidability of enabledness after
     compensation (emloc, implied by enabled_after_comp and by decidable enabledness), confluence
     from c0 IFF JCsplit c0.
   - Reduction to JC. jcsplit_iff_jc: under enabled_after_comp the disabled clause is vacuous and
     JCsplit c0 IFF JC c0, with no termination hypothesis. jc_jcg, jcg_iff_jc: JC c0 implies
     JCg c0 under enabled_after_comp, and they are equivalent under termination from c0.
     jc_exact_recovered and sn_jc_exact_recovered rederive GovernanceConverse.jc_exact and
     GovernanceWFConverse.sn_jc_exact from jcg_exact (types checked against the originals).

   Normal forms with a non-empty buffer.
   - gnf_iff: (sigma, B) is a normal form IFF sigma is not invalid (~ ~ valid sigma) and every
     event of B is disabled at (sigma, B). The buffer need not be empty: a normal form may hold
     stuck events (stuck_nf). Uniqueness of normal forms is uniqueness of the pair (state,
     residual buffer), so a run that strands an event and a run that fires it end in different
     normal forms even when their states would agree.
   - free_nf_empty: under free delivery no event is ever stuck: every normal form has an empty
     buffer. Stuck events are a feature of guarded or causal enabledness.

   Counterexample: JC is not sufficient without enabled_after_comp (the dc_ definitions).
   A payment is Pending (invalid); compensation cancels it (Cancelled, valid). The event Settle
   is guarded: it may not fire on a cancelled payment. Settle moves any state to Settled. JC holds
   at every configuration (rho* (apply Settle x) = Settled for every x), yet from
   (Pending, [Settle]) there are two normal forms: (Settled, []) and (Cancelled, [Settle]), the
   second with Settle stuck. dc_jc_insufficient states it; dc_eac_fails: compensation disables
   Settle; dc_not_jcg: JC' fails, as jcg_exact requires. With the guard removed (free delivery,
   the fr_ instance) the same data satisfy enabled_after_comp and are confluent (fr_confluent,
   through jc_exact_recovered).

   Non-vacuity of JC' with a disabling compensation (the nv_ definitions). An account Over its
   limit (invalid) is repaired in two compensation steps: first to Locked (invalid: mid-repair,
   under audit), then to Ok. The event Reset is guarded off while Locked (applied there it would
   produce a Torn snapshot); otherwise it resets to Ok. Compensation Over -> Locked disables Reset
   and Locked -> Ok enables it again (nv_disables, nv_enables). JC' holds at every configuration
   (nv_jcg), so every configuration is confluent (nv_confluent, nv_unique). The old JC FAILS at
   (Over, [Reset]) (nv_not_jc): it asks to join with rho* (apply Reset Locked) = Torn, which no
   run reaches. So without enabled_after_comp, JC is neither sufficient (dc) nor necessary (nv).
   nv_jcsplit: the split form holds as well (enabledness there is decidable). *)

Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.GovernanceWFConverse.
From Coq Require Import List Arith Lia.
Import ListNotations.

(* ============================================================================================ *)
(* 1. The general system: JC' and its exactness                                                 *)
(* ============================================================================================ *)

Section General.
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

  (* The hypothesis this file removes, named for the reduction theorems. *)
  Definition eac : Prop := forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  (* JC': every critical pair of the general system, at every configuration reachable from c0.
     The event/compensation clause joins with the compensation successor (rho sigma, B) itself,
     whether or not compensation disables e. *)
  Definition JCg (c0 : State * list Event) : Prop :=
    forall sigma B, star gstep c0 (sigma, B) ->
      (forall e1 e2, In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
         joinable gstep (rho_star (apply e1 sigma), rm e1 B) (rho_star (apply e2 sigma), rm e2 B)) /\
      (forall e, ~ valid sigma -> In e B -> enabled e sigma B ->
         joinable gstep (rho_star (apply e sigma), rm e B) (rho sigma, B)).

  Lemma eg_apply_norm : forall sigma B e, In e B -> enabled e sigma B ->
    star gstep (sigma, B) (rho_star (apply e sigma), rm e B).
  Proof.
    intros. apply (Governance.apply_then_normalize event_eq_dec apply rho rho_star valid enabled
                     rho_star_reach); assumption.
  Qed.

  Lemma eg_join_back : forall x x' y y', star gstep x x' -> star gstep y y' ->
    joinable gstep x' y' -> joinable gstep x y.
  Proof.
    intros x x' y y' Sx Sy [w [A1 A2]]. exists w. split; eapply star_trans; eassumption.
  Qed.

  Lemma eg_join_sym : forall x y, joinable gstep x y -> joinable gstep y x.
  Proof. intros x y [w [A1 A2]]. exists w. split; assumption. Qed.

  (* Confluence from c0 gives JC', for any enabledness and with no termination hypothesis. *)
  Lemma cr_jcg : forall c0, CR gstep c0 -> JCg c0.
  Proof.
    intros c0 H sigma B Hr. split.
    - intros e1 e2 Hin1 Hin2 Hen1 Hen2 _. apply H.
      + eapply star_trans; [exact Hr |]. apply eg_apply_norm; assumption.
      + eapply star_trans; [exact Hr |]. apply eg_apply_norm; assumption.
    - intros e Hinv Hin Hen. apply H.
      + eapply star_trans; [exact Hr |]. apply eg_apply_norm; assumption.
      + eapply star_trans; [exact Hr |]. apply star_one. apply Governance.st_comp. exact Hinv.
  Qed.

  (* The exact condition: for any enabledness and any c0 from which the system terminates,
     confluence from c0 IFF JC' c0. *)
  Theorem jcg_exact : forall c0, SN gstep c0 -> (CR gstep c0 <-> JCg c0).
  Proof.
    intros c0 Hsn. split; [apply cr_jcg |].
    intros HJ. apply (newman_on gstep (fun c => star gstep c0 c)).
    - intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
    - intros [sigma B] X1 X2 Hr H1 H2.
      destruct (HJ sigma B Hr) as [J1 J2].
      inversion H1 as [s1 B1 e1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst.
      + inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
        * destruct (event_eq_dec e1 e2) as [-> | Hne].
          -- exists (apply e2 sigma, rm e2 B). split; apply star_refl.
          -- apply (eg_join_back _ _ _ _ (rho_star_reach _ _) (rho_star_reach _ _)).
             apply J1; assumption.
        * apply (eg_join_back _ _ _ _ (rho_star_reach _ _) (star_refl _ _)).
          apply J2; assumption.
      + inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
        * apply eg_join_sym.
          apply (eg_join_back _ _ _ _ (rho_star_reach _ _) (star_refl _ _)).
          apply J2; assumption.
        * exists (rho sigma, B). split; apply star_refl.
    - intros x Hx. exact (SN_star_closed gstep c0 x Hx Hsn).
    - apply star_refl.
  Qed.

  Corollary jcg_unique_normal_forms : forall c0, SN gstep c0 -> JCg c0 -> UN gstep c0.
  Proof. intros c0 Hsn H. apply CR_UN. apply (proj2 (jcg_exact c0 Hsn)). exact H. Qed.

  (* JC' is exactly joinability of every critical pair at every configuration reachable from c0. *)
  Definition LCreach (c0 : State * list Event) : Prop :=
    forall x y z, star gstep c0 x -> gstep x y -> gstep x z -> joinable gstep y z.

  Theorem cr_iff_critical : forall c0, SN gstep c0 -> (CR gstep c0 <-> LCreach c0).
  Proof.
    intros c0 Hsn. split.
    - intros H x y z Hx Hy Hz. apply H.
      + eapply star_trans; [exact Hx | apply star_one; exact Hy].
      + eapply star_trans; [exact Hx | apply star_one; exact Hz].
    - intros HL. apply (newman_on gstep (fun c => star gstep c0 c)).
      + intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
      + exact HL.
      + intros x Hx. exact (SN_star_closed gstep c0 x Hx Hsn).
      + apply star_refl.
  Qed.

  Theorem jcg_iff_critical : forall c0, SN gstep c0 -> (JCg c0 <-> LCreach c0).
  Proof.
    intros c0 Hsn. rewrite <- (jcg_exact c0 Hsn). apply cr_iff_critical. exact Hsn.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* Normal forms of the general system: the buffer may be non-empty.                           *)
  (* ------------------------------------------------------------------------------------------ *)

  Theorem gnf_iff : forall sigma B,
    normal_form gstep (sigma, B) <->
    (~ ~ valid sigma) /\ (forall e, In e B -> ~ enabled e sigma B).
  Proof.
    intros sigma B. split.
    - intros N. split.
      + intros Hinv. apply N. exists (rho sigma, B). apply Governance.st_comp. exact Hinv.
      + intros e Hin Hen. apply N. exists (apply e sigma, rm e B).
        apply Governance.st_apply; assumption.
    - intros [Hv He] [y Hy].
      inversion Hy as [s B' e Hin Hen E1 E2 | s B' Hinv E1 E2]; subst.
      + exact (He e Hin Hen).
      + exact (Hv Hinv).
  Qed.

  (* A stuck normal form: no step applies, yet events remain buffered. *)
  Definition stuck_nf (c : State * list Event) : Prop := normal_form gstep c /\ snd c <> [].

  Lemma stuck_nf_iff : forall sigma B,
    stuck_nf (sigma, B) <->
    (~ ~ valid sigma) /\ B <> [] /\ (forall e, In e B -> ~ enabled e sigma B).
  Proof.
    intros sigma B. unfold stuck_nf. simpl. rewrite gnf_iff. tauto.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The split form: JC's clause where e persists, the direct join where compensation disables. *)
  (* ------------------------------------------------------------------------------------------ *)

  Definition JCsplit (c0 : State * list Event) : Prop :=
    forall sigma B, star gstep c0 (sigma, B) ->
      (forall e1 e2, In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
         joinable gstep (rho_star (apply e1 sigma), rm e1 B) (rho_star (apply e2 sigma), rm e2 B)) /\
      (* compensation keeps e enabled: JC's clause *)
      (forall e, ~ valid sigma -> In e B -> enabled e sigma B -> enabled e (rho sigma) B ->
         joinable gstep (rho_star (apply e sigma), rm e B) (rho_star (apply e (rho sigma)), rm e B)) /\
      (* compensation disables e: join with the compensation successor *)
      (forall e, ~ valid sigma -> In e B -> enabled e sigma B -> ~ enabled e (rho sigma) B ->
         joinable gstep (rho_star (apply e sigma), rm e B) (rho sigma, B)).

  (* Enabledness after compensation is decided (at invalid states, for enabled events). *)
  Definition emloc : Prop :=
    forall sigma B e, ~ valid sigma -> enabled e sigma B ->
      enabled e (rho sigma) B \/ ~ enabled e (rho sigma) B.

  Lemma eac_emloc : eac -> emloc.
  Proof. intros H sigma B e _ Hen. left. exact (H sigma B e Hen). Qed.

  Lemma jcsplit_jcg : emloc -> forall c0, JCsplit c0 -> JCg c0.
  Proof.
    intros Hem c0 HJ sigma B Hr. destruct (HJ sigma B Hr) as [J1 [J3 J4]]. split; [exact J1 |].
    intros e Hinv Hin Hen. destruct (Hem sigma B e Hinv Hen) as [Hen' | Hdis].
    - apply (eg_join_back _ _ _ _ (star_refl _ _) (eg_apply_norm (rho sigma) B e Hin Hen')).
      apply J3; assumption.
    - apply J4; assumption.
  Qed.

  Lemma jcg_jcsplit : forall c0, SN gstep c0 -> JCg c0 -> JCsplit c0.
  Proof.
    intros c0 Hsn HJ. pose proof (proj2 (jcg_exact c0 Hsn) HJ) as HC.
    intros sigma B Hr. destruct (HJ sigma B Hr) as [J1 J2].
    split; [exact J1 | split].
    - intros e Hinv Hin Hen Hen'. apply HC.
      + eapply star_trans; [exact Hr |]. apply eg_apply_norm; assumption.
      + eapply star_trans; [exact Hr |]. eapply star_step; [apply Governance.st_comp; exact Hinv |].
        apply eg_apply_norm; assumption.
    - intros e Hinv Hin Hen _. apply J2; assumption.
  Qed.

  Theorem jcsplit_exact : forall c0, SN gstep c0 -> emloc -> (CR gstep c0 <-> JCsplit c0).
  Proof.
    intros c0 Hsn Hem. rewrite (jcg_exact c0 Hsn). split.
    - apply jcg_jcsplit. exact Hsn.
    - apply jcsplit_jcg. exact Hem.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* Reduction to JC under enabled_after_comp.                                                  *)
  (* ------------------------------------------------------------------------------------------ *)

  Local Notation JC := (GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled).

  (* Under enabled_after_comp the disabled clause is vacuous: JCsplit is JC, with no termination
     hypothesis. *)
  Theorem jcsplit_iff_jc : eac -> forall c0, JCsplit c0 <-> JC c0.
  Proof.
    intros Heac c0. split.
    - intros HJ sigma B Hr. destruct (HJ sigma B Hr) as [J1 [J3 _]]. split; [exact J1 |].
      intros e Hinv Hin Hen. apply J3; [exact Hinv | exact Hin | exact Hen | apply Heac; exact Hen].
    - intros HJ sigma B Hr. destruct (HJ sigma B Hr) as [J1 J2].
      split; [exact J1 | split].
      + intros e Hinv Hin Hen _. apply J2; assumption.
      + intros e _ _ Hen Hdis. exfalso. apply Hdis. apply Heac. exact Hen.
  Qed.

  Theorem jc_jcg : eac -> forall c0, JC c0 -> JCg c0.
  Proof.
    intros Heac c0 H. apply (jcsplit_jcg (eac_emloc Heac)).
    apply (proj2 (jcsplit_iff_jc Heac c0)). exact H.
  Qed.

  Theorem jcg_iff_jc : eac -> forall c0, SN gstep c0 -> (JCg c0 <-> JC c0).
  Proof.
    intros Heac c0 Hsn. split.
    - intros H. apply (proj1 (jcsplit_iff_jc Heac c0)). apply jcg_jcsplit; assumption.
    - apply jc_jcg. exact Heac.
  Qed.

  (* GovernanceWFConverse.sn_jc_exact, rederived from jcg_exact. *)
  Corollary sn_jc_exact_recovered : eac ->
    forall c0, SN gstep c0 -> (CR gstep c0 <-> JC c0).
  Proof.
    intros Heac c0 Hsn. rewrite (jcg_exact c0 Hsn). apply jcg_iff_jc; assumption.
  Qed.
End General.

(* Free delivery never strands an event: every normal form has an empty buffer. *)
Theorem free_nf_empty :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho : State -> State) (valid : State -> Prop) sigma B,
  normal_form (Governance.step event_eq_dec apply rho valid (free_enabled (State:=State)))
              (sigma, B) -> B = [].
Proof.
  intros State Event dec apply rho valid sigma [| e B] N; [reflexivity |].
  exfalso. apply N. eexists. apply Governance.st_apply; left; reflexivity.
Qed.

(* GovernanceConverse.jc_exact (nat potential), rederived from jcg_exact. *)
Corollary jc_exact_recovered :
  forall {State Event : Type} (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
    (apply : Event -> State -> State) (rho rho_star : State -> State) (valid : State -> Prop)
    (Phi : State -> nat) (enabled : Event -> State -> list Event -> Prop),
  (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
  (forall sigma B, star (Governance.step event_eq_dec apply rho valid enabled)
                        (sigma, B) (rho_star sigma, B)) ->
  (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
  forall c0 : Governance.Config,
  CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
  GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled c0.
Proof.
  intros State Event dec apply rho rho_star valid Phi enabled wfc reach Heac c0.
  apply (sn_jc_exact_recovered dec apply rho rho_star valid enabled reach Heac c0).
  exact (Governance.terminating dec apply rho valid Phi enabled wfc c0).
Qed.

(* The recovered statements have exactly the types of the originals. *)
Check (@jc_exact_recovered : ltac:(let T := type of (@GovernanceConverse.jc_exact) in exact T)).
Check (@GovernanceConverse.jc_exact : ltac:(let T := type of (@jc_exact_recovered) in exact T)).
Check (@sn_jc_exact_recovered
         : forall (State Event : Type) (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
             (apply : Event -> State -> State) (rho rho_star : State -> State)
             (valid : State -> Prop) (enabled : Event -> State -> list Event -> Prop),
           (forall sigma B, star (Governance.step event_eq_dec apply rho valid enabled)
                                 (sigma, B) (rho_star sigma, B)) ->
           (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
           forall c0, SN (Governance.step event_eq_dec apply rho valid enabled) c0 ->
           (CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
            GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled c0)).
Check (@GovernanceWFConverse.sn_jc_exact
         : forall (State Event : Type) (event_eq_dec : forall a b : Event, {a = b} + {a <> b})
             (apply : Event -> State -> State) (rho rho_star : State -> State)
             (valid : State -> Prop) (enabled : Event -> State -> list Event -> Prop),
           (forall sigma B, star (Governance.step event_eq_dec apply rho valid enabled)
                                 (sigma, B) (rho_star sigma, B)) ->
           (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
           forall c0, SN (Governance.step event_eq_dec apply rho valid enabled) c0 ->
           (CR (Governance.step event_eq_dec apply rho valid enabled) c0 <->
            GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled c0)).

(* ============================================================================================ *)
(* 2. Counterexample: JC holds everywhere, compensation disables Settle, two normal forms        *)
(* ============================================================================================ *)

Inductive dcst := Pending | Cancelled | Settled.
Inductive dcev := Settle.

Definition dcev_eq_dec : forall a b : dcev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition dc_apply (_ : dcev) (_ : dcst) : dcst := Settled.
Definition dc_rho (s : dcst) : dcst := match s with Pending => Cancelled | x => x end.
Definition dc_rho_star := dc_rho.
Definition dc_valid (s : dcst) : Prop := s <> Pending.
Definition dc_Phi (s : dcst) : nat := match s with Pending => 1 | _ => 0 end.
(* The guard: Settle may not fire on a cancelled payment. *)
Definition dc_enabled (_ : dcev) (s : dcst) (_ : list dcev) : Prop := s <> Cancelled.

Definition dc_step := Governance.step dcev_eq_dec dc_apply dc_rho dc_valid dc_enabled.
Definition dc_start : dcst * list dcev := (Pending, [Settle]).

Lemma dc_wfc : forall s, ~ dc_valid s -> dc_Phi (dc_rho s) < dc_Phi s.
Proof.
  intros [| |] H; simpl; try lia; exfalso; apply H; discriminate.
Qed.

Lemma dc_reach : forall s B, star dc_step (s, B) (dc_rho_star s, B).
Proof.
  intros [| |] B; simpl; [| apply star_refl | apply star_refl].
  apply star_one. apply Governance.st_comp. intro H. apply H. reflexivity.
Qed.

Lemma dc_sn : forall c, SN dc_step c.
Proof.
  exact (Governance.terminating dcev_eq_dec dc_apply dc_rho dc_valid dc_Phi dc_enabled dc_wfc).
Qed.

Theorem dc_eac_fails :
  dc_enabled Settle Pending [Settle] /\ ~ dc_enabled Settle (dc_rho Pending) [Settle] /\
  ~ eac dc_rho dc_enabled.
Proof.
  split; [discriminate | split].
  - intro H. apply H. reflexivity.
  - intros H. apply (H Pending [Settle] Settle); [discriminate | reflexivity].
Qed.

(* JC holds at every configuration: rho* (apply Settle x) = Settled for every x. *)
Theorem dc_jc : forall c0,
  GovernanceConverse.JC dcev_eq_dec dc_apply dc_rho dc_rho_star dc_valid dc_enabled c0.
Proof.
  intros c0 sigma B _. split.
  - intros [] [] _ _ _ _ Hne. exfalso. apply Hne. reflexivity.
  - intros [] _ _ _. exists (Settled, Governance.remove1 dcev_eq_dec Settle B).
    split; apply star_refl.
Qed.

Lemma dc_nf_settled : normal_form dc_step (Settled, []).
Proof.
  apply (gnf_iff dcev_eq_dec dc_apply dc_rho dc_valid dc_enabled). split.
  - intros H. apply H. discriminate.
  - intros e [].
Qed.

(* Cancelled with Settle still buffered: a stuck normal form. *)
Theorem dc_stuck : stuck_nf dcev_eq_dec dc_apply dc_rho dc_valid dc_enabled (Cancelled, [Settle]).
Proof.
  apply (stuck_nf_iff dcev_eq_dec dc_apply dc_rho dc_valid dc_enabled). split; [| split].
  - intros H. apply H. discriminate.
  - discriminate.
  - intros e _ H. apply H. reflexivity.
Qed.

Theorem dc_two_normal_forms :
  star dc_step dc_start (Settled, []) /\ normal_form dc_step (Settled, []) /\
  star dc_step dc_start (Cancelled, [Settle]) /\ normal_form dc_step (Cancelled, [Settle]) /\
  (Settled, @nil dcev) <> (Cancelled, [Settle]).
Proof.
  split; [| split; [exact dc_nf_settled | split; [| split; [exact (proj1 dc_stuck) | discriminate]]]].
  - apply star_one. unfold dc_start. pose proof (Governance.st_apply dcev_eq_dec dc_apply dc_rho
      dc_valid dc_enabled Pending [Settle] Settle (or_introl eq_refl)) as H.
    simpl in H. apply H. discriminate.
  - apply star_one. apply Governance.st_comp. intro H. apply H. reflexivity.
Qed.

Theorem dc_not_cr : ~ CR dc_step dc_start.
Proof.
  intros H. destruct dc_two_normal_forms as [S1 [N1 [S2 [N2 D]]]].
  apply D. exact (CR_UN dc_step dc_start H _ _ S1 N1 S2 N2).
Qed.

(* The old JC holds, compensation disables an enabled event, and confluence fails. *)
Theorem dc_jc_insufficient :
  GovernanceConverse.JC dcev_eq_dec dc_apply dc_rho dc_rho_star dc_valid dc_enabled dc_start /\
  ~ eac dc_rho dc_enabled /\
  ~ CR dc_step dc_start /\
  ~ UN dc_step dc_start.
Proof.
  split; [apply dc_jc | split; [exact (proj2 (proj2 dc_eac_fails)) | split; [exact dc_not_cr |]]].
  intros H. destruct dc_two_normal_forms as [S1 [N1 [S2 [N2 D]]]]. exact (D (H _ _ S1 N1 S2 N2)).
Qed.

(* JC' fails, as jcg_exact requires: the event/compensation pair at the start is not joinable. *)
Theorem dc_not_jcg : ~ JCg dcev_eq_dec dc_apply dc_rho dc_rho_star dc_valid dc_enabled dc_start.
Proof.
  intros H. apply dc_not_cr.
  apply (proj2 (jcg_exact dcev_eq_dec dc_apply dc_rho dc_rho_star dc_valid dc_enabled dc_reach
                  dc_start (dc_sn dc_start))).
  exact H.
Qed.

(* The same data with the guard removed: free delivery, enabled_after_comp holds, confluent. *)
Definition fr_step := Governance.step dcev_eq_dec dc_apply dc_rho dc_valid (free_enabled (State:=dcst)).

Lemma fr_reach : forall s B, star fr_step (s, B) (dc_rho_star s, B).
Proof.
  intros [| |] B; simpl; [| apply star_refl | apply star_refl].
  apply star_one. apply Governance.st_comp. intro H. apply H. reflexivity.
Qed.

Theorem fr_confluent : forall c, CR fr_step c.
Proof.
  intros c. apply (proj2 (jc_exact_recovered dcev_eq_dec dc_apply dc_rho dc_rho_star dc_valid dc_Phi
                           (free_enabled (State:=dcst)) dc_wfc fr_reach (fun _ _ _ H => H) c)).
  intros sigma B _. split.
  - intros [] [] _ _ _ _ Hne. exfalso. apply Hne. reflexivity.
  - intros [] _ _ _. exists (Settled, Governance.remove1 dcev_eq_dec Settle B).
    split; apply star_refl.
Qed.

(* ============================================================================================ *)
(* 3. Non-vacuity: compensation disables (and re-enables) Reset, JC' holds, JC fails            *)
(* ============================================================================================ *)

Inductive nvst := Ok | Locked | Over | Torn.
Inductive nvev := Reset.

Definition nvev_eq_dec : forall a b : nvev, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition nv_apply (_ : nvev) (s : nvst) : nvst := match s with Locked => Torn | _ => Ok end.
Definition nv_rho (s : nvst) : nvst := match s with Over => Locked | Locked => Ok | x => x end.
Definition nv_rho_star (s : nvst) : nvst := match s with Torn => Torn | _ => Ok end.
Definition nv_valid (s : nvst) : Prop := s = Ok \/ s = Torn.
Definition nv_Phi (s : nvst) : nat := match s with Over => 2 | Locked => 1 | _ => 0 end.
(* The guard: Reset may not fire while the account is locked for audit. *)
Definition nv_enabled (_ : nvev) (s : nvst) (_ : list nvev) : Prop := s <> Locked.

Definition nv_step := Governance.step nvev_eq_dec nv_apply nv_rho nv_valid nv_enabled.
Definition nv_start : nvst * list nvev := (Over, [Reset]).

Lemma nv_inv_ok : ~ ~ nv_valid Ok.
Proof. intros H. apply H. left. reflexivity. Qed.

Lemma nv_wfc : forall s, ~ nv_valid s -> nv_Phi (nv_rho s) < nv_Phi s.
Proof.
  intros [| | |] H; simpl; try lia; exfalso; apply H; [left | right]; reflexivity.
Qed.

Lemma nv_locked_invalid : ~ nv_valid Locked.
Proof. intros [H | H]; discriminate H. Qed.

Lemma nv_over_invalid : ~ nv_valid Over.
Proof. intros [H | H]; discriminate H. Qed.

Lemma nv_reach : forall s B, star nv_step (s, B) (nv_rho_star s, B).
Proof.
  intros [| | |] B; simpl; try apply star_refl.
  - apply star_one. apply Governance.st_comp. exact nv_locked_invalid.
  - eapply star_step; [apply Governance.st_comp; exact nv_over_invalid |].
    apply star_one. apply Governance.st_comp. exact nv_locked_invalid.
Qed.

Lemma nv_sn : forall c, SN nv_step c.
Proof.
  exact (Governance.terminating nvev_eq_dec nv_apply nv_rho nv_valid nv_Phi nv_enabled nv_wfc).
Qed.

(* Compensation Over -> Locked disables Reset; Locked -> Ok enables it again. *)
Theorem nv_disables : forall B,
  ~ nv_valid Over /\ nv_enabled Reset Over B /\ ~ nv_enabled Reset (nv_rho Over) B.
Proof.
  intros B. split; [exact nv_over_invalid | split; [discriminate |]].
  intros H. apply H. reflexivity.
Qed.

Theorem nv_enables : forall B,
  ~ nv_valid Locked /\ ~ nv_enabled Reset Locked B /\ nv_enabled Reset (nv_rho Locked) B.
Proof.
  intros B. split; [exact nv_locked_invalid | split; [| discriminate]].
  intros H. apply H. reflexivity.
Qed.

Theorem nv_not_eac : ~ eac nv_rho nv_enabled.
Proof.
  intros H. apply (proj2 (proj2 (nv_disables [Reset]))). apply H. discriminate.
Qed.

(* JC' at every configuration. *)
Theorem nv_jcg : forall c0, JCg nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled c0.
Proof.
  intros c0 sigma B _. split.
  - intros [] [] _ _ _ _ Hne. exfalso. apply Hne. reflexivity.
  - intros [] Hinv Hin Hen.
    destruct sigma; [exfalso; apply Hinv; left; reflexivity | exfalso; apply Hen; reflexivity | |
                     exfalso; apply Hinv; right; reflexivity].
    (* sigma = Over: compensate to Locked, then to Ok, then fire Reset. *)
    exists (Ok, Governance.remove1 nvev_eq_dec Reset B). split; [apply star_refl |].
    simpl. eapply star_step; [apply Governance.st_comp; exact nv_locked_invalid |].
    apply star_one.
    exact (Governance.st_apply nvev_eq_dec nv_apply nv_rho nv_valid nv_enabled Ok B Reset Hin
             ltac:(discriminate)).
Qed.

Theorem nv_confluent : forall c, CR nv_step c.
Proof.
  intros c. apply (proj2 (jcg_exact nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled
                           nv_reach c (nv_sn c))).
  apply nv_jcg.
Qed.

Theorem nv_unique : forall c, UN nv_step c.
Proof. intros c. apply CR_UN. apply nv_confluent. Qed.

Lemma nv_emloc : emloc nv_rho nv_valid nv_enabled.
Proof.
  intros sigma B e _ _. unfold nv_enabled.
  destruct (nv_rho sigma); [left; discriminate | right; intros H; apply H; reflexivity
                            | left; discriminate | left; discriminate].
Qed.

Theorem nv_jcsplit : forall c0,
  JCsplit nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled c0.
Proof.
  intros c0. apply (proj1 (jcsplit_exact nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid
                             nv_enabled nv_reach c0 (nv_sn c0) nv_emloc)).
  apply nv_confluent.
Qed.

Lemma nv_nf_ok : normal_form nv_step (Ok, []).
Proof.
  apply (gnf_iff nvev_eq_dec nv_apply nv_rho nv_valid nv_enabled). split.
  - exact nv_inv_ok.
  - intros e [].
Qed.

Lemma nv_nf_torn : normal_form nv_step (Torn, []).
Proof.
  apply (gnf_iff nvev_eq_dec nv_apply nv_rho nv_valid nv_enabled). split.
  - intros H. apply H. right. reflexivity.
  - intros e [].
Qed.

(* The old JC fails at the start: it asks to join with rho* (apply Reset Locked) = Torn, a
   normal form no run from the start reaches. So JC is not necessary without enabled_after_comp. *)
Theorem nv_not_jc :
  ~ GovernanceConverse.JC nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled nv_start.
Proof.
  intros H. destruct (H Over [Reset] (star_refl _ _)) as [_ J2].
  destruct (J2 Reset nv_over_invalid (or_introl eq_refl) ltac:(discriminate)) as [w [A1 A2]].
  simpl in A1, A2.
  rewrite <- (star_from_nf nv_step _ _ nv_nf_ok A1) in A2.
  pose proof (star_from_nf nv_step _ _ nv_nf_torn A2) as E. discriminate E.
Qed.

(* Summary: a disabling compensation, JC' holds, confluence holds, the old JC fails. *)
Theorem nv_jc_not_necessary :
  ~ eac nv_rho nv_enabled /\
  JCg nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled nv_start /\
  CR nv_step nv_start /\
  ~ GovernanceConverse.JC nvev_eq_dec nv_apply nv_rho nv_rho_star nv_valid nv_enabled nv_start.
Proof.
  split; [exact nv_not_eac | split; [apply nv_jcg | split; [apply nv_confluent | exact nv_not_jc]]].
Qed.
