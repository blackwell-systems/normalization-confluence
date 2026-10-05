(* CanonicalInstances.v: the six validation criteria for the canonical-execution kernel
   (CanonicalExecution.v). EXPERIMENTAL: validation in progress, do not cite yet. Axiom-free.

   Each criterion rederives an existing exact theorem through the kernel. The kernel theorem
   used, the instance-specific glue, and the outcome (PASS, PARTIAL, LEAK) are recorded at each
   section head and in docs/canonical-execution.md.

   A. jc_exact_kernel, jcg_exact_kernel: GovernanceConverse.jc_exact and
      EnabledAfterComp.jcg_exact through classified_peak_exact. Event/compensation peaks are
      StatePeaks, distinct event/event peaks are HistoryPeaks, compensation/compensation peaks
      (and an event against itself) are trivial, StructuralPeak is empty.
   B. causal_exact_kernel: GovernanceConverse.causal_exact through history_descent_exact. The
      admissible executions are the causally consistent orders, the generators are adjacent
      concurrent swaps at a causally consistent prefix (causal_adequate, from
      CausalReplay.causal_tequiv, GovernanceConverse.tequiv_causal and causal_swap).
   C. causal_alo_exact_idem_kernel, causal_alo_exact_kernel, alo_exact_kernel: the at-least-once
      theorems through history_descent_exact. The admissible executions are the causally
      consistent at-least-once deliveries; the generators are the concurrent swaps of B plus one
      duplicate generator at its LEGAL LANDING POINT: dup_idem (a copy right after its first
      delivery, at an exactly-once causal prefix) gives IdemAt, dup_abs (a copy at the end of an
      exactly-once causal run that holds it and none of its causal successors) gives AbsorbAt.
      Adequacy (alo_adequate) is semantics-free combinatorics of words.
   D. fed_exact_kernel: FederationEventsConverse.fed_exact. The history layer (trace
      convergence <-> commutation at each reachable independent swap) goes through
      history_descent_exact; C1R1 is reachable state descent of the overwrite canonicalizer
      N_{j,z} := f j z (c1r1_state_descent), C2R is the one-swap history condition of the local
      governed run (c2at_history). Splitting the swap condition into C1R1 and C2R needs the
      model's locality lemma (FederationEventsConverse.gc_iff_reach). XU, XUat (hence XUR) and
      XUc are state descent on larger exposure domains (xu_state_descent, xuat_state_descent,
      xuc_state_descent).
   E. pjc_exact_kernel, stream_exact_kernel, stream_free_history: the processor discipline
      normalizes before it applies, so its StatePeak class is empty (stream_state_peaks_empty)
      and confluence is the HistoryPeak condition PJC alone; under free delivery stream agreement
      is history descent of the governed run from rho* s0 over duplicate-free reorderings.
   F. flush_fed_iff_kernel: DistributedCyclesExact.flush_fed_iff as an instance of
      CanonicalExecution.esh_exact (Settlement = FlushR, CanonicalFidelity = NoGhostR,
      StateDescentR = XUcR, HistoryDescentC = FMConv (Nc s0)); it needs none of the order
      hypotheses of DistributedCyclesExact's section. The ghost family, in E/S/H terms:
      flip_esh (Settlement fails alone), ghost_esh (CanonicalFidelity fails alone),
      conv_ghost_esh (H and convergence without E: Fidelity fails), copy_xu_esh (S fails alone),
      fm_conv_esh (H fails alone). *)

Require Import NC.Newman NC.CanonicalExecution.
Require Import NC.Trace NC.CausalReplay.
Require NC.Governance NC.GovernanceConverse NC.GovernanceWFConverse NC.EnabledAfterComp.
Require NC.AtLeastOnce NC.AtLeastOnceExact.
Require NC.GovernanceCausal NC.Stream NC.StreamExact.
Require NC.FederationEvents NC.FederationEventsConverse.
Require NC.Federation NC.FederationEventsCycles NC.FederationEventsCyclesCheck.
Require NC.DistributedExact NC.DistributedCycles NC.DistributedCyclesExact.
From Coq Require Import List Arith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* ============================================================================================ *)
(* A. The single-registry rewrite system: jc_exact and jcg_exact through classified peaks       *)
(* ============================================================================================ *)

Section GovPeaks.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho rho_star : State -> State.
  Variable valid : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.

  Local Notation gstep := (Governance.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (Governance.remove1 event_eq_dec).
  Hypothesis rho_star_reach : forall sigma B, star gstep (sigma, B) (rho_star sigma, B).

  Lemma gp_an : forall sigma B e, In e B -> enabled e sigma B ->
    star gstep (sigma, B) (rho_star (apply e sigma), rm e B).
  Proof.
    intros. apply (Governance.apply_then_normalize event_eq_dec apply rho rho_star valid enabled
                     rho_star_reach); assumption.
  Qed.

  (* StatePeak: an event step against a compensation step, in either orientation. *)
  Definition gov_state_peak (x y z : State * list Event) : Prop :=
    exists sigma B e, x = (sigma, B) /\ ~ valid sigma /\ In e B /\ enabled e sigma B /\
      ((y = (apply e sigma, rm e B) /\ z = (rho sigma, B)) \/
       (y = (rho sigma, B) /\ z = (apply e sigma, rm e B))).

  (* HistoryPeak: two distinct event steps. *)
  Definition gov_history_peak (x y z : State * list Event) : Prop :=
    exists sigma B e1 e2, x = (sigma, B) /\ e1 <> e2 /\ In e1 B /\ In e2 B /\
      enabled e1 sigma B /\ enabled e2 sigma B /\
      y = (apply e1 sigma, rm e1 B) /\ z = (apply e2 sigma, rm e2 B).

  Definition gov_cls (x y z : State * list Event) (k : PeakKind) : Prop :=
    match k with
    | StatePeak => gov_state_peak x y z
    | HistoryPeak => gov_history_peak x y z
    | StructuralPeak => False
    end.

  (* Every reachable non-trivial peak is classified (compensation/compensation is trivial). *)
  Lemma gov_complete : forall c0, ClassComplete gstep c0 gov_cls.
  Proof.
    intros c0 [sigma B] y z _ H1 H2.
    inversion H1 as [s1 B1 e1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst;
      inversion H2 as [s2 B2 e2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
    - destruct (event_eq_dec e1 e2) as [-> | Hne]; [left; reflexivity |].
      right. exists HistoryPeak, sigma, B, e1, e2. tauto.
    - right. exists StatePeak, sigma, B, e1. tauto.
    - right. exists StatePeak, sigma, B, e2. tauto.
    - left. reflexivity.
  Qed.

  Lemma gov_history_joins : forall c0,
    (forall sigma B, star gstep c0 (sigma, B) ->
       forall e1 e2, In e1 B -> In e2 B -> enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
       joinable gstep (rho_star (apply e1 sigma), rm e1 B) (rho_star (apply e2 sigma), rm e2 B)) ->
    KindJoins gstep c0 gov_cls HistoryPeak.
  Proof.
    intros c0 J x y z Hx _ _ (sigma & B & e1 & e2 & -> & Hne & Hin1 & Hin2 & Hen1 & Hen2 & -> & ->).
    apply (join_back_star gstep _ _ _ _ (rho_star_reach _ _) (rho_star_reach _ _)).
    apply J; assumption.
  Qed.

  (* A StatePeak joins when the event side, repaired, joins a target the compensation side
     reaches (JC: fire the event after compensating; JC': the compensation successor itself). *)
  Lemma gov_state_joins : forall c0 (tgt : State -> list Event -> Event -> State * list Event),
    (forall sigma B e, ~ valid sigma -> In e B -> enabled e sigma B ->
       star gstep (rho sigma, B) (tgt sigma B e)) ->
    (forall sigma B, star gstep c0 (sigma, B) -> forall e, ~ valid sigma -> In e B ->
       enabled e sigma B -> joinable gstep (rho_star (apply e sigma), rm e B) (tgt sigma B e)) ->
    KindJoins gstep c0 gov_cls StatePeak.
  Proof.
    intros c0 tgt Ht J x y z Hx _ _ (sigma & B & e & -> & Hinv & Hin & Hen & [[-> ->] | [-> ->]]).
    - apply (join_back_star gstep _ _ _ _ (rho_star_reach _ _) (Ht sigma B e Hinv Hin Hen)).
      apply J; assumption.
    - apply joinable_sym.
      apply (join_back_star gstep _ _ _ _ (rho_star_reach _ _) (Ht sigma B e Hinv Hin Hen)).
      apply J; assumption.
  Qed.

  (* Criterion A, first half: GovernanceConverse.jc_exact through the kernel. *)
  Theorem jc_exact_kernel : forall (Phi : State -> nat),
    (forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma) ->
    (forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B) ->
    forall c0, CR gstep c0 <-> GovernanceConverse.JC event_eq_dec apply rho rho_star valid enabled c0.
  Proof.
    intros Phi wfc eac c0. split.
    - intros H sigma B Hr. split.
      + intros e1 e2 Hin1 Hin2 Hen1 Hen2 _.
        apply (cr_join_reach gstep c0 H (sigma, B)); [exact Hr | apply gp_an | apply gp_an]; assumption.
      + intros e Hinv Hin Hen. apply (cr_join_reach gstep c0 H (sigma, B)); [exact Hr | apply gp_an; assumption |].
        eapply star_step; [apply Governance.st_comp; exact Hinv |]. apply gp_an; [exact Hin | apply eac; exact Hen].
    - intros HJ. apply (proj2 (classified_peak_exact gstep c0 gov_cls
        (Governance.terminating event_eq_dec apply rho valid Phi enabled wfc c0) (gov_complete c0))).
      split; [| split].
      + apply (gov_state_joins c0 (fun sigma B e => (rho_star (apply e (rho sigma)), rm e B))).
        * intros sigma B e _ Hin Hen. apply gp_an; [exact Hin | apply eac; exact Hen].
        * intros sigma B Hr. exact (proj2 (HJ sigma B Hr)).
      + apply gov_history_joins. intros sigma B Hr. exact (proj1 (HJ sigma B Hr)).
      + apply empty_kind_joins. intros x y z _ _ _ [].
  Qed.

  (* Criterion A, second half: EnabledAfterComp.jcg_exact (no enabled_after_comp). *)
  Theorem jcg_exact_kernel : forall c0, SN gstep c0 ->
    (CR gstep c0 <-> EnabledAfterComp.JCg event_eq_dec apply rho rho_star valid enabled c0).
  Proof.
    intros c0 Hsn. split.
    - intros H sigma B Hr. split.
      + intros e1 e2 Hin1 Hin2 Hen1 Hen2 _.
        apply (cr_join_reach gstep c0 H (sigma, B)); [exact Hr | apply gp_an | apply gp_an]; assumption.
      + intros e Hinv Hin Hen. apply (cr_join_reach gstep c0 H (sigma, B)); [exact Hr | apply gp_an; assumption |].
        apply star_one. apply Governance.st_comp. exact Hinv.
    - intros HJ. apply (proj2 (classified_peak_exact gstep c0 gov_cls Hsn (gov_complete c0))).
      split; [| split].
      + apply (gov_state_joins c0 (fun sigma B _ => (rho sigma, B))); [intros; apply star_refl |].
        intros sigma B Hr. exact (proj2 (HJ sigma B Hr)).
      + apply gov_history_joins. intros sigma B Hr. exact (proj1 (HJ sigma B Hr)).
      + apply empty_kind_joins. intros x y z _ _ _ [].
  Qed.
End GovPeaks.

(* ============================================================================================ *)
(* Words: concurrent swaps at a causally consistent prefix connect causal permutations          *)
(* ============================================================================================ *)

Section CausalWords.
  Context {E : Type}.
  Variable hb : E -> E -> Prop.
  Variable Ev : E -> Prop.

  (* The swap generator: adjacent concurrent events, after an exactly-once causal prefix. *)
  Definition cswap (t u : list E) : Prop :=
    exists p a b r, concurrent hb a b /\ causal hb (p ++ [a; b]) /\
      t = p ++ a :: b :: r /\ u = p ++ b :: a :: r.

  Lemma cswap_perm : forall t u, cswap t u -> Permutation t u.
  Proof.
    intros t u (p & a & b & r & _ & _ & -> & ->). apply Permutation_app_head. apply perm_swap.
  Qed.

  Variable Adm : list E -> Prop.
  Variable G : list E -> list E -> Prop.
  Hypothesis adm_causal : forall o, causal hb o -> Forall Ev o -> Adm o.
  Hypothesis G_swap : forall t u, cswap t u -> G t u.

  Lemma swaps_connect : forall o1 o2, tequiv (concurrent hb) o1 o2 ->
    causal hb o1 -> Forall Ev o1 -> AC Adm G o1 o2.
  Proof.
    intros o1 o2 H.
    induction H as [l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H1 IH1 H2 IH2]; intros Hc Hev.
    - apply ac_refl. apply adm_causal; assumption.
    - assert (Hc' : causal hb (l ++ b :: a :: r))
        by exact (GovernanceConverse.causal_swap hb l a b r (proj1 (proj2 Hab)) Hc).
      apply ac_gen.
      + apply adm_causal; assumption.
      + apply adm_causal; [exact Hc' |].
        exact (Permutation_Forall (Permutation_app_head l (perm_swap b a r)) Hev).
      + apply G_swap. exists l, a, b, r. split; [exact Hab |]. split; [| split; reflexivity].
        apply (GovernanceConverse.causal_prefix hb _ r). rewrite <- app_assoc. exact Hc.
    - apply ac_sym. apply IH.
      + exact (proj2 (GovernanceConverse.tequiv_causal hb l1 l2 H) Hc).
      + exact (Permutation_Forall (Permutation_sym (tequiv_perm _ _ _ H)) Hev).
    - eapply ac_trans; [apply IH1; assumption |]. apply IH2.
      + exact (proj1 (GovernanceConverse.tequiv_causal hb l1 l2 H1) Hc).
      + exact (Permutation_Forall (tequiv_perm _ _ _ H1) Hev).
  Qed.

  Lemma causal_connect : forall o1 o2, causal hb o1 -> causal hb o2 ->
    (forall x, In x o1 <-> In x o2) -> Forall Ev o1 -> AC Adm G o1 o2.
  Proof.
    intros o1 o2 H1 H2 Hs Hev. apply swaps_connect; [| exact H1 | exact Hev].
    apply causal_tequiv; [exact H1 | exact H2 |].
    apply NoDup_Permutation; [exact (proj1 H1) | exact (proj1 H2) | exact Hs].
  Qed.
End CausalWords.

(* ============================================================================================ *)
(* B. Causal delivery: causal_exact through history descent                                     *)
(* ============================================================================================ *)

Section CausalInstance.
  Context {S E : Type}.
  Variable step : E -> S -> S.
  Variable hb : E -> E -> Prop.
  Variable s0 : S.
  Local Notation run := (CausalReplay.run step).

  Lemma causal_adequate : Adequate (causal hb) (cswap hb) (@Permutation E).
  Proof.
    intros t u Ht Hu. split.
    - intros HP. apply (swaps_connect hb (fun _ => True)); [intros o Ho _; exact Ho | intros; assumption
        | apply causal_tequiv; assumption | exact Ht | apply Forall_forall; intros; exact I].
    - intros H. clear Ht Hu. induction H as [t _ | t u _ _ Hg | t u _ IH | t u v _ IH1 _ IH2].
      + apply Permutation_refl.
      + exact (cswap_perm hb t u Hg).
      + apply Permutation_sym. exact IH.
      + eapply Permutation_trans; eassumption.
  Qed.

  (* The generator condition is CCR. *)
  Lemma causal_gen_iff :
    GenDescent (causal hb) (cswap hb) (fun o => run o s0) eq <-> GovernanceConverse.CCR step hb s0.
  Proof.
    split.
    - intros H p a b Hab Hc.
      assert (Hc' : causal hb (p ++ [b; a]))
        by exact (GovernanceConverse.causal_swap hb p a b [] (proj1 (proj2 Hab)) Hc).
      pose proof (H (p ++ [a; b]) (p ++ [b; a]) Hc Hc'
                    (ex_intro _ p (ex_intro _ a (ex_intro _ b (ex_intro _ []
                      (conj Hab (conj Hc (conj eq_refl eq_refl)))))))) as Eq.
      cbv beta in Eq. rewrite !(GovernanceConverse.run_app step) in Eq. exact Eq.
    - intros H t u _ _ (p & a & b & r & Hab & Hc & -> & ->). cbv beta.
      rewrite !(GovernanceConverse.run_app step).
      change (run r (step b (step a (run p s0))) = run r (step a (step b (run p s0)))).
      rewrite (H p a b Hab Hc). reflexivity.
  Qed.

  (* Criterion B: GovernanceConverse.causal_exact through the kernel. *)
  Theorem causal_exact_kernel :
    GovernanceConverse.CausalConv step hb s0 <-> GovernanceConverse.CCR step hb s0.
  Proof.
    rewrite <- causal_gen_iff.
    rewrite <- (history_descent_exact (causal hb) (cswap hb) (@Permutation E) (fun o => run o s0) eq
                  (@eq_refl _) (@eq_sym _) (@eq_trans _) causal_adequate).
    split; intros H; exact H.
  Qed.
End CausalInstance.

(* ============================================================================================ *)
(* C. At-least-once delivery: duplicate generators at their legal landing point                 *)
(* ============================================================================================ *)

Section ALOWords.
  Context {E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable Ev : E -> Prop.
  Variable hb : E -> E -> Prop.
  Hypothesis hb_irrefl : forall x, ~ hb x x.

  Local Notation calo := (AtLeastOnce.causal_alo hb).

  (* Admissible executions: causally consistent at-least-once deliveries over Ev. *)
  Definition alo_adm (d : list E) : Prop := Forall Ev d /\ calo d.
  Definition same_set (t u : list E) : Prop := forall x, In x t <-> In x u.

  (* Duplicate generator, idempotence form: a copy right after its first delivery, which ends an
     exactly-once causally consistent prefix. *)
  Definition dup_idem (t u : list E) : Prop :=
    exists p a r, causal hb (p ++ [a]) /\ t = p ++ a :: a :: r /\ u = p ++ a :: r.

  (* Duplicate generator, absorption form: a copy at the end of an exactly-once causally
     consistent run that contains it and none of its causal successors. *)
  Definition dup_abs (t u : list E) : Prop :=
    exists w a r, causal hb w /\ In a w /\ (forall b, In b w -> ~ hb a b) /\
      t = w ++ a :: r /\ u = w ++ r.

  Definition G_idem (t u : list E) : Prop := cswap hb t u \/ dup_idem t u.
  Definition G_abs (t u : list E) : Prop := cswap hb t u \/ dup_abs t u.

  (* ----- list facts ----- *)

  Lemma calo_snoc : forall l x, calo l -> (forall y, In y l -> ~ hb x y) -> calo (l ++ [x]).
  Proof.
    intros l x Hl Hx a b Hab L R Ed Hb Ha.
    destruct (AtLeastOnceExact.rev_case R) as [-> | [z [R' ->]]]; [destruct Ha |].
    rewrite app_assoc in Ed. apply app_inj_tail in Ed. destruct Ed as [El Ez]. subst l z.
    apply in_app_or in Ha. destruct Ha as [Ha | [<- | []]].
    - exact (Hl a b Hab L R' eq_refl Hb Ha).
    - exact (Hx b (in_or_app _ _ _ (or_introl Hb)) Hab).
  Qed.

  Lemma calo_snoc_inv : forall l x, calo (l ++ [x]) -> calo l /\ (forall y, In y l -> ~ hb x y).
  Proof.
    intros l x H. split; [exact (AtLeastOnce.causal_alo_prefix hb l x H) |].
    intros y Hy Hxy. exact (H x y Hxy l [x] eq_refl Hy (or_introl eq_refl)).
  Qed.

  Lemma prec_app_r : forall (k i : E) l r, prec k i l -> prec k i (l ++ r).
  Proof.
    intros k i l r. induction l as [| y l IH]; simpl; [contradiction |].
    intros [[-> Hi] | H]; [left; split; [reflexivity | apply in_or_app; left; exact Hi]
                          | right; apply IH; exact H].
  Qed.

  Lemma prec_snoc : forall (k i : E) l, In k l -> prec k i (l ++ [i]).
  Proof.
    intros k i l. induction l as [| y l IH]; simpl; [contradiction |].
    intros [-> | H]; [left; split; [reflexivity | apply in_or_app; right; left; reflexivity]
                     | right; apply IH; exact H].
  Qed.

  Lemma causal_snoc : forall w x, causal hb w -> ~ In x w -> (forall b, In b w -> ~ hb x b) ->
    causal hb (w ++ [x]).
  Proof.
    intros w x [Hnd Hc] Hx Hns. split.
    - apply (Permutation_NoDup (Permutation_cons_append w x)). constructor; assumption.
    - intros a b Hab Ha Hb. apply in_app_or in Ha. apply in_app_or in Hb.
      destruct Hb as [Hb | [<- | []]].
      + destruct Ha as [Ha | [<- | []]]; [apply prec_app_r; apply Hc; assumption |].
        exfalso. exact (Hns b Hb Hab).
      + destruct Ha as [Ha | [<- | []]]; [apply prec_snoc; exact Ha | exfalso; exact (hb_irrefl _ Hab)].
  Qed.

  Lemma adm_causal : forall o, causal hb o -> Forall Ev o -> alo_adm o.
  Proof. intros o Hc Hev. split; [exact Hev | exact (AtLeastOnceExact.causal_causal_alo hb o Hc)]. Qed.

  Lemma adm_snoc : forall w x, causal hb w -> Forall Ev w -> Ev x ->
    (forall b, In b w -> ~ hb x b) -> alo_adm (w ++ [x]).
  Proof.
    intros w x Hc Hev Hx Hns. split; [apply Forall_app; split; [exact Hev | constructor; [exact Hx | constructor]] |].
    exact (AtLeastOnceExact.causal_snoc_alo hb w x Hc Hns).
  Qed.

  Lemma forall_set : forall t u, same_set t u -> Forall Ev t -> Forall Ev u.
  Proof.
    intros t u Hs Ht. apply Forall_forall. intros x Hx. rewrite Forall_forall in Ht.
    apply Ht. apply Hs. exact Hx.
  Qed.

  (* ----- adequacy, for any generator set containing the swaps ----- *)

  Section Adequacy.
    Variable G : list E -> list E -> Prop.
    Hypothesis G_swap : forall t u, cswap hb t u -> G t u.
    Hypothesis G_set : forall t u, G t u -> same_set t u.
    Hypothesis G_snoc : forall t u x, G t u -> G (t ++ [x]) (u ++ [x]).
    (* Closing a redelivery of x after an exactly-once causal run w that contains x. *)
    Hypothesis dup_close : forall w x, causal hb w -> In x w -> Forall Ev w ->
      (forall b, In b w -> ~ hb x b) ->
      exists w', causal hb w' /\ same_set (w ++ [x]) w' /\ AC alo_adm G (w ++ [x]) w'.

    Lemma ac_set : forall t u, AC alo_adm G t u -> same_set t u.
    Proof.
      intros t u H. induction H as [t _ | t u _ _ Hg | t u _ IH | t u v _ IH1 _ IH2]; intros z.
      - reflexivity.
      - exact (G_set t u Hg z).
      - symmetry. exact (IH z).
      - rewrite (IH1 z). exact (IH2 z).
    Qed.

    Lemma ac_snoc : forall x, Ev x -> forall t u, AC alo_adm G t u ->
      (forall y, In y t -> ~ hb x y) -> AC alo_adm G (t ++ [x]) (u ++ [x]).
    Proof.
      intros x Hx t u H. induction H as [t [Et Ct] | t u [Et Ct] [Eu Cu] Hg | t u Htu IH
                                         | t u v Htu IH1 Huv IH2]; intros Hns.
      - apply ac_refl. split; [apply Forall_app; split; [exact Et | constructor; [exact Hx | constructor]] |].
        apply calo_snoc; assumption.
      - apply ac_gen; [| | apply G_snoc; exact Hg].
        + split; [apply Forall_app; split; [exact Et | constructor; [exact Hx | constructor]] |].
          apply calo_snoc; assumption.
        + split; [apply Forall_app; split; [exact Eu | constructor; [exact Hx | constructor]] |].
          apply calo_snoc; [exact Cu |]. intros y Hy. apply Hns. apply (G_set t u Hg). exact Hy.
      - apply ac_sym. apply IH. intros y Hy. apply Hns. apply (ac_set t u Htu). exact Hy.
      - eapply ac_trans; [apply IH1; exact Hns |]. apply IH2.
        intros y Hy. apply Hns. apply (ac_set t u Htu). exact Hy.
    Qed.

    Lemma to_causal : forall t, alo_adm t ->
      exists t', causal hb t' /\ same_set t t' /\ AC alo_adm G t t'.
    Proof.
      intros t. induction t as [| x t0 IH] using rev_ind; intros [Ht Ct].
      - exists []. split; [split; [constructor | intros a b _ []] |].
        split; [intros z; reflexivity | apply ac_refl; split; [constructor | exact Ct]].
      - apply Forall_app in Ht. destruct Ht as [Ht0 Hx]. inversion Hx as [| ? ? Hx' _]; subst.
        destruct (calo_snoc_inv t0 x Ct) as [Ct0 Hns].
        destruct (IH (conj Ht0 Ct0)) as [t0' [Hc0 [Hs0 Hac0]]].
        assert (Hns' : forall b, In b t0' -> ~ hb x b) by (intros b Hb; apply Hns; apply Hs0; exact Hb).
        assert (Hev0 : Forall Ev t0') by exact (forall_set t0 t0' Hs0 Ht0).
        assert (Hac1 : AC alo_adm G (t0 ++ [x]) (t0' ++ [x])) by (apply ac_snoc; assumption).
        assert (Hs1 : same_set (t0 ++ [x]) (t0' ++ [x])).
        { intros z. rewrite !in_app_iff. rewrite (Hs0 z). reflexivity. }
        destruct (in_dec dec x t0') as [Hin | Hnin].
        + destruct (dup_close t0' x Hc0 Hin Hev0 Hns') as [w' [Hw' [Hs2 Hac2]]].
          exists w'. split; [exact Hw' |]. split; [intros z; rewrite (Hs1 z); exact (Hs2 z) |].
          eapply ac_trans; eassumption.
        + exists (t0' ++ [x]). split; [apply causal_snoc; assumption |]. split; assumption.
    Qed.

    Theorem alo_adequate : Adequate alo_adm G same_set.
    Proof.
      intros t u Ht Hu. split; [| apply ac_set].
      intros Hs.
      destruct (to_causal t Ht) as [t' [Ct [Hst Hat]]].
      destruct (to_causal u Hu) as [u' [Cu [Hsu Hau]]].
      assert (Hev : Forall Ev t') by exact (forall_set t t' Hst (proj1 Ht)).
      assert (Hm : AC alo_adm G t' u').
      { apply (causal_connect hb Ev alo_adm G adm_causal G_swap t' u' Ct Cu); [| exact Hev].
        intros z. rewrite <- (Hst z), <- (Hsu z). exact (Hs z). }
      eapply ac_trans; [exact Hat |]. eapply ac_trans; [exact Hm |]. apply ac_sym. exact Hau.
    Qed.
  End Adequacy.

  (* ----- the two duplicate generators satisfy the adequacy hypotheses ----- *)

  Lemma G_abs_set : forall t u, G_abs t u -> same_set t u.
  Proof.
    intros t u [Hs | (w & a & r & _ & Ha & _ & -> & ->)].
    - intros z. split; apply Permutation_in; [| apply Permutation_sym]; exact (cswap_perm hb t u Hs).
    - intros z. rewrite !in_app_iff. simpl. split; [| tauto]. intros [H | [<- | H]]; tauto.
  Qed.

  Lemma G_idem_set : forall t u, G_idem t u -> same_set t u.
  Proof.
    intros t u [Hs | (p & a & r & _ & -> & ->)].
    - intros z. split; apply Permutation_in; [| apply Permutation_sym]; exact (cswap_perm hb t u Hs).
    - intros z. rewrite !in_app_iff. simpl. tauto.
  Qed.

  Lemma cswap_snoc : forall t u x, cswap hb t u -> cswap hb (t ++ [x]) (u ++ [x]).
  Proof.
    intros t u x (p & a & b & r & Hab & Hc & -> & ->). exists p, a, b, (r ++ [x]).
    split; [exact Hab |]. split; [exact Hc |]. split; rewrite <- app_assoc; reflexivity.
  Qed.

  Lemma G_abs_snoc : forall t u x, G_abs t u -> G_abs (t ++ [x]) (u ++ [x]).
  Proof.
    intros t u x [Hs | (w & a & r & Hc & Ha & Hn & -> & ->)]; [left; apply cswap_snoc; exact Hs |].
    right. exists w, a, (r ++ [x]). split; [exact Hc |]. split; [exact Ha |]. split; [exact Hn |].
    split; rewrite <- app_assoc; reflexivity.
  Qed.

  Lemma G_idem_snoc : forall t u x, G_idem t u -> G_idem (t ++ [x]) (u ++ [x]).
  Proof.
    intros t u x [Hs | (p & a & r & Hc & -> & ->)]; [left; apply cswap_snoc; exact Hs |].
    right. exists p, a, (r ++ [x]). split; [exact Hc |]. split; rewrite <- app_assoc; reflexivity.
  Qed.

  (* Absorption form: one edge closes the redelivery. *)
  Lemma abs_close : forall w x, causal hb w -> In x w -> Forall Ev w ->
    (forall b, In b w -> ~ hb x b) ->
    exists w', causal hb w' /\ same_set (w ++ [x]) w' /\ AC alo_adm G_abs (w ++ [x]) w'.
  Proof.
    intros w x Hc Hx Hev Hns. exists w. split; [exact Hc |]. split.
    - intros z. rewrite in_app_iff. simpl. split; [intros [H | [<- | []]]; assumption | tauto].
    - apply ac_gen.
      + apply adm_snoc; [exact Hc | exact Hev | rewrite Forall_forall in Hev; exact (Hev x Hx) | exact Hns].
      + apply adm_causal; assumption.
      + right. exists w, x, []. split; [exact Hc |]. split; [exact Hx |]. split; [exact Hns |].
        split; [reflexivity | symmetry; apply app_nil_r].
  Qed.

  (* Idempotence form: the first copy moves right past concurrent events to meet the second. *)
  Lemma move_right : forall x p2 p1, causal hb (p1 ++ x :: p2) -> Forall Ev (p1 ++ x :: p2) ->
    (forall y, In y (p1 ++ x :: p2) -> ~ hb x y) ->
    causal hb (p1 ++ p2 ++ [x]) /\ AC alo_adm G_idem (p1 ++ x :: p2 ++ [x]) (p1 ++ p2 ++ [x; x]).
  Proof.
    intros x p2. induction p2 as [| y p2 IH]; intros p1 Hc Hev Hns.
    - split; [exact Hc |]. apply ac_refl.
      assert (Hx : Ev x) by (rewrite Forall_forall in Hev; apply Hev; apply in_or_app; right; left; reflexivity).
      pose proof (adm_snoc (p1 ++ [x]) x Hc Hev Hx Hns) as H. rewrite <- app_assoc in H. exact H.
    - assert (HP : Permutation (p1 ++ x :: y :: p2) (p1 ++ y :: x :: p2))
        by (apply Permutation_app_head; apply perm_swap).
      assert (Hxy : concurrent hb x y).
      { destruct Hc as [Hnd Hcc]. split; [| split].
        - intros ->. apply (NoDup_remove_2 p1 (y :: p2) y Hnd). apply in_or_app. right. left. reflexivity.
        - apply Hns. apply in_or_app. right. right. left. reflexivity.
        - intro Hyx. apply (AtLeastOnceExact.prec_after_contra p1 x (y :: p2) y Hnd (or_introl eq_refl)).
          apply Hcc; [exact Hyx | apply in_or_app; right; right; left; reflexivity
                     | apply in_or_app; right; left; reflexivity]. }
      assert (Hc' : causal hb ((p1 ++ [y]) ++ x :: p2)).
      { rewrite <- app_assoc. exact (GovernanceConverse.causal_swap hb p1 x y p2 (proj1 (proj2 Hxy)) Hc). }
      assert (Hev' : Forall Ev ((p1 ++ [y]) ++ x :: p2)).
      { rewrite <- app_assoc. exact (Permutation_Forall HP Hev). }
      assert (Hns' : forall z, In z ((p1 ++ [y]) ++ x :: p2) -> ~ hb x z).
      { intros z Hz. apply Hns. rewrite <- app_assoc in Hz.
        exact (Permutation_in z (Permutation_sym HP) Hz). }
      assert (Hx : Ev x) by (rewrite Forall_forall in Hev; apply Hev; apply in_or_app; right; left; reflexivity).
      destruct (IH (p1 ++ [y]) Hc' Hev' Hns') as [Hc2 Hac].
      rewrite <- app_assoc in Hc2. repeat rewrite <- app_assoc in Hac. split; [exact Hc2 |].
      eapply ac_trans; [| exact Hac].
      apply ac_gen.
      + pose proof (adm_snoc (p1 ++ x :: y :: p2) x Hc Hev Hx Hns) as H.
        rewrite <- app_assoc in H. exact H.
      + rewrite <- app_assoc in Hc', Hev'.
        pose proof (adm_snoc (p1 ++ [y] ++ x :: p2) x Hc' Hev' Hx
                      (fun z Hz => Hns' z ltac:(rewrite <- app_assoc; exact Hz))) as H.
        rewrite <- app_assoc in H. exact H.
      + left. exists p1, x, y, (p2 ++ [x]). split; [exact Hxy |]. split; [| split; reflexivity].
        apply (GovernanceConverse.causal_prefix hb _ p2). rewrite <- app_assoc. exact Hc.
  Qed.

  Lemma idem_close : forall w x, causal hb w -> In x w -> Forall Ev w ->
    (forall b, In b w -> ~ hb x b) ->
    exists w', causal hb w' /\ same_set (w ++ [x]) w' /\ AC alo_adm G_idem (w ++ [x]) w'.
  Proof.
    intros w x Hc Hx Hev Hns. apply in_split in Hx. destruct Hx as [p1 [p2 ->]].
    destruct (move_right x p2 p1 Hc Hev Hns) as [Hc2 Hac].
    assert (Hx : Ev x) by (rewrite Forall_forall in Hev; apply Hev; apply in_or_app; right; left; reflexivity).
    exists (p1 ++ p2 ++ [x]). split; [exact Hc2 |]. split.
    - intros z. rewrite !in_app_iff. simpl. tauto.
    - rewrite <- app_assoc. eapply ac_trans; [exact Hac |].
      assert (Hev2 : Forall Ev (p1 ++ p2 ++ [x])).
      { apply (forall_set (p1 ++ x :: p2)); [intros z; rewrite !in_app_iff; simpl; tauto | exact Hev]. }
      assert (Hns2 : forall b, In b (p1 ++ p2 ++ [x]) -> ~ hb x b).
      { intros b Hb. apply Hns. rewrite in_app_iff in *. simpl. rewrite in_app_iff in Hb. simpl in Hb. tauto. }
      apply ac_gen.
      + pose proof (adm_snoc (p1 ++ p2 ++ [x]) x Hc2 Hev2 Hx Hns2) as H.
        rewrite <- !app_assoc in H. exact H.
      + apply adm_causal; assumption.
      + right. exists (p1 ++ p2), x, []. split; [rewrite <- app_assoc; exact Hc2 |].
        split; rewrite <- app_assoc; reflexivity.
  Qed.

  Theorem alo_adequate_abs : Adequate alo_adm G_abs same_set.
  Proof.
    apply alo_adequate; [intros t u H; left; exact H | exact G_abs_set | exact G_abs_snoc | exact abs_close].
  Qed.

  Theorem alo_adequate_idem : Adequate alo_adm G_idem same_set.
  Proof.
    apply alo_adequate; [intros t u H; left; exact H | exact G_idem_set | exact G_idem_snoc | exact idem_close].
  Qed.
End ALOWords.

Lemma gen_union : forall {T Y : Type} (Adm : T -> Prop) (G1 G2 : T -> T -> Prop) (sem : T -> Y) eqY,
  GenDescent Adm (fun t u => G1 t u \/ G2 t u) sem eqY <->
  GenDescent Adm G1 sem eqY /\ GenDescent Adm G2 sem eqY.
Proof.
  intros T Y Adm G1 G2 sem eqY. split.
  - intros H. split; intros t u Ht Hu Hg; apply H; tauto.
  - intros [H1 H2] t u Ht Hu [Hg | Hg]; [apply H1 | apply H2]; assumption.
Qed.

Section ALOInstance.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.
  Variable Ev : E -> Prop.
  Variable hb : E -> E -> Prop.
  Hypothesis hb_irrefl : forall x, ~ hb x x.
  Variable s0 : S.
  Local Notation run := (runT step).
  Local Notation sem := (fun d => runT step d s0).
  Local Notation adm := (alo_adm Ev hb).

  Lemma run1' : forall x t, run [x] t = step x t.
  Proof. reflexivity. Qed.

  (* Semantic classes of admissible executions are exactly AtLeastOnceExact.CALOConv. *)
  Lemma caloconv_hd :
    AtLeastOnceExact.CALOConv step Ev hb s0 <-> HistoryDescent adm (@same_set E) sem eq.
  Proof.
    split.
    - intros H t u [Et Ct] [Eu Cu] Hs. cbv beta.
      pose proof (AtLeastOnce.causal_alo_dedup_causal dec hb t hb_irrefl Ct) as Dt.
      pose proof (AtLeastOnce.causal_alo_dedup_causal dec hb u hb_irrefl Cu) as Du.
      rewrite (H t (AtLeastOnce.dedup dec t) Et Ct Dt (fun x => AtLeastOnce.dedup_In dec t x)).
      rewrite (H u (AtLeastOnce.dedup dec u) Eu Cu Du (fun x => AtLeastOnce.dedup_In dec u x)).
      apply H; [exact (AtLeastOnceExact.Forall_dedup dec Ev t Et)
               | exact (AtLeastOnceExact.causal_causal_alo hb _ Dt) | exact Du |].
      intros x. rewrite !AtLeastOnce.dedup_In. symmetry. exact (Hs x).
    - intros H d o Hev Hca Ho Heq. apply (H d o (conj Hev Hca)).
      + split; [| exact (AtLeastOnceExact.causal_causal_alo hb o Ho)].
        apply (forall_set Ev d o); [intros x; symmetry; exact (Heq x) | exact Hev].
      + intros x. symmetry. exact (Heq x).
  Qed.

  (* The three generator conditions are CCRon, IdemAt and AbsorbAt. *)
  Lemma gen_swap_ccron :
    GenDescent adm (cswap hb) sem eq <-> AtLeastOnceExact.CCRon step Ev hb s0.
  Proof.
    split.
    - intros H p a b Hev Hab Hc.
      assert (Hc' : causal hb (p ++ [b; a]))
        by exact (GovernanceConverse.causal_swap hb p a b [] (proj1 (proj2 Hab)) Hc).
      assert (Hev' : Forall Ev (p ++ [b; a]))
        by exact (Permutation_Forall (Permutation_app_head p (perm_swap b a [])) Hev).
      pose proof (H (p ++ [a; b]) (p ++ [b; a]) (adm_causal Ev hb _ Hc Hev) (adm_causal Ev hb _ Hc' Hev')
                    (ex_intro _ p (ex_intro _ a (ex_intro _ b (ex_intro _ []
                      (conj Hab (conj Hc (conj eq_refl eq_refl)))))))) as Eq.
      cbv beta in Eq. rewrite !runT_app in Eq. exact Eq.
    - intros H t u [Et _] _ (p & a & b & r & Hab & Hc & -> & ->). cbv beta.
      rewrite !runT_app, !runT_cons.
      rewrite (H p a b); [reflexivity | | exact Hab | exact Hc].
      replace (p ++ a :: b :: r) with ((p ++ [a; b]) ++ r) in Et by (rewrite <- app_assoc; reflexivity).
      apply Forall_app in Et. exact (proj1 Et).
  Qed.

  Lemma gen_idem :
    GenDescent adm (dup_idem hb) sem eq <-> forall a, AtLeastOnceExact.IdemAt step Ev hb s0 a.
  Proof.
    split.
    - intros H a u Hev Hc.
      assert (Hx : Ev a) by (rewrite Forall_forall in Hev; apply Hev; apply in_or_app; right; left; reflexivity).
      assert (Hns : forall b, In b (u ++ [a]) -> ~ hb a b).
      { intros b Hb Hab. apply in_app_or in Hb. destruct Hb as [Hb | [<- | []]]; [| exact (hb_irrefl a Hab)].
        destruct Hc as [Hnd Hcc]. apply (prec_before_contra u a [] b Hnd Hb).
        apply Hcc; [exact Hab | apply in_or_app; right; left; reflexivity | apply in_or_app; left; exact Hb]. }
      pose proof (adm_snoc Ev hb (u ++ [a]) a Hc Hev Hx Hns) as A1. rewrite <- app_assoc in A1.
      pose proof (H (u ++ [a; a]) (u ++ [a]) A1 (adm_causal Ev hb _ Hc Hev)
                    (ex_intro _ u (ex_intro _ a (ex_intro _ [] (conj Hc (conj eq_refl eq_refl)))))) as Eq.
      cbv beta in Eq. rewrite !runT_app in Eq. exact Eq.
    - intros H t v [Et _] _ (p & a & r & Hc & -> & ->). cbv beta.
      rewrite !runT_app, !runT_cons.
      rewrite (H a p); [reflexivity | | exact Hc].
      replace (p ++ a :: a :: r) with ((p ++ [a]) ++ a :: r) in Et by (rewrite <- app_assoc; reflexivity).
      apply Forall_app in Et. exact (proj1 Et).
  Qed.

  Lemma gen_abs :
    GenDescent adm (dup_abs hb) sem eq <-> forall a, AtLeastOnceExact.AbsorbAt step Ev hb s0 a.
  Proof.
    split.
    - intros H a w Hev Hc Ha Hns.
      assert (Hx : Ev a) by (rewrite Forall_forall in Hev; exact (Hev a Ha)).
      pose proof (H (w ++ [a]) w (adm_snoc Ev hb w a Hc Hev Hx Hns) (adm_causal Ev hb _ Hc Hev)
                    (ex_intro _ w (ex_intro _ a (ex_intro _ []
                      (conj Hc (conj Ha (conj Hns (conj eq_refl (eq_sym (app_nil_r w)))))))))) as Eq.
      cbv beta in Eq. rewrite runT_app in Eq. exact Eq.
    - intros H t u [Et _] _ (w & a & r & Hc & Ha & Hns & -> & ->). cbv beta.
      rewrite !runT_app, runT_cons.
      apply Forall_app in Et. rewrite (H a w (proj1 Et) Hc Ha Hns). reflexivity.
  Qed.

  (* Criterion C, causal, idempotence form: AtLeastOnceExact.causal_alo_exact_idem. *)
  Theorem causal_alo_exact_idem_kernel :
    AtLeastOnceExact.CALOConv step Ev hb s0 <->
    AtLeastOnceExact.CCRon step Ev hb s0 /\ forall a, AtLeastOnceExact.IdemAt step Ev hb s0 a.
  Proof.
    rewrite caloconv_hd, (history_descent_exact adm (G_idem hb) (@same_set E) sem eq
      (@eq_refl _) (@eq_sym _) (@eq_trans _) (alo_adequate_idem dec Ev hb hb_irrefl)).
    unfold G_idem. rewrite gen_union, gen_swap_ccron, gen_idem. reflexivity.
  Qed.

  (* Criterion C, causal, absorption form: AtLeastOnceExact.causal_alo_exact. *)
  Theorem causal_alo_exact_kernel :
    AtLeastOnceExact.CALOConv step Ev hb s0 <->
    AtLeastOnceExact.CCRon step Ev hb s0 /\ forall a, AtLeastOnceExact.AbsorbAt step Ev hb s0 a.
  Proof.
    rewrite caloconv_hd, (history_descent_exact adm (G_abs hb) (@same_set E) sem eq
      (@eq_refl _) (@eq_sym _) (@eq_trans _) (alo_adequate_abs dec Ev hb hb_irrefl)).
    unfold G_abs. rewrite gen_union, gen_swap_ccron, gen_abs. reflexivity.
  Qed.
End ALOInstance.

(* Criterion C, free: AtLeastOnceExact.alo_exact, the instance hb = empty (the swap generator is
   any adjacent pair of distinct events at a duplicate-free prefix; the duplicate generator is a
   copy right after its only earlier delivery). *)
Theorem alo_exact_kernel : forall {S E : Type} (dec : forall x y : E, {x = y} + {x <> y})
  (step : E -> S -> S) (Ev : E -> Prop) (s0 : S),
  AtLeastOnceExact.ALOConv step Ev s0 <->
  AtLeastOnceExact.CommReach step Ev s0 /\ forall a, AtLeastOnceExact.IdemReach step Ev s0 a.
Proof.
  intros S E dec step Ev s0.
  rewrite AtLeastOnceExact.aloconv_iff,
    (causal_alo_exact_idem_kernel dec step Ev AtLeastOnceExact.nohb AtLeastOnceExact.nohb_irrefl s0),
    AtLeastOnceExact.comm_iff.
  split; intros [HC H]; split; try exact HC; intros a; apply AtLeastOnceExact.idem_iff; exact (H a).
Qed.

(* ============================================================================================ *)
(* D. Acyclic federation, event order: fed_exact                                                *)
(* ============================================================================================ *)

Section FedInstance.
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

  Local Notation feqF := (FederationEvents.feq V).
  Local Notation IfedF := (FederationEvents.Ifed E reg I).
  Local Notation rF := (FederationEvents.runF V f rho E reg sig o).
  Local Notation aF := (FederationEvents.applyF V f rho E reg sig o).

  (* The generator: an adjacent swap of two federated-independent events (every event word is
     an admissible execution). *)
  Definition fswap (t u : list E) : Prop :=
    exists p a b r, IfedF a b /\ t = p ++ a :: b :: r /\ u = p ++ b :: a :: r.

  Lemma fed_adequate : Adequate (fun _ : list E => True) fswap (tequiv IfedF).
  Proof.
    intros t u _ _. split.
    - intros H. induction H as [l | l a b r Hab | l1 l2 _ IH | l1 l2 l3 _ IH1 _ IH2].
      + apply ac_refl. exact Logic.I.
      + apply ac_gen; [exact Logic.I | exact Logic.I |]. exists l, a, b, r. split; [exact Hab | split; reflexivity].
      + apply ac_sym. exact IH.
      + eapply ac_trans; eassumption.
    - intros H. induction H as [t _ | t u _ _ (p & a & b & r & Hab & -> & ->) | t u _ IH | t u v _ IH1 _ IH2].
      + apply teq_refl.
      + apply teq_swap. exact Hab.
      + apply teq_sym. exact IH.
      + eapply teq_trans; eassumption.
  Qed.

  Lemma fed_gen_iff : forall s0,
    GenDescent (fun _ : list E => True) fswap (fun es => rF es s0) feqF <->
    FederationEventsConverse.GCF V f rho E reg sig I o s0.
  Proof.
    intros s0. split.
    - intros H p a b Hab.
      pose proof (H (p ++ [a; b]) (p ++ [b; a]) Logic.I Logic.I
                    (ex_intro _ p (ex_intro _ a (ex_intro _ b (ex_intro _ [] (conj Hab (conj eq_refl eq_refl))))))) as Eq.
      cbv beta in Eq. rewrite !FederationEvents.runF_app in Eq. exact Eq.
    - intros H t u _ _ (p & a & b & r & Hab & -> & ->). cbv beta.
      change (p ++ a :: b :: r) with (p ++ [a; b] ++ r). change (p ++ b :: a :: r) with (p ++ [b; a] ++ r).
      rewrite !FederationEvents.runF_app.
      apply (FederationEvents.runF_ext V src f valid rho E reg sig o HC). exact (H p a b Hab).
  Qed.

  (* Criterion D: FederationEventsConverse.fed_exact. The history layer is the kernel; the split
     of the swap condition into C1R1 and C2R is the model's locality lemma gc_iff_reach. *)
  Theorem fed_exact_kernel : forall s0, FederationEvents.Inv V valid s0 -> FederationEvents.Cons V f o s0 ->
    (FederationEventsConverse.TraceConv V f rho E reg sig I o s0 <->
     FederationEventsConverse.C1R1 V f rho E reg sig o s0 /\ FederationEventsConverse.C2R V f rho E reg sig I o s0).
  Proof.
    intros s0 Hi Hc.
    rewrite <- (FederationEventsConverse.gc_iff_reach V src f valid rho E reg sig I o HC s0 Hi Hc),
      <- fed_gen_iff,
      <- (history_descent_exact (fun _ : list E => True) fswap (tequiv IfedF) (fun es => rF es s0) feqF
            (fun y k => eq_refl) (fun y z H k => eq_sym (H k)) (fun x y z H1 H2 k => eq_trans (H1 k) (H2 k))
            fed_adequate).
    split; [intros H t u _ _; exact (H t u) | intros H es1 es2; exact (H es1 es2 Logic.I Logic.I)].
  Qed.

  (* N_{j,z} := f j z is a canonicalizer on valid target states (c_absorb). *)
  Lemma overwrite_canonicalizer : forall j z x, FederationEvents.Inv V valid z -> valid j x ->
    f j z (f j z x) = f j z x.
  Proof. intros j z x Hz Hx. exact (FederationEvents.c_absorb _ _ _ _ _ _ _ _ _ HC j z z x Hz Hz Hx). Qed.

  (* C1 at a reachable witness is state descent of N_{reg e, z} for the event's action. *)
  Lemma c1at_state_descent : forall s e a,
    FederationEventsConverse.C1at V f rho E reg sig o s e a <->
    StateDescentAt (f (reg e) (aF a s)) sig e (s (reg e)).
  Proof. intros s e a. split; intros H; symmetry; exact H. Qed.

  Theorem c1r1_state_descent : forall s0,
    FederationEventsConverse.C1R1 V f rho E reg sig o s0 <->
    (forall p e a, reg a <> reg e ->
       StateDescentAt (f (reg e) (aF a (rF p s0))) sig e (rF p s0 (reg e))).
  Proof.
    intros s0. split; intros H p e a Ne; apply c1at_state_descent; apply H; exact Ne.
  Qed.

  (* C2 at a reachable state is the one-swap history condition of the local governed run. *)
  Theorem c2at_history : forall s e1 e2,
    FederationEventsConverse.C2at V f E reg sig s e1 e2 <->
    grun (f (reg e1) s) sig [e1; e2] (s (reg e1)) = grun (f (reg e1) s) sig [e2; e1] (s (reg e1)).
  Proof. intros s e1 e2. split; intros H; exact H. Qed.

  (* XU (FederationEvents) is state descent of every N_{reg e, z} on valid target states;
     XUat (DistributedExact, hence XUR) is state descent at a stale reachable state, with the
     image of the flushed sources. *)
  Theorem xu_state_descent :
    FederationEvents.XU V f valid E reg sig <->
    (forall e z b, FederationEvents.Inv V valid z -> valid (reg e) b ->
       StateDescentAt (f (reg e) z) sig e b).
  Proof. split; intros H e z b Hz Hb; symmetry; apply H; assumption. Qed.

  Theorem xuat_state_descent : forall t e,
    DistributedExact.XUat V f rho E reg sig o t e <->
    StateDescentAt (f (reg e) (FederationEvents.N V f rho o t)) sig e (t (reg e)).
  Proof. intros t e. split; intros H; symmetry; exact H. Qed.
End FedInstance.

(* ============================================================================================ *)
(* E. Streams: the StatePeak class is empty; agreement is H alone                               *)
(* ============================================================================================ *)

Section StreamInstance.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho : State -> State.
  Variable valid : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.
  Variable P : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).

  Local Notation pstep := (Stream.prstep event_eq_dec apply rho valid enabled).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).

  (* The two rules' critical pair: an event step (premise valid sigma) against a compensation
     step (premise ~ valid sigma). *)
  Definition st_state_peak (x y z : State * list Event) : Prop :=
    exists sigma B e, x = (sigma, B) /\ valid sigma /\ ~ valid sigma /\ In e B /\ enabled e sigma B /\
      ((y = (apply e sigma, rm e B) /\ z = (rho sigma, B)) \/
       (y = (rho sigma, B) /\ z = (apply e sigma, rm e B))).

  Definition st_history_peak (x y z : State * list Event) : Prop :=
    exists sigma B e1 e2, x = (sigma, B) /\ valid sigma /\ e1 <> e2 /\ In e1 B /\ In e2 B /\
      enabled e1 sigma B /\ enabled e2 sigma B /\
      y = (apply e1 sigma, rm e1 B) /\ z = (apply e2 sigma, rm e2 B).

  Definition st_cls (x y z : State * list Event) (k : PeakKind) : Prop :=
    match k with
    | StatePeak => st_state_peak x y z
    | HistoryPeak => st_history_peak x y z
    | StructuralPeak => False
    end.

  (* The processor normalizes before it applies: no state peak exists. *)
  Theorem stream_state_peaks_empty : forall x y z, ~ st_state_peak x y z.
  Proof. intros x y z (sigma & B & e & _ & Hv & Hinv & _). exact (Hinv Hv). Qed.

  Lemma st_complete : forall c0, ClassComplete pstep c0 st_cls.
  Proof.
    intros c0 [sigma B] y z _ H1 H2.
    inversion H1 as [s1 B1 e1 Hv1 Hin1 Hen1 EA1 EB1 | s1 B1 Hinv1 EA1 EB1]; subst;
      inversion H2 as [s2 B2 e2 Hv2 Hin2 Hen2 EA2 EB2 | s2 B2 Hinv2 EA2 EB2]; subst.
    - destruct (event_eq_dec e1 e2) as [-> | Hne]; [left; reflexivity |].
      right. exists HistoryPeak, sigma, B, e1, e2. tauto.
    - right. exists StatePeak, sigma, B, e1. tauto.
    - right. exists StatePeak, sigma, B, e2. tauto.
    - left. reflexivity.
  Qed.

  (* Criterion E: StreamExact.pjc_exact through classified peaks (StatePeak empty). *)
  Theorem pjc_exact_kernel : forall c0,
    CR pstep c0 <-> StreamExact.PJC event_eq_dec apply rho valid enabled c0.
  Proof.
    intros c0. split.
    - intros H sigma B Hr Hv e1 e2 Hin1 Hin2 Hen1 Hen2 _.
      apply (cr_join_reach pstep c0 H (sigma, B)); [exact Hr | |]; apply star_one; apply Stream.ps_apply; assumption.
    - intros HJ. apply (proj2 (classified_peak_exact pstep c0 st_cls
        (Stream.st_SN_prstep event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf c0) (st_complete c0))).
      split; [| split].
      + apply empty_kind_joins. intros x y z _ _ _. apply stream_state_peaks_empty.
      + intros x y z Hx _ _ (sigma & B & e1 & e2 & -> & Hv & Hne & Hin1 & Hin2 & Hen1 & Hen2 & -> & ->).
        exact (HJ sigma B Hx Hv e1 e2 Hin1 Hin2 Hen1 Hen2 Hne).
      + apply empty_kind_joins. intros x y z _ _ _ [].
  Qed.

  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm : forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  (* StreamExact.stream_exact, with pjc_exact replaced by the kernel route. *)
  Theorem stream_exact_kernel : StreamExact.Progress valid enabled -> forall s0,
    StreamExact.StreamAgree event_eq_dec apply rho valid enabled s0 <->
    (forall E, NoDup E -> StreamExact.PJC event_eq_dec apply rho valid enabled (s0, E)).
  Proof.
    intros Hp s0. rewrite (StreamExact.stream_agree_set_function event_eq_dec apply rho valid enabled
                             enabled_perm s0).
    split.
    - intros H E Hnd. apply pjc_exact_kernel.
      apply (StreamExact.sx_un_cr event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf
               valid_dec enabled_dec).
      intros [s1 B1] [s2 B2] S1 N1 S2 N2.
      pose proof (H E Hnd _ _ S1 N1 S2 N2) as Es. simpl in Es.
      pose proof (StreamExact.sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N1) as E1.
      pose proof (StreamExact.sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N2) as E2.
      simpl in E1, E2. subst. reflexivity.
    - intros H E Hnd n1 n2 S1 N1 S2 N2.
      rewrite (GovernanceConverse.CR_UN pstep (s0, E) (proj2 (pjc_exact_kernel (s0, E)) (H E Hnd))
                 n1 n2 S1 N1 S2 N2).
      reflexivity.
  Qed.
End StreamInstance.

(* Free delivery: stream agreement is history descent of the governed run from rho* s0 over the
   duplicate-free reorderings, i.e. H alone (no S, no E). *)
Section StreamFree.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho rho_star : State -> State.
  Variable valid : State -> Prop.
  Variable P : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).
  Hypothesis rho_star_reach : forall sigma B,
    star (GovernanceCausal.step event_eq_dec apply rho valid StreamExact.fen) (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  Local Notation gr := (StreamExact.grun apply rho_star).
  Local Notation gov := (StreamExact.gov apply rho_star).

  Lemma pcc_gen_iff : forall s0,
    GenDescent (causal AtLeastOnceExact.nohb) (cswap AtLeastOnceExact.nohb) (fun w => gr (rho_star s0) w) eq <->
    StreamExact.PCC apply rho_star s0.
  Proof.
    intros s0. split.
    - intros H w e1 e2 Hnd.
      assert (Hc : causal AtLeastOnceExact.nohb (w ++ [e1; e2])) by (apply AtLeastOnceExact.causal_nohb; exact Hnd).
      assert (Hab : concurrent AtLeastOnceExact.nohb e1 e2).
      { apply AtLeastOnceExact.concurrent_nohb. intros ->.
        apply (NoDup_remove_2 w [e2] e2 Hnd). apply in_or_app. right. left. reflexivity. }
      assert (Hc' : causal AtLeastOnceExact.nohb (w ++ [e2; e1]))
        by exact (GovernanceConverse.causal_swap _ w e1 e2 [] (proj1 (proj2 Hab)) Hc).
      pose proof (H (w ++ [e1; e2]) (w ++ [e2; e1]) Hc Hc'
                    (ex_intro _ w (ex_intro _ e1 (ex_intro _ e2 (ex_intro _ []
                      (conj Hab (conj Hc (conj eq_refl eq_refl)))))))) as Eq.
      cbv beta in Eq. rewrite !StreamExact.fx_grun_app in Eq. exact Eq.
    - intros H t u _ _ (p & a & b & r & Hab & Hc & -> & ->). cbv beta.
      rewrite !StreamExact.fx_grun_app. simpl.
      rewrite (H p a b (proj1 (AtLeastOnceExact.causal_nohb _) Hc)). reflexivity.
  Qed.

  Theorem stream_free_history : forall s0,
    StreamExact.StreamAgree event_eq_dec apply rho valid StreamExact.fen s0 <->
    HistoryDescent (causal AtLeastOnceExact.nohb) (@Permutation Event) (fun w => gr (rho_star s0) w) eq.
  Proof.
    intros s0.
    rewrite (StreamExact.stream_exact_free event_eq_dec apply rho rho_star valid P ltP wf_ltP Phi wfc_wf
               rho_star_reach rho_star_valid s0), <- pcc_gen_iff.
    symmetry. apply history_descent_exact; [reflexivity | intros; symmetry; assumption
      | intros; etransitivity; eassumption | apply causal_adequate].
  Qed.
End StreamFree.

(* ============================================================================================ *)
(* F. The no-reset distributed model on monotone cycles: flush_fed_iff as E /\ S /\ H           *)
(* ============================================================================================ *)

Section DistInstance.
  Variables Loc Sh : Type.
  Variable bot : Sh.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable u : Loc -> nat -> Sh -> Sh.
  Variable K : nat.
  Variable js : list nat.
  Variable E : Type.
  Variable ev : E -> Loc * Sh -> Loc * Sh.
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.
  Variable r : bool.

  Local Notation NC := (DistributedCycles.Nc Loc Sh bot sh_eq_dec u K js).
  Local Notation cact := (DistributedCycles.cact E).
  Local Notation cstp := (DistributedCycles.cstep Loc Sh bot u E ev).

  Definition dkind (a : cact) : option E :=
    match a with DistributedCycles.AEv _ e => Some e | _ => None end.
  Definition dinj (e : E) : cact := DistributedCycles.AEv E e.
  Definition dok : cact -> Prop := DistributedCycles.okc js E r.
  Definition dflush (c : list cact) : Prop :=
    exists c', Forall (fun j => In j js) c' /\ c = map (DistributedCycles.AProp E) c'.
  Definition dsettled : Loc * Sh -> Prop := DistributedCycles.Quiet Loc Sh u js.
  Definition deqh : list E -> list E -> Prop := tequiv (FederationEventsCycles.Ifd E reg I).

  Lemma d_act_event : forall a e t, dkind a = Some e -> cstp a t = ev e t.
  Proof. intros [e' | j |] e t H; simpl in H; [injection H as ->; reflexivity | discriminate | discriminate]. Qed.

  Lemma d_act_internal : forall a t, dkind a = None -> NC (cstp a t) = NC t.
  Proof. intros [e' | j |] t H; [discriminate | |]; apply DistributedCycles.Nc_fst; reflexivity. Qed.

  Lemma d_flush_ok : forall c, dflush c -> Forall dok c.
  Proof.
    intros c [c' [Hc ->]]. induction Hc as [| j c' Hj _ IH]; [constructor |]. constructor; [exact Hj | exact IH].
  Qed.

  Lemma d_flush_internal : forall c, dflush c -> Forall (fun a => dkind a = None) c.
  Proof.
    intros c [c' [_ ->]]. induction c' as [| j c' IH]; [constructor |]. constructor; [reflexivity | exact IH].
  Qed.

  Lemma d_xrun : forall w t, xrun cstp w t = DistributedCycles.crun Loc Sh bot u E ev w t.
  Proof. induction w as [| a w IH]; intros t; [reflexivity |]. exact (IH (cstp a t)). Qed.

  Lemma d_proj : forall w, proj dkind w = DistributedCycles.cevs E w.
  Proof.
    induction w as [| a w IH]; [reflexivity |].
    destruct a as [e | j |]; unfold proj in *; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma d_grun : forall es s, grun NC ev es s = DistributedCycles.FM Loc Sh bot sh_eq_dec u K js E ev es s.
  Proof. reflexivity. Qed.

  Lemma d_settle : forall s0,
    DistributedCycles.FlushR Loc Sh bot u js E ev r s0 <-> Settlement cstp dok dflush dsettled s0.
  Proof.
    intros s0. split.
    - intros H w Hw. destruct (H w Hw) as [c [Hc Hq]].
      exists (map (DistributedCycles.AProp E) c). split; [exists c; split; [exact Hc | reflexivity] |].
      unfold dsettled. rewrite d_xrun. exact Hq.
    - intros H w Hw. destruct (H w Hw) as [c [[c' [Hc' ->]] Hq]].
      exists c'. split; [exact Hc' |]. unfold dsettled in Hq. rewrite d_xrun in Hq. exact Hq.
  Qed.

  Lemma d_fidelity : forall s0,
    DistributedCycles.NoGhostR Loc Sh bot sh_eq_dec u K js E ev r s0 <->
    CanonicalFidelity NC cstp dok dsettled s0.
  Proof.
    intros s0. split.
    - intros H w Hw Hq. unfold dsettled in Hq. rewrite d_xrun in *.
      apply DistributedCycles.quiet_normal. exact (H w Hw Hq).
    - intros H w Hw Hq. pose proof (H w Hw) as Hf. unfold dsettled in Hf. rewrite !d_xrun in Hf.
      rewrite (Hf Hq) at 1. rewrite DistributedCycles.Nc_eq. reflexivity.
  Qed.

  Lemma d_state_descent : forall s0,
    DistributedCycles.XUcR Loc Sh bot sh_eq_dec u K js E ev r s0 <->
    StateDescentR NC ev cstp dok s0.
  Proof.
    intros s0. split.
    - intros H p e Hp. rewrite d_xrun. apply DistributedCycles.Nc_fst. exact (H p e Hp).
    - intros H p e Hp. pose proof (f_equal fst (H p e Hp)) as X. rewrite !DistributedCycles.fst_Nc, d_xrun in X.
      exact X.
  Qed.

  Lemma d_history : forall s0,
    DistributedCycles.FMConv Loc Sh bot sh_eq_dec u K js E ev reg I (NC s0) <->
    HistoryDescentC NC ev deqh s0.
  Proof. intros s0. split; intros H es1 es2 He; exact (H es1 es2 He). Qed.

  Lemma d_agree : forall s0,
    DistributedCycles.DAgreeQ Loc Sh bot sh_eq_dec u K js E ev r s0 <->
    CanonAgree NC ev cstp dkind dok dsettled s0.
  Proof.
    intros s0. split.
    - intros H w Hw Hq. unfold dsettled in Hq. rewrite d_xrun in *. rewrite d_proj, d_grun. exact (H w Hw Hq).
    - intros H w Hw Hq. pose proof (H w Hw) as A. unfold dsettled in A. rewrite !d_xrun, d_proj, d_grun in A.
      exact (A Hq).
  Qed.

  Lemma d_conv : forall s0,
    DistributedCycles.DConvQ Loc Sh bot u js E ev reg I r s0 <->
    CanonConv cstp dkind dok dsettled deqh s0.
  Proof.
    intros s0. unfold CanonConv, DistributedCycles.DConvQ, deqh, dsettled.
    split; intros H w1 w2 H1 H2; specialize (H w1 w2 H1 H2); rewrite ?d_xrun, ?d_proj in *; exact H.
  Qed.

  (* Criterion F: DistributedCyclesExact.flush_fed_iff as an instance of esh_exact. None of the
     order, rank or cover hypotheses of DistributedCyclesExact's section is needed. *)
  Theorem flush_fed_iff_kernel : forall s0,
    (DistributedCycles.FlushR Loc Sh bot u js E ev r s0 /\
     DistributedCycles.DAgreeQ Loc Sh bot sh_eq_dec u K js E ev r s0 /\
     DistributedCycles.DConvQ Loc Sh bot u js E ev reg I r s0) <->
    (DistributedCycles.XUcR Loc Sh bot sh_eq_dec u K js E ev r s0 /\
     DistributedCycles.FMConv Loc Sh bot sh_eq_dec u K js E ev reg I (NC s0) /\
     DistributedCycles.FlushR Loc Sh bot u js E ev r s0 /\
     DistributedCycles.NoGhostR Loc Sh bot sh_eq_dec u K js E ev r s0).
  Proof.
    intros s0. rewrite d_settle, d_agree, d_conv, d_state_descent, d_history, d_fidelity.
    pose proof (esh_exact NC (DistributedCycles.Nc_idem Loc Sh bot sh_eq_dec u K js) ev cstp dkind
                  d_act_event d_act_internal dinj (fun e => eq_refl) dok (fun e => Logic.I) dflush d_flush_ok
                  d_flush_internal dsettled deqh s0) as H.
    unfold EffectiveCanon in H. tauto.
  Qed.

  (* XUc is state descent for N := Nc at one cycle state. *)
  Theorem xuc_state_descent : forall t e,
    DistributedCycles.XUc Loc Sh bot sh_eq_dec u K js E ev t e <-> StateDescentAt NC ev e t.
  Proof.
    intros t e. split.
    - intros H. apply DistributedCycles.Nc_fst. exact H.
    - intros H. pose proof (f_equal fst H) as X. rewrite !DistributedCycles.fst_Nc in X. exact X.
  Qed.
  (* The E/S/H vocabulary for this model (argument lists as in DistributedCycles). *)
  Definition esh_settle (s0 : Loc * Sh) : Prop := Settlement cstp dok dflush dsettled s0.
  Definition esh_fid (s0 : Loc * Sh) : Prop := CanonicalFidelity NC cstp dok dsettled s0.
  Definition esh_sd (s0 : Loc * Sh) : Prop := StateDescentR NC ev cstp dok s0.
  Definition esh_hd (s0 : Loc * Sh) : Prop := HistoryDescentC NC ev deqh s0.
  Definition esh_agree (s0 : Loc * Sh) : Prop := CanonAgree NC ev cstp dkind dok dsettled s0.
  Definition esh_conv (s0 : Loc * Sh) : Prop := CanonConv cstp dkind dok dsettled deqh s0.
End DistInstance.

(* The ghost family of DistributedCyclesExact.v in E/S/H terms: each instance fails exactly one
   layer (or, for conv_ghost_esh, has H and convergence but not E). The failure of agreement is
   derived through the kernel (flush_fed_iff_kernel), not cited. *)

Import NC.FederationEventsCycles NC.FederationEventsCyclesCheck NC.DistributedCycles
  NC.DistributedCyclesExact.

(* flip1: Settlement fails alone. *)
Theorem flip_esh :
  ~ esh_settle unit Fl fz fu1 fjs1 unit fid false (tt, fa) /\
  esh_fid unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid false (tt, fa) /\
  esh_sd unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid false (tt, fa) /\
  esh_hd unit Fl fz fl_eq_dec fu1 2 fjs1 unit fid (fun _ => 0) noI (tt, fa).
Proof.
  destruct flip_noflush as (_ & Hx & Hm & Hg & Hf).
  split; [intro H; apply Hf; apply d_settle; exact H |].
  split; [apply d_fidelity; exact Hg |]. split; [apply d_state_descent; exact Hx |].
  apply d_history. exact Hm.
Qed.

(* dist_cyc_ghost: CanonicalFidelity fails alone, so agreement fails. *)
Theorem ghost_esh :
  esh_settle B2 B2 cbot cu cts iev icev false gs0 /\
  ~ esh_fid B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  esh_sd B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
  esh_hd B2 B2 cbot ceq_dec cu 3 cts iev icev inreg iI gs0 /\
  ~ (FlushR B2 B2 cbot cu cts iev icev false gs0 /\
     DAgreeQ B2 B2 cbot ceq_dec cu 3 cts iev icev false gs0 /\
     DConvQ B2 B2 cbot cu cts iev icev inreg iI false gs0).
Proof.
  destruct ghost_exact as (_ & Hf & Hx & Hm & Hg & _).
  split; [apply d_settle; exact Hf |]. split; [intro H; apply Hg; apply d_fidelity; exact H |].
  split; [apply d_state_descent; exact Hx |]. split; [apply d_history; exact Hm |].
  intro H. apply Hg. exact (proj2 (proj2 (proj2 (proj1 (flush_fed_iff_kernel _ _ _ _ _ _ _ _ _ _ _ _ _) H)))).
Qed.

(* conv_ghost_normal: H and convergence hold, E fails at CanonicalFidelity, agreement fails. *)
Theorem conv_ghost_esh :
  esh_settle B2 B2 cbot gu cts gev gcev false gs0 /\
  esh_sd B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  esh_hd B2 B2 cbot ceq_dec gu 3 cts gev gcev gnreg noI gs0 /\
  esh_conv B2 B2 cbot gu cts gev gcev gnreg noI false gs0 /\
  ~ esh_fid B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0 /\
  ~ esh_agree B2 B2 cbot ceq_dec gu 3 cts gev gcev false gs0.
Proof.
  destruct conv_ghost_normal as (_ & Hff & Hx & Hm & Hc & Hg & _).
  assert (Hf : FlushR B2 B2 cbot gu cts gev gcev false gs0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec gF gu gu_incr gu_sound gu_mono gu_fixed 3 K3 cts
             g_cover gev gcev gnreg noI false gs0 Hff). }
  split; [apply d_settle; exact Hf |]. split; [apply d_state_descent; exact Hx |].
  split; [apply d_history; exact Hm |]. split; [apply d_conv; exact Hc |].
  split; [intro H; apply Hg; apply d_fidelity; exact H |].
  intro H. apply Hg.
  refine (proj2 (proj2 (proj2 (proj1 (flush_fed_iff_kernel _ _ _ _ _ _ _ _ _ _ _ _ _) _)))).
  split; [exact Hf | split; [apply d_agree; exact H | exact Hc]].
Qed.

(* copy_xu_fails: StateDescentR (XUcR) fails alone, so agreement fails. *)
Theorem copy_xu_esh :
  esh_settle B2 B2 cbot uu cts cpev cpcev false cps0 /\
  esh_fid B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0 /\
  esh_hd B2 B2 cbot ceq_dec uu 3 cts cpev cpcev cpnreg noI cps0 /\
  ~ esh_sd B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0 /\
  ~ (FlushR B2 B2 cbot uu cts cpev cpcev false cps0 /\
     DAgreeQ B2 B2 cbot ceq_dec uu 3 cts cpev cpcev false cps0 /\
     DConvQ B2 B2 cbot uu cts cpev cpcev cpnreg noI false cps0).
Proof.
  destruct copy_xu_fails as (_ & Hff & Hg & Hm & Hx & _).
  assert (Hf : FlushR B2 B2 cbot uu cts cpev cpcev false cps0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 K3 cts
             u_cover cpev cpcev cpnreg noI false cps0 Hff). }
  split; [apply d_settle; exact Hf |]. split; [apply d_fidelity; exact Hg |].
  split; [apply d_history; exact Hm |]. split; [intro H; apply Hx; apply d_state_descent; exact H |].
  intro H. apply Hx. exact (proj1 (proj1 (flush_fed_iff_kernel _ _ _ _ _ _ _ _ _ _ _ _ _) H)).
Qed.

(* fm_conv_fails: HistoryDescentC (FMConv) fails alone, so agreement fails. *)
Theorem fm_conv_esh : forall r s0,
  esh_settle B2 B2 cbot uu cts sev scev r s0 /\
  esh_fid B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
  esh_sd B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
  ~ esh_hd B2 B2 cbot ceq_dec uu 3 cts sev scev snreg sI s0 /\
  ~ (FlushR B2 B2 cbot uu cts sev scev r s0 /\
     DAgreeQ B2 B2 cbot ceq_dec uu 3 cts sev scev r s0 /\
     DConvQ B2 B2 cbot uu cts sev scev snreg sI r s0).
Proof.
  intros r s0. destruct (fm_conv_fails r s0) as (Hff & Hx & Hg & Hm & _).
  assert (Hf : FlushR B2 B2 cbot uu cts sev scev r s0).
  { exact (fairflushR_flushR B2 B2 cle cle_refl cle_trans cle_antisym cbot cbot_least crank
             crank_strict 2 crank_bound ceq_dec uF uu uu_incr uu_sound uu_mono uu_fixed 3 K3 cts
             u_cover sev scev snreg sI r s0 Hff). }
  split; [apply d_settle; exact Hf |]. split; [apply d_fidelity; exact Hg |].
  split; [apply d_state_descent; exact Hx |]. split; [intro H; apply Hm; apply d_history; exact H |].
  intro H. apply Hm. exact (proj1 (proj2 (proj1 (flush_fed_iff_kernel _ _ _ _ _ _ _ _ _ _ _ _ _) H))).
Qed.

(* Non-vacuity of all three layers together: the raise-only events of dist_cyc_raise_only from
   every start at the least fixed point satisfy E, S and H (derived through the kernel from
   agreement and convergence). *)
Theorem raise_only_esh : forall l r,
  (esh_settle B2 B2 cbot cu cts DistributedCycles.rev rcev r (l, dLfp l) /\
   esh_fid B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev r (l, dLfp l)) /\
  esh_sd B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev r (l, dLfp l) /\
  esh_hd B2 B2 cbot ceq_dec cu 3 cts DistributedCycles.rev rcev rnreg rI (l, dLfp l).
Proof.
  intros l r. destruct (raise_only_exact l r) as (_ & _ & _ & Ha & Hc).
  pose proof (c_flushR DistributedCycles.rev rcev r (l, dLfp l)) as Hf.
  destruct (proj1 (flush_fed_iff_kernel _ _ _ _ _ _ _ _ _ _ _ _ _) (conj Hf (conj Ha Hc)))
    as (Hx & Hm & _ & Hg).
  split; [split; [apply d_settle | apply d_fidelity] | split; [apply d_state_descent | apply d_history]];
    assumption.
Qed.
