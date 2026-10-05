(* CanonicalExecution.v: an EXPERIMENTAL meta-theory, "canonical execution". Axiom-free.
   Experimental: validation in progress. Do not cite yet; CanonicalInstances.v records which
   existing exact theorems the abstraction rederives and where it leaks.

   The hypothesis under test. Convergence of governed execution decomposes into three layers:
     E  effective canonicalization: the dynamics settles (Settlement) and the settled
        configurations it reaches are the canonical ones designated by a canonicalizer N
        (CanonicalFidelity);
     S  state descent (coherence): an event's canonical outcome does not depend on whether it
        acts on a raw state or on its canonical form, N (act e s) = N (act e (N s));
     H  history descent (coherence): the canonical semantics is constant on the semantic
        equivalence classes of executions.
   A fourth, compositional layer (spatial descent and gluing) is out of scope here; see the
   sheaf-gluing development (SheafGluing.v, a separate module) for that layer.

   This file is the generic kernel. Every proof is elementary and reuses existing lemmas.

   1. Canonicalizers (section Canonicalizer). N idempotent; canon_equiv x y := N x = N y.
      - state_descent_iff_respects_canon: StateDescent (N (act e s) = N (act e (N s)) for all e, s)
        IFF every act e respects canon_equiv.
      - normalization_descent: under StateDescent the raw run, normalized, is the governed run of
        the normalized start: N (rawrun w s) = grun w (N s), with gact e s := N (act e s).
        normalization_descent_from: the same from s0 when StateDescent holds only at the states
        rawrun reaches from s0.
      - state_descent_iff_cc2: with N := RhoStar.rho_star (built from WFC), StateDescent is
        exactly CC2 in its all-events form (every event at every invalid state, both sides compared
        under rho_star), not the paper's Axiom CC2, which is required only for enabled events
        (RhoStar.base_rem_absorption_enabled gives that direction). This is
        RhoStar.strong_absorption_iff_cc2 read in the new vocabulary.

   2. Rewrite presentations (section Peaks). A step relation R, a start c0, SN from c0.
      - peak_exact: SN R c0 -> (CR R c0 <-> every peak at a configuration reachable from c0 is
        joinable). This is Newman's Lemma localized (GovernanceConverse.newman_on, credited), in
        the form EnabledAfterComp.cr_iff_critical proves for the governance rewrite system.
      - classified_peak_exact: a classifier assigns each reachable non-trivial peak a kind
        (StatePeak, HistoryPeak, StructuralPeak); given completeness of the classifier,
        SN R c0 -> (CR R c0 <-> all StatePeaks join /\ all HistoryPeaks join /\ all
        StructuralPeaks join). The kinds are labels: the theorem holds for any complete
        classifier, and nothing in it ties StatePeak to S or HistoryPeak to H. That reading is
        supplied by each instance's choice of classifier.

   3. Execution equivalence (section ExecEquiv). Admissible executions are the elements t of an
      execution type T with Adm t (for instance: a delivery order with a proof that it is causally
      consistent). Generators G relate admissible executions; AC is the reflexive, symmetric,
      transitive closure of G whose every vertex is admissible (there is no context rule and no
      free word: every edge, and so every intermediate execution, is admissible).
      - history_descent_exact: under presentation adequacy (on admissible executions, the
        semantic equivalence is exactly AC), a semantics is constant on semantic classes IFF it
        is constant across each generator edge. Semantic values are compared up to an arbitrary
        equivalence relation (pointwise equality of functions, in the federation instance).

   4. Effective canonicalization (section Effective). A configuration system with raw actions
      (each one an event, or an internal action that preserves N), admissible action words,
      flush words, a settledness predicate, a canonicalizer N, and a history equivalence EqH on
      event words. The canonical semantics runs gact from N s0.
      - canonical_execution_exact: under Settlement,
          (agreement of every settled run with the canonical semantics /\ convergence of
           settled runs with EqH-equivalent events)
          IFF CanonicalFidelity /\ StateDescentR /\ HistoryDescentC.
      - esh_exact: Settlement /\ agreement /\ convergence IFF E /\ S /\ H. Settlement is a
        conjunct of both sides (E is Settlement /\ CanonicalFidelity): esh_exact is
        canonical_execution_exact with its premise moved into the iff, and does not derive
        Settlement.
      - esh_sufficient: the backward direction needs no Settlement.
      Qualifier for the whole section (hypothesis ok_inj, a premise of every exported theorem
      that uses it): every event is an admissible action after every admissible word. So
      "reachable" in StateDescentR means reachable by any word of events and admissible internal
      actions, and HistoryDescentC ranges over all EqH-related event words; event-level
      admissibility (enabledness, causal delivery) is not expressible here. The regimes that
      restrict the event order (causal and at-least-once delivery) go through
      history_descent_exact instead, where admissibility is the predicate Adm. *)

Require Import NC.Newman NC.GovernanceConverse NC.GovernanceWFConverse NC.RhoStar.
From Coq Require Import List.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Canonicalizers, state descent, normalization descent                                      *)
(* ============================================================================================ *)

Section Canonicalizer.
  Context {X Ev : Type}.
  Variable N : X -> X.
  Hypothesis N_idem : forall x, N (N x) = N x.
  Variable act : Ev -> X -> X.

  Definition canon_equiv (x y : X) : Prop := N x = N y.

  (* S: an event's canonical outcome descends to canonical classes. *)
  Definition StateDescent : Prop := forall e s, N (act e s) = N (act e (N s)).

  Definition RespectsCanon : Prop :=
    forall e s t, canon_equiv s t -> canon_equiv (act e s) (act e t).

  (* S at one point (used where the canonicalizer depends on the context, as in a federation). *)
  Definition StateDescentAt (e : Ev) (s : X) : Prop := N (act e s) = N (act e (N s)).

  Lemma canon_equiv_N : forall x, canon_equiv x (N x).
  Proof. intros x. unfold canon_equiv. rewrite N_idem. reflexivity. Qed.

  Theorem state_descent_iff_respects_canon : StateDescent <-> RespectsCanon.
  Proof.
    split.
    - intros H e s t Hst. unfold canon_equiv in *. rewrite (H e s), (H e t), Hst. reflexivity.
    - intros H e s. apply H. apply canon_equiv_N.
  Qed.

  (* The governed step and the two runs. *)
  Definition gact (e : Ev) (s : X) : X := N (act e s).
  Definition rawrun (w : list Ev) (s : X) : X := fold_left (fun t e => act e t) w s.
  Definition grun (w : list Ev) (s : X) : X := fold_left (fun t e => gact e t) w s.

  Lemma grun_snoc : forall w e s, grun (w ++ [e]) s = gact e (grun w s).
  Proof. intros w e s. unfold grun. rewrite fold_left_app. reflexivity. Qed.

  (* The governed run from a canonical state stays canonical. *)
  Lemma grun_canonical : forall w s, N (grun w (N s)) = grun w (N s).
  Proof.
    induction w as [| e w IH]; intros s; [apply N_idem |].
    change (grun (e :: w) (N s)) with (grun w (N (act e (N s)))). apply IH.
  Qed.

  Theorem normalization_descent : StateDescent -> forall w s, N (rawrun w s) = grun w (N s).
  Proof.
    intros H w. induction w as [| e w IH]; intros s; [reflexivity |].
    change (N (rawrun w (act e s)) = grun w (N (act e (N s)))).
    rewrite IH, (H e s). reflexivity.
  Qed.

  (* State descent only at the states reached from s0. *)
  Definition StateDescentFrom (s0 : X) : Prop :=
    forall w e, N (act e (rawrun w s0)) = N (act e (N (rawrun w s0))).

  Theorem normalization_descent_from :
    forall s0, StateDescentFrom s0 -> forall w, N (rawrun w s0) = grun w (N s0).
  Proof.
    intros s0 H w. induction w as [| e w IH] using rev_ind; [reflexivity |].
    rewrite grun_snoc. unfold rawrun. rewrite fold_left_app. simpl.
    unfold gact. rewrite <- IH. apply H.
  Qed.
End Canonicalizer.

(* With N := rho* built from WFC (RhoStar.v), N is a canonicalizer and state descent is CC2 in
   its all-events form (every event, every invalid state), not the enabled-events Axiom CC2. *)
Theorem rho_star_canonicalizer :
  forall {State : Type} (rho : State -> State) (valid : State -> Prop)
    (valid_dec : forall s, {valid s} + {~ valid s}) (Phi : State -> nat),
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  forall s, rho_star rho valid valid_dec Phi (rho_star rho valid valid_dec Phi s) =
            rho_star rho valid valid_dec Phi s.
Proof. intros State rho valid valid_dec Phi wfc s. apply rho_star_idem. exact wfc. Qed.

Theorem state_descent_iff_cc2 :
  forall {State Event : Type} (apply : Event -> State -> State) (rho : State -> State)
    (valid : State -> Prop) (valid_dec : forall s, {valid s} + {~ valid s}) (Phi : State -> nat),
  (forall s, ~ valid s -> Phi (rho s) < Phi s) ->
  (StateDescent (rho_star rho valid valid_dec Phi) apply <->
   (forall s e, ~ valid s ->
      rho_star rho valid valid_dec Phi (apply e s) = rho_star rho valid valid_dec Phi (apply e (rho s)))).
Proof.
  intros State Event apply rho valid valid_dec Phi wfc.
  exact (strong_absorption_iff_cc2 apply rho valid valid_dec Phi wfc).
Qed.

(* ============================================================================================ *)
(* 2. Rewrite presentations: peaks, and classified peaks                                        *)
(* ============================================================================================ *)

Inductive PeakKind : Type := StatePeak | HistoryPeak | StructuralPeak.

Section Peaks.
  Context {A : Type}.
  Variable R : A -> A -> Prop.
  Variable c0 : A.

  Definition Reach (x : A) : Prop := star R c0 x.

  Definition PeaksJoin : Prop :=
    forall x y z, Reach x -> R x y -> R x z -> joinable R y z.

  Lemma joinable_sym : forall x y, joinable R x y -> joinable R y x.
  Proof. intros x y [w [A1 A2]]. exists w. split; assumption. Qed.

  Lemma join_back_star : forall x x' y y', star R x x' -> star R y y' ->
    joinable R x' y' -> joinable R x y.
  Proof.
    intros x x' y y' Sx Sy [w [A1 A2]]. exists w. split; eapply star_trans; eassumption.
  Qed.

  (* Confluence from c0 joins every divergence at a reachable configuration. *)
  Lemma cr_join_reach : CR R c0 ->
    forall x y z, Reach x -> star R x y -> star R x z -> joinable R y z.
  Proof. intros H x y z Hx Hy Hz. apply H; eapply star_trans; eassumption. Qed.

  (* Newman localized to the reachable part (GovernanceConverse.newman_on). *)
  Theorem peak_exact : SN R c0 -> (CR R c0 <-> PeaksJoin).
  Proof.
    intros Hsn. split.
    - intros H x y z Hx Hy Hz.
      apply (cr_join_reach H x); [exact Hx | apply star_one; exact Hy | apply star_one; exact Hz].
    - intros HL. apply (newman_on R Reach).
      + intros x y Hx Hxy. eapply star_trans; [exact Hx | apply star_one; exact Hxy].
      + exact HL.
      + intros x Hx. exact (SN_star_closed R c0 x Hx Hsn).
      + apply star_refl.
  Qed.

  (* A classifier of the reachable peaks, complete up to trivial peaks (y = z). *)
  Variable cls : A -> A -> A -> PeakKind -> Prop.

  Definition ClassComplete : Prop :=
    forall x y z, Reach x -> R x y -> R x z -> y = z \/ exists k, cls x y z k.

  Definition KindJoins (k : PeakKind) : Prop :=
    forall x y z, Reach x -> R x y -> R x z -> cls x y z k -> joinable R y z.

  Theorem classified_peak_exact : SN R c0 -> ClassComplete ->
    (CR R c0 <-> KindJoins StatePeak /\ KindJoins HistoryPeak /\ KindJoins StructuralPeak).
  Proof.
    intros Hsn Hc. rewrite (peak_exact Hsn). split.
    - intros H. split; [| split]; intros x y z Hx Hy Hz _; exact (H x y z Hx Hy Hz).
    - intros [HS [HH HX]] x y z Hx Hy Hz.
      destruct (Hc x y z Hx Hy Hz) as [-> | [[| |] Hk]].
      + exists z. split; apply star_refl.
      + exact (HS x y z Hx Hy Hz Hk).
      + exact (HH x y z Hx Hy Hz Hk).
      + exact (HX x y z Hx Hy Hz Hk).
  Qed.

  (* A kind with no member joins vacuously: the classified condition drops it. *)
  Lemma empty_kind_joins : forall k,
    (forall x y z, Reach x -> R x y -> R x z -> ~ cls x y z k) -> KindJoins k.
  Proof. intros k H x y z Hx Hy Hz Hk. exfalso. exact (H x y z Hx Hy Hz Hk). Qed.
End Peaks.

(* ============================================================================================ *)
(* 3. Execution equivalence: history descent on admissible executions                           *)
(* ============================================================================================ *)

Section ExecEquiv.
  Context {T Y : Type}.
  Variable Adm : T -> Prop.          (* admissible executions from the start *)
  Variable G : T -> T -> Prop.       (* generator edges *)
  Variable SemEq : T -> T -> Prop.   (* semantic equivalence of executions *)
  Variable sem : T -> Y.             (* the semantics, e.g. the state an execution reaches *)
  Variable eqY : Y -> Y -> Prop.
  Hypothesis eqY_refl : forall y, eqY y y.
  Hypothesis eqY_sym : forall y z, eqY y z -> eqY z y.
  Hypothesis eqY_trans : forall x y z, eqY x y -> eqY y z -> eqY x z.

  (* The equivalence closure of the generators, every vertex admissible. *)
  Inductive AC : T -> T -> Prop :=
  | ac_refl : forall t, Adm t -> AC t t
  | ac_gen : forall t u, Adm t -> Adm u -> G t u -> AC t u
  | ac_sym : forall t u, AC t u -> AC u t
  | ac_trans : forall t u v, AC t u -> AC u v -> AC t v.

  Lemma ac_adm : forall t u, AC t u -> Adm t /\ Adm u.
  Proof.
    intros t u H. induction H as [t Ht | t u Ht Hu _ | t u _ [A1 A2] | t u v _ [A1 _] _ [_ A3]];
      tauto.
  Qed.

  (* Presentation adequacy. *)
  Definition Adequate : Prop :=
    forall t u, Adm t -> Adm u -> (SemEq t u <-> AC t u).

  Definition HistoryDescent : Prop :=
    forall t u, Adm t -> Adm u -> SemEq t u -> eqY (sem t) (sem u).

  Definition GenDescent : Prop :=
    forall t u, Adm t -> Adm u -> G t u -> eqY (sem t) (sem u).

  Lemma ac_sem : GenDescent -> forall t u, AC t u -> eqY (sem t) (sem u).
  Proof.
    intros HG t u H.
    induction H as [t _ | t u Ht Hu Hg | t u _ IH | t u v _ IH1 _ IH2].
    - apply eqY_refl.
    - exact (HG t u Ht Hu Hg).
    - apply eqY_sym. exact IH.
    - exact (eqY_trans _ _ _ IH1 IH2).
  Qed.

  Theorem history_descent_exact : Adequate -> (HistoryDescent <-> GenDescent).
  Proof.
    intros HA. split.
    - intros H t u Ht Hu Hg. apply H; [exact Ht | exact Hu |].
      apply (proj2 (HA t u Ht Hu)). apply ac_gen; assumption.
    - intros HG t u Ht Hu Hs. apply (ac_sem HG). exact (proj1 (HA t u Ht Hu) Hs).
  Qed.
End ExecEquiv.

(* ============================================================================================ *)
(* 4. Effective canonicalization: agreement with the canonical semantics iff E /\ S /\ H        *)
(* ============================================================================================ *)

Section Effective.
  Context {Cf Ev Act : Type}.
  Variable N : Cf -> Cf.                       (* the designated canonicalizer *)
  Hypothesis N_idem : forall x, N (N x) = N x.
  Variable ev : Ev -> Cf -> Cf.                (* an event's raw action *)
  Variable act : Act -> Cf -> Cf.              (* the raw actions of the dynamics *)
  Variable kind : Act -> option Ev.            (* Some e: the action is event e; None: internal *)
  Hypothesis act_event : forall a e t, kind a = Some e -> act a t = ev e t.
  Hypothesis act_internal : forall a t, kind a = None -> N (act a t) = N t.
  Variable inj : Ev -> Act.
  Hypothesis kind_inj : forall e, kind (inj e) = Some e.
  Variable okA : Act -> Prop.                  (* admissible actions *)
  Hypothesis ok_inj : forall e, okA (inj e).      (* every event admissible everywhere *)
  Variable Flush : list Act -> Prop.           (* flush words: admissible and internal *)
  Hypothesis flush_ok : forall c, Flush c -> Forall okA c.
  Hypothesis flush_internal : forall c, Flush c -> Forall (fun a => kind a = None) c.
  Variable Settled : Cf -> Prop.
  Variable EqH : list Ev -> list Ev -> Prop.   (* history equivalence of event words *)

  Definition xrun (w : list Act) (t : Cf) : Cf := fold_left (fun t a => act a t) w t.
  Definition proj (w : list Act) : list Ev :=
    flat_map (fun a => match kind a with Some e => [e] | None => [] end) w.
  Definition OKw (w : list Act) : Prop := Forall okA w.
  Local Notation cgrun := (grun N ev).

  (* E: effective canonicalization. *)
  Definition Settlement (s0 : Cf) : Prop :=
    forall w, OKw w -> exists c, Flush c /\ Settled (xrun (w ++ c) s0).
  Definition CanonicalFidelity (s0 : Cf) : Prop :=
    forall w, OKw w -> Settled (xrun w s0) -> xrun w s0 = N (xrun w s0).
  Definition EffectiveCanon (s0 : Cf) : Prop := Settlement s0 /\ CanonicalFidelity s0.
  (* S: state descent at every reachable configuration. Reachable means by any admissible action
     word, and under ok_inj every event is admissible after every admissible word. *)
  Definition StateDescentR (s0 : Cf) : Prop :=
    forall p e, OKw p -> N (ev e (xrun p s0)) = N (ev e (N (xrun p s0))).
  (* H: history descent of the canonical semantics. *)
  Definition HistoryDescentC (s0 : Cf) : Prop :=
    forall es1 es2, EqH es1 es2 -> cgrun es1 (N s0) = cgrun es2 (N s0).
  (* Agreement with the canonical semantics, and convergence, at settled configurations. *)
  Definition CanonAgree (s0 : Cf) : Prop :=
    forall w, OKw w -> Settled (xrun w s0) -> xrun w s0 = cgrun (proj w) (N s0).
  Definition CanonConv (s0 : Cf) : Prop :=
    forall w1 w2, OKw w1 -> OKw w2 -> EqH (proj w1) (proj w2) ->
      Settled (xrun w1 s0) -> Settled (xrun w2 s0) -> xrun w1 s0 = xrun w2 s0.

  Lemma proj_app : forall p q, proj (p ++ q) = proj p ++ proj q.
  Proof. intros p q. unfold proj. apply flat_map_app. Qed.

  Lemma proj_internal : forall c, Forall (fun a => kind a = None) c -> proj c = [].
  Proof.
    intros c H. induction H as [| a c Ha _ IH]; [reflexivity |].
    unfold proj in *. simpl. rewrite Ha. exact IH.
  Qed.

  Lemma proj_inj : forall es, proj (map inj es) = es.
  Proof.
    induction es as [| e es IH]; [reflexivity |].
    unfold proj in *. simpl. rewrite kind_inj. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma xrun_app : forall p q t, xrun (p ++ q) t = xrun q (xrun p t).
  Proof. intros. unfold xrun. apply fold_left_app. Qed.

  Lemma xrun_internal_N : forall c t, Forall (fun a => kind a = None) c -> N (xrun c t) = N t.
  Proof.
    intros c. induction c as [| a c IH]; intros t H; [reflexivity |].
    inversion H as [| ? ? Ha Hc]; subst.
    change (N (xrun c (act a t)) = N t). rewrite (IH _ Hc). apply act_internal. exact Ha.
  Qed.

  Lemma okw_app : forall p q, OKw p -> OKw q -> OKw (p ++ q).
  Proof. intros p q Hp Hq. apply Forall_app. split; assumption. Qed.

  Lemma okw_inj : forall es, OKw (map inj es).
  Proof. intros es. apply Forall_forall. intros a Ha. apply in_map_iff in Ha.
    destruct Ha as [e [<- _]]. apply ok_inj. Qed.

  (* Under S, the normalized raw run is the canonical run of the projected events. *)
  Lemma descent_run : forall s0, StateDescentR s0 ->
    forall w, OKw w -> N (xrun w s0) = cgrun (proj w) (N s0).
  Proof.
    intros s0 HS w. induction w as [| a w IH] using rev_ind; intros Hw; [reflexivity |].
    apply Forall_app in Hw. destruct Hw as [Hw Ha].
    rewrite xrun_app, proj_app. change (xrun [a] (xrun w s0)) with (act a (xrun w s0)).
    unfold proj at 2. simpl. destruct (kind a) as [e |] eqn:K.
    - rewrite (act_event a e _ K), (HS w e Hw), (IH Hw). simpl. rewrite grun_snoc. reflexivity.
    - rewrite (act_internal a _ K), (IH Hw), app_nil_r. reflexivity.
  Qed.

  (* The backward direction needs no Settlement. *)
  Theorem esh_sufficient : forall s0,
    CanonicalFidelity s0 -> StateDescentR s0 -> HistoryDescentC s0 ->
    CanonAgree s0 /\ CanonConv s0.
  Proof.
    intros s0 HF HS HH.
    assert (HA : CanonAgree s0).
    { intros w Hw Hs. rewrite (HF w Hw Hs). apply descent_run; assumption. }
    split; [exact HA |].
    intros w1 w2 H1 H2 He S1 S2. rewrite (HA w1 H1 S1), (HA w2 H2 S2). apply HH. exact He.
  Qed.

  (* A settled flush of a reachable configuration exhibits its canonical form. *)
  Lemma flush_point : forall s0, CanonAgree s0 -> forall w c, OKw w -> Flush c ->
    Settled (xrun (w ++ c) s0) ->
    xrun (w ++ c) s0 = cgrun (proj w) (N s0) /\ N (xrun w s0) = cgrun (proj w) (N s0).
  Proof.
    intros s0 HA w c Hw Hc Hs.
    pose proof (HA (w ++ c) (okw_app w c Hw (flush_ok c Hc)) Hs) as E.
    rewrite proj_app, (proj_internal c (flush_internal c Hc)), app_nil_r in E.
    split; [exact E |].
    rewrite <- (xrun_internal_N c (xrun w s0) (flush_internal c Hc)), <- xrun_app, E.
    apply grun_canonical. exact N_idem.
  Qed.

  Theorem canonical_execution_exact : forall s0, Settlement s0 ->
    (CanonAgree s0 /\ CanonConv s0 <->
     CanonicalFidelity s0 /\ StateDescentR s0 /\ HistoryDescentC s0).
  Proof.
    intros s0 HSet. split; [| intros [HF [HS HH]]; apply esh_sufficient; assumption].
    intros [HA HC]. split; [| split].
    - intros w Hw Hs. rewrite (HA w Hw Hs). symmetry. apply grun_canonical. exact N_idem.
    - intros p e Hp.
      destruct (HSet p Hp) as [c1 [Hc1 S1]].
      destruct (flush_point s0 HA p c1 Hp Hc1 S1) as [_ E1].
      assert (Hpe : OKw (p ++ [inj e])) by (apply okw_app; [exact Hp | constructor; [apply ok_inj | constructor]]).
      destruct (HSet _ Hpe) as [c2 [Hc2 S2]].
      destruct (flush_point s0 HA _ c2 Hpe Hc2 S2) as [_ E2].
      rewrite xrun_app, proj_app in E2.
      change (xrun [inj e] (xrun p s0)) with (act (inj e) (xrun p s0)) in E2.
      rewrite (act_event (inj e) e _ (kind_inj e)) in E2.
      unfold proj at 2 in E2. simpl in E2. rewrite kind_inj in E2. simpl in E2.
      rewrite E2, grun_snoc, E1. reflexivity.
    - intros es1 es2 He.
      destruct (HSet (map inj es1) (okw_inj es1)) as [c1 [Hc1 S1]].
      destruct (HSet (map inj es2) (okw_inj es2)) as [c2 [Hc2 S2]].
      destruct (flush_point s0 HA _ c1 (okw_inj es1) Hc1 S1) as [E1 _].
      destruct (flush_point s0 HA _ c2 (okw_inj es2) Hc2 S2) as [E2 _].
      rewrite proj_inj in E1, E2. rewrite <- E1, <- E2.
      apply HC; [apply okw_app; [apply okw_inj | apply flush_ok; exact Hc1]
                | apply okw_app; [apply okw_inj | apply flush_ok; exact Hc2] | | exact S1 | exact S2].
      rewrite !proj_app, (proj_internal c1 (flush_internal c1 Hc1)),
        (proj_internal c2 (flush_internal c2 Hc2)), !app_nil_r, !proj_inj. exact He.
  Qed.

  (* The headline: settled agreement with the canonical semantics iff E /\ S /\ H. Settlement
     appears on both sides; the content is canonical_execution_exact. *)
  Theorem esh_exact : forall s0,
    (Settlement s0 /\ CanonAgree s0 /\ CanonConv s0) <->
    (EffectiveCanon s0 /\ StateDescentR s0 /\ HistoryDescentC s0).
  Proof.
    intros s0. split.
    - intros [HSet HAC]. destruct (proj1 (canonical_execution_exact s0 HSet) HAC) as [HF HSH].
      split; [split; assumption | exact HSH].
    - intros [[HSet HF] [HS HH]]. split; [exact HSet |].
      apply esh_sufficient; assumption.
  Qed.
End Effective.
