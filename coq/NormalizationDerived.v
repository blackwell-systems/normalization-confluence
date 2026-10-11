(* NormalizationDerived.v: the headline normalization-confluence theorem (GovernanceConverse.v's
   cc_exact_from, cc_exact and cc_exact_global) derived from the framework kernels. Axiom-free.

   This is a derivation, not a prediction: the framework (CanonicalExecution.v,
   PresentedExecution.v, LayerInterfaces.v) was built after cc_exact, with cc_exact in view. What
   the file shows is that the kernels, used as they are, reproduce the exact statement: the
   free-delivery governance rewrite system is the base case of the framework.

   Setting: GovernanceConverse.v's section FreeExact, unchanged. Free delivery (every buffered
   event may fire), WFC, rho_star a reduct by compensation steps (rho_star_reach) that repairs to
   validity (rho_star_valid). The canonicalizer is N := rho_star; the governed step is
   gov e s := N (apply e s).

   The dictionary.
     S  (state descent) is CC2. Globally: CanonicalExecution.StateDescent N apply is CC2 at every
        invalid state (nd_state_descent_cc2; for the constructed rho_star of RhoStar.v this is
        CanonicalExecution.state_descent_iff_cc2, see nd_derived_global_constructed). From s0:
        every event descends along N on the states reachable from s0, in the relativized form
        LayerInterfaces.DescendsOn (reach s0) N (apply e), is CC2 on those states
        (nd_descends_cc2).
     H  (history descent) is CC1. FreeHistoryDescent s0: the governed semantics from the canonical
        start, t |-> grun N apply t (N s0), is invariant under PresentedExecution's free-delivery
        presentation (admissibility trivial, generators the adjacent swaps), whose generated
        equivalence is Permutation (swap_peq_perm). By P1 (local_exact_all) this holds iff every
        adjacent swap commutes after every word (nd_history_seeds), and given S it is CC1 on the
        states reachable from s0 (nd_history_cc1). H alone is CC1 at the canonical states the
        governed runs reach; S carries it to the raw reachable states, which is where CC1 is
        needed (an event can fire before repair).
     WFC is the progress side: termination is Governance.terminating.
     Newman joins them: CanonicalExecution.classified_peak_exact, with the classifier nd_cls that
        labels an apply/repair peak a StatePeak and a peak of two distinct applies a HistoryPeak
        (no StructuralPeak). State peaks join by S (nd_state_peaks_join), history peaks by CC1
        (nd_history_peaks_join).
     The converse is by tiny executions: buffer [e1; e2] in both orders forces CC1 at a reachable
        state, buffer [e] with the event first versus the repair first forces CC2
        (nd_tiny_cc1, nd_tiny_cc2).

   Main results.
     nd_derived_from (start-relative, the strong form): for every s0,
       (forall B, UN (s0, B)) <-> FreeHistoryDescent s0 /\ StateDescentReach s0, and the right
       side is CC1 /\ CC2 on the states reachable from s0 (nd_dictionary_from).
     nd_cc_exact_from, nd_cc_exact, nd_cc_exact_global: the statements of cc_exact_from,
       cc_exact and cc_exact_global, word for word, proved here without them.
     nd_derived_global: (forall sigma B, UN (sigma, B)) <-> CC1 /\ CC2 <->
       (forall s0, FreeHistoryDescent s0) /\ StateDescent N apply.
     nd_derived_matches_original: the derived statements are equivalent to the originals'
       statements, and the originals inhabit the same statements. This is the only place
       cc_exact, cc_exact_from and cc_exact_global appear.

   Dependency rule. Apart from nd_derived_matches_original, no proof here uses cc_exact,
   cc_exact_from, cc_exact_global or RhoStar.wfc_cc_exact_from (checked by turning those four into
   admitted axioms in a scratch copy: every other theorem here stays closed under the global
   context). No proof here cites a lemma of GovernanceConverse.v: the small facts about runs
   (reach_run, the tiny executions, CR_UN) are reproved below, and from GovernanceConverse.v only
   the definitions UN, reach and free_enabled are named, so that the statements match. The
   kernel's peak_exact uses GovernanceConverse.newman_on (Newman localized), as credited there. *)

From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Governance NC.CanonicalExecution NC.PresentedExecution.
Require NC.GovernanceConverse NC.LayerInterfaces NC.RhoStar.
Import ListNotations.

Section Derived.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable Phi      : State -> nat.

  Local Notation fstep :=
    (step event_eq_dec apply rho valid (GovernanceConverse.free_enabled (State:=State))).
  Local Notation rm := (remove1 event_eq_dec).
  Local Notation N := rho_star.
  Local Notation gov e s := (rho_star (apply e s)).
  Local Notation reach := (GovernanceConverse.reach apply rho valid).
  Local Notation UN := GovernanceConverse.UN.

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star fstep (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  (* ------------------------------------------------------------------------------------------ *)
  (* The framework conditions.                                                                   *)
  (* ------------------------------------------------------------------------------------------ *)

  (* S from s0: every event descends along N on the states reachable from s0 (the kernel's
     relativized descent, LayerInterfaces.DescendsOn). *)
  Definition StateDescentReach (s0 : State) : Prop :=
    forall e, LayerInterfaces.DescendsOn (reach s0) N (apply e).

  (* H from s0: the governed semantics from the canonical start, under free delivery's adjacent
     swaps (PresentedExecution's free presentation). *)
  Definition gsem (s0 : State) (t : list Event) : State := grun N apply t (N s0).

  Definition FreeHistoryDescent (s0 : State) : Prop :=
    PInv (@fs_adm Event) (@fs_gen Event) (gsem s0) eq.

  (* CC1 and CC2 on the states reachable from s0, as in cc_exact_from. *)
  Definition CC1Reach (s0 : State) : Prop :=
    forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma).

  Definition CC2Reach (s0 : State) : Prop :=
    forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma).

  (* ------------------------------------------------------------------------------------------ *)
  (* Runs of the rewrite system (reproved here; GovernanceConverse.v's lemmas are not used).    *)
  (* ------------------------------------------------------------------------------------------ *)

  Lemma nd_rm_head : forall e l, rm e (e :: l) = l.
  Proof. intros e l. simpl. destruct (event_eq_dec e e) as [_ | E]; [reflexivity | contradiction]. Qed.

  Lemma nd_rm_skip : forall e x l, x <> e -> rm e (x :: l) = x :: rm e l.
  Proof. intros e x l H. simpl. destruct (event_eq_dec x e) as [E | _]; [contradiction | reflexivity]. Qed.

  Lemma nd_in_rm : forall e x l, In x l -> x <> e -> In x (rm e l).
  Proof.
    intros e x l. induction l as [| y l IH]; intros Hin Hne; [destruct Hin |].
    simpl. destruct (event_eq_dec y e) as [-> | Hy].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma nd_nf_valid_empty : forall t, valid t -> normal_form fstep (t, []).
  Proof.
    intros t Hv [y H]. inversion H as [s B e Hin _ E1 E2 | s B Hinv E1 E2]; subst.
    - destruct Hin.
    - apply Hinv. exact Hv.
  Qed.

  Lemma nd_gov_run : forall sigma B e, In e B -> star fstep (sigma, B) (gov e sigma, rm e B).
  Proof.
    intros sigma B e Hin. eapply star_step; [apply st_apply; [exact Hin | exact Hin] |].
    apply rho_star_reach.
  Qed.

  Lemma nd_cr_un : forall c, CR fstep c -> UN fstep c.
  Proof.
    intros c H n1 n2 S1 N1 S2 N2. destruct (H n1 n2 S1 S2) as [w [A1 A2]].
    rewrite (star_from_nf fstep n1 w N1 A1), (star_from_nf fstep n2 w N2 A2). reflexivity.
  Qed.

  (* With an empty buffer the only move is a repair. *)
  Lemma nd_empty_first : forall x t, star fstep (x, []) t ->
    t = (x, []) \/ (~ valid x /\ star fstep (rho x, []) t).
  Proof.
    intros x t S. inversion S as [c Ec | c y z H S' Ec Et]; subst; [left; reflexivity |].
    right. inversion H as [s B e Hin _ E1 E2 | s B Hinv E1 E2]; subst; [destruct Hin |].
    split; assumption.
  Qed.

  (* Runs from an empty buffer are deterministic. *)
  Lemma nd_empty_det : forall x t1 t2, star fstep (x, []) t1 -> normal_form fstep t1 ->
    star fstep (x, []) t2 -> normal_form fstep t2 -> t1 = t2.
  Proof.
    intros x t1 t2 S1. remember (x, @nil Event) as c eqn:Ec. revert x Ec t2.
    induction S1 as [c | c y z H1 S1 IH]; intros x Ec t2 N1 S2 N2.
    - subst c. exact (star_from_nf fstep _ _ N1 S2).
    - subst c. inversion H1 as [s B e Hin _ E1 E2 | s B Hinv E1 E2]; subst; [destruct Hin |].
      destruct (nd_empty_first x t2 S2) as [-> | [_ S2']].
      + exfalso. apply N2. eexists. exact H1.
      + exact (IH (rho x) eq_refl t2 N1 S2' N2).
  Qed.

  (* N is a canonicalizer: it fixes valid states, is idempotent, and absorbs one repair. *)
  Lemma nd_N_fix : forall s, valid s -> N s = s.
  Proof.
    intros s Hv. pose proof (star_from_nf fstep _ _ (nd_nf_valid_empty s Hv) (rho_star_reach s []))
      as E. injection E as E. symmetry. exact E.
  Qed.

  Lemma nd_N_idem : forall s, N (N s) = N s.
  Proof. intros s. apply nd_N_fix. apply rho_star_valid. Qed.

  Lemma nd_N_rho : forall s, ~ valid s -> N (rho s) = N s.
  Proof.
    intros s Hn. destruct (nd_empty_first s (N s, []) (rho_star_reach s [])) as [E | [_ S]].
    - exfalso. injection E as E. apply Hn. rewrite <- E. apply rho_star_valid.
    - pose proof (nd_empty_det (rho s) _ _ (rho_star_reach (rho s) [])
                    (nd_nf_valid_empty _ (rho_star_valid _)) S
                    (nd_nf_valid_empty _ (rho_star_valid _))) as E.
      injection E as E. exact E.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* Reachable states.                                                                           *)
  (* ------------------------------------------------------------------------------------------ *)

  Lemma nd_reach_step : forall s0 c d, reach s0 (fst c) -> fstep c d -> reach s0 (fst d).
  Proof.
    intros s0 c d Hc H. destruct H as [s B e _ _ | s B Hinv]; simpl in *.
    - apply GovernanceConverse.r_apply. exact Hc.
    - apply GovernanceConverse.r_comp; assumption.
  Qed.

  Lemma nd_reach_star : forall s0 c d, star fstep c d -> reach s0 (fst c) -> reach s0 (fst d).
  Proof.
    intros s0 c d S. induction S as [c | c y z H _ IH]; intros Hc; [exact Hc |].
    apply IH. exact (nd_reach_step s0 c y Hc H).
  Qed.

  Lemma nd_reach_N : forall s0 s, reach s0 s -> reach s0 (N s).
  Proof. intros s0 s H. exact (nd_reach_star s0 (s, []) (N s, []) (rho_star_reach s []) H). Qed.

  Lemma nd_reach_gov : forall s0 s e, reach s0 s -> reach s0 (gov e s).
  Proof. intros s0 s e H. apply nd_reach_N. apply GovernanceConverse.r_apply. exact H. Qed.

  Lemma nd_reach_grun : forall s0 w s, reach s0 s -> reach s0 (grun N apply w s).
  Proof.
    intros s0 w. induction w as [| e w IH]; intros s H; [exact H |].
    change (reach s0 (grun N apply w (gov e s))). apply IH. apply nd_reach_gov. exact H.
  Qed.

  Lemma nd_reach_trans : forall s0 s t, reach s0 s -> reach s t -> reach s0 t.
  Proof.
    intros s0 s t Hs Ht. induction Ht as [| e x _ IH | x _ IH Hinv].
    - exact Hs.
    - apply GovernanceConverse.r_apply. exact IH.
    - apply GovernanceConverse.r_comp; assumption.
  Qed.

  (* Every reachable state is reached by a run from s0: a word w of events, delivered first. *)
  Lemma nd_reach_run : forall s0 sigma, reach s0 sigma ->
    exists w, forall B, star fstep (s0, w ++ B) (sigma, B).
  Proof.
    intros s0 sigma H. induction H as [| e s _ [w IH] | s _ [w IH] Hinv].
    - exists []. intros B. apply star_refl.
    - exists (w ++ [e]). intros B. rewrite <- app_assoc. simpl.
      eapply star_trans; [apply IH |]. apply star_one.
      pose proof (st_apply event_eq_dec apply rho valid (GovernanceConverse.free_enabled (State:=State))
                    s (e :: B) e (or_introl eq_refl) (or_introl eq_refl)) as St.
      rewrite nd_rm_head in St. exact St.
    - exists w. intros B. eapply star_trans; [apply IH |]. apply star_one. apply st_comp. exact Hinv.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The converse by tiny executions.                                                            *)
  (* ------------------------------------------------------------------------------------------ *)

  (* Buffer [e1; e2]: the two delivery orders end in the two sides of CC1. *)
  Lemma nd_two_orders : forall sigma e1 e2, e1 <> e2 ->
    star fstep (sigma, [e1; e2]) (gov e2 (gov e1 sigma), []) /\
    star fstep (sigma, [e1; e2]) (gov e1 (gov e2 sigma), []).
  Proof.
    intros sigma e1 e2 Hne. split.
    - eapply star_trans; [apply (nd_gov_run sigma [e1; e2] e1); left; reflexivity |].
      rewrite nd_rm_head. pose proof (nd_gov_run (gov e1 sigma) [e2] e2 (or_introl eq_refl)) as H.
      rewrite nd_rm_head in H. exact H.
    - eapply star_trans; [apply (nd_gov_run sigma [e1; e2] e2); right; left; reflexivity |].
      rewrite (nd_rm_skip e2 e1 [e2] Hne), nd_rm_head.
      pose proof (nd_gov_run (gov e2 sigma) [e1] e1 (or_introl eq_refl)) as H.
      rewrite nd_rm_head in H. exact H.
  Qed.

  (* Buffer [e] at an invalid state: event first, or repair first. *)
  Lemma nd_event_or_repair : forall sigma e, ~ valid sigma ->
    star fstep (sigma, [e]) (gov e sigma, []) /\
    star fstep (sigma, [e]) (gov e (rho sigma), []).
  Proof.
    intros sigma e Hinv. split.
    - pose proof (nd_gov_run sigma [e] e (or_introl eq_refl)) as H. rewrite nd_rm_head in H. exact H.
    - eapply star_step; [apply st_comp; exact Hinv |].
      pose proof (nd_gov_run (rho sigma) [e] e (or_introl eq_refl)) as H. rewrite nd_rm_head in H.
      exact H.
  Qed.

  Theorem nd_tiny_cc1 : forall s0, (forall B, UN fstep (s0, B)) -> CC1Reach s0.
  Proof.
    intros s0 H sigma e1 e2 Hs. destruct (event_eq_dec e1 e2) as [-> | Hd]; [reflexivity |].
    destruct (nd_reach_run s0 sigma Hs) as [w Hw].
    destruct (nd_two_orders sigma e1 e2 Hd) as [S1 S2].
    pose proof (H (w ++ [e1; e2]) _ _ (star_trans _ _ _ _ (Hw _) S1)
                  (nd_nf_valid_empty _ (rho_star_valid _))
                  (star_trans _ _ _ _ (Hw _) S2) (nd_nf_valid_empty _ (rho_star_valid _))) as E.
    injection E as E. exact E.
  Qed.

  Theorem nd_tiny_cc2 : forall s0, (forall B, UN fstep (s0, B)) -> CC2Reach s0.
  Proof.
    intros s0 H sigma e Hs Hinv. destruct (nd_reach_run s0 sigma Hs) as [w Hw].
    destruct (nd_event_or_repair sigma e Hinv) as [S1 S2].
    pose proof (H (w ++ [e]) _ _ (star_trans _ _ _ _ (Hw _) S1)
                  (nd_nf_valid_empty _ (rho_star_valid _))
                  (star_trans _ _ _ _ (Hw _) S2) (nd_nf_valid_empty _ (rho_star_valid _))) as E.
    injection E as E. exact E.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The state side: S is CC2.                                                                   *)
  (* ------------------------------------------------------------------------------------------ *)

  (* Along a repair chain from a reachable state, CC2 keeps the governed outcome. *)
  Lemma nd_cc2_chain : forall s0 e c d, CC2Reach s0 -> star fstep c d -> snd c = [] ->
    reach s0 (fst c) -> gov e (fst d) = gov e (fst c).
  Proof.
    intros s0 e c d H2 S. induction S as [c | c y z H _ IH]; intros Ec Hc; [reflexivity |].
    destruct c as [x B]. simpl in Ec, Hc. subst B.
    inversion H as [s B e' Hin _ E1 E2 | s B Hinv E1 E2]; subst; [destruct Hin |].
    rewrite (IH eq_refl (GovernanceConverse.r_comp _ _ _ _ _ Hc Hinv)). simpl.
    symmetry. exact (H2 x e Hc Hinv).
  Qed.

  Theorem nd_descends_cc2 : forall s0, StateDescentReach s0 <-> CC2Reach s0.
  Proof.
    intros s0. split.
    - intros HS sigma e Hs Hinv.
      rewrite <- (HS e sigma Hs), <- (HS e (rho sigma) (GovernanceConverse.r_comp _ _ _ _ _ Hs Hinv)).
      rewrite (nd_N_rho sigma Hinv). reflexivity.
    - intros H2 e x Hx.
      exact (nd_cc2_chain s0 e (x, []) (N x, []) H2 (rho_star_reach x []) eq_refl Hx).
  Qed.

  (* Globally: CanonicalExecution.StateDescent N apply is CC2 at every invalid state. *)
  Theorem nd_state_descent_cc2 :
    StateDescent N apply <-> (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma)).
  Proof.
    split.
    - intros HS sigma e Hinv. rewrite (HS e sigma), (HS e (rho sigma)), (nd_N_rho sigma Hinv).
      reflexivity.
    - intros H2 e s. symmetry.
      apply (proj2 (nd_descends_cc2 s)); [| apply GovernanceConverse.r_init].
      intros sigma e' _ Hinv. apply H2. exact Hinv.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The history side: H is CC1 (given S).                                                       *)
  (* ------------------------------------------------------------------------------------------ *)

  Lemma nd_grun_pair : forall p a b s,
    grun N apply (p ++ [a; b]) s = gov b (gov a (grun N apply p s)).
  Proof. intros p a b s. unfold grun. rewrite fold_left_app. reflexivity. Qed.

  (* P1 for the free presentation: invariance iff every adjacent swap commutes after every word. *)
  Theorem nd_history_seeds : forall s0, FreeHistoryDescent s0 <->
    (forall p a b, gsem s0 (p ++ [a; b]) = gsem s0 (p ++ [b; a])).
  Proof.
    intros s0.
    assert (HR : forall t t' e, @fs_adm Event (t ++ [e]) -> @fs_adm Event (t' ++ [e]) ->
               gsem s0 t = gsem s0 t' -> gsem s0 (t ++ [e]) = gsem s0 (t' ++ [e])).
    { intros t t' e _ _ E. unfold gsem in *. rewrite !grun_snoc, E. reflexivity. }
    pose proof (local_exact_all (@fs_adm Event) (@fs_gen Event) (gsem s0) eq
                  (@eq_refl State) (@eq_sym State) (@eq_trans State) (@fs_prefix Event) HR) as K.
    unfold FreeHistoryDescent. split.
    - intros H p a b. apply (proj1 K H p [a; b] [b; a]); [exists a, b; split; reflexivity | exact I | exact I].
    - intros H. apply (proj2 K). intros p u v (a & b & -> & ->) _ _. apply H.
  Qed.

  (* The same, read as invariance under permutations (swap_peq_perm). *)
  Theorem nd_history_perm : forall s0, FreeHistoryDescent s0 <->
    (forall t t', Permutation t t' -> gsem s0 t = gsem s0 t').
  Proof.
    intros s0. unfold FreeHistoryDescent, PInv. split.
    - intros H t t' P. apply H. apply swap_peq_perm. exact P.
    - intros H t t' E. apply H. apply swap_peq_perm. exact E.
  Qed.

  (* Under S, the canonical form of every reachable state is a governed run from N s0. *)
  Lemma nd_reach_canon : forall s0, StateDescentReach s0 ->
    forall sigma, reach s0 sigma -> exists w, N sigma = grun N apply w (N s0).
  Proof.
    intros s0 HS sigma H. induction H as [| e s Hs [w IH] | s Hs [w IH] Hinv].
    - exists []. reflexivity.
    - exists (w ++ [e]). rewrite grun_snoc, <- IH. unfold gact. symmetry. exact (HS e s Hs).
    - exists w. rewrite (nd_N_rho s Hinv). exact IH.
  Qed.

  Theorem nd_history_cc1 : forall s0, StateDescentReach s0 ->
    (FreeHistoryDescent s0 <-> CC1Reach s0).
  Proof.
    intros s0 HS. split.
    - intros H sigma e1 e2 Hs. pose proof (proj1 (nd_history_seeds s0) H) as K.
      destruct (nd_reach_canon s0 HS sigma Hs) as [w Hw].
      rewrite <- (HS e1 sigma Hs), <- (HS e2 sigma Hs), Hw.
      pose proof (K w e1 e2) as E. unfold gsem in E. rewrite !nd_grun_pair in E. exact E.
    - intros H. apply (proj2 (nd_history_seeds s0)). intros p a b. unfold gsem.
      rewrite !nd_grun_pair. apply (H _ a b). apply nd_reach_grun. apply nd_reach_N.
      apply GovernanceConverse.r_init.
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* Newman joins them: classified peaks.                                                        *)
  (* ------------------------------------------------------------------------------------------ *)

  (* An apply/repair peak is a StatePeak; two distinct applies make a HistoryPeak. *)
  Definition nd_cls (x y z : State * list Event) (k : PeakKind) : Prop :=
    match k with
    | StatePeak => exists s B e, x = (s, B) /\ In e B /\ ~ valid s /\
        ((y = (apply e s, rm e B) /\ z = (rho s, B)) \/ (y = (rho s, B) /\ z = (apply e s, rm e B)))
    | HistoryPeak => exists s B e1 e2, x = (s, B) /\ In e1 B /\ In e2 B /\ e1 <> e2 /\
        y = (apply e1 s, rm e1 B) /\ z = (apply e2 s, rm e2 B)
    | StructuralPeak => False
    end.

  Lemma nd_cls_complete : forall c0, ClassComplete fstep c0 nd_cls.
  Proof.
    intros c0 x y z _ H1 H2. destruct H1 as [s B e1 Hin1 _ | s B Hinv1].
    - inversion H2 as [s' B' e2 Hin2 _ E1 E2 | s' B' Hinv2 E1 E2]; subst.
      + destruct (event_eq_dec e1 e2) as [-> | Hne]; [left; reflexivity |].
        right. exists HistoryPeak. exists s, B, e1, e2. repeat split; assumption.
      + right. exists StatePeak. exists s, B, e1. repeat split; try assumption.
        left. split; reflexivity.
    - inversion H2 as [s' B' e2 Hin2 _ E1 E2 | s' B' Hinv2 E1 E2]; subst.
      + right. exists StatePeak. exists s, B, e2. repeat split; try assumption.
        right. split; reflexivity.
      + left. reflexivity.
  Qed.

  Lemma nd_state_peaks_join : forall s0 B0, StateDescentReach s0 ->
    KindJoins fstep (s0, B0) nd_cls StatePeak.
  Proof.
    intros s0 B0 HS x y z Hx _ _ (s & B & e & -> & Hin & Hinv & Hyz).
    assert (Hs : reach s0 s)
      by exact (nd_reach_star s0 (s0, B0) (s, B) Hx (GovernanceConverse.r_init _ _ _ _)).
    assert (E : gov e s = gov e (rho s)) by exact (proj1 (nd_descends_cc2 s0) HS s e Hs Hinv).
    assert (J : joinable fstep (apply e s, rm e B) (rho s, B)).
    { exists (gov e s, rm e B). split; [apply rho_star_reach |].
      rewrite E. apply nd_gov_run. exact Hin. }
    destruct Hyz as [[-> ->] | [-> ->]]; [exact J | apply joinable_sym; exact J].
  Qed.

  Lemma nd_history_peaks_join : forall s0 B0, CC1Reach s0 ->
    KindJoins fstep (s0, B0) nd_cls HistoryPeak.
  Proof.
    intros s0 B0 H1 x y z Hx _ _ (s & B & e1 & e2 & -> & Hin1 & Hin2 & Hne & -> & ->).
    assert (Hs : reach s0 s)
      by exact (nd_reach_star s0 (s0, B0) (s, B) Hx (GovernanceConverse.r_init _ _ _ _)).
    exists (gov e2 (gov e1 s), rm e2 (rm e1 B)). split.
    - eapply star_trans; [apply rho_star_reach |]. apply nd_gov_run. apply nd_in_rm; [exact Hin2 |].
      intro E. apply Hne. symmetry. exact E.
    - rewrite (H1 s e1 e2 Hs), remove1_comm. eapply star_trans; [apply rho_star_reach |].
      apply nd_gov_run. apply nd_in_rm; [exact Hin1 | exact Hne].
  Qed.

  (* WFC gives termination; the classified peaks join; Newman (classified_peak_exact) concludes. *)
  Theorem nd_confluent_from : forall s0 B, StateDescentReach s0 -> CC1Reach s0 -> CR fstep (s0, B).
  Proof.
    intros s0 B HS H1.
    apply (proj2 (classified_peak_exact fstep (s0, B) nd_cls
                    (terminating event_eq_dec apply rho valid Phi
                       (GovernanceConverse.free_enabled (State:=State)) wfc (s0, B))
                    (nd_cls_complete (s0, B)))).
    split; [| split].
    - exact (nd_state_peaks_join s0 B HS).
    - exact (nd_history_peaks_join s0 B H1).
    - apply empty_kind_joins. intros x y z _ _ _ [].
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The start-relative form.                                                                    *)
  (* ------------------------------------------------------------------------------------------ *)

  Theorem nd_derived_from : forall s0,
    (forall B, UN fstep (s0, B)) <-> FreeHistoryDescent s0 /\ StateDescentReach s0.
  Proof.
    intros s0. split.
    - intros H.
      assert (HS : StateDescentReach s0) by exact (proj2 (nd_descends_cc2 s0) (nd_tiny_cc2 s0 H)).
      split; [| exact HS]. exact (proj2 (nd_history_cc1 s0 HS) (nd_tiny_cc1 s0 H)).
    - intros [HH HS] B. apply nd_cr_un. apply nd_confluent_from; [exact HS |].
      exact (proj1 (nd_history_cc1 s0 HS) HH).
  Qed.

  Theorem nd_dictionary_from : forall s0,
    CC1Reach s0 /\ CC2Reach s0 <-> FreeHistoryDescent s0 /\ StateDescentReach s0.
  Proof.
    intros s0. split.
    - intros [H1 H2]. assert (HS : StateDescentReach s0) by exact (proj2 (nd_descends_cc2 s0) H2).
      split; [exact (proj2 (nd_history_cc1 s0 HS) H1) | exact HS].
    - intros [HH HS].
      split; [exact (proj1 (nd_history_cc1 s0 HS) HH) | exact (proj1 (nd_descends_cc2 s0) HS)].
  Qed.

  (* cc_exact_from's statement, word for word, derived. *)
  Theorem nd_cc_exact_from : forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma))).
  Proof.
    intros s0. split; intros H.
    - exact (proj2 (nd_dictionary_from s0) (proj1 (nd_derived_from s0) H)).
    - exact (proj2 (nd_derived_from s0) (proj1 (nd_dictionary_from s0) H)).
  Qed.

  (* cc_exact's statement (every configuration over a reachable state), derived. *)
  Theorem nd_cc_exact : forall s0,
    (forall sigma B, reach s0 sigma -> UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma))).
  Proof.
    intros s0. split.
    - intros H. apply (proj1 (nd_cc_exact_from s0)). intros B. apply H.
      apply GovernanceConverse.r_init.
    - intros [H1 H2] sigma B Hs. apply (proj2 (nd_cc_exact_from sigma)). split.
      + intros t e1 e2 Ht. apply H1. exact (nd_reach_trans s0 sigma t Hs Ht).
      + intros t e Ht Hinv. apply H2; [exact (nd_reach_trans s0 sigma t Hs Ht) | exact Hinv].
  Qed.

  (* The same in the framework's terms. *)
  Theorem nd_derived_reach : forall s0,
    (forall sigma B, reach s0 sigma -> UN fstep (sigma, B)) <->
    FreeHistoryDescent s0 /\ StateDescentReach s0.
  Proof.
    intros s0. split; intros H.
    - exact (proj1 (nd_dictionary_from s0) (proj1 (nd_cc_exact s0) H)).
    - exact (proj2 (nd_cc_exact s0) (proj2 (nd_dictionary_from s0) H)).
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The global form.                                                                            *)
  (* ------------------------------------------------------------------------------------------ *)

  (* cc_exact_global's statement, derived. *)
  Theorem nd_cc_exact_global :
    (forall sigma B, UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma))).
  Proof.
    split.
    - intros H. split.
      + intros sigma e1 e2.
        exact (nd_tiny_cc1 sigma (fun B => H sigma B) sigma e1 e2 (GovernanceConverse.r_init _ _ _ _)).
      + intros sigma e Hinv.
        exact (nd_tiny_cc2 sigma (fun B => H sigma B) sigma e (GovernanceConverse.r_init _ _ _ _) Hinv).
    - intros [H1 H2] sigma B. apply (proj2 (nd_cc_exact_from sigma)).
      split; [intros t e1 e2 _; apply H1 | intros t e _ Hinv; apply H2; exact Hinv].
  Qed.

  (* Unique normal forms everywhere <-> CC1 /\ CC2 <-> free-history descent at every canonical
     start /\ state descent (CanonicalExecution.StateDescent, N := rho_star). *)
  Theorem nd_derived_global :
    ((forall sigma B, UN fstep (sigma, B)) <->
     ((forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
      (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma)))) /\
    ((forall sigma B, UN fstep (sigma, B)) <->
     (forall s0, FreeHistoryDescent s0) /\ StateDescent N apply).
  Proof.
    split; [exact nd_cc_exact_global |]. split.
    - intros H. split.
      + intros s0. exact (proj1 (proj1 (nd_derived_from s0) (fun B => H s0 B))).
      + apply (proj2 nd_state_descent_cc2). exact (proj2 (proj1 nd_cc_exact_global H)).
    - intros [HH HS] sigma B. apply (proj2 (nd_derived_from sigma)). split; [exact (HH sigma) |].
      intros e x _. symmetry. exact (HS e x).
  Qed.

  (* ------------------------------------------------------------------------------------------ *)
  (* The originals' statements.                                                                  *)
  (* ------------------------------------------------------------------------------------------ *)

  Definition CCExactFromStatement : Prop := forall s0,
    (forall B, UN fstep (s0, B)) <->
    ((forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma))).

  Definition CCExactStatement : Prop := forall s0,
    (forall sigma B, reach s0 sigma -> UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, reach s0 sigma -> gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach s0 sigma -> ~ valid sigma -> gov e sigma = gov e (rho sigma))).

  Definition CCExactGlobalStatement : Prop :=
    (forall sigma B, UN fstep (sigma, B)) <->
    ((forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma))).

  (* The derivation proves the three statements (without the originals). *)
  Theorem nd_derived_statements : CCExactFromStatement /\ CCExactStatement /\ CCExactGlobalStatement.
  Proof. split; [exact nd_cc_exact_from | split; [exact nd_cc_exact | exact nd_cc_exact_global]]. Qed.

  (* The derived framework statements are equivalent to the originals' statements (by the
     dictionary alone), and the originals inhabit exactly those statements. This is the only
     place cc_exact_from, cc_exact and cc_exact_global appear. *)
  Theorem nd_derived_matches_original :
    (CCExactFromStatement <->
       forall s0, (forall B, UN fstep (s0, B)) <-> FreeHistoryDescent s0 /\ StateDescentReach s0) /\
    (CCExactStatement <->
       forall s0, (forall sigma B, reach s0 sigma -> UN fstep (sigma, B)) <->
                  FreeHistoryDescent s0 /\ StateDescentReach s0) /\
    (CCExactGlobalStatement <->
       ((forall sigma B, UN fstep (sigma, B)) <->
        (forall s0, FreeHistoryDescent s0) /\ StateDescent N apply)) /\
    (CCExactFromStatement /\ CCExactStatement /\ CCExactGlobalStatement).
  Proof.
    assert (D : forall s0, CC1Reach s0 /\ CC2Reach s0 <-> FreeHistoryDescent s0 /\ StateDescentReach s0)
      by exact nd_dictionary_from.
    assert (DG : ((forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
                  (forall sigma e, ~ valid sigma -> gov e sigma = gov e (rho sigma))) <->
                 (forall s0, FreeHistoryDescent s0) /\ StateDescent N apply).
    { pose proof nd_derived_global as [G1 G2]. split; intros H.
      - exact (proj1 G2 (proj2 G1 H)).
      - exact (proj1 G1 (proj2 G2 H)). }
    unfold CCExactFromStatement, CCExactStatement, CCExactGlobalStatement.
    unfold CC1Reach, CC2Reach in D.
    split; [| split; [| split]].
    - split; intros H s0; specialize (H s0); specialize (D s0); tauto.
    - split; intros H s0; specialize (H s0); specialize (D s0); tauto.
    - tauto.
    - split; [| split].
      + exact (GovernanceConverse.cc_exact_from event_eq_dec apply rho rho_star valid Phi wfc
                 rho_star_reach rho_star_valid).
      + exact (GovernanceConverse.cc_exact event_eq_dec apply rho rho_star valid Phi wfc
                 rho_star_reach rho_star_valid).
      + exact (GovernanceConverse.cc_exact_global event_eq_dec apply rho rho_star valid Phi wfc
                 rho_star_reach rho_star_valid).
  Qed.
End Derived.

(* ============================================================================================ *)
(* With rho_star constructed from WFC (RhoStar.v): S is CC2 by the kernel's state_descent_iff_cc2. *)
(* ============================================================================================ *)

Section Constructed.
  Context {State Event : Type}.
  Variable event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply : Event -> State -> State.
  Variable rho   : State -> State.
  Variable valid : State -> Prop.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Variable Phi : State -> nat.
  Hypothesis wfc : forall s, ~ valid s -> Phi (rho s) < Phi s.

  Local Notation N := (RhoStar.rho_star rho valid valid_dec Phi).
  Local Notation fstep :=
    (step event_eq_dec apply rho valid (GovernanceConverse.free_enabled (State:=State))).

  Theorem nd_derived_global_constructed :
    ((forall sigma B, GovernanceConverse.UN fstep (sigma, B)) <->
     (forall s0, FreeHistoryDescent apply N s0) /\ StateDescent N apply) /\
    (StateDescent N apply <-> (forall s e, ~ valid s -> N (apply e s) = N (apply e (rho s)))).
  Proof.
    split.
    - exact (proj2 (nd_derived_global event_eq_dec apply rho N valid Phi wfc
                      (RhoStar.rs_reach_gov event_eq_dec apply rho valid valid_dec Phi wfc
                         (GovernanceConverse.free_enabled (State:=State)))
                      (RhoStar.rho_star_valid rho valid valid_dec Phi wfc))).
    - exact (state_descent_iff_cc2 apply rho valid valid_dec Phi wfc).
  Qed.
End Constructed.

(* ============================================================================================ *)
(* Non-vacuity: GovernanceConverse.v's one-boolean system (only false is valid, repair resets to *)
(* false) meets every hypothesis, and both sides of the derived theorems hold there.             *)
(* ============================================================================================ *)

Lemma nd_q_wfc : forall s, ~ GovernanceConverse.q_valid s ->
  GovernanceConverse.q_Phi (GovernanceConverse.q_rho s) < GovernanceConverse.q_Phi s.
Proof. intros [|] H; [simpl; auto | exfalso; apply H; reflexivity]. Qed.

Lemma nd_q_reach : forall s B,
  star GovernanceConverse.q_step (s, B) (GovernanceConverse.q_rho s, B).
Proof.
  intros [|] B.
  - eapply star_step; [apply st_comp; discriminate | apply star_refl].
  - apply star_refl.
Qed.

Theorem nd_nonvacuous :
  (forall s B, GovernanceConverse.UN GovernanceConverse.q_step (s, B)) /\
  (forall s0, FreeHistoryDescent GovernanceConverse.q_apply GovernanceConverse.q_rho s0) /\
  StateDescent GovernanceConverse.q_rho GovernanceConverse.q_apply.
Proof.
  destruct (nd_derived_global Bool.bool_dec GovernanceConverse.q_apply GovernanceConverse.q_rho
              GovernanceConverse.q_rho GovernanceConverse.q_valid GovernanceConverse.q_Phi
              nd_q_wfc nd_q_reach (fun _ => eq_refl)) as [G1 G2].
  assert (CC : (forall (s : bool) (e1 e2 : bool),
                  GovernanceConverse.q_rho (GovernanceConverse.q_apply e2
                    (GovernanceConverse.q_rho (GovernanceConverse.q_apply e1 s))) =
                  GovernanceConverse.q_rho (GovernanceConverse.q_apply e1
                    (GovernanceConverse.q_rho (GovernanceConverse.q_apply e2 s)))) /\
               (forall (s e : bool), ~ GovernanceConverse.q_valid s ->
                  GovernanceConverse.q_rho (GovernanceConverse.q_apply e s) =
                  GovernanceConverse.q_rho (GovernanceConverse.q_apply e (GovernanceConverse.q_rho s))))
    by (split; reflexivity).
  pose proof (proj2 G1 CC) as HU.
  split; [exact HU |]. exact (proj1 G2 HU).
Qed.
