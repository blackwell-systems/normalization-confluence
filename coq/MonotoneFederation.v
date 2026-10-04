(* MonotoneFederation.v: the monotone-cycles section of the federation paper, completed and
   checked against the paper's exact hypotheses, axiom-free (ROADMAP item 7, work package WP6).

   Paper: normalization_confluence_in_federated_registry_networks.tex, section "Monotone Cycles"
   (def:lattice-shared, thm:monotone-cycles, cor:acyclicity-monotone, rem:infinite-lattice) and
   the remark "Convexity and the monotone regime" after cor:modular. Row IDs are those of
   coq/PAPER-MAP.md (F22, F23, F24, F27, F31).

   Map from paper labels to theorems.
     F22 def:lattice-shared   The repair operator Phi is BUILT from a network: component states
                              S * Lc (shared, local), source entries read the component's own
                              shared value, a target reads its resolver Gam j applied to the
                              current states of its sources (a single-source morphism is the case
                              of one source). fed_def_lattice_shared_cyclic_hyps: Phi monotone
                              discharges every hypothesis of FederationEventsCycles' cyclic
                              normalizer (u_incr, u_sound, u_mono, u_fixed, Cover).
     F23 thm:monotone-cycles  Three claims beyond what Federation.v, Chaotic.v and ChaoticACC.v
                              already prove.
       (i) "Validity is preserved along the iteration by M1/R2 ..., so s* is federally valid."
           FALSE AS STATED: fed_thm_monotone_cycles_lfp_invalid. A 2-cycle of identity
           morphisms on bool (false < true), valid iff the shared flag is true: every hypothesis
           holds (complete lattice, Phi monotone, M1/R2, components WFC, no events so CC is
           vacuous, local normal forms valid), yet the least fixed point (false, false) is not
           federally valid, while (true, true) is a federally valid fixed point. The gap is the
           base case: bottom need not be valid, and M1/R2 only transport validity.
           Corrected (net_lfp_valid, net_Ncyc_correct, net_sweep_valid, net_iter_valid): if
           moreover every component is valid with bottom shared value
           (LValid l nbot), every Kleene iterate and every chaotic schedule from bottom stays
           valid, and the least fixed point is federally valid (under ACC; net_Ncyc_correct for
           the cyclic normalizer, net_Ncyc_idem discharges FederationEventsCycles' assumption
           lfp_valid). Non-vacuity: fed_valid_corrected_instance (the same 2-cycle with the
           order reversed, so that bottom is valid).
       (ii) "s* = sup_k Phi^k(bot)" on a complete lattice. FALSE AS STATED without continuity:
           fed_thm_monotone_cycles_kleene_formula_fails, on the complete chain
           0 < 1 < ... < w < w+1 (complete: w_complete_nn) with a monotone Phi whose Kleene sup
           w is not a fixed point; the least fixed point w+1 is never reached, not even in the
           limit. Corrected: kleene_sup_lfp (Phi preserving the sup of the Kleene chain makes the
           sup the least fixed point) and kleene_sup_valid (validity closed under sups of chains
           carries it to the lfp); non-vacuity kleene_sup_instance.
       (iii) "Consequently all processors ... converge": already refuted (cyc_counterexample);
           restated here against the paper's exact hypotheses with Phi built from the network:
           fed_thm_monotone_cycles_events_refuted. Corrected form: net_events_converge_iff and
           its instance fed_thm_monotone_cycles_events_corrected (the global condition GC is
           exact).
     F24 cor:acyclicity-monotone   negation_not_monotone (the excluded operator is antitone and
                              not monotone). The corollary holds for the repair normal form
                              (net_Ncyc_correct), not for event interleavings (F23 (iii)).
     F27 rem:infinite-lattice    Precise form: existence and uniqueness of the lfp do not need ACC,
                              but finite iteration need not reach it even for continuous Phi
                              (kleene_sup_instance: the lfp w is never reached), and for
                              non-continuous Phi not even the limit is the lfp (F23 (ii)). ACC
                              gives finite reachability (ChaoticACC.kleene_acc_lfp). Widening:
                              widening_sound (every post-fixed point bounds the iteration and the
                              lfp), widening_not_normal_form (a post-fixed point need not be a
                              fixed point, so a widened result is not the federated normal form).
     F31 remark "Convexity and the monotone regime": "if the sub-federation's repair is monotone
                              then so is rho_Fed^J". FALSE AS STATED: fed_rem_convexity_refuted
                              (a one-registry sub-federation with no internal edges: its repair is
                              monotone, but rho_Fed^J is the component normalizer, which is not).
                              Corrected: fed_rem_convexity_corrected (phase 1 monotone and Phi
                              monotone in the locals as well as in the shared values make
                              rho_Fed^J monotone); non-vacuity convexity_corrected_instance. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Newman NC.Federation NC.Chaotic NC.ChaoticACC NC.Trace NC.FederationEventsCycles.
Import ListNotations.

(* ======================================================================================= *)
(* Part 0. Order-theoretic helpers.                                                         *)
(* ======================================================================================= *)

Definition is_ub {L : Type} (le : L -> L -> Prop) (P : L -> Prop) (s : L) : Prop :=
  forall x, P x -> le x s.
Definition is_lub {L : Type} (le : L -> L -> Prop) (P : L -> Prop) (s : L) : Prop :=
  is_ub le P s /\ forall u, is_ub le P u -> le s u.

(* "Complete lattice", read classically: every subset has a least upper bound. Constructively
   this cannot be proved for any lattice with an undecidable membership test, so we prove its
   double negation, which is what classical completeness means intuitionistically. *)
Definition complete_nn {L : Type} (le : L -> L -> Prop) : Prop :=
  forall P : L -> Prop, ~ ~ exists s, is_lub le P s.

Lemma nn_lem : forall (Q G : Prop), (Q \/ ~ Q -> ~ ~ G) -> ~ ~ G.
Proof. intros Q G H HG. apply (H (or_intror (fun q => H (or_introl q) HG)) HG). Qed.

(* A finite lattice (bottom, binary joins, finite enumeration) is complete. *)
Section FiniteComplete.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.
  Variable join : L -> L -> L.
  Hypothesis join_l : forall a b, le a (join a b).
  Hypothesis join_r : forall a b, le b (join a b).
  Hypothesis join_lub : forall a b c, le a c -> le b c -> le (join a b) c.
  Variable all : list L.
  Hypothesis all_in : forall x, In x all.

  Lemma partial_lub_nn : forall (P : L -> Prop) xs, ~ ~ exists s,
      (forall x, In x xs -> P x -> le x s) /\
      (forall u, (forall x, In x xs -> P x -> le x u) -> le s u).
  Proof.
    intros P xs. induction xs as [| a xs IH].
    - intro H. apply H. exists bot. split; [intros x [] | intros; apply bot_least].
    - intro H. apply IH. intros [s [Hu Hl]].
      refine (nn_lem (P a) _ _ H). intros [Pa | nPa] H'.
      + apply H'. exists (join a s). split.
        * intros x [<- | Hx] Px; [apply join_l |].
          eapply le_trans; [apply Hu; assumption | apply join_r].
        * intros u Hu'. apply join_lub; [apply Hu'; [left; reflexivity | exact Pa] |].
          apply Hl. intros x Hx Px. apply Hu'; [right; exact Hx | exact Px].
      + apply H'. exists s. split.
        * intros x [<- | Hx] Px; [contradiction | apply Hu; assumption].
        * intros u Hu'. apply Hl. intros x Hx Px. apply Hu'; [right |]; assumption.
  Qed.

  Theorem finite_complete_nn : complete_nn le.
  Proof.
    intros P H. apply (partial_lub_nn P all). intros [s [Hu Hl]]. apply H. exists s. split.
    - intros x Px. apply Hu; [apply all_in | exact Px].
    - intros u Hu'. apply Hl. intros x _ Px. apply Hu'. exact Px.
  Qed.
End FiniteComplete.

(* Every post-fixed point (f w <= w) bounds the whole Kleene iteration. *)
Lemma iter_below_prefixed :
  forall {L : Type} (le : L -> L -> Prop) (f : L -> L) (bot : L),
    (forall x y z, le x y -> le y z -> le x z) ->
    (forall x y, le x y -> le (f x) (f y)) ->
    (forall x, le bot x) ->
    forall w, le (f w) w -> forall k, le (iter f bot k) w.
Proof.
  intros L le f bot Htr Hmono Hbot w Hw k. induction k as [| k IH]; simpl; [apply Hbot |].
  eapply Htr; [apply Hmono; exact IH | exact Hw].
Qed.

(* ======================================================================================= *)
(* Part 1. F22: the federated repair operator Phi built from morphisms and resolvers.       *)
(* ======================================================================================= *)

Section Network.
  (* Component states are pairs (shared, local): the paper's decomposition
     Sigma_j ~ S_j x L_j, with merge = pairing (one type for every component; heterogeneous
     components embed by a sum). *)
  Context {S Lc Loc Sh : Type}.

  (* The ordered shared domain (def:lattice-shared). *)
  Variable leS : S -> S -> Prop.
  Hypothesis leS_refl : forall a, leS a a.
  Hypothesis leS_trans : forall a b c, leS a b -> leS b c -> leS a c.
  Hypothesis leS_antisym : forall a b, leS a b -> leS b a -> a = b.
  Variable botS : S.
  Hypothesis botS_least : forall a, leS botS a.

  (* n components; Sh is the product of their shared values, with projections get and the
     tupling tab. *)
  Variable n : nat.
  Variable get : nat -> Sh -> S.
  Variable tab : (nat -> S) -> Sh.
  Hypothesis get_tab : forall g j, j < n -> get j (tab g) = g j.
  Hypothesis sh_ext : forall x y, (forall j, j < n -> get j x = get j y) -> x = y.

  (* Loc carries the components' normalized states (phase 1 output); lst l j is component j's. *)
  Variable lst : Loc -> nat -> S * Lc.

  (* Local validity of each component. *)
  Variable V : nat -> S * Lc -> Prop.

  (* The network: srcs j are the sources of j (empty for a source registry); Gam j is the
     resolver reading the source states in that order. A single-source morphism phi_ij is
     srcs j = [i], Gam j [t] = phi_ij t. R1 (source determinacy) holds by construction: Gam j
     never sees component j's local part. *)
  Variable srcs : nat -> list nat.
  Variable Gam : nat -> list (S * Lc) -> S.
  Hypothesis srcs_range : forall j i, j < n -> In i (srcs j) -> i < n.

  Definition nle (x y : Sh) : Prop := forall j, j < n -> leS (get j x) (get j y).
  Definition nbot : Sh := tab (fun _ => botS).
  Definition nupd (j : nat) (v : S) (x : Sh) : Sh :=
    tab (fun k => if Nat.eqb k j then v else get k x).

  (* sigma_j[sh -> x_j] *)
  Definition comp (l : Loc) (x : Sh) (j : nat) : S * Lc := (get j x, snd (lst l j)).

  (* Phi(s)_j: a source keeps its own (event-determined) shared value; a target reads its
     resolver on the current source states. *)
  Definition entry (l : Loc) (x : Sh) (j : nat) : S :=
    match srcs j with
    | [] => fst (lst l j)
    | ss => Gam j (map (comp l x) ss)
    end.
  Definition Phi (l : Loc) (x : Sh) : Sh := tab (entry l x).

  (* The repair of one target (one coordinate of Phi): FederationEventsCycles' u. *)
  Definition nu (l : Loc) (j : nat) (x : Sh) : Sh := nupd j (get j (Phi l x)) x.

  (* The paper's hypotheses. *)
  Definition Mono : Prop := forall l x y, nle x y -> nle (Phi l x) (Phi l y).
  Definition R2 : Prop :=
    forall j, j < n -> srcs j <> [] ->
      forall f : nat -> S * Lc, (forall i, In i (srcs j) -> V i (f i)) ->
      forall t, V j t -> V j (Gam j (map f (srcs j)), snd t).
  Definition LocValid (l : Loc) : Prop := forall j, j < n -> V j (lst l j).
  Definition LValid (l : Loc) (x : Sh) : Prop := forall j, j < n -> V j (comp l x j).
  (* Federal validity: every component locally valid and every morphism / resolution invariant
     satisfied (Phi l x = x says exactly that). *)
  Definition FedValid (l : Loc) (x : Sh) : Prop := LValid l x /\ Phi l x = x.

  Lemma nle_refl : forall x, nle x x.
  Proof. intros x j _. apply leS_refl. Qed.
  Lemma nle_trans : forall x y z, nle x y -> nle y z -> nle x z.
  Proof. intros x y z H1 H2 j Hj. eapply leS_trans; [apply H1 | apply H2]; exact Hj. Qed.
  Lemma nle_antisym : forall x y, nle x y -> nle y x -> x = y.
  Proof. intros x y H1 H2. apply sh_ext. intros j Hj. apply leS_antisym; auto. Qed.
  Lemma nbot_least : forall x, nle nbot x.
  Proof. intros x j Hj. unfold nbot. rewrite get_tab by exact Hj. apply botS_least. Qed.

  Lemma get_nupd : forall j v x k, k < n ->
    get k (nupd j v x) = if Nat.eqb k j then v else get k x.
  Proof. intros. unfold nupd. rewrite get_tab by assumption. reflexivity. Qed.

  Lemma nupd_get : forall j x, nupd j (get j x) x = x.
  Proof.
    intros j x. apply sh_ext. intros k Hk. rewrite get_nupd by exact Hk.
    destruct (Nat.eqb k j) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | reflexivity].
  Qed.

  Lemma Phi_get : forall l x j, j < n -> get j (Phi l x) = entry l x j.
  Proof. intros. unfold Phi. rewrite get_tab by assumption. reflexivity. Qed.

  (* ---- The cyclic normalizer's hypotheses, discharged from "Phi monotone". ---- *)

  Lemma nu_incr : forall l j x, nle x (Phi l x) -> nle x (nu l j x).
  Proof.
    intros l j x H k Hk. unfold nu. rewrite get_nupd by exact Hk.
    destruct (Nat.eqb k j) eqn:E; [apply Nat.eqb_eq in E; subst; apply H; exact Hk |].
    apply leS_refl.
  Qed.

  Lemma nu_sound : Mono -> forall l j x, nle x (Phi l x) -> nle (nu l j x) (Phi l (nu l j x)).
  Proof.
    intros Hm l j x H. pose proof (nu_incr l j x H) as Hxu. pose proof (Hm l _ _ Hxu) as HP.
    intros k Hk. unfold nu at 1. rewrite get_nupd by exact Hk.
    destruct (Nat.eqb k j) eqn:E.
    - apply Nat.eqb_eq in E; subst. apply HP. exact Hk.
    - eapply leS_trans; [apply H; exact Hk | apply HP; exact Hk].
  Qed.

  Lemma nu_mono : Mono -> forall l j x y, nle x y -> nle (nu l j x) (nu l j y).
  Proof.
    intros Hm l j x y H k Hk. unfold nu. rewrite !get_nupd by exact Hk.
    destruct (Nat.eqb k j) eqn:E; [apply Nat.eqb_eq in E; subst; apply (Hm l x y H); exact Hk |].
    apply H. exact Hk.
  Qed.

  Lemma nu_fixed : forall l j x, Phi l x = x -> nu l j x = x.
  Proof. intros l j x H. unfold nu. rewrite H. apply nupd_get. Qed.

  Lemma nu_cover : Cover Loc Sh Phi nu (seq 0 n).
  Proof.
    intros l x H. apply sh_ext. intros j Hj.
    assert (Hin : In j (seq 0 n)) by (apply in_seq; lia).
    specialize (H j Hin). unfold nu in H.
    rewrite <- H at 2. rewrite get_nupd by exact Hj. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (* F22, discharged: Phi built from the network, monotone, satisfies every hypothesis of the
     cyclic normalizer (FederationEventsCycles, section Cyclic). *)
  Theorem fed_def_lattice_shared_cyclic_hyps :
    Mono ->
    (forall x, nle x x) /\ (forall x y z, nle x y -> nle y z -> nle x z) /\
    (forall x y, nle x y -> nle y x -> x = y) /\ (forall x, nle nbot x) /\
    (forall l j x, FederationEventsCycles.sound Loc Sh nle Phi l x -> nle x (nu l j x)) /\
    (forall l j x, FederationEventsCycles.sound Loc Sh nle Phi l x ->
                   FederationEventsCycles.sound Loc Sh nle Phi l (nu l j x)) /\
    (forall l j x y, nle x y -> nle (nu l j x) (nu l j y)) /\
    (forall l j x, Phi l x = x -> nu l j x = x) /\
    Cover Loc Sh Phi nu (seq 0 n).
  Proof.
    intros Hm. split; [exact nle_refl |]. split; [exact nle_trans |].
    split; [exact nle_antisym |]. split; [exact nbot_least |].
    split; [exact nu_incr |]. split; [exact (nu_sound Hm) |].
    split; [exact (nu_mono Hm) |]. split; [exact nu_fixed | exact nu_cover].
  Qed.

  (* ---- Validity along the iteration (F23 (i), corrected). ---- *)

  Lemma entry_valid : R2 -> forall l x j, j < n -> LocValid l -> LValid l x ->
    V j (entry l x j, snd (lst l j)).
  Proof.
    intros HR l x j Hj Hl Hx. unfold entry. destruct (srcs j) as [| i r] eqn:E.
    - rewrite <- surjective_pairing. apply Hl. exact Hj.
    - assert (Hne : srcs j <> []) by (rewrite E; discriminate).
      pose proof (HR j Hj Hne (comp l x)) as H. rewrite E in H.
      apply (H (fun i Hi => Hx i (srcs_range j i Hj (eq_ind_r (fun ls => In i ls) Hi E)))
               (comp l x j) (Hx j Hj)).
  Qed.

  Lemma Phi_valid : R2 -> forall l x, LocValid l -> LValid l x -> LValid l (Phi l x).
  Proof.
    intros HR l x Hl Hx j Hj. unfold comp. rewrite Phi_get by exact Hj.
    apply entry_valid; assumption.
  Qed.

  Lemma nu_valid : R2 -> forall l j x, LocValid l -> LValid l x -> LValid l (nu l j x).
  Proof.
    intros HR l j x Hl Hx k Hk. unfold comp, nu. rewrite get_nupd by exact Hk.
    destruct (Nat.eqb k j) eqn:E.
    - apply Nat.eqb_eq in E; subst. rewrite Phi_get by exact Hk. apply entry_valid; assumption.
    - apply Hx. exact Hk.
  Qed.

  (* Every finite chaotic schedule (any list of targets, any order, repetitions allowed) from a
     valid state stays valid. *)
  Theorem net_sweep_valid : R2 -> forall l js x, LocValid l -> LValid l x ->
    LValid l (sweep Loc Sh nu l js x).
  Proof.
    intros HR l js. induction js as [| j js IH]; intros x Hl Hx; [exact Hx |].
    simpl. apply IH; [exact Hl | apply nu_valid; assumption].
  Qed.

  (* Every Kleene iterate from a valid bottom is valid. *)
  Theorem net_iter_valid : R2 -> forall l, LocValid l -> LValid l nbot ->
    forall k, LValid l (iter (Phi l) nbot k).
  Proof.
    intros HR l Hl Hb k. induction k as [| k IH]; [exact Hb |].
    simpl. apply Phi_valid; assumption.
  Qed.

  (* F23 (i), corrected: under ACC, with bottom valid, the least fixed point is federally
     valid. *)
  Theorem net_lfp_valid :
    R2 -> Mono -> well_founded (ascends nle) -> (forall x y : Sh, {x = y} + {x <> y}) ->
    forall l, LocValid l -> LValid l nbot ->
    forall m, is_lfp nle (Phi l) m -> FedValid l m.
  Proof.
    intros HR Hm Hacc Hdec l Hl Hb m Hlfp.
    destruct (kleene_acc_stabilizes nle (Phi l) (Hm l) nbot nbot_least Hacc
                (fun x => Hdec (Phi l x) x)) as [k Hk].
    pose proof (kleene_lfp nle (Phi l) (Hm l) nbot nbot_least k Hk) as Hk'.
    rewrite (lfp_unique nle nle_antisym (Phi l) m _ Hlfp Hk').
    split; [apply net_iter_valid; assumption | exact Hk].
  Qed.

  (* ---- The cyclic normalizer on the network. ---- *)
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, nle x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable rho1 : Loc * Sh -> Loc * Sh.   (* phase 1: every component's own normalizer *)
  Variable K : nat.
  Hypothesis K_big : height < K.

  Definition Nnet : Loc * Sh -> Loc * Sh := Ncyc_with Loc Sh nbot sh_eq_dec nu rho1 K (seq 0 n).

  (* F23 corrected, for gsm's cyclic normalizer on a network: the normal form is the least
     fixed point of the repair built from the network, and it is federally valid, provided
     phase 1 yields valid components that remain valid with bottom shared values. *)
  Theorem net_Ncyc_correct :
    Mono -> R2 ->
    (forall t, LocValid (fst (rho1 t))) -> (forall t, LValid (fst (rho1 t)) nbot) ->
    forall t, fst (Nnet t) = fst (rho1 t) /\ is_lfp nle (Phi (fst (rho1 t))) (snd (Nnet t)) /\
              FedValid (fst (Nnet t)) (snd (Nnet t)).
  Proof.
    intros Hm HR Hl Hb t.
    destruct (cyc_N_lfp Loc Sh nle nle_refl nle_trans nbot nbot_least rank rank_strict height
                rank_bound sh_eq_dec Phi nu nu_incr (nu_sound Hm) (nu_mono Hm) nu_fixed rho1 K
                K_big (seq 0 n) nu_cover t) as [Hf Hlfp].
    split; [exact Hf |]. split; [exact Hlfp |].
    unfold Nnet in *. rewrite Hf.
    apply (net_lfp_valid HR Hm (finite_height_acc nle rank height rank_strict rank_bound)
             sh_eq_dec); [apply Hl | apply Hb | exact Hlfp].
  Qed.

  (* The assumption lfp_valid of FederationEventsCycles.cyc_N_idem, now discharged. *)
  Theorem net_Ncyc_idem :
    Mono -> R2 ->
    (forall t, LocValid (fst (rho1 t))) -> (forall t, LValid (fst (rho1 t)) nbot) ->
    (forall s, FedValid (fst s) (snd s) -> rho1 s = s) ->
    forall t, Nnet (Nnet t) = Nnet t.
  Proof.
    intros Hm HR Hl Hb Hr t.
    apply (cyc_N_idem Loc Sh nle nle_refl nle_trans nbot nbot_least rank rank_strict height
             rank_bound sh_eq_dec Phi nu nu_incr (nu_sound Hm) (nu_mono Hm) nu_fixed rho1 K K_big
             (fun s => FedValid (fst s) (snd s)) Hr).
    - intros t' m Hlfp. simpl.
      apply (net_lfp_valid HR Hm (finite_height_acc nle rank height rank_strict rank_bound)
               sh_eq_dec); [apply Hl | apply Hb | exact Hlfp].
    - exact nu_cover.
  Qed.

  (* F23 (iii), corrected: on the network, governed event steps converge on all trace-equivalent
     sequences from s0 exactly when the global condition holds. *)
  Theorem net_events_converge_iff :
    forall (E : Type) (ev : E -> Loc * Sh -> Loc * Sh) (reg : E -> nat) (I : E -> E -> Prop) s0,
      GC (Loc * Sh) E Nnet ev reg I s0 <-> Converges (Loc * Sh) E Nnet ev reg I s0.
  Proof. intros. apply (cyc_events_converge_iff Loc Sh nbot sh_eq_dec Phi nu). exact nu_cover. Qed.
End Network.

(* ======================================================================================= *)
(* Part 2. Two-component networks on bool * bool: shared helpers.                          *)
(* ======================================================================================= *)

Definition bget (j : nat) (x : bool * bool) : bool := match j with 0 => fst x | _ => snd x end.
Definition btab (g : nat -> bool) : bool * bool := (g 0, g 1).

Lemma bget_tab : forall g j, j < 2 -> bget j (btab g) = g j.
Proof. intros g [| [| j]] H; [reflexivity | reflexivity | lia]. Qed.

Lemma bsh_ext : forall x y : bool * bool, (forall j, j < 2 -> bget j x = bget j y) -> x = y.
Proof.
  intros [a b] [c d] H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H 1 ltac:(lia)) as H1.
  simpl in H0, H1. subst. reflexivity.
Qed.

Definition beq2_dec : forall x y : bool * bool, {x = y} + {x <> y}.
Proof. decide equality; apply bool_dec. Defined.

(* A 2-cycle: component 0's shared value is fed by component 1, and 1's by 0. *)
Definition bsrcs (j : nat) : list nat := match j with 0 => [1] | 1 => [0] | _ => [] end.

Lemma bsrcs_range : forall j i, j < 2 -> In i (bsrcs j) -> i < 2.
Proof.
  intros [| [| j]] i Hj H; simpl in H;
    [destruct H as [<- | []]; lia | destruct H as [<- | []]; lia | lia].
Qed.

(* false < true, and its reverse. *)
Definition bleq (a b : bool) : Prop := implb a b = true.
Definition bleqr (a b : bool) : Prop := implb b a = true.

Lemma bleq_refl : forall a, bleq a a. Proof. destruct a; reflexivity. Qed.
Lemma bleq_trans : forall a b c, bleq a b -> bleq b c -> bleq a c.
Proof. destruct a, b, c; unfold bleq; simpl; congruence. Qed.
Lemma bleq_antisym : forall a b, bleq a b -> bleq b a -> a = b.
Proof. destruct a, b; unfold bleq; simpl; congruence. Qed.
Lemma bleq_bot : forall a, bleq false a. Proof. destruct a; reflexivity. Qed.
Lemma bleqr_refl : forall a, bleqr a a. Proof. destruct a; reflexivity. Qed.
Lemma bleqr_trans : forall a b c, bleqr a b -> bleqr b c -> bleqr a c.
Proof. destruct a, b, c; unfold bleqr; simpl; congruence. Qed.
Lemma bleqr_antisym : forall a b, bleqr a b -> bleqr b a -> a = b.
Proof. destruct a, b; unfold bleqr; simpl; congruence. Qed.
Lemma bleqr_bot : forall a, bleqr true a. Proof. destruct a; reflexivity. Qed.

Lemma nle2_iff : forall (le : bool -> bool -> Prop) x y,
  nle le 2 bget x y <-> le (fst x) (fst y) /\ le (snd x) (snd y).
Proof.
  intros le x y. split.
  - intros H. split; [apply (H 0) | apply (H 1)]; lia.
  - intros [H0 H1] [| [| j]] Hj; [exact H0 | exact H1 | lia].
Qed.

Ltac bdes := repeat match goal with
  | x : bool * bool |- _ => destruct x
  | x : B2 |- _ => destruct x
  | x : bool * unit |- _ => destruct x
  | x : unit |- _ => destruct x
  | b : bool |- _ => destruct b
  end.

(* bool * bool is a complete lattice under either componentwise order. *)
Lemma b2_complete : complete_nn (nle bleq 2 bget).
Proof.
  apply (finite_complete_nn (nle bleq 2 bget)) with
    (bot := (false, false)) (join := fun x y => (fst x || fst y, snd x || snd y))
    (all := [(false, false); (false, true); (true, false); (true, true)]).
  - intros x y z H1 H2. apply nle2_iff in H1, H2. apply nle2_iff.
    destruct H1, H2; split; eapply bleq_trans; eassumption.
  - intros x. apply nle2_iff. split; apply bleq_bot.
  - intros a b. apply nle2_iff. bdes; split; reflexivity.
  - intros a b. apply nle2_iff. bdes; split; reflexivity.
  - intros a b c Ha Hb. apply nle2_iff in Ha, Hb. apply nle2_iff. revert Ha Hb.
    bdes; unfold bleq; simpl; intuition congruence.
  - intros x. bdes; simpl; tauto.
Qed.

Lemma b2r_complete : complete_nn (nle bleqr 2 bget).
Proof.
  apply (finite_complete_nn (nle bleqr 2 bget)) with
    (bot := (true, true)) (join := fun x y => (fst x && fst y, snd x && snd y))
    (all := [(false, false); (false, true); (true, false); (true, true)]).
  - intros x y z H1 H2. apply nle2_iff in H1, H2. apply nle2_iff.
    destruct H1, H2; split; eapply bleqr_trans; eassumption.
  - intros x. apply nle2_iff. split; apply bleqr_bot.
  - intros a b. apply nle2_iff. bdes; split; reflexivity.
  - intros a b. apply nle2_iff. bdes; split; reflexivity.
  - intros a b c Ha Hb. apply nle2_iff in Ha, Hb. apply nle2_iff. revert Ha Hb.
    bdes; unfold bleqr; simpl; intuition congruence.
  - intros x. bdes; simpl; tauto.
Qed.

(* ======================================================================================= *)
(* Part 3. F23 (i): the least fixed point need not be federally valid.                      *)
(* ======================================================================================= *)

(* Two registries, each with state (shared flag, unit), valid iff the flag is set. Each one's
   shared flag is a copy of the other's (identity morphisms, a 2-cycle). The local normal forms
   are (true, tt). *)
Definition Vflag (_ : nat) (t : bool * unit) : Prop := fst t = true.
Definition idGam (_ : nat) (ts : list (bool * unit)) : bool :=
  match ts with [t] => fst t | _ => false end.
Definition lone (_ : unit) (_ : nat) : bool * unit := (true, tt).

(* Component compensation: set the flag (WFC: one step to a valid state, valid states fixed). *)
Definition rflag (t : bool * unit) : bool * unit := (true, snd t).

Definition Phi1 : unit -> bool * bool -> bool * bool := Phi bget btab lone bsrcs idGam.

Lemma Phi1_swap : forall l x, Phi1 l x = (snd x, fst x).
Proof. intros l [a b]. reflexivity. Qed.

Lemma flag_mono : Mono bleq 2 bget btab lone bsrcs idGam.
Proof.
  intros l x y H. fold Phi1. rewrite !Phi1_swap. apply nle2_iff in H. apply nle2_iff.
  simpl. tauto.
Qed.

Lemma flag_R2 : R2 2 Vflag bsrcs idGam.
Proof.
  intros [| [| j]] Hj Hne f Hf t Ht; simpl; unfold Vflag; simpl;
    [apply (Hf 1); left; reflexivity | apply (Hf 0); left; reflexivity | lia].
Qed.

Theorem fed_thm_monotone_cycles_lfp_invalid :
  (* the hypotheses of thm:monotone-cycles *)
  complete_nn (nle bleq 2 bget) /\
  Mono bleq 2 bget btab lone bsrcs idGam /\
  R2 2 Vflag bsrcs idGam /\
  (forall j t, Vflag j (rflag t) /\ (Vflag j t -> rflag t = t)) /\
  LocValid 2 lone Vflag tt /\
  (* the least fixed point, reached by Kleene iteration at once *)
  (forall k, iter (Phi1 tt) (nbot false btab) k = (false, false)) /\
  is_lfp (nle bleq 2 bget) (Phi1 tt) (false, false) /\
  (* is not federally valid, although a federally valid fixed point exists *)
  ~ FedValid 2 bget btab lone Vflag bsrcs idGam tt (false, false) /\
  FedValid 2 bget btab lone Vflag bsrcs idGam tt (true, true) /\
  (* the cyclic normalizer moves even the valid state (true, true) to the invalid one *)
  Nnet false 2 bget btab lone bsrcs idGam beq2_dec (fun t => t) 3 (tt, (true, true)) =
    (tt, (false, false)) /\
  (* and the missing hypothesis: bottom is invalid *)
  ~ LValid 2 bget lone Vflag tt (nbot false btab).
Proof.
  assert (Hit : forall k, iter (Phi1 tt) (nbot false btab) k = (false, false)).
  { induction k as [| k IH]; [reflexivity | simpl; rewrite IH; reflexivity]. }
  split; [exact b2_complete |]. split; [exact flag_mono |]. split; [exact flag_R2 |].
  split; [intros j [b []]; unfold Vflag, rflag; simpl; split; [reflexivity | intros ->; reflexivity] |].
  split; [intros j _; reflexivity |].
  split; [exact Hit |].
  split.
  { split; [reflexivity |]. intros x Hx. apply nle2_iff. split; apply bleq_bot. }
  split; [intros [Hv _]; specialize (Hv 0 ltac:(lia)); discriminate Hv |].
  split; [split; [intros [| [| j]] Hj; [reflexivity | reflexivity | lia] | reflexivity] |].
  split; [reflexivity |].
  intros Hv. specialize (Hv 0 ltac:(lia)). discriminate Hv.
Qed.

(* Non-vacuity of the corrected hypotheses: the same 2-cycle with the order reversed
   (true < false), so that bottom (true, true) is valid. Every hypothesis of net_Ncyc_correct
   and net_Ncyc_idem is discharged; the normal form is the valid least fixed point. *)
Definition rrank (x : bool * bool) : nat := (if fst x then 0 else 1) + (if snd x then 0 else 1).

Lemma rrank_strict : forall x y, nle bleqr 2 bget x y -> x <> y -> rrank x < rrank y.
Proof.
  intros x y H Hne. apply nle2_iff in H. revert H Hne. bdes; unfold bleqr, rrank; simpl;
    intuition (try congruence; try lia).
Qed.
Lemma rrank_bound : forall x, rrank x <= 2. Proof. intros; bdes; unfold rrank; simpl; lia. Qed.

Lemma flagr_mono : Mono bleqr 2 bget btab lone bsrcs idGam.
Proof.
  intros l x y H. fold Phi1. rewrite !Phi1_swap. apply nle2_iff in H. apply nle2_iff.
  simpl. tauto.
Qed.

Definition rho1u (t : unit * (bool * bool)) : unit * (bool * bool) := (tt, snd t).

Definition Nflag : unit * (bool * bool) -> unit * (bool * bool) :=
  Nnet true 2 bget btab lone bsrcs idGam beq2_dec rho1u 3.

Theorem fed_valid_corrected_instance :
  complete_nn (nle bleqr 2 bget) /\
  LValid 2 bget lone Vflag tt (nbot true btab) /\
  (forall t, fst (Nflag t) = tt /\ is_lfp (nle bleqr 2 bget) (Phi1 tt) (snd (Nflag t)) /\
             FedValid 2 bget btab lone Vflag bsrcs idGam (fst (Nflag t)) (snd (Nflag t))) /\
  (forall t, Nflag (Nflag t) = Nflag t) /\
  Nflag (tt, (false, false)) = (tt, (true, true)).
Proof.
  assert (Hb : forall t, LValid 2 bget lone Vflag (fst (rho1u t)) (nbot true btab)).
  { intros t [| [| j]] Hj; [reflexivity | reflexivity | lia]. }
  assert (Hl : forall t, LocValid 2 lone Vflag (fst (rho1u t))) by (intros t j _; reflexivity).
  split; [exact b2r_complete |]. split; [exact (Hb (tt, (true, true))) |].
  split.
  { intros t.
    destruct (net_Ncyc_correct bleqr bleqr_refl bleqr_trans bleqr_antisym true bleqr_bot 2 bget btab
                bget_tab bsh_ext lone Vflag bsrcs idGam bsrcs_range rrank rrank_strict 2 rrank_bound
                beq2_dec rho1u 3 ltac:(lia) flagr_mono flag_R2 Hl Hb t) as [H1 [H2 H3]].
    split; [destruct (fst (Nflag t)); reflexivity |]. split; [exact H2 | exact H3]. }
  split.
  { apply (net_Ncyc_idem bleqr bleqr_refl bleqr_trans bleqr_antisym true bleqr_bot 2 bget btab
             bget_tab bsh_ext lone Vflag bsrcs idGam bsrcs_range rrank rrank_strict 2 rrank_bound
             beq2_dec rho1u 3 ltac:(lia) flagr_mono flag_R2 Hl Hb).
    intros [[] x] _. reflexivity. }
  reflexivity.
Qed.

(* ======================================================================================= *)
(* Part 4. F23 (iii): "all processors converge", refuted under the paper's exact hypotheses, *)
(* with Phi built from the network (restating FederationEventsCycles.cyc_counterexample).  *)
(* ======================================================================================= *)

(* Components: state (shared flag, local alarm); every state valid. Component 0's shared flag
   is fed by component 1 (its alarm or its shared flag), and vice versa: Phi l x is exactly
   FederationEventsCycles.cF l x. Loc = (alarm of 0, alarm of 1). *)
Definition alst (l : bool * bool) (j : nat) : bool * bool :=
  match j with 0 => (false, fst l) | _ => (false, snd l) end.
Definition Vall (_ : nat) (_ : bool * bool) : Prop := True.
Definition orGam (_ : nat) (ts : list (bool * bool)) : bool :=
  match ts with [t] => snd t || fst t | _ => false end.

Definition Phi3 : bool * bool -> bool * bool -> bool * bool := Phi bget btab alst bsrcs orGam.

Lemma Phi3_cF : forall l x, Phi3 l x = cF l x.
Proof. intros [a b] [c d]. reflexivity. Qed.

Definition brank (x : bool * bool) : nat := (if fst x then 1 else 0) + (if snd x then 1 else 0).
Lemma brank_strict : forall x y, nle bleq 2 bget x y -> x <> y -> brank x < brank y.
Proof.
  intros x y H Hne. apply nle2_iff in H. revert H Hne. bdes; unfold bleq, brank; simpl;
    intuition (try congruence; try lia).
Qed.
Lemma brank_bound : forall x, brank x <= 2. Proof. intros; bdes; unfold brank; simpl; lia. Qed.

Lemma or_mono : Mono bleq 2 bget btab alst bsrcs orGam.
Proof.
  intros l x y H. fold Phi3. rewrite !Phi3_cF. apply nle2_iff in H. apply nle2_iff.
  revert H. bdes; unfold bleq, cF; simpl; intuition congruence.
Qed.

Lemma or_R2 : R2 2 Vall bsrcs orGam.
Proof. unfold R2; intros; exact I. Qed.

Definition rho1id (t : (bool * bool) * (bool * bool)) := t.

Definition Nor : (bool * bool) * (bool * bool) -> (bool * bool) * (bool * bool) :=
  Nnet false 2 bget btab alst bsrcs orGam beq2_dec rho1id 3.

Theorem fed_thm_monotone_cycles_events_refuted :
  (* the hypotheses of thm:monotone-cycles *)
  complete_nn (nle bleq 2 bget) /\
  Mono bleq 2 bget btab alst bsrcs orGam /\
  R2 2 Vall bsrcs orGam /\
  (forall j t, Vall j t) /\                       (* WFC: every state valid, no compensation *)
  (forall a b, xreg a = xreg b -> a = b) /\       (* one event per registry: CC is vacuous *)
  (forall l x, Phi3 l x = cF l x) /\
  (* the normal form is the federally valid least fixed point *)
  (forall t, is_lfp (nle bleq 2 bget) (Phi3 (fst t)) (snd (Nor t)) /\
             FedValid 2 bget btab alst Vall bsrcs orGam (fst (Nor t)) (snd (Nor t))) /\
  (* yet two trace-equivalent event sequences diverge *)
  tequiv (Ifd xev xreg xI) [LatchA; RaiseB'] [RaiseB'; LatchA] /\
  grun _ xev Nor xstep [LatchA; RaiseB'] xs0 = ((false, true), (true, true)) /\
  grun _ xev Nor xstep [RaiseB'; LatchA] xs0 = ((true, true), (true, true)) /\
  ~ GC _ xev Nor xstep xreg xI xs0 /\
  ~ Converges _ xev Nor xstep xreg xI xs0.
Proof.
  assert (Ht : tequiv (Ifd xev xreg xI) [LatchA; RaiseB'] [RaiseB'; LatchA]).
  { apply (teq_swap _ [] LatchA RaiseB' []). left. discriminate. }
  assert (Hn : ~ Converges _ xev Nor xstep xreg xI xs0).
  { intro H. pose proof (H _ _ Ht) as Hd. discriminate Hd. }
  split; [exact b2_complete |]. split; [exact or_mono |]. split; [exact or_R2 |].
  split; [intros; exact I |].
  split; [intros [] [] H; (reflexivity || discriminate H) |].
  split; [exact Phi3_cF |].
  split.
  { intros t.
    destruct (net_Ncyc_correct bleq bleq_refl bleq_trans bleq_antisym false bleq_bot 2 bget btab
                bget_tab bsh_ext alst Vall bsrcs orGam bsrcs_range brank brank_strict 2 brank_bound
                beq2_dec rho1id 3 ltac:(lia) or_mono or_R2 (fun _ _ _ => I) (fun _ _ _ => I) t)
      as [_ [H2 H3]].
    split; [exact H2 | exact H3]. }
  split; [exact Ht |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| exact Hn].
  intro H. apply Hn. apply gc_sufficient. exact H.
Qed.

(* F23 (iii) corrected, on the same network: convergence holds exactly when GC holds. *)
Theorem fed_thm_monotone_cycles_events_corrected :
  forall (E : Type) (ev : E -> _ -> _) (reg : E -> nat) (I : E -> E -> Prop) s0,
    GC _ E Nor ev reg I s0 <-> Converges _ E Nor ev reg I s0.
Proof.
  intros. apply (net_events_converge_iff false 2 bget btab bget_tab bsh_ext alst bsrcs orGam
                   beq2_dec rho1id 3).
Qed.

(* F24: the operator excluded by cor:acyclicity-monotone, negation, is not monotone. *)
Theorem negation_not_monotone : ~ (forall a b, bleq a b -> bleq (negb a) (negb b)).
Proof. intro H. specialize (H false true eq_refl). discriminate H. Qed.

(* ======================================================================================= *)
(* Part 5. F23 (ii) and F27: infinite complete lattices.                                    *)
(* ======================================================================================= *)

(* The chain 0 < 1 < 2 < ... < w < w+1 (ordinal w+2): Fin k, Om = w, Om1 = w+1. *)
Inductive W : Type := Fin (k : nat) | Om | Om1.

Definition wleb (x y : W) : bool :=
  match x, y with
  | Fin a, Fin b => Nat.leb a b
  | Fin _, _ => true
  | Om, Fin _ => false
  | Om, _ => true
  | Om1, Om1 => true
  | Om1, _ => false
  end.
Definition wle (x y : W) : Prop := wleb x y = true.

Lemma wle_refl : forall x, wle x x.
Proof. intros [k | |]; unfold wle; simpl; [apply Nat.leb_refl | reflexivity | reflexivity]. Qed.
Lemma wle_trans : forall x y z, wle x y -> wle y z -> wle x z.
Proof.
  intros [a | |] [b | |] [c | |]; unfold wle; simpl; try discriminate; try reflexivity.
  intros H1 H2. apply Nat.leb_le in H1, H2. apply Nat.leb_le. lia.
Qed.
Lemma wle_antisym : forall x y, wle x y -> wle y x -> x = y.
Proof.
  intros [a | |] [b | |]; unfold wle; simpl; try discriminate; try reflexivity.
  intros H1 H2. apply Nat.leb_le in H1, H2. f_equal. lia.
Qed.
Lemma wbot_least : forall x, wle (Fin 0) x.
Proof. intros [k | |]; reflexivity. Qed.

(* w+2 is a complete lattice (classically: every subset has a supremum). *)
Theorem w_complete_nn : complete_nn wle.
Proof.
  intros P H.
  refine (nn_lem (P Om1) _ _ H). intros [H1 | n1] H'.
  { apply H'. exists Om1. split.
    - intros x _. destruct x; reflexivity.
    - intros u Hu. exact (Hu Om1 H1). }
  refine (nn_lem (P Om) _ _ H'). intros [H0 | n0] H''.
  { apply H''. exists Om. split.
    - intros [k | |] Px; [reflexivity | reflexivity | contradiction].
    - intros u Hu. exact (Hu Om H0). }
  refine (nn_lem (exists k, P (Fin k) /\ forall m, P (Fin m) -> m <= k) _ _ H'').
  intros [[k [Pk Hk]] | nmax] H3.
  { apply H3. exists (Fin k). split.
    - intros [m | |] Px; [apply Nat.leb_le, Hk, Px | contradiction | contradiction].
    - intros u Hu. exact (Hu (Fin k) Pk). }
  refine (nn_lem (exists m, P (Fin m)) _ _ H3). intros [[m Pm] | nemp] H4.
  - apply H4. exists Om. split.
    + intros [k | |] Px; [reflexivity | contradiction | contradiction].
    + intros u Hu. destruct u as [k | |]; [exfalso | reflexivity | reflexivity].
      assert (Hb : forall m', P (Fin m') -> m' <= k)
        by (intros m' Pm'; apply Nat.leb_le; exact (Hu _ Pm')).
      clear Hu H4 H3 H'' H' H. revert Hb. induction k as [| k IH]; intros Hb.
      * apply nmax. exists 0. split.
        -- assert (m = 0) by (specialize (Hb m Pm); lia). subst. exact Pm.
        -- intros m' Pm'. apply Hb. exact Pm'.
      * refine (nn_lem (P (Fin (S k))) False _ (fun f => f)). intros [Ps | nPs] HF.
        -- apply HF. apply nmax. exists (S k). split; [exact Ps | exact Hb].
        -- apply HF. apply IH. intros m' Pm'. specialize (Hb m' Pm').
           destruct (Nat.eq_dec m' (S k)) as [-> | Ne]; [contradiction | lia].
  - apply H4. exists (Fin 0). split.
    + intros [k | |] Px; [exfalso; apply nemp; exists k; exact Px | contradiction | contradiction].
    + intros u _. apply wbot_least.
Qed.

Lemma wle_dec : forall x y, {wle x y} + {~ wle x y}.
Proof. intros x y. unfold wle. destruct (wleb x y); [left; reflexivity | right; discriminate]. Qed.

Definition W_eq_dec : forall x y : W, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(* The Kleene chain from bottom and its supremum. *)
Definition kchain (f : W -> W) : W -> Prop := fun x => exists k, x = iter f (Fin 0) k.

(* A monotone operator that is not continuous: it jumps from w to w+1. *)
Definition wPhi (x : W) : W := match x with Fin k => Fin (S k) | _ => Om1 end.

Lemma wPhi_mono : forall x y, wle x y -> wle (wPhi x) (wPhi y).
Proof.
  intros [a | |] [b | |]; unfold wle; simpl; try discriminate; try reflexivity. tauto.
Qed.

Lemma wPhi_iter : forall k, iter wPhi (Fin 0) k = Fin k.
Proof. induction k as [| k IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

Lemma Om_lub_chain : forall f, (forall k, iter f (Fin 0) k = Fin k) -> is_lub wle (kchain f) Om.
Proof.
  intros f Hf. split.
  - intros x [k ->]. rewrite Hf. reflexivity.
  - intros u Hu. destruct u as [m | |]; [| reflexivity | reflexivity].
    specialize (Hu (Fin (S m)) (ex_intro _ (S m) (eq_sym (Hf (S m))))).
    apply Nat.leb_le in Hu. lia.
Qed.

(* F23 (ii): "s* = sup_k Phi^k(bot)" is false on a complete lattice without continuity, and
   no iteration from bottom, finite or in the limit, reaches the least fixed point. *)
Theorem fed_thm_monotone_cycles_kleene_formula_fails :
  complete_nn wle /\ (forall x y, wle x y -> wle (wPhi x) (wPhi y)) /\
  is_lub wle (kchain wPhi) Om /\ wPhi Om <> Om /\
  is_lfp wle wPhi Om1 /\ (forall x, wPhi x = x -> x = Om1) /\
  (forall k, iter wPhi (Fin 0) k <> Om1).
Proof.
  split; [exact w_complete_nn |]. split; [exact wPhi_mono |].
  split; [apply Om_lub_chain; exact wPhi_iter |]. split; [discriminate |].
  split; [split; [reflexivity | intros [k | |] H; try unfold fixed_point in H; simpl in H; try discriminate; try (injection H; lia); reflexivity] |].
  split.
  - intros [k | |] H; try unfold fixed_point in H; simpl in H; [injection H; lia | discriminate | reflexivity].
  - intros k. rewrite wPhi_iter. discriminate.
Qed.

(* Corrected (Kleene's theorem): if Phi preserves the supremum of its Kleene chain, that
   supremum is the least fixed point; if moreover validity holds at bottom, is preserved by Phi
   and is closed under suprema of ascending chains, the least fixed point is valid. *)
Section KleeneSup.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable f : L -> L.
  Hypothesis f_mono : forall x y, le x y -> le (f x) (f y).
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  Variable s : L.
  Hypothesis s_lub : is_lub le (fun x => exists k, x = iter f bot k) s.
  Hypothesis f_cont : is_lub le (fun x => exists k, x = f (iter f bot k)) (f s).

  Theorem kleene_sup_lfp : is_lfp le f s.
  Proof.
    destruct s_lub as [Hub Hleast]. destruct f_cont as [Fub Fleast].
    split.
    - apply le_antisym.
      + apply Fleast. intros x [k ->]. apply Hub. exists (S k). reflexivity.
      + apply Hleast. intros x [[| k] ->]; [apply bot_least |]. apply Fub. exists k. reflexivity.
    - intros x Hx. apply Hleast. intros y [k ->].
      apply (iter_below_fixed le f f_mono bot bot_least x Hx k).
  Qed.

  Variable Valid : L -> Prop.
  Hypothesis valid_bot : Valid bot.
  Hypothesis valid_f : forall x, Valid x -> Valid (f x).
  Hypothesis valid_sup : forall (c : nat -> L) t, (forall k, le (c k) (c (S k))) ->
    (forall k, Valid (c k)) -> is_lub le (fun x => exists k, x = c k) t -> Valid t.

  Theorem kleene_sup_valid : Valid s.
  Proof.
    apply (valid_sup (iter f bot)).
    - apply (iter_ascending le f f_mono bot bot_least).
    - induction k as [| k IH]; [exact valid_bot | apply valid_f; exact IH].
    - exact s_lub.
  Qed.
End KleeneSup.

(* Non-vacuity of the corrected form, and the precise F27: the continuous operator stays at w;
   its least fixed point w is the Kleene supremum and is valid, but no finite iteration reaches
   it (finite reachability needs ACC: ChaoticACC.kleene_acc_lfp). *)
Definition wPhic (x : W) : W := match x with Fin k => Fin (S k) | y => y end.

Lemma wPhic_mono : forall x y, wle x y -> wle (wPhic x) (wPhic y).
Proof.
  intros [a | |] [b | |]; unfold wle; simpl; try discriminate; try reflexivity. tauto.
Qed.
Lemma wPhic_iter : forall k, iter wPhic (Fin 0) k = Fin k.
Proof. induction k as [| k IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

Definition wValid (x : W) : Prop := x <> Om1.

Theorem kleene_sup_instance :
  is_lfp wle wPhic Om /\ wValid Om /\ (forall k, iter wPhic (Fin 0) k <> Om).
Proof.
  assert (Hlub : is_lub wle (fun x => exists k, x = iter wPhic (Fin 0) k) Om)
    by (apply Om_lub_chain; exact wPhic_iter).
  assert (Hcont : is_lub wle (fun x => exists k, x = wPhic (iter wPhic (Fin 0) k)) (wPhic Om)).
  { simpl. split.
    - intros x [k ->]. rewrite wPhic_iter. reflexivity.
    - intros u Hu. destruct u as [m | |]; [| reflexivity | reflexivity].
      assert (Hm : exists k, Fin (S m) = wPhic (iter wPhic (Fin 0) k))
        by (exists m; rewrite wPhic_iter; reflexivity).
      specialize (Hu (Fin (S m)) Hm). apply Nat.leb_le in Hu. lia. }
  split; [exact (kleene_sup_lfp wle wle_antisym wPhic wPhic_mono (Fin 0) wbot_least Om Hlub Hcont) |].
  split.
  - apply (kleene_sup_valid wle wPhic wPhic_mono (Fin 0) wbot_least Om Hlub wValid).
    + discriminate.
    + intros [k | |] H; simpl; [discriminate | discriminate | exact H].
    + intros c t _ Hc [Hub Hl]. intros ->.
      assert (Hb : is_ub wle (fun x => exists k, x = c k) Om).
      { intros x [k ->]. specialize (Hc k). destruct (c k); [reflexivity | reflexivity | contradiction]. }
      specialize (Hl Om Hb). discriminate Hl.
  - intros k. rewrite wPhic_iter. discriminate.
Qed.

(* ======================================================================================= *)
(* Part 6. F27: widening.                                                                   *)
(* ======================================================================================= *)

(* A widened result w is a post-fixed point (Phi w <= w): it bounds every Kleene iterate, and
   the least fixed point whenever the latter is reached (ACC) or is the Kleene supremum. *)
Theorem widening_sound :
  forall {L : Type} (le : L -> L -> Prop) (f : L -> L) (bot : L),
    (forall x y z, le x y -> le y z -> le x z) ->
    (forall x y, le x y -> le (f x) (f y)) ->
    (forall x, le bot x) ->
    forall w, le (f w) w ->
    (forall k, le (iter f bot k) w) /\
    (forall m, is_lfp le f m -> (exists k, m = iter f bot k) -> le m w) /\
    (forall s, is_lub le (fun x => exists k, x = iter f bot k) s -> le s w).
Proof.
  intros L le f bot Htr Hmono Hbot w Hw.
  pose proof (iter_below_prefixed le f bot Htr Hmono Hbot w Hw) as H.
  split; [exact H |]. split.
  - intros m _ [k ->]. apply H.
  - intros s [_ Hl]. apply Hl. intros x [k ->]. apply H.
Qed.

(* But a widened result need not be a fixed point, so it is not the federated normal form (its
   morphism invariants fail): widening trades the normal form for a sound bound. *)
Definition wPhiw (x : W) : W :=
  match x with Fin k => Fin (Nat.min (S k) 3) | _ => Om end.

Theorem widening_not_normal_form :
  (forall x y, wle x y -> wle (wPhiw x) (wPhiw y)) /\
  wle (wPhiw Om1) Om1 /\ wPhiw Om1 <> Om1 /\
  is_lfp wle wPhiw (Fin 3) /\ iter wPhiw (Fin 0) 3 = Fin 3.
Proof.
  split.
  { intros [a | |] [b | |]; unfold wle; simpl; try discriminate; try reflexivity.
    intros H. apply Nat.leb_le in H. apply Nat.leb_le. lia. }
  split; [reflexivity |]. split; [discriminate |]. split; [| reflexivity].
  split; [reflexivity |].
  intros [k | |] H; try unfold fixed_point in H; simpl in H; try discriminate; [| reflexivity].
  injection H as H. change (Nat.leb 3 k = true). apply Nat.leb_le. lia.
Qed.

(* ======================================================================================= *)
(* Part 7. F31: remark "Convexity and the monotone regime".                                 *)
(* ======================================================================================= *)

(* The chain a0 < a1 < a2. *)
Inductive T3 : Type := a0 | a1 | a2.
Definition t3n (x : T3) : nat := match x with a0 => 0 | a1 => 1 | a2 => 2 end.
Definition t3le (x y : T3) : Prop := t3n x <= t3n y.

(* A one-registry sub-federation J = {A}: A's state is (shared value in T3, unit), valid iff
   the value is not a0; A's compensation sends a0 to a2 (WFC: one step, valid states fixed). *)
Definition VA (_ : nat) (t : T3 * unit) : Prop := fst t <> a0.
Definition rhoA (t : T3 * unit) : T3 * unit :=
  match fst t with a0 => (a2, snd t) | _ => t end.

(* As a network: one component, no internal edges (A is a source inside J; its imports come
   from outside J). *)
Definition t3get (_ : nat) (x : T3) : T3 := x.
Definition t3tab (g : nat -> T3) : T3 := g 0.
Definition t3lst (l : T3 * unit) (_ : nat) : T3 * unit := l.
Definition nosrcs (_ : nat) : list nat := [].
Definition noGam (_ : nat) (_ : list (T3 * unit)) : T3 := a0.

(* rho_Fed^J (def:fed-comp): Phase 1 normalizes A, Phase 2 has no internal edge to repair. *)
Definition rhoJ : T3 * unit -> T3 * unit := rhoA.

Theorem fed_rem_convexity_refuted :
  (* the sub-federation's repair Phi_J is monotone (it has no internal edges) *)
  Mono t3le 1 t3get t3tab t3lst nosrcs noGam /\
  (* A satisfies WFC *)
  (forall t, VA 0 (rhoA t) /\ (VA 0 t -> rhoA t = t)) /\
  (* but rho_Fed^J is not monotone *)
  t3le (fst (a0, tt)) (fst (a1, tt)) /\
  ~ t3le (fst (rhoJ (a0, tt))) (fst (rhoJ (a1, tt))).
Proof.
  split.
  { intros l x y _ j Hj. apply Nat.le_refl. }
  split.
  { intros [[| |] []]; unfold VA, rhoA; simpl; split; try discriminate; try reflexivity.
    intros H. exfalso. apply H. reflexivity. }
  split; [unfold t3le; simpl; lia |].
  unfold t3le; simpl; lia.
Qed.

(* Corrected: rho_Fed^J is monotone when Phase 1 is monotone (in the whole state, ordered as
   locals and shared values) and the repair Phi is monotone in the locals as well as in the
   shared values. Stated for the cyclic normal form: locals rho1 t, shared values the least
   fixed point of Phi (rho1 t); under ACC. *)
Section ConvexCorrected.
  Context {Loc Sh : Type}.
  Variable leL : Loc -> Loc -> Prop.
  Variable le : Sh -> Sh -> Prop.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable bot : Sh.
  Hypothesis bot_least : forall x, le bot x.
  Hypothesis acc : well_founded (ascends le).
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable F : Loc -> Sh -> Sh.
  Hypothesis F_mono : forall l x y, le x y -> le (F l x) (F l y).
  Hypothesis F_mono_loc : forall l l' x, leL l l' -> le (F l x) (F l' x).
  Variable rho1 : Loc * Sh -> Loc.

  Definition tle (t t' : Loc * Sh) : Prop := leL (fst t) (fst t') /\ le (snd t) (snd t').
  Hypothesis rho1_mono : forall t t', tle t t' -> leL (rho1 t) (rho1 t').

  Lemma lfp_mono_param : forall l l' m m', leL l l' ->
    is_lfp le (F l) m -> is_lfp le (F l') m' -> le m m'.
  Proof.
    intros l l' m m' Hl Hm Hm'.
    destruct (kleene_acc_stabilizes le (F l) (F_mono l) bot bot_least acc
                (fun x => sh_eq_dec (F l x) x)) as [k Hk].
    rewrite (lfp_unique le le_antisym (F l) m _ Hm (kleene_lfp le (F l) (F_mono l) bot bot_least k Hk)).
    apply (iter_below_prefixed le (F l) bot le_trans (F_mono l) bot_least m').
    destruct Hm' as [Hf _]. unfold fixed_point in Hf. rewrite <- Hf at 2. apply F_mono_loc. exact Hl.
  Qed.

  Theorem fed_rem_convexity_corrected : forall t t' m m', tle t t' ->
    is_lfp le (F (rho1 t)) m -> is_lfp le (F (rho1 t')) m' -> tle (rho1 t, m) (rho1 t', m').
  Proof.
    intros t t' m m' H Hm Hm'. split; [apply rho1_mono; exact H |].
    apply (lfp_mono_param (rho1 t) (rho1 t')); [apply rho1_mono; exact H | exact Hm | exact Hm'].
  Qed.
End ConvexCorrected.

(* Non-vacuity: the 2-cycle of FederationEventsCycles (cF, alarms as locals, ordered
   componentwise), phase 1 the identity on locals. *)
Theorem convexity_corrected_instance :
  (forall l x y, cle x y -> cle (cF l x) (cF l y)) /\
  (forall l l' x, cle l l' -> cle (cF l x) (cF l' x)) /\
  (forall t t' m m', tle cle cle t t' -> is_lfp cle (cF (fst t)) m ->
     is_lfp cle (cF (fst t')) m' -> tle cle cle (fst t, m) (fst t', m')) /\
  is_lfp cle (cF (true, false)) (true, true) /\ is_lfp cle (cF (false, false)) (false, false).
Proof.
  assert (Hm : forall l x y, cle x y -> cle (cF l x) (cF l y)).
  { intros l x y. bdes; unfold cle, cF; simpl; intuition congruence. }
  assert (Hml : forall l l' x, cle l l' -> cle (cF l x) (cF l' x)).
  { intros l l' x. bdes; unfold cle, cF; simpl; intuition congruence. }
  split; [exact Hm |]. split; [exact Hml |].
  split.
  { apply (fed_rem_convexity_corrected cle cle cle_trans cle_antisym cbot cbot_least
             (finite_height_acc cle crank 2 crank_strict crank_bound) ceq_dec cF Hm Hml fst).
    intros t t' [H _]. exact H. }
  split; split; try reflexivity; intros x Hx; unfold fixed_point in Hx; revert Hx; bdes;
    unfold cle, cF; simpl; intro Hx; try discriminate; intuition congruence.
Qed.
