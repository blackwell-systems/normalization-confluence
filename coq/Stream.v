(* Stream.v: stream processors over time and the Stream Convergence Theorem of the base paper
   (normalization_confluence_2026.tex, Section "Convergence Theorem"), mechanized axiom-free.

   Up to this file the development proved convergence for the Governance Rewrite System (GRS) as a
   rewrite system: unique normal forms from (sigma0, E). The paper's headline theorem is about
   STREAM PROCESSORS (Def. "Stream Processor", label def:processor): processes that receive a
   growing set of events E_P(t) over time t, apply them in a causality-respecting order and
   compensate incrementally, with state Psi_P(t). This file formalizes that model and proves the
   paper's stream-level results on top of the causal GRS (GovernanceCausal.v) with the
   well-founded generalization of WFC (GovernanceWF.v), so every result here is domain-independent
   (Cor. "Domain-Independent Convergence", label cor:infinite) by construction.

   rho* is taken as in Governance.v and GovernanceCausal.v: an operator specified by
   rho_star_reach ((sigma, B) reduces to (rho* sigma, B)). Only the application-order form of
   part (b) also uses rho_star_valid (rho* lands in a valid state), which is the paper's own
   definition of rho* (Def. "Iterated Compensation", label def:rhostar).

   Model (Def. def:processor).
   - prstep: the processor's discipline inside the GRS. A compensation step fires on an invalid
     state; an enabled event is applied only from a valid state ("after applying each event, the
     processor applies rho until validity is restored"). Every prstep is a GRS step (prstep_cstep),
     and a prstep normal form is a GRS normal form (nf_prstep_cstep).
   - processor: received sets recv : nat -> list Event (E_P(t), duplicate-free, growing by
     appending new arrivals) and configurations conf : nat -> State * list Event, with
     Psi_P(t) = fst (conf t).
   - is_processor Str s0 p: received events come from the stream Str, eventual delivery, and the
     paper's last sentence of the definition: the computation on E_P(t) is a reduction sequence
     from (s0, E_P(t)), i.e. star prstep (s0, recv t) (conf t).
   - settled p t: the processor has finished processing E_P(t) (conf t is a normal form).
   - fair p: while nothing new arrives, the processor keeps reducing and makes progress when it
     is not finished.

   Paper map (label: Coq).
   - def:processor (B16): prstep, processor, is_processor, settled, fair; incremental processors
     that carry their state across arrivals are processors (incremental_computes).
   - thm:convergence (a) (B21): stream_validity (settled implies valid), comp_phase_terminates
     (the incremental compensation phase terminates in a valid state), comp_phase_done_valid
     (once no compensation step applies the state is valid), settled_empty_buffer (with a
     progress hypothesis the normal form has an empty buffer, the paper's "normal form").
   - thm:convergence (b): stream_order_independence (any two finished reductions from the same
     received set reach the same state), stream_orders_agree (any two feasible application
     orders of the same set, each followed by compensation, end in the same state).
   - thm:convergence (c): stream_agreement (settled processors with equal received sets agree;
     also across different times), base_thm_convergence_c.
   - thm:convergence as a whole: stream_convergence (WF potential), base_thm_convergence (nat
     potential, the paper's exact setting).
   - thm:convergence (c) AS WRITTEN (no "settled" qualifier) is false:
     base_thm_convergence_c_counterexample. Corrected form: stream_agreement.
   - thm:convergence, closing sentence ("disagreements are transient ... restoring agreement")
     and rem:infinite-streams (B24) are false for infinite streams:
     base_thm_convergence_transient_counterexample. Corrected forms: base_cor_quiescent (finite
     streams) and stream_agreement across times.
   - rem:set-function (B22): base_rem_set_function (F(E) exists and depends only on the set E).
   - cor:quiescent (B23): base_cor_quiescent (WF potential), base_cor_quiescent_nat.
   - cor:infinite at stream level (B32): base_cor_infinite (stream_convergence for any state
     space and any well-founded potential), base_cor_infinite_quiescent; non-vacuity on the
     unbounded state space Z: zw_stream_registry, zw_processors, zw_stream_agree,
     zw_stream_quiescent, zw_stream_quiescent_nat.

   Non-vacuity: every hypothesis set is discharged by the Z withdrawal registry with two
   processors that receive the same two withdrawals in different orders and at different times
   (the zw_ names), and by the counter registry used for the counterexamples (the ct_ names). *)

Require Import NC.Newman NC.GovernanceCausal NC.GovernanceWF.
From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
From Coq Require Import ZArith ZArith.Zwf.
Import ListNotations.

(* ===================== Generic facts about relations ===================== *)

Lemma stream_star_inv : forall {A} (R : A -> A -> Prop) x y,
    star R x y -> x = y \/ exists z, R x z /\ star R z y.
Proof.
  intros A R x y H. destruct H as [x | x z y Hxz Hzy].
  - left; reflexivity.
  - right; exists z; split; assumption.
Qed.

Lemma stream_star_sub : forall {A} (R S : A -> A -> Prop),
    (forall x y, R x y -> S x y) -> forall x y, star R x y -> star S x y.
Proof.
  intros A R S Hsub x y H. induction H as [x | x z y Hxz _ IH].
  - apply star_refl.
  - eapply star_step; [apply Hsub; exact Hxz | exact IH].
Qed.

Lemma stream_SN_sub : forall {A} (R S : A -> A -> Prop),
    (forall x y, R x y -> S x y) -> forall x, SN S x -> SN R x.
Proof.
  intros A R S Hsub x H. induction H as [x _ IH].
  constructor. intros y Hxy. apply IH. apply Hsub. exact Hxy.
Qed.

(* ===================== The stream model ===================== *)

Section Stream.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.

  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.

  (* WFC over an arbitrary well-founded order (GovernanceWF.v): domain independence. *)
  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.

  Local Notation cstep := (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).

  (* The registry conditions, exactly as in GovernanceWF.v's causal section. *)
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).
  Hypothesis rho_star_reach : forall sigma B, star cstep (sigma, B) (rho_star sigma, B).
  Hypothesis cc1_coenabled : forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma))).
  Hypothesis cc2 : forall sigma e,
      ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma)).
  Hypothesis enabled_after_remove :
    forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (rm e1 B) /\ enabled e2 (rho_star (apply e1 sigma)) (rm e1 B).
  Hypothesis enabled_after_comp :
    forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.

  (* Stream-level conditions. V_R is a boolean predicate in the paper (V_R(sigma) = top or bot),
     enabledness is decidable (deps(e) intersect B is empty), and it depends on the buffer only
     as a set (the paper's B is a set). *)
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm :
    forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  (* ---------- buffers ---------- *)

  Lemma st_rm_head : forall e l, rm e (e :: l) = l.
  Proof. intros e l. simpl. destruct (event_eq_dec e e) as [_ | H]; [reflexivity | congruence]. Qed.

  Lemma st_rm_notin : forall e l, ~ In e l -> rm e l = l.
  Proof.
    intros e l. induction l as [| x l IH]; intros H; [reflexivity |].
    simpl. destruct (event_eq_dec x e) as [-> | Hx].
    - exfalso. apply H. left. reflexivity.
    - f_equal. apply IH. intro Hin. apply H. right. exact Hin.
  Qed.

  Lemma st_rm_perm_cons : forall e l, In e l -> Permutation l (e :: rm e l).
  Proof.
    intros e l. induction l as [| x l IH]; intros H; [destruct H |].
    simpl. destruct (event_eq_dec x e) as [-> | Hx].
    - apply Permutation_refl.
    - destruct H as [-> | H]; [congruence |].
      eapply Permutation_trans; [apply perm_skip; apply IH; exact H | apply perm_swap].
  Qed.

  Lemma st_rm_perm : forall e B C, Permutation B C -> Permutation (rm e B) (rm e C).
  Proof.
    intros e B C H. destruct (in_dec event_eq_dec e B) as [Hin | Hnin].
    - assert (HinC : In e C) by (exact (Permutation_in e H Hin)).
      apply (Permutation_cons_inv (a := e)).
      eapply Permutation_trans; [apply Permutation_sym; apply st_rm_perm_cons; exact Hin |].
      eapply Permutation_trans; [exact H | apply st_rm_perm_cons; exact HinC].
    - assert (HnC : ~ In e C) by (intro Hc; apply Hnin; exact (Permutation_in e (Permutation_sym H) Hc)).
      rewrite (st_rm_notin e B Hnin), (st_rm_notin e C HnC). exact H.
  Qed.

  Lemma st_in_rm_neq : forall e1 e2 B, In e2 B -> e1 <> e2 -> In e2 (rm e1 B).
  Proof.
    intros e1 e2 B. induction B as [| x xs IH]; intros Hin Hne; [inversion Hin |].
    simpl. destruct (event_eq_dec x e1) as [-> | Hx].
    - destruct Hin as [-> | Hin]; [contradiction | exact Hin].
    - destruct Hin as [-> | Hin]; [left; reflexivity | right; apply IH; assumption].
  Qed.

  Lemma st_rm_app : forall e B N, In e B -> rm e (B ++ N) = rm e B ++ N.
  Proof.
    intros e B N. induction B as [| x B IH]; intros H; [destruct H |].
    simpl. destruct (event_eq_dec x e) as [-> | Hx]; [reflexivity |].
    destruct H as [-> | H]; [congruence |]. rewrite (IH H). reflexivity.
  Qed.

  (* ---------- the processor discipline inside the GRS ---------- *)

  (* Incremental compensation: compensate while invalid; apply an enabled event only from a
     valid state. *)
  Inductive prstep : (State * list Event) -> (State * list Event) -> Prop :=
  | ps_apply : forall sigma B e,
      valid sigma -> In e B -> enabled e sigma B ->
      prstep (sigma, B) (apply e sigma, rm e B)
  | ps_comp : forall sigma B,
      ~ valid sigma -> prstep (sigma, B) (rho sigma, B).

  Lemma prstep_cstep : forall c c', prstep c c' -> cstep c c'.
  Proof.
    intros c c' H. destruct H as [s B e _ Hin Hen | s B Hinv].
    - apply GovernanceCausal.st_apply; assumption.
    - apply GovernanceCausal.st_comp; assumption.
  Qed.

  Lemma star_prstep_cstep : forall c c', star prstep c c' -> star cstep c c'.
  Proof. apply stream_star_sub. exact prstep_cstep. Qed.

  Lemma nf_prstep_cstep : forall c, normal_form prstep c -> normal_form cstep c.
  Proof.
    intros c Hnf [c' H]. apply Hnf.
    destruct H as [s B e Hin Hen | s B Hinv].
    - destruct (valid_dec s) as [Hv | Hv].
      + exists (apply e s, rm e B). apply ps_apply; assumption.
      + exists (rho s, B). apply ps_comp; assumption.
    - exists (rho s, B). apply ps_comp; assumption.
  Qed.

  Lemma nf_cstep_prstep : forall c, normal_form cstep c -> normal_form prstep c.
  Proof. intros c Hnf [c' H]. apply Hnf. exists c'. apply prstep_cstep. exact H. Qed.

  Lemma st_SN_cstep : forall c, SN cstep c.
  Proof.
    exact (causal_governance_wf_terminating event_eq_dec apply rho valid enabled P ltP wf_ltP Phi
             wfc_wf).
  Qed.

  Lemma st_SN_prstep : forall c, SN prstep c.
  Proof. intros c. apply (stream_SN_sub prstep cstep prstep_cstep). apply st_SN_cstep. Qed.

  Lemma st_cstep_unique_nf :
    forall c n1 n2, star cstep c n1 -> normal_form cstep n1 ->
                    star cstep c n2 -> normal_form cstep n2 -> n1 = n2.
  Proof.
    exact (causal_governance_wf_unique_normal_forms event_eq_dec apply rho rho_star valid enabled
             P ltP wf_ltP Phi wfc_wf rho_star_reach cc1_coenabled cc2 enabled_after_remove
             enabled_after_comp).
  Qed.

  (* ---------- the buffer is a set: permutation invariance ---------- *)

  Lemma st_cstep_perm :
    forall s B s' B' C, cstep (s, B) (s', B') -> Permutation B C ->
      exists C', cstep (s, C) (s', C') /\ Permutation B' C'.
  Proof.
    intros s B s' B' C H HP. inversion H as [s0 B0 e Hin Hen E1 E2 | s0 B0 Hinv E1 E2]; subst.
    - exists (rm e C). split.
      + apply GovernanceCausal.st_apply.
        * exact (Permutation_in e HP Hin).
        * exact (enabled_perm e s B C HP Hen).
      + apply st_rm_perm. exact HP.
    - exists C. split; [apply GovernanceCausal.st_comp; exact Hinv | exact HP].
  Qed.

  Lemma st_star_cstep_perm :
    forall c c', star cstep c c' -> forall C, Permutation (snd c) C ->
      exists C', star cstep (fst c, C) (fst c', C') /\ Permutation (snd c') C'.
  Proof.
    intros c c' H. induction H as [c | c d c' Hcd _ IH]; intros C HP.
    - exists C. split; [apply star_refl | exact HP].
    - destruct c as [s B], d as [s1 B1]. simpl in HP.
      destruct (st_cstep_perm s B s1 B1 C Hcd HP) as [C1 [H1 HP1]].
      destruct (IH C1 HP1) as [C' [H2 HP2]]. simpl in H2.
      exists C'. split; [eapply star_step; [exact H1 | exact H2] | exact HP2].
  Qed.

  Lemma st_nf_cstep_perm :
    forall s B C, normal_form cstep (s, B) -> Permutation B C -> normal_form cstep (s, C).
  Proof.
    intros s B C Hnf HP [[s' C'] H]. apply Hnf.
    destruct (st_cstep_perm s C s' C' B H (Permutation_sym HP)) as [B' [HB _]].
    exists (s', B'). exact HB.
  Qed.

  (* ---------- decidability of the next move ---------- *)

  Lemma st_find_enabled :
    forall s B L, {e | In e L /\ enabled e s B} + {forall e, In e L -> ~ enabled e s B}.
  Proof.
    intros s B L. induction L as [| x L IH].
    - right. intros e H. destruct H.
    - destruct (enabled_dec x s B) as [Hx | Hx].
      + left. exists x. split; [left; reflexivity | exact Hx].
      + destruct IH as [[e [He Hen]] | Hnone].
        * left. exists e. split; [right; exact He | exact Hen].
        * right. intros e [-> | He]; [exact Hx | apply Hnone; exact He].
  Qed.

  Lemma st_nf_or_step : forall c, normal_form prstep c \/ exists c', prstep c c'.
  Proof.
    intros [s B]. destruct (valid_dec s) as [Hv | Hv].
    - destruct (st_find_enabled s B B) as [[e [Hin Hen]] | Hnone].
      + right. exists (apply e s, rm e B). apply ps_apply; assumption.
      + left. intros [c' H]. inversion H; subst.
        * exact (Hnone _ ltac:(eassumption) ltac:(eassumption)).
        * contradiction.
    - right. exists (rho s, B). apply ps_comp; exact Hv.
  Qed.

  Lemma st_pnf_exists : forall c, exists n, star prstep c n /\ normal_form prstep n.
  Proof.
    intros c. induction (st_SN_prstep c) as [c _ IH].
    destruct (st_nf_or_step c) as [Hnf | [c' H]].
    - exists c. split; [apply star_refl | exact Hnf].
    - destruct (IH c' H) as [n [Hs Hn]]. exists n. split; [eapply star_step; eassumption | exact Hn].
  Qed.

  (* ================= Part (a): validity ================= *)

  Lemma st_nf_valid : forall c, normal_form prstep c -> valid (fst c).
  Proof.
    intros [s B] Hnf. simpl. destruct (valid_dec s) as [Hv | Hv]; [exact Hv |].
    exfalso. apply Hnf. exists (rho s, B). apply ps_comp; exact Hv.
  Qed.

  (* The incremental compensation phase terminates (Lemma "Termination") in a valid state, with
     the buffer untouched: only compensation steps are taken. *)
  Theorem comp_phase_terminates :
    forall s B, exists s', star prstep (s, B) (s', B) /\ valid s'.
  Proof.
    intros s B.
    assert (Hacc : Acc ltP (Phi s)) by (apply wf_ltP).
    remember (Phi s) as x eqn:Ex. revert s Ex.
    induction Hacc as [x _ IH]; intros s Ex; subst x.
    destruct (valid_dec s) as [Hv | Hv].
    - exists s. split; [apply star_refl | exact Hv].
    - destruct (IH (Phi (rho s)) (wfc_wf s Hv) (rho s) eq_refl) as [s' [Hs Hv']].
      exists s'. split; [eapply star_step; [apply ps_comp; exact Hv | exact Hs] | exact Hv'].
  Qed.

  (* "After it completes the incremental compensation phase": no compensation step applies. *)
  Theorem comp_phase_done_valid :
    forall s B, ~ (exists s', prstep (s, B) (s', B) /\ ~ valid s) -> valid s.
  Proof.
    intros s B H. destruct (valid_dec s) as [Hv | Hv]; [exact Hv |].
    exfalso. apply H. exists (rho s). split; [apply ps_comp; exact Hv | exact Hv].
  Qed.

  (* ---------- processors ---------- *)

  Record processor : Type := mkProc {
    recv : nat -> list Event;                (* E_P(t)                         *)
    conf : nat -> (State * list Event)       (* (Psi_P(t), buffer) at time t   *)
  }.

  Definition psi (p : processor) (t : nat) : State := fst (conf p t).

  (* Def. "Stream Processor" for the stream Str (a predicate: the stream may be infinite). *)
  Definition is_processor (Str : Event -> Prop) (s0 : State) (p : processor) : Prop :=
    (forall t, NoDup (recv p t)) /\                                   (* unique ids        *)
    (forall t e, In e (recv p t) -> Str e) /\                         (* E_P(t) in S       *)
    (forall t, exists N, recv p (S t) = recv p t ++ N) /\             (* received sets grow *)
    (forall e, Str e -> exists ti, forall t, ti <= t -> In e (recv p t)) /\ (* eventual delivery *)
    (forall t, star prstep (s0, recv p t) (conf p t)).                 (* reduction from (s0, E_P(t)) *)

  (* The processor has finished processing E_P(t). *)
  Definition settled (p : processor) (t : nat) : Prop := normal_form prstep (conf p t).

  (* Progress while nothing new arrives. *)
  Definition fair (p : processor) : Prop :=
    forall t, recv p (S t) = recv p t ->
      star prstep (conf p t) (conf p (S t)) /\
      (~ normal_form prstep (conf p t) ->
         exists c, prstep (conf p t) c /\ star prstep c (conf p (S t))).

  Theorem stream_validity :
    forall Str s0 p t, is_processor Str s0 p -> settled p t -> valid (psi p t).
  Proof. intros Str s0 p t _ H. exact (st_nf_valid _ H). Qed.

  (* With a progress hypothesis (the received set is causally closed, so a non-empty buffer always
     has an enabled event) the finished configuration is the paper's normal form (empty, valid). *)
  Theorem settled_empty_buffer :
    (forall s B, B <> [] -> exists e, In e B /\ enabled e s B) ->
    forall p t, settled p t -> snd (conf p t) = [] /\ valid (psi p t).
  Proof.
    intros Hprog p t Hnf. split; [| exact (st_nf_valid _ Hnf)].
    unfold settled in Hnf. destruct (conf p t) as [s B] eqn:Ec. simpl.
    destruct B as [| x B]; [reflexivity | exfalso].
    pose proof (st_nf_valid _ Hnf) as Hv. simpl in Hv.
    destruct (Hprog s (x :: B) ltac:(discriminate)) as [e [Hin Hen]].
    apply Hnf. exists (apply e s, rm e (x :: B)). apply ps_apply; assumption.
  Qed.

  (* ================= Part (b): order independence ================= *)

  Theorem stream_order_independence :
    forall s0 E1 E2 n1 n2, Permutation E1 E2 ->
      star prstep (s0, E1) n1 -> normal_form prstep n1 ->
      star prstep (s0, E2) n2 -> normal_form prstep n2 ->
      fst n1 = fst n2.
  Proof.
    intros s0 E1 E2 n1 n2 HP S1 N1 S2 N2.
    apply star_prstep_cstep in S1, S2. apply nf_prstep_cstep in N1, N2.
    destruct (st_star_cstep_perm _ _ S2 E1 (Permutation_sym HP)) as [C [S2' HC]]. simpl in S2'.
    destruct n2 as [s2 B2]. simpl in *.
    assert (N2' : normal_form cstep (s2, C)) by (exact (st_nf_cstep_perm s2 B2 C N2 HC)).
    rewrite (st_cstep_unique_nf _ _ _ S1 N1 S2' N2'). reflexivity.
  Qed.

  (* The application-order form: a processor that applies the events of E in order o, each
     followed by its compensation phase, rho*, with every event enabled when applied. *)
  Fixpoint prun (s : State) (o : list Event) : State :=
    match o with
    | [] => s
    | e :: o' => prun (rho_star (apply e s)) o'
    end.

  Fixpoint rm_all (o B : list Event) : list Event :=
    match o with
    | [] => B
    | e :: o' => rm_all o' (rm e B)
    end.

  Inductive feasible : State -> list Event -> list Event -> Prop :=
  | feas_nil : forall s B, feasible s B []
  | feas_cons : forall s B e o,
      In e B -> enabled e s B -> feasible (rho_star (apply e s)) (rm e B) o ->
      feasible s B (e :: o).

  Lemma st_feasible_reach :
    forall s B o, feasible s B o -> star cstep (s, B) (prun s o, rm_all o B).
  Proof.
    intros s B o H. induction H as [s B | s B e o Hin Hen _ IH]; simpl.
    - apply star_refl.
    - eapply star_step; [apply GovernanceCausal.st_apply; eassumption |].
      eapply star_trans; [apply rho_star_reach | exact IH].
  Qed.

  Lemma st_feasible_nil_buffer : forall s o, feasible s [] o -> o = [].
  Proof. intros s o H. inversion H; subst; [reflexivity | contradiction]. Qed.

  Lemma prun_valid :
    (forall s, valid (rho_star s)) -> forall o s, o <> [] -> valid (prun s o).
  Proof.
    intros Hv o. induction o as [| e o IH]; intros s Hne; [congruence |].
    simpl. destruct o as [| e' o']; [apply Hv | apply IH; discriminate].
  Qed.

  Lemma st_valid_empty_nf : forall s, valid s -> normal_form cstep (s, []).
  Proof.
    intros s Hv [c' H]. inversion H; subst; [contradiction | contradiction].
  Qed.

  Theorem stream_orders_agree :
    (forall s, valid (rho_star s)) ->
    forall s0 E1 E2 o1 o2, Permutation E1 E2 ->
      feasible s0 E1 o1 -> rm_all o1 E1 = [] ->
      feasible s0 E2 o2 -> rm_all o2 E2 = [] ->
      prun s0 o1 = prun s0 o2.
  Proof.
    intros Hv s0 E1 E2 o1 o2 HP F1 R1 F2 R2.
    destruct o1 as [| a1 o1'].
    - simpl in R1. subst E1. apply Permutation_nil in HP. subst E2.
      rewrite (st_feasible_nil_buffer _ _ F2). reflexivity.
    - destruct o2 as [| a2 o2'].
      + simpl in R2. subst E2. apply Permutation_sym, Permutation_nil in HP. subst E1.
        pose proof (st_feasible_nil_buffer _ _ F1). discriminate.
      + pose proof (st_feasible_reach _ _ _ F1) as S1. pose proof (st_feasible_reach _ _ _ F2) as S2.
        rewrite R1 in S1. rewrite R2 in S2.
        destruct (st_star_cstep_perm _ _ S2 E1 (Permutation_sym HP)) as [C [S2' HC]]. simpl in S2', HC.
        apply Permutation_nil in HC. subst C.
        assert (E : (prun s0 (a1 :: o1'), @nil Event) = (prun s0 (a2 :: o2'), [])).
        { apply (st_cstep_unique_nf (s0, E1)); [exact S1 | | exact S2' |];
            apply st_valid_empty_nf; apply prun_valid; first [exact Hv | discriminate]. }
        injection E as E. exact E.
  Qed.

  (* ================= Part (c): agreement ================= *)

  Lemma st_same_set_perm :
    forall l1 l2 : list Event, NoDup l1 -> NoDup l2 -> (forall e, In e l1 <-> In e l2) -> Permutation l1 l2.
  Proof. intros l1 l2 H1 H2 H. exact (NoDup_Permutation H1 H2 H). Qed.

  (* Settled processors with the same received set agree, at the same or at different times. *)
  Theorem stream_agreement :
    forall Str s0 p1 p2 t1 t2,
      is_processor Str s0 p1 -> is_processor Str s0 p2 ->
      settled p1 t1 -> settled p2 t2 ->
      (forall e, In e (recv p1 t1) <-> In e (recv p2 t2)) ->
      psi p1 t1 = psi p2 t2.
  Proof.
    intros Str s0 p1 p2 t1 t2 [Nd1 [_ [_ [_ C1]]]] [Nd2 [_ [_ [_ C2]]]] H1 H2 Hset.
    apply (stream_order_independence s0 (recv p1 t1) (recv p2 t2)).
    - apply st_same_set_perm; auto.
    - apply C1.
    - exact H1.
    - apply C2.
    - exact H2.
  Qed.

  (* The paper's (c), same time t. *)
  Corollary base_thm_convergence_c :
    forall Str s0 p1 p2 t,
      is_processor Str s0 p1 -> is_processor Str s0 p2 ->
      settled p1 t -> settled p2 t ->
      (forall e, In e (recv p1 t) <-> In e (recv p2 t)) ->
      psi p1 t = psi p2 t.
  Proof. intros. eapply stream_agreement; eassumption. Qed.

  (* Thm. "Stream Convergence" (a), (b), (c) in one statement. *)
  Theorem stream_convergence :
    forall Str s0 p1 p2,
      is_processor Str s0 p1 -> is_processor Str s0 p2 ->
      (* (a) validity once processing of the received set is finished *)
      (forall t, settled p1 t -> valid (psi p1 t)) /\
      (forall t, settled p2 t -> valid (psi p2 t)) /\
      (* (b) the finished state depends only on the received set *)
      (forall (E1 E2 : list Event) (n1 n2 : State * list Event), Permutation E1 E2 ->
         star prstep (s0, E1) n1 -> normal_form prstep n1 ->
         star prstep (s0, E2) n2 -> normal_form prstep n2 -> fst n1 = fst n2) /\
      (* (c) agreement *)
      (forall t, settled p1 t -> settled p2 t ->
         (forall e, In e (recv p1 t) <-> In e (recv p2 t)) -> psi p1 t = psi p2 t).
  Proof.
    intros Str s0 p1 p2 H1 H2. split; [| split; [| split]].
    - intros t. exact (stream_validity Str s0 p1 t H1).
    - intros t. exact (stream_validity Str s0 p2 t H2).
    - intros E1 E2 n1 n2. apply stream_order_independence.
    - intros t. apply (base_thm_convergence_c Str s0 p1 p2 t H1 H2).
  Qed.

  (* ================= Rem. "Semantic Projection": F(E) is a function of the set ================= *)

  Definition StreamNF (s0 : State) (E : list Event) (s : State) : Prop :=
    exists B, star prstep (s0, E) (s, B) /\ normal_form prstep (s, B).

  Theorem base_rem_set_function :
    forall s0 E, exists s, StreamNF s0 E s /\
      forall E' s', NoDup E -> NoDup E' -> (forall e, In e E <-> In e E') -> StreamNF s0 E' s' -> s' = s.
  Proof.
    intros s0 E. destruct (st_pnf_exists (s0, E)) as [[s B] [Hs Hn]].
    exists s. split; [exists B; split; assumption |].
    intros E' s' Nd Nd' Hset [B' [Hs' Hn']].
    symmetry. exact (stream_order_independence s0 E E' (s, B) (s', B')
                       (st_same_set_perm E E' Nd Nd' Hset) Hs Hn Hs' Hn').
  Qed.

  (* ================= Cor. "Convergence Under Quiescent Streams" ================= *)

  Lemma stream_settle :
    forall p, fair p -> forall c, SN prstep c -> forall t, star prstep c (conf p t) ->
      (forall k, recv p (t + k) = recv p t) ->
      exists T, t <= T /\ forall k, normal_form prstep (conf p (T + k)) /\ conf p (T + k) = conf p T.
  Proof.
    intros p Hf c Hsn. induction Hsn as [c _ IH]. intros t Hst Hc.
    assert (Hfair : forall k, star prstep (conf p (t + k)) (conf p (t + S k)) /\
              (~ normal_form prstep (conf p (t + k)) ->
                 exists c', prstep (conf p (t + k)) c' /\ star prstep c' (conf p (t + S k)))).
    { intros k. rewrite Nat.add_succ_r. apply Hf. rewrite <- Nat.add_succ_r, !Hc. reflexivity. }
    destruct (st_nf_or_step (conf p t)) as [Hnf | [c1 Hc1]].
    - exists t. split; [reflexivity |].
      assert (Heq : forall k, conf p (t + k) = conf p t).
      { induction k as [| k IHk]; [rewrite Nat.add_0_r; reflexivity |].
        destruct (Hfair k) as [Hs _]. rewrite IHk in Hs.
        symmetry. exact (star_from_nf _ _ _ Hnf Hs). }
      intros k. rewrite Heq. split; [exact Hnf | reflexivity].
    - assert (Hnn : ~ normal_form prstep (conf p t)) by (intro N; apply N; exists c1; exact Hc1).
      destruct (stream_star_inv _ _ _ Hst) as [Ec | [d [Hcd Hd]]].
      + subst c. destruct (Hfair 0) as [_ Hprog]. rewrite Nat.add_0_r in Hprog.
        destruct (Hprog Hnn) as [c2 [H2 Hs2]].
        destruct (IH c2 H2 (S t)) as [T [HT HT']].
        * rewrite <- Nat.add_1_r. exact Hs2.
        * intros k. replace (S t + k) with (t + S k) by lia. rewrite Hc.
          replace (S t) with (t + 1) by lia. rewrite Hc. reflexivity.
        * exists T. split; [lia | exact HT'].
      + destruct (IH d Hcd t Hd Hc) as [T [HT HT']]. exists T. split; assumption.
  Qed.

  Lemma stream_all_received :
    forall (Str : Event -> Prop) p,
      (forall e, Str e -> exists ti, forall t, ti <= t -> In e (recv p t)) ->
      forall l, (forall e, In e l -> Str e) ->
      exists T, forall t, T <= t -> forall e, In e l -> In e (recv p t).
  Proof.
    intros Str p Hdel l. induction l as [| x l IH]; intros Hl.
    - exists 0. intros t _ e H. destruct H.
    - destruct (Hdel x (Hl x (or_introl eq_refl))) as [tx Htx].
      destruct IH as [T HT]; [intros e He; apply Hl; right; exact He |].
      exists (Nat.max tx T). intros t Ht e [-> | He].
      + apply Htx. lia.
      + apply HT; [lia | exact He].
  Qed.

  Lemma st_nodup_app_covered :
    forall (l N : list Event), NoDup (l ++ N) -> (forall x, In x N -> In x l) -> N = [].
  Proof.
    intros l N Hnd Hc. destruct N as [| x N]; [reflexivity | exfalso].
    apply (NoDup_remove_2 l N x Hnd). apply in_or_app. left. apply Hc. left. reflexivity.
  Qed.

  Theorem base_cor_quiescent :
    forall (Sl : list Event) s0 p1 p2,
      is_processor (fun e => In e Sl) s0 p1 -> is_processor (fun e => In e Sl) s0 p2 ->
      fair p1 -> fair p2 ->
      exists sigma, valid sigma /\
        exists T, forall t, T <= t -> psi p1 t = sigma /\ psi p2 t = sigma.
  Proof.
    intros Sl s0 p1 p2 HP1 HP2 F1 F2.
    (* each processor eventually holds the whole stream and its received set stops changing *)
    assert (Hq : forall p, is_processor (fun e => In e Sl) s0 p -> fair p ->
              exists T, (forall k, normal_form prstep (conf p (T + k)) /\ conf p (T + k) = conf p T) /\
                        (forall e, In e (recv p T) <-> In e Sl)).
    { intros p [Nd [Sub [Gr [Del Comp]]]] Fp.
      destruct (stream_all_received _ p Del Sl (fun e H => H)) as [T0 HT0].
      assert (Hconst : forall k, recv p (T0 + k) = recv p T0).
      { induction k as [| k IHk]; [rewrite Nat.add_0_r; reflexivity |].
        rewrite Nat.add_succ_r. destruct (Gr (T0 + k)) as [N HN]. rewrite HN.
        assert (N = []) as ->.
        { apply (st_nodup_app_covered (recv p (T0 + k))). rewrite <- HN. apply Nd.
          intros x Hx. apply (HT0 (T0 + k)); [lia |]. apply (Sub (S (T0 + k))). rewrite HN.
          apply in_or_app. right. exact Hx. }
        rewrite app_nil_r. exact IHk. }
      destruct (stream_settle p Fp (conf p T0) (st_SN_prstep _) T0 (star_refl _ _) Hconst) as [T [HT HT']].
      exists T. split; [exact HT' |].
      intros e. split; [apply Sub |]. intros He. apply (HT0 T); [exact HT | exact He]. }
    destruct (Hq p1 HP1 F1) as [T1 [H1 S1]]. destruct (Hq p2 HP2 F2) as [T2 [H2 S2]].
    assert (Hag : psi p1 T1 = psi p2 T2).
    { apply (stream_agreement (fun e => In e Sl) s0 p1 p2 T1 T2 HP1 HP2).
      - destruct (H1 0) as [N _]. rewrite Nat.add_0_r in N. exact N.
      - destruct (H2 0) as [N _]. rewrite Nat.add_0_r in N. exact N.
      - intros e. rewrite S1, S2. reflexivity. }
    exists (psi p1 T1). split.
    - destruct (H1 0) as [N _]. rewrite Nat.add_0_r in N. exact (st_nf_valid _ N).
    - exists (Nat.max T1 T2). intros t Ht. split.
      + unfold psi. replace t with (T1 + (t - T1)) by lia. destruct (H1 (t - T1)) as [_ E]. rewrite E.
        reflexivity.
      + rewrite Hag. unfold psi. replace t with (T2 + (t - T2)) by lia.
        destruct (H2 (t - T2)) as [_ E]. rewrite E. reflexivity.
  Qed.

  (* ================= Incremental processors are processors ================= *)

  (* A processor that carries its configuration across time: new arrivals are appended to its
     buffer and it keeps reducing. Its computation at every time is a reduction from
     (s0, E_P(t)), as Def. "Stream Processor" requires, provided an event enabled in a buffer stays
     enabled when later arrivals are appended (under causal delivery the later arrivals contain
     no dependency of a received event). *)
  Hypothesis enabled_app : forall e s B N, enabled e s B -> enabled e s (B ++ N).

  Lemma star_prstep_app :
    forall c c', star prstep c c' -> forall N, star prstep (fst c, snd c ++ N) (fst c', snd c' ++ N).
  Proof.
    intros c c' H. induction H as [c | c d c' Hcd _ IH]; intros N.
    - apply star_refl.
    - eapply star_step; [| apply IH].
      destruct Hcd as [s B e Hv Hin Hen | s B Hinv]; simpl.
      + rewrite <- (st_rm_app e B N Hin). apply ps_apply; [exact Hv | apply in_or_app; left; exact Hin |].
        apply enabled_app. exact Hen.
      + apply ps_comp. exact Hinv.
  Qed.

  Theorem incremental_computes :
    forall s0 (p : processor) (arr : nat -> list Event),
      (forall t, recv p (S t) = recv p t ++ arr t) ->
      star prstep (s0, recv p 0) (conf p 0) ->
      (forall t, star prstep (fst (conf p t), snd (conf p t) ++ arr t) (conf p (S t))) ->
      forall t, star prstep (s0, recv p t) (conf p t).
  Proof.
    intros s0 p arr Hr H0 HS t. induction t as [| t IH]; [exact H0 |].
    rewrite Hr. eapply star_trans; [| apply HS].
    exact (star_prstep_app _ _ IH (arr t)).
  Qed.

End Stream.

(* ===================== The paper's exact setting: a natural-number potential ===================== *)

Section NatPotential.
  Context {State : Type}.
  Context {Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.
  Variable enabled  : Event -> State -> list Event -> Prop.
  Variable Phi      : State -> nat.

  Local Notation cstep := (GovernanceCausal.step event_eq_dec apply rho valid enabled).
  Local Notation rm := (GovernanceCausal.remove1 event_eq_dec).
  Local Notation prstep := (prstep event_eq_dec apply rho valid enabled).

  Hypothesis wfc : forall sigma, ~ valid sigma -> Phi (rho sigma) < Phi sigma.
  Hypothesis rho_star_reach : forall sigma B, star cstep (sigma, B) (rho_star sigma, B).
  Hypothesis cc1_coenabled : forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      rho_star (apply e2 (rho_star (apply e1 sigma)))
    = rho_star (apply e1 (rho_star (apply e2 sigma))).
  Hypothesis cc2 : forall sigma e,
      ~ valid sigma -> rho_star (apply e sigma) = rho_star (apply e (rho sigma)).
  Hypothesis enabled_after_remove :
    forall sigma B e1 e2,
      enabled e1 sigma B -> enabled e2 sigma B -> e1 <> e2 ->
      In e2 (rm e1 B) /\ enabled e2 (rho_star (apply e1 sigma)) (rm e1 B).
  Hypothesis enabled_after_comp :
    forall sigma B e, enabled e sigma B -> enabled e (rho sigma) B.
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm :
    forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  (* Thm. "Stream Convergence" with WFC as stated in the paper (Phi : Sigma -> N). *)
  Theorem base_thm_convergence :
    forall Str s0 p1 p2,
      is_processor event_eq_dec apply rho valid enabled Str s0 p1 ->
      is_processor event_eq_dec apply rho valid enabled Str s0 p2 ->
      (forall t, settled event_eq_dec apply rho valid enabled p1 t -> valid (psi p1 t)) /\
      (forall t, settled event_eq_dec apply rho valid enabled p2 t -> valid (psi p2 t)) /\
      (forall (E1 E2 : list Event) (n1 n2 : State * list Event), Permutation E1 E2 ->
         star prstep (s0, E1) n1 -> normal_form prstep n1 ->
         star prstep (s0, E2) n2 -> normal_form prstep n2 -> fst n1 = fst n2) /\
      (forall t, settled event_eq_dec apply rho valid enabled p1 t ->
         settled event_eq_dec apply rho valid enabled p2 t ->
         (forall e, In e (recv p1 t) <-> In e (recv p2 t)) -> psi p1 t = psi p2 t).
  Proof.
    exact (stream_convergence event_eq_dec apply rho rho_star valid enabled nat lt lt_wf Phi wfc
             rho_star_reach cc1_coenabled cc2 enabled_after_remove enabled_after_comp valid_dec
             enabled_perm).
  Qed.

  Theorem base_cor_quiescent_nat :
    forall (Sl : list Event) s0 p1 p2,
      is_processor event_eq_dec apply rho valid enabled (fun e => In e Sl) s0 p1 ->
      is_processor event_eq_dec apply rho valid enabled (fun e => In e Sl) s0 p2 ->
      fair event_eq_dec apply rho valid enabled p1 -> fair event_eq_dec apply rho valid enabled p2 ->
      exists sigma, valid sigma /\
        exists T, forall t, T <= t -> psi p1 t = sigma /\ psi p2 t = sigma.
  Proof.
    exact (base_cor_quiescent event_eq_dec apply rho rho_star valid enabled nat lt lt_wf Phi wfc
             rho_star_reach cc1_coenabled cc2 enabled_after_remove enabled_after_comp valid_dec
             enabled_dec enabled_perm).
  Qed.
End NatPotential.

(* Cor. "Domain-Independent Convergence" at stream level: the Stream Convergence Theorem and the
   quiescent corollary for ANY state space and ANY well-founded compensation measure. These are the
   section theorems themselves; the names record the paper label. *)
Definition base_cor_infinite := @stream_convergence.
Definition base_cor_infinite_quiescent := @base_cor_quiescent.

(* ============================================================
   Counterexamples to the statement as written. Counter registry: State = nat, every state valid,
   no compensation, Event = nat (event ids), each event increments the counter, enabled = pending.
   WFC, CC1, CC2 and every other hypothesis hold (ct_registry).
   ============================================================ *)

Definition ct_apply (_ : nat) (s : nat) : nat := S s.
Definition ct_rho (s : nat) : nat := s.
Definition ct_valid (_ : nat) : Prop := True.
Definition ct_enabled (e : nat) (_ : nat) (B : list nat) : Prop := In e B.
Definition ct_Phi (_ : nat) : nat := 0.

Local Notation ct_cstep := (GovernanceCausal.step Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled).
Local Notation ct_pstep := (prstep Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled).
Local Notation ct_rm := (GovernanceCausal.remove1 Nat.eq_dec).
Local Notation ct_proc := (is_processor Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled).
Local Notation ct_fair := (fair Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled).
Local Notation ct_settled := (settled Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled).

Theorem ct_registry :
  (forall s, ~ ct_valid s -> ct_Phi (ct_rho s) < ct_Phi s) /\
  (forall s B, star ct_cstep (s, B) (ct_rho s, B)) /\
  (forall s B e1 e2, ct_enabled e1 s B -> ct_enabled e2 s B -> e1 <> e2 ->
     ct_rho (ct_apply e2 (ct_rho (ct_apply e1 s))) = ct_rho (ct_apply e1 (ct_rho (ct_apply e2 s)))) /\
  (forall s e, ~ ct_valid s -> ct_rho (ct_apply e s) = ct_rho (ct_apply e (ct_rho s))) /\
  (forall s B e1 e2, ct_enabled e1 s B -> ct_enabled e2 s B -> e1 <> e2 ->
     In e2 (ct_rm e1 B) /\ ct_enabled e2 (ct_rho (ct_apply e1 s)) (ct_rm e1 B)) /\
  (forall s B e, ct_enabled e s B -> ct_enabled e (ct_rho s) B) /\
  (forall e s B C, Permutation B C -> ct_enabled e s B -> ct_enabled e s C).
Proof.
  split; [intros s H; exfalso; exact (H I) |].
  split; [intros s B; apply star_refl |].
  split; [reflexivity |].
  split; [intros s e H; exfalso; exact (H I) |].
  split; [intros s B e1 e2 _ H2 Hne; unfold ct_enabled;
          split; apply (st_in_rm_neq Nat.eq_dec); assumption |].
  split; [intros s B e H; exact H |].
  intros e s B C HP H. exact (Permutation_in e HP H).
Qed.

(* The decidability hypotheses (in Type, so stated separately). *)
Definition ct_valid_dec (s : nat) : {ct_valid s} + {~ ct_valid s} := left I.
Definition ct_enabled_dec (e s : nat) (B : list nat) : {ct_enabled e s B} + {~ ct_enabled e s B} :=
  in_dec Nat.eq_dec e B.

Lemma ct_nf_empty : forall s, normal_form ct_pstep (s, []).
Proof.
  intros s [c' H]. inversion H as [? ? ? ? Hin | ? ? Hinv]; subst; [destruct Hin | apply Hinv; exact I].
Qed.

(* Applying the whole buffer in order adds its length. *)
Lemma ct_run : forall l s, star ct_pstep (s, l) (s + length l, []).
Proof.
  induction l as [| e l IH]; intros s; simpl.
  - rewrite Nat.add_0_r. apply star_refl.
  - eapply star_step.
    + apply (ps_apply Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled s (e :: l) e I (or_introl eq_refl)).
      left. reflexivity.
    + rewrite (st_rm_head Nat.eq_dec). replace (s + S (length l)) with (ct_apply e s + length l)
        by (unfold ct_apply; lia). apply IH.
Qed.

(* (c) without "settled": at time 0 both processors have received {0}; one has applied it, the
   other has not started. Both meet Def. "Stream Processor" (and are fair), yet they disagree. *)
Definition ct_p1 : processor := mkProc (fun _ => [0]) (fun _ => (1, [])).
Definition ct_p2 : processor :=
  mkProc (fun _ => [0]) (fun t => match t with 0 => (0, [0]) | S _ => (1, []) end).

Lemma ct_one_step : star ct_pstep (0, [0]) (1, []).
Proof. exact (ct_run [0] 0). Qed.

Theorem base_thm_convergence_c_counterexample :
  ct_proc (fun e => e = 0) 0 ct_p1 /\ ct_proc (fun e => e = 0) 0 ct_p2 /\
  ct_fair ct_p1 /\ ct_fair ct_p2 /\
  recv ct_p1 0 = recv ct_p2 0 /\ psi ct_p1 0 <> psi ct_p2 0.
Proof.
  assert (Hnd : NoDup [0]) by (constructor; [intros [] | constructor]).
  split; [| split; [| split; [| split; [| split]]]].
  - split; [intros; exact Hnd |]. split; [intros t e [H | []]; symmetry; exact H |].
    split; [intros t; exists []; reflexivity |].
    split; [intros e -> ; exists 0; intros t _; left; reflexivity |].
    intros t. exact ct_one_step.
  - split; [intros; exact Hnd |]. split; [intros t e [H | []]; symmetry; exact H |].
    split; [intros t; exists []; reflexivity |].
    split; [intros e -> ; exists 0; intros t _; left; reflexivity |].
    intros [| t]; [apply star_refl | exact ct_one_step].
  - intros t _. split; [apply star_refl |]. intros N. exfalso. apply N. apply ct_nf_empty.
  - intros [| t] _.
    + split; [exact ct_one_step |]. intros _. exists (1, []). split; [| apply star_refl].
      pose proof (ps_apply Nat.eq_dec ct_apply ct_rho ct_valid ct_enabled 0 [0] 0 I
                    (or_introl eq_refl) (or_introl eq_refl)) as H.
      rewrite (st_rm_head Nat.eq_dec) in H. exact H.
    + split; [apply star_refl |]. intros N. exfalso. apply N. apply ct_nf_empty.
  - reflexivity.
  - simpl. discriminate.
Qed.

(* Infinite stream, "disagreements are transient": the stream is every natural number; p1 receives
   event n at time n, p2 one tick later. Both are processors, fair and settled at EVERY time, and
   they disagree at EVERY time. So agreement is never restored. *)
Definition ct_q1 : processor := mkProc (fun t => seq 0 (S t)) (fun t => (S t, [])).
Definition ct_q2 : processor := mkProc (fun t => seq 0 t) (fun t => (t, [])).

Lemma ct_seq_snoc : forall n, seq 0 (S n) = seq 0 n ++ [n].
Proof.
  assert (H : forall n k, seq k (S n) = seq k n ++ [k + n]).
  { induction n as [| n IH]; intros k; [simpl; rewrite Nat.add_0_r; reflexivity |].
    change (seq k (S (S n))) with (k :: seq (S k) (S n)). rewrite IH.
    change (seq k (S n)) with (k :: seq (S k) n). simpl. do 3 f_equal. lia. }
  intros n. exact (H n 0).
Qed.

Lemma ct_seq_len : forall n k, length (seq k n) = n.
Proof. induction n as [| n IH]; intros k; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Theorem base_thm_convergence_transient_counterexample :
  ct_proc (fun _ => True) 0 ct_q1 /\ ct_proc (fun _ => True) 0 ct_q2 /\
  ct_fair ct_q1 /\ ct_fair ct_q2 /\
  (forall t, ct_settled ct_q1 t /\ ct_settled ct_q2 t) /\
  (forall t, psi ct_q1 t <> psi ct_q2 t).
Proof.
  split; [| split; [| split; [| split; [| split]]]].
  - split; [intros t; apply seq_NoDup |]. split; [intros; exact I |].
    split; [intros t; exists [S t]; apply ct_seq_snoc |].
    split; [intros e _; exists e; intros t Ht; apply in_seq; lia |].
    intros t. pose proof (ct_run (seq 0 (S t)) 0) as H. rewrite ct_seq_len in H. exact H.
  - split; [intros t; apply seq_NoDup |]. split; [intros; exact I |].
    split; [intros t; exists [t]; apply ct_seq_snoc |].
    split; [intros e _; exists (S e); intros t Ht; apply in_seq; lia |].
    intros t. pose proof (ct_run (seq 0 t) 0) as H. rewrite ct_seq_len in H. exact H.
  - intros t H. exfalso. apply (f_equal (@length nat)) in H. simpl in H.
    rewrite !ct_seq_len in H. lia.
  - intros t H. exfalso. apply (f_equal (@length nat)) in H. simpl in H.
    rewrite !ct_seq_len in H. lia.
  - intros t. split; apply ct_nf_empty.
  - intros t. simpl. unfold psi. simpl. lia.
Qed.

(* ============================================================
   Non-vacuity on an infinite domain: the Z withdrawal registry of GovernanceWF.v under the
   causal GRS, with two processors receiving withdrawals 1 and 2 in different orders and at
   different times, starting from balance 1.
   ============================================================ *)

Open Scope Z_scope.

Local Notation zc_cstep := (GovernanceCausal.step Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).
Local Notation zc_pstep := (prstep Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).
Local Notation zc_rm := (GovernanceCausal.remove1 Nat.eq_dec).

Lemma zc_rho_star_reach : forall s B, star zc_cstep (s, B) (zw_rho_star s, B).
Proof.
  assert (H : forall (n : nat) s B, Z.to_nat (- s) = n -> star zc_cstep (s, B) (zw_rho_star s, B)).
  { induction n as [| n IH]; intros s B Hn; unfold zw_rho_star.
    - replace (Z.max s 0) with s by lia. apply star_refl.
    - destruct (Z_le_gt_dec 0 s) as [Hv | Hinv].
      + replace (Z.max s 0) with s by lia. apply star_refl.
      + eapply star_step.
        * apply GovernanceCausal.st_comp. unfold zw_valid. lia.
        * replace (Z.max s 0) with (Z.max (zw_rho s) 0) by (unfold zw_rho; lia).
          apply IH. unfold zw_rho. lia. }
  intros s B. apply (H (Z.to_nat (- s))). reflexivity.
Qed.

Definition zw_Phi_nat (s : Z) : nat := Z.to_nat (- s).

(* Every hypothesis of the stream section, for both potentials (Zwf on Z, and lt on nat). *)
Theorem zw_stream_registry :
  (forall s, ~ zw_valid s -> Zwf 0 (zw_Phi (zw_rho s)) (zw_Phi s)) /\
  (forall s, ~ zw_valid s -> (zw_Phi_nat (zw_rho s) < zw_Phi_nat s)%nat) /\
  (forall s B, star zc_cstep (s, B) (zw_rho_star s, B)) /\
  (forall s B e1 e2, zw_enabled e1 s B -> zw_enabled e2 s B -> e1 <> e2 ->
     zw_rho_star (zw_apply e2 (zw_rho_star (zw_apply e1 s)))
   = zw_rho_star (zw_apply e1 (zw_rho_star (zw_apply e2 s)))) /\
  (forall s e, ~ zw_valid s -> zw_rho_star (zw_apply e s) = zw_rho_star (zw_apply e (zw_rho s))) /\
  (forall s B e1 e2, zw_enabled e1 s B -> zw_enabled e2 s B -> e1 <> e2 ->
     In e2 (zc_rm e1 B) /\ zw_enabled e2 (zw_rho_star (zw_apply e1 s)) (zc_rm e1 B)) /\
  (forall s B e, zw_enabled e s B -> zw_enabled e (zw_rho s) B) /\
  (forall e s B C, Permutation B C -> zw_enabled e s B -> zw_enabled e s C) /\
  (forall s, zw_valid (zw_rho_star s)) /\
  (forall e s B N, zw_enabled e s B -> zw_enabled e s (B ++ N)) /\
  (forall s B, B <> [] -> exists e, In e B /\ zw_enabled e s B).
Proof.
  split; [exact zw_wfc |].
  split; [intros s H; unfold zw_valid in H; unfold zw_Phi_nat, zw_rho; lia |].
  split; [exact zc_rho_star_reach |].
  split; [intros s B e1 e2 _ _ _; apply zw_cc1 |].
  split; [exact zw_cc2 |].
  split; [intros s B e1 e2 _ H2 Hne; unfold zw_enabled;
          split; apply (st_in_rm_neq Nat.eq_dec); assumption |].
  split; [exact zw_enabled_after_comp |].
  split; [intros e s B C HP H; exact (Permutation_in e HP H) |].
  split; [intros s; unfold zw_valid, zw_rho_star; lia |].
  split; [intros e s B N H; apply in_or_app; left; exact H |].
  intros s [| x B] H; [congruence |]. exists x. split; left; reflexivity.
Qed.

Definition zw_valid_dec (s : Z) : {zw_valid s} + {~ zw_valid s} := Z_le_dec 0 s.
Definition zw_enabled_dec (e : nat) (s : Z) (B : list nat) : {zw_enabled e s B} + {~ zw_enabled e s B} :=
  in_dec Nat.eq_dec e B.

Lemma zc_apply : forall s B e s' B',
    0 <= s -> In e B -> s' = zw_apply e s -> zc_rm e B = B' -> zc_pstep (s, B) (s', B').
Proof. intros s B e s' B' Hv Hin -> <-. apply ps_apply; [exact Hv | exact Hin | exact Hin]. Qed.

Lemma zc_comp : forall s B s', s < 0 -> s' = zw_rho s -> zc_pstep (s, B) (s', B).
Proof. intros s B s' H ->. apply ps_comp. unfold zw_valid. lia. Qed.

Lemma zc_rm1 : forall (e : nat) l, zc_rm e (e :: l) = l.
Proof. exact (st_rm_head Nat.eq_dec). Qed.

Lemma zc_rm2 : forall (a e : nat) l, a <> e -> zc_rm e (a :: l) = a :: zc_rm e l.
Proof. intros a e l H. simpl. destruct (Nat.eq_dec a e); [contradiction | reflexivity]. Qed.

Lemma zc_nf_empty : forall s, 0 <= s -> normal_form zc_pstep (s, []).
Proof.
  intros s Hs [c' H]. inversion H as [? ? ? ? Hin | ? ? Hinv]; subst; [destruct Hin | apply Hinv; exact Hs].
Qed.

(* p1 receives 1 at time 0 and 2 at time 1; p2 receives 2 at time 1 and 1 at time 2. *)
Definition zp1 : processor :=
  mkProc (fun t => match t with 0%nat => [1%nat] | _ => [1%nat; 2%nat] end) (fun _ => (0, [])).
Definition zp2 : processor :=
  mkProc (fun t => match t with 0%nat => [] | 1%nat => [2%nat] | _ => [2%nat; 1%nat] end)
         (fun t => match t with 0%nat => (1, []) | _ => (0, []) end).

Ltac zc_app s e cfg :=
  apply (star_step _ _ cfg);
  [apply (zc_apply s _ e); [lia | left; reflexivity | reflexivity | apply zc_rm1] |].
Ltac zc_cmp cfg :=
  apply (star_step _ _ cfg); [apply zc_comp; [lia | reflexivity] |].

Lemma zp_run12 : star zc_pstep (1, [1%nat; 2%nat]) (0, []).
Proof.
  zc_app 1 1%nat (0, [2%nat]). zc_app 0 2%nat (-2, @nil nat).
  zc_cmp (-1, @nil nat). zc_cmp (0, @nil nat). apply star_refl.
Qed.

Lemma zp_run21 : star zc_pstep (1, [2%nat; 1%nat]) (0, []).
Proof.
  zc_app 1 2%nat (-1, [1%nat]). zc_cmp (0, [1%nat]).
  zc_app 0 1%nat (-1, @nil nat). zc_cmp (0, @nil nat). apply star_refl.
Qed.

Lemma zp_run1 : star zc_pstep (1, [1%nat]) (0, []).
Proof. zc_app 1 1%nat (0, @nil nat). apply star_refl. Qed.

Lemma zp_run2 : star zc_pstep (1, [2%nat]) (0, []).
Proof. zc_app 1 2%nat (-1, @nil nat). zc_cmp (0, @nil nat). apply star_refl. Qed.

Local Notation zc_proc := (is_processor Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).
Local Notation zc_fair := (fair Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).
Local Notation zc_settled := (settled Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled).

Definition zstream (e : nat) : Prop := In e [1%nat; 2%nat].

Theorem zw_processors :
  zc_proc zstream 1 zp1 /\ zc_proc zstream 1 zp2 /\ zc_fair zp1 /\ zc_fair zp2 /\
  (forall t, zc_settled zp1 t /\ zc_settled zp2 t) /\
  recv zp1 2 <> recv zp2 2.
Proof.
  assert (Nd12 : NoDup [1%nat; 2%nat]) by (repeat constructor; simpl; intuition discriminate).
  assert (Nd21 : NoDup [2%nat; 1%nat]) by (repeat constructor; simpl; intuition discriminate).
  assert (Nd1 : NoDup [1%nat]) by (repeat constructor; simpl; intuition).
  assert (Nd2 : NoDup [2%nat]) by (repeat constructor; simpl; intuition).
  split; [| split; [| split; [| split; [| split]]]].
  - split; [intros [| t]; assumption |].
    split; [intros [| t] e H; unfold zstream; simpl in *; intuition |].
    split; [intros [| t]; [exists [2%nat]; reflexivity | exists []; reflexivity] |].
    split; [intros e He; exists 1%nat; intros [| t] Ht; [lia | exact He] |].
    intros [| t]; [exact zp_run1 | exact zp_run12].
  - split; [intros [| [| t]]; [apply NoDup_nil | assumption | assumption] |].
    split; [intros [| [| t]] e H; unfold zstream; simpl in *; intuition |].
    split; [intros [| [| t]];
              [exists [2%nat]; reflexivity | exists [1%nat]; reflexivity | exists []; reflexivity] |].
    split; [intros e He; exists 2%nat; intros [| [| t]] Ht; [lia | lia |];
              unfold zstream in He; simpl in *; intuition |].
    intros [| [| t]]; [apply star_refl | exact zp_run2 | exact zp_run21].
  - intros [| t] H; [discriminate |]. split; [apply star_refl |].
    intros N. exfalso. apply N. apply zc_nf_empty. lia.
  - intros [| [| t]] H; try discriminate. split; [apply star_refl |].
    intros N. exfalso. apply N. apply zc_nf_empty. lia.
  - intros [| t]; split; apply zc_nf_empty; lia.
  - simpl. discriminate.
Qed.

(* The stream theorem applies (WF potential on Z): the processors agree at time 2, where they hold
   the same set in different orders. *)
Theorem zw_stream_agree : psi zp1 2 = psi zp2 2.
Proof.
  destruct zw_stream_registry as [Hw [_ [Hr [H1 [H2 [Hear [Heac [Hep _]]]]]]]].
  destruct zw_processors as [P1 [P2 [_ [_ [Hs _]]]]].
  destruct (Hs 2%nat) as [S1 _]. destruct (Hs 2%nat) as [_ S2].
  destruct (base_cor_infinite _ _ Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled Z (Zwf 0)
              (Zwf_well_founded 0) zw_Phi Hw Hr H1 H2 Hear Heac zw_valid_dec Hep zstream 1 zp1 zp2 P1 P2)
    as [_ [_ [_ Hc]]].
  apply Hc; [exact S1 | exact S2 |]. intros e. simpl. intuition.
Qed.

Theorem zw_stream_quiescent :
  exists sigma, zw_valid sigma /\ exists T, forall t, (T <= t)%nat -> psi zp1 t = sigma /\ psi zp2 t = sigma.
Proof.
  destruct zw_stream_registry as [Hw [_ [Hr [H1 [H2 [Hear [Heac [Hep _]]]]]]]].
  destruct zw_processors as [P1 [P2 [F1 [F2 _]]]].
  exact (base_cor_infinite_quiescent _ _ Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled Z
           (Zwf 0) (Zwf_well_founded 0) zw_Phi Hw Hr H1 H2 Hear Heac zw_valid_dec zw_enabled_dec Hep [1%nat; 2%nat] 1
           zp1 zp2 P1 P2 F1 F2).
Qed.

(* The same processors under the paper's nat-valued potential. *)
Theorem zw_stream_quiescent_nat :
  exists sigma, zw_valid sigma /\ exists T, forall t, (T <= t)%nat -> psi zp1 t = sigma /\ psi zp2 t = sigma.
Proof.
  destruct zw_stream_registry as [_ [Hw [Hr [H1 [H2 [Hear [Heac [Hep _]]]]]]]].
  destruct zw_processors as [P1 [P2 [F1 [F2 _]]]].
  exact (base_cor_quiescent_nat Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled zw_Phi_nat
           Hw Hr H1 H2 Hear Heac zw_valid_dec zw_enabled_dec Hep [1%nat; 2%nat] 1 zp1 zp2 P1 P2 F1 F2).
Qed.

Theorem zw_stream_convergence_nat : psi zp1 2 = psi zp2 2.
Proof.
  destruct zw_stream_registry as [_ [Hw [Hr [H1 [H2 [Hear [Heac [Hep _]]]]]]]].
  destruct zw_processors as [P1 [P2 [_ [_ [Hs _]]]]].
  destruct (Hs 2%nat) as [S1 S2].
  destruct (base_thm_convergence Nat.eq_dec zw_apply zw_rho zw_rho_star zw_valid zw_enabled zw_Phi_nat
              Hw Hr H1 H2 Hear Heac zw_valid_dec Hep zstream 1 zp1 zp2 P1 P2) as [_ [_ [_ Hc]]].
  apply Hc; [exact S1 | exact S2 |]. intros e. simpl. intuition.
Qed.

(* Incremental processing: p2 carries its configuration across arrivals and satisfies the
   incremental hypotheses, so incremental_computes rederives its reduction property. *)
Theorem zw_incremental :
  forall t, star zc_pstep (1, recv zp2 t) (conf zp2 t).
Proof.
  destruct zw_stream_registry as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Happ _]]]]]]]]]].
  apply (incremental_computes Nat.eq_dec zw_apply zw_rho zw_valid zw_enabled Happ 1 zp2
           (fun t => match t with 0%nat => [2%nat] | 1%nat => [1%nat] | _ => [] end)).
  - intros [| [| t]]; reflexivity.
  - apply star_refl.
  - intros [| [| t]]; simpl.
    + exact zp_run2.
    + zc_app 0 1%nat (-1, @nil nat). zc_cmp (0, @nil nat). apply star_refl.
    + apply star_refl.
Qed.

Close Scope Z_scope.
