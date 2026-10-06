(* RobertFair.v: Robert's theorem for fair asynchronous schedules on acyclic networks, in the
   repository's own propagation model (gap 16 (d) of REGIME-AUDIT.md). Axiom-free.

   The gap. On an acyclic federation the repository gated the unique fixed point and the runs that
   follow a topological order or end in a final flush (frun_solves, solve_unique,
   order_independent, propagation_flush, dist_exact), and, for Boolean resolver networks, the
   reduction of fair settlement to acyclicity of the asynchronous state graph
   (LocalFairSettlement.fair_settlement_of_acyclic). That EVERY fair asynchronous schedule of
   propagation steps settles, the asynchronous half of Robert's theorem (F. Robert, Discrete
   Iterations, 1986; stated as Theorem 1 of A. Richard's 2019 survey), was cited and not
   mechanized. This file mechanizes it. The theorem is Robert's; nothing here is new
   mathematics.

   Model. The distributed model of FederationEvents.v: a state t : nat -> V; the propagation step
   of target j is fstep t j (j overwrites its shared part with the image of its sources' CURRENT
   states, f j t (t j)); o lists the targets in a topological order (topoF src o). The hypotheses
   are the propagation part of FederationEvents.Common: f j reads t only through src j (f_loc),
   preserves validity (f_m1), and a later overwrite absorbs an earlier one (f_abs). A schedule
   sg : nat -> nat is fair (DistributedCycles.Fair o sg) when it names only targets and every
   target infinitely often; rb_run sg n h is the state after its first n steps; RSettles sg h q:
   from some step on the state is q (pointwise). RQuiet t: no propagation step changes t.

   Results, propagation only (Part 1).
     rb_robert_fair     every fair schedule from every valid start settles at frun o h, the run of
                        one topological order (Robert's asynchronous half).
     rb_limit_quiet     that state is quiescent; rb_unique: every quiescent state any propagation
                        word reaches from h equals it (the unique fixed point reachable from h).
     rb_topo_runs, rb_order_independent
                        every topological order of the targets reaches it: order_independent,
                        recovered in the distributed model.
     rb_rounds, rb_rounds_all, rb_rounds_pos
                        the bound. With any level function lv strictly increasing along source
                        arcs (for instance the depth: the longest source path into a vertex), and
                        rounds T 0 <= T 1 <= ... in each of which every target is updated, vertex
                        j is final from the end of round lv j + 1 on, so the state is final after
                        D + 1 rounds when every level is at most D (with the position in o, after
                        |o| rounds).
     rb_effective, rb_closed
                        with decidable values: along ANY propagation word (fair or not) the number
                        of effective steps (steps that change the state) is below 2^|o|, and a
                        closed word changes nothing: the asynchronous state graph is acyclic (the
                        alternative route, through a lexicographic potential on the unstable
                        targets).
   Results with events (Part 2), under Common, XU (and, for the exact form, the hypotheses of
   dist_exact):
     rb_events          a finite word of events and propagation steps followed by any fair
                        propagation schedule settles at the FedMachine run of its events
                        (propagation_flush, with the final flush replaced by any fair schedule).
     rb_event_schedule  the same for an infinite schedule of events and propagation steps with
                        finitely many events in which every target propagates infinitely often.
     rb_fair_dist_exact the exact condition: the limits of fair schedules of words with
                        trace-equivalent events agree iff XUR s0 /\ C2R (N s0), the condition of
                        DistributedExact.dist_exact. Infinitely many events give no settlement in
                        general and are not treated.
   Results in the lens (resolver) model and the Boolean form (Part 3).
     rb_lens_robert     the resolver model of SignedResolver.v (values X, a lens on js, the
                        asynchronous step rupd j): if every resolver Fv j reads only its sources
                        src j and src is acyclic (a topological order o of js), there is a unique
                        fixed point and every fair schedule from every start settles at it.
     rb_lens_closed     with decidable values, no closed asynchronous run changes the state.
     rb_robert_boolean  Robert's theorem for a Boolean network F on n vertices: if the GLOBAL
                        interaction graph G(F) (rb_garc: j -> i when flipping x_j changes F_i at
                        some state) has no cycle, then no local graph has one, the asynchronous
                        state graph is acyclic (NoClosedChange), F has a unique fixed point, and
                        every fair schedule from every start settles at it. The last two
                        conclusions go through LocalFairSettlement.fair_settlement_of_acyclic.
   Boundaries (Part 4).
     rb_neg2_cycle      acyclicity cannot be dropped: the negative 2-cycle x0 := not x1, x1 := x0
                        has a cycle in G(F), no fixed point, and no fair schedule settles.
     rb_copyback_cycle  the positive 2-cycle x0 := x1, x1 := x0: two fixed points, and from (0, 1)
                        two fair schedules settle at different ones.
     rb_converse_fails  the converse of Robert's theorem fails: Shih and Ho's network has a cycle
                        in G(F), and every fair schedule from every start still settles at its
                        unique fixed point (LocalFairSettlement.shih_ho_instance).
     rb_dist_cycle_needed, rb_absorb_needed
                        in the distributed model: a negation loop satisfies every hypothesis but
                        acyclicity (no order is topological) and no fair schedule settles; a
                        counter (f 0 z x = x + 1) satisfies every hypothesis but absorption and no
                        schedule settles.
   Non-vacuity: rb_example (FederationOrder.v's three-registry example: every fair schedule
   settles at the state with 12 at registry 2, within two rounds, with fewer than 8 effective
   steps; both topological orders agree), rb_supply_events (the supply federation with events),
   rb_supply_fair_conv and rb_gg_not_fair_conv (the exact condition holds and fails),
   rb_bool3 (a Boolean network with an acyclic global graph and its fixed point). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.FederationEvents NC.FederationEventsConverse NC.DistributedExact
  NC.DistributedCycles NC.DistributedCyclesExact NC.CanonicalExecution NC.SignedResolver
  NC.LocalSigned NC.LocalFairSettlement.
Require NC.FederationOrder NC.FederationGRS.
Import ListNotations.

(* ============================================================================================ *)
(* Part 0. Generic pieces.                                                                      *)
(* ============================================================================================ *)

Definition rb_noreg (e : Empty_set) : nat := match e with end.
Definition rb_nosig {V : Type} (e : Empty_set) (x : V) : V := match e with end.
Definition rb_idr {V : Type} (j : nat) (x : V) : V := x.

(* The position of j in l. *)
Fixpoint rb_idx (l : list nat) (j : nat) : nat :=
  match l with [] => 0 | a :: r => if Nat.eqb a j then 0 else S (rb_idx r j) end.

Lemma rb_idx_lt : forall l j, In j l -> rb_idx l j < length l.
Proof.
  induction l as [| a l IH]; intros j Hj; [destruct Hj |]. simpl.
  destruct (Nat.eqb_spec a j) as [_ | N]; [lia |].
  destruct Hj as [E | Hj]; [contradiction | specialize (IH j Hj); lia].
Qed.

Lemma rb_fstep_at : forall (V : Type) (f : nat -> (nat -> V) -> V -> V) t j k,
  fstep V f t j k = if Nat.eqb k j then f j t (t j) else t k.
Proof. reflexivity. Qed.

Lemma rb_frun_cons : forall (V : Type) (f : nat -> (nat -> V) -> V -> V) a w t,
  frun V f (a :: w) t = frun V f w (fstep V f t a).
Proof. reflexivity. Qed.

Lemma rb_frun_app : forall (V : Type) (f : nat -> (nat -> V) -> V -> V) w1 w2 t,
  frun V f (w1 ++ w2) t = frun V f w2 (frun V f w1 t).
Proof. intros V f w1 w2 t. unfold frun. apply fold_left_app. Qed.

Section Topo.
  Variable src : nat -> list nat.

  Lemma rb_topo_tail : forall pre l, topoF src (pre ++ l) -> topoF src l.
  Proof.
    induction pre as [| a pre IH]; intros l H; [exact H |].
    simpl in H. destruct H as [_ [_ H]]. exact (IH l H).
  Qed.

  (* In a topological order, the sources of a vertex that lie in the order lie before it. *)
  Lemma rb_topo_src : forall pre a suf, topoF src (pre ++ a :: suf) ->
    forall k, In k (src a) -> In k (pre ++ a :: suf) -> In k pre.
  Proof.
    intros pre a suf H k Hk Ho. pose proof (rb_topo_tail pre (a :: suf) H) as H'.
    simpl in H'. destruct H' as [_ [Hs _]].
    apply in_app_or in Ho. destruct Ho as [Ho | Ho]; [exact Ho |]. exfalso. exact (Hs k Hk Ho).
  Qed.

  Lemma rb_idx_topo : forall l, topoF src l -> forall j k, In j l -> In k (src j) -> In k l ->
    rb_idx l k < rb_idx l j.
  Proof.
    induction l as [| a l IH]; intros H j k Hj Hk Hkl; [destruct Hj |].
    simpl in H. destruct H as [Ha [Hs Hr]]. simpl.
    destruct (Nat.eqb_spec a j) as [-> | Naj].
    - exfalso. exact (Hs k Hk Hkl).
    - destruct Hj as [E | Hj]; [contradiction |].
      destruct (Nat.eqb_spec a k) as [_ | Nak]; [lia |].
      destruct Hkl as [E | Hkl]; [contradiction |]. specialize (IH Hr j k Hj Hk Hkl). lia.
  Qed.

  (* Appending a vertex that no listed vertex reads, and that does not read itself. *)
  Lemma rb_topo_snoc : forall l k, topoF src l -> ~ In k l -> (forall a, In a l -> ~ In k (src a)) ->
    ~ In k (src k) -> topoF src (l ++ [k]).
  Proof.
    induction l as [| a l IH]; intros k H Hk Hs Hkk.
    - simpl. split; [intros [] |]. split; [| exact I].
      intros x Hx [E | []]. subst x. exact (Hkk Hx).
    - simpl in H. destruct H as [Ha [Has Hr]]. simpl. split; [| split].
      + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | [E | []]]; [exact (Ha Hin) |].
        subst k. apply Hk. left. reflexivity.
      + intros x Hx [E | Hin]; [subst x; apply (Has a Hx); left; reflexivity |].
        apply in_app_or in Hin. destruct Hin as [Hin | [E | []]]; [apply (Has x Hx); right; exact Hin |].
        subst x. exact (Hs a (or_introl eq_refl) Hx).
      + apply IH; [exact Hr | intro Hin; apply Hk; right; exact Hin | | exact Hkk].
        intros b Hb. apply Hs. right. exact Hb.
  Qed.
End Topo.

(* ============================================================================================ *)
(* Part 1. Robert's theorem in the distributed propagation model.                               *)
(* ============================================================================================ *)

Section Robert.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable o : list nat.

  Hypothesis f_loc : forall j z1 z2 x, (forall k, In k (src j) -> z1 k = z2 k) -> f j z1 x = f j z2 x.
  Hypothesis o_topo : topoF src o.
  Hypothesis f_m1 : forall j z x, Inv V valid z -> valid j x -> valid j (f j z x).
  Hypothesis f_abs : forall j z z' x, Inv V valid z -> Inv V valid z' -> valid j x ->
    f j z (f j z' x) = f j z x.

  Local Notation feqV := (feq V).
  Local Notation InvV := (Inv V valid).
  Local Notation fr := (frun V f).

  Definition rb_step (j : nat) (t : nat -> V) : nat -> V := fstep V f t j.
  Definition rb_run (sg : nat -> nat) (n : nat) (h : nat -> V) : nat -> V := prs (nat -> V) rb_step sg n h.
  Definition RSettles (sg : nat -> nat) (h q : nat -> V) : Prop :=
    exists M, forall n, M <= n -> feqV (rb_run sg n h) q.
  Definition RQuiet (t : nat -> V) : Prop := forall j, In j o -> f j t (t j) = t j.

  (* The propagation hypotheses are the propagation part of FederationEvents.Common. *)
  Lemma rb_common : Common V src f valid rb_idr Empty_set rb_noreg rb_nosig o.
  Proof.
    constructor; [exact f_loc | exact o_topo | exact f_m1 | exact f_abs | intros; reflexivity | intros [] | intros []].
  Qed.

  Lemma rb_feq_refl : forall t, feqV t t.
  Proof. intros t k. reflexivity. Qed.
  Lemma rb_feq_sym : forall t u, feqV t u -> feqV u t.
  Proof. intros t u H k. symmetry. apply H. Qed.
  Lemma rb_feq_trans : forall t u w, feqV t u -> feqV u w -> feqV t w.
  Proof. intros t u w H1 H2 k. rewrite H1. apply H2. Qed.

  Lemma rb_run_S : forall sg n h, rb_run sg (S n) h = rb_step (sg n) (rb_run sg n h).
  Proof. reflexivity. Qed.

  Lemma rb_step_at : forall j t k, rb_step j t k = if Nat.eqb k j then f j t (t j) else t k.
  Proof. reflexivity. Qed.

  Lemma rb_step_inv : forall j t, InvV t -> InvV (rb_step j t).
  Proof.
    intros j t H k. rewrite rb_step_at. destruct (Nat.eqb_spec k j) as [-> | _]; [| apply H].
    apply f_m1; [exact H | apply H].
  Qed.

  Lemma rb_run_inv : forall sg n h, InvV h -> InvV (rb_run sg n h).
  Proof.
    intros sg n h H. induction n as [| n IH]; [exact H |]. rewrite rb_run_S. apply rb_step_inv. exact IH.
  Qed.

  Lemma rb_step_ext : forall j t u, feqV t u -> feqV (rb_step j t) (rb_step j u).
  Proof.
    intros j t u H k. rewrite !rb_step_at. destruct (Nat.eqb k j); [| apply H].
    rewrite (H j). apply f_loc. intros i _. apply H.
  Qed.

  Lemma rb_run_out : forall sg, (forall n, In (sg n) o) -> forall h k, ~ In k o -> forall n,
    rb_run sg n h k = h k.
  Proof.
    intros sg Hs h k Hk n. induction n as [| n IH]; [reflexivity |].
    rewrite rb_run_S, rb_step_at. destruct (Nat.eqb_spec k (sg n)) as [E | _]; [| exact IH].
    exfalso. apply Hk. rewrite E. apply Hs.
  Qed.

  Lemma rb_settles_feq : forall sg h q q', RSettles sg h q -> feqV q q' -> RSettles sg h q'.
  Proof.
    intros sg h q q' [M HM] E. exists M. intros n Hn. exact (rb_feq_trans _ _ _ (HM n Hn) E).
  Qed.

  Lemma rb_settles_unique : forall sg h q1 q2, RSettles sg h q1 -> RSettles sg h q2 -> feqV q1 q2.
  Proof.
    intros sg h q1 q2 [M1 H1] [M2 H2].
    apply (rb_feq_trans _ (rb_run sg (Nat.max M1 M2) h)); [apply rb_feq_sym, H1 | apply H2]; lia.
  Qed.

  (* The image a target is repaired to does not depend on the stale values it held. *)
  Lemma rb_image : forall sg h, InvV h -> forall z, InvV z -> forall j n,
    f j z (rb_run sg n h j) = f j z (h j).
  Proof.
    intros sg h Hh z Hz j n. induction n as [| n IH]; [reflexivity |].
    rewrite rb_run_S, rb_step_at. destruct (Nat.eqb_spec j (sg n)) as [E | _]; [| exact IH].
    rewrite <- E. rewrite f_abs; [exact IH | exact Hz | exact (rb_run_inv sg n h Hh) |].
    exact (rb_run_inv sg n h Hh j).
  Qed.

  Lemma rb_q_inv : forall h, InvV h -> InvV (fr o h).
  Proof. intros h H. exact (frun_inv _ _ _ _ _ _ _ _ _ rb_common o h H). Qed.

  Lemma rb_q_solves : forall h j, In j o -> fr o h j = f j (fr o h) (h j).
  Proof. intros h j Hj. exact (frun_solves _ _ _ _ _ _ _ _ _ rb_common o h o_topo j Hj). Qed.

  Lemma rb_q_out : forall h k, ~ In k o -> fr o h k = h k.
  Proof. intros h k Hk. apply frun_out. exact Hk. Qed.

  (* Once the sources of j are final, the next update of j makes j final. *)
  Lemma rb_final : forall sg, (forall n, In (sg n) o) -> forall h, InvV h -> forall j n0,
    (forall k, In k (src j) -> In k o -> forall m, n0 <= m -> rb_run sg m h k = fr o h k) ->
    forall m, n0 <= m -> sg m = j -> rb_run sg (S m) h j = fr o h j.
  Proof.
    intros sg Hs h Hh j n0 Hsrc m Hm Ej.
    assert (Hj : In j o) by (rewrite <- Ej; apply Hs).
    rewrite rb_run_S, rb_step_at, Ej, Nat.eqb_refl.
    rewrite (f_loc j (rb_run sg m h) (fr o h)).
    - rewrite (rb_image sg h Hh (fr o h) (rb_q_inv h Hh) j m). symmetry. apply rb_q_solves. exact Hj.
    - intros k Hk. destruct (in_dec Nat.eq_dec k o) as [Hko | Hko].
      + exact (Hsrc k Hk Hko m Hm).
      + rewrite (rb_run_out sg Hs h k Hko m). symmetry. apply rb_q_out. exact Hko.
  Qed.

  Lemma rb_final_after : forall sg, (forall n, In (sg n) o) -> forall h, InvV h -> forall j n0,
    (forall k, In k (src j) -> In k o -> forall m, n0 <= m -> rb_run sg m h k = fr o h k) ->
    forall t, n0 <= t -> sg t = j -> forall m, t < m -> rb_run sg m h j = fr o h j.
  Proof.
    intros sg Hs h Hh j n0 Hsrc t Ht Et m Hm. induction m as [| m IH]; [lia |].
    destruct (Nat.eq_dec (sg m) j) as [E | N].
    - apply (rb_final sg Hs h Hh j n0 Hsrc m); [lia | exact E].
    - rewrite rb_run_S, rb_step_at.
      destruct (Nat.eqb_spec j (sg m)) as [E | _]; [congruence |].
      apply IH. destruct (Nat.eq_dec t m) as [-> | Ntm]; [congruence | lia].
  Qed.

  Lemma rb_max_list : forall (Q : nat -> nat -> Prop), (forall k M M', M <= M' -> Q k M -> Q k M') ->
    forall l, (forall k, In k l -> In k o -> exists M, Q k M) ->
    exists M, forall k, In k l -> In k o -> Q k M.
  Proof.
    intros Q Hmono. induction l as [| a l IH]; intros H; [exists 0; intros k [] |].
    destruct IH as [M1 H1]; [intros k Hk; apply H; right; exact Hk |].
    destruct (in_dec Nat.eq_dec a o) as [Ha | Ha].
    - destruct (H a (or_introl eq_refl) Ha) as [M2 H2]. exists (Nat.max M1 M2).
      intros k [<- | Hk] Hko.
      + apply (Hmono a M2); [lia | exact H2].
      + apply (Hmono k M1); [lia | exact (H1 k Hk Hko)].
    - exists M1. intros k [<- | Hk] Hko; [contradiction | exact (H1 k Hk Hko)].
  Qed.

  (* Each target becomes final, by induction along the topological order. *)
  Theorem rb_fair_vertex : forall sg, Fair o sg -> forall h, InvV h -> forall j, In j o ->
    exists M, forall m, M <= m -> rb_run sg m h j = fr o h j.
  Proof.
    intros sg Hfair h Hh. destruct Hfair as [Hs Hf].
    set (Q := fun k M => forall m, M <= m -> rb_run sg m h k = fr o h k).
    assert (Qm : forall k M M', M <= M' -> Q k M -> Q k M').
    { intros k M M' HM HQ m Hm. apply HQ. lia. }
    assert (G : forall pre, (exists suf, o = pre ++ suf) -> forall j, In j pre -> exists M, Q j M).
    { apply (List.rev_ind (fun pre => (exists suf, o = pre ++ suf) -> forall j, In j pre -> exists M, Q j M)).
      { intros _ j []. }
      intros a pre IH [suf Hsuf] j Hj.
      assert (Ho : o = pre ++ a :: suf) by (rewrite Hsuf, <- app_assoc; reflexivity).
      assert (IH' : forall k, In k pre -> exists M, Q k M)
        by (apply IH; exists (a :: suf); exact Ho).
      apply in_app_or in Hj. destruct Hj as [Hj | [<- | []]]; [exact (IH' j Hj) |].
      assert (Hsrc : forall k, In k (src a) -> In k o -> In k pre).
      { intros k Hk Hko. rewrite Ho in Hko. apply (rb_topo_src src pre a suf); [| exact Hk | exact Hko].
        rewrite <- Ho. exact o_topo. }
      destruct (rb_max_list Q Qm (src a)) as [M HM].
      { intros k Hk Hko. exact (IH' k (Hsrc k Hk Hko)). }
      destruct (Hf a M) as [t [Ht Et]]; [rewrite Ho; apply in_or_app; right; left; reflexivity |].
      exists (S t). intros m Hm.
      exact (rb_final_after sg Hs h Hh a M HM t Ht Et m ltac:(lia)). }
    intros j Hj. apply (G o); [exists []; rewrite app_nil_r; reflexivity | exact Hj].
  Qed.

  (* Robert's asynchronous half: every fair schedule from every valid start settles at the run of
     one topological order. *)
  Theorem rb_robert_fair : forall sg, Fair o sg -> forall h, InvV h -> RSettles sg h (fr o h).
  Proof.
    intros sg Hfair h Hh.
    set (Q := fun k M => forall m, M <= m -> rb_run sg m h k = fr o h k).
    destruct (rb_max_list Q (fun k M M' HM HQ m Hm => HQ m ltac:(lia)) o) as [M HM].
    { intros k _ Hk. exact (rb_fair_vertex sg Hfair h Hh k Hk). }
    exists M. intros n Hn k. destruct (in_dec Nat.eq_dec k o) as [Hk | Hk].
    - exact (HM k Hk Hk n Hn).
    - rewrite (rb_run_out sg (proj1 Hfair) h k Hk n). symmetry. apply rb_q_out. exact Hk.
  Qed.

  (* The limit is quiescent. *)
  Theorem rb_limit_quiet : forall h, InvV h -> RQuiet (fr o h).
  Proof.
    intros h Hh j Hj. rewrite (rb_q_solves h j Hj).
    apply f_abs; [exact (rb_q_inv h Hh) | exact (rb_q_inv h Hh) | exact (Hh j)].
  Qed.

  (* A fair run can only settle at a quiescent state. *)
  Lemma rb_settles_quiet : forall sg, Fair o sg -> forall h q, RSettles sg h q -> RQuiet q.
  Proof.
    intros sg [_ Hf] h q [M HM] j Hj. destruct (Hf j M Hj) as [t [Ht Et]].
    pose proof (HM (S t) ltac:(lia) j) as A. pose proof (HM t Ht) as B.
    rewrite rb_run_S, rb_step_at, Et, Nat.eqb_refl in A.
    transitivity (f j (rb_run sg t h) (rb_run sg t h j)); [| exact A].
    rewrite (B j). apply f_loc. intros k _. symmetry. apply B.
  Qed.

  Lemma rb_quiet_ext : forall t u, feqV t u -> RQuiet t -> RQuiet u.
  Proof.
    intros t u H Ht j Hj. rewrite <- (H j).
    transitivity (f j t (t j)); [apply f_loc; intros k _; symmetry; apply H | exact (Ht j Hj)].
  Qed.

  Lemma rb_frun_quiet : forall l t, RQuiet t -> (forall j, In j l -> In j o) -> feqV (fr l t) t.
  Proof.
    induction l as [| a l IH]; intros t Ht Hl; [apply rb_feq_refl |].
    rewrite rb_frun_cons.
    assert (E : feqV (fstep V f t a) t).
    { intro k. rewrite rb_fstep_at. destruct (Nat.eqb_spec k a) as [-> | _]; [| reflexivity].
      apply Ht. apply Hl. left. reflexivity. }
    apply (rb_feq_trans _ (fr l t)); [exact (frun_ext _ _ _ _ _ _ _ _ _ rb_common l _ _ E) |].
    apply IH; [exact Ht | intros j Hj; apply Hl; right; exact Hj].
  Qed.

  Lemma rb_word_flush : forall w t, InvV t -> Forall (fun j => In j o) w ->
    feqV (N V f rb_idr o (fr w t)) (N V f rb_idr o t).
  Proof.
    induction w as [| a w IH]; intros t Ht Hw; [apply rb_feq_refl |].
    inversion Hw as [| ? ? Ha Hw']; subst. rewrite rb_frun_cons.
    apply (rb_feq_trans _ (N V f rb_idr o (fstep V f t a))).
    - apply IH; [exact (rb_step_inv a t Ht) | exact Hw'].
    - exact (flush_prop _ _ _ _ _ _ _ _ _ rb_common a t Ht Ha).
  Qed.

  (* Uniqueness: every quiescent state that a propagation word reaches from h is the limit. *)
  Theorem rb_unique : forall h, InvV h -> forall w, Forall (fun j => In j o) w ->
    RQuiet (fr w h) -> feqV (fr w h) (fr o h).
  Proof.
    intros h Hh w Hw Hq.
    assert (Iw : InvV (fr w h)) by exact (frun_inv _ _ _ _ _ _ _ _ _ rb_common w h Hh).
    apply (rb_feq_trans _ (fr o (fr w h))); [apply rb_feq_sym, rb_frun_quiet; [exact Hq | auto] |].
    apply (rb_feq_trans _ (N V f rb_idr o (fr w h))).
    { apply rb_feq_sym. exact (N_frun _ _ _ _ _ _ _ _ _ rb_common _ Iw). }
    apply (rb_feq_trans _ (N V f rb_idr o h)); [exact (rb_word_flush w h Hh Hw) |].
    exact (N_frun _ _ _ _ _ _ _ _ _ rb_common _ Hh).
  Qed.

  (* Every topological order of the targets reaches the limit (order_independent, recovered). *)
  Theorem rb_topo_runs : forall o', topoF src o' -> (forall j, In j o' <-> In j o) ->
    forall h, InvV h -> feqV (fr o' h) (fr o h).
  Proof.
    intros o' Ht Hiff h Hh. apply rb_unique; [exact Hh | apply Forall_forall; intros j Hj; apply Hiff; exact Hj |].
    intros j Hj. assert (Hj' : In j o') by (apply Hiff; exact Hj).
    rewrite (frun_solves _ _ _ _ _ _ _ _ _ rb_common o' h Ht j Hj').
    assert (I' : InvV (fr o' h)) by exact (frun_inv _ _ _ _ _ _ _ _ _ rb_common o' h Hh).
    apply f_abs; [exact I' | exact I' | exact (Hh j)].
  Qed.

  Theorem rb_order_independent : forall o1 o2, topoF src o1 -> topoF src o2 ->
    (forall j, In j o1 <-> In j o) -> (forall j, In j o2 <-> In j o) ->
    forall h, InvV h -> feqV (fr o1 h) (fr o2 h).
  Proof.
    intros o1 o2 H1 H2 E1 E2 h Hh.
    apply (rb_feq_trans _ (fr o h)); [exact (rb_topo_runs o1 H1 E1 h Hh) |].
    apply rb_feq_sym. exact (rb_topo_runs o2 H2 E2 h Hh).
  Qed.

  (* ----- the bound in rounds ----- *)

  (* Round [a, b): every target is updated at some step of it. *)
  Definition RCovers (sg : nat -> nat) (a b : nat) : Prop :=
    forall j, In j o -> exists t, a <= t < b /\ sg t = j.

  Theorem rb_rounds : forall sg, (forall n, In (sg n) o) -> forall h, InvV h ->
    forall (lv T : nat -> nat),
    (forall j k, In j o -> In k (src j) -> In k o -> lv k < lv j) ->
    (forall i, T i <= T (S i)) -> (forall i, RCovers sg (T i) (T (S i))) ->
    forall j, In j o -> forall m, T (S (lv j)) <= m -> rb_run sg m h j = fr o h j.
  Proof.
    intros sg Hs h Hh lv T Hlv Hmono Hcov.
    assert (Tm : forall i i', i <= i' -> T i <= T i').
    { intros i i' H. induction H as [| i' _ IH]; [lia | pose proof (Hmono i'); lia]. }
    assert (G : forall d j, In j o -> lv j <= d -> forall m, T (S (lv j)) <= m -> rb_run sg m h j = fr o h j).
    { induction d as [| d IH]; intros j Hj Hd m Hm;
        destruct (Hcov (lv j) j Hj) as [t [[Ht1 Ht2] Et]].
      - assert (Hsrc : forall k, In k (src j) -> In k o -> forall m', T (lv j) <= m' ->
                  rb_run sg m' h k = fr o h k).
        { intros k Hk Hko. pose proof (Hlv j k Hj Hk Hko). lia. }
        exact (rb_final_after sg Hs h Hh j (T (lv j)) Hsrc t Ht1 Et m ltac:(lia)).
      - assert (Hsrc : forall k, In k (src j) -> In k o -> forall m', T (lv j) <= m' ->
                  rb_run sg m' h k = fr o h k).
        { intros k Hk Hko m' Hm'. pose proof (Hlv j k Hj Hk Hko) as L.
          apply (IH k Hko); [lia |]. pose proof (Tm (S (lv k)) (lv j) ltac:(lia)). lia. }
        exact (rb_final_after sg Hs h Hh j (T (lv j)) Hsrc t Ht1 Et m ltac:(lia)). }
    intros j Hj. exact (G (lv j) j Hj (le_n _)).
  Qed.

  Theorem rb_rounds_all : forall sg, (forall n, In (sg n) o) -> forall h, InvV h ->
    forall (lv T : nat -> nat),
    (forall j k, In j o -> In k (src j) -> In k o -> lv k < lv j) ->
    (forall i, T i <= T (S i)) -> (forall i, RCovers sg (T i) (T (S i))) ->
    forall R, (forall j, In j o -> lv j < R) -> forall m, T R <= m -> feqV (rb_run sg m h) (fr o h).
  Proof.
    intros sg Hs h Hh lv T Hlv Hmono Hcov R HR m Hm k.
    assert (Tm : forall i i', i <= i' -> T i <= T i').
    { intros i i' H. induction H as [| i' _ IH]; [lia | pose proof (Hmono i'); lia]. }
    destruct (in_dec Nat.eq_dec k o) as [Hk | Hk].
    - apply (rb_rounds sg Hs h Hh lv T Hlv Hmono Hcov k Hk). pose proof (Tm (S (lv k)) R (HR k Hk)). lia.
    - rewrite (rb_run_out sg Hs h k Hk m). symmetry. apply rb_q_out. exact Hk.
  Qed.

  (* With the position in o as the level: final after |o| rounds. *)
  Theorem rb_rounds_pos : forall sg, (forall n, In (sg n) o) -> forall h, InvV h ->
    forall T : nat -> nat, (forall i, T i <= T (S i)) -> (forall i, RCovers sg (T i) (T (S i))) ->
    forall m, T (length o) <= m -> feqV (rb_run sg m h) (fr o h).
  Proof.
    intros sg Hs h Hh T Hmono Hcov.
    apply (rb_rounds_all sg Hs h Hh (rb_idx o) T); [| exact Hmono | exact Hcov |].
    - intros j k Hj Hk Hko. exact (rb_idx_topo src o o_topo j k Hj Hk Hko).
    - intros j Hj. apply rb_idx_lt. exact Hj.
  Qed.

  (* ----- effective steps and acyclicity of the asynchronous state graph ----- *)

  Section Eff.
    Variable V_eq_dec : forall a b : V, {a = b} + {a <> b}.

    (* j is unstable at t: its propagation step changes t. *)
    Definition rb_unst (t : nat -> V) (j : nat) : bool :=
      if V_eq_dec (f j t (t j)) (t j) then false else true.

    (* The unstable targets of l, read as a binary number, most significant first. *)
    Fixpoint rb_pot (l : list nat) (t : nat -> V) : nat :=
      match l with
      | [] => 0
      | a :: r => (if rb_unst t a then 2 ^ length r else 0) + rb_pot r t
      end.

    (* The number of effective steps of a propagation word. *)
    Fixpoint rb_eff (w : list nat) (t : nat -> V) : nat :=
      match w with
      | [] => 0
      | j :: w' => (if rb_unst t j then 1 else 0) + rb_eff w' (fstep V f t j)
      end.

    Lemma rb_pot_lt : forall l t, rb_pot l t < 2 ^ length l.
    Proof.
      induction l as [| a r IH]; intros t; [simpl; lia |]. cbn [rb_pot length].
      replace (2 ^ S (length r)) with (2 * 2 ^ length r) by reflexivity.
      pose proof (IH t). destruct (rb_unst t a); lia.
    Qed.

    Lemma rb_unst_ext : forall t u j, feqV t u -> rb_unst t j = rb_unst u j.
    Proof.
      intros t u j H. unfold rb_unst. rewrite (H j).
      rewrite (f_loc j t u (u j)) by (intros k _; apply H). reflexivity.
    Qed.

    Lemma rb_pot_ext : forall l t u, feqV t u -> rb_pot l t = rb_pot l u.
    Proof.
      induction l as [| a l IH]; intros t u H; [reflexivity |]. cbn [rb_pot].
      rewrite (rb_unst_ext t u a H), (IH t u H). reflexivity.
    Qed.

    Lemma rb_noop : forall t j, rb_unst t j = false -> feqV (fstep V f t j) t.
    Proof.
      intros t j H k. unfold rb_unst in H. rewrite rb_fstep_at.
      destruct (V_eq_dec (f j t (t j)) (t j)) as [E | _]; [| discriminate H].
      destruct (Nat.eqb_spec k j) as [-> | _]; [exact E | reflexivity].
    Qed.

    (* An effective step lowers the potential: the updated target becomes stable, and no target
       placed before it reads it. *)
    Lemma rb_pot_step : forall l, topoF src l -> forall j t, In j l -> InvV t -> rb_unst t j = true ->
      rb_pot l (fstep V f t j) < rb_pot l t.
    Proof.
      induction l as [| a r IH]; intros Ht j t Hj Hi Hu; [destruct Hj |].
      simpl in Ht. destruct Ht as [Ha [Hs Hr]]. cbn [rb_pot].
      destruct (Nat.eq_dec j a) as [-> | Nja].
      - assert (Es : rb_unst (fstep V f t a) a = false).
        { unfold rb_unst. rewrite rb_fstep_at, Nat.eqb_refl.
          rewrite (f_loc a (fstep V f t a) t).
          - rewrite f_abs; [| exact Hi | exact Hi | exact (Hi a)].
            destruct (V_eq_dec (f a t (t a)) (f a t (t a))) as [_ | N]; [reflexivity | contradiction].
          - intros k Hk. rewrite rb_fstep_at. destruct (Nat.eqb_spec k a) as [-> | _]; [| reflexivity].
            exfalso. exact (Hs a Hk (or_introl eq_refl)). }
        rewrite Es, Hu. pose proof (rb_pot_lt r (fstep V f t a)). lia.
      - destruct Hj as [E | Hj]; [congruence |].
        assert (Ea : rb_unst (fstep V f t j) a = rb_unst t a).
        { unfold rb_unst. rewrite (rb_fstep_at V f t j a).
          destruct (Nat.eqb_spec a j) as [E | _]; [congruence |].
          rewrite (f_loc a (fstep V f t j) t); [reflexivity |].
          intros k Hk. rewrite rb_fstep_at. destruct (Nat.eqb_spec k j) as [-> | _]; [| reflexivity].
          exfalso. exact (Hs j Hk (or_intror Hj)). }
        rewrite Ea. pose proof (IH Hr j t Hj Hi Hu). lia.
    Qed.

    Theorem rb_eff_bound : forall w h, InvV h -> Forall (fun j => In j o) w ->
      rb_eff w h + rb_pot o (fr w h) <= rb_pot o h.
    Proof.
      induction w as [| j w IH]; intros h Hh Hw; [simpl; lia |].
      inversion Hw as [| ? ? Hj Hw']; subst. cbn [rb_eff]. rewrite rb_frun_cons.
      pose proof (IH (fstep V f h j) (rb_step_inv j h Hh) Hw') as A.
      destruct (rb_unst h j) eqn:U.
      - pose proof (rb_pot_step o o_topo j h Hj Hh U). lia.
      - rewrite (rb_pot_ext o _ _ (rb_noop h j U)) in A. lia.
    Qed.

    (* Along any propagation word, fair or not, fewer than 2^|o| steps change the state. *)
    Theorem rb_effective : forall w h, InvV h -> Forall (fun j => In j o) w -> rb_eff w h < 2 ^ length o.
    Proof.
      intros w h Hh Hw. pose proof (rb_eff_bound w h Hh Hw). pose proof (rb_pot_lt o h). lia.
    Qed.

    Lemma rb_eff_app : forall w1 w2 h, rb_eff (w1 ++ w2) h = rb_eff w1 h + rb_eff w2 (fr w1 h).
    Proof.
      induction w1 as [| a w1 IH]; intros w2 h; [reflexivity |].
      cbn [app rb_eff]. rewrite IH, rb_frun_cons. lia.
    Qed.

    Lemma rb_eff_zero : forall w h, rb_eff w h = 0 -> feqV (fr w h) h.
    Proof.
      induction w as [| a w IH]; intros h H; [apply rb_feq_refl |].
      cbn [rb_eff] in H. rewrite rb_frun_cons.
      destruct (rb_unst h a) eqn:U; [lia |].
      apply (rb_feq_trans _ (fstep V f h a)); [apply IH; lia | exact (rb_noop h a U)].
    Qed.

    (* The asynchronous state graph is acyclic: a closed propagation word changes nothing. *)
    Theorem rb_closed : forall h, InvV h -> forall w1 w2, Forall (fun j => In j o) (w1 ++ w2) ->
      feqV (fr (w1 ++ w2) h) h -> feqV (fr w1 h) h.
    Proof.
      intros h Hh w1 w2 Hw Hc. pose proof (rb_eff_bound (w1 ++ w2) h Hh Hw) as A.
      rewrite (rb_pot_ext o _ _ Hc), rb_eff_app in A. apply rb_eff_zero. lia.
    Qed.
  End Eff.
End Robert.

(* ============================================================================================ *)
(* Part 2. Events: finitely many events, then (or interleaved with) fair propagation.           *)
(* ============================================================================================ *)

Section Events.
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
  Hypothesis HC : Common V src f valid rho E reg sig o.

  Local Notation feqV := (feq V).
  Local Notation InvV := (Inv V valid).
  Local Notation dr := (drun V f E reg sig).
  Local Notation okA := (okact E o).

  Lemma rb_drun_inv : forall w s, InvV s -> InvV (dr w s).
  Proof.
    induction w as [| a w IH]; intros s Hs; [exact Hs |]. simpl. apply IH.
    exact (dstep_inv _ _ _ _ _ _ _ _ _ HC a s Hs).
  Qed.

  Lemma rb_ev_fair : forall sg, Fair o sg -> forall h, InvV h -> RSettles V f sg h (frun V f o h).
  Proof.
    intros sg Hf h Hh.
    exact (rb_robert_fair V src f valid o (c_local _ _ _ _ _ _ _ _ _ HC) (c_topo _ _ _ _ _ _ _ _ _ HC)
      (c_m1 _ _ _ _ _ _ _ _ _ HC) (c_absorb _ _ _ _ _ _ _ _ _ HC) sg Hf h Hh).
  Qed.

  (* Events, then any fair propagation schedule: the FedMachine run of the events. *)
  Theorem rb_events : XU V f valid E reg sig -> forall w s, InvV s -> Forall okA w ->
    forall sg, Fair o sg -> RSettles V f sg (dr w s) (runF V f rho E reg sig o (evs E w) (N V f rho o s)).
  Proof.
    intros HX w s Hs Hw sg Hf.
    assert (Hd : InvV (dr w s)) by exact (rb_drun_inv w s Hs).
    apply (rb_settles_feq V f sg _ (frun V f o (dr w s))); [exact (rb_ev_fair sg Hf _ Hd) |].
    apply (rb_feq_trans V _ (N V f rho o (dr w s))).
    - apply rb_feq_sym. exact (N_frun _ _ _ _ _ _ _ _ _ HC _ Hd).
    - exact (propagation_flush _ _ _ _ _ _ _ _ _ HC HX w s Hs Hw).
  Qed.

  (* An infinite schedule of events and propagation steps: finitely many events, and every target
     propagates infinitely often. *)
  Fixpoint rb_arun (a : nat -> act E) (n : nat) (s : nat -> V) : nat -> V :=
    match n with 0 => s | S m => dstep V f E reg sig (a m) (rb_arun a m s) end.

  Definition RFairEv (a : nat -> act E) : Prop :=
    (forall n, okA (a n)) /\ (exists T, forall n, T <= n -> exists j, a n = DProp E j) /\
    (forall j m, In j o -> exists n, m <= n /\ a n = DProp E j).

  Lemma rb_arun_drun : forall a n s, rb_arun a n s = dr (map a (seq 0 n)) s.
  Proof.
    intros a n s. induction n as [| n IH]; [reflexivity |].
    rewrite lfs_seq_snoc, map_app, drun_app. simpl. rewrite IH. reflexivity.
  Qed.

  Theorem rb_event_schedule : XU V f valid E reg sig -> forall a, RFairEv a -> forall s, InvV s ->
    exists T, (forall n, T <= n -> exists j, a n = DProp E j) /\
      exists M, forall n, M <= n ->
        feqV (rb_arun a n s) (runF V f rho E reg sig o (evs E (map a (seq 0 T))) (N V f rho o s)).
  Proof.
    intros HX a [Hok [[T HT] Hinf]] s Hs. exists T. split; [exact HT |].
    set (sg := fun k => match a (T + k) with DProp _ j => j | DEv _ _ => 0 end).
    assert (Ha : forall k, a (T + k) = DProp E (sg k)).
    { intros k. unfold sg. destruct (HT (T + k) ltac:(lia)) as [j Ej]. rewrite Ej. reflexivity. }
    assert (Hfair : Fair o sg).
    { split.
      - intros k. pose proof (Hok (T + k)) as Ok. rewrite Ha in Ok. exact Ok.
      - intros j m Hj. destruct (Hinf j (T + m) Hj) as [n [Hn En]]. exists (n - T). split; [lia |].
        pose proof (Ha (n - T)) as Ek. replace (T + (n - T)) with n in Ek by lia.
        rewrite En in Ek. injection Ek as Ek. symmetry. exact Ek. }
    assert (Hsplit : forall k, rb_arun a (T + k) s = rb_run V f sg k (rb_arun a T s)).
    { induction k as [| k IH]; [rewrite Nat.add_0_r; reflexivity |].
      rewrite Nat.add_succ_r. cbn [rb_arun]. rewrite IH, (Ha k). reflexivity. }
    assert (Hw : Forall okA (map a (seq 0 T))).
    { apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [n [<- _]]. apply Hok. }
    destruct (rb_events HX (map a (seq 0 T)) s Hs Hw sg Hfair) as [M HM].
    exists (T + M). intros n Hn. replace n with (T + (n - T)) by lia.
    rewrite Hsplit, rb_arun_drun. apply HM. lia.
  Qed.

  (* Convergence of fair schedules with finitely many events: limits of words with trace-equivalent
     events agree. *)
  Definition RFairConv (s0 : nat -> V) : Prop :=
    forall w1 w2 sg1 sg2 q1 q2, Forall okA w1 -> Forall okA w2 ->
      tequiv (Ifed E reg I) (evs E w1) (evs E w2) -> Fair o sg1 -> Fair o sg2 ->
      RSettles V f sg1 (dr w1 s0) q1 -> RSettles V f sg2 (dr w2 s0) q2 -> feqV q1 q2.

  Lemma rb_fair_conv_iff : o <> [] -> forall s0, InvV s0 ->
    (RFairConv s0 <-> DistConv V f rho E reg sig I o s0).
  Proof.
    intros Hne s0 Hi.
    assert (Lim : forall w sg q, Fair o sg -> RSettles V f sg (dr w s0) q -> feqV q (N V f rho o (dr w s0))).
    { intros w sg q Hf Hq. assert (Hd : InvV (dr w s0)) by exact (rb_drun_inv w s0 Hi).
      apply (rb_feq_trans V _ (frun V f o (dr w s0))).
      - exact (rb_settles_unique V f sg _ q _ Hq (rb_ev_fair sg Hf _ Hd)).
      - apply rb_feq_sym. exact (N_frun _ _ _ _ _ _ _ _ _ HC _ Hd). }
    split.
    - intros H w1 w2 Hw1 Hw2 Ht.
      pose proof (rrs_fair o Hne) as Hf.
      pose proof (rb_ev_fair (rrs o) Hf _ (rb_drun_inv w1 s0 Hi)) as S1.
      pose proof (rb_ev_fair (rrs o) Hf _ (rb_drun_inv w2 s0 Hi)) as S2.
      pose proof (H w1 w2 _ _ _ _ Hw1 Hw2 Ht Hf Hf S1 S2) as Q.
      apply (rb_feq_trans V _ _ _ (rb_feq_sym V _ _ (Lim w1 _ _ Hf S1))).
      apply (rb_feq_trans V _ _ _ Q). exact (Lim w2 _ _ Hf S2).
    - intros H w1 w2 sg1 sg2 q1 q2 Hw1 Hw2 Ht Hf1 Hf2 S1 S2.
      apply (rb_feq_trans V _ _ _ (Lim w1 _ _ Hf1 S1)).
      apply (rb_feq_trans V _ _ _ (H w1 w2 Hw1 Hw2 Ht)). apply rb_feq_sym. exact (Lim w2 _ _ Hf2 S2).
  Qed.

  (* The exact condition for fair schedules with finitely many events: dist_exact's. *)
  Theorem rb_fair_dist_exact : o <> [] -> forall s0, InvV s0 ->
    (RFairConv s0 <-> XUR V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o (N V f rho o s0)).
  Proof.
    intros Hne s0 Hi. rewrite (rb_fair_conv_iff Hne s0 Hi). exact (dist_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi).
  Qed.
End Events.

(* ============================================================================================ *)
(* Part 3. The resolver (lens) model and the Boolean form.                                      *)
(* ============================================================================================ *)

Section Lens.
  Variables (X Sh : Type).
  Variable js : list nat.
  Variable get : nat -> Sh -> X.
  Variable set : nat -> X -> Sh -> Sh.
  Hypothesis get_set_eq : forall j x s, In j js -> get j (set j x s) = x.
  Hypothesis get_set_neq : forall j k x s, k <> j -> get k (set j x s) = get k s.
  Hypothesis sh_ext : forall s t, (forall j, In j js -> get j s = get j t) -> s = t.
  Variable Fv : nat -> Sh -> X.
  Variable src : nat -> list nat.
  Variable o : list nat.
  Hypothesis o_js : forall j, In j o <-> In j js.
  Hypothesis o_topo : topoF src o.
  Hypothesis src_js : forall j k, In k (src j) -> In k js.
  (* Each resolver reads only its sources: src is (a supergraph of) the global interaction graph. *)
  Hypothesis reads : forall j, In j js -> forall s t, (forall k, In k (src j) -> get k s = get k t) ->
    Fv j s = Fv j t.
  Variable z0 : Sh.

  Local Notation ru := (rupd X Sh js set Fv).

  Definition rb_obs (s : Sh) : nat -> X := fun k => get k s.
  Definition rb_lf (j : nat) (z : nat -> X) (x : X) : X :=
    if in_dec Nat.eq_dec j js then Fv j (setl X Sh set js z z0) else x.
  Definition rb_lvalid (_ : nat) (_ : X) : Prop := True.

  Lemma rb_setl_get : forall z a k, In k js -> get k (setl X Sh set js z a) = z k.
  Proof. intros z a k Hk. exact (get_setl_in X Sh js get set get_set_eq get_set_neq js z a k (fun j H => H) Hk). Qed.

  Lemma rb_setl_obs : forall s, setl X Sh set js (rb_obs s) z0 = s.
  Proof. intros s. apply sh_ext. intros k Hk. rewrite rb_setl_get by exact Hk. reflexivity. Qed.

  Lemma rb_lf_obs : forall j s x, In j js -> rb_lf j (rb_obs s) x = Fv j s.
  Proof.
    intros j s x Hj. unfold rb_lf. destruct (in_dec Nat.eq_dec j js) as [_ | N]; [| contradiction].
    rewrite rb_setl_obs. reflexivity.
  Qed.

  Lemma rb_lf_in : forall j z x, In j js -> rb_lf j z x = Fv j (setl X Sh set js z z0).
  Proof.
    intros j z x Hj. unfold rb_lf. destruct (in_dec Nat.eq_dec j js) as [_ | N]; [reflexivity | contradiction].
  Qed.

  Lemma rb_lf_loc : forall j z1 z2 x, (forall k, In k (src j) -> z1 k = z2 k) -> rb_lf j z1 x = rb_lf j z2 x.
  Proof.
    intros j z1 z2 x H. unfold rb_lf. destruct (in_dec Nat.eq_dec j js) as [Hj | _]; [| reflexivity].
    apply reads; [exact Hj |]. intros k Hk. rewrite !rb_setl_get by exact (src_js j k Hk). exact (H k Hk).
  Qed.

  Lemma rb_lf_m1 : forall j z x, Inv X rb_lvalid z -> rb_lvalid j x -> rb_lvalid j (rb_lf j z x).
  Proof. intros. exact I. Qed.

  Lemma rb_lf_abs : forall j z z' x, Inv X rb_lvalid z -> Inv X rb_lvalid z' -> rb_lvalid j x ->
    rb_lf j z (rb_lf j z' x) = rb_lf j z x.
  Proof. intros j z z' x _ _ _. unfold rb_lf. destruct (in_dec Nat.eq_dec j js); reflexivity. Qed.

  Lemma rb_linv : forall z, Inv X rb_lvalid z.
  Proof. intros z k. exact I. Qed.

  Lemma rb_lcommon : Common X src rb_lf rb_lvalid rb_idr Empty_set rb_noreg rb_nosig o.
  Proof. exact (rb_common X src rb_lf rb_lvalid o rb_lf_loc o_topo rb_lf_m1 rb_lf_abs). Qed.

  (* The resolver step, read through the lens, is the distributed propagation step. *)
  Lemma rb_obs_step : forall j s, feq X (rb_obs (ru j s)) (fstep X rb_lf (rb_obs s) j).
  Proof.
    intros j s k. rewrite rb_fstep_at. unfold rb_obs, rupd.
    destruct (in_dec Nat.eq_dec j js) as [Hj | Hj].
    - destruct (Nat.eqb_spec k j) as [-> | N].
      + rewrite get_set_eq by exact Hj. symmetry. exact (rb_lf_obs j s _ Hj).
      + exact (get_set_neq j k _ s N).
    - destruct (Nat.eqb_spec k j) as [-> | _]; [| reflexivity].
      unfold rb_lf. destruct (in_dec Nat.eq_dec j js); [contradiction | reflexivity].
  Qed.

  Lemma rb_obs_run : forall sg n s, feq X (rb_obs (prs Sh ru sg n s)) (rb_run X rb_lf sg n (rb_obs s)).
  Proof.
    intros sg n s. induction n as [| n IH]; [intro k; reflexivity |].
    change (prs Sh ru sg (S n) s) with (ru (sg n) (prs Sh ru sg n s)). rewrite rb_run_S.
    apply (rb_feq_trans X _ _ _ (rb_obs_step (sg n) _)).
    exact (rb_step_ext X src rb_lf rb_lf_loc (sg n) _ _ IH).
  Qed.

  Lemma rb_obs_xr : forall w s, feq X (rb_obs (xr X Sh js set Fv w s)) (frun X rb_lf w (rb_obs s)).
  Proof.
    induction w as [| a w IH]; intros s; [intro k; reflexivity |].
    change (xr X Sh js set Fv (a :: w) s) with (xr X Sh js set Fv w (ru a s)). rewrite rb_frun_cons.
    apply (rb_feq_trans X _ _ _ (IH (ru a s))).
    exact (frun_ext _ _ _ _ _ _ _ _ _ rb_lcommon w _ _ (rb_obs_step a s)).
  Qed.

  (* The candidate fixed point built from the run of the topological order. *)
  Definition rb_lq (s : Sh) : Sh := setl X Sh set js (frun X rb_lf o (rb_obs s)) s.

  Lemma rb_fv_setl : forall k z a b, In k js -> Fv k (setl X Sh set js z a) = Fv k (setl X Sh set js z b).
  Proof.
    intros k z a b Hk. apply reads; [exact Hk |]. intros i Hi. rewrite !rb_setl_get by exact (src_js k i Hi).
    reflexivity.
  Qed.

  Lemma rb_lq_fixed : forall s, Fsync X Sh js set Fv (rb_lq s) = rb_lq s.
  Proof.
    intros s. apply sh_ext. intros k Hk. rewrite (get_Fsync X Sh js get set get_set_eq get_set_neq) by exact Hk.
    unfold rb_lq. rewrite rb_setl_get by exact Hk.
    rewrite (rb_q_solves X src rb_lf rb_lvalid o rb_lf_loc o_topo rb_lf_m1 rb_lf_abs (rb_obs s) k
               (proj2 (o_js k) Hk)).
    rewrite rb_lf_in by exact Hk. apply rb_fv_setl. exact Hk.
  Qed.

  Lemma rb_fixed_get : forall p, Fsync X Sh js set Fv p = p -> forall j, In j js -> get j p = Fv j p.
  Proof.
    intros p Hp j Hj. rewrite <- (get_Fsync X Sh js get set get_set_eq get_set_neq Fv p j Hj), Hp. reflexivity.
  Qed.

  (* Two fixed points agree, along the topological order. *)
  Theorem rb_lens_unique : forall p p', Fsync X Sh js set Fv p = p -> Fsync X Sh js set Fv p' = p' -> p = p'.
  Proof.
    intros p p' Hp Hp'.
    assert (G : forall pre, (exists suf, o = pre ++ suf) -> forall j, In j pre -> get j p = get j p').
    { apply (List.rev_ind (fun pre => (exists suf, o = pre ++ suf) -> forall j, In j pre -> get j p = get j p')).
      { intros _ j []. }
      intros a pre IH [suf Hsuf] j Hj.
      assert (Ho : o = pre ++ a :: suf) by (rewrite Hsuf, <- app_assoc; reflexivity).
      assert (IH' : forall k, In k pre -> get k p = get k p') by (apply IH; exists (a :: suf); exact Ho).
      apply in_app_or in Hj. destruct Hj as [Hj | [<- | []]]; [exact (IH' j Hj) |].
      assert (Ha : In a js) by (apply o_js; rewrite Ho; apply in_or_app; right; left; reflexivity).
      rewrite (rb_fixed_get p Hp a Ha), (rb_fixed_get p' Hp' a Ha). apply reads; [exact Ha |].
      intros k Hk. apply IH'. apply (rb_topo_src src pre a suf); [rewrite <- Ho; exact o_topo | exact Hk |].
      rewrite <- Ho. apply o_js. exact (src_js a k Hk). }
    apply sh_ext. intros j Hj. apply (G o); [exists []; rewrite app_nil_r; reflexivity | apply o_js; exact Hj].
  Qed.

  (* Robert's theorem in the resolver model: a unique fixed point, reached by every fair schedule
     from every start. *)
  Theorem rb_lens_robert :
    Fsync X Sh js set Fv (rb_lq z0) = rb_lq z0 /\
    (forall p, Fsync X Sh js set Fv p = p -> p = rb_lq z0) /\
    (forall sg, Fair js sg -> forall h0, Settles Sh ru sg h0 (rb_lq z0)).
  Proof.
    split; [apply rb_lq_fixed |]. split; [intros p Hp; exact (rb_lens_unique p _ Hp (rb_lq_fixed z0)) |].
    intros sg Hf h0.
    assert (Hfo : Fair o sg) by (apply (fair_same js o sg Hf); intro j; symmetry; apply o_js).
    destruct (rb_robert_fair X src rb_lf rb_lvalid o rb_lf_loc o_topo rb_lf_m1 rb_lf_abs sg Hfo (rb_obs h0)
                (rb_linv _)) as [M HM].
    exists M. intros n Hn. rewrite <- (rb_lens_unique (rb_lq h0) (rb_lq z0) (rb_lq_fixed h0) (rb_lq_fixed z0)).
    apply sh_ext. intros k Hk. unfold rb_lq. rewrite rb_setl_get by exact Hk.
    change (get k (prs Sh ru sg n h0)) with (rb_obs (prs Sh ru sg n h0) k).
    rewrite (rb_obs_run sg n h0 k). exact (HM n Hn k).
  Qed.

  Lemma rb_xr_filter : forall w s, xr X Sh js set Fv w s =
    xr X Sh js set Fv (filter (fun j => if in_dec Nat.eq_dec j js then true else false) w) s.
  Proof.
    induction w as [| a w IH]; intros s; [reflexivity |]. cbn [filter].
    change (xr X Sh js set Fv (a :: w) s) with (xr X Sh js set Fv w (ru a s)).
    destruct (in_dec Nat.eq_dec a js) as [Ha | Ha].
    - change (xr X Sh js set Fv (a :: filter (fun j => if in_dec Nat.eq_dec j js then true else false) w) s)
        with (xr X Sh js set Fv (filter (fun j => if in_dec Nat.eq_dec j js then true else false) w) (ru a s)).
      apply IH.
    - rewrite (rupd_out X Sh js set Fv a s Ha). apply IH.
  Qed.

  Lemma rb_filter_app : forall (p : nat -> bool) (l1 l2 : list nat), filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
  Proof.
    intros p. induction l1 as [| a l1 IH]; intros l2; [reflexivity |]. cbn [app filter].
    rewrite IH. destruct (p a); reflexivity.
  Qed.

  (* With decidable values, no closed asynchronous run changes the state. *)
  Theorem rb_lens_closed : (forall a b : X, {a = b} + {a <> b}) ->
    forall x w1 w2, xr X Sh js set Fv (w1 ++ w2) x = x -> xr X Sh js set Fv w1 x = x.
  Proof.
    intros Xd x w1 w2 Hc.
    set (p := fun j => if in_dec Nat.eq_dec j js then true else false).
    rewrite rb_xr_filter. fold p. rewrite rb_xr_filter, rb_filter_app in Hc. fold p in Hc.
    assert (Hw : Forall (fun j => In j o) (filter p w1 ++ filter p w2)).
    { apply Forall_forall. intros j Hj. rewrite <- rb_filter_app in Hj. apply filter_In in Hj.
      destruct Hj as [_ Hj]. unfold p in Hj. destruct (in_dec Nat.eq_dec j js) as [H | _]; [| discriminate Hj].
      apply o_js. exact H. }
    assert (Hcl : feq X (frun X rb_lf (filter p w1 ++ filter p w2) (rb_obs x)) (rb_obs x)).
    { apply (rb_feq_trans X _ _ _ (rb_feq_sym X _ _ (rb_obs_xr _ x))). rewrite Hc. intro k. reflexivity. }
    pose proof (rb_closed X src rb_lf rb_lvalid o rb_lf_loc o_topo rb_lf_m1 rb_lf_abs Xd (rb_obs x) (rb_linv _)
                  _ _ Hw Hcl) as R.
    apply sh_ext. intros k _. change (get k (xr X Sh js set Fv (filter p w1) x)) with
      (rb_obs (xr X Sh js set Fv (filter p w1) x) k).
    rewrite (rb_obs_xr _ x k). exact (R k).
  Qed.
End Lens.

(* ----- Boolean networks: the global interaction graph ----- *)

(* The global interaction graph G(F) of a Boolean network on n vertices: j -> i when flipping x_j
   changes F_i at some state. *)
Definition rb_garc (n : nat) (Fv : nat -> BV n -> bool) (j i : nat) : bool :=
  existsb (fun x => larc (BV n) (bget n) (bset n) Fv x j i) (benum n).
Definition rb_gsrc (n : nat) (Fv : nat -> BV n -> bool) (i : nat) : list nat :=
  filter (fun j => rb_garc n Fv j i) (seq 0 n).

Lemma rb_garc_local : forall n Fv x j i, larc (BV n) (bget n) (bset n) Fv x j i = true -> rb_garc n Fv j i = true.
Proof. intros n Fv x j i H. apply existsb_exists. exists x. split; [apply benum_all | exact H]. Qed.

Lemma rb_garc_false : forall n Fv j i, rb_garc n Fv j i = false -> forall x, larc (BV n) (bget n) (bset n) Fv x j i = false.
Proof.
  intros n Fv j i H x. destruct (larc (BV n) (bget n) (bset n) Fv x j i) eqn:E; [| reflexivity].
  rewrite (rb_garc_local n Fv x j i E) in H. discriminate H.
Qed.

Lemma rb_cyc_ok_mono : forall (a1 a2 : nat -> nat -> bool) c, (forall u v, a1 u v = true -> a2 u v = true) ->
  cyc_ok a1 c = true -> cyc_ok a2 c = true.
Proof.
  intros a1 a2 c H H1. unfold cyc_ok in *. rewrite forallb_forall in *. intros p Hp. apply H. exact (H1 p Hp).
Qed.

(* No cycle in G(F) gives no cycle in any local graph G(F)(x). *)
Theorem rb_global_local : forall n Fv, (forall c, incl c (seq 0 n) -> ~ IsCycle (rb_garc n Fv) c) ->
  NoLocalCycle (BV n) (bget n) (bset n) Fv (seq 0 n).
Proof.
  intros n Fv H x c Hc [Hne [Hnd Hok]]. apply (H c Hc). split; [exact Hne | split; [exact Hnd |]].
  apply (rb_cyc_ok_mono (larc (BV n) (bget n) (bset n) Fv x)); [| exact Hok].
  intros u v. apply rb_garc_local.
Qed.

(* A Boolean resolver reads only its in-neighbors in G(F). *)
Lemma rb_reads_walk : forall n Fv i l s t,
  (forall j, In j (seq 0 n) -> ~ In j l -> bget n j s = bget n j t) ->
  (forall j, In j l -> rb_garc n Fv j i = false) -> Fv i s = Fv i t.
Proof.
  intros n Fv i. induction l as [| a l IH]; intros s t Hag Hl.
  - f_equal. apply bext. intros j Hj. exact (Hag j Hj (fun H => H)).
  - destruct (in_dec Nat.eq_dec a (seq 0 n)) as [Ha | Ha].
    + set (s' := bset n a (bget n a t) s).
      assert (Hs' : Fv i s' = Fv i t).
      { apply IH; [| intros j Hj; apply Hl; right; exact Hj].
        intros j Hj Hn. unfold s'. destruct (Nat.eq_dec j a) as [-> | N].
        - apply bget_bset_eq. exact Ha.
        - rewrite (bget_bset_neq n a j _ s N). apply Hag; [exact Hj |]. intros [E | E]; [congruence | contradiction]. }
      rewrite <- Hs'. unfold s'.
      destruct (Bool.bool_dec (bget n a s) (bget n a t)) as [E | N].
      * rewrite <- E. f_equal. apply bext. intros k Hk. destruct (Nat.eq_dec k a) as [-> | Nk].
        -- rewrite bget_bset_eq by exact Ha. reflexivity.
        -- rewrite bget_bset_neq by exact Nk. reflexivity.
      * assert (Et : bget n a t = negb (bget n a s)) by (destruct (bget n a s), (bget n a t); simpl; congruence).
        rewrite Et. pose proof (rb_garc_false n Fv a i (Hl a (or_introl eq_refl)) s) as L.
        unfold larc, flip in L. destruct (Fv i (bset n a (negb (bget n a s)) s)), (Fv i s); simpl in L;
          congruence.
    + apply IH; [| intros j Hj; apply Hl; right; exact Hj].
      intros j Hj Hn. apply Hag; [exact Hj |]. intros [E | E]; [subst; contradiction | contradiction].
Qed.

Lemma rb_reads_bool : forall n Fv i s t, (forall k, In k (rb_gsrc n Fv i) -> bget n k s = bget n k t) ->
  Fv i s = Fv i t.
Proof.
  intros n Fv i s t H.
  apply (rb_reads_walk n Fv i (filter (fun j => negb (rb_garc n Fv j i)) (seq 0 n))).
  - intros j Hj Hn. apply H. unfold rb_gsrc. apply filter_In. split; [exact Hj |].
    destruct (rb_garc n Fv j i) eqn:G; [reflexivity |]. exfalso. apply Hn. apply filter_In.
    rewrite G. split; [exact Hj | reflexivity].
  - intros j Hj. apply filter_In in Hj. destruct Hj as [_ Hj]. destruct (rb_garc n Fv j i); [discriminate | reflexivity].
Qed.

(* An acyclic graph has a topological order of any vertex subset (remove a sink, recurse). *)
Lemma rb_topo_of_acyclic : forall (ar : nat -> nat -> bool) (Iv : list nat),
  (forall c, incl c Iv -> ~ IsCycle ar c) ->
  forall m J, length J <= m -> incl J Iv ->
  exists l, (forall j, In j l <-> In j J) /\ topoF (fun i => filter (fun j => ar j i) Iv) l.
Proof.
  intros ar Iv Hac. induction m as [| m IH]; intros J Hl Hi.
  - destruct J as [| a J]; [| simpl in Hl; lia]. exists []. split; [tauto | exact I].
  - destruct J as [| a J0]; [exists []; split; [tauto | exact I] |].
    set (J := a :: J0).
    destruct (cycle_or_sink ar J ltac:(discriminate)) as [[c [Hc Hcy]] | [k [Hk Hs]]].
    { exfalso. apply (Hac c); [intros u Hu; apply Hi; apply Hc; exact Hu | exact Hcy]. }
    destruct (IH (rm k J)) as [l [Hlj Ht]].
    { pose proof (rm_length k J Hk). simpl in Hl. unfold J in *. simpl length in *. lia. }
    { intros u Hu. apply rm_In in Hu. apply Hi. exact (proj1 Hu). }
    exists (l ++ [k]). split.
    + intros j. rewrite in_app_iff. split.
      * intros [Hj | [E | []]]; [apply Hlj in Hj; apply rm_In in Hj; exact (proj1 Hj) | subst; exact Hk].
      * intros Hj. destruct (Nat.eq_dec j k) as [-> | N]; [right; left; reflexivity |].
        left. apply Hlj. apply rm_In. split; [exact Hj | exact N].
    + apply rb_topo_snoc; [exact Ht | | |].
      * intro Hin. apply Hlj in Hin. apply rm_In in Hin. destruct Hin as [_ N]. apply N. reflexivity.
      * intros b Hb Hkb. apply filter_In in Hkb. destruct Hkb as [_ A].
        apply Hlj in Hb. apply rm_In in Hb. rewrite (Hs b (proj1 Hb)) in A. discriminate A.
      * intros Hkk. apply filter_In in Hkk. destruct Hkk as [_ A]. rewrite (Hs k Hk) in A. discriminate A.
Qed.

Fixpoint rb_bz (n : nat) : BV n := match n return BV n with O => tt | S m => (false, rb_bz m) end.

(* Robert's theorem for Boolean networks (Robert 1986; Richard 2019, Theorem 1): if the global
   interaction graph has no cycle, the asynchronous state graph is acyclic, there is a unique fixed
   point, and every fair schedule from every start settles at it. *)
Theorem rb_robert_boolean : forall n (Fv : nat -> BV n -> bool),
  (forall c, incl c (seq 0 n) -> ~ IsCycle (rb_garc n Fv) c) ->
  NoLocalCycle (BV n) (bget n) (bset n) Fv (seq 0 n) /\
  NoClosedChange (BV n) (seq 0 n) (bset n) Fv (fun _ => True) /\
  exists q, Fsync bool (BV n) (seq 0 n) (bset n) Fv q = q /\
    (forall p, Fsync bool (BV n) (seq 0 n) (bset n) Fv p = p -> p = q) /\
    (forall sch, Fair (seq 0 n) sch -> forall h0, Settles (BV n) (rupd bool (BV n) (seq 0 n) (bset n) Fv) sch h0 q).
Proof.
  intros n Fv Hac.
  destruct (rb_topo_of_acyclic (rb_garc n Fv) (seq 0 n) Hac (length (seq 0 n)) (seq 0 n) (le_n _) (incl_refl _))
    as [l [Hl Ht]].
  assert (Hsrc : forall j k, In k (rb_gsrc n Fv j) -> In k (seq 0 n))
    by (intros j k Hk; apply filter_In in Hk; exact (proj1 Hk)).
  assert (Hreads : forall j, In j (seq 0 n) -> forall s t, (forall k, In k (rb_gsrc n Fv j) -> bget n k s = bget n k t) ->
             Fv j s = Fv j t) by (intros j _ s t H; exact (rb_reads_bool n Fv j s t H)).
  assert (Hnl : NoLocalCycle (BV n) (bget n) (bset n) Fv (seq 0 n)) by exact (rb_global_local n Fv Hac).
  assert (Hnc : NoClosedChange (BV n) (seq 0 n) (bset n) Fv (fun _ => True)).
  { intros x w1 w2 _ Hw.
    exact (rb_lens_closed bool (BV n) (seq 0 n) (bget n) (bset n) (bget_bset_eq n) (bget_bset_neq n) (bext n)
             Fv (rb_gsrc n Fv) l Hl Ht Hsrc Hreads (rb_bz n) Bool.bool_dec x w1 w2 Hw). }
  destruct (rb_lens_robert bool (BV n) (seq 0 n) (bget n) (bset n) (bget_bset_eq n) (bget_bset_neq n) (bext n)
              Fv (rb_gsrc n Fv) l Hl Ht Hsrc Hreads (rb_bz n)) as [Hq _].
  split; [exact Hnl | split; [exact Hnc |]].
  exists (rb_lq bool (BV n) (seq 0 n) (bget n) (bset n) Fv l (rb_bz n) (rb_bz n)). split; [exact Hq |].
  exact (fair_settlement_of_acyclic (BV n) (seq 0 n) (bget n) (bset n) (bget_bset_eq n) (bget_bset_neq n) (bext n)
           Fv Hnl Hnc _ Hq).
Qed.

(* A sound decision procedure for "G(F) has no cycle" on small instances. *)
Definition rb_gacyclic_b (n : nat) (Fv : nat -> BV n -> bool) : bool :=
  forallb (fun c => match c with [] => true | _ => negb (cyc_ok (rb_garc n Fv) c) end) (nl n (seq 0 n)).

Lemma rb_gacyclic_sound : forall n Fv, rb_gacyclic_b n Fv = true ->
  forall c, incl c (seq 0 n) -> ~ IsCycle (rb_garc n Fv) c.
Proof.
  intros n Fv H c Hc [Hne [Hnd Hok]]. unfold rb_gacyclic_b in H. rewrite forallb_forall in H.
  assert (Hlen : length c <= n).
  { pose proof (NoDup_incl_length Hnd Hc) as L. rewrite lfs_len_seq in L. exact L. }
  pose proof (H c (nl_complete n (seq 0 n) c Hnd Hc Hlen)) as A.
  destruct c as [| a c]; [congruence |]. rewrite Hok in A. discriminate A.
Qed.

(* ============================================================================================ *)
(* Part 4. Boundaries: acyclicity cannot be dropped, and the converse fails.                    *)
(* ============================================================================================ *)

Definition rb_h01 : BV 2 := (false, (true, tt)).
Definition rb_ff : BV 2 := (false, (false, tt)).
Definition rb_tt : BV 2 := (true, (true, tt)).

Lemma rb_nodup01 : NoDup [0; 1].
Proof. constructor; [simpl; intros [H | []]; discriminate | constructor; [intros [] | constructor]]. Qed.

(* The negative 2-cycle x0 := not x1, x1 := x0. *)
Definition rb_nF (i : nat) (s : BV 2) : bool :=
  match i with 0 => negb (bget 2 1 s) | 1 => bget 2 0 s | _ => false end.

Theorem rb_neg2_cycle :
  IsCycle (rb_garc 2 rb_nF) [0; 1] /\
  (forall p, Fsync bool (BV 2) (seq 0 2) (bset 2) rb_nF p <> p) /\
  (forall sch, Fair (seq 0 2) sch -> forall h0 q, ~ Settles (BV 2) (rupd bool (BV 2) (seq 0 2) (bset 2) rb_nF) sch h0 q).
Proof.
  assert (Hn : forall p, Fsync bool (BV 2) (seq 0 2) (bset 2) rb_nF p <> p).
  { intros p H. apply bfixed_iff in H. destruct p as [a [b []]]. destruct a, b; vm_compute in H; discriminate H. }
  split; [split; [discriminate | split; [exact rb_nodup01 | vm_compute; reflexivity]] |].
  split; [exact Hn |]. intros sch Hf h0 q Hs.
  exact (Hn q (settles_fixed (BV 2) (seq 0 2) (bget 2) (bset 2) (bget_bset_eq 2) (bget_bset_neq 2) (bext 2)
                 rb_nF sch Hf h0 q Hs)).
Qed.

(* The positive 2-cycle x0 := x1, x1 := x0. *)
Definition rb_cF (i : nat) (s : BV 2) : bool :=
  match i with 0 => bget 2 1 s | 1 => bget 2 0 s | _ => false end.

Lemma rb_cF_fixed : forall q, q = rb_ff \/ q = rb_tt ->
  forall j, rupd bool (BV 2) (seq 0 2) (bset 2) rb_cF j q = q.
Proof.
  intros q Hq j. unfold rupd. destruct (in_dec Nat.eq_dec j (seq 0 2)) as [H | H]; [| reflexivity].
  simpl in H. destruct Hq as [-> | ->]; destruct H as [<- | [<- | []]]; vm_compute; reflexivity.
Qed.

Lemma rb_cF_settles : forall sch q, q = rb_ff \/ q = rb_tt ->
  prs (BV 2) (rupd bool (BV 2) (seq 0 2) (bset 2) rb_cF) sch 1 rb_h01 = q ->
  Settles (BV 2) (rupd bool (BV 2) (seq 0 2) (bset 2) rb_cF) sch rb_h01 q.
Proof.
  intros sch q Hq H1. exists 1. intros m Hm. replace m with (1 + (m - 1)) by lia.
  rewrite LocalSigned.prs_shift, H1. apply prs_fixed. exact (rb_cF_fixed q Hq).
Qed.

Theorem rb_copyback_cycle :
  IsCycle (rb_garc 2 rb_cF) [0; 1] /\
  Fsync bool (BV 2) (seq 0 2) (bset 2) rb_cF rb_ff = rb_ff /\
  Fsync bool (BV 2) (seq 0 2) (bset 2) rb_cF rb_tt = rb_tt /\ rb_ff <> rb_tt /\
  Fair (seq 0 2) (rrs [0; 1]) /\ Fair (seq 0 2) (rrs [1; 0]) /\
  Settles (BV 2) (rupd bool (BV 2) (seq 0 2) (bset 2) rb_cF) (rrs [0; 1]) rb_h01 rb_tt /\
  Settles (BV 2) (rupd bool (BV 2) (seq 0 2) (bset 2) rb_cF) (rrs [1; 0]) rb_h01 rb_ff.
Proof.
  split; [split; [discriminate | split; [exact rb_nodup01 | vm_compute; reflexivity]] |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [discriminate |].
  split; [exact (rrs_fair [0; 1] ltac:(discriminate)) |].
  split; [apply (fair_same [1; 0]); [exact (rrs_fair [1; 0] ltac:(discriminate)) | intro j; simpl; tauto] |].
  split; apply rb_cF_settles; [right; reflexivity | vm_compute; reflexivity | left; reflexivity | vm_compute; reflexivity].
Qed.

(* The converse of Robert's theorem fails: Shih and Ho's network has the cycle 0 -> 3 -> 0 in its
   global interaction graph, and every fair schedule from every start settles at its unique fixed
   point. *)
Theorem rb_converse_fails :
  IsCycle (rb_garc 4 sh_F) [0; 3] /\
  Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F sh_q = sh_q /\
  (forall p, Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F p = p -> p = sh_q) /\
  (forall sch, Fair (seq 0 4) sch -> forall h0, Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sh_F) sch h0 sh_q).
Proof.
  destruct shih_ho_instance as (_ & _ & _ & _ & _ & _ & Hq & Hu & Hs & _).
  split; [| exact (conj Hq (conj Hu Hs))].
  split; [discriminate | split; [| vm_compute; reflexivity]].
  constructor; [simpl; intros [H | []]; discriminate | constructor; [intros [] | constructor]].
Qed.

(* In the distributed model: a negation loop satisfies every hypothesis but acyclicity. *)
Definition rb_nsrc (k : nat) : list nat := match k with 0 => [1] | 1 => [0] | _ => [] end.
Definition rb_nf (j : nat) (z : nat -> bool) (x : bool) : bool :=
  match j with 0 => negb (z 1) | 1 => z 0 | _ => x end.

Theorem rb_dist_cycle_needed :
  (forall j z1 z2 x, (forall k, In k (rb_nsrc j) -> z1 k = z2 k) -> rb_nf j z1 x = rb_nf j z2 x) /\
  (forall j z z' x, rb_nf j z (rb_nf j z' x) = rb_nf j z x) /\
  (forall l, In 0 l -> In 1 l -> ~ topoF rb_nsrc l) /\
  Fair [0; 1] (rrs [0; 1]) /\
  (forall sg, Fair [0; 1] sg -> forall h q, ~ RSettles bool rb_nf sg h q).
Proof.
  assert (Hl : forall j z1 z2 x, (forall k, In k (rb_nsrc j) -> z1 k = z2 k) -> rb_nf j z1 x = rb_nf j z2 x).
  { intros [| [| j]] z1 z2 x H; simpl.
    - rewrite (H 1 (or_introl eq_refl)). reflexivity.
    - exact (H 0 (or_introl eq_refl)).
    - reflexivity. }
  split; [exact Hl |]. split; [intros [| [| j]] z z' x; reflexivity |].
  split.
  { intros l H0 H1 Ht.
    pose proof (rb_idx_topo rb_nsrc l Ht 0 1 H0 (or_introl eq_refl) H1).
    pose proof (rb_idx_topo rb_nsrc l Ht 1 0 H1 (or_introl eq_refl) H0). lia. }
  split; [exact (rrs_fair [0; 1] ltac:(discriminate)) |].
  intros sg Hf h q Hs. pose proof (rb_settles_quiet bool rb_nsrc rb_nf [0; 1] Hl sg Hf h q Hs) as Q.
  pose proof (Q 0 (or_introl eq_refl)) as Q0. pose proof (Q 1 (or_intror (or_introl eq_refl))) as Q1.
  simpl in Q0, Q1. rewrite <- Q1 in Q0. destruct (q 0); discriminate Q0.
Qed.

(* A counter satisfies every hypothesis but absorption. *)
Definition rb_cf (j : nat) (z : nat -> nat) (x : nat) : nat := S x.

Theorem rb_absorb_needed :
  (forall j z1 z2 x, (forall k, In k ((fun _ => []) j) -> z1 k = z2 k) -> rb_cf j z1 x = rb_cf j z2 x) /\
  topoF (fun _ => []) [0] /\
  rb_cf 0 (fun _ => 0) (rb_cf 0 (fun _ => 0) 0) <> rb_cf 0 (fun _ => 0) 0 /\
  (forall sg, Fair [0] sg -> forall h q, ~ RSettles nat rb_cf sg h q).
Proof.
  assert (Hl : forall j z1 z2 x, (forall k, In k ((fun _ : nat => @nil nat) j) -> z1 k = z2 k) ->
                 rb_cf j z1 x = rb_cf j z2 x) by reflexivity.
  split; [exact Hl |]. split; [simpl; split; [intros [] | split; [intros k [] | exact I]] |].
  split; [discriminate |].
  intros sg Hf h q Hs. pose proof (rb_settles_quiet nat (fun _ => []) rb_cf [0] Hl sg Hf h q Hs 0 (or_introl eq_refl)) as Q.
  unfold rb_cf in Q. lia.
Qed.

(* ============================================================================================ *)
(* Part 5. Non-vacuity.                                                                          *)
(* ============================================================================================ *)

Definition rb_true {V : Type} (_ : nat) (_ : V) : Prop := True.

Lemma rb_ex_abs : forall j z z' x, FederationOrder.ex_f j z (FederationOrder.ex_f j z' x) = FederationOrder.ex_f j z x.
Proof. intros [| [| [| j]]] z z' x; reflexivity. Qed.

Lemma rb_ex_topo012 : topoF FederationOrder.ex_src [0; 1; 2].
Proof.
  simpl. repeat split; intros; simpl in *; intuition congruence.
Qed.

Lemma rb_ex_topo102 : topoF FederationOrder.ex_src [1; 0; 2].
Proof.
  simpl. repeat split; intros; simpl in *; intuition congruence.
Qed.

Definition rb_ex_lv (j : nat) : nat := match j with 2 => 1 | _ => 0 end.

(* FederationOrder.v's three registries (registry 2 reads 0 and 1): every fair schedule from every
   start settles at the state with 12 at registry 2, within 2 rounds (the depth levels) where the
   position bound gives 3; both topological orders reach it; fewer than 8 steps of any
   propagation word change the state. *)
Theorem rb_example :
  (forall sg, Fair [0; 1; 2] sg -> forall h,
     RSettles nat FederationOrder.ex_f sg h (frun nat FederationOrder.ex_f [0; 1; 2] h)) /\
  (forall h, frun nat FederationOrder.ex_f [0; 1; 2] h 2 = 12) /\
  (forall h, feq nat (frun nat FederationOrder.ex_f [1; 0; 2] h) (frun nat FederationOrder.ex_f [0; 1; 2] h)) /\
  (forall sg, (forall n, In (sg n) [0; 1; 2]) -> forall T : nat -> nat, (forall i, T i <= T (S i)) ->
     (forall i, RCovers [0; 1; 2] sg (T i) (T (S i))) -> forall h m, T 2 <= m ->
     feq nat (rb_run nat FederationOrder.ex_f sg m h) (frun nat FederationOrder.ex_f [0; 1; 2] h)) /\
  (forall w h, Forall (fun j => In j [0; 1; 2]) w -> rb_eff nat FederationOrder.ex_f Nat.eq_dec w h < 8).
Proof.
  pose proof FederationOrder.ex_f_local as Hl.
  assert (Hm : forall j z x, Inv nat rb_true z -> rb_true j x -> rb_true j (FederationOrder.ex_f j z x))
    by (intros; exact I).
  assert (Ha : forall j z z' x, Inv nat rb_true z -> Inv nat rb_true z' -> rb_true j x ->
            FederationOrder.ex_f j z (FederationOrder.ex_f j z' x) = FederationOrder.ex_f j z x)
    by (intros; apply rb_ex_abs).
  assert (Hi : forall h : nat -> nat, Inv nat rb_true h) by (intros h k; exact I).
  split; [intros sg Hf h; exact (rb_robert_fair nat _ _ rb_true _ Hl rb_ex_topo012 Hm Ha sg Hf h (Hi h)) |].
  split; [intros h; reflexivity |].
  split.
  { intros h. apply (rb_topo_runs nat _ _ rb_true _ Hl rb_ex_topo012 Hm Ha); [exact rb_ex_topo102 | | exact (Hi h)].
    intro j. simpl. tauto. }
  split.
  { intros sg Hs T Hmono Hcov h m Hmm.
    refine (rb_rounds_all nat _ _ rb_true _ Hl rb_ex_topo012 Hm Ha sg Hs h (Hi h) rb_ex_lv T _ Hmono Hcov 2 _ m Hmm).
    - intros j k Hj Hk Hko. destruct Hj as [<- | [<- | [<- | []]]]; simpl in Hk; [destruct Hk | destruct Hk |].
      destruct Hk as [<- | [<- | []]]; simpl; lia.
    - intros j Hj. destruct Hj as [<- | [<- | [<- | []]]]; simpl; lia. }
  intros w h Hw. exact (rb_effective nat _ _ rb_true _ Hl rb_ex_topo012 Hm Ha Nat.eq_dec w h (Hi h) Hw).
Qed.

(* The supply federation with events (FederationEvents.supply_instance). *)
Theorem rb_supply_events : forall w s, Inv (bool * nat) sp_valid s -> Forall (okact FederationEvents.sev [0; 1]) w ->
  forall sg, Fair [0; 1] sg ->
  RSettles (bool * nat) sp_f sg (drun (bool * nat) sp_f FederationEvents.sev sp_reg sp_sig w s)
    (runF (bool * nat) sp_f sp_rho FederationEvents.sev sp_reg sp_sig [0; 1] (evs FederationEvents.sev w) (N (bool * nat) sp_f sp_rho [0; 1] s)).
Proof.
  intros w s Hs Hw sg Hf. destruct supply_instance as [HC [HX _]].
  exact (rb_events _ _ _ _ _ _ _ _ _ HC HX w s Hs Hw sg Hf).
Qed.

Theorem rb_supply_fair_conv : forall s0, Inv (bool * nat) sp_valid s0 ->
  RFairConv (bool * nat) sp_f FederationEvents.sev sp_reg sp_sig sp_I [0; 1] s0.
Proof.
  intros s0 Hi. destruct supply_instance as [HC _]. destruct (supply_dist_exact s0 Hi) as [A [B _]].
  exact (proj2 (rb_fair_dist_exact _ _ _ _ _ _ _ _ sp_I _ HC ltac:(discriminate) s0 Hi) (conj A B)).
Qed.

(* The exact condition fails on the federation of dist_strictly_stronger_than_fed. *)
Theorem rb_gg_not_fair_conv :
  ~ RFairConv (bool * bool) (FederationGRS.pf (bool * bool) bool bool snd pair src2 FederationGRS.gg_G)
      FederationGRS.gev FederationGRS.gg_reg
      (FederationGRS.gsig (bool * bool) FederationGRS.gg_rho FederationGRS.gev FederationGRS.gg_reg FederationGRS.gg_ap)
      (FederationGRS.Itot FederationGRS.gev) [0; 1] gg_start.
Proof.
  destruct dist_strictly_stronger_than_fed as (HC & _ & Hi & _ & Nx & _). intro H.
  apply Nx. exact (proj1 (proj1 (rb_fair_dist_exact _ _ _ _ _ _ _ _ _ _ HC ltac:(discriminate) gg_start Hi) H)).
Qed.

(* A Boolean network with an acyclic global graph: x0 := 1, x1 := not x0, x2 := x0 xor x1. *)
Definition rb_b3F (i : nat) (s : BV 3) : bool :=
  match i with
  | 0 => true
  | 1 => negb (bget 3 0 s)
  | 2 => xorb (bget 3 0 s) (bget 3 1 s)
  | _ => false
  end.
Definition rb_b3q : BV 3 := (true, (false, (true, tt))).

Theorem rb_bool3 :
  rb_garc 3 rb_b3F 0 1 = true /\ rb_garc 3 rb_b3F 0 2 = true /\ rb_garc 3 rb_b3F 1 2 = true /\
  (forall c, incl c (seq 0 3) -> ~ IsCycle (rb_garc 3 rb_b3F) c) /\
  NoClosedChange (BV 3) (seq 0 3) (bset 3) rb_b3F (fun _ => True) /\
  Fsync bool (BV 3) (seq 0 3) (bset 3) rb_b3F rb_b3q = rb_b3q /\
  (forall p, Fsync bool (BV 3) (seq 0 3) (bset 3) rb_b3F p = p -> p = rb_b3q) /\
  (forall sch, Fair (seq 0 3) sch -> forall h0, Settles (BV 3) (rupd bool (BV 3) (seq 0 3) (bset 3) rb_b3F) sch h0 rb_b3q).
Proof.
  assert (Hac : forall c, incl c (seq 0 3) -> ~ IsCycle (rb_garc 3 rb_b3F) c)
    by (apply rb_gacyclic_sound; vm_compute; reflexivity).
  destruct (rb_robert_boolean 3 rb_b3F Hac) as [_ [Hnc [q [Hq [Hu Hs]]]]].
  assert (Hq3 : Fsync bool (BV 3) (seq 0 3) (bset 3) rb_b3F rb_b3q = rb_b3q) by (vm_compute; reflexivity).
  assert (E : rb_b3q = q) by exact (Hu rb_b3q Hq3). subst q.
  split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]]].
  exact (conj Hac (conj Hnc (conj Hq3 (conj Hu Hs)))).
Qed.
