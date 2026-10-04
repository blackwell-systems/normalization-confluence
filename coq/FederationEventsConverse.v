(* FederationEventsConverse.v: C1 and C2 are EXACTLY the right check for event interleavings in
   an acyclic federation, once each is restricted to the witnesses a run can produce. Axiom-free.

   FederationEvents.v proves that C1 + C2 are sufficient (fed_interleavings_converge) and shows by
   two counterexamples that neither can be dropped. This file proves the general converse, in the
   strongest form that is true, for the same machine model (FedMachine.Apply sequences; acyclic,
   Common), from any valid morphism-consistent start s0 (any FedMachine state).

   1. The witness equations ARE runs (conv_c1_runs, conv_c2_runs). For a reachable state s, an
      event e on registry j and a sequence w of events on other registries, with z := runF w s:
        runF (e :: w) s j     = ow_z (sig e b)                 (b := s j, consistent with s)
        runF (w ++ [e]) s j   = ow_z (sig e (ow_z b))
      and the two sequences are trace-equivalent (e is swapped past each event of w). These are
      exactly the two sides of C1 at (e, z, z' := s, b). Likewise, for two events of j,
        runF [e1; e2] s j = ow_s (sig e2 (ow_s (sig e1 b))), the left side of C2 at (z := s, b).
      So every C1 or C2 failure at a witness realized by a reachable state is an observable
      divergence (conv_c1_diverge, conv_c2_diverge): the C1 pair differs by moving e past w
      (a chain of allowed swaps), the C2 pair by one allowed swap.

   2. The exact characterization. Write C1R1 s0 (C1 at reachable witnesses with ONE intervening
      event: s reachable from s0, a on another registry, z := applyF a s) and C2R s0 (C2 at
      (s, s j) for s reachable from s0). Then (fed_exact)
        all trace-equivalent sequences from s0 converge  <->  C1R1 s0 /\ C2R s0
      and the same holds with C1R s0 (any number of intervening events) in place of C1R1 s0
      (fed_exact_full), so one intervening event is already the general case. Pointwise:
      reach_commute_iff says two federated-independent events commute at a reachable state iff
      the C1 instances (different registries) or the C2 instance (same registry) hold there.

   3. The global condition of the cycles development, specialized to the acyclic machine:
      GCF s0 (independent events commute after full re-normalization at every state reachable
      from s0) is equivalent to convergence (acyclic_gc_iff) and is implied by static C1 + C2
      (static_c1_c2_gc). So the picture is
        C1 /\ C2  ->  C1R1 /\ C2R  <->  GCF  <->  all interleavings from s0 converge.

   4. Why the naive converse is false (naive_converse_fails). "C1 fails, hence some two
      interleavings diverge" does not hold: a federation can violate C1 while every interleaving
      from every valid consistent start converges, even though the failing witness's target state
      and source state are realized together by a valid consistent start. C1 quantifies over
      every pair of valid source states (z', z); a divergence needs the sources to MOVE from z'
      to z while the target holds b, and in the instance no source event changes the image the
      target reads. The exact converse therefore has to quantify over reachable witnesses, as in
      2. (For C2 the witness is a single pair (z, b); whenever some valid consistent state has
      sources z and target b, for example in a two-registry federation whose source has no
      repair, conv_c2_diverge applies with that state as the start.)

   Static C1 and C2 remain what gsm can check per edge without exploring runs; C1R1 and C2R are
   the same equations over reachable states, so they are the exact (and more expensive) check. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.FederationEvents.
Import ListNotations.

Section Conv.
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

  Local Notation feqF := (feq V).
  Local Notation InvF := (Inv V valid).
  Local Notation ConsF := (Cons V f o).
  Local Notation aF := (applyF V f rho E reg sig o).
  Local Notation rF := (runF V f rho E reg sig o).
  Local Notation nF := (N V f rho o).
  Local Notation frF := (frun V f).
  Local Notation evF := (evstep V E reg sig).
  Local Notation IfedF := (Ifed E reg I).

  (* C1 at a witness realized by a run: target state b := s j of a reachable s, the source
     states before (s) and after (z := applyF a s) one event a on another registry. *)
  Definition C1at (s : nat -> V) (e a : E) : Prop :=
    f (reg e) (aF a s) (sig e (f (reg e) (aF a s) (s (reg e)))) =
    f (reg e) (aF a s) (sig e (s (reg e))).

  (* C2 at the witness (z := s, b := s j) of a reachable s. *)
  Definition C2at (s : nat -> V) (e1 e2 : E) : Prop :=
    f (reg e1) s (sig e2 (f (reg e1) s (sig e1 (s (reg e1))))) =
    f (reg e1) s (sig e1 (f (reg e1) s (sig e2 (s (reg e1))))).

  (* Reachable-witness forms of C1 and C2, relative to a start s0. *)
  Definition C1R (s0 : nat -> V) : Prop :=
    forall p e w, Forall (fun a => reg a <> reg e) w ->
      f (reg e) (rF w (rF p s0)) (sig e (f (reg e) (rF w (rF p s0)) (rF p s0 (reg e)))) =
      f (reg e) (rF w (rF p s0)) (sig e (rF p s0 (reg e))).

  Definition C1R1 (s0 : nat -> V) : Prop :=
    forall p e a, reg a <> reg e -> C1at (rF p s0) e a.

  Definition C2R (s0 : nat -> V) : Prop :=
    forall p e1 e2, reg e1 = reg e2 -> I e1 e2 -> C2at (rF p s0) e1 e2.

  (* The global condition (as in FederationEventsCycles.v), for the acyclic machine. *)
  Definition GCF (s0 : nat -> V) : Prop :=
    forall p a b, IfedF a b ->
      feqF (aF b (aF a (rF p s0))) (aF a (aF b (rF p s0))).

  Definition TraceConv (s0 : nat -> V) : Prop :=
    forall es1 es2, tequiv IfedF es1 es2 -> feqF (rF es1 s0) (rF es2 s0).

  (* ---------------------------------------------------------------------------------- *)
  (* Trace-equivalence facts.                                                            *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma tequiv_app_l : forall p l1 l2, tequiv IfedF l1 l2 -> tequiv IfedF (p ++ l1) (p ++ l2).
  Proof.
    induction p as [| x p IH]; intros l1 l2 H; [exact H |].
    simpl. apply tequiv_cons. apply IH. exact H.
  Qed.

  Lemma tequiv_move : forall e w, Forall (fun a => reg a <> reg e) w ->
    tequiv IfedF (e :: w) (w ++ [e]).
  Proof.
    intros e w. induction w as [| a w IH]; intros Hw; [apply teq_refl |].
    inversion Hw as [| ? ? Ha Hw']; subst.
    apply (teq_trans _ _ (a :: e :: w)).
    - apply (teq_swap _ [] e a w). left. intro H. apply Ha. symmetry. exact H.
    - simpl. apply tequiv_cons. apply IH. exact Hw'.
  Qed.

  Section WithCommon.
  Hypothesis HC : Common V src f valid rho E reg sig o.

  (* ---------------------------------------------------------------------------------- *)
  (* Locality: an event on j changes nothing outside j and the registries after j.       *)
  (* ---------------------------------------------------------------------------------- *)

  Definition upL (L : list nat) (t t' : nat -> V) : Prop := forall k, ~ In k L -> t k = t' k.

  Lemma upL_feq : forall L t t', feqF t t' -> upL L t t'.
  Proof. intros L t t' H k _. apply H. Qed.

  Lemma upL_sym : forall L t t', upL L t t' -> upL L t' t.
  Proof. intros L t t' H k Hk. symmetry. apply H. exact Hk. Qed.

  Lemma upL_trans : forall L t u w, upL L t u -> upL L u w -> upL L t w.
  Proof. intros L t u w H1 H2 k Hk. rewrite (H1 k Hk). apply H2. exact Hk. Qed.

  Lemma topoF_app : forall l1 l2, topoF src (l1 ++ l2) ->
    topoF src l2 /\ (forall a, In a l1 -> ~ In a l2 /\ forall k, In k (src a) -> ~ In k l2).
  Proof.
    induction l1 as [| x l1 IH]; intros l2 H; simpl in H.
    - split; [exact H | intros a []].
    - destruct H as [Hx [Hs Hr]]. destruct (IH l2 Hr) as [T Hl]. split; [exact T |].
      intros a [<- | Ha].
      + split.
        * intro H'. apply Hx. apply in_or_app. right. exact H'.
        * intros k Hk Hk2. apply (Hs k Hk). right. apply in_or_app. right. exact Hk2.
      + apply Hl. exact Ha.
  Qed.

  Lemma split_at : forall j, In j o ->
    exists o1 L, o = o1 ++ L /\ In j L /\ (forall k, In k (src j) -> ~ In k L).
  Proof.
    intros j Hj. destruct (in_split j o Hj) as [o1 [o2 Ho]].
    exists o1, (j :: o2). split; [exact Ho |]. split; [left; reflexivity |].
    pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as T. rewrite Ho in T.
    destruct (topoF_app o1 (j :: o2) T) as [[_ [Hs _]] _]. exact Hs.
  Qed.

  Lemma frun_app : forall l1 l2 t, frF (l1 ++ l2) t = frF l2 (frF l1 t).
  Proof. intros. unfold frun. apply fold_left_app. Qed.

  Lemma frun_upL_pre : forall l L t t',
    (forall a, In a l -> ~ In a L /\ forall k, In k (src a) -> ~ In k L) ->
    upL L t t' -> upL L (frF l t) (frF l t').
  Proof.
    induction l as [| a l IH]; intros L t t' Hl H; [exact H |].
    change (frF (a :: l) t) with (frF l (fstep V f t a)).
    change (frF (a :: l) t') with (frF l (fstep V f t' a)).
    apply IH; [intros b Hb; apply Hl; right; exact Hb |].
    intros k Hk. unfold fstep, upd. destruct (Nat.eqb k a) eqn:Ek.
    - apply Nat.eqb_eq in Ek. subst k. rewrite (H a Hk).
      apply (c_local _ _ _ _ _ _ _ _ _ HC). intros m Hm. apply H.
      apply (proj2 (Hl a (or_introl eq_refl))). exact Hm.
    - apply H. exact Hk.
  Qed.

  Lemma frun_upL : forall o1 L t t', o = o1 ++ L -> upL L t t' -> upL L (frF o t) (frF o t').
  Proof.
    intros o1 L t t' Ho H. pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as T. rewrite Ho in T |- *.
    destruct (topoF_app o1 L T) as [_ Hl].
    intros k Hk. rewrite !frun_app. rewrite (frun_out _ _ L (frF o1 t) k Hk).
    rewrite (frun_out _ _ L (frF o1 t') k Hk).
    apply (frun_upL_pre o1 L t t' Hl H). exact Hk.
  Qed.

  Lemma N_upL : forall o1 L t t', o = o1 ++ L -> upL L t t' -> upL L (nF t) (nF t').
  Proof.
    intros o1 L t t' Ho H. unfold N. apply (frun_upL o1); [exact Ho |].
    intros k Hk. cbv beta. rewrite (H k Hk). reflexivity.
  Qed.

  Lemma evstep_upL : forall L e t t', upL L t t' -> upL L (evF e t) (evF e t').
  Proof.
    intros L e t t' H k Hk. unfold evstep, upd.
    destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply H; exact Hk].
    apply Nat.eqb_eq in Ek. subst k. rewrite (H _ Hk). reflexivity.
  Qed.

  Lemma evstep_upL_self : forall L e t, In (reg e) L -> upL L (evF e t) t.
  Proof.
    intros L e t He k Hk. unfold evstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| reflexivity].
    apply Nat.eqb_eq in Ek. subst k. contradiction.
  Qed.

  Lemma applyF_upL : forall o1 L e t t', o = o1 ++ L -> upL L t t' -> upL L (aF e t) (aF e t').
  Proof. intros. unfold applyF. apply (N_upL o1); [assumption |]. apply evstep_upL. assumption. Qed.

  Lemma runF_upL : forall o1 L w t t', o = o1 ++ L -> upL L t t' -> upL L (rF w t) (rF w t').
  Proof.
    intros o1 L w. induction w as [| a w IH]; intros t t' Ho H; [exact H |].
    change (rF (a :: w) t) with (rF w (aF a t)). change (rF (a :: w) t') with (rF w (aF a t')).
    apply IH; [exact Ho |]. apply (applyF_upL o1); assumption.
  Qed.

  Lemma f_upL : forall j L t t' x, (forall k, In k (src j) -> ~ In k L) -> upL L t t' ->
    f j t x = f j t' x.
  Proof.
    intros j L t t' x Hs H. apply (c_local _ _ _ _ _ _ _ _ _ HC).
    intros k Hk. apply H. apply Hs. exact Hk.
  Qed.

  Lemma f_feq : forall j t t' x, feqF t t' -> f j t x = f j t' x.
  Proof. intros. apply (c_local _ _ _ _ _ _ _ _ _ HC). intros. auto. Qed.

  Lemma Cons_frun : forall l t, ConsF t -> (forall a, In a l -> In a o) -> feqF (frF l t) t.
  Proof.
    induction l as [| a l IH]; intros t Hc Hl; [intro k; reflexivity |].
    change (frF (a :: l) t) with (frF l (fstep V f t a)).
    assert (Hs : feqF (fstep V f t a) t).
    { intro k. unfold fstep, upd. destruct (Nat.eqb k a) eqn:Ek; [| reflexivity].
      apply Nat.eqb_eq in Ek. subst k. symmetry. apply Hc. apply Hl. left. reflexivity. }
    eapply feq_trans; [apply (frun_ext _ _ _ _ _ _ _ _ _ HC); exact Hs |].
    apply IH; [exact Hc |]. intros b Hb. apply Hl. right. exact Hb.
  Qed.

  Lemma Cons_feq : forall t u, ConsF t -> feqF t u -> ConsF u.
  Proof.
    intros t u Hc H j Hj. rewrite <- (H j). rewrite (Hc j Hj) at 1.
    rewrite (f_feq j t u (t j) H). reflexivity.
  Qed.

  Lemma N_self : forall t, InvF t -> ConsF t -> feqF (nF t) t.
  Proof.
    intros t Hi Hc. eapply feq_trans; [apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact Hi |].
    apply Cons_frun; [exact Hc | auto].
  Qed.

  (* After an event on j from a consistent state, nothing outside j and its successors moved. *)
  Lemma applyF_upL_self : forall o1 L e s, o = o1 ++ L -> In (reg e) L -> InvF s -> ConsF s ->
    upL L (aF e s) s.
  Proof.
    intros o1 L e s Ho He Hi Hc. unfold applyF.
    eapply upL_trans; [apply (N_upL o1 L _ s Ho); apply evstep_upL_self; exact He |].
    apply upL_feq. apply N_self; assumption.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* The computation lemmas: the value a run leaves on a registry.                        *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma at_ev : forall e s, InvF s -> ConsF s ->
    aF e s (reg e) = f (reg e) s (sig e (s (reg e))).
  Proof.
    intros e s Hi Hc. pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e) as Re.
    destruct (split_at (reg e) Re) as [o1 [L [Ho [Hj Hs]]]].
    pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as T.
    assert (Hie : InvF (evF e s)) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    unfold applyF. rewrite (N_frun _ _ _ _ _ _ _ _ _ HC _ Hie (reg e)).
    rewrite (frun_solves _ _ _ _ _ _ _ _ _ HC o _ T (reg e) Re).
    unfold evstep at 2. rewrite upd_eq.
    apply (f_upL (reg e) L); [exact Hs |].
    eapply upL_trans; [apply (frun_upL o1 L _ s Ho); apply evstep_upL_self; exact Hj |].
    apply upL_feq. apply Cons_frun; [exact Hc | auto].
  Qed.

  Lemma at_off : forall a t j, InvF t -> In j o -> j <> reg a ->
    aF a t j = f j (aF a t) (t j).
  Proof.
    intros a t j Hi Hj Ne. pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as T.
    assert (Hie : InvF (evF a t)) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    pose proof (N_frun _ _ _ _ _ _ _ _ _ HC _ Hie) as Hn.
    unfold applyF. rewrite (Hn j).
    rewrite (frun_solves _ _ _ _ _ _ _ _ _ HC o _ T j Hj).
    unfold evstep at 2. rewrite (upd_neq _ _ _ _ _ Ne).
    apply f_feq. apply feq_sym. exact Hn.
  Qed.

  Lemma run_off : forall w s j, InvF s -> ConsF s -> In j o ->
    Forall (fun a => reg a <> j) w -> rF w s j = f j (rF w s) (s j).
  Proof.
    induction w as [| a w IH]; intros s j Hi Hc Hj Hw.
    - simpl. apply Hc. exact Hj.
    - inversion Hw as [| ? ? Ha Hw']; subst.
      change (rF (a :: w) s) with (rF w (aF a s)).
      assert (Ia : InvF (aF a s)) by (apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
      assert (Ca : ConsF (aF a s)) by (apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hi).
      rewrite (IH (aF a s) j Ia Ca Hj Hw').
      rewrite (at_off a s j Hi Hj (fun H => Ha (eq_sym H))).
      apply (c_absorb _ _ _ _ _ _ _ _ _ HC);
        [apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Ia | exact Ia | apply Hi].
  Qed.

  (* Converse, C1 side: moving e past events of other registries IS the C1 equation. *)
  Theorem conv_c1_runs : forall s e w, InvF s -> ConsF s -> Forall (fun a => reg a <> reg e) w ->
    rF (e :: w) s (reg e) = f (reg e) (rF w s) (sig e (s (reg e))) /\
    rF (w ++ [e]) s (reg e) = f (reg e) (rF w s) (sig e (f (reg e) (rF w s) (s (reg e)))).
  Proof.
    intros s e w Hi Hc Hw. pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e) as Re.
    destruct (split_at (reg e) Re) as [o1 [L [Ho [Hj Hs]]]].
    assert (Ie : InvF (aF e s)) by (apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Ce : ConsF (aF e s)) by (apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hi).
    split.
    - change (rF (e :: w) s) with (rF w (aF e s)).
      rewrite (run_off w (aF e s) (reg e) Ie Ce Re Hw).
      rewrite (at_ev e s Hi Hc).
      rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC);
        [| apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Ie | exact Hi
         | apply (c_sig _ _ _ _ _ _ _ _ _ HC); apply Hi].
      apply (f_upL (reg e) L); [exact Hs |].
      apply (runF_upL o1 L w _ _ Ho). apply (applyF_upL_self o1); assumption.
    - rewrite runF_app. change (rF [e] (rF w s)) with (aF e (rF w s)).
      rewrite (at_ev e (rF w s)); [| apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi
                                   | apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption].
      rewrite (run_off w s (reg e) Hi Hc Re Hw). reflexivity.
  Qed.

  (* Converse, C2 side: running two events of one registry IS the left side of C2. *)
  Theorem conv_c2_runs : forall s e1 e2, InvF s -> ConsF s -> reg e1 = reg e2 ->
    rF [e1; e2] s (reg e1) = f (reg e1) s (sig e2 (f (reg e1) s (sig e1 (s (reg e1))))).
  Proof.
    intros s e1 e2 Hi Hc E12. pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e1) as Re.
    destruct (split_at (reg e1) Re) as [o1 [L [Ho [Hj Hs]]]].
    assert (Ie : InvF (aF e1 s)) by (apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Ce : ConsF (aF e1 s)) by (apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hi).
    change (rF [e1; e2] s) with (aF e2 (aF e1 s)).
    rewrite E12. rewrite (at_ev e2 (aF e1 s) Ie Ce). rewrite <- E12.
    rewrite (at_ev e1 s Hi Hc).
    apply (f_upL (reg e1) L); [exact Hs |]. apply (applyF_upL_self o1); assumption.
  Qed.

  (* A C1 failure at a reachable witness is a divergence of trace-equivalent sequences. *)
  Theorem conv_c1_diverge : forall s0 p e w, InvF s0 -> ConsF s0 ->
    Forall (fun a => reg a <> reg e) w ->
    f (reg e) (rF w (rF p s0)) (sig e (f (reg e) (rF w (rF p s0)) (rF p s0 (reg e)))) <>
    f (reg e) (rF w (rF p s0)) (sig e (rF p s0 (reg e))) ->
    tequiv IfedF (p ++ e :: w) (p ++ w ++ [e]) /\
    rF (p ++ e :: w) s0 (reg e) <> rF (p ++ w ++ [e]) s0 (reg e).
  Proof.
    intros s0 p e w Hi Hc Hw Hne. split.
    - apply tequiv_app_l. apply tequiv_move. exact Hw.
    - rewrite (runF_app _ _ _ _ _ _ _ p (e :: w)), (runF_app _ _ _ _ _ _ _ p (w ++ [e])).
      destruct (conv_c1_runs (rF p s0) e w) as [A B];
        [apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi
        | apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption | exact Hw |].
      rewrite A, B. intro H. apply Hne. symmetry. exact H.
  Qed.

  (* A C2 failure at a reachable witness is a divergence of two sequences one swap apart. *)
  Theorem conv_c2_diverge : forall s0 p e1 e2, InvF s0 -> ConsF s0 -> reg e1 = reg e2 -> I e1 e2 ->
    ~ C2at (rF p s0) e1 e2 ->
    tequiv IfedF (p ++ [e1; e2]) (p ++ [e2; e1]) /\
    rF (p ++ [e1; e2]) s0 (reg e1) <> rF (p ++ [e2; e1]) s0 (reg e1).
  Proof.
    intros s0 p e1 e2 Hi Hc E12 Hab Hne. split.
    - apply (teq_swap _ p e1 e2 []). right. exact Hab.
    - rewrite !runF_app.
      assert (Is : InvF (rF p s0)) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
      assert (Cs : ConsF (rF p s0)) by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
      rewrite (conv_c2_runs _ e1 e2 Is Cs E12).
      rewrite E12. rewrite (conv_c2_runs _ e2 e1 Is Cs (eq_sym E12)). rewrite <- E12.
      exact Hne.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Pointwise exactness: commutation at a reachable state iff the local C1/C2 instances. *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma pair_commute : forall s e1 e2, InvF s -> ConsF s ->
    (reg e1 <> reg e2 -> C1at s e1 e2 /\ C1at s e2 e1) ->
    (reg e1 = reg e2 -> C2at s e1 e2) ->
    feqF (aF e2 (aF e1 s)) (aF e1 (aF e2 s)).
  Proof.
    intros s e1 e2 Hs Hcs HC1 HC2.
    pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as Ht.
    set (z1 := frF o (evF e1 s)). set (z2 := frF o (evF e2 s)).
    set (z12 := frF o (evF e2 z1)). set (z21 := frF o (evF e1 z2)).
    assert (Iv : forall e t, InvF t -> InvF (evF e t))
      by (intros; apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); assumption).
    assert (Ifr : forall l t, InvF t -> InvF (frF l t))
      by (intros; apply (frun_inv _ _ _ _ _ _ _ _ _ HC); assumption).
    assert (I1 : InvF z1) by (apply Ifr, Iv; assumption).
    assert (I2 : InvF z2) by (apply Ifr, Iv; assumption).
    assert (I12 : InvF z12) by (apply Ifr, Iv; assumption).
    assert (I21 : InvF z21) by (apply Ifr, Iv; assumption).
    assert (A1 : feqF (aF e1 s) z1) by (apply (N_frun _ _ _ _ _ _ _ _ _ HC), Iv; assumption).
    assert (A2 : feqF (aF e2 s) z2) by (apply (N_frun _ _ _ _ _ _ _ _ _ HC), Iv; assumption).
    assert (A12 : feqF (aF e2 (aF e1 s)) z12).
    { eapply feq_trans; [apply (applyF_ext _ _ _ _ _ _ _ _ _ HC); exact A1 |].
      apply (N_frun _ _ _ _ _ _ _ _ _ HC). apply Iv; assumption. }
    assert (A21 : feqF (aF e1 (aF e2 s)) z21).
    { eapply feq_trans; [apply (applyF_ext _ _ _ _ _ _ _ _ _ HC); exact A2 |].
      apply (N_frun _ _ _ _ _ _ _ _ _ HC). apply Iv; assumption. }
    assert (C1' : ConsF z1).
    { apply (Cons_feq (aF e1 s)); [apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hs | exact A1]. }
    assert (C2' : ConsF z2).
    { apply (Cons_feq (aF e2 s)); [apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hs | exact A2]. }
    eapply feq_trans; [exact A12 |]. eapply feq_trans; [| apply feq_sym; exact A21].
    pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e1) as R1. pose proof (c_reg _ _ _ _ _ _ _ _ _ HC e2) as R2.
    assert (S1 : forall j, In j o -> z1 j = f j z1 (evF e1 s j))
      by (intros; apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption).
    assert (S2 : forall j, In j o -> z2 j = f j z2 (evF e2 s j))
      by (intros; apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption).
    apply (solve_unique _ _ _ _ _ _ _ _ _ HC o z12 z21 (evF e2 z1) (evF e1 z2) Ht).
    - intros k Hk. unfold z12, z21. rewrite !frun_out by assumption.
      rewrite !evstep_off by (intro E'; subst; contradiction).
      unfold z1, z2. rewrite !frun_out by assumption.
      rewrite !evstep_off by (intro E'; subst; contradiction). reflexivity.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros j Hj. pose proof (Hcs j Hj) as Hx. pose proof (Hs j) as Vx.
      destruct (split_at j Hj) as [o1 [L [Ho [HjL HsL]]]].
      assert (Fr : forall t t', upL L t t' -> upL L (frF o t) (frF o t'))
        by (intros; apply (frun_upL o1); assumption).
      assert (Fs : upL L (frF o s) s) by (apply upL_feq, Cons_frun; [exact Hcs | auto]).
      destruct (Nat.eq_dec j (reg e1)) as [J1 | J1]; destruct (Nat.eq_dec j (reg e2)) as [J2 | J2].
      + (* the same registry: C2 at s *)
        assert (L1 : In (reg e1) L) by (rewrite <- J1; exact HjL).
        assert (L2 : In (reg e2) L) by (rewrite <- J2; exact HjL).
        assert (U1 : upL L z1 s) by (eapply upL_trans; [apply Fr, evstep_upL_self, L1 | exact Fs]).
        assert (U2 : upL L z2 s) by (eapply upL_trans; [apply Fr, evstep_upL_self, L2 | exact Fs]).
        assert (U12 : upL L z12 s).
        { eapply upL_trans; [apply Fr, evstep_upL_self, L2 |].
          eapply upL_trans; [apply Fr, U1 | exact Fs]. }
        rewrite (evstep_at _ _ _ _ e2 z1 j J2), (evstep_at _ _ _ _ e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_at _ _ _ _ e1 s j J1), (evstep_at _ _ _ _ e2 s j J2).
        assert (F12 : forall x, f j z12 x = f j s x) by (intro; apply (f_upL j L); assumption).
        assert (F1 : forall x, f j z1 x = f j s x) by (intro; apply (f_upL j L); assumption).
        assert (F2 : forall x, f j z2 x = f j s x) by (intro; apply (f_upL j L); assumption).
        rewrite !F12, !F1, !F2.
        pose proof (HC2 (eq_trans (eq_sym J1) J2)) as H. unfold C2at in H.
        rewrite <- J1 in H. exact H.
      + (* j is e1's registry only: C1 at (s, e1, e2) *)
        assert (L1 : In (reg e1) L) by (rewrite <- J1; exact HjL).
        assert (U12 : upL L z12 z2).
        { apply Fr. apply evstep_upL. eapply upL_trans; [apply Fr, evstep_upL_self, L1 | exact Fs]. }
        rewrite (evstep_off _ _ _ _ e2 z1 j J2), (evstep_at _ _ _ _ e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_at _ _ _ _ e1 s j J1), (evstep_off _ _ _ _ e2 s j J2).
        assert (V1 : valid j (sig e1 (s j)))
          by (rewrite J1; apply (c_sig _ _ _ _ _ _ _ _ _ HC); rewrite <- J1; exact Vx).
        rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC) by assumption.
        assert (F12 : forall x, f j z12 x = f j z2 x) by (intro; apply (f_upL j L); assumption).
        rewrite !F12.
        destruct (HC1 (fun E' => J2 (eq_trans J1 E'))) as [H _]. unfold C1at in H.
        rewrite <- J1 in H. rewrite !(f_feq j (aF e2 s) z2 _ A2) in H.
        symmetry. exact H.
      + (* j is e2's registry only: C1 at (s, e2, e1) *)
        assert (L2 : In (reg e2) L) by (rewrite <- J2; exact HjL).
        assert (U12 : upL L z12 z1).
        { eapply upL_trans; [apply Fr, evstep_upL_self, L2 |].
          apply upL_feq. apply Cons_frun; [exact C1' | auto]. }
        rewrite (evstep_at _ _ _ _ e2 z1 j J2), (evstep_off _ _ _ _ e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_off _ _ _ _ e1 s j J1), (evstep_at _ _ _ _ e2 s j J2).
        assert (V2 : valid j (sig e2 (s j)))
          by (rewrite J2; apply (c_sig _ _ _ _ _ _ _ _ _ HC); rewrite <- J2; exact Vx).
        rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC j z12 z2) by assumption.
        assert (F12 : forall x, f j z12 x = f j z1 x) by (intro; apply (f_upL j L); assumption).
        rewrite !F12.
        assert (Nn : reg e1 <> reg e2) by (intro E'; apply J1; rewrite J2; symmetry; exact E').
        destruct (HC1 Nn) as [_ H]. unfold C1at in H.
        rewrite <- J2 in H. rewrite !(f_feq j (aF e1 s) z1 _ A1) in H. exact H.
      + (* neither: both sides are re-projections of the same state *)
        rewrite (evstep_off _ _ _ _ e2 z1 j J2), (evstep_off _ _ _ _ e1 z2 j J1).
        rewrite (S1 j Hj), (S2 j Hj), (evstep_off _ _ _ _ e1 s j J1), (evstep_off _ _ _ _ e2 s j J2).
        rewrite !(c_absorb _ _ _ _ _ _ _ _ _ HC) by assumption. reflexivity.
  Qed.

  Lemma pair_commute_nec : forall s e1 e2, InvF s -> ConsF s ->
    feqF (aF e2 (aF e1 s)) (aF e1 (aF e2 s)) ->
    (reg e1 <> reg e2 -> C1at s e1 e2 /\ C1at s e2 e1) /\
    (reg e1 = reg e2 -> C2at s e1 e2).
  Proof.
    intros s e1 e2 Hi Hc H. split.
    - intros Ne.
      assert (W1 : Forall (fun a => reg a <> reg e1) [e2])
        by (constructor; [intro E'; apply Ne; symmetry; exact E' | constructor]).
      assert (W2 : Forall (fun a => reg a <> reg e2) [e1]) by (constructor; [exact Ne | constructor]).
      destruct (conv_c1_runs s e1 [e2] Hi Hc W1) as [A1 B1].
      destruct (conv_c1_runs s e2 [e1] Hi Hc W2) as [A2 B2].
      change (rF [e1; e2] s) with (aF e2 (aF e1 s)) in A1.
      change (rF ([e2] ++ [e1]) s) with (aF e1 (aF e2 s)) in B1.
      change (rF [e2; e1] s) with (aF e1 (aF e2 s)) in A2.
      change (rF ([e1] ++ [e2]) s) with (aF e2 (aF e1 s)) in B2.
      change (rF [e2] s) with (aF e2 s) in A1, B1.
      change (rF [e1] s) with (aF e1 s) in A2, B2.
      unfold C1at. split.
      + rewrite <- B1, <- A1. symmetry. apply H.
      + rewrite <- B2, <- A2. apply H.
    - intros E12. unfold C2at.
      rewrite <- (conv_c2_runs s e1 e2 Hi Hc E12).
      rewrite E12 at 2 3 4. rewrite E12 at 1.
      rewrite <- (conv_c2_runs s e2 e1 Hi Hc (eq_sym E12)).
      rewrite <- E12. apply H.
  Qed.

  (* Headline (pointwise): at a reachable state, two events commute iff their C1 instances
     (different registries) or their C2 instance (same registry) hold there. *)
  Theorem reach_commute_iff : forall s e1 e2, InvF s -> ConsF s ->
    (feqF (aF e2 (aF e1 s)) (aF e1 (aF e2 s)) <->
     (reg e1 <> reg e2 -> C1at s e1 e2 /\ C1at s e2 e1) /\ (reg e1 = reg e2 -> C2at s e1 e2)).
  Proof.
    intros s e1 e2 Hi Hc. split.
    - apply pair_commute_nec; assumption.
    - intros [A B]. apply pair_commute; assumption.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* The global condition and the exact characterization.                                *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem acyclic_gc_iff : forall s0, GCF s0 <-> TraceConv s0.
  Proof.
    intros s0. split.
    - intros Hg es1 es2 H.
      induction H as [ l | l a b r Hab | l1 l2 H IH | l1 l2 l3 H12 IH12 H23 IH23 ].
      + intro k. reflexivity.
      + rewrite !runF_app, !runF_two. apply (runF_ext _ _ _ _ _ _ _ _ _ HC).
        apply Hg. exact Hab.
      + apply feq_sym. exact IH.
      + eapply feq_trans; eassumption.
    - intros Ht p a b Hab.
      pose proof (Ht _ _ (teq_swap _ p a b [] Hab)) as H.
      rewrite !runF_app in H. exact H.
  Qed.

  Theorem gc_iff_reach : forall s0, InvF s0 -> ConsF s0 -> (GCF s0 <-> C1R1 s0 /\ C2R s0).
  Proof.
    intros s0 Hi Hc.
    assert (Is : forall p, InvF (rF p s0)) by (intro; apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Cs : forall p, ConsF (rF p s0))
      by (intro; apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
    split.
    - intros Hg. split.
      + intros p e a Ne.
        assert (Hf : IfedF e a) by (left; intro E'; apply Ne; symmetry; exact E').
        destruct (pair_commute_nec _ e a (Is p) (Cs p) (Hg p e a Hf)) as [H _].
        apply H. intro E'. apply Ne. symmetry. exact E'.
      + intros p e1 e2 E12 Hab.
        destruct (pair_commute_nec _ e1 e2 (Is p) (Cs p) (Hg p e1 e2 (or_intror Hab))) as [_ H].
        apply H. exact E12.
    - intros [H1 H2] p a b Hab. apply pair_commute; [apply Is | apply Cs | |].
      + intros Ne. split; [apply H1 | apply H1]; [intro E'; apply Ne; symmetry; exact E' | exact Ne].
      + intros E12. apply H2; [exact E12 |].
        destruct Hab as [Ne | Hi']; [contradiction | exact Hi'].
  Qed.

  (* Headline: all trace-equivalent sequences from s0 converge iff C1 and C2 hold at the
     witnesses reachable from s0 (C1 with one intervening event). *)
  Theorem fed_exact : forall s0, InvF s0 -> ConsF s0 -> (TraceConv s0 <-> C1R1 s0 /\ C2R s0).
  Proof.
    intros s0 Hi Hc. rewrite <- (gc_iff_reach s0 Hi Hc). symmetry. apply acyclic_gc_iff.
  Qed.

  (* Headline: the same with any number of intervening events (so one is the general case). *)
  Theorem fed_exact_full : forall s0, InvF s0 -> ConsF s0 -> (TraceConv s0 <-> C1R s0 /\ C2R s0).
  Proof.
    intros s0 Hi Hc. split.
    - intros Ht. split; [| apply (proj1 (fed_exact s0 Hi Hc) Ht)].
      intros p e w Hw.
      pose proof (Ht _ _ (tequiv_app_l p _ _ (tequiv_move e w Hw)) (reg e)) as H.
      rewrite (runF_app _ _ _ _ _ _ _ p (e :: w)), (runF_app _ _ _ _ _ _ _ p (w ++ [e])) in H.
      destruct (conv_c1_runs (rF p s0) e w) as [A B];
        [apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi
        | apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption | exact Hw |].
      rewrite <- A, <- B. symmetry. exact H.
    - intros [H1 H2]. apply (proj2 (fed_exact s0 Hi Hc)). split; [| exact H2].
      intros p e a Ne. unfold C1at.
      assert (Hw : Forall (fun x => reg x <> reg e) [a]) by (constructor; [exact Ne | constructor]).
      exact (H1 p e [a] Hw).
  Qed.

  (* (b) of the cycles development: in the acyclic case static C1 + C2 imply the global
     condition (and hence its reachable restriction). *)
  Theorem static_c1_c2_gc : C1 V f valid E reg sig -> C2 V f valid E reg sig I ->
    forall s0, InvF s0 -> ConsF s0 -> GCF s0 /\ C1R1 s0 /\ C2R s0.
  Proof.
    intros H1 H2 s0 Hi Hc.
    assert (Hg : GCF s0).
    { intros p a b Hab. apply (fed_events_commute _ _ _ _ _ _ _ _ _ _ HC H1 H2);
        [apply (runF_inv _ _ _ _ _ _ _ _ _ HC) | apply (runF_cons _ _ _ _ _ _ _ _ _ HC) | ];
        assumption. }
    split; [exact Hg |]. apply (gc_iff_reach s0 Hi Hc). exact Hg.
  Qed.

  (* Static C1 (resp. C2) alone gives its reachable restriction. *)
  Lemma static_c1_reach : C1 V f valid E reg sig ->
    forall s0, InvF s0 -> ConsF s0 -> C1R1 s0.
  Proof.
    intros H1 s0 Hi Hc p e a _. unfold C1at. unfold C1 in H1.
    assert (Is : InvF (rF p s0)) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Cs : ConsF (rF p s0)) by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
    apply (H1 e _ (rF p s0)); [apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Is | exact Is | apply Is |].
    apply Cs. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma static_c2_reach : C2 V f valid E reg sig I ->
    forall s0, InvF s0 -> ConsF s0 -> C2R s0.
  Proof.
    intros H2 s0 Hi Hc p e1 e2 E12 Hab. unfold C2at. unfold C2 in H2.
    assert (Is : InvF (rF p s0)) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (Cs : ConsF (rF p s0)) by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
    apply H2; [exact E12 | exact Hab | exact Is | apply Is |].
    apply Cs. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  End WithCommon.
End Conv.

(* ========================================================================================= *)
(* The naive converse is false: C1 fails, yet every interleaving from every valid consistent *)
(* start converges. Registry 0 (manufacturer) has Touch, which bumps a counter but never     *)
(* changes the recall flag the morphism reads; registry 1 (supplier) has Sell, which reads   *)
(* the shared listed flag (the audit's CSell). C1's witness needs the flag to flip between    *)
(* z' and z; no run can flip it, so no divergence exists.                                    *)
(* ========================================================================================= *)

Inductive tev : Type := TTouch | TSell.

Definition tv_reg (e : tev) : nat := match e with TTouch => 0 | TSell => 1 end.

Definition tv_sig (e : tev) (x : bool * nat) : bool * nat :=
  match e with
  | TTouch => (fst x, Nat.min (S (snd x)) 3)
  | TSell => if fst x then (fst x, Nat.min (S (snd x)) 3) else x
  end.

Definition tv_I (_ _ : tev) : Prop := True.

Lemma tv_common : Common (bool * nat) src2 sp_f sp_valid sp_rho tev tv_reg tv_sig [0; 1].
Proof.
  apply sp_common_parts.
  - intros [] [[] n] H; simpl in *; trivial; lia.
  - intros []; simpl; tauto.
Qed.

Theorem naive_converse_fails :
  Common (bool * nat) src2 sp_f sp_valid sp_rho tev tv_reg tv_sig [0; 1] /\
  C2 (bool * nat) sp_f sp_valid tev tv_reg tv_sig tv_I /\
  ~ C1 (bool * nat) sp_f sp_valid tev tv_reg tv_sig /\
  Inv (bool * nat) sp_valid ce_s0 /\ Cons (bool * nat) sp_f [0; 1] ce_s0 /\ ce_s0 1 = (true, 0) /\
  (forall s0, Inv (bool * nat) sp_valid s0 -> Cons (bool * nat) sp_f [0; 1] s0 ->
     TraceConv (bool * nat) sp_f sp_rho tev tv_reg tv_sig tv_I [0; 1] s0).
Proof.
  assert (Hc2 : C2 (bool * nat) sp_f sp_valid tev tv_reg tv_sig tv_I).
  { intros [] [] z b E' _ _ _ _; simpl in E'; try discriminate; reflexivity. }
  split; [exact tv_common |]. split; [exact Hc2 |]. split.
  { intro Hc.
    assert (Hz : Inv (bool * nat) sp_valid (fun _ => (true, 0))) by (intros [| [| k]]; simpl; lia).
    assert (Hz' : Inv (bool * nat) sp_valid (fun _ => (false, 0))) by (intros [| [| k]]; simpl; lia).
    assert (Hb : sp_valid (tv_reg TSell) (true, 0)) by (simpl; lia).
    pose proof (Hc TSell (fun _ => (true, 0)) (fun _ => (false, 0)) (true, 0) Hz Hz' Hb eq_refl)
      as Hd.
    simpl in Hd. discriminate Hd. }
  split. { intros [| [| k]]; simpl; lia. }
  split. { intros j [<- | [<- | []]]; reflexivity. }
  split; [reflexivity |].
  intros s0 Hi Hc. apply (fed_exact _ _ _ _ _ _ _ _ _ _ tv_common s0 Hi Hc). split.
  - intros p e a Ne.
    set (s := runF (bool * nat) sp_f sp_rho tev tv_reg tv_sig [0; 1] p s0).
    assert (Cs : Cons (bool * nat) sp_f [0; 1] s)
      by (apply (runF_cons _ _ _ _ _ _ _ _ _ tv_common); assumption).
    destruct e, a; simpl in Ne; try (exfalso; apply Ne; reflexivity); unfold C1at; simpl.
    + reflexivity.
    + (* e = Sell, a = Touch: the touch leaves the recall flag, so the target stays consistent *)
      assert (H1 : s 1 = sp_f 1 s (s 1)) by (apply Cs; right; left; reflexivity).
      unfold applyF, N, frun, evstep, upd. simpl.
      simpl in H1. destruct (s 1) as [b n]. injection H1 as Hb. subst b.
      unfold sp_rho; simpl. reflexivity.
  - apply (static_c2_reach _ _ _ _ _ _ _ _ _ _ tv_common Hc2 s0 Hi Hc).
Qed.
