(* ProjectionChannels.v: propagation over CHANNELS that deliver projections late, reordered or
   duplicated (REGIME-AUDIT.md gap 21, a new axis). Axiom-free.

   The gap. The distributed model of FederationEvents.v and DistributedExact.v has a propagation
   step DProp j that reads the sources' CURRENT states. gsm's nodes instead send projections
   (SharedProjection) over a transport and merge whatever arrives: MergeProjection applies every
   projection; MergeProjectionAfter refuses one whose Version is not newer than the last one
   applied from that edge (versions strictly increasing per edge, assigned by the source).

   Model. A configuration holds every registry's state cs, the projections in flight to each
   target cb j (pairs (version, snapshot of the state when sent)), the last applied version cl j
   and the last sent version cv j. Actions: CEv e (a local event), CSend j v (send j the
   projection of the current state with version v), CDel j i (deliver the i-th projection in
   flight to j and remove it: any i, so any order and any delay), CDup j i (deliver it and keep it:
   a duplicate that can arrive again later). A delivery merges t j := f j z (t j) with the
   snapshot z (f reads z only through src j). vm = false is MergeProjection; vm = true is
   MergeProjectionAfter. disc: the version discipline (each send to j has a version above every
   earlier one). The channel is per target; for a single-source target it is gsm's per-edge
   channel, and a multi-source target's channel carries all its sources at one snapshot (gsm
   reports multi-source targets as not certified anyway). fround c: the final round, in
   topological order each target is sent the projection of the current state with the next
   version and that projection is delivered; a drain is any word of deliveries.

   Results, from a valid start s0, over disciplined runs.
     emb_run           : the current-value model is the channel model with every send delivered at
                         once, in either mode (no hypothesis, so also on cycles).
     chan_flush        : under XU at the channel-reachable states, every channel run flushes to the
                         FedMachine run of its events (any order, duplicates, either mode).
     chan_exact        : ChanConv vm s0 <-> CXUR vm s0 /\ C2R (N s0)
                         (convergence compared after a flush, exactly: XU at every state a channel
                          run reaches, plus the FedMachine's C2; in either merge mode).
     chan_exact_global : (forall valid s0, ChanConv vm s0) <-> XUG /\ C2G, the current-value model's
                         own condition; chan_global_exact_roots: when every target's sources are
                         roots, XU /\ C2 (gsm's static check), in either mode. chan_xu_c2: XU + C2
                         suffice.
   Versioned merge: the channels deliver the flush themselves.
     vsettle           : after the final round every projection in flight is refused, so every
                         drain ends at frun o (cs c), the current-value flush of the state reached.
     vsettle_settled   : the drained state is a fixed point of every repair (Cons).
     vsettle_exact     : SettleConv s0 <-> ChanConv true s0, so (vsettle_exact_cond)
                         SettleConv s0 <-> CXUR true s0 /\ C2R (N s0): converging at drain, with no
                         outside flush, exactly.
     vsettle_cv        : the drained state is the state of the current-value run "the same events,
                         then a flush".
     vsettle_xu_c2     : gsm's XU (FedReport.ProjectionSafe) and C2 (Build) give convergence at drain.
   Plain merge: the flush cannot be delivered.
     plain_settle_iff  : after the final round, every drain settles iff every projection still in
                         flight to j carries the image of the flushed state at j.
     plain_stale_counterexample : on the supply federation (Common, XU, LocalCC), a drained plain
                         run whose last send came after the source's last change, and was
                         delivered, ends unsettled (a recalled product still listed), and another
                         drained run with the same events ends elsewhere; ChanConv false still
                         holds (the failure is the stale overwrite, not XU); the versioned merge
                         refuses the stale projection and SettleConv holds.
   Hypotheses are necessary.
     version_order_counterexample : versions out of send order (a newer version on an older
                         snapshot: a restamped retry, or a version read off a value the source
                         revisits) let the versioned merge apply a stale projection last.
     no_final_send_counterexample : drained channels with no send after the last source change
                         leave the target stale, in either mode.
     chan_exact        : necessity of CXUR and C2R.
   Two-level networks (TwoLevel rt: every registry is a pure root, whose repair is the identity, or
   a sink nobody reads; any two-registry federation, any star).
     vchan_emulate     : every state a versioned channel run reaches is, at any target and at every
                         root, the state of a current-value run (projections reordered, duplicated or
                         late included).
     vchan_twolevel_exact : ChanConv true s0 <-> XUR s0 /\ C2R (N s0), SettleConv s0 <-> the same,
                         and SettleConv s0 <-> DistConv s0: the exact condition of
                         DistributedExact.dist_exact, unchanged by the channels.
     late_delivery_instance : non-vacuity, a projection delivered after later local events.
   Cycles.
     vchan_cyc_ghost   : on the flag cycle of DistributedCycles.v, a disciplined versioned run with
                         in-order fresh deliveries and a final round is drained and settled at the
                         ghost ((false,true),(false,true)), while the same events give the least
                         fixed point; versioned channels do not remove the ghost (dist_cyc_ghost).
   Not covered (the residue of gap 21): whether CXUR true = XUR beyond two-level networks (chains,
   forests, multi-source targets); flush and reset epochs over channels on cycles (an in-flight
   pre-reset projection is a new hazard); lossy channels.

   States are compared pointwise (feq); no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.FederationEvents NC.FederationEventsConverse NC.FederationGRS.
Require Import NC.DistributedExact.
Import ListNotations.

Section Chan.
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
  Local Notation fsF := (fstep V f).
  Local Notation evF := (evstep V E reg sig).
  Local Notation IfedF := (Ifed E reg I).
  Local Notation dF := (drun V f E reg sig).
  Local Notation okF := (okact E o).
  Local Notation evsF := (evs E).
  Local Notation DE := (DEv E).
  Local Notation DP := (DProp E).
  Local Notation TC := (TraceConv V f rho E reg sig I o).
  Local Notation C2Rf := (C2R V f rho E reg sig I o).
  Local Notation XUatF := (XUat V f rho E reg sig o).
  Local Notation XURF := (XUR V f rho E reg sig o).
  Local Notation DistConvF := (DistConv V f rho E reg sig I o).
  Local Notation updF := (upd V).

  (* ---------------------------------------------------------------------------------- *)
  (* The channel model.                                                                  *)
  (* ---------------------------------------------------------------------------------- *)

  (* A projection in flight to target j: its version and the snapshot of the global state taken
     when it was sent (the merge reads it only through src j, by c_local). *)
  Definition msg : Type := (nat * (nat -> V))%type.

  (* cs: every registry's state; cb j: the projections in flight to j (newest first, delivered in
     any order); cl j: the version of the last projection j applied (versioned merge); cv j: the
     version of the last projection sent to j. *)
  Record cfg : Type := Cfg { cs : nat -> V; cb : nat -> list msg; cl : nat -> nat; cv : nat -> nat }.

  Definition setb (b : nat -> list msg) (j : nat) (l : list msg) : nat -> list msg :=
    fun k => if Nat.eqb k j then l else b k.

  Definition setn (g : nat -> nat) (j n : nat) : nat -> nat :=
    fun k => if Nat.eqb k j then n else g k.

  (* CEv e: a local event. CSend j v: send j the projection of the current state with version v.
     CDel j i: deliver the i-th projection in flight to j and remove it (any i: reordering).
     CDup j i: deliver it and keep it (duplication: it can be delivered again, at any later time). *)
  Inductive cact : Type :=
  | CEv : E -> cact
  | CSend : nat -> nat -> cact
  | CDel : nat -> nat -> cact
  | CDup : nat -> nat -> cact.

  Fixpoint rmn (i : nat) (l : list msg) : list msg :=
    match l with
    | [] => []
    | x :: l' => match i with 0 => l' | S i' => x :: rmn i' l' end
    end.

  (* Merge modes: vm = false is gsm's MergeProjection (apply whatever arrives); vm = true is
     MergeProjectionAfter (apply only a version newer than the last applied one, and record it). *)
  Definition applies (vm : bool) (c : cfg) (j : nat) (m : msg) : bool :=
    if vm then Nat.ltb (cl c j) (fst m) else true.

  Definition merge (vm : bool) (j : nat) (m : msg) (c : cfg) : cfg :=
    if applies vm c j m
    then Cfg (updF (cs c) j (f j (snd m) (cs c j))) (cb c)
             (if vm then setn (cl c) j (fst m) else cl c) (cv c)
    else c.

  Definition cstep (vm : bool) (a : cact) (c : cfg) : cfg :=
    match a with
    | CEv e => Cfg (evF e (cs c)) (cb c) (cl c) (cv c)
    | CSend j v => Cfg (cs c) (setb (cb c) j ((v, cs c) :: cb c j)) (cl c) (setn (cv c) j v)
    | CDel j i =>
        match nth_error (cb c j) i with
        | Some m => merge vm j m (Cfg (cs c) (setb (cb c) j (rmn i (cb c j))) (cl c) (cv c))
        | None => c
        end
    | CDup j i =>
        match nth_error (cb c j) i with
        | Some m => merge vm j m c
        | None => c
        end
    end.

  Fixpoint crun (vm : bool) (w : list cact) (c : cfg) : cfg :=
    match w with [] => c | a :: w' => crun vm w' (cstep vm a c) end.

  Fixpoint cevs (w : list cact) : list E :=
    match w with [] => [] | CEv e :: w' => e :: cevs w' | _ :: w' => cevs w' end.

  Definition okc (a : cact) : Prop :=
    match a with CEv _ => True | CSend j _ | CDel j _ | CDup j _ => In j o end.

  (* The version discipline (gsm's contract): versions sent to j strictly increase in send order. *)
  Fixpoint disc (vm : bool) (w : list cact) (c : cfg) : Prop :=
    match w with
    | [] => True
    | a :: w' => (match a with CSend j v => cv c j < v | _ => True end) /\ disc vm w' (cstep vm a c)
    end.

  (* A drain: deliveries only (no events, no sends). *)
  Definition isdrain (a : cact) : Prop :=
    match a with CDel j _ | CDup j _ => In j o | _ => False end.

  Definition init (s : nat -> V) : cfg := Cfg s (fun _ => []) (fun _ => 0) (fun _ => 0).

  Definition Drained (c : cfg) : Prop := forall j, cb c j = [].

  (* The final round: in topological order, each target is sent the projection of the current
     state with the next version, and that projection is delivered. *)
  Fixpoint frnd (l : list nat) (g : nat -> nat) : list cact :=
    match l with [] => [] | j :: l' => CSend j (S (g j)) :: CDel j 0 :: frnd l' g end.

  Definition fround (c : cfg) : list cact := frnd o (cv c).

  (* The current-value model inside the channel model: a propagation step is a send immediately
     delivered. *)
  Fixpoint emb (w : list (act E)) (g : nat -> nat) : list cact :=
    match w with
    | [] => []
    | DEv _ e :: w' => CEv e :: emb w' g
    | DProp _ j :: w' => CSend j (S (g j)) :: CDel j 0 :: emb w' (setn g j (S (g j)))
    end.

  (* Invariants: states and snapshots are valid; versions in flight are at most the last sent. *)
  Definition CInv (c : cfg) : Prop :=
    InvF (cs c) /\ forall j m, In m (cb c j) -> InvF (snd m).

  Definition VInv (c : cfg) : Prop :=
    forall j, cl c j <= cv c j /\ forall m, In m (cb c j) -> fst m <= cv c j.

  (* ---------------------------------------------------------------------------------- *)
  (* Basic facts.                                                                        *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma setb_eq : forall b j l, setb b j l j = l.
  Proof. intros. unfold setb. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma setb_neq : forall b j l k, k <> j -> setb b j l k = b k.
  Proof. intros b j l k H. unfold setb. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

  Lemma setn_eq : forall g j n, setn g j n j = n.
  Proof. intros. unfold setn. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma setn_neq : forall g j n k, k <> j -> setn g j n k = g k.
  Proof. intros g j n k H. unfold setn. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

  Lemma updF_eq : forall t j x, updF t j x j = x.
  Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma updF_neq : forall t j x k, k <> j -> updF t j x k = t k.
  Proof. intros t j x k H. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

  Lemma rmn_in : forall i l m, In m (rmn i l) -> In m l.
  Proof.
    induction i as [| i IH]; intros [| x l] m H; simpl in *; try contradiction.
    - right. exact H.
    - destruct H as [<- | H]; [left; reflexivity | right; apply (IH l m H)].
  Qed.

  Lemma crun_app : forall vm p q c, crun vm (p ++ q) c = crun vm q (crun vm p c).
  Proof. induction p as [| a p IH]; intros q c; [reflexivity |]. simpl. apply IH. Qed.

  Lemma cevs_app : forall p q, cevs (p ++ q) = cevs p ++ cevs q.
  Proof.
    induction p as [| a p IH]; intros q; [reflexivity |].
    destruct a; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma disc_app : forall vm p q c, disc vm (p ++ q) c <-> disc vm p c /\ disc vm q (crun vm p c).
  Proof.
    induction p as [| a p IH]; intros q c; simpl; [tauto |].
    rewrite IH. tauto.
  Qed.

  Lemma ok_capp : forall p q, Forall okc p -> Forall okc q -> Forall okc (p ++ q).
  Proof. intros p q Hp Hq. apply Forall_app. split; assumption. Qed.

  Lemma cevs_emb : forall w g, cevs (emb w g) = evsF w.
  Proof.
    induction w as [| a w IH]; intros g; [reflexivity |].
    destruct a as [e | j]; simpl; rewrite IH; reflexivity.
  Qed.

  Lemma ok_emb : forall w g, Forall okF w -> Forall okc (emb w g).
  Proof.
    induction w as [| a w IH]; intros g Hw; [constructor |].
    inversion Hw as [| ? ? Ha Hw']; subst.
    destruct a as [e | j]; simpl.
    - constructor; [exact Logic.I | apply IH; exact Hw'].
    - simpl in Ha. constructor; [exact Ha |]. constructor; [exact Ha | apply IH; exact Hw'].
  Qed.

  Lemma nth_error_in : forall (l : list msg) i m, nth_error l i = Some m -> In m l.
  Proof.
    induction l as [| x l IH]; intros [| i] m H; simpl in H; try discriminate.
    - injection H as <-. left. reflexivity.
    - right. exact (IH i m H).
  Qed.

  (* The version discipline keeps every version in flight at most the last one sent, and the
     last applied one too (both modes). *)
  Lemma vinv_step : forall vm a c, VInv c ->
    (match a with CSend j v => cv c j < v | _ => True end) -> VInv (cstep vm a c).
  Proof.
    intros vm a c Hv Ha. destruct a as [e | j v | j i | j i]; simpl.
    - exact Hv.
    - intros k. simpl. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite setb_eq, setn_eq. destruct (Hv j) as [Hl Hm]. split; [lia |].
        intros m [<- | Hin]; [simpl; lia |]. specialize (Hm m Hin). lia.
      + rewrite (setb_neq _ _ _ _ Ne), (setn_neq _ _ _ _ Ne). exact (Hv k).
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| exact Hv].
      assert (Hm : fst m <= cv c j) by (apply (proj2 (Hv j)); exact (nth_error_in _ _ _ Hn)).
      unfold merge. destruct (applies vm _ j m).
      + intros k. simpl. split.
        * destruct vm; [| apply (proj1 (Hv k))].
          destruct (Nat.eq_dec k j) as [-> | Ne]; [rewrite setn_eq; exact Hm |].
          rewrite (setn_neq _ _ _ _ Ne). apply (proj1 (Hv k)).
        * intros m' Hin. destruct (Nat.eq_dec k j) as [-> | Ne].
          -- rewrite setb_eq in Hin. apply (proj2 (Hv j)). exact (rmn_in _ _ _ Hin).
          -- rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (proj2 (Hv k)). exact Hin.
      + intros k. simpl. split; [apply (proj1 (Hv k)) |].
        intros m' Hin. destruct (Nat.eq_dec k j) as [-> | Ne].
        * rewrite setb_eq in Hin. apply (proj2 (Hv j)). exact (rmn_in _ _ _ Hin).
        * rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (proj2 (Hv k)). exact Hin.
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| exact Hv].
      assert (Hm : fst m <= cv c j) by (apply (proj2 (Hv j)); exact (nth_error_in _ _ _ Hn)).
      unfold merge. destruct (applies vm c j m); [| exact Hv].
      intros k. simpl. split; [| apply (proj2 (Hv k))].
      destruct vm; [| apply (proj1 (Hv k))].
      destruct (Nat.eq_dec k j) as [-> | Ne]; [rewrite setn_eq; exact Hm |].
      rewrite (setn_neq _ _ _ _ Ne). apply (proj1 (Hv k)).
  Qed.

  Lemma vinv_run : forall vm w c, VInv c -> disc vm w c -> VInv (crun vm w c).
  Proof.
    induction w as [| a w IH]; intros c Hv Hd; [exact Hv |].
    destruct Hd as [Ha Hd]. simpl. apply IH; [apply vinv_step; assumption | exact Hd].
  Qed.

  Lemma vinv_init : forall s, VInv (init s).
  Proof. intros s j. simpl. split; [lia | intros m []]. Qed.

  (* The embedding: a current-value run is a channel run whose sends are delivered at once, in
     either mode, with the discipline. No hypothesis on the federation. *)
  Lemma emb_run : forall vm w c, VInv c ->
    cs (crun vm (emb w (cv c)) c) = dF w (cs c) /\
    (forall k, cb (crun vm (emb w (cv c)) c) k = cb c k) /\
    disc vm (emb w (cv c)) c /\ VInv (crun vm (emb w (cv c)) c).
  Proof.
    induction w as [| a w IH]; intros c Hv.
    - simpl. split; [reflexivity |]. split; [reflexivity |]. split; [exact Logic.I | exact Hv].
    - destruct a as [e | j].
      + simpl. destruct (IH (Cfg (evF e (cs c)) (cb c) (cl c) (cv c)) Hv) as [A [B [C D]]].
        simpl in A, B, C, D. split; [exact A |]. split; [exact B |]. split; [| exact D].
        split; [exact Logic.I | exact C].
      + cbn [emb crun disc dF dstep].
        set (c1 := Cfg (cs c) (setb (cb c) j ((S (cv c j), cs c) :: cb c j)) (cl c)
                       (setn (cv c) j (S (cv c j)))).
        assert (Hn : nth_error (cb c1 j) 0 = Some (S (cv c j), cs c))
          by (unfold c1; simpl; rewrite setb_eq; reflexivity).
        assert (Ha : applies vm (Cfg (cs c1) (setb (cb c1) j (rmn 0 (cb c1 j))) (cl c1) (cv c1)) j
                       (S (cv c j), cs c) = true).
        { unfold applies. destruct vm; [| reflexivity]. simpl. apply Nat.ltb_lt.
          pose proof (proj1 (Hv j)). lia. }
        set (c2 := Cfg (updF (cs c) j (f j (cs c) (cs c j)))
                       (setb (cb c1) j (rmn 0 (cb c1 j)))
                       (if vm then setn (cl c) j (S (cv c j)) else cl c) (setn (cv c) j (S (cv c j)))).
        assert (E2 : cstep vm (CDel j 0) c1 = c2).
        { unfold cstep. rewrite Hn. unfold merge. rewrite Ha. reflexivity. }
        assert (Hv1 : VInv c1) by (apply (vinv_step vm (CSend j (S (cv c j))) c Hv); simpl; lia).
        assert (Hv2 : VInv c2) by (rewrite <- E2; apply (vinv_step vm (CDel j 0) c1 Hv1); exact Logic.I).
        change (cstep vm (CSend j (S (cv c j))) c) with c1. rewrite E2.
        destruct (IH c2 Hv2) as [A [B [C D]]].
        assert (Cv : cv c2 = setn (cv c) j (S (cv c j))) by reflexivity.
        rewrite Cv in A, B, C, D.
        split; [rewrite A; reflexivity |].
        split.
        { intros k. rewrite B. unfold c2. simpl. unfold c1. simpl.
          destruct (Nat.eq_dec k j) as [-> | Ne].
          - rewrite !setb_eq. reflexivity.
          - rewrite !(setb_neq _ _ _ _ Ne). reflexivity. }
        split; [| exact D].
        split; [simpl; lia |]. split; [exact Logic.I | exact C].
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* The final round computes the current-value flush.                                   *)
  (* ---------------------------------------------------------------------------------- *)

  Fixpoint ndp (l : list nat) : Prop :=
    match l with [] => True | a :: r => ~ In a r /\ ndp r end.

  Lemma topo_ndp : forall l, topoF src l -> ndp l.
  Proof.
    induction l as [| a l IH]; intros H; [exact Logic.I |].
    destruct H as [Ha [_ Hr]]. split; [exact Ha | apply IH; exact Hr].
  Qed.

  Lemma frnd_ext : forall l g g', (forall k, In k l -> g k = g' k) -> frnd l g = frnd l g'.
  Proof.
    induction l as [| a l IH]; intros g g' H; [reflexivity |]. simpl.
    rewrite (H a (or_introl eq_refl)). rewrite (IH g g'); [reflexivity |].
    intros k Hk. apply H. right. exact Hk.
  Qed.

  Lemma frnd_run : forall vm l c, ndp l -> (vm = true -> forall k, In k l -> cl c k <= cv c k) ->
    cs (crun vm (frnd l (cv c)) c) = frF l (cs c) /\
    (forall k, cb (crun vm (frnd l (cv c)) c) k = cb c k) /\
    (forall k, In k l -> vm = true -> cl (crun vm (frnd l (cv c)) c) k = S (cv c k)) /\
    (forall k, ~ In k l -> cl (crun vm (frnd l (cv c)) c) k = cl c k) /\
    (forall k, vm = false -> cl (crun vm (frnd l (cv c)) c) k = cl c k) /\
    (forall k, In k l -> cv (crun vm (frnd l (cv c)) c) k = S (cv c k)) /\
    (forall k, ~ In k l -> cv (crun vm (frnd l (cv c)) c) k = cv c k) /\
    disc vm (frnd l (cv c)) c.
  Proof.
    induction l as [| j l IH]; intros c Hn Hl.
    - simpl. repeat split; intros; try reflexivity; try contradiction.
    - destruct Hn as [Hj Hn]. cbn [frnd crun disc].
      set (c1 := Cfg (cs c) (setb (cb c) j ((S (cv c j), cs c) :: cb c j)) (cl c)
                     (setn (cv c) j (S (cv c j)))).
      assert (Hnth : nth_error (cb c1 j) 0 = Some (S (cv c j), cs c))
        by (unfold c1; simpl; rewrite setb_eq; reflexivity).
      assert (Ha : applies vm (Cfg (cs c1) (setb (cb c1) j (rmn 0 (cb c1 j))) (cl c1) (cv c1)) j
                     (S (cv c j), cs c) = true).
      { unfold applies. destruct vm; [| reflexivity]. simpl. apply Nat.ltb_lt.
        pose proof (Hl eq_refl j (or_introl eq_refl)). lia. }
      set (c2 := Cfg (updF (cs c) j (f j (cs c) (cs c j)))
                     (setb (cb c1) j (rmn 0 (cb c1 j)))
                     (if vm then setn (cl c) j (S (cv c j)) else cl c) (setn (cv c) j (S (cv c j)))).
      assert (E2 : cstep vm (CDel j 0) c1 = c2).
      { unfold cstep. rewrite Hnth. unfold merge. rewrite Ha. reflexivity. }
      change (cstep vm (CSend j (S (cv c j))) c) with c1. rewrite E2.
      assert (Fr : frnd l (cv c) = frnd l (cv c2)).
      { apply frnd_ext. intros k Hk. unfold c2. simpl. rewrite setn_neq; [reflexivity |].
        intro E'. subst. contradiction. }
      assert (Hl2 : vm = true -> forall k, In k l -> cl c2 k <= cv c2 k).
      { intros Hvm k Hk. assert (Nk : k <> j) by (intro E'; subst; contradiction).
        unfold c2. simpl. rewrite (setn_neq _ _ _ _ Nk).
        destruct vm; [rewrite (setn_neq _ _ _ _ Nk) |]; apply Hl; try exact Hvm; right; exact Hk. }
      rewrite Fr. destruct (IH c2 Hn Hl2) as [A [B [C [D [D' [F [G H]]]]]]].
      split; [rewrite A; reflexivity |].
      split.
      { intros k. rewrite B. unfold c2, c1. simpl. destruct (Nat.eq_dec k j) as [-> | Ne].
        - rewrite !setb_eq. reflexivity.
        - rewrite !(setb_neq _ _ _ _ Ne). reflexivity. }
      split.
      { intros k [<- | Hk] Hvm.
        - rewrite (D j Hj). unfold c2. simpl. subst vm. rewrite setn_eq. reflexivity.
        - rewrite (C k Hk Hvm). unfold c2. simpl. rewrite setn_neq; [reflexivity |].
          intro E'. subst. contradiction. }
      split.
      { intros k Hk. assert (Nk : k <> j) by (intro E'; apply Hk; left; symmetry; exact E').
        assert (Nl : ~ In k l) by (intro H'; apply Hk; right; exact H').
        rewrite (D k Nl). unfold c2. simpl. destruct vm; [apply setn_neq; exact Nk | reflexivity]. }
      split.
      { intros k Hvm. rewrite (D' k Hvm). unfold c2. simpl. subst vm. reflexivity. }
      split.
      { intros k [<- | Hk].
        - rewrite (G j Hj). unfold c2. simpl. rewrite setn_eq. reflexivity.
        - rewrite (F k Hk). unfold c2. simpl. rewrite setn_neq; [reflexivity |].
          intro E'. subst. contradiction. }
      split.
      { intros k Hk. assert (Nk : k <> j) by (intro E'; apply Hk; left; symmetry; exact E').
        assert (Nl : ~ In k l) by (intro H'; apply Hk; right; exact H').
        rewrite (G k Nl). unfold c2. simpl. apply setn_neq. exact Nk. }
      split; [unfold c1; simpl; lia |]. split; [exact Logic.I | exact H].
  Qed.

  Section WithCommon.
  Hypothesis HC : Common V src f valid rho E reg sig o.

  Lemma o_ndp : ndp o.
  Proof. apply topo_ndp. exact (c_topo _ _ _ _ _ _ _ _ _ HC). Qed.

  Lemma fround_run : forall vm c, (vm = true -> VInv c) ->
    cs (crun vm (fround c) c) = frF o (cs c) /\
    (forall k, cb (crun vm (fround c) c) k = cb c k) /\
    (forall k, In k o -> vm = true -> cl (crun vm (fround c) c) k = S (cv c k)) /\
    (forall k, In k o -> cv (crun vm (fround c) c) k = S (cv c k)) /\
    disc vm (fround c) c.
  Proof.
    intros vm c Hv. unfold fround.
    destruct (frnd_run vm o c o_ndp (fun Hvm k _ => proj1 (Hv Hvm k))) as [A [B [C [_ [_ [F [_ H]]]]]]].
    repeat split; assumption.
  Qed.

  Lemma ok_frnd : forall l g, (forall k, In k l -> In k o) -> Forall okc (frnd l g).
  Proof.
    induction l as [| a l IH]; intros g H; [constructor |]. simpl.
    constructor; [apply H; left; reflexivity |]. constructor; [apply H; left; reflexivity |].
    apply IH. intros k Hk. apply H. right. exact Hk.
  Qed.

  Lemma ok_fround : forall c, Forall okc (fround c).
  Proof. intros c. apply ok_frnd. intros k Hk. exact Hk. Qed.

  Lemma cevs_frnd : forall l g, cevs (frnd l g) = [].
  Proof. induction l as [| a l IH]; intros g; [reflexivity | simpl; apply IH]. Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Validity.                                                                           *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma cinv_step : forall vm a c, CInv c -> CInv (cstep vm a c).
  Proof.
    intros vm a c [Hs Hb]. destruct a as [e | j v | j i | j i]; simpl.
    - split; [apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact Hs | exact Hb].
    - split; [exact Hs |]. intros k m Hin. simpl in Hin. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite setb_eq in Hin. destruct Hin as [<- | Hin]; [exact Hs | apply (Hb j m Hin)].
      + rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (Hb k m Hin).
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| split; assumption].
      assert (Hz : InvF (snd m)) by (apply (Hb j m); exact (nth_error_in _ _ _ Hn)).
      assert (Hb' : forall k m', In m' (setb (cb c) j (rmn i (cb c j)) k) -> InvF (snd m')).
      { intros k m' Hin. destruct (Nat.eq_dec k j) as [-> | Ne].
        - rewrite setb_eq in Hin. apply (Hb j m'). exact (rmn_in _ _ _ Hin).
        - rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (Hb k m' Hin). }
      unfold merge. destruct (applies vm _ j m); cbn [cs cb cl cv]; [| split; assumption].
      split; [| exact Hb'].
      intros k. change (valid k (updF (cs c) j (f j (snd m) (cs c j)) k)).
      destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite updF_eq. apply (c_m1 _ _ _ _ _ _ _ _ _ HC); [exact Hz | apply Hs].
      + rewrite (updF_neq _ _ _ _ Ne). apply Hs.
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| split; assumption].
      assert (Hz : InvF (snd m)) by (apply (Hb j m); exact (nth_error_in _ _ _ Hn)).
      unfold merge. destruct (applies vm c j m); cbn [cs cb cl cv]; [| split; assumption].
      split; [| exact Hb].
      intros k. change (valid k (updF (cs c) j (f j (snd m) (cs c j)) k)).
      destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite updF_eq. apply (c_m1 _ _ _ _ _ _ _ _ _ HC); [exact Hz | apply Hs].
      + rewrite (updF_neq _ _ _ _ Ne). apply Hs.
  Qed.

  Lemma cinv_run : forall vm w c, CInv c -> CInv (crun vm w c).
  Proof.
    induction w as [| a w IH]; intros c H; [exact H |]. simpl. apply IH. apply cinv_step. exact H.
  Qed.

  Lemma cinv_init : forall s, InvF s -> CInv (init s).
  Proof. intros s H. split; [exact H | intros j m []]. Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Flushing: a merge of ANY valid snapshot is erased by the flush.                     *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma flush_merge : forall j z t, In j o -> InvF t -> InvF z ->
    feqF (nF (updF t j (f j z (t j)))) (nF t).
  Proof.
    intros j z t Hj Ht Hz. pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as To.
    set (t1 := updF t j (f j z (t j))).
    assert (I1 : InvF t1).
    { intros k. unfold t1. destruct (Nat.eq_dec k j) as [-> | Ne].
      - rewrite updF_eq. apply (c_m1 _ _ _ _ _ _ _ _ _ HC); [exact Hz | apply Ht].
      - rewrite (updF_neq _ _ _ _ Ne). apply Ht. }
    eapply feq_trans; [apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact I1 |].
    eapply feq_trans; [| apply feq_sym, (N_frun _ _ _ _ _ _ _ _ _ HC); exact Ht].
    assert (Iz : InvF (frF o t1)) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact I1).
    apply (solve_unique _ _ _ _ _ _ _ _ _ HC o _ _ t1 t To).
    - intros k Hk. rewrite !(frun_out V f) by exact Hk. unfold t1.
      apply updF_neq. intro E'. subst. contradiction.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros k Hk. unfold t1. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite updF_eq. apply (c_absorb _ _ _ _ _ _ _ _ _ HC); [exact Iz | exact Hz | apply Ht].
      + rewrite (updF_neq _ _ _ _ Ne). reflexivity.
  Qed.

  Lemma cstep_flush : forall vm a c, CInv c -> okc a ->
    (forall e, a = CEv e -> XUatF (cs c) e) ->
    feqF (nF (cs (cstep vm a c))) (rF (cevs [a]) (nF (cs c))).
  Proof.
    intros vm a c [Hs Hb] Ha Hx. destruct a as [e | j v | j i | j i]; simpl.
    - apply (flush_ev_at _ _ _ _ _ _ _ _ _ HC); [exact Hs | apply Hx; reflexivity].
    - intro k. reflexivity.
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| intro k; reflexivity].
      assert (Hz : InvF (snd m)) by (apply (Hb j m); exact (nth_error_in _ _ _ Hn)).
      unfold merge. destruct (applies vm _ j m); simpl; [| intro k; reflexivity].
      apply flush_merge; assumption.
    - destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| intro k; reflexivity].
      assert (Hz : InvF (snd m)) by (apply (Hb j m); exact (nth_error_in _ _ _ Hn)).
      unfold merge. destruct (applies vm c j m); simpl; [| intro k; reflexivity].
      apply flush_merge; assumption.
  Qed.

  (* Every channel run flushes to the FedMachine run of its events, given XU at the states where
     its events fire (any delivery order, duplicates, either merge mode). *)
  Lemma crun_flush : forall vm w c, CInv c -> Forall okc w ->
    (forall q r e, w = q ++ r -> XUatF (cs (crun vm q c)) e) ->
    feqF (nF (cs (crun vm w c))) (rF (cevs w) (nF (cs c))).
  Proof.
    induction w as [| a w IH]; intros c Hc Hw Hx; [intro k; reflexivity |].
    inversion Hw as [| ? ? Ha Hw']; subst. cbn [crun].
    assert (Hc1 : CInv (cstep vm a c)) by (apply cinv_step; exact Hc).
    eapply feq_trans.
    { apply (IH (cstep vm a c) Hc1 Hw'). intros q r e Hq.
      exact (Hx (a :: q) r e ltac:(rewrite Hq; reflexivity)). }
    replace (cevs (a :: w)) with (cevs [a] ++ cevs w) by (rewrite <- cevs_app; reflexivity).
    rewrite (runF_app _ _ _ _ _ _ _ (cevs [a]) (cevs w)).
    apply (runF_ext _ _ _ _ _ _ _ _ _ HC).
    apply cstep_flush; [exact Hc | exact Ha |].
    intros e Ea. subst a. exact (Hx [] (CEv e :: w) e eq_refl).
  Qed.
  End WithCommon.

  (* Reachable XU over channel runs, and channel convergence (compared after a final flush, as
     DistConv does). Runs keep the version discipline in either mode (for the plain mode versions
     are ignored, so this restricts nothing). *)
  Definition CXUR (vm : bool) (s0 : nat -> V) : Prop :=
    forall p e, Forall okc p -> disc vm p (init s0) -> XUatF (cs (crun vm p (init s0))) e.

  Definition ChanConv (vm : bool) (s0 : nat -> V) : Prop :=
    forall w1 w2, Forall okc w1 -> Forall okc w2 -> disc vm w1 (init s0) -> disc vm w2 (init s0) ->
      tequiv IfedF (cevs w1) (cevs w2) ->
      feqF (nF (cs (crun vm w1 (init s0)))) (nF (cs (crun vm w2 (init s0)))).


  (* Converging at drain, with no flush from outside: versioned runs completed by a final round
     and then any drain. *)
  Definition SettleConv (s0 : nat -> V) : Prop :=
    forall w1 w2 d1 d2, Forall okc w1 -> Forall okc w2 ->
      disc true w1 (init s0) -> disc true w2 (init s0) ->
      Forall isdrain d1 -> Forall isdrain d2 -> tequiv IfedF (cevs w1) (cevs w2) ->
      feqF (cs (crun true (w1 ++ fround (crun true w1 (init s0)) ++ d1) (init s0)))
           (cs (crun true (w2 ++ fround (crun true w2 (init s0)) ++ d2) (init s0))).

  Lemma in_nth : forall (l : list msg) m, In m l -> exists i, nth_error l i = Some m.
  Proof.
    induction l as [| x l IH]; intros m H; [destruct H |].
    destruct H as [<- | H]; [exists 0; reflexivity |].
    destruct (IH m H) as [i Hi]. exists (S i). exact Hi.
  Qed.

  Lemma topo_noself : forall l j, topoF src l -> In j l -> ~ In j (src j).
  Proof.
    induction l as [| a l IH]; intros j Ht Hj; [destruct Hj |].
    destruct Ht as [_ [Hs Hr]]. destruct Hj as [<- | Hj].
    - intro H. exact (Hs a H (or_introl eq_refl)).
    - exact (IH j Hr Hj).
  Qed.

  Section Exact.
  Hypothesis HC : Common V src f valid rho E reg sig o.

  Lemma cons_feq : forall t t', feqF t t' -> ConsF t -> ConsF t'.
  Proof.
    intros t t' H Hc j Hj. rewrite <- (H j). rewrite (Hc j Hj) at 1.
    apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k _. apply H.
  Qed.

  Lemma frun_cons : forall t, InvF t -> ConsF (frF o t).
  Proof.
    intros t Ht. apply (cons_feq (nF t)); [apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact Ht |].
    apply (N_cons _ _ _ _ _ _ _ _ _ HC). exact Ht.
  Qed.

  Lemma xuat_feq : forall t t' e, feqF t t' -> XUatF t e -> XUatF t' e.
  Proof.
    intros t t' e H X. unfold XUat in *.
    assert (Hn : feqF (nF t) (nF t')) by (apply (N_ext _ _ _ _ _ _ _ _ _ HC); exact H).
    rewrite <- !(f_ext _ _ _ _ _ _ _ _ _ HC (reg e) _ _ _ Hn). rewrite <- (H (reg e)). exact X.
  Qed.

  (* The current-value model is the special case of immediate delivery, in either mode. *)
  Lemma cxur_xur : forall vm s0, CXUR vm s0 -> XURF s0.
  Proof.
    intros vm s0 Hx p e Hp.
    destruct (emb_run vm p (init s0) (vinv_init s0)) as [A [_ [D _]]].
    pose proof (Hx (emb p (cv (init s0))) e (ok_emb p _ Hp) D) as X.
    rewrite A in X. exact X.
  Qed.

  Lemma chan_dist : forall vm s0, ChanConv vm s0 -> DistConvF s0.
  Proof.
    intros vm s0 Hc w1 w2 H1 H2 Ht.
    destruct (emb_run vm w1 (init s0) (vinv_init s0)) as [A1 [_ [D1 _]]].
    destruct (emb_run vm w2 (init s0) (vinv_init s0)) as [A2 [_ [D2 _]]].
    assert (Ht' : tequiv IfedF (cevs (emb w1 (cv (init s0)))) (cevs (emb w2 (cv (init s0)))))
      by (rewrite !cevs_emb; exact Ht).
    pose proof (Hc _ _ (ok_emb w1 _ H1) (ok_emb w2 _ H2) D1 D2 Ht') as X.
    rewrite A1, A2 in X. exact X.
  Qed.

  Lemma ok_prefix : forall vm s0 w q r, w = q ++ r -> Forall okc w -> disc vm w (init s0) ->
    Forall okc q /\ disc vm q (init s0).
  Proof.
    intros vm s0 w q r -> Hw Hd. apply Forall_app in Hw. apply disc_app in Hd. tauto.
  Qed.

  (* Under reachable XU over channel runs, every channel run flushes to the FedMachine run of
     its events from the flushed start. *)
  Theorem chan_flush : forall vm s0, InvF s0 -> CXUR vm s0 ->
    forall w, Forall okc w -> disc vm w (init s0) ->
      feqF (nF (cs (crun vm w (init s0)))) (rF (cevs w) (nF s0)).
  Proof.
    intros vm s0 Hi Hx w Hw Hd. apply (crun_flush HC vm w (init s0) (cinv_init s0 Hi) Hw).
    intros q r e Hq. destruct (ok_prefix vm s0 w q r Hq Hw Hd) as [Hq1 Hq2]. exact (Hx q e Hq1 Hq2).
  Qed.

  (* The two runs whose flushes are the two sides of XU at a channel-reachable state: "event"
     and "final round, then event". *)
  Lemma chan_xur_nec : forall vm s0, InvF s0 -> ChanConv vm s0 -> CXUR vm s0.
  Proof.
    intros vm s0 Hi Hc p e Hp Hd. set (c := crun vm p (init s0)). set (t := cs c).
    assert (Hv : VInv c) by (apply vinv_run; [apply vinv_init | exact Hd]).
    assert (It : InvF t) by (apply (cinv_run HC vm p (init s0) (cinv_init s0 Hi))).
    destruct (fround_run HC vm c (fun _ => Hv)) as [Fc [_ [_ [_ Fd]]]].
    set (w1 := p ++ [CEv e]). set (w2 := p ++ fround c ++ [CEv e]).
    assert (S1 : cs (crun vm w1 (init s0)) = evF e t)
      by (unfold w1; rewrite crun_app; reflexivity).
    assert (S2 : cs (crun vm w2 (init s0)) = evF e (frF o t)).
    { unfold w2. rewrite crun_app. fold c. rewrite crun_app. simpl. rewrite Fc. reflexivity. }
    assert (O1 : Forall okc w1) by (apply ok_capp; [exact Hp | repeat constructor]).
    assert (O2 : Forall okc w2)
      by (apply ok_capp; [exact Hp | apply ok_capp; [apply ok_fround | repeat constructor]]).
    assert (D1 : disc vm w1 (init s0))
      by (apply disc_app; split; [exact Hd | simpl; tauto]).
    assert (D2 : disc vm w2 (init s0)).
    { apply disc_app. split; [exact Hd |]. fold c. apply disc_app. split; [exact Fd | simpl; tauto]. }
    assert (Ev : cevs w1 = cevs w2).
    { unfold w1, w2. rewrite !cevs_app. unfold fround. rewrite cevs_frnd. reflexivity. }
    pose proof (Hc w1 w2 O1 O2 D1 D2 (eq_rect _ (fun l => tequiv IfedF (cevs w1) l)
                                         (teq_refl IfedF _) _ Ev) (reg e)) as H.
    rewrite S1, S2 in H.
    assert (Re : In (reg e) o) by exact (c_reg _ _ _ _ _ _ _ _ _ HC e).
    assert (Ifr : InvF (frF o t)) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact It).
    assert (Fr : feqF (frF o t) (nF t))
      by (apply feq_sym; apply (N_frun _ _ _ _ _ _ _ _ _ HC); exact It).
    assert (In_ : InvF (nF t)) by (apply (N_inv _ _ _ _ _ _ _ _ _ HC); exact It).
    assert (Nn : feqF (nF (frF o t)) (nF t)).
    { eapply feq_trans; [apply (N_ext _ _ _ _ _ _ _ _ _ HC); exact Fr |].
      apply (N_self _ _ _ _ _ _ _ _ _ HC); [exact In_ | apply (N_cons _ _ _ _ _ _ _ _ _ HC); exact It]. }
    rewrite (N_ev_at _ _ _ _ _ _ _ _ _ HC e t It) in H.
    rewrite (N_ev_at _ _ _ _ _ _ _ _ _ HC e _ Ifr) in H.
    rewrite (f_ext _ _ _ _ _ _ _ _ _ HC _ _ _ _ Nn) in H. rewrite (Fr (reg e)) in H.
    rewrite (N_at _ _ _ _ _ _ _ _ _ HC t (reg e) It Re) in H.
    unfold XUat. symmetry. exact H.
  Qed.

  (* Headline: the exact condition for propagation over channels, in either merge mode, compared
     after a final flush: reachable XU over CHANNEL-reachable states, plus the FedMachine's C2
     from the flushed start. *)
  Theorem chan_exact : forall vm s0, InvF s0 ->
    (ChanConv vm s0 <-> CXUR vm s0 /\ C2Rf (nF s0)).
  Proof.
    intros vm s0 Hi. split.
    - intros Hc. split; [apply chan_xur_nec; assumption |].
      exact (proj2 (proj1 (dist_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi) (chan_dist vm s0 Hc))).
    - intros [Hx H2].
      assert (Hxr : XURF s0) by exact (cxur_xur vm s0 Hx).
      assert (Hd : DistConvF s0)
        by (apply (proj2 (dist_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi)); split; assumption).
      assert (Ht : TC (nF s0)) by exact (proj2 (proj1 (dist_exact_tc _ _ _ _ _ _ _ _ _ _ HC s0 Hi) Hd)).
      intros w1 w2 H1 H2' D1 D2 Hq.
      eapply feq_trans; [exact (chan_flush vm s0 Hi Hx w1 H1 D1) |].
      eapply feq_trans; [exact (Ht _ _ Hq) | apply feq_sym; exact (chan_flush vm s0 Hi Hx w2 H2' D2)].
  Qed.

  (* Every valid start: the same condition as the current-value model, in either mode. *)
  Theorem chan_exact_global : forall vm,
    (forall s0, InvF s0 -> ChanConv vm s0) <->
    XUG V f valid rho E reg sig o /\ C2G V f valid E reg sig I o.
  Proof.
    intros vm. rewrite <- (dist_exact_global _ _ _ _ _ _ _ _ _ _ HC). split.
    - intros H s0 Hi. exact (chan_dist vm s0 (H s0 Hi)).
    - intros H s0 Hi. destruct (proj1 (dist_exact_global _ _ _ _ _ _ _ _ _ _ HC) H) as [Hx H2].
      apply (proj2 (chan_exact vm s0 Hi)). split.
      + intros p e _ _. apply Hx. exact (proj1 (cinv_run HC vm p (init s0) (cinv_init s0 Hi))).
      + exact (c2g_c2r _ _ _ _ _ _ _ _ _ _ HC H2 s0 Hi).
  Qed.

  (* When every target's sources are roots (any two-registry federation, any star): gsm's static
     XU + C2 is exact for channels too, for every valid start, in either merge mode. *)
  Theorem chan_global_exact_roots : forall vm, RootSrc V src f E reg ->
    ((forall s0, InvF s0 -> ChanConv vm s0) <-> XU V f valid E reg sig /\ C2 V f valid E reg sig I).
  Proof.
    intros vm HR. rewrite <- (dist_global_exact_roots _ _ _ _ _ _ _ _ _ _ HC HR).
    rewrite (chan_exact_global vm). rewrite (dist_exact_global _ _ _ _ _ _ _ _ _ _ HC). reflexivity.
  Qed.

  Theorem chan_xu_c2 : XU V f valid E reg sig -> C2 V f valid E reg sig I ->
    forall vm s0, InvF s0 -> ChanConv vm s0.
  Proof.
    intros HX H2 vm s0 Hi. apply (proj2 (chan_exact vm s0 Hi)). split.
    - intros p e _ _. unfold XUat. apply HX.
      + apply (N_inv _ _ _ _ _ _ _ _ _ HC). exact (proj1 (cinv_run HC vm p (init s0) (cinv_init s0 Hi))).
      + exact (proj1 (cinv_run HC vm p (init s0) (cinv_init s0 Hi)) (reg e)).
    - apply (static_c2_reach _ _ _ _ _ _ _ _ _ _ HC H2);
        [apply (N_inv _ _ _ _ _ _ _ _ _ HC) | apply (N_cons _ _ _ _ _ _ _ _ _ HC)]; exact Hi.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Versioned merge: the channels deliver the flush themselves.                         *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma drain_refused : forall d c, Forall isdrain d ->
    (forall j m, In j o -> In m (cb c j) -> fst m < cl c j) -> cs (crun true d c) = cs c.
  Proof.
    induction d as [| a d IH]; intros c Hd Hc; [reflexivity |].
    inversion Hd as [| ? ? Ha Hd']; subst. simpl.
    destruct a as [e | j v | j i | j i]; simpl in Ha; try contradiction.
    - unfold cstep. destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| apply IH; assumption].
      assert (Ap : applies true (Cfg (cs c) (setb (cb c) j (rmn i (cb c j))) (cl c) (cv c)) j m = false).
      { unfold applies. simpl. apply Nat.ltb_ge. pose proof (Hc j m Ha (nth_error_in _ _ _ Hn)). lia. }
      unfold merge. rewrite Ap. rewrite IH; [reflexivity | exact Hd' |].
      intros k m' Hk Hin. simpl in *. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite setb_eq in Hin. apply (Hc j m' Hk). exact (rmn_in _ _ _ Hin).
      + rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (Hc k m' Hk Hin).
    - unfold cstep. destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| apply IH; assumption].
      assert (Ap : applies true c j m = false).
      { unfold applies. apply Nat.ltb_ge. pose proof (Hc j m Ha (nth_error_in _ _ _ Hn)). lia. }
      unfold merge. rewrite Ap. apply IH; assumption.
  Qed.

  (* After the final round every projection still in flight is stale and refused: the drained
     state is the current-value flush of the state the run reached, whatever the drain does. *)
  Theorem vsettle : forall c d, VInv c -> Forall isdrain d ->
    cs (crun true (fround c ++ d) c) = frF o (cs c).
  Proof.
    intros c d Hv Hd. rewrite crun_app.
    destruct (fround_run HC true c (fun _ => Hv)) as [A [B [C [_ _]]]].
    rewrite drain_refused; [exact A | exact Hd |].
    intros j m Hj Hin. rewrite B in Hin. rewrite (C j Hj eq_refl).
    pose proof (proj2 (Hv j) m Hin). lia.
  Qed.

  Theorem vsettle_settled : forall s0 w d, InvF s0 -> disc true w (init s0) -> Forall isdrain d ->
    ConsF (cs (crun true (w ++ fround (crun true w (init s0)) ++ d) (init s0))).
  Proof.
    intros s0 w d Hi Hd Hdr. rewrite crun_app.
    rewrite vsettle; [| apply vinv_run; [apply vinv_init | exact Hd] | exact Hdr].
    apply frun_cons. exact (proj1 (cinv_run HC true w (init s0) (cinv_init s0 Hi))).
  Qed.

  (* Converging at drain is exactly converging after a flush: the versioned channels need no
     outside flush. *)
  Theorem vsettle_exact : forall s0, InvF s0 -> (SettleConv s0 <-> ChanConv true s0).
  Proof.
    intros s0 Hi.
    assert (Fin : forall w d, disc true w (init s0) -> Forall isdrain d ->
              feqF (cs (crun true (w ++ fround (crun true w (init s0)) ++ d) (init s0)))
                   (nF (cs (crun true w (init s0))))).
    { intros w d Hd Hdr. rewrite crun_app.
      rewrite vsettle; [| apply vinv_run; [apply vinv_init | exact Hd] | exact Hdr].
      apply feq_sym. apply (N_frun _ _ _ _ _ _ _ _ _ HC).
      exact (proj1 (cinv_run HC true w (init s0) (cinv_init s0 Hi))). }
    split.
    - intros Hs w1 w2 H1 H2 D1 D2 Hq.
      pose proof (Hs w1 w2 [] [] H1 H2 D1 D2 ltac:(constructor) ltac:(constructor) Hq) as X.
      eapply feq_trans; [apply feq_sym; apply (Fin w1 []); [exact D1 | constructor] |].
      eapply feq_trans; [exact X | apply (Fin w2 []); [exact D2 | constructor]].
    - intros Hc w1 w2 d1 d2 H1 H2 D1 D2 R1 R2 Hq.
      eapply feq_trans; [apply (Fin w1 d1 D1 R1) |].
      eapply feq_trans; [exact (Hc w1 w2 H1 H2 D1 D2 Hq) | apply feq_sym; apply (Fin w2 d2 D2 R2)].
  Qed.

  (* Headline (versioned): converging at drain, exactly. *)
  Theorem vsettle_exact_cond : forall s0, InvF s0 ->
    (SettleConv s0 <-> CXUR true s0 /\ C2Rf (nF s0)).
  Proof. intros s0 Hi. rewrite (vsettle_exact s0 Hi). apply chan_exact. exact Hi. Qed.

  (* The drained state is the state of a current-value run: the same events, then a flush. *)
  Theorem vsettle_cv : forall s0 w d, InvF s0 -> CXUR true s0 ->
    Forall okc w -> disc true w (init s0) -> Forall isdrain d ->
    feqF (cs (crun true (w ++ fround (crun true w (init s0)) ++ d) (init s0)))
         (dF (map DE (cevs w) ++ map DP o) s0).
  Proof.
    intros s0 w d Hi Hx Hw Hd Hdr. rewrite crun_app.
    rewrite vsettle; [| apply vinv_run; [apply vinv_init | exact Hd] | exact Hdr].
    eapply feq_trans; [apply feq_sym; apply (N_frun _ _ _ _ _ _ _ _ _ HC);
                       exact (proj1 (cinv_run HC true w (init s0) (cinv_init s0 Hi))) |].
    eapply feq_trans; [exact (chan_flush true s0 Hi Hx w Hw Hd) |].
    apply feq_sym. apply (reach_flush _ _ _ _ _ _ _ _ _ HC s0 Hi). exact (cxur_xur true s0 Hx).
  Qed.

  (* XU (gsm's ProjectionSafe) and C2 (Build) give convergence at drain for versioned channels. *)
  Theorem vsettle_xu_c2 : XU V f valid E reg sig -> C2 V f valid E reg sig I ->
    forall s0, InvF s0 -> SettleConv s0.
  Proof.
    intros HX H2 s0 Hi. apply (proj2 (vsettle_exact_cond s0 Hi)). split.
    - intros p e _ _. unfold XUat. apply HX.
      + apply (N_inv _ _ _ _ _ _ _ _ _ HC). exact (proj1 (cinv_run HC true p (init s0) (cinv_init s0 Hi))).
      + exact (proj1 (cinv_run HC true p (init s0) (cinv_init s0 Hi)) (reg e)).
    - apply (static_c2_reach _ _ _ _ _ _ _ _ _ _ HC H2);
        [apply (N_inv _ _ _ _ _ _ _ _ _ HC) | apply (N_cons _ _ _ _ _ _ _ _ _ HC)]; exact Hi.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Plain merge: the drain settles exactly when nothing stale is in flight.             *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma drain_plain : forall d c T, Forall isdrain d -> feqF (cs c) T ->
    (forall j m, In j o -> In m (cb c j) -> f j (snd m) (T j) = T j) ->
    feqF (cs (crun false d c)) T.
  Proof.
    induction d as [| a d IH]; intros c T Hd Hs Hc; [exact Hs |].
    inversion Hd as [| ? ? Ha Hd']; subst. simpl.
    destruct a as [e | j v | j i | j i]; simpl in Ha; try contradiction.
    - unfold cstep. destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| apply IH; assumption].
      pose proof (Hc j m Ha (nth_error_in _ _ _ Hn)) as Hm.
      unfold merge, applies. apply IH; [exact Hd' | |].
      + intros k. simpl. destruct (Nat.eq_dec k j) as [-> | Ne].
        * rewrite updF_eq. rewrite (Hs j). exact Hm.
        * rewrite (updF_neq _ _ _ _ Ne). apply Hs.
      + intros k m' Hk Hin. simpl in Hin. destruct (Nat.eq_dec k j) as [-> | Ne].
        * rewrite setb_eq in Hin. apply (Hc j m' Hk). exact (rmn_in _ _ _ Hin).
        * rewrite (setb_neq _ _ _ _ Ne) in Hin. apply (Hc k m' Hk Hin).
    - unfold cstep. destruct (nth_error (cb c j) i) as [m |] eqn:Hn; [| apply IH; assumption].
      pose proof (Hc j m Ha (nth_error_in _ _ _ Hn)) as Hm.
      unfold merge, applies. apply IH; [exact Hd' | | exact Hc].
      intros k. simpl. destruct (Nat.eq_dec k j) as [-> | Ne].
      + rewrite updF_eq. rewrite (Hs j). exact Hm.
      + rewrite (updF_neq _ _ _ _ Ne). apply Hs.
  Qed.

  (* Headline (plain): after the final round, every drain settles iff every projection still in
     flight carries the image of the flushed state. A stale image in flight is enough to break
     it, whatever XU says. *)
  Theorem plain_settle_iff : forall c, CInv c ->
    (forall d, Forall isdrain d -> ConsF (cs (crun false (fround c ++ d) c))) <->
    (forall j m, In j o -> In m (cb c j) -> f j (snd m) (frF o (cs c) j) = frF o (cs c) j).
  Proof.
    intros c [Hs Hb].
    destruct (fround_run HC false c (fun H => ltac:(discriminate H))) as [A [B _]].
    set (T := frF o (cs c)).
    assert (IT : InvF T) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact Hs).
    assert (CT : ConsF T) by (apply frun_cons; exact Hs).
    split.
    - intros H j m Hj Hin. destruct (in_nth (cb c j) m Hin) as [i Hi].
      assert (Hd : Forall isdrain [CDel j i]) by (repeat constructor; exact Hj).
      pose proof (H [CDel j i] Hd j Hj) as X. rewrite crun_app in X. simpl in X.
      rewrite B, Hi in X. unfold merge, applies in X. simpl in X. fold T in X. rewrite A in X.
      fold T in X. rewrite updF_eq in X. rewrite X at 1.
      assert (Iz : InvF (snd m)) by exact (Hb j m Hin).
      assert (It1 : InvF (updF T j (f j (snd m) (T j)))).
      { intros k. destruct (Nat.eq_dec k j) as [-> | Ne].
        - rewrite updF_eq. apply (c_m1 _ _ _ _ _ _ _ _ _ HC); [exact Iz | apply IT].
        - rewrite (updF_neq _ _ _ _ Ne). apply IT. }
      rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC); [| exact It1 | exact Iz | apply IT].
      transitivity (f j T (T j)); [| symmetry; exact (CT j Hj)].
      apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk.
      apply updF_neq. intro E'. subst k.
      exact (topo_noself o j (c_topo _ _ _ _ _ _ _ _ _ HC) Hj Hk).
    - intros H d Hd. rewrite crun_app. apply (cons_feq T); [| exact CT].
      apply feq_sym. apply drain_plain; [exact Hd | rewrite A; intro k; reflexivity |].
      intros j m Hj Hin. rewrite B in Hin. exact (H j m Hj Hin).
  Qed.

  End Exact.


  (* ---------------------------------------------------------------------------------- *)
  (* Two-level networks: versioned channels reach nothing new.                           *)
  (* ---------------------------------------------------------------------------------- *)

  Lemma Forall_firstn' : forall (A : Type) (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
  Proof.
    intros A P n. induction n as [| n IH]; intros [| x l] H; simpl; try constructor.
    - inversion H; assumption.
    - apply IH. inversion H; assumption.
  Qed.

  Lemma Forall_skipn' : forall (A : Type) (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
  Proof.
    intros A P n. induction n as [| n IH]; intros [| x l] H; simpl; try exact H; try constructor.
    apply IH. inversion H; assumption.
  Qed.

  Lemma firstn_le_app : forall (A : Type) n (l r : list A), n <= length l -> firstn n (l ++ r) = firstn n l.
  Proof.
    intros A n. induction n as [| n IH]; intros [| x l] r H; simpl in *; try reflexivity; try lia.
    rewrite IH by lia. reflexivity.
  Qed.

  Lemma firstn_split : forall (A : Type) d n (l : list A), d <= n ->
    firstn n l = firstn d l ++ firstn (n - d) (skipn d l).
  Proof.
    intros A d. induction d as [| d IH]; intros n l H.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
    - destruct n as [| n]; [lia |]. destruct l as [| x l]; simpl; [destruct (n - d); reflexivity |].
      rewrite (IH n l) by lia. reflexivity.
  Qed.

  Lemma length_skipn' : forall (A : Type) n (l : list A), length (skipn n l) = length l - n.
  Proof.
    intros A n. induction n as [| n IH]; intros [| x l]; simpl; try reflexivity; try lia.
    apply IH.
  Qed.

  Lemma len_app : forall (A : Type) (l r : list A), length (l ++ r) = length l + length r.
  Proof. intros A l r. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma firstn_all' : forall (A : Type) (l : list A), firstn (length l) l = l.
  Proof. intros A l. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma dF_ev_local : forall R, Forall (fun a => exists e, a = DE e) R ->
    forall t t' k, t k = t' k -> dF R t k = dF R t' k.
  Proof.
    induction R as [| a R IH]; intros HR t t' k H; [exact H |].
    inversion HR as [| ? ? [e Ea] HR']; subst. cbn [drun dstep]. apply IH; [exact HR' |].
    unfold evstep. destruct (Nat.eq_dec k (reg e)) as [-> | Ne].
    - rewrite !updF_eq. rewrite H. reflexivity.
    - rewrite !(updF_neq _ _ _ _ Ne). exact H.
  Qed.

  Lemma dF_ev_off : forall k R, Forall (fun a => exists e, a = DE e /\ reg e <> k) R ->
    forall t, dF R t k = t k.
  Proof.
    intros k. induction R as [| a R IH]; intros HR t; [reflexivity |].
    inversion HR as [| ? ? [e [Ea Ne]] HR']; subst. cbn [drun dstep].
    rewrite IH by exact HR'. unfold evstep. apply updF_neq. intro E'. apply Ne. symmetry. exact E'.
  Qed.

  Section TwoLevelSec.
  Hypothesis HC : Common V src f valid rho E reg sig o.
  Variable rt : nat -> bool.

  (* Every registry is a pure root (its repair is the identity) or a sink (nobody reads it):
     every target's sources are roots. Two-registry federations and stars are two-level. *)
  Definition TwoLevel : Prop :=
    forall j, (rt j = true -> forall z x, f j z x = x) /\ (rt j = false -> forall l, ~ In j (src l)).

  Hypothesis HT : TwoLevel.

  Definition isJ (j : nat) (a : act E) : Prop := exists e, a = DE e /\ reg e = j.
  Definition isR (a : act E) : Prop := exists e, a = DE e /\ rt (reg e) = true.

  Lemma src_root : forall k l, In k (src l) -> rt k = true.
  Proof.
    intros k l H. destruct (rt k) eqn:Ek; [reflexivity |]. exfalso. exact (proj2 (HT k) Ek l H).
  Qed.

  Lemma isR_ev : forall R, Forall isR R -> Forall (fun a => exists e, a = DE e) R.
  Proof. intros R H. eapply Forall_impl; [| exact H]. intros a [e [Ea _]]. exists e. exact Ea. Qed.

  Lemma isR_off : forall R k, Forall isR R -> rt k = false ->
    Forall (fun a => exists e, a = DE e /\ reg e <> k) R.
  Proof.
    intros R k H Hk. eapply Forall_impl; [| exact H]. intros a [e [Ea Er]].
    exists e. split; [exact Ea |]. intro E'. rewrite E' in Er. congruence.
  Qed.

  Lemma isJ_off : forall R j k, Forall (isJ j) R -> k <> j ->
    Forall (fun a => exists e, a = DE e /\ reg e <> k) R.
  Proof.
    intros R j k H Hk. eapply Forall_impl; [| exact H]. intros a [e [Ea Er]].
    exists e. split; [exact Ea |]. intro E'. apply Hk. rewrite <- E'. exact Er.
  Qed.

  Lemma isJ_ok : forall j R, Forall (isJ j) R -> Forall okF R.
  Proof. intros j R H. eapply Forall_impl; [| exact H]. intros a [e [-> _]]. exact Logic.I. Qed.

  Lemma isR_ok : forall R, Forall isR R -> Forall okF R.
  Proof. intros R H. eapply Forall_impl; [| exact H]. intros a [e [-> _]]. exact Logic.I. Qed.

  (* A target event commutes with root events, at the target and at every root. *)
  Lemma comm_jev : forall R e t k, Forall isR R -> rt (reg e) = false -> (k = reg e \/ rt k = true) ->
    dF R (evF e t) k = evF e (dF R t) k.
  Proof.
    intros R e t k HR He [-> | Hk].
    - rewrite (dF_ev_off (reg e) R (isR_off R (reg e) HR He)).
      unfold evstep. rewrite !updF_eq. rewrite (dF_ev_off (reg e) R (isR_off R (reg e) HR He)).
      reflexivity.
    - assert (Ne : k <> reg e) by (intro E'; rewrite E' in Hk; congruence).
      rewrite (dF_ev_local R (isR_ev R HR) (evF e t) t k);
        [| unfold evstep; apply updF_neq; exact Ne].
      unfold evstep. rewrite (updF_neq _ _ _ _ Ne). reflexivity.
  Qed.

  (* The emulation invariant for one target j: the current-value word W0 ++ Jt ++ Rt reaches the
     channel state at j and at every root; Jt holds j's events since its last merge, Rt the root
     events since then; each live projection in flight to j snapshots the roots after P v of the
     root events in Rt, and P is monotone in the version. *)
  Definition Emu (s0 : nat -> V) (j : nat) (c : cfg) (W0 Jt Rt : list (act E)) (P : nat -> nat) : Prop :=
    Forall okF (W0 ++ Jt ++ Rt) /\ Forall (isJ j) Jt /\ Forall isR Rt /\
    dF (W0 ++ Jt ++ Rt) s0 j = cs c j /\
    (forall k, rt k = true -> dF (W0 ++ Jt ++ Rt) s0 k = cs c k) /\
    (forall m, In m (cb c j) -> cl c j < fst m ->
       P (fst m) <= length Rt /\
       forall k, In k (src j) -> snd m k = dF (W0 ++ Jt ++ firstn (P (fst m)) Rt) s0 k) /\
    (forall m1 m2, In m1 (cb c j) -> In m2 (cb c j) -> cl c j < fst m1 -> fst m1 < fst m2 ->
       P (fst m1) <= P (fst m2)).

  Lemma emu_ev : forall s0 j e c W0 Jt Rt P, rt j = false -> Emu s0 j c W0 Jt Rt P ->
    exists W0' Jt' Rt' P', Emu s0 j (cstep true (CEv e) c) W0' Jt' Rt' P'.
  Proof.
    intros s0 j e c W0 Jt Rt P Hj [Ok [HJ [HR [Sj [Sr [Sn Mo]]]]]].
    destruct (Nat.eq_dec (reg e) j) as [Ej | Nj].
    - (* an event of the target: appended to Jt *)
      exists W0, (Jt ++ [DE e]), Rt, P.
      assert (Re : rt (reg e) = false) by (rewrite Ej; exact Hj).
      assert (Split : forall X, W0 ++ (Jt ++ [DE e]) ++ X = (W0 ++ Jt) ++ [DE e] ++ X)
        by (intros; rewrite <- !app_assoc; reflexivity).
      assert (Old : forall X, W0 ++ Jt ++ X = (W0 ++ Jt) ++ X) by (intros; rewrite app_assoc; reflexivity).
      assert (St : forall k, (k = reg e \/ rt k = true) ->
                dF (W0 ++ (Jt ++ [DE e]) ++ Rt) s0 k = evF e (dF (W0 ++ Jt ++ Rt) s0) k).
      { intros k Hk. rewrite Split, Old, !drun_app. cbn [drun dstep]. apply comm_jev; assumption. }
      split.
      { rewrite Split. rewrite Old in Ok. apply Forall_app in Ok as [O1 O2].
        apply Forall_app. split; [exact O1 |]. constructor; [exact Logic.I | exact O2]. }
      split; [apply Forall_app; split; [exact HJ | constructor; [exists e; split; [reflexivity | exact Ej] | constructor]] |].
      split; [exact HR |].
      split.
      { rewrite (St j (or_introl (eq_sym Ej))). simpl. unfold evstep.
        rewrite <- Ej, !updF_eq. rewrite Ej, Sj. reflexivity. }
      split.
      { intros k Hk. rewrite (St k (or_intror Hk)). simpl. unfold evstep.
        assert (Ne : k <> reg e) by (intro E'; rewrite E' in Hk; congruence).
        rewrite !(updF_neq _ _ _ _ Ne). apply Sr. exact Hk. }
      split.
      { intros m Hin Hl. destruct (Sn m Hin Hl) as [Pl Hs]. split; [exact Pl |].
        intros k Hk. rewrite (Hs k Hk). rewrite Split, Old, !drun_app. cbn [drun dstep].
        assert (Ne : k <> reg e) by (intro E'; pose proof (src_root k j Hk); rewrite E' in *; congruence).
        apply (dF_ev_local _ (isR_ev _ (Forall_firstn' _ _ _ _ HR))).
        unfold evstep. rewrite (updF_neq _ _ _ _ Ne). reflexivity. }
      exact Mo.
    - destruct (rt (reg e)) eqn:Re.
      + (* a root event: appended to Rt *)
        exists W0, Jt, (Rt ++ [DE e]), P.
        assert (Eq : W0 ++ Jt ++ Rt ++ [DE e] = (W0 ++ Jt ++ Rt) ++ [DE e])
          by (rewrite <- !app_assoc; reflexivity).
        split; [rewrite Eq; apply Forall_app; split; [exact Ok | repeat constructor] |].
        split; [exact HJ |].
        split; [apply Forall_app; split; [exact HR | constructor; [exists e; split; [reflexivity | exact Re] | constructor]] |].
        split.
        { rewrite Eq, drun_app. cbn [drun dstep]. simpl. unfold evstep.
          assert (Ne : j <> reg e) by (intro E'; apply Nj; symmetry; exact E').
          rewrite !(updF_neq _ _ _ _ Ne). exact Sj. }
        split.
        { intros k Hk. rewrite Eq, drun_app. cbn [drun dstep]. simpl. unfold evstep.
          destruct (Nat.eq_dec k (reg e)) as [-> | Ne].
          - rewrite !updF_eq. rewrite (Sr (reg e) Re). reflexivity.
          - rewrite !(updF_neq _ _ _ _ Ne). apply Sr. exact Hk. }
        split.
        { intros m Hin Hl. destruct (Sn m Hin Hl) as [Pl Hs]. split; [rewrite len_app; simpl; lia |].
          intros k Hk. rewrite (Hs k Hk). rewrite firstn_le_app by exact Pl. reflexivity. }
        exact Mo.
      + (* another target's event: invisible at j and at the roots *)
        exists W0, Jt, Rt, P.
        split; [exact Ok |]. split; [exact HJ |]. split; [exact HR |].
        split.
        { simpl. unfold evstep. assert (Ne : j <> reg e) by (intro E'; apply Nj; symmetry; exact E').
          rewrite (updF_neq _ _ _ _ Ne). exact Sj. }
        split.
        { intros k Hk. simpl. unfold evstep.
          assert (Ne : k <> reg e) by (intro E'; rewrite E' in Hk; congruence).
          rewrite (updF_neq _ _ _ _ Ne). apply Sr. exact Hk. }
        split; [exact Sn | exact Mo].
  Qed.

  Lemma emu_send : forall s0 j l v c W0 Jt Rt P, VInv c -> cv c l < v -> Emu s0 j c W0 Jt Rt P ->
    exists W0' Jt' Rt' P', Emu s0 j (cstep true (CSend l v) c) W0' Jt' Rt' P'.
  Proof.
    intros s0 j l v c W0 Jt Rt P Hv Hlt [Ok [HJ [HR [Sj [Sr [Sn Mo]]]]]].
    destruct (Nat.eq_dec l j) as [-> | Ne].
    - exists W0, Jt, Rt, (fun x => if Nat.eqb x v then length Rt else P x).
      assert (Old : forall m, In m (cb c j) -> fst m < v)
        by (intros m Hin; pose proof (proj2 (Hv j) m Hin); lia).
      split; [exact Ok |]. split; [exact HJ |]. split; [exact HR |].
      split; [exact Sj |]. split; [exact Sr |].
      cbn [cs cb cl cv cstep]. rewrite setb_eq.
      split.
      + intros m [<- | Hin] Hl; simpl.
        * rewrite Nat.eqb_refl. split; [lia |]. intros k Hk. rewrite firstn_all'.
          symmetry. apply Sr. exact (src_root k j Hk).
        * assert (Nv : fst m <> v) by (pose proof (Old m Hin); lia).
          apply Nat.eqb_neq in Nv. rewrite Nv. exact (Sn m Hin Hl).
      + intros m1 m2 H1 H2 Hl Hlt12. simpl.
        destruct H1 as [<- | H1]; destruct H2 as [<- | H2]; simpl in *.
        * lia.
        * pose proof (Old m2 H2). lia.
        * assert (Nv : fst m1 <> v) by (pose proof (Old m1 H1); lia).
          apply Nat.eqb_neq in Nv. rewrite Nv, Nat.eqb_refl. exact (proj1 (Sn m1 H1 Hl)).
        * assert (Nv1 : fst m1 <> v) by (pose proof (Old m1 H1); lia).
          assert (Nv2 : fst m2 <> v) by (pose proof (Old m2 H2); lia).
          apply Nat.eqb_neq in Nv1, Nv2. rewrite Nv1, Nv2. exact (Mo m1 m2 H1 H2 Hl Hlt12).
    - exists W0, Jt, Rt, P.
      split; [exact Ok |]. split; [exact HJ |]. split; [exact HR |].
      split; [exact Sj |]. split; [exact Sr |].
      cbn [cs cb cl cv cstep]. rewrite (setb_neq _ _ _ _ (fun E' => Ne (eq_sym E'))).
      split; [exact Sn | exact Mo].
  Qed.

  (* Removing projections in flight keeps the invariant. *)
  Lemma emu_shrink : forall s0 j c c' W0 Jt Rt P, cs c' = cs c -> cl c' = cl c ->
    (forall m, In m (cb c' j) -> In m (cb c j)) ->
    Emu s0 j c W0 Jt Rt P -> Emu s0 j c' W0 Jt Rt P.
  Proof.
    intros s0 j c c' W0 Jt Rt P Hs Hl Hb [Ok [HJ [HR [Sj [Sr [Sn Mo]]]]]].
    split; [exact Ok |]. split; [exact HJ |]. split; [exact HR |].
    rewrite Hs, Hl. split; [exact Sj |]. split; [exact Sr |].
    split; [intros m Hin; apply Sn; apply Hb; exact Hin |].
    intros m1 m2 H1 H2. apply Mo; apply Hb; assumption.
  Qed.

  (* A delivery: a projection to another registry is invisible at j and at the roots (a root's
     repair is the identity); an applied projection to j becomes a propagation step of the
     current-value word, placed where its snapshot was taken. *)
  Lemma emu_merge : forall s0 j l m c c' W0 Jt Rt P, rt j = false -> In l o ->
    cs c' = cs c -> cl c' = cl c -> (forall m', In m' (cb c' j) -> In m' (cb c j)) ->
    (l = j -> In m (cb c j)) ->
    Emu s0 j c W0 Jt Rt P ->
    exists W0' Jt' Rt' P', Emu s0 j (merge true l m c') W0' Jt' Rt' P'.
  Proof.
    intros s0 j l m c c' W0 Jt Rt P Hj Hlo Hs Hl Hb Hm He.
    pose proof (emu_shrink s0 j c c' W0 Jt Rt P Hs Hl Hb He) as He'.
    unfold merge, applies. destruct (Nat.ltb (cl c' l) (fst m)) eqn:Ap;
      [| exists W0, Jt, Rt, P; exact He'].
    apply Nat.ltb_lt in Ap.
    destruct (Nat.eq_dec l j) as [-> | Ne].
    - (* the applied projection to j *)
      destruct He as [Ok [HJ [HR [Sj [Sr [Sn Mo]]]]]].
      rewrite Hl in Ap. specialize (Hm eq_refl).
      destruct (Sn m Hm Ap) as [Pl Hsn]. set (d := P (fst m)).
      set (u := dF (W0 ++ Jt ++ firstn d Rt) s0).
      exists (W0 ++ Jt ++ firstn d Rt ++ [DP j]), [], (skipn d Rt), (fun x => P x - d).
      assert (Wq : forall X, (W0 ++ Jt ++ firstn d Rt ++ [DP j]) ++ [] ++ X =
                             (W0 ++ Jt ++ firstn d Rt) ++ [DP j] ++ X)
        by (intros; rewrite <- !app_assoc; reflexivity).
      assert (Ws : W0 ++ Jt ++ Rt = (W0 ++ Jt ++ firstn d Rt) ++ skipn d Rt).
      { rewrite <- !app_assoc. rewrite firstn_skipn. reflexivity. }
      assert (RS : Forall isR (skipn d Rt)) by (apply Forall_skipn'; exact HR).
      assert (RF : forall n, Forall isR (firstn n Rt)) by (intros; apply Forall_firstn'; exact HR).
      assert (Hu : forall k, k <> j -> fsF u j k = u k) by (intros k Nk; apply (fstep_neq V f); exact Nk).
      assert (Uj : u j = cs c j).
      { rewrite <- Sj. rewrite Ws, (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)). fold u. symmetry.
        apply (dF_ev_off j _ (isR_off _ j RS Hj)). }
      split.
      { rewrite Wq. rewrite Ws in Ok. apply Forall_app in Ok as [O1 O2].
        apply Forall_app. split; [exact O1 |]. constructor; [exact Hlo | exact O2]. }
      split; [constructor |]. split; [exact RS |].
      cbn [cs cb cl cv]. rewrite Hs. rewrite updF_eq.
      split.
      { rewrite Wq, (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)), (drun_app V f E reg sig [DP j]).
        fold u. cbn [drun dstep].
        rewrite (dF_ev_off j _ (isR_off _ j RS Hj)). rewrite (fstep_eq V f). rewrite Uj.
        apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk. rewrite (Hsn k Hk). reflexivity. }
      split.
      { intros k Hk. assert (Nk : k <> j) by (intro E'; subst; congruence).
        rewrite (updF_neq _ _ _ _ Nk). rewrite <- (Sr k Hk).
        rewrite Wq, Ws, (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)),
          (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)), (drun_app V f E reg sig [DP j]).
        fold u. cbn [drun dstep].
        apply (dF_ev_local _ (isR_ev _ RS)). apply Hu. exact Nk. }
      rewrite setn_eq.
      split.
      { intros m0 Hin0 Hl0. pose proof (Hb m0 Hin0) as Hin0'.
        assert (L0 : cl c j < fst m0) by lia.
        pose proof (Mo m m0 Hm Hin0' Ap Hl0) as Dm. fold d in Dm.
        destruct (Sn m0 Hin0' L0) as [Pl0 Hs0].
        split; [rewrite length_skipn'; lia |].
        intros k Hk. rewrite (Hs0 k Hk). rewrite (firstn_split _ d (P (fst m0)) Rt Dm).
        assert (Nk : k <> j) by (intro E'; subst; pose proof (src_root j j Hk); congruence).
        replace (W0 ++ Jt ++ firstn d Rt ++ firstn (P (fst m0) - d) (skipn d Rt))
          with ((W0 ++ Jt ++ firstn d Rt) ++ firstn (P (fst m0) - d) (skipn d Rt))
          by (rewrite <- !app_assoc; reflexivity).
        rewrite Wq, (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)),
          (drun_app V f E reg sig (W0 ++ Jt ++ firstn d Rt)), (drun_app V f E reg sig [DP j]).
        fold u. cbn [drun dstep]. symmetry.
        apply (dF_ev_local _ (isR_ev _ (Forall_firstn' _ _ _ _ RS))). apply Hu. exact Nk. }
      intros m1 m2 H1 H2 L1 L12. pose proof (Hb m1 H1) as H1'. pose proof (Hb m2 H2) as H2'.
      pose proof (Mo m m1 Hm H1' Ap L1) as D1. pose proof (Mo m1 m2 H1' H2' ltac:(lia) L12) as D12.
      fold d in D1. lia.
    - (* a projection to another registry *)
      exists W0, Jt, Rt, P.
      destruct He' as [Ok [HJ [HR [Sj [Sr [Sn Mo]]]]]].
      split; [exact Ok |]. split; [exact HJ |]. split; [exact HR |].
      cbn [cs cb cl cv].
      split; [rewrite (updF_neq _ _ _ _ (fun E' => Ne (eq_sym E'))); exact Sj |].
      split.
      { intros k Hk. destruct (Nat.eq_dec k l) as [-> | Nk].
        - rewrite updF_eq. rewrite (proj1 (HT l) Hk). apply Sr. exact Hk.
        - rewrite (updF_neq _ _ _ _ Nk). apply Sr. exact Hk. }
      rewrite (setn_neq _ _ _ _ (fun E' => Ne (eq_sym E'))).
      split; [exact Sn | exact Mo].
  Qed.

  Lemma emu_step : forall s0 j a c W0 Jt Rt P, rt j = false -> VInv c -> okc a ->
    (match a with CSend l v => cv c l < v | _ => True end) -> Emu s0 j c W0 Jt Rt P ->
    exists W0' Jt' Rt' P', Emu s0 j (cstep true a c) W0' Jt' Rt' P'.
  Proof.
    intros s0 j a c W0 Jt Rt P Hj Hv Ha Hd He. destruct a as [e | l v | l i | l i].
    - exact (emu_ev s0 j e c W0 Jt Rt P Hj He).
    - exact (emu_send s0 j l v c W0 Jt Rt P Hv Hd He).
    - unfold cstep. destruct (nth_error (cb c l) i) as [m |] eqn:Hn; [| exists W0, Jt, Rt, P; exact He].
      apply (emu_merge s0 j l m c (Cfg (cs c) (setb (cb c) l (rmn i (cb c l))) (cl c) (cv c))
               W0 Jt Rt P Hj Ha eq_refl eq_refl); [| | exact He].
      + intros m' Hin. simpl in Hin. destruct (Nat.eq_dec j l) as [-> | Ne].
        * rewrite setb_eq in Hin. exact (rmn_in _ _ _ Hin).
        * rewrite (setb_neq _ _ _ _ Ne) in Hin. exact Hin.
      + intros ->. exact (nth_error_in _ _ _ Hn).
    - unfold cstep. destruct (nth_error (cb c l) i) as [m |] eqn:Hn; [| exists W0, Jt, Rt, P; exact He].
      apply (emu_merge s0 j l m c c W0 Jt Rt P Hj Ha eq_refl eq_refl); [| | exact He].
      + intros m' Hin. exact Hin.
      + intros ->. exact (nth_error_in _ _ _ Hn).
  Qed.

  Lemma emu_run : forall s0 j w c W0 Jt Rt P, rt j = false -> VInv c -> Forall okc w -> disc true w c ->
    Emu s0 j c W0 Jt Rt P -> exists W0' Jt' Rt' P', Emu s0 j (crun true w c) W0' Jt' Rt' P'.
  Proof.
    intros s0 j w. induction w as [| a w IH]; intros c W0 Jt Rt P Hj Hv Hw Hd He.
    - exists W0, Jt, Rt, P. exact He.
    - inversion Hw as [| ? ? Ha Hw']; subst. destruct Hd as [Hd1 Hd].
      destruct (emu_step s0 j a c W0 Jt Rt P Hj Hv Ha Hd1 He) as [W1 [J1 [R1 [P1 He1]]]].
      exact (IH (cstep true a c) W1 J1 R1 P1 Hj (vinv_step true a c Hv Hd1) Hw' Hd He1).
  Qed.

  (* Headline (emulation): on a two-level network, every state a versioned channel run reaches
     (any reordering, duplication, late delivery) is, at any target j and at every root, the
     state of a current-value run. *)
  Theorem vchan_emulate : forall s0 j w, rt j = false -> Forall okc w -> disc true w (init s0) ->
    exists w', Forall okF w' /\ dF w' s0 j = cs (crun true w (init s0)) j /\
      forall k, rt k = true -> dF w' s0 k = cs (crun true w (init s0)) k.
  Proof.
    intros s0 j w Hj Hw Hd.
    assert (He : Emu s0 j (init s0) [] [] [] (fun _ => 0)).
    { split; [constructor |]. split; [constructor |]. split; [constructor |].
      split; [reflexivity |]. split; [reflexivity |]. split; intros m; simpl; tauto. }
    destruct (emu_run s0 j w (init s0) [] [] [] (fun _ => 0) Hj (vinv_init s0) Hw Hd He)
      as [W0 [Jt [Rt [P [Ok [_ [_ [Sj [Sr _]]]]]]]]].
    exists (W0 ++ Jt ++ Rt). split; [exact Ok |]. split; [exact Sj | exact Sr].
  Qed.

  Lemma N_root : forall t k, InvF t -> rt k = true -> nF t k = t k.
  Proof.
    intros t k Ht Hk. rewrite (N_frun _ _ _ _ _ _ _ _ _ HC t Ht k).
    destruct (in_dec Nat.eq_dec k o) as [Ho | Ho].
    - rewrite (frun_solves _ _ _ _ _ _ _ _ _ HC o t (c_topo _ _ _ _ _ _ _ _ _ HC) k Ho).
      apply (proj1 (HT k) Hk).
    - apply (frun_out V f). exact Ho.
  Qed.

  (* XU at a state depends only on the event's registry and the roots. *)
  Lemma xuat_transfer : forall t t' e, InvF t -> InvF t' -> t (reg e) = t' (reg e) ->
    (forall k, rt k = true -> t k = t' k) -> XUatF t e -> XUatF t' e.
  Proof.
    intros t t' e Ht Ht' Hj Hr X. unfold XUat in *.
    assert (Hf : forall x, f (reg e) (nF t) x = f (reg e) (nF t') x).
    { intros x. apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk.
      pose proof (src_root k (reg e) Hk) as Rk.
      rewrite (N_root t k Ht Rk), (N_root t' k Ht' Rk). apply Hr. exact Rk. }
    rewrite <- !Hf. rewrite <- Hj. exact X.
  Qed.

  Theorem cxur_twolevel : forall s0, InvF s0 -> XURF s0 -> CXUR true s0.
  Proof.
    intros s0 Hi Hx p e Hp Hd.
    assert (It : InvF (cs (crun true p (init s0)))) by exact (proj1 (cinv_run HC true p (init s0) (cinv_init s0 Hi))).
    destruct (rt (reg e)) eqn:Re.
    - unfold XUat. rewrite !(proj1 (HT (reg e)) Re). reflexivity.
    - destruct (vchan_emulate s0 (reg e) p Re Hp Hd) as [w' [Ok [Sj Sr]]].
      apply (xuat_transfer (dF w' s0)); [apply (drun_inv _ _ _ _ _ _ _ _ _ HC); exact Hi | exact It
                                        | exact Sj | exact Sr |].
      exact (Hx w' e Ok).
  Qed.

  (* Headline (two-level, versioned): the exact condition over channels is the current-value
     model's own (DistributedExact.dist_exact), whether compared after a flush or at drain. *)
  Theorem vchan_twolevel_exact : forall s0, InvF s0 ->
    (ChanConv true s0 <-> XURF s0 /\ C2Rf (nF s0)) /\
    (SettleConv s0 <-> XURF s0 /\ C2Rf (nF s0)) /\
    (SettleConv s0 <-> DistConvF s0).
  Proof.
    intros s0 Hi.
    assert (A : ChanConv true s0 <-> XURF s0 /\ C2Rf (nF s0)).
    { rewrite (chan_exact HC true s0 Hi). split.
      - intros [Hx H2]. split; [exact (cxur_xur true s0 Hx) | exact H2].
      - intros [Hx H2]. split; [exact (cxur_twolevel s0 Hi Hx) | exact H2]. }
    assert (B : SettleConv s0 <-> XURF s0 /\ C2Rf (nF s0)) by (rewrite (vsettle_exact HC s0 Hi); exact A).
    split; [exact A |]. split; [exact B |].
    rewrite B. symmetry. apply (dist_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi).
  Qed.

End TwoLevelSec.

End Chan.

Arguments CEv {E} _.
Arguments CSend {E} _ _.
Arguments CDel {E} _ _.
Arguments CDup {E} _ _.

(* ========================================================================================= *)
(* Instances on the supply federation of FederationEvents.v: registry 0 (the manufacturer's   *)
(* recall flag) is the source, registry 1 (the supplier's (listed_ok, sold)) the target, with *)
(* listed_ok := negb recalled. Common, XU and LocalCC hold (supply_instance).                  *)
(* ========================================================================================= *)

Definition sp_run (vm : bool) (w : list (cact sev)) :=
  crun (bool * nat) sp_f sev sp_reg sp_sig vm w (init (bool * nat) ce_s0).

Definition sp_rt (k : nat) : bool := Nat.eqb k 0.

Lemma sp_twolevel : TwoLevel (bool * nat) src2 sp_f sp_rt.
Proof.
  intros [| [| j]]; split; intros H; simpl in H; try discriminate.
  - intros z x. reflexivity.
  - intros [| [| l]] Hin; simpl in Hin; try contradiction. destruct Hin as [Hin | []]. discriminate.
  - intros [| [| l]] Hin; simpl in Hin; try contradiction. destruct Hin as [Hin | []]. discriminate.
Qed.

Lemma ce_s0_inv : Inv (bool * nat) sp_valid ce_s0.
Proof. intros [| [| k]]; simpl; lia. Qed.

(* The run: the source is snapshot, then recalls; the final round sends the fresh projection; a
   stale copy of the first projection is delivered after it. *)
Definition w_stale : list (cact sev) :=
  [CSend 1 1; CEv Recall; CSend 0 1; CDel 0 0; CSend 1 2; CDel 1 0; CDel 1 0].
(* The same sends and events, with the old projection delivered before the fresh one. *)
Definition w_order : list (cact sev) :=
  [CSend 1 1; CEv Recall; CDel 1 0; CSend 0 1; CDel 0 0; CSend 1 2; CDel 1 0].

(* Counterexample (plain merge): under XU, the plain merge over a reordering channel ends a
   drained run, whose last send to the target came after the source's last change and was
   delivered, in a state that is not a fixed point of the repair (the target still lists a recalled
   product), and two drained runs with the same events end in different states. After an outside
   flush both agree (ChanConv false holds); the versioned merge refuses the stale projection and
   settles (and SettleConv holds). *)
Theorem plain_stale_counterexample :
  Common (bool * nat) src2 sp_f sp_valid sp_rho sev sp_reg sp_sig [0; 1] /\
  XU (bool * nat) sp_f sp_valid sev sp_reg sp_sig /\
  LocalCC (bool * nat) sp_valid sev sp_reg sp_sig sp_I /\
  w_stale = [CSend 1 1; CEv Recall] ++
            fround (bool * nat) sev [0; 1] (sp_run false [CSend 1 1; CEv Recall]) ++ [CDel 1 0] /\
  Forall (okc sev [0; 1]) w_stale /\ Forall (okc sev [0; 1]) w_order /\
  disc (bool * nat) sp_f sev sp_reg sp_sig false w_stale (init _ ce_s0) /\
  disc (bool * nat) sp_f sev sp_reg sp_sig false w_order (init _ ce_s0) /\
  disc (bool * nat) sp_f sev sp_reg sp_sig true w_stale (init _ ce_s0) /\
  cevs sev w_stale = [Recall] /\ cevs sev w_order = [Recall] /\
  Drained (bool * nat) (sp_run false w_stale) /\ Drained (bool * nat) (sp_run false w_order) /\
  cs _ (sp_run false w_stale) 0 = (true, 0) /\ cs _ (sp_run false w_stale) 1 = (true, 0) /\
  cs _ (sp_run false w_order) 0 = (true, 0) /\ cs _ (sp_run false w_order) 1 = (false, 0) /\
  ~ Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run false w_stale)) /\
  Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run false w_order)) /\
  cs _ (sp_run true w_stale) 1 = (false, 0) /\
  Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run true w_stale)) /\
  ChanConv (bool * nat) sp_f sp_rho sev sp_reg sp_sig sp_I [0; 1] false ce_s0 /\
  SettleConv (bool * nat) sp_f sev sp_reg sp_sig sp_I [0; 1] ce_s0.
Proof.
  destruct supply_instance as [Hc [Hx [Hl [_ [H2 _]]]]].
  split; [exact Hc |]. split; [exact Hx |]. split; [exact Hl |].
  split; [reflexivity |].
  split; [repeat constructor; simpl; tauto |]. split; [repeat constructor; simpl; tauto |].
  split; [simpl; unfold setn; simpl; repeat split; lia |]. split; [simpl; unfold setn; simpl; repeat split; lia |].
  split; [simpl; unfold setn; simpl; repeat split; lia |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [intros [| [| j]]; reflexivity |]. split; [intros [| [| j]]; reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [intros H; specialize (H 1 (or_intror (or_introl eq_refl))); vm_compute in H; discriminate H |].
  split; [intros j [<- | [<- | []]]; reflexivity |].
  split; [reflexivity |].
  split; [intros j [<- | [<- | []]]; reflexivity |].
  split; [exact (chan_xu_c2 _ _ _ _ _ _ _ _ _ _ Hc Hx H2 false ce_s0 ce_s0_inv) |].
  exact (vsettle_xu_c2 _ _ _ _ _ _ _ _ _ _ Hc Hx H2 ce_s0 ce_s0_inv).
Qed.

(* The run-level condition fails there: after the stale-free prefix, the first projection is
   still in flight and its image differs from the flushed one (plain_settle_iff). *)
Theorem plain_stale_in_flight :
  let c := sp_run false [CSend 1 1; CEv Recall] in
  In (1, ce_s0) (cb _ c 1) /\
  sp_f 1 ce_s0 (frun (bool * nat) sp_f [0; 1] (cs _ c) 1) <> frun (bool * nat) sp_f [0; 1] (cs _ c) 1.
Proof. simpl. split; [left; reflexivity | intro H; discriminate H]. Qed.

(* Counterexample (the version discipline): versions that do not follow the send order (a newer
   version stamped on an older snapshot: a restamped retry, or a version derived from a value
   the source revisits) let the versioned merge apply a stale projection last. *)
Definition w_badver : list (cact sev) :=
  [CSend 1 5; CEv Recall; CSend 1 3; CDel 1 0; CDel 1 0].
Definition w_goodver : list (cact sev) :=
  [CSend 1 1; CEv Recall; CSend 1 2; CDel 1 0; CDel 1 0].

Theorem version_order_counterexample :
  ~ disc (bool * nat) sp_f sev sp_reg sp_sig true w_badver (init _ ce_s0) /\
  disc (bool * nat) sp_f sev sp_reg sp_sig true w_goodver (init _ ce_s0) /\
  cevs sev w_badver = cevs sev w_goodver /\
  Drained (bool * nat) (sp_run true w_badver) /\ Drained (bool * nat) (sp_run true w_goodver) /\
  cs _ (sp_run true w_badver) 1 = (true, 0) /\ cs _ (sp_run true w_goodver) 1 = (false, 0) /\
  ~ Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run true w_badver)) /\
  Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run true w_goodver)).
Proof.
  split; [simpl; unfold setn; simpl; lia |]. split; [simpl; unfold setn; simpl; repeat split; lia |].
  split; [reflexivity |].
  split; [intros [| [| j]]; reflexivity |]. split; [intros [| [| j]]; reflexivity |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [intros H; specialize (H 1 (or_intror (or_introl eq_refl))); vm_compute in H; discriminate H |].
  intros j [<- | [<- | []]]; reflexivity.
Qed.

(* Counterexample (the final send): drained channels alone settle nothing; a source change with
   no projection sent after it leaves the target stale, in either mode. *)
Theorem no_final_send_counterexample : forall vm,
  Drained (bool * nat) (sp_run vm [CEv Recall]) /\
  ~ Cons (bool * nat) sp_f [0; 1] (cs _ (sp_run vm [CEv Recall])).
Proof.
  intros vm. split; [intros j; reflexivity |].
  intros H. specialize (H 1 (or_intror (or_introl eq_refl))). vm_compute in H. discriminate H.
Qed.

(* Late delivery (non-vacuity): a projection snapshot before a sale and a recall, delivered after
   both; the final round settles the target, at the state of the current-value run "the same
   events, then a flush" (vsettle_cv). *)
Definition w_late : list (cact sev) := [CSend 1 1; CEv Sell; CEv Recall; CDel 1 0].

Theorem late_delivery_instance :
  cs _ (sp_run true w_late) 1 = (true, 1) /\
  cs _ (sp_run true (w_late ++ fround (bool * nat) sev [0; 1] (sp_run true w_late))) 1 = (false, 1) /\
  drun (bool * nat) sp_f sev sp_reg sp_sig
    (map (DEv sev) (cevs sev w_late) ++ map (DProp sev) [0; 1]) ce_s0 1 = (false, 1) /\
  TwoLevel (bool * nat) src2 sp_f sp_rt /\
  (forall s0, Inv (bool * nat) sp_valid s0 ->
     SettleConv (bool * nat) sp_f sev sp_reg sp_sig sp_I [0; 1] s0 /\
     DistConv (bool * nat) sp_f sp_rho sev sp_reg sp_sig sp_I [0; 1] s0).
Proof.
  destruct supply_instance as [Hc [Hx [_ [_ [H2 _]]]]].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact sp_twolevel |].
  intros s0 Hi. pose proof (vsettle_xu_c2 _ _ _ _ _ _ _ _ _ _ Hc Hx H2 s0 Hi) as S.
  split; [exact S |].
  exact (proj1 (proj2 (proj2 (vchan_twolevel_exact _ _ _ _ _ _ _ _ _ _ Hc sp_rt sp_twolevel s0 Hi))) S).
Qed.

(* ========================================================================================= *)
(* Cycles: versioned channels do not remove the ghost (DistributedCycles.dist_cyc_ghost).     *)
(* Two nodes A = 0 and B = 1, each (alarm, flag), with A.flag := B.alarm || B.flag and        *)
(* B.flag := A.alarm || A.flag.                                                                *)
(* ========================================================================================= *)

Definition cy_src (k : nat) : list nat := match k with 0 => [1] | 1 => [0] | _ => [] end.

Definition cy_f (k : nat) (z : nat -> bool * bool) (x : bool * bool) : bool * bool :=
  match k with
  | 0 => (fst x, fst (z 1) || snd (z 1))
  | 1 => (fst x, fst (z 0) || snd (z 0))
  | _ => x
  end.

Inductive cyev : Type := RaiseA | ClearA.

Definition cy_reg (e : cyev) : nat := 0.

Definition cy_sig (e : cyev) (x : bool * bool) : bool * bool :=
  match e with RaiseA => (true, snd x) | ClearA => (false, snd x) end.

Definition cy_run (w : list (cact cyev)) :=
  crun (bool * bool) cy_f cyev cy_reg cy_sig true w (init (bool * bool) (fun _ => (false, false))).

(* Raise A, propagate to B, propagate back to A, clear A; then a final round of fresh,
   in-order versioned projections. *)
Definition w_cy_ghost : list (cact cyev) :=
  [CEv RaiseA; CSend 1 1; CDel 1 0; CSend 0 1; CDel 0 0; CEv ClearA;
   CSend 0 2; CDel 0 0; CSend 1 2; CDel 1 0].
Definition w_cy_clean : list (cact cyev) :=
  [CEv RaiseA; CEv ClearA; CSend 0 1; CDel 0 0; CSend 1 1; CDel 1 0].

Theorem vchan_cyc_ghost :
  disc (bool * bool) cy_f cyev cy_reg cy_sig true w_cy_ghost (init _ (fun _ => (false, false))) /\
  disc (bool * bool) cy_f cyev cy_reg cy_sig true w_cy_clean (init _ (fun _ => (false, false))) /\
  cevs cyev w_cy_ghost = [RaiseA; ClearA] /\ cevs cyev w_cy_clean = [RaiseA; ClearA] /\
  Drained (bool * bool) (cy_run w_cy_ghost) /\ Drained (bool * bool) (cy_run w_cy_clean) /\
  Cons (bool * bool) cy_f [0; 1] (cs _ (cy_run w_cy_ghost)) /\
  Cons (bool * bool) cy_f [0; 1] (cs _ (cy_run w_cy_clean)) /\
  cs _ (cy_run w_cy_ghost) 0 = (false, true) /\ cs _ (cy_run w_cy_ghost) 1 = (false, true) /\
  cs _ (cy_run w_cy_clean) 0 = (false, false) /\ cs _ (cy_run w_cy_clean) 1 = (false, false).
Proof.
  split; [simpl; unfold setn; simpl; repeat split; lia |]. split; [simpl; unfold setn; simpl; repeat split; lia |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [intros [| [| j]]; reflexivity |]. split; [intros [| [| j]]; reflexivity |].
  split; [intros j [<- | [<- | []]]; reflexivity |].
  split; [intros j [<- | [<- | []]]; reflexivity |].
  repeat split; reflexivity.
Qed.
