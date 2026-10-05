(* SignedResolver.v: the signed-cycle to E bridge for resolver networks (reading B of
   LOSSY-NETWORKS.md). Axiom-free. Sufficient certificates for E under an explicit resolver
   semantics, not an identity: each hypothesis is shown needed by a counterexample.

   Resolver model (reading B). A finite family of value sets, all carried by one type X with a
   partial order leX that has a least element botX and a greatest element topX and finite height
   (rank rX <= hX). A state s : Sh exposes the value of vertex j through a lens (get j, set j) on
   the vertex list js, with extensionality on js. Each vertex v has a resolver Fv v : Sh -> X; the
   asynchronous step rupd j replaces the value of j by Fv j of the CURRENT state; Fsync updates
   every vertex at once. Schedules are DistributedCycles' fair schedules (every vertex named
   infinitely often), runs are prs, settling is Settles, quiescence is Stable.

   Signed interaction graph: the GLOBAL graph. sg is a list of signed edges (u, v, b), b = false
   positive and b = true negative. Resp sg: for every vertex v and states s, t, if every positive
   in-edge (u, v) has get u s <= get u t and every negative one has get u t <= get u s, then
   Fv v s <= Fv v t. So Fv v reads only its in-neighbors and is monotone in its positive inputs and
   antitone in its negative inputs, with signs FIXED ACROSS ALL STATES. Local (state-dependent)
   interaction graphs, unsigned maps (no order making a map monotone or antitone), and value sets
   without a top or bottom are OUT OF SCOPE of the certificates below; each is shown to break them.

   Switching. A switching o : nat -> bool (SignedCycles.Switching: every edge (u, v, b) has
   b = xorb (o u) (o v)) reverses the order of the vertices with o = true (leo, le_o). Harary
   (SignedCycles.harary_balance, proved): a switching exists iff no closed undirected walk carries
   an odd number of negative edges.

   Results.
     switched_monotone     Resp + Switching o: every resolver is monotone for the switched orders.
     signed_settlement     (bridge, attempt 1: settlement and fidelity from LOW starts) Resp +
                           Switching o: slfp o, the least fixed point of Fsync in the switched order,
                           exists; from every start h0 <= slfp o (switched order) every fair
                           schedule settles at slfp o; from every SOUND start (h0 <= Fsync h0) every
                           fair schedule settles at the least fixed point above h0; and E holds:
                           EffectiveCanon (Settlement /\ CanonicalFidelity of
                           CanonicalExecution.v) with canonicalizer N := const (slfp o), from every
                           start h0 <= slfp o, together with the left side of esh_exact
                           (signed_esh).
     signed_settlement_harary
                           the same with the switching produced by harary_balance from "no
                           negative undirected cycle".
     signed_fidelity       (bridge, attempt 2: every start) Resp + Switching o + AT MOST ONE fixed
                           point: every fair schedule from EVERY start settles at the fixed point,
                           and E (and the left side of esh_exact) holds from every start. This is
                           DistributedCycles.q1_unique_iff after the change of order; it uses topX.
   Uniqueness is a hypothesis, not derived from signs: SignedCycles.balanced_no_positive_acyclic
   shows that balance plus Thomas's sign condition (no positive directed cycle) leaves no directed
   cycle at all, so on a balanced graph the sign route to uniqueness (Richard and Comet 2007,
   Aracena 2008; cited, not mechanized) covers only acyclic networks (Robert). unique_pos_cycle
   is a monotone network with a positive cycle and one fixed point, outside every sign condition,
   to which signed_fidelity applies.

   Non-vacuity: neg_chain_settles (x0 := true, x1 := not x0, switching (false, true): every start
   is below slfp, E holds everywhere) and unique_pos_cycle.

   Breaks (each a theorem).
     neg2_no_fixed_point   negative 2-cycle x0 := not x1, x1 := x0: Resp holds, no switching exists,
                           no fixed point, so no schedule from any start ever settles (the Boolean
                           form of flip_noflush and of the negation counterexample
                           prop_cycle_necessary / rootless_negation_no_nf).
     copyback_ghost        positive 2-cycle x0 := x1, x1 := x0: Resp and the switching hold, two
                           fixed points; from the SOUND start (1, 1), above slfp = (0, 0), every
                           schedule stays at (1, 1): CanonicalFidelity and E fail. The start
                           condition h0 <= slfp is needed for fidelity (sound is not enough). This
                           is copyback_without_authority's loop and the ghost of ghost_exact.
     toggle_ghost          the same with two negative edges (x0 := not x1, x1 := not x0), switching
                           (false, true): slfp = (0, 1), and the other fixed point (1, 0) is a
                           ghost.
     ring_needs_low_start  the positive 3-ring x0 := x1, x1 := x2, x2 := x0 (dist_ring_livelock):
                           Resp and the switching hold, but from (1, 0, 0), not below slfp, a fair
                           schedule never reaches a quiescent state. The start condition is needed
                           for settlement too.
     unbalanced_unique_oscillates
                           x0 := x0, x1 := x0 and not x1: Resp holds, exactly one fixed point,
                           no switching (a negative self-loop), and from every start with x0 = 1 no
                           schedule ever settles. Balance cannot be dropped from attempt 2.
     flip_needs_top        flip_noflush's swap on {fz < fa, fb}: monotone, one fixed point, but
                           the value set has no top and no propagation word from fa ever reaches
                           quiescence. Attempt 2 needs bounded value sets.
     xor_no_certificate    x1 := x0 xor x1 reads x0 neither monotonically nor antitonically:
                           every global signed graph certifying it (Resp) admits no switching (the
                           arc 0 -> 1 needs both signs, an unbalanced 2-cycle). Lossy non-monotone
                           resolvers are rejected, not misclassified.
     cyc3_unsignable       the 3-cycle permutation of {t0, t1, t2} (one vertex, a self-loop) is
                           neither monotone nor antitone for ANY partial order with a least
                           element, and has no fixed point: unsigned maps are out of reach of the
                           certificates.
   Local graphs: not mechanized and out of scope; see docs/LOSSY-NETWORKS.md (Ruet 2017 refutes
   the local form of the negative-cycle rule in general). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.SignedCycles NC.FederationEventsCycles
  NC.DistributedCycles NC.DistributedCyclesExact NC.CanonicalExecution.
Import ListNotations.

Section Resolver.
  Variables (X Sh : Type).
  Variable leX : X -> X -> Prop.
  Hypothesis leX_refl : forall a, leX a a.
  Hypothesis leX_trans : forall a b c, leX a b -> leX b c -> leX a c.
  Hypothesis leX_antisym : forall a b, leX a b -> leX b a -> a = b.
  Variables botX topX : X.
  Hypothesis botX_least : forall a, leX botX a.
  Hypothesis topX_greatest : forall a, leX a topX.
  Variable rX : X -> nat.
  Hypothesis rX_strict : forall a b, leX a b -> a <> b -> rX a < rX b.
  Variable hX : nat.
  Hypothesis rX_bound : forall a, rX a <= hX.
  Variable x_eq_dec : forall a b : X, {a = b} + {a <> b}.

  Variable js : list nat.
  Variable get : nat -> Sh -> X.
  Variable set : nat -> X -> Sh -> Sh.
  Hypothesis get_set_eq : forall j x s, In j js -> get j (set j x s) = x.
  Hypothesis get_set_neq : forall j k x s, k <> j -> get k (set j x s) = get k s.
  Hypothesis sh_ext : forall s t, (forall j, In j js -> get j s = get j t) -> s = t.
  Variable z0 : Sh.

  Variable Fv : nat -> Sh -> X.
  Variable sg : list (@edge bool).

  (* The signed GLOBAL interaction graph sg is a sign certificate for the resolvers. *)
  Definition Resp : Prop :=
    forall v, In v js -> forall s t,
      (forall u b, In (u, v, b) sg -> if b then leX (get u t) (get u s) else leX (get u s) (get u t)) ->
      leX (Fv v s) (Fv v t).

  Definition SgOn : Prop := forall u v b, In (u, v, b) sg -> In u js /\ In v js.

  (* ----- the dynamics ----- *)

  Fixpoint setl (l : list nat) (f : nat -> X) (s : Sh) : Sh :=
    match l with [] => s | j :: r => set j (f j) (setl r f s) end.

  Definition Fsync (s : Sh) : Sh := setl js (fun j => Fv j s) s.
  Definition rupd (j : nat) (s : Sh) : Sh :=
    if in_dec Nat.eq_dec j js then set j (Fv j s) s else s.

  Lemma get_setl_in : forall l f s k,
    (forall j, In j l -> In j js) -> In k l -> get k (setl l f s) = f k.
  Proof.
    induction l as [| j l IH]; intros f s k Hl Hk; [destruct Hk |]. simpl.
    destruct (Nat.eq_dec k j) as [-> | Nk].
    - apply get_set_eq. apply Hl. left. reflexivity.
    - rewrite (get_set_neq j k _ _ Nk). apply IH; [intros i Hi; apply Hl; right; exact Hi |].
      destruct Hk as [E | Hk]; [subst; contradiction | exact Hk].
  Qed.

  Lemma get_Fsync : forall s k, In k js -> get k (Fsync s) = Fv k s.
  Proof. intros s k Hk. apply get_setl_in; [auto | exact Hk]. Qed.

  Lemma get_rupd_same : forall j s, In j js -> get j (rupd j s) = Fv j s.
  Proof.
    intros j s Hj. unfold rupd. destruct (in_dec Nat.eq_dec j js); [| contradiction].
    apply get_set_eq. exact Hj.
  Qed.

  Lemma get_rupd_other : forall j k s, k <> j -> get k (rupd j s) = get k s.
  Proof.
    intros j k s Nk. unfold rupd. destruct (in_dec Nat.eq_dec j js); [| reflexivity].
    apply get_set_neq. exact Nk.
  Qed.

  Lemma rupd_out : forall j s, ~ In j js -> rupd j s = s.
  Proof. intros j s Hj. unfold rupd. destruct (in_dec Nat.eq_dec j js); [contradiction | reflexivity]. Qed.

  Definition all_eq_dec : forall (l : list nat) (s t : Sh),
    {forall j, In j l -> get j s = get j t} + {exists j, In j l /\ get j s <> get j t}.
  Proof.
    induction l as [| a l IH]; intros s t.
    - left. intros j [].
    - destruct (x_eq_dec (get a s) (get a t)) as [Ea | Na].
      + destruct (IH s t) as [Hs | Hn].
        * left. intros j [<- | Hj]; [exact Ea | apply Hs; exact Hj].
        * right. destruct Hn as [j [Hj Hn]]. exists j. split; [right; exact Hj | exact Hn].
      + right. exists a. split; [left; reflexivity | exact Na].
  Defined.

  Definition sh_eq_dec : forall s t : Sh, {s = t} + {s <> t}.
  Proof.
    intros s t. destruct (all_eq_dec js s t) as [H | H].
    - left. apply sh_ext. exact H.
    - right. intro E. subst t. destruct H as [j [_ Hj]]. apply Hj. reflexivity.
  Defined.

  (* ----- switched orders ----- *)

  Section Switched.
    Variable o : nat -> bool.

    Definition leo (j : nat) (a b : X) : Prop := if o j then leX b a else leX a b.
    Definition le_o (s t : Sh) : Prop := forall j, In j js -> leo j (get j s) (get j t).

    Lemma leo_refl : forall j a, leo j a a.
    Proof. intros j a. unfold leo. destruct (o j); apply leX_refl. Qed.
    Lemma leo_trans : forall j a b c, leo j a b -> leo j b c -> leo j a c.
    Proof. intros j a b c. unfold leo. destruct (o j); eauto. Qed.
    Lemma leo_antisym : forall j a b, leo j a b -> leo j b a -> a = b.
    Proof. intros j a b. unfold leo. destruct (o j); auto. Qed.

    Lemma le_o_refl : forall s, le_o s s.
    Proof. intros s j _. apply leo_refl. Qed.
    Lemma le_o_trans : forall s t w, le_o s t -> le_o t w -> le_o s w.
    Proof. intros s t w H1 H2 j Hj. exact (leo_trans j _ _ _ (H1 j Hj) (H2 j Hj)). Qed.
    Lemma le_o_antisym : forall s t, le_o s t -> le_o t s -> s = t.
    Proof. intros s t H1 H2. apply sh_ext. intros j Hj. exact (leo_antisym j _ _ (H1 j Hj) (H2 j Hj)). Qed.

    Definition bot_o : Sh := setl js (fun j => if o j then topX else botX) z0.
    Definition top_o : Sh := setl js (fun j => if o j then botX else topX) z0.

    Lemma bot_o_least : forall s, le_o bot_o s.
    Proof.
      intros s j Hj. unfold bot_o. rewrite get_setl_in; [| auto | exact Hj].
      unfold leo. destruct (o j); [apply topX_greatest | apply botX_least].
    Qed.

    Lemma top_o_greatest : forall s, le_o s top_o.
    Proof.
      intros s j Hj. unfold top_o. rewrite get_setl_in; [| auto | exact Hj].
      unfold leo. destruct (o j); [apply botX_least | apply topX_greatest].
    Qed.

    Definition rj (j : nat) (a : X) : nat := if o j then hX - rX a else rX a.
    Fixpoint rsum (l : list nat) (s : Sh) : nat :=
      match l with [] => 0 | j :: r => rj j (get j s) + rsum r s end.
    Definition rk (s : Sh) : nat := rsum js s.
    Definition rheight : nat := length js * hX.

    Lemma rX_mono : forall a b, leX a b -> rX a <= rX b.
    Proof.
      intros a b H. destruct (x_eq_dec a b) as [-> | Ne]; [lia |].
      pose proof (rX_strict a b H Ne). lia.
    Qed.

    Lemma rj_mono : forall j a b, leo j a b -> rj j a <= rj j b.
    Proof.
      intros j a b. unfold leo, rj. destruct (o j); intro H; pose proof (rX_mono _ _ H); lia.
    Qed.

    Lemma rj_strict : forall j a b, leo j a b -> a <> b -> rj j a < rj j b.
    Proof.
      intros j a b. unfold leo, rj. destruct (o j); intros H Ne.
      - pose proof (rX_strict b a H (fun E => Ne (eq_sym E))). pose proof (rX_bound a). lia.
      - exact (rX_strict a b H Ne).
    Qed.

    Lemma rsum_le : forall l s t, (forall j, In j l -> leo j (get j s) (get j t)) -> rsum l s <= rsum l t.
    Proof.
      induction l as [| j l IH]; intros s t H; simpl; [lia |].
      pose proof (rj_mono j _ _ (H j (or_introl eq_refl))).
      pose proof (IH s t (fun i Hi => H i (or_intror Hi))). lia.
    Qed.

    Lemma rsum_lt : forall l s t, (forall j, In j l -> leo j (get j s) (get j t)) ->
      (exists j, In j l /\ get j s <> get j t) -> rsum l s < rsum l t.
    Proof.
      induction l as [| j l IH]; intros s t H [i [Hi Ne]]; [destruct Hi |]. simpl.
      destruct Hi as [-> | Hi].
      - pose proof (rj_strict i _ _ (H i (or_introl eq_refl)) Ne).
        pose proof (rsum_le l s t (fun k Hk => H k (or_intror Hk))). lia.
      - pose proof (rj_mono j _ _ (H j (or_introl eq_refl))).
        pose proof (IH s t (fun k Hk => H k (or_intror Hk)) (ex_intro _ i (conj Hi Ne))). lia.
    Qed.

    Lemma rk_strict : forall s t, le_o s t -> s <> t -> rk s < rk t.
    Proof.
      intros s t H Ne. unfold rk. apply rsum_lt; [exact H |].
      destruct (all_eq_dec js s t) as [E | D]; [exfalso; apply Ne; apply sh_ext; exact E | exact D].
    Qed.

    Lemma rsum_bound : forall l s, rsum l s <= length l * hX.
    Proof.
      induction l as [| j l IH]; intros s; simpl; [lia |].
      assert (rj j (get j s) <= hX) by (unfold rj; destruct (o j); pose proof (rX_bound (get j s)); lia).
      specialize (IH s). lia.
    Qed.

    Lemma rk_bound : forall s, rk s <= rheight.
    Proof. intros s. apply rsum_bound. Qed.

    Definition rK : nat := S rheight.
    Lemma rK_big : rheight < rK. Proof. unfold rK. lia. Qed.

    Local Notation F := (fun (_ : unit) => Fsync).
    Local Notation u := (fun (_ : unit) => rupd).

    (* The resolvers are monotone for the switched orders. *)
    Hypothesis Hmono : forall v, In v js -> forall s t, le_o s t -> leo v (Fv v s) (Fv v t).

    Lemma s_incr : forall (l : unit) j x, sound unit Sh le_o F l x -> le_o x (rupd j x).
    Proof.
      intros l j x Hs k Hk. destruct (in_dec Nat.eq_dec j js) as [Hj | Hj];
        [| rewrite rupd_out; [apply leo_refl | exact Hj]].
      destruct (Nat.eq_dec k j) as [-> | Nk].
      - rewrite get_rupd_same; [| exact Hj]. pose proof (Hs j Hj) as E. cbv beta in E.
        rewrite get_Fsync in E; exact E || exact Hj.
      - rewrite get_rupd_other; [apply leo_refl | exact Nk].
    Qed.

    Lemma s_mono : forall (l : unit) j x y, le_o x y -> le_o (rupd j x) (rupd j y).
    Proof.
      intros l j x y H k Hk. destruct (in_dec Nat.eq_dec j js) as [Hj | Hj];
        [| rewrite !rupd_out by exact Hj; exact (H k Hk)].
      destruct (Nat.eq_dec k j) as [-> | Nk].
      - rewrite !get_rupd_same by exact Hj. exact (Hmono j Hj x y H).
      - rewrite !get_rupd_other by exact Nk. exact (H k Hk).
    Qed.

    Lemma s_sound : forall (l : unit) j x, sound unit Sh le_o F l x -> sound unit Sh le_o F l (rupd j x).
    Proof.
      intros l j x Hs. pose proof (s_incr l j x Hs) as Hup. intros k Hk. cbv beta.
      rewrite get_Fsync by exact Hk.
      pose proof (Hmono k Hk _ _ Hup) as M.
      destruct (in_dec Nat.eq_dec j js) as [Hj | Hj].
      - destruct (Nat.eq_dec k j) as [-> | Nk].
        + rewrite get_rupd_same by exact Hj. exact M.
        + rewrite get_rupd_other by exact Nk. pose proof (Hs k Hk) as S. cbv beta in S.
          rewrite get_Fsync in S by exact Hk. exact (leo_trans k _ _ _ S M).
      - rewrite rupd_out by exact Hj. pose proof (Hs k Hk) as S. cbv beta in S.
        rewrite get_Fsync in S by exact Hk. exact S.
    Qed.

    Lemma s_fixed : forall (l : unit) j x, Fsync x = x -> rupd j x = x.
    Proof.
      intros l j x H. destruct (in_dec Nat.eq_dec j js) as [Hj | Hj]; [| apply rupd_out; exact Hj].
      apply sh_ext. intros k Hk. destruct (Nat.eq_dec k j) as [-> | Nk].
      - rewrite get_rupd_same by exact Hj. rewrite <- (get_Fsync x j Hj), H. reflexivity.
      - apply get_rupd_other. exact Nk.
    Qed.

    Lemma s_cover : Cover unit Sh F u js.
    Proof.
      intros l x H. apply sh_ext. intros k Hk. rewrite get_Fsync by exact Hk.
      rewrite <- (get_rupd_same k x Hk). rewrite (H k Hk). reflexivity.
    Qed.

    Lemma s_decr : forall (l : unit) j x, le_o (Fsync x) x -> le_o (rupd j x) x.
    Proof.
      intros l j x Hs k Hk. destruct (in_dec Nat.eq_dec j js) as [Hj | Hj];
        [| rewrite rupd_out; [apply leo_refl | exact Hj]].
      destruct (Nat.eq_dec k j) as [-> | Nk].
      - rewrite get_rupd_same by exact Hj. pose proof (Hs j Hj) as E.
        rewrite get_Fsync in E by exact Hj. exact E.
      - rewrite get_rupd_other; [apply leo_refl | exact Nk].
    Qed.

    Lemma s_cosound : forall (l : unit) j x, le_o (Fsync x) x -> le_o (Fsync (rupd j x)) (rupd j x).
    Proof.
      intros l j x Hs. pose proof (s_decr l j x Hs) as Hdn. intros k Hk.
      rewrite get_Fsync by exact Hk.
      pose proof (Hmono k Hk _ _ Hdn) as M.
      destruct (in_dec Nat.eq_dec j js) as [Hj | Hj].
      - destruct (Nat.eq_dec k j) as [-> | Nk].
        + rewrite get_rupd_same by exact Hj. exact M.
        + rewrite get_rupd_other by exact Nk. pose proof (Hs k Hk) as S.
          rewrite get_Fsync in S by exact Hk. exact (leo_trans k _ _ _ M S).
      - rewrite rupd_out by exact Hj. pose proof (Hs k Hk) as S.
        rewrite get_Fsync in S by exact Hk. exact S.
    Qed.

    (* The least fixed point of the switched order (DistributedCycles.Lfp, gsm's reset-and-sweep). *)
    Definition slfp : Sh := Lfp unit Sh bot_o sh_eq_dec u rK js tt.

    Local Ltac dc := first
      [ exact le_o_refl | exact le_o_trans | exact le_o_antisym | exact bot_o_least | exact rk_strict
      | exact rk_bound | exact s_incr | exact s_sound | exact s_mono | exact s_fixed | exact rK_big
      | exact s_cover | exact top_o_greatest | exact s_decr | exact s_cosound ].

    Lemma slfp_fixed : Fsync slfp = slfp.
    Proof. exact (Lfp_fixed unit Sh le_o ltac:(dc) ltac:(dc) bot_o ltac:(dc) rk ltac:(dc) rheight
                    ltac:(dc) sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc) rK ltac:(dc) js
                    ltac:(dc) tt). Qed.

    Lemma slfp_least : forall p, Fsync p = p -> le_o slfp p.
    Proof. exact (Lfp_least unit Sh le_o ltac:(dc) ltac:(dc) bot_o ltac:(dc) rk ltac:(dc) rheight
                    ltac:(dc) sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc) rK ltac:(dc) js
                    ltac:(dc) tt). Qed.

    Lemma s_below : forall j h, le_o h slfp -> le_o (rupd j h) slfp.
    Proof. exact (below_u unit Sh le_o ltac:(dc) ltac:(dc) bot_o ltac:(dc) rk ltac:(dc) rheight
                    ltac:(dc) sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc) rK ltac:(dc) js
                    ltac:(dc) tt). Qed.

    Theorem sw_below : forall h0 sch, le_o h0 slfp -> Fair js sch -> Settles Sh rupd sch h0 slfp.
    Proof. exact (q1_below unit Sh le_o ltac:(dc) ltac:(dc) ltac:(dc) bot_o ltac:(dc) rk ltac:(dc)
                    rheight ltac:(dc) sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc) rK
                    ltac:(dc) js ltac:(dc) tt). Qed.

    Theorem sw_sound : forall h0 sch, le_o h0 (Fsync h0) -> Fair js sch ->
      exists q, (Fsync q = q /\ le_o h0 q /\ (forall p, Fsync p = p -> le_o h0 p -> le_o q p)) /\
                Settles Sh rupd sch h0 q.
    Proof. exact (q1_sound_settles unit Sh le_o ltac:(dc) ltac:(dc) rk ltac:(dc) rheight ltac:(dc)
                    sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc) js ltac:(dc) tt). Qed.

    Theorem sw_unique : forall sch, Fair js sch ->
      ((forall h0, Settles Sh rupd sch h0 slfp) <-> (forall p, Fsync p = p -> p = slfp)).
    Proof. exact (q1_unique_iff unit Sh le_o ltac:(dc) ltac:(dc) ltac:(dc) bot_o ltac:(dc) rk
                    ltac:(dc) rheight ltac:(dc) sh_eq_dec F u ltac:(dc) ltac:(dc) ltac:(dc) ltac:(dc)
                    rK ltac:(dc) js ltac:(dc) top_o ltac:(dc) ltac:(dc) ltac:(dc) tt). Qed.
  End Switched.

  (* ----- the kernel instance (CanonicalExecution, section Effective) ----- *)

  (* No events: the actions are the vertex updates, all internal; the canonicalizer is a constant. *)
  Definition r_ev (e : Empty_set) (s : Sh) : Sh := match e with end.
  Definition r_kind (_ : nat) : option Empty_set := None.
  Definition r_inj (e : Empty_set) : nat := match e with end.
  Definition r_ok (j : nat) : Prop := In j js.
  Definition r_flush (c : list nat) : Prop := Forall r_ok c.
  Definition r_settled (s : Sh) : Prop := Stable Sh rupd js s.
  Definition r_eqh (_ _ : list Empty_set) : Prop := True.

  Definition xr (w : list nat) (s : Sh) : Sh := xrun rupd w s.

  Lemma xr_app : forall p q s, xr (p ++ q) s = xr q (xr p s).
  Proof. intros. unfold xr, xrun. apply fold_left_app. Qed.

  Lemma prs_xr : forall sch n h, prs Sh rupd sch n h = xr (map sch (seq 0 n)) h.
  Proof.
    intros sch n h. induction n as [| n IH]; [reflexivity |].
    rewrite seq_S, map_app, xr_app, <- IH. reflexivity.
  Qed.

  Lemma settled_fixed : forall s, r_settled s <-> Fsync s = s.
  Proof.
    intros s. split.
    - intro H. apply sh_ext. intros k Hk. rewrite get_Fsync by exact Hk.
      rewrite <- (get_rupd_same k s Hk), (H k Hk). reflexivity.
    - intros H j Hj. apply sh_ext. intros k Hk. destruct (Nat.eq_dec k j) as [-> | Nk].
      + rewrite get_rupd_same by exact Hj. rewrite <- (get_Fsync s j Hj), H. reflexivity.
      + apply get_rupd_other. exact Nk.
  Qed.

  Lemma js_cases : js = [] \/ js <> [].
  Proof. destruct js; [left; reflexivity | right; discriminate]. Qed.

  (* From a state that every fair schedule settles from at q (a fixed point), a flush word exists. *)
  Lemma flush_from : forall t q, Fsync q = q -> (forall sch, Fair js sch -> Settles Sh rupd sch t q) ->
    exists c, r_flush c /\ xr c t = q.
  Proof.
    intros t q Hq H. destruct js_cases as [E | Ne].
    - exists []. split; [constructor |]. simpl. apply sh_ext. intros j Hj. rewrite E in Hj. destruct Hj.
    - destruct (H (rrs js) (rrs_fair js Ne)) as [N HN].
      exists (map (rrs js) (seq 0 N)). split.
      + apply Forall_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as [n [<- _]].
        exact (proj1 (rrs_fair js Ne) n).
      + rewrite <- prs_xr. apply HN. lia.
  Qed.

  Lemma empty_list : forall l : list Empty_set, l = [].
  Proof. intros [| [] l]. reflexivity. Qed.

  Section Kernel.
    Variable q : Sh.
    Hypothesis q_fixed : Fsync q = q.
    Variable P : Sh -> Prop.
    Hypothesis P_step : forall j s, P s -> P (rupd j s).
    Hypothesis P_settle : forall s, P s -> forall sch, Fair js sch -> Settles Sh rupd sch s q.
    Hypothesis P_fid : forall s, P s -> Fsync s = s -> s = q.

    Let N := fun (_ : Sh) => q.

    Lemma P_run : forall w s, P s -> P (xr w s).
    Proof. induction w as [| a w IH]; intros s H; [exact H |]. apply IH. apply P_step. exact H. Qed.

    Theorem kernel_E : forall s0, P s0 -> EffectiveCanon N rupd r_ok r_flush r_settled s0.
    Proof.
      intros s0 H0. split.
      - intros w _. destruct (flush_from (xr w s0) q q_fixed (P_settle _ (P_run w s0 H0))) as [c [Hc Ec]].
        exists c. split; [exact Hc |]. change (xrun rupd (w ++ c) s0) with (xr (w ++ c) s0).
        rewrite xr_app, Ec. apply settled_fixed. exact q_fixed.
      - intros w _ Hs. change (xrun rupd w s0) with (xr w s0) in *. unfold N.
        apply P_fid; [apply P_run; exact H0 | apply settled_fixed; exact Hs].
    Qed.

    Theorem kernel_esh : forall s0, P s0 ->
      Settlement rupd r_ok r_flush r_settled s0 /\
      CanonAgree N r_ev rupd r_kind r_ok r_settled s0 /\
      CanonConv rupd r_kind r_ok r_settled r_eqh s0.
    Proof.
      intros s0 H0.
      apply (proj2 (esh_exact N (fun _ => eq_refl) r_ev rupd r_kind
                      (fun a e t (H : None = Some e) => match e with end)
                      (fun a t _ => eq_refl) r_inj (fun e => match e with end) r_ok
                      (fun e => match e with end) r_flush (fun c H => H)
                      (fun c _ => proj2 (Forall_forall _ c) (fun a _ => eq_refl))
                      r_settled r_eqh s0)).
      split; [exact (kernel_E s0 H0) | split].
      - intros p [].
      - intros es1 es2 _. rewrite (empty_list es1), (empty_list es2). reflexivity.
    Qed.
  End Kernel.

  (* ----- the bridge theorems ----- *)

  Lemma switched_monotone : SgOn -> Resp -> forall o, Switching sg o ->
    forall v, In v js -> forall s t, le_o o s t -> leo o v (Fv v s) (Fv v t).
  Proof.
    intros Hon Hr o Hsw v Hv s t Hst. unfold leo. destruct (o v) eqn:Ov.
    - apply (Hr v Hv t s). intros u b Hin. pose proof (Hst u (proj1 (Hon u v b Hin))) as H.
      unfold leo in H. rewrite (Hsw u v b Hin), Ov. destruct (o u); simpl; exact H.
    - apply (Hr v Hv s t). intros u b Hin. pose proof (Hst u (proj1 (Hon u v b Hin))) as H.
      unfold leo in H. rewrite (Hsw u v b Hin), Ov. destruct (o u); simpl; exact H.
  Qed.

  (* Attempt 1: settlement and fidelity from starts at or below the least fixed point of the
     switched order (and settlement from sound starts). *)
  Theorem signed_settlement : SgOn -> Resp -> forall o, Switching sg o ->
    (Fsync (slfp o) = slfp o /\ forall p, Fsync p = p -> le_o o (slfp o) p) /\
    (forall h0 sch, le_o o h0 (slfp o) -> Fair js sch -> Settles Sh rupd sch h0 (slfp o)) /\
    (forall h0 sch, le_o o h0 (Fsync h0) -> Fair js sch ->
       exists q, (Fsync q = q /\ le_o o h0 q /\ (forall p, Fsync p = p -> le_o o h0 p -> le_o o q p)) /\
                 Settles Sh rupd sch h0 q) /\
    (forall h0, le_o o h0 (slfp o) ->
       EffectiveCanon (fun _ => slfp o) rupd r_ok r_flush r_settled h0 /\
       Settlement rupd r_ok r_flush r_settled h0 /\
       CanonAgree (fun _ => slfp o) r_ev rupd r_kind r_ok r_settled h0 /\
       CanonConv rupd r_kind r_ok r_settled r_eqh h0).
  Proof.
    intros Hon Hr o Hsw. pose proof (switched_monotone Hon Hr o Hsw) as Hm.
    split; [split; [exact (slfp_fixed o Hm) | exact (slfp_least o Hm)] |].
    split; [exact (sw_below o Hm) |]. split; [exact (sw_sound o Hm) |].
    assert (Hst : forall j s, le_o o s (slfp o) -> le_o o (rupd j s) (slfp o)) by exact (s_below o Hm).
    assert (Hse : forall s, le_o o s (slfp o) -> forall sch, Fair js sch -> Settles Sh rupd sch s (slfp o))
      by (intros s Hs sch Hf; exact (sw_below o Hm s sch Hs Hf)).
    assert (Hfi : forall s, le_o o s (slfp o) -> Fsync s = s -> s = slfp o)
      by (intros s Hs Hf; apply (le_o_antisym o); [exact Hs | exact (slfp_least o Hm s Hf)]).
    intros h0 H0. split; [exact (kernel_E (slfp o) (slfp_fixed o Hm) _ Hst Hse Hfi h0 H0) |].
    exact (kernel_esh (slfp o) (slfp_fixed o Hm) _ Hst Hse Hfi h0 H0).
  Qed.

  (* Attempt 1 with the switching produced by Harary (no negative undirected cycle). *)
  Theorem signed_settlement_harary : SgOn -> Resp ->
    (forall u h, swalk sg u u h -> h = false) ->
    exists o, Switching sg o /\
      (forall h0 sch, le_o o h0 (slfp o) -> Fair js sch -> Settles Sh rupd sch h0 (slfp o)) /\
      (forall h0, le_o o h0 (slfp o) -> EffectiveCanon (fun _ => slfp o) rupd r_ok r_flush r_settled h0).
  Proof.
    intros Hon Hr Hb. destruct (proj2 (harary_balance sg) Hb) as [o Ho]. exists o.
    destruct (signed_settlement Hon Hr o Ho) as (_ & H1 & _ & H2).
    split; [exact Ho | split; [exact H1 | intros h0 H; exact (proj1 (H2 h0 H))]].
  Qed.

  (* Attempt 2: with at most one fixed point, every fair schedule from EVERY start settles at it,
     and E holds from every start. *)
  Theorem signed_fidelity : SgOn -> Resp -> forall o, Switching sg o ->
    (forall p q, Fsync p = p -> Fsync q = q -> p = q) ->
    Fsync (slfp o) = slfp o /\
    (forall sch, Fair js sch -> forall h0, Settles Sh rupd sch h0 (slfp o)) /\
    (forall h0,
       EffectiveCanon (fun _ => slfp o) rupd r_ok r_flush r_settled h0 /\
       Settlement rupd r_ok r_flush r_settled h0 /\
       CanonAgree (fun _ => slfp o) r_ev rupd r_kind r_ok r_settled h0 /\
       CanonConv rupd r_kind r_ok r_settled r_eqh h0).
  Proof.
    intros Hon Hr o Hsw Hu. pose proof (switched_monotone Hon Hr o Hsw) as Hm.
    pose proof (slfp_fixed o Hm) as Hfix.
    assert (Hset : forall sch, Fair js sch -> forall h0, Settles Sh rupd sch h0 (slfp o)).
    { intros sch Hf. apply (proj2 (sw_unique o Hm sch Hf)). intros p Hp. exact (Hu p _ Hp Hfix). }
    split; [exact Hfix | split; [exact Hset |]].
    assert (Hfi : forall s, True -> Fsync s = s -> s = slfp o) by (intros s _ Hs; exact (Hu s _ Hs Hfix)).
    intros h0. split.
    - exact (kernel_E (slfp o) Hfix (fun _ => True) (fun _ _ _ => I) (fun s _ sch Hf => Hset sch Hf s)
               Hfi h0 I).
    - exact (kernel_esh (slfp o) Hfix (fun _ => True) (fun _ _ _ => I) (fun s _ sch Hf => Hset sch Hf s)
               Hfi h0 I).
  Qed.
End Resolver.

(* ============================================================================================ *)
(* Instances. Boolean value sets: false < true.                                                 *)
(* ============================================================================================ *)

Definition sbl (a b : bool) : Prop := implb a b = true.
Lemma sbl_refl : forall a, sbl a a. Proof. intros []; reflexivity. Qed.
Lemma sbl_trans : forall a b c, sbl a b -> sbl b c -> sbl a c.
Proof. intros [] [] []; unfold sbl; simpl; congruence. Qed.
Lemma sbl_antisym : forall a b, sbl a b -> sbl b a -> a = b.
Proof. intros [] []; unfold sbl; simpl; congruence. Qed.
Lemma sbl_bot : forall a, sbl false a. Proof. intros []; reflexivity. Qed.
Lemma sbl_top : forall a, sbl a true. Proof. intros []; reflexivity. Qed.
Definition sb2n (b : bool) : nat := if b then 1 else 0.
Lemma sb2n_strict : forall a b, sbl a b -> a <> b -> sb2n a < sb2n b.
Proof. intros [] []; unfold sbl, sb2n; simpl; intros H N; try congruence; lia. Qed.
Lemma sb2n_bound : forall a, sb2n a <= 1. Proof. intros []; simpl; lia. Qed.

(* ----- two vertices: states bool * bool ----- *)

Definition SS2 : Type := (bool * bool)%type.
Definition js2 : list nat := [0; 1].
Definition get2 (j : nat) (s : SS2) : bool :=
  match j with 0 => fst s | 1 => snd s | _ => false end.
Definition set2 (j : nat) (x : bool) (s : SS2) : SS2 :=
  match j with 0 => (x, snd s) | 1 => (fst s, x) | _ => s end.
Lemma get2_set_eq : forall j x s, In j js2 -> get2 j (set2 j x s) = x.
Proof. intros j x s [<- | [<- | []]]; reflexivity. Qed.
Lemma get2_set_neq : forall j k x s, k <> j -> get2 k (set2 j x s) = get2 k s.
Proof. intros [| [| j]] [| [| k]] x s H; try reflexivity; exfalso; apply H; reflexivity. Qed.
Lemma s2_ext : forall s t, (forall j, In j js2 -> get2 j s = get2 j t) -> s = t.
Proof.
  intros [a b] [c d] H. pose proof (H 0 (or_introl eq_refl)). pose proof (H 1 (or_intror (or_introl eq_refl))).
  simpl in *. subst. reflexivity.
Qed.

Definition z2 : SS2 := (false, false).
Definition rupd2 (Fv : nat -> SS2 -> bool) := rupd bool SS2 js2 set2 Fv.
Definition Fsync2 (Fv : nat -> SS2 -> bool) := Fsync bool SS2 js2 set2 Fv.
Definition le2 (o : nat -> bool) := le_o bool SS2 sbl js2 get2 o.
Definition Resp2 (Fv : nat -> SS2 -> bool) (sg : list (@edge bool)) := Resp bool SS2 sbl js2 get2 Fv sg.
Definition slfp2 (Fv : nat -> SS2 -> bool) (o : nat -> bool) :=
  slfp bool SS2 false true 1 bool_dec js2 get2 set2 s2_ext z2 Fv o.
Definition settled2 (Fv : nat -> SS2 -> bool) := r_settled bool SS2 js2 set2 Fv.

Lemma settled2_fixed : forall Fv s, settled2 Fv s <-> Fsync2 Fv s = s.
Proof. intros Fv s. exact (settled_fixed bool SS2 js2 get2 set2 get2_set_eq get2_set_neq s2_ext Fv s). Qed.

Ltac s2 := repeat match goal with
  | s : SS2 |- _ => destruct s
  | s : _ * _ |- _ => destruct s
  | b : bool |- _ => destruct b
  end.

(* The negative 2-cycle: x0 := not x1, x1 := x0. *)
Definition neg_F (j : nat) (s : SS2) : bool := match j with 0 => negb (snd s) | _ => fst s end.
Definition neg_sg : list (@edge bool) := [(1, 0, true); (0, 1, false)].

Theorem neg2_no_fixed_point :
  SgOn js2 neg_sg /\ Resp2 neg_F neg_sg /\
  ~ (exists o, Switching neg_sg o) /\
  (exists h, swalk neg_sg 0 0 h /\ h = true) /\
  (forall p, Fsync2 neg_F p <> p) /\
  (forall h0 sch n, ~ settled2 neg_F (prs SS2 (rupd2 neg_F) sch n h0)) /\
  (forall h0, ~ Settlement (rupd2 neg_F) (r_ok js2) (r_flush js2) (settled2 neg_F) h0).
Proof.
  assert (Hnf : forall p, Fsync2 neg_F p <> p) by (intros p H; s2; vm_compute in H; congruence).
  split; [intros u v b [E | [E | []]]; injection E as <- <- <-; simpl; tauto |].
  split.
  { intros v Hv s t H. destruct Hv as [<- | [<- | []]].
    - pose proof (H 1 true (or_introl eq_refl)) as H1. simpl in H1. revert H1. s2; unfold sbl; simpl; auto.
    - pose proof (H 0 false (or_intror (or_introl eq_refl))) as H1. simpl in H1. exact H1. }
  split.
  { intros [o Ho]. pose proof (Ho 1 0 true (or_introl eq_refl)) as E1.
    pose proof (Ho 0 1 false (or_intror (or_introl eq_refl))) as E2.
    destruct (o 0), (o 1); discriminate. }
  split.
  { exists true. split; [| reflexivity].
    change true with (xorb (xorb false false) true).
    apply (w_bwd xorb false (fun x => x) neg_sg 0 1 0 true (xorb false false)); [left; reflexivity |].
    apply (w_bwd xorb false (fun x => x) neg_sg 1 0 0 false false); [right; left; reflexivity |].
    apply w_nil. }
  split; [exact Hnf |].
  split; [intros h0 sch n H; exact (Hnf _ (proj1 (settled2_fixed _ _) H)) |].
  intros h0 H. destruct (H [] (Forall_nil _)) as [c [_ Hs]].
  exact (Hnf _ (proj1 (settled2_fixed _ _) Hs)).
Qed.

(* The positive copy-back 2-cycle: x0 := x1, x1 := x0. *)
Definition cb_F (j : nat) (s : SS2) : bool := match j with 0 => snd s | _ => fst s end.
Definition cb_sg : list (@edge bool) := [(1, 0, false); (0, 1, false)].
Definition ofalse (_ : nat) : bool := false.

Lemma cb_on : SgOn js2 cb_sg.
Proof. intros u v b [E | [E | []]]; injection E as <- <- <-; simpl; tauto. Qed.
Lemma cb_resp : Resp2 cb_F cb_sg.
Proof.
  intros v Hv s t H. destruct Hv as [<- | [<- | []]].
  - exact (H 1 false (or_introl eq_refl)).
  - exact (H 0 false (or_intror (or_introl eq_refl))).
Qed.
Lemma cb_switch : Switching cb_sg ofalse.
Proof. intros u v b [E | [E | []]]; injection E as <- <- <-; reflexivity. Qed.

Theorem copyback_ghost :
  SgOn js2 cb_sg /\ Resp2 cb_F cb_sg /\ Switching cb_sg ofalse /\
  slfp2 cb_F ofalse = (false, false) /\
  Fsync2 cb_F (true, true) = (true, true) /\
  le2 ofalse (true, true) (Fsync2 cb_F (true, true)) /\
  ~ le2 ofalse (true, true) (slfp2 cb_F ofalse) /\
  xr bool SS2 js2 set2 cb_F [0] (false, true) = (true, true) /\
  xr bool SS2 js2 set2 cb_F [1] (false, true) = (false, false) /\
  (forall sch n, prs SS2 (rupd2 cb_F) sch n (true, true) = (true, true)) /\
  ~ CanonicalFidelity (fun _ => slfp2 cb_F ofalse) (rupd2 cb_F) (r_ok js2) (settled2 cb_F) (true, true) /\
  ~ EffectiveCanon (fun _ => slfp2 cb_F ofalse) (rupd2 cb_F) (r_ok js2) (r_flush js2) (settled2 cb_F)
      (true, true).
Proof.
  assert (Hl : slfp2 cb_F ofalse = (false, false)) by (vm_compute; reflexivity).
  assert (Hf : Fsync2 cb_F (true, true) = (true, true)) by reflexivity.
  assert (Nf : ~ CanonicalFidelity (fun _ => slfp2 cb_F ofalse) (rupd2 cb_F) (r_ok js2) (settled2 cb_F)
                 (true, true)).
  { intro H. specialize (H [] (Forall_nil _) (proj2 (settled2_fixed cb_F _) Hf)).
    rewrite Hl in H. discriminate H. }
  split; [exact cb_on | split; [exact cb_resp | split; [exact cb_switch | split; [exact Hl |]]]].
  split; [exact Hf |]. split; [rewrite Hf; apply le_o_refl; exact sbl_refl |].
  split; [rewrite Hl; intro H; specialize (H 0 (or_introl eq_refl)); discriminate H |].
  split; [reflexivity | split; [reflexivity |]].
  split; [| split; [exact Nf | intros [_ H]; exact (Nf H)]].
  intros sch n. apply prs_fixed. intros [| [| j]]; reflexivity.
Qed.

(* Two negative edges (a balanced toggle): x0 := not x1, x1 := not x0; switching (false, true). *)
Definition tg_F (j : nat) (s : SS2) : bool := match j with 0 => negb (snd s) | _ => negb (fst s) end.
Definition tg_sg : list (@edge bool) := [(1, 0, true); (0, 1, true)].
Definition otg (j : nat) : bool := match j with 1 => true | _ => false end.

Theorem toggle_ghost :
  SgOn js2 tg_sg /\ Resp2 tg_F tg_sg /\ Switching tg_sg otg /\
  slfp2 tg_F otg = (false, true) /\
  Fsync2 tg_F (true, false) = (true, false) /\
  ~ le2 otg (true, false) (slfp2 tg_F otg) /\
  (forall sch n, prs SS2 (rupd2 tg_F) sch n (true, false) = (true, false)) /\
  ~ CanonicalFidelity (fun _ => slfp2 tg_F otg) (rupd2 tg_F) (r_ok js2) (settled2 tg_F) (true, false).
Proof.
  assert (Hl : slfp2 tg_F otg = (false, true)) by (vm_compute; reflexivity).
  assert (Hf : Fsync2 tg_F (true, false) = (true, false)) by reflexivity.
  split; [intros u v b [E | [E | []]]; injection E as <- <- <-; simpl; tauto |].
  split.
  { intros v Hv s t H. destruct Hv as [<- | [<- | []]].
    - pose proof (H 1 true (or_introl eq_refl)) as H1. simpl in H1. revert H1. s2; unfold sbl; simpl; auto.
    - pose proof (H 0 true (or_intror (or_introl eq_refl))) as H1. simpl in H1. revert H1. s2; unfold sbl; simpl; auto. }
  split; [intros u v b [E | [E | []]]; injection E as <- <- <-; reflexivity |].
  split; [exact Hl | split; [exact Hf |]].
  split; [rewrite Hl; intro H; specialize (H 0 (or_introl eq_refl)); discriminate H |].
  split; [intros sch n; apply prs_fixed; intros [| [| j]]; reflexivity |].
  intro H. specialize (H [] (Forall_nil _) (proj2 (settled2_fixed tg_F _) Hf)).
  rewrite Hl in H. discriminate H.
Qed.

(* Balance cannot be dropped from attempt 2: x0 := x0, x1 := x0 and not x1. One fixed point,
   a negative self-loop, and no schedule from x0 = 1 ever settles. *)
Definition uu_F (j : nat) (s : SS2) : bool := match j with 0 => fst s | _ => fst s && negb (snd s) end.
Definition uu_sg : list (@edge bool) := [(0, 0, false); (0, 1, false); (1, 1, true)].

Lemma uu_fst : forall j s, fst (rupd2 uu_F j s) = fst s.
Proof. intros [| [| j]] s; s2; reflexivity. Qed.

Theorem unbalanced_unique_oscillates :
  SgOn js2 uu_sg /\ Resp2 uu_F uu_sg /\ ~ (exists o, Switching uu_sg o) /\
  (forall p q, Fsync2 uu_F p = p -> Fsync2 uu_F q = q -> p = q) /\
  Fsync2 uu_F (false, false) = (false, false) /\
  (forall b sch n, ~ settled2 uu_F (prs SS2 (rupd2 uu_F) sch n (true, b))) /\
  (forall b, ~ Settlement (rupd2 uu_F) (r_ok js2) (r_flush js2) (settled2 uu_F) (true, b)).
Proof.
  assert (Hu : forall p, Fsync2 uu_F p = p -> p = (false, false)) by (intros p H; s2; vm_compute in H; congruence).
  assert (Hns : forall s, fst s = true -> ~ settled2 uu_F s).
  { intros s E H. apply settled2_fixed in H. destruct s as [a b]. simpl in E. subst a. destruct b;
      vm_compute in H; congruence. }
  assert (Hrun : forall w s, fst s = true -> fst (xr bool SS2 js2 set2 uu_F w s) = true).
  { induction w as [| a w IH]; intros s E; [exact E |]. apply IH. exact (eq_trans (uu_fst a s) E). }
  split; [intros u v b [E | [E | [E | []]]]; injection E as <- <- <-; simpl; tauto |].
  split.
  { intros v Hv s t H. destruct Hv as [<- | [<- | []]].
    - exact (H 0 false (or_introl eq_refl)).
    - pose proof (H 0 false (or_intror (or_introl eq_refl))) as H1.
      pose proof (H 1 true (or_intror (or_intror (or_introl eq_refl)))) as H2.
      simpl in H1, H2. revert H1 H2. s2; unfold sbl; simpl; auto. }
  split; [intros [o Ho]; pose proof (Ho 1 1 true (or_intror (or_intror (or_introl eq_refl)))) as E;
          destruct (o 1); discriminate |].
  split; [intros p q Hp Hq; rewrite (Hu p Hp), (Hu q Hq); reflexivity |].
  split; [reflexivity |].
  split.
  { intros b sch n. apply Hns. rewrite (prs_xr bool SS2 js2 set2 uu_F). apply Hrun. reflexivity. }
  intros b H. destruct (H [] (Forall_nil _)) as [c [_ Hs]].
  exact (Hns _ (Hrun ([] ++ c) (true, b) eq_refl) Hs).
Qed.

(* Attempt 1 with a negative edge and a non-trivial switching: x0 := true, x1 := not x0,
   switching (false, true). Every start is below slfp = (true, false) in the switched order. *)
Definition nc_F (j : nat) (s : SS2) : bool := match j with 0 => true | _ => negb (fst s) end.
Definition nc_sg : list (@edge bool) := [(0, 1, true)].

Theorem neg_chain_settles :
  slfp2 nc_F otg = (true, false) /\
  (forall h0, le2 otg h0 (slfp2 nc_F otg)) /\
  (forall h0 sch, Fair js2 sch -> Settles SS2 (rupd2 nc_F) sch h0 (true, false)) /\
  (forall h0, EffectiveCanon (fun _ => slfp2 nc_F otg) (rupd2 nc_F) (r_ok js2) (r_flush js2)
                (settled2 nc_F) h0).
Proof.
  assert (Hon : SgOn js2 nc_sg) by (intros u v b [E | []]; injection E as <- <- <-; simpl; tauto).
  assert (Hr : Resp2 nc_F nc_sg).
  { intros v Hv s t H. destruct Hv as [<- | [<- | []]]; [reflexivity |].
    pose proof (H 0 true (or_introl eq_refl)) as H1. simpl in H1. revert H1. s2; unfold sbl; simpl; auto. }
  assert (Hs : Switching nc_sg otg) by (intros u v b [E | []]; injection E as <- <- <-; reflexivity).
  assert (Hl : slfp2 nc_F otg = (true, false)) by (vm_compute; reflexivity).
  assert (Hlow : forall h0, le2 otg h0 (slfp2 nc_F otg)).
  { rewrite Hl. intros h0 j Hj. destruct Hj as [<- | [<- | []]]; s2; reflexivity. }
  destruct (signed_settlement bool SS2 sbl sbl_refl sbl_trans sbl_antisym false true sbl_bot sbl_top
              sb2n sb2n_strict 1 sb2n_bound bool_dec js2 get2 set2 get2_set_eq get2_set_neq s2_ext z2
              nc_F nc_sg Hon Hr otg Hs) as (_ & H1 & _ & H2).
  split; [exact Hl | split; [exact Hlow |]].
  split; [intros h0 sch Hf; rewrite <- Hl; exact (H1 h0 sch (Hlow h0) Hf) |].
  intros h0. exact (proj1 (H2 h0 (Hlow h0))).
Qed.

(* ----- three vertices: states bool * bool * bool (DistributedCycles.R3) ----- *)

Definition get3 (j : nat) (s : R3) : bool :=
  match s with (a, b, c) => match j with 0 => a | 1 => b | 2 => c | _ => false end end.
Definition set3 (j : nat) (x : bool) (s : R3) : R3 :=
  match s with (a, b, c) => match j with 0 => (x, b, c) | 1 => (a, x, c) | 2 => (a, b, x) | _ => (a, b, c) end end.
Lemma get3_set_eq : forall j x s, In j r3js -> get3 j (set3 j x s) = x.
Proof. intros j x [[a b] c] [<- | [<- | [<- | []]]]; reflexivity. Qed.
Lemma get3_set_neq : forall j k x s, k <> j -> get3 k (set3 j x s) = get3 k s.
Proof.
  intros [| [| [| j]]] [| [| [| k]]] x [[a b] c] H; try reflexivity; exfalso; apply H; reflexivity.
Qed.
Lemma s3_ext : forall s t, (forall j, In j r3js -> get3 j s = get3 j t) -> s = t.
Proof.
  intros [[a b] c] [[d e] f] H. pose proof (H 0 (or_introl eq_refl)).
  pose proof (H 1 (or_intror (or_introl eq_refl))). pose proof (H 2 (or_intror (or_intror (or_introl eq_refl)))).
  simpl in *. subst. reflexivity.
Qed.

Definition rupd3 (Fv : nat -> R3 -> bool) := rupd bool R3 r3js set3 Fv.
Definition Fsync3 (Fv : nat -> R3 -> bool) := Fsync bool R3 r3js set3 Fv.
Definition le3 (o : nat -> bool) := le_o bool R3 sbl r3js get3 o.
Definition slfp3 (Fv : nat -> R3 -> bool) (o : nat -> bool) :=
  slfp bool R3 false true 1 bool_dec r3js get3 set3 s3_ext r3bot Fv o.
Definition settled3 (Fv : nat -> R3 -> bool) := r_settled bool R3 r3js set3 Fv.

Ltac s3 := repeat match goal with
  | s : R3 |- _ => destruct s
  | s : _ * _ |- _ => destruct s
  | b : bool |- _ => destruct b
  end.

Lemma prs_ext : forall (Sh : Type) (up1 up2 : nat -> Sh -> Sh), (forall j x, up1 j x = up2 j x) ->
  forall sch n h, prs Sh up1 sch n h = prs Sh up2 sch n h.
Proof.
  intros Sh up1 up2 H sch n h. induction n as [| n IH]; [reflexivity |]. simpl. rewrite IH. apply H.
Qed.

(* The positive 3-ring x0 := x1, x1 := x2, x2 := x0 is dist_ring_livelock's r3u. *)
Definition ring_F (j : nat) (s : R3) : bool := match j with 0 => get3 1 s | 1 => get3 2 s | _ => get3 0 s end.
Definition ring_sg : list (@edge bool) := [(1, 0, false); (2, 1, false); (0, 2, false)].

Lemma ring_is_r3u : forall j x, rupd3 ring_F j x = r3u tt j x.
Proof. intros [| [| [| j]]] [[a b] c]; reflexivity. Qed.

Theorem ring_needs_low_start :
  SgOn r3js ring_sg /\ Resp bool R3 sbl r3js get3 ring_F ring_sg /\ Switching ring_sg ofalse /\
  slfp3 ring_F ofalse = (false, false, false) /\
  ~ le3 ofalse r3h0 (slfp3 ring_F ofalse) /\
  Fair r3js r3sg /\
  (forall n, ~ settled3 ring_F (prs R3 (rupd3 ring_F) r3sg n r3h0)) /\
  Fsync3 ring_F (true, true, true) = (true, true, true).
Proof.
  destruct dist_ring_livelock as (_ & _ & _ & _ & _ & _ & _ & Hf & nS & _).
  split; [intros u v b [E | [E | [E | []]]]; injection E as <- <- <-; simpl; tauto |].
  split.
  { intros v Hv s t H. destruct Hv as [<- | [<- | [<- | []]]].
    - exact (H 1 false (or_introl eq_refl)).
    - exact (H 2 false (or_intror (or_introl eq_refl))).
    - exact (H 0 false (or_intror (or_intror (or_introl eq_refl)))). }
  split; [intros u v b [E | [E | [E | []]]]; injection E as <- <- <-; reflexivity |].
  assert (Hl : slfp3 ring_F ofalse = (false, false, false)) by (vm_compute; reflexivity).
  split; [exact Hl |].
  split; [rewrite Hl; intro H; specialize (H 0 (or_introl eq_refl)); discriminate H |].
  split; [exact Hf |].
  split; [| reflexivity].
  intros n H. apply (nS n). rewrite <- (prs_ext R3 _ _ ring_is_r3u). intros j Hj.
  rewrite <- ring_is_r3u. exact (H j Hj).
Qed.

(* Attempt 2 outside every sign condition: x0 := x1, x1 := x0 and x2, x2 := false. A positive
   directed cycle 0 -> 1 -> 0, one fixed point; every fair schedule from every start settles. *)
Definition up_F (j : nat) (s : R3) : bool :=
  match j with 0 => get3 1 s | 1 => get3 0 s && get3 2 s | _ => false end.
Definition up_sg : list (@edge bool) := [(1, 0, false); (0, 1, false); (2, 1, false)].

Theorem unique_pos_cycle :
  In (0, 1, false) up_sg /\ In (1, 0, false) up_sg /\
  slfp3 up_F ofalse = (false, false, false) /\
  (forall p q, Fsync3 up_F p = p -> Fsync3 up_F q = q -> p = q) /\
  (forall sch, Fair r3js sch -> forall h0, Settles R3 (rupd3 up_F) sch h0 (false, false, false)) /\
  (forall h0, EffectiveCanon (fun _ => slfp3 up_F ofalse) (rupd3 up_F) (r_ok r3js) (r_flush r3js)
                (settled3 up_F) h0).
Proof.
  assert (Hon : SgOn r3js up_sg) by (intros u v b [E | [E | [E | []]]]; injection E as <- <- <-; simpl; tauto).
  assert (Hr : Resp bool R3 sbl r3js get3 up_F up_sg).
  { intros v Hv s t H. destruct Hv as [<- | [<- | [<- | []]]].
    - exact (H 1 false (or_introl eq_refl)).
    - pose proof (H 0 false (or_intror (or_introl eq_refl))) as H1.
      pose proof (H 2 false (or_intror (or_intror (or_introl eq_refl)))) as H2.
      revert H1 H2. s3; unfold sbl; simpl; auto.
    - reflexivity. }
  assert (Hs : Switching up_sg ofalse) by (intros u v b [E | [E | [E | []]]]; injection E as <- <- <-; reflexivity).
  assert (Hu0 : forall p, Fsync3 up_F p = p -> p = (false, false, false))
    by (intros p H; s3; vm_compute in H; congruence).
  assert (Hu : forall p q, Fsync3 up_F p = p -> Fsync3 up_F q = q -> p = q)
    by (intros p q Hp Hq; rewrite (Hu0 p Hp), (Hu0 q Hq); reflexivity).
  assert (Hl : slfp3 up_F ofalse = (false, false, false)) by (vm_compute; reflexivity).
  destruct (signed_fidelity bool R3 sbl sbl_refl sbl_trans sbl_antisym false true sbl_bot sbl_top
              sb2n sb2n_strict 1 sb2n_bound bool_dec r3js get3 set3 get3_set_eq get3_set_neq s3_ext r3bot
              up_F up_sg Hon Hr ofalse Hs Hu) as (_ & H1 & H2).
  split; [right; left; reflexivity | split; [left; reflexivity | split; [exact Hl | split; [exact Hu |]]]].
  split; [intros sch Hf h0; rewrite <- Hl; exact (H1 sch Hf h0) |].
  intros h0. exact (proj1 (H2 h0)).
Qed.

(* ----- breaks outside the Boolean resolver model ----- *)

(* Value sets need a top: flip_noflush's swap on {fz < fa, fb} is monotone with one fixed point,
   but the order has no greatest element, and from fa no propagation word reaches quiescence. *)
Theorem flip_needs_top :
  (forall x y, fle x y -> fle (fsw x) (fsw y)) /\
  (forall p, fsw p = p -> p = fz) /\
  ~ (exists t, forall x, fle x t) /\
  ~ FlushR unit Fl fz fu1 fjs1 unit fid false (tt, fa).
Proof.
  split; [intros [] [] [H | H]; unfold fle; simpl; try discriminate; auto |].
  split; [intros [] H; simpl in H; congruence |].
  split; [| exact (proj2 (proj2 (proj2 (proj2 flip_noflush))))].
  intros [t Ht]. pose proof (Ht fa) as Ha. pose proof (Ht fb) as Hb.
  destruct t; unfold fle in Ha, Hb; intuition discriminate.
Qed.

(* Unsigned maps: the 3-cycle permutation of {t0, t1, t2} is neither monotone nor antitone for any
   partial order with a least element, and has no fixed point. *)
Definition cyc3 (x : tri) : tri := match x with t0 => t1 | t1 => t2 | t2 => t0 end.

Theorem cyc3_unsignable :
  (forall x, cyc3 x <> x) /\
  forall (le : tri -> tri -> Prop),
    (forall x y, le x y -> le y x -> x = y) ->
    forall b, (forall x, le b x) ->
    ~ (forall x y, le x y -> le (cyc3 x) (cyc3 y)) /\
    ~ (forall x y, le x y -> le (cyc3 y) (cyc3 x)).
Proof.
  assert (C3 : forall x, cyc3 (cyc3 (cyc3 x)) = x) by (intros []; reflexivity).
  split; [intros [] H; discriminate H |].
  intros le Ha b Hb. split.
  - intros Hm. pose proof (Hm b (cyc3 (cyc3 b)) (Hb _)) as H. rewrite C3 in H.
    pose proof (Ha _ _ H (Hb _)) as E. destruct b; discriminate E.
  - intros Hm.
    assert (Top : forall y, le y (cyc3 b)).
    { intros y. pose proof (Hm b (cyc3 (cyc3 y)) (Hb _)) as H. rewrite C3 in H. exact H. }
    pose proof (Hm _ _ (Top (cyc3 (cyc3 b)))) as H. rewrite C3 in H.
    pose proof (Ha _ _ H (Hb _)) as E. destruct b; discriminate E.
Qed.

(* Non-monotone (lossy) resolvers are never certified: x1 := x0 xor x1 reads x0 neither
   monotonically nor antitonically, so a global signed graph that certifies it (Resp) must carry
   both signs on the arc 0 -> 1 (or otherwise fail), and then no switching exists. *)
Definition xor_F (j : nat) (s : SS2) : bool := match j with 0 => fst s | _ => xorb (fst s) (snd s) end.

Theorem xor_no_certificate : forall sg, SgOn js2 sg -> Resp2 xor_F sg -> ~ exists o, Switching sg o.
Proof.
  intros sg Hon Hr [o Ho].
  pose proof (switched_monotone bool SS2 sbl js2 get2 xor_F sg Hon Hr o Ho 1 (or_intror (or_introl eq_refl)))
    as Hm.
  assert (L : forall b, le_o bool SS2 sbl js2 get2 o (o 0, b) (negb (o 0), b)).
  { intros b j [<- | [<- | []]]; [| apply (leo_refl bool sbl sbl_refl)].
    unfold leo. simpl. destruct (o 0); reflexivity. }
  pose proof (Hm _ _ (L false)) as H1. pose proof (Hm _ _ (L true)) as H2.
  unfold leo in H1, H2. simpl in H1, H2. destruct (o 0), (o 1); discriminate.
Qed.
