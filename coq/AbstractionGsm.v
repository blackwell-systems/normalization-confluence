(* AbstractionGsm.v: the gsm instantiation of AbstractionCutoff.v (roadmap item 8, step 2; gsm
   roadmap item 1b). Axiom-free.

   gsm's Build, on a registry declared with Abstract, checks over the representatives reps N C:
   repair reaches a valid state from every representative state (TermD), CC1 for the checked event
   pairs at every VALID representative state (not CC2), and which events are idempotent at the
   valid representative states. Its runtime normalizes every input before applying an event, so
   runs start from valid states. AbstractionCutoff.v transfers CC1 and CC2 at every state; this file
   transfers exactly what gsm checks and what its runtime needs. Events of the registry are the
   in-signature ones (kind below nk, m parameters); gsm's events take no parameters (m = 0), and
   every statement here is for general m, so it specializes with cutoff N = n.

   - cc1_valid_abs: CC1 for the pairs of a relation I on event kinds, at every valid state, holds
     over Z iff it holds over reps N C, for N >= n + 2m (cc1v_order_type: one check per order type).
   - idem_abs, idem_valid_abs: an event kind is idempotent (its governed step applied twice equals
     once) at every state, or at every valid state, over Z iff over reps N C, for N >= n + m
     (idem_order_type). idem_runtime_abs: the same for gsm's runtime step (normalize, apply,
     normalize), from every integer state. So idempotence transfers, and gsm can list NotIdempotent
     from the representatives: the list is exact for every integer state.
   - Fragment preservation: OIMap g (g keeps n variables and commutes with every order isomorphism
     fixing C) is closed under composition (oimap_comp) and iteration (oimap_itr), repair is one
     (oimap_rp), order-invariant maps output only input values and constants (oimap_closed), and an
     event after an order-invariant map is order invariant (oi_ap_after). The repair-first
     registry apR K (gsm's runtime: repair to validity, then apply the event) stays in the fragment
     (derived_ordinv, derived_shaped).
   - The derived-registry route: under TermK, CC1 at every state of the repair-first registry is
     exactly CC1 at every valid state of the original (cc1_derived_valid), so cc1_abs applied to the
     derived registry decides it too (cc1_valid_derived_abs). This mechanizes the prose argument.
   - gsm_abs_exact: given TermD over reps N C (N >= n + 2m), CC1 for I at the valid representative
     states holds iff, over all of Z, from every valid state any two event sequences that differ
     by reordering adjacent I-independent events reach the same state (Trace.run_tequiv, the same
     guarantee as TableCheck.check_tables_converges for table machines).
   - gsm_abs_sound: under the same two checks, gsm's runtime step (govK (apR K)) gives the same
     state for trace-equivalent sequences from EVERY integer start, the zero state included;
     gsm_abs_sound_all: any permutation, when every pair is checked.
   - Finite checks: cc1v_check, idemv_check, with their exact specifications.
   Non-vacuity.
   - capped_*: the capped inventory of AbstractionCutoff.v (m = 1) with every new statement
     instantiated over 7 representatives.
   - inventory_*: gsm's documented example (stock, ship_a, ship_b; receive_a, receive_b; cap 5;
     m = 0, cutoff N = n = 3): every permutation of receive events converges from every integer
     state, and both events are idempotent at every valid integer state.
   - swapxy_*: an order-invariant event that is not idempotent; the representative check reports it,
     with an integer witness.
   Boundary.
   - idem13_*: an undeclared exact test (swap x and y when z = 13) is idempotent at every
     representative state of reps 3 [] and not over Z; ord_frag refuses it. *)

Require Import NC.Newman NC.Governance NC.SymmetryCutoff NC.AbstractionCutoff NC.Trace.
From Coq Require Import List Arith Lia Bool ZArith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Lemma implb_true : forall a b, implb a b = true <-> (a = true -> b = true).
Proof. intros [|] [|]; simpl; split; intros H; try reflexivity; try discriminate; auto. Qed.

Lemma incl_l : forall (a b c : list Z), incl a (a ++ b ++ c).
Proof. intros a b c v Hv. apply in_or_app. left. exact Hv. Qed.

Section Gsm.
  Variable C : list Z.                          (* declared constants *)
  Variable n m nk : nat.                        (* variables, event parameters, event kinds *)
  Variable ap : nat * list Z -> list Z -> list Z.
  Variable rp : list Z -> list Z.
  Variable vd : list Z -> bool.

  Local Notation G K := (govK ap rp K).

  (* ============================================================================================ *)
  (* The conditions gsm checks, over Z and over the representatives.                              *)
  (* ============================================================================================ *)

  (* The events of the registry: a declared kind with m parameters. *)
  Definition InSig (e : nat * list Z) : Prop := (fst e < nk)%nat /\ length (snd e) = m.

  (* CC1 for the pairs of kinds related by I, at every valid state (gsm's verifyCC / absWitness). *)
  Definition CC1VZ (K : nat) (I : nat -> nat -> Prop) : Prop :=
    forall s k1 p1 k2 p2, length s = n -> vd s = true ->
      (k1 < nk)%nat -> (k2 < nk)%nat -> length p1 = m -> length p2 = m -> I k1 k2 ->
      G K (k2, p2) (G K (k1, p1) s) = G K (k1, p1) (G K (k2, p2) s).

  Definition CC1VD (K N : nat) (I : nat -> nat -> Prop) : Prop :=
    forall s k1 p1 k2 p2, In s (tup (reps N C) n) -> vd s = true ->
      (k1 < nk)%nat -> (k2 < nk)%nat -> In p1 (tup (reps N C) m) -> In p2 (tup (reps N C) m) ->
      I k1 k2 ->
      G K (k2, p2) (G K (k1, p1) s) = G K (k1, p1) (G K (k2, p2) s).

  (* Idempotence of kind k: the governed step applied twice equals once. *)
  Definition IdemZ (K k : nat) : Prop :=
    forall s p, length s = n -> length p = m -> G K (k, p) (G K (k, p) s) = G K (k, p) s.
  Definition IdemVZ (K k : nat) : Prop :=
    forall s p, length s = n -> vd s = true -> length p = m ->
      G K (k, p) (G K (k, p) s) = G K (k, p) s.
  Definition IdemD (K N k : nat) : Prop :=
    forall s p, In s (tup (reps N C) n) -> In p (tup (reps N C) m) ->
      G K (k, p) (G K (k, p) s) = G K (k, p) s.
  Definition IdemVD (K N k : nat) : Prop :=
    forall s p, In s (tup (reps N C) n) -> vd s = true -> In p (tup (reps N C) m) ->
      G K (k, p) (G K (k, p) s) = G K (k, p) s.

  (* The finite checks. *)
  Definition cc1v_check (K N : nat) (Ib : nat -> nat -> bool) : bool :=
    forallb (fun s => implb (vd s)
      (forallb (fun k1 => forallb (fun k2 => implb (Ib k1 k2)
        (forallb (fun p1 => forallb (fun p2 =>
           leq (G K (k2, p2) (G K (k1, p1) s)) (G K (k1, p1) (G K (k2, p2) s)))
           (tup (reps N C) m)) (tup (reps N C) m)))
        (seq 0 nk)) (seq 0 nk)))
      (tup (reps N C) n).

  Definition idemv_check (K N k : nat) : bool :=
    forallb (fun s => implb (vd s)
      (forallb (fun p => leq (G K (k, p) (G K (k, p) s)) (G K (k, p) s)) (tup (reps N C) m)))
      (tup (reps N C) n).

  Theorem cc1v_check_spec : forall K N Ib,
    cc1v_check K N Ib = true <-> CC1VD K N (fun a b => Ib a b = true).
  Proof.
    intros K N Ib. unfold cc1v_check, CC1VD. rewrite forallb_forall. split.
    - intros H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI. specialize (H s Hs).
      rewrite implb_true in H. specialize (H Hv). rewrite forallb_forall in H.
      specialize (H k1 (proj2 (in_seq nk 0 k1) (conj (Nat.le_0_l _) H1))).
      rewrite forallb_forall in H. specialize (H k2 (proj2 (in_seq nk 0 k2) (conj (Nat.le_0_l _) H2))).
      rewrite implb_true in H. specialize (H HI). rewrite forallb_forall in H.
      specialize (H p1 Hp1). rewrite forallb_forall in H. apply leq_spec. exact (H p2 Hp2).
    - intros H s Hs. apply implb_true. intros Hv. apply forallb_forall. intros k1 H1.
      apply forallb_forall. intros k2 H2. apply implb_true. intros HI.
      apply forallb_forall. intros p1 Hp1. apply forallb_forall. intros p2 Hp2.
      apply in_seq in H1. apply in_seq in H2. apply leq_spec.
      apply H; [exact Hs | exact Hv | lia | lia | exact Hp1 | exact Hp2 | exact HI].
  Qed.

  Theorem idemv_check_spec : forall K N k, idemv_check K N k = true <-> IdemVD K N k.
  Proof.
    intros K N k. unfold idemv_check, IdemVD. rewrite forallb_forall. split.
    - intros H s p Hs Hv Hp. specialize (H s Hs). rewrite implb_true in H. specialize (H Hv).
      rewrite forallb_forall in H. apply leq_spec. exact (H p Hp).
    - intros H s Hs. apply implb_true. intros Hv. apply forallb_forall. intros p Hp.
      apply leq_spec. exact (H s p Hs Hv Hp).
  Qed.

  (* ============================================================================================ *)
  (* One check per order type, and the transfers.                                                 *)
  (* ============================================================================================ *)

  Section Transfer.
    Hypothesis HS : Shaped n m nk ap rp vd.
    Hypothesis HO : OrdInv C n ap rp vd.

    (* CC1 at a valid state has the truth value of every instance with the same order type. *)
    Theorem cc1v_order_type : forall K f s k1 p1 k2 p2, length s = n -> OIso C (s ++ p1 ++ p2) f ->
      ((vd s = true -> G K (k2, p2) (G K (k1, p1) s) = G K (k1, p1) (G K (k2, p2) s)) <->
       (vd (map f s) = true ->
        G K (k2, map f p2) (G K (k1, map f p1) (map f s)) =
        G K (k1, map f p1) (G K (k2, map f p2) (map f s)))).
    Proof.
      intros K f s k1 p1 k2 p2 Hs Hf.
      assert (Hsx : incl s ((s ++ p1 ++ p2) ++ C)).
      { intros v Hv. apply in_or_app. left. apply in_or_app. left. exact Hv. }
      rewrite (oi_vd C n ap rp vd HO f s Hs (oiso_sub C _ s f Hsx Hf)).
      pose proof (cc1_order_type C n m nk ap rp vd HS HO K f s k1 p1 k2 p2 Hs Hf) as E.
      split; intros H Hv; apply E, H, Hv.
    Qed.

    (* Idempotence has the truth value of every instance with the same order type. *)
    Theorem idem_order_type : forall K f s k p, length s = n -> OIso C (s ++ p) f ->
      (G K (k, p) (G K (k, p) s) = G K (k, p) s <->
       G K (k, map f p) (G K (k, map f p) (map f s)) = G K (k, map f p) (map f s)).
    Proof.
      intros K f s k p Hs Hf. set (X := s ++ p).
      assert (T1 : incl (s ++ p) (X ++ C)) by (intros v Hv; apply in_or_app; left; exact Hv).
      assert (Cl1 : incl (G K (k, p) s) (X ++ C)).
      { intros v Hv. pose proof (gov_closed C n m nk ap rp vd HS HO K k p s v Hs Hv) as H.
        rewrite app_assoc in H. exact H. }
      assert (T2 : incl (G K (k, p) s ++ p) (X ++ C)).
      { intros v Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv]; [exact (Cl1 v Hv)|].
        apply in_or_app. left. unfold X. apply in_or_app. right. exact Hv. }
      pose proof (G_len n m nk ap rp vd HS K (k, p) s Hs) as L1.
      assert (Cl2 : incl (G K (k, p) (G K (k, p) s)) (X ++ C)).
      { intros v Hv. pose proof (gov_closed C n m nk ap rp vd HS HO K k p _ v L1 Hv) as H.
        rewrite app_assoc in H. apply in_app_or in H. destruct H as [H | H];
          [exact (T2 v H) | apply in_or_app; right; exact H]. }
      rewrite (gov_map C n m nk ap rp vd HS HO K f X k p s Hs T1 Hf).
      rewrite (gov_map C n m nk ap rp vd HS HO K f X k p _ L1 T2 Hf).
      split; [intros E; rewrite E; reflexivity|].
      intros E. exact (oiso_inj C X f _ _ Hf Cl2 Cl1 E).
    Qed.

    (* The compression of s ++ p into the representatives. *)
    Lemma cmp_tup : forall N X l k, (length X <= N)%nat -> incl l X -> length l = k ->
      In (map (cmp C X) l) (tup (reps N C) k).
    Proof.
      intros N X l k HN Hi Hl. apply tup_map; [exact Hl|].
      intros x Hx. apply cmp_in_reps; [exact HN | exact (Hi x Hx)].
    Qed.

    Lemma tup_len : forall N k l, In l (tup (reps N C) k) -> length l = k.
    Proof. intros N k l H. apply tup_spec in H. apply H. Qed.

    (* CC1 at the valid states, for the pairs of I: over Z iff over reps N C, N >= n + 2m. *)
    Theorem cc1_valid_abs : forall K N I, (n + 2 * m <= N)%nat -> (CC1VZ K I <-> CC1VD K N I).
    Proof.
      intros K N I HN. split.
      - intros H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI.
        exact (H s k1 p1 k2 p2 (tup_len N n s Hs) Hv H1 H2 (tup_len N m p1 Hp1) (tup_len N m p2 Hp2) HI).
      - intros H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI.
        set (X := s ++ p1 ++ p2). set (f := cmp C X). destruct (compress C X) as [Hf _].
        assert (HX : (length X <= N)%nat) by (unfold X; rewrite !lenA; lia).
        apply (proj2 (cc1v_order_type K f s k1 p1 k2 p2 Hs Hf)); [|exact Hv].
        intros Hv'. apply H; try assumption.
        + apply cmp_tup; [exact HX | apply incl_l | exact Hs].
        + apply cmp_tup; [exact HX | | exact Hp1]. intros v Hv0. unfold X. rewrite !in_app_iff. tauto.
        + apply cmp_tup; [exact HX | | exact Hp2]. intros v Hv0. unfold X. rewrite !in_app_iff. tauto.
    Qed.

    (* Idempotence at every state: over Z iff over reps N C, N >= n + m. *)
    Theorem idem_abs : forall K N k, (n + m <= N)%nat -> (IdemZ K k <-> IdemD K N k).
    Proof.
      intros K N k HN. split.
      - intros H s p Hs Hp. exact (H s p (tup_len N n s Hs) (tup_len N m p Hp)).
      - intros H s p Hs Hp.
        set (X := s ++ p). set (f := cmp C X). destruct (compress C X) as [Hf _].
        assert (HX : (length X <= N)%nat) by (unfold X; rewrite lenA; lia).
        apply (proj2 (idem_order_type K f s k p Hs Hf)). apply H.
        + apply cmp_tup; [exact HX | | exact Hs]. intros v Hv. unfold X. rewrite in_app_iff. tauto.
        + apply cmp_tup; [exact HX | | exact Hp]. intros v Hv. unfold X. rewrite in_app_iff. tauto.
    Qed.

    (* Idempotence at every valid state: over Z iff over reps N C, N >= n + m. *)
    Theorem idem_valid_abs : forall K N k, (n + m <= N)%nat -> (IdemVZ K k <-> IdemVD K N k).
    Proof.
      intros K N k HN. split.
      - intros H s p Hs Hv Hp. exact (H s p (tup_len N n s Hs) Hv (tup_len N m p Hp)).
      - intros H s p Hs Hv Hp.
        set (X := s ++ p). set (f := cmp C X). destruct (compress C X) as [Hf _].
        assert (HX : (length X <= N)%nat) by (unfold X; rewrite lenA; lia).
        assert (Hsx : incl s (X ++ C)).
        { intros v Hv0. apply in_or_app. left. unfold X. apply in_or_app. left. exact Hv0. }
        apply (proj2 (idem_order_type K f s k p Hs Hf)). apply H.
        + apply cmp_tup; [exact HX | | exact Hs]. intros v Hv0. unfold X. rewrite in_app_iff. tauto.
        + rewrite (oi_vd C n ap rp vd HO f s Hs (oiso_sub C X s f Hsx Hf)). exact Hv.
        + apply cmp_tup; [exact HX | | exact Hp]. intros v Hv0. unfold X. rewrite in_app_iff. tauto.
    Qed.
  End Transfer.

  (* ============================================================================================ *)
  (* Fragment preservation: order-invariant maps compose; repair-then-event stays in the fragment. *)
  (* ============================================================================================ *)

  (* g keeps n variables and commutes with every order isomorphism of its input fixing C. *)
  Definition OIMap (g : list Z -> list Z) : Prop :=
    (forall s, length s = n -> length (g s) = n) /\
    (forall f s, length s = n -> OIso C s f -> g (map f s) = map f (g s)).

  (* No fresh values: an order-invariant map outputs only input values and constants. *)
  Theorem oimap_closed : forall g, OIMap g -> forall s v, length s = n -> In v (g s) -> In v (s ++ C).
  Proof.
    intros g [_ Hg] s v Hs Hv.
    destruct (in_dec Z.eq_dec v (s ++ C)) as [Hi | Hn]; [exact Hi|]. exfalso.
    pose proof (Hg (bump (s ++ C)) s Hs (bump_oiso C s)) as E.
    rewrite (bump_fix _ s) in E by (intros x Hx; apply in_or_app; left; exact Hx).
    symmetry in E. exact (bump_out _ v Hn (map_fix_pt _ _ v E Hv)).
  Qed.

  Theorem oimap_id : OIMap (fun s => s).
  Proof. split; [intros s H; exact H | reflexivity]. Qed.

  (* The composition of order-invariant maps is order invariant. *)
  Theorem oimap_comp : forall g1 g2, OIMap g1 -> OIMap g2 -> OIMap (fun s => g1 (g2 s)).
  Proof.
    intros g1 g2 H1 H2. split.
    - intros s Hs. apply (proj1 H1). apply (proj1 H2). exact Hs.
    - intros f s Hs Hf. rewrite (proj2 H2 f s Hs Hf).
      apply (proj2 H1); [apply (proj1 H2); exact Hs|].
      apply (oiso_sub C s); [|exact Hf]. intros v Hv. exact (oimap_closed g2 H2 s v Hs Hv).
  Qed.

  Theorem oimap_itr : forall g, OIMap g -> forall j, OIMap (itr j g).
  Proof.
    intros g Hg j. induction j as [|j IH]; [exact oimap_id|].
    exact (oimap_comp (itr j g) g IH Hg).
  Qed.

  Theorem oimap_rp : Shaped n m nk ap rp vd -> OrdInv C n ap rp vd -> OIMap rp.
  Proof.
    intros HS HO. split; [exact (rp_len_n n m nk ap rp vd HS)|].
    intros f s Hs Hf. exact (oi_rp C n ap rp vd HO f s Hs Hf).
  Qed.

  (* An event applied after an order-invariant map is order invariant. *)
  Theorem oi_ap_after : OrdInv C n ap rp vd -> forall g, OIMap g ->
    forall f k p s, length s = n -> OIso C (s ++ p) f ->
      ap (k, map f p) (g (map f s)) = map f (ap (k, p) (g s)).
  Proof.
    intros HO g Hg f k p s Hs Hf.
    rewrite (proj2 Hg f s Hs (oiso_sub C (s ++ p) s f (fun v Hv => in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl Hv)))) Hf)).
    apply (oi_ap C n ap rp vd HO); [apply (proj1 Hg); exact Hs|].
    apply (oiso_sub C (s ++ p)); [|exact Hf]. intros v Hv. apply in_app_or in Hv.
    destruct Hv as [Hv | Hv].
    - pose proof (oimap_closed g Hg s v Hs Hv) as H. apply in_app_or in H.
      destruct H as [H | H]; [apply in_or_app; left; apply in_or_app; left; exact H
                             | apply in_or_app; right; exact H].
    - apply in_or_app. left. apply in_or_app. right. exact Hv.
  Qed.

  (* The repair-first registry (gsm's runtime Apply): repair to validity, then apply the event. *)
  Definition sigb (e : nat * list Z) : bool := Nat.ltb (fst e) nk && Nat.eqb (length (snd e)) m.

  Lemma sigb_spec : forall e, sigb e = true <-> InSig e.
  Proof.
    intros [k p]. unfold sigb, InSig; simpl. rewrite andb_true_iff, Nat.ltb_lt, Nat.eqb_eq. split; intros H; exact H.
  Qed.

  Definition apR (K : nat) (e : nat * list Z) (s : list Z) : list Z :=
    if sigb e then ap e (itr K rp s) else s.

  Theorem derived_shaped : forall K, Shaped n m nk ap rp vd -> Shaped n m nk (apR K) rp vd.
  Proof.
    intros K HS. constructor.
    - intros k p s Hn. unfold apR. destruct (sigb (k, p)) eqn:E; [|reflexivity].
      exfalso. apply Hn. apply sigb_spec in E. exact E.
    - intros e s Hs. unfold apR. destruct (sigb e); [|exact Hs].
      apply (sh_len_ap n m nk ap rp vd HS).
      exact (itr_len rp vd n (sh_len_rp n m nk ap rp vd HS) (sh_rp_fix n m nk ap rp vd HS) K s Hs).
    - exact (sh_len_rp n m nk ap rp vd HS).
    - exact (sh_rp_fix n m nk ap rp vd HS).
  Qed.

  (* Repair-then-event stays in the fragment. *)
  Theorem derived_ordinv : forall K, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    OrdInv C n (apR K) rp vd.
  Proof.
    intros K HS HO. constructor.
    - intros f k p s Hs Hf. unfold apR.
      replace (sigb (k, map f p)) with (sigb (k, p)) by (unfold sigb; simpl; rewrite lenM; reflexivity).
      destruct (sigb (k, p)); [|reflexivity].
      exact (oi_ap_after HO (itr K rp) (oimap_itr rp (oimap_rp HS HO) K) f k p s Hs Hf).
    - exact (oi_rp C n ap rp vd HO).
    - exact (oi_vd C n ap rp vd HO).
  Qed.

  (* ============================================================================================ *)
  (* The derived-registry route, and gsm's runtime.                                               *)
  (* ============================================================================================ *)

  Local Notation GR K := (govK (apR K) rp K).

  Section Runtime.
    Hypothesis HS : Shaped n m nk ap rp vd.
    Variable K : nat.
    Hypothesis HT : TermK rp vd n K.

    Lemma nf_fix : forall j t, vd t = true -> itr j rp t = t.
    Proof. intros j t H. apply itr_fix. exact (sh_rp_fix n m nk ap rp vd HS t H). Qed.

    Lemma nf_len : forall s, length s = n -> length (itr K rp s) = n.
    Proof. exact (itr_len rp vd n (sh_len_rp n m nk ap rp vd HS) (sh_rp_fix n m nk ap rp vd HS) K). Qed.

    Lemma G_valid : forall e s, length s = n -> vd (G K e s) = true.
    Proof. intros e s Hs. apply HT. apply (sh_len_ap n m nk ap rp vd HS). exact Hs. Qed.

    (* The runtime step, from any state: normalize, then (for an event of the registry) the
       governed step. *)
    Definition runH (e : nat * list Z) (t : list Z) : list Z := if sigb e then G K e t else t.

    Lemma GR_eq : forall e s, length s = n -> GR K e s = runH e (itr K rp s).
    Proof.
      intros e s _. unfold govK at 1, apR, runH. destruct (sigb e); reflexivity.
    Qed.

    Lemma runH_len : forall e t, length t = n -> length (runH e t) = n.
    Proof.
      intros e t Ht. unfold runH. destruct (sigb e); [|exact Ht].
      exact (G_len n m nk ap rp vd HS K e t Ht).
    Qed.

    Lemma runH_valid : forall e t, length t = n -> vd t = true -> vd (runH e t) = true.
    Proof. intros e t Ht Hv. unfold runH. destruct (sigb e); [apply G_valid; exact Ht | exact Hv]. Qed.

    Lemma GR_len : forall e s, length s = n -> length (GR K e s) = n.
    Proof. intros e s Hs. rewrite (GR_eq e s Hs). apply runH_len, nf_len, Hs. Qed.

    Lemma GR_valid : forall e s, length s = n -> vd (GR K e s) = true.
    Proof. intros e s Hs. rewrite (GR_eq e s Hs). apply runH_valid; [apply nf_len, Hs | apply HT, Hs]. Qed.

    (* Commutation of the runtime step at every state, from CC1 at the valid states. *)
    Lemma GR_comm : forall I, CC1VZ K I -> forall s e1 e2, length s = n ->
      (InSig e1 -> InSig e2 -> I (fst e1) (fst e2)) ->
      GR K e2 (GR K e1 s) = GR K e1 (GR K e2 s).
    Proof.
      intros I H s e1 e2 Hs HI. set (t := itr K rp s).
      assert (Ht : length t = n) by (apply nf_len, Hs).
      assert (Hv : vd t = true) by (apply HT, Hs).
      rewrite (GR_eq e1 s Hs), (GR_eq e2 s Hs). fold t.
      rewrite (GR_eq e2 _ (runH_len e1 t Ht)), (GR_eq e1 _ (runH_len e2 t Ht)).
      rewrite (nf_fix K _ (runH_valid e1 t Ht Hv)), (nf_fix K _ (runH_valid e2 t Ht Hv)).
      unfold runH. destruct (sigb e1) eqn:E1, (sigb e2) eqn:E2; try reflexivity.
      apply sigb_spec in E1. apply sigb_spec in E2. destruct e1 as [k1 p1], e2 as [k2 p2].
      destruct E1 as [K1 L1], E2 as [K2 L2]. simpl in *.
      exact (H t k1 p1 k2 p2 Ht Hv K1 K2 L1 L2 (HI (conj K1 L1) (conj K2 L2))).
    Qed.

    (* CC1 at every state of the repair-first registry is exactly CC1 at every valid state. *)
    Theorem cc1_derived_valid : CC1Z (apR K) rp n K <-> CC1VZ K (fun _ _ => True).
    Proof.
      split.
      - intros H s k1 p1 k2 p2 Hs Hv K1 K2 L1 L2 _.
        assert (S1 : sigb (k1, p1) = true) by (apply sigb_spec; split; assumption).
        assert (S2 : sigb (k2, p2) = true) by (apply sigb_spec; split; assumption).
        pose proof (H s (k1, p1) (k2, p2) Hs) as E.
        rewrite (GR_eq (k1, p1) s Hs), (GR_eq (k2, p2) s Hs) in E.
        rewrite (nf_fix K s Hv) in E. unfold runH in E. rewrite S1, S2 in E.
        pose proof (G_len n m nk ap rp vd HS K (k1, p1) s Hs) as La.
        pose proof (G_len n m nk ap rp vd HS K (k2, p2) s Hs) as Lb.
        rewrite (GR_eq _ _ La), (GR_eq _ _ Lb) in E.
        rewrite (nf_fix K _ (G_valid _ s Hs)), (nf_fix K _ (G_valid _ s Hs)) in E.
        unfold runH in E. rewrite S1, S2 in E. exact E.
      - intros H s e1 e2 Hs. apply (GR_comm (fun _ _ => True) H s e1 e2 Hs). auto.
    Qed.
  End Runtime.

  (* The prose route, mechanized: the repair-first registry is in the fragment, so cc1_abs decides
     its CC1, which is CC1 at the valid states of the original. *)
  Theorem cc1_valid_derived_abs : forall K N, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    (n + 2 * m <= N)%nat -> TermK rp vd n K ->
    (CC1VZ K (fun _ _ => True) <-> CC1D C n m nk (apR K) rp K N).
  Proof.
    intros K N HS HO HN HT. rewrite <- (cc1_derived_valid HS K HT).
    exact (cc1_abs C n m nk (apR K) rp vd (derived_shaped K HS) (derived_ordinv K HS HO) K N HN).
  Qed.

  (* ============================================================================================ *)
  (* gsm's guarantee.                                                                             *)
  (* ============================================================================================ *)

  (* The independence relation on events: their kinds are related by I. *)
  Definition evI (I : nat -> nat -> Prop) (a b : nat * list Z) : Prop := I (fst a) (fst b).

  (* From every valid integer state, trace-equivalent sequences of events reach the same state. *)
  Definition RunConvZ (K : nat) (I : nat -> nat -> Prop) : Prop :=
    forall s, length s = n -> vd s = true -> forall es1 es2, tequiv (evI I) es1 es2 ->
      Forall InSig es1 -> runT (G K) es1 s = runT (G K) es2 s.

  (* Given repair within K steps over the representatives, CC1 for I at the valid representative
     states holds iff runs from every valid integer state converge up to I-reordering. *)
  Theorem gsm_abs_exact : forall K N I, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    (n + 2 * m <= N)%nat -> TermD C n rp vd K N ->
    (CC1VD K N I <-> RunConvZ K I).
  Proof.
    intros K N I HS HO HN HD.
    pose proof (proj2 (term_abs C n m nk ap rp vd HS HO K N ltac:(lia)) HD) as HT.
    rewrite <- (cc1_valid_abs HS HO K N I HN). split.
    - intros H s Hs Hv es1 es2 Hte Hev.
      apply (run_tequiv (G K) (evI I) InSig (fun t => length t = n /\ vd t = true)
                        (fun t => length t = n /\ vd t = true)); try assumption.
      + intros t Ht. exact Ht.
      + intros e t _ [Ht _]. split; [exact (G_len n m nk ap rp vd HS K e t Ht) | exact (G_valid HS K HT e t Ht)].
      + intros [k1 p1] [k2 p2] t [K1 L1] [K2 L2] HI [Ht Hv']. simpl in *. symmetry.
        exact (H t k1 p1 k2 p2 Ht Hv' K1 K2 L1 L2 HI).
      + split; assumption.
    - intros H s k1 p1 k2 p2 Hs Hv K1 K2 L1 L2 HI.
      pose proof (H s Hs Hv [(k1, p1); (k2, p2)] [(k2, p2); (k1, p1)]
                    (teq_swap (evI I) [] (k1, p1) (k2, p2) [] HI)) as E.
      apply E. constructor; [split; assumption|]. constructor; [split; assumption|]. constructor.
  Qed.

  (* gsm's runtime: Apply normalizes its input, applies the event, normalizes. From EVERY integer
     state (the zero state included), trace-equivalent sequences reach the same state, given the
     two checks gsm runs over the representatives. *)
  Theorem gsm_abs_sound : forall K N I, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    (n + 2 * m <= N)%nat -> TermD C n rp vd K N -> CC1VD K N I ->
    forall s0, length s0 = n -> forall es1 es2, tequiv (evI I) es1 es2 -> Forall InSig es1 ->
      runT (GR K) es1 s0 = runT (GR K) es2 s0.
  Proof.
    intros K N I HS HO HN HD HC s0 Hs0 es1 es2 Hte Hev.
    pose proof (proj2 (term_abs C n m nk ap rp vd HS HO K N ltac:(lia)) HD) as HT.
    pose proof (proj2 (cc1_valid_abs HS HO K N I HN) HC) as HZ.
    apply (run_tequiv (GR K) (evI I) InSig (fun t => length t = n) (fun t => length t = n));
      try assumption.
    - intros t Ht. exact Ht.
    - intros e t _ Ht. exact (GR_len HS K e t Ht).
    - intros a b t Ha Hb HI Ht. symmetry. apply (GR_comm HS K HT I HZ t a b Ht). intros _ _. exact HI.
  Qed.

  (* Every pair checked (gsm's default): any permutation. *)
  Theorem gsm_abs_sound_all : forall K N, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    (n + 2 * m <= N)%nat -> TermD C n rp vd K N -> CC1VD K N (fun _ _ => True) ->
    forall s0, length s0 = n -> forall es1 es2, Permutation es1 es2 -> Forall InSig es1 ->
      runT (GR K) es1 s0 = runT (GR K) es2 s0.
  Proof.
    intros K N HS HO HN HD HC s0 Hs0 es1 es2 Hp Hev.
    apply (gsm_abs_sound K N (fun _ _ => True) HS HO HN HD HC s0 Hs0); [|exact Hev].
    apply (perm_tequiv_total (evI (fun _ _ => True)) InSig); [| exact Hp | exact Hev].
    intros a b _ _. exact I.
  Qed.

  (* Idempotence of gsm's runtime step from every integer state iff at every valid
     representative state. *)
  Theorem idem_runtime_abs : forall K N k, Shaped n m nk ap rp vd -> OrdInv C n ap rp vd ->
    (n + m <= N)%nat -> TermD C n rp vd K N -> (k < nk)%nat ->
    ((forall s p, length s = n -> length p = m -> GR K (k, p) (GR K (k, p) s) = GR K (k, p) s) <->
     IdemVD K N k).
  Proof.
    intros K N k HS HO HN HD Hk.
    pose proof (proj2 (term_abs C n m nk ap rp vd HS HO K N ltac:(lia)) HD) as HT.
    rewrite <- (idem_valid_abs HS HO K N k HN).
    assert (R : forall s p, length s = n -> length p = m ->
              GR K (k, p) (GR K (k, p) s) = GR K (k, p) s <->
              G K (k, p) (G K (k, p) (itr K rp s)) = G K (k, p) (itr K rp s)).
    { intros s p Hs Hp.
      assert (Sg : sigb (k, p) = true) by (apply sigb_spec; split; assumption).
      pose proof (nf_len HS K s Hs) as Lt.
      pose proof (G_len n m nk ap rp vd HS K (k, p) _ Lt) as Lg.
      rewrite (GR_eq K _ _ (GR_len HS K (k, p) s Hs)), (GR_eq K (k, p) s Hs).
      unfold runH. rewrite Sg.
      rewrite (nf_fix HS K _ (G_valid HS K HT (k, p) _ Lt)). reflexivity. }
    split.
    - intros H s p Hs Hv Hp. pose proof (proj1 (R s p Hs Hp) (H s p Hs Hp)) as E.
      rewrite (nf_fix HS K s Hv) in E. exact E.
    - intros H s p Hs Hp. apply (R s p Hs Hp). apply H; [apply (nf_len HS K s Hs) | apply HT, Hs | exact Hp].
  Qed.
End Gsm.

(* ============================================================================================ *)
(* Non-vacuity: the capped inventory of AbstractionCutoff.v (m = 1).                            *)
(* ============================================================================================ *)

Definition capped_sh := prog_shaped capped 1 1 eq_refl.
Definition capped_oi := ord_frag_sound [5%Z] capped 1 1 eq_refl eq_refl.

Theorem capped_term : TermD [5%Z] 1 (srp capped) (svd capped) 1 3.
Proof.
  intros s Hs. revert s Hs. apply forallb_forall. vm_compute. reflexivity.
Qed.

Theorem capped_cc1v_check :
  cc1v_check [5%Z] 1 1 1 (sap capped 1) (srp capped) (svd capped) 1 3 (fun _ _ => true) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem capped_idemv_check : idemv_check [5%Z] 1 1 (sap capped 1) (srp capped) (svd capped) 1 3 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* CC1 at every valid integer stock, for every two restock levels. *)
Theorem capped_cc1_valid : CC1VZ 1 1 1 (sap capped 1) (srp capped) (svd capped) 1 (fun _ _ => True).
Proof.
  apply (proj2 (cc1_valid_abs [5%Z] 1 1 1 _ _ _ capped_sh capped_oi 1 3 _ ltac:(lia))).
  pose proof (proj1 (cc1v_check_spec [5%Z] 1 1 1 _ _ _ 1 3 (fun _ _ => true)) capped_cc1v_check) as H.
  intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 eq_refl).
Qed.

(* Restock is idempotent at every valid integer stock, for every level. *)
Theorem capped_idem : IdemVZ 1 1 (sap capped 1) (srp capped) (svd capped) 1 0.
Proof.
  apply (proj2 (idem_valid_abs [5%Z] 1 1 1 _ _ _ capped_sh capped_oi 1 3 0 ltac:(lia))).
  exact (proj1 (idemv_check_spec [5%Z] 1 1 _ _ _ 1 3 0) capped_idemv_check).
Qed.

(* The repair-first registry of the capped inventory is in the fragment. *)
Theorem capped_derived : Shaped 1 1 1 (apR 1 1 (sap capped 1) (srp capped) 1) (srp capped) (svd capped) /\
  OrdInv [5%Z] 1 (apR 1 1 (sap capped 1) (srp capped) 1) (srp capped) (svd capped).
Proof.
  split; [exact (derived_shaped 1 1 1 _ _ _ 1 capped_sh)
         | exact (derived_ordinv [5%Z] 1 1 1 _ _ _ 1 capped_sh capped_oi)].
Qed.

(* Every permutation of restock events converges from every integer stock, at run time. *)
Theorem capped_runtime : forall s0, length s0 = 1%nat -> forall es1 es2, Permutation es1 es2 ->
  Forall (InSig 1 1) es1 ->
  runT (govK (apR 1 1 (sap capped 1) (srp capped) 1) (srp capped) 1) es1 s0 =
  runT (govK (apR 1 1 (sap capped 1) (srp capped) 1) (srp capped) 1) es2 s0.
Proof.
  apply (gsm_abs_sound_all [5%Z] 1 1 1 _ _ _ 1 3 capped_sh capped_oi ltac:(lia) capped_term).
  pose proof (proj1 (cc1v_check_spec [5%Z] 1 1 1 _ _ _ 1 3 (fun _ _ => true)) capped_cc1v_check) as H.
  intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 eq_refl).
Qed.

(* ============================================================================================ *)
(* Non-vacuity: gsm's documented example (m = 0, cutoff N = n = 3).                             *)
(* ============================================================================================ *)

(* Variables (stock, ship_a, ship_b); receive_a: if stock < ship_a then stock := ship_a;
   receive_b likewise; invariant stock <= 5; repair stock := 5. *)
Definition inventory : prog :=
  mkProg [[If (FLt (Vr 0) (Vr 1)) (Vr 1) (Vr 0); Vr 1; Vr 2];
          [If (FLt (Vr 0) (Vr 2)) (Vr 2) (Vr 0); Vr 1; Vr 2]]
         [Cst 5%Z; Vr 1; Vr 2] (FLe (Vr 0) (Cst 5%Z)).

Theorem inventory_frag : wf inventory 3 0 = true /\ ord_frag [5%Z] inventory = true.
Proof. split; reflexivity. Qed.

Definition inventory_sh := prog_shaped inventory 3 0 eq_refl.
Definition inventory_oi := ord_frag_sound [5%Z] inventory 3 0 eq_refl eq_refl.

(* 7 representatives, 343 representative states. *)
Theorem inventory_reps : length (tup (reps 3 [5%Z]) 3) = 343%nat.
Proof. reflexivity. Qed.

Theorem inventory_term : TermD [5%Z] 3 (srp inventory) (svd inventory) 1 3.
Proof.
  intros s Hs. revert s Hs. apply forallb_forall. vm_compute. reflexivity.
Qed.

Theorem inventory_cc1v_check :
  cc1v_check [5%Z] 3 0 2 (sap inventory 0) (srp inventory) (svd inventory) 1 3 (fun _ _ => true) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem inventory_idemv_check :
  idemv_check [5%Z] 3 0 (sap inventory 0) (srp inventory) (svd inventory) 1 3 0 = true /\
  idemv_check [5%Z] 3 0 (sap inventory 0) (srp inventory) (svd inventory) 1 3 1 = true.
Proof. split; vm_compute; reflexivity. Qed.

(* Every permutation of receive events converges from every integer state, at run time. *)
Theorem inventory_runtime : forall s0, length s0 = 3%nat -> forall es1 es2, Permutation es1 es2 ->
  Forall (InSig 0 2) es1 ->
  runT (govK (apR 0 2 (sap inventory 0) (srp inventory) 1) (srp inventory) 1) es1 s0 =
  runT (govK (apR 0 2 (sap inventory 0) (srp inventory) 1) (srp inventory) 1) es2 s0.
Proof.
  apply (gsm_abs_sound_all [5%Z] 3 0 2 _ _ _ 1 3 inventory_sh inventory_oi ltac:(lia) inventory_term).
  pose proof (proj1 (cc1v_check_spec [5%Z] 3 0 2 _ _ _ 1 3 (fun _ _ => true)) inventory_cc1v_check) as H.
  intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 eq_refl).
Qed.

(* Both receive events are idempotent at every valid integer state (no deduplication needed). *)
Theorem inventory_idem : forall k, (k < 2)%nat ->
  IdemVZ 3 0 (sap inventory 0) (srp inventory) (svd inventory) 1 k.
Proof.
  intros k Hk. apply (proj2 (idem_valid_abs [5%Z] 3 0 2 _ _ _ inventory_sh inventory_oi 1 3 k ltac:(lia))).
  apply idemv_check_spec. destruct inventory_idemv_check as [H0 H1].
  destruct k as [|[|k]]; [exact H0 | exact H1 | lia].
Qed.

(* ============================================================================================ *)
(* Non-vacuity of a failure: an order-invariant event that is not idempotent.                   *)
(* ============================================================================================ *)

(* Two variables; swapxy: (x, y) := (y, x); every state valid. *)
Definition swapxy : prog := mkProg [[Vr 1; Vr 0]] [Vr 0; Vr 1] FT.

Theorem swapxy_frag : wf swapxy 2 0 = true /\ ord_frag [] swapxy = true.
Proof. split; reflexivity. Qed.

(* The representative check reports swapxy as not idempotent. *)
Theorem swapxy_check_fails : idemv_check [] 2 0 (sap swapxy 0) (srp swapxy) (svd swapxy) 0 2 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* And, by idem_valid_abs, it is not idempotent over Z; a witness at (0, 1). *)
Theorem swapxy_not_idem : ~ IdemVZ 2 0 (sap swapxy 0) (srp swapxy) (svd swapxy) 0 0 /\
  govK (sap swapxy 0) (srp swapxy) 0 (0%nat, []) (govK (sap swapxy 0) (srp swapxy) 0 (0%nat, []) [0%Z; 1%Z]) = [0%Z; 1%Z] /\
  govK (sap swapxy 0) (srp swapxy) 0 (0%nat, []) [0%Z; 1%Z] = [1%Z; 0%Z].
Proof.
  split; [|split; reflexivity].
  intros H. apply (proj1 (idem_valid_abs [] 2 0 1 _ _ _ (prog_shaped swapxy 2 0 eq_refl)
                            (ord_frag_sound [] swapxy 2 0 eq_refl eq_refl) 0 2 0 ltac:(lia))) in H.
  apply idemv_check_spec in H. rewrite swapxy_check_fails in H. discriminate.
Qed.

(* ============================================================================================ *)
(* Boundary: an undeclared exact test breaks the idempotence transfer.                          *)
(* ============================================================================================ *)

(* Three variables; event: if z = 13 then swap x and y. *)
Definition idem13 : prog :=
  mkProg [[If (FEq (Vr 2) (Cst 13%Z)) (Vr 1) (Vr 0); If (FEq (Vr 2) (Cst 13%Z)) (Vr 0) (Vr 1); Vr 2]]
         [Vr 0; Vr 1; Vr 2] FT.

(* Idempotent at every valid representative state of reps 3 []. *)
Theorem idem13_passes : idemv_check [] 3 0 (sap idem13 0) (srp idem13) (svd idem13) 0 3 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* Not idempotent at the integer state (0, 1, 13). *)
Theorem idem13_diverges :
  ~ IdemVZ 3 0 (sap idem13 0) (srp idem13) (svd idem13) 0 0 /\
  govK (sap idem13 0) (srp idem13) 0 (0%nat, []) [0%Z; 1%Z; 13%Z] = [1%Z; 0%Z; 13%Z] /\
  govK (sap idem13 0) (srp idem13) 0 (0%nat, [])
    (govK (sap idem13 0) (srp idem13) 0 (0%nat, []) [0%Z; 1%Z; 13%Z]) = [0%Z; 1%Z; 13%Z].
Proof.
  split; [|split; reflexivity].
  intros H. specialize (H [0%Z; 1%Z; 13%Z] [] eq_refl eq_refl eq_refl). vm_compute in H. discriminate.
Qed.

(* ord_frag refuses it; with 13 declared it is in the fragment and the check fails, as it should. *)
Theorem idem13_refused : wf idem13 3 0 = true /\ ord_frag [] idem13 = false /\
  ord_frag [13%Z] idem13 = true /\
  idemv_check [13%Z] 3 0 (sap idem13 0) (srp idem13) (svd idem13) 0 3 0 = false.
Proof. split; [reflexivity | split; [reflexivity | split; [reflexivity | vm_compute; reflexivity]]]. Qed.
