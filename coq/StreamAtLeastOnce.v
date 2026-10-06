(* StreamAtLeastOnce.v: at-least-once delivery for stream processors, exactly (gap 15 (b) of
   REGIME-AUDIT.md). Axiom-free.

   StreamExact.v characterizes stream agreement (settled processors with the same received set
   agree) for processors whose received lists are duplicate-free (is_processor requires
   NoDup (recv p t)). Under at-least-once delivery a processor may receive an event more than once:
   every copy enters the buffer and is applied. This file drops the NoDup requirement.

   Setting. As in Stream.v and StreamExact.v: the processor discipline prstep (compensate while
   invalid, apply an enabled buffered event only from a valid state), any well-founded potential,
   decidable validity and enabledness, enabledness invariant under permutation of the buffer.

   - is_processor_d D: is_processor with NoDup (recv p t) replaced by D (recv p t), for a delivery
     class D of received lists. is_processor_d NoDup is is_processor (procd_nodup_iff).
   - StreamAgreeD D s0: settled D-processors with the same received SET agree.
     StreamAgreeA s0 := StreamAgreeD (fun _ => True) s0, at-least-once agreement: the received
     lists may repeat events, and two processors are compared whenever their lists have the same
     events, whatever the multiplicities.
   - stream_agree_d_set_function: StreamAgreeD D s0 <-> for every two D-lists with the same events,
     the finished reductions from s0 end in the same state (FinEq).

   Any enabledness (Progress, as in stream_exact).
   - stream_alo_exact: Progress ->
       StreamAgreeA s0 <-> (forall E, PJC (s0, E)) /\ DupAbsorb s0,
     PJC at EVERY received list (duplicates allowed), and DupAbsorb s0: for every list E and
     every a in E, some finished reduction from (s0, a :: E) ends where some finished reduction
     from (s0, E) ends (one redelivered copy is absorbed). The two conjuncts are independent
     (ct_general, ow_general).
   - stream_exact_recovered: Progress -> StreamAgreeD NoDup s0 <-> forall E, NoDup E -> PJC (s0, E),
     derived through the set-function form (duplicate-free lists with the same events are
     permutations), and StreamAgreeD NoDup is StreamExact.StreamAgree (stream_agree_nodup_iff).

   Free delivery (every buffered event enabled; canonical repair rho_star, reached by compensation
   and valid), the C8 cell of docs/COVERAGE.md. gov e s = rho_star (apply e s), grun s w its run.
   - stream_alo_aloconv: StreamAgreeA s0 <-> ALOConv gov (fun _ => True) (rho_star s0): the stream
     property is the governed-replay at-least-once property from rho_star s0.
   - stream_alo_exact_free: StreamAgreeA s0 <-> PCC s0 /\ forall a, PIdem s0 a,
     PCC s0 (StreamExact: governed steps of fresh distinct events commute at every state a processor
     reaches) and PIdem s0 a: a is idempotent at every state grun (rho_star s0) u with u ++ [a]
     duplicate-free (where a is first delivered). Through AtLeastOnceExact.alo_exact.
   - stream_alo_free_split: StreamAgreeA s0 <-> StreamAgree s0 /\ forall a, PIdem s0 a; the first
     conjunct is StreamExact.stream_exact_free's property (duplicate-free received sets), so the
     at-least-once condition is the exactly-once one plus reachable idempotence.

   Counterexamples and non-vacuity (free delivery, every state valid).
   - ct_alo_fails: the counter (every event adds 1). PCC, StreamAgree and PJC at every list hold;
     PIdem fails, DupAbsorb fails, StreamAgreeA fails, and two processors receiving [0] and
     [0; 0] settle at 1 and 2. The naive claim "stream_exact's condition, PJC at duplicate-free
     sets, gives at-least-once agreement" is false, and the idempotence clause is needed.
   - ow_alo_fails: the overwrite register (event e sets the state to e). Every event is idempotent
     at every state (gsm's NotIdempotent would list nothing; PIdem holds), DupAbsorb holds, yet
     PCC, PJC and StreamAgreeA fail: idempotence alone is not enough, the commutation clause is
     needed.
   - ct_general, ow_general: the two conjuncts of stream_alo_exact are independent.
   - mx_alo_holds: the max-register satisfies PCC and PIdem from every start, so StreamAgreeA
     holds; two processors receiving [1; 2; 1] and [2; 1] settle at the same state. *)

Require Import NC.Newman NC.GovernanceCausal NC.GovernanceWF NC.Stream NC.StreamExact.
Require Import NC.Trace NC.AtLeastOnce NC.AtLeastOnceExact.
Require NC.GovernanceConverse.
From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* A list with a repeated event splits around one repeated copy. *)
Lemma sa_nodup_or_dup : forall {E : Type} (dec : forall a b : E, {a = b} + {a <> b}) (l : list E),
  NoDup l \/ exists x a r, l = x ++ a :: r /\ In a (x ++ r).
Proof.
  intros E dec l. induction l as [| y l IH]; [left; constructor |].
  destruct (in_dec dec y l) as [Hin | Hn].
  - right. exists [], y, l. split; [reflexivity | exact Hin].
  - destruct IH as [Hnd | [x [a [r [-> Ha]]]]].
    + left. constructor; assumption.
    + right. exists (y :: x), a, r. split; [reflexivity |]. right. exact Ha.
Qed.

(* ============================================================================================ *)
(* Delivery classes for stream processors.                                                      *)
(* ============================================================================================ *)

Section StreamDelivery.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply   : Event -> State -> State.
  Variable rho     : State -> State.
  Variable valid   : State -> Prop.
  Variable enabled : Event -> State -> list Event -> Prop.

  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).

  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.
  Hypothesis enabled_dec : forall e s B, {enabled e s B} + {~ enabled e s B}.
  Hypothesis enabled_perm : forall e s B C, Permutation B C -> enabled e s B -> enabled e s C.

  Local Notation pstep := (prstep event_eq_dec apply rho valid enabled).
  Local Notation done := (settled event_eq_dec apply rho valid enabled).

  (* A processor whose received lists lie in the delivery class D. *)
  Definition is_processor_d (D : list Event -> Prop) (Str : Event -> Prop) (s0 : State)
      (p : @processor State Event) : Prop :=
    (forall t, D (recv p t)) /\
    (forall t e, In e (recv p t) -> Str e) /\
    (forall t, exists N, recv p (S t) = recv p t ++ N) /\
    (forall e, Str e -> exists ti, forall t, ti <= t -> In e (recv p t)) /\
    (forall t, star pstep (s0, recv p t) (conf p t)).

  Definition StreamAgreeD (D : list Event -> Prop) (s0 : State) : Prop :=
    forall (Str : Event -> Prop) p1 p2 t1 t2,
      is_processor_d D Str s0 p1 -> is_processor_d D Str s0 p2 -> done p1 t1 -> done p2 t2 ->
      (forall e, In e (recv p1 t1) <-> In e (recv p2 t2)) ->
      psi p1 t1 = psi p2 t2.

  (* At-least-once agreement: received lists may repeat events. *)
  Definition StreamAgreeA (s0 : State) : Prop := StreamAgreeD (fun _ => True) s0.

  Definition SameSet (l1 l2 : list Event) : Prop := forall e, In e l1 <-> In e l2.

  (* Every finished reduction from c1 ends where every finished reduction from c2 ends. *)
  Definition FinEq (c1 c2 : State * list Event) : Prop :=
    forall n1 n2, star pstep c1 n1 -> normal_form pstep n1 ->
                  star pstep c2 n2 -> normal_form pstep n2 -> fst n1 = fst n2.

  (* One redelivered copy is absorbed: some finished reduction from (s0, a :: E) ends where some
     finished reduction from (s0, E) ends. *)
  Definition DupAbsorb (s0 : State) : Prop :=
    forall E a, In a E -> exists n1 n2,
      star pstep (s0, a :: E) n1 /\ normal_form pstep n1 /\
      star pstep (s0, E) n2 /\ normal_form pstep n2 /\ fst n1 = fst n2.

  (* ---------- the duplicate-free class is StreamExact's ---------- *)

  Lemma procd_nodup_iff : forall Str s0 p,
    is_processor_d (@NoDup Event) Str s0 p <-> is_processor event_eq_dec apply rho valid enabled Str s0 p.
  Proof. intros Str s0 p. unfold is_processor_d, is_processor. tauto. Qed.

  Theorem stream_agree_nodup_iff : forall s0,
    StreamAgreeD (@NoDup Event) s0 <-> StreamAgree event_eq_dec apply rho valid enabled s0.
  Proof.
    intros s0. split.
    - intros H Str p1 p2 t1 t2 H1 H2 N1 N2 HS.
      exact (H Str p1 p2 t1 t2 (proj2 (procd_nodup_iff Str s0 p1) H1) (proj2 (procd_nodup_iff Str s0 p2) H2)
               N1 N2 HS).
    - intros H Str p1 p2 t1 t2 H1 H2 N1 N2 HS.
      exact (H Str p1 p2 t1 t2 (proj1 (procd_nodup_iff Str s0 p1) H1) (proj1 (procd_nodup_iff Str s0 p2) H2)
               N1 N2 HS).
  Qed.

  (* At-least-once agreement contains exactly-once agreement. *)
  Theorem stream_alo_nodup : forall s0, StreamAgreeA s0 -> StreamAgree event_eq_dec apply rho valid enabled s0.
  Proof.
    intros s0 H. apply stream_agree_nodup_iff.
    intros Str p1 p2 t1 t2 [_ H1] [_ H2] N1 N2 HS.
    exact (H Str p1 p2 t1 t2 (conj (fun _ => Logic.I) H1) (conj (fun _ => Logic.I) H2) N1 N2 HS).
  Qed.

  (* ---------- the set-function form ---------- *)

  Lemma sa_const_procd : forall (D : list Event -> Prop) (Str : Event -> Prop) s0 E n,
    D E -> (forall e, In e E <-> Str e) -> star pstep (s0, E) n ->
    is_processor_d D Str s0 (const_proc E n).
  Proof.
    intros D Str s0 E n HD HS Hs. split; [intros t; exact HD |].
    split; [intros t e H; apply HS; exact H |].
    split; [intros t; exists []; simpl; rewrite app_nil_r; reflexivity |].
    split; [intros e He; exists 0; intros t _; apply HS; exact He |].
    intros t. exact Hs.
  Qed.

  Theorem stream_agree_d_set_function : forall (D : list Event -> Prop) s0,
    StreamAgreeD D s0 <-> forall E1 E2, D E1 -> D E2 -> SameSet E1 E2 -> FinEq (s0, E1) (s0, E2).
  Proof.
    intros D s0. split.
    - intros H E1 E2 D1 D2 HS n1 n2 S1 N1 S2 N2.
      exact (H (fun e => In e E1) (const_proc E1 n1) (const_proc E2 n2) 0 0
               (sa_const_procd D _ s0 E1 n1 D1 (fun e => iff_refl _) S1)
               (sa_const_procd D _ s0 E2 n2 D2 (fun e => iff_sym (HS e)) S2) N1 N2 HS).
    - intros H Str p1 p2 t1 t2 [D1 [_ [_ [_ C1]]]] [D2 [_ [_ [_ C2]]]] N1 N2 HS.
      exact (H _ _ (D1 t1) (D2 t2) HS _ _ (C1 t1) N1 (C2 t2) N2).
  Qed.

  (* ---------- finished states under PJC ---------- *)

  Lemma sa_fin_exists : forall c, exists n, star pstep c n /\ normal_form pstep n.
  Proof. exact (st_pnf_exists event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec enabled_dec). Qed.

  Lemma sa_pjc_un : forall c, PJC event_eq_dec apply rho valid enabled c -> GovernanceConverse.UN pstep c.
  Proof.
    intros c H. apply GovernanceConverse.CR_UN.
    exact (proj2 (pjc_exact event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf c) H).
  Qed.

  Lemma sa_fin_self : forall c, PJC event_eq_dec apply rho valid enabled c -> FinEq c c.
  Proof. intros c H n1 n2 S1 N1 S2 N2. rewrite (sa_pjc_un c H n1 n2 S1 N1 S2 N2). reflexivity. Qed.

  Lemma sa_fin_perm : forall s0 E1 E2, PJC event_eq_dec apply rho valid enabled (s0, E1) ->
    Permutation E1 E2 -> FinEq (s0, E1) (s0, E2).
  Proof.
    intros s0 E1 E2 H HP n1 [s2 B2] S1 N1 S2 N2.
    destruct (sx_star_pstep_perm event_eq_dec apply rho valid enabled enabled_perm _ _ S2 E1
                (Permutation_sym HP)) as [C [S2' HC]]. simpl in S2', HC.
    assert (N2' : normal_form pstep (s2, C))
      by exact (sx_nf_pstep_perm event_eq_dec apply rho valid enabled enabled_perm s2 B2 C N2 HC).
    rewrite (sa_pjc_un _ H n1 (s2, C) S1 N1 S2' N2'). reflexivity.
  Qed.

  Lemma sa_fin_sym : forall c1 c2, FinEq c1 c2 -> FinEq c2 c1.
  Proof. intros c1 c2 H n1 n2 S1 N1 S2 N2. symmetry. exact (H n2 n1 S2 N2 S1 N1). Qed.

  Lemma sa_fin_trans : forall c1 c2 c3, FinEq c1 c2 -> FinEq c2 c3 -> FinEq c1 c3.
  Proof.
    intros c1 c2 c3 H12 H23 n1 n3 S1 N1 S3 N3.
    destruct (sa_fin_exists c2) as [n2 [S2 N2]].
    rewrite (H12 n1 n2 S1 N1 S2 N2). exact (H23 n2 n3 S2 N2 S3 N3).
  Qed.

  (* Under PJC everywhere and DupAbsorb, every received list is finish-equivalent to a
     duplicate-free list with the same events. *)
  Lemma sa_reduce : forall s0, (forall E, PJC event_eq_dec apply rho valid enabled (s0, E)) ->
    DupAbsorb s0 ->
    forall n E, length E <= n -> exists E0, NoDup E0 /\ SameSet E E0 /\ FinEq (s0, E) (s0, E0).
  Proof.
    intros s0 HP HD n. induction n as [| n IH]; intros E Hl.
    - destruct E; [| simpl in Hl; lia]. exists []. split; [constructor |].
      split; [intros e; reflexivity | apply sa_fin_self; apply HP].
    - destruct (sa_nodup_or_dup event_eq_dec E) as [Hnd | [x [a [r [-> Ha]]]]].
      + exists E. split; [exact Hnd |]. split; [intros e; reflexivity | apply sa_fin_self; apply HP].
      + assert (Hl' : length (x ++ r) <= n) by (rewrite app_length in *; simpl in Hl; lia).
        destruct (IH (x ++ r) Hl') as [E0 [Hnd [HS HF]]].
        exists E0. split; [exact Hnd |]. split.
        * intros e. rewrite <- (HS e). rewrite in_app_iff in Ha. rewrite !in_app_iff. simpl.
          split; [| tauto]. intros [H | [<- | H]]; tauto.
        * apply (sa_fin_trans _ (s0, a :: x ++ r)).
          { apply sa_fin_perm; [apply HP |]. apply Permutation_sym. apply Permutation_middle. }
          apply (sa_fin_trans _ (s0, x ++ r)); [| exact HF].
          destruct (HD (x ++ r) a Ha) as [m1 [m2 [S1 [N1 [S2 [N2 E12]]]]]].
          intros n1 n2 T1 M1 T2 M2.
          rewrite (sa_pjc_un _ (HP _) n1 m1 T1 M1 S1 N1), (sa_pjc_un _ (HP _) n2 m2 T2 M2 S2 N2).
          exact E12.
  Qed.

  (* The exact condition for any enabledness. *)
  Theorem stream_alo_exact : Progress valid enabled -> forall s0,
    StreamAgreeA s0 <-> (forall E, PJC event_eq_dec apply rho valid enabled (s0, E)) /\ DupAbsorb s0.
  Proof.
    intros Hp s0. unfold StreamAgreeA. rewrite stream_agree_d_set_function. split.
    - intros H. split.
      + intros E. apply pjc_exact with (P := P) (ltP := ltP) (Phi := Phi); [exact wf_ltP | exact wfc_wf |].
        apply (sx_un_cr event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec enabled_dec).
        intros [s1 B1] [s2 B2] S1 N1 S2 N2.
        pose proof (H E E Logic.I Logic.I (fun e => iff_refl _) _ _ S1 N1 S2 N2) as Es. simpl in Es.
        pose proof (sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N1) as E1.
        pose proof (sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N2) as E2.
        simpl in E1, E2. subst. reflexivity.
      + intros E a Ha.
        destruct (sa_fin_exists (s0, a :: E)) as [n1 [S1 N1]].
        destruct (sa_fin_exists (s0, E)) as [n2 [S2 N2]].
        exists n1, n2. repeat split; try assumption.
        apply (H (a :: E) E Logic.I Logic.I); try assumption.
        intros e. simpl. split; [intros [<- | He]; assumption | intros He; right; exact He].
    - intros [HP HD] E1 E2 _ _ HS.
      destruct (sa_reduce s0 HP HD (length E1) E1 (le_n _)) as [F1 [Nd1 [HS1 HF1]]].
      destruct (sa_reduce s0 HP HD (length E2) E2 (le_n _)) as [F2 [Nd2 [HS2 HF2]]].
      apply (sa_fin_trans _ (s0, F1)); [exact HF1 |].
      apply (sa_fin_trans _ (s0, F2)); [| apply sa_fin_sym; exact HF2].
      apply sa_fin_perm; [apply HP |]. apply NoDup_Permutation; [exact Nd1 | exact Nd2 |].
      intros e. rewrite <- (HS1 e), <- (HS2 e). apply HS.
  Qed.

  (* stream_exact, rederived through the set-function form of the duplicate-free class. *)
  Theorem stream_exact_recovered : Progress valid enabled -> forall s0,
    StreamAgreeD (@NoDup Event) s0 <-> (forall E, NoDup E -> PJC event_eq_dec apply rho valid enabled (s0, E)).
  Proof.
    intros Hp s0. rewrite stream_agree_d_set_function. split.
    - intros H E Hnd. apply pjc_exact with (P := P) (ltP := ltP) (Phi := Phi); [exact wf_ltP | exact wfc_wf |].
      apply (sx_un_cr event_eq_dec apply rho valid enabled P ltP wf_ltP Phi wfc_wf valid_dec enabled_dec).
      intros [s1 B1] [s2 B2] S1 N1 S2 N2.
      pose proof (H E E Hnd Hnd (fun e => iff_refl _) _ _ S1 N1 S2 N2) as Es. simpl in Es.
      pose proof (sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N1) as E1.
      pose proof (sx_nf_empty_progress event_eq_dec apply rho valid enabled valid_dec Hp _ N2) as E2.
      simpl in E1, E2. subst. reflexivity.
    - intros H E1 E2 Nd1 Nd2 HS. apply sa_fin_perm; [apply H; exact Nd1 |].
      apply NoDup_Permutation; assumption.
  Qed.
End StreamDelivery.

(* ============================================================================================ *)
(* Free delivery: the local exact condition.                                                    *)
(* ============================================================================================ *)

Section FreeStreamALO.
  Context {State Event : Type}.
  Hypothesis event_eq_dec : forall a b : Event, {a = b} + {a <> b}.
  Variable apply    : Event -> State -> State.
  Variable rho      : State -> State.
  Variable rho_star : State -> State.
  Variable valid    : State -> Prop.

  Variable P   : Type.
  Variable ltP : P -> P -> Prop.
  Hypothesis wf_ltP : well_founded ltP.
  Variable Phi : State -> P.
  Hypothesis wfc_wf : forall sigma, ~ valid sigma -> ltP (Phi (rho sigma)) (Phi sigma).
  Hypothesis valid_dec : forall s, {valid s} + {~ valid s}.

  Local Notation fpstep := (prstep event_eq_dec apply rho valid fen).
  Local Notation fcstep := (GovernanceCausal.step event_eq_dec apply rho valid fen).

  Hypothesis rho_star_reach : forall sigma B, star fcstep (sigma, B) (rho_star sigma, B).
  Hypothesis rho_star_valid : forall sigma, valid (rho_star sigma).

  Local Notation g := (gov apply rho_star).
  Local Notation gr := (grun apply rho_star).

  (* a is idempotent at every state where a processor first applies it. *)
  Definition PIdem (s0 : State) (a : Event) : Prop :=
    forall u, NoDup (u ++ [a]) -> g a (g a (gr (rho_star s0) u)) = g a (gr (rho_star s0) u).

  Definition StreamAgreeAF (s0 : State) : Prop :=
    StreamAgreeA event_eq_dec apply rho valid fen s0.

  Lemma sf_grun_runT : forall w s, gr s w = runT g w s.
  Proof. induction w as [| e w IH]; intros s; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

  Lemma sf_grun_valid : forall w s, valid s -> valid (gr s w).
  Proof. induction w as [| e w IH]; intros s Hv; simpl; [exact Hv | apply IH; apply rho_star_valid]. Qed.

  (* Every finished processor reduction from (s0, E) is a governed run of a reordering of E. *)
  Lemma sf_final : forall s0 E n, star fpstep (s0, E) n -> normal_form fpstep n ->
    exists w, Permutation w E /\ n = (gr (rho_star s0) w, []).
  Proof.
    intros s0 E n S N.
    pose proof (fx_inv_reach event_eq_dec apply rho rho_star valid rho_star_reach rho_star_valid s0 E n S) as Hi.
    pose proof (st_nf_valid event_eq_dec apply rho valid fen valid_dec n N) as Hv.
    pose proof (sx_nf_empty_progress event_eq_dec apply rho valid fen valid_dec (fen_progress valid) n N) as Hb.
    destruct (fx_inv_valid event_eq_dec apply rho rho_star valid rho_star_valid s0 E n Hi Hv) as [w [HP Hs]].
    exists w. destruct n as [s B]. simpl in *. subst B. rewrite app_nil_r in HP.
    split; [exact HP | rewrite Hs; reflexivity].
  Qed.

  Lemma sf_run : forall s0 w, star fpstep (s0, w) (gr (rho_star s0) w, []) /\
                             normal_form fpstep (gr (rho_star s0) w, []).
  Proof.
    intros s0 w. split.
    - pose proof (fx_run_from event_eq_dec apply rho rho_star valid rho_star_reach rho_star_valid s0 w [])
        as H. rewrite app_nil_r in H. exact H.
    - apply fx_nf_empty. apply sf_grun_valid. apply rho_star_valid.
  Qed.

  (* The stream property is the governed-replay at-least-once property from rho_star s0. *)
  Theorem stream_alo_aloconv : forall s0,
    StreamAgreeAF s0 <-> ALOConv g (fun _ => True) (rho_star s0).
  Proof.
    intros s0. unfold StreamAgreeAF, StreamAgreeA. rewrite stream_agree_d_set_function. split.
    - intros H d o _ Hnd Hs. rewrite <- !sf_grun_runT.
      destruct (sf_run s0 d) as [S1 N1]. destruct (sf_run s0 o) as [S2 N2].
      exact (H d o Logic.I Logic.I (fun e => iff_sym (Hs e)) _ _ S1 N1 S2 N2).
    - intros H E1 E2 _ _ HS n1 n2 S1 N1 S2 N2.
      destruct (sf_final s0 E1 n1 S1 N1) as [w1 [P1 ->]].
      destruct (sf_final s0 E2 n2 S2 N2) as [w2 [P2 ->]]. simpl.
      rewrite !sf_grun_runT.
      set (o := dedup event_eq_dec w1).
      assert (Ho1 : forall x, In x o <-> In x w1) by (intros x; apply dedup_In).
      assert (Ho2 : forall x, In x o <-> In x w2).
      { intros x. rewrite Ho1. split; intros Hx.
        - apply (Permutation_in x (Permutation_sym P2)). apply HS. exact (Permutation_in x P1 Hx).
        - apply (Permutation_in x (Permutation_sym P1)). apply HS. exact (Permutation_in x P2 Hx). }
      rewrite (H w1 o (Forall_True _) (dedup_NoDup event_eq_dec w1) Ho1).
      symmetry. exact (H w2 o (Forall_True _) (dedup_NoDup event_eq_dec w1) Ho2).
  Qed.

  Lemma sf_pcc_iff : forall s0, CommReach g (fun _ => True) (rho_star s0) <-> PCC apply rho_star s0.
  Proof.
    intros s0. split.
    - intros H w e1 e2 Hnd. rewrite sf_grun_runT.
      exact (H w e1 e2 (Forall_True _) (fx_nodup_ne w e1 e2 Hnd) Hnd).
    - intros H p a b _ _ Hnd. rewrite <- sf_grun_runT. exact (H p a b Hnd).
  Qed.

  Lemma sf_idem_iff : forall s0 a, IdemReach g (fun _ => True) (rho_star s0) a <-> PIdem s0 a.
  Proof.
    intros s0 a. split.
    - intros H u Hnd. rewrite sf_grun_runT. exact (H u (Forall_True _) Hnd).
    - intros H u _ Hnd. rewrite <- sf_grun_runT. exact (H u Hnd).
  Qed.

  (* The exact condition under free delivery. *)
  Theorem stream_alo_exact_free : forall s0,
    StreamAgreeAF s0 <-> PCC apply rho_star s0 /\ forall a, PIdem s0 a.
  Proof.
    intros s0. rewrite stream_alo_aloconv, alo_exact; [| exact event_eq_dec]. rewrite sf_pcc_iff.
    split; intros [HC HI]; split; try exact HC; intros a; apply sf_idem_iff; exact (HI a).
  Qed.

  (* At-least-once agreement is exactly-once agreement (stream_exact_free's property) plus
     reachable idempotence. *)
  Theorem stream_alo_free_split : forall s0,
    StreamAgreeAF s0 <-> StreamAgree event_eq_dec apply rho valid fen s0 /\ forall a, PIdem s0 a.
  Proof.
    intros s0. rewrite stream_alo_exact_free.
    rewrite (stream_exact_free event_eq_dec apply rho rho_star valid P ltP wf_ltP Phi wfc_wf
               rho_star_reach rho_star_valid s0). reflexivity.
  Qed.
End FreeStreamALO.

(* ============================================================================================ *)
(* Instances: every state valid, no compensation, free delivery.                                *)
(* ============================================================================================ *)

Section Instances.
  Variable ap : nat -> nat -> nat.

  Local Notation ip := (prstep Nat.eq_dec ap (fun s : nat => s) (fun _ : nat => True) fen).

  Lemma in_wfc : forall s : nat, ~ True -> (fun _ : nat => 0) s < (fun _ : nat => 0) s.
  Proof. intros s H. exfalso. exact (H Logic.I). Qed.

  Lemma in_reach : forall (s : nat) (B : list nat),
    star (GovernanceCausal.step Nat.eq_dec ap (fun s => s) (fun _ => True) fen) (s, B) (s, B).
  Proof. intros. apply star_refl. Qed.

  Definition in_valid_dec (s : nat) : {True} + {~ True} := left Logic.I.

  Lemma in_progress : Progress (fun _ : nat => True) (@fen nat nat).
  Proof. exact (fen_progress _). Qed.

  Lemma in_run : forall s w, star ip (s, w) (grun ap (fun s => s) s w, []) /\
                             normal_form ip (grun ap (fun s => s) s w, []).
  Proof.
    exact (sf_run Nat.eq_dec ap (fun s => s) (fun s => s) (fun _ => True) in_reach (fun _ => Logic.I)).
  Qed.

  Lemma in_final : forall s E n, star ip (s, E) n -> normal_form ip n ->
    exists w, Permutation w E /\ n = (grun ap (fun s => s) s w, []).
  Proof.
    exact (sf_final Nat.eq_dec ap (fun s => s) (fun s => s) (fun _ => True) in_valid_dec in_reach
             (fun _ => Logic.I)).
  Qed.

  Theorem in_alo_exact : forall s0,
    StreamAgreeA Nat.eq_dec ap (fun s => s) (fun _ => True) fen s0 <->
    PCC ap (fun s => s) s0 /\ forall a, PIdem ap (fun s => s) s0 a.
  Proof.
    exact (stream_alo_exact_free Nat.eq_dec ap (fun s => s) (fun s => s) (fun _ => True) in_valid_dec
             in_reach (fun _ => Logic.I)).
  Qed.

  Theorem in_alo_general : forall s0,
    StreamAgreeA Nat.eq_dec ap (fun s => s) (fun _ => True) fen s0 <->
    (forall E, PJC Nat.eq_dec ap (fun s => s) (fun _ => True) fen (s0, E)) /\
    DupAbsorb Nat.eq_dec ap (fun s => s) (fun _ => True) fen s0.
  Proof.
    exact (stream_alo_exact Nat.eq_dec ap (fun s => s) (fun _ => True) fen nat lt lt_wf (fun _ => 0)
             in_wfc in_valid_dec (fen_dec Nat.eq_dec) fen_perm in_progress).
  Qed.
End Instances.

(* ----- the counter: every event adds 1 ----- *)

Definition ct_add (_ : nat) (s : nat) : nat := S s.

Lemma ct_grun : forall w s, grun ct_add (fun s => s) s w = s + length w.
Proof. induction w as [| e w IH]; intros s; simpl; [lia | rewrite IH; unfold gov, ct_add; lia]. Qed.

Theorem ct_alo_fails :
  PCC ct_add (fun s => s) 0 /\
  StreamAgree Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen 0 /\
  (forall E, PJC Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen (0, E)) /\
  ~ PIdem ct_add (fun s => s) 0 0 /\
  ~ DupAbsorb Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen 0 /\
  ~ StreamAgreeA Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen 0 /\
  exists p1 p2,
    is_processor_d Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen (fun _ => True)
      (fun e => In e [0]) 0 p1 /\
    is_processor_d Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen (fun _ => True)
      (fun e => In e [0]) 0 p2 /\
    settled Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen p1 0 /\
    settled Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen p2 0 /\
    recv p1 0 = [0] /\ recv p2 0 = [0; 0] /\ psi p1 0 = 1 /\ psi p2 0 = 2.
Proof.
  assert (Hpcc : PCC ct_add (fun s => s) 0) by (intros w e1 e2 _; reflexivity).
  assert (Hpi : ~ PIdem ct_add (fun s => s) 0 0).
  { intro H. pose proof (H [] ltac:(repeat constructor; simpl; tauto)) as E. cbv in E. discriminate E. }
  assert (Hna : ~ StreamAgreeA Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen 0).
  { intro H. apply Hpi. exact (proj2 (proj1 (in_alo_exact ct_add 0) H) 0). }
  assert (Hpjc : forall E, PJC Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen (0, E)).
  { intros E. apply (pjc_exact Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen nat lt lt_wf
                       (fun _ => 0) in_wfc).
    apply (sx_un_cr Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen nat lt lt_wf (fun _ => 0)
             in_wfc in_valid_dec (fen_dec Nat.eq_dec)).
    intros n1 n2 S1 N1 S2 N2.
    destruct (in_final ct_add 0 E n1 S1 N1) as [w1 [P1 ->]].
    destruct (in_final ct_add 0 E n2 S2 N2) as [w2 [P2 ->]].
    rewrite !ct_grun, (Permutation_length P1), (Permutation_length P2). reflexivity. }
  split; [exact Hpcc |].
  split.
  { apply (stream_exact_free Nat.eq_dec ct_add (fun s => s) (fun s => s) (fun _ => True) nat lt lt_wf
             (fun _ => 0) in_wfc (in_reach ct_add) (fun _ => Logic.I)). exact Hpcc. }
  split; [exact Hpjc |]. split; [exact Hpi |].
  split; [intro HD; apply Hna; apply (proj2 (in_alo_general ct_add 0)); split; assumption |].
  split; [exact Hna |].
  destruct (in_run ct_add 0 [0]) as [S1 N1]. destruct (in_run ct_add 0 [0; 0]) as [S2 N2].
  exists (const_proc [0] (grun ct_add (fun s => s) 0 [0], [])),
         (const_proc [0; 0] (grun ct_add (fun s => s) 0 [0; 0], [])).
  split; [apply sa_const_procd; [exact Logic.I | intros e; reflexivity | exact S1] |].
  split; [apply sa_const_procd; [exact Logic.I | | exact S2] |].
  { intros e. simpl. tauto. }
  split; [exact N1 |]. split; [exact N2 |].
  repeat split.
Qed.

(* ----- the overwrite register: event e sets the state to e ----- *)

Definition ow_set (e : nat) (_ : nat) : nat := e.

Lemma ow_grun_snoc : forall w z s, grun ow_set (fun s => s) s (w ++ [z]) = z.
Proof. induction w as [| e w IH]; intros z s; [reflexivity | apply IH]. Qed.

Theorem ow_alo_fails :
  (forall s0 a, PIdem ow_set (fun s => s) s0 a) /\
  (forall a s, ow_set a (ow_set a s) = ow_set a s) /\
  DupAbsorb Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen 0 /\
  ~ PCC ow_set (fun s => s) 0 /\
  ~ PJC Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen (0, [1; 2]) /\
  ~ StreamAgreeA Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen 0.
Proof.
  assert (Hpcc : ~ PCC ow_set (fun s => s) 0).
  { intro H. pose proof (H [] 1 2 ltac:(repeat constructor; simpl; intuition discriminate)) as E.
    cbv in E. discriminate E. }
  split; [intros s0 a u _; reflexivity |].
  split; [intros a s; reflexivity |].
  split.
  - intros E a Ha.
    destruct (rev_case E) as [-> | [z [r ->]]]; [destruct Ha |].
    destruct (in_run ow_set 0 (a :: r ++ [z])) as [S1 N1].
    destruct (in_run ow_set 0 (r ++ [z])) as [S2 N2].
    exists (grun ow_set (fun s => s) 0 (a :: r ++ [z]), []), (grun ow_set (fun s => s) 0 (r ++ [z]), []).
    repeat split; try assumption. simpl.
    change (grun ow_set (fun s => s) (gov ow_set (fun s => s) a 0) (r ++ [z]) =
            grun ow_set (fun s => s) 0 (r ++ [z])).
    rewrite !ow_grun_snoc. reflexivity.
  - split; [exact Hpcc |]. split.
    + intro H.
      pose proof (proj2 (pjc_exact Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen nat lt lt_wf
                           (fun _ => 0) in_wfc (0, [1; 2])) H) as Hcr.
      destruct (in_run ow_set 0 [1; 2]) as [S1 N1].
      assert (S2 : star (prstep Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen) (0, [1; 2]) (1, [])).
      { eapply star_step; [apply (ps_apply Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen 0 [1; 2] 2);
          [exact Logic.I | right; left; reflexivity | right; left; reflexivity] |].
        cbn. eapply star_step; [apply (ps_apply Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen 2 [1] 1);
          [exact Logic.I | left; reflexivity | left; reflexivity] |]. cbn. apply star_refl. }
      destruct (Hcr _ _ S1 S2) as [w [A1 A2]].
      rewrite <- (star_from_nf _ _ _ N1 A1) in A2.
      pose proof (star_from_nf _ _ _ (fx_nf_empty Nat.eq_dec ow_set (fun s => s) (fun _ => True) 1 Logic.I) A2) as E.
      cbv in E. discriminate E.
    + intro H. apply Hpcc. exact (proj1 (proj1 (in_alo_exact ow_set 0) H)).
Qed.

Theorem ow_general :
  DupAbsorb Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen 0 /\
  ~ (forall E, PJC Nat.eq_dec ow_set (fun s => s) (fun _ => True) fen (0, E)).
Proof.
  destruct ow_alo_fails as [_ [_ [HD [_ [HP _]]]]].
  split; [exact HD | intro H; exact (HP (H _))].
Qed.

Theorem ct_general :
  (forall E, PJC Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen (0, E)) /\
  ~ DupAbsorb Nat.eq_dec ct_add (fun s => s) (fun _ => True) fen 0.
Proof. destruct ct_alo_fails as [_ [_ [HP [_ [HD _]]]]]. split; assumption. Qed.

(* ----- the max-register: non-vacuity ----- *)

Definition mx_max (e s : nat) : nat := Nat.max e s.

Theorem mx_alo_holds :
  (forall s0, PCC mx_max (fun s => s) s0) /\
  (forall s0 a, PIdem mx_max (fun s => s) s0 a) /\
  (forall s0, StreamAgreeA Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen s0) /\
  exists p1 p2,
    is_processor_d Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen (fun _ => True)
      (fun e => In e [1; 2]) 0 p1 /\
    is_processor_d Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen (fun _ => True)
      (fun e => In e [1; 2]) 0 p2 /\
    settled Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen p1 0 /\
    settled Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen p2 0 /\
    recv p1 0 = [1; 2; 1] /\ recv p2 0 = [2; 1] /\ psi p1 0 = psi p2 0.
Proof.
  assert (Hpcc : forall s0, PCC mx_max (fun s => s) s0).
  { intros s0 w e1 e2 _. unfold gov, mx_max. lia. }
  assert (Hpi : forall s0 a, PIdem mx_max (fun s => s) s0 a).
  { intros s0 a u _. unfold gov, mx_max. lia. }
  assert (Hag : forall s0, StreamAgreeA Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen s0).
  { intros s0. apply (in_alo_exact mx_max s0). split; [apply Hpcc | apply Hpi]. }
  split; [exact Hpcc |]. split; [exact Hpi |]. split; [exact Hag |].
  destruct (in_run mx_max 0 [1; 2; 1]) as [S1 N1]. destruct (in_run mx_max 0 [2; 1]) as [S2 N2].
  assert (P1 : is_processor_d Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen (fun _ => True)
                 (fun e => In e [1; 2]) 0 (const_proc [1; 2; 1] (grun mx_max (fun s => s) 0 [1; 2; 1], [])))
    by (apply sa_const_procd; [exact Logic.I | intros e; simpl; tauto | exact S1]).
  assert (P2 : is_processor_d Nat.eq_dec mx_max (fun s => s) (fun _ => True) fen (fun _ => True)
                 (fun e => In e [1; 2]) 0 (const_proc [2; 1] (grun mx_max (fun s => s) 0 [2; 1], [])))
    by (apply sa_const_procd; [exact Logic.I | intros e; simpl; tauto | exact S2]).
  exists (const_proc [1; 2; 1] (grun mx_max (fun s => s) 0 [1; 2; 1], [])),
         (const_proc [2; 1] (grun mx_max (fun s => s) 0 [2; 1], [])).
  split; [exact P1 |]. split; [exact P2 |]. split; [exact N1 |]. split; [exact N2 |].
  split; [reflexivity |]. split; [reflexivity |].
  apply (Hag 0 _ _ _ 0 0 P1 P2 N1 N2). intros e. simpl. tauto.
Qed.
