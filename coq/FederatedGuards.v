(* FederatedGuards.v: buffered guards in acyclic federations, exactly (gap 15 (d) of
   REGIME-AUDIT.md). Axiom-free.

   FederationGRS.v presents the federated rewrite system as an instance of Governance.step on list
   states (apply steps run the raw event on its registry, the compensation step is rho_Fed), with an
   enabledness parameter en. Its exact theorems fix en: free delivery (fed_grs_exact) and the
   federal guard genab (an event fires only at a federally valid state: fed_guarded_exact). Here
   events WAIT: a buffered event is applied only when its guard holds, and stays in the buffer
   otherwise; a normal form may hold stuck events.

   (d1) Any enabledness. fed_jcg_exact: for every en (guards on the federated state and the buffer,
   evaluated at any state, possibly disabled or enabled by compensation), the federated system is
   confluent from c0 iff JC' (EnabledAfterComp.JCg) holds from c0. This is jcg_exact instantiated
   at the federated GRS; termination is discharged (fed_terminating), so the statement has no
   termination premise.

   (d2) Buffered guards under the federal guard (the FedMachine discipline: compensation completes
   before the next event). A guard g e l is a decidable predicate on the federated state;
     benab e l B := In e B /\ gvalid l /\ g e l.
   A word p is guard-feasible from l (feas l p) when each event's guard holds at the federated
   state where it is applied. The local condition at the states such runs reach:
     GCR s0 := for every guard-feasible p from s0 and distinct e1, e2 whose guards both hold at
               l := lrun p s0 (co-enabled), each stays enabled after the other
               (g e2 (gov e1 l) /\ g e1 (gov e2 l)) and they commute (gov e2 (gov e1 l) =
               gov e1 (gov e2 l)).
   - fed_buffered_exact: gvalid s0 -> ((forall B, UN Gb (s0, B)) <-> GCR s0).
   - fed_buffered_cr: gvalid s0 -> ((forall B, CR Gb (s0, B)) <-> GCR s0).
   - fed_buffered_edge: the per-edge form: the commutation clause is, at the reachable federated
     state, C1 in both directions for co-enabled events on different registries and C2 for
     co-enabled events of one registry (FederationEventsConverse.reach_commute_iff), so
     (forall B, UN Gb (s0, B)) <-> GCRE s0.
   - fed_buffered_recovers: with the trivial guard (g = True, no waiting), GCR s0 <-> C1R1 /\ C2R,
     the condition of fed_guarded_exact: the guarded theorem is the case of guards that never
     block.

   Counterexamples and non-vacuity (a two-registry federation: registry 0 holds a value, registry
   1 copies it; events act on registry 0).
   - bg_persistence_needed: Raise and Lift both set the value to 1, so every two events commute at
     every state and fed_guarded_exact's condition (C1R1 /\ C2R) holds; Lift waits for the value 0.
     From ([0; 0], [Raise; Lift]) the run "Raise first" strands Lift (normal form ([1; 1], [Lift]))
     and the run "Lift first" ends at ([1; 1], []): UN fails, GCR fails. Commutation (the
     unguarded condition) is not sufficient once guards make events wait: enabledness must
     persist across co-enabled events.
   - bg_commute_needed: Put1 and Put2 overwrite the value (1, 2), no guard: every enabledness
     persists, the commutation clause fails, UN fails.
   - bg_wait_exact: WRaise sets the value to 1 and waits for 0; WBump sets it to 2 and waits for
     1. No two distinct events are ever co-enabled, so GCR holds from every start and every buffer
     has a unique normal form (and the system is confluent, so JC' holds by fed_jcg_exact); from
     ([0; 0], [WBump; WRaise]) WBump waits for WRaise and the run ends at ([2; 2], []). WRaise and
     WBump do not commute, so C1R1 /\ C2R fails: the unguarded condition is not necessary either. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.EnabledAfterComp
  NC.FederationEvents NC.FederationEventsConverse NC.FederationGRS.
Import ListNotations.

Section Guards.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable ap : E -> V -> V.
  Variable o : list nat.
  Variable n : nat.
  Variable d : V.

  Hypothesis HC : Common V src f valid rho E reg (gsig V rho E reg ap) o.
  Hypothesis HR : forall j x, valid j (rho j x).
  Hypothesis Hrange : forall k, In k o <-> k < n.
  Hypothesis Hsrc : forall j k, In k (src j) -> k < n.
  Hypothesis Hout : forall k x, n <= k -> valid k x.
  Hypothesis vdec : forall k x, {valid k x} + {~ valid k x}.
  Hypothesis Veq : forall x y : V, {x = y} + {x <> y}.
  Hypothesis Eeq : forall x y : E, {x = y} + {x <> y}.

  Local Notation GA := (gapply V E reg ap n d).
  Local Notation GR := (grho V f rho o n d).
  Local Notation GV := (gvalid V f valid o n d).
  Local Notation GOV := (gov V f rho E reg ap o n d).
  Local Notation LR := (lrun V f rho E reg ap o n d).
  Local Notation GPhi := (gPhi V f valid o n d Hout vdec Veq).
  Local Notation sg := (gsig V rho E reg ap).

  Lemma bg_wfc : forall l, ~ GV l -> GPhi (GR l) < GPhi l.
  Proof. exact (g_wfc V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout vdec Veq). Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* (d1) Any enabledness: JC' is exact on the federated system.                          *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem fed_terminating : forall (en : E -> list V -> list E -> Prop) c,
    SN (step Eeq GA GR GV en) c.
  Proof. intros en c. exact (terminating Eeq GA GR GV GPhi en bg_wfc c). Qed.

  Theorem fed_jcg_exact : forall (en : E -> list V -> list E -> Prop) c0,
    CR (step Eeq GA GR GV en) c0 <-> JCg Eeq GA GR GR GV en c0.
  Proof.
    intros en c0.
    exact (jcg_exact Eeq GA GR GR GV en (g_reach V src f valid rho E reg ap o n d HC Hout vdec Veq Eeq en)
             c0 (fed_terminating en c0)).
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* (d2) Buffered guards under the federal guard.                                       *)
  (* ---------------------------------------------------------------------------------- *)

  Variable g : E -> list V -> Prop.
  Hypothesis gdec : forall e l, {g e l} + {~ g e l}.

  Definition benab (e : E) (l : list V) (B : list E) : Prop := In e B /\ GV l /\ g e l.

  Local Notation Gb := (step Eeq GA GR GV benab).

  (* Guard-feasible words: each event's guard holds where it is applied. *)
  Inductive feas : list V -> list E -> Prop :=
  | feas_nil : forall l, feas l []
  | feas_cons : forall l e p, g e l -> feas (GOV e l) p -> feas l (e :: p).

  Lemma lrun_cons : forall e p l, LR (e :: p) l = LR p (GOV e l).
  Proof. reflexivity. Qed.

  Lemma feas_snoc : forall p e l, feas l p -> g e (LR p l) -> feas l (p ++ [e]).
  Proof.
    induction p as [| x p IH]; intros e l Hp Hg; simpl in *.
    - constructor; [exact Hg | constructor].
    - inversion Hp as [| ? ? ? Hx Hp']; subst. constructor; [exact Hx |]. apply IH; assumption.
  Qed.

  Definition GCR (s0 : list V) : Prop :=
    forall p e1 e2, feas s0 p -> e1 <> e2 -> g e1 (LR p s0) -> g e2 (LR p s0) ->
      g e2 (GOV e1 (LR p s0)) /\ g e1 (GOV e2 (LR p s0)) /\
      GOV e2 (GOV e1 (LR p s0)) = GOV e1 (GOV e2 (LR p s0)).

  Lemma bg_lrun_valid : forall p l, GV l -> GV (LR p l).
  Proof. exact (lrun_valid V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout). Qed.

  Lemma bg_gov_valid : forall e l, GV (GOV e l).
  Proof. exact (gov_valid V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout). Qed.

  Lemma bg_reach : forall l B, star Gb (l, B) (GR l, B).
  Proof. exact (g_reach V src f valid rho E reg ap o n d HC Hout vdec Veq Eeq benab). Qed.

  Lemma bg_run : forall l B e, In e B -> benab e l B -> star Gb (l, B) (GOV e l, remove1 Eeq e B).
  Proof. exact (g_gov_run V src f valid rho E reg ap o n d HC Hout vdec Veq Eeq benab). Qed.

  Lemma bg_comp : forall l B e, benab e l B -> benab e (GR l) B.
  Proof.
    intros l B e [Hin [Hv Hg]].
    rewrite (grho_id V src f valid rho E reg ap o n d HC l Hv). split; [| split]; assumption.
  Qed.

  (* The states the buffered system reaches. *)
  Lemma bg_form : forall s0 B c, GV s0 -> star Gb (s0, B) c ->
    exists p, feas s0 p /\
      (fst c = LR p s0 \/ exists e, g e (LR p s0) /\ fst c = GA e (LR p s0)).
  Proof.
    intros s0 B c Hs0 S.
    apply (star_closed Gb (fun c => exists p, feas s0 p /\
             (fst c = LR p s0 \/ exists e, g e (LR p s0) /\ fst c = GA e (LR p s0))))
      with (x := (s0, B)); [| exists []; split; [constructor | left; reflexivity] | exact S].
    intros x y [p [Hp Hx]] Hst. destruct Hst as [s B' e Hin [_ [Hv Hg]] | s B' Hinv]; simpl in *.
    - destruct Hx as [-> | [e' [Hg' ->]]].
      + exists p. split; [exact Hp |]. right. exists e. split; [exact Hg | reflexivity].
      + assert (Es : GA e' (LR p s0) = LR (p ++ [e']) s0).
        { unfold lrun. rewrite fold_left_app. simpl. change (GA e' (LR p s0) = GOV e' (LR p s0)).
          unfold gov. symmetry. apply (grho_id V src f valid rho E reg ap o n d HC). exact Hv. }
        exists (p ++ [e']). split; [apply feas_snoc; assumption |].
        right. exists e. rewrite <- Es. split; [exact Hg | reflexivity].
    - destruct Hx as [-> | [e' [Hg' ->]]].
      + exfalso. apply Hinv. apply bg_lrun_valid. exact Hs0.
      + exists (p ++ [e']). split; [apply feas_snoc; assumption |].
        left. unfold lrun. rewrite fold_left_app. reflexivity.
  Qed.

  Lemma bg_valid_form : forall s0 B s B', GV s0 -> star Gb (s0, B) (s, B') -> GV s ->
    exists p, feas s0 p /\ s = LR p s0.
  Proof.
    intros s0 B s B' Hs0 S Hv. destruct (bg_form s0 B _ Hs0 S) as [p [Hp [Hx | [e [Hg Hx]]]]]; simpl in Hx.
    - exists p. split; assumption.
    - exists (p ++ [e]). split; [apply feas_snoc; assumption |].
      unfold lrun. rewrite fold_left_app. simpl. change (s = GOV e (LR p s0)). unfold gov.
      rewrite <- Hx. symmetry. apply (grho_id V src f valid rho E reg ap o n d HC). exact Hv.
  Qed.

  Lemma bg_jc : forall s0, GV s0 -> GCR s0 -> forall B, JC Eeq GA GR GR GV benab (s0, B).
  Proof.
    intros s0 Hs0 HG B sigma B' Hr. split.
    - intros e1 e2 Hin1 Hin2 [_ [Hv Hg1]] [_ [_ Hg2]] Hne.
      destruct (bg_valid_form s0 B sigma B' Hs0 Hr Hv) as [p [Hp ->]].
      destruct (HG p e1 e2 Hp Hne Hg1 Hg2) as [P21 [P12 Hc]].
      assert (Hne' : e2 <> e1) by (intro E'; apply Hne; symmetry; exact E').
      exists (GOV e2 (GOV e1 (LR p s0)), remove1 Eeq e2 (remove1 Eeq e1 B')). split.
      + change (GR (GA e1 (LR p s0))) with (GOV e1 (LR p s0)).
        apply bg_run; [apply in_rm; [exact Hin2 | exact Hne'] |].
        split; [apply in_rm; [exact Hin2 | exact Hne'] |]. split; [apply bg_gov_valid | exact P21].
      + change (GR (GA e2 (LR p s0))) with (GOV e2 (LR p s0)).
        rewrite Hc, remove1_comm.
        apply bg_run; [apply in_rm; [exact Hin1 | exact Hne] |].
        split; [apply in_rm; [exact Hin1 | exact Hne] |]. split; [apply bg_gov_valid | exact P12].
    - intros e Hinv _ [_ [Hv _]]. contradiction.
  Qed.

  Lemma bg_rm_head : forall e B, remove1 Eeq e (e :: B) = B.
  Proof. intros e B. simpl. destruct (Eeq e e) as [_ | H]; [reflexivity | congruence]. Qed.

  (* A guard-feasible word runs to completion, the rest of the buffer untouched. *)
  Lemma bg_run_feas : forall p l R, feas l p -> GV l -> star Gb (l, p ++ R) (LR p l, R).
  Proof.
    induction p as [| e p IH]; intros l R Hp Hl; [apply star_refl |].
    inversion Hp as [| ? ? ? Hg Hp']; subst.
    eapply star_trans.
    - apply (bg_run l ((e :: p) ++ R) e); [left; reflexivity |].
      split; [left; reflexivity | split; assumption].
    - cbn [app]. rewrite bg_rm_head. apply IH; [exact Hp' | apply bg_gov_valid].
  Qed.

  Lemma bg_nf_empty : forall l, GV l -> normal_form Gb (l, []).
  Proof. intros l Hv. exact (g_nf V f valid rho E reg ap o n d Eeq benab l Hv). Qed.

  Lemma bg_nf_stuck : forall l e, GV l -> ~ g e l -> normal_form Gb (l, [e]).
  Proof.
    intros l e Hv Hg [y H]. inversion H as [s B e' Hin [_ [_ He]] E1 E2 | s B Hinv E1 E2]; subst.
    - destruct Hin as [<- | []]. apply Hg. exact He.
    - exact (Hinv Hv).
  Qed.

  (* One branch of the peak at (l, [e1; e2]): e1 first. *)
  Lemma bg_branch : forall l e1 e2, GV l -> g e1 l -> e1 <> e2 ->
    (g e2 (GOV e1 l) -> star Gb (l, [e1; e2]) (GOV e2 (GOV e1 l), [])) /\
    (~ g e2 (GOV e1 l) -> star Gb (l, [e1; e2]) (GOV e1 l, [e2])).
  Proof.
    intros l e1 e2 Hv Hg Hne.
    assert (S1 : star Gb (l, [e1; e2]) (GOV e1 l, [e2])).
    { pose proof (bg_run l [e1; e2] e1 (or_introl eq_refl)
                    (conj (or_introl eq_refl) (conj Hv Hg))) as H.
      rewrite bg_rm_head in H. exact H. }
    split; [| intros _; exact S1].
    intros Hg2. eapply star_trans; [exact S1 |].
    pose proof (bg_run (GOV e1 l) [e2] e2 (or_introl eq_refl)
                  (conj (or_introl eq_refl) (conj (bg_gov_valid e1 l) Hg2))) as H.
    rewrite bg_rm_head in H. exact H.
  Qed.

  Lemma bg_branch' : forall l e1 e2, GV l -> g e2 l -> e1 <> e2 ->
    (g e1 (GOV e2 l) -> star Gb (l, [e1; e2]) (GOV e1 (GOV e2 l), [])) /\
    (~ g e1 (GOV e2 l) -> star Gb (l, [e1; e2]) (GOV e2 l, [e1])).
  Proof.
    intros l e1 e2 Hv Hg Hne.
    assert (R : remove1 Eeq e2 [e1; e2] = [e1]).
    { simpl. destruct (Eeq e1 e2) as [E' | _]; [contradiction |].
      destruct (Eeq e2 e2) as [_ | C]; [reflexivity | congruence]. }
    assert (S1 : star Gb (l, [e1; e2]) (GOV e2 l, [e1])).
    { pose proof (bg_run l [e1; e2] e2 (or_intror (or_introl eq_refl))
                    (conj (or_intror (or_introl eq_refl)) (conj Hv Hg))) as H.
      rewrite R in H. exact H. }
    split; [| intros _; exact S1].
    intros Hg1. eapply star_trans; [exact S1 |].
    pose proof (bg_run (GOV e2 l) [e1] e1 (or_introl eq_refl)
                  (conj (or_introl eq_refl) (conj (bg_gov_valid e2 l) Hg1))) as H.
    rewrite bg_rm_head in H. exact H.
  Qed.

  Lemma bg_necessary : forall s0, GV s0 -> (forall B, GovernanceConverse.UN Gb (s0, B)) -> GCR s0.
  Proof.
    intros s0 Hs0 HU p e1 e2 Hp Hne Hg1 Hg2. set (l := LR p s0).
    assert (Hv : GV l) by (apply bg_lrun_valid; exact Hs0).
    assert (S0 : star Gb (s0, p ++ [e1; e2]) (l, [e1; e2])) by (apply bg_run_feas; assumption).
    pose proof (HU (p ++ [e1; e2])) as U.
    destruct (bg_branch l e1 e2 Hv Hg1 Hne) as [A1 A2].
    destruct (bg_branch' l e1 e2 Hv Hg2 Hne) as [B1 B2].
    assert (Hv1 : GV (GOV e1 l)) by apply bg_gov_valid.
    assert (Hv2 : GV (GOV e2 l)) by apply bg_gov_valid.
    destruct (gdec e2 (GOV e1 l)) as [G21 | G21]; destruct (gdec e1 (GOV e2 l)) as [G12 | G12].
    - split; [exact G21 |]. split; [exact G12 |].
      assert (Eq := U _ _ (star_trans _ _ _ _ S0 (A1 G21)) (bg_nf_empty _ (bg_gov_valid _ _))
                      (star_trans _ _ _ _ S0 (B1 G12)) (bg_nf_empty _ (bg_gov_valid _ _))).
      injection Eq as Eq. exact Eq.
    - exfalso.
      assert (Eq := U _ _ (star_trans _ _ _ _ S0 (A1 G21)) (bg_nf_empty _ (bg_gov_valid _ _))
                      (star_trans _ _ _ _ S0 (B2 G12)) (bg_nf_stuck _ _ Hv2 G12)).
      discriminate Eq.
    - exfalso.
      assert (Eq := U _ _ (star_trans _ _ _ _ S0 (A2 G21)) (bg_nf_stuck _ _ Hv1 G21)
                      (star_trans _ _ _ _ S0 (B1 G12)) (bg_nf_empty _ (bg_gov_valid _ _))).
      discriminate Eq.
    - exfalso.
      assert (Eq := U _ _ (star_trans _ _ _ _ S0 (A2 G21)) (bg_nf_stuck _ _ Hv1 G21)
                      (star_trans _ _ _ _ S0 (B2 G12)) (bg_nf_stuck _ _ Hv2 G12)).
      injection Eq as _ Eq. apply Hne. symmetry. exact Eq.
  Qed.

  (* Headline: unique normal forms for every buffer iff GCR. *)
  Theorem fed_buffered_exact : forall s0, GV s0 ->
    ((forall B, GovernanceConverse.UN Gb (s0, B)) <-> GCR s0).
  Proof.
    intros s0 Hs0. split; [apply bg_necessary; exact Hs0 |].
    intros HG B. apply (jc_unique_normal_forms Eeq GA GR GR GV GPhi benab bg_wfc bg_reach bg_comp).
    apply bg_jc; assumption.
  Qed.

  (* The same with confluence. *)
  Theorem fed_buffered_cr : forall s0, GV s0 -> ((forall B, CR Gb (s0, B)) <-> GCR s0).
  Proof.
    intros s0 Hs0. split.
    - intros H. apply (fed_buffered_exact s0 Hs0). intros B. apply CR_UN. apply H.
    - intros HG B. apply (proj2 (jc_exact Eeq GA GR GR GV GPhi benab bg_wfc bg_reach bg_comp (s0, B))).
      apply bg_jc; assumption.
  Qed.

  (* ---------- the per-edge form ---------- *)

  Lemma bg_commute_feq : forall l e1 e2, GV l ->
    (GOV e2 (GOV e1 l) = GOV e1 (GOV e2 l) <->
     feq V (applyF V f rho E reg sg o e2 (applyF V f rho E reg sg o e1 (toF V d l)))
           (applyF V f rho E reg sg o e1 (applyF V f rho E reg sg o e2 (toF V d l)))).
  Proof.
    intros l e1 e2 [Hl [Hi Hc]].
    rewrite !(gov_two_eq V src f valid rho E reg ap o n d HC HR Hrange Hsrc). split.
    - intros Eq k. destruct (le_lt_dec n k) as [Hk | Hk].
      + assert (Hno : ~ In k o) by (intro H; apply Hrange in H; lia).
        pose proof (runF_out V src f valid rho E reg ap o HC [e1; e2] (toF V d l) k Hi Hno) as A.
        pose proof (runF_out V src f valid rho E reg ap o HC [e2; e1] (toF V d l) k Hi Hno) as B.
        simpl in A, B. unfold runF in A, B. simpl in A, B. rewrite A, B. reflexivity.
      + rewrite <- (toF_fromF V n d _ k Hk), <- (toF_fromF V n d (applyF V f rho E reg sg o e1 _) k Hk).
        rewrite Eq. reflexivity.
    - intros H. apply fromF_ext. apply feq_feqn. exact H.
  Qed.

  Definition GCRE (s0 : list V) : Prop :=
    forall p e1 e2, feas s0 p -> e1 <> e2 -> g e1 (LR p s0) -> g e2 (LR p s0) ->
      g e2 (GOV e1 (LR p s0)) /\ g e1 (GOV e2 (LR p s0)) /\
      (reg e1 <> reg e2 -> C1at V f rho E reg sg o (toF V d (LR p s0)) e1 e2 /\
                           C1at V f rho E reg sg o (toF V d (LR p s0)) e2 e1) /\
      (reg e1 = reg e2 -> C2at V f E reg sg (toF V d (LR p s0)) e1 e2).

  Theorem gcr_edge_iff : forall s0, GV s0 -> (GCR s0 <-> GCRE s0).
  Proof.
    intros s0 Hs0.
    assert (Hp : forall p, GV (LR p s0)) by (intros p; apply bg_lrun_valid; exact Hs0).
    assert (K : forall p e1 e2,
               GOV e2 (GOV e1 (LR p s0)) = GOV e1 (GOV e2 (LR p s0)) <->
               (reg e1 <> reg e2 -> C1at V f rho E reg sg o (toF V d (LR p s0)) e1 e2 /\
                                    C1at V f rho E reg sg o (toF V d (LR p s0)) e2 e1) /\
               (reg e1 = reg e2 -> C2at V f E reg sg (toF V d (LR p s0)) e1 e2)).
    { intros p e1 e2. rewrite (bg_commute_feq _ e1 e2 (Hp p)).
      destruct (Hp p) as [_ [Hi Hc]]. apply (reach_commute_iff V src f valid rho E reg sg o HC); assumption. }
    split.
    - intros H p e1 e2 Hf Hne G1 G2. destruct (H p e1 e2 Hf Hne G1 G2) as [A [B C]].
      split; [exact A |]. split; [exact B |]. apply K. exact C.
    - intros H p e1 e2 Hf Hne G1 G2. destruct (H p e1 e2 Hf Hne G1 G2) as [A [B C]].
      split; [exact A |]. split; [exact B |]. apply K. exact C.
  Qed.

  Theorem fed_buffered_edge : forall s0, GV s0 ->
    ((forall B, GovernanceConverse.UN Gb (s0, B)) <-> GCRE s0).
  Proof. intros s0 Hs0. rewrite fed_buffered_exact by exact Hs0. apply gcr_edge_iff. exact Hs0. Qed.
End Guards.

(* ============================================================================================ *)
(* The trivial guard recovers fed_guarded_exact's condition.                                    *)
(* ============================================================================================ *)

Section Recovered.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable ap : E -> V -> V.
  Variable o : list nat.
  Variable n : nat.
  Variable d : V.
  Hypothesis HC : Common V src f valid rho E reg (gsig V rho E reg ap) o.
  Hypothesis HR : forall j x, valid j (rho j x).
  Hypothesis Hrange : forall k, In k o <-> k < n.
  Hypothesis Hsrc : forall j k, In k (src j) -> k < n.
  Hypothesis Hout : forall k x, n <= k -> valid k x.
  Hypothesis vdec : forall k x, {valid k x} + {~ valid k x}.
  Hypothesis Veq : forall x y : V, {x = y} + {x <> y}.
  Hypothesis Eeq : forall x y : E, {x = y} + {x <> y}.

  Definition gtrue (_ : E) (_ : list V) : Prop := True.
  Definition gtrue_dec (e : E) (l : list V) : {gtrue e l} + {~ gtrue e l} := left Logic.I.

  Local Notation GA := (gapply V E reg ap n d).
  Local Notation GR := (grho V f rho o n d).
  Local Notation GV := (gvalid V f valid o n d).

  Lemma rc_step_iff : forall c c',
    step Eeq GA GR GV (benab V f valid E o n d gtrue) c c' <->
    step Eeq GA GR GV (genab V f valid E o n d) c c'.
  Proof.
    intros c c'. split; intros H.
    - destruct H as [s B e Hin [Hi [Hv _]] | s B Hinv].
      + apply st_apply; [exact Hin | split; assumption].
      + apply st_comp. exact Hinv.
    - destruct H as [s B e Hin [Hi Hv] | s B Hinv].
      + apply st_apply; [exact Hin | split; [exact Hi | split; [exact Hv | exact Logic.I]]].
      + apply st_comp. exact Hinv.
  Qed.

  Lemma rc_un : forall c, GovernanceConverse.UN (step Eeq GA GR GV (benab V f valid E o n d gtrue)) c <->
                          GovernanceConverse.UN (step Eeq GA GR GV (genab V f valid E o n d)) c.
  Proof.
    assert (Sub : forall (R S : (list V * list E) -> (list V * list E) -> Prop),
               (forall x y, R x y -> S x y) -> forall x y, star R x y -> star S x y).
    { intros R S HRS x y H. induction H as [x | x z y Hxz _ IH]; [apply star_refl |].
      eapply star_step; [apply HRS; exact Hxz | exact IH]. }
    intros c. split; intros H n1 n2 S1 N1 S2 N2.
    - apply H.
      + apply (Sub _ _ (fun x y => proj2 (rc_step_iff x y))). exact S1.
      + intros [y Hy]. apply N1. exists y. apply rc_step_iff. exact Hy.
      + apply (Sub _ _ (fun x y => proj2 (rc_step_iff x y))). exact S2.
      + intros [y Hy]. apply N2. exists y. apply rc_step_iff. exact Hy.
    - apply H.
      + apply (Sub _ _ (fun x y => proj1 (rc_step_iff x y))). exact S1.
      + intros [y Hy]. apply N1. exists y. apply rc_step_iff. exact Hy.
      + apply (Sub _ _ (fun x y => proj1 (rc_step_iff x y))). exact S2.
      + intros [y Hy]. apply N2. exists y. apply rc_step_iff. exact Hy.
  Qed.

  (* With guards that never block, GCR is the condition of fed_guarded_exact. *)
  Theorem fed_buffered_recovers : forall s0, GV s0 ->
    (GCR V f rho E reg ap o n d gtrue s0 <->
     C1R1 V f rho E reg (gsig V rho E reg ap) o (toF V d s0) /\
     C2R V f rho E reg (gsig V rho E reg ap) (Itot E) o (toF V d s0)).
  Proof.
    intros s0 Hs0.
    rewrite <- (fed_buffered_exact V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout vdec Veq Eeq
                  gtrue gtrue_dec s0 Hs0).
    rewrite <- (fed_guarded_exact V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout vdec Veq Eeq s0 Hs0).
    split; intros H B; apply rc_un; apply H.
  Qed.

  (* Under the trivial guard every word is feasible and GCR is commutation at every run state. *)
  Theorem gcr_true_iff : forall s0,
    GCR V f rho E reg ap o n d gtrue s0 <->
    forall p e1 e2, e1 <> e2 ->
      gov V f rho E reg ap o n d e2 (gov V f rho E reg ap o n d e1 (lrun V f rho E reg ap o n d p s0)) =
      gov V f rho E reg ap o n d e1 (gov V f rho E reg ap o n d e2 (lrun V f rho E reg ap o n d p s0)).
  Proof.
    assert (Hf : forall p l, feas V f rho E reg ap o n d gtrue l p).
    { induction p as [| e p IH]; intros l; constructor; [exact Logic.I | apply IH]. }
    intros s0. split.
    - intros H p e1 e2 Hne. exact (proj2 (proj2 (H p e1 e2 (Hf p s0) Hne Logic.I Logic.I))).
    - intros H p e1 e2 _ Hne _ _. split; [exact Logic.I |]. split; [exact Logic.I |]. apply H. exact Hne.
  Qed.
End Recovered.

(* ============================================================================================ *)
(* Instances: registry 0 holds a value, registry 1 copies it; every event acts on registry 0.    *)
(* ============================================================================================ *)

Definition bg_f (j : nat) (z : nat -> nat) (x : nat) : nat := if Nat.eqb j 1 then z 0 else x.
Definition bg_valid (_ : nat) (_ : nat) : Prop := True.
Definition bg_rho (_ : nat) (x : nat) : nat := x.

Lemma bg_common : forall (E : Type) (ap : E -> nat -> nat),
  Common nat src2 bg_f bg_valid bg_rho E (fun _ => 0) (gsig nat bg_rho E (fun _ => 0) ap) [0; 1].
Proof.
  intros E ap. constructor.
  - intros [| [| j]] z1 z2 x H; unfold bg_f; simpl; try reflexivity.
    apply H. left. reflexivity.
  - exact topo2.
  - intros; exact Logic.I.
  - intros [| [| j]] z z' x _ _ _; reflexivity.
  - intros; reflexivity.
  - intros; exact Logic.I.
  - intros e. left. reflexivity.
Qed.

Lemma bg_HR : forall j x, bg_valid j (bg_rho j x).
Proof. intros; exact Logic.I. Qed.

Lemma bg_range : forall k, In k [0; 1] <-> k < 2.
Proof. intros k. simpl. split; [intros [<- | [<- | []]]; lia | intros H; lia]. Qed.

Lemma bg_src : forall j k, In k (src2 j) -> k < 2.
Proof. intros [| [| j]] k H; simpl in H; try contradiction. destruct H as [<- | []]. lia. Qed.

Lemma bg_out : forall k x, 2 <= k -> bg_valid k x.
Proof. intros; exact Logic.I. Qed.

Definition bg_vdec (k x : nat) : {bg_valid k x} + {~ bg_valid k x} := left Logic.I.

Local Notation BGV := (gvalid nat bg_f bg_valid [0; 1] 2 0).

Lemma bg_valid_iff : forall l, BGV l <-> length l = 2 /\ nth 1 l 0 = nth 0 l 0.
Proof.
  intros l. split.
  - intros [Hl [_ Hc]]. split; [exact Hl |]. exact (Hc 1 (or_intror (or_introl eq_refl))).
  - intros [Hl Hc]. split; [exact Hl |]. split; [intros k; exact Logic.I |].
    intros j [<- | [<- | []]]; [reflexivity | exact Hc].
Qed.

Lemma bg_s0 : BGV [0; 0].
Proof. apply bg_valid_iff. split; reflexivity. Qed.

Lemma bg_v11 : BGV [1; 1].
Proof. apply bg_valid_iff. split; reflexivity. Qed.

Lemma bg_v22 : BGV [2; 2].
Proof. apply bg_valid_iff. split; reflexivity. Qed.

Definition at_v (v : nat) (l : list nat) : Prop := nth 0 l 0 = v.

(* ----- persistence is needed: Raise and Lift both set 1; Lift waits for 0 ----- *)

Inductive pev : Type := Raise | Lift.
Definition pev_eq : forall x y : pev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition p_ap (_ : pev) (_ : nat) : nat := 1.
Definition p_g (e : pev) (l : list nat) : Prop := match e with Raise => True | Lift => at_v 0 l end.
Definition p_gdec (e : pev) (l : list nat) : {p_g e l} + {~ p_g e l}.
Proof. destruct e; simpl; [left; exact Logic.I | unfold at_v; apply Nat.eq_dec]. Defined.

Local Notation PGOV := (gov nat bg_f bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0).
Local Notation PGb := (step pev_eq (gapply nat pev (fun _ => 0) p_ap 2 0) (grho nat bg_f bg_rho [0; 1] 2 0)
                         BGV (benab nat bg_f bg_valid pev [0; 1] 2 0 p_g)).

Lemma p_gov : forall e l, PGOV e l = [1; 1].
Proof. intros e l. reflexivity. Qed.

Theorem bg_persistence_needed :
  (forall l e1 e2, PGOV e2 (PGOV e1 l) = PGOV e1 (PGOV e2 l)) /\
  C1R1 nat bg_f bg_rho pev (fun _ => 0) (gsig nat bg_rho pev (fun _ => 0) p_ap) [0; 1] (toF nat 0 [0; 0]) /\
  C2R nat bg_f bg_rho pev (fun _ => 0) (gsig nat bg_rho pev (fun _ => 0) p_ap) (Itot pev) [0; 1]
    (toF nat 0 [0; 0]) /\
  star PGb ([0; 0], [Raise; Lift]) ([1; 1], [Lift]) /\ normal_form PGb ([1; 1], [Lift]) /\
  star PGb ([0; 0], [Raise; Lift]) ([1; 1], []) /\ normal_form PGb ([1; 1], []) /\
  ~ GovernanceConverse.UN PGb ([0; 0], [Raise; Lift]) /\
  ~ GCR nat bg_f bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 p_g [0; 0].
Proof.
  pose proof (bg_common pev p_ap) as HC.
  assert (Hcomm : forall l e1 e2, PGOV e2 (PGOV e1 l) = PGOV e1 (PGOV e2 l))
    by (intros; rewrite !p_gov; reflexivity).
  assert (Hrec : C1R1 nat bg_f bg_rho pev (fun _ => 0) (gsig nat bg_rho pev (fun _ => 0) p_ap) [0; 1]
                   (toF nat 0 [0; 0]) /\
                 C2R nat bg_f bg_rho pev (fun _ => 0) (gsig nat bg_rho pev (fun _ => 0) p_ap) (Itot pev) [0; 1]
                   (toF nat 0 [0; 0])).
  { apply (fed_buffered_recovers nat src2 bg_f bg_valid bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 HC bg_HR
             bg_range bg_src bg_out bg_vdec Nat.eq_dec pev_eq [0; 0] bg_s0).
    apply gcr_true_iff. intros p e1 e2 _. apply Hcomm. }
  assert (Hgcr : ~ GCR nat bg_f bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 p_g [0; 0]).
  { intro H. destruct (H [] Raise Lift (feas_nil _ _ _ _ _ _ _ _ _ _ _) ltac:(discriminate)
                         Logic.I eq_refl) as [G _].
    cbv in G. discriminate G. }
  assert (Hnf : normal_form PGb ([1; 1], [Lift])).
  { apply (bg_nf_stuck nat bg_f bg_valid bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 pev_eq p_g); [exact bg_v11 | cbv; discriminate]. }
  assert (Hnf0 : normal_form PGb ([1; 1], []))
    by exact (bg_nf_empty nat bg_f bg_valid bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 pev_eq p_g _ bg_v11).
  destruct (bg_branch nat src2 bg_f bg_valid bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 HC bg_HR
              bg_range bg_src bg_out bg_vdec Nat.eq_dec pev_eq p_g [0; 0] Raise Lift bg_s0 Logic.I
              ltac:(discriminate)) as [_ A2].
  destruct (bg_branch' nat src2 bg_f bg_valid bg_rho pev (fun _ => 0) p_ap [0; 1] 2 0 HC bg_HR
              bg_range bg_src bg_out bg_vdec Nat.eq_dec pev_eq p_g [0; 0] Raise Lift bg_s0 eq_refl
              ltac:(discriminate)) as [B1 _].
  pose proof (A2 ltac:(cbv; discriminate)) as S1. pose proof (B1 Logic.I) as S2.
  rewrite p_gov in S1. rewrite !p_gov in S2.
  split; [exact Hcomm |]. split; [exact (proj1 Hrec) |]. split; [exact (proj2 Hrec) |].
  split; [exact S1 |]. split; [exact Hnf |]. split; [exact S2 |]. split; [exact Hnf0 |].
  split; [| exact Hgcr].
  intro U. pose proof (U _ _ S1 Hnf S2 Hnf0) as Eq. discriminate Eq.
Qed.

(* ----- commutation is needed: Put1 and Put2 overwrite, no guard ----- *)

Inductive cev : Type := Put1 | Put2.
Definition cev_eq : forall x y : cev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition c_ap (e : cev) (_ : nat) : nat := match e with Put1 => 1 | Put2 => 2 end.

Theorem bg_commute_needed :
  (forall p, feas nat bg_f bg_rho cev (fun _ => 0) c_ap [0; 1] 2 0 (gtrue nat cev) [0; 0] p) /\
  ~ GCR nat bg_f bg_rho cev (fun _ => 0) c_ap [0; 1] 2 0 (gtrue nat cev) [0; 0] /\
  ~ (forall B, GovernanceConverse.UN
        (step cev_eq (gapply nat cev (fun _ => 0) c_ap 2 0) (grho nat bg_f bg_rho [0; 1] 2 0) BGV
           (benab nat bg_f bg_valid cev [0; 1] 2 0 (gtrue nat cev))) ([0; 0], B)).
Proof.
  pose proof (bg_common cev c_ap) as HC.
  assert (Hf : forall p l, feas nat bg_f bg_rho cev (fun _ => 0) c_ap [0; 1] 2 0 (gtrue nat cev) l p).
  { induction p as [| e p IH]; intros l; constructor; [exact Logic.I | apply IH]. }
  assert (Hg : ~ GCR nat bg_f bg_rho cev (fun _ => 0) c_ap [0; 1] 2 0 (gtrue nat cev) [0; 0]).
  { intro H. destruct (H [] Put1 Put2 (Hf [] _) ltac:(discriminate) Logic.I Logic.I) as [_ [_ Eq]].
    cbv in Eq. discriminate Eq. }
  split; [intros p; apply Hf |]. split; [exact Hg |].
  intro U. apply Hg.
  exact (proj1 (fed_buffered_exact nat src2 bg_f bg_valid bg_rho cev (fun _ => 0) c_ap [0; 1] 2 0 HC bg_HR
                  bg_range bg_src bg_out bg_vdec Nat.eq_dec cev_eq (gtrue nat cev) (gtrue_dec nat cev)
                  [0; 0] bg_s0) U).
Qed.

(* ----- waiting is exact: Raise waits for 0 and sets 1, Bump waits for 1 and sets 2 ----- *)

Inductive wev : Type := WRaise | WBump.
Definition wev_eq : forall x y : wev, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition w_ap (e : wev) (_ : nat) : nat := match e with WRaise => 1 | WBump => 2 end.
Definition w_g (e : wev) (l : list nat) : Prop := match e with WRaise => at_v 0 l | WBump => at_v 1 l end.
Definition w_gdec (e : wev) (l : list nat) : {w_g e l} + {~ w_g e l}.
Proof. destruct e; simpl; unfold at_v; apply Nat.eq_dec. Defined.

Local Notation WGb := (step wev_eq (gapply nat wev (fun _ => 0) w_ap 2 0) (grho nat bg_f bg_rho [0; 1] 2 0)
                         BGV (benab nat bg_f bg_valid wev [0; 1] 2 0 w_g)).
Local Notation WGOV := (gov nat bg_f bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0).

Lemma w_gcr : forall s0, GCR nat bg_f bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 w_g s0.
Proof.
  intros s0 p e1 e2 _ Hne G1 G2. exfalso.
  destruct e1, e2; try (apply Hne; reflexivity); simpl in G1, G2; unfold at_v in G1, G2;
    rewrite G1 in G2; discriminate G2.
Qed.

Theorem bg_wait_exact :
  (forall s0, BGV s0 -> forall B, GovernanceConverse.UN WGb (s0, B)) /\
  (forall s0, BGV s0 -> forall B, CR WGb (s0, B)) /\
  (forall s0, BGV s0 -> forall B,
     JCg wev_eq (gapply nat wev (fun _ => 0) w_ap 2 0) (grho nat bg_f bg_rho [0; 1] 2 0)
       (grho nat bg_f bg_rho [0; 1] 2 0) BGV (benab nat bg_f bg_valid wev [0; 1] 2 0 w_g) (s0, B)) /\
  star WGb ([0; 0], [WBump; WRaise]) ([2; 2], []) /\ normal_form WGb ([2; 2], []) /\
  WGOV WBump (WGOV WRaise [0; 0]) <> WGOV WRaise (WGOV WBump [0; 0]) /\
  ~ (C1R1 nat bg_f bg_rho wev (fun _ => 0) (gsig nat bg_rho wev (fun _ => 0) w_ap) [0; 1] (toF nat 0 [0; 0]) /\
     C2R nat bg_f bg_rho wev (fun _ => 0) (gsig nat bg_rho wev (fun _ => 0) w_ap) (Itot wev) [0; 1]
       (toF nat 0 [0; 0])).
Proof.
  pose proof (bg_common wev w_ap) as HC.
  assert (Hne : WGOV WBump (WGOV WRaise [0; 0]) <> WGOV WRaise (WGOV WBump [0; 0])) by (cbv; discriminate).
  assert (Hcr : forall s0, BGV s0 -> forall B, CR WGb (s0, B)).
  { intros s0 Hs0. apply (fed_buffered_cr nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC
                            bg_HR bg_range bg_src bg_out bg_vdec Nat.eq_dec wev_eq w_g w_gdec s0 Hs0).
    apply w_gcr. }
  split.
  { intros s0 Hs0. apply (fed_buffered_exact nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC
                            bg_HR bg_range bg_src bg_out bg_vdec Nat.eq_dec wev_eq w_g w_gdec s0 Hs0).
    apply w_gcr. }
  split; [exact Hcr |].
  split.
  { intros s0 Hs0 B. apply (fed_jcg_exact nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC
                              bg_HR bg_range bg_src bg_out bg_vdec Nat.eq_dec wev_eq).
    apply Hcr. exact Hs0. }
  split.
  { (* Bump is stuck until Raise has fired *)
    assert (R1 : star WGb ([0; 0], [WBump; WRaise]) (WGOV WRaise [0; 0], [WBump])).
    { pose proof (bg_run nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC
                    bg_out bg_vdec Nat.eq_dec wev_eq w_g [0; 0] [WBump; WRaise] WRaise
                    (or_intror (or_introl eq_refl))
                    (conj (or_intror (or_introl eq_refl)) (conj bg_s0 eq_refl))) as H.
      exact H. }
    eapply star_trans; [exact R1 |].
    pose proof (bg_run nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC
                  bg_out bg_vdec Nat.eq_dec wev_eq w_g (WGOV WRaise [0; 0]) [WBump] WBump
                  (or_introl eq_refl) (conj (or_introl eq_refl) (conj bg_v11 eq_refl))) as H.
    exact H. }
  split; [exact (bg_nf_empty nat bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 wev_eq w_g _ bg_v22) |].
  split; [exact Hne |].
  intro Hc.
  apply (proj2 (fed_buffered_recovers nat src2 bg_f bg_valid bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 HC bg_HR
                  bg_range bg_src bg_out bg_vdec Nat.eq_dec wev_eq [0; 0] bg_s0)) in Hc.
  apply Hne. exact (proj1 (gcr_true_iff nat bg_f bg_rho wev (fun _ => 0) w_ap [0; 1] 2 0 [0; 0]) Hc []
                      WRaise WBump ltac:(discriminate)).
Qed.
