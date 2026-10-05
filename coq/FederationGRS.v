(* FederationGRS.v: the federated theorems of the federation paper (Section "Federated
   Convergence"), mechanized in corrected form. Axiom-free.

   PART A (generic): the paper's federated rewrite system, as an instance of Governance.step.
   PART B (paper level): the paper's hypotheses (registry morphisms with a shared/local
          decomposition, resolution operators R1/R2, M1, acyclic or tree networks, component WFC
          and CC) as a record, and each federated result under its paper label.
   PART C (instances): the counterexamples, restated against the paper's exact hypotheses.

   Paper label -> Coq (federation paper, Section "Federated Convergence"):
     lem:authority (a)            fed_lem_authority_a                     exact
     lem:authority (b)            fed_lem_authority_b                     exact
     lem:authority (c)            fed_lem_authority_c_local               exact (first clause)
                                  fed_lem_authority_c_refuted             counterexample
                                  fed_lem_authority_c_corrected           corrected
     lem:fed-termination          fed_lem_fed_termination, fed_phase1_bound   exact, any state
     lem:resolved-termination     fed_lem_resolved_termination            exact, any state
     thm:fed-cc                   fed_thm_fed_cc_refuted                  counterexample
                                  fed_thm_fed_cc_corrected (XU), fed_thm_fed_cc_corrected_machine
     thm:fed-convergence          fed_thm_fed_convergence_refuted, fed_c2_paper_counterexample
                                  fed_thm_fed_convergence_corrected (XU),
                                  fed_thm_fed_convergence_guarded (C1 + C2),
                                  fed_thm_fed_convergence_exact
     thm:resolved-convergence     fed_thm_resolved_convergence_refuted
                                  fed_thm_resolved_convergence_corrected / _guarded / _exact
     cor:fed-nf                   fed_cor_fed_nf_refuted, fed_cor_fed_nf_corrected
     cor:resolved-nf              fed_cor_resolved_nf_corrected
   The federated GRS as a Governance.step instance: fed_grs_exact (cc_exact_from),
   fed_grs_un_c1_c2 (fed_exact), grs_unique_nf, fed_guarded_exact; C1 + C2 do not suffice for the
   unrestricted GRS: fed_grs_c1_c2_insufficient. See coq/README.md ("FederationGRS.v"). *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Governance NC.Trace NC.FederationEvents NC.FederationEventsConverse
  NC.GovernanceConverse.
Import ListNotations.

(* ========================================================================================= *)
(* PART A. The federated GRS.                                                                 *)
(* ========================================================================================= *)

Section GRS.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.        (* rho_{R_j}^*: phase 1 of rho_Fed on registry j *)
  Variable E : Type.
  Variable reg : E -> nat.
  Variable ap : E -> V -> V.           (* the raw apply(e, -) on registry reg e *)
  Variable o : list nat.               (* a topological order of the registries *)
  Variable n : nat.                    (* the registries are 0 .. n-1 *)
  Variable d : V.                      (* a filler value for list lookups *)

  (* gsm's Machine.Apply: the raw event, then the component normalizer. *)
  Definition gsig (e : E) (x : V) : V := rho (reg e) (ap e x).

  (* Free delivery: every pair of buffered events may arrive in either order. *)
  Definition Itot (_ _ : E) : Prop := True.

  Local Notation InvF := (Inv V valid).
  Local Notation ConsF := (Cons V f o).
  Local Notation NF := (N V f rho o).
  Local Notation aF := (applyF V f rho E reg gsig o).
  Local Notation rF := (runF V f rho E reg gsig o).
  Local Notation evF := (evstep V E reg gsig).
  Local Notation frF := (frun V f).

  Hypothesis HC : Common V src f valid rho E reg gsig o.
  (* Phase 1 reaches local validity (Def. "Iterated Compensation"; derived from component WFC in
     PART B, paper_rho_valid). *)
  Hypothesis HR : forall j x, valid j (rho j x).

  Lemma rho_idem : forall j x, rho j (rho j x) = rho j x.
  Proof. intros. apply (c_rho _ _ _ _ _ _ _ _ _ HC). apply HR. Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* lem:fed-termination, function level: ONE application of rho_Fed from ANY state is    *)
  (* federally valid (locally valid everywhere, every morphism invariant holds).          *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem single_round : forall t, InvF (NF t) /\ ConsF (NF t).
  Proof.
    intros t. assert (Hp : InvF (fun k => rho k (t k))) by (intro k; apply HR).
    assert (Hi : InvF (NF t)) by (unfold N; apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact Hp).
    split; [exact Hi |]. intros j Hj.
    assert (Hs : NF t j = f j (NF t) (rho j (t j))).
    { unfold N. exact (frun_solves _ _ _ _ _ _ _ _ _ HC o _ (c_topo _ _ _ _ _ _ _ _ _ HC) j Hj). }
    rewrite Hs at 2. rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC); [exact Hs | exact Hi | exact Hi | apply HR].
  Qed.

  (* Phase 2 keeps local validity at every intermediate stage (the invariant the paper's proof
     of lem:fed-termination states). *)
  Lemma phase2_invariant : forall l t, InvF (frF l (fun k => rho k (t k))).
  Proof. intros l t. apply (frun_inv _ _ _ _ _ _ _ _ _ HC). intro k. apply HR. Qed.

  Lemma N_idem : forall t, feq V (NF (NF t)) (NF t).
  Proof.
    intros t. destruct (single_round t) as [Hi Hc].
    apply (N_self _ _ _ _ _ _ _ _ _ HC); assumption.
  Qed.

  (* Applying gsm's Machine.Apply or the raw event makes no difference once rho_Fed runs. *)
  Definition rstep (e : E) (t : nat -> V) : nat -> V := upd V t (reg e) (ap e (t (reg e))).

  Lemma raw_ev : forall e t, feq V (NF (rstep e t)) (NF (evF e t)).
  Proof.
    intros e t. unfold N. apply (frun_ext _ _ _ _ _ _ _ _ _ HC). intro k.
    unfold rstep, evstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| reflexivity].
    apply Nat.eqb_eq in Ek. subst k. unfold gsig. rewrite rho_idem. reflexivity.
  Qed.

  Lemma runF_out : forall es t k, InvF t -> ~ In k o -> rF es t k = t k.
  Proof.
    induction es as [| e es IH]; intros t k Ht Hk; [reflexivity |].
    change (rF (e :: es) t) with (rF es (aF e t)).
    rewrite IH; [| apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Ht | exact Hk].
    unfold applyF, N. rewrite (frun_out V f o _ k Hk).
    rewrite (evstep_off V E reg gsig e t k).
    - apply (c_rho _ _ _ _ _ _ _ _ _ HC). apply Ht.
    - intro E'. apply Hk. rewrite E'. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* States as lists: Leibniz equality of federated states, so Governance.step applies.   *)
  (* ---------------------------------------------------------------------------------- *)

  Hypothesis Hrange : forall k, In k o <-> k < n.
  Hypothesis Hsrc : forall j k, In k (src j) -> k < n.
  Hypothesis Hout : forall k x, n <= k -> valid k x.

  Definition toF (l : list V) : nat -> V := fun k => nth k l d.
  Definition fromF (t : nat -> V) : list V := map t (seq 0 n).
  Definition feqn (t u : nat -> V) : Prop := forall k, k < n -> t k = u k.

  Lemma len_map : forall (A B : Type) (g : A -> B) l, length (map g l) = length l.
  Proof. intros A B g l. induction l as [| x l IH]; simpl; congruence. Qed.

  Lemma len_seq : forall m s, length (seq s m) = m.
  Proof. induction m as [| m IH]; intros s; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma fromF_length : forall t, length (fromF t) = n.
  Proof. intros t. unfold fromF. rewrite len_map, len_seq. reflexivity. Qed.

  Lemma nth_map_seq : forall m s k (t : nat -> V), k < m -> nth k (map t (seq s m)) d = t (s + k).
  Proof.
    induction m as [| m IH]; intros s k t Hk; [lia |].
    simpl. destruct k as [| k].
    - rewrite Nat.add_0_r. reflexivity.
    - rewrite (IH (S s) k t) by lia. f_equal. lia.
  Qed.

  Lemma toF_fromF : forall t k, k < n -> toF (fromF t) k = t k.
  Proof. intros t k Hk. unfold toF, fromF. rewrite nth_map_seq by exact Hk. reflexivity. Qed.

  Lemma len_snoc : forall (pre : list V) x, length (pre ++ [x]) = S (length pre).
  Proof. induction pre as [| y pre IH]; intros x; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma map_nth_pre : forall l pre,
    map (fun k => nth k (pre ++ l) d) (seq (length pre) (length l)) = l.
  Proof.
    induction l as [| x l IH]; intros pre; [reflexivity |].
    simpl. rewrite nth_middle. f_equal.
    rewrite <- (len_snoc pre x). replace (pre ++ x :: l) with ((pre ++ [x]) ++ l)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
  Qed.

  Lemma fromF_toF : forall l, length l = n -> fromF (toF l) = l.
  Proof.
    intros l Hl. unfold fromF, toF. rewrite <- Hl.
    exact (map_nth_pre l []).
  Qed.

  Lemma fromF_ext : forall t u, feqn t u -> fromF t = fromF u.
  Proof.
    intros t u H. unfold fromF. apply map_ext_in. intros k Hk.
    apply in_seq in Hk. apply H. lia.
  Qed.

  Lemma feq_feqn : forall t u, feq V t u -> feqn t u.
  Proof. intros t u H k _. apply H. Qed.

  Lemma feqn_trans : forall t u w, feqn t u -> feqn u w -> feqn t w.
  Proof. intros t u w H1 H2 k Hk. rewrite H1 by exact Hk. apply H2. exact Hk. Qed.

  Lemma feqn_sym : forall t u, feqn t u -> feqn u t.
  Proof. intros t u H k Hk. symmetry. apply H. exact Hk. Qed.

  Lemma toF_fromF_n : forall t, feqn (toF (fromF t)) t.
  Proof. intros t k Hk. apply toF_fromF. exact Hk. Qed.

  Lemma reg_lt : forall e, reg e < n.
  Proof. intros e. apply Hrange. apply (c_reg _ _ _ _ _ _ _ _ _ HC). Qed.

  Lemma f_extn : forall j t u x, feqn t u -> f j t x = f j u x.
  Proof.
    intros j t u x H. apply (c_local _ _ _ _ _ _ _ _ _ HC). intros k Hk. apply H.
    exact (Hsrc j k Hk).
  Qed.

  Lemma frun_extn : forall l t u, (forall a, In a l -> a < n) -> feqn t u -> feqn (frF l t) (frF l u).
  Proof.
    induction l as [| a l IH]; intros t u Hl H; [exact H |].
    change (frF (a :: l) t) with (frF l (fstep V f t a)).
    change (frF (a :: l) u) with (frF l (fstep V f u a)).
    apply IH; [intros b Hb; apply Hl; right; exact Hb |].
    intros k Hk. unfold fstep, upd. destruct (Nat.eqb k a) eqn:Ek; [| apply H; exact Hk].
    apply Nat.eqb_eq in Ek. subst k. rewrite (H a Hk). apply f_extn. exact H.
  Qed.

  Lemma N_extn : forall t u, feqn t u -> feqn (NF t) (NF u).
  Proof.
    intros t u H. unfold N. apply frun_extn; [intros a Ha; apply Hrange; exact Ha |].
    intros k Hk. rewrite (H k Hk). reflexivity.
  Qed.

  Lemma evstep_extn : forall e t u, feqn t u -> feqn (evF e t) (evF e u).
  Proof.
    intros e t u H k Hk. unfold evstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply H; exact Hk].
    apply Nat.eqb_eq in Ek. subst k. rewrite (H _ Hk). reflexivity.
  Qed.

  Lemma rstep_extn : forall e t u, feqn t u -> feqn (rstep e t) (rstep e u).
  Proof.
    intros e t u H k Hk. unfold rstep, upd. destruct (Nat.eqb k (reg e)) eqn:Ek; [| apply H; exact Hk].
    apply Nat.eqb_eq in Ek. subst k. rewrite (H _ Hk). reflexivity.
  Qed.

  Lemma applyF_extn : forall e t u, feqn t u -> feqn (aF e t) (aF e u).
  Proof. intros e t u H. unfold applyF. apply N_extn. apply evstep_extn. exact H. Qed.

  Lemma runF_extn : forall es t u, feqn t u -> feqn (rF es t) (rF es u).
  Proof.
    induction es as [| e es IH]; intros t u H; [exact H |].
    apply IH. apply applyF_extn. exact H.
  Qed.

  Lemma Inv_toF : forall l, (forall k, k < n -> valid k (nth k l d)) -> InvF (toF l).
  Proof.
    intros l H k. destruct (le_lt_dec n k) as [Hk | Hk]; [apply Hout; exact Hk | apply H; exact Hk].
  Qed.

  (* Federal validity of a list state: n registries, each locally valid, every morphism (or
     resolution) invariant satisfied. *)
  Definition gvalid (l : list V) : Prop := length l = n /\ InvF (toF l) /\ ConsF (toF l).

  Hypothesis vdec : forall k x, {valid k x} + {~ valid k x}.
  Hypothesis Veq : forall x y : V, {x = y} + {x <> y}.
  Hypothesis Eeq : forall x y : E, {x = y} + {x <> y}.

  Lemma all_dec : forall (P : nat -> Prop) (l : list nat), (forall x, {P x} + {~ P x}) ->
    {forall x, In x l -> P x} + {~ forall x, In x l -> P x}.
  Proof.
    intros P l Hd. induction l as [| a l IH]; [left; intros x [] |].
    destruct (Hd a) as [Ha | Ha]; [| right; intro H; apply Ha; apply H; left; reflexivity].
    destruct IH as [Hl | Hl]; [left | right].
    - intros x [<- | Hx]; [exact Ha | apply Hl; exact Hx].
    - intro H. apply Hl. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma gvalid_dec : forall l, {gvalid l} + {~ gvalid l}.
  Proof.
    intros l. destruct (Nat.eq_dec (length l) n) as [Hl | Hl]; [| right; intros [H _]; contradiction].
    destruct (all_dec (fun k => valid k (toF l k)) (seq 0 n) (fun k => vdec k (toF l k))) as [Hv | Hv].
    - destruct (all_dec (fun j => toF l j = f j (toF l) (toF l j)) o
                  (fun j => Veq (toF l j) (f j (toF l) (toF l j)))) as [Hc | Hc].
      + left. split; [exact Hl |]. split; [| exact Hc].
        apply Inv_toF. intros k Hk. apply (Hv k). apply in_seq. lia.
      + right. intros [_ [_ H]]. apply Hc. exact H.
    - right. intros [_ [H _]]. apply Hv. intros k _. apply H.
  Qed.

  (* The federated GRS (Def. "Governance Rewrite System" for R_Fed, Def. "Federated
     Normalization Operator"): apply steps run the raw event on its registry; the compensation
     step is rho_Fed. *)
  Definition gapply (e : E) (l : list V) : list V := fromF (rstep e (toF l)).
  Definition grho (l : list V) : list V := fromF (NF (toF l)).
  Definition gov (e : E) (l : list V) : list V := grho (gapply e l).
  Definition gPhi (l : list V) : nat := if gvalid_dec l then 0 else 1.

  Lemma Cons_toF_fromF : forall t, ConsF t -> ConsF (toF (fromF t)).
  Proof.
    intros t Hc j Hj. assert (Hn : j < n) by (apply Hrange; exact Hj).
    rewrite (toF_fromF t j Hn). rewrite (Hc j Hj) at 1. apply f_extn.
    apply feqn_sym. apply toF_fromF_n.
  Qed.

  Lemma Inv_toF_fromF : forall t, InvF t -> InvF (toF (fromF t)).
  Proof.
    intros t H. apply Inv_toF. intros k Hk. change (nth k (fromF t) d) with (toF (fromF t) k).
    rewrite (toF_fromF t k Hk). apply H.
  Qed.

  Lemma gvalid_fromF : forall t, InvF t -> ConsF t -> gvalid (fromF t).
  Proof.
    intros t Hi Hc. split; [apply fromF_length |].
    split; [apply Inv_toF_fromF; exact Hi | apply Cons_toF_fromF; exact Hc].
  Qed.

  (* lem:fed-termination, list level: one rho_Fed from ANY state is federally valid. *)
  Theorem grho_valid : forall l, gvalid (grho l).
  Proof. intros l. destruct (single_round (toF l)) as [Hi Hc]. apply gvalid_fromF; assumption. Qed.

  Lemma grho_id : forall l, gvalid l -> grho l = l.
  Proof.
    intros l [Hl [Hi Hc]]. unfold grho. rewrite <- (fromF_toF l Hl) at 2. apply fromF_ext.
    apply feq_feqn. apply (N_self _ _ _ _ _ _ _ _ _ HC); assumption.
  Qed.

  Lemma g_wfc : forall l, ~ gvalid l -> gPhi (grho l) < gPhi l.
  Proof.
    intros l H. unfold gPhi. destruct (gvalid_dec (grho l)) as [_ | H'];
      [| exfalso; apply H'; apply grho_valid].
    destruct (gvalid_dec l); [contradiction | lia].
  Qed.

  Section Enabled.
  Variable en : E -> list V -> list E -> Prop.
  Local Notation G := (step Eeq gapply grho gvalid en).

  Lemma g_reach : forall l B, star G (l, B) (grho l, B).
  Proof.
    intros l B. destruct (gvalid_dec l) as [Hv | Hv].
    - rewrite (grho_id l Hv). apply star_refl.
    - apply star_one. apply st_comp. exact Hv.
  Qed.

  Lemma g_nf : forall l, gvalid l -> normal_form G (l, []).
  Proof.
    intros l Hv [y H]. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst.
    - destruct Hin.
    - apply Hinv. exact Hv.
  Qed.

  Lemma g_gov_run : forall l B e, In e B -> en e l B -> star G (l, B) (gov e l, remove1 Eeq e B).
  Proof. intros. apply (apply_then_normalize Eeq gapply grho grho gvalid en g_reach); assumption. Qed.
  End Enabled.

  Definition lrun (es : list E) (l : list V) : list V := fold_left (fun s e => gov e s) es l.

  Lemma gov_len : forall e l, length (gov e l) = n.
  Proof. intros. apply fromF_length. Qed.

  Lemma gov_valid : forall e l, gvalid (gov e l).
  Proof. intros. apply grho_valid. Qed.

  Lemma lrun_valid : forall es l, gvalid l -> gvalid (lrun es l).
  Proof.
    induction es as [| e es IH]; intros l H; [exact H |]. apply IH. apply gov_valid.
  Qed.

  Lemma lrun_snoc : forall p e l, lrun (p ++ [e]) l = gov e (lrun p l).
  Proof. intros. unfold lrun. rewrite fold_left_app. reflexivity. Qed.

  (* The governed step of the GRS is FedMachine.Apply. *)
  Lemma gov_eq : forall e l, gov e l = fromF (aF e (toF l)).
  Proof.
    intros e l. unfold gov, grho, gapply. apply fromF_ext.
    eapply feqn_trans; [apply N_extn, toF_fromF_n |].
    apply feq_feqn. apply raw_ev.
  Qed.

  Lemma gov_two_eq : forall e1 e2 l, gov e2 (gov e1 l) = fromF (aF e2 (aF e1 (toF l))).
  Proof.
    intros e1 e2 l. rewrite (gov_eq e2), (gov_eq e1). apply fromF_ext. apply applyF_extn.
    apply toF_fromF_n.
  Qed.

  (* Corrected thm:fed-cc, machine form: under C1 and C2 the federated CC1 holds at every
     federally valid state, for every pair of events. *)
  Theorem grs_cc1_valid : C1 V f valid E reg gsig -> C2 V f valid E reg gsig Itot ->
    forall l, gvalid l -> forall e1 e2, gov e2 (gov e1 l) = gov e1 (gov e2 l).
  Proof.
    intros H1 H2 l [_ [Hi Hc]] e1 e2. rewrite !gov_two_eq. apply fromF_ext. apply feq_feqn.
    apply (fed_events_commute _ _ _ _ _ _ _ _ _ _ HC H1 H2); [exact Hi | exact Hc | right; exact I].
  Qed.

  Lemma lrun_eq : forall es l, length l = n -> lrun es l = fromF (rF es (toF l)).
  Proof.
    induction es as [| e es IH]; intros l Hl.
    - simpl. symmetry. apply fromF_toF. exact Hl.
    - change (lrun (e :: es) l) with (lrun es (gov e l)). rewrite IH by apply gov_len.
      change (rF (e :: es) (toF l)) with (rF es (aF e (toF l))). apply fromF_ext.
      apply runF_extn. rewrite gov_eq. apply toF_fromF_n.
  Qed.

  Lemma rm_perm : forall e B, In e B -> Permutation B (e :: remove1 Eeq e B).
  Proof.
    intros e B. induction B as [| x B IH]; intros Hin; [destruct Hin |].
    simpl. destruct (Eeq x e) as [-> | Hne]; [apply Permutation_refl |].
    destruct Hin as [-> | Hin]; [contradiction |].
    eapply Permutation_trans; [apply perm_skip; apply IH; exact Hin |]. apply perm_swap.
  Qed.

  Lemma perm_rm : forall e r B, Permutation B (e :: r) -> Permutation (remove1 Eeq e B) r.
  Proof.
    intros e r B H. assert (Hin : In e B) by (apply (Permutation_in e (Permutation_sym H)); left; reflexivity).
    apply (Permutation_cons_inv (a := e)). eapply Permutation_trans; [| exact H].
    apply Permutation_sym. apply rm_perm. exact Hin.
  Qed.

  (* Delivering a buffer in the order es, normalizing after each event. *)
  Lemma g_run_perm : forall (en : E -> list V -> list E -> Prop),
    (forall e l B, In e B -> gvalid l -> en e l B) ->
    forall es B l, gvalid l -> Permutation B es ->
      star (step Eeq gapply grho gvalid en) (l, B) (lrun es l, []).
  Proof.
    intros en Hen. induction es as [| e r IH]; intros B l Hl Hp.
    - apply Permutation_sym in Hp. apply Permutation_nil in Hp. subst. apply star_refl.
    - assert (Hin : In e B) by (apply (Permutation_in e (Permutation_sym Hp)); left; reflexivity).
      eapply star_trans; [apply (g_gov_run en); [exact Hin | apply Hen; assumption] |].
      apply IH; [apply gov_valid | apply perm_rm; exact Hp].
  Qed.

  (* Unique normal forms of a GRS forces FedMachine convergence for every permutation, hence
     C1 and C2 at the reachable witnesses (fed_exact). *)
  Lemma g_un_trace : forall (en : E -> list V -> list E -> Prop),
    (forall e l B, In e B -> gvalid l -> en e l B) ->
    forall s0, gvalid s0 -> (forall B, UN (step Eeq gapply grho gvalid en) (s0, B)) ->
      TraceConv V f rho E reg gsig Itot o (toF s0).
  Proof.
    intros en Hen s0 Hs0 Hun es1 es2 Ht k.
    pose proof (tequiv_perm _ _ _ Ht) as Hp.
    assert (Eq : lrun es1 s0 = lrun es2 s0).
    { assert (H := Hun es1 (lrun es1 s0, []) (lrun es2 s0, [])
                    (g_run_perm en Hen es1 es1 s0 Hs0 (Permutation_refl _))
                    (g_nf en _ (lrun_valid es1 s0 Hs0))
                    (g_run_perm en Hen es2 es1 s0 Hs0 Hp)
                    (g_nf en _ (lrun_valid es2 s0 Hs0))).
      injection H. auto. }
    destruct Hs0 as [Hl [Hi Hc]].
    rewrite !lrun_eq in Eq by exact Hl.
    destruct (le_lt_dec n k) as [Hk | Hk].
    - assert (Hno : ~ In k o) by (intro H; apply Hrange in H; lia).
      rewrite !runF_out by assumption. reflexivity.
    - rewrite <- (toF_fromF (rF es1 (toF s0)) k Hk), <- (toF_fromF (rF es2 (toF s0)) k Hk).
      rewrite Eq. reflexivity.
  Qed.

  Local Notation G := (step Eeq gapply grho gvalid free_enabled).

  (* ---------------------------------------------------------------------------------- *)
  (* Bridge 1: the federated GRS (free delivery) is an instance of Governance.step, and  *)
  (* cc_exact_from applies: unique normal forms from s0 iff CC1 and CC2 of the federated  *)
  (* system hold on the states reachable from s0.                                         *)
  (* ---------------------------------------------------------------------------------- *)

  Theorem fed_grs_exact : forall s0,
    (forall B, UN G (s0, B)) <->
    ((forall sigma e1 e2, reach gapply grho gvalid s0 sigma ->
        gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma)) /\
     (forall sigma e, reach gapply grho gvalid s0 sigma -> ~ gvalid sigma ->
        gov e sigma = gov e (grho sigma))).
  Proof.
    intros s0.
    exact (cc_exact_from Eeq gapply grho grho gvalid gPhi g_wfc (g_reach free_enabled) grho_valid s0).
  Qed.

  (* Bridge 2: unique normal forms of the GRS imply C1 and C2 at the reachable witnesses of the
     FedMachine model (fed_exact). *)
  Theorem fed_grs_un_c1_c2 : forall s0, gvalid s0 ->
    (forall B, UN G (s0, B)) ->
    C1R1 V f rho E reg gsig o (toF s0) /\ C2R V f rho E reg gsig Itot o (toF s0).
  Proof.
    intros s0 Hs0 Hun.
    assert (Ht : TraceConv V f rho E reg gsig Itot o (toF s0))
      by (apply (g_un_trace free_enabled); [intros e l B Hin _; exact Hin | exact Hs0 | exact Hun]).
    destruct Hs0 as [_ [Hi Hc]].
    exact (proj1 (fed_exact _ _ _ _ _ _ _ _ Itot _ HC (toF s0) Hi Hc) Ht).
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Bridge 3 (corrected thm:fed-cc and thm:fed-convergence, unrestricted GRS): XU, the   *)
  (* component CC (LocalCC on every same-registry pair, and CC2 iterated to rho star) give *)
  (* CC1 and CC2 of the federated system at EVERY state; Governance.v's Convergence       *)
  (* Theorem then gives unique normal forms.                                              *)
  (* ---------------------------------------------------------------------------------- *)

  Section Unguarded.
  Hypothesis HX : XU V f valid E reg gsig.
  Hypothesis HL : LocalCC V valid E reg gsig Itot.
  Hypothesis HCC2 : forall e x, rho (reg e) (ap e (rho (reg e) x)) = rho (reg e) (ap e x).

  Lemma flush_raw : forall e t, feq V (NF (rstep e t)) (aF e (NF t)).
  Proof.
    intros e t. pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as To.
    set (P0 := fun k => rho k (t k)). set (W := NF t).
    set (P1 := fun k => rho k (rstep e t k)).
    assert (IW : InvF W) by (apply single_round).
    assert (I1 : InvF (frF o P1)) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); intro k; apply HR).
    assert (IE : InvF (evF e W)) by (apply (evstep_inv _ _ _ _ _ _ _ _ _ HC); exact IW).
    change (NF (rstep e t)) with (frF o P1).
    unfold applyF. eapply feq_trans; [| apply feq_sym, (N_frun _ _ _ _ _ _ _ _ _ HC); exact IE].
    assert (SW : forall j, In j o -> W j = f j W (P0 j))
      by (intros j Hj; exact (frun_solves _ _ _ _ _ _ _ _ _ HC o P0 To j Hj)).
    apply (solve_unique _ _ _ _ _ _ _ _ _ HC o _ _ P1 (evF e W) To).
    - intros k Hk. rewrite !(frun_out V f o _ k Hk).
      assert (Ne : k <> reg e) by (intro E'; apply Hk; rewrite E'; apply (c_reg _ _ _ _ _ _ _ _ _ HC)).
      unfold P1, rstep. rewrite (upd_neq V t _ _ k Ne). rewrite (evstep_off V E reg gsig e W k Ne).
      unfold W, N. rewrite (frun_out V f o _ k Hk). reflexivity.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros. apply (frun_solves _ _ _ _ _ _ _ _ _ HC); assumption.
    - intros j Hj. destruct (Nat.eq_dec j (reg e)) as [J | J].
      + subst j. unfold P1, rstep. rewrite upd_eq. rewrite (evstep_at V E reg gsig e W (reg e) eq_refl).
        rewrite (SW (reg e) Hj). rewrite <- HCC2. change (rho (reg e) (ap e (rho (reg e) (t (reg e)))))
          with (gsig e (P0 (reg e))).
        symmetry. apply (xu_strong _ _ _ _ _ _ _ _ _ HC HX); [exact I1 | exact IW | apply HR].
      + unfold P1, rstep. rewrite (upd_neq V t _ _ j J). rewrite (evstep_off V E reg gsig e W j J).
        rewrite (SW j Hj). symmetry. apply (c_absorb _ _ _ _ _ _ _ _ _ HC); [exact I1 | exact IW | apply HR].
  Qed.

  Lemma gov_flush : forall e l, gov e l = fromF (aF e (NF (toF l))).
  Proof.
    intros e l. unfold gov, grho, gapply. apply fromF_ext.
    eapply feqn_trans; [apply N_extn, toF_fromF_n |]. apply feq_feqn. apply flush_raw.
  Qed.

  Lemma toF_grho : forall l, feqn (toF (grho l)) (NF (toF l)).
  Proof. intros l. apply toF_fromF_n. Qed.

  Lemma gov_after : forall e t, InvF t -> ConsF t -> feqn (NF (toF (fromF (aF e t)))) (aF e t).
  Proof.
    intros e t Hi Hc. eapply feqn_trans; [apply N_extn, toF_fromF_n |].
    apply feq_feqn. apply (N_self _ _ _ _ _ _ _ _ _ HC);
      [apply (applyF_inv _ _ _ _ _ _ _ _ _ HC) | apply (applyF_cons _ _ _ _ _ _ _ _ _ HC)]; exact Hi.
  Qed.

  Lemma gov_two : forall e1 e2 l, gov e2 (gov e1 l) = fromF (aF e2 (aF e1 (NF (toF l)))).
  Proof.
    intros e1 e2 l. rewrite (gov_flush e2). rewrite (gov_flush e1). apply fromF_ext.
    apply applyF_extn. destruct (single_round (toF l)) as [Hi Hc]. apply gov_after; assumption.
  Qed.

  Theorem grs_cc1 : forall sigma e1 e2, gov e2 (gov e1 sigma) = gov e1 (gov e2 sigma).
  Proof.
    intros sigma e1 e2. rewrite !gov_two. apply fromF_ext. apply feq_feqn.
    destruct (xu_implies_c1_c2 _ _ _ _ _ _ _ _ Itot _ HC HX HL) as [H1 H2].
    destruct (single_round (toF sigma)) as [Hi Hc].
    apply (fed_events_commute _ _ _ _ _ _ _ _ _ _ HC H1 H2); [exact Hi | exact Hc | right; exact I].
  Qed.

  Theorem grs_cc2 : forall sigma e, gov e sigma = gov e (grho sigma).
  Proof.
    intros sigma e. rewrite !gov_flush. apply fromF_ext. apply applyF_extn.
    eapply feqn_trans; [| apply feqn_sym, N_extn, toF_grho].
    apply feqn_sym. apply feq_feqn. apply N_idem.
  Qed.

  Lemma free_after_remove : forall (sigma : list V) B e1 e2,
    free_enabled e1 sigma B -> free_enabled e2 sigma B -> e1 <> e2 ->
    In e2 (remove1 Eeq e1 B) /\ free_enabled e2 (grho (gapply e1 sigma)) (remove1 Eeq e1 B).
  Proof.
    intros sigma B e1 e2 _ H2 Hne. unfold free_enabled.
    assert (Hi : In e2 (remove1 Eeq e1 B)) by (apply in_rm; [exact H2 | intro E'; apply Hne; symmetry; exact E']).
    split; exact Hi.
  Qed.

  Theorem grs_unique_nf : forall c n1 n2,
    star G c n1 -> normal_form G n1 -> star G c n2 -> normal_form G n2 -> n1 = n2.
  Proof.
    apply (governance_unique_normal_forms Eeq gapply grho grho gvalid gPhi free_enabled g_wfc
             (g_reach free_enabled) grs_cc1 (fun s e _ => grs_cc2 s e) free_after_remove (fun _ _ _ H => H)).
  Qed.
  End Unguarded.

  (* Every configuration reaches a federally valid normal form. *)
  Theorem grs_nf_exists : forall l B, exists m, star G (l, B) (m, []) /\ normal_form G (m, []) /\ gvalid m.
  Proof.
    intros l B. exists (lrun B (grho l)). split; [| split].
    - eapply star_trans; [apply g_reach |].
      apply (g_run_perm free_enabled (fun e _ _ H _ => H)); [apply grho_valid | apply Permutation_refl].
    - apply g_nf. apply lrun_valid. apply grho_valid.
    - apply lrun_valid. apply grho_valid.
  Qed.

  (* ---------------------------------------------------------------------------------- *)
  (* Bridge 4: the GUARDED federated GRS (an event is applied only at a federally valid    *)
  (* state; compensation first; FedMachine.Apply semantics). Unique normal forms iff C1    *)
  (* and C2 hold at the reachable witnesses.                                              *)
  (* ---------------------------------------------------------------------------------- *)

  Definition genab (e : E) (l : list V) (B : list E) : Prop := In e B /\ gvalid l.
  Local Notation Gg := (step Eeq gapply grho gvalid genab).

  Lemma genab_comp : forall l B e, genab e l B -> genab e (grho l) B.
  Proof. intros l B e [H _]. split; [exact H | apply grho_valid]. Qed.

  Lemma guarded_form : forall s0 B c, gvalid s0 -> star Gg (s0, B) c ->
    exists p, fst c = lrun p s0 \/ exists e, fst c = gapply e (lrun p s0).
  Proof.
    intros s0 B c Hs0 S.
    apply (star_closed Gg (fun c => exists p, fst c = lrun p s0 \/ exists e, fst c = gapply e (lrun p s0)))
      with (x := (s0, B)); [| exists []; left; reflexivity | exact S].
    intros x y [p Hp] Hst. destruct Hst as [s B' e Hin [_ Hv] | s B' Hinv]; simpl in *.
    - destruct Hp as [-> | [e' ->]].
      + exists p. right. exists e. reflexivity.
      + exists (p ++ [e']). right. exists e. rewrite lrun_snoc. unfold gov.
        rewrite (grho_id _ Hv). reflexivity.
    - destruct Hp as [-> | [e' ->]].
      + exfalso. apply Hinv. apply lrun_valid. exact Hs0.
      + exists (p ++ [e']). left. rewrite lrun_snoc. reflexivity.
  Qed.

  Lemma guarded_valid_form : forall s0 B s B', gvalid s0 -> star Gg (s0, B) (s, B') -> gvalid s ->
    exists p, s = lrun p s0.
  Proof.
    intros s0 B s B' Hs0 S Hv. destruct (guarded_form s0 B _ Hs0 S) as [p [Hp | [e Hp]]]; simpl in Hp.
    - exists p. exact Hp.
    - exists (p ++ [e]). rewrite lrun_snoc. unfold gov. rewrite <- Hp. symmetry. apply grho_id. exact Hv.
  Qed.

  Lemma guarded_jc : forall s0, gvalid s0 ->
    (forall p e1 e2, gov e2 (gov e1 (lrun p s0)) = gov e1 (gov e2 (lrun p s0))) ->
    forall B, JC Eeq gapply grho grho gvalid genab (s0, B).
  Proof.
    intros s0 Hs0 Hcomm B sigma B' Hr. split.
    - intros e1 e2 Hin1 Hin2 [_ Hv] [_ _] Hne.
      destruct (guarded_valid_form s0 B sigma B' Hs0 Hr Hv) as [p ->].
      exists (gov e2 (gov e1 (lrun p s0)), remove1 Eeq e2 (remove1 Eeq e1 B')). split.
      + apply (g_gov_run genab); [apply in_rm; [exact Hin2 | intro E'; apply Hne; symmetry; exact E'] |].
        split; [apply in_rm; [exact Hin2 | intro E'; apply Hne; symmetry; exact E'] | apply gov_valid].
      + rewrite Hcomm, remove1_comm.
        apply (g_gov_run genab); [apply in_rm; [exact Hin1 | exact Hne] |].
        split; [apply in_rm; [exact Hin1 | exact Hne] | apply gov_valid].
    - intros e Hinv _ [_ Hv]. contradiction.
  Qed.

  Theorem fed_guarded_exact : forall s0, gvalid s0 ->
    ((forall B, UN Gg (s0, B)) <->
     C1R1 V f rho E reg gsig o (toF s0) /\ C2R V f rho E reg gsig Itot o (toF s0)).
  Proof.
    intros s0 Hs0. pose proof Hs0 as [Hl [Hi Hc]].
    rewrite <- (fed_exact _ _ _ _ _ _ _ _ Itot _ HC (toF s0) Hi Hc). split.
    - apply (g_un_trace genab); [intros e l B Hin Hv; split; assumption | exact Hs0].
    - intros Ht B. apply (jc_unique_normal_forms Eeq gapply grho grho gvalid gPhi genab g_wfc
                           (g_reach genab) genab_comp).
      apply (guarded_jc s0 Hs0). intros p e1 e2.
      rewrite <- !lrun_snoc. rewrite <- !app_assoc. simpl.
      rewrite !lrun_eq by exact Hl. apply fromF_ext. apply feq_feqn. apply Ht.
      apply (teq_swap (Ifed E reg Itot) p e1 e2 []). right. exact I.
  Qed.

  (* Corrected thm:fed-convergence for the guarded GRS: static C1 and C2 suffice. *)
  Theorem fed_guarded_c1_c2 :
    C1 V f valid E reg gsig -> C2 V f valid E reg gsig Itot ->
    forall s0, gvalid s0 -> forall B, UN Gg (s0, B).
  Proof.
    intros H1 H2 s0 Hs0. apply (proj2 (fed_guarded_exact s0 Hs0)).
    destruct Hs0 as [_ [Hi Hc]].
    destruct (static_c1_c2_gc _ _ _ _ _ _ _ _ _ _ HC H1 H2 (toF s0) Hi Hc) as [_ H]. exact H.
  Qed.
  (* ---------------------------------------------------------------------------------- *)
  (* lem:authority (a): a source registry's component in ANY normal form of the GRS is a  *)
  (* normal form of that source's own single-registry GRS on its own events.              *)
  (* ---------------------------------------------------------------------------------- *)

  Section Source.
  Variable i : nat.
  Hypothesis Hio : In i o.
  Hypothesis Hid : forall z x, f i z x = x.       (* no incoming morphism *)
  Variable c : V -> V.                           (* the source's one-step compensation rho_R *)

  (* The single-registry GRS of R_i: events of other registries do not act on R_i. *)
  Definition capp (e : E) (x : V) : V := if Nat.eqb (reg e) i then ap e x else x.
  Definition filt (B : list E) : list E := filter (fun e => Nat.eqb (reg e) i) B.
  Local Notation CG := (step Eeq capp c (valid i) free_enabled).

  Hypothesis Hcomp : forall x F, star CG (x, F) (rho i x, F).

  Lemma filt_rm : forall e B,
    filt (remove1 Eeq e B) = if Nat.eqb (reg e) i then remove1 Eeq e (filt B) else filt B.
  Proof.
    intros e B. induction B as [| x B IH].
    - simpl. destruct (Nat.eqb (reg e) i); reflexivity.
    - simpl. destruct (Eeq x e) as [-> | Hne].
      + unfold filt at 2. simpl. destruct (Nat.eqb (reg e) i) eqn:Hr; [| reflexivity].
        simpl. destruct (Eeq e e) as [_ | N']; [reflexivity | contradiction].
      + unfold filt at 1. simpl. fold (filt (remove1 Eeq e B)). rewrite IH.
        unfold filt at 3. simpl. fold (filt B).
        destruct (Nat.eqb (reg x) i) eqn:Hx; destruct (Nat.eqb (reg e) i) eqn:He; try reflexivity.
        simpl. destruct (Eeq x e) as [E' | _]; [contradiction | reflexivity].
  Qed.

  Lemma src_at_grho : forall l, nth i (grho l) d = rho i (nth i l d).
  Proof.
    intros l. assert (Hn : i < n) by (apply Hrange; exact Hio).
    change (nth i (grho l) d) with (toF (fromF (NF (toF l))) i). rewrite (toF_fromF _ i Hn).
    unfold N. rewrite (frun_solves _ _ _ _ _ _ _ _ _ HC o _ (c_topo _ _ _ _ _ _ _ _ _ HC) i Hio).
    rewrite Hid. reflexivity.
  Qed.

  Lemma proj_step : forall l B l' B', step Eeq gapply grho gvalid free_enabled (l, B) (l', B') ->
    star CG (nth i l d, filt B) (nth i l' d, filt B').
  Proof.
    intros l B l' B' H. assert (Hn : i < n) by (apply Hrange; exact Hio).
    inversion H as [s B0 e Hin Hen E1 E2 | s B0 Hinv E1 E2]; subst.
    - change (nth i (gapply e l) d) with (toF (fromF (rstep e (toF l))) i).
      rewrite (toF_fromF _ i Hn). rewrite filt_rm. unfold rstep, upd.
      destruct (Nat.eqb (reg e) i) eqn:Hr.
      + apply Nat.eqb_eq in Hr. rewrite <- Hr. rewrite Nat.eqb_refl. rewrite Hr.
        apply star_one.
        assert (Hc : capp e (toF l i) = ap e (toF l i))
          by (unfold capp; rewrite Hr, Nat.eqb_refl; reflexivity).
        rewrite <- Hc. apply st_apply; unfold free_enabled; apply filter_In;
          (split; [exact Hin | rewrite Hr; apply Nat.eqb_refl]).
      + assert (Hne : Nat.eqb i (reg e) = false) by (rewrite Nat.eqb_sym; exact Hr).
        rewrite Hne. apply star_refl.
    - rewrite src_at_grho. apply Hcomp.
  Qed.

  Theorem source_projection : forall c1 c2, star (step Eeq gapply grho gvalid free_enabled) c1 c2 ->
    star CG (nth i (fst c1) d, filt (snd c1)) (nth i (fst c2) d, filt (snd c2)).
  Proof.
    intros c1 c2 S. induction S as [x | x y z Hxy _ IH]; [apply star_refl |].
    eapply star_trans; [| exact IH]. destruct x as [l B], y as [l' B']. apply proj_step. exact Hxy.
  Qed.

  Theorem fed_authority_a_gen : forall s0 B nf,
    star (step Eeq gapply grho gvalid free_enabled) (s0, B) (nf, []) -> gvalid nf ->
    star CG (nth i s0 d, filt B) (nth i nf d, []) /\ normal_form CG (nth i nf d, []).
  Proof.
    intros s0 B nf S Hv. split; [exact (source_projection _ _ S) |].
    intros [y Hy]. inversion Hy as [s B0 e Hin _ E1 E2 | s B0 Hinv E1 E2]; subst.
    - destruct Hin.
    - apply Hinv. destruct Hv as [_ [Hi _]]. apply Hi.
  Qed.
  End Source.
End GRS.

(* ========================================================================================= *)
(* cor:fed-nf and cor:resolved-nf, corrected: the constructive normal form of the FedMachine  *)
(* model. Registries are finalized in topological order; a registry's events are applied     *)
(* with the repair against its FINALIZED sources interleaved after each event.               *)
(* ========================================================================================= *)

Section Constructive.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable o : list nat.

  Local Notation InvF := (Inv V valid).
  Local Notation ConsF := (Cons V f o).
  Local Notation aF := (applyF V f rho E reg sig o).
  Local Notation rF := (runF V f rho E reg sig o).

  Hypothesis HC : Common V src f valid rho E reg sig o.

  Definition filt_on (j : nat) (es : list E) : list E := filter (fun e => Nat.eqb (reg e) j) es.
  Definition grp (es : list E) : list E := flat_map (fun j => filt_on j es) o.
  Definition cstep (j : nat) (Z : nat -> V) (x : V) (e : E) : V := f j Z (sig e x).

  (* The constructive value of registry j, given the final federated state Z (only Z's values
     on the sources of j are read) and the start state s. *)
  Definition Gc (s : nat -> V) (es : list E) (j : nat) (Z : nat -> V) : V :=
    f j Z (fold_left (cstep j Z) (filt_on j es) (f j Z (s j))).

  Lemma topo_nodup : forall l, topoF src l -> NoDup l.
  Proof.
    induction l as [| a l IH]; intros H; [constructor |].
    destruct H as [Ha [_ Hr]]. constructor; [exact Ha | apply IH; exact Hr].
  Qed.

  Lemma perm_partition : forall (p : E -> bool) es,
    Permutation es (filter p es ++ filter (fun e => negb (p e)) es).
  Proof.
    intros p es. induction es as [| x es IH]; [apply Permutation_refl |].
    simpl. destruct (p x); simpl.
    - apply perm_skip. exact IH.
    - apply Permutation_cons_app. exact IH.
  Qed.

  Lemma filt_neg : forall k j es, k <> j ->
    filt_on k (filter (fun e => negb (Nat.eqb (reg e) j)) es) = filt_on k es.
  Proof.
    intros k j es Hkj. induction es as [| x es IH]; [reflexivity |].
    unfold filt_on in *. simpl.
    destruct (Nat.eqb (reg x) j) eqn:Hj; destruct (Nat.eqb (reg x) k) eqn:Hk; simpl;
      try rewrite Hk; try rewrite IH; try reflexivity.
    apply Nat.eqb_eq in Hj. apply Nat.eqb_eq in Hk. exfalso. apply Hkj. congruence.
  Qed.

  Lemma flat_map_ext_in : forall (g h : nat -> list E) l,
    (forall x, In x l -> g x = h x) -> flat_map g l = flat_map h l.
  Proof.
    intros g h l H. induction l as [| x l IH]; [reflexivity |]. simpl.
    rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity |]. intros y Hy. apply H. right. exact Hy.
  Qed.

  Lemma flat_map_app' : forall (g : nat -> list E) l1 l2,
    flat_map g (l1 ++ l2) = flat_map g l1 ++ flat_map g l2.
  Proof.
    intros g l1 l2. induction l1 as [| x l1 IH]; [reflexivity |]. simpl. rewrite IH.
    apply app_assoc.
  Qed.

  Lemma perm_grp_gen : forall l es, NoDup l -> Forall (fun e => In (reg e) l) es ->
    Permutation es (flat_map (fun j => filt_on j es) l).
  Proof.
    induction l as [| j l IH]; intros es Hnd Hes.
    - destruct es as [| e es]; [apply Permutation_refl |]. inversion Hes as [| ? ? H _]. destruct H.
    - inversion Hnd as [| ? ? Hj Hnd']; subst. simpl.
      eapply Permutation_trans; [apply (perm_partition (fun e => Nat.eqb (reg e) j)) |].
      apply Permutation_app_head.
      set (es' := filter (fun e => negb (Nat.eqb (reg e) j)) es).
      assert (Hes' : Forall (fun e => In (reg e) l) es').
      { apply Forall_forall. intros e He. unfold es' in He. apply filter_In in He as [He Hn].
        rewrite Forall_forall in Hes. destruct (Hes e He) as [E' | H']; [| exact H'].
        rewrite E', Nat.eqb_refl in Hn. discriminate. }
      eapply Permutation_trans; [apply (IH es' Hnd' Hes') |].
      rewrite (flat_map_ext_in (fun k => filt_on k es') (fun k => filt_on k es));
        [apply Permutation_refl |].
      intros k Hk. apply filt_neg. intro E'. subst. contradiction.
  Qed.

  Lemma perm_grp : forall es, Permutation es (grp es).
  Proof.
    intros es. apply perm_grp_gen; [apply topo_nodup, (c_topo _ _ _ _ _ _ _ _ _ HC) |].
    apply Forall_forall. intros e _. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Lemma runF_off : forall es t k, InvF t -> ~ In k o -> rF es t k = t k.
  Proof.
    induction es as [| e es IH]; intros t k Ht Hk; [reflexivity |].
    change (rF (e :: es) t) with (rF es (aF e t)).
    rewrite IH; [| apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Ht | exact Hk].
    unfold applyF, N. rewrite (frun_out V f o _ k Hk).
    rewrite (evstep_off V E reg sig e t k).
    - apply (c_rho _ _ _ _ _ _ _ _ _ HC). apply Ht.
    - intro E'. apply Hk. rewrite E'. apply (c_reg _ _ _ _ _ _ _ _ _ HC).
  Qed.

  (* A run of events on registries in a suffix L of o leaves everything outside L alone. *)
  Lemma run_upL_on : forall o1 L w t, o = o1 ++ L -> Forall (fun e => In (reg e) L) w ->
    InvF t -> ConsF t -> upL V L (rF w t) t.
  Proof.
    intros o1 L w. induction w as [| e w IH]; intros t Ho Hw Hi Hc; [intros k _; reflexivity |].
    inversion Hw as [| ? ? He Hw'].
    change (rF (e :: w) t) with (rF w (aF e t)).
    eapply upL_trans; [apply IH; [exact Ho | exact Hw' | apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi
                                  | apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hi] |].
    apply (applyF_upL_self _ _ _ _ _ _ _ _ _ HC o1); assumption.
  Qed.

  Lemma fold_ext : forall (g h : V -> E -> V) w x, (forall y e, g y e = h y e) ->
    fold_left g w x = fold_left h w x.
  Proof.
    intros g h w. induction w as [| e w IH]; intros x H; [reflexivity |]. simpl.
    rewrite (H x e). apply IH. exact H.
  Qed.

  (* Events of registry j, run from a consistent state whose sources of j are already final. *)
  Lemma block : forall j Z w t, In j o -> Forall (fun e => reg e = j) w -> InvF t -> ConsF t ->
    (forall k, In k (src j) -> t k = Z k) -> rF w t j = fold_left (cstep j Z) w (t j).
  Proof.
    intros j Z w. induction w as [| e w IH]; intros t Hj Hw Hi Hc Ht; [reflexivity |].
    inversion Hw as [| ? ? He Hw']; subst j.
    change (rF (e :: w) t) with (rF w (aF e t)).
    destruct (split_at _ _ _ _ _ _ _ _ _ HC (reg e) Hj) as [o1 [L [Ho [HjL Hs]]]].
    assert (U : upL V L (aF e t) t) by (apply (applyF_upL_self _ _ _ _ _ _ _ _ _ HC o1); assumption).
    rewrite IH; [| exact Hj | exact Hw' | apply (applyF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi
                | apply (applyF_cons _ _ _ _ _ _ _ _ _ HC); exact Hi
                | intros k Hk; rewrite (U k (Hs k Hk)); apply Ht; exact Hk].
    simpl. f_equal. rewrite (at_ev _ _ _ _ _ _ _ _ _ HC e t Hi Hc). unfold cstep.
    apply (c_local _ _ _ _ _ _ _ _ _ HC). exact Ht.
  Qed.

  Lemma Gc_local : forall s es j Z1 Z2, (forall k, In k (src j) -> Z1 k = Z2 k) ->
    Gc s es j Z1 = Gc s es j Z2.
  Proof.
    intros s es j Z1 Z2 H. unfold Gc.
    assert (Hf : forall x, f j Z1 x = f j Z2 x) by (intro; apply (c_local _ _ _ _ _ _ _ _ _ HC); exact H).
    rewrite !Hf. f_equal. apply fold_ext. intros y e. unfold cstep. apply Hf.
  Qed.

  (* The grouped run satisfies the constructive equations (no C1/C2 needed for this order). *)
  Lemma grp_equations : forall es s, InvF s -> ConsF s ->
    forall j, In j o -> rF (grp es) s j = Gc s es j (rF (grp es) s).
  Proof.
    intros es s Hi Hc j Hj. pose proof (c_topo _ _ _ _ _ _ _ _ _ HC) as T.
    destruct (in_split j o Hj) as [o1 [o2 Ho]].
    pose proof T as T'. rewrite Ho in T'. destruct (topoF_app src o1 (j :: o2) T') as [[Hj2 [Hs _]] Hpre].
    assert (Hj1 : ~ In j o1) by (intro H; apply (proj1 (Hpre j H)); left; reflexivity).
    set (P := flat_map (fun k => filt_on k es) o1). set (B := filt_on j es).
    set (Q := flat_map (fun k => filt_on k es) o2).
    assert (Hg : grp es = P ++ B ++ Q).
    { unfold grp. rewrite Ho at 1. rewrite flat_map_app'. reflexivity. }
    rewrite Hg. rewrite !(runF_app V f rho E reg sig o).
    set (A := rF P s). set (C := rF B A). set (Z := rF Q C).
    assert (IA : InvF A) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi).
    assert (CA : ConsF A) by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
    assert (IC : InvF C) by (apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact IA).
    assert (CC : ConsF C) by (apply (runF_cons _ _ _ _ _ _ _ _ _ HC); assumption).
    assert (FP : Forall (fun e => reg e <> j) P).
    { apply Forall_forall. intros e He. unfold P in He. apply in_flat_map in He as [k [Hk He]].
      unfold filt_on in He. apply filter_In in He as [_ He]. apply Nat.eqb_eq in He. subst k.
      intro E'. rewrite E' in Hk. contradiction. }
    assert (FB : Forall (fun e => reg e = j) B).
    { apply Forall_forall. intros e He. unfold B, filt_on in He. apply filter_In in He as [_ He].
      apply Nat.eqb_eq. exact He. }
    assert (FQ : Forall (fun e => reg e <> j /\ In (reg e) (j :: o2)) Q).
    { apply Forall_forall. intros e He. unfold Q in He. apply in_flat_map in He as [k [Hk He]].
      unfold filt_on in He. apply filter_In in He as [_ He]. apply Nat.eqb_eq in He. subst k.
      split; [intro E'; rewrite E' in Hk; contradiction | right; exact Hk]. }
    assert (UQ : upL V (j :: o2) Z C).
    { apply (run_upL_on o1); [exact Ho | | exact IC | exact CC].
      eapply Forall_impl; [| exact FQ]. intros e [_ H]. exact H. }
    assert (UB : upL V (j :: o2) C A).
    { apply (run_upL_on o1); [exact Ho | | exact IA | exact CA].
      eapply Forall_impl; [| exact FB]. intros e H. rewrite H. left. reflexivity. }
    assert (AZ : forall k, In k (src j) -> A k = Z k).
    { intros k Hk. symmetry. rewrite (UQ k (Hs k Hk)). apply UB. apply Hs. exact Hk. }
    assert (Z1 : Z j = f j Z (C j)).
    { apply (run_off _ _ _ _ _ _ _ _ _ HC); [exact IC | exact CC | exact Hj |].
      eapply Forall_impl; [| exact FQ]. intros e [H _]. exact H. }
    assert (C1' : C j = fold_left (cstep j Z) B (A j)) by (apply block; assumption).
    assert (A1 : A j = f j A (s j)) by (apply (run_off _ _ _ _ _ _ _ _ _ HC); assumption).
    rewrite Z1, C1', A1. unfold Gc. f_equal. f_equal.
    apply (c_local _ _ _ _ _ _ _ _ _ HC). exact AZ.
  Qed.

  (* Unique solvability of local equations along the topological order. *)
  Lemma topo_unique : forall (G : nat -> (nat -> V) -> V) l, topoF src l ->
    (forall j Z1 Z2, (forall k, In k (src j) -> Z1 k = Z2 k) -> G j Z1 = G j Z2) ->
    forall Y1 Y2, (forall k, ~ In k l -> Y1 k = Y2 k) ->
      (forall j, In j l -> Y1 j = G j Y1) -> (forall j, In j l -> Y2 j = G j Y2) -> feq V Y1 Y2.
  Proof.
    intros G l. induction l as [| a l IH]; intros Ht Hloc Y1 Y2 Hout H1 H2.
    - intro k. apply Hout. intros [].
    - destruct Ht as [Ha [Hs Hr]].
      assert (Ea : Y1 a = Y2 a).
      { rewrite (H1 a (or_introl eq_refl)), (H2 a (or_introl eq_refl)). apply Hloc.
        intros k Hk. apply Hout. apply Hs. exact Hk. }
      apply (IH Hr Hloc).
      + intros k Hk. destruct (Nat.eq_dec k a) as [-> | Hne]; [exact Ea |].
        apply Hout. intros [E' | E']; [congruence | contradiction].
      + intros j Hj. apply H1. right. exact Hj.
      + intros j Hj. apply H2. right. exact Hj.
  Qed.

  (* Headline (cor:fed-nf / cor:resolved-nf, corrected). Under C1 and C2 (every same-registry
     pair independent), for every event sequence es from a valid consistent s, the federated
     normal form Z = runF es s is the unique solution of
       Z k = s k                                          (k not a registry)
       Z j = f j Z (fold (x, e) |-> f j Z (sig e x) over j's events in es, from f j Z (s j))
     computed registry by registry in topological order: sources first, each target from its
     finalized sources, the repair against them interleaved after EACH event of the target. *)
  Theorem fed_nf_constructive :
    C1 V f valid E reg sig -> C2 V f valid E reg sig (fun _ _ => True) ->
    forall es s, InvF s -> ConsF s ->
      (forall k, ~ In k o -> rF es s k = s k) /\
      (forall j, In j o -> rF es s j = Gc s es j (rF es s)) /\
      (forall Y, (forall k, ~ In k o -> Y k = s k) -> (forall j, In j o -> Y j = Gc s es j Y) ->
         feq V Y (rF es s)).
  Proof.
    intros H1 H2 es s Hi Hc.
    assert (Hp : feq V (rF es s) (rF (grp es) s)).
    { apply (fed_permutations_converge _ _ _ _ _ _ _ _ (fun _ _ => True) _ HC H1 H2);
        [intros; exact I | apply perm_grp | exact Hi | exact Hc]. }
    assert (Heq : forall j, In j o -> rF es s j = Gc s es j (rF es s)).
    { intros j Hj. rewrite (Hp j). rewrite (grp_equations es s Hi Hc j Hj).
      apply Gc_local. intros k _. symmetry. apply Hp. }
    assert (Hoff : forall k, ~ In k o -> rF es s k = s k) by (intros; apply runF_off; assumption).
    split; [exact Hoff |]. split; [exact Heq |].
    intros Y HY1 HY2. apply (topo_unique (Gc s es) o (c_topo _ _ _ _ _ _ _ _ _ HC)).
    - intros j Z1 Z2 H. apply Gc_local. exact H.
    - intros k Hk. rewrite HY1, Hoff by exact Hk. reflexivity.
    - exact HY2.
    - exact Heq.
  Qed.

  (* Under XU the paper's own recipe is right: a registry's component is its single-registry run
     on its own events from its start state, with the shared component then overwritten from its
     finalized sources (for a source, f = identity: exactly its single-registry run). *)
  Lemma recipe_xu : forall j Z w y, XU V f valid E reg sig -> InvF Z -> Forall (fun e => reg e = j) w ->
    valid j y ->
    f j Z (fold_left (cstep j Z) w (f j Z y)) = f j Z (fold_left (fun x e => sig e x) w y).
  Proof.
    intros j Z w. induction w as [| e w IH]; intros y HX HZ Hw Hy.
    - simpl. apply (c_absorb _ _ _ _ _ _ _ _ _ HC); assumption.
    - inversion Hw as [| ? ? He Hw']; subst j. simpl. unfold cstep at 2.
      rewrite (xu_strong _ _ _ _ _ _ _ _ _ HC HX e Z Z y HZ HZ Hy).
      apply IH; [exact HX | exact HZ | exact Hw' | apply (c_sig _ _ _ _ _ _ _ _ _ HC); exact Hy].
  Qed.

  Theorem fed_nf_recipe_xu : XU V f valid E reg sig -> LocalCC V valid E reg sig (fun _ _ => True) ->
    forall es s, InvF s -> ConsF s ->
      forall j, In j o -> rF es s j = f j (rF es s) (fold_left (fun x e => sig e x) (filt_on j es) (s j)).
  Proof.
    intros HX HL es s Hi Hc j Hj.
    destruct (xu_implies_c1_c2 _ _ _ _ _ _ _ _ (fun _ _ => True) _ HC HX HL) as [H1 H2].
    destruct (fed_nf_constructive H1 H2 es s Hi Hc) as [_ [Heq _]].
    rewrite (Heq j Hj) at 1. unfold Gc. apply recipe_xu;
      [exact HX | apply (runF_inv _ _ _ _ _ _ _ _ _ HC); exact Hi | | apply Hi].
    apply Forall_forall. intros e He. unfold filt_on in He. apply filter_In in He as [_ He].
    apply Nat.eqb_eq. exact He.
  Qed.
End Constructive.

(* ========================================================================================= *)
(* PART B. The paper's hypotheses and its federated results, by label.                       *)
(* ========================================================================================= *)

Section Paper.
  Variables (V Sh Lo : Type) (sh : V -> Sh) (lc : V -> Lo) (mk : Sh -> Lo -> V).
  Variable src : nat -> list nat.                 (* S(j): the sources of registry j *)
  Variable Gam : nat -> (nat -> V) -> Sh.         (* phi_ij (one source) or Gamma_j (several) *)
  Variable valid : nat -> V -> Prop.              (* V_{R_j} *)
  Variable rho : nat -> V -> V.                   (* rho_{R_j}^* *)
  Variable E : Type.
  Variable reg : E -> nat.
  Variable ap : E -> V -> V.                      (* apply(e, -) *)
  Variable o : list nat.                          (* a topological order *)
  Variable cj : nat -> V -> V.                    (* rho_{R_j}: one compensation step *)
  Variable Phij : nat -> V -> nat.                (* the WFC potential of R_j *)
  Hypothesis vdec : forall k x, {valid k x} + {~ valid k x}.

  (* Phase 2 of rho_Fed on registry j: sigma_j[sh |-> Gamma_j(sources)], identity on a source. *)
  Definition pf (j : nat) (z : nat -> V) (x : V) : V :=
    match src j with [] => x | _ :: _ => mk (Gam j z) (lc x) end.

  (* The hypotheses of thm:resolved-convergence: an acyclic resolved network (Def.
     "Resolution Operator", "Resolved Network"; a single-source target's resolver is its
     authority morphism and R2 is then M1), component WFC (Ax. "WFC", Def. "Iterated
     Compensation") and component CC (Ax. "CC"). The shared/local split is Def. "Registry
     Morphism". *)
  Record PaperNet : Prop := {
    pn_iso1 : forall x, mk (sh x) (lc x) = x;
    pn_iso2 : forall s l, sh (mk s l) = s;
    pn_iso3 : forall s l, lc (mk s l) = l;
    pn_acyclic : topoF src o;
    pn_src_in : forall j k, In k (src j) -> In k o;
    pn_R1 : forall j z1 z2, (forall k, In k (src j) -> z1 k = z2 k) -> Gam j z1 = Gam j z2;
    pn_R2 : forall j z x, src j <> [] -> (forall k, In k (src j) -> valid k (z k)) -> valid j x ->
      valid j (mk (Gam j z) (lc x));
    pn_wfc : forall j x, ~ valid j x -> Phij j (cj j x) < Phij j x;
    pn_rho_id : forall j x, valid j x -> rho j x = x;
    pn_rho_rec : forall j x, ~ valid j x -> rho j x = rho j (cj j x);
    pn_cc1 : forall e1 e2 x, reg e1 = reg e2 ->
      rho (reg e1) (ap e2 (rho (reg e1) (ap e1 x))) = rho (reg e1) (ap e1 (rho (reg e1) (ap e2 x)));
    pn_cc2 : forall e x, ~ valid (reg e) x ->
      rho (reg e) (ap e x) = rho (reg e) (ap e (cj (reg e) x));
    pn_reg : forall e, In (reg e) o
  }.

  (* The hypotheses of thm:fed-cc / thm:fed-convergence: additionally a tree (each non-source
     has exactly one incoming morphism). *)
  Definition PaperTree : Prop := PaperNet /\ forall j, length (src j) <= 1.

  Lemma tree_net : PaperTree -> PaperNet.
  Proof. intros [H _]. exact H. Qed.

  Local Notation sg := (gsig V rho E reg ap).

  Lemma rho_valid_m : PaperNet -> forall j m x, Phij j x <= m -> valid j (rho j x).
  Proof.
    intros HP j m. induction m as [| m IH]; intros x Hx; destruct (vdec j x) as [Hv | Hv];
      try (rewrite (pn_rho_id HP j x Hv); exact Hv).
    - pose proof (pn_wfc HP j x Hv). lia.
    - rewrite (pn_rho_rec HP j x Hv). apply IH. pose proof (pn_wfc HP j x Hv). lia.
  Qed.

  (* Def. "Iterated Compensation": WFC makes rho^* reach validity. *)
  Lemma paper_rho_valid : PaperNet -> forall j x, valid j (rho j x).
  Proof. intros HP j x. apply (rho_valid_m HP j (Phij j x)). lia. Qed.

  Fixpoint citer (j k : nat) (x : V) : V :=
    match k with 0 => x | S k' => if vdec j x then x else citer j k' (cj j x) end.

  (* lem:fed-termination, Phase 1: rho_{R_j}^* is at most Phi_j(x) compensation steps and
     lands in a valid state (the paper's "<= sum_i M_i steps"). *)
  Theorem fed_phase1_bound : PaperNet -> forall j x,
    rho j x = citer j (Phij j x) x /\ valid j (rho j x).
  Proof.
    intros HP j x. split; [| apply paper_rho_valid; exact HP].
    assert (G : forall m y, Phij j y <= m -> rho j y = citer j m y).
    { induction m as [| m IH]; intros y Hy; simpl.
      - destruct (vdec j y) as [Hv | Hv]; [apply (pn_rho_id HP); exact Hv |].
        pose proof (pn_wfc HP j y Hv). lia.
      - destruct (vdec j y) as [Hv | Hv]; [apply (pn_rho_id HP); exact Hv |].
        rewrite (pn_rho_rec HP j y Hv). apply IH. pose proof (pn_wfc HP j y Hv). lia. }
    apply G. lia.
  Qed.

  (* Component CC2, iterated to rho^* by WFC. *)
  Lemma paper_cc2_star : PaperNet -> forall e x, rho (reg e) (ap e (rho (reg e) x)) = rho (reg e) (ap e x).
  Proof.
    intros HP e x.
    assert (G : forall m y, Phij (reg e) y <= m -> rho (reg e) (ap e (rho (reg e) y)) = rho (reg e) (ap e y)).
    { induction m as [| m IH]; intros y Hy; destruct (vdec (reg e) y) as [Hv | Hv];
        try (rewrite (pn_rho_id HP _ y Hv); reflexivity).
      - pose proof (pn_wfc HP _ y Hv). lia.
      - rewrite (pn_cc2 HP e y Hv). rewrite (pn_rho_rec HP _ y Hv). apply IH.
        pose proof (pn_wfc HP _ y Hv). lia. }
    apply (G (Phij (reg e) x)). lia.
  Qed.

  Lemma paper_rho_idem : PaperNet -> forall j x, rho j (rho j x) = rho j x.
  Proof. intros HP j x. apply (pn_rho_id HP). apply paper_rho_valid. exact HP. Qed.

  (* The paper's hypotheses give the Common conditions of the FedMachine model. *)
  Theorem paper_common : PaperNet -> Common V src pf valid rho E reg sg o.
  Proof.
    intros HP. constructor.
    - intros j z1 z2 x H. unfold pf. destruct (src j) eqn:Hs; [reflexivity |].
      rewrite (pn_R1 HP j z1 z2); [reflexivity |]. rewrite Hs. exact H.
    - exact (pn_acyclic HP).
    - intros j z x Hz Hx. unfold pf. destruct (src j) eqn:Hs; [exact Hx |].
      apply (pn_R2 HP); [rewrite Hs; discriminate | intros; apply Hz | exact Hx].
    - intros j z z' x _ _ _. unfold pf. destruct (src j); [reflexivity |].
      rewrite (pn_iso3 HP). reflexivity.
    - exact (pn_rho_id HP).
    - intros e x _. unfold gsig. apply paper_rho_valid. exact HP.
    - exact (pn_reg HP).
  Qed.

  Lemma paper_localcc : PaperNet -> LocalCC V valid E reg sg (Itot E).
  Proof.
    intros HP e1 e2 x E12 _ _. unfold gsig. rewrite E12.
    exact (pn_cc1 HP e2 e1 x (eq_sym E12)).
  Qed.

  (* ----- lem:authority (b) and the true half of (c) ----- *)

  (* (b): in a federally valid state the shared component of every target is its resolver
     (single source: morphism) image, a function of its sources alone. *)
  Theorem fed_lem_authority_b : PaperNet -> forall t, Cons V pf o t ->
    forall j, In j o -> src j <> [] ->
      sh (t j) = Gam j t /\ (forall t', (forall k, In k (src j) -> t' k = t k) -> Gam j t' = sh (t j)).
  Proof.
    intros HP t Hc j Hj Hs.
    assert (Hb : sh (t j) = Gam j t).
    { rewrite (Hc j Hj). unfold pf. destruct (src j); [contradiction |]. apply (pn_iso2 HP). }
    split; [exact Hb |]. intros t' H. rewrite Hb. apply (pn_R1 HP). exact H.
  Qed.

  (* (c), first clause: morphism and resolver repair never modify a local component. *)
  Theorem fed_lem_authority_c_local : PaperNet -> forall j z x, lc (pf j z x) = lc x.
  Proof. intros HP j z x. unfold pf. destruct (src j); [reflexivity | apply (pn_iso3 HP)]. Qed.

  (* ----- the list layer ----- *)
  Variable n : nat.
  Variable d : V.
  Hypothesis Hrange : forall k, In k o <-> k < n.
  Hypothesis Hout : forall k x, n <= k -> valid k x.
  Hypothesis Veq : forall x y : V, {x = y} + {x <> y}.
  Hypothesis Eeq : forall x y : E, {x = y} + {x <> y}.

  Lemma paper_src_lt : PaperNet -> forall j k, In k (src j) -> k < n.
  Proof. intros HP j k H. apply Hrange. apply (pn_src_in HP j k H). Qed.

  Local Notation GA := (gapply V E reg ap n d).
  Local Notation GR := (grho V pf rho o n d).
  Local Notation GV := (gvalid V pf valid o n d).
  Local Notation GOV := (gov V pf rho E reg ap o n d).
  Local Notation GRS := (step Eeq GA GR GV free_enabled).
  Local Notation GRSg := (step Eeq GA GR GV (genab V pf valid E o n d)).
  Local Notation NFed := (N V pf rho o).

  (* lem:resolved-termination (F17): one application of rho_Fed from ANY federated state is
     federally valid. *)
  Theorem fed_lem_resolved_termination : PaperNet ->
    (forall t, Inv V valid (NFed t) /\ Cons V pf o (NFed t)) /\ (forall l, GV (GR l)).
  Proof.
    intros HP. split.
    - exact (single_round V src pf valid rho E reg ap o (paper_common HP) (paper_rho_valid HP)).
    - exact (grho_valid V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout).
  Qed.

  (* lem:fed-termination (F7). *)
  Theorem fed_lem_fed_termination : PaperTree ->
    (forall t, Inv V valid (NFed t) /\ Cons V pf o (NFed t)) /\ (forall l, GV (GR l)).
  Proof. intros HT. apply fed_lem_resolved_termination. apply tree_net. exact HT. Qed.

  (* ----- lem:authority (a) ----- *)

  Local Notation CG i := (step Eeq (capp V E reg ap i) (cj i) (valid i) free_enabled).

  Lemma comp_reach : PaperNet -> forall i x F, star (CG i) (x, F) (rho i x, F).
  Proof.
    intros HP i x F.
    assert (G : forall m y, Phij i y <= m -> star (CG i) (y, F) (rho i y, F)).
    { induction m as [| m IH]; intros y Hy; destruct (vdec i y) as [Hv | Hv];
        try (rewrite (pn_rho_id HP i y Hv); apply star_refl).
      - pose proof (pn_wfc HP i y Hv). lia.
      - eapply star_step; [apply st_comp; exact Hv |]. rewrite (pn_rho_rec HP i y Hv). apply IH.
        pose proof (pn_wfc HP i y Hv). lia. }
    apply (G (Phij i x)). lia.
  Qed.

  Lemma comp_cc1 : PaperNet -> forall i x e1 e2,
    rho i (capp V E reg ap i e2 (rho i (capp V E reg ap i e1 x))) =
    rho i (capp V E reg ap i e1 (rho i (capp V E reg ap i e2 x))).
  Proof.
    intros HP i x e1 e2. unfold capp.
    destruct (Nat.eqb (reg e1) i) eqn:H1; destruct (Nat.eqb (reg e2) i) eqn:H2;
      try apply Nat.eqb_eq in H1; try apply Nat.eqb_eq in H2.
    - subst i. exact (pn_cc1 HP e1 e2 x (eq_sym H2)).
    - subst i. rewrite (paper_rho_idem HP). symmetry. apply (paper_cc2_star HP).
    - subst i. rewrite (paper_rho_idem HP). apply (paper_cc2_star HP).
    - reflexivity.
  Qed.

  Lemma comp_cc2 : PaperNet -> forall i x e, ~ valid i x ->
    rho i (capp V E reg ap i e x) = rho i (capp V E reg ap i e (cj i x)).
  Proof.
    intros HP i x e Hx. unfold capp. destruct (Nat.eqb (reg e) i) eqn:H.
    - apply Nat.eqb_eq in H. subst i. apply (pn_cc2 HP). exact Hx.
    - apply (pn_rho_rec HP). exact Hx.
  Qed.

  Lemma comp_after_remove : forall i (sigma : V) B e1 e2,
    free_enabled e1 sigma B -> free_enabled e2 sigma B -> e1 <> e2 ->
    In e2 (remove1 Eeq e1 B) /\
    free_enabled e2 (rho i (capp V E reg ap i e1 sigma)) (remove1 Eeq e1 B).
  Proof.
    intros i sigma B e1 e2 _ H2 Hne. unfold free_enabled.
    assert (Hi : In e2 (remove1 Eeq e1 B)) by (apply in_rm; [exact H2 | intro E'; apply Hne; symmetry; exact E']).
    split; exact Hi.
  Qed.

  (* (a): in every normal form of the federated GRS, a source registry's state is THE normal
     form of its own single-registry GRS on its own events (unique by component WFC + CC and
     the Convergence Theorem). *)
  Theorem fed_lem_authority_a : PaperNet -> forall i, In i o -> src i = [] ->
    forall s0 B nf, star GRS (s0, B) (nf, []) -> GV nf ->
      star (CG i) (nth i s0 d, filt E reg i B) (nth i nf d, []) /\
      normal_form (CG i) (nth i nf d, []) /\
      (forall m, star (CG i) (nth i s0 d, filt E reg i B) m -> normal_form (CG i) m ->
         m = (nth i nf d, [])).
  Proof.
    intros HP i Hi Hs s0 B nf S Hv.
    assert (Hid : forall z x, pf i z x = x) by (intros; unfold pf; rewrite Hs; reflexivity).
    destruct (fed_authority_a_gen V src pf valid rho E reg ap o n d (paper_common HP) Hrange Eeq i Hi
                Hid (cj i) (comp_reach HP i) s0 B nf S Hv) as [A1 A2].
    split; [exact A1 |]. split; [exact A2 |].
    intros m Sm Nm.
    exact (governance_unique_normal_forms Eeq (capp V E reg ap i) (cj i) (rho i) (valid i) (Phij i)
             free_enabled (pn_wfc HP i) (comp_reach HP i) (comp_cc1 HP i) (comp_cc2 HP i)
             (comp_after_remove i) (fun _ _ _ H => H) _ _ _ Sm Nm A1 A2).
  Qed.

  (* ----- corrected thm:fed-cc / thm:fed-convergence / thm:resolved-convergence ----- *)

  (* Unrestricted GRS, resolved (acyclic) networks: add XU. *)
  Theorem fed_resolved_cc_corrected : PaperNet -> XU V pf valid E reg sg ->
    (forall sigma e1 e2, GOV e2 (GOV e1 sigma) = GOV e1 (GOV e2 sigma)) /\
    (forall sigma e, GOV e sigma = GOV e (GR sigma)).
  Proof.
    intros HP HX. split.
    - exact (grs_cc1 V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP) Hrange
               (paper_src_lt HP) HX (paper_localcc HP) (paper_cc2_star HP)).
    - exact (grs_cc2 V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP) Hrange
               (paper_src_lt HP) HX (paper_cc2_star HP)).
  Qed.

  Theorem fed_thm_resolved_convergence_corrected : PaperNet -> XU V pf valid E reg sg ->
    (forall c n1 n2, star GRS c n1 -> normal_form GRS n1 -> star GRS c n2 -> normal_form GRS n2 ->
       n1 = n2) /\
    (forall l B, exists m, star GRS (l, B) (m, []) /\ normal_form GRS (m, []) /\ GV m).
  Proof.
    intros HP HX. split.
    - exact (grs_unique_nf V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout vdec Veq Eeq HX (paper_localcc HP) (paper_cc2_star HP)).
    - exact (grs_nf_exists V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout vdec Veq Eeq).
  Qed.

  (* Guarded GRS (FedMachine.Apply semantics), resolved networks: C1 and C2 suffice. *)
  Theorem fed_thm_resolved_convergence_guarded : PaperNet ->
    C1 V pf valid E reg sg -> C2 V pf valid E reg sg (Itot E) ->
    forall s0, GV s0 -> forall B, UN GRSg (s0, B).
  Proof.
    intros HP H1 H2.
    exact (fed_guarded_c1_c2 V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
             Hrange (paper_src_lt HP) Hout vdec Veq Eeq H1 H2).
  Qed.

  (* The exact conditions, resolved networks. *)
  Theorem fed_thm_resolved_convergence_exact : PaperNet -> forall s0, GV s0 ->
    ((forall B, UN GRS (s0, B)) <->
      ((forall sigma e1 e2, reach GA GR GV s0 sigma -> GOV e2 (GOV e1 sigma) = GOV e1 (GOV e2 sigma)) /\
       (forall sigma e, reach GA GR GV s0 sigma -> ~ GV sigma -> GOV e sigma = GOV e (GR sigma)))) /\
    ((forall B, UN GRS (s0, B)) ->
      C1R1 V pf rho E reg sg o (toF V d s0) /\ C2R V pf rho E reg sg (Itot E) o (toF V d s0)) /\
    ((forall B, UN GRSg (s0, B)) <->
      C1R1 V pf rho E reg sg o (toF V d s0) /\ C2R V pf rho E reg sg (Itot E) o (toF V d s0)).
  Proof.
    intros HP s0 Hs0. split; [| split].
    - exact (fed_grs_exact V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout vdec Veq Eeq s0).
    - exact (fed_grs_un_c1_c2 V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout vdec Veq Eeq s0 Hs0).
    - exact (fed_guarded_exact V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
               Hrange (paper_src_lt HP) Hout vdec Veq Eeq s0 Hs0).
  Qed.

  (* Tree versions (thm:fed-cc, thm:fed-convergence), as special cases. *)
  Theorem fed_thm_fed_cc_corrected : PaperTree -> XU V pf valid E reg sg ->
    (forall sigma e1 e2, GOV e2 (GOV e1 sigma) = GOV e1 (GOV e2 sigma)) /\
    (forall sigma e, GOV e sigma = GOV e (GR sigma)).
  Proof. intros HT. apply fed_resolved_cc_corrected. apply tree_net. exact HT. Qed.

  Theorem fed_thm_fed_cc_corrected_machine : PaperTree ->
    C1 V pf valid E reg sg -> C2 V pf valid E reg sg (Itot E) ->
    forall l, GV l -> forall e1 e2, GOV e2 (GOV e1 l) = GOV e1 (GOV e2 l).
  Proof.
    intros HT H1 H2. pose proof (tree_net HT) as HP.
    exact (grs_cc1_valid V src pf valid rho E reg ap o n d (paper_common HP) (paper_rho_valid HP)
             Hrange (paper_src_lt HP) H1 H2).
  Qed.

  Theorem fed_thm_fed_convergence_corrected : PaperTree -> XU V pf valid E reg sg ->
    (forall c n1 n2, star GRS c n1 -> normal_form GRS n1 -> star GRS c n2 -> normal_form GRS n2 ->
       n1 = n2) /\
    (forall l B, exists m, star GRS (l, B) (m, []) /\ normal_form GRS (m, []) /\ GV m).
  Proof. intros HT. apply fed_thm_resolved_convergence_corrected. apply tree_net. exact HT. Qed.

  Theorem fed_thm_fed_convergence_guarded : PaperTree ->
    C1 V pf valid E reg sg -> C2 V pf valid E reg sg (Itot E) ->
    forall s0, GV s0 -> forall B, UN GRSg (s0, B).
  Proof. intros HT. apply fed_thm_resolved_convergence_guarded. apply tree_net. exact HT. Qed.

  Theorem fed_thm_fed_convergence_exact : PaperTree -> forall s0, GV s0 ->
    ((forall B, UN GRS (s0, B)) <->
      ((forall sigma e1 e2, reach GA GR GV s0 sigma -> GOV e2 (GOV e1 sigma) = GOV e1 (GOV e2 sigma)) /\
       (forall sigma e, reach GA GR GV s0 sigma -> ~ GV sigma -> GOV e sigma = GOV e (GR sigma)))) /\
    ((forall B, UN GRS (s0, B)) ->
      C1R1 V pf rho E reg sg o (toF V d s0) /\ C2R V pf rho E reg sg (Itot E) o (toF V d s0)) /\
    ((forall B, UN GRSg (s0, B)) <->
      C1R1 V pf rho E reg sg o (toF V d s0) /\ C2R V pf rho E reg sg (Itot E) o (toF V d s0)).
  Proof. intros HT. apply fed_thm_resolved_convergence_exact. apply tree_net. exact HT. Qed.

  (* lem:authority (c), corrected: under XU every two normal forms agree, local components
     included. *)
  Theorem fed_lem_authority_c_corrected : PaperNet -> XU V pf valid E reg sg ->
    forall c nf1 nf2, star GRS c (nf1, []) -> normal_form GRS (nf1, []) ->
      star GRS c (nf2, []) -> normal_form GRS (nf2, []) -> forall j, lc (nth j nf1 d) = lc (nth j nf2 d).
  Proof.
    intros HP HX c nf1 nf2 S1 N1 S2 N2 j.
    destruct (fed_thm_resolved_convergence_corrected HP HX) as [U _].
    pose proof (U _ _ _ S1 N1 S2 N2) as Hq. injection Hq as ->. reflexivity.
  Qed.

  (* ----- cor:fed-nf / cor:resolved-nf, corrected ----- *)

  Theorem fed_cor_resolved_nf_corrected : PaperNet ->
    (C1 V pf valid E reg sg -> C2 V pf valid E reg sg (fun _ _ => True) ->
     forall es s, Inv V valid s -> Cons V pf o s ->
       let Z := runF V pf rho E reg sg o es s in
       (forall k, ~ In k o -> Z k = s k) /\
       (forall j, In j o -> Z j = Gc V pf E reg sg s es j Z) /\
       (forall Y, (forall k, ~ In k o -> Y k = s k) -> (forall j, In j o -> Y j = Gc V pf E reg sg s es j Y) ->
          feq V Y Z)) /\
    (XU V pf valid E reg sg ->
     forall es s, Inv V valid s -> Cons V pf o s -> forall j, In j o ->
       let Z := runF V pf rho E reg sg o es s in
       Z j = pf j Z (fold_left (fun x e => sg e x) (filt_on E reg j es) (s j))).
  Proof.
    intros HP. split.
    - intros H1 H2 es s Hi Hc. exact (fed_nf_constructive V src pf valid rho E reg sg o (paper_common HP) H1 H2 es s Hi Hc).
    - intros HX es s Hi Hc j Hj.
      apply (fed_nf_recipe_xu V src pf valid rho E reg sg o (paper_common HP) HX); try assumption.
      intros e1 e2 x E12 _ Hx. apply (paper_localcc HP); [exact E12 | exact I | exact Hx].
  Qed.

  Theorem fed_cor_fed_nf_corrected : PaperTree ->
    (C1 V pf valid E reg sg -> C2 V pf valid E reg sg (fun _ _ => True) ->
     forall es s, Inv V valid s -> Cons V pf o s ->
       let Z := runF V pf rho E reg sg o es s in
       (forall k, ~ In k o -> Z k = s k) /\
       (forall j, In j o -> Z j = Gc V pf E reg sg s es j Z) /\
       (forall Y, (forall k, ~ In k o -> Y k = s k) -> (forall j, In j o -> Y j = Gc V pf E reg sg s es j Y) ->
          feq V Y Z)) /\
    (XU V pf valid E reg sg ->
     forall es s, Inv V valid s -> Cons V pf o s -> forall j, In j o ->
       let Z := runF V pf rho E reg sg o es s in
       Z j = pf j Z (fold_left (fun x e => sg e x) (filt_on E reg j es) (s j))).
  Proof. intros HT. apply fed_cor_resolved_nf_corrected. apply tree_net. exact HT. Qed.
End Paper.

(* ========================================================================================= *)
(* PART C. The counterexamples, restated against the paper's exact hypotheses, and the       *)
(* non-vacuity instances. Two registries: 0 (source) and 1 (target), o = [0; 1], n = 2.      *)
(* ========================================================================================= *)

Lemma app_step : forall {St Ev : Type} (Eeq : forall x y : Ev, {x = y} + {x <> y})
  (apply : Ev -> St -> St) (rho : St -> St) (valid : St -> Prop) l B e l' B',
  In e B -> l' = apply e l -> B' = remove1 Eeq e B ->
  step Eeq apply rho valid free_enabled (l, B) (l', B').
Proof. intros. subst. apply st_apply; assumption. Qed.

Lemma comp_step : forall {St Ev : Type} (Eeq : forall x y : Ev, {x = y} + {x <> y})
  (apply : Ev -> St -> St) (rho : St -> St) (valid : St -> Prop) (l : St) (B : list Ev) l',
  ~ valid l -> l' = rho l -> step Eeq apply rho valid free_enabled (l, B) (l', B).
Proof. intros. subst. apply st_comp. assumption. Qed.

Lemma nf_of_valid : forall {St Ev : Type} (Eeq : forall x y : Ev, {x = y} + {x <> y})
  (apply : Ev -> St -> St) (rho : St -> St) (valid : St -> Prop) (l : St),
  valid l -> normal_form (step Eeq apply rho valid free_enabled) (l, []).
Proof.
  intros St Ev Eeq apply rho valid l Hv [y H].
  inversion H as [s B e Hin _ E1 E2 | s B Hinv E1 E2]; subst; [destruct Hin | contradiction].
Qed.

Lemma range2 : forall k, In k [0; 1] <-> k < 2.
Proof.
  intros k. split; [intros [<- | [<- | []]]; lia |].
  intros H. destruct k as [| [| k]]; [left; reflexivity | right; left; reflexivity | lia].
Qed.

Definition bn_eq : forall x y : bool * nat, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition bbb_eq : forall x y : bool * bool * bool, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition bb_eq : forall x y : bool * bool, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

(* ----- the supply chain and the audit counterexample (state: (flag, count)) ----- *)

Definition au_G (j : nat) (z : nat -> bool * nat) : bool :=
  match j with 1 => negb (fst (z 0)) | _ => false end.

Definition au_Phi (j : nat) (x : bool * nat) : nat :=
  match j with 1 => if Nat.leb (snd x) 3 then 0 else 1 | _ => 0 end.

Definition sp_vdec : forall k x, {sp_valid k x} + {~ sp_valid k x}.
Proof. intros [| [| k]] x; simpl; [left; exact I | apply le_dec | left; exact I]. Defined.

Lemma sp_out : forall k x, 2 <= k -> sp_valid k x.
Proof. intros [| [| k]] x H; simpl; [lia | lia | exact I]. Qed.

Definition ce_eq : forall x y : cev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition sev_eq : forall x y : sev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Local Notation au_pf := (pf (bool * nat) bool nat snd pair src2 au_G).

Lemma sp_rho_rec : forall j x, ~ sp_valid j x -> sp_rho j x = sp_rho j (sp_rho j x).
Proof. intros [| [| j]] [b m] H; simpl in *; try reflexivity. f_equal. lia. Qed.

Lemma sp_rho_id : forall j x, sp_valid j x -> sp_rho j x = x.
Proof. intros [| [| j]] [b m] H; simpl in *; try reflexivity. f_equal. lia. Qed.

Lemma sp_wfc : forall j x, ~ sp_valid j x -> au_Phi j (sp_rho j x) < au_Phi j x.
Proof.
  intros [| [| j]] [b m] H; simpl in *; try (exfalso; apply H; exact I).
  destruct (Nat.leb (Nat.min m 3) 3) eqn:E1; destruct (Nat.leb m 3) eqn:E2;
    try apply Nat.leb_le in E1; try apply Nat.leb_le in E2;
    try apply Nat.leb_gt in E1; try apply Nat.leb_gt in E2; lia.
Qed.

Lemma au_paper : PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho
                   cev ce_reg ce_sig [0; 1] sp_rho au_Phi.
Proof.
  split; [| intros [| [| j]]; simpl; lia].
  constructor.
  - intros [b m]. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact topo2.
  - intros [| [| j]] k H; simpl in H; try contradiction. destruct H as [<- | []]. left. reflexivity.
  - intros [| [| j]] z1 z2 H; simpl; try reflexivity. rewrite (H 0); [reflexivity | left; reflexivity].
  - intros [| [| j]] z [b m] Hs _ Hx; simpl in *; try (exfalso; apply Hs; reflexivity); exact Hx.
  - exact sp_wfc.
  - exact sp_rho_id.
  - exact sp_rho_rec.
  - intros [] [] x H; simpl in H; try discriminate; reflexivity.
  - intros [] [b m] H; simpl in *; [exfalso; apply H; exact I |].
    destruct b; simpl; f_equal; lia.
  - intros []; simpl; tauto.
Qed.

Local Notation au_GA := (gapply (bool * nat) cev ce_reg ce_sig 2 (false, 0)).
Local Notation au_GR := (grho (bool * nat) au_pf sp_rho [0; 1] 2 (false, 0)).
Local Notation au_GV := (gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0)).
Local Notation au_GOV := (gov (bool * nat) au_pf sp_rho cev ce_reg ce_sig [0; 1] 2 (false, 0)).
Local Notation au_GRS := (step ce_eq au_GA au_GR au_GV free_enabled).

Definition au_s0 : list (bool * nat) := [(false, 0); (true, 0)].
Definition au_nf1 : list (bool * nat) := [(true, 0); (false, 0)].
Definition au_nf2 : list (bool * nat) := [(true, 0); (false, 1)].

Lemma au_valid : forall l, l = au_s0 \/ l = au_nf1 \/ l = au_nf2 \/ l = [(false, 0); (true, 1)] -> au_GV l.
Proof.
  intros l Hl. split; [destruct Hl as [-> | [-> | [-> | ->]]]; reflexivity |].
  split.
  - intros [| [| k]]; destruct Hl as [-> | [-> | [-> | ->]]]; simpl; try lia; exact I.
  - intros j [<- | [<- | []]]; destruct Hl as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma au_invalid : forall l, l = [(true, 0); (true, 0)] \/ l = [(true, 0); (true, 1)] -> ~ au_GV l.
Proof.
  intros l Hl [_ [_ Hc]]. pose proof (Hc 1 (or_intror (or_introl eq_refl))) as H.
  destruct Hl as [-> | ->]; vm_compute in H; discriminate H.
Qed.

(* The two event orders of the audit counterexample, as runs of the federated GRS. *)
Lemma au_paths :
  au_GV au_s0 /\
  star au_GRS (au_s0, [CRecall; CSell]) (au_nf1, []) /\ normal_form au_GRS (au_nf1, []) /\
  star au_GRS (au_s0, [CRecall; CSell]) (au_nf2, []) /\ normal_form au_GRS (au_nf2, []) /\
  au_nf1 <> au_nf2.
Proof.
  split; [apply au_valid; left; reflexivity |].
  split.
  { eapply star_step; [apply (app_step ce_eq _ _ _ _ _ CRecall [(true, 0); (true, 0)] [CSell]);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step ce_eq _ _ _ _ _ au_nf1);
                       [apply au_invalid; left; reflexivity | vm_compute; reflexivity] |].
    eapply star_step; [apply (app_step ce_eq _ _ _ _ _ CSell au_nf1 []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply au_valid; right; left; reflexivity |].
  split.
  { eapply star_step; [apply (app_step ce_eq _ _ _ _ _ CSell [(false, 0); (true, 1)] [CRecall]);
                       [right; left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (app_step ce_eq _ _ _ _ _ CRecall [(true, 0); (true, 1)] []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step ce_eq _ _ _ _ _ au_nf2);
                       [apply au_invalid; right; reflexivity | vm_compute; reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply au_valid; right; right; left; reflexivity |].
  discriminate.
Qed.

(* thm:fed-cc, as stated, is false: a tree, component WFC and CC, M1; the federated CC1 fails
   at a federally valid state. *)
Theorem fed_thm_fed_cc_refuted :
  PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho cev ce_reg ce_sig [0; 1]
    sp_rho au_Phi /\
  au_GV au_s0 /\ au_GOV CSell (au_GOV CRecall au_s0) <> au_GOV CRecall (au_GOV CSell au_s0).
Proof.
  split; [exact au_paper |]. split; [apply au_valid; left; reflexivity |].
  intro H. vm_compute in H. discriminate H.
Qed.

(* thm:fed-convergence, as stated, is false: the same federation, one federally valid start,
   one event buffer, two distinct federally valid normal forms. *)
Theorem fed_thm_fed_convergence_refuted :
  PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho cev ce_reg ce_sig [0; 1]
    sp_rho au_Phi /\
  au_GV au_s0 /\
  exists nf1 nf2, star au_GRS (au_s0, [CRecall; CSell]) (nf1, []) /\ normal_form au_GRS (nf1, []) /\
                  star au_GRS (au_s0, [CRecall; CSell]) (nf2, []) /\ normal_form au_GRS (nf2, []) /\
                  nf1 <> nf2.
Proof.
  destruct au_paths as [H0 [S1 [N1 [S2 [N2 D]]]]].
  split; [exact au_paper |]. split; [exact H0 |]. exists au_nf1, au_nf2. tauto.
Qed.

(* thm:resolved-convergence, as stated, is false: a tree is an acyclic resolved network (its
   single-source resolvers are the morphisms; R1 and R2 are M1). *)
Theorem fed_thm_resolved_convergence_refuted :
  PaperNet (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho cev ce_reg ce_sig [0; 1]
    sp_rho au_Phi /\
  au_GV au_s0 /\
  exists nf1 nf2, star au_GRS (au_s0, [CRecall; CSell]) (nf1, []) /\ normal_form au_GRS (nf1, []) /\
                  star au_GRS (au_s0, [CRecall; CSell]) (nf2, []) /\ normal_form au_GRS (nf2, []) /\
                  nf1 <> nf2.
Proof.
  destruct fed_thm_fed_convergence_refuted as [HT H]. split; [apply tree_net; exact HT | exact H].
Qed.

(* lem:authority (c) is false: in the two normal forms the source state agrees ((a) holds),
   the target's shared component agrees ((b) holds), and the target's LOCAL component differs,
   although the target satisfies component CC (part of PaperTree). *)
Theorem fed_lem_authority_c_refuted :
  PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho cev ce_reg ce_sig [0; 1]
    sp_rho au_Phi /\
  star au_GRS (au_s0, [CRecall; CSell]) (au_nf1, []) /\ normal_form au_GRS (au_nf1, []) /\
  star au_GRS (au_s0, [CRecall; CSell]) (au_nf2, []) /\ normal_form au_GRS (au_nf2, []) /\
  nth 0 au_nf1 (false, 0) = nth 0 au_nf2 (false, 0) /\
  fst (nth 1 au_nf1 (false, 0)) = fst (nth 1 au_nf2 (false, 0)) /\
  snd (nth 1 au_nf1 (false, 0)) <> snd (nth 1 au_nf2 (false, 0)).
Proof.
  destruct au_paths as [_ [S1 [N1 [S2 [N2 _]]]]].
  split; [exact au_paper |]. repeat (split; [assumption |]).
  split; [reflexivity |]. split; [reflexivity |]. simpl. discriminate.
Qed.

(* ----- non-vacuity: the supply chain satisfies the paper's hypotheses plus XU ----- *)

Lemma su_paper : PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho
                   sev sp_reg sp_sig [0; 1] sp_rho au_Phi.
Proof.
  split; [| intros [| [| j]]; simpl; lia].
  constructor.
  - intros [b m]. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact topo2.
  - intros [| [| j]] k H; simpl in H; try contradiction. destruct H as [<- | []]. left. reflexivity.
  - intros [| [| j]] z1 z2 H; simpl; try reflexivity. rewrite (H 0); [reflexivity | left; reflexivity].
  - intros [| [| j]] z [b m] Hs _ Hx; simpl in *; try (exfalso; apply Hs; reflexivity); exact Hx.
  - exact sp_wfc.
  - exact sp_rho_id.
  - exact sp_rho_rec.
  - intros [] [] [b m] H; simpl in H; try discriminate; simpl; f_equal; lia.
  - intros [] [b m] H; simpl in *; [exfalso; apply H; exact I | f_equal; lia | f_equal; lia].
  - intros []; simpl; tauto.
Qed.

Local Notation su_sg := (gsig (bool * nat) sp_rho sev sp_reg sp_sig).

Lemma su_xu : XU (bool * nat) au_pf sp_valid sev sp_reg su_sg.
Proof. intros [] z [b m] _ _; reflexivity. Qed.

Theorem fed_supply_paper_instance :
  PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho sev sp_reg sp_sig [0; 1]
    sp_rho au_Phi /\
  XU (bool * nat) au_pf sp_valid sev sp_reg su_sg /\
  C1 (bool * nat) au_pf sp_valid sev sp_reg su_sg /\
  C2 (bool * nat) au_pf sp_valid sev sp_reg su_sg (Itot sev) /\
  gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0) au_s0 /\
  (forall c n1 n2,
     star (step sev_eq (gapply (bool * nat) sev sp_reg sp_sig 2 (false, 0))
             (grho (bool * nat) au_pf sp_rho [0; 1] 2 (false, 0))
             (gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0)) free_enabled) c n1 ->
     normal_form (step sev_eq (gapply (bool * nat) sev sp_reg sp_sig 2 (false, 0))
             (grho (bool * nat) au_pf sp_rho [0; 1] 2 (false, 0))
             (gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0)) free_enabled) n1 ->
     star (step sev_eq (gapply (bool * nat) sev sp_reg sp_sig 2 (false, 0))
             (grho (bool * nat) au_pf sp_rho [0; 1] 2 (false, 0))
             (gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0)) free_enabled) c n2 ->
     normal_form (step sev_eq (gapply (bool * nat) sev sp_reg sp_sig 2 (false, 0))
             (grho (bool * nat) au_pf sp_rho [0; 1] 2 (false, 0))
             (gvalid (bool * nat) au_pf sp_valid [0; 1] 2 (false, 0)) free_enabled) n2 ->
     n1 = n2).
Proof.
  pose proof su_paper as HT. pose proof (tree_net _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT) as HP.
  assert (HL := paper_localcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
  assert (HC := paper_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp_vdec HP).
  destruct (xu_implies_c1_c2 _ _ _ _ _ _ _ _ _ _ HC su_xu HL) as [H1 H2].
  split; [exact HT |]. split; [exact su_xu |]. split; [exact H1 |]. split; [exact H2 |].
  split; [apply au_valid; left; reflexivity |].
  exact (proj1 (fed_thm_fed_convergence_corrected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp_vdec 2 (false, 0)
                  range2 sp_out bn_eq sev_eq HT su_xu)).
Qed.

(* ----- C2 is needed: the c2_counterexample against the paper's hypotheses ----- *)
(* State ((slot_a, slot_b), audit); registry 1's slot_a is shared. The source's compensation
   now repairs its slot_a (component WFC), so every paper hypothesis holds, and C1 holds. *)

Definition cw_sh (x : bool * bool * bool) : bool := fst (fst x).
Definition cw_lc (x : bool * bool * bool) : bool * bool := (snd (fst x), snd x).
Definition cw_mk (s : bool) (l : bool * bool) : bool * bool * bool := ((s, fst l), snd l).
Definition cw_G (j : nat) (z : nat -> bool * bool * bool) : bool :=
  match j with 1 => fst (fst (z 0)) | _ => false end.
Definition cw_rho2 (j : nat) (x : bool * bool * bool) : bool * bool * bool :=
  match j with 0 => ((false, snd (fst x)), snd x) | _ => x end.
Definition cw_Phi (j : nat) (x : bool * bool * bool) : nat :=
  match j with 0 => if fst (fst x) then 1 else 0 | _ => 0 end.

Definition cw_vdec : forall k x, {cw_valid k x} + {~ cw_valid k x}.
Proof. intros [| k] x; simpl; [apply bool_dec | left; exact I]. Defined.

Lemma cw_out : forall k x, 2 <= k -> cw_valid k x.
Proof. intros [| k] x H; simpl; [lia | exact I]. Qed.

Definition wev_eq : forall x y : wev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Local Notation cw_pf := (pf (bool * bool * bool) bool (bool * bool) cw_lc cw_mk src2 cw_G).
Local Notation cw_sg := (gsig (bool * bool * bool) cw_rho2 wev cw_reg cw_sig).

Lemma cw_paper : PaperTree (bool * bool * bool) bool (bool * bool) cw_sh cw_lc cw_mk src2 cw_G
                   cw_valid cw_rho2 wev cw_reg cw_sig [0; 1] cw_rho2 cw_Phi.
Proof.
  split; [| intros [| [| j]]; simpl; lia].
  constructor.
  - intros [[a b] c]. reflexivity.
  - reflexivity.
  - intros s [b c]. reflexivity.
  - exact topo2.
  - intros [| [| j]] k H; simpl in H; try contradiction. destruct H as [<- | []]. left. reflexivity.
  - intros [| [| j]] z1 z2 H; simpl; try reflexivity. rewrite (H 0); [reflexivity | left; reflexivity].
  - intros [| [| j]] z x Hs _ Hx; simpl in *; try (exfalso; apply Hs; reflexivity); exact I.
  - intros [| j] [[a b] c] H; simpl in *; [destruct a; [lia | contradiction] | exfalso; apply H; exact I].
  - intros [| j] [[a b] c] H; simpl in *; [subst a |]; reflexivity.
  - intros [| j] [[a b] c] H; reflexivity.
  - intros [] [] [[a b] c] _; simpl; try reflexivity; destruct a, b; reflexivity.
  - intros e x H. exfalso. apply H. exact I.
  - intros e. simpl. tauto.
Qed.

Lemma cw_c1 : C1 (bool * bool * bool) cw_pf cw_valid wev cw_reg cw_sg.
Proof.
  intros e z z' [[a b] c] Hz Hz' _ Hb.
  assert (Hza : fst (fst (z 0)) = false) by exact (Hz 0).
  assert (Hza' : fst (fst (z' 0)) = false) by exact (Hz' 0).
  cbv beta iota delta [pf cw_mk cw_lc cw_G src2 gsig cw_rho2 cw_reg] in *.
  rewrite Hza' in Hb. rewrite Hza. injection Hb as Ha. subst a. reflexivity.
Qed.

Local Notation cw_GA := (gapply (bool * bool * bool) wev cw_reg cw_sig 2 ((false, false), false)).
Local Notation cw_GR := (grho (bool * bool * bool) cw_pf cw_rho2 [0; 1] 2 ((false, false), false)).
Local Notation cw_GV := (gvalid (bool * bool * bool) cw_pf cw_valid [0; 1] 2 ((false, false), false)).
Local Notation cw_GRS := (step wev_eq cw_GA cw_GR cw_GV free_enabled).

Definition cw_l0 : list (bool * bool * bool) := [((false, false), false); ((false, true), false)].
Definition cw_nf1 : list (bool * bool * bool) := [((false, false), false); ((false, false), true)].
Definition cw_nf2 : list (bool * bool * bool) := [((false, false), false); ((false, false), false)].

Lemma cw_valid_l : forall l, l = cw_l0 \/ l = cw_nf1 \/ l = cw_nf2 \/
    l = [((false, false), false); ((false, true), true)] -> cw_GV l.
Proof.
  intros l Hl. split; [destruct Hl as [-> | [-> | [-> | ->]]]; reflexivity |].
  split.
  - intros [| [| k]]; destruct Hl as [-> | [-> | [-> | ->]]]; simpl; reflexivity || exact I.
  - intros j [<- | [<- | []]]; destruct Hl as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma cw_invalid : forall l, l = [((false, false), false); ((true, false), true)] \/
    l = [((false, false), false); ((true, false), false)] -> ~ cw_GV l.
Proof.
  intros l Hl [_ [_ Hc]]. pose proof (Hc 1 (or_intror (or_introl eq_refl))) as H.
  destruct Hl as [-> | ->]; vm_compute in H; discriminate H.
Qed.

Theorem fed_c2_paper_counterexample :
  PaperTree (bool * bool * bool) bool (bool * bool) cw_sh cw_lc cw_mk src2 cw_G
    cw_valid cw_rho2 wev cw_reg cw_sig [0; 1] cw_rho2 cw_Phi /\
  C1 (bool * bool * bool) cw_pf cw_valid wev cw_reg cw_sg /\
  ~ C2 (bool * bool * bool) cw_pf cw_valid wev cw_reg cw_sg (Itot wev) /\
  cw_GV cw_l0 /\
  star cw_GRS (cw_l0, [Audit; Swap]) (cw_nf1, []) /\ normal_form cw_GRS (cw_nf1, []) /\
  star cw_GRS (cw_l0, [Audit; Swap]) (cw_nf2, []) /\ normal_form cw_GRS (cw_nf2, []) /\
  cw_nf1 <> cw_nf2.
Proof.
  split; [exact cw_paper |]. split; [exact cw_c1 |]. split.
  { intro Hc.
    assert (Hz : Inv (bool * bool * bool) cw_valid (fun _ => ((false, false), false)))
      by (intros [| k]; simpl; trivial).
    pose proof (Hc Audit Swap (fun _ => ((false, false), false)) ((false, true), false)
                   eq_refl I Hz I eq_refl) as Hd.
    vm_compute in Hd. discriminate Hd. }
  split; [apply cw_valid_l; left; reflexivity |].
  split.
  { eapply star_step; [apply (app_step wev_eq _ _ _ _ _ Audit
                                [((false, false), false); ((false, true), true)] [Swap]);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (app_step wev_eq _ _ _ _ _ Swap
                                [((false, false), false); ((true, false), true)] []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step wev_eq _ _ _ _ _ cw_nf1);
                       [apply cw_invalid; left; reflexivity | vm_compute; reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply cw_valid_l; right; left; reflexivity |].
  split.
  { eapply star_step; [apply (app_step wev_eq _ _ _ _ _ Swap
                                [((false, false), false); ((true, false), false)] [Audit]);
                       [right; left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step wev_eq _ _ _ _ _ cw_nf2);
                       [apply cw_invalid; right; reflexivity | vm_compute; reflexivity] |].
    eapply star_step; [apply (app_step wev_eq _ _ _ _ _ Audit cw_nf2 []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply cw_valid_l; right; right; left; reflexivity |].
  discriminate.
Qed.

(* ----- C1 + C2 do not suffice for the UNRESTRICTED GRS (two raw events stacked) ----- *)
(* State (shared, local) on the target; the only image is shared = false. Both events flip the
   shared flag and add it into the local bit. Every paper hypothesis holds, C1 and C2 hold, the
   FedMachine and the guarded GRS converge, yet the unrestricted GRS has two normal forms: the
   second event, applied before compensation, reads the shared value the first event wrote. *)

Inductive gev : Type := G1 | G2.

Definition gg_reg (_ : gev) : nat := 1.
Definition gg_ap (_ : gev) (x : bool * bool) : bool * bool := (negb (fst x), xorb (snd x) (fst x)).
Definition gg_valid (_ : nat) (_ : bool * bool) : Prop := True.
Definition gg_rho (_ : nat) (x : bool * bool) : bool * bool := x.
Definition gg_Phi (_ : nat) (_ : bool * bool) : nat := 0.
Definition gg_G (_ : nat) (_ : nat -> bool * bool) : bool := false.

Definition gg_vdec : forall k x, {gg_valid k x} + {~ gg_valid k x}.
Proof. intros. left. exact I. Defined.

Definition gev_eq : forall x y : gev, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Local Notation gg_pf := (pf (bool * bool) bool bool snd pair src2 gg_G).
Local Notation gg_sg := (gsig (bool * bool) gg_rho gev gg_reg gg_ap).

Lemma gg_paper : PaperTree (bool * bool) bool bool fst snd pair src2 gg_G gg_valid gg_rho
                   gev gg_reg gg_ap [0; 1] gg_rho gg_Phi.
Proof.
  split; [| intros [| [| j]]; simpl; lia].
  constructor.
  - intros [a b]. reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - exact topo2.
  - intros [| [| j]] k H; simpl in H; try contradiction. destruct H as [<- | []]. left. reflexivity.
  - intros; reflexivity.
  - intros; exact I.
  - intros j x H. exfalso. apply H. exact I.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros e. simpl. tauto.
Qed.

Lemma gg_c1 : C1 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg.
Proof.
  intros e z z' [s x] _ _ _ Hb. unfold gg_reg in *. simpl in Hb. injection Hb as ->. reflexivity.
Qed.

Lemma gg_c2 : C2 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg (Itot gev).
Proof. intros e1 e2 z b _ _ _ _ _. reflexivity. Qed.

Local Notation gg_GA := (gapply (bool * bool) gev gg_reg gg_ap 2 (false, false)).
Local Notation gg_GR := (grho (bool * bool) gg_pf gg_rho [0; 1] 2 (false, false)).
Local Notation gg_GV := (gvalid (bool * bool) gg_pf gg_valid [0; 1] 2 (false, false)).
Local Notation gg_GRS := (step gev_eq gg_GA gg_GR gg_GV free_enabled).
Local Notation gg_GRSg := (step gev_eq gg_GA gg_GR gg_GV
                             (genab (bool * bool) gg_pf gg_valid gev [0; 1] 2 (false, false))).

Definition gg_s0 : list (bool * bool) := [(false, false); (false, false)].
Definition gg_nf1 : list (bool * bool) := [(false, false); (false, true)].

Lemma gg_valid_l : forall l, l = gg_s0 \/ l = gg_nf1 -> gg_GV l.
Proof.
  intros l Hl. split; [destruct Hl as [-> | ->]; reflexivity |].
  split; [intros k; exact I |].
  intros j [<- | [<- | []]]; destruct Hl as [-> | ->]; reflexivity.
Qed.

Lemma gg_invalid : ~ gg_GV [(false, false); (true, false)].
Proof.
  intros [_ [_ Hc]]. pose proof (Hc 1 (or_intror (or_introl eq_refl))) as H.
  vm_compute in H. discriminate H.
Qed.

Theorem fed_grs_c1_c2_insufficient :
  PaperTree (bool * bool) bool bool fst snd pair src2 gg_G gg_valid gg_rho gev gg_reg gg_ap [0; 1]
    gg_rho gg_Phi /\
  C1 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg /\
  C2 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg (Itot gev) /\
  ~ XU (bool * bool) gg_pf gg_valid gev gg_reg gg_sg /\
  (forall es1 es2 s, Permutation es1 es2 -> Inv (bool * bool) gg_valid s -> Cons (bool * bool) gg_pf [0; 1] s ->
     feq (bool * bool) (runF (bool * bool) gg_pf gg_rho gev gg_reg gg_sg [0; 1] es1 s)
                       (runF (bool * bool) gg_pf gg_rho gev gg_reg gg_sg [0; 1] es2 s)) /\
  (forall B, UN gg_GRSg (gg_s0, B)) /\
  gg_GV gg_s0 /\
  star gg_GRS (gg_s0, [G1; G2]) (gg_nf1, []) /\ normal_form gg_GRS (gg_nf1, []) /\
  star gg_GRS (gg_s0, [G1; G2]) (gg_s0, []) /\ normal_form gg_GRS (gg_s0, []) /\
  gg_nf1 <> gg_s0.
Proof.
  pose proof gg_paper as HT. pose proof (tree_net _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT) as HP.
  assert (HC := paper_common _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg_vdec HP).
  split; [exact HT |]. split; [exact gg_c1 |]. split; [exact gg_c2 |]. split.
  { intro HX. pose proof (HX G1 (fun _ => (false, false)) (true, false) (fun _ => I) I) as H.
    vm_compute in H. discriminate H. }
  split.
  { intros es1 es2 s Hp Hi Hc.
    apply (fed_permutations_converge _ _ _ _ _ _ _ _ (Itot gev) _ HC gg_c1 gg_c2);
      [intros; exact I | exact Hp | exact Hi | exact Hc]. }
  split.
  { apply (fed_thm_fed_convergence_guarded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg_vdec 2 (false, false)
             range2 (fun _ _ _ => I) bb_eq gev_eq HT gg_c1 gg_c2).
    apply gg_valid_l. left. reflexivity. }
  split; [apply gg_valid_l; left; reflexivity |].
  split.
  { eapply star_step; [apply (app_step gev_eq _ _ _ _ _ G1 [(false, false); (true, false)] [G2]);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (app_step gev_eq _ _ _ _ _ G2 gg_nf1 []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply gg_valid_l; right; reflexivity |].
  split.
  { eapply star_step; [apply (app_step gev_eq _ _ _ _ _ G1 [(false, false); (true, false)] [G2]);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step gev_eq _ _ _ _ _ gg_s0);
                       [exact gg_invalid | vm_compute; reflexivity] |].
    eapply star_step; [apply (app_step gev_eq _ _ _ _ _ G2 [(false, false); (true, false)] []);
                       [left; reflexivity | vm_compute; reflexivity | reflexivity] |].
    eapply star_step; [apply (comp_step gev_eq _ _ _ _ _ gg_s0);
                       [exact gg_invalid | vm_compute; reflexivity] |].
    apply star_refl. }
  split; [apply nf_of_valid; apply gg_valid_l; left; reflexivity |].
  discriminate.
Qed.

(* cor:fed-nf as stated is false even under C1 and C2: the paper's recipe (the target runs its
   own events as a single registry, then its shared component is set from its finalized
   sources) gives (false, true), but every event order of the FedMachine gives (false, false);
   the corrected recipe (Gc, repair interleaved after each target event) gives (false, false). *)
Theorem fed_cor_fed_nf_refuted :
  PaperTree (bool * bool) bool bool fst snd pair src2 gg_G gg_valid gg_rho gev gg_reg gg_ap [0; 1]
    gg_rho gg_Phi /\
  C1 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg /\
  C2 (bool * bool) gg_pf gg_valid gev gg_reg gg_sg (fun _ _ => True) /\
  let s := toF (bool * bool) (false, false) gg_s0 in
  let Z := runF (bool * bool) gg_pf gg_rho gev gg_reg gg_sg [0; 1] [G1; G2] s in
  Z 1 = (false, false) /\
  Gc (bool * bool) gg_pf gev gg_reg gg_sg s [G1; G2] 1 Z = (false, false) /\
  gg_pf 1 Z (fold_left (fun x e => gg_sg e x) (filt_on gev gg_reg 1 [G1; G2]) (s 1)) = (false, true).
Proof.
  split; [exact gg_paper |]. split; [exact gg_c1 |]. split; [exact gg_c2 |].
  split; [vm_compute; reflexivity |]. split; vm_compute; reflexivity.
Qed.

(* Non-vacuity of lem:authority (a): in the audit federation the source's component of a
   federated normal form is the unique normal form of the source's own GRS. *)
Theorem fed_lem_authority_a_instance :
  star (step ce_eq (capp (bool * nat) cev ce_reg ce_sig 0) (sp_rho 0) (sp_valid 0) free_enabled)
    ((false, 0), [CRecall]) ((true, 0), []) /\
  normal_form (step ce_eq (capp (bool * nat) cev ce_reg ce_sig 0) (sp_rho 0) (sp_valid 0) free_enabled)
    ((true, 0), []) /\
  (forall m, star (step ce_eq (capp (bool * nat) cev ce_reg ce_sig 0) (sp_rho 0) (sp_valid 0) free_enabled)
               ((false, 0), [CRecall]) m ->
     normal_form (step ce_eq (capp (bool * nat) cev ce_reg ce_sig 0) (sp_rho 0) (sp_valid 0) free_enabled) m ->
     m = ((true, 0), [])).
Proof.
  destruct au_paths as [_ [S1 _]].
  exact (fed_lem_authority_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp_vdec 2 (false, 0) range2 ce_eq
           (tree_net _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ au_paper) 0 (or_introl eq_refl) eq_refl
           au_s0 [CRecall; CSell] au_nf1 S1 (au_valid au_nf1 (or_intror (or_introl eq_refl)))).
Qed.
