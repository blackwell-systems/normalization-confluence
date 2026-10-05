(* CvRDTExact.v: state-based CRDT merges as an instance of the exact theorems, and the exact
   converse. Axiom-free. Closes REGIME-AUDIT section 4, row "State-based: convergence of merges"
   (gap 7).

   CRDT.v proves the sufficient direction for a state-based CRDT (CvRDT): with a commutative,
   associative, idempotent join, merges in any order converge (cvrdt_SEC) and a duplicate merge
   is absorbed (cvrdt_absorbs_duplicates). This file places that model under the exact theorems
   of the single registry (GovernanceConverse.cc_exact_from, GovernanceWFConverse.
   canonical_cc_exact_from) and of at-least-once delivery (AtLeastOnceExact.alo_exact), and proves
   the exact converse: which compensation-free registries converge under every order and every
   duplication.

   Setting. A compensation-free registry: every state is valid, compensation is the identity, so
   the governed step of an event e is the raw action act e. A CvRDT is the instance with events
   the payload states x and act x s = join s x (CRDT.merge). Ev (written X) is the set of events
   in range, s0 the start state. Reach s0 s: s = runT act u s0 for some delivery u over X
   (duplicates allowed).

   Part 1. The compensation-free single registry (Governance Rewrite System, free delivery).
   - cf_cc_exact_from: every event buffer from s0 has a unique normal form IFF the actions commute
     at every state reachable from s0 (CC2 is vacuous; an instance of canonical_cc_exact_from,
     with rho_star the identity). cf_cc_exact_from_wfc: the same through cc_exact_from (the WFC
     form, with the zero potential). cf_reach_iff: the registry's reachable states are exactly
     the runs from s0.
   - cf_star_run: a buffer B reaches (runT act B' s0, []) for every permutation B' of B; so unique
     normal forms give order independence (cf_un_perm).

   Part 2. The exact converse, for any compensation-free registry (section Converse).
   - MergeConv s0: every two deliveries over X with the same SET of events (any order, any
     duplication) reach the same state from s0.
   - mergeconv_alo: MergeConv s0 <-> AtLeastOnceExact.ALOConv act X s0.
   - merge_conv_alo_exact: MergeConv s0 <-> CommReach /\ IdemReach (alo_exact's conditions).
   - merge_action_exact (the action form): MergeConv s0 IFF the action is commutative and
     idempotent at every reachable state: act y (act x s) = act x (act y s) and
     act x (act x s) = act x s for Reach s0 s, X x, X y. That is, the actions of X restricted to
     the reachable states are an action of the free semilattice on X.
   - CvRDTOn s0: there is a binary operation j that is a join-semilattice on the reachable states
     (closed, commutative, associative, idempotent there) such that every event in range acts as
     a join with a fixed state: act e s = j s (act e s0) for reachable s. This is the precise
     sense of "is a state-based CRDT": on its reachable states, with payload e read as the state
     iota e = act e s0.
   - cvrdt_on_conv: CvRDTOn s0 -> MergeConv s0 (no hypothesis).
   - conv_cvrdt_on: MergeConv s0 -> CvRDTOn s0, when X is finite (listed by xs) and state
     equality is decidable (so the join can be computed without choice: j s t merges into s the
     events of a subset of xs that reaches t).
   - cvrdt_on_exact: under those two qualifiers, MergeConv s0 <-> CvRDTOn s0. Together with
     merge_action_exact: converge under every order and duplication <-> commutative and
     idempotent action at reachable states <-> a state-based CRDT on the reachable states.
   - cvrdt_on_inflationary: in that representation each event is inflationary in the join order.

   Part 3. The CvRDT instance (section CvRDTInstance; join commutative, associative,
   idempotent).
   - cvrdt_action: the action is commutative and idempotent at every state.
   - cvrdt_cc: CC1 holds at every state (so CC holds at reachable states for every s0);
     cvrdt_unique_normal_forms: every buffer from every state has a unique normal form, through
     cf_cc_exact_from. cvrdt_SEC_via_cc: CRDT.cvrdt_SEC recovered through the registry's exact
     theorem.
   - cvrdt_alo: at-least-once convergence from every s0 over every X, through alo_exact.
     cvrdt_merge_conv: MergeConv through merge_action_exact.
   - cvrdt_SEC_recovered: CRDT.cvrdt_SEC recovered through MergeConv; cvrdt_set_SEC strengthens it
     (same event set, any duplication, not only a permutation).
   - cvrdt_absorbs_duplicates_recovered: CRDT.cvrdt_absorbs_duplicates recovered through
     AtLeastOnceExact.alo_idem_reachable.
   - cvrdt_on_join: CvRDTOn holds with j = join itself, for every s0 and X (no finiteness).
   - cvrdt_causal_cmrdt, cvrdt_compensation_free: under causal delivery the merges also satisfy
     the op-based condition of CausalReplay.compensation_free_exact.

   Part 4. The monotone regime. A CvRDT is the compensation-free monotone case: with
   le a b := join a b = b, every merge is inflationary and monotone (merge_inflationary,
   merge_monotone), and the state a delivery reaches is the least upper bound of s0 and the
   delivered payloads (run_upper, run_least), equivalently the least common fixed point above s0
   of the delivered merges (cvrdt_lfp): the least-fixed-point characterization of the monotone
   regime, reached with nothing to repair.

   Counterexamples (the naive iffs are false).
   - naive_cvrdt_iff_fails: "MergeConv from s0 iff the merge m (act x s = m s x) is a
     join-semilattice on S" is false. ignore_conv: m s x = s converges from every s0 for every X,
     but m is not commutative (ignore_not_comm); it is still CvRDTOn (ignore_cvrdt_on: its
     reachable set is {s0}). zero_conv: m s x = 0 converges but m is not idempotent
     (zero_not_idem). The semilattice laws of the merge itself are sufficient, not necessary.
   - clamp_reach_qualifier: the reachability qualifier is needed. On nat with X = {x <= 5},
     act x s = max s x when s <= 5 and s + x otherwise: MergeConv from 0 holds, but the action is
     not idempotent at the unreachable state 6 and MergeConv from 6 fails.
   - add_cc_not_alo: the idempotence clause is needed and is not implied by the registry's exact
     condition. act x s = s + x (a counter without idempotence): every buffer has a unique normal
     form from every state (cf_cc_exact_from holds), yet duplication diverges (MergeConv 0
     fails).
   - lww_not_conv: the commutation clause is needed. act x s = x (overwrite) is idempotent at
     every state, yet MergeConv fails.

   Non-vacuity: max-register (maxreg_exact), a two-replica G-Counter as the pointwise max on nat * nat
   (gcounter_exact), and a grow-only set as a bitset with union Nat.lor (gset_exact), each with
   MergeConv, CvRDTOn, at-least-once convergence and unique normal forms. *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Trace.
Require NC.Governance NC.GovernanceConverse NC.GovernanceWFConverse.
Require NC.Checker NC.CRDT NC.CausalReplay NC.AtLeastOnce NC.AtLeastOnceExact.
Import ListNotations.

(* ============================================================================================ *)
(* Part 1. The compensation-free single registry.                                               *)
(* ============================================================================================ *)

Section CompFree.
  Context {S E : Type}.
  Variable dec : forall a b : E, {a = b} + {a <> b}.
  Variable act : E -> S -> S.

  Local Notation fstep :=
    (NC.Governance.step dec act (fun s : S => s) (fun _ : S => True) NC.GovernanceConverse.free_enabled).
  Local Notation creach := (NC.GovernanceConverse.reach act (fun s : S => s) (fun _ : S => True)).
  Local Notation run := (runT act).

  Lemma cf_rho_star_reach : forall sigma B, star fstep (sigma, B) (sigma, B).
  Proof. intros. apply star_refl. Qed.

  Lemma cf_valid : forall sigma : S, (fun _ : S => True) ((fun s : S => s) sigma).
  Proof. intros. exact I. Qed.

  (* The single-registry exact theorem, compensation-free: unique normal forms for every buffer
     from s0 iff the actions commute at every state reachable from s0. *)
  Theorem cf_cc_exact_from : forall s0,
    (forall B, NC.GovernanceConverse.UN fstep (s0, B)) <->
    (forall sigma e1 e2, creach s0 sigma -> act e2 (act e1 sigma) = act e1 (act e2 sigma)).
  Proof.
    intros s0. rewrite (NC.GovernanceWFConverse.canonical_cc_exact_from dec act (fun s => s) (fun s => s)
                          (fun _ => True) cf_rho_star_reach cf_valid s0).
    split; [intros [H _]; exact H |]. intros H. split; [exact H |].
    intros sigma e _ Hinv. exfalso. exact (Hinv I).
  Qed.

  (* The same through cc_exact_from (the WFC form; the potential is zero, WFC is vacuous). *)
  Theorem cf_cc_exact_from_wfc : forall s0,
    (forall B, NC.GovernanceConverse.UN fstep (s0, B)) <->
    (forall sigma e1 e2, creach s0 sigma -> act e2 (act e1 sigma) = act e1 (act e2 sigma)).
  Proof.
    intros s0. rewrite (NC.GovernanceConverse.cc_exact_from dec act (fun s => s) (fun s => s)
                          (fun _ => True) (fun _ => 0) (fun sigma H => False_ind _ (H I))
                          cf_rho_star_reach cf_valid s0).
    split; [intros [H _]; exact H |]. intros H. split; [exact H |].
    intros sigma e _ Hinv. exfalso. exact (Hinv I).
  Qed.

  Lemma cf_reach_run : forall s0 u s, creach s0 s -> creach s0 (run u s).
  Proof.
    intros s0 u. induction u as [| x u IH]; intros s Hs; [exact Hs |].
    rewrite runT_cons. apply IH. apply NC.GovernanceConverse.r_apply. exact Hs.
  Qed.

  (* The registry's reachable states are exactly the runs from s0. *)
  Theorem cf_reach_iff : forall s0 s, creach s0 s <-> exists u, run u s0 = s.
  Proof.
    intros s0 s. split.
    - intros H. induction H as [| e s _ [u IH] | s _ _ Hinv].
      + exists []. reflexivity.
      + exists (u ++ [e]). rewrite runT_app, IH. reflexivity.
      + exfalso. exact (Hinv I).
    - intros [u <-]. apply cf_reach_run. apply NC.GovernanceConverse.r_init.
  Qed.

  Lemma perm_remove1 : forall e B, In e B -> Permutation B (e :: NC.Governance.remove1 dec e B).
  Proof.
    intros e B. induction B as [| x B IH]; intros Hin; [destruct Hin |]. simpl.
    destruct (dec x e) as [-> | Hne]; [apply Permutation_refl |].
    destruct Hin as [-> | Hin]; [exfalso; apply Hne; reflexivity |].
    apply (Permutation_trans (l' := x :: e :: NC.Governance.remove1 dec e B)).
    - apply perm_skip. exact (IH Hin).
    - apply perm_swap.
  Qed.

  (* A buffer can be delivered in the order of any permutation of it. *)
  Lemma cf_star_run : forall B' B s, Permutation B B' -> star fstep (s, B) (run B' s, []).
  Proof.
    induction B' as [| e B' IH]; intros B s HP.
    - apply Permutation_sym, Permutation_nil in HP. subst B. apply star_refl.
    - assert (Hin : In e B) by (apply (Permutation_in e (Permutation_sym HP)); left; reflexivity).
      eapply star_step.
      + apply (NC.Governance.st_apply dec act (fun s : S => s) (fun _ : S => True)
                 NC.GovernanceConverse.free_enabled s B e Hin Hin).
      + rewrite runT_cons. apply IH.
        apply (Permutation_cons_inv (a := e)).
        apply (Permutation_trans (Permutation_sym (perm_remove1 e B Hin))). exact HP.
  Qed.

  Lemma cf_nf_empty : forall t, normal_form fstep (t, []).
  Proof.
    intros t [y H]. inversion H as [s B e Hin _ Q1 Q2 | s B Hinv Q1 Q2]; subst.
    - destruct Hin.
    - exact (Hinv I).
  Qed.

  (* Unique normal forms give order independence of permuted deliveries. *)
  Theorem cf_un_perm : forall s0 B1 B2, NC.GovernanceConverse.UN fstep (s0, B1) ->
    Permutation B1 B2 -> run B1 s0 = run B2 s0.
  Proof.
    intros s0 B1 B2 H HP.
    pose proof (H _ _ (cf_star_run B1 B1 s0 (Permutation_refl _)) (cf_nf_empty _)
                      (cf_star_run B2 B1 s0 HP) (cf_nf_empty _)) as Q.
    injection Q. auto.
  Qed.
End CompFree.

(* ============================================================================================ *)
(* Part 2. The exact converse for any compensation-free registry.                               *)
(* ============================================================================================ *)

Section Converse.
  Context {S E : Type}.
  Variable dec : forall a b : E, {a = b} + {a <> b}.
  Variable act : E -> S -> S.
  Variable X : E -> Prop.

  Local Notation run := (runT act).

  (* Convergence under every order and every duplication: deliveries with the same event set
     reach the same state. *)
  Definition MergeConv (s0 : S) : Prop :=
    forall d1 d2, Forall X d1 -> Forall X d2 -> (forall x, In x d1 <-> In x d2) ->
      run d1 s0 = run d2 s0.

  (* States reachable from s0 by a delivery over X (duplicates allowed). *)
  Definition Reach (s0 s : S) : Prop := exists u, Forall X u /\ run u s0 = s.

  (* The action is commutative and idempotent at reachable states. *)
  Definition ActComm (s0 : S) : Prop :=
    forall s x y, Reach s0 s -> X x -> X y -> act y (act x s) = act x (act y s).
  Definition ActIdem (s0 : S) : Prop :=
    forall s x, Reach s0 s -> X x -> act x (act x s) = act x s.

  Lemma Forall_snoc : forall (u : list E) x, Forall X u -> X x -> Forall X (u ++ [x]).
  Proof. intros u x Hu Hx. apply Forall_app. split; [exact Hu | constructor; [exact Hx | constructor]]. Qed.

  Lemma Forall_snoc2 : forall (u : list E) x y, Forall X u -> X x -> X y -> Forall X (u ++ [x; y]).
  Proof.
    intros u x y Hu Hx Hy. apply Forall_app.
    split; [exact Hu | constructor; [exact Hx | constructor; [exact Hy | constructor]]].
  Qed.

  Lemma reach_init : forall s0, Reach s0 s0.
  Proof. intros s0. exists []. split; [constructor | reflexivity]. Qed.

  Lemma reach_act : forall s0 s e, Reach s0 s -> X e -> Reach s0 (act e s).
  Proof.
    intros s0 s e [u [Hu <-]] He. exists (u ++ [e]). split; [apply Forall_snoc; assumption |].
    rewrite runT_app. reflexivity.
  Qed.

  Lemma reach_run : forall s0 s v, Reach s0 s -> Forall X v -> Reach s0 (run v s).
  Proof.
    intros s0 s v [u [Hu <-]] Hv. exists (u ++ v). split; [apply Forall_app; split; assumption |].
    rewrite runT_app. reflexivity.
  Qed.

  (* MergeConv is AtLeastOnceExact's at-least-once convergence. *)
  Theorem mergeconv_alo : forall s0, MergeConv s0 <-> NC.AtLeastOnceExact.ALOConv act X s0.
  Proof.
    intros s0. split.
    - intros H d o Hd Hnd Heq. apply H; [exact Hd | |].
      + apply Forall_forall. intros x Hx. rewrite Forall_forall in Hd. apply Hd. apply Heq. exact Hx.
      + intros x. symmetry. apply Heq.
    - intros H d1 d2 H1 H2 Heq.
      rewrite (H d1 (NC.AtLeastOnce.dedup dec d1) H1 (NC.AtLeastOnce.dedup_NoDup dec d1)
                 (NC.AtLeastOnce.dedup_In dec d1)).
      symmetry. apply H; [exact H2 | apply NC.AtLeastOnce.dedup_NoDup |].
      intros x. rewrite NC.AtLeastOnce.dedup_In. apply Heq.
  Qed.

  (* Through alo_exact: the exact conditions of at-least-once delivery. *)
  Theorem merge_conv_alo_exact : forall s0,
    MergeConv s0 <->
    NC.AtLeastOnceExact.CommReach act X s0 /\ forall a, NC.AtLeastOnceExact.IdemReach act X s0 a.
  Proof.
    intros s0. rewrite mergeconv_alo. exact (NC.AtLeastOnceExact.alo_exact dec act X s0).
  Qed.

  (* The action form: convergence under every order and duplication iff the action is
     commutative and idempotent at every reachable state. *)
  Theorem merge_action_exact : forall s0, MergeConv s0 <-> ActComm s0 /\ ActIdem s0.
  Proof.
    intros s0. split.
    - intros H. split.
      + intros s x y [u [Hu <-]] Hx Hy.
        pose proof (H (u ++ [x; y]) (u ++ [y; x]) (Forall_snoc2 u x y Hu Hx Hy)
                      (Forall_snoc2 u y x Hu Hy Hx)) as Eq.
        rewrite !runT_app in Eq. apply Eq. intros z. rewrite !in_app_iff. simpl. tauto.
      + intros s x [u [Hu <-]] Hx.
        pose proof (H (u ++ [x; x]) (u ++ [x]) (Forall_snoc2 u x x Hu Hx Hx) (Forall_snoc u x Hu Hx))
          as Eq.
        rewrite !runT_app in Eq. apply Eq. intros z. rewrite !in_app_iff. simpl. tauto.
    - intros [HC HI]. apply (proj2 (merge_conv_alo_exact s0)). split.
      + intros p a b Hev _ _. apply Forall_app in Hev. destruct Hev as [Hp Hab].
        inversion Hab as [| ? ? Ha Hb' Q1]; subst. inversion Hb' as [| ? ? Hb Q2]; subst.
        apply HC; [exists p; split; [exact Hp | reflexivity] | exact Ha | exact Hb].
      + intros a u Hev _. apply Forall_app in Hev. destruct Hev as [Hu Ha].
        inversion Ha as [| ? ? Ha' Q1]; subst.
        apply HI; [exists u; split; [exact Hu | reflexivity] | exact Ha'].
  Qed.

  (* ----- the semilattice representation ----- *)

  Definition SemilatticeOn (R : S -> Prop) (j : S -> S -> S) : Prop :=
    (forall s t, R s -> R t -> R (j s t)) /\
    (forall s t, R s -> R t -> j s t = j t s) /\
    (forall s t r, R s -> R t -> R r -> j (j s t) r = j s (j t r)) /\
    (forall s, R s -> j s s = s).

  (* A state-based CRDT on the reachable states: a join-semilattice there, with every event in
     range acting as a join with the fixed state act e s0. *)
  Definition CvRDTOn (s0 : S) : Prop :=
    exists j, SemilatticeOn (Reach s0) j /\
      forall s e, Reach s0 s -> X e -> act e s = j s (act e s0).

  Theorem cvrdt_on_conv : forall s0, CvRDTOn s0 -> MergeConv s0.
  Proof.
    intros s0 [j [[Hcl [Hcm [Has Hid]]] Hm]]. apply merge_action_exact.
    assert (Hi : forall e, X e -> Reach s0 (act e s0)) by (intros e He; exact (reach_act s0 s0 e (reach_init s0) He)).
    split.
    - intros s x y Hs Hx Hy.
      rewrite (Hm (act x s) y (reach_act s0 s x Hs Hx) Hy), (Hm (act y s) x (reach_act s0 s y Hs Hy) Hx).
      rewrite (Hm s x Hs Hx), (Hm s y Hs Hy).
      rewrite (Has s _ _ Hs (Hi x Hx) (Hi y Hy)), (Has s _ _ Hs (Hi y Hy) (Hi x Hx)).
      rewrite (Hcm _ _ (Hi x Hx) (Hi y Hy)). reflexivity.
    - intros s x Hs Hx.
      rewrite (Hm (act x s) x (reach_act s0 s x Hs Hx) Hx), (Hm s x Hs Hx).
      rewrite (Has s _ _ Hs (Hi x Hx) (Hi x Hx)), (Hid _ (Hi x Hx)). reflexivity.
  Qed.

  (* In the representation, each event is inflationary in the join order. *)
  Theorem cvrdt_on_inflationary : forall s0 j, SemilatticeOn (Reach s0) j ->
    (forall s e, Reach s0 s -> X e -> act e s = j s (act e s0)) ->
    forall s e, Reach s0 s -> X e -> j s (act e s) = act e s.
  Proof.
    intros s0 j [Hcl [Hcm [Has Hid]]] Hm s e Hs He.
    assert (Hi : Reach s0 (act e s0)) by exact (reach_act s0 s0 e (reach_init s0) He).
    rewrite (Hm s e Hs He). rewrite <- (Has s s _ Hs Hs Hi). rewrite (Hid s Hs). reflexivity.
  Qed.

  (* ----- the converse construction: finite X, decidable state equality ----- *)

  Fixpoint subseqs (l : list E) : list (list E) :=
    match l with
    | [] => [[]]
    | x :: r => subseqs r ++ map (cons x) (subseqs r)
    end.

  Lemma subseqs_incl : forall l v, In v (subseqs l) -> incl v l.
  Proof.
    induction l as [| x l IH]; simpl; intros v Hv.
    - destruct Hv as [<- | []]. intros z [].
    - apply in_app_or in Hv. destruct Hv as [Hv | Hv].
      + intros z Hz. right. exact (IH v Hv z Hz).
      + apply in_map_iff in Hv. destruct Hv as [w [<- Hw]].
        intros z [<- | Hz]; [left; reflexivity | right; exact (IH w Hw z Hz)].
  Qed.

  Lemma filter_subseqs : forall (f : E -> bool) l, In (filter f l) (subseqs l).
  Proof.
    intros f. induction l as [| x l IH]; simpl; [left; reflexivity |].
    destruct (f x); apply in_or_app; [right; apply in_map; exact IH | left; exact IH].
  Qed.

  Fixpoint findl {A : Type} (p : A -> bool) (l : list A) : option A :=
    match l with
    | [] => None
    | x :: r => if p x then Some x else findl p r
    end.

  Lemma findl_some : forall {A : Type} (p : A -> bool) l x, findl p l = Some x -> In x l /\ p x = true.
  Proof.
    intros A p l. induction l as [| y l IH]; intros x H; simpl in H; [discriminate H |].
    destruct (p y) eqn:Ep.
    - injection H as <-. split; [left; reflexivity | exact Ep].
    - destruct (IH x H) as [Hin Hp]. split; [right; exact Hin | exact Hp].
  Qed.

  Lemma findl_none : forall {A : Type} (p : A -> bool) l, findl p l = None -> forall x, In x l -> p x = false.
  Proof.
    intros A p l. induction l as [| y l IH]; intros H x Hx; [destruct Hx |]. simpl in H.
    destruct (p y) eqn:Ep; [discriminate H |].
    destruct Hx as [<- | Hx]; [exact Ep | exact (IH H x Hx)].
  Qed.

  Section Finite.
    Variable xs : list E.
    Hypothesis X_xs : forall e, X e <-> In e xs.
    Variable Sdec : forall a b : S, {a = b} + {a <> b}.
    Variable s0 : S.

    (* A subset of xs whose run from s0 reaches t, if there is one. *)
    Definition pick (t : S) : option (list E) :=
      findl (fun v => if Sdec (run v s0) t then true else false) (subseqs xs).

    (* The join on reachable states: merge into s the events of a subset that reaches t. *)
    Definition jn (s t : S) : S :=
      match pick t with Some v => run v s | None => s end.

    Lemma subseqs_X : forall v, In v (subseqs xs) -> Forall X v.
    Proof.
      intros v Hv. apply Forall_forall. intros z Hz. apply X_xs. exact (subseqs_incl xs v Hv z Hz).
    Qed.

    Hypothesis Hconv : MergeConv s0.

    Lemma mc_swap : forall a b, Forall X a -> Forall X b -> run (a ++ b) s0 = run (b ++ a) s0.
    Proof.
      intros a b Ha Hb. apply Hconv; [apply Forall_app; split; assumption | apply Forall_app; split; assumption |].
      intros z. rewrite !in_app_iff. tauto.
    Qed.

    Lemma pick_spec : forall t, Reach s0 t ->
      exists v, Forall X v /\ run v s0 = t /\ forall s, jn s t = run v s.
    Proof.
      intros t [u [Hu <-]]. unfold jn. destruct (pick (run u s0)) as [v |] eqn:Ep.
      - unfold pick in Ep. apply findl_some in Ep. destruct Ep as [Hin Hp].
        destruct (Sdec (run v s0) (run u s0)) as [Eq | _]; [| discriminate Hp].
        exists v. split; [exact (subseqs_X v Hin) | split; [exact Eq | reflexivity]].
      - exfalso. unfold pick in Ep.
        set (v0 := filter (fun e => if in_dec dec e u then true else false) xs).
        pose proof (findl_none _ _ Ep v0 (filter_subseqs _ xs)) as Hn. simpl in Hn.
        destruct (Sdec (run v0 s0) (run u s0)) as [_ | Ne]; [discriminate Hn |]. apply Ne.
        apply Hconv; [exact (subseqs_X v0 (filter_subseqs _ xs)) | exact Hu |].
        intros z. unfold v0. rewrite filter_In. destruct (in_dec dec z u) as [Hz | Hz].
        + split; [intros _; exact Hz | intros _; split; [| reflexivity]].
          apply X_xs. rewrite Forall_forall in Hu. exact (Hu z Hz).
        + split; [intros [_ F]; discriminate F | intros H; contradiction].
    Qed.

    Theorem conv_cvrdt_on : CvRDTOn s0.
    Proof.
      exists jn. split; [split; [| split; [| split]] |].
      - intros s t Hs Ht. destruct (pick_spec t Ht) as [v [Hv [_ Hj]]]. rewrite Hj.
        exact (reach_run s0 s v Hs Hv).
      - intros s t Hs Ht.
        destruct (pick_spec s Hs) as [vs [Hvs [Es Hjs]]]. destruct (pick_spec t Ht) as [vt [Hvt [Et Hjt]]].
        rewrite Hjt, Hjs. rewrite <- Es, <- Et.
        rewrite <- (runT_app act vs vt s0), <- (runT_app act vt vs s0).
        exact (mc_swap vs vt Hvs Hvt).
      - intros s t r Hs Ht Hr.
        destruct (pick_spec s Hs) as [vs [Hvs [Es Hjs]]].
        destruct (pick_spec t Ht) as [vt [Hvt [Et Hjt]]].
        destruct (pick_spec r Hr) as [vr [Hvr [Er Hjr]]].
        assert (Htr : Reach s0 (jn t r)) by (rewrite Hjr; exact (reach_run s0 t vr Ht Hvr)).
        destruct (pick_spec (jn t r) Htr) as [w [Hw [Ew Hjw]]].
        transitivity (run (vs ++ vt ++ vr) s0).
        + rewrite Hjr, Hjt, <- Es, (runT_app act vs (vt ++ vr) s0), (runT_app act vt vr). reflexivity.
        + rewrite Hjw, <- Es. rewrite <- (runT_app act vs w s0), (mc_swap vs w Hvs Hw).
          rewrite (runT_app act w vs s0), Ew, Hjr, <- Et.
          rewrite <- (runT_app act vt vr s0), <- (runT_app act (vt ++ vr) vs s0).
          apply mc_swap; [exact Hvs | apply Forall_app; split; assumption].
      - intros s Hs. destruct (pick_spec s Hs) as [vs [Hvs [Es Hjs]]].
        rewrite Hjs. transitivity (run vs (run vs s0)); [rewrite Es; reflexivity |].
        rewrite <- (runT_app act vs vs s0). rewrite <- Es.
        apply Hconv; [apply Forall_app; split; assumption | exact Hvs |].
        intros z. rewrite in_app_iff. tauto.
      - intros s e Hs He. destruct Hs as [u [Hu <-]].
        assert (Hi : Reach s0 (act e s0)) by exact (reach_act s0 s0 e (reach_init s0) He).
        assert (He' : Forall X [e]) by exact (Forall_cons _ He (Forall_nil _)).
        destruct (pick_spec _ Hi) as [w [Hw [Ew Hjw]]]. rewrite Hjw.
        rewrite <- (runT_app act u w s0), (mc_swap u w Hu Hw), (runT_app act w u s0), Ew.
        change (act e s0) with (run [e] s0). rewrite <- (runT_app act [e] u s0).
        rewrite <- (mc_swap u [e] Hu He'), (runT_app act u [e] s0). reflexivity.
    Qed.

    (* The exact characterization: converge under every order and duplication iff a state-based
       CRDT on the reachable states. *)
    Theorem cvrdt_on_exact : MergeConv s0 <-> CvRDTOn s0.
    Proof. split; [intros _; exact conv_cvrdt_on | apply cvrdt_on_conv]. Qed.
  End Finite.

  (* The three equivalent forms, with the qualifiers of the representation stated. *)
  Theorem cvrdt_exact_all : forall xs, (forall e, X e <-> In e xs) ->
    (forall a b : S, {a = b} + {a <> b}) -> forall s0,
    (MergeConv s0 <-> ActComm s0 /\ ActIdem s0) /\ (MergeConv s0 <-> CvRDTOn s0).
  Proof.
    intros xs Hxs Sdec s0. split; [apply merge_action_exact |].
    split; [intros H; exact (conv_cvrdt_on xs Hxs Sdec s0 H) | apply cvrdt_on_conv].
  Qed.
End Converse.

Arguments MergeConv {S E} act X s0.
Arguments Reach {S E} act X s0 s.
Arguments ActComm {S E} act X s0.
Arguments ActIdem {S E} act X s0.
Arguments SemilatticeOn {S} R j.
Arguments CvRDTOn {S E} act X s0.

(* ============================================================================================ *)
(* Part 3. The CvRDT instance: a join-semilattice.                                               *)
(* ============================================================================================ *)

Section CvRDTInstance.
  Context {S : Type}.
  Variable Sdec : forall a b : S, {a = b} + {a <> b}.
  Variable join : S -> S -> S.
  Hypothesis join_comm  : forall a b, join a b = join b a.
  Hypothesis join_assoc : forall a b c, join (join a b) c = join a (join b c).
  Hypothesis join_idem  : forall a, join a a = a.

  Local Notation mrg := (NC.CRDT.merge join).
  Local Notation run := (runT mrg).
  Local Notation fstep :=
    (NC.Governance.step Sdec mrg (fun s : S => s) (fun _ : S => True) NC.GovernanceConverse.free_enabled).

  Lemma mrg_comm : forall x y s, mrg y (mrg x s) = mrg x (mrg y s).
  Proof.
    intros x y s. unfold NC.CRDT.merge. rewrite !join_assoc. rewrite (join_comm y x). reflexivity.
  Qed.

  Lemma mrg_idem : forall x s, mrg x (mrg x s) = mrg x s.
  Proof. intros x s. unfold NC.CRDT.merge. rewrite join_assoc, join_idem. reflexivity. Qed.

  (* The action is commutative and idempotent at every state, so for every s0 and X. *)
  Theorem cvrdt_action : forall (X : S -> Prop) s0, ActComm mrg X s0 /\ ActIdem mrg X s0.
  Proof. intros X s0. split; [intros s x y _ _ _; apply mrg_comm | intros s x _ _; apply mrg_idem]. Qed.

  (* Converges under every order and duplication, through the action form of the exact
     theorem. *)
  Theorem cvrdt_merge_conv : forall (X : S -> Prop) s0, MergeConv mrg X s0.
  Proof. intros X s0. apply (proj2 (merge_action_exact Sdec mrg X s0)). apply cvrdt_action. Qed.

  (* At-least-once convergence, through alo_exact: joins commute and are idempotent. *)
  Theorem cvrdt_alo : forall (X : S -> Prop) s0, NC.AtLeastOnceExact.ALOConv mrg X s0.
  Proof.
    intros X s0. apply (proj2 (NC.AtLeastOnceExact.alo_exact Sdec mrg X s0)). split.
    - intros p a b _ _ _. apply mrg_comm.
    - intros a u _ _. apply mrg_idem.
  Qed.

  (* CC1 at every state; CC2 is vacuous (nothing is invalid). *)
  Theorem cvrdt_cc : forall s0 sigma e1 e2,
    NC.GovernanceConverse.reach mrg (fun s : S => s) (fun _ : S => True) s0 sigma ->
    mrg e2 (mrg e1 sigma) = mrg e1 (mrg e2 sigma).
  Proof. intros. apply mrg_comm. Qed.

  (* Unique normal forms for every buffer from every state, through the registry's exact
     theorem. *)
  Theorem cvrdt_unique_normal_forms : forall s0 B, NC.GovernanceConverse.UN fstep (s0, B).
  Proof. intros s0. apply (proj2 (cf_cc_exact_from Sdec mrg s0)). apply cvrdt_cc. Qed.

  (* CRDT.cvrdt_SEC, recovered through the registry's exact theorem. *)
  Theorem cvrdt_SEC_via_cc : forall xs1 xs2, Permutation xs1 xs2 ->
    forall s, NC.Checker.run mrg xs1 s = NC.Checker.run mrg xs2 s.
  Proof.
    intros xs1 xs2 HP s. exact (cf_un_perm Sdec mrg s xs1 xs2 (cvrdt_unique_normal_forms s xs1) HP).
  Qed.

  (* Same event set, any order, any duplication: strictly more than cvrdt_SEC. *)
  Theorem cvrdt_set_SEC : forall d1 d2, (forall x, In x d1 <-> In x d2) ->
    forall s, run d1 s = run d2 s.
  Proof.
    intros d1 d2 Heq s. apply (cvrdt_merge_conv (fun _ => True) s);
      [apply Forall_forall; intros; exact I | apply Forall_forall; intros; exact I | exact Heq].
  Qed.

  (* CRDT.cvrdt_SEC, recovered through MergeConv. *)
  Theorem cvrdt_SEC_recovered : forall xs1 xs2, Permutation xs1 xs2 ->
    forall s, NC.Checker.run mrg xs1 s = NC.Checker.run mrg xs2 s.
  Proof.
    intros xs1 xs2 HP s. apply (cvrdt_set_SEC xs1 xs2). intros x.
    split; [apply Permutation_in; exact HP | apply Permutation_in; exact (Permutation_sym HP)].
  Qed.

  (* CRDT.cvrdt_absorbs_duplicates, recovered through alo_idem_reachable. *)
  Theorem cvrdt_absorbs_duplicates_recovered : forall x s, mrg x (mrg x s) = mrg x s.
  Proof.
    intros x s.
    exact (NC.AtLeastOnceExact.alo_idem_reachable Sdec mrg (fun _ => True) s
             (cvrdt_alo (fun _ => True) s) [] x (Forall_nil _) I).
  Qed.

  (* ----- the order and the representation with j = join ----- *)

  Definition le (a b : S) : Prop := join a b = b.

  Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
  Proof. unfold le. intros a b c H1 H2. rewrite <- H2, <- join_assoc, H1. reflexivity. Qed.

  Lemma le_join_l : forall a b, le a (join a b).
  Proof. intros a b. unfold le. rewrite <- join_assoc, join_idem. reflexivity. Qed.

  Lemma le_join_r : forall a b, le b (join a b).
  Proof. intros a b. rewrite (join_comm a b). apply le_join_l. Qed.

  (* Merging is inflationary and monotone: the monotone regime. *)
  Theorem merge_inflationary : forall x s, le s (mrg x s).
  Proof. intros x s. apply le_join_l. Qed.

  Theorem merge_monotone : forall x s t, le s t -> le (mrg x s) (mrg x t).
  Proof.
    intros x s t H. unfold le, NC.CRDT.merge in *.
    rewrite join_assoc, (join_comm x (join t x)), join_assoc, join_idem, <- join_assoc, H.
    reflexivity.
  Qed.

  Lemma run_infl : forall v s, le s (run v s).
  Proof.
    induction v as [| x v IH]; intros s; [apply join_idem |].
    rewrite runT_cons. apply (le_trans _ (mrg x s)); [apply merge_inflationary | apply IH].
  Qed.

  Lemma run_shift : forall v s t, run v (join s t) = join s (run v t).
  Proof.
    induction v as [| x v IH]; intros s t; [reflexivity |].
    rewrite !runT_cons. change (NC.CRDT.merge join x (join s t)) with (join (join s t) x).
    rewrite join_assoc. exact (IH s (join t x)).
  Qed.

  (* The delivered state is an upper bound of s0 and every delivered payload ... *)
  Theorem run_upper : forall d s0, le s0 (run d s0) /\ forall x, In x d -> le x (run d s0).
  Proof.
    intros d s0. split; [apply run_infl |]. intros x Hx. apply in_split in Hx.
    destruct Hx as [l [r ->]]. rewrite runT_app, runT_cons.
    apply (le_trans _ (mrg x (run l s0))); [apply le_join_r | apply run_infl].
  Qed.

  (* ... and below every upper bound: the least upper bound. *)
  Theorem run_least : forall d s0 u, le s0 u -> (forall x, In x d -> le x u) -> le (run d s0) u.
  Proof.
    induction d as [| x d IH]; intros s0 u H0 Hd; [exact H0 |].
    rewrite runT_cons. apply IH; [| intros y Hy; apply Hd; right; exact Hy].
    unfold le, NC.CRDT.merge. rewrite join_assoc. rewrite (Hd x (or_introl eq_refl)). exact H0.
  Qed.

  (* The least-fixed-point form: the delivered state is the least common fixed point above s0 of
     the delivered merges. *)
  Theorem cvrdt_lfp : forall d s0,
    le s0 (run d s0) /\ (forall x, In x d -> mrg x (run d s0) = run d s0) /\
    forall u, le s0 u -> (forall x, In x d -> mrg x u = u) -> le (run d s0) u.
  Proof.
    intros d s0. destruct (run_upper d s0) as [H0 Hd]. split; [exact H0 |]. split.
    - intros x Hx. unfold NC.CRDT.merge. rewrite join_comm. exact (Hd x Hx).
    - intros u Hu Hf. apply run_least; [exact Hu |]. intros x Hx. unfold le.
      rewrite join_comm. exact (Hf x Hx).
  Qed.

  (* CvRDTOn with j = join itself, for every s0 and X: the payload x acts as join with
     act x s0 = join s0 x, and join s0 is absorbed at reachable states. *)
  Theorem cvrdt_on_join : forall (X : S -> Prop) s0, CvRDTOn mrg X s0.
  Proof.
    intros X s0.
    assert (Habs : forall s, Reach mrg X s0 s -> join s s0 = s).
    { intros s [u [_ <-]]. rewrite join_comm. apply run_infl. }
    exists join. split; [split; [| split; [| split]] |].
    - intros s t Hs [v [Hv <-]]. destruct Hs as [u [Hu Es]].
      exists (u ++ v). split; [apply Forall_app; split; assumption |].
      rewrite runT_app, Es. rewrite <- run_shift.
      rewrite (Habs s (ex_intro _ u (conj Hu Es))). reflexivity.
    - intros. apply join_comm.
    - intros. apply join_assoc.
    - intros. apply join_idem.
    - intros s e Hs _. unfold NC.CRDT.merge. rewrite <- join_assoc, (Habs s Hs). reflexivity.
  Qed.

  (* Under causal delivery the merges satisfy the op-based condition, and the governed steps
     (identity normalization) satisfy CausalReplay.compensation_free_exact's left side. *)
  Theorem cvrdt_causal_cmrdt : forall hb, NC.CausalReplay.causal_cmrdt mrg hb.
  Proof. intros hb a b s _. apply mrg_comm. Qed.

  Theorem cvrdt_compensation_free : forall hb a b s, NC.CausalReplay.concurrent hb a b ->
    NC.CausalReplay.gstep mrg (fun s => s) a (NC.CausalReplay.gstep mrg (fun s => s) b s) =
    NC.CausalReplay.gstep mrg (fun s => s) b (NC.CausalReplay.gstep mrg (fun s => s) a s).
  Proof.
    intros hb. apply (proj2 (NC.CausalReplay.compensation_free_exact mrg hb (fun s => s) (fun s => eq_refl))).
    apply cvrdt_causal_cmrdt.
  Qed.
End CvRDTInstance.

(* ============================================================================================ *)
(* Counterexamples.                                                                              *)
(* ============================================================================================ *)

Lemma Forall_True_l : forall {E : Type} (l : list E), Forall (fun _ => True) l.
Proof. intros E l. apply Forall_forall. intros; exact I. Qed.

(* m s x = s: ignores every merge. *)
Definition ignore_act (_ : nat) (s : nat) : nat := s.

Lemma ignore_run : forall u s, runT ignore_act u s = s.
Proof. induction u as [| x u IH]; intros s; [reflexivity | rewrite runT_cons; apply IH]. Qed.

Theorem ignore_conv : forall (X : nat -> Prop) s0, MergeConv ignore_act X s0.
Proof. intros X s0 d1 d2 _ _ _. rewrite !ignore_run. reflexivity. Qed.

Theorem ignore_not_comm : ~ (forall a b, ignore_act b a = ignore_act a b).
Proof. intro H. specialize (H 0 1). discriminate H. Qed.

Theorem ignore_cvrdt_on : forall (X : nat -> Prop) s0, CvRDTOn ignore_act X s0.
Proof.
  intros X s0. exists (fun s _ => s).
  assert (Hr : forall s, Reach ignore_act X s0 s -> s = s0) by (intros s [u [_ <-]]; apply ignore_run).
  split; [split; [| split; [| split]] |].
  - intros s t Hs _. exact Hs.
  - intros s t Hs Ht. rewrite (Hr s Hs), (Hr t Ht). reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

(* m s x = 0: commutative and associative as a binary operation, converges, not idempotent. *)
Definition zero_act (_ : nat) (_ : nat) : nat := 0.

Lemma zero_run0 : forall u, runT zero_act u 0 = 0.
Proof. induction u as [| x u IH]; [reflexivity | rewrite runT_cons; exact IH]. Qed.

Lemma zero_run : forall x u s, runT zero_act (x :: u) s = 0.
Proof. intros x u s. rewrite runT_cons. apply zero_run0. Qed.

Theorem zero_conv : forall (X : nat -> Prop) s0, MergeConv zero_act X s0.
Proof.
  intros X s0 [| a d1] [| b d2] _ _ Heq; try reflexivity.
  - exfalso. apply (proj2 (Heq b)). left. reflexivity.
  - exfalso. apply (proj1 (Heq a)). left. reflexivity.
  - rewrite !zero_run. reflexivity.
Qed.

Theorem zero_not_idem : ~ (forall a, zero_act a a = a).
Proof. intro H. specialize (H 1). discriminate H. Qed.

(* The naive iff (convergence under every order and duplication iff the merge is a
   join-semilattice on the whole state space) is false. *)
Theorem naive_cvrdt_iff_fails :
  ~ (forall (m : nat -> nat -> nat) s0,
       MergeConv (fun x s => m s x) (fun _ => True) s0 <->
       ((forall a b, m a b = m b a) /\ (forall a b c, m (m a b) c = m a (m b c)) /\
        (forall a, m a a = a))).
Proof.
  intro H. destruct (proj1 (H (fun s _ => s) 0) (ignore_conv (fun _ => True) 0)) as [Hc _].
  specialize (Hc 0 1). discriminate Hc.
Qed.

(* The reachability qualifier is needed: a merge that is max on the reachable states and not
   idempotent above them. *)
Definition clamp_act (x s : nat) : nat := if s <=? 5 then Nat.max s x else s + x.
Definition clampX (x : nat) : Prop := x <= 5.

Lemma clamp_low : forall x s, s <= 5 -> clamp_act x s = Nat.max s x.
Proof. intros x s H. unfold clamp_act. rewrite (proj2 (Nat.leb_le s 5) H). reflexivity. Qed.

Lemma clamp_run_low : forall u s, Forall clampX u -> s <= 5 -> runT clamp_act u s <= 5.
Proof.
  induction u as [| x u IH]; intros s Hu Hs; [exact Hs |].
  inversion Hu as [| ? ? Hx Hu' Q1]; subst. rewrite runT_cons. apply IH; [exact Hu' |].
  rewrite (clamp_low x s Hs). unfold clampX in Hx. lia.
Qed.

Lemma clamp_reach : forall s, Reach clamp_act clampX 0 s -> s <= 5.
Proof. intros s [u [Hu <-]]. apply clamp_run_low; [exact Hu | lia]. Qed.

Theorem clamp_reach_qualifier :
  MergeConv clamp_act clampX 0 /\
  ~ (forall s x, clampX x -> clamp_act x (clamp_act x s) = clamp_act x s) /\
  ~ MergeConv clamp_act clampX 6.
Proof.
  split; [| split].
  - apply (proj2 (merge_action_exact Nat.eq_dec clamp_act clampX 0)). split.
    + intros s x y Hs Hx Hy. pose proof (clamp_reach s Hs) as Hs5. unfold clampX in Hx, Hy.
      rewrite (clamp_low x s Hs5), (clamp_low y s Hs5).
      rewrite (clamp_low y (Nat.max s x)) by lia. rewrite (clamp_low x (Nat.max s y)) by lia. lia.
    + intros s x Hs Hx. pose proof (clamp_reach s Hs) as Hs5. unfold clampX in Hx.
      rewrite (clamp_low x s Hs5). rewrite (clamp_low x (Nat.max s x)) by lia. lia.
  - intro H. specialize (H 6 1 ltac:(unfold clampX; lia)). vm_compute in H. discriminate H.
  - intro H. assert (H1 : clampX 1) by (unfold clampX; lia).
    specialize (H [1; 1] [1] (Forall_cons _ H1 (Forall_cons _ H1 (Forall_nil _)))
                  (Forall_cons _ H1 (Forall_nil _))).
    assert (Eq : runT clamp_act [1; 1] 6 = runT clamp_act [1] 6) by (apply H; intros x; simpl; tauto).
    vm_compute in Eq. discriminate Eq.
Qed.

(* The idempotence clause is needed, and is not implied by the registry's exact condition: an
   additive counter has unique normal forms for every buffer from every state, yet duplication
   diverges. *)
Definition add_act (x s : nat) : nat := s + x.

Theorem add_cc_not_alo :
  (forall s0 B, NC.GovernanceConverse.UN
     (NC.Governance.step Nat.eq_dec add_act (fun s : nat => s) (fun _ : nat => True)
        NC.GovernanceConverse.free_enabled) (s0, B)) /\
  ~ ActIdem add_act (fun _ => True) 0 /\
  ~ MergeConv add_act (fun _ => True) 0.
Proof.
  split; [| split].
  - intros s0. apply (proj2 (cf_cc_exact_from Nat.eq_dec add_act s0)).
    intros sigma e1 e2 _. unfold add_act. lia.
  - intro H. specialize (H 0 1 (reach_init add_act (fun _ => True) 0) I). discriminate H.
  - intro H. specialize (H [1; 1] [1] (Forall_True_l _) (Forall_True_l _)).
    assert (Eq : runT add_act [1; 1] 0 = runT add_act [1] 0) by (apply H; intros x; simpl; tauto).
    discriminate Eq.
Qed.

(* The commutation clause is needed: overwrite is idempotent at every state, yet diverges. *)
Definition lww_act (x _ : nat) : nat := x.

Theorem lww_not_conv :
  (forall x s, lww_act x (lww_act x s) = lww_act x s) /\
  ~ ActComm lww_act (fun _ => True) 0 /\
  ~ MergeConv lww_act (fun _ => True) 0.
Proof.
  split; [reflexivity |]. split.
  - intro H. specialize (H 0 1 2 (reach_init lww_act (fun _ => True) 0) I I). discriminate H.
  - intro H. specialize (H [1; 2] [2; 1] (Forall_True_l _) (Forall_True_l _)).
    assert (Eq : runT lww_act [1; 2] 0 = runT lww_act [2; 1] 0) by (apply H; intros x; simpl; tauto).
    discriminate Eq.
Qed.

(* ============================================================================================ *)
(* Non-vacuity: max-register, G-Counter, grow-only set.                                          *)
(* ============================================================================================ *)

(* Everything at once for a join-semilattice. *)
Theorem cvrdt_all : forall {S : Type} (Sdec : forall a b : S, {a = b} + {a <> b}) (join : S -> S -> S),
  (forall a b, join a b = join b a) -> (forall a b c, join (join a b) c = join a (join b c)) ->
  (forall a, join a a = a) ->
  forall (X : S -> Prop) s0,
  MergeConv (NC.CRDT.merge join) X s0 /\ CvRDTOn (NC.CRDT.merge join) X s0 /\
  NC.AtLeastOnceExact.ALOConv (NC.CRDT.merge join) X s0 /\
  forall B, NC.GovernanceConverse.UN
    (NC.Governance.step Sdec (NC.CRDT.merge join) (fun s : S => s) (fun _ : S => True)
       NC.GovernanceConverse.free_enabled) (s0, B).
Proof.
  intros S Sdec join Hc Ha Hi X s0. split; [| split; [| split]].
  - exact (cvrdt_merge_conv Sdec join Hc Ha Hi X s0).
  - exact (cvrdt_on_join join Hc Ha Hi X s0).
  - exact (cvrdt_alo Sdec join Hc Ha Hi X s0).
  - exact (cvrdt_unique_normal_forms Sdec join Hc Ha s0).
Qed.

(* Max-register. *)
Theorem maxreg_exact : forall (X : nat -> Prop) s0,
  MergeConv (NC.CRDT.merge Nat.max) X s0 /\ CvRDTOn (NC.CRDT.merge Nat.max) X s0 /\
  NC.AtLeastOnceExact.ALOConv (NC.CRDT.merge Nat.max) X s0 /\
  forall B, NC.GovernanceConverse.UN
    (NC.Governance.step Nat.eq_dec (NC.CRDT.merge Nat.max) (fun s : nat => s) (fun _ : nat => True)
       NC.GovernanceConverse.free_enabled) (s0, B).
Proof. apply cvrdt_all; intros; lia. Qed.

Example maxreg_dup : runT (NC.CRDT.merge Nat.max) [3; 7; 3; 2; 7] 0 = runT (NC.CRDT.merge Nat.max) [2; 7; 3] 0.
Proof. reflexivity. Qed.

(* G-Counter for two replicas: pointwise max of per-replica counts. *)
Definition gc_join (p q : nat * nat) : nat * nat := (Nat.max (fst p) (fst q), Nat.max (snd p) (snd q)).

Definition gc_dec : forall a b : nat * nat, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Theorem gcounter_exact : forall (X : nat * nat -> Prop) s0,
  MergeConv (NC.CRDT.merge gc_join) X s0 /\ CvRDTOn (NC.CRDT.merge gc_join) X s0 /\
  NC.AtLeastOnceExact.ALOConv (NC.CRDT.merge gc_join) X s0 /\
  forall B, NC.GovernanceConverse.UN
    (NC.Governance.step gc_dec (NC.CRDT.merge gc_join) (fun s : nat * nat => s)
       (fun _ : nat * nat => True) NC.GovernanceConverse.free_enabled) (s0, B).
Proof.
  apply cvrdt_all; unfold gc_join; [intros [a1 a2] [b1 b2] | intros [a1 a2] [b1 b2] [c1 c2] | intros [a1 a2]];
    simpl; f_equal; lia.
Qed.

Example gcounter_dup :
  runT (NC.CRDT.merge gc_join) [(2, 0); (0, 5); (2, 0); (1, 3)] (0, 0) =
  runT (NC.CRDT.merge gc_join) [(1, 3); (0, 5); (2, 0)] (0, 0).
Proof. reflexivity. Qed.

(* Grow-only set (the add-only core of an OR-set) as a bitset; merge is union, Nat.lor. *)
Theorem gset_exact : forall (X : nat -> Prop) s0,
  MergeConv (NC.CRDT.merge Nat.lor) X s0 /\ CvRDTOn (NC.CRDT.merge Nat.lor) X s0 /\
  NC.AtLeastOnceExact.ALOConv (NC.CRDT.merge Nat.lor) X s0 /\
  forall B, NC.GovernanceConverse.UN
    (NC.Governance.step Nat.eq_dec (NC.CRDT.merge Nat.lor) (fun s : nat => s) (fun _ : nat => True)
       NC.GovernanceConverse.free_enabled) (s0, B).
Proof.
  apply cvrdt_all; [apply Nat.lor_comm | intros a b c; first [apply Nat.lor_assoc | symmetry; apply Nat.lor_assoc] | apply Nat.lor_diag].
Qed.

Example gset_dup : runT (NC.CRDT.merge Nat.lor) [1; 4; 1; 2; 4] 0 = runT (NC.CRDT.merge Nat.lor) [2; 1; 4] 0.
Proof. reflexivity. Qed.

(* A finite instance of the converse construction: the clamped merge from 0 over X = {0..5}
   is a state-based CRDT on its reachable states, though not a semilattice on nat. *)
Theorem clamp_cvrdt_on : CvRDTOn clamp_act clampX 0.
Proof.
  apply (conv_cvrdt_on Nat.eq_dec clamp_act clampX [0; 1; 2; 3; 4; 5]).
  - intros e. unfold clampX. simpl. split; [intros H; lia | intros H; repeat destruct H as [<- | H]; try lia; destruct H].
  - exact Nat.eq_dec.
  - exact (proj1 clamp_reach_qualifier).
Qed.
