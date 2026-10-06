(* CompositionalCheck.v: compositional checking by default (roadmap item 8, step 3; gsm roadmap
   item 1c). Check each footprint component on its own subspace, conclude for the registry.
   Axiom-free.

   Model (section Compositional). A registry over a state type St with variables X and values D:
   - state access get : St -> X -> D, a merge mix C s t (s on C, t elsewhere), and state equality
     determined by the variables (StateOK);
   - events A e (the guarded effect: a disabled event is the identity), invariants (chk i, rep i)
     in a declared order, repair one step at a time by the FIRST violated invariant (rho), the
     registry valid when every invariant holds (valid);
   - a partition of the variables into components (blk : X -> K), a set of shared variables (sh),
     and a component for every event (bE) and invariant (bI);
   - footprints: every event has a read set RE and a write set WE, every invariant a check read set
     RC and a repair read set RR and write set WR. Local R W f: f changes only W, and its values on
     W depend only on R. Inside k R W: R lies in component k or the shared variables, W lies in k
     and is not shared. A guarded event's read set contains its guard's reads and, because a
     disabled event leaves its write set unchanged, its write set.
   Hyps bundles these hypotheses. With no shared variables they say exactly what gsm's
   BuildCompositional enforces: each event reads and writes only its footprint (gsm requires reads
   inside the write set), each invariant's check and repair only its footprint, and footprints are
   grouped into components by union-find.

   gsm's guarantee (docs/theory.md 6.5, 9.3). gsm runs eager compensation: the step of event e from
   a valid state is G e s = N (A e s) with N the repair iteration, and the guarantee is that every
   permutation of a list of events from a valid state reaches the same state (Conv; the conclusion
   of Checker.run_perm_invariant over valid states, as AstChecker.check_sound_converges). It checks
   WFC (repair terminates) and CC1 on valid states; it does not check CC2. N is the iteration to a
   repair bound B (WFCb B), as gsm's lazy machine normalizes to the bound BuildCompositional
   computes; N does not depend on the bound once it is one (N_indep, conv_indep).

   Restriction to a component k. Sub k: states that agree with a background state z outside k and
   the shared variables (gsm holds the other variables at zero). The component's registry has the
   invariants of k (invK), repair rhoK by the first violated one, validity validK, normalization NK
   and step GK; WFCk, TermK, CC1K, ConvK are its conditions over Sub k.

   Decomposition (exact).
   - rho_step: one repair step of the registry is one repair step of exactly one component, and
     leaves the others unchanged. iter_proj: every repair run projects to a run of each component.
   - term_iff, wfc_iff: repair terminates from s iff it terminates in each component from the
     restriction of s; the registry has WFC iff every component does (over Sub k). bound_sum: if
     component k terminates within d k steps from every state of Sub k, the registry terminates
     within the sum, which is the bound gsm's lazy machine uses. wfcb_iff: the uniform forms.
   - raw_cross_commute: events in different components commute as raw effects (generalizing
     Gsm.disjoint_events_commute to read and write sets).
   - cc1_cross: events in different components satisfy CC1 at every valid state, with no check.
   - cc1_same_iff, cc1_component: events in the same component k satisfy CC1 at s iff the component
     does at the restriction of s; so CC1 over the valid states of the registry iff over the valid
     states of Sub k.
   - conv_iff_cc1, convK_iff_cc1K: the guarantee is exactly CC1 on valid states (perm_good_iff).
   - compositional_exact: Conv iff ConvK for every component. compositional_gsm: with component
     bounds d k, the registry has WFC within the sum and Conv iff every component's ConvK.
   - comp_check_exact, wfc_check_exact, enum_length: a boolean check that enumerates each
     component's subspace (length |D|^(number of the component's variables), not |D|^|X|)
     decides WFC within the bounds and the guarantee.
   - gsm_literal, gsm_literal_iter, gsm_literal_step: with no shared variables and a valid
     background, the registry's own validity and repair on Sub k are the component's, so gsm's
     component check (global rules evaluated with the other variables at zero) computes exactly
     WFCk and CC1K.

   Shared variables. A variable read by several components is allowed when no event and no repair
   writes it (Inside requires W disjoint from sh); the components' subspaces then include it, and
   every theorem above holds as stated. Writing a shared variable is not: sw_diverges.

   Boundaries (each with every other hypothesis holding, every component's conditions passing, and
   the registry diverging).
   - ws_diverges: footprints with writes only. Pay writes paid, ship writes shipped and its guard
     reads paid; ship's declared footprint omits the read (ws_ship_not_local). inside_merge: once
     reads are in the footprint, the two variables must share a component.
   - rc_diverges: a repair that writes a variable in another component (rc_repair_not_local).
   - sw_diverges: a shared variable written by one component and read by another
     (sw_pay_writes_shared).

   Combinator rules (section AstFootprint, over AstChecker's rule grammar, which models gsm's
   combinators). readsE, readsP, readsT, writesT extract the variables an expression, predicate or
   transform reads and writes, as gsm's vars, readVars and writeVars do. evalE_reads, evalP_reads,
   applyT_writes, applyT_reads, and on fixed-length valuations ast_event_local, ast_check_local,
   ast_repair_local: the extracted sets over-approximate the true ones, so they satisfy Local and
   PLocal. ast_hyps: the induced registry satisfies Hyps whenever the decidable blocks_ok accepts
   the component assignment; ast_rho_repair1 and ast_N_normalize: its repair and normalization are
   AstChecker's. Closures are opaque: gsm tests their footprints by perturbation
   (TrustClosureFootprints), which is not proved here and is a trust boundary.

   Non-vacuity. shop: orders (status, paid; ship forces paid by repair) and inventory (stock,
   reserved, backorder flag recomputed by repair), with or without a shared read-only store-open
   flag read by both components' guards. shop_hyps, shop_check (the boolean check passes),
   shop_converges, shop_repair_fires, shop_cost (36 or 108 enumerated states instead of 729),
   shop_gsm_literal (no shared variable, zero background valid), shop_shared_read. ast_demo: a
   combinator machine accepted by blocks_ok. *)

From Coq Require Import List Arith Lia Bool ZArith.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Logic.Eqdep_dec.
Require NC.AstChecker.
Import ListNotations.

(* ============================================================================================ *)
(* Footprints: a function reads R and writes W.                                                 *)
(* ============================================================================================ *)

Section Footprint.
  Context {X D St : Type}.
  Variable get : St -> X -> D.

  Definition agree (R : X -> bool) (s t : St) : Prop :=
    forall x, R x = true -> get s x = get t x.

  (* f changes only W, and its values on W depend only on R. *)
  Definition Local (R W : X -> bool) (f : St -> St) : Prop :=
    (forall s x, W x = false -> get (f s) x = get s x) /\
    (forall s t, agree R s t -> forall x, W x = true -> get (f s) x = get (f t) x).

  (* p depends only on R. *)
  Definition PLocal (R : X -> bool) (p : St -> bool) : Prop :=
    forall s t, agree R s t -> p s = p t.
End Footprint.

(* ============================================================================================ *)
(* Order independence over a closed set of states: exactly pairwise commutation there.         *)
(* ============================================================================================ *)

Section PermGood.
  Context {S E : Type}.
  Variable g : E -> S -> S.
  Variable P : S -> Prop.
  Variable EP : E -> Prop.
  Hypothesis closed : forall e s, EP e -> P s -> P (g e s).

  Definition runG (l : list E) (s : S) : S := fold_left (fun u e => g e u) l s.

  Lemma Forall_perm : forall (l1 l2 : list E), Permutation l1 l2 -> Forall EP l1 -> Forall EP l2.
  Proof.
    intros l1 l2 Hp H. rewrite Forall_forall in *. intros x Hx.
    apply H. apply (Permutation_in x (Permutation_sym Hp) Hx).
  Qed.

  Theorem perm_good_iff :
    (forall s, P s -> forall l1 l2, Permutation l1 l2 -> Forall EP l1 -> runG l1 s = runG l2 s) <->
    (forall s, P s -> forall e1 e2, EP e1 -> EP e2 -> g e2 (g e1 s) = g e1 (g e2 s)).
  Proof.
    split.
    - intros H s Hs e1 e2 H1 H2.
      exact (H s Hs [e1; e2] [e2; e1] (perm_swap e2 e1 []) (Forall_cons _ H1 (Forall_cons _ H2 (Forall_nil _)))).
    - intros Hc s Hs l1 l2 Hp. revert s Hs.
      induction Hp as [|x l l' Hp IH|x y l|l l' l'' Hp1 IH1 Hp2 IH2]; intros s Hs HF.
      + reflexivity.
      + inversion HF; subst. unfold runG; simpl. apply IH; [apply closed; assumption | assumption].
      + inversion HF as [|a b Hy HF1]; subst. inversion HF1 as [|a b Hx HF2]; subst.
        unfold runG; simpl. rewrite (Hc s Hs y x Hy Hx). reflexivity.
      + rewrite (IH1 s Hs HF). apply IH2; [exact Hs | apply (Forall_perm l l' Hp1 HF)].
  Qed.
End PermGood.

(* ============================================================================================ *)
(* Registries with footprints and components.                                                   *)
(* ============================================================================================ *)

Section Model.
  Context {X D St K E I : Type}.
  Record Reg := mkReg {
    cget : St -> X -> D;
    cmix : (X -> bool) -> St -> St -> St;
    ckeq : forall a b : K, {a = b} + {a <> b};
    cblk : X -> K;
    csh : X -> bool;
    cz : St;
    cA : E -> St -> St;
    cinvs : list I;
    cchk : I -> St -> bool;
    crep : I -> St -> St;
    cbE : E -> K;
    cbI : I -> K;
    cRE : E -> X -> bool;
    cWE : E -> X -> bool;
    cRC : I -> X -> bool;
    cRR : I -> X -> bool;
    cWR : I -> X -> bool }.

  (* Finite descriptions, for the boolean check: decidable variables, a state update, the value
     domain, state equality, each component's variables (its own and the shared ones), the events,
     and the components to check. *)
  Record Fin := mkFin {
    fxeq : forall a b : X, {a = b} + {a <> b};
    fupd : X -> D -> St -> St;
    fallD : list D;
    feqb : St -> St -> bool;
    fvars : K -> list X;
    fevs : list E;
    fKs : list K }.
End Model.
Arguments Reg : clear implicits.
Arguments Fin : clear implicits.

Section Compositional.
  Context {X D St K E I : Type}.
  Variable r : Reg X D St K E I.

  Local Notation get := (cget r).
  Local Notation mix := (cmix r).
  Local Notation keq := (ckeq r).
  Local Notation blk := (cblk r).
  Local Notation sh := (csh r).
  Local Notation z := (cz r).
  Local Notation A := (cA r).
  Local Notation invs := (cinvs r).
  Local Notation chk := (cchk r).
  Local Notation rep := (crep r).
  Local Notation bE := (cbE r).
  Local Notation bI := (cbI r).

  Definition StateOK : Prop :=
    (forall C s t x, get (mix C s t) x = if C x then get s x else get t x) /\
    (forall s t, (forall x, get s x = get t x) -> s = t).

  Definition own (k : K) (x : X) : bool := if keq (blk x) k then true else false.
  Definition home (k : K) (x : X) : bool := own k x || sh x.

  (* R lies in component k or the shared variables; W lies in k and is not shared. *)
  Definition Inside (k : K) (R W : X -> bool) : Prop :=
    (forall x, R x = true -> home k x = true) /\
    (forall x, W x = true -> own k x = true /\ sh x = false).

  Definition EvOK (e : E) : Prop :=
    Local get (cRE r e) (cWE r e) (A e) /\ Inside (bE e) (cRE r e) (cWE r e).

  Definition InvOK (i : I) : Prop :=
    PLocal get (cRC r i) (chk i) /\ Local get (cRR r i) (cWR r i) (rep i) /\
    Inside (bI i) (cRC r i) (fun _ => false) /\ Inside (bI i) (cRR r i) (cWR r i).

  Definition Hyps : Prop :=
    StateOK /\ (forall e, EvOK e) /\ (forall i, In i invs -> InvOK i).

  (* Repair, validity, normalization, steps, runs. *)
  Fixpoint repL (l : list I) (s : St) : St :=
    match l with
    | [] => s
    | i :: l' => if chk i s then repL l' s else rep i s
    end.

  Definition validL (l : list I) (s : St) : bool := forallb (fun i => chk i s) l.

  Fixpoint iter (n : nat) (f : St -> St) (s : St) : St :=
    match n with 0 => s | S n' => iter n' f (f s) end.

  Definition isK (k : K) (i : I) : bool := if keq (bI i) k then true else false.
  Definition invK (k : K) : list I := filter (isK k) invs.

  Definition rho : St -> St := repL invs.
  Definition valid : St -> bool := validL invs.
  Definition rhoK (k : K) : St -> St := repL (invK k).
  Definition validK (k : K) : St -> bool := validL (invK k).

  Definition restrict (k : K) (s : St) : St := mix (home k) s z.
  Definition Sub (k : K) (t : St) : Prop := forall x, home k x = false -> get t x = get z x.

  Definition N (B : nat) (s : St) : St := iter B rho s.
  Definition NK (k : K) (B : nat) (t : St) : St := iter B (rhoK k) t.
  Definition G (B : nat) (e : E) (s : St) : St := N B (A e s).
  Definition GK (k : K) (B : nat) (e : E) (t : St) : St := NK k B (A e t).
  Definition run (B : nat) (l : list E) (s : St) : St := fold_left (fun u e => G B e u) l s.
  Definition runK (k : K) (B : nat) (l : list E) (t : St) : St :=
    fold_left (fun u e => GK k B e u) l t.

  Definition Term (s : St) : Prop := exists n, valid (iter n rho s) = true.
  Definition TermK (k : K) (t : St) : Prop := exists n, validK k (iter n (rhoK k) t) = true.
  Definition WFCb (B : nat) : Prop := forall s, valid (iter B rho s) = true.
  Definition WFCk (k : K) (B : nat) : Prop :=
    forall t, Sub k t -> validK k (iter B (rhoK k) t) = true.

  Definition CC1 (B : nat) (e1 e2 : E) (s : St) : Prop := G B e2 (G B e1 s) = G B e1 (G B e2 s).
  Definition CC1K (k : K) (B : nat) (e1 e2 : E) (t : St) : Prop :=
    GK k B e2 (GK k B e1 t) = GK k B e1 (GK k B e2 t).

  (* gsm's guarantee: every permutation of the same events from a valid state, same state. *)
  Definition Conv (B : nat) : Prop :=
    forall s, valid s = true -> forall l1 l2, Permutation l1 l2 -> run B l1 s = run B l2 s.
  Definition ConvK (k : K) (B : nat) : Prop :=
    forall t, Sub k t -> validK k t = true -> forall l1 l2, Permutation l1 l2 ->
      Forall (fun e => bE e = k) l1 -> runK k B l1 t = runK k B l2 t.

  Definition sumK (Ks : list K) (f : K -> nat) : nat := fold_right (fun k a => f k + a) 0 Ks.

  (* Facts that need no hypothesis. *)
  Lemma iter_add : forall f n m s, iter (n + m) f s = iter m f (iter n f s).
  Proof. intros f n; induction n as [|n IH]; intros m s; simpl; [reflexivity | apply IH]. Qed.

  Lemma repL_valid : forall l s, validL l s = true -> repL l s = s.
  Proof.
    induction l as [|i l IH]; intros s H; simpl in *; [reflexivity|].
    apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. apply IH, H2.
  Qed.

  Lemma iter_fix : forall l n s, validL l s = true -> iter n (repL l) s = s.
  Proof.
    intros l n; induction n as [|n IH]; intros s H; simpl; [reflexivity|].
    rewrite (repL_valid l s H). apply IH, H.
  Qed.

  Lemma iter_mono : forall l n m s, validL l (iter n (repL l) s) = true -> n <= m ->
    iter m (repL l) s = iter n (repL l) s.
  Proof.
    intros l n m s H Hle. replace m with (n + (m - n)) by lia.
    rewrite iter_add. apply iter_fix, H.
  Qed.

  Lemma isK_true : forall k i, isK k i = true -> bI i = k.
  Proof. intros k i. unfold isK. destruct (keq (bI i) k); [auto | discriminate]. Qed.

  Lemma isK_refl : forall i, isK (bI i) i = true.
  Proof. intros i. unfold isK. destruct (keq (bI i) (bI i)); congruence. Qed.

  Lemma own_blk : forall x, own (blk x) x = true.
  Proof. intros x. unfold own. destruct (keq (blk x) (blk x)); congruence. Qed.

  Lemma home_blk : forall x, home (blk x) x = true.
  Proof. intros x. unfold home. rewrite own_blk. reflexivity. Qed.

  Lemma own_disj : forall k k' x, k <> k' -> own k x = true -> own k' x = false.
  Proof.
    unfold own. intros k k' x Hne H. destruct (keq (blk x) k); [|discriminate].
    destruct (keq (blk x) k'); congruence.
  Qed.

  Lemma forallb_ext_in : forall {T} (f g : T -> bool) l,
    (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
  Proof.
    intros T f g l; induction l as [|a l IH]; intros H; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma sumK_ge : forall Ks f k, In k Ks -> f k <= sumK Ks f.
  Proof.
    induction Ks as [|a Ks IH]; intros f k H; [destruct H|]. simpl.
    destruct H as [<- | H]; [lia|]. specialize (IH f k H). lia.
  Qed.

  Lemma sumK_le : forall Ks f g, (forall k, f k <= g k) -> sumK Ks f <= sumK Ks g.
  Proof.
    induction Ks as [|a Ks IH]; intros f g H; simpl; [lia|].
    pose proof (H a). specialize (IH f g H). lia.
  Qed.

  Definition dec1 (k0 : K) (f : K -> nat) : K -> nat :=
    fun k => if keq k k0 then pred (f k) else f k.

  Lemma sumK_dec1 : forall Ks f k0, In k0 Ks -> 1 <= f k0 -> sumK Ks (dec1 k0 f) < sumK Ks f.
  Proof.
    induction Ks as [|a Ks IH]; intros f k0 Hin H1; [destruct Hin|]. simpl.
    assert (Hle : sumK Ks (dec1 k0 f) <= sumK Ks f).
    { apply sumK_le. intros k. unfold dec1. destruct (keq k k0); lia. }
    unfold dec1 at 1. destruct (keq a k0) as [-> | Hne]; [lia|].
    destruct Hin as [-> | Hin]; [contradiction|]. specialize (IH f k0 Hin H1). lia.
  Qed.

  Lemma choose : forall (P : K -> nat -> Prop) Ks,
    (forall k, In k Ks -> exists n, P k n) -> exists f : K -> nat, forall k, In k Ks -> P k (f k).
  Proof.
    intros P Ks; induction Ks as [|a Ks IH]; intros H.
    - exists (fun _ => 0). intros k [].
    - destruct (H a (or_introl eq_refl)) as [na Ha].
      destruct IH as [f Hf]; [intros k Hk; apply H; right; exact Hk|].
      exists (fun k => if keq k a then na else f k). intros k Hk.
      destruct (keq k a) as [-> | Hne]; [exact Ha|].
      destruct Hk as [-> | Hk]; [contradiction | apply Hf, Hk].
  Qed.

  Lemma perm_single : forall (P : E -> Prop) l1 l2, (forall e e', P e -> P e' -> e = e') ->
    Forall P l1 -> Permutation l1 l2 -> l1 = l2.
  Proof.
    intros P l1 l2 Hu H1 Hp.
    assert (H2 : Forall P l2).
    { apply Forall_forall. intros x Hx. rewrite Forall_forall in H1. apply H1.
      apply (Permutation_in x (Permutation_sym Hp) Hx). }
    assert (Hl : length l1 = length l2) by (apply Permutation_length; exact Hp).
    clear Hp. revert l2 H2 Hl. induction l1 as [|a l1 IH]; intros [|b l2] H2 Hl;
      simpl in Hl; try discriminate; [reflexivity|].
    inversion H1; subst. inversion H2; subst. f_equal; [apply Hu; assumption|].
    apply IH; auto.
  Qed.

  (* Raw effects and normalization in a component that has no invariants. *)
  Lemma validK_nil : forall k t, invK k = [] -> validK k t = true.
  Proof. intros k t H. unfold validK. rewrite H. reflexivity. Qed.

  (* Reads in the footprint force variables into one component (with no shared variables). *)
  Lemma inside_merge : forall k R W x y, Inside k R W -> R x = true -> sh x = false ->
    W y = true -> blk x = blk y.
  Proof.
    intros k R W x y [HR HW] Hx Hs Hy. specialize (HR x Hx). unfold home in HR.
    rewrite Hs, orb_false_r in HR. destruct (HW y Hy) as [Ho _].
    unfold own in HR, Ho. destruct (keq (blk x) k); [|discriminate].
    destruct (keq (blk y) k); [congruence | discriminate].
  Qed.

  Section Proofs.
    Hypothesis HH : Hyps.

    Lemma get_mix : forall C s t x, get (mix C s t) x = if C x then get s x else get t x.
    Proof. exact (proj1 (proj1 HH)). Qed.

    Lemma st_ext : forall s t, (forall x, get s x = get t x) -> s = t.
    Proof. exact (proj2 (proj1 HH)). Qed.

    Lemma restrict_get : forall k s x, get (restrict k s) x = if home k x then get s x else get z x.
    Proof. intros. unfold restrict. apply get_mix. Qed.

    Lemma restrict_Sub : forall k s, Sub k (restrict k s).
    Proof. intros k s x Hx. rewrite restrict_get, Hx. reflexivity. Qed.

    Lemma Sub_restrict : forall k t, Sub k t -> restrict k t = t.
    Proof.
      intros k t Ht. apply st_ext. intros x. rewrite restrict_get.
      destruct (home k x) eqn:Ex; [reflexivity | symmetry; apply Ht, Ex].
    Qed.

    Lemma eq_by_restrict : forall s t, (forall k, restrict k s = restrict k t) -> s = t.
    Proof.
      intros s t H. apply st_ext. intros x.
      pose proof (f_equal (fun u => get u x) (H (blk x))) as E1. simpl in E1.
      rewrite !restrict_get, home_blk in E1. exact E1.
    Qed.

    Lemma local_own : forall k R W f, Local get R W f -> Inside k R W ->
      forall s, restrict k (f s) = f (restrict k s).
    Proof.
      intros k R W f [Hw Hr] [HR HW] s. apply st_ext. intros x. rewrite restrict_get.
      destruct (W x) eqn:Ex.
      - destruct (HW x Ex) as [Ho _].
        assert (Hh : home k x = true) by (unfold home; rewrite Ho; reflexivity).
        rewrite Hh. apply Hr; [|exact Ex].
        intros y Hy. rewrite restrict_get, (HR y Hy). reflexivity.
      - rewrite (Hw (restrict k s) x Ex), restrict_get, (Hw s x Ex). reflexivity.
    Qed.

    Lemma local_other : forall k k' R W f, Local get R W f ->
      (forall x, W x = true -> own k' x = true /\ sh x = false) -> k <> k' ->
      forall s, restrict k (f s) = restrict k s.
    Proof.
      intros k k' R W f [Hw _] HW Hne s. apply st_ext. intros x. rewrite !restrict_get.
      destruct (home k x) eqn:Eh; [|reflexivity].
      destruct (W x) eqn:Ex; [|apply Hw; exact Ex].
      exfalso. destruct (HW x Ex) as [Ho Hs]. unfold home in Eh.
      rewrite Hs, (own_disj k' k x (not_eq_sym Hne) Ho) in Eh. discriminate.
    Qed.

    Lemma local_Sub : forall k R W f, Local get R W f ->
      (forall x, W x = true -> own k x = true /\ sh x = false) ->
      forall t, Sub k t -> Sub k (f t).
    Proof.
      intros k R W f [Hw _] HW t Ht x Hx. destruct (W x) eqn:Ex.
      - destruct (HW x Ex) as [Ho _]. unfold home in Hx. rewrite Ho in Hx. discriminate.
      - rewrite (Hw t x Ex). apply Ht, Hx.
    Qed.

    Lemma ev_own : forall e s, restrict (bE e) (A e s) = A e (restrict (bE e) s).
    Proof. intros e s. destruct (proj1 (proj2 HH) e) as [Hl Hi]. exact (local_own _ _ _ _ Hl Hi s). Qed.

    Lemma ev_other : forall e k s, k <> bE e -> restrict k (A e s) = restrict k s.
    Proof.
      intros e k s Hne. destruct (proj1 (proj2 HH) e) as [Hl [_ HW]].
      exact (local_other k (bE e) _ _ _ Hl HW Hne s).
    Qed.

    Lemma ev_Sub : forall e t, Sub (bE e) t -> Sub (bE e) (A e t).
    Proof. intros e t. destruct (proj1 (proj2 HH) e) as [Hl [_ HW]]. apply (local_Sub _ _ _ _ Hl HW). Qed.

    Lemma chk_restrict : forall i k s, In i invs -> bI i = k -> chk i (restrict k s) = chk i s.
    Proof.
      intros i k s Hi <-. destruct (proj2 (proj2 HH) i Hi) as [Hc [_ [[HR _] _]]].
      apply Hc. intros x Hx. rewrite restrict_get, (HR x Hx). reflexivity.
    Qed.

    Lemma rep_own : forall i s, In i invs -> restrict (bI i) (rep i s) = rep i (restrict (bI i) s).
    Proof.
      intros i s Hi. destruct (proj2 (proj2 HH) i Hi) as [_ [Hl [_ Hin]]].
      exact (local_own _ _ _ _ Hl Hin s).
    Qed.

    Lemma rep_other : forall i k s, In i invs -> k <> bI i -> restrict k (rep i s) = restrict k s.
    Proof.
      intros i k s Hi Hne. destruct (proj2 (proj2 HH) i Hi) as [_ [Hl [_ [_ HW]]]].
      exact (local_other k (bI i) _ _ _ Hl HW Hne s).
    Qed.

    Lemma rep_Sub : forall i t, In i invs -> Sub (bI i) t -> Sub (bI i) (rep i t).
    Proof.
      intros i t Hi. destruct (proj2 (proj2 HH) i Hi) as [_ [Hl [_ [_ HW]]]].
      apply (local_Sub _ _ _ _ Hl HW).
    Qed.

    (* One repair step: either valid, or the first violated invariant i fires, and it is the first
       violated invariant of its component at the restriction. *)
    Lemma repL_cases : forall l s, (forall i, In i l -> In i invs) ->
      (validL l s = true /\ repL l s = s) \/
      (exists i, In i l /\ chk i s = false /\ repL l s = rep i s /\
         validL (filter (isK (bI i)) l) (restrict (bI i) s) = false /\
         repL (filter (isK (bI i)) l) (restrict (bI i) s) = rep i (restrict (bI i) s)).
    Proof.
      induction l as [|i l IH]; intros s Hl; [left; split; reflexivity|].
      assert (Hi : In i invs) by (apply Hl; left; reflexivity).
      assert (Hl' : forall j, In j l -> In j invs) by (intros j Hj; apply Hl; right; exact Hj).
      simpl. destruct (chk i s) eqn:Ci.
      - destruct (IH s Hl') as [[V R] | [j [Hj [Cj [Rj [Vf Rf]]]]]].
        + left. split; [exact V | exact R].
        + right. exists j. split; [right; exact Hj|]. split; [exact Cj|]. split; [exact Rj|].
          destruct (isK (bI j) i) eqn:Ki.
          * simpl. rewrite (chk_restrict i (bI j) s Hi (isK_true _ _ Ki)), Ci. simpl.
            split; [exact Vf | exact Rf].
          * split; [exact Vf | exact Rf].
      - right. exists i. split; [left; reflexivity|]. split; [exact Ci|]. split; [reflexivity|].
        rewrite isK_refl. simpl. rewrite (chk_restrict i (bI i) s Hi eq_refl), Ci.
        split; reflexivity.
    Qed.

    Lemma rho_step : forall s,
      (valid s = true /\ rho s = s) \/
      (exists k, validK k (restrict k s) = false /\ restrict k (rho s) = rhoK k (restrict k s) /\
         (forall k', k' <> k -> restrict k' (rho s) = restrict k' s) /\
         exists i, In i invs /\ bI i = k).
    Proof.
      intros s. destruct (repL_cases invs s (fun i H => H)) as [[V R] | [i [Hi [_ [R [Vf Rf]]]]]].
      - left. split; assumption.
      - right. exists (bI i). unfold validK, rhoK, invK, rho. rewrite R.
        split; [exact Vf|]. split; [rewrite Rf; apply rep_own, Hi|]. split.
        + intros k' Hk'. apply rep_other; assumption.
        + exists i. split; [exact Hi | reflexivity].
    Qed.

    Lemma validK_restrict : forall k s, validK k (restrict k s) = validK k s.
    Proof.
      intros k s. unfold validK, validL, invK. apply forallb_ext_in. intros i Hi.
      apply filter_In in Hi. destruct Hi as [Hi Hk]. apply chk_restrict; [exact Hi | apply isK_true, Hk].
    Qed.

    Lemma valid_validK : forall k s, valid s = true -> validK k s = true.
    Proof.
      intros k s H. unfold valid, validL in H. unfold validK, validL, invK.
      rewrite forallb_forall in *. intros i Hi. apply filter_In in Hi. apply H, Hi.
    Qed.

    Lemma valid_iff_Ks : forall Ks, (forall i, In i invs -> In (bI i) Ks) ->
      forall s, valid s = true <-> forall k, In k Ks -> validK k (restrict k s) = true.
    Proof.
      intros Ks Hc s. split.
      - intros H k _. rewrite validK_restrict. apply valid_validK, H.
      - intros H. unfold valid, validL. apply forallb_forall. intros i Hi.
        specialize (H (bI i) (Hc i Hi)). rewrite validK_restrict in H.
        unfold validK, validL, invK in H. rewrite forallb_forall in H. apply H.
        apply filter_In. split; [exact Hi | apply isK_refl].
    Qed.

    Lemma valid_iff : forall s, valid s = true <-> forall k, validK k (restrict k s) = true.
    Proof.
      intros s. split.
      - intros H k. rewrite validK_restrict. apply valid_validK, H.
      - intros H. apply (proj2 (valid_iff_Ks (map bI invs) (fun i Hi => in_map bI invs i Hi) s)).
        intros k _. apply H.
    Qed.

    Lemma rhoK_Sub : forall k t, Sub k t -> Sub k (rhoK k t).
    Proof.
      intros k t Ht. unfold rhoK, invK.
      assert (G1 : forall l, (forall i, In i l -> In i invs /\ bI i = k) -> Sub k (repL l t)).
      { induction l as [|i l IH]; intros Hl; simpl; [exact Ht|].
        destruct (chk i t).
        - apply IH. intros j Hj. apply Hl. right. exact Hj.
        - destruct (Hl i (or_introl eq_refl)) as [Hi <-]. apply rep_Sub; [exact Hi | exact Ht]. }
      apply G1. intros i Hi. apply filter_In in Hi. split; [apply Hi | apply isK_true, Hi].
    Qed.

    Lemma iterK_Sub : forall k n t, Sub k t -> Sub k (iter n (rhoK k) t).
    Proof. intros k n; induction n as [|n IH]; intros t Ht; simpl; [exact Ht | apply IH, rhoK_Sub, Ht]. Qed.

    (* Every repair run projects to a repair run of each component. *)
    Lemma iter_proj : forall n s k, exists m, m <= n /\
      restrict k (iter n rho s) = iter m (rhoK k) (restrict k s).
    Proof.
      induction n as [|n IH]; intros s k; [exists 0; split; [lia | reflexivity]|].
      simpl. destruct (rho_step s) as [[_ R] | [k0 [_ [Rk [Ro _]]]]].
      - rewrite R. destruct (IH s k) as [m [Hm E1]]. exists m. split; [lia | exact E1].
      - destruct (keq k k0) as [-> | Hne].
        + destruct (IH (rho s) k0) as [m [Hm E1]]. exists (S m). split; [lia|].
          rewrite E1, Rk. reflexivity.
        + destruct (IH (rho s) k) as [m [Hm E1]]. exists m. split; [lia|].
          rewrite E1, (Ro k Hne). reflexivity.
    Qed.

    Theorem term_proj : forall s k, Term s -> TermK k (restrict k s).
    Proof.
      intros s k [n Hn]. destruct (iter_proj n s k) as [m [_ E1]]. exists m.
      rewrite <- E1. apply (proj1 (valid_iff _) Hn).
    Qed.

    Lemma bound_gen : forall Ks, (forall i, In i invs -> In (bI i) Ks) ->
      forall M s f, sumK Ks f <= M ->
      (forall k, In k Ks -> validK k (iter (f k) (rhoK k) (restrict k s)) = true) ->
      valid (iter M rho s) = true.
    Proof.
      intros Ks Hc M. induction M as [|M IH]; intros s f Hs Hf.
      - simpl. apply (proj2 (valid_iff_Ks Ks Hc s)). intros k Hk.
        specialize (Hf k Hk). pose proof (sumK_ge Ks f k Hk) as Hg.
        replace (f k) with 0 in Hf by lia. exact Hf.
      - destruct (rho_step s) as [[V _] | [k0 [Vk [Rk [Ro [i [Hi Hb]]]]]]].
        + unfold rho. rewrite iter_fix; [exact V | exact V].
        + assert (Hk0 : In k0 Ks) by (rewrite <- Hb; apply Hc, Hi).
          assert (H1 : 1 <= f k0).
          { destruct (f k0) eqn:Ef; [|lia]. specialize (Hf k0 Hk0). rewrite Ef in Hf.
            simpl in Hf. rewrite Hf in Vk. discriminate. }
          simpl. apply (IH (rho s) (dec1 k0 f)).
          * pose proof (sumK_dec1 Ks f k0 Hk0 H1). lia.
          * intros k Hk. unfold dec1. destruct (keq k k0) as [-> | Hne].
            -- rewrite Rk. specialize (Hf k0 Hk0).
               destruct (f k0) as [|p] eqn:Ef; [lia|]. simpl. simpl in Hf. exact Hf.
            -- rewrite (Ro k Hne). apply Hf, Hk.
    Qed.

    Theorem bound_sum : forall Ks d, (forall i, In i invs -> In (bI i) Ks) ->
      (forall k, In k Ks -> WFCk k (d k)) -> WFCb (sumK Ks d).
    Proof.
      intros Ks d Hc Hd s. apply (bound_gen Ks Hc _ s d (le_n _)).
      intros k Hk. apply Hd; [exact Hk | apply restrict_Sub].
    Qed.

    Theorem term_iff : forall Ks, (forall i, In i invs -> In (bI i) Ks) ->
      forall s, Term s <-> forall k, In k Ks -> TermK k (restrict k s).
    Proof.
      intros Ks Hc s. split.
      - intros H k _. apply term_proj, H.
      - intros H. destruct (choose (fun k n => validK k (iter n (rhoK k) (restrict k s)) = true) Ks H)
          as [f Hf].
        exists (sumK Ks f). apply (bound_gen Ks Hc _ s f (le_n _) Hf).
    Qed.

    Theorem wfc_iff : forall Ks, (forall i, In i invs -> In (bI i) Ks) ->
      (forall s, Term s) <-> (forall k, In k Ks -> forall t, Sub k t -> TermK k t).
    Proof.
      intros Ks Hc. split.
      - intros H k _ t Ht. rewrite <- (Sub_restrict k t Ht). apply term_proj, H.
      - intros H s. apply (proj2 (term_iff Ks Hc s)). intros k Hk. apply H; [exact Hk | apply restrict_Sub].
    Qed.

    Lemma wfcb_wfck : forall B, WFCb B -> forall k, WFCk k B.
    Proof.
      intros B HB k t Ht. destruct (iter_proj B t k) as [m [Hm E1]].
      rewrite (Sub_restrict k t Ht) in E1.
      assert (Hv : validK k (iter m (rhoK k) t) = true).
      { rewrite <- E1. apply (proj1 (valid_iff _) (HB t)). }
      unfold rhoK. rewrite (iter_mono (invK k) m B t Hv Hm). exact Hv.
    Qed.

    Theorem wfcb_iff : forall Ks, (forall i, In i invs -> In (bI i) Ks) ->
      (exists B, WFCb B) <-> (forall k, In k Ks -> exists d, WFCk k d).
    Proof.
      intros Ks Hc. split.
      - intros [B HB] k _. exists B. apply wfcb_wfck, HB.
      - intros H. destruct (choose (fun k d => WFCk k d) Ks H) as [d Hd].
        exists (sumK Ks d). apply bound_sum; assumption.
    Qed.

    Section Bound.
      Variable B : nat.
      Hypothesis HB : WFCb B.

      Lemma N_valid : forall s, valid (N B s) = true.
      Proof. intros s. apply HB. Qed.

      Lemma N_fix : forall s, valid s = true -> N B s = s.
      Proof. intros s H. apply iter_fix, H. Qed.

      Lemma G_valid : forall e s, valid (G B e s) = true.
      Proof. intros e s. apply HB. Qed.

      Lemma NK_valid : forall k t, Sub k t -> validK k (NK k B t) = true.
      Proof. intros k t Ht. apply (wfcb_wfck B HB k t Ht). Qed.

      Lemma NK_fix : forall k t, validK k t = true -> NK k B t = t.
      Proof. intros k t H. apply iter_fix, H. Qed.

      Lemma NK_Sub : forall k t, Sub k t -> Sub k (NK k B t).
      Proof. intros. apply iterK_Sub; assumption. Qed.

      Lemma N_proj : forall k s, restrict k (N B s) = NK k B (restrict k s).
      Proof.
        intros k s. destruct (iter_proj B s k) as [m [Hm E1]]. unfold N. rewrite E1.
        assert (Hv : validK k (iter m (rhoK k) (restrict k s)) = true).
        { rewrite <- E1. apply (proj1 (valid_iff _) (HB s)). }
        unfold NK, rhoK. symmetry. apply (iter_mono (invK k) m B _ Hv Hm).
      Qed.

      Lemma NK_idem : forall k t, Sub k t -> NK k B (NK k B t) = NK k B t.
      Proof. intros k t Ht. apply NK_fix, NK_valid, Ht. Qed.

      Lemma G_own : forall k e s, bE e = k -> restrict k (G B e s) = GK k B e (restrict k s).
      Proof. intros k e s <-. unfold G, GK. rewrite N_proj, ev_own. reflexivity. Qed.

      Lemma G_other : forall k e s, k <> bE e -> restrict k (G B e s) = NK k B (restrict k s).
      Proof. intros k e s Hne. unfold G. rewrite N_proj, (ev_other e k s Hne). reflexivity. Qed.

      Lemma G_other_valid : forall k e s, valid s = true -> k <> bE e ->
        restrict k (G B e s) = restrict k s.
      Proof.
        intros k e s Hv Hne. rewrite (G_other k e s Hne). apply NK_fix.
        rewrite validK_restrict. apply valid_validK, Hv.
      Qed.

      Lemma GK_Sub : forall k e t, bE e = k -> Sub k t -> Sub k (GK k B e t).
      Proof. intros k e t <- Ht. apply NK_Sub, ev_Sub, Ht. Qed.

      (* Events in different components: CC1 at every valid state, with no check. *)
      Theorem cc1_cross : forall e1 e2 s, bE e1 <> bE e2 -> valid s = true -> CC1 B e1 e2 s.
      Proof.
        intros e1 e2 s Hne Hv. unfold CC1. apply eq_by_restrict. intros k.
        destruct (keq k (bE e1)) as [-> | n1].
        - rewrite (G_other_valid _ e2 _ (G_valid _ _) Hne), (G_own _ e1 _ eq_refl).
          rewrite (G_own _ e1 _ eq_refl), (G_other_valid _ e2 _ Hv Hne). reflexivity.
        - destruct (keq k (bE e2)) as [-> | n2].
          + rewrite (G_own _ e2 _ eq_refl), (G_other_valid _ e1 _ Hv n1).
            rewrite (G_other_valid _ e1 _ (G_valid _ _) n1), (G_own _ e2 _ eq_refl). reflexivity.
          + rewrite (G_other_valid _ e2 _ (G_valid _ _) n2), (G_other_valid _ e1 _ Hv n1).
            rewrite (G_other_valid _ e1 _ (G_valid _ _) n1), (G_other_valid _ e2 _ Hv n2). reflexivity.
      Qed.

      (* Events in the same component: CC1 at s iff the component's CC1 at the restriction. *)
      Theorem cc1_same_iff : forall k e1 e2 s, bE e1 = k -> bE e2 = k ->
        (CC1 B e1 e2 s <-> CC1K k B e1 e2 (restrict k s)).
      Proof.
        intros k e1 e2 s H1 H2. unfold CC1, CC1K. split.
        - intros H. pose proof (f_equal (restrict k) H) as E1.
          rewrite (G_own k e2 _ H2), (G_own k e1 _ H1), (G_own k e1 _ H1), (G_own k e2 _ H2) in E1.
          exact E1.
        - intros H. apply eq_by_restrict. intros k'. destruct (keq k' k) as [-> | Hne].
          + rewrite (G_own k e2 _ H2), (G_own k e1 _ H1), (G_own k e1 _ H1), (G_own k e2 _ H2).
            exact H.
          + assert (n1 : k' <> bE e1) by (rewrite H1; exact Hne).
            assert (n2 : k' <> bE e2) by (rewrite H2; exact Hne).
            rewrite (G_other k' e2 _ n2), (G_other k' e1 _ n1), (G_other k' e1 _ n1), (G_other k' e2 _ n2).
            rewrite !NK_idem by apply restrict_Sub. reflexivity.
      Qed.

      Theorem cc1_component : forall k e1 e2, bE e1 = k -> bE e2 = k ->
        ((forall s, valid s = true -> CC1 B e1 e2 s) <->
         (forall t, Sub k t -> validK k t = true -> CC1K k B e1 e2 t)).
      Proof.
        intros k e1 e2 H1 H2. split.
        - intros H t Ht Hv. pose proof (proj1 (cc1_same_iff k e1 e2 (N B t) H1 H2) (H _ (N_valid t))) as C.
          rewrite N_proj, (Sub_restrict k t Ht), (NK_fix k t Hv) in C. exact C.
        - intros H s Hv. apply (proj2 (cc1_same_iff k e1 e2 s H1 H2)). apply H.
          + apply restrict_Sub.
          + rewrite validK_restrict. apply valid_validK, Hv.
      Qed.

      (* gsm's guarantee is exactly CC1 on valid states. *)
      Theorem conv_iff_cc1 : Conv B <-> (forall e1 e2 s, valid s = true -> CC1 B e1 e2 s).
      Proof.
        pose proof (perm_good_iff (G B) (fun s => valid s = true) (fun _ => True)
                      (fun e s _ _ => G_valid e s)) as P.
        unfold Conv, CC1. split.
        - intros H e1 e2 s Hv. apply (proj1 P); [|exact Hv|exact Logic.I|exact Logic.I].
          intros u Hu l1 l2 Hp _. apply H; assumption.
        - intros H s Hv l1 l2 Hp. apply (proj2 P); [|exact Hv|exact Hp|].
          + intros u Hu e1 e2 _ _. apply H, Hu.
          + apply Forall_forall. intros; exact Logic.I.
      Qed.

      Theorem convK_iff_cc1K : forall k, ConvK k B <->
        (forall t, Sub k t -> validK k t = true -> forall e1 e2, bE e1 = k -> bE e2 = k ->
           CC1K k B e1 e2 t).
      Proof.
        intros k.
        assert (Hcl : forall e t, bE e = k -> (Sub k t /\ validK k t = true) ->
                        Sub k (GK k B e t) /\ validK k (GK k B e t) = true).
        { intros e t He [Ht _]. split; [apply GK_Sub; assumption|].
          apply NK_valid. rewrite <- He in *. apply ev_Sub, Ht. }
        pose proof (perm_good_iff (GK k B) (fun t => Sub k t /\ validK k t = true)
                      (fun e => bE e = k) Hcl) as P.
        unfold ConvK, CC1K. split.
        - intros H t Ht Hv e1 e2 H1 H2. apply (proj1 P); [|split; assumption|exact H1|exact H2].
          intros u [Hu Hvu] l1 l2 Hp HF. apply H; assumption.
        - intros H t Ht Hv l1 l2 Hp HF. apply (proj2 P); [|split; assumption|exact Hp|exact HF].
          intros u [Hu Hvu] e1 e2 H1 H2. apply H; assumption.
      Qed.

      (* The headline: gsm's guarantee for the registry iff for every component. *)
      Theorem compositional_exact : Conv B <-> (forall k, ConvK k B).
      Proof.
        rewrite conv_iff_cc1. split.
        - intros H k. apply convK_iff_cc1K. intros t Ht Hv e1 e2 H1 H2.
          apply (proj1 (cc1_component k e1 e2 H1 H2)); [|exact Ht|exact Hv].
          intros s Hs. apply H, Hs.
        - intros H e1 e2 s Hv. destruct (keq (bE e1) (bE e2)) as [E12 | Hne].
          + refine (proj2 (cc1_component (bE e1) e1 e2 eq_refl (eq_sym E12)) _ s Hv).
            intros t Ht Hvt.
            exact (proj1 (convK_iff_cc1K (bE e1)) (H (bE e1)) t Ht Hvt e1 e2 eq_refl (eq_sym E12)).
          + apply cc1_cross; assumption.
      Qed.
    End Bound.

    Theorem N_indep : forall B1 B2, WFCb B1 -> WFCb B2 -> forall s, N B1 s = N B2 s.
    Proof.
      intros B1 B2 H1 H2 s. unfold N, rho. destruct (le_ge_dec B1 B2) as [Hle | Hge].
      - symmetry. apply iter_mono; [apply H1 | exact Hle].
      - apply iter_mono; [apply H2 | lia].
    Qed.

    Theorem conv_indep : forall B1 B2, WFCb B1 -> WFCb B2 -> (Conv B1 <-> Conv B2).
    Proof.
      intros B1 B2 H1 H2.
      assert (Hr : forall l s, run B1 l s = run B2 l s).
      { intros l; induction l as [|e l IH]; intros s; [reflexivity|].
        unfold run in *; simpl.
        replace (G B1 e s) with (G B2 e s) by (unfold G; symmetry; apply N_indep; assumption).
        apply IH. }
      unfold Conv. split; intros H s Hv l1 l2 Hp; [rewrite <- !Hr | rewrite !Hr]; apply H; assumption.
    Qed.

    (* gsm's form: component bounds d k, the registry's bound their sum (the lazy machine's bound). *)
    Theorem compositional_gsm : forall Ks d, (forall i, In i invs -> In (bI i) Ks) ->
      (forall k, In k Ks -> WFCk k (d k)) ->
      WFCb (sumK Ks d) /\ (Conv (sumK Ks d) <-> forall k, ConvK k (sumK Ks d)).
    Proof.
      intros Ks d Hc Hd. assert (HB : WFCb (sumK Ks d)) by (apply bound_sum; assumption).
      split; [exact HB | apply compositional_exact, HB].
    Qed.

    (* gsm's literal component check: with no shared variable and a valid background, the
       registry's validity and repair on Sub k are the component's. *)
    Lemma filter_other : forall k t l, (forall i, In i l -> In i invs) ->
      (forall i, In i l -> bI i <> k -> chk i t = true) ->
      validL l t = validL (filter (isK k) l) t /\ repL l t = repL (filter (isK k) l) t.
    Proof.
      intros k t l; induction l as [|i l IH]; intros Hl Ho; [split; reflexivity|].
      assert (Hl' : forall j, In j l -> In j invs) by (intros j Hj; apply Hl; right; exact Hj).
      assert (Ho' : forall j, In j l -> bI j <> k -> chk j t = true)
        by (intros j Hj; apply Ho; right; exact Hj).
      destruct (IH Hl' Ho') as [V R]. simpl. destruct (isK k i) eqn:Ki.
      - simpl. unfold validL in *. rewrite V, R. split; reflexivity.
      - assert (Hk : bI i <> k) by (intro E1; rewrite <- E1, isK_refl in Ki; discriminate).
        rewrite (Ho i (or_introl eq_refl) Hk). simpl. split; [exact V | exact R].
    Qed.

    Theorem gsm_literal : (forall x, sh x = false) -> valid z = true ->
      forall k t, Sub k t -> valid t = validK k t /\ rho t = rhoK k t.
    Proof.
      intros Hsh Hz k t Ht. apply filter_other; [intros i Hi; exact Hi|].
      intros i Hi Hne. destruct (proj2 (proj2 HH) i Hi) as [Hc [_ [[HR _] _]]].
      rewrite (Hc t z).
      - unfold valid, validL in Hz. rewrite forallb_forall in Hz. apply Hz, Hi.
      - intros x Hx. apply Ht. specialize (HR x Hx). unfold home in *. rewrite Hsh in *.
        rewrite orb_false_r in *. apply (own_disj (bI i) k x Hne HR).
    Qed.

    Theorem gsm_literal_iter : (forall x, sh x = false) -> valid z = true ->
      forall k n t, Sub k t -> iter n rho t = iter n (rhoK k) t.
    Proof.
      intros Hsh Hz k n; induction n as [|n IH]; intros t Ht; [reflexivity|].
      simpl. rewrite (proj2 (gsm_literal Hsh Hz k t Ht)). apply IH, rhoK_Sub, Ht.
    Qed.

    Theorem gsm_literal_step : (forall x, sh x = false) -> valid z = true ->
      forall B k e t, bE e = k -> Sub k t -> G B e t = GK k B e t.
    Proof.
      intros Hsh Hz B k e t He Ht. unfold G, GK, N, NK. apply gsm_literal_iter; [exact Hsh | exact Hz|].
      rewrite <- He in *. apply ev_Sub, Ht.
    Qed.

    Theorem raw_cross_commute : forall e1 e2 s, bE e1 <> bE e2 -> A e1 (A e2 s) = A e2 (A e1 s).
    Proof.
      intros e1 e2 s Hne. apply eq_by_restrict. intros k.
      destruct (keq k (bE e1)) as [-> | n1].
      - rewrite ev_own, (ev_other e2 _ s Hne), (ev_other e2 _ _ Hne), ev_own. reflexivity.
      - destruct (keq k (bE e2)) as [-> | n2].
        + rewrite (ev_other e1 _ _ (not_eq_sym Hne)), ev_own, ev_own, (ev_other e1 _ s (not_eq_sym Hne)).
          reflexivity.
        + rewrite (ev_other e1 _ _ n1), (ev_other e2 _ _ n2), (ev_other e2 _ _ n2), (ev_other e1 _ _ n1).
          reflexivity.
    Qed.
  End Proofs.

  (* ========================================================================================== *)
  (* The check enumerates each component's subspace, not the product.                          *)
  (* ========================================================================================== *)

  Section Checker.
    Variable f : Fin X D St K E.

    Definition FinOK : Prop :=
      (forall x d s y, get (fupd f x d s) y = if fxeq f y x then d else get s y) /\
      (forall d, In d (fallD f)) /\
      (forall s t, feqb f s t = true <-> s = t) /\
      (forall k x, In x (fvars f k) <-> home k x = true) /\
      (forall e, In e (fevs f)) /\
      (forall i, In i invs -> In (bI i) (fKs f)) /\
      (forall e, In (bE e) (fKs f)).

    (* Every assignment of the variables vs, the others as in the background z. *)
    Fixpoint enumSub (vs : list X) : list St :=
      match vs with
      | [] => [z]
      | x :: vs' => flat_map (fun s => map (fun d => fupd f x d s) (fallD f)) (enumSub vs')
      end.

    Definition evsK (k : K) : list E := filter (fun e => if keq (bE e) k then true else false) (fevs f).

    Definition wfc_check (k : K) (d : nat) : bool :=
      forallb (fun t => validK k (iter d (rhoK k) t)) (enumSub (fvars f k)).

    Definition cc1_check (k : K) (B : nat) : bool :=
      forallb (fun t => negb (validK k t) ||
        forallb (fun e1 => forallb (fun e2 =>
          feqb f (GK k B e2 (GK k B e1 t)) (GK k B e1 (GK k B e2 t))) (evsK k)) (evsK k))
        (enumSub (fvars f k)).

    Definition comp_check (d : K -> nat) : bool :=
      forallb (fun k => wfc_check k (d k)) (fKs f) &&
      forallb (fun k => cc1_check k (sumK (fKs f) d)) (fKs f).

    Lemma len_app : forall (l1 l2 : list St), length (l1 ++ l2) = length l1 + length l2.
    Proof. induction l1 as [|a l1 IH]; intros l2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

    Lemma len_map : forall (g : D -> St) l, length (map g l) = length l.
    Proof. intros g l; induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

    Lemma len_flat_map : forall (g : St -> list St) c l, (forall s, length (g s) = c) ->
      length (flat_map g l) = c * length l.
    Proof.
      intros g c l H; induction l as [|a l IH]; simpl; [lia|]. rewrite len_app, H, IH. lia.
    Qed.

    (* The cost: |D| to the number of the component's variables. *)
    Theorem enum_length : forall vs, length (enumSub vs) = length (fallD f) ^ length vs.
    Proof.
      induction vs as [|x vs IH]; simpl; [reflexivity|].
      rewrite (len_flat_map _ (length (fallD f))); [rewrite IH; reflexivity|].
      intros s. apply len_map.
    Qed.

    Section CheckerProofs.
      Hypothesis HH : Hyps.
      Hypothesis HF : FinOK.

      Lemma enum_complete : forall vs t, (forall x, ~ In x vs -> get t x = get z x) ->
        In t (enumSub vs).
      Proof.
        destruct HF as [Hupd [HD _]].
        induction vs as [|x vs IH]; intros t Ht; simpl.
        - left. apply (st_ext HH). intros y. symmetry. apply Ht. intros [].
        - apply in_flat_map. exists (fupd f x (get z x) t). split.
          + apply IH. intros y Hy. rewrite Hupd. destruct (fxeq f y x) as [-> | Hne]; [reflexivity|].
            apply Ht. intros [E1 | E1]; [congruence | contradiction].
          + apply in_map_iff. exists (get t x). split; [|apply HD].
            apply (st_ext HH). intros y. rewrite !Hupd. destruct (fxeq f y x) as [-> | Hne]; reflexivity.
      Qed.

      Lemma enum_sound : forall vs t, In t (enumSub vs) -> forall x, ~ In x vs -> get t x = get z x.
      Proof.
        destruct HF as [Hupd _].
        induction vs as [|a vs IH]; intros t Ht y Hy; simpl in Ht.
        - destruct Ht as [<- | []]. reflexivity.
        - apply in_flat_map in Ht. destruct Ht as [u [Hu Hm]]. apply in_map_iff in Hm.
          destruct Hm as [d [<- _]]. rewrite Hupd. destruct (fxeq f y a) as [-> | Hne].
          + exfalso. apply Hy. left. reflexivity.
          + apply IH; [exact Hu|]. intros H. apply Hy. right. exact H.
      Qed.

      Lemma enum_Sub : forall k t, In t (enumSub (fvars f k)) <-> Sub k t.
      Proof.
        destruct HF as [_ [_ [_ [Hv _]]]]. intros k t. split.
        - intros H x Hx. apply (enum_sound _ t H). intros Hin. apply Hv in Hin. congruence.
        - intros H. apply enum_complete. intros x Hx. apply H.
          destruct (home k x) eqn:E1; [|reflexivity]. exfalso. apply Hx, Hv, E1.
      Qed.

      Theorem wfc_check_exact : forall k d, wfc_check k d = true <-> WFCk k d.
      Proof.
        intros k d. unfold wfc_check, WFCk. rewrite forallb_forall. split.
        - intros H t Ht. apply H, enum_Sub, Ht.
        - intros H t Ht. apply H, enum_Sub, Ht.
      Qed.

      Lemma evsK_In : forall k e, In e (evsK k) <-> bE e = k.
      Proof.
        destruct HF as [_ [_ [_ [_ [He _]]]]]. intros k e. unfold evsK. rewrite filter_In. split.
        - intros [_ H]. destruct (keq (bE e) k); [assumption | discriminate].
        - intros H. split; [apply He|]. destruct (keq (bE e) k); [reflexivity | contradiction].
      Qed.

      Theorem cc1_check_exact : forall k B, cc1_check k B = true <->
        (forall t, Sub k t -> validK k t = true -> forall e1 e2, bE e1 = k -> bE e2 = k ->
           CC1K k B e1 e2 t).
      Proof.
        destruct HF as [_ [_ [Heq _]]]. intros k B. unfold cc1_check, CC1K.
        rewrite forallb_forall. split.
        - intros H t Ht Hv e1 e2 H1 H2. specialize (H t (proj2 (enum_Sub k t) Ht)).
          rewrite Hv in H. simpl in H. rewrite forallb_forall in H.
          specialize (H e1 (proj2 (evsK_In k e1) H1)). rewrite forallb_forall in H.
          apply Heq, H, evsK_In, H2.
        - intros H t Ht. apply enum_Sub in Ht. destruct (validK k t) eqn:Hv; [|reflexivity].
          simpl. apply forallb_forall. intros e1 H1. apply forallb_forall. intros e2 H2.
          apply Heq, H; [exact Ht | exact Hv | apply evsK_In, H1 | apply evsK_In, H2].
      Qed.

      (* The boolean check decides WFC within the component bounds and gsm's guarantee. *)
      Theorem comp_check_exact : forall d, comp_check d = true <->
        (forall k, In k (fKs f) -> WFCk k (d k)) /\ Conv (sumK (fKs f) d).
      Proof.
        destruct HF as [_ [_ [_ [_ [_ [Hci Hce]]]]]]. intros d. unfold comp_check.
        rewrite andb_true_iff, !forallb_forall.
        assert (Hw : (forall k, In k (fKs f) -> wfc_check k (d k) = true) <->
                     (forall k, In k (fKs f) -> WFCk k (d k))).
        { split; intros H k Hk; apply wfc_check_exact, H, Hk. }
        rewrite Hw. split.
        - intros [Hd Hc]. split; [exact Hd|].
          assert (HB : WFCb (sumK (fKs f) d)) by (apply (bound_sum HH); assumption).
          apply (compositional_exact HH _ HB). intros k. apply (convK_iff_cc1K HH _ HB).
          intros t Ht Hv e1 e2 H1 H2. apply (proj1 (cc1_check_exact k _) (Hc k ltac:(rewrite <- H1; apply Hce)));
            assumption.
        - intros [Hd Hconv]. split; [exact Hd|].
          assert (HB : WFCb (sumK (fKs f) d)) by (apply (bound_sum HH); assumption).
          intros k _. apply cc1_check_exact. apply (convK_iff_cc1K HH _ HB).
          apply (compositional_exact HH _ HB), Hconv.
      Qed.
    End CheckerProofs.
  End Checker.
End Compositional.

(* ============================================================================================ *)
(* A concrete state: six variables over three values.                                           *)
(* ============================================================================================ *)

Inductive V3 := v0 | v1 | v2.
Inductive X6 := xSt | xPd | xSk | xRs | xBo | xOp.
Record S6 := mkS { sSt : V3; sPd : V3; sSk : V3; sRs : V3; sBo : V3; sOp : V3 }.

Definition V3eqb (a b : V3) : bool :=
  match a, b with v0, v0 | v1, v1 | v2, v2 => true | _, _ => false end.

Lemma V3eqb_spec : forall a b, V3eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; intro H; congruence. Qed.

Definition X6_eq : forall a b : X6, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition nat_eq : forall a b : nat, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition g6 (s : S6) (x : X6) : V3 :=
  match x with
  | xSt => sSt s | xPd => sPd s | xSk => sSk s | xRs => sRs s | xBo => sBo s | xOp => sOp s
  end.

Definition mix6 (C : X6 -> bool) (s t : S6) : S6 :=
  mkS (if C xSt then sSt s else sSt t) (if C xPd then sPd s else sPd t)
      (if C xSk then sSk s else sSk t) (if C xRs then sRs s else sRs t)
      (if C xBo then sBo s else sBo t) (if C xOp then sOp s else sOp t).

Definition upd6 (x : X6) (d : V3) (s : S6) : S6 :=
  mix6 (fun y => if X6_eq y x then true else false) (mkS d d d d d d) s.

Definition S6eqb (s t : S6) : bool :=
  forallb (fun x => V3eqb (g6 s x) (g6 t x)) [xSt; xPd; xSk; xRs; xBo; xOp].

Definition z6 : S6 := mkS v0 v0 v0 v0 v0 v0.
Definition allV3 : list V3 := [v0; v1; v2].

Definition inL (l : list X6) (x : X6) : bool :=
  existsb (fun y => if X6_eq x y then true else false) l.

Lemma g6_mix : forall C s t x, g6 (mix6 C s t) x = if C x then g6 s x else g6 t x.
Proof. intros C s t []; reflexivity. Qed.

Lemma g6_ext : forall s t, (forall x, g6 s x = g6 t x) -> s = t.
Proof.
  intros [a b c d e f] [a' b' c' d' e' f'] H.
  f_equal; [exact (H xSt) | exact (H xPd) | exact (H xSk) | exact (H xRs) | exact (H xBo) | exact (H xOp)].
Qed.

Lemma g6_upd : forall x d s y, g6 (upd6 x d s) y = if X6_eq y x then d else g6 s y.
Proof. intros x d s y. unfold upd6. rewrite g6_mix. destruct (X6_eq y x); [destruct y|]; reflexivity. Qed.

Lemma S6eqb_spec : forall s t, S6eqb s t = true <-> s = t.
Proof.
  intros s t. unfold S6eqb. rewrite forallb_forall. split.
  - intros H. apply g6_ext. intros x. apply V3eqb_spec, H. destruct x; simpl; tauto.
  - intros <- x _. apply V3eqb_spec. reflexivity.
Qed.

Lemma allV3_complete : forall d, In d allV3.
Proof. intros []; simpl; tauto. Qed.

(* Tactics for footprint proofs on S6. *)
Ltac ag6 H :=
  try (let E := fresh "E" in pose proof (H xSt eq_refl) as E; simpl in E; subst);
  try (let E := fresh "E" in pose proof (H xPd eq_refl) as E; simpl in E; subst);
  try (let E := fresh "E" in pose proof (H xSk eq_refl) as E; simpl in E; subst);
  try (let E := fresh "E" in pose proof (H xRs eq_refl) as E; simpl in E; subst);
  try (let E := fresh "E" in pose proof (H xBo eq_refl) as E; simpl in E; subst);
  try (let E := fresh "E" in pose proof (H xOp eq_refl) as E; simpl in E; subst).

Ltac ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c end.

Ltac local6 :=
  split;
  [ let s := fresh "s" in let x := fresh "x" in let Hx := fresh "Hx" in
    intros s x Hx; destruct s; destruct x; try discriminate Hx; cbn; ifs; reflexivity
  | let s := fresh "s" in let t := fresh "t" in let H := fresh "H" in
    let x := fresh "x" in let Hx := fresh "Hx" in
    intros s t H x Hx; destruct s, t; ag6 H; destruct x; try discriminate Hx; cbn; ifs; reflexivity ].

Ltac plocal6 :=
  let s := fresh "s" in let t := fresh "t" in let H := fresh "H" in
  intros s t H; destruct s, t; ag6 H; reflexivity.

Ltac inside6 :=
  split; [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; destruct x; try discriminate Hx; reflexivity
         | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; destruct x; try discriminate Hx; split; reflexivity ].

(* ============================================================================================ *)
(* Non-vacuity: orders and inventory, with or without a shared read-only store-open flag.       *)
(* ============================================================================================ *)

Inductive ShopEv := Pay | Ship | Reserve | Restock.
Inductive ShopInv := ShipPaid | BoFlag.

Definition vsucc (a : V3) : V3 := match a with v0 => v1 | _ => v2 end.
Definition vgt (a b : V3) : bool :=
  match a, b with v1, v0 | v2, v0 | v2, v1 => true | _, _ => false end.
Definition vflag (b : bool) : V3 := if b then v1 else v0.

(* With g, ship and reserve need the store open (sOp <> v0); xOp is shared and never written. *)
Definition opn (g : bool) (s : S6) : bool := negb g || negb (V3eqb (sOp s) v0).

Definition shopA (g : bool) (e : ShopEv) (s : S6) : S6 :=
  match e with
  | Pay => upd6 xPd v1 s
  | Ship => if opn g s then upd6 xSt v2 s else s
  | Reserve => if opn g s then upd6 xRs (vsucc (sRs s)) s else s
  | Restock => upd6 xSk (vsucc (sSk s)) s
  end.

(* Shipped implies paid (repair: charge); the backorder flag is reserved > stock (repair: recompute). *)
Definition shopChk (i : ShopInv) (s : S6) : bool :=
  match i with
  | ShipPaid => negb (V3eqb (sSt s) v2) || V3eqb (sPd s) v1
  | BoFlag => V3eqb (sBo s) (vflag (vgt (sRs s) (sSk s)))
  end.

Definition shopRep (i : ShopInv) (s : S6) : S6 :=
  match i with
  | ShipPaid => upd6 xPd v1 s
  | BoFlag => upd6 xBo (vflag (vgt (sRs s) (sSk s))) s
  end.

(* Components: orders 0 (status, paid), inventory 1 (stock, reserved, backorder), config 2. *)
Definition shopBlk (x : X6) : nat :=
  match x with xSt | xPd => 0 | xSk | xRs | xBo => 1 | xOp => 2 end.
Definition shopSh (g : bool) (x : X6) : bool := g && inL [xOp] x.
Definition shopBE (e : ShopEv) : nat := match e with Pay | Ship => 0 | _ => 1 end.
Definition shopBI (i : ShopInv) : nat := match i with ShipPaid => 0 | BoFlag => 1 end.
Definition opL (g : bool) : list X6 := if g then [xOp] else [].
Definition shopRE (g : bool) (e : ShopEv) : X6 -> bool :=
  inL (match e with Pay => [xPd] | Ship => xSt :: opL g | Reserve => xRs :: opL g | Restock => [xSk] end).
Definition shopWE (e : ShopEv) : X6 -> bool :=
  inL (match e with Pay => [xPd] | Ship => [xSt] | Reserve => [xRs] | Restock => [xSk] end).
Definition shopRC (i : ShopInv) : X6 -> bool :=
  inL (match i with ShipPaid => [xSt; xPd] | BoFlag => [xBo; xRs; xSk] end).
Definition shopRR (i : ShopInv) : X6 -> bool :=
  inL (match i with ShipPaid => [] | BoFlag => [xRs; xSk] end).
Definition shopWR (i : ShopInv) : X6 -> bool :=
  inL (match i with ShipPaid => [xPd] | BoFlag => [xBo] end).

Definition shop (g : bool) : Reg X6 V3 S6 nat ShopEv ShopInv :=
  mkReg g6 mix6 nat_eq shopBlk (shopSh g) z6 (shopA g) [ShipPaid; BoFlag] shopChk shopRep
        shopBE shopBI (shopRE g) shopWE shopRC shopRR shopWR.

Definition shopVars (g : bool) (k : nat) : list X6 :=
  match k with
  | 0 => xSt :: xPd :: opL g
  | 1 => xSk :: xRs :: xBo :: opL g
  | 2 => [xOp]
  | _ => opL g
  end.

Definition shopFin (g : bool) : Fin X6 V3 S6 nat ShopEv :=
  mkFin X6_eq upd6 allV3 S6eqb (shopVars g) [Pay; Ship; Reserve; Restock] [0; 1].

Theorem shop_hyps : forall g, Hyps (shop g).
Proof.
  intros g. split; [split; [exact g6_mix | exact g6_ext]|]. split.
  - intros e. destruct g, e; (split; [local6 | inside6]).
  - intros i Hi. destruct g, i; (split; [plocal6|]; split; [local6|]; split; inside6).
Qed.

Theorem shop_fin : forall g, FinOK (shop g) (shopFin g).
Proof.
  intros g. split; [exact g6_upd|]. split; [exact allV3_complete|]. split; [exact S6eqb_spec|].
  split; [|split; [|split]].
  - intros k x. destruct g, k as [|[|[|k]]], x; simpl; split; intro H;
      repeat (destruct H as [H|H]; [try discriminate H|]); try tauto; try discriminate; reflexivity.
  - intros []; simpl; tauto.
  - intros i [<- | [<- | []]]; simpl; tauto.
  - intros []; simpl; tauto.
Qed.

(* The per-component check passes: 9 + 27 states without the shared flag, 27 + 81 with it. *)
Theorem shop_check : forall g, comp_check (shop g) (shopFin g) (fun _ => 1) = true.
Proof. intros []; vm_compute; reflexivity. Qed.

Theorem shop_converges : forall g, WFCb (shop g) 2 /\ Conv (shop g) 2.
Proof.
  intros g. destruct (proj1 (comp_check_exact (shop g) (shopFin g) (shop_hyps g) (shop_fin g) (fun _ => 1))
                        (shop_check g)) as [Hd Hc].
  split; [|exact Hc]. apply (bound_sum (shop g) (shop_hyps g) [0; 1] (fun _ => 1)); [|exact Hd].
  intros i [<- | [<- | []]]; simpl; tauto.
Qed.

(* Repair does fire: shipping unpaid and reserving beyond stock leave invariants violated. *)
Theorem shop_repair_fires : forall g,
  let s1 := mkS v0 v0 v0 v0 v0 v1 in
  valid (shop g) s1 = true /\ valid (shop g) (shopA g Ship s1) = false /\
  valid (shop g) (shopA g Reserve s1) = false.
Proof. intros []; vm_compute; repeat split. Qed.

(* The cost: each component's subspace, not the 3^6 = 729 states of the product. *)
Theorem shop_cost : forall g,
  length (enumSub (shop g) (shopFin g) (shopVars g 0)) = (if g then 27 else 9) /\
  length (enumSub (shop g) (shopFin g) (shopVars g 1)) = (if g then 81 else 27) /\
  length (enumSub (shop g) (shopFin g) [xSt; xPd; xSk; xRs; xBo; xOp]) = 729.
Proof. intros g. rewrite !enum_length. destruct g; repeat split. Qed.

(* No shared variable, zero background valid: gsm's literal component check is the component's. *)
Theorem shop_gsm_literal : forall k t, Sub (shop false) k t ->
  valid (shop false) t = validK (shop false) k t /\ rho (shop false) t = rhoK (shop false) k t.
Proof.
  apply (gsm_literal (shop false) (shop_hyps false)); [intros x; reflexivity | vm_compute; reflexivity].
Qed.

(* With the flag, the shared variable is read by both components and written by none. *)
Theorem shop_shared_read :
  csh (shop true) xOp = true /\ cRE (shop true) Ship xOp = true /\ cRE (shop true) Reserve xOp = true /\
  cbE (shop true) Ship <> cbE (shop true) Reserve /\
  (forall e, cWE (shop true) e xOp = false) /\ (forall i, cWR (shop true) i xOp = false).
Proof.
  repeat split; try reflexivity; [discriminate | intros []; reflexivity | intros []; reflexivity].
Qed.

(* ============================================================================================ *)
(* Boundaries. In each registry every component's check passes and the registry diverges; one  *)
(* hypothesis fails, and every other one holds.                                                 *)
(* ============================================================================================ *)

Inductive Two := Ea | Eb.

Definition twoBE (e : Two) : nat := match e with Ea => 0 | Eb => 1 end.
Definition none6 : X6 -> bool := fun _ => false.
Definition noChk (_ : unit) (_ : S6) : bool := true.
Definition noRep (_ : unit) (s : S6) : S6 := s.

Lemma twoBE_inj : forall k e e', twoBE e = k -> twoBE e' = k -> e = e'.
Proof. intros k [] [] H1 H2; subst; try discriminate; reflexivity. Qed.

(* ---- Footprints with writes only: pay writes paid; ship, guarded on paid, writes shipped. ---- *)

Definition psBlk (x : X6) : nat := match x with xPd => 0 | xSt => 1 | _ => 2 end.
Definition psA (e : Two) (s : S6) : S6 :=
  match e with
  | Ea => upd6 xPd v1 s
  | Eb => if V3eqb (sPd s) v1 then upd6 xSt v2 s else s
  end.
Definition psW (e : Two) : X6 -> bool := inL (match e with Ea => [xPd] | Eb => [xSt] end).

(* Declared footprints are the write sets: ship's read of paid is missing. *)
Definition ws : Reg X6 V3 S6 nat Two unit :=
  mkReg g6 mix6 nat_eq psBlk none6 z6 psA [] noChk noRep twoBE (fun _ => 0) psW psW
        (fun _ => none6) (fun _ => none6) (fun _ => none6).

Definition twoFin (v0s v1s : list X6) : Fin X6 V3 S6 nat Two :=
  mkFin X6_eq upd6 allV3 S6eqb (fun k => match k with 0 => v0s | 1 => v1s | _ => [] end) [Ea; Eb] [0; 1].

Theorem ws_other_hyps :
  StateOK ws /\ Local g6 (cRE ws Ea) (cWE ws Ea) (cA ws Ea) /\
  (forall e, Inside ws (cbE ws e) (cRE ws e) (cWE ws e)) /\ (forall i, In i (cinvs ws) -> InvOK ws i).
Proof.
  split; [split; [exact g6_mix | exact g6_ext]|]. split; [local6|]. split; [|intros i []].
  intros []; inside6.
Qed.

Theorem ws_ship_not_local : ~ Local g6 (cRE ws Eb) (cWE ws Eb) (cA ws Eb).
Proof.
  intros [_ H]. assert (Ha : agree g6 (cRE ws Eb) (mkS v0 v1 v0 v0 v0 v0) z6)
    by (intros [] Hx; try discriminate Hx; reflexivity).
  specialize (H _ _ Ha xSt eq_refl). vm_compute in H. discriminate H.
Qed.

Theorem ws_check_passes : comp_check ws (twoFin [xPd] [xSt]) (fun _ => 0) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ws_components_pass : forall k B, WFCk ws k B /\ ConvK ws k B.
Proof.
  intros k B. split; [intros t _; reflexivity|].
  intros t _ _ l1 l2 Hp HF. rewrite (perm_single _ l1 l2 (twoBE_inj k) HF Hp). reflexivity.
Qed.

Theorem ws_wfc : forall B, WFCb ws B.
Proof. intros B s. reflexivity. Qed.

Lemma ws_N : forall B u, N ws B u = u.
Proof. unfold N. intros B; induction B as [|B IH]; intros u; [reflexivity | apply IH]. Qed.

Theorem ws_diverges : forall B, ~ Conv ws B.
Proof.
  intros B H. specialize (H z6 eq_refl [Ea; Eb] [Eb; Ea] (perm_swap Eb Ea [])).
  cbn [run fold_left] in H. unfold G in H. rewrite !ws_N in H. vm_compute in H. discriminate H.
Qed.

(* With the read in the footprint, ship is local, and no split of paid and shipped fits it: the
   footprint forces them into one component (inside_merge). *)
Theorem ws_true_footprint :
  Local g6 (inL [xSt; xPd]) (inL [xSt]) (psA Eb) /\ ~ Inside ws 1 (inL [xSt; xPd]) (inL [xSt]) /\
  (forall k, Inside ws k (inL [xSt; xPd]) (inL [xSt]) -> cblk ws xPd = cblk ws xSt).
Proof.
  split; [local6|]. split.
  - intros [HR _]. specialize (HR xPd eq_refl). discriminate HR.
  - intros k Hk. exact (inside_merge ws k _ _ xPd xSt Hk eq_refl eq_refl eq_refl).
Qed.

(* ---- A repair that writes a variable of another component. ---- *)

Definition rcBlk (x : X6) : nat := match x with xSk => 0 | xRs => 1 | _ => 2 end.
Definition rcA (e : Two) (s : S6) : S6 :=
  match e with Ea => upd6 xSk v2 s | Eb => upd6 xRs v2 s end.
Definition rcW (e : Two) : X6 -> bool := inL (match e with Ea => [xSk] | Eb => [xRs] end).
Definition rcChk (_ : unit) (s : S6) : bool := negb (V3eqb (sSk s) v2).
(* Declared to write stock only, it also sets reserved, in component 1. *)
Definition rcRep (_ : unit) (s : S6) : S6 := upd6 xRs v1 (upd6 xSk v0 s).

Definition rc : Reg X6 V3 S6 nat Two unit :=
  mkReg g6 mix6 nat_eq rcBlk none6 z6 rcA [tt] rcChk rcRep twoBE (fun _ => 0) rcW rcW
        (fun _ => inL [xSk]) (fun _ => none6) (fun _ => inL [xSk]).

Theorem rc_other_hyps :
  StateOK rc /\ (forall e, EvOK rc e) /\ PLocal g6 (cRC rc tt) (cchk rc tt) /\
  Inside rc 0 (cRC rc tt) (fun _ => false) /\ Inside rc 0 (cRR rc tt) (cWR rc tt).
Proof.
  split; [split; [exact g6_mix | exact g6_ext]|]. split; [intros []; (split; [local6 | inside6])|].
  split; [plocal6|]. split; inside6.
Qed.

Theorem rc_repair_not_local : ~ Local g6 (cRR rc tt) (cWR rc tt) (crep rc tt).
Proof. intros [H _]. specialize (H z6 xRs eq_refl). discriminate H. Qed.

Theorem rc_check_passes : comp_check rc (twoFin [xSk] [xRs]) (fun _ => 1) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem rc_components_pass : WFCk rc 0 1 /\ (forall B, WFCk rc 1 B) /\ (forall k B, ConvK rc k B).
Proof.
  split; [intros [a b [] d e f] _; reflexivity|]. split; [intros B t _; reflexivity|].
  intros k B t _ _ l1 l2 Hp HF. rewrite (perm_single _ l1 l2 (twoBE_inj k) HF Hp). reflexivity.
Qed.

Theorem rc_wfc : WFCb rc 2.
Proof. intros [a b [] d e f]; reflexivity. Qed.

Theorem rc_diverges : ~ Conv rc 2.
Proof.
  intros H. specialize (H z6 eq_refl [Ea; Eb] [Eb; Ea] (perm_swap Eb Ea [])).
  vm_compute in H. discriminate H.
Qed.

(* ---- A shared variable written by one component: paid is shared, pay writes it. ---- *)

Definition swSh (x : X6) : bool := inL [xPd] x.
Definition swR (e : Two) : X6 -> bool := inL (match e with Ea => [xPd] | Eb => [xSt; xPd] end).

Definition sw : Reg X6 V3 S6 nat Two unit :=
  mkReg g6 mix6 nat_eq psBlk swSh z6 psA [] noChk noRep twoBE (fun _ => 0) swR psW
        (fun _ => none6) (fun _ => none6) (fun _ => none6).

Theorem sw_other_hyps :
  StateOK sw /\ (forall e, Local g6 (cRE sw e) (cWE sw e) (cA sw e)) /\
  Inside sw 1 (cRE sw Eb) (cWE sw Eb) /\ (forall x, cRE sw Ea x = true -> home sw 0 x = true) /\
  (forall i, In i (cinvs sw) -> InvOK sw i).
Proof.
  split; [split; [exact g6_mix | exact g6_ext]|]. split; [intros []; local6|].
  split; [inside6|]. split; [intros [] Hx; try discriminate Hx; reflexivity | intros i []].
Qed.

Theorem sw_pay_writes_shared : ~ Inside sw 0 (cRE sw Ea) (cWE sw Ea).
Proof. intros [_ HW]. destruct (HW xPd eq_refl) as [_ H]. discriminate H. Qed.

Theorem sw_check_passes : comp_check sw (twoFin [xPd] [xSt; xPd]) (fun _ => 0) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sw_components_pass : forall k B, WFCk sw k B /\ ConvK sw k B.
Proof.
  intros k B. split; [intros t _; reflexivity|].
  intros t _ _ l1 l2 Hp HF. rewrite (perm_single _ l1 l2 (twoBE_inj k) HF Hp). reflexivity.
Qed.

Lemma sw_N : forall B u, N sw B u = u.
Proof. unfold N. intros B; induction B as [|B IH]; intros u; [reflexivity | apply IH]. Qed.

Theorem sw_diverges : forall B, ~ Conv sw B.
Proof.
  intros B H. specialize (H z6 eq_refl [Ea; Eb] [Eb; Ea] (perm_swap Eb Ea [])).
  cbn [run fold_left] in H. unfold G in H. rewrite !sw_N in H. vm_compute in H. discriminate H.
Qed.

(* ============================================================================================ *)
(* Combinator rules (AstChecker's grammar, gsm's combinators): footprints are extracted from    *)
(* the rules, decidably, and over-approximate what the rules read and write.                    *)
(* ============================================================================================ *)

Section AstFootprint.
  Local Notation rd := AstChecker.rd.
  Local Notation wr := AstChecker.wr.

  (* gsm's vars (predicate), readVars and writeVars (transform). *)
  Fixpoint readsE (e : AstChecker.expr) : list nat :=
    match e with
    | AstChecker.EVar i => [i]
    | AstChecker.ELit _ => []
    | AstChecker.EAdd a b | AstChecker.ESub a b => readsE a ++ readsE b
    end.
  Definition readsP (p : AstChecker.pred) : list nat := flat_map readsE (AstChecker.exprsP p).
  Definition readsT (t : AstChecker.transform) : list nat := flat_map (fun a => readsE (snd a)) t.
  Definition writesT (t : AstChecker.transform) : list nat := map fst t.

  Definition inN (l : list nat) (x : nat) : bool := existsb (Nat.eqb x) l.

  Lemma inN_spec : forall l x, inN l x = true <-> In x l.
  Proof.
    intros l x. unfold inN. rewrite existsb_exists. split.
    - intros [y [Hy E1]]. apply Nat.eqb_eq in E1. subst. exact Hy.
    - intros H. exists x. split; [exact H | apply Nat.eqb_refl].
  Qed.

  Lemma evalE_reads : forall mins e s t,
    (forall i, In i (readsE e) -> rd i s = rd i t) ->
    AstChecker.evalE mins s e = AstChecker.evalE mins t e.
  Proof.
    intros mins e s t; induction e as [i | n | a IHa b IHb | a IHa b IHb]; intros H; simpl.
    - rewrite (H i (or_introl eq_refl)). reflexivity.
    - reflexivity.
    - rewrite IHa, IHb; [reflexivity | |]; intros i Hi; apply H; simpl; apply in_or_app; tauto.
    - rewrite IHa, IHb; [reflexivity | |]; intros i Hi; apply H; simpl; apply in_or_app; tauto.
  Qed.

  (* Induction over predicates with nested lists. *)
  Section PredInd.
    Variable P : AstChecker.pred -> Prop.
    Hypothesis HLe : forall a b, P (AstChecker.PLe a b).
    Hypothesis HLt : forall a b, P (AstChecker.PLt a b).
    Hypothesis HEq : forall a b, P (AstChecker.PEq a b).
    Hypothesis HAnd : forall ps, Forall P ps -> P (AstChecker.PAnd ps).
    Hypothesis HOr : forall ps, Forall P ps -> P (AstChecker.POr ps).
    Hypothesis HNot : forall p, P p -> P (AstChecker.PNot p).

    Fixpoint pred_ind' (p : AstChecker.pred) : P p :=
      match p with
      | AstChecker.PLe a b => HLe a b
      | AstChecker.PLt a b => HLt a b
      | AstChecker.PEq a b => HEq a b
      | AstChecker.PAnd ps => HAnd ps ((fix go (l : list AstChecker.pred) : Forall P l :=
          match l with
          | [] => @Forall_nil _ P
          | q :: l' => @Forall_cons _ P q l' (pred_ind' q) (go l')
          end) ps)
      | AstChecker.POr ps => HOr ps ((fix go (l : list AstChecker.pred) : Forall P l :=
          match l with
          | [] => @Forall_nil _ P
          | q :: l' => @Forall_cons _ P q l' (pred_ind' q) (go l')
          end) ps)
      | AstChecker.PNot q => HNot q (pred_ind' q)
      end.
  End PredInd.

  Lemma readsP_in : forall p e i, In e (AstChecker.exprsP p) -> In i (readsE e) -> In i (readsP p).
  Proof. intros p e i He Hi. unfold readsP. apply in_flat_map. exists e. split; assumption. Qed.

  Lemma readsP_cons : forall q ps i,
    (In i (readsP q) -> In i (readsP (AstChecker.PAnd (q :: ps)))) /\
    (In i (readsP (AstChecker.PAnd ps)) -> In i (readsP (AstChecker.PAnd (q :: ps)))) /\
    (In i (readsP q) -> In i (readsP (AstChecker.POr (q :: ps)))) /\
    (In i (readsP (AstChecker.POr ps)) -> In i (readsP (AstChecker.POr (q :: ps)))).
  Proof.
    intros q ps i. unfold readsP. rewrite !in_flat_map.
    repeat split; intros [e [He Hi]]; exists e; (split; [|exact Hi]); simpl; apply in_or_app; tauto.
  Qed.

  Lemma evalP_reads : forall mins p s t,
    (forall i, In i (readsP p) -> rd i s = rd i t) ->
    AstChecker.evalP mins s p = AstChecker.evalP mins t p.
  Proof.
    intros mins p.
    apply (pred_ind' (fun p => forall s t, (forall i, In i (readsP p) -> rd i s = rd i t) ->
                                 AstChecker.evalP mins s p = AstChecker.evalP mins t p)); clear p.
    - intros a b s t H. simpl. rewrite (evalE_reads mins a s t), (evalE_reads mins b s t);
        [reflexivity | |]; intros i Hi; apply H; [apply (readsP_in _ b) | apply (readsP_in _ a)];
        simpl; tauto.
    - intros a b s t H. simpl. rewrite (evalE_reads mins a s t), (evalE_reads mins b s t);
        [reflexivity | |]; intros i Hi; apply H; [apply (readsP_in _ b) | apply (readsP_in _ a)];
        simpl; tauto.
    - intros a b s t H. simpl. rewrite (evalE_reads mins a s t), (evalE_reads mins b s t);
        [reflexivity | |]; intros i Hi; apply H; [apply (readsP_in _ b) | apply (readsP_in _ a)];
        simpl; tauto.
    - intros ps HF s t H. simpl. induction HF as [|q ps Hq HF IH]; [reflexivity|]. simpl.
      rewrite (Hq s t), IH; [reflexivity | |]; intros i Hi; apply H;
        first [apply (proj1 (readsP_cons q ps i)), Hi | apply (proj1 (proj2 (readsP_cons q ps i))), Hi].
    - intros ps HF s t H. simpl. induction HF as [|q ps Hq HF IH]; [reflexivity|]. simpl.
      rewrite (Hq s t), IH; [reflexivity | |]; intros i Hi; apply H;
        first [apply (proj1 (proj2 (proj2 (readsP_cons q ps i)))), Hi
              | apply (proj2 (proj2 (proj2 (readsP_cons q ps i)))), Hi].
    - intros q Hq s t H. simpl. rewrite (Hq s t H). reflexivity.
  Qed.

  Lemma rd_wr_ne : forall s i j v, j <> i -> rd j (wr i v s) = rd j s.
  Proof. intros s i j v H. rewrite !AstChecker.rd_nth. apply AstChecker.wr_nth_neq, H. Qed.

  Lemma rd_wr_same : forall s t i v, length s = length t -> rd i (wr i v s) = rd i (wr i v t).
  Proof.
    intros s t i v Hl. rewrite !AstChecker.rd_nth. destruct (Nat.lt_ge_cases i (length s)) as [Hi | Hi].
    - rewrite !AstChecker.wr_nth_eq by lia. reflexivity.
    - rewrite !nth_overflow; [reflexivity | |]; rewrite AstChecker.wr_length; lia.
  Qed.

  Lemma applyT_len : forall m t s, length (AstChecker.applyT m t s) = length s.
  Proof.
    intros m t; induction t as [|[i e] t IH]; intros s; simpl; [reflexivity|].
    rewrite IH. unfold AstChecker.setClamped. apply AstChecker.wr_length.
  Qed.

  (* A transform writes only its targets. *)
  Lemma applyT_writes : forall m t s j, ~ In j (writesT t) -> rd j (AstChecker.applyT m t s) = rd j s.
  Proof.
    intros m t; induction t as [|[i e] t IH]; intros s j Hj; simpl; [reflexivity|].
    simpl in Hj. rewrite IH by tauto. unfold AstChecker.setClamped. apply rd_wr_ne.
    intro E1. apply Hj. left. congruence.
  Qed.

  (* A transform's values on a read-closed set depend only on that set. *)
  Lemma applyT_reads : forall m t (R : nat -> bool) s s', length s = length s' ->
    (forall i, In i (readsT t) -> R i = true) ->
    (forall i, R i = true -> rd i s = rd i s') ->
    forall j, R j = true \/ In j (writesT t) ->
    rd j (AstChecker.applyT m t s) = rd j (AstChecker.applyT m t s').
  Proof.
    intros m t; induction t as [|[i e] t IH]; intros R s s' Hl HR Hag j Hj; simpl.
    - destruct Hj as [Hj | []]. apply Hag, Hj.
    - assert (Hv : AstChecker.evalE (AstChecker.mins m) s e = AstChecker.evalE (AstChecker.mins m) s' e).
      { apply evalE_reads. intros x Hx. apply Hag, HR. simpl. apply in_or_app. left. exact Hx. }
      rewrite <- Hv. unfold AstChecker.setClamped.
      set (c := Init.Nat.min _ _).
      assert (Hl1 : length (wr i c s) = length (wr i c s')) by (rewrite !AstChecker.wr_length; exact Hl).
      assert (Hag1 : forall x, R x = true -> rd x (wr i c s) = rd x (wr i c s')).
      { intros x Hx. destruct (Nat.eq_dec x i) as [-> | Hne].
        - apply rd_wr_same, Hl.
        - rewrite !rd_wr_ne by exact Hne. apply Hag, Hx. }
      assert (HR1 : forall x, In x (readsT t) -> R x = true).
      { intros x Hx. apply HR. simpl. apply in_or_app. right. exact Hx. }
      destruct (in_dec Nat.eq_dec j (writesT t)) as [Hw | Hw].
      + apply (IH R _ _ Hl1 HR1 Hag1). right. exact Hw.
      + destruct (R j) eqn:Rj.
        * apply (IH R _ _ Hl1 HR1 Hag1). left. exact Rj.
        * destruct Hj as [Hj | [Hj | Hj]]; [discriminate | | contradiction].
          simpl in Hj. subst j. rewrite !applyT_writes by exact Hw. apply rd_wr_same, Hl.
  Qed.

  (* Valuations of a fixed length n: the state type of a combinator registry. *)
  Definition Val (n : nat) : Type := { s : list nat | length s = n }.

  Variable n : nat.

  Definition vget (s : Val n) (x : nat) : nat := rd x (proj1_sig s).

  Fixpoint build (f : nat -> nat) (a k : nat) : list nat :=
    match k with 0 => [] | S k' => f a :: build f (S a) k' end.

  Lemma build_len : forall f a k, length (build f a k) = k.
  Proof. intros f a k; revert a; induction k as [|k IH]; intros a; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma build_rd : forall f k a x, rd x (build f a k) = if Nat.ltb x k then f (a + x) else 0.
  Proof.
    intros f k; induction k as [|k IH]; intros a x; simpl; [destruct x; reflexivity|].
    destruct x as [|x]; simpl; [rewrite Nat.add_0_r; reflexivity|].
    rewrite IH. destruct (Nat.ltb_spec x k), (Nat.ltb_spec (S x) (S k)); try lia.
    all: try reflexivity. all: f_equal; lia.
  Qed.

  Lemma rd_beyond : forall s x, length s <= x -> rd x s = 0.
  Proof. intros s x H. rewrite AstChecker.rd_nth. apply nth_overflow, H. Qed.

  Definition vmix (C : nat -> bool) (s t : Val n) : Val n :=
    exist _ (build (fun x => if C x then vget s x else vget t x) 0 n) (build_len _ 0 n).

  Lemma list_rd_ext : forall l1 l2, length l1 = length l2 -> (forall x, rd x l1 = rd x l2) -> l1 = l2.
  Proof.
    induction l1 as [|a l1 IH]; intros [|b l2] Hl H; simpl in Hl; try discriminate; [reflexivity|].
    f_equal; [exact (H 0) | apply IH; [lia | intros x; exact (H (S x))]].
  Qed.

  Lemma Val_eq : forall s t : Val n, proj1_sig s = proj1_sig t -> s = t.
  Proof.
    intros [l Hl] [l' Hl'] E1. simpl in E1. subst l'. f_equal. apply UIP_dec, Nat.eq_dec.
  Qed.

  Lemma vget_mix : forall C s t x, vget (vmix C s t) x = if C x then vget s x else vget t x.
  Proof.
    intros C [l Hl] [l' Hl'] x. unfold vget, vmix. simpl. rewrite build_rd.
    destruct (Nat.ltb_spec x n) as [Hx | Hx]; [reflexivity|].
    rewrite !rd_beyond by lia. destruct (C x); reflexivity.
  Qed.

  Lemma vget_ext : forall s t : Val n, (forall x, vget s x = vget t x) -> s = t.
  Proof.
    intros [l Hl] [l' Hl'] H. apply Val_eq. simpl. apply list_rd_ext; [congruence | exact H].
  Qed.

  Definition vlift (f : list nat -> list nat) (Hf : forall s, length (f s) = length s) (s : Val n) : Val n :=
    exist _ (f (proj1_sig s)) (eq_trans (Hf _) (proj2_sig s)).

  Variable m : AstChecker.machine.

  Definition rawE (ge : AstChecker.gevent) (s : list nat) : list nat :=
    if AstChecker.evalP (AstChecker.mins m) s (fst ge) then AstChecker.applyT m (snd ge) s else s.

  Lemma rawE_len : forall ge s, length (rawE ge s) = length s.
  Proof. intros ge s. unfold rawE. destruct (AstChecker.evalP _ _ _); [apply applyT_len | reflexivity]. Qed.

  Definition RdE (ge : AstChecker.gevent) : nat -> bool :=
    inN (readsP (fst ge) ++ readsT (snd ge) ++ writesT (snd ge)).
  Definition WrE (ge : AstChecker.gevent) : nat -> bool := inN (writesT (snd ge)).

  (* The extracted footprints satisfy the framework's hypotheses. *)
  Theorem ast_event_local : forall ge, Local vget (RdE ge) (WrE ge) (vlift (rawE ge) (rawE_len ge)).
  Proof.
    intros [g t]. unfold RdE, WrE, vget, vlift, rawE. simpl. split.
    - intros [s Hs] x Hx. simpl. destruct (AstChecker.evalP _ s g); [|reflexivity].
      apply applyT_writes. intros Hin. apply inN_spec in Hin. congruence.
    - intros [s Hs] [s' Hs'] H x Hx. unfold agree, vget in H. simpl in *.
      assert (Hag : forall i, inN (readsP g ++ readsT t ++ writesT t) i = true -> rd i s = rd i s')
        by exact H.
      rewrite (evalP_reads _ g s s').
      + destruct (AstChecker.evalP _ s' g).
        * apply (applyT_reads m t (inN (readsP g ++ readsT t ++ writesT t)) s s'
                   (eq_trans Hs (eq_sym Hs'))); [| exact Hag |].
          -- intros i Hi. apply inN_spec. apply in_or_app. right. apply in_or_app. left. exact Hi.
          -- right. apply inN_spec, Hx.
        * apply Hag, inN_spec. apply in_or_app. right. apply in_or_app. right. apply inN_spec, Hx.
      + intros i Hi. apply Hag, inN_spec. apply in_or_app. left. exact Hi.
  Qed.

  Theorem ast_check_local : forall p,
    PLocal vget (inN (readsP p)) (fun s => AstChecker.evalP (AstChecker.mins m) (proj1_sig s) p).
  Proof.
    intros p [s Hs] [s' Hs'] H. simpl. apply evalP_reads. intros i Hi. apply (H i), inN_spec, Hi.
  Qed.

  Theorem ast_repair_local : forall t,
    Local vget (inN (readsT t)) (inN (writesT t)) (vlift (AstChecker.applyT m t) (applyT_len m t)).
  Proof.
    intros t. unfold vget, vlift. split.
    - intros [s Hs] x Hx. simpl. apply applyT_writes. intros Hin. apply inN_spec in Hin. congruence.
    - intros [s Hs] [s' Hs'] H x Hx. simpl in *.
      apply (applyT_reads m t (inN (readsT t)) s s' (eq_trans Hs (eq_sym Hs'))).
      + intros i Hi. apply inN_spec, Hi.
      + exact H.
      + right. apply inN_spec, Hx.
  Qed.

  (* The registry of a combinator machine, with a component assignment (gsm's union-find). *)
  Variable blkv : nat -> nat.
  Variable shv : nat -> bool.
  Variable bEv : AstChecker.gevent -> nat.
  Variable bIv : AstChecker.pred * AstChecker.transform -> nat.

  Definition zeroVal : Val n := exist _ (repeat 0 n) (repeat_length 0 n).

  Definition astReg : Reg nat nat (Val n) nat nat (AstChecker.pred * AstChecker.transform) :=
    mkReg vget vmix nat_eq blkv shv zeroVal
      (fun e => vlift (rawE (AstChecker.evAt m e)) (rawE_len _))
      (AstChecker.invs m)
      (fun i s => AstChecker.evalP (AstChecker.mins m) (proj1_sig s) (fst i))
      (fun i => vlift (AstChecker.applyT m (snd i)) (applyT_len m (snd i)))
      (fun e => bEv (AstChecker.evAt m e)) bIv
      (fun e => RdE (AstChecker.evAt m e)) (fun e => WrE (AstChecker.evAt m e))
      (fun i => inN (readsP (fst i))) (fun i => inN (readsT (snd i))) (fun i => inN (writesT (snd i))).

  (* The decidable component check on the extracted footprints. *)
  Definition homeB (k x : nat) : bool := Nat.eqb (blkv x) k || shv x.
  Definition ownB (k x : nat) : bool := Nat.eqb (blkv x) k && negb (shv x).

  Definition blocks_ok : bool :=
    forallb (fun ge =>
      forallb (homeB (bEv ge)) (readsP (fst ge) ++ readsT (snd ge) ++ writesT (snd ge)) &&
      forallb (ownB (bEv ge)) (writesT (snd ge))) (AstChecker.evs m) &&
    forallb (fun iv =>
      forallb (homeB (bIv iv)) (readsP (fst iv)) && forallb (homeB (bIv iv)) (readsT (snd iv)) &&
      forallb (ownB (bIv iv)) (writesT (snd iv))) (AstChecker.invs m).

  Lemma nat_eq_eqb : forall a b, (if nat_eq a b then true else false) = Nat.eqb a b.
  Proof. intros a b. destruct (nat_eq a b) as [-> | H]; [symmetry; apply Nat.eqb_refl | symmetry; apply Nat.eqb_neq, H]. Qed.

  Lemma inside_of_check : forall k (Rl Wl : list nat),
    forallb (homeB k) Rl = true -> forallb (ownB k) Wl = true ->
    Inside astReg k (inN Rl) (inN Wl).
  Proof.
    intros k Rl Wl HR HW. rewrite forallb_forall in HR, HW. split.
    - intros x Hx. apply inN_spec in Hx. specialize (HR x Hx). unfold homeB in HR.
      unfold home, own. simpl. rewrite nat_eq_eqb. exact HR.
    - intros x Hx. apply inN_spec in Hx. specialize (HW x Hx). unfold ownB in HW.
      apply andb_true_iff in HW. destruct HW as [H1 H2]. unfold own. simpl. rewrite nat_eq_eqb.
      split; [exact H1 | apply negb_true_iff, H2].
  Qed.

  (* gsm's computed footprints are sound: if the check accepts the component assignment, the
     registry satisfies every hypothesis of the decomposition theorems. *)
  Theorem ast_hyps : blocks_ok = true -> Hyps astReg.
  Proof.
    intros Hok. unfold blocks_ok in Hok. apply andb_true_iff in Hok. destruct Hok as [He Hi].
    rewrite forallb_forall in He, Hi.
    split; [split; [exact vget_mix | exact vget_ext]|]. split.
    - intros e. split; [apply ast_event_local|]. simpl.
      destruct (nth_in_or_default e (AstChecker.evs m) AstChecker.noEvent) as [Hin | Hd].
      + specialize (He _ Hin). apply andb_true_iff in He. destruct He as [H1 H2].
        unfold AstChecker.evAt. apply inside_of_check; assumption.
      + unfold AstChecker.evAt. rewrite Hd. split; intros x Hx; discriminate Hx.
    - intros i Hin. specialize (Hi i Hin). apply andb_true_iff in Hi. destruct Hi as [Hi H3].
      apply andb_true_iff in Hi. destruct Hi as [H1 H2].
      split; [apply ast_check_local|]. split; [apply ast_repair_local|]. split.
      + split; [|intros x Hx; discriminate Hx]. intros x Hx. apply inN_spec in Hx.
        rewrite forallb_forall in H1. specialize (H1 x Hx). unfold homeB in H1.
        unfold home, own. simpl. rewrite nat_eq_eqb. exact H1.
      + apply inside_of_check; assumption.
  Qed.

  (* The registry's repair and normalization are AstChecker's (the verified rules oracle's). *)
  Theorem ast_rho_repair1 : forall s, proj1_sig (rho astReg s) = AstChecker.repair1 m (proj1_sig s).
  Proof.
    intros s. unfold rho, AstChecker.repair1. simpl. generalize (AstChecker.invs m) as l.
    induction l as [|i l IH]; simpl; [reflexivity|].
    destruct (AstChecker.evalP _ _ (fst i)); simpl; [apply IH | reflexivity].
  Qed.

  Theorem ast_N_normalize : forall B s,
    proj1_sig (N astReg B s) = AstChecker.normalize m B (proj1_sig s).
  Proof.
    unfold N. intros B; induction B as [|B IH]; intros s; [reflexivity|].
    change (iter (S B) (rho astReg) s) with (iter B (rho astReg) (rho astReg s)).
    cbn [AstChecker.normalize].
    destruct (AstChecker.allValid m (proj1_sig s)) eqn:V.
    - assert (Hv : validL astReg (cinvs astReg) s = true) by exact V.
      assert (Hr : rho astReg s = s) by (unfold rho; apply repL_valid; exact Hv).
      rewrite Hr. unfold rho. rewrite (iter_fix astReg _ B s Hv). reflexivity.
    - rewrite IH, ast_rho_repair1. reflexivity.
  Qed.
End AstFootprint.

(* Non-vacuity: two variables in two components; an event and an invariant in each. *)
Definition ast_demo_m : AstChecker.machine :=
  {| AstChecker.doms := [3; 3]; AstChecker.mins := [0%Z; 0%Z];
     AstChecker.invs := [ (AstChecker.PLe (AstChecker.EVar 0) (AstChecker.ELit 1), [(0, AstChecker.ELit 1)]);
                          (AstChecker.PLe (AstChecker.EVar 1) (AstChecker.ELit 1), [(1, AstChecker.ELit 0)]) ];
     AstChecker.evs := [ (AstChecker.PAnd [], [(0, AstChecker.EAdd (AstChecker.EVar 0) (AstChecker.ELit 1))]);
                         (AstChecker.PLe (AstChecker.EVar 1) (AstChecker.ELit 0),
                            [(1, AstChecker.EAdd (AstChecker.EVar 1) (AstChecker.ELit 2))]) ] |}.

Definition ast_demo_blk (x : nat) : nat := x.
Definition ast_demo_bE (ge : AstChecker.gevent) : nat := hd 0 (writesT (snd ge)).
Definition ast_demo_bI (iv : AstChecker.pred * AstChecker.transform) : nat := hd 0 (writesT (snd iv)).

Theorem ast_demo : blocks_ok ast_demo_m ast_demo_blk (fun _ => false) ast_demo_bE ast_demo_bI = true /\
  Hyps (astReg 2 ast_demo_m ast_demo_blk (fun _ => false) ast_demo_bE ast_demo_bI).
Proof.
  assert (H : blocks_ok ast_demo_m ast_demo_blk (fun _ => false) ast_demo_bE ast_demo_bI = true)
    by (vm_compute; reflexivity).
  split; [exact H | apply ast_hyps, H].
Qed.
