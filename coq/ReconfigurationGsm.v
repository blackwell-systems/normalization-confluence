(* ReconfigurationGsm.v: the two steps of gsm's migration check under a delivery class that rested
   on gsm's own argument (gsm docs/theory.md section 11.11), mechanized in the model gsm runs
   (section Det of ReconfigurationClosure.v and ReconfigurationDelivery.v). Axiom-free.

   1. Declared closure pruning (section DeclPruned). ClosureI (ReconfigurationDelivery.v) is the
      pair closure seeded with the declared pairs only. gsm searches a pruned form, PCIg: seeds
      only for the declared pairs in one orientation sel a b (gsm: the event index order i < j),
      only where the two states differ, closed only into pairs of different states.
      - closureIg_exact: for a symmetric declared relation I and an orientation covering every pair
        (a = b \/ sel a b \/ sel b a), ClosureIg <-> ClosureI; closureIg_witness_iff: the pruned
        closure has a pair obs separates iff the unpruned one does (no finiteness), and on finite
        instances closureIg_witness_exact: ~ ClosureI <-> a PCIg witness exists, so
        closureI_witness_exact transfers to the pruned search.
      - closureI_symmetrize: ClosureI I <-> ClosureI (symI I), so for any I the pruned search over
        the symmetrized relation (what gsm's declaredPairs computes: an unordered pair is kept when
        either orientation is declared) is exact, closureIg_sym_exact.
      - barrier_declared_pruned_exact: barrier_declared_exact with the pruned closure.
      - Symmetry is needed: pruning_needs_symmetry, an asymmetric relation (true before false only,
        orientation false before true) whose pruned closure is empty while ClosureI has a pair the
        migration separates (lww with partialM).
      - Non-vacuity: declared_pruned_instances (lww with mergeM and partialM, every distinct pair
        declared: the pruned search certifies one and refutes the other), declared_barrier_instances
        (through the pruned theorem: mergeM BarrierOnly, partialM Unsafe).

   2. At-least-once with repeated submissions (sections Labels, Submissions). In gsm an event may be
      submitted any number of times, each submission a fresh message. Messages are pairs (event,
      submission number): EA * nat before the switch, EB * nat after it; a message steps as its
      event, an in-flight A-message translates to (tau a, k). Free delivery, every message at least
      once: Adm = AdmF, and two runs are compared by SameSet over messages (the same submissions)
      or, as gsm's witnesses compare them (migration.go, witness: sameSet of the old events and of
      the new events), by RelG, the same set of events.
      - commnd_fresh, idemnd_fresh (section Labels): when every sequence of events is the label
        sequence of a duplicate-free sequence of messages (SubFresh, the fresh-submission
        hypothesis), commutation and idempotence after duplicate-free prefixes (CommND, IdemND) over
        messages are commutation and idempotence at every reachable state. subfresh_tg,
        subfresh_tagX: gsm's model satisfies SubFresh.
      - submissions_live_exact, submissions_barrier_exact: the live and barrier conditions of the
        submission model are gsm's checks: PermB-start, Idem-start and DS1; PermB-every,
        Idem-every, AbsorbFree (gsm's AbsorbS: at every state reached by a run that applied a) and
        AmodFree over events (gsm's AmodA: runs with the same set of events, each any number of
        times).
      - gsm_alo_live_exact, gsm_alo_barrier_exact: the same with gsm's comparison RelG.
      - submissions_one_message_live, submissions_one_message_barrier: the submission model and the
        one-message model of ReconfigurationDelivery.v (each event one message, redelivered) have
        the same live and barrier outcomes, with either comparison.
      - classify_submissions_complete: on finite instances the outcome in gsm's model is decided
        with no unknown case (from classify_alo_complete through the bridge);
        amodfree_search_exact: AmodFree is the search gsm runs, over pairs of a state and the set
        of events applied: two nodes with the same set migrate to equivalent states.
      - Instances: rescaled_max (Online, every check holding), count_dup_prefix (DS1 failing at a
        second submission), reset_straddle (Unsafe by AbsorbS alone), and the lww instances of
        ReconfigurationClosure.v classified Online, BarrierOnly and Unsafe by
        classify_submissions_complete (submission_instances_classified). *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Trace NC.AtLeastOnce NC.AtLeastOnceExact NC.Reconfiguration
  NC.ReconfigurationClosure NC.ReconfigurationDelivery.
Import ListNotations.

(* ============================================================================================ *)
(* 1. Declared closure pruning.                                                                  *)
(* ============================================================================================ *)

Section DeclPruned.
  Context {S E O : Type}.
  Variable step : E -> S -> S.
  Variable obs : S -> O.
  Variable eqv : O -> O -> Prop.
  Hypothesis eqv_refl : forall x, eqv x x.
  Hypothesis eqv_sym : forall x y, eqv x y -> eqv y x.
  Variable eqS : forall a b : S, {a = b} + {a <> b}.
  Variable I : E -> E -> Prop.
  Variable sel : E -> E -> Prop.
  Hypothesis sel_cover : forall a b, a = b \/ sel a b \/ sel b a.

  Local Notation run := (runT step).

  (* gsm's declared search: one orientation per declared pair, seeds only where the two states
     differ, pairs of equal states not expanded. *)
  Inductive PCIg (s0 : S) : S -> S -> Prop :=
  | pcig_seed : forall u a b, sel a b -> I a b ->
      step b (step a (run u s0)) <> step a (step b (run u s0)) ->
      PCIg s0 (step b (step a (run u s0))) (step a (step b (run u s0)))
  | pcig_step : forall e x y, PCIg s0 x y -> step e x <> step e y -> PCIg s0 (step e x) (step e y).

  Definition ClosureIg (s0 : S) : Prop := forall x y, PCIg s0 x y -> eqv (obs x) (obs y).

  Lemma pcig_pci : forall s0 x y, PCIg s0 x y -> PCI step I s0 x y.
  Proof.
    intros s0 x y H. induction H as [u a b _ Hab _ | e x y _ IH _].
    - apply pci_seed. exact Hab.
    - apply pci_step. exact IH.
  Qed.

  Lemma pci_pcig : (forall a b, I a b -> I b a) ->
    forall s0 x y, PCI step I s0 x y -> x = y \/ PCIg s0 x y \/ PCIg s0 y x.
  Proof.
    intros Isym s0 x y H. induction H as [u a b Hab | e x y _ IH].
    - destruct (eqS (step b (step a (run u s0))) (step a (step b (run u s0)))) as [Eq | Ne];
        [left; exact Eq |].
      destruct (sel_cover a b) as [-> | [Hs | Hs]].
      + left. reflexivity.
      + right. left. apply pcig_seed; assumption.
      + right. right. apply pcig_seed; [exact Hs | apply Isym; exact Hab |].
        intro Eq. apply Ne. symmetry. exact Eq.
    - destruct (eqS (step e x) (step e y)) as [Eq | Ne]; [left; exact Eq |].
      destruct IH as [-> | [IH | IH]].
      + left. reflexivity.
      + right. left. apply pcig_step; assumption.
      + right. right. apply pcig_step; [exact IH |]. intro Eq. apply Ne. symmetry. exact Eq.
  Qed.

  Theorem closureIg_exact : (forall a b, I a b -> I b a) ->
    forall s0, ClosureIg s0 <-> ClosureI step obs eqv I s0.
  Proof.
    intros Isym s0. split.
    - intros H x y P. destruct (pci_pcig Isym s0 x y P) as [-> | [G | G]].
      + apply eqv_refl.
      + apply H. exact G.
      + apply eqv_sym. apply H. exact G.
    - intros H x y G. apply H. apply pcig_pci. exact G.
  Qed.

  (* The pruned search finds a separated pair iff the unpruned closure has one (no finiteness). *)
  Theorem closureIg_witness_iff : (forall a b, I a b -> I b a) -> forall s0,
    (exists x y, PCIg s0 x y /\ ~ eqv (obs x) (obs y)) <->
    (exists x y, PCI step I s0 x y /\ ~ eqv (obs x) (obs y)).
  Proof.
    intros Isym s0. split.
    - intros [x [y [G N]]]. exists x, y. split; [apply pcig_pci; exact G | exact N].
    - intros [x [y [P N]]]. destruct (pci_pcig Isym s0 x y P) as [-> | [G | G]].
      + exfalso. apply N. apply eqv_refl.
      + exists x, y. split; assumption.
      + exists y, x. split; [exact G |]. intro K. apply N. apply eqv_sym. exact K.
  Qed.
End DeclPruned.

(* Symmetrizing the declared relation changes nothing: the mirror of a seed is the mirrored pair. *)
Definition symI {E : Type} (I : E -> E -> Prop) (a b : E) : Prop := I a b \/ I b a.

Lemma symI_sym : forall {E : Type} (I : E -> E -> Prop) a b, symI I a b -> symI I b a.
Proof. intros E I a b [H | H]; [right | left]; exact H. Qed.

Lemma pci_symI : forall {S E : Type} (step : E -> S -> S) (I : E -> E -> Prop) s0 x y,
  PCI step (symI I) s0 x y -> PCI step I s0 x y \/ PCI step I s0 y x.
Proof.
  intros S E step I s0 x y H. induction H as [u a b [Hab | Hba] | e x y _ [IH | IH]].
  - left. apply pci_seed. exact Hab.
  - right. apply pci_seed. exact Hba.
  - left. apply pci_step. exact IH.
  - right. apply pci_step. exact IH.
Qed.

Lemma pci_I_symI : forall {S E : Type} (step : E -> S -> S) (I : E -> E -> Prop) s0 x y,
  PCI step I s0 x y -> PCI step (symI I) s0 x y.
Proof.
  intros S E step I s0 x y H. induction H as [u a b Hab | e x y _ IH].
  - apply pci_seed. left. exact Hab.
  - apply pci_step. exact IH.
Qed.

Theorem closureI_symmetrize : forall {S E O : Type} (step : E -> S -> S) (obs : S -> O)
  (eqv : O -> O -> Prop), (forall x y, eqv x y -> eqv y x) ->
  forall I s0, ClosureI step obs eqv I s0 <-> ClosureI step obs eqv (symI I) s0.
Proof.
  intros S E O step obs eqv eqv_sym I s0. split.
  - intros H x y P. destruct (pci_symI step I s0 x y P) as [Q | Q]; [apply H; exact Q |].
    apply eqv_sym. apply H. exact Q.
  - intros H x y P. apply H. apply pci_I_symI. exact P.
Qed.

(* gsm's declaredPairs keeps an unordered pair when either orientation is declared: the pruned
   search over symI I is exact for every declared relation I. *)
Theorem closureIg_sym_exact : forall {S E O : Type} (step : E -> S -> S) (obs : S -> O)
  (eqv : O -> O -> Prop), (forall x, eqv x x) -> (forall x y, eqv x y -> eqv y x) ->
  forall (eqS : forall a b : S, {a = b} + {a <> b}) (sel : E -> E -> Prop),
  (forall a b, a = b \/ sel a b \/ sel b a) ->
  forall I s0, ClosureIg step obs eqv (symI I) sel s0 <-> ClosureI step obs eqv I s0.
Proof.
  intros S E O step obs eqv eqv_refl eqv_sym eqS sel Hc I s0.
  rewrite (closureIg_exact step obs eqv eqv_refl eqv_sym eqS (symI I) sel Hc (symI_sym I) s0).
  symmetry. apply closureI_symmetrize. exact eqv_sym.
Qed.

(* On finite instances: ClosureI fails iff the pruned search finds a witness, so an exhausted
   pruned search is a certificate (closureI_witness_exact transferred). *)
Theorem closureIg_witness_exact : forall {S E O : Type} (step : E -> S -> S) (obs : S -> O)
  (eqv : O -> O -> Prop), (forall x, eqv x x) -> (forall x y, eqv x y -> eqv y x) ->
  forall (eqS : forall a b : S, {a = b} + {a <> b}) (allS : list S), (forall s, In s allS) ->
  forall (evs : list E), (forall e, In e evs) ->
  forall (I sel : E -> E -> Prop), (forall a b, I a b -> I b a) -> (forall a b, a = b \/ sel a b \/ sel b a) ->
  (forall a b, {I a b} + {~ I a b}) -> (forall x y, {eqv (obs x) (obs y)} + {~ eqv (obs x) (obs y)}) ->
  forall s0, ~ ClosureI step obs eqv I s0 <-> exists x y, PCIg step I sel s0 x y /\ ~ eqv (obs x) (obs y).
Proof.
  intros S E O step obs eqv eqv_refl eqv_sym eqS allS allS_full evs evs_full I sel Isym Hc I_dec eqv_dec s0.
  rewrite (closureI_witness_exact step obs eqv I eqS allS allS_full evs evs_full I_dec eqv_dec s0).
  symmetry. exact (closureIg_witness_iff step obs eqv eqv_refl eqv_sym eqS I sel Hc Isym s0).
Qed.

(* The barrier under declared independence with gsm's pruned search. *)
Theorem barrier_declared_pruned_exact : forall {SA EA SB EB : Type} (stepA : EA -> SA -> SA)
  (stepB : EB -> SB -> SB) (eqvB : SB -> SB -> Prop),
  (forall x, eqvB x x) -> (forall x y, eqvB x y -> eqvB y x) ->
  (forall x y z, eqvB x y -> eqvB y z -> eqvB x z) ->
  (forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y)) ->
  forall (M : SA -> SB) (tau : EA -> EB) (IX : EA + EB -> EA + EB -> Prop),
  (forall x y, IX x y -> IX y x) ->
  forall (eqSA : forall a b : SA, {a = b} + {a <> b}) (sel : EA -> EA -> Prop),
  (forall a b, a = b \/ sel a b \/ sel b a) ->
  forall s0, BarD stepA stepB eqvB M tau AdmF (tequiv IX) QT s0 <->
    (forall u v a b, IB IX a b ->
       eqvB (stepB b (stepB a (runT stepB v (M (runT stepA u s0))))) (stepB a (stepB b (runT stepB v (M (runT stepA u s0)))))) /\
    ClosureIg stepA M eqvB (IA IX) sel s0.
Proof.
  intros SA EA SB EB stepA stepB eqvB Hr Hs Ht Hx M tau IX IXs eqSA sel Hc s0.
  rewrite (barrier_declared_exact stepA stepB eqvB Hr Hs Ht Hx M tau IX IXs s0).
  rewrite (closureIg_exact stepA M eqvB Hr Hs eqSA (IA IX) sel Hc (fun a b H => IXs _ _ H) s0). tauto.
Qed.

(* ---- Instances of the pruning (A last-writer-wins on option bool, ReconfigurationClosure.v). ---- *)

(* Every pair of distinct events declared: a symmetric relation. *)
Definition I_ne (a b : bool) : Prop := a <> b.
Lemma I_ne_sym : forall a b, I_ne a b -> I_ne b a.
Proof. intros a b H E1. apply H. symmetry. exact E1. Qed.

Lemma lww_pci_some : forall (I : bool -> bool -> Prop) s0 x y, PCI lwwA I s0 x y -> exists a b, x = Some a /\ y = Some b.
Proof.
  intros I s0 x y H. destruct H as [u a b _ | e x y _].
  - exists b, a. split; reflexivity.
  - exists e, e. split; reflexivity.
Qed.

(* The pruned search with the orientation true before false: it certifies mergeM and finds the
   witness for partialM. *)
Theorem declared_pruned_instances :
  ClosureIg lwwA mergeM eq I_ne sel_tf None /\ ~ ClosureIg lwwA partialM eq I_ne sel_tf None.
Proof.
  split.
  - apply (closureIg_exact lwwA mergeM eq eq_refl' eq_sym' ob_eq_dec I_ne sel_tf sel_tf_cover I_ne_sym None).
    intros x y P. destruct (lww_pci_some I_ne None x y P) as [a [b [-> ->]]]. reflexivity.
  - intro H. apply (closureIg_exact lwwA partialM eq eq_refl' eq_sym' ob_eq_dec I_ne sel_tf sel_tf_cover I_ne_sym None) in H.
    assert (P : PCI lwwA I_ne None (Some false) (Some true)) by (apply (pci_seed lwwA I_ne None [] true false); discriminate).
    specialize (H _ _ P). discriminate H.
Qed.

(* Symmetry is needed. I_tf declares true before false only; the search takes the orientation
   false before true. The pruned closure is empty, so it reports no witness, while ClosureI has the
   pair (Some false, Some true), which partialM separates. Symmetrizing restores the witness. *)
Definition I_tf (a b : bool) : Prop := a = true /\ b = false.
Definition sel_ft (a b : bool) : Prop := a = false /\ b = true.

Lemma sel_ft_cover : forall a b, a = b \/ sel_ft a b \/ sel_ft b a.
Proof. intros [|] [|]; unfold sel_ft; tauto. Qed.

Theorem pruning_needs_symmetry :
  (forall a b, a = b \/ sel_ft a b \/ sel_ft b a) /\ ~ (forall a b, I_tf a b -> I_tf b a) /\
  ClosureIg lwwA partialM eq I_tf sel_ft None /\ ~ ClosureI lwwA partialM eq I_tf None /\
  ~ ClosureIg lwwA partialM eq (symI I_tf) sel_ft None.
Proof.
  assert (P : PCI lwwA I_tf None (Some false) (Some true)).
  { apply (pci_seed lwwA I_tf None [] true false). split; reflexivity. }
  assert (NI : ~ ClosureI lwwA partialM eq I_tf None) by (intro H; specialize (H _ _ P); discriminate H).
  split; [exact sel_ft_cover | split; [| split; [| split; [exact NI |]]]].
  - intro H. destruct (H true false (conj eq_refl eq_refl)) as [E1 _]. discriminate E1.
  - intros x y G. exfalso. induction G as [u a b [Ha Hb] [Ha' Hb'] _ | e x y _ IH _]; [congruence | exact IH].
  - intro H. apply NI. apply (closureIg_sym_exact lwwA partialM eq eq_refl' eq_sym' ob_eq_dec sel_ft sel_ft_cover I_tf None).
    exact H.
Qed.

(* The barrier through the pruned theorem: A = lwwA with every distinct A-pair declared, B ignores
   the translated events. mergeM: BarrierOnly (DS1 fails at None); partialM: Unsafe. *)
Definition IXa (x y : bool + unit) : Prop :=
  match x, y with
  | inl a, inl b => a <> b
  | _, _ => False
  end.
Lemma IXa_sym : forall x y, IXa x y -> IXa y x.
Proof. intros [a | []] [b | []]; simpl; try tauto. intros H E1. apply H. symmetry. exact E1. Qed.

Theorem declared_barrier_instances :
  ClassD lwwA idleB eq mergeM toUnit AdmF (tequiv IXa) QT None BarrierOnly /\
  ClassD lwwA idleB eq partialM toUnit AdmF (tequiv IXa) QT None Unsafe.
Proof.
  destruct declared_pruned_instances as [Cm Cp]. split.
  - split.
    + apply (barrier_declared_pruned_exact lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) mergeM toUnit IXa
               IXa_sym ob_eq_dec sel_tf sel_tf_cover None).
      split; [intros u v a b [] | exact Cm].
    + intro H. apply (live_declared_exact lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) mergeM toUnit IXa
                        IXa_sym None) in H.
      destruct H as [_ H]. specialize (H [] true). discriminate H.
  - simpl. intro H. apply (barrier_declared_pruned_exact lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) partialM
                             toUnit IXa IXa_sym ob_eq_dec sel_tf sel_tf_cover None) in H.
    exact (Cp (proj2 H)).
Qed.

(* ============================================================================================ *)
(* 2. At-least-once delivery with repeated submissions.                                         *)
(* ============================================================================================ *)

(* Every sequence of events is the label sequence of a duplicate-free sequence of messages: fresh
   submissions reach every state a sequence of events reaches without repeating a message. *)
Definition SubFresh {X E : Type} (ev : X -> E) : Prop := forall l : list E, exists p : list X, NoDup p /\ map ev p = l.

Lemma runT_label : forall {S X E : Type} (ev : X -> E) (step : E -> S -> S) (stepM : X -> S -> S),
  (forall m s, stepM m s = step (ev m) s) -> forall p s, runT stepM p s = runT step (map ev p) s.
Proof.
  intros S X E ev step stepM H p. induction p as [| m p IH]; intros s; [reflexivity |].
  simpl map. rewrite !runT_cons, H. apply IH.
Qed.

Lemma ml_nodup_app_r : forall {X : Type} (l r : list X), NoDup (l ++ r) -> NoDup r.
Proof.
  intros X l r. induction l as [| x l IH]; intros H; [exact H |].
  inversion H as [| ? ? _ H2]. exact (IH H2).
Qed.

Lemma ml_map_eq_app : forall {X Y : Type} (f : X -> Y) l l1 l2, map f l = l1 ++ l2 ->
  exists r1 r2, l = r1 ++ r2 /\ map f r1 = l1 /\ map f r2 = l2.
Proof.
  intros X Y f l. induction l as [| x l IH]; intros l1 l2 H.
  - symmetry in H. apply app_eq_nil in H. destruct H as [-> ->]. exists [], []. split; [| split]; reflexivity.
  - destruct l1 as [| y l1].
    + exists [], (x :: l). split; [| split]; [reflexivity | reflexivity | exact H].
    + simpl in H. injection H as Hy H. destruct (IH l1 l2 H) as [r1 [r2 [-> [E1 E2]]]].
      exists (x :: r1), r2. split; [reflexivity |]. split; [simpl; rewrite Hy, E1; reflexivity | exact E2].
Qed.

Lemma ml_map_eq_one : forall {X Y : Type} (f : X -> Y) l y, map f l = [y] -> exists m, l = [m] /\ f m = y.
Proof.
  intros X Y f [| m [| m' l]] y H; simpl in H; try discriminate H.
  injection H as H. exists m. split; [reflexivity | exact H].
Qed.

Section Labels.
  Context {S X E : Type}.
  Variable ev : X -> E.
  Variable step : E -> S -> S.
  Variable stepM : X -> S -> S.
  Hypothesis stepM_ev : forall m s, stepM m s = step (ev m) s.
  Variable eqv : S -> S -> Prop.
  Hypothesis fresh : SubFresh ev.

  Local Notation run := (runT step).
  Local Notation runM := (runT stepM).

  Lemma fresh_two : forall w a b, exists p m1 m2, NoDup (p ++ [m1; m2]) /\ map ev p = w /\ ev m1 = a /\ ev m2 = b.
  Proof.
    intros w a b. destruct (fresh (w ++ [a; b])) as [q [Hq Eq]].
    destruct (ml_map_eq_app ev q w [a; b] Eq) as [p [r [-> [Ep Er]]]].
    destruct (ml_map_eq_app ev r [a] [b] Er) as [r1 [r2 [-> [E1 E2]]]].
    destruct (ml_map_eq_one ev r1 a E1) as [m1 [-> H1]]. destruct (ml_map_eq_one ev r2 b E2) as [m2 [-> H2]].
    exists p, m1, m2. split; [exact Hq | split; [exact Ep | split; assumption]].
  Qed.

  Lemma fresh_one : forall w a, exists p m, NoDup (p ++ [m]) /\ map ev p = w /\ ev m = a.
  Proof.
    intros w a. destruct (fresh (w ++ [a])) as [q [Hq Eq]].
    destruct (ml_map_eq_app ev q w [a] Eq) as [p [r [-> [Ep Er]]]].
    destruct (ml_map_eq_one ev r a Er) as [m [-> H1]].
    exists p, m. split; [exact Hq | split; assumption].
  Qed.

  (* Commutation after duplicate-free prefixes of messages is commutation at every reachable state. *)
  Theorem commnd_fresh : forall y, CommND stepM eqv y <->
    forall w a b, eqv (step b (step a (run w y))) (step a (step b (run w y))).
  Proof.
    intros y. split.
    - intros H w a b. destruct (fresh_two w a b) as [p [m1 [m2 [Hnd [Ep [E1 E2]]]]]].
      assert (Ne : m1 <> m2).
      { intros <-. apply ml_nodup_app_r in Hnd. inversion Hnd as [| ? ? Hn _]. apply Hn. left. reflexivity. }
      specialize (H p m1 m2 Ne Hnd). rewrite !stepM_ev, (runT_label ev step stepM stepM_ev), Ep, E1, E2 in H. exact H.
    - intros H p a b _ _. rewrite !stepM_ev, (runT_label ev step stepM stepM_ev). apply H.
  Qed.

  (* Idempotence where a message is first delivered is idempotence at every reachable state. *)
  Theorem idemnd_fresh : forall y, (forall m, IdemND stepM eqv y m) <->
    forall w a, eqv (step a (step a (run w y))) (step a (run w y)).
  Proof.
    intros y. split.
    - intros H w a. destruct (fresh_one w a) as [p [m [Hnd [Ep E1]]]].
      specialize (H m p Hnd). rewrite !stepM_ev, (runT_label ev step stepM stepM_ev), Ep, E1 in H. exact H.
    - intros H m u _. rewrite !stepM_ev, (runT_label ev step stepM stepM_ev). apply H.
  Qed.
End Labels.

(* gsm's model: a message is an event with a submission number. *)
Fixpoint tg {T : Type} (i : nat) (l : list T) : list (T * nat) :=
  match l with
  | [] => []
  | x :: l => (x, i) :: tg (S i) l
  end.

Lemma tg_fst : forall {T : Type} (l : list T) i, map fst (tg i l) = l.
Proof. intros T l. induction l as [| x l IH]; intros i; [reflexivity |]. simpl. f_equal. apply IH. Qed.

Lemma tg_ids : forall {T : Type} (l : list T) i m, In m (tg i l) -> i <= snd m.
Proof.
  intros T l. induction l as [| x l IH]; intros i m H; [destruct H |].
  destruct H as [<- | H]; [simpl; lia |]. pose proof (IH (S i) m H). lia.
Qed.

Lemma tg_nodup : forall {T : Type} (l : list T) i, NoDup (tg i l).
Proof.
  intros T l. induction l as [| x l IH]; intros i; [constructor |]. simpl. constructor; [| apply IH].
  intros H. pose proof (tg_ids l (S i) (x, i) H) as K. simpl in K. lia.
Qed.

Theorem subfresh_tg : forall {T : Type}, SubFresh (@fst T nat).
Proof. intros T l. exists (tg 0 l). split; [apply tg_nodup | apply tg_fst]. Qed.

(* The combined alphabet of messages: A-submissions and B-submissions. *)
Definition toMsg {EA EB : Type} (p : (EA + EB) * nat) : (EA * nat) + (EB * nat) :=
  match p with
  | (inl a, k) => inl (a, k)
  | (inr b, k) => inr (b, k)
  end.
Definition evX {EA EB : Type} (x : (EA * nat) + (EB * nat)) : EA + EB :=
  match x with
  | inl m => inl (fst m)
  | inr m => inr (fst m)
  end.

Lemma evX_toMsg : forall {EA EB : Type} (p : (EA + EB) * nat), evX (toMsg p) = fst p.
Proof. intros EA EB [[a | b] k]; reflexivity. Qed.

Lemma toMsg_inj : forall {EA EB : Type} (p q : (EA + EB) * nat), toMsg p = toMsg q -> p = q.
Proof. intros EA EB [[a | b] k] [[a' | b'] k'] H; simpl in H; try discriminate H; injection H as -> ->; reflexivity. Qed.

Theorem subfresh_tagX : forall {EA EB : Type}, SubFresh (@evX EA EB).
Proof.
  intros EA EB w. exists (map toMsg (tg 0 w)). split.
  - apply (rd_nodup_map_inj toMsg toMsg_inj). apply tg_nodup.
  - rewrite map_map. rewrite (map_ext _ fst evX_toMsg). apply tg_fst.
Qed.

(* A message steps as its event; an in-flight A-message translates to a B-message. *)
Definition stepS {S E : Type} (step : E -> S -> S) (m : E * nat) (s : S) : S := step (fst m) s.
Definition tauS {EA EB : Type} (tau : EA -> EB) (m : EA * nat) : EB * nat := (tau (fst m), snd m).
(* gsm's comparison of two at-least-once runs (migration.go, witness): the same set of events. *)
Definition RelG {EA EB : Type} (w1 w2 : list ((EA * nat) + (EB * nat))) : Prop := SameSet (map evX w1) (map evX w2).
(* One submission per event, number 0: the one-message model inside the submission model. *)
Definition t0 {T : Type} (a : T) : T * nat := (a, 0).
Definition t0X {EA EB : Type} (x : EA + EB) : (EA * nat) + (EB * nat) := toMsg (x, 0).

Lemma runS : forall {S E : Type} (step : E -> S -> S) p s, runT (stepS step) p s = runT step (map fst p) s.
Proof. intros S E step. apply (runT_label fst step (stepS step)). reflexivity. Qed.

Lemma sameset_map : forall {X Y : Type} (f : X -> Y) l1 l2, SameSet l1 l2 -> SameSet (map f l1) (map f l2).
Proof.
  intros X Y f l1 l2 H y. rewrite !in_map_iff.
  split; intros [x [<- Hx]]; exists x; split; [reflexivity | apply H; exact Hx | reflexivity | apply H; exact Hx].
Qed.

Lemma map_fst_t0 : forall {T : Type} (l : list T), map fst (map t0 l) = l.
Proof. intros T l. rewrite map_map. apply map_id. Qed.
Lemma map_evX_t0X : forall {EA EB : Type} (l : list (EA + EB)), map evX (map t0X l) = l.
Proof. intros EA EB l. induction l as [| [a | b] l IH]; [reflexivity | |]; simpl; rewrite IH; reflexivity. Qed.
Lemma map_evX_inl : forall {EA EB : Type} (p : list (EA * nat)), map evX (map (@inl _ (EB * nat)) p) = map inl (map fst p).
Proof. intros EA EB p. rewrite !map_map. reflexivity. Qed.
Lemma map_t0X_inl : forall {EA EB : Type} (p : list EA), map t0X (map (@inl _ EB) p) = map inl (map t0 p).
Proof. intros EA EB p. rewrite !map_map. reflexivity. Qed.

Section Submissions.
  Context {SA EA SB EB : Type}.
  Variable decA : forall x y : EA, {x = y} + {x <> y}.
  Variable decB : forall x y : EB, {x = y} + {x <> y}.
  Variable stepA : EA -> SA -> SA.
  Variable stepB : EB -> SB -> SB.
  Variable eqvB : SB -> SB -> Prop.
  Hypothesis eqvB_refl : forall x, eqvB x x.
  Hypothesis eqvB_sym : forall x y, eqvB x y -> eqvB y x.
  Hypothesis eqvB_trans : forall x y z, eqvB x y -> eqvB y z -> eqvB x z.
  Hypothesis stepB_ext : forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y).
  Variable M : SA -> SB.
  Variable tau : EA -> EB.

  Local Notation runA := (runT stepA).
  Local Notation runB := (runT stepB).

  (* gsm's checks (migration.go): commutation and idempotence of the new events at every state the
     new configuration reaches from the migrated start (PermB-start, Idem-start) and from every
     migrated reachable state (PermB-every, Idem-every). *)
  Definition PermBStart (s0 : SA) : Prop :=
    forall v b b', eqvB (stepB b' (stepB b (runB v (M s0)))) (stepB b (stepB b' (runB v (M s0)))).
  Definition IdemStart (s0 : SA) : Prop :=
    forall v b, eqvB (stepB b (stepB b (runB v (M s0)))) (stepB b (runB v (M s0))).
  Definition PermBEvery (s0 : SA) : Prop :=
    forall u v b b', eqvB (stepB b' (stepB b (runB v (M (runA u s0))))) (stepB b (stepB b' (runB v (M (runA u s0))))).
  Definition IdemEvery (s0 : SA) : Prop :=
    forall u v b, eqvB (stepB b (stepB b (runB v (M (runA u s0))))) (stepB b (runB v (M (runA u s0)))).

  Lemma stepXS : forall x y, stepX (stepS stepB) (tauS tau) x y = stepX stepB tau (evX x) y.
  Proof. intros [[a k] | [b k]] y; reflexivity. Qed.

  Lemma outDS : forall s0 p q, outD (stepS stepA) (stepS stepB) M (tauS tau) s0 p q = outD stepA stepB M tau s0 (map fst p) (map evX q).
  Proof.
    intros s0 p q. unfold outD. rewrite runS. apply (runT_label evX (stepX stepB tau)). exact stepXS.
  Qed.

  Let extS : forall e x y, eqvB x y -> eqvB (stepS stepB e x) (stepS stepB e y) := fun e => stepB_ext (fst e).

  Lemma ds1_sub : forall s0, DS1 (stepS stepA) (stepS stepB) eqvB M (tauS tau) s0 <-> DS1 stepA stepB eqvB M tau s0.
  Proof.
    intros s0. unfold DS1. split.
    - intros H u e. specialize (H (tg 0 u) (e, 0)). rewrite runS, tg_fst in H. exact H.
    - intros H u e. rewrite runS. apply H.
  Qed.

  Lemma comm_start_iff : forall s0,
    (forall w x y, eqvB (stepX stepB tau y (stepX stepB tau x (runT (stepX stepB tau) w (M s0))))
                        (stepX stepB tau x (stepX stepB tau y (runT (stepX stepB tau) w (M s0))))) <-> PermBStart s0.
  Proof.
    intros s0. split.
    - intros H v b b'. specialize (H (map inr v) (inr b) (inr b')). rewrite runX_inr in H. exact H.
    - intros H w x y. rewrite runX_map. apply H.
  Qed.

  Lemma idem_start_iff : forall s0,
    (forall w x, eqvB (stepX stepB tau x (stepX stepB tau x (runT (stepX stepB tau) w (M s0))))
                      (stepX stepB tau x (runT (stepX stepB tau) w (M s0)))) <-> IdemStart s0.
  Proof.
    intros s0. split.
    - intros H v b. specialize (H (map inr v) (inr b)). rewrite runX_inr in H. exact H.
    - intros H w x. rewrite runX_map. apply H.
  Qed.

  (* The live switch in the submission model is exactly gsm's online checks. *)
  Theorem submissions_live_exact : forall s0,
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet s0 <->
    (PermBStart s0 /\ IdemStart s0) /\ DS1 stepA stepB eqvB M tau s0.
  Proof.
    intros s0.
    rewrite (live_free_alo_exact (prod_eq_dec decA Nat.eq_dec) (prod_eq_dec decB Nat.eq_dec) (stepS stepA) (stepS stepB)
               eqvB eqvB_refl eqvB_sym eqvB_trans extS M (tauS tau) s0).
    rewrite (commnd_fresh evX (stepX stepB tau) _ stepXS eqvB subfresh_tagX (M s0)).
    rewrite (idemnd_fresh evX (stepX stepB tau) _ stepXS eqvB subfresh_tagX (M s0)).
    rewrite comm_start_iff, idem_start_iff, ds1_sub. tauto.
  Qed.

  Lemma absorb_sub : forall s0,
    AbsorbFree (stepS stepA) (stepS stepB) eqvB M (tauS tau) s0 <-> AbsorbFree stepA stepB eqvB M tau s0.
  Proof.
    intros s0. unfold AbsorbFree. split.
    - intros H p v a Ha. rewrite <- (tg_fst p 0) in Ha. apply in_map_iff in Ha. destruct Ha as [m [<- Hm]].
      specialize (H (tg 0 p) (tg 0 v) m Hm). rewrite !runS, !tg_fst in H. exact H.
    - intros H p v m Hm. rewrite !runS. apply H. apply in_map. exact Hm.
  Qed.

  Lemma amod_sub : forall s0, AmodFree (stepS stepA) eqvB M s0 <-> AmodFree stepA eqvB M s0.
  Proof.
    intros s0. unfold AmodFree. split.
    - intros H p1 p2 HS. specialize (H (map t0 p1) (map t0 p2) (sameset_map t0 p1 p2 HS)).
      rewrite !runS, !map_fst_t0 in H. exact H.
    - intros H p1 p2 HS. rewrite !runS. apply H. apply sameset_map. exact HS.
  Qed.

  (* The barrier switch in the submission model is exactly gsm's barrier checks. *)
  Theorem submissions_barrier_exact : forall s0,
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet QA s0 <->
    (PermBEvery s0 /\ IdemEvery s0) /\ AbsorbFree stepA stepB eqvB M tau s0 /\ AmodFree stepA eqvB M s0.
  Proof.
    intros s0.
    rewrite (barrier_free_alo_exact (prod_eq_dec decB Nat.eq_dec) (stepS stepA) (stepS stepB) eqvB eqvB_refl eqvB_sym
               eqvB_trans extS M (tauS tau) s0).
    rewrite absorb_sub, amod_sub.
    assert (K : (forall p, CommND (stepS stepB) eqvB (M (runT (stepS stepA) p s0)) /\
                   forall b, IdemND (stepS stepB) eqvB (M (runT (stepS stepA) p s0)) b) <->
                PermBEvery s0 /\ IdemEvery s0).
    { split.
      - intros H. split.
        + intros u v b b'. destruct (H (tg 0 u)) as [Hc _].
          rewrite (commnd_fresh fst stepB (stepS stepB) (fun m s => eq_refl) eqvB subfresh_tg) in Hc.
          rewrite runS, tg_fst in Hc. apply Hc.
        + intros u v b. destruct (H (tg 0 u)) as [_ Hi].
          rewrite (idemnd_fresh fst stepB (stepS stepB) (fun m s => eq_refl) eqvB subfresh_tg) in Hi.
          rewrite runS, tg_fst in Hi. apply Hi.
      - intros [Hc Hi] p. rewrite runS. split.
        + apply (commnd_fresh fst stepB (stepS stepB) (fun m s => eq_refl) eqvB subfresh_tg). intros w a b. apply Hc.
        + apply (idemnd_fresh fst stepB (stepS stepB) (fun m s => eq_refl) eqvB subfresh_tg). intros w a. apply Hi. }
    rewrite K. tauto.
  Qed.

  (* The comparison: any relation on runs of messages that implies the same set of events and holds
     between the one-submission images of runs with the same set of events gives the outcomes of
     the one-message model. Both the same submissions (SameSet) and gsm's RelG are such relations. *)
  Section Compare.
    Variable R : list ((EA * nat) + (EB * nat)) -> list ((EA * nat) + (EB * nat)) -> Prop.
    Hypothesis R_proj : forall w1 w2, R w1 w2 -> SameSet (map evX w1) (map evX w2).
    Hypothesis R_lift : forall e1 e2, SameSet e1 e2 -> R (map t0X e1) (map t0X e2).

    Lemma compare_live : forall s0,
      LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF R s0 <-> LiveD stepA stepB eqvB M tau AdmF SameSet s0.
    Proof.
      intros s0. split.
      - intros H p1 q1 p2 q2 _ _ HS.
        specialize (H (map t0 p1) (map t0X q1) (map t0 p2) (map t0X q2) I I).
        rewrite !outDS, !map_fst_t0, !map_evX_t0X in H. apply H.
        rewrite <- !map_t0X_inl, <- !map_app. apply R_lift. exact HS.
      - intros H p1 q1 p2 q2 _ _ HR. rewrite !outDS. apply H; [exact I | exact I |].
        apply R_proj in HR. rewrite !map_app, !map_evX_inl in HR. exact HR.
    Qed.

    Lemma qa_proj : forall (p : list (EA * nat)) (q : list ((EA * nat) + (EB * nat))), QA p q -> QA (map fst p) (map evX q).
    Proof.
      intros p q H x Hx. apply in_map_iff in Hx. destruct Hx as [y [<- Hy]].
      destruct (H y Hy) as [[b ->] | [a [-> Ha]]].
      - left. exists (fst b). reflexivity.
      - right. exists (fst a). split; [reflexivity | apply in_map; exact Ha].
    Qed.

    Lemma qa_lift : forall (p : list EA) (q : list (EA + EB)), QA p q -> QA (map t0 p) (map t0X q).
    Proof.
      intros p q H x Hx. apply in_map_iff in Hx. destruct Hx as [y [<- Hy]].
      destruct (H y Hy) as [[b ->] | [a [-> Ha]]].
      - left. exists (b, 0). reflexivity.
      - right. exists (a, 0). split; [reflexivity | apply (in_map t0); exact Ha].
    Qed.

    Lemma compare_barrier : forall s0,
      BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF R QA s0 <-> BarD stepA stepB eqvB M tau AdmF SameSet QA s0.
    Proof.
      intros s0. split.
      - intros H p1 q1 p2 q2 Q1 Q2 _ _ HS.
        specialize (H (map t0 p1) (map t0X q1) (map t0 p2) (map t0X q2) (qa_lift p1 q1 Q1) (qa_lift p2 q2 Q2) I I).
        rewrite !outDS, !map_fst_t0, !map_evX_t0X in H. apply H.
        rewrite <- !map_t0X_inl, <- !map_app. apply R_lift. exact HS.
      - intros H p1 q1 p2 q2 Q1 Q2 _ _ HR. rewrite !outDS.
        apply H; [apply qa_proj; exact Q1 | apply qa_proj; exact Q2 | exact I | exact I |].
        apply R_proj in HR. rewrite !map_app, !map_evX_inl in HR. exact HR.
    Qed.
  End Compare.

  Lemma sameset_proj : forall w1 w2 : list ((EA * nat) + (EB * nat)), SameSet w1 w2 -> SameSet (map evX w1) (map evX w2).
  Proof. intros w1 w2. apply sameset_map. Qed.
  Lemma sameset_lift : forall e1 e2 : list (EA + EB), SameSet e1 e2 -> SameSet (map t0X e1) (map t0X e2).
  Proof. intros e1 e2. apply sameset_map. Qed.
  Lemma relg_proj : forall w1 w2 : list ((EA * nat) + (EB * nat)), RelG w1 w2 -> SameSet (map evX w1) (map evX w2).
  Proof. intros w1 w2 H. exact H. Qed.
  Lemma relg_lift : forall e1 e2 : list (EA + EB), SameSet e1 e2 -> RelG (map t0X e1) (map t0X e2).
  Proof. intros e1 e2 H. unfold RelG. rewrite !map_evX_t0X. exact H. Qed.

  (* The submission model and the one-message model (each event one message, redelivered) have the
     same outcomes. *)
  Theorem submissions_one_message_live : forall s0,
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet s0 <-> LiveD stepA stepB eqvB M tau AdmF SameSet s0.
  Proof. exact (compare_live SameSet sameset_proj sameset_lift). Qed.

  Theorem submissions_one_message_barrier : forall s0,
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet QA s0 <-> BarD stepA stepB eqvB M tau AdmF SameSet QA s0.
  Proof. exact (compare_barrier SameSet sameset_proj sameset_lift). Qed.

  (* gsm's comparison (the same set of events) gives the same outcomes as the same submissions. *)
  Theorem gsm_relg_live : forall s0,
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG s0 <->
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet s0.
  Proof. intros s0. rewrite (compare_live RelG relg_proj relg_lift). symmetry. apply submissions_one_message_live. Qed.

  Theorem gsm_relg_barrier : forall s0,
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG QA s0 <->
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF SameSet QA s0.
  Proof. intros s0. rewrite (compare_barrier RelG relg_proj relg_lift). symmetry. apply submissions_one_message_barrier. Qed.

  (* gsm's at-least-once checks, exact in gsm's model with gsm's comparison. *)
  Theorem gsm_alo_live_exact : forall s0,
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG s0 <->
    (PermBStart s0 /\ IdemStart s0) /\ DS1 stepA stepB eqvB M tau s0.
  Proof. intros s0. rewrite gsm_relg_live. apply submissions_live_exact. Qed.

  Theorem gsm_alo_barrier_exact : forall s0,
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG QA s0 <->
    (PermBEvery s0 /\ IdemEvery s0) /\ AbsorbFree stepA stepB eqvB M tau s0 /\ AmodFree stepA eqvB M s0.
  Proof. intros s0. rewrite gsm_relg_barrier. apply submissions_barrier_exact. Qed.

  Theorem gsm_alo_live_implies_barrier : forall s0,
    LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG s0 ->
    BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG QA s0.
  Proof. intros s0. apply live_implies_barrier_d. Qed.
End Submissions.

(* ---- Finite instances: gsm's model decided, with no unknown outcome. ---- *)

Definition okT {X : Type} (_ : list X) (_ : X) : Prop := True.
Definition okT_dec {X : Type} (D : list X) (x : X) : {okT D x} + {~ okT D x} := left I.
Lemma okT_ext : forall {X : Type} (D D' : list X) x, (forall z, In z D <-> In z D') -> okT D x -> okT D' x.
Proof. intros X D D' x _ H. exact H. Qed.

Section SubFinite.
  Context {SA EA SB EB : Type}.
  Variable stepA : EA -> SA -> SA.
  Variable stepB : EB -> SB -> SB.
  Variable eqvB : SB -> SB -> Prop.
  Hypothesis eqvB_refl : forall x, eqvB x x.
  Hypothesis eqvB_sym : forall x y, eqvB x y -> eqvB y x.
  Hypothesis eqvB_trans : forall x y z, eqvB x y -> eqvB y z -> eqvB x z.
  Hypothesis stepB_ext : forall e x y, eqvB x y -> eqvB (stepB e x) (stepB e y).
  Variable M : SA -> SB.
  Variable tau : EA -> EB.
  Variable decA : forall x y : EA, {x = y} + {x <> y}.
  Variable decB : forall x y : EB, {x = y} + {x <> y}.
  Variable eqSA : forall a b : SA, {a = b} + {a <> b}.
  Variable eqSB : forall a b : SB, {a = b} + {a <> b}.
  Variable allA : list SA.
  Hypothesis allA_full : forall s, In s allA.
  Variable allB : list SB.
  Hypothesis allB_full : forall x, In x allB.
  Variable evsA : list EA.
  Hypothesis evsA_full : forall e, In e evsA.
  Variable evsB : list EB.
  Hypothesis evsB_full : forall e, In e evsB.
  Hypothesis eqvB_dec : forall x y, {eqvB x y} + {~ eqvB x y}.

  (* The outcome in gsm's model (submissions, gsm's comparison), decided on finite instances. *)
  Theorem classify_submissions_complete : forall s0,
    {o : outcome | ClassD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG QA s0 o}.
  Proof.
    intros s0.
    destruct (classify_alo_complete stepA stepB eqvB eqvB_refl eqvB_sym eqvB_trans stepB_ext M tau (@nohb (EA + EB))
                (@nohb_irrefl' (EA + EB)) (@nohb_BA EA EB) decA decB eqSA eqSB allA allA_full allB allB_full
                evsA evsA_full evsB evsB_full eqvB_dec (@nohb_dec (EA + EB)) s0) as [o H].
    exists o.
    assert (L : LiveD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG s0 <->
                LiveD stepA stepB eqvB M tau (causal_alo nohb) SameSet s0).
    { rewrite gsm_relg_live, submissions_one_message_live. apply liveD_adm_ext. apply admF_alo. }
    assert (Bq : BarD (stepS stepA) (stepS stepB) eqvB M (tauS tau) AdmF RelG QA s0 <->
                 BarD stepA stepB eqvB M tau (causal_alo nohb) SameSet QA s0).
    { rewrite gsm_relg_barrier, submissions_one_message_barrier. apply barD_adm_ext. apply admF_alo. }
    destruct o; simpl in *; rewrite ?L, ?Bq; exact H.
  Qed.

  (* gsm's AmodA search: the nodes are pairs (state, set of events applied) reached from
     (s0, none), one event at a time. AmodFree holds iff every two nodes with the same set migrate to
     equivalent states, so an exhausted search with none apart certifies it and two nodes apart
     refute it. *)
  Theorem amodfree_search_exact : forall s0, AmodFree stepA eqvB M s0 <->
    forall t1 t2 D,
      star (Rsucc (msucc decA evsA stepA okT okT_dec)) (s0, canon decA evsA []) (t1, D) ->
      star (Rsucc (msucc decA evsA stepA okT okT_dec)) (s0, canon decA evsA []) (t2, D) -> eqvB (M t1) (M t2).
  Proof.
    intros s0. split.
    - intros H t1 t2 D R1 R2.
      apply (mreach_iff decA evsA evsA_full stepA okT okT_dec okT_ext []) in R1. destruct R1 as [w1 [_ [-> E1]]].
      apply (mreach_iff decA evsA evsA_full stepA okT okT_dec okT_ext []) in R2. destruct R2 as [w2 [_ [-> E2]]].
      apply H. intros z.
      pose proof (canon_in decA evsA evsA_full ([] ++ w1) z) as C1.
      pose proof (canon_in decA evsA evsA_full ([] ++ w2) z) as C2.
      rewrite <- E1 in C1. rewrite <- E2 in C2. simpl in C1, C2. rewrite <- C1, <- C2. reflexivity.
    - intros H p1 p2 HS. apply (H _ _ (canon decA evsA ([] ++ p1))).
      + apply (mreach_iff decA evsA evsA_full stepA okT okT_dec okT_ext []).
        exists p1. split; [intros l x r _; exact I | split; reflexivity].
      + apply (mreach_iff decA evsA evsA_full stepA okT okT_dec okT_ext []).
        exists p2. split; [intros l x r _; exact I | split; [reflexivity |]].
        apply canon_ext. intros z. simpl. apply HS.
  Qed.
End SubFinite.

(* ---- Instances in gsm's model. ---- *)

(* Non-vacuity: max-registers, M and tau doubling. Every check holds: Online from every start. *)
Theorem sub_rescaled_online : forall s0,
  ClassD (stepS rmA) (stepS rmB) eq rmM (tauS rmTau) AdmF RelG QA s0 Online /\
  (PermBEvery rmA rmB eq rmM s0 /\ IdemEvery rmA rmB eq rmM s0) /\
  AbsorbFree rmA rmB eq rmM rmTau s0 /\ AmodFree rmA eq rmM s0.
Proof.
  intros s0. destruct (rescaled_max s0) as [_ [_ [Hab [Ham _]]]]. split; [| split; [split | split; assumption]].
  - simpl. apply (gsm_alo_live_exact Nat.eq_dec Nat.eq_dec rmA rmB eq eq_refl' eq_sym' eq_trans' (eq_ext' rmB) rmM rmTau s0).
    split; [split | apply rm_ds1].
    + intros v b b'. unfold rmB. apply max_swap.
    + intros v b. unfold rmB. apply max_idem.
  - intros u v b b'. unfold rmB. apply max_swap.
  - intros u v b. unfold rmB. apply max_idem.
Qed.

(* A counter, B's image saturating at 1: the new events commute and are idempotent everywhere, but
   DS1 fails at the state a second submission reaches, so the live switch diverges. *)
Theorem sub_count_dup :
  (PermBStart cdB eq idN 0 /\ IdemStart cdB eq idN 0) /\ ~ DS1 cdA cdB eq idN idU 0 /\
  ~ LiveD (stepS cdA) (stepS cdB) eq idN (tauS idU) AdmF RelG 0.
Proof.
  assert (Ds : ~ DS1 cdA cdB eq idN idU 0) by (intro H; specialize (H [tt] tt); discriminate H).
  split; [split | split; [exact Ds |]].
  - intros v b b'. reflexivity.
  - intros v b. unfold cdB. rewrite <- Nat.max_assoc, Nat.max_id. reflexivity.
  - intro H. apply (gsm_alo_live_exact unit_dec' unit_dec' cdA cdB eq eq_refl' eq_sym' eq_trans' (eq_ext' cdB)
                      idN idU 0) in H. exact (Ds (proj2 H)).
Qed.

(* The straddling duplicate: Unsafe by AbsorbS alone, every other barrier check holding. *)
Theorem sub_reset_straddle :
  ClassD (stepS rsA) (stepS rsB) eq rsM (tauS idU) AdmF RelG QA false Unsafe /\
  (PermBEvery rsA rsB eq rsM false /\ IdemEvery rsA rsB eq rsM false) /\ AmodFree rsA eq rsM false /\
  ~ AbsorbFree rsA rsB eq rsM idU false.
Proof.
  assert (NA : ~ AbsorbFree rsA rsB eq rsM idU false).
  { intro H. specialize (H [tt] [] tt (or_introl eq_refl)). discriminate H. }
  split; [| split; [split | split; [| exact NA]]].
  - simpl. intro H. apply (gsm_alo_barrier_exact unit_dec' rsA rsB eq eq_refl' eq_sym' eq_trans' (eq_ext' rsB) rsM idU
                             false) in H. exact (NA (proj1 (proj2 H))).
  - intros u v b b'. reflexivity.
  - intros u v b. reflexivity.
  - intros p1 p2 _. reflexivity.
Qed.

(* The lww instances of ReconfigurationClosure.v, in gsm's model. *)
Lemma merge_run_cons : forall e p s, mergeM (runT lwwA (e :: p) s) = true.
Proof.
  intros e p. revert e. induction p as [| e' p IH]; intros e s; [reflexivity |].
  rewrite runT_cons. apply IH.
Qed.

Lemma lww_amod_merge : AmodFree lwwA eq mergeM None.
Proof.
  intros [| e1 p1] [| e2 p2] HS; try reflexivity.
  - destruct (proj2 (HS e2) (or_introl eq_refl)).
  - destruct (proj1 (HS e1) (or_introl eq_refl)).
  - rewrite !merge_run_cons. reflexivity.
Qed.

Theorem sub_merged_online : ClassD (stepS lwwA) (stepS flagB) eq mergeM (tauS toUnit) AdmF RelG QA None Online.
Proof.
  simpl. apply (gsm_alo_live_exact bool_dec unit_dec' lwwA flagB eq eq_refl' eq_sym' eq_trans' (eq_ext' flagB) mergeM toUnit None).
  split; [split; [intros v b b'; reflexivity | intros v b; reflexivity] | intros u e; reflexivity].
Qed.

Theorem sub_merged_barrier : ClassD (stepS lwwA) (stepS idleB) eq mergeM (tauS toUnit) AdmF RelG QA None BarrierOnly.
Proof.
  split.
  - apply (gsm_alo_barrier_exact unit_dec' lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) mergeM toUnit None).
    split; [split; [intros u v b b'; reflexivity | intros u v b; reflexivity] |].
    split; [intros p v a _; reflexivity | exact lww_amod_merge].
  - intro H. apply (gsm_alo_live_exact bool_dec unit_dec' lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) mergeM
                      toUnit None) in H.
    destruct H as [_ H]. specialize (H [] true). discriminate H.
Qed.

Theorem sub_partial_unsafe : ClassD (stepS lwwA) (stepS idleB) eq partialM (tauS toUnit) AdmF RelG QA None Unsafe /\
  ~ AmodFree lwwA eq partialM None.
Proof.
  assert (NA : ~ AmodFree lwwA eq partialM None).
  { intro H. assert (HS : SameSet [true; false] [false; true]) by (intros x; simpl; tauto).
    specialize (H _ _ HS). vm_compute in H. discriminate H. }
  split; [| exact NA]. simpl. intro H.
  apply (gsm_alo_barrier_exact unit_dec' lwwA idleB eq eq_refl' eq_sym' eq_trans' (eq_ext' idleB) partialM toUnit None) in H.
  exact (NA (proj2 (proj2 H))).
Qed.

(* classify_submissions_complete runs on the finite instances (its hypotheses all hold). *)
Definition sub_lww_classified (M : option bool -> bool) (stepB : unit -> bool -> bool) :
  {o : outcome | ClassD (stepS lwwA) (stepS stepB) eq M (tauS toUnit) AdmF RelG QA None o} :=
  classify_submissions_complete lwwA stepB eq eq_refl' eq_sym' eq_trans' (eq_ext' stepB) M toUnit bool_dec unit_dec'
    ob_eq_dec bool_dec [None; Some true; Some false] ob_full [true; false] b_full [true; false] b_full [tt] u_full
    bool_dec None.

Definition sub_reset_classified : {o : outcome | ClassD (stepS rsA) (stepS rsB) eq rsM (tauS idU) AdmF RelG QA false o} :=
  classify_submissions_complete rsA rsB eq eq_refl' eq_sym' eq_trans' (eq_ext' rsB) rsM idU unit_dec' unit_dec'
    bool_dec bool_dec [true; false] bool_full' [true; false] bool_full' [tt] unit_full' [tt] unit_full' bool_dec false.

Theorem submission_instances_classified :
  proj1_sig (sub_lww_classified mergeM flagB) = Online /\
  proj1_sig (sub_lww_classified mergeM idleB) = BarrierOnly /\
  proj1_sig (sub_lww_classified partialM idleB) = Unsafe /\
  proj1_sig sub_reset_classified = Unsafe.
Proof.
  split; [| split; [| split]].
  - destruct (sub_lww_classified mergeM flagB) as [o H]. exact (classD_unique _ _ _ _ _ _ _ _ _ _ _ H sub_merged_online).
  - destruct (sub_lww_classified mergeM idleB) as [o H]. exact (classD_unique _ _ _ _ _ _ _ _ _ _ _ H sub_merged_barrier).
  - destruct (sub_lww_classified partialM idleB) as [o H].
    exact (classD_unique _ _ _ _ _ _ _ _ _ _ _ H (proj1 sub_partial_unsafe)).
  - destruct sub_reset_classified as [o H]. exact (classD_unique _ _ _ _ _ _ _ _ _ _ _ H (proj1 sub_reset_straddle)).
Qed.
