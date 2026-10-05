(* CoordinatedExact.v: the EXACT event-order condition under the holonomy-minimal coordination
   plan of CoordinatedCycles.v. Axiom-free.

   The gap. CoordinatedCycles.coordinated_events_converge proves that permutations of local
   events converge under the plan when the authority root's own events commute (at every value).
   That is a sufficient condition only. The plan's driving network (dsrc, dfun) is an acyclic
   federation satisfying FederationEvents.Common (drive_common), so the exact converse of
   FederationEventsConverse.v (fed_exact, fed_exact_full, acyclic_gc_iff) applies to it. This
   file instantiates it and computes what its two conditions say on the driving network.

   Setting (fixed throughout): a group (G, op, e, inv), an authority root r, a spanning tree T
   grown from r, a topological order o of the driving network over exactly the tree's vertices,
   and local events (E, reg, sig) on tree registries, with any declared same-registry
   independence J. Runs are FederationEvents.runF (FedMachine.Apply sequences) on the driving
   network with the identity normalizer and no validity constraint; a start s0 is any
   morphism-consistent state (Cons) of that network.

   1. Direct instantiation (any start s0 consistent with the driving network):
        coordinated_gc_iff        GCF s0 <-> TraceConv s0
        coordinated_fed_exact     TraceConv s0 <-> C1R1 s0 /\ C2R s0
        coordinated_fed_exact_full TraceConv s0 <-> C1R s0 /\ C2R s0
      where TraceConv s0 says every two J-trace-equivalent event sequences reach the same state.

   2. What C1 and C2 reduce to on the driving network.
      - coordinated_network_shape: every non-root tree vertex w is driven by a single group
        translation x |-> g * s(p) or g^-1 * s(p) of its tree parent p (it ignores its own value),
        the root keeps its own value (dfun r s x = x), and off-tree registries are untouched.
        Balanced non-tree edges B never enter dfun (they are constraints only, checked on the
        result: coordinated_runs_kept), and coordinated edges C are absent altogether.
      - coordinated_c1_static, coordinated_c1r1: C1 holds unconditionally, statically and hence
        at every reachable witness. A driven target's repair overwrites the whole value with the
        translated parent value, so both sides of C1 are that value; the root's repair is the
        identity, so both sides are sig e b.
      - coordinated_c2at_iff: C2 at a reachable witness s is trivial on driven registries, and on
        the root it is exactly sig e2 (sig e1 (s r)) = sig e1 (sig e2 (s r)).
      - coordinated_root_run, coordinated_root_reach: the root value of a run is the root value
        of the start pushed through the run's root events only (rrun of the filtered list);
        events on other registries never reach the root.

   3. The exact condition (coordinated_events_exact): for every consistent start s0,
        TraceConv s0  <->  RootCC (s0 r)
      where RootCC x0 says: every two J-independent root events commute at every root value
      reachable from x0 by root events (RootReach). With every pair declared (J total) this is
      the Permutation form (coordinated_perm_exact), and with the plan's balanced constraints the
      reached states also satisfy T ++ B (coordinated_events_exact_plan).

   4. The old sufficient condition, placed exactly.
      - coordinated_events_exact_global: "converges from EVERY consistent start" iff every two
        J-independent root events commute at EVERY value. So the old hypothesis of
        coordinated_events_converge is exactly the uniform (all starts) condition, and that theorem
        is recovered as coordinated_events_converge_recovered.
      - old_condition_not_necessary: for a fixed start it is not necessary. Over the Klein group
        V4 = (bool * bool, componentwise xor), on the two-registry tree A -> B rooted at A, the
        root events Swap (a, b) |-> (b, a) and Clear (a, b) |-> (a, false) do not commute at
        (true, false), yet from the consistent start with root (false, false) every permutation of
        events (including a B event) converges, because both root events fix (false, false). From
        the consistent start with root (true, false) the two orders of Swap and Clear diverge, so
        the exact condition depends on the start, as the iff says.

   5. Non-vacuity, on CoordinatedCycles.v's two Z/2 loops with events.
      - copyback_events_exact (copy-back loop, balanced back edge kept as a constraint, zero
        coordination): root event Flip (negation) and a B event Write; from every consistent start
        every permutation converges and every reached state satisfies cc_T ++ cb_B ++ cb_C.
      - negation_events_exact (negation loop, back edge coordinated): root events Set0 and Set1
        and a B event; from every consistent start the two orders of Set0 and Set1 diverge (so
        permutations do not converge, and RootCC fails), every reached state satisfies the kept
        network cc_T ++ neg_B, and none satisfies cc_T ++ neg_B ++ neg_C.
      The driving network of the two loops is the same (it depends only on T and r), so event
      convergence depends only on the root's events; B and C only change which constraints the
      reached states satisfy.

   States are compared pointwise, so no functional extensionality is used. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.CohomologyGraph NC.FederationOrder NC.FederationEvents
  NC.FederationEventsConverse NC.CoordinatedCycles.
Import ListNotations.

Section Exact.
  Context {G : Type}.
  Variables (op : G -> G -> G) (e : G) (inv : G -> G).
  Hypothesis assoc : forall a b c, op a (op b c) = op (op a b) c.
  Hypothesis id_l  : forall a, op e a = a.
  Hypothesis inv_r : forall a, op a (inv a) = e.
  Hypothesis inv_l : forall a, op (inv a) a = e.

  Variables (r : nat) (T : list (@edge G)) (o : list nat).
  Hypothesis HT : tree r T.
  Hypothesis Ho : FederationOrder.topo (dsrc r T) o.
  Hypothesis Hset : forall w, In w o <-> In w (r :: verts T).

  Variables (E : Type) (reg : E -> nat) (sig : E -> G -> G).
  Hypothesis Hreg : forall ev, In (reg ev) o.

  Local Notation F := (dfun op inv r T).
  Local Notation idN := (fun (_ : nat) (x : G) => x).
  Local Notation rF := (FederationEvents.runF G F idN E reg sig o).
  Local Notation aF := (FederationEvents.applyF G F idN E reg sig o).
  Local Notation ConsD := (FederationEvents.Cons G F o).

  (* ----- the root's own events ----- *)

  (* Root events applied to a root value, in order. *)
  Definition rrun (p : list E) (x : G) : G := fold_left (fun y ev => sig ev y) p x.

  (* x is reachable from x0 by root events. *)
  Definition RootReach (x0 x : G) : Prop :=
    exists p, Forall (fun ev => reg ev = r) p /\ x = rrun p x0.

  (* The exact condition: J-independent root events commute at every reachable root value. *)
  Definition RootCC (J : E -> E -> Prop) (x0 : G) : Prop :=
    forall x, RootReach x0 x -> forall e1 e2, reg e1 = r -> reg e2 = r -> J e1 e2 ->
      sig e2 (sig e1 x) = sig e1 (sig e2 x).

  Lemma HC : FederationEvents.Common G (dsrc r T) F (fun _ _ => True) idN E reg sig o.
  Proof. exact (drive_common op inv r T o E reg sig Ho Hreg). Qed.

  Lemma Inv_all : forall s, FederationEvents.Inv G (fun _ _ => True) s.
  Proof. intros s k. exact I. Qed.

  Lemma dfun_root : forall s x, F r s x = x.
  Proof. intros s x. unfold dfun. rewrite (root_none r T HT). reflexivity. Qed.

  Lemma root_in_o : In r o.
  Proof. apply Hset. left. reflexivity. Qed.

  (* Every event is on the root or on a driven registry. *)
  Lemma reg_cases : forall ev, reg ev = r \/ exists p g b, rule r T (reg ev) = Some (p, g, b).
  Proof.
    intro ev. destruct (Nat.eq_dec (reg ev) r) as [R | R]; [left; exact R | right].
    exact (driven r T HT (reg ev) (proj1 (Hset _) (Hreg ev)) R).
  Qed.

  (* ----- the shape of the driving network ----- *)

  Theorem coordinated_network_shape :
    (forall w, In w (r :: verts T) -> w <> r ->
       exists p g b, In p (r :: verts T) /\ forall s x, F w s x = tr op inv g b (s p)) /\
    (forall s x, F r s x = x) /\
    (forall w s x, ~ In w (r :: verts T) -> F w s x = x).
  Proof.
    split; [| split; [exact dfun_root |]].
    - intros w Hw Hr. destruct (driven r T HT w Hw Hr) as [p [g [b Hs]]].
      exists p, g, b. split; [exact (proj1 (rule_some r T HT w p g b Hs)) |].
      intros s x. unfold dfun. rewrite Hs. reflexivity.
    - intros w s x Hw. unfold dfun. destruct (rule r T w) as [[[p g] b] |] eqn:Hs; [| reflexivity].
      exfalso. apply Hw. destruct (rule_some r T HT w p g b Hs) as [_ [Hv _]]. right. exact Hv.
  Qed.

  (* ----- C1 and C2 on the driving network ----- *)

  Theorem coordinated_c1_static : FederationEvents.C1 G F (fun _ _ => True) E reg sig.
  Proof.
    intros ev z z' b _ _ _ _. unfold dfun.
    destruct (rule r T (reg ev)) as [[[p g] bb] |]; reflexivity.
  Qed.

  Theorem coordinated_c1r1 : forall s0, FederationEventsConverse.C1R1 G F idN E reg sig o s0.
  Proof.
    intros s0 p ev a _. unfold FederationEventsConverse.C1at, dfun.
    destruct (rule r T (reg ev)) as [[[q g] bb] |]; reflexivity.
  Qed.

  Theorem coordinated_c2at_iff : forall s e1 e2, reg e1 = reg e2 ->
    (FederationEventsConverse.C2at G F E reg sig s e1 e2 <->
     (reg e1 = r -> sig e2 (sig e1 (s r)) = sig e1 (sig e2 (s r)))).
  Proof.
    intros s e1 e2 _. unfold FederationEventsConverse.C2at.
    destruct (reg_cases e1) as [R | [p [g [b Hs]]]].
    - rewrite R, !dfun_root. split; intro H; [intros _; exact H | exact (H eq_refl)].
    - unfold dfun. rewrite Hs. split; [intros _ R | intros _; reflexivity].
      exfalso. rewrite R in Hs. rewrite (root_none r T HT) in Hs. discriminate.
  Qed.

  (* ----- the root value of a run ----- *)

  Lemma applyF_root : forall ev s,
    aF ev s r = if Nat.eq_dec (reg ev) r then sig ev (s r) else s r.
  Proof.
    intros ev s. unfold FederationEvents.applyF, FederationEvents.N.
    rewrite (FederationEvents.frun_solves _ _ _ _ _ _ _ _ _ HC o _ (topo_topoF _ _ Ho) r root_in_o).
    rewrite dfun_root. unfold FederationEvents.evstep.
    destruct (Nat.eq_dec (reg ev) r) as [R | R].
    - rewrite <- R. apply FederationEvents.upd_eq.
    - apply FederationEvents.upd_neq. intro H. apply R. symmetry. exact H.
  Qed.

  Theorem coordinated_root_run : forall p s,
    rF p s r = rrun (filter (fun ev => Nat.eqb (reg ev) r) p) (s r).
  Proof.
    induction p as [| a p IH]; intros s; [reflexivity |].
    change (rF (a :: p) s) with (rF p (aF a s)). rewrite IH, applyF_root.
    cbn [filter]. destruct (Nat.eq_dec (reg a) r) as [R | R].
    - rewrite (proj2 (Nat.eqb_eq _ _) R). reflexivity.
    - rewrite (proj2 (Nat.eqb_neq _ _) R). reflexivity.
  Qed.

  Theorem coordinated_root_reach : forall p s, RootReach (s r) (rF p s r).
  Proof.
    intros p s. exists (filter (fun ev => Nat.eqb (reg ev) r) p). split.
    - apply Forall_forall. intros x Hx. apply filter_In in Hx. apply Nat.eqb_eq. exact (proj2 Hx).
    - apply coordinated_root_run.
  Qed.

  Lemma filter_root_only : forall q, Forall (fun ev => reg ev = r) q ->
    filter (fun ev => Nat.eqb (reg ev) r) q = q.
  Proof.
    induction q as [| a q IH]; intros H; [reflexivity |].
    inversion H as [| ? ? Ha Hq]. cbn [filter].
    rewrite (proj2 (Nat.eqb_eq _ _) Ha), (IH Hq). reflexivity.
  Qed.

  Lemma root_only_run : forall q s, Forall (fun ev => reg ev = r) q -> rF q s r = rrun q (s r).
  Proof. intros q s Hq. rewrite coordinated_root_run, (filter_root_only q Hq). reflexivity. Qed.

  (* ----- the exact theorem, instantiated ----- *)

  Theorem coordinated_gc_iff : forall J s0,
    FederationEventsConverse.GCF G F idN E reg sig J o s0 <->
    FederationEventsConverse.TraceConv G F idN E reg sig J o s0.
  Proof. intros J s0. exact (acyclic_gc_iff G (dsrc r T) F _ idN E reg sig J o HC s0). Qed.

  Theorem coordinated_fed_exact : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv G F idN E reg sig J o s0 <->
     FederationEventsConverse.C1R1 G F idN E reg sig o s0 /\
     FederationEventsConverse.C2R G F idN E reg sig J o s0).
  Proof. intros J s0 Hc. exact (fed_exact G (dsrc r T) F _ idN E reg sig J o HC s0 (Inv_all s0) Hc). Qed.

  Theorem coordinated_fed_exact_full : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv G F idN E reg sig J o s0 <->
     FederationEventsConverse.C1R G F idN E reg sig o s0 /\
     FederationEventsConverse.C2R G F idN E reg sig J o s0).
  Proof.
    intros J s0 Hc. exact (fed_exact_full G (dsrc r T) F _ idN E reg sig J o HC s0 (Inv_all s0) Hc).
  Qed.

  (* Headline: event interleavings converge from s0 iff the root's J-independent events commute
     at every root value reachable from s0's root value by root events. *)
  Theorem coordinated_events_exact : forall J s0, ConsD s0 ->
    (FederationEventsConverse.TraceConv G F idN E reg sig J o s0 <-> RootCC J (s0 r)).
  Proof.
    intros J s0 Hc. rewrite (coordinated_fed_exact J s0 Hc). split.
    - intros [_ H2] x [q [Hq ->]] e1 e2 R1 R2 Hj.
      assert (E12 : reg e1 = reg e2) by (rewrite R1, R2; reflexivity).
      pose proof (proj1 (coordinated_c2at_iff _ e1 e2 E12) (H2 q e1 e2 E12 Hj) R1) as H.
      rewrite (root_only_run q s0 Hq) in H. exact H.
    - intros H. split; [apply coordinated_c1r1 |]. intros p e1 e2 E12 Hj.
      apply (proj2 (coordinated_c2at_iff _ e1 e2 E12)). intros R1.
      apply H; [apply coordinated_root_reach | exact R1 | rewrite <- E12; exact R1 | exact Hj].
  Qed.

  (* With every pair declared independent: permutations converge iff root events commute at
     every reachable root value. *)
  Theorem coordinated_perm_exact : forall s0, ConsD s0 ->
    ((forall es1 es2, Permutation es1 es2 -> FederationEvents.feq G (rF es1 s0) (rF es2 s0)) <->
     RootCC (fun _ _ => True) (s0 r)).
  Proof.
    intros s0 Hc. rewrite <- (coordinated_events_exact (fun _ _ => True) s0 Hc). split.
    - intros H es1 es2 Ht. apply H. exact (tequiv_perm _ _ _ Ht).
    - intros H es1 es2 Hp. apply H.
      apply (perm_tequiv_total _ (fun _ => True)); [intros; right; exact I | exact Hp |].
      apply Forall_forall. intros. exact I.
  Qed.

  (* The uniform version: convergence from every consistent start iff the root's J-independent
     events commute at every value (the old sufficient condition, made exact). *)
  Theorem coordinated_events_exact_global : forall J,
    (forall s0, ConsD s0 -> FederationEventsConverse.TraceConv G F idN E reg sig J o s0) <->
    (forall e1 e2 x, reg e1 = r -> reg e2 = r -> J e1 e2 -> sig e2 (sig e1 x) = sig e1 (sig e2 x)).
  Proof.
    intros J. split.
    - intros H e1 e2 x R1 R2 Hj.
      set (s := drive op inv r T o (fun _ => x)).
      destruct (drive_consistent op inv r T o (fun _ => x) HT Ho Hset) as [Hc [Hr _]].
      assert (Cs : ConsD s) by (intros j Hj'; apply Hc; apply Hset; exact Hj').
      pose proof (proj1 (coordinated_events_exact J s Cs) (H s Cs)) as Hcc.
      fold s in Hr. rewrite <- Hr. apply Hcc; [| exact R1 | exact R2 | exact Hj].
      exists []. split; [constructor | reflexivity].
    - intros H s0 Hc. apply (coordinated_events_exact J s0 Hc).
      intros x _ e1 e2 R1 R2 Hj. apply H; assumption.
  Qed.

  (* The old sufficient condition implies the exact one at every start. *)
  Lemma old_implies_rootcc : forall J,
    (forall e1 e2 x, reg e1 = r -> reg e2 = r -> J e1 e2 -> sig e2 (sig e1 x) = sig e1 (sig e2 x)) ->
    forall x0, RootCC J x0.
  Proof. intros J H x0 x _ e1 e2 R1 R2 Hj. apply H; assumption. Qed.

  (* ----- the plan: reached states satisfy the kept constraints ----- *)

  Theorem coordinated_runs_kept : forall B sT, is_section op sT T -> spans r T B ->
    (forall x, In x B -> sat op sT x) ->
    forall s0, ConsD s0 -> forall es, is_section op (rF es s0) (T ++ B).
  Proof.
    intros B sT HsT Hsp Hbal s0 Hc es.
    apply (kept_section op e inv assoc id_l inv_r inv_l r T B sT HT HsT Hsp Hbal).
    intros w Hw. apply (FederationEvents.runF_cons _ _ _ _ _ _ _ _ _ HC es s0 (Inv_all s0) Hc).
    apply Hset. exact Hw.
  Qed.

  Theorem coordinated_events_exact_plan : forall B sT, is_section op sT T -> spans r T B ->
    (forall x, In x B -> sat op sT x) ->
    forall J s0, ConsD s0 ->
      (FederationEventsConverse.TraceConv G F idN E reg sig J o s0 <-> RootCC J (s0 r)) /\
      (forall es, is_section op (rF es s0) (T ++ B)).
  Proof.
    intros B sT HsT Hsp Hbal J s0 Hc. split.
    - exact (coordinated_events_exact J s0 Hc).
    - exact (coordinated_runs_kept B sT HsT Hsp Hbal s0 Hc).
  Qed.

  (* coordinated_events_converge recovered: the old hypothesis gives permutation convergence
     from every consistent start, and the reached states satisfy T ++ B. *)
  Theorem coordinated_events_converge_recovered : forall B sT, is_section op sT T -> spans r T B ->
    (forall x, In x B -> sat op sT x) ->
    (forall e1 e2 x, reg e1 = r -> reg e2 = r -> sig e1 (sig e2 x) = sig e2 (sig e1 x)) ->
    forall es1 es2, Permutation es1 es2 -> forall s, ConsD s ->
      FederationEvents.feq G (rF es1 s) (rF es2 s) /\ is_section op (rF es1 s) (T ++ B).
  Proof.
    intros B sT HsT Hsp Hbal Hcc es1 es2 Hp s Hc. split.
    - apply (proj2 (coordinated_perm_exact s Hc)); [| exact Hp].
      apply old_implies_rootcc. intros e1 e2 x R1 R2 _. symmetry. apply Hcc; assumption.
    - exact (coordinated_runs_kept B sT HsT Hsp Hbal s Hc es1).
  Qed.
End Exact.

(* ============================================================
   The old sufficient condition is not necessary for a fixed start: the Klein group
   V4 = (bool * bool, componentwise xor), the tree A -> B (identity label) rooted at A.
   ============================================================ *)

Definition kop (a b : bool * bool) : bool * bool := (xorb (fst a) (fst b), xorb (snd a) (snd b)).
Definition kinv (a : bool * bool) : bool * bool := a.
Definition k0 : bool * bool := (false, false).

Lemma klein_group :
  (forall a b c, kop a (kop b c) = kop (kop a b) c) /\ (forall a, kop k0 a = a) /\
  (forall a, kop a k0 = a) /\ (forall a, kop a (kinv a) = k0) /\ (forall a, kop (kinv a) a = k0).
Proof.
  repeat split; intros; repeat match goal with p : (bool * bool)%type |- _ => destruct p end;
    repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.

Definition kT : list (@edge (bool * bool)) := [] ++ [(0, 1, k0)].

Lemma kT_tree : tree 0 kT.
Proof. unfold kT. apply t_out; [apply t_nil | left; reflexivity | simpl; intuition congruence]. Qed.

Lemma kT_order : FederationOrder.topo (dsrc 0 kT) [0; 1].
Proof.
  split; [repeat constructor; simpl; intuition congruence |].
  intros i k Hi Hk Hko. simpl in Hi.
  destruct Hi as [<- | [<- | []]]; cbv in Hk; [destruct Hk | destruct Hk as [<- | []]; simpl; auto].
Qed.

Lemma kT_verts : forall w, In w [0; 1] <-> In w (0 :: verts kT).
Proof. intro w. simpl. tauto. Qed.

Inductive kev : Type := KSwap | KClear | KWrite.

Definition kreg (ev : kev) : nat := match ev with KWrite => 1 | _ => 0 end.

Definition ksig (ev : kev) (x : bool * bool) : bool * bool :=
  match ev with
  | KSwap => (snd x, fst x)
  | KClear => (fst x, false)
  | KWrite => (true, true)
  end.

Lemma kreg_in : forall ev, In (kreg ev) [0; 1].
Proof. intros []; simpl; auto. Qed.

Definition kz (_ : nat) : bool * bool := (false, false).
Definition kt (_ : nat) : bool * bool := (true, false).

Lemma k_rrun_fixed : forall q, Forall (fun ev => kreg ev = 0) q -> rrun kev ksig q k0 = k0.
Proof.
  induction q as [| a q IH]; intros H; [reflexivity |].
  inversion H as [| ? ? Ha Hq]; subst. destruct a; simpl in Ha; try discriminate;
    unfold rrun in *; simpl; apply IH; exact Hq.
Qed.

Theorem old_condition_not_necessary :
  ~ (forall e1 e2 x, kreg e1 = 0 -> kreg e2 = 0 -> ksig e2 (ksig e1 x) = ksig e1 (ksig e2 x)) /\
  FederationEvents.Cons (bool * bool) (dfun kop kinv 0 kT) [0; 1] kz /\
  (forall es1 es2, Permutation es1 es2 ->
     FederationEvents.feq (bool * bool)
       (FederationEvents.runF (bool * bool) (dfun kop kinv 0 kT) (fun _ x => x) kev kreg ksig [0; 1] es1 kz)
       (FederationEvents.runF (bool * bool) (dfun kop kinv 0 kT) (fun _ x => x) kev kreg ksig [0; 1] es2 kz)) /\
  FederationEvents.Cons (bool * bool) (dfun kop kinv 0 kT) [0; 1] kt /\
  FederationEvents.runF (bool * bool) (dfun kop kinv 0 kT) (fun _ x => x) kev kreg ksig [0; 1]
    [KSwap; KClear] kt 0 <>
  FederationEvents.runF (bool * bool) (dfun kop kinv 0 kT) (fun _ x => x) kev kreg ksig [0; 1]
    [KClear; KSwap] kt 0.
Proof.
  assert (Cz : FederationEvents.Cons (bool * bool) (dfun kop kinv 0 kT) [0; 1] kz)
    by (intros j [<- | [<- | []]]; reflexivity).
  split.
  { intro H. pose proof (H KSwap KClear (true, false) eq_refl eq_refl) as Hd. discriminate Hd. }
  split; [exact Cz |]. split.
  - apply (coordinated_perm_exact kop kinv 0 kT [0; 1] kT_tree kT_order kT_verts kev kreg ksig
             kreg_in kz Cz).
    intros x [q [Hq ->]] e1 e2 R1 R2 _. change (kz 0) with k0. rewrite (k_rrun_fixed q Hq).
    destruct e1, e2; simpl in R1, R2; try discriminate; reflexivity.
  - split; [intros j [<- | [<- | []]]; reflexivity |].
    vm_compute. discriminate.
Qed.

(* ============================================================
   Non-vacuity on CoordinatedCycles.v's two Z/2 loops, with events.
   ============================================================ *)

Lemma cc_reg_cons : FederationEvents.Cons bool (dfun xorb (fun a => a) 0 cc_T) [0; 1] (fun _ => false).
Proof. intros j [<- | [<- | []]]; reflexivity. Qed.

(* ----- copy-back loop: root Flip, B Write; converges from every consistent start ----- *)

Inductive cbev : Type := CBFlip | CBWrite.

Definition cbreg (ev : cbev) : nat := match ev with CBFlip => 0 | CBWrite => 1 end.
Definition cbsig (ev : cbev) (x : bool) : bool := match ev with CBFlip => negb x | CBWrite => true end.

Lemma cbreg_in : forall ev, In (cbreg ev) [0; 1].
Proof. intros []; simpl; auto. Qed.

Lemma cc_spans_B : spans 0 cc_T cb_B.
Proof. apply cc_spans. intros u v g [H | []]. injection H as Eu Ev Eg. subst. lia. Qed.

Lemma cc_spans_negBC : spans 0 cc_T (neg_B ++ neg_C).
Proof. apply cc_spans. intros u v g [H | []]. injection H as Eu Ev Eg. subst. lia. Qed.

Theorem copyback_events_exact :
  FederationEvents.Cons bool (dfun xorb (fun a => a) 0 cc_T) [0; 1] (fun _ => false) /\
  forall s0, FederationEvents.Cons bool (dfun xorb (fun a => a) 0 cc_T) [0; 1] s0 ->
    RootCC 0 cbev cbreg cbsig (fun _ _ => True) (s0 0) /\
    (forall es1 es2, Permutation es1 es2 ->
       FederationEvents.feq bool
         (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) cbev cbreg cbsig [0; 1] es1 s0)
         (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) cbev cbreg cbsig [0; 1] es2 s0)) /\
    (forall es, is_section xorb
       (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) cbev cbreg cbsig [0; 1] es s0)
       (cc_T ++ cb_B ++ cb_C)).
Proof.
  split; [exact cc_reg_cons |]. intros s0 Hc.
  assert (Hr : RootCC 0 cbev cbreg cbsig (fun _ _ => True) (s0 0)).
  { intros x _ e1 e2 R1 R2 _. destruct e1, e2; simpl in R1, R2; try discriminate; reflexivity. }
  destruct (coordinated_events_exact_plan xorb false (fun a => a) xor_assoc xor_id_l xor_inv_r
              xor_inv_l 0 cc_T [0; 1] cc_tree0 cc_order0 cc_order0_verts cbev cbreg cbsig cbreg_in
              cb_B sT0 cc_section cc_spans_B cb_balanced (fun _ _ => True) s0 Hc) as [_ Hk].
  split; [exact Hr |]. split.
  - apply (proj2 (coordinated_perm_exact xorb (fun a => a) 0 cc_T [0; 1] cc_tree0 cc_order0
                    cc_order0_verts cbev cbreg cbsig cbreg_in s0 Hc)). exact Hr.
  - intro es. unfold cb_C. rewrite app_nil_r. apply Hk.
Qed.

(* ----- negation loop: root Set0 and Set1, B Flip; diverges from every consistent start ----- *)

Inductive ngev : Type := NSet0 | NSet1 | NFlip.

Definition ngreg (ev : ngev) : nat := match ev with NFlip => 1 | _ => 0 end.
Definition ngsig (ev : ngev) (x : bool) : bool :=
  match ev with NSet0 => false | NSet1 => true | NFlip => negb x end.

Lemma ngreg_in : forall ev, In (ngreg ev) [0; 1].
Proof. intros []; simpl; auto. Qed.

Theorem negation_events_exact :
  FederationEvents.Cons bool (dfun xorb (fun a => a) 0 cc_T) [0; 1] (fun _ => false) /\
  forall s0, FederationEvents.Cons bool (dfun xorb (fun a => a) 0 cc_T) [0; 1] s0 ->
    ~ RootCC 0 ngev ngreg ngsig (fun _ _ => True) (s0 0) /\
    FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1]
      [NSet0; NSet1] s0 0 <>
    FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1]
      [NSet1; NSet0] s0 0 /\
    ~ (forall es1 es2, Permutation es1 es2 ->
         FederationEvents.feq bool
           (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1] es1 s0)
           (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1] es2 s0)) /\
    (forall es, is_section xorb
       (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1] es s0)
       (cc_T ++ neg_B)) /\
    (forall es, ~ is_section xorb
       (FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1] es s0)
       (cc_T ++ neg_B ++ neg_C)).
Proof.
  split; [exact cc_reg_cons |]. intros s0 Hc.
  assert (Hnr : ~ RootCC 0 ngev ngreg ngsig (fun _ _ => True) (s0 0)).
  { intro H. assert (Hx : RootReach 0 ngev ngreg ngsig (s0 0) (s0 0))
      by (exists []; split; [constructor | reflexivity]).
    pose proof (H (s0 0) Hx NSet0 NSet1 eq_refl eq_refl I) as Hd. discriminate Hd. }
  split; [exact Hnr |].
  assert (Hd : FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1]
                 [NSet0; NSet1] s0 0 <>
               FederationEvents.runF bool (dfun xorb (fun a => a) 0 cc_T) (fun _ x => x) ngev ngreg ngsig [0; 1]
                 [NSet1; NSet0] s0 0).
  { rewrite (root_only_run xorb (fun a => a) 0 cc_T [0; 1] cc_tree0 cc_order0 cc_order0_verts
               ngev ngreg ngsig ngreg_in [NSet0; NSet1] s0) by (repeat constructor).
    rewrite (root_only_run xorb (fun a => a) 0 cc_T [0; 1] cc_tree0 cc_order0 cc_order0_verts
               ngev ngreg ngsig ngreg_in [NSet1; NSet0] s0) by (repeat constructor).
    discriminate. }
  split; [exact Hd |]. split.
  - intro H. apply Hd. apply (H [NSet0; NSet1] [NSet1; NSet0]). apply perm_swap.
  - split.
    + intro es.
      exact (coordinated_runs_kept xorb false (fun a => a) xor_assoc xor_id_l xor_inv_r xor_inv_l
               0 cc_T [0; 1] cc_tree0 cc_order0 cc_order0_verts ngev ngreg ngsig ngreg_in
               neg_B sT0 cc_section (fun u v g H => match H with end) (fun x H => match H with end)
               s0 Hc es).
    + intro es.
      exact (coordination_needed xorb false (fun a => a) xor_assoc xor_id_l xor_id_r xor_inv_r
               xor_inv_l 0 cc_T neg_B neg_C sT0 (1, 0, true) cc_tree0 cc_section cc_spans_negBC
               (or_introl eq_refl) (neg_unbalanced _ (or_introl eq_refl)) _).
Qed.
