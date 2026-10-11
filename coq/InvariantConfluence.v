(* InvariantConfluence.v: invariant confluence (Bailis, Fekete, Franklin, Ghodsi, Hellerstein and
   Stoica, "Coordination Avoidance in Database Systems", PVLDB 8(3), 2014) recovered through the
   framework kernels, with the kernels frozen. Axiom-free. A preregistered external-recovery
   experiment (docs/THEORY.md, "An outside theorem: invariant confluence").

   The outside definitions, as the papers state them.
     Bailis et al., section 4.1: a state is I-T-reachable if a (partially ordered) sequence of
     transaction and merge invocations yields it and every intermediate state produced by a
     transaction or a merge is I-valid; the earlier states are its ancestors (I-T-reachable states
     or the initial state D0, which is required to be I-valid). Definition 6: T is I-confluent
     with respect to I if, for all I-T-reachable states Di, Dj with a common ancestor state,
     Di merged with Dj is I-valid. Theorem 1: a globally I-valid system can execute T with
     coordination-freedom, transactional availability and convergence iff T is I-confluent.
     System model (section 3): transactions are maps D -> D run on one replica, a transaction
     commits unless it aborts itself or its result would violate I (Definition 2), progress
     depends only on the local replica (Definition 5), replicas exchange states by a merge that
     is assumed commutative, associative and idempotent (set union of versions in the initial
     model), convergence is pairwise (Definition 3), and the necessity proof (Appendix B) replays
     histories on servers isolated by partitions.
     Whittaker and Hellerstein, "Interactive checks for coordination avoidance", PVLDB 12(1),
     2018: reachability is inductive and a merge is never aborted (section 2); invariant closure
     (I s1 and I s2 imply I (s1 merged with s2)) is sufficient (their Theorem 1) and not necessary
     (their Example 2, an invariant-satisfying state that is not reachable), and the two coincide
     when every invariant-satisfying state is reachable (their Theorem 2).

   Frozen: no existing .v file is edited. The kernels used are TransportCSP.pol_solutions,
   pol_gamma_iff, section_solution, chain_pol (layer B), PresentedExecution.perm_swap_recovered
   (layer A, P2 on the free-delivery swap presentation, with N the identity) and
   CanonicalExecution.normalization_descent (state descent).

   Part 1, the outside definitions (section Model). itr_from a s: s is I-T-reachable from a (the
     base case is the start itself; a transaction step needs T to contain it and its result
     I-valid; a merge step needs its result I-valid). ITR := itr_from s0. CommonAnc, IConfB (the
     definition word for word, with a common ancestor), IConf (without it), wreach and WConf
     (Whittaker and Hellerstein's form), IClosed (invariant closure).
     - common_ancestor_free: two I-T-reachable states always have D0 as a common ancestor, so
       iconfb_iff: IConfB <-> IConf.
     - itr_valid: every I-T-reachable state is I-valid. iconf_iff_wconf: Bailis's and Whittaker
       and Hellerstein's definitions agree.
     - iclosed_iconf: invariant closure implies I-confluence.
     - iconf_iff_reach_closed (the exact statement): I-confluence iff the merge maps two
       I-T-reachable states to an I-T-reachable state.
     - iconf_iff_iclosed_all_reachable: when every I-valid state is I-T-reachable, closure and
       I-confluence coincide (Whittaker and Hellerstein, Theorem 2).
   Part 2, the layer B bridge (section Pointwise): states nat -> D, merge pmerge p s1 s2 :=
     fun w => p [s1 w; s2 w] (Bailis's set union is p = orb on version-membership vectors).
     - pol_iclosed, pol_iconfluent (target 1): a binary polymorphism of a template Gamma, with I
       the solutions of an instance over Gamma, makes T I-confluent for every T
       (pol_solutions). network_iconfluent: for an invariant that is a pinned transport network
       labeled by F, it suffices that p commutes with every map of F and fixes the pinned values
       (pol_gamma_iff, section_solution). max_iconfluent: pointwise max for monotone networks on
       nat (chain_pol), the merge of Whittaker and Hellerstein's Example 1.
     - preserves_prel: the kernel's preserves 2 p on the n-ary relation of a state predicate is
       closure of the predicate under pmerge up to the first n items. iclosed_iff_pol: for an
       invariant on n items, invariant closure is exactly "pmerge is a polymorphism of I".
       iconf_iff_pol_reach (target 2, exact): I-confluence is exactly "pmerge is a polymorphism of
       the relation of I-T-reachable states".
   Part 3, the counterexample (target 2): two versions a, b (items 0, 1), merge = set union, I =
     not both present (a two-version uniqueness constraint, a finite form of Whittaker and
     Hellerstein's Example 2 and of Bailis et al.'s Claim 3). With T = {add a}: I-confluent
     (uq_iconf) but the merge is not a polymorphism of I (uq_not_pol). With T = {add a, add b}:
     not I-confluent (uq2_not_iconf).
   Part 4, Theorem 1 (section Replicas): unboundedly many servers, all at D0; a transaction runs on
     one server and commits iff its local result is I-valid; a merge is never refused; any
     schedule. replica_valid (sufficiency, global validity), deliver_perm (order independence
     of merge delivery, from perm_swap_recovered), replica_converge (pairwise convergence after
     an exchange, to an I-valid state), replay (every I-T-reachable state is held by a server
     after some execution, Bailis's Lemma 1), replica_exact (Theorem 1 in this model: every
     execution keeps every server I-valid iff T is I-confluent).
   Part 5, repair (target 4): the two-version system with T = {add a, add b} is not I-confluent;
     the deterministic repair N (x, y) = (x, y && negb x) has state descent for every merge event
     and history descent (normalization_descent with perm_swap_recovered), every repaired state
     is I-valid, and two replicas that exchange repaired states agree with the repaired run of
     the joint history (repair_enlarges). *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.CohomologyGraph NC.CohomologyGeneral NC.Trace NC.TransportCSP.
Require NC.PresentedExecution NC.CanonicalExecution.
Import ListNotations.

(* ===================================================================== *)
(* Part 1: the outside definitions. *)

Section Model.
  Context {S : Type}.
  Variable m : S -> S -> S.          (* the merge *)
  Variable Tr : (S -> S) -> Prop.    (* the transaction set T *)
  Variable I : S -> Prop.            (* the invariant *)
  Variable s0 : S.                   (* the initial state D0 *)

  (* Bailis et al.: s is I-T-reachable from a; every intermediate state is I-valid. *)
  Inductive itr_from (a : S) : S -> Prop :=
  | if_start : itr_from a a
  | if_tx : forall s t, itr_from a s -> Tr t -> I (t s) -> itr_from a (t s)
  | if_merge : forall s1 s2, itr_from a s1 -> itr_from a s2 -> I (m s1 s2) -> itr_from a (m s1 s2).

  Definition ITR (s : S) : Prop := itr_from s0 s.

  Definition CommonAnc (s1 s2 : S) : Prop :=
    exists a, (a = s0 \/ ITR a) /\ itr_from a s1 /\ itr_from a s2.

  (* Definition 6, word for word. *)
  Definition IConfB : Prop :=
    forall s1 s2, ITR s1 -> ITR s2 -> CommonAnc s1 s2 -> I (m s1 s2).

  Definition IConf : Prop := forall s1 s2, ITR s1 -> ITR s2 -> I (m s1 s2).

  (* Whittaker and Hellerstein: merges are never aborted; confluence is "every reachable state is
     I-valid". *)
  Inductive wreach : S -> Prop :=
  | w_start : wreach s0
  | w_tx : forall s t, wreach s -> Tr t -> I (t s) -> wreach (t s)
  | w_merge : forall s1 s2, wreach s1 -> wreach s2 -> wreach (m s1 s2).

  Definition WConf : Prop := forall s, wreach s -> I s.

  Definition IClosed : Prop := forall s1 s2, I s1 -> I s2 -> I (m s1 s2).

  Lemma common_ancestor_free : forall s1 s2, ITR s1 -> ITR s2 -> CommonAnc s1 s2.
  Proof. intros s1 s2 H1 H2. exists s0. split; [left; reflexivity | split; assumption]. Qed.

  Theorem iconfb_iff : IConfB <-> IConf.
  Proof.
    split.
    - intros H s1 s2 H1 H2. exact (H s1 s2 H1 H2 (common_ancestor_free s1 s2 H1 H2)).
    - intros H s1 s2 H1 H2 _. exact (H s1 s2 H1 H2).
  Qed.

  Lemma itr_from_valid : forall a s, I a -> itr_from a s -> I s.
  Proof. intros a s Ha H. induction H; assumption. Qed.

  Theorem itr_valid : I s0 -> forall s, ITR s -> I s.
  Proof. intros H0 s H. exact (itr_from_valid s0 s H0 H). Qed.

  Theorem iconf_iff_wconf : I s0 -> (IConf <-> WConf).
  Proof.
    intros H0. split.
    - intros H. assert (K : forall s, wreach s -> ITR s).
      { intros s Hw. induction Hw as [| s t _ IH Ht Hi | s1 s2 _ IH1 _ IH2].
        - apply if_start.
        - apply if_tx; assumption.
        - apply if_merge; [exact IH1 | exact IH2 | exact (H s1 s2 IH1 IH2)]. }
      intros s Hw. exact (itr_valid H0 s (K s Hw)).
    - intros H. assert (K : forall s, ITR s -> wreach s).
      { intros s Hr. induction Hr as [| s t _ IH Ht Hi | s1 s2 _ IH1 _ IH2 _].
        - apply w_start.
        - apply w_tx; assumption.
        - apply w_merge; assumption. }
      intros s1 s2 H1 H2. apply H. apply w_merge; apply K; assumption.
  Qed.

  Theorem iclosed_iconf : I s0 -> IClosed -> IConf.
  Proof. intros H0 Hc s1 s2 H1 H2. apply Hc; apply itr_valid; assumption. Qed.

  (* The exact statement: I-confluence is closure of the I-T-reachable states under merge. *)
  Theorem iconf_iff_reach_closed :
    I s0 -> (IConf <-> forall s1 s2, ITR s1 -> ITR s2 -> ITR (m s1 s2)).
  Proof.
    intros H0. split.
    - intros H s1 s2 H1 H2. apply if_merge; [exact H1 | exact H2 | exact (H s1 s2 H1 H2)].
    - intros H s1 s2 H1 H2. apply itr_valid; [exact H0 | exact (H s1 s2 H1 H2)].
  Qed.

  (* Whittaker and Hellerstein, Theorem 2. *)
  Theorem iconf_iff_iclosed_all_reachable :
    I s0 -> (forall s, I s -> ITR s) -> (IClosed <-> IConf).
  Proof.
    intros H0 Hall. split.
    - exact (iclosed_iconf H0).
    - intros H s1 s2 H1 H2. exact (H s1 s2 (Hall s1 H1) (Hall s2 H2)).
  Qed.
End Model.

(* ===================================================================== *)
(* Part 2: the layer B bridge. States are assignments nat -> D (an item w holds the value s w);
   the merge acts item by item through a binary operation p. *)

Section Pointwise.
  Context {D : Type}.
  Variable p : list D -> D.

  Definition pmerge (s1 s2 : nat -> D) : nat -> D := fun w => p [s1 w; s2 w].

  (* The two states as the rows of pol_solutions' family. *)
  Definition pick (s1 s2 : nat -> D) (i : nat) : nat -> D := match i with 0 => s1 | _ => s2 end.

  (* Target 1, step 1 (pol_solutions): a polymorphism of the template closes the solution set. *)
  Theorem pol_iclosed : forall Gamma Ic, pol 2 p Gamma -> over Gamma Ic ->
    IClosed pmerge (fun s => solution s Ic).
  Proof.
    intros Gamma Ic Hp Hov s1 s2 H1 H2.
    exact (pol_solutions 2 p Gamma Ic Hp Hov (pick s1 s2)
             (fun i Hi => match i as j return solution (pick s1 s2 j) Ic with
                          | 0 => H1 | S _ => H2 end)).
  Qed.

  (* Target 1: a polymorphism of the invariant's template makes every T I-confluent. *)
  Theorem pol_iconfluent : forall Gamma Ic s0 (Tr : ((nat -> D) -> nat -> D) -> Prop),
    pol 2 p Gamma -> over Gamma Ic -> solution s0 Ic ->
    IConf pmerge Tr (fun s => solution s Ic) s0.
  Proof.
    intros Gamma Ic s0 Tr Hp Hov H0.
    exact (iclosed_iconf pmerge Tr _ s0 H0 (pol_iclosed Gamma Ic Hp Hov)).
  Qed.

  (* The invariant is a pinned transport network: commuting with its maps and fixing its pins
     suffices (pol_gamma_iff, section_iff_csp). *)
  Theorem network_iconfluent :
    forall (F : list (D -> D)) cs (G : list (@edge (D -> D))) P s0 (Tr : ((nat -> D) -> nat -> D) -> Prop),
      labeled F G -> (forall r c, In (r, c) P -> In c cs) ->
      (forall f, In f F -> commutes 2 p f) -> (forall c, In c cs -> p [c; c] = c) ->
      msection s0 G -> pinned s0 P ->
      IConf pmerge Tr (fun s => msection s G /\ pinned s P) s0.
  Proof.
    intros F cs G P s0 Tr HF Hcs Hc Hpin Hs0 Hp0.
    apply iclosed_iconf; [split; assumption |].
    assert (Hpol : pol 2 p (gamma F cs)) by (apply pol_gamma_iff; split; assumption).
    pose proof (proj2 (section_iff_csp F cs G P HF Hcs)) as Hov.
    intros s1 s2 H1 H2. apply section_solution.
    apply (pol_iclosed (gamma F cs) (csp_of G P) Hpol Hov); apply section_solution; assumption.
  Qed.

  (* The relation on n items of a state predicate. *)
  Definition prel (n : nat) (Q : (nat -> D) -> Prop) : @rel D :=
    (n, fun t => exists s, Q s /\ map s (seq 0 n) = t).

  Lemma map_eq_seq : forall (f g : nat -> D) n, map f (seq 0 n) = map g (seq 0 n) ->
    forall w, w < n -> f w = g w.
  Proof.
    intros f g n E w Hw. assert (Hin : In w (seq 0 n)) by (apply in_seq; lia).
    revert E Hin. generalize (seq 0 n). intros l. induction l as [| x l IH]; simpl; [tauto |].
    intros E [<- | Hin]; injection E as E1 E2; [exact E1 | exact (IH E2 Hin)].
  Qed.

  (* The kernel's preserves, read on states. *)
  Theorem preserves_prel : forall n Q,
    preserves 2 p (prel n Q) <->
    forall s1 s2, Q s1 -> Q s2 -> exists s, Q s /\ forall w, w < n -> s w = pmerge s1 s2 w.
  Proof.
    intros n Q. split.
    - intros H s1 s2 H1 H2.
      assert (Hrow : forall i, i < 2 -> snd (prel n Q) (row (fst (prel n Q)) (pick s1 s2) i)).
      { intros [| i] _; [exists s1 | exists s2]; split; try assumption; reflexivity. }
      destruct (H (pick s1 s2) Hrow) as [s [Hs E]]. exists s. split; [exact Hs |].
      intros w Hw. exact (map_eq_seq s (fun j => p (col 2 (pick s1 s2) j)) n E w Hw).
    - intros H M Hrow.
      destruct (Hrow 0 ltac:(lia)) as [s1 [H1 E1]]. destruct (Hrow 1 ltac:(lia)) as [s2 [H2 E2]].
      destruct (H s1 s2 H1 H2) as [s [Hs Hw]]. exists s. split; [exact Hs |]. simpl.
      apply map_ext_in. intros j Hj. apply in_seq in Hj. rewrite (Hw j ltac:(lia)).
      unfold pmerge, col. simpl.
      rewrite (map_eq_seq s1 (M 0) n E1 j ltac:(lia)), (map_eq_seq s2 (M 1) n E2 j ltac:(lia)).
      reflexivity.
  Qed.

  (* An invariant that reads only the first n items. *)
  Definition Local (n : nat) (Q : (nat -> D) -> Prop) : Prop :=
    forall s s', (forall w, w < n -> s w = s' w) -> Q s -> Q s'.

  (* Invariant closure is exactly "the merge is a polymorphism of I". *)
  Theorem iclosed_iff_pol : forall n (Iv : (nat -> D) -> Prop), Local n Iv ->
    (IClosed pmerge Iv <-> preserves 2 p (prel n Iv)).
  Proof.
    intros n Iv HL. rewrite preserves_prel. split.
    - intros H s1 s2 H1 H2. exists (pmerge s1 s2). split; [exact (H s1 s2 H1 H2) | reflexivity].
    - intros H s1 s2 H1 H2. destruct (H s1 s2 H1 H2) as [s [Hs Hw]]. exact (HL s _ Hw Hs).
  Qed.

  (* Target 2, exact: I-confluence is exactly "the merge is a polymorphism of the relation of
     I-T-reachable states". *)
  Theorem iconf_iff_pol_reach : forall n (Iv : (nat -> D) -> Prop) Tr s0, Local n Iv -> Iv s0 ->
    (IConf pmerge Tr Iv s0 <-> preserves 2 p (prel n (ITR pmerge Tr Iv s0))).
  Proof.
    intros n Iv Tr s0 HL H0. rewrite preserves_prel, (iconf_iff_reach_closed _ _ _ _ H0). split.
    - intros H s1 s2 H1 H2. exists (pmerge s1 s2). split; [exact (H s1 s2 H1 H2) | reflexivity].
    - intros H s1 s2 H1 H2. destruct (H s1 s2 H1 H2) as [s [Hs Hw]].
      apply if_merge; [exact H1 | exact H2 |].
      exact (HL s _ Hw (itr_valid _ _ _ _ H0 s Hs)).
  Qed.
End Pointwise.

(* Non-vacuity of target 1: pointwise max on a monotone network over nat (chain_pol), with a
   transaction that changes the state. *)
Definition capS2 (x : nat) : nat := Nat.min (S x) 3.
Definition mx_G : list (@edge (nat -> nat)) := [(0, 1, capS2)].
Definition mx_s0 (w : nat) : nat := match w with 0 => 0 | 1 => 1 | _ => 0 end.
Definition mx_bump (s : nat -> nat) : nat -> nat :=
  fun w => match w with 0 => S (s 0) | 1 => capS2 (S (s 0)) | _ => s w end.

Theorem max_iconfluent : forall (Tr : ((nat -> nat) -> nat -> nat) -> Prop) (F : list (nat -> nat)) G s0,
  (forall f, In f F -> TransportCSP.mono f) -> labeled F G -> msection s0 G ->
  IConf (pmerge max2) Tr (fun s => msection s G /\ pinned s []) s0.
Proof.
  intros Tr F G s0 HF HG Hs0.
  destruct (chain_pol F [] HF) as [_ [Hmax _]].
  apply iclosed_iconf; [split; [exact Hs0 | intros r c []] |].
  pose proof (proj2 (section_iff_csp F [] G [] HG (fun r c H => match H with end))) as Hov.
  intros s1 s2 H1 H2. apply section_solution.
  apply (pol_iclosed max2 (gamma F []) (csp_of G []) Hmax Hov); apply section_solution; assumption.
Qed.

Theorem max_nonvacuous :
  msection mx_s0 mx_G /\ msection (mx_bump mx_s0) mx_G /\ mx_bump mx_s0 0 <> mx_s0 0 /\
  ITR (pmerge max2) (fun t => t = mx_bump) (fun s => msection s mx_G /\ pinned s []) mx_s0
      (mx_bump mx_s0) /\
  IConf (pmerge max2) (fun t => t = mx_bump) (fun s => msection s mx_G /\ pinned s []) mx_s0.
Proof.
  assert (Hs : msection mx_s0 mx_G) by (intros x [<- | []]; reflexivity).
  assert (Hb : msection (mx_bump mx_s0) mx_G) by (intros x [<- | []]; reflexivity).
  split; [exact Hs | split; [exact Hb | split; [discriminate | split]]].
  - apply if_tx; [apply if_start | reflexivity | split; [exact Hb | intros r c []]].
  - apply (max_iconfluent _ [capS2]); [| intros u v f [E | []]; injection E as _ _ <-; left; reflexivity
                                       | exact Hs].
    intros f [<- | []] x y Hxy. unfold capS2. lia.
Qed.

(* ===================================================================== *)
(* Part 3: the counterexample to the converse of target 1. Two versions, a (item 0) and b
   (item 1); a state is the membership vector of its versions; merge is set union (orb); the
   invariant forbids both versions at once. *)

Definition orb2 (l : list bool) : bool := match l with [x; y] => orb x y | _ => false end.
Definition uq_merge : (nat -> bool) -> (nat -> bool) -> nat -> bool := pmerge orb2.
Definition uq_I (s : nat -> bool) : Prop := ~ (s 0 = true /\ s 1 = true).
Definition uq_s0 (_ : nat) : bool := false.
Definition add_a (s : nat -> bool) : nat -> bool := fun w => if Nat.eqb w 0 then true else s w.
Definition add_b (s : nat -> bool) : nat -> bool := fun w => if Nat.eqb w 1 then true else s w.
Definition uq_T1 (t : (nat -> bool) -> nat -> bool) : Prop := t = add_a.
Definition uq_T2 (t : (nat -> bool) -> nat -> bool) : Prop := t = add_a \/ t = add_b.

Lemma uq_local : Local 2 uq_I.
Proof. intros s s' Hw H [E0 E1]. apply H. rewrite (Hw 0), (Hw 1) by lia. tauto. Qed.

(* With T = {add a}, version b never appears in a reachable state. *)
Lemma uq_reach_no_b : forall s, ITR uq_merge uq_T1 uq_I uq_s0 s -> s 1 = false.
Proof.
  intros s H. induction H as [| s t _ IH Ht _ | s1 s2 _ IH1 _ IH2 _].
  - reflexivity.
  - unfold uq_T1 in Ht. subst t. exact IH.
  - unfold uq_merge, pmerge. simpl. rewrite IH1, IH2. reflexivity.
Qed.

Theorem uq_iconf : IConf uq_merge uq_T1 uq_I uq_s0.
Proof.
  intros s1 s2 H1 H2 [_ E]. unfold uq_merge, pmerge in E. simpl in E.
  rewrite (uq_reach_no_b s1 H1), (uq_reach_no_b s2 H2) in E. discriminate.
Qed.

Definition uq_sa (w : nat) : bool := Nat.eqb w 0.
Definition uq_sb (w : nat) : bool := Nat.eqb w 1.

Theorem uq_not_iclosed : ~ IClosed uq_merge uq_I.
Proof.
  intros H. apply (H uq_sa uq_sb); [intros [_ E]; discriminate | intros [E _]; discriminate |].
  split; reflexivity.
Qed.

(* The counterexample: I-confluent, and the merge is not a polymorphism of I. *)
Theorem uq_not_pol :
  IConf uq_merge uq_T1 uq_I uq_s0 /\ ~ preserves 2 orb2 (prel 2 uq_I).
Proof.
  split; [exact uq_iconf |]. intros H. apply uq_not_iclosed.
  apply (iclosed_iff_pol orb2 2 uq_I uq_local). exact H.
Qed.

(* The exact statement applies: the merge is a polymorphism of the reachable relation. *)
Theorem uq_pol_reach : preserves 2 orb2 (prel 2 (ITR uq_merge uq_T1 uq_I uq_s0)).
Proof.
  apply (iconf_iff_pol_reach orb2 2 uq_I uq_T1 uq_s0 uq_local); [intros [E _]; discriminate |].
  exact uq_iconf.
Qed.

(* With T = {add a, add b}: not I-confluent (two versions written apart, merged invalid). *)
Theorem uq2_not_iconf : ~ IConf uq_merge uq_T2 uq_I uq_s0.
Proof.
  intros H.
  assert (Ha : ITR uq_merge uq_T2 uq_I uq_s0 (add_a uq_s0))
    by (apply if_tx; [apply if_start | left; reflexivity | intros [_ E]; discriminate]).
  assert (Hb : ITR uq_merge uq_T2 uq_I uq_s0 (add_b uq_s0))
    by (apply if_tx; [apply if_start | right; reflexivity | intros [E _]; discriminate]).
  apply (H _ _ Ha Hb). split; reflexivity.
Qed.

(* ===================================================================== *)
(* Part 4: Bailis et al.'s Theorem 1 in a replica model. Servers are indexed by nat and all start
   at D0. Tx r t: server r runs t on its own state and commits iff the result is I-valid
   (transactional availability with no voluntary aborts; coordination-free, since the decision
   reads only server r's state). Mg r r': server r merges in server r''s state; a merge is never
   refused. Any word of steps is an execution (partitions are schedules). *)

Section Replicas.
  Context {S : Type}.
  Variable m : S -> S -> S.
  Variable Tr : (S -> S) -> Prop.
  Variable I : S -> Prop.
  Variable Idec : forall s, {I s} + {~ I s}.
  Variable s0 : S.

  Inductive rev : Type := Tx (r : nat) (t : S -> S) | Mg (r r' : nat).

  Definition upd (c : nat -> S) (r : nat) (v : S) : nat -> S :=
    fun x => if Nat.eqb x r then v else c x.

  Definition rstep (e : rev) (c : nat -> S) : nat -> S :=
    match e with
    | Tx r t => if Idec (t (c r)) then upd c r (t (c r)) else c
    | Mg r r' => upd c r (m (c r) (c r'))
    end.

  Definition okE (e : rev) : Prop := match e with Tx _ t => Tr t | Mg _ _ => True end.
  Definition init : nat -> S := fun _ => s0.
  Definition exec (w : list rev) : nat -> S := runT rstep w init.

  (* Transactional availability: a transaction commits iff its local result is I-valid. *)
  Theorem tx_available : forall c r t,
    (I (t (c r)) -> rstep (Tx r t) c r = t (c r)) /\ (~ I (t (c r)) -> rstep (Tx r t) c = c).
  Proof.
    intros c r t. simpl. split; intros H; destruct (Idec (t (c r))) as [K | K]; try contradiction.
    - unfold upd. rewrite Nat.eqb_refl. reflexivity.
    - reflexivity.
  Qed.

  (* Sufficiency, global validity: every server always holds an I-T-reachable state. *)
  Lemma rstep_itr : IConf m Tr I s0 -> forall e c, okE e ->
    (forall r, ITR m Tr I s0 (c r)) -> forall r, ITR m Tr I s0 (rstep e c r).
  Proof.
    intros H [r t | r r'] c He Hc x; simpl; unfold upd.
    - destruct (Idec (t (c r))) as [K | K]; [| apply Hc].
      destruct (Nat.eqb x r); [apply if_tx; [apply Hc | exact He | exact K] | apply Hc].
    - destruct (Nat.eqb x r); [| apply Hc].
      apply if_merge; [apply Hc | apply Hc | apply H; apply Hc].
  Qed.

  Theorem replica_valid : I s0 -> IConf m Tr I s0 ->
    forall w, Forall okE w -> forall r, ITR m Tr I s0 (exec w r) /\ I (exec w r).
  Proof.
    intros H0 H w Hw.
    assert (K : forall c, (forall r, ITR m Tr I s0 (c r)) -> forall r, ITR m Tr I s0 (runT rstep w c r)).
    { induction Hw as [| e w He _ IH]; intros c Hc; [exact Hc |].
      rewrite runT_cons. apply IH. exact (rstep_itr H e c He Hc). }
    intros r. assert (R : ITR m Tr I s0 (exec w r)) by (apply K; intros x; apply if_start).
    split; [exact R | exact (itr_valid m Tr I s0 H0 _ R)].
  Qed.

  (* Convergence. A server delivering the states l merges them in, one at a time. *)
  Definition deliver (x : S) (l : list S) : S := runT (fun a s => m s a) l x.

  Hypothesis m_comm : forall x y, m x y = m y x.
  Hypothesis m_assoc : forall x y z, m (m x y) z = m x (m y z).

  (* Layer A with N the identity: delivery order does not matter (perm_swap_recovered). *)
  Theorem deliver_perm : forall x l l', Permutation l l' -> deliver x l = deliver x l'.
  Proof.
    intros x. apply (proj2 (NC.PresentedExecution.perm_swap_recovered (fun a s => m s a)
                              (fun s => s) eq (@eq_refl S) (@eq_sym S) (@eq_trans S) x)).
    intros u a b w. f_equal. rewrite !m_assoc, (m_comm a b). reflexivity.
  Qed.

  Lemma deliver_swap : forall a b l, deliver a (b :: l) = deliver b (a :: l).
  Proof. intros a b l. unfold deliver. rewrite !runT_cons, m_comm. reflexivity. Qed.

  (* The delivered state depends only on the multiset of the start and the delivered states. *)
  Theorem deliver_multiset : forall x1 l1 x2 l2,
    Permutation (x1 :: l1) (x2 :: l2) -> deliver x1 l1 = deliver x2 l2.
  Proof.
    intros x1 l1 x2 l2 P.
    assert (Hin : In x2 (x1 :: l1)) by (apply (Permutation_in x2 (Permutation_sym P)); left; reflexivity).
    destruct Hin as [-> | Hin].
    - apply deliver_perm. exact (Permutation_cons_inv P).
    - apply in_split in Hin. destruct Hin as [la [lb ->]].
      rewrite (deliver_perm x1 _ (x2 :: la ++ lb)) by (apply Permutation_sym, Permutation_middle).
      rewrite deliver_swap. apply deliver_perm. apply (Permutation_cons_inv (a := x2)).
      apply (Permutation_trans (l' := x1 :: la ++ x2 :: lb)); [| exact P].
      apply (Permutation_trans (l' := x1 :: x2 :: la ++ lb)); [apply perm_swap |].
      apply perm_skip. apply Permutation_middle.
  Qed.

  Lemma deliver_itr : IConf m Tr I s0 -> forall l x, ITR m Tr I s0 x ->
    Forall (ITR m Tr I s0) l -> ITR m Tr I s0 (deliver x l).
  Proof.
    intros H l. induction l as [| y l IH]; intros x Hx Hl; [exact Hx |].
    inversion Hl as [| ? ? Hy Hl']; subst. unfold deliver. rewrite runT_cons. apply IH; [| exact Hl'].
    apply if_merge; [exact Hx | exact Hy | exact (H x y Hx Hy)].
  Qed.

  (* Sufficiency, convergence: after any execution, two servers that each merge in states held by
     servers, so that their own state and what they receive form the same multiset, hold the
     same state, and it is I-valid. The basic exchange is l1 = [c r2], l2 = [c r1]. *)
  Theorem replica_converge : I s0 -> IConf m Tr I s0 ->
    forall w, Forall okE w -> forall r1 r2 l1 l2,
      Forall (fun y => exists r, y = exec w r) l1 -> Forall (fun y => exists r, y = exec w r) l2 ->
      Permutation (exec w r1 :: l1) (exec w r2 :: l2) ->
      deliver (exec w r1) l1 = deliver (exec w r2) l2 /\ I (deliver (exec w r1) l1).
  Proof.
    intros H0 H w Hw r1 r2 l1 l2 H1 _ P. split; [exact (deliver_multiset _ _ _ _ P) |].
    apply (itr_valid m Tr I s0 H0). apply deliver_itr; [exact H | apply replica_valid; assumption |].
    apply (Forall_impl _ (fun y (Hy : exists r, y = exec w r) =>
             match Hy with ex_intro _ r E => eq_ind_r (ITR m Tr I s0) (proj1 (replica_valid H0 H w Hw r)) E end)).
    exact H1.
  Qed.
End Replicas.

(* Necessity in the replica model: every I-T-reachable state is held by some server after some
   execution (Bailis et al.'s Lemma 1, REPLAY), by running the two halves of a merge on disjoint
   sets of servers (even and odd indices) and then merging. *)
Section Replay.
  Context {S : Type}.
  Variable m : S -> S -> S.
  Variable Tr : (S -> S) -> Prop.
  Variable I : S -> Prop.
  Variable Idec : forall s, {I s} + {~ I s}.
  Variable s0 : S.

  Local Notation rstep := (InvariantConfluence.rstep m I Idec).
  Local Notation exec := (InvariantConfluence.exec m I Idec s0).

  Definition ren (f : nat -> nat) (e : @rev S) : @rev S :=
    match e with Tx r t => Tx (f r) t | Mg r r' => Mg (f r) (f r') end.

  Lemma rstep_ren : forall f, (forall x y, f x = f y -> x = y) ->
    forall e c d, (forall n, c (f n) = d n) -> forall n, rstep (ren f e) c (f n) = rstep e d n.
  Proof.
    intros f Hf [r t | r r'] c d Hcd n; simpl; unfold upd.
    - rewrite (Hcd r). destruct (Idec (t (d r))); [| apply Hcd].
      destruct (Nat.eqb_spec (f n) (f r)) as [E | E]; destruct (Nat.eqb_spec n r) as [E' | E'];
        try reflexivity; [exfalso; exact (E' (Hf _ _ E)) | subst; contradiction | apply Hcd].
    - rewrite (Hcd r), (Hcd r').
      destruct (Nat.eqb_spec (f n) (f r)) as [E | E]; destruct (Nat.eqb_spec n r) as [E' | E'];
        try reflexivity; [exfalso; exact (E' (Hf _ _ E)) | subst; contradiction | apply Hcd].
  Qed.

  Lemma run_ren : forall f, (forall x y, f x = f y -> x = y) -> forall w c d,
    (forall n, c (f n) = d n) -> forall n, runT rstep (map (ren f) w) c (f n) = runT rstep w d n.
  Proof.
    intros f Hf w. induction w as [| e w IH]; intros c d Hcd n; [apply Hcd |].
    simpl map. rewrite !runT_cons. apply IH. apply rstep_ren; assumption.
  Qed.

  Lemma run_ren_out : forall f w c x, (forall n, x <> f n) -> runT rstep (map (ren f) w) c x = c x.
  Proof.
    intros f w. induction w as [| e w IH]; intros c x Hx; [reflexivity |].
    simpl map. rewrite runT_cons, IH by exact Hx.
    destruct e as [r t | r r']; simpl; unfold upd; [destruct (Idec (t (c (f r)))); [| reflexivity] |];
      destruct (Nat.eqb_spec x (f r)) as [E | E]; try reflexivity; exfalso; exact (Hx r E).
  Qed.

  Definition evn (n : nat) : nat := n + n.
  Definition odd1 (n : nat) : nat := Datatypes.S (n + n).

  Lemma okE_ren : forall f w, Forall (okE Tr) w -> Forall (okE Tr) (map (ren f) w).
  Proof. intros f w Hw. induction Hw as [| [r t | r r'] w He _ IH]; simpl; constructor; assumption. Qed.

  (* Two executions, run side by side on even and odd servers, then merged. *)
  Lemma replay_merge : forall w1 r1 w2 r2, Forall (okE Tr) w1 -> Forall (okE Tr) w2 ->
    exists w r, Forall (okE Tr) w /\ exec w r = m (exec w1 r1) (exec w2 r2).
  Proof.
    intros w1 r1 w2 r2 Hw1 Hw2.
    exists (map (ren evn) w1 ++ map (ren odd1) w2 ++ [Mg (evn r1) (odd1 r2)]), (evn r1). split.
    - apply Forall_app. split; [apply okE_ren; exact Hw1 |].
      apply Forall_app. split; [apply okE_ren; exact Hw2 | constructor; [exact Logic.I | constructor]].
    - unfold exec. rewrite !runT_app. simpl. unfold upd. rewrite Nat.eqb_refl.
      set (c1 := runT rstep (map (ren evn) w1) (init s0)).
      assert (Hinj1 : forall x y, evn x = evn y -> x = y) by (unfold evn; lia).
      assert (Hinj2 : forall x y, odd1 x = odd1 y -> x = y) by (unfold odd1; lia).
      assert (Hc1 : forall n, c1 (odd1 n) = init s0 n)
        by (intros n; change (c1 (odd1 n) = init s0 (odd1 n)); unfold c1; apply run_ren_out; unfold evn, odd1; lia).
      rewrite (run_ren_out odd1 w2 c1 (evn r1)) by (unfold evn, odd1; lia).
      rewrite (run_ren odd1 Hinj2 w2 c1 (init s0) Hc1 r2).
      unfold c1. rewrite (run_ren evn Hinj1 w1 (init s0) (init s0) (fun _ => eq_refl) r1).
      reflexivity.
  Qed.

  (* Bailis et al.'s Lemma 1: every I-T-reachable state is held by a server after some execution. *)
  Theorem replay : forall s, ITR m Tr I s0 s -> exists w r, Forall (okE Tr) w /\ exec w r = s.
  Proof.
    intros s H.
    induction H as [| s t _ [w [r [Hw E]]] Ht Hi | s1 s2 _ [w1 [r1 [Hw1 E1]]] _ [w2 [r2 [Hw2 E2]]] _].
    - exists [], 0. split; [constructor | reflexivity].
    - exists (w ++ [Tx r t]), r. split.
      + apply Forall_app. split; [exact Hw | constructor; [exact Ht | constructor]].
      + unfold exec. rewrite runT_app. simpl. fold (exec w). rewrite E.
        destruct (Idec (t s)) as [K | K]; [| contradiction]. unfold upd. rewrite Nat.eqb_refl. reflexivity.
    - rewrite <- E1, <- E2. apply replay_merge; assumption.
  Qed.

  (* Necessity in this model: if every execution keeps every server I-valid, T is I-confluent. *)
  Theorem replica_necessity :
    (forall w, Forall (okE Tr) w -> forall r, I (exec w r)) -> IConf m Tr I s0.
  Proof.
    intros H s1 s2 H1 H2.
    destruct (replay s1 H1) as [w1 [r1 [Hw1 <-]]]. destruct (replay s2 H2) as [w2 [r2 [Hw2 <-]]].
    destruct (replay_merge w1 r1 w2 r2 Hw1 Hw2) as [w [r [Hw <-]]]. exact (H w Hw r).
  Qed.

  (* Theorem 1 in the replica model: the check-locally-and-merge system is globally I-valid iff
     T is I-confluent. *)
  Theorem replica_exact : I s0 ->
    ((forall w, Forall (okE Tr) w -> forall r, I (exec w r)) <-> IConf m Tr I s0).
  Proof.
    intros H0. split; [exact replica_necessity |].
    intros H w Hw r. exact (proj2 (replica_valid m Tr I Idec s0 H0 H w Hw r)).
  Qed.
End Replay.

(* ===================================================================== *)
(* Part 5: the two-version system on pairs (a present, b present), where states have decidable
   equality and set union is commutative and associative; non-vacuity of Part 4; and repair. *)

Definition bb : Type := (bool * bool)%type.
Definition bm (x y : bb) : bb := (fst x || fst y, snd x || snd y).
Definition bI (x : bb) : Prop := ~ (fst x = true /\ snd x = true).
Definition b0 : bb := (false, false).
Definition ba (x : bb) : bb := bm x (true, false).
Definition bbv (x : bb) : bb := bm x (false, true).
Definition bT1 (t : bb -> bb) : Prop := t = ba.
Definition bT2 (t : bb -> bb) : Prop := t = ba \/ t = bbv.

Definition bI_dec (x : bb) : {bI x} + {~ bI x}.
Proof.
  destruct x as [[|] [|]]; unfold bI; simpl;
    first [right; intros H; apply H; split; reflexivity | left; intros [E1 E2]; discriminate].
Defined.

Lemma bm_comm : forall x y, bm x y = bm y x.
Proof. intros [a b] [c d]. unfold bm. simpl. rewrite (orb_comm a c), (orb_comm b d). reflexivity. Qed.

Lemma bm_assoc : forall x y z, bm (bm x y) z = bm x (bm y z).
Proof. intros [a b] [c d] [e f]. unfold bm. simpl. rewrite !orb_assoc. reflexivity. Qed.

Lemma b1_reach : forall s, ITR bm bT1 bI b0 s -> snd s = false.
Proof.
  intros s H. induction H as [| s t _ IH Ht _ | s1 s2 _ IH1 _ IH2 _].
  - reflexivity.
  - unfold bT1 in Ht. subst t. destruct s as [x y]. simpl in *. rewrite IH. reflexivity.
  - destruct s1 as [x1 y1], s2 as [x2 y2]. simpl in *. subst. reflexivity.
Qed.

Theorem b1_iconf : IConf bm bT1 bI b0.
Proof.
  intros s1 s2 H1 H2 [_ E]. destruct s1 as [x1 y1], s2 as [x2 y2].
  pose proof (b1_reach _ H1) as K1. pose proof (b1_reach _ H2) as K2. simpl in *. subst. discriminate.
Qed.

Theorem b2_not_iconf : ~ IConf bm bT2 bI b0.
Proof.
  intros H.
  assert (Ha : ITR bm bT2 bI b0 (ba b0))
    by (apply if_tx; [apply if_start | left; reflexivity | intros [_ E]; discriminate]).
  assert (Hb : ITR bm bT2 bI b0 (bbv b0))
    by (apply if_tx; [apply if_start | right; reflexivity | intros [E _]; discriminate]).
  apply (H _ _ Ha Hb). split; reflexivity.
Qed.

(* Non-vacuity of Part 4. With T = {add a}: Theorem 1 holds, and after server 0 adds a, servers
   0 and 1 exchange and agree on an I-valid state. With T = {add a, add b}: some execution leaves
   a server I-invalid. *)
Theorem replica_nonvacuous :
  (forall w, Forall (okE bT1) w -> forall r, bI (exec bm bI bI_dec b0 w r)) /\
  deliver bm (exec bm bI bI_dec b0 [Tx 0 ba] 0) [exec bm bI bI_dec b0 [Tx 0 ba] 1] = (true, false) /\
  deliver bm (exec bm bI bI_dec b0 [Tx 0 ba] 1) [exec bm bI bI_dec b0 [Tx 0 ba] 0] = (true, false) /\
  bI (true, false) /\
  ~ (forall w, Forall (okE bT2) w -> forall r, bI (exec bm bI bI_dec b0 w r)).
Proof.
  split; [apply (replica_exact bm bT1 bI bI_dec b0); [intros [E _]; discriminate | exact b1_iconf] |].
  split; [reflexivity | split; [reflexivity | split; [intros [_ E]; discriminate |]]].
  intros H. apply b2_not_iconf. apply (replica_necessity bm bT2 bI bI_dec b0). exact H.
Qed.

(* Repair: keep a, drop b when both are present. *)
Definition bN (x : bb) : bb := (fst x, snd x && negb (fst x)).
Definition bact (e : bb) (s : bb) : bb := bm s e.   (* transactions and deliveries are merges *)

Lemma bN_idem : forall x, bN (bN x) = bN x.
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bN_valid : forall x, bI (bN x).
Proof. intros [[|] [|]]; unfold bI; simpl; intros [E1 E2]; discriminate. Qed.

Theorem b_state_descent : NC.CanonicalExecution.StateDescent bN bact.
Proof. intros [[|] [|]] [[|] [|]]; reflexivity. Qed.

Lemma bN_merge : forall x y, bN (bm (bN x) (bN y)) = bN (bm x y).
Proof. intros [[|] [|]] [[|] [|]]; reflexivity. Qed.

Lemma b_raw_join : forall w x,
  NC.CanonicalExecution.rawrun bact w x = bm x (NC.CanonicalExecution.rawrun bact w b0).
Proof.
  intros w. induction w as [| e w IH]; intros x; [destruct x as [[|] [|]]; reflexivity |].
  unfold NC.CanonicalExecution.rawrun in *. simpl. rewrite (IH (bact e x)), (IH (bact e b0)).
  destruct x as [[|] [|]], e as [[|] [|]], (fold_left _ w b0) as [[|] [|]]; reflexivity.
Qed.

(* History descent: the repaired run is invariant under reordering (normalization_descent for
   state descent, perm_swap_recovered through deliver_perm for the raw order). *)
Theorem b_history_descent : forall s u u', Permutation u u' ->
  NC.CanonicalExecution.grun bN bact u (bN s) = NC.CanonicalExecution.grun bN bact u' (bN s).
Proof.
  intros s u u' P. rewrite <- !(NC.CanonicalExecution.normalization_descent bN bact b_state_descent).
  f_equal. exact (deliver_perm bm bm_comm bm_assoc s u u' P).
Qed.

(* Repair enlarges what converges coordination-free: T = {add a, add b} is not I-confluent, yet
   with repair every state is I-valid, the repaired run does not depend on the order, and two
   replicas that exchange repaired states agree with the repaired run of the joint history. *)
Theorem repair_enlarges :
  ~ IConf bm bT2 bI b0 /\
  NC.CanonicalExecution.StateDescent bN bact /\
  (forall s u u', Permutation u u' ->
     NC.CanonicalExecution.grun bN bact u (bN s) = NC.CanonicalExecution.grun bN bact u' (bN s)) /\
  (forall s w, bI (NC.CanonicalExecution.grun bN bact w (bN s))) /\
  (forall s w1 w2,
     bN (bm (NC.CanonicalExecution.grun bN bact w1 (bN s)) (NC.CanonicalExecution.grun bN bact w2 (bN s))) =
       NC.CanonicalExecution.grun bN bact (w1 ++ w2) (bN s) /\
     bN (bm (NC.CanonicalExecution.grun bN bact w1 (bN s)) (NC.CanonicalExecution.grun bN bact w2 (bN s))) =
       bN (bm (NC.CanonicalExecution.grun bN bact w2 (bN s)) (NC.CanonicalExecution.grun bN bact w1 (bN s)))).
Proof.
  split; [exact b2_not_iconf | split; [exact b_state_descent | split; [exact b_history_descent |]]].
  split.
  - intros s w. rewrite <- (NC.CanonicalExecution.normalization_descent bN bact b_state_descent). apply bN_valid.
  - intros s w1 w2. split; [| rewrite bm_comm; reflexivity].
    rewrite <- !(NC.CanonicalExecution.normalization_descent bN bact b_state_descent), bN_merge.
    f_equal.
    replace (NC.CanonicalExecution.rawrun bact (w1 ++ w2) s)
      with (NC.CanonicalExecution.rawrun bact w2 (NC.CanonicalExecution.rawrun bact w1 s))
      by (unfold NC.CanonicalExecution.rawrun; rewrite fold_left_app; reflexivity).
    rewrite (b_raw_join w2 (NC.CanonicalExecution.rawrun bact w1 s)).
    rewrite (b_raw_join w2 s), (b_raw_join w1 s).
    destruct s as [[|] [|]], (NC.CanonicalExecution.rawrun bact w1 b0) as [[|] [|]],
      (NC.CanonicalExecution.rawrun bact w2 b0) as [[|] [|]]; reflexivity.
Qed.
