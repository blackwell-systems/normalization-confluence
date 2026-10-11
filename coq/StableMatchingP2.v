(* StableMatchingP2.v: the test of prediction P2 (research/predictions/P2.md). Axiom-free.

   P2 claims: some marriage market with n <= 4 men and n women, complete strict preferences and
   exactly one stable matching mu*, has a start matching mu0 with BadLasso Stable mu0 for the
   blocking-pair dynamics, so fair settlement fails from mu0 (bad_lasso_refutes).

   The model, as committed in P2.md:
   - State: a matching (partial allowed), here a list of length n whose entry m is the wife of
     man m (None = single).
   - Labels: the n^2 pairs (m, w), label j = m * n + w (labels = seq 0 (n * n)).
   - Update upd j mu: if (m, w) blocks mu (each single or prefers the other to the current
     partner) then m and w marry and their former partners become single; otherwise mu.
   - Fair schedules: DistributedCycles.Fair, through the frozen kernel CanonicalRecurrence.
   - Stable: DistributedCycles.Stable (fixed by every label). stable_iff_no_blocking shows this is
     "no blocking pair", the usual stability.

   The instance (found by the search in research/predictions/p2/, 0-based names):
     men:   m0: w0 > w1 > w2    m1: w0 > w1 > w2    m2: w1 > w2 > w0
     women: w0: m2 > m0 > m1    w1: m1 > m2 > m0    w2: m2 > m0 > m1
   Its only stable matching is mu* = {m0-w0, m1-w1, m2-w2} (p2_unique_stable). From the empty
   matching, p = [(m0,w2); (m2,w0)] reaches x = {m0-w2, m2-w0}, and the loop word
     q = [(m0,w0); (m0,w2); (m1,w2); (m2,w1); (m0,w1); (m2,w2); (m1,w1); (m1,w0); (m2,w0)]
   names each of the 9 pairs exactly once and returns to x through the unstable matchings
     x -> {m0-w2, m2-w1} -> {m0-w2, m1-w1} -> {m0-w2, m1-w0} -> x.
   So even the periodic round-robin schedule p q q q ... cycles forever.

   Main results:
     stable_iff_no_blocking (generic n): Stable <-> no blocking pair, for states of length n.
     p2_wellformed:      the preferences are complete and strict.
     p2_unique_stable:   for every matching mu, Stable mu <-> mu = mu*.
     p2_bad_lasso:       BadLasso Stable from the empty matching.
     p2_refutes_settlement: ~ FairSettles and ~ FairSettlesNN (bad_lasso_refutes).
     p2_round_robin:     the loop word is a permutation of the 9 labels.
     p2_pass:            the committed claim, quantified: exists n <= 4 and preferences with a
                         unique stable matching and a bad fair lasso. *)

From Coq Require Import List Arith Lia Bool.
Require Import NC.DistributedCycles NC.CanonicalRecurrence.
Import ListNotations.

(* ============================================================================================ *)
(* Part 1. The blocking-pair dynamics of a marriage market (generic n).                         *)
(* ============================================================================================ *)

Section Market.
  Variable n : nat.
  Variable mp : list (list nat).   (* mp[m]: man m's list of women, best first *)
  Variable wp : list (list nat).   (* wp[w]: woman w's list of men, best first *)

  Fixpoint pos (x : nat) (l : list nat) : nat :=
    match l with [] => 0 | y :: l' => if x =? y then 0 else S (pos x l') end.
  Definition rm (m w : nat) : nat := pos w (nth m mp []).
  Definition rw (w m : nat) : nat := pos m (nth w wp []).

  Definition State := list (option nat).
  Definition wife (mu : State) (m : nat) : option nat := nth m mu None.
  Definition is_wife (mu : State) (m w : nat) : bool :=
    match wife mu m with Some w' => w' =? w | None => false end.
  Definition husb (mu : State) (w : nat) : option nat := find (fun m => is_wife mu m w) (seq 0 n).

  Definition better_m (m w : nat) (c : option nat) : bool :=
    match c with None => true | Some w' => rm m w <? rm m w' end.
  Definition better_w (w m : nat) (c : option nat) : bool :=
    match c with None => true | Some m' => rw w m <? rw w m' end.
  (* (m, w) blocks mu: not married to each other, each single or preferring the other. *)
  Definition blocks (mu : State) (m w : nat) : bool :=
    negb (is_wife mu m w) && better_m m w (wife mu m) && better_w w m (husb mu w).
  (* m marries w; w's former husband becomes single; m's former wife is left single. *)
  Definition marry (mu : State) (m w : nat) : State :=
    map (fun k => if k =? m then Some w else if is_wife mu k w then None else wife mu k) (seq 0 n).
  Definition upd (j : nat) (mu : State) : State :=
    if blocks mu (j / n) (j mod n) then marry mu (j / n) (j mod n) else mu.
  Definition labels : list nat := seq 0 (n * n).

  Definition SM : State -> Prop := Stable State upd labels.
  Definition IsMatching (mu : State) : Prop :=
    length mu = n /\ (forall m w, wife mu m = Some w -> w < n) /\
    (forall m m' w, wife mu m = Some w -> wife mu m' = Some w -> m = m').
  Definition WellFormed : Prop :=
    length mp = n /\ length wp = n /\
    (forall l, In l mp \/ In l wp -> length l = n /\ NoDup l /\ forall x, In x l -> x < n).

  Lemma marry_wife : forall mu m w, m < n -> wife (marry mu m w) m = Some w.
  Proof.
    intros mu m w Hm.
    assert (G : forall (f : nat -> option nat) k, k < n -> nth k (map f (seq 0 n)) None = f k).
    { intros f k Hk. rewrite nth_indep with (d' := f 0) by (rewrite map_length, seq_length; exact Hk).
      rewrite map_nth, seq_nth by exact Hk. reflexivity. }
    unfold wife at 1, marry. rewrite G by exact Hm. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Lemma label_pair : forall m w, m < n -> w < n ->
    In (m * n + w) labels /\ (m * n + w) / n = m /\ (m * n + w) mod n = w.
  Proof.
    intros m w Hm Hw. assert (Hn : n <> 0) by lia. split; [| split].
    - unfold labels. apply in_seq. split; [lia |]. simpl. nia.
    - rewrite Nat.div_add_l by exact Hn. rewrite Nat.div_small by exact Hw. lia.
    - rewrite Nat.add_comm, Nat.mod_add by exact Hn. apply Nat.mod_small. exact Hw.
  Qed.

  Lemma label_bounds : forall j, In j labels -> j / n < n /\ j mod n < n.
  Proof.
    intros j Hj. unfold labels in Hj. apply in_seq in Hj. assert (Hn : n <> 0) by (intro; subst; lia).
    split; [apply Nat.div_lt_upper_bound; lia | apply Nat.mod_upper_bound; exact Hn].
  Qed.

  (* Stable (fixed by every label) is exactly "no blocking pair". *)
  Theorem stable_iff_no_blocking : forall mu,
    SM mu <-> forall m w, m < n -> w < n -> blocks mu m w = false.
  Proof.
    intros mu. split.
    - intros H m w Hm Hw. destruct (label_pair m w Hm Hw) as [Hin [Ed Em]].
      specialize (H _ Hin). unfold upd in H. rewrite Ed, Em in H.
      destruct (blocks mu m w) eqn:B; [| reflexivity].
      assert (E : wife mu m = Some w) by (rewrite <- H; apply marry_wife; exact Hm).
      unfold blocks, is_wife in B. rewrite E, Nat.eqb_refl in B. discriminate.
    - intros H j Hj. destruct (label_bounds j Hj) as [Hm Hw]. unfold upd. rewrite (H _ _ Hm Hw).
      reflexivity.
  Qed.

  Definition stableb (mu : State) : bool :=
    forallb (fun m => forallb (fun w => negb (blocks mu m w)) (seq 0 n)) (seq 0 n).

  Lemma stableb_spec : forall mu, SM mu <-> stableb mu = true.
  Proof.
    intros mu. rewrite stable_iff_no_blocking. unfold stableb. rewrite forallb_forall. split.
    - intros H m Hm. apply forallb_forall. intros w Hw. apply in_seq in Hm, Hw.
      rewrite (H m w ltac:(lia) ltac:(lia)). reflexivity.
    - intros H m w Hm Hw. assert (Hm' : In m (seq 0 n)) by (apply in_seq; lia).
      assert (Hw' : In w (seq 0 n)) by (apply in_seq; lia).
      specialize (H m Hm'). rewrite forallb_forall in H. specialize (H w Hw').
      destruct (blocks mu m w); [discriminate | reflexivity].
  Qed.
End Market.

(* ============================================================================================ *)
(* Part 2. The instance: three men, three women, one stable matching, a fair cycle.             *)
(* ============================================================================================ *)

Definition p2n : nat := 3.
Definition p2men : list (list nat) := [[0; 1; 2]; [0; 1; 2]; [1; 2; 0]].
Definition p2women : list (list nat) := [[2; 0; 1]; [1; 2; 0]; [2; 0; 1]].

Definition p2upd : nat -> State -> State := upd p2n p2men p2women.
Definition p2labels : list nat := labels p2n.
Definition p2SM : State -> Prop := SM p2n p2men p2women.

Definition mu_star : State := [Some 0; Some 1; Some 2].
Definition mu_empty : State := [None; None; None].
Definition x_loop : State := [Some 2; None; Some 0].
Definition p_word : list nat := [2; 6].
Definition q_word : list nat := [0; 2; 5; 7; 1; 8; 4; 3; 6].

Theorem p2_wellformed : WellFormed p2n p2men p2women.
Proof.
  split; [reflexivity | split; [reflexivity |]].
  intros l [H | H]; simpl in H;
    repeat (destruct H as [<- | H]; [split; [reflexivity | split;
      [repeat constructor; simpl; intuition discriminate | intros x Hx; simpl in Hx; unfold p2n; lia]] |]);
    destruct H.
Qed.

Lemma p2_mu_star_matching : IsMatching p2n mu_star.
Proof.
  split; [reflexivity | split].
  - intros m w H. unfold wife, mu_star in H.
    destruct m as [| [| [| m]]]; simpl in H; [injection H as <- .. | destruct m; discriminate];
      unfold p2n; lia.
  - intros m m' w H H'. unfold wife, mu_star in H, H'.
    destruct m as [| [| [| m]]]; destruct m' as [| [| [| m']]]; simpl in H, H';
      try (destruct m; discriminate); try (destruct m'; discriminate); congruence.
Qed.

(* Uniqueness of the stable matching, by computation over the 4^3 candidate lists. The two
   non-injective lists [w0; w0; w1] and [w0; w1; w1] pass the boolean check and are excluded by
   injectivity. *)
Theorem p2_unique_stable : forall mu, IsMatching p2n mu -> (p2SM mu <-> mu = mu_star).
Proof.
  intros mu [Hl [Hr Hi]]. unfold p2SM. rewrite stableb_spec.
  destruct mu as [| a [| b [| c [| d t]]]]; simpl in Hl; try discriminate.
  assert (Ha : forall k, a = Some k -> k < 3) by (intros k E; subst; exact (Hr 0 k eq_refl)).
  assert (Hb : forall k, b = Some k -> k < 3) by (intros k E; subst; exact (Hr 1 k eq_refl)).
  assert (Hc : forall k, c = Some k -> k < 3) by (intros k E; subst; exact (Hr 2 k eq_refl)).
  destruct a as [[| [| [| a]]] |]; [| | | specialize (Ha _ eq_refl); lia |];
  destruct b as [[| [| [| b]]] |]; try (specialize (Hb _ eq_refl); lia);
  destruct c as [[| [| [| c]]] |]; try (specialize (Hc _ eq_refl); lia);
  first
    [ vm_compute; split; intro H; (reflexivity || discriminate)
    | exfalso; solve [ discriminate (Hi 0 1 _ eq_refl eq_refl) | discriminate (Hi 0 2 _ eq_refl eq_refl)
                     | discriminate (Hi 1 2 _ eq_refl eq_refl) ] ].
Qed.

Theorem p2_mu_star_stable : p2SM mu_star.
Proof. apply p2_unique_stable; [exact p2_mu_star_matching | reflexivity]. Qed.

(* ============================================================================================ *)
(* Part 3. The bad fair lasso and the refutation of fair settlement.                            *)
(* ============================================================================================ *)

Lemma p2_not_stable : forall mu, stableb p2n p2men p2women mu = false -> ~ p2SM mu.
Proof. intros mu E H. unfold p2SM in H. rewrite stableb_spec, E in H. discriminate. Qed.

(* Every state on the loop is unstable. *)
Theorem p2_loop_unstable : forall k, k < length q_word -> ~ p2SM (wrun State p2upd (firstn k q_word) x_loop).
Proof.
  intros k Hk. apply p2_not_stable.
  do 9 (destruct k as [| k]; [vm_compute; reflexivity |]). simpl in Hk. lia.
Qed.

Lemma p2_all_labels : forall j, In j p2labels -> In j q_word.
Proof.
  intros j Hj. unfold p2labels, labels, p2n in Hj. apply in_seq in Hj.
  do 9 (destruct j as [| j]; [simpl; tauto |]). lia.
Qed.

Lemma p2_path : forall w, Forall (fun j => j < 9) w -> Path p2labels w.
Proof.
  intros w H. unfold Path. eapply Forall_impl; [| exact H]. intros j Hj. simpl in Hj.
  unfold p2labels, labels, p2n. apply in_seq. lia.
Qed.

Theorem p2_bad_lasso : BadLasso State p2labels p2upd p2SM mu_empty.
Proof.
  exists x_loop, p_word, q_word, x_loop. split; [split; [| split; [| split; [| split; [| split]]]] | split].
  - apply p2_path. repeat constructor.
  - vm_compute. reflexivity.
  - discriminate.
  - apply p2_path. repeat constructor.
  - vm_compute. reflexivity.
  - exact p2_all_labels.
  - exists 0. split; [simpl; lia | reflexivity].
  - exact (p2_loop_unstable 0 ltac:(simpl; lia)).
Qed.

(* Through the frozen kernel: some fair schedule from the empty matching is unstable infinitely
   often, so fair settlement fails, in the strong and in the double-negation form. *)
Theorem p2_refutes_settlement :
  ~ FairSettles State p2labels p2upd p2SM mu_empty /\ ~ FairSettlesNN State p2labels p2upd p2SM mu_empty.
Proof. exact (bad_lasso_refutes State p2labels p2upd p2SM mu_empty p2_bad_lasso). Qed.

(* The loop word names each of the 9 pairs exactly once: a round-robin schedule. *)
Theorem p2_round_robin :
  NoDup q_word /\ length q_word = length p2labels /\ (forall j, In j p2labels <-> In j q_word).
Proof.
  split; [repeat constructor; simpl; intuition discriminate | split; [reflexivity |]].
  intro j. split; [apply p2_all_labels |]. intro H. unfold p2labels, labels, p2n. apply in_seq.
  simpl in H. intuition lia.
Qed.

(* The empty matching and x_loop are matchings (non-vacuity of the start and the loop). *)
Lemma p2_start_matching : IsMatching p2n mu_empty.
Proof.
  split; [reflexivity | split].
  - intros m w H. unfold wife, mu_empty in H. destruct m as [| [| [| m]]]; simpl in H;
      try discriminate; destruct m; discriminate.
  - intros m m' w H. unfold wife, mu_empty in H. destruct m as [| [| [| m]]]; simpl in H;
      try discriminate; destruct m; discriminate.
Qed.

(* ============================================================================================ *)
(* Part 4. The committed claim of P2.                                                            *)
(* ============================================================================================ *)

Theorem p2_pass : exists n mp wp,
  n <= 4 /\ WellFormed n mp wp /\
  (exists mu_s, IsMatching n mu_s /\ forall mu, IsMatching n mu -> (SM n mp wp mu <-> mu = mu_s)) /\
  (exists mu0, IsMatching n mu0 /\ BadLasso State (labels n) (upd n mp wp) (SM n mp wp) mu0 /\
     ~ FairSettles State (labels n) (upd n mp wp) (SM n mp wp) mu0).
Proof.
  exists p2n, p2men, p2women. split; [unfold p2n; lia | split; [exact p2_wellformed | split]].
  - exists mu_star. split; [exact p2_mu_star_matching | exact p2_unique_stable].
  - exists mu_empty. split; [exact p2_start_matching | split; [exact p2_bad_lasso |]].
    exact (proj1 p2_refutes_settlement).
Qed.
