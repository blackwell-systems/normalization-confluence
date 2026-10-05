(* LocalSigned.v: local (state-dependent) interaction graphs of Boolean resolver networks, and
   what they give for E (Settlement and CanonicalFidelity of CanonicalExecution.v). Axiom-free.

   Setting. The resolver model of SignedResolver.v with the value set bool: a state s : Sh
   exposes the value of vertex j through a lens (get j, set j) on the vertex list js, with
   extensionality on js; vertex v has a resolver Fv v : Sh -> bool; the asynchronous step
   rupd j replaces the value of j by Fv j of the current state; Fsync updates every vertex.
   flip j x is x with the value of j negated.

   Local interaction graph G(x) (Remy, Ruet and Thieffry 2008, the discrete Jacobian).
     larc x j i = true   iff  Fv i (flip j x) <> Fv i x  (an arc j -> i at x);
     lneg x j i          the sign of that arc, true for negative: xorb (Fv i x) (get j x).
   lneg_spec: for an arc j -> i at x, Fv i (set j false x) = lneg x j i and
   Fv i (set j true x) = negb (lneg x j i); so the arc is positive iff raising x_j from false to
   true (other coordinates as in x) raises Fv i, and negative iff it lowers it.
   A cycle is a nonempty list c of DISTINCT vertices (an elementary circuit) with an arc from each
   vertex to the next and from the last to the first (IsCycle, cpairs); its sign is the xor of
   its arc signs (csign). NoLocalPos I, NoLocalNeg I, NoLocalCycle I: for every state x, G(x)
   restricted to the vertices of I has no positive cycle, no negative cycle, no cycle at all.
   The global certificate of SignedResolver.v is a list sg of signed edges with Resp (signs fixed
   across all states); SgCycle sg c b is an elementary cycle of sg with sign b.

   Results (local fidelity).
     rrt_sub, local_fidelity
                         (Remy, Ruet and Thieffry 2008: if G(x) has no positive cycle for
                         every x, then F has at most one fixed point; mechanized here for every
                         n, with a proof by induction on subcubes): NoLocalPos js implies that Fsync has at most one fixed point.
                         The key facts: every cycle of G(x) at a fixed point x is positive
                         (fixed_csign), so G(x) is acyclic there and has a sink k
                         (cycle_or_sink); flipping k gives a fixed point of the subcube with k
                         frozen at the other value.
     local_fidelity_canon
                         with NoLocalPos js and a fixed point q: CanonicalFidelity with the
                         constant canonicalizer q from every start (every settled reachable
                         configuration is q). No global sign hypothesis.
     local_signed_fidelity
                         the lift through SignedResolver.signed_fidelity: Resp, SgOn and a
                         switching of the global certificate, plus NoLocalPos js (in place of
                         uniqueness, which is now derived): every fair schedule from every start
                         settles at the unique fixed point, and E holds from every start.
     local_in_global, local_cycle_global, global_to_local
                         under Resp, every arc of G(x) is an edge of sg with the same sign, so a
                         local cycle is a cycle of sg with the same sign; "no positive cycle in
                         the global certificate" implies NoLocalPos js (non-vacuity:
                         global_to_local_instance, the unbalanced negative 2-cycle).
     local_weaker_than_global
                         the converse fails: x0 := x1 && x2, x1 := x0 || x2, x2 := false. No
                         G(x) has any cycle, but EVERY global certificate contains the positive
                         2-cycle 0 -> 1 -> 0; the fixed point is unique, every fair schedule
                         from every start settles at it, and E holds from every start
                         (via local_signed_fidelity). The global sign route cannot see this
                         network (compare SignedResolver.unique_pos_cycle_every_certificate).
   Results (local settlement).
     local_neg_free_no_fixed_point
                         the local form of Thomas's second rule is false: a 6-vertex Boolean
                         network (Tonello 2017, the Boolean conversion of Richard 2010's
                         Example 6) whose local graphs have no negative cycle, with no fixed
                         point, so no run ever settles and E's Settlement fails from every
                         start. Six vertices is the least possible (Tonello, Farcot and Chaouiya
                         2018, cited: for n <= 5 a cyclic attractor forces a local negative
                         cycle).
     t3_path, richard_t3 (Richard 2011, Theorem 3, mechanized for every n, following Richard's
                         proof: Claims 1 to 4 are claim1, claim2, partners, claim3, four_point and
                         opp_core; opp_false is his Lemma 2): NoDup js, NoLocalNeg js and
                         OutDeg1 js (every vertex of every G(x) has out-degree at most one, which
                         is non-expansiveness for the Hamming distance: outdeg_nonexpansive)
                         imply that from every state some update word over js reaches a fixed
                         point; hence a fixed point exists and E's Settlement holds from every
                         start (the reachability form is Ruet 2017, Remark 2, and Richard 2015,
                         Remark 4: no cyclic attractor).
     t4_full, richard_t4 (Richard 2011, Theorem 4, with the same reachability strengthening):
                         NoLocalNeg js and one vertex k on every positive cycle of every G(x)
                         imply that from every state some update word over js reaches a fixed
                         point; hence a fixed point exists and E's Settlement holds from every
                         start. Proved from rrt_sub applied to the network with Fv k negated.
     sd_path, shih_dong_E (Shih and Dong 2005, with the reachability strengthening of Richard):
                         NoLocalCycle js implies a unique fixed point q, reachable from every
                         state by an update word, and E with the constant canonicalizer q from
                         every start. No global sign hypothesis.
     shih_dong_not_fair  fair asynchronous settlement does NOT follow, even from the strongest
                         local condition: x0 := not x1 && not x2, x1 := x0 || not x2 || x3,
                         x2 := x0 && x1 && x3, x3 := not x0 has no cycle in any G(x) (so E holds
                         from every start, shih_dong_E), but the fair periodic schedule
                         2, 3, 0, 1, 3, 2, 0, 1, ... from (1, 1, 0, 1) never settles. Contrast
                         with Robert's theorem (an acyclic GLOBAL graph makes every fair
                         asynchronous run converge).
     ring_local_conditions
                         the positive 3-ring x0 := x1, x1 := x2, x2 := x0 satisfies NoLocalNeg,
                         OutDeg1 (so richard_t3 applies and gives E's Settlement from every start)
                         and "vertex 0 on every local positive cycle" (Theorem 4); it has two fixed
                         points, from (1, 0, 0) a fair schedule that never settles, and a run
                         that settles away from the least fixed point (SignedResolver
                         ring_needs_low_start, ring_low_start_E): under either corrected local
                         condition only E's Settlement half follows, not fair settlement and not
                         fidelity.
   Cited, not mechanized: Richard and Comet 2007 (the multivalued local positive-cycle theorem),
   Richard 2010, Example 6 (the multivalued 2-component counterexample that tn_F converts),
   Ruet 2017, Theorem A (a 12-component and-net counterexample), and Tonello, Farcot and
   Chaouiya 2018 (no Boolean counterexample with at most 5 components).
   Decision procedure for the instances: chk enumerates every state and every list of distinct
   vertices (nl_complete) and is proved sound (chk_sound). *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.CohomologyGraph NC.SignedCycles NC.DistributedCycles NC.CanonicalExecution
  NC.SignedResolver.
Import ListNotations.

(* ============================================================================================ *)
(* Part 0. Elementary cycles of a vertex list, their signs, and finite enumeration.             *)
(* ============================================================================================ *)

(* The arcs of the cycle c = [c0; ...; c(p-1)]: (c(p-1), c0), (c0, c1), ..., (c(p-2), c(p-1)). *)
Fixpoint cpf (a : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | b :: r => (a, b) :: cpf b r end.

Definition cpairs (c : list nat) : list (nat * nat) :=
  match c with [] => [] | a :: _ => cpf (last c a) c end.

Definition cyc_ok (ar : nat -> nat -> bool) (c : list nat) : bool :=
  forallb (fun p => ar (fst p) (snd p)) (cpairs c).

Definition csign (sn : nat -> nat -> bool) (c : list nat) : bool :=
  fold_right (fun p h => xorb (sn (fst p) (snd p)) h) false (cpairs c).

Definition IsCycle (ar : nat -> nat -> bool) (c : list nat) : Prop :=
  c <> [] /\ NoDup c /\ cyc_ok ar c = true.

Lemma last_indep : forall (l : list nat) a b, l <> [] -> last l a = last l b.
Proof.
  induction l as [| x l IH]; intros a b H; [congruence |].
  destruct l as [| y l]; [reflexivity |]. simpl. apply IH. discriminate.
Qed.

Lemma last_cons_ne : forall (l : list nat) a d, l <> [] -> last (a :: l) d = last l d.
Proof. intros l a d H. destruct l as [| c l]; [congruence | reflexivity]. Qed.

Lemma last_cons2 : forall (l : list nat) a b, last (b :: l) a = last l b.
Proof.
  intros l a b. destruct l as [| c l]; [reflexivity |].
  rewrite last_cons_ne by discriminate. apply last_indep. discriminate.
Qed.

Lemma last_app_cons : forall (p1 p2 : list nat) v d, last (p1 ++ v :: p2) d = last (v :: p2) d.
Proof.
  induction p1 as [| a p1 IH]; intros p2 v d; [reflexivity |].
  simpl (( a :: p1) ++ v :: p2). rewrite last_cons_ne; [apply IH |].
  destruct p1; discriminate.
Qed.

Lemma last_in : forall (l : list nat) d, l <> [] -> In (last l d) l.
Proof.
  induction l as [| a l IH]; intros d H; [congruence |].
  destruct l as [| b l]; [left; reflexivity |]. right. rewrite last_cons_ne by discriminate.
  apply IH. discriminate.
Qed.

Lemma in_cpf : forall l a p, In p (cpf a l) -> In (fst p) (a :: l) /\ In (snd p) l.
Proof.
  induction l as [| b l IH]; intros a p H; [destruct H |].
  destruct H as [<- | H]; [simpl; tauto |].
  destruct (IH b p H) as [H1 H2]. split; right; assumption.
Qed.

Lemma in_cpairs : forall c p, In p (cpairs c) -> In (fst p) c /\ In (snd p) c.
Proof.
  intros [| a l] p H; [destruct H |]. unfold cpairs in H.
  destruct (in_cpf (a :: l) _ p H) as [H1 H2]. split; [| exact H2].
  destruct H1 as [E | H1]; [rewrite <- E; apply last_in; discriminate | exact H1].
Qed.

Lemma csign_ext : forall s1 s2 c, (forall u v, In v c -> s1 u v = s2 u v) -> csign s1 c = csign s2 c.
Proof.
  intros s1 s2 c H. unfold csign.
  assert (G : forall ps, (forall p, In p ps -> In (snd p) c) ->
            fold_right (fun p h => xorb (s1 (fst p) (snd p)) h) false ps =
            fold_right (fun p h => xorb (s2 (fst p) (snd p)) h) false ps).
  { induction ps as [| p ps IH]; intros Hp; [reflexivity |]. cbn [fold_right].
    rewrite (H (fst p) (snd p) (Hp p (or_introl eq_refl))).
    rewrite IH; [reflexivity |]. intros q Hq. apply Hp. right. exact Hq. }
  apply G. intros p Hp. exact (proj2 (in_cpairs c p Hp)).
Qed.

Lemma cyc_ok_ext : forall a1 a2 c, (forall u v, a1 u v = a2 u v) -> cyc_ok a1 c = cyc_ok a2 c.
Proof.
  intros a1 a2 c H. unfold cyc_ok. induction (cpairs c) as [| p ps IH]; [reflexivity |].
  simpl. rewrite H, IH. reflexivity.
Qed.

(* Telescoping: a sign of the form xorb (e u) (e v) sums to false around every cycle. *)
Lemma cpf_tele : forall (sn : nat -> nat -> bool) (e : nat -> bool),
  (forall u v, sn u v = xorb (e u) (e v)) -> forall l a,
  fold_right (fun p h => xorb (sn (fst p) (snd p)) h) false (cpf a l) = xorb (e a) (e (last l a)).
Proof.
  intros sn e Hs. induction l as [| b l IH]; intros a.
  - simpl. destruct (e a); reflexivity.
  - cbn [cpf fold_right fst snd]. rewrite IH, Hs, last_cons2.
    destruct (e a), (e b), (e (last l b)); reflexivity.
Qed.

Lemma csign_tele : forall (e : nat -> bool) c, csign (fun u v => xorb (e u) (e v)) c = false.
Proof.
  intros e [| a l]; [reflexivity |]. unfold csign, cpairs.
  rewrite (cpf_tele (fun u v => xorb (e u) (e v)) e (fun u v => eq_refl)).
  rewrite (last_indep (a :: l) (last (a :: l) a) a) by discriminate.
  destruct (e (last (a :: l) a)); reflexivity.
Qed.

Lemma csign_xor : forall s1 s2 c,
  csign (fun u v => xorb (s1 u v) (s2 u v)) c = xorb (csign s1 c) (csign s2 c).
Proof.
  intros s1 s2 c. unfold csign. induction (cpairs c) as [| p ps IH]; [reflexivity |].
  cbn [fold_right]. rewrite IH.
  generalize (s1 (fst p) (snd p)) (s2 (fst p) (snd p))
    (fold_right (fun p h => xorb (s1 (fst p) (snd p)) h) false ps)
    (fold_right (fun p h => xorb (s2 (fst p) (snd p)) h) false ps).
  intros [] [] [] []; reflexivity.
Qed.

Lemma csign_target : forall (g : nat -> bool) c,
  csign (fun _ v => g v) c = fold_right (fun i h => xorb (g i) h) false c.
Proof.
  intros g [| a l]; [reflexivity |]. unfold csign, cpairs. generalize (last (a :: l) a). intros d.
  generalize (a :: l). intros m. revert d. induction m as [| b m IH]; intros d; [reflexivity |].
  cbn [cpf fold_right snd]. rewrite IH. reflexivity.
Qed.

Lemma parity_in : forall k l, NoDup l ->
  (fold_right (fun i h => xorb (Nat.eqb i k) h) false l = true <-> In k l).
Proof.
  intros k. induction l as [| b l IH]; intros Hn; [simpl; split; [discriminate | intros []] |].
  inversion Hn as [| ? ? Hb Hl]; subst. cbn [fold_right]. specialize (IH Hl).
  destruct (Nat.eqb_spec b k) as [<- | N].
  - simpl. split; [intros _; left; reflexivity | intros _].
    destruct (fold_right (fun i h => xorb (Nat.eqb i b) h) false l) eqn:E; [| reflexivity].
    exfalso. apply Hb. apply IH. reflexivity.
  - simpl. rewrite IH. split; [intros H; right; exact H | intros [E | H]; [contradiction | exact H]].
Qed.

(* ----- cycles or sinks ----- *)

Fixpoint pathOK (ar : nat -> nat -> bool) (p : list nat) : bool :=
  match p with
  | a :: ((b :: _) as r) => ar a b && pathOK ar r
  | _ => true
  end.

Lemma forallb_cpf : forall ar l a,
  forallb (fun p => ar (fst p) (snd p)) (cpf a l) = pathOK ar (a :: l).
Proof.
  intros ar. induction l as [| b l IH]; intros a; [reflexivity |].
  cbn [cpf forallb fst snd]. rewrite IH. reflexivity.
Qed.

Lemma pathOK_tail : forall ar a r, pathOK ar (a :: r) = true -> pathOK ar r = true.
Proof. intros ar a [| b r] H; [reflexivity |]. simpl in H. apply andb_prop in H. tauto. Qed.

Lemma pathOK_suffix : forall ar p1 p2, pathOK ar (p1 ++ p2) = true -> pathOK ar p2 = true.
Proof.
  intros ar. induction p1 as [| a p1 IH]; intros p2 H; [exact H |].
  apply IH. exact (pathOK_tail ar a _ H).
Qed.

Lemma pathOK_snoc : forall ar p a v,
  pathOK ar ((a :: p) ++ [v]) = pathOK ar (a :: p) && ar (last (a :: p) 0) v.
Proof.
  intros ar. induction p as [| b p IH]; intros a v.
  - simpl. destruct (ar a v); reflexivity.
  - change ((a :: b :: p) ++ [v]) with (a :: ((b :: p) ++ [v])).
    change (pathOK ar (a :: (b :: p) ++ [v])) with (ar a b && pathOK ar ((b :: p) ++ [v])).
    rewrite IH. change (pathOK ar (a :: b :: p)) with (ar a b && pathOK ar (b :: p)).
    rewrite (last_cons_ne (b :: p) a 0) by discriminate. apply andb_assoc.
Qed.

Lemma nodup_app_r : forall (l1 l2 : list nat), NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1 as [| a l1 IH]; intros l2 H; [exact H |]. inversion H; subst. apply IH. assumption. Qed.

Lemma nodup_snoc : forall (l : list nat) v, NoDup l -> ~ In v l -> NoDup (l ++ [v]).
Proof.
  induction l as [| a l IH]; intros v Hn Hv; [constructor; [intros [] | constructor] |].
  inversion Hn; subst. simpl. constructor.
  - intro H. apply in_app_or in H. destruct H as [H | [E | []]]; [contradiction |].
    apply Hv. left. symmetry. exact E.
  - apply IH; [assumption |]. intro H. apply Hv. right. exact H.
Qed.

Lemma len_snoc : forall (l : list nat) v, length (l ++ [v]) = S (length l).
Proof. induction l as [| a l IH]; intros v; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Lemma walk_cycle : forall ar I, (forall k, In k I -> exists i, In i I /\ ar k i = true) ->
  forall n a p, NoDup (a :: p) -> incl (a :: p) I -> pathOK ar (a :: p) = true ->
  length I < length (a :: p) + n -> exists c, incl c I /\ IsCycle ar c.
Proof.
  intros ar I Hs. induction n as [| n IH]; intros a p Hn Hi Hp Hl.
  - pose proof (NoDup_incl_length Hn Hi). lia.
  - set (cur := last (a :: p) 0).
    assert (Hc : In cur (a :: p)) by (apply last_in; discriminate).
    destruct (Hs cur (Hi cur Hc)) as [v [Hv Ha]].
    destruct (in_dec Nat.eq_dec v (a :: p)) as [Hin | Hout].
    + destruct (in_split v (a :: p) Hin) as [p1 [p2 E]].
      exists (v :: p2). split; [| split; [discriminate | split]].
      * intros u Hu. apply Hi. rewrite E. apply in_or_app. right. exact Hu.
      * rewrite E in Hn. exact (nodup_app_r p1 _ Hn).
      * unfold cyc_ok, cpairs. cbn [cpf forallb fst snd]. rewrite forallb_cpf.
        assert (Lc : last (v :: p2) v = cur).
        { unfold cur. rewrite E, last_app_cons. apply last_indep. discriminate. }
        rewrite Lc, Ha. simpl. rewrite E in Hp. exact (pathOK_suffix ar p1 (v :: p2) Hp).
    + apply (IH a (p ++ [v])).
      * exact (nodup_snoc (a :: p) v Hn Hout).
      * intros u Hu. change (a :: p ++ [v]) with ((a :: p) ++ [v]) in Hu.
        apply in_app_or in Hu. destruct Hu as [Hu | [<- | []]]; [apply Hi; exact Hu | exact Hv].
      * change (a :: p ++ [v]) with ((a :: p) ++ [v]). rewrite pathOK_snoc, Hp. exact Ha.
      * change (a :: p ++ [v]) with ((a :: p) ++ [v]). rewrite len_snoc. simpl in Hl |- *. lia.
Qed.

Lemma forallb_false_ex : forall (f : nat -> bool) l, forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros f. induction l as [| a l IH]; intros H; [discriminate |]. simpl in H.
  destruct (f a) eqn:Fa; [simpl in H; destruct (IH H) as [x [Hx Fx]]; exists x; split; [right |]; assumption |].
  exists a. split; [left; reflexivity | exact Fa].
Qed.

(* A finite digraph on I either contains an elementary cycle or has a vertex with no out-arc
   into I. *)
Lemma cycle_or_sink : forall ar I, I <> [] ->
  (exists c, incl c I /\ IsCycle ar c) \/ (exists k, In k I /\ forall i, In i I -> ar k i = false).
Proof.
  intros ar I HI. destruct (forallb (fun k => existsb (ar k) I) I) eqn:E.
  - left. destruct I as [| a I']; [congruence |].
    apply (walk_cycle ar (a :: I')) with (n := length (a :: I')) (a := a) (p := []).
    + intros k Hk. rewrite forallb_forall in E. apply existsb_exists. exact (E k Hk).
    + constructor; [intros [] | constructor].
    + intros u [<- | []]. left. reflexivity.
    + reflexivity.
    + simpl. lia.
  - right. destruct (forallb_false_ex _ I E) as [k [Hk Ek]]. exists k. split; [exact Hk |].
    intros i Hi. destruct (ar k i) eqn:A; [| reflexivity]. exfalso.
    assert (existsb (ar k) I = true) by (apply existsb_exists; exists i; split; assumption). congruence.
Qed.

(* ----- removing a vertex, and enumerating lists of distinct vertices ----- *)

Definition rm (k : nat) (l : list nat) : list nat := filter (fun j => negb (Nat.eqb j k)) l.

Lemma rm_In : forall k l j, In j (rm k l) <-> In j l /\ j <> k.
Proof.
  intros k l j. unfold rm. rewrite filter_In.
  destruct (Nat.eqb_spec j k) as [E | N]; simpl; split; intros [H1 H2].
  - discriminate.
  - contradiction.
  - split; [exact H1 | exact N].
  - split; [exact H1 | reflexivity].
Qed.

Lemma rm_length_le : forall k l, length (rm k l) <= length l.
Proof.
  intros k. induction l as [| a l IH]; [reflexivity |]. unfold rm in *. simpl.
  destruct (negb (Nat.eqb a k)); simpl; lia.
Qed.

Lemma rm_length : forall k l, In k l -> length (rm k l) < length l.
Proof.
  intros k. induction l as [| a l IH]; intros H; [destruct H |]. unfold rm in *. simpl.
  destruct (Nat.eqb_spec a k) as [-> | N]; simpl.
  - pose proof (rm_length_le k l). unfold rm in H0. lia.
  - destruct H as [E | H]; [congruence |]. specialize (IH H). lia.
Qed.

Fixpoint nl (n : nat) (l : list nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S m => [] :: flat_map (fun a => map (cons a) (nl m (rm a l))) l
  end.

Lemma nl_complete : forall n l c, NoDup c -> incl c l -> length c <= n -> In c (nl n l).
Proof.
  induction n as [| m IH]; intros l c Hn Hi Hl.
  - destruct c; [left; reflexivity | simpl in Hl; lia].
  - destruct c as [| a c]; [left; reflexivity |]. right. apply in_flat_map. exists a.
    split; [apply Hi; left; reflexivity |]. apply in_map. inversion Hn; subst. apply IH.
    + assumption.
    + intros b Hb. apply rm_In. split; [apply Hi; right; exact Hb |]. intro E. subst b. contradiction.
    + simpl in Hl. lia.
Qed.

(* Elementary cycles of a global signed edge list, with their sign. *)
Inductive SgPath (sg : list (@edge bool)) : list (nat * nat) -> bool -> Prop :=
  | sgp_nil : SgPath sg [] false
  | sgp_cons : forall u v b ps h, In (u, v, b) sg -> SgPath sg ps h -> SgPath sg ((u, v) :: ps) (xorb b h).

Definition SgCycle (sg : list (@edge bool)) (c : list nat) (h : bool) : Prop :=
  c <> [] /\ NoDup c /\ SgPath sg (cpairs c) h.

(* ============================================================================================ *)
(* Part 1. Local interaction graphs of Boolean resolver networks.                               *)
(* ============================================================================================ *)

Section Lens.
  Variable Sh : Type.
  Variable js : list nat.
  Variable get : nat -> Sh -> bool.
  Variable set : nat -> bool -> Sh -> Sh.
  Hypothesis get_set_eq : forall j x s, In j js -> get j (set j x s) = x.
  Hypothesis get_set_neq : forall j k x s, k <> j -> get k (set j x s) = get k s.
  Hypothesis sh_ext : forall s t, (forall j, In j js -> get j s = get j t) -> s = t.

  Definition flip (j : nat) (x : Sh) : Sh := set j (negb (get j x)) x.

  Lemma set_get : forall j x, In j js -> set j (get j x) x = x.
  Proof.
    intros j x Hj. apply sh_ext. intros k Hk. destruct (Nat.eq_dec k j) as [-> | N].
    - apply get_set_eq. exact Hj.
    - apply get_set_neq. exact N.
  Qed.

  Section Net.
    Variable Fv : nat -> Sh -> bool.

    Definition larc (x : Sh) (j i : nat) : bool := negb (Bool.eqb (Fv i (flip j x)) (Fv i x)).
    Definition lneg (x : Sh) (j i : nat) : bool := xorb (Fv i x) (get j x).

    Definition PosCycleAt (x : Sh) (c : list nat) : Prop := IsCycle (larc x) c /\ csign (lneg x) c = false.
    Definition NegCycleAt (x : Sh) (c : list nat) : Prop := IsCycle (larc x) c /\ csign (lneg x) c = true.
    Definition NoLocalPos (I : list nat) : Prop := forall x c, incl c I -> ~ PosCycleAt x c.
    Definition NoLocalNeg (I : list nat) : Prop := forall x c, incl c I -> ~ NegCycleAt x c.
    Definition NoLocalCycle (I : list nat) : Prop := forall x c, incl c I -> ~ IsCycle (larc x) c.
    Definition IFixed (I : list nat) (x : Sh) : Prop := forall i, In i I -> Fv i x = get i x.

    (* The sign of an arc j -> i at x is the direction in which Fv i moves when x_j rises. *)
    Lemma lneg_spec : forall x j i, In j js -> larc x j i = true ->
      Fv i (set j false x) = lneg x j i /\ Fv i (set j true x) = negb (lneg x j i).
    Proof.
      intros x j i Hj Ha. pose proof (set_get j x Hj) as Ex. unfold larc, lneg, flip in *.
      destruct (get j x) eqn:G; simpl in *; rewrite Ex in *.
      - destruct (Fv i (set j false x)), (Fv i x); simpl in *; split; congruence.
      - destruct (Fv i (set j true x)), (Fv i x); simpl in *; split; congruence.
    Qed.

    (* At a point fixed on I, every cycle inside I has sign false (is positive). *)
    Lemma fixed_csign : forall I x c, IFixed I x -> incl c I -> csign (lneg x) c = false.
    Proof.
      intros I x c Hf Hc.
      rewrite (csign_ext (lneg x) (fun u v => xorb (get u x) (get v x)) c).
      - exact (csign_tele (fun u => get u x) c).
      - intros u v Hv. unfold lneg. rewrite (Hf v (Hc v Hv)). apply xorb_comm.
    Qed.

    Lemma sink_flip : forall x k i, larc x k i = false -> Fv i (flip k x) = Fv i x.
    Proof.
      intros x k i H. unfold larc in H. destruct (Bool.eqb (Fv i (flip k x)) (Fv i x)) eqn:Q.
      - apply Bool.eqb_prop. exact Q.
      - discriminate H.
    Qed.

    (* Remy, Ruet and Thieffry, on every subcube: two points that agree off I and are both fixed
       on I agree on I, when no G(x) has a positive cycle inside I. *)
    Theorem rrt_sub : forall n I, length I <= n -> incl I js -> NoLocalPos I ->
      forall x y, (forall j, In j js -> ~ In j I -> get j x = get j y) ->
      IFixed I x -> IFixed I y -> forall j, In j I -> get j x = get j y.
    Proof.
      induction n as [| n IH]; intros I Hl HI Hp x y Ho Hx Hy.
      { destruct I as [| a I]; [intros j [] | simpl in Hl; lia]. }
      assert (Hsub : forall k, In k I -> length (rm k I) <= n /\ incl (rm k I) js /\
                       NoLocalPos (rm k I) /\ forall z, IFixed I z -> IFixed (rm k I) z).
      { intros k Hk. pose proof (rm_length k I Hk). split; [lia |].
        split; [intros u Hu; apply HI; exact (proj1 (proj1 (rm_In k I u) Hu)) |].
        split; [intros z c Hc; apply Hp; intros u Hu; exact (proj1 (proj1 (rm_In k I u) (Hc u Hu))) |].
        intros z Hz i Hi. apply Hz. exact (proj1 (proj1 (rm_In k I i) Hi)). }
      destruct (existsb (fun k => Bool.eqb (get k x) (get k y)) I) eqn:E.
      - (* x and y agree at some k of I: freeze k *)
        apply existsb_exists in E. destruct E as [k [Hk Ek]]. apply Bool.eqb_prop in Ek.
        destruct (Hsub k Hk) as (L & Inc & P & Fx).
        assert (Hr : forall j, In j (rm k I) -> get j x = get j y).
        { apply (IH (rm k I) L Inc P x y); [| apply Fx; exact Hx | apply Fx; exact Hy].
          intros j Hj Hn. destruct (Nat.eq_dec j k) as [-> | Nk]; [exact Ek |].
          apply Ho; [exact Hj |]. intro HjI. apply Hn. apply rm_In. split; assumption. }
        intros j Hj. destruct (Nat.eq_dec j k) as [-> | Nk]; [exact Ek |].
        apply Hr. apply rm_In. split; assumption.
      - (* x and y are antipodal on I *)
        assert (Hd : forall k, In k I -> get k y = negb (get k x)).
        { intros k Hk. destruct (get k x) eqn:Gx, (get k y) eqn:Gy; try reflexivity; exfalso;
          assert (existsb (fun k => Bool.eqb (get k x) (get k y)) I = true)
            by (apply existsb_exists; exists k; split; [exact Hk | rewrite Gx, Gy; reflexivity]);
          congruence. }
        destruct I as [| a I0]; [intros j [] |].
        destruct (cycle_or_sink (larc x) (a :: I0) ltac:(discriminate)) as [[c [Hc Hcy]] | [k [Hk Hs]]].
        + exfalso. apply (Hp x c Hc). split; [exact Hcy |]. exact (fixed_csign (a :: I0) x c Hx Hc).
        + exfalso. destruct (Hsub k Hk) as (L & Inc & P & Fx).
          assert (Hkjs : In k js) by (apply HI; exact Hk).
          assert (Hsink : forall i, In i (a :: I0) -> Fv i (flip k x) = Fv i x)
            by (intros i Hi; apply sink_flip; apply Hs; exact Hi).
          assert (Hx' : IFixed (rm k (a :: I0)) (flip k x)).
          { intros i Hi. apply rm_In in Hi. destruct Hi as [Hi Nk]. rewrite (Hsink i Hi), (Hx i Hi).
            unfold flip. rewrite get_set_neq by exact Nk. reflexivity. }
          assert (Hout : forall j, In j js -> ~ In j (rm k (a :: I0)) -> get j (flip k x) = get j y).
          { intros j Hj Hn. unfold flip. destruct (Nat.eq_dec j k) as [-> | Nk].
            - rewrite get_set_eq by exact Hkjs. rewrite (Hd k Hk). reflexivity.
            - rewrite get_set_neq by exact Nk. apply Ho; [exact Hj |]. intro HjI. apply Hn.
              apply rm_In. split; assumption. }
          assert (Hr : forall j, In j (rm k (a :: I0)) -> get j (flip k x) = get j y)
            by exact (IH (rm k (a :: I0)) L Inc P (flip k x) y Hout Hx' (Fx y Hy)).
          assert (Eq : flip k x = y).
          { apply sh_ext. intros j Hj. destruct (in_dec Nat.eq_dec j (rm k (a :: I0))) as [Hin | Hn];
              [exact (Hr j Hin) | exact (Hout j Hj Hn)]. }
          pose proof (Hy k Hk) as Fy. rewrite <- Eq in Fy. rewrite (Hsink k Hk), (Hx k Hk) in Fy.
          rewrite Eq, (Hd k Hk) in Fy. destruct (get k x); discriminate Fy.
    Qed.

    Lemma fixed_iff : forall p, Fsync bool Sh js set Fv p = p <-> IFixed js p.
    Proof.
      intros p. split.
      - intros H i Hi. rewrite <- (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv p i Hi).
        rewrite H. reflexivity.
      - intros H. apply sh_ext. intros k Hk.
        rewrite (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv p k Hk). apply H. exact Hk.
    Qed.

    (* Local fidelity (Remy, Ruet and Thieffry 2008): no positive cycle in any local graph gives
       at most one fixed point. *)
    Theorem local_fidelity : NoLocalPos js -> forall p q,
      Fsync bool Sh js set Fv p = p -> Fsync bool Sh js set Fv q = q -> p = q.
    Proof.
      intros Hn p q Hp Hq. apply fixed_iff in Hp. apply fixed_iff in Hq. apply sh_ext.
      apply (rrt_sub (length js) js (le_n _) (incl_refl _) Hn p q); [| exact Hp | exact Hq].
      intros j Hj Hn'. contradiction.
    Qed.

    (* Into E: every settled reachable configuration is the fixed point. *)
    Theorem local_fidelity_canon : NoLocalPos js -> forall q, Fsync bool Sh js set Fv q = q ->
      forall s0, CanonicalFidelity (fun _ => q) (rupd bool Sh js set Fv) (r_ok js)
                   (r_settled bool Sh js set Fv) s0.
    Proof.
      intros Hn q Hq s0 w _ Hs. apply (settled_fixed bool Sh js get set get_set_eq get_set_neq sh_ext Fv) in Hs.
      exact (local_fidelity Hn _ _ Hs Hq).
    Qed.

    (* The lift through the global signed certificate (SignedResolver.signed_fidelity), with
       uniqueness derived from the local graphs. *)
    Theorem local_signed_fidelity : forall (z0 : Sh) sg o,
      SgOn js sg -> Resp bool Sh sbl js get Fv sg -> Switching sg o -> NoLocalPos js ->
      let q := slfp bool Sh false true 1 bool_dec js get set sh_ext z0 Fv o in
      Fsync bool Sh js set Fv q = q /\
      (forall p, Fsync bool Sh js set Fv p = p -> p = q) /\
      (forall sch, Fair js sch -> forall h0, Settles Sh (rupd bool Sh js set Fv) sch h0 q) /\
      (forall h0, EffectiveCanon (fun _ => q) (rupd bool Sh js set Fv) (r_ok js) (r_flush js)
                    (r_settled bool Sh js set Fv) h0).
    Proof.
      intros z0 sg o Hon Hr Hsw Hn q.
      destruct (signed_fidelity bool Sh sbl sbl_refl sbl_trans sbl_antisym false true sbl_bot sbl_top
                  sb2n sb2n_strict 1 sb2n_bound bool_dec js get set get_set_eq get_set_neq sh_ext z0 Fv
                  sg Hon Hr o Hsw (local_fidelity Hn)) as (Hfix & H1 & H2).
      split; [exact Hfix |]. split; [intros p Hp; exact (local_fidelity Hn p q Hp Hfix) |].
      split; [exact H1 |]. intros h0. exact (proj1 (H2 h0)).
    Qed.

    (* Every local arc is an arc of every global certificate, with the same sign. *)
    Lemma local_in_global : forall sg, Resp bool Sh sbl js get Fv sg -> forall x j i,
      In i js -> In j js -> larc x j i = true -> In (j, i, lneg x j i) sg.
    Proof.
      intros sg Hr x j i Hi Hj Ha.
      destruct (in_dec sedge_dec (j, i, lneg x j i) sg) as [H | H]; [exact H | exfalso].
      destruct (lneg_spec x j i Hj Ha) as [E0 E1].
      assert (Gu : forall u b, u <> j -> get u (set j b x) = get u x)
        by (intros u b N; apply get_set_neq; exact N).
      destruct (lneg x j i) eqn:L; simpl in E1.
      - (* negative arc missing: Fv i falls from true to false *)
        assert (P : forall u b, In (u, i, b) sg ->
                  if b then sbl (get u (set j true x)) (get u (set j false x))
                  else sbl (get u (set j false x)) (get u (set j true x))).
        { intros u b Hin. destruct (Nat.eq_dec u j) as [-> | N].
          - destruct b; [exfalso; exact (H Hin) |].
            rewrite !get_set_eq by exact Hj. reflexivity.
          - rewrite !Gu by exact N. destruct b; apply sbl_refl. }
        pose proof (Hr i Hi _ _ P) as R. rewrite E0, E1 in R. discriminate R.
      - assert (P : forall u b, In (u, i, b) sg ->
                  if b then sbl (get u (set j false x)) (get u (set j true x))
                  else sbl (get u (set j true x)) (get u (set j false x))).
        { intros u b Hin. destruct (Nat.eq_dec u j) as [-> | N].
          - destruct b; [| exfalso; exact (H Hin)].
            rewrite !get_set_eq by exact Hj. reflexivity.
          - rewrite !Gu by exact N. destruct b; apply sbl_refl. }
        pose proof (Hr i Hi _ _ P) as R. rewrite E0, E1 in R. discriminate R.
    Qed.

    Lemma local_cycle_global : forall sg, Resp bool Sh sbl js get Fv sg -> forall x c,
      incl c js -> IsCycle (larc x) c -> SgCycle sg c (csign (lneg x) c).
    Proof.
      intros sg Hr x c Hc [Hne [Hnd Hok]]. split; [exact Hne | split; [exact Hnd |]].
      unfold csign. unfold cyc_ok in Hok. rewrite forallb_forall in Hok.
      assert (G : forall ps, (forall p, In p ps -> In (fst p) js /\ In (snd p) js /\
                                larc x (fst p) (snd p) = true) ->
                SgPath sg ps (fold_right (fun p h => xorb (lneg x (fst p) (snd p)) h) false ps)).
      { induction ps as [| [u v] ps IH]; intros Hp; [constructor |]. cbn [fold_right fst snd].
        destruct (Hp (u, v) (or_introl eq_refl)) as (Hu & Hv & Ha). apply sgp_cons.
        - exact (local_in_global sg Hr x u v Hv Hu Ha).
        - apply IH. intros p Hq. apply Hp. right. exact Hq. }
      apply G. intros p Hp. destruct (in_cpairs c p Hp) as [H1 H2].
      split; [apply Hc; exact H1 | split; [apply Hc; exact H2 | exact (Hok p Hp)]].
    Qed.

    (* The global condition implies the local one. *)
    Theorem global_to_local : forall sg, Resp bool Sh sbl js get Fv sg ->
      (forall c, incl c js -> ~ SgCycle sg c false) -> NoLocalPos js.
    Proof.
      intros sg Hr Hg x c Hc [Hcy Hs]. apply (Hg c Hc). rewrite <- Hs.
      exact (local_cycle_global sg Hr x c Hc Hcy).
    Qed.
  End Net.

  (* ----- local settlement: paths to fixed points ----- *)

  Definition negk (Fv : nat -> Sh -> bool) (k : nat) : nat -> Sh -> bool :=
    fun j s => if Nat.eqb j k then negb (Fv j s) else Fv j s.

  Lemma negk_larc : forall Fv k x j i, larc (negk Fv k) x j i = larc Fv x j i.
  Proof.
    intros Fv k x j i. unfold larc, negk. destruct (Nat.eqb i k); [| reflexivity].
    destruct (Fv i (flip j x)), (Fv i x); reflexivity.
  Qed.

  Lemma negk_csign : forall Fv k x c, NoDup c ->
    csign (lneg (negk Fv k) x) c = xorb (csign (lneg Fv x) c) (if in_dec Nat.eq_dec k c then true else false).
  Proof.
    intros Fv k x c Hn.
    rewrite (csign_ext (lneg (negk Fv k) x) (fun u v => xorb (lneg Fv x u v) (Nat.eqb v k)) c).
    - rewrite csign_xor. f_equal. rewrite (csign_target (fun v => Nat.eqb v k)).
      destruct (in_dec Nat.eq_dec k c) as [Hin | Hout].
      + apply (parity_in k c Hn). exact Hin.
      + destruct (fold_right (fun i h => xorb (Nat.eqb i k) h) false c) eqn:E; [| reflexivity].
        exfalso. apply Hout. apply (parity_in k c Hn). exact E.
    - intros u v _. unfold lneg, negk. destruct (Nat.eqb v k); [| destruct (xorb (Fv v x) (get u x)); reflexivity].
      destruct (Fv v x), (get u x); reflexivity.
  Qed.

  Section Paths.
    Variable Fv : nat -> Sh -> bool.
    Local Notation xw := (xr bool Sh js set Fv).
    Local Notation ru := (rupd bool Sh js set Fv).

    Lemma xr_cons : forall a w x, xw (a :: w) x = xw w (ru a x).
    Proof. reflexivity. Qed.

    Lemma xr_out : forall w x j, ~ In j w -> get j (xw w x) = get j x.
    Proof.
      induction w as [| a w IH]; intros x j H; [reflexivity |].
      rewrite xr_cons, IH by (intro Hj; apply H; right; exact Hj).
      apply (get_rupd_other bool Sh js get set get_set_neq Fv a j x). intro E. apply H. left. symmetry. exact E.
    Qed.

    (* One step of Richard's Theorem 4: from paths on I without k to paths on I. *)
    Lemma t4_path : forall I k, In k I -> incl I js -> NoLocalNeg Fv I ->
      (forall x c, incl c I -> PosCycleAt Fv x c -> In k c) ->
      (forall x, exists w, incl w (rm k I) /\ IFixed Fv (rm k I) (xw w x)) ->
      forall x, exists w, incl w I /\ IFixed Fv I (xw w x).
    Proof.
      intros I k Hk HI Hneg Hpos Hsub x.
      assert (Hkjs : In k js) by (apply HI; exact Hk).
      assert (Hrm : forall i, In i I -> i <> k -> In i (rm k I)) by (intros i Hi N; apply rm_In; split; assumption).
      assert (Hnk : forall w, incl w (rm k I) -> ~ In k w)
        by (intros w Hw Hin; exact (proj2 (proj1 (rm_In k I k) (Hw k Hin)) eq_refl)).
      assert (Hsw : forall w, incl w (rm k I) -> incl w I)
        by (intros w Hw u Hu; exact (proj1 (proj1 (rm_In k I u) (Hw u Hu)))).
      assert (Comb : forall z, IFixed Fv (rm k I) z -> Fv k z = get k z -> IFixed Fv I z).
      { intros z Hz Hzk i Hi. destruct (Nat.eq_dec i k) as [-> | N]; [exact Hzk |]. apply Hz. apply Hrm; assumption. }
      destruct (Hsub x) as [w1 [Hw1 F1]].
      destruct (Bool.bool_dec (Fv k (xw w1 x)) (get k (xw w1 x))) as [E1 | N1].
      { exists w1. split; [exact (Hsw w1 Hw1) | apply Comb; assumption]. }
      destruct (Hsub (ru k (xw w1 x))) as [w2 [Hw2 F2]].
      destruct (Bool.bool_dec (Fv k (xw w2 (ru k (xw w1 x)))) (get k (xw w2 (ru k (xw w1 x))))) as [E3 | N3].
      { exists (w1 ++ k :: w2). split.
        - intros u Hu. apply in_app_or in Hu. destruct Hu as [Hu | [<- | Hu]];
            [exact (Hsw w1 Hw1 u Hu) | exact Hk | exact (Hsw w2 Hw2 u Hu)].
        - rewrite (xr_app bool Sh js set Fv w1 (k :: w2)), xr_cons. apply Comb; assumption. }
      exfalso.
      assert (G : forall z, IFixed Fv (rm k I) z -> Fv k z <> get k z -> IFixed (negk Fv k) I z).
      { intros z Hz Nz i Hi. unfold negk. destruct (Nat.eqb_spec i k) as [-> | N].
        - destruct (Fv k z), (get k z); simpl; congruence.
        - apply Hz. apply Hrm; assumption. }
      assert (NP : NoLocalPos (negk Fv k) I).
      { intros z c Hc [[Hne [Hnd Hok]] Hs].
        assert (Cy : IsCycle (larc Fv z) c).
        { split; [exact Hne | split; [exact Hnd |]]. rewrite <- Hok. apply cyc_ok_ext.
          intros u v. symmetry. apply negk_larc. }
        revert Hs. rewrite (negk_csign Fv k z c Hnd). destruct (in_dec Nat.eq_dec k c) as [Hin | Hout]; intro Hs.
        - apply (Hneg z c Hc). split; [exact Cy |]. destruct (csign (lneg Fv z) c); [reflexivity | discriminate Hs].
        - apply Hout. apply (Hpos z c Hc). split; [exact Cy |].
          destruct (csign (lneg Fv z) c); [discriminate Hs | reflexivity]. }
      assert (O1 : forall j, ~ In j I -> get j (xw w1 x) = get j x).
      { intros j Hn. apply xr_out. intro Hj. apply Hn. exact (Hsw w1 Hw1 j Hj). }
      assert (Out : forall j, In j js -> ~ In j I -> get j (xw w1 x) = get j (xw w2 (ru k (xw w1 x)))).
      { intros j Hj Hn. rewrite (xr_out w2 _ j) by (intro Hj2; apply Hn; exact (Hsw w2 Hw2 j Hj2)).
        rewrite (get_rupd_other bool Sh js get set get_set_neq Fv k j); [reflexivity |].
        intro E. apply Hn. rewrite E. exact Hk. }
      pose proof (rrt_sub (negk Fv k) (length I) I (le_n _) HI NP (xw w1 x) (xw w2 (ru k (xw w1 x)))
                    Out (G _ F1 N1) (G _ F2 N3) k Hk) as Ek.
      rewrite (xr_out w2 _ k) in Ek by exact (Hnk w2 Hw2).
      rewrite (get_rupd_same bool Sh js get set get_set_eq Fv k _ Hkjs) in Ek.
      apply N1. symmetry. exact Ek.
    Qed.

    (* Shih and Dong, with paths: no cycle in any local graph inside I, then from every state an
       update word over I reaches a point fixed on I. *)
    Lemma sd_path : forall n I, length I <= n -> incl I js -> NoLocalCycle Fv I ->
      forall x, exists w, incl w I /\ IFixed Fv I (xw w x).
    Proof.
      induction n as [| n IH]; intros I Hl HI Hc x.
      - destruct I as [| a I]; [| simpl in Hl; lia].
        exists []. split; [intros u [] | intros i []].
      - destruct I as [| k I0]; [exists []; split; [intros u [] | intros i []] |].
        apply (t4_path (k :: I0) k (or_introl eq_refl) HI).
        + intros z c Hcc [Hcy _]. exact (Hc z c Hcc Hcy).
        + intros z c Hcc [Hcy _]. exfalso. exact (Hc z c Hcc Hcy).
        + apply IH.
          * pose proof (rm_length k (k :: I0) (or_introl eq_refl)) as L. lia.
          * intros u Hu. apply HI. exact (proj1 (proj1 (rm_In k _ u) Hu)).
          * intros z c Hcc. apply Hc. intros u Hu. exact (proj1 (proj1 (rm_In k _ u) (Hcc u Hu))).
    Qed.

    (* Richard 2011, Theorem 4, with paths: no negative cycle in any local graph inside I, and a
       vertex k on every positive one. *)
    Theorem t4_full : forall I k, In k I -> incl I js -> NoLocalNeg Fv I ->
      (forall x c, incl c I -> PosCycleAt Fv x c -> In k c) ->
      forall x, exists w, incl w I /\ IFixed Fv I (xw w x).
    Proof.
      intros I k Hk HI Hn Hp. apply (t4_path I k Hk HI Hn Hp).
      apply (sd_path (length (rm k I)) (rm k I) (le_n _)).
      - intros u Hu. apply HI. exact (proj1 (proj1 (rm_In k I u) Hu)).
      - intros z c Hc Hcy.
        assert (Hc' : incl c I) by (intros u Hu; exact (proj1 (proj1 (rm_In k I u) (Hc u Hu)))).
        destruct (csign (lneg Fv z) c) eqn:S.
        + exact (Hn z c Hc' (conj Hcy S)).
        + pose proof (Hp z c Hc' (conj Hcy S)) as Hin. exact (proj2 (proj1 (rm_In k I k) (Hc k Hin)) eq_refl).
    Qed.

    Lemma settle_from_paths : (forall s, exists w, incl w js /\ IFixed Fv js (xw w s)) ->
      forall s0, Settlement ru (r_ok js) (r_flush js) (r_settled bool Sh js set Fv) s0.
    Proof.
      intros H s0 w _. destruct (H (xw w s0)) as [c [Hc Hf]]. exists c. split.
      - apply Forall_forall. intros a Ha. exact (Hc a Ha).
      - change (xrun ru (w ++ c) s0) with (xw (w ++ c) s0). rewrite (xr_app bool Sh js set Fv).
        apply (settled_fixed bool Sh js get set get_set_eq get_set_neq sh_ext Fv). apply (fixed_iff Fv). exact Hf.
    Qed.

    (* Local settlement, corrected (Richard 2011, Theorem 4): a fixed point exists and is reached
       from every state by some update word, so E's Settlement holds from every start. *)
    Theorem richard_t4 : forall k, In k js -> NoLocalNeg Fv js ->
      (forall x c, incl c js -> PosCycleAt Fv x c -> In k c) ->
      (forall s0, exists w, Forall (r_ok js) w /\ Fsync bool Sh js set Fv (xw w s0) = xw w s0) /\
      (forall s0, Settlement ru (r_ok js) (r_flush js) (r_settled bool Sh js set Fv) s0).
    Proof.
      intros k Hk Hn Hp.
      pose proof (t4_full js k Hk (incl_refl _) Hn Hp) as H.
      split; [| exact (settle_from_paths H)].
      intros s0. destruct (H s0) as [w [Hw Hf]]. exists w. split.
      - apply Forall_forall. intros a Ha. exact (Hw a Ha).
      - apply (fixed_iff Fv). exact Hf.
    Qed.

    (* Shih and Dong 2005 into E: no cycle in any local graph gives a unique fixed point q, and E
       with the constant canonicalizer q holds from every start. *)
    Theorem shih_dong_E : NoLocalCycle Fv js -> forall z : Sh, exists q,
      Fsync bool Sh js set Fv q = q /\ (forall p, Fsync bool Sh js set Fv p = p -> p = q) /\
      forall s0, EffectiveCanon (fun _ => q) ru (r_ok js) (r_flush js) (r_settled bool Sh js set Fv) s0.
    Proof.
      intros Hc z.
      assert (Hp : NoLocalPos Fv js) by (intros x c Hcc [Hcy _]; exact (Hc x c Hcc Hcy)).
      pose proof (sd_path (length js) js (le_n _) (incl_refl _) Hc) as H.
      destruct (H z) as [w [_ Hf]]. apply (fixed_iff Fv) in Hf. exists (xw w z).
      split; [exact Hf |]. split; [intros p Hq; exact (local_fidelity Fv Hp p _ Hq Hf) |].
      intros s0. split; [exact (settle_from_paths H s0) |]. exact (local_fidelity_canon Fv Hp _ Hf s0).
    Qed.
  End Paths.

  (* ----- Richard 2011, Theorem 3: out-degree at most one (non-expansive networks) ----- *)

  Lemma get_flip : forall j t z, In j js -> get t (flip j z) = xorb (get t z) (Nat.eqb j t).
  Proof.
    intros j t z Hj. unfold flip. destruct (Nat.eqb_spec j t) as [<- | N].
    - rewrite get_set_eq by exact Hj. destruct (get j z); reflexivity.
    - rewrite get_set_neq by (intro E; apply N; symmetry; exact E). destruct (get t z); reflexivity.
  Qed.

  Lemma flip_flip : forall j z, In j js -> flip j (flip j z) = z.
  Proof.
    intros j z Hj. apply sh_ext. intros t Ht. rewrite !get_flip by exact Hj.
    destruct (get t z), (Nat.eqb j t); reflexivity.
  Qed.

  Lemma flip_comm : forall a c z, In a js -> In c js -> flip a (flip c z) = flip c (flip a z).
  Proof.
    intros a c z Ha Hc. apply sh_ext. intros t Ht. rewrite !get_flip by assumption.
    destruct (get t z), (Nat.eqb a t), (Nat.eqb c t); reflexivity.
  Qed.

  Section Opp.
    Variable Fv : nat -> Sh -> bool.
    Local Notation xw := (xr bool Sh js set Fv).
    Local Notation ru := (rupd bool Sh js set Fv).

    (* Richard's property P: every vertex of every local graph has out-degree at most one inside
       I. Equivalent to non-expansiveness for the Hamming distance (outdeg_nonexpansive). *)
    Definition OutDeg1 (I : list nat) : Prop := forall x j, In j I -> length (filter (larc Fv x j) I) <= 1.
    Definition AgreeOff (I : list nat) (u v : Sh) : Prop := forall j, In j js -> ~ In j I -> get j u = get j v.
    (* z is in opposition at i: the synchronous update on I flips exactly the coordinate i. *)
    Definition Opp (I : list nat) (i : nat) (z : Sh) : Prop :=
      In i I /\ forall t, In t I -> Fv t z = get t (flip i z).
    Definition OppPair (I : list nat) (i : nat) (a b : Sh) : Prop :=
      Opp I i a /\ Opp I i b /\ AgreeOff I a b /\ get i a <> get i b.

    Definition cnt (I : list nat) (f g : nat -> bool) : nat :=
      length (filter (fun t => negb (Bool.eqb (f t) (g t))) I).
    Definition dS (I : list nat) (u v : Sh) : nat := cnt I (fun t => get t u) (fun t => get t v).
    Definition dF (I : list nat) (u v : Sh) : nat := cnt I (fun t => Fv t u) (fun t => Fv t v).

    Lemma filter_ext_in' : forall (f g : nat -> bool) l, (forall a, In a l -> f a = g a) -> filter f l = filter g l.
    Proof.
      intros f g. induction l as [| a l IH]; intros H; [reflexivity |]. simpl.
      rewrite (H a (or_introl eq_refl)), IH by (intros b Hb; apply H; right; exact Hb). reflexivity.
    Qed.

    Lemma cnt_ext : forall I f f' g g', (forall t, In t I -> f t = f' t) -> (forall t, In t I -> g t = g' t) ->
      cnt I f g = cnt I f' g'.
    Proof.
      intros I f f' g g' Hf Hg. unfold cnt. f_equal. apply filter_ext_in'. intros t Ht.
      rewrite (Hf t Ht), (Hg t Ht). reflexivity.
    Qed.

    Lemma cnt_sym : forall I f g, cnt I f g = cnt I g f.
    Proof.
      intros I f g. unfold cnt. f_equal. apply filter_ext_in'. intros t _. destruct (f t), (g t); reflexivity.
    Qed.

    Lemma cnt_refl : forall I f, cnt I f f = 0.
    Proof. intros I f. unfold cnt. induction I as [| a I IH]; [reflexivity |]. simpl. rewrite Bool.eqb_reflx. exact IH. Qed.

    Lemma cnt_le : forall I f g, cnt I f g <= length I.
    Proof.
      intros I f g. unfold cnt. induction I as [| a I IH]; [reflexivity |]. simpl.
      destruct (negb (Bool.eqb (f a) (g a))); simpl; lia.
    Qed.

    Lemma cnt_tri : forall I f g h, cnt I f h <= cnt I f g + cnt I g h.
    Proof.
      intros I f g h. unfold cnt. induction I as [| a I IH]; [reflexivity |]. simpl.
      destruct (f a), (g a), (h a); simpl; lia.
    Qed.

    Lemma cnt_zero : forall I f g, cnt I f g = 0 -> forall t, In t I -> f t = g t.
    Proof.
      intros I f g. unfold cnt. induction I as [| a I IH]; intros H t Ht; [destruct Ht |]. simpl in H.
      destruct (Bool.eqb (f a) (g a)) eqn:E; simpl in H; [| discriminate H].
      destruct Ht as [<- | Ht]; [apply Bool.eqb_prop; exact E | exact (IH H t Ht)].
    Qed.

    Lemma cnt_pos : forall I f g, cnt I f g <> 0 -> exists t, In t I /\ f t <> g t.
    Proof.
      intros I f g. unfold cnt. induction I as [| a I IH]; intros H; [simpl in H; congruence |]. simpl in H.
      destruct (Bool.eqb (f a) (g a)) eqn:E; simpl in H.
      - destruct (IH H) as [t [Ht Nt]]. exists t. split; [right; exact Ht | exact Nt].
      - exists a. split; [left; reflexivity |]. intro Q. rewrite Q, Bool.eqb_reflx in E. discriminate E.
    Qed.

    Lemma cnt_full : forall I f g, cnt I f g = length I -> forall t, In t I -> f t <> g t.
    Proof.
      intros I f g. induction I as [| a I IH]; intros H t Ht; [destruct Ht |].
      pose proof (cnt_le I f g) as L. unfold cnt in H, L |- *. simpl in H.
      destruct (Bool.eqb (f a) (g a)) eqn:E; simpl in H; [lia |].
      destruct Ht as [<- | Ht].
      - intro Q. rewrite Q, Bool.eqb_reflx in E. discriminate E.
      - apply IH; [unfold cnt; lia | exact Ht].
    Qed.

    Lemma cnt_all : forall I f g, (forall t, In t I -> f t <> g t) -> cnt I f g = length I.
    Proof.
      intros I f g. induction I as [| a I IH]; intros H; [reflexivity |]. unfold cnt in *. simpl.
      destruct (Bool.eqb (f a) (g a)) eqn:E.
      - exfalso. apply (H a (or_introl eq_refl)). apply Bool.eqb_prop. exact E.
      - simpl. rewrite IH; [reflexivity |]. intros t Ht. apply H. right. exact Ht.
    Qed.

    Lemma cnt_one : forall I f g, cnt I f g = 1 ->
      exists j, In j I /\ f j <> g j /\ forall t, In t I -> t <> j -> f t = g t.
    Proof.
      intros I f g. induction I as [| a I IH]; intros H; [discriminate H |].
      unfold cnt in H. simpl in H. destruct (Bool.eqb (f a) (g a)) eqn:E; simpl in H.
      - destruct (IH H) as [j [Hj [Nj Oj]]]. exists j. split; [right; exact Hj | split; [exact Nj |]].
        intros t [<- | Ht] Nt; [apply Bool.eqb_prop; exact E | exact (Oj t Ht Nt)].
      - injection H as H. exists a. split; [left; reflexivity | split].
        + intro Q. rewrite Q, Bool.eqb_reflx in E. discriminate E.
        + intros t [<- | Ht] Nt; [congruence | exact (cnt_zero I f g H t Ht)].
    Qed.

    Lemma cnt_flip_notin : forall I f g j, ~ In j I ->
      cnt I (fun t => xorb (f t) (Nat.eqb j t)) g = cnt I f g.
    Proof.
      intros I f g j H. apply cnt_ext; [| reflexivity].
      intros t Ht. rewrite (proj2 (Nat.eqb_neq j t)) by (intro E; subst; contradiction). apply xorb_false_r.
    Qed.

    Lemma cnt_flip_eq : forall I f g j, NoDup I -> In j I -> f j = g j ->
      cnt I (fun t => xorb (f t) (Nat.eqb j t)) g = S (cnt I f g).
    Proof.
      intros I f g j. induction I as [| a I IH]; intros Hn Hj E; [destruct Hj |].
      inversion Hn as [| ? ? Ha Hn']; subst.
      unfold cnt in *. simpl. destruct (Nat.eqb_spec j a) as [<- | N].
      - pose proof (cnt_flip_notin I f g j Ha) as C. unfold cnt in C.
        rewrite E, Bool.eqb_reflx. destruct (g j); simpl; f_equal; first [exact C | symmetry; exact C].
      - rewrite xorb_false_r. destruct Hj as [Q | Hj]; [congruence |].
        destruct (Bool.eqb (f a) (g a)); simpl; [| f_equal]; exact (IH Hn' Hj E).
    Qed.

    Lemma cnt_flip_neq : forall I f g j, NoDup I -> In j I -> f j <> g j ->
      S (cnt I (fun t => xorb (f t) (Nat.eqb j t)) g) = cnt I f g.
    Proof.
      intros I f g j. induction I as [| a I IH]; intros Hn Hj E; [destruct Hj |].
      inversion Hn as [| ? ? Ha Hn']; subst.
      unfold cnt in *. simpl. destruct (Nat.eqb_spec j a) as [<- | N].
      - pose proof (cnt_flip_notin I f g j Ha) as C. unfold cnt in C.
        destruct (f j), (g j); try congruence; simpl; f_equal; first [exact C | symmetry; exact C].
      - rewrite xorb_false_r. destruct Hj as [Q | Hj]; [congruence |].
        destruct (Bool.eqb (f a) (g a)); simpl; [| f_equal]; exact (IH Hn' Hj E).
    Qed.

    Lemma two_le_length : forall (l : list nat) a b, In a l -> In b l -> a <> b -> 2 <= length l.
    Proof.
      induction l as [| c l IH]; intros a b Ha Hb N; [destruct Ha |].
      destruct Ha as [<- | Ha], Hb as [<- | Hb].
      - congruence.
      - destruct l; [destruct Hb | simpl; lia].
      - destruct l; [destruct Ha | simpl; lia].
      - pose proof (IH a b Ha Hb N). simpl. lia.
    Qed.

    Lemma od_unique : forall I x j t1 t2, OutDeg1 I -> In j I -> In t1 I -> In t2 I ->
      larc Fv x j t1 = true -> larc Fv x j t2 = true -> t1 = t2.
    Proof.
      intros I x j t1 t2 Hod Hj H1 H2 A1 A2. destruct (Nat.eq_dec t1 t2) as [E | N]; [exact E | exfalso].
      pose proof (Hod x j Hj) as L.
      pose proof (two_le_length (filter (larc Fv x j) I) t1 t2 (proj2 (filter_In _ _ _) (conj H1 A1))
                    (proj2 (filter_In _ _ _) (conj H2 A2)) N). lia.
    Qed.

    Lemma dF_flip : forall I x j, dF I x (flip j x) = length (filter (larc Fv x j) I).
    Proof.
      intros I x j. unfold dF, cnt, larc. f_equal. apply filter_ext_in'. intros t _.
      destruct (Fv t x), (Fv t (flip j x)); reflexivity.
    Qed.

    Lemma agree_sym : forall I u v, AgreeOff I u v -> AgreeOff I v u.
    Proof. intros I u v H j Hj Hn. symmetry. exact (H j Hj Hn). Qed.

    Lemma agree_trans : forall I u v w, AgreeOff I u v -> AgreeOff I v w -> AgreeOff I u w.
    Proof. intros I u v w H1 H2 j Hj Hn. rewrite (H1 j Hj Hn). exact (H2 j Hj Hn). Qed.

    Lemma agree_flip : forall I j z, In j I -> In j js -> AgreeOff I (flip j z) z.
    Proof.
      intros I j z HjI Hj t Ht Hn. rewrite get_flip by exact Hj.
      rewrite (proj2 (Nat.eqb_neq j t)) by (intro E; subst; contradiction). apply xorb_false_r.
    Qed.

    Lemma dS_flip_self : forall I j z, NoDup I -> In j I -> In j js -> dS I (flip j z) z = 1.
    Proof.
      intros I j z Hn HjI Hj. unfold dS.
      rewrite (cnt_ext I (fun t => get t (flip j z)) (fun t => xorb (get t z) (Nat.eqb j t))
                 (fun t => get t z) (fun t => get t z)) by (intros t _; first [apply get_flip; exact Hj | reflexivity]).
      rewrite (cnt_flip_eq I _ _ j Hn HjI eq_refl), cnt_refl. reflexivity.
    Qed.

    (* Out-degree at most one gives non-expansiveness: the synchronous update on I does not
       increase the Hamming distance on I. *)
    Lemma nonexp : forall I, NoDup I -> incl I js -> OutDeg1 I ->
      forall m x y, dS I x y = m -> AgreeOff I x y -> dF I x y <= m.
    Proof.
      intros I Hn HI Hod. induction m as [| m IH]; intros x y Hd Ha.
      - assert (E : x = y).
        { apply sh_ext. intros j Hj. destruct (in_dec Nat.eq_dec j I) as [Hi | Hi];
            [exact (cnt_zero I _ _ Hd j Hi) | exact (Ha j Hj Hi)]. }
        subst y. unfold dF. rewrite cnt_refl. lia.
      - assert (Hnz : cnt I (fun t => get t x) (fun t => get t y) <> 0) by (unfold dS in Hd; rewrite Hd; discriminate).
        destruct (cnt_pos I _ _ Hnz) as [j [Hj Nj]].
        assert (Hjs : In j js) by (apply HI; exact Hj).
        assert (D : dS I (flip j x) y = m).
        { unfold dS in *.
          rewrite (cnt_ext I (fun t => get t (flip j x)) (fun t => xorb (get t x) (Nat.eqb j t))
                     (fun t => get t y) (fun t => get t y)) by (intros t _; first [apply get_flip; exact Hjs | reflexivity]).
          pose proof (cnt_flip_neq I (fun t => get t x) (fun t => get t y) j Hn Hj Nj) as C. lia. }
        assert (A : AgreeOff I (flip j x) y) by exact (agree_trans I _ _ _ (agree_flip I j x Hj Hjs) Ha).
        pose proof (IH (flip j x) y D A) as H1.
        pose proof (Hod x j Hj) as H2. rewrite <- dF_flip in H2.
        pose proof (cnt_tri I (fun t => Fv t x) (fun t => Fv t (flip j x)) (fun t => Fv t y)) as T.
        unfold dF in *. lia.
    Qed.

    Theorem outdeg_nonexpansive : forall I, NoDup I -> incl I js ->
      (OutDeg1 I <-> forall x y, AgreeOff I x y -> dF I x y <= dS I x y).
    Proof.
      intros I Hn HI. split.
      - intros Hod x y Ha. exact (nonexp I Hn HI Hod _ x y eq_refl Ha).
      - intros H x j Hj. rewrite <- dF_flip.
        assert (Hjs : In j js) by (apply HI; exact Hj).
        pose proof (H x (flip j x) (agree_sym I _ _ (agree_flip I j x Hj Hjs))) as L.
        unfold dS in L. rewrite cnt_sym in L. fold (dS I (flip j x) x) in L.
        rewrite (dS_flip_self I j x Hn Hj Hjs) in L. exact L.
    Qed.

    (* ----- orbits of flips ----- *)

    Definition flips (w : list nat) (z : Sh) : Sh := fold_left (fun z j => flip j z) w z.
    Definition pw (t : nat) (w : list nat) : bool := fold_right (fun j h => xorb (Nat.eqb j t) h) false w.

    Lemma get_flips : forall w z t, incl w js -> get t (flips w z) = xorb (get t z) (pw t w).
    Proof.
      induction w as [| j w IH]; intros z t Hw.
      - unfold flips, pw. simpl. destruct (get t z); reflexivity.
      - change (flips (j :: w) z) with (flips w (flip j z)).
        change (pw t (j :: w)) with (xorb (Nat.eqb j t) (pw t w)).
        rewrite IH by (intros u Hu; apply Hw; right; exact Hu).
        rewrite get_flip by (apply Hw; left; reflexivity).
        destruct (get t z), (Nat.eqb j t), (pw t w); reflexivity.
    Qed.

    Lemma pw_notin : forall t w, ~ In t w -> pw t w = false.
    Proof.
      intros t. induction w as [| j w IH]; intros H; [reflexivity |].
      change (pw t (j :: w)) with (xorb (Nat.eqb j t) (pw t w)).
      rewrite IH by (intro Q; apply H; right; exact Q).
      rewrite (proj2 (Nat.eqb_neq j t)) by (intro E; apply H; left; exact E). reflexivity.
    Qed.

    Lemma pw_in : forall t w, NoDup w -> In t w -> pw t w = true.
    Proof. intros t w Hn Hi. exact (proj2 (parity_in t w Hn) Hi). Qed.

    Lemma flips_snoc : forall w j z, flips (w ++ [j]) z = flip j (flips w z).
    Proof. intros w j z. unfold flips. rewrite fold_left_app. reflexivity. Qed.

    Lemma agree_flips : forall I w z, incl I js -> incl w I -> AgreeOff I (flips w z) z.
    Proof.
      intros I w z HI Hw t Ht Hn. rewrite get_flips by (intros u Hu; apply HI; apply Hw; exact Hu).
      rewrite pw_notin by (intro Q; apply Hn; apply Hw; exact Q). apply xorb_false_r.
    Qed.

    Lemma opp_csign : forall I j z c, incl I js -> Opp I j z -> incl c I -> NoDup c -> In j c ->
      csign (lneg Fv z) c = true.
    Proof.
      intros I j z c HI [Hj Hz] Hc Hn Hin.
      rewrite (csign_ext (lneg Fv z) (fun u v => xorb (xorb (get u z) (get v z)) (Nat.eqb v j)) c).
      - rewrite csign_xor, csign_tele, (csign_target (fun v => Nat.eqb v j)). simpl.
        exact (proj2 (parity_in j c Hn) Hin).
      - intros u v Hv. unfold lneg. rewrite (Hz v (Hc v Hv)), get_flip by (apply HI; exact Hj).
        rewrite Nat.eqb_sym. destruct (get u z), (get v z), (Nat.eqb v j); reflexivity.
    Qed.

    Lemma opp_sym : forall I i a b, OppPair I i a b -> OppPair I i b a.
    Proof.
      intros I i a b [Ha [Hb [Hab N]]]. split; [exact Hb | split; [exact Ha | split; [apply agree_sym; exact Hab |]]].
      intro E. apply N. symmetry. exact E.
    Qed.

    (* Two points in opposition at i that agree somewhere on I. *)
    Definition Hesc (I : list nat) : Prop :=
      forall j g h, OppPair I j g h -> (exists t, In t I /\ get t g = get t h) -> False.

    Lemma pair_anti : forall I i a b, Hesc I -> OppPair I i a b -> forall t, In t I -> get t a <> get t b.
    Proof. intros I i a b He Hp t Ht E. exact (He i a b Hp (ex_intro _ t (conj Ht E))). Qed.

    (* Richard's Claim 1: a pair in opposition leaves no fixed point in its subcube. *)
    Lemma claim1 : forall I i a b, NoDup I -> incl I js -> OutDeg1 I -> OppPair I i a b ->
      forall z, AgreeOff I z a -> IFixed Fv I z -> False.
    Proof.
      intros I i a b Hn HI Hod [[Hi Ha] [[_ Hb] [Hab Nab]]] z Hza Hz.
      assert (Hijs : In i js) by (apply HI; exact Hi).
      assert (G : forall c, (forall t, In t I -> Fv t c = get t (flip i c)) -> AgreeOff I z c ->
                   get i z = get i c -> False).
      { intros c Hc Hzc E. pose proof (nonexp I Hn HI Hod _ z c eq_refl Hzc) as N.
        unfold dF, dS in N.
        rewrite (cnt_ext I (fun t => Fv t z) (fun t => get t z) (fun t => Fv t c)
                   (fun t => xorb (get t c) (Nat.eqb i t))) in N.
        2: { intros t Ht. exact (Hz t Ht). }
        2: { intros t Ht. rewrite (Hc t Ht). apply get_flip. exact Hijs. }
        rewrite (cnt_sym I (fun t => get t z) (fun t => xorb (get t c) (Nat.eqb i t))) in N.
        rewrite (cnt_flip_eq I (fun t => get t c) (fun t => get t z) i Hn Hi (eq_sym E)) in N.
        rewrite (cnt_sym I (fun t => get t c)) in N. lia. }
      destruct (Bool.bool_dec (get i z) (get i a)) as [E | N].
      - exact (G a Ha Hza E).
      - apply (G b Hb).
        + exact (agree_trans I _ _ _ Hza Hab).
        + destruct (get i z), (get i a), (get i b); congruence.
    Qed.

    Definition Chain (I : list nat) (a : Sh) (l : list nat) : Prop :=
      forall k, k < length l -> Opp I (nth k l 0) (flips (firstn k l) a).

    Lemma firstn_snoc_nth : forall (l : list nat) k d, k < length l -> firstn (S k) l = firstn k l ++ [nth k l d].
    Proof.
      induction l as [| a l IH]; intros k d H; [simpl in H; lia |].
      destruct k as [| k]; [reflexivity |].
      change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l).
      change (firstn (S k) (a :: l)) with (a :: firstn k l).
      change (nth (S k) (a :: l) d) with (nth k l d).
      rewrite (IH k d) by (simpl in H; lia). reflexivity.
    Qed.

    Lemma firstn_app_le : forall (l m : list nat) k, k <= length l -> firstn k (l ++ m) = firstn k l.
    Proof.
      induction l as [| a l IH]; intros m k H; [simpl in H; destruct k; [reflexivity | lia] |].
      destruct k as [| k]; [reflexivity |]. simpl. rewrite IH by (simpl in H; lia). reflexivity.
    Qed.

    Lemma in_firstn : forall (l : list nat) k x, In x (firstn k l) -> In x l.
    Proof.
      induction l as [| a l IH]; intros [| k] x H; simpl in *; try tauto.
      destruct H as [H | H]; [left; exact H | right; exact (IH k x H)].
    Qed.

    Lemma nth_notin_firstn : forall (l : list nat) m k d, NoDup l -> m <= k -> k < length l ->
      ~ In (nth k l d) (firstn m l).
    Proof.
      induction l as [| a l IH]; intros m k d Hn Hm Hk; [simpl in Hk; lia |].
      inversion Hn as [| ? ? Ha Hl]; subst.
      destruct m as [| m]; [simpl; tauto |]. destruct k as [| k]; [lia |].
      simpl. intros [E | H].
      - apply Ha. rewrite E. apply nth_In. simpl in Hk. lia.
      - exact (IH m k d Hl ltac:(lia) ltac:(simpl in Hk; lia) H).
    Qed.

    Lemma flips_next : forall (l : list nat) a k, k < length l ->
      flips (firstn (S k) l) a = flip (nth k l 0) (flips (firstn k l) a).
    Proof. intros l a k Hk. rewrite (firstn_snoc_nth l k 0 Hk). apply flips_snoc. Qed.

    (* Richard's Claim 2, forward half: from a point of a pair in opposition, the synchronous
       orbit flips one new coordinate at a time. *)
    Lemma claim2 : forall I i a b, NoDup I -> incl I js -> OutDeg1 I -> Hesc I -> OppPair I i a b ->
      forall p, p <= length I -> exists l, length l = p /\ NoDup l /\ incl l I /\
        (0 < p -> nth 0 l 0 = i) /\ Chain I a l.
    Proof.
      intros I i a b Hn HI Hod He Hp.
      assert (Hpa := Hp). destruct Hpa as [[Hi Ha] _].
      induction p as [| p IH]; intros Hle.
      { exists []. split; [reflexivity | split; [constructor | split; [intros u [] |]]].
        split; [intros H; lia | intros k Hk; simpl in Hk; lia]. }
      destruct (IH ltac:(lia)) as (l & Hl & Hnd & Hinc & H0 & Hch).
      destruct p as [| p].
      { exists [i]. split; [reflexivity | split; [constructor; [intros [] | constructor] |]].
        split; [intros u [<- | []]; exact Hi |]. split; [intros _; reflexivity |].
        intros k Hk. simpl in Hk. assert (k = 0) by lia. subst k. exact (conj Hi Ha). }
      assert (Hlfull : firstn (length l) l = l) by apply firstn_all.
      set (m := nth p l 0). set (y := flips (firstn p l) a).
      assert (Ez : flips l a = flip m y).
      { unfold y, m. rewrite <- flips_next by lia. rewrite <- Hl, firstn_all. reflexivity. }
      set (z := flips l a).
      assert (Hy : Opp I m y) by (apply Hch; lia).
      assert (Hm : In m I) by (apply Hinc; apply nth_In; lia).
      assert (Hmjs : In m js) by (apply HI; exact Hm).
      assert (Az : AgreeOff I z a) by (apply agree_flips; assumption).
      assert (Azy : AgreeOff I z y) by (unfold z; rewrite Ez; apply agree_flip; assumption).
      assert (D1 : cnt I (fun t => Fv t z) (fun t => get t z) <= 1).
      { pose proof (nonexp I Hn HI Hod _ z y eq_refl Azy) as N.
        unfold dS in N. unfold z in N at 2. rewrite Ez in N. fold (dS I (flip m y) y) in N.
        rewrite (dS_flip_self I m y Hn Hm Hmjs) in N. unfold dF in N.
        rewrite (cnt_ext I (fun t => Fv t z) (fun t => Fv t z) (fun t => Fv t y) (fun t => get t z)) in N;
          [exact N | reflexivity |].
        intros t Ht. unfold z. rewrite Ez. exact (proj2 Hy t Ht). }
      assert (D0 : cnt I (fun t => Fv t z) (fun t => get t z) <> 0).
      { intro Q. apply (claim1 I i a b Hn HI Hod Hp z Az). intros t Ht. exact (cnt_zero I _ _ Q t Ht). }
      destruct (cnt_one I (fun t => Fv t z) (fun t => get t z) ltac:(lia)) as [j [Hj [Nj Oj]]].
      assert (Hjs : In j js) by (apply HI; exact Hj).
      assert (Hoz : Opp I j z).
      { split; [exact Hj |]. intros t Ht. rewrite get_flip by exact Hjs.
        destruct (Nat.eqb_spec j t) as [<- | N].
        - destruct (Fv j z), (get j z); simpl; congruence.
        - rewrite xorb_false_r. apply Oj; [exact Ht | intro E; apply N; symmetry; exact E]. }
      destruct (in_dec Nat.eq_dec j l) as [Hjl | Hjl].
      - exfalso. destruct (In_nth l j 0 Hjl) as [m' [Hm' Em']].
        set (g := flips (firstn m' l) a).
        assert (Hog : Opp I j g) by (unfold g; rewrite <- Em'; apply Hch; exact Hm').
        destruct (forallb (fun t => existsb (Nat.eqb t) l) I) eqn:Fa.
        + assert (Inc : incl I l).
          { intros t Ht. rewrite forallb_forall in Fa. pose proof (Fa t Ht) as Q.
            apply existsb_exists in Q. destruct Q as [u [Hu Eu]]. apply Nat.eqb_eq in Eu. subst u. exact Hu. }
          pose proof (NoDup_incl_length Hn Inc). lia.
        + destruct (forallb_false_ex _ I Fa) as [t [Ht Et]].
          assert (Htl : ~ In t l).
          { intro Q. assert (existsb (Nat.eqb t) l = true) by (apply existsb_exists; exists t; split; [exact Q | apply Nat.eqb_refl]).
            congruence. }
          assert (Hlj : incl l js) by (intros u Hu; apply HI; apply Hinc; exact Hu).
          assert (Hfj : incl (firstn m' l) js) by (intros u Hu; apply Hlj; exact (in_firstn l m' u Hu)).
          apply (He j g z).
          * split; [exact Hog | split; [exact Hoz | split]].
            -- apply (agree_trans I _ a); [apply agree_flips; [exact HI | intros u Hu; apply Hinc; exact (in_firstn l m' u Hu)] |].
               apply agree_sym. exact Az.
            -- unfold g, z. rewrite !get_flips by assumption.
               rewrite (pw_in j l Hnd Hjl). rewrite pw_notin by (rewrite <- Em'; apply nth_notin_firstn; [exact Hnd | lia | exact Hm']).
               destruct (get j a); discriminate.
          * exists t. split; [exact Ht |]. unfold g, z. rewrite !get_flips by assumption.
            rewrite (pw_notin t l Htl), pw_notin by (intro Q; apply Htl; exact (in_firstn l m' t Q)). reflexivity.
      - exists (l ++ [j]). split; [rewrite len_snoc, Hl; reflexivity |].
        split; [exact (nodup_snoc l j Hnd Hjl) |].
        split; [intros u Hu; apply in_app_or in Hu; destruct Hu as [Hu | [<- | []]]; [apply Hinc; exact Hu | exact Hj] |].
        split; [intros _; rewrite app_nth1 by lia; apply H0; lia |].
        intros k Hk. rewrite len_snoc in Hk. destruct (Nat.eq_dec k (length l)) as [-> | Nk].
        + rewrite firstn_app_le by lia. rewrite firstn_all, nth_middle. exact Hoz.
        + rewrite firstn_app_le by lia. rewrite app_nth1 by lia. apply Hch. lia.
    Qed.

    Lemma full_perm : forall (I l : list nat), NoDup I -> NoDup l -> incl l I -> length l = length I -> incl I l.
    Proof.
      intros I l HnI Hnl Hinc Hlen t Ht. destruct (in_dec Nat.eq_dec t l) as [H | H]; [exact H | exfalso].
      assert (Inc : incl l (rm t I)).
      { intros u Hu. apply rm_In. split; [apply Hinc; exact Hu | intro E; subst; contradiction]. }
      pose proof (NoDup_incl_length Hnl Inc). pose proof (rm_length t I Ht). lia.
    Qed.

    Lemma orbit_end : forall I i a b l, incl I js -> OppPair I i a b -> (forall t, In t I -> get t a <> get t b) ->
      NoDup l -> incl l I -> incl I l -> flips l a = b.
    Proof.
      intros I i a b l HI [_ [_ [Hab _]]] Hanti Hn Hinc Hinc' . apply sh_ext. intros t Ht.
      rewrite get_flips by (intros u Hu; apply HI; apply Hinc; exact Hu).
      destruct (in_dec Nat.eq_dec t I) as [HtI | HtI].
      - rewrite (pw_in t l Hn (Hinc' t HtI)). pose proof (Hanti t HtI). destruct (get t a), (get t b); simpl; congruence.
      - rewrite pw_notin by (intro Q; apply HtI; apply Hinc; exact Q). rewrite xorb_false_r. exact (Hab t Ht HtI).
    Qed.

    (* Richard's Claim 2, backward half: the two orbits stay antipodal and flip the same
       coordinates, so every point of the orbit is again in a pair in opposition. *)
    Lemma partners : forall I i a b l l', NoDup I -> incl I js -> OutDeg1 I -> OppPair I i a b ->
      (forall t, In t I -> get t a <> get t b) ->
      length l = length I -> incl l I -> Chain I a l -> length l' = length I -> incl l' I -> Chain I b l' ->
      flips l a = b -> flips l' b = a ->
      forall k, k < length I -> nth k l 0 = nth k l' 0 /\
        OppPair I (nth k l 0) (flips (firstn k l) a) (flips (firstn k l') b).
    Proof.
      intros I i a b l l' Hn HI Hod Hp Hanti Hl Hinc Hch Hl' Hinc' Hch' Ea Eb.
      set (n := length I).
      assert (Ag : forall k, AgreeOff I (flips (firstn k l) a) (flips (firstn k l') b)).
      { intros k. apply (agree_trans I _ a); [apply agree_flips; [exact HI | intros u Hu; apply Hinc; exact (in_firstn l k u Hu)] |].
        apply (agree_trans I _ b); [exact (proj1 (proj2 (proj2 Hp))) |].
        apply agree_sym. apply agree_flips; [exact HI | intros u Hu; apply Hinc'; exact (in_firstn l' k u Hu)]. }
      assert (Q : forall d, d <= n -> dS I (flips (firstn (n - d) l) a) (flips (firstn (n - d) l') b) = n).
      { induction d as [| d IH]; intros Hd.
        - rewrite Nat.sub_0_r. unfold n.
          replace (firstn (length I) l) with l by (rewrite <- Hl; symmetry; apply firstn_all).
          replace (firstn (length I) l') with l' by (rewrite <- Hl'; symmetry; apply firstn_all).
          rewrite Ea, Eb.
          unfold dS. apply cnt_all. intros t Ht E. apply (Hanti t Ht). symmetry. exact E.
        - set (k := n - S d). assert (Hk : k < length l) by (unfold k; lia).
          assert (Hk' : k < length l') by (unfold k; lia).
          assert (Ek : n - d = S k) by (unfold k; lia).
          specialize (IH ltac:(lia)). rewrite Ek in IH.
          pose proof (nonexp I Hn HI Hod _ _ _ eq_refl (Ag k)) as N.
          assert (F : dF I (flips (firstn k l) a) (flips (firstn k l') b) = n).
          { rewrite <- IH. rewrite (flips_next l a k Hk), (flips_next l' b k Hk'). unfold dF, dS. apply cnt_ext.
            - intros t Ht. exact (proj2 (Hch k Hk) t Ht).
            - intros t Ht. exact (proj2 (Hch' k Hk') t Ht). }
          pose proof (cnt_le I (fun t => get t (flips (firstn k l) a)) (fun t => get t (flips (firstn k l') b))).
          assert (En : n = length I) by reflexivity. unfold dS in *. lia. }
      assert (Q' : forall k, k <= n -> dS I (flips (firstn k l) a) (flips (firstn k l') b) = n).
      { intros k Hk. replace k with (n - (n - k)) by lia. apply Q. lia. }
      intros k Hk.
      assert (Hkl : k < length l) by lia. assert (Hkl' : k < length l') by lia.
      pose proof (Hch k Hkl) as [Hm Hom]. pose proof (Hch' k Hkl') as [Hm' Hom'].
      assert (Anti : forall t, In t I -> get t (flips (firstn k l) a) <> get t (flips (firstn k l') b))
        by (apply cnt_full; exact (Q' k ltac:(lia))).
      assert (Same : nth k l 0 = nth k l' 0).
      { destruct (Nat.eq_dec (nth k l 0) (nth k l' 0)) as [E | N]; [exact E | exfalso].
        pose proof (cnt_full I _ _ (Q' (S k) ltac:(lia)) (nth k l 0) Hm) as C. apply C.
        rewrite (flips_next l a k Hkl), (flips_next l' b k Hkl').
        rewrite !get_flip by (apply HI; assumption).
        rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq (nth k l' 0) (nth k l 0))) by (intro E; apply N; symmetry; exact E).
        pose proof (Anti _ Hm). destruct (get (nth k l 0) (flips (firstn k l) a)), (get (nth k l 0) (flips (firstn k l') b));
          simpl; congruence. }
      split; [exact Same |]. split; [exact (conj Hm Hom) |]. split; [rewrite Same; exact (conj Hm' Hom') |].
      split; [exact (Ag k) | exact (Anti _ Hm)].
    Qed.

    (* Richard's Claim 3: the opposition coordinate has at most one predecessor. *)
    Lemma claim3 : forall I j g h, NoDup I -> incl I js -> OutDeg1 I -> Hesc I -> OppPair I j g h ->
      forall u1 u2, In u1 I -> In u2 I -> larc Fv g u1 j = true -> larc Fv g u2 j = true -> u1 = u2.
    Proof.
      intros I j g h Hn HI Hod He Hp u1 u2 H1 H2 A1 A2.
      destruct (claim2 I j g h Hn HI Hod He Hp (length I) (le_n _)) as (l & Hl & Hnd & Hinc & H0 & Hch).
      assert (Hinc' : incl I l) by exact (full_perm I l Hn Hnd Hinc Hl).
      destruct Hp as [[Hj Hg] _].
      assert (Hjs : In j js) by (apply HI; exact Hj).
      set (lst := nth (length l - 1) l 0).
      assert (Key : forall u, In u I -> larc Fv g u j = true -> u <> lst -> False).
      { intros u Hu Au Nu.
        assert (Hujs : In u js) by (apply HI; exact Hu).
        destruct (In_nth l u 0 (Hinc' u Hu)) as [m [Hm Em]].
        assert (Hml : m < length l - 1).
        { destruct (Nat.eq_dec m (length l - 1)) as [E | N]; [| lia]. exfalso. apply Nu. unfold lst. rewrite <- E. symmetry. exact Em. }
        set (g' := flip u g).
        assert (Og' : Opp I u g').
        { split; [exact Hu |]. intros t Ht. unfold g'. rewrite flip_flip by exact Hujs.
          destruct (Nat.eq_dec t j) as [-> | Ntj].
          - unfold larc in Au. rewrite (Hg j Hj), get_flip in Au by exact Hjs. rewrite Nat.eqb_refl in Au.
            destruct (Fv j (flip u g)), (get j g); simpl in Au; congruence.
          - assert (Lf : larc Fv g u t = false).
            { destruct (larc Fv g u t) eqn:L; [| reflexivity]. exfalso. apply Ntj.
              exact (od_unique I g u t j Hod Hu Ht Hj L Au). }
            rewrite (sink_flip Fv g u t Lf), (Hg t Ht), get_flip by exact Hjs.
            rewrite (proj2 (Nat.eqb_neq j t)) by (intro E; apply Ntj; symmetry; exact E). apply xorb_false_r. }
        set (am := flips (firstn m l) g).
        assert (Oam : Opp I u am) by (unfold am; rewrite <- Em; apply Hch; exact Hm).
        assert (Hfj : incl (firstn m l) js) by (intros v Hv; apply HI; apply Hinc; exact (in_firstn l m v Hv)).
        assert (Hlst : In lst I) by (apply Hinc; apply nth_In; lia).
        apply (He u am g').
        - split; [exact Oam | split; [exact Og' | split]].
          + apply (agree_trans I _ g); [apply agree_flips; [exact HI | intros v Hv; apply Hinc; exact (in_firstn l m v Hv)] |].
            apply agree_sym. apply agree_flip; assumption.
          + unfold am, g'. rewrite get_flips by exact Hfj. rewrite get_flip by exact Hujs.
            rewrite pw_notin by (rewrite <- Em; apply nth_notin_firstn; [exact Hnd | lia | exact Hm]).
            rewrite Nat.eqb_refl. destruct (get u g); discriminate.
        - exists lst. split; [exact Hlst |]. unfold am, g'. rewrite get_flips by exact Hfj. rewrite get_flip by exact Hujs.
          rewrite pw_notin by (apply nth_notin_firstn; [exact Hnd | lia | lia]).
          rewrite (proj2 (Nat.eqb_neq u lst)) by exact Nu. reflexivity. }
      destruct (Nat.eq_dec u1 u2) as [E | N]; [exact E | exfalso].
      destruct (Nat.eq_dec u1 lst) as [E1 | N1].
      - apply (Key u2 H2 A2). intro E2. apply N. rewrite E1, E2. reflexivity.
      - exact (Key u1 H1 A1 N1).
    Qed.

    (* The four-point step of Richard's Claim 4. *)
    Lemma four_point : forall I x a b c d, incl I js -> OutDeg1 I -> In a I -> In b I -> In c I -> In d I -> b <> d ->
      larc Fv x a b = true -> larc Fv x c d = true -> larc Fv (flip c x) a b = false ->
      forall t, In t I -> Fv t (flip a (flip c x)) = Fv t x.
    Proof.
      intros I x a b c d HI Hod Ha Hb Hc Hd Nbd Aab Acd Nab t Ht.
      assert (Hajs : In a js) by (apply HI; exact Ha). assert (Hcjs : In c js) by (apply HI; exact Hc).
      assert (E1 : Fv b (flip c x) = Fv b x).
      { destruct (Bool.bool_dec (Fv b (flip c x)) (Fv b x)) as [E | N]; [exact E | exfalso].
        apply Nbd. apply (od_unique I x c b d Hod Hc Hb Hd); [| exact Acd].
        unfold larc. destruct (Fv b (flip c x)), (Fv b x); simpl; congruence. }
      assert (E2 : Fv b (flip a (flip c x)) = Fv b (flip c x)) by exact (sink_flip Fv (flip c x) a b Nab).
      assert (Acb : larc Fv (flip a x) c b = true).
      { unfold larc in *. rewrite (flip_comm c a x Hcjs Hajs), E2, E1.
        destruct (Fv b (flip a x)), (Fv b x); simpl in *; congruence. }
      destruct (Nat.eq_dec t b) as [-> | Ntb].
      - rewrite E2. exact E1.
      - assert (L1 : larc Fv (flip a x) c t = false).
        { destruct (larc Fv (flip a x) c t) eqn:L; [| reflexivity]. exfalso. apply Ntb.
          exact (od_unique I (flip a x) c t b Hod Hc Ht Hb L Acb). }
        assert (L2 : larc Fv x a t = false).
        { destruct (larc Fv x a t) eqn:L; [| reflexivity]. exfalso. apply Ntb.
          exact (od_unique I x a t b Hod Ha Ht Hb L Aab). }
        rewrite (flip_comm a c x Hajs Hcjs), (sink_flip Fv (flip a x) c t L1). exact (sink_flip Fv x a t L2).
    Qed.

    Lemma pathOK_nth : forall ar (l : list nat) d,
      (forall k, S k < length l -> ar (nth k l d) (nth (S k) l d) = true) -> pathOK ar l = true.
    Proof.
      intros ar. induction l as [| a l IH]; intros d H; [reflexivity |].
      destruct l as [| b l]; [reflexivity |].
      change (pathOK ar (a :: b :: l)) with (ar a b && pathOK ar (b :: l)).
      pose proof (H 0 ltac:(simpl; lia)) as H0. simpl in H0. rewrite H0. simpl.
      apply (IH d). intros k Hk. exact (H (S k) ltac:(simpl in *; lia)).
    Qed.

    Lemma last_nth : forall (l : list nat) d, last l d = nth (length l - 1) l d.
    Proof.
      induction l as [| a l IH]; intros d; [reflexivity |].
      destruct l as [| b l]; [reflexivity |].
      rewrite last_cons_ne by discriminate. rewrite IH.
      replace (length (a :: b :: l) - 1) with (S (length (b :: l) - 1)) by (simpl; lia). reflexivity.
    Qed.

    Lemma cyc_ok_cons : forall ar a r, cyc_ok ar (a :: r) = ar (last (a :: r) a) a && pathOK ar (a :: r).
    Proof. intros ar a r. unfold cyc_ok, cpairs. cbn [cpf forallb fst snd]. rewrite forallb_cpf. reflexivity. Qed.

    (* Richard's Claim 4 and Lemma 2: a pair in opposition, with every pair in opposition
       antipodal, forces a negative cycle (through every coordinate) in one local graph. *)
    Lemma opp_core : forall I i a b, NoDup I -> incl I js -> OutDeg1 I -> Hesc I -> NoLocalNeg Fv I ->
      OppPair I i a b -> False.
    Proof.
      intros I i a b Hn HI Hod He Hneg Hp.
      pose proof (pair_anti I i a b He Hp) as Hanti.
      destruct (claim2 I i a b Hn HI Hod He Hp (length I) (le_n _)) as (l & Hl & Hnd & Hinc & H0 & Hch).
      destruct (claim2 I i b a Hn HI Hod He (opp_sym I i a b Hp) (length I) (le_n _)) as (l' & Hl' & Hnd' & Hinc' & _ & Hch').
      assert (Pl : incl I l) by exact (full_perm I l Hn Hnd Hinc Hl).
      assert (Pl' : incl I l') by exact (full_perm I l' Hn Hnd' Hinc' Hl').
      assert (Ea : flips l a = b) by exact (orbit_end I i a b l HI Hp Hanti Hnd Hinc Pl).
      assert (Eb : flips l' b = a).
      { apply (orbit_end I i b a l' HI (opp_sym I i a b Hp)); [| exact Hnd' | exact Hinc' | exact Pl'].
        intros t Ht E. apply (Hanti t Ht). symmetry. exact E. }
      pose proof (partners I i a b l l' Hn HI Hod Hp Hanti Hl Hinc Hch Hl' Hinc' Hch' Ea Eb) as Hpart.
      set (n := length I). destruct Hp as [[Hi Ha] [[_ Hb] _]].
      assert (Hn1 : 1 <= n) by (unfold n; destruct I as [| u I]; [destruct Hi | simpl; lia]).
      set (A := fun k => flips (firstn k l) a). set (L := fun k => nth k l 0).
      assert (HA : forall k, k < n -> A (S k) = flip (L k) (A k)) by (intros k Hk; apply flips_next; lia).
      assert (HO : forall k, k < n -> Opp I (L k) (A k)) by (intros k Hk; apply Hch; lia).
      assert (HL : forall k, k < n -> In (L k) I) by (intros k Hk; apply Hinc; apply nth_In; lia).
      assert (HLjs : forall k, k < n -> In (L k) js) by (intros k Hk; apply HI; apply HL; exact Hk).
      assert (HLd : forall k k', k < n -> k' < n -> k <> k' -> L k <> L k').
      { intros k k' Hk Hk' N E. apply N. exact (proj1 (NoDup_nth l 0) Hnd k k' ltac:(lia) ltac:(lia) E). }
      assert (HAn : A n = b).
      { unfold A. change n with (length I).
        replace (firstn (length I) l) with l by (rewrite <- Hl; symmetry; apply firstn_all). exact Ea. }
      assert (Fnext : forall k t, k < n -> In t I -> Fv t (A k) = get t (A (S k))).
      { intros k t Hk Ht. rewrite (HA k Hk). exact (proj2 (HO k Hk) t Ht). }
      assert (Fself : forall k, k < n -> Fv (L k) (A k) = negb (get (L k) (A k))).
      { intros k Hk. rewrite (proj2 (HO k Hk) (L k) (HL k Hk)), get_flip by exact (HLjs k Hk).
        rewrite Nat.eqb_refl. destruct (get (L k) (A k)); reflexivity. }
      assert (Ar : forall k, S k < n -> larc Fv (A k) (L k) (L (S k)) = true).
      { intros k Hk. unfold larc. fold (A (S k)). rewrite <- (HA k ltac:(lia)).
        rewrite (Fnext k (L (S k)) ltac:(lia) (HL (S k) Hk)), (Fself (S k) Hk).
        destruct (get (L (S k)) (A (S k))); reflexivity. }
      assert (Br : forall k, S k < n -> larc Fv (A (S k)) (L k) (L (S k)) = true).
      { intros k Hk. unfold larc. rewrite (HA k ltac:(lia)), flip_flip by exact (HLjs k ltac:(lia)).
        rewrite <- (HA k ltac:(lia)).
        rewrite (Fnext k (L (S k)) ltac:(lia) (HL (S k) Hk)), (Fself (S k) Hk).
        destruct (get (L (S k)) (A (S k))); reflexivity. }
      assert (Main : forall q k, k < q -> q < n -> larc Fv (A q) (L k) (L (S k)) = true).
      { induction q as [| q IH]; intros k Hkq Hq; [lia |].
        destruct (Nat.eq_dec k q) as [-> | Nkq]; [exact (Br q Hq) |].
        destruct (larc Fv (A (S q)) (L k) (L (S k))) eqn:Lb; [reflexivity | exfalso].
        assert (Ax : larc Fv (A q) (L k) (L (S k)) = true) by (apply IH; lia).
        assert (Nbd : L (S k) <> L (S q)) by (apply HLd; lia).
        assert (Nac : L k <> L q) by (apply HLd; lia).
        rewrite (HA q ltac:(lia)) in Lb.
        pose proof (four_point I (A q) (L k) (L (S k)) (L q) (L (S q)) HI Hod (HL k ltac:(lia)) (HL (S k) ltac:(lia))
                      (HL q ltac:(lia)) (HL (S q) Hq) Nbd Ax (Ar q Hq) Lb) as FP.
        rewrite <- (HA q ltac:(lia)) in FP.
        assert (Ad : larc Fv (A (S q)) (L k) (L (S q)) = true).
        { unfold larc. rewrite (FP (L (S q)) (HL (S q) Hq)), (Fnext q (L (S q)) ltac:(lia) (HL (S q) Hq)), (Fself (S q) Hq).
          destruct (get (L (S q)) (A (S q))); reflexivity. }
        destruct (Hpart (S q) Hq) as [_ Pq].
        apply Nac. exact (claim3 I (L (S q)) (A (S q)) _ Hn HI Hod He Pq (L k) (L q)
                            (HL k ltac:(lia)) (HL q ltac:(lia)) Ad (Br q Hq)). }
      set (x := A (n - 1)).
      assert (Close : larc Fv x (L (n - 1)) (L 0) = true).
      { unfold larc, x. rewrite <- (HA (n - 1) ltac:(lia)). replace (S (n - 1)) with n by lia. rewrite HAn.
        rewrite (Fnext (n - 1) (L 0) ltac:(lia) (HL 0 ltac:(lia))). replace (S (n - 1)) with n by lia. rewrite HAn.
        assert (L0 : L 0 = i) by (apply H0; lia). rewrite L0, (Hb i Hi), get_flip by (apply HI; exact Hi).
        rewrite Nat.eqb_refl. destruct (get i b); reflexivity. }
      apply (Hneg x l Hinc). split.
      - split; [intro E; rewrite E in Hl; simpl in Hl; lia | split; [exact Hnd |]].
        destruct l as [| a0 r]; [simpl in Hl; lia |]. rewrite cyc_ok_cons. apply andb_true_intro. split.
        + assert (Lst : last (a0 :: r) a0 = L (n - 1)).
          { rewrite last_nth. unfold L. rewrite Hl. apply nth_indep. rewrite Hl. lia. }
          rewrite Lst. exact Close.
        + apply (pathOK_nth _ _ 0). intros k Hk. rewrite Hl in Hk. apply (Main (n - 1) k); lia.
      - apply (opp_csign I (L (n - 1)) x l HI (HO (n - 1) ltac:(lia)) Hinc Hnd). apply nth_In. lia.
    Qed.

    Lemma nodup_rm : forall k l, NoDup l -> NoDup (rm k l).
    Proof.
      intros k. induction l as [| a l IH]; intros H; [constructor |]. inversion H; subst. unfold rm in *. simpl.
      destruct (negb (Nat.eqb a k)); [constructor; [| exact (IH H3)] | exact (IH H3)].
      intro Q. apply filter_In in Q. exact (H2 (proj1 Q)).
    Qed.

    Lemma filter_rm_le : forall (f : nat -> bool) k l, length (filter f (rm k l)) <= length (filter f l).
    Proof.
      intros f k. induction l as [| a l IH]; [reflexivity |]. unfold rm in *. simpl.
      destruct (negb (Nat.eqb a k)); simpl; destruct (f a); simpl; lia.
    Qed.

    Lemma opp_restrict : forall I j g h t, OppPair I j g h -> In t I -> get t g = get t h -> OppPair (rm t I) j g h.
    Proof.
      intros I j g h t [[Hj Hg] [[_ Hh] [Agh Ngh]]] Ht Et.
      assert (Ntj : j <> t) by (intro E; subst; contradiction).
      assert (Hjr : In j (rm t I)) by (apply rm_In; split; assumption).
      split; [split; [exact Hjr | intros s Hs; exact (Hg s (proj1 (proj1 (rm_In t I s) Hs)))] |].
      split; [split; [exact Hjr | intros s Hs; exact (Hh s (proj1 (proj1 (rm_In t I s) Hs)))] |].
      split; [| exact Ngh]. intros s Hs Hn. destruct (Nat.eq_dec s t) as [-> | N]; [exact Et |].
      apply Agh; [exact Hs |]. intro Q. apply Hn. apply rm_In. split; assumption.
    Qed.

    (* Richard 2011, Lemma 2: under out-degree at most one and no local negative cycle inside I,
       no two points of a subcube are in opposition. *)
    Lemma opp_false : forall n I, length I <= n -> NoDup I -> incl I js -> OutDeg1 I -> NoLocalNeg Fv I ->
      forall i a b, OppPair I i a b -> False.
    Proof.
      induction n as [| n IH]; intros I Hl Hn HI Hod Hneg i a b Hp.
      - destruct I as [| u I]; [exact (proj1 (proj1 Hp)) | simpl in Hl; lia].
      - apply (opp_core I i a b Hn HI Hod); [| exact Hneg | exact Hp].
        intros j g h Hq [t [Ht Et]].
        apply (IH (rm t I) ltac:(pose proof (rm_length t I Ht); lia) (nodup_rm t I Hn)
                  (fun u Hu => HI u (proj1 (proj1 (rm_In t I u) Hu))) ) with (i := j) (a := g) (b := h).
        + intros x u Hu. eapply Nat.le_trans; [apply filter_rm_le |]. apply Hod. exact (proj1 (proj1 (rm_In t I u) Hu)).
        + intros x c Hc. apply Hneg. intros u Hu. exact (proj1 (proj1 (rm_In t I u) (Hc u Hu))).
        + exact (opp_restrict I j g h t Hq Ht Et).
    Qed.

    (* Richard 2011, Theorem 3, with paths: out-degree at most one and no negative cycle in any
       local graph inside I; then from every state an update word over I reaches a point fixed
       on I. *)
    Theorem t3_path : forall n I, length I <= n -> NoDup I -> incl I js -> NoLocalNeg Fv I -> OutDeg1 I ->
      forall x, exists w, incl w I /\ IFixed Fv I (xw w x).
    Proof.
      induction n as [| n IH]; intros I Hl Hn HI Hneg Hod x.
      { destruct I as [| u I]; [exists []; split; [intros u [] | intros t []] | simpl in Hl; lia]. }
      destruct I as [| k I0]; [exists []; split; [intros u [] | intros t []] |].
      inversion Hn as [| ? ? Hk0 Hn0]; subst.
      assert (Hkjs : In k js) by (apply HI; left; reflexivity).
      assert (Sub : forall u, In u I0 -> In u (k :: I0)) by (intros u Hu; right; exact Hu).
      assert (IH0 : forall z, exists w, incl w I0 /\ IFixed Fv I0 (xw w z)).
      { apply IH; [simpl in Hl; lia | exact Hn0 | intros u Hu; apply HI; right; exact Hu | |].
        - intros z c Hc. apply Hneg. intros u Hu. right. exact (Hc u Hu).
        - intros z u Hu. eapply Nat.le_trans; [| apply (Hod z u (Sub u Hu))]. simpl.
          destruct (larc Fv z u k); simpl; lia. }
      assert (Nk : forall w, incl w I0 -> ~ In k w) by (intros w Hw Q; exact (Hk0 (Hw k Q))).
      assert (Comb : forall z, IFixed Fv I0 z -> Fv k z = get k z -> IFixed Fv (k :: I0) z).
      { intros z Hz E t [<- | Ht]; [exact E | exact (Hz t Ht)]. }
      destruct (IH0 x) as [w1 [Hw1 F1]].
      destruct (Bool.bool_dec (Fv k (xw w1 x)) (get k (xw w1 x))) as [E1 | N1].
      { exists w1. split; [intros u Hu; right; exact (Hw1 u Hu) | apply Comb; assumption]. }
      destruct (IH0 (ru k (xw w1 x))) as [w2 [Hw2 F2]].
      destruct (Bool.bool_dec (Fv k (xw w2 (ru k (xw w1 x)))) (get k (xw w2 (ru k (xw w1 x))))) as [E3 | N3].
      { exists (w1 ++ k :: w2). split.
        - intros u Hu. apply in_app_or in Hu. destruct Hu as [Hu | [<- | Hu]];
            [right; exact (Hw1 u Hu) | left; reflexivity | right; exact (Hw2 u Hu)].
        - rewrite (xr_app bool Sh js set Fv w1 (k :: w2)), (xr_cons Fv). apply Comb; assumption. }
      exfalso.
      assert (OppOf : forall z, IFixed Fv I0 z -> Fv k z <> get k z -> Opp (k :: I0) k z).
      { intros z Hz Nz. split; [left; reflexivity |]. intros t Ht. rewrite get_flip by exact Hkjs.
        destruct (Nat.eqb_spec k t) as [<- | N].
        - destruct (Fv k z), (get k z); simpl; congruence.
        - rewrite xorb_false_r. destruct Ht as [E | Ht]; [congruence | exact (Hz t Ht)]. }
      apply (opp_false (length (k :: I0)) (k :: I0) (le_n _) Hn HI Hod Hneg k (xw w1 x) (xw w2 (ru k (xw w1 x)))).
      split; [exact (OppOf _ F1 N1) | split; [exact (OppOf _ F2 N3) | split]].
      - intros s Hs Hns.
        assert (Ns : s <> k) by (intro E; apply Hns; left; symmetry; exact E).
        rewrite (xr_out Fv w2 _ s) by (intro Q; apply Hns; right; exact (Hw2 s Q)).
        rewrite (get_rupd_other bool Sh js get set get_set_neq Fv k s _ Ns). reflexivity.
      - rewrite (xr_out Fv w2 _ k (Nk w2 Hw2)), (get_rupd_same bool Sh js get set get_set_eq Fv k _ Hkjs).
        intro E. apply N1. symmetry. exact E.
    Qed.

    (* Local settlement, corrected (Richard 2011, Theorem 3, with the reachability form of
       Ruet 2017, Remark 2): a fixed point exists, it is reached from every state by an update
       word, and E's Settlement holds from every start. *)
    Theorem richard_t3 : NoDup js -> NoLocalNeg Fv js -> OutDeg1 js ->
      (forall s0, exists w, Forall (r_ok js) w /\ Fsync bool Sh js set Fv (xw w s0) = xw w s0) /\
      (forall s0, Settlement ru (r_ok js) (r_flush js) (r_settled bool Sh js set Fv) s0).
    Proof.
      intros Hn Hneg Hod.
      assert (H : forall s, exists w, incl w js /\ IFixed Fv js (xw w s))
        by exact (t3_path (length js) js (le_n _) Hn (incl_refl _) Hneg Hod).
      split; [| exact (settle_from_paths Fv H)].
      intros s0. destruct (H s0) as [w [Hw Hf]]. exists w. split.
      - apply Forall_forall. intros a Ha. exact (Hw a Ha).
      - apply (fixed_iff Fv). exact Hf.
    Qed.
  End Opp.
End Lens.

(* ============================================================================================ *)
(* Part 2. A sound decision procedure for finite instances.                                     *)
(* ============================================================================================ *)

Definition chk {Sh : Type} (get : nat -> Sh -> bool) (set : nat -> bool -> Sh -> Sh) (sts : list Sh)
  (vs : list nat) (Fv : nat -> Sh -> bool) (bad : list nat -> bool -> bool) : bool :=
  forallb (fun x => forallb (fun c => match c with
                                      | [] => true
                                      | _ => negb (cyc_ok (larc Sh get set Fv x) c && bad c (csign (lneg Sh get Fv x) c))
                                      end)
                      (nl (length vs) vs)) sts.

Lemma chk_sound : forall (Sh : Type) get set sts vs Fv bad, (forall s : Sh, In s sts) ->
  chk get set sts vs Fv bad = true ->
  forall x c, incl c vs -> IsCycle (larc Sh get set Fv x) c -> bad c (csign (lneg Sh get Fv x) c) = false.
Proof.
  intros Sh get set sts vs Fv bad Hall H x c Hc [Hne [Hn Hok]].
  unfold chk in H. rewrite forallb_forall in H. pose proof (H x (Hall x)) as H1.
  rewrite forallb_forall in H1.
  pose proof (H1 c (nl_complete _ vs c Hn Hc (NoDup_incl_length Hn Hc))) as H2.
  destruct c as [| a l]; [congruence |].
  rewrite Hok in H2. destruct (bad (a :: l) _); [discriminate H2 | reflexivity].
Qed.

Lemma chk_neg : forall (Sh : Type) get set sts vs Fv, (forall s : Sh, In s sts) ->
  chk get set sts vs Fv (fun _ h => h) = true -> NoLocalNeg Sh get set Fv vs.
Proof.
  intros Sh get set sts vs Fv Hall H x c Hc [Hcy Hs].
  pose proof (chk_sound Sh get set sts vs Fv _ Hall H x c Hc Hcy) as E. simpl in E. congruence.
Qed.

Lemma chk_pos : forall (Sh : Type) get set sts vs Fv, (forall s : Sh, In s sts) ->
  chk get set sts vs Fv (fun _ h => negb h) = true -> NoLocalPos Sh get set Fv vs.
Proof.
  intros Sh get set sts vs Fv Hall H x c Hc [Hcy Hs].
  pose proof (chk_sound Sh get set sts vs Fv _ Hall H x c Hc Hcy) as E. simpl in E. rewrite Hs in E. discriminate E.
Qed.

Lemma chk_none : forall (Sh : Type) get set sts vs Fv, (forall s : Sh, In s sts) ->
  chk get set sts vs Fv (fun _ _ => true) = true -> NoLocalCycle Sh get set Fv vs.
Proof.
  intros Sh get set sts vs Fv Hall H x c Hc Hcy.
  pose proof (chk_sound Sh get set sts vs Fv _ Hall H x c Hc Hcy) as E. discriminate E.
Qed.

Lemma chk_through : forall (Sh : Type) get set sts vs Fv k, (forall s : Sh, In s sts) ->
  chk get set sts vs Fv (fun c h => negb h && negb (existsb (Nat.eqb k) c)) = true ->
  forall x c, incl c vs -> PosCycleAt Sh get set Fv x c -> In k c.
Proof.
  intros Sh get set sts vs Fv k Hall H x c Hc [Hcy Hs].
  pose proof (chk_sound Sh get set sts vs Fv _ Hall H x c Hc Hcy) as E. rewrite Hs in E. simpl in E.
  destruct (existsb (Nat.eqb k) c) eqn:X; [| discriminate E].
  apply existsb_exists in X. destruct X as [u [Hu Eu]]. apply Nat.eqb_eq in Eu. subst u. exact Hu.
Qed.

(* Out-degree at most one in every local graph (OutDeg1, Richard's property P, equivalent to
   non-expansiveness for the Hamming distance: outdeg_nonexpansive), decided on finite instances. *)
Definition outdeg_b {Sh : Type} (get : nat -> Sh -> bool) (set : nat -> bool -> Sh -> Sh) (sts : list Sh)
  (vs : list nat) (Fv : nat -> Sh -> bool) : bool :=
  forallb (fun x => forallb (fun j => Nat.leb (length (filter (larc Sh get set Fv x j) vs)) 1) vs) sts.

Lemma outdeg_sound : forall (Sh : Type) get set sts vs Fv, (forall s : Sh, In s sts) ->
  outdeg_b get set sts vs Fv = true -> OutDeg1 Sh get set Fv vs.
Proof.
  intros Sh get set sts vs Fv Hall H x j Hj. unfold outdeg_b in H. rewrite forallb_forall in H.
  pose proof (H x (Hall x)) as H1. rewrite forallb_forall in H1. apply Nat.leb_le. exact (H1 j Hj).
Qed.

(* ----- Boolean vectors of length n: the lens on seq 0 n ----- *)

Fixpoint BV (n : nat) : Type := match n with O => unit | S m => (bool * BV m)%type end.

Fixpoint bget (n : nat) : nat -> BV n -> bool :=
  match n return nat -> BV n -> bool with
  | O => fun _ _ => false
  | S m => fun j s => match j with O => fst s | S j' => bget m j' (snd s) end
  end.

Fixpoint bset (n : nat) : nat -> bool -> BV n -> BV n :=
  match n return nat -> bool -> BV n -> BV n with
  | O => fun _ _ s => s
  | S m => fun j b s => match j with O => (b, snd s) | S j' => (fst s, bset m j' b (snd s)) end
  end.

Fixpoint benum (n : nat) : list (BV n) :=
  match n return list (BV n) with
  | O => [tt]
  | S m => flat_map (fun s => [(false, s); (true, s)]) (benum m)
  end.

Lemma benum_all : forall n (s : BV n), In s (benum n).
Proof.
  induction n as [| m IH]; intros s; simpl in *.
  - destruct s. left. reflexivity.
  - destruct s as [b s]. apply in_flat_map. exists s. split; [apply IH |]. destruct b; simpl; auto.
Qed.

Lemma bget_bset_eq : forall n j b s, In j (seq 0 n) -> bget n j (bset n j b s) = b.
Proof.
  induction n as [| m IH]; intros j b s Hj; [destruct Hj |].
  destruct j as [| j]; [reflexivity |]. simpl. apply IH.
  apply in_seq in Hj. apply in_seq. lia.
Qed.

Lemma bget_bset_neq : forall n j k b s, k <> j -> bget n k (bset n j b s) = bget n k s.
Proof.
  induction n as [| m IH]; intros j k b s H; [reflexivity |].
  destruct j as [| j], k as [| k]; simpl; try reflexivity; [congruence |]. apply IH. congruence.
Qed.

Lemma bext : forall n (s t : BV n), (forall j, In j (seq 0 n) -> bget n j s = bget n j t) -> s = t.
Proof.
  induction n as [| m IH]; intros s t H; simpl in *.
  - destruct s, t. reflexivity.
  - destruct s as [a s], t as [b t]. f_equal.
    + exact (H 0 (or_introl eq_refl)).
    + apply IH. intros j Hj. apply (H (S j)). right. apply in_seq. apply in_seq in Hj. lia.
Qed.

Lemma bv_eq_dec : forall n (s t : BV n), {s = t} + {s <> t}.
Proof.
  induction n as [| m IH]; intros s t; simpl in *.
  - left. destruct s, t. reflexivity.
  - destruct s as [a s], t as [b t]. destruct (bool_dec a b) as [<- | N]; [| right; congruence].
    destruct (IH s t) as [<- | N]; [left; reflexivity | right; congruence].
Defined.

Definition ifixed_b (n : nat) (Fv : nat -> BV n -> bool) (s : BV n) : bool :=
  forallb (fun i => Bool.eqb (Fv i s) (bget n i s)) (seq 0 n).

Lemma ifixed_b_spec : forall n Fv s, ifixed_b n Fv s = true <-> IFixed (BV n) (bget n) Fv (seq 0 n) s.
Proof.
  intros n Fv s. unfold ifixed_b. rewrite forallb_forall. split.
  - intros H i Hi. apply Bool.eqb_prop. exact (H i Hi).
  - intros H i Hi. rewrite (H i Hi). apply Bool.eqb_reflx.
Qed.

Lemma bfixed_iff : forall n Fv p,
  Fsync bool (BV n) (seq 0 n) (bset n) Fv p = p <-> ifixed_b n Fv p = true.
Proof.
  intros n Fv p. rewrite ifixed_b_spec.
  exact (fixed_iff (BV n) (seq 0 n) (bget n) (bset n) (bget_bset_eq n) (bget_bset_neq n) (bext n) Fv p).
Qed.

Ltac dbv := repeat match goal with
  | s : BV (S _) |- _ => destruct s
  | s : BV 0 |- _ => destruct s
  | s : (bool * _)%type |- _ => destruct s
  | s : unit |- _ => destruct s
  | b : bool |- _ => destruct b
  end.

(* ============================================================================================ *)
(* Part 3. Instances.                                                                            *)
(* ============================================================================================ *)

(* ----- the local condition is strictly weaker than the global one ----- *)

Definition lc_F (i : nat) (s : BV 3) : bool :=
  match i with
  | 0 => bget 3 1 s && bget 3 2 s
  | 1 => bget 3 0 s || bget 3 2 s
  | _ => false
  end.
Definition lc_sg : list (@edge bool) := [(1, 0, false); (2, 0, false); (0, 1, false); (2, 1, false)].
Definition lc_q : BV 3 := (false, (false, (false, tt))).

Lemma lc_no_cycle : NoLocalCycle (BV 3) (bget 3) (bset 3) lc_F (seq 0 3).
Proof. apply (chk_none _ _ _ (benum 3)); [apply benum_all | vm_compute; reflexivity]. Qed.

Lemma lc_resp : Resp bool (BV 3) sbl (seq 0 3) (bget 3) lc_F lc_sg.
Proof.
  intros v Hv s t H. simpl in Hv. destruct Hv as [<- | [<- | [<- | []]]].
  - pose proof (H 1 false (or_introl eq_refl)) as H1.
    pose proof (H 2 false (or_intror (or_introl eq_refl))) as H2.
    revert H1 H2. dbv; unfold sbl; simpl; auto.
  - pose proof (H 0 false (or_intror (or_intror (or_introl eq_refl)))) as H1.
    pose proof (H 2 false (or_intror (or_intror (or_intror (or_introl eq_refl))))) as H2.
    revert H1 H2. dbv; unfold sbl; simpl; auto.
  - reflexivity.
Qed.

Theorem local_weaker_than_global :
  NoLocalCycle (BV 3) (bget 3) (bset 3) lc_F (seq 0 3) /\
  NoLocalPos (BV 3) (bget 3) (bset 3) lc_F (seq 0 3) /\
  (forall sg, Resp bool (BV 3) sbl (seq 0 3) (bget 3) lc_F sg ->
     In (1, 0, false) sg /\ In (0, 1, false) sg /\ SgCycle sg [0; 1] false) /\
  SgOn (seq 0 3) lc_sg /\ Resp bool (BV 3) sbl (seq 0 3) (bget 3) lc_F lc_sg /\ Switching lc_sg ofalse /\
  (forall p, Fsync bool (BV 3) (seq 0 3) (bset 3) lc_F p = p <-> p = lc_q) /\
  (forall sch, Fair (seq 0 3) sch -> forall h0, Settles (BV 3) (rupd bool (BV 3) (seq 0 3) (bset 3) lc_F) sch h0 lc_q) /\
  (forall h0, EffectiveCanon (fun _ => lc_q) (rupd bool (BV 3) (seq 0 3) (bset 3) lc_F) (r_ok (seq 0 3))
                (r_flush (seq 0 3)) (r_settled bool (BV 3) (seq 0 3) (bset 3) lc_F) h0).
Proof.
  pose proof lc_no_cycle as Hc.
  assert (Hp : NoLocalPos (BV 3) (bget 3) (bset 3) lc_F (seq 0 3)) by (intros x c Hcc [Hcy _]; exact (Hc x c Hcc Hcy)).
  assert (Hcert : forall sg, Resp bool (BV 3) sbl (seq 0 3) (bget 3) lc_F sg -> In (1, 0, false) sg /\ In (0, 1, false) sg).
  { intros sg Hr. split.
    - destruct (in_dec sedge_dec (1, 0, false) sg) as [H | H]; [exact H | exfalso].
      assert (P : forall u b, In (u, 0, b) sg ->
                if b then sbl (bget 3 u (false, (false, (true, tt)))) (bget 3 u (false, (true, (true, tt))))
                else sbl (bget 3 u (false, (true, (true, tt)))) (bget 3 u (false, (false, (true, tt))))).
      { intros u b Hin. destruct u as [| [| [| u]]]; destruct b; try reflexivity. exfalso. exact (H Hin). }
      pose proof (Hr 0 (or_introl eq_refl) _ _ P) as R. discriminate R.
    - destruct (in_dec sedge_dec (0, 1, false) sg) as [H | H]; [exact H | exfalso].
      assert (P : forall u b, In (u, 1, b) sg ->
                if b then sbl (bget 3 u (false, (false, (false, tt)))) (bget 3 u (true, (false, (false, tt))))
                else sbl (bget 3 u (true, (false, (false, tt)))) (bget 3 u (false, (false, (false, tt))))).
      { intros u b Hin. destruct u as [| [| [| u]]]; destruct b; try reflexivity. exfalso. exact (H Hin). }
      pose proof (Hr 1 (or_intror (or_introl eq_refl)) _ _ P) as R. discriminate R. }
  assert (Hon : SgOn (seq 0 3) lc_sg).
  { intros u v b Hin. simpl in Hin. destruct Hin as [E | [E | [E | [E | []]]]]; injection E as <- <- <-; simpl; tauto. }
  assert (Hsw : Switching lc_sg ofalse).
  { intros u v b Hin. simpl in Hin. destruct Hin as [E | [E | [E | [E | []]]]]; injection E as <- <- <-; reflexivity. }
  assert (Hq : Fsync bool (BV 3) (seq 0 3) (bset 3) lc_F lc_q = lc_q) by (vm_compute; reflexivity).
  assert (Hu : forall p, Fsync bool (BV 3) (seq 0 3) (bset 3) lc_F p = p <-> p = lc_q).
  { intros p. split; [intros H | intros ->; exact Hq].
    exact (local_fidelity (BV 3) (seq 0 3) (bget 3) (bset 3) (bget_bset_eq 3) (bget_bset_neq 3) (bext 3) lc_F Hp p lc_q H Hq). }
  destruct (local_signed_fidelity (BV 3) (seq 0 3) (bget 3) (bset 3) (bget_bset_eq 3) (bget_bset_neq 3) (bext 3)
              lc_F lc_q lc_sg ofalse Hon lc_resp Hsw Hp) as (Hfix & _ & H1 & H2).
  assert (Hl : slfp bool (BV 3) false true 1 bool_dec (seq 0 3) (bget 3) (bset 3) (bext 3) lc_q lc_F ofalse = lc_q)
    by exact (proj1 (Hu _) Hfix).
  split; [exact Hc | split; [exact Hp |]].
  split.
  { intros sg Hr. destruct (Hcert sg Hr) as [H10 H01]. split; [exact H10 | split; [exact H01 |]].
    split; [discriminate | split; [constructor; [intros [E | []]; discriminate | constructor; [intros [] | constructor]] |]].
    change false with (xorb false (xorb false false)). simpl (cpairs [0; 1]).
    apply sgp_cons; [exact H10 |]. apply sgp_cons; [exact H01 | constructor]. }
  split; [exact Hon | split; [exact lc_resp | split; [exact Hsw | split; [exact Hu |]]]].
  rewrite Hl in H1, H2. split; [exact H1 | exact H2].
Qed.

(* ----- local settlement: no local negative cycle, no fixed point (Boolean, 6 vertices) ----- *)

(* Richard 2010, Example 6, on {0..3}^2: f1 = 3 iff x2 = 3, or x2 > 0 and x1 >= 2; f2 = 3 iff
   x1 = 0, or x1 < 3 and x2 >= 2; otherwise 0. Its stepwise version moves each coordinate one
   unit toward f. Tonello 2017's Boolean conversion: vertex 3 i + (h - 1) carries "level of
   component i is at least h", and a Boolean state is read through the number of its true
   coordinates in each block of three. *)
Definition b2n (b : bool) : nat := if b then 1 else 0.
Definition cnt3 (a b c : bool) : nat := b2n a + b2n b + b2n c.
Definition rc_step (g : bool) (c : nat) : nat := if g then Nat.min 3 (S c) else pred c.

Definition tn_F (i : nat) (s : BV 6) : bool :=
  let c0 := cnt3 (bget 6 0 s) (bget 6 1 s) (bget 6 2 s) in
  let c1 := cnt3 (bget 6 3 s) (bget 6 4 s) (bget 6 5 s) in
  let g0 := Nat.eqb c1 3 || (Nat.ltb 0 c1 && Nat.leb 2 c0) in
  let g1 := Nat.eqb c0 0 || (Nat.ltb c0 3 && Nat.leb 2 c1) in
  match i with
  | 0 => Nat.leb 1 (rc_step g0 c0) | 1 => Nat.leb 2 (rc_step g0 c0) | 2 => Nat.leb 3 (rc_step g0 c0)
  | 3 => Nat.leb 1 (rc_step g1 c1) | 4 => Nat.leb 2 (rc_step g1 c1) | 5 => Nat.leb 3 (rc_step g1 c1)
  | _ => false
  end.

Theorem local_neg_free_no_fixed_point :
  NoLocalNeg (BV 6) (bget 6) (bset 6) tn_F (seq 0 6) /\
  (forall p, Fsync bool (BV 6) (seq 0 6) (bset 6) tn_F p <> p) /\
  (forall h0 w, ~ r_settled bool (BV 6) (seq 0 6) (bset 6) tn_F (xr bool (BV 6) (seq 0 6) (bset 6) tn_F w h0)) /\
  (forall h0, ~ Settlement (rupd bool (BV 6) (seq 0 6) (bset 6) tn_F) (r_ok (seq 0 6)) (r_flush (seq 0 6))
                  (r_settled bool (BV 6) (seq 0 6) (bset 6) tn_F) h0).
Proof.
  assert (Hn : forall p, Fsync bool (BV 6) (seq 0 6) (bset 6) tn_F p <> p).
  { intros p H. apply bfixed_iff in H.
    assert (A : forallb (fun s => negb (ifixed_b 6 tn_F s)) (benum 6) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in A. pose proof (A p (benum_all 6 p)) as Ap. rewrite H in Ap. discriminate Ap. }
  assert (Hs : forall s, ~ r_settled bool (BV 6) (seq 0 6) (bset 6) tn_F s).
  { intros s H. apply (settled_fixed bool (BV 6) (seq 0 6) (bget 6) (bset 6) (bget_bset_eq 6) (bget_bset_neq 6) (bext 6)) in H.
    exact (Hn s H). }
  split; [apply (chk_neg _ _ _ (benum 6)); [apply benum_all | vm_compute; reflexivity] |].
  split; [exact Hn |]. split; [intros h0 w; apply Hs |].
  intros h0 H. destruct (H [] (Forall_nil _)) as [c [_ Hc]]. exact (Hs _ Hc).
Qed.

(* ----- the strongest local condition does not give fair settlement ----- *)

Definition sd_F (i : nat) (s : BV 4) : bool :=
  match i with
  | 0 => negb (bget 4 1 s) && negb (bget 4 2 s)
  | 1 => bget 4 0 s || negb (bget 4 2 s) || bget 4 3 s
  | 2 => bget 4 0 s && bget 4 1 s && bget 4 3 s
  | 3 => negb (bget 4 0 s)
  | _ => false
  end.
Definition sd_word : list nat := [2; 3; 0; 1; 3; 2; 0; 1].
Definition sd_sch (n : nat) : nat := nth (n mod 8) sd_word 0.
Definition sd_h0 : BV 4 := (true, (true, (false, (true, tt)))).
Definition sd_q : BV 4 := (false, (true, (false, (true, tt)))).

Lemma prs_shift : forall (Sh : Type) up sch n k (h : Sh),
  prs Sh up sch (n + k) h = prs Sh up (fun t => sch (n + t)) k (prs Sh up sch n h).
Proof.
  intros Sh up sch n k h. induction k as [| k IH]; [rewrite Nat.add_0_r; reflexivity |].
  rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

Lemma prs_sch_ext : forall (Sh : Type) up s1 s2, (forall t, s1 t = s2 t) -> forall k (h : Sh),
  prs Sh up s1 k h = prs Sh up s2 k h.
Proof. intros Sh up s1 s2 H k h. induction k as [| k IH]; [reflexivity |]. simpl. rewrite IH, H. reflexivity. Qed.

Lemma sd_sch_shift : forall m t, sd_sch (m * 8 + t) = sd_sch t.
Proof.
  intros m t. unfold sd_sch. f_equal. rewrite Nat.add_comm. apply Nat.mod_add. discriminate.
Qed.

Lemma sd_sch_fair : Fair (seq 0 4) sd_sch.
Proof.
  split.
  - intros n. unfold sd_sch. pose proof (Nat.mod_upper_bound n 8 ltac:(discriminate)) as H.
    destruct (n mod 8) as [| [| [| [| [| [| [| [| k]]]]]]]]; simpl; try tauto; lia.
  - intros j n Hj. simpl in Hj.
    assert (Hp : exists t, t < 8 /\ nth t sd_word 0 = j)
      by (destruct Hj as [<- | [<- | [<- | [<- | []]]]];
          [exists 2 | exists 3 | exists 0 | exists 1]; split; [lia | reflexivity | lia | reflexivity
                                                              | lia | reflexivity | lia | reflexivity]).
    destruct Hp as [t [Ht Et]]. exists (n * 8 + t). split; [lia |].
    rewrite sd_sch_shift. unfold sd_sch. rewrite Nat.mod_small by exact Ht. exact Et.
Qed.

Theorem shih_dong_not_fair :
  NoLocalCycle (BV 4) (bget 4) (bset 4) sd_F (seq 0 4) /\
  (forall p, Fsync bool (BV 4) (seq 0 4) (bset 4) sd_F p = p <-> p = sd_q) /\
  (forall h0, EffectiveCanon (fun _ => sd_q) (rupd bool (BV 4) (seq 0 4) (bset 4) sd_F) (r_ok (seq 0 4))
                (r_flush (seq 0 4)) (r_settled bool (BV 4) (seq 0 4) (bset 4) sd_F) h0) /\
  Fair (seq 0 4) sd_sch /\
  (forall m, prs (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sd_F) sd_sch (m * 8) sd_h0 = sd_h0) /\
  (forall q, ~ Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sd_F) sd_sch sd_h0 q).
Proof.
  set (up := rupd bool (BV 4) (seq 0 4) (bset 4) sd_F).
  assert (Hc : NoLocalCycle (BV 4) (bget 4) (bset 4) sd_F (seq 0 4))
    by (apply (chk_none _ _ _ (benum 4)); [apply benum_all | vm_compute; reflexivity]).
  destruct (shih_dong_E (BV 4) (seq 0 4) (bget 4) (bset 4) (bget_bset_eq 4) (bget_bset_neq 4) (bext 4) sd_F Hc sd_q)
    as (q & Hq & Hu & HE).
  assert (Hsq : Fsync bool (BV 4) (seq 0 4) (bset 4) sd_F sd_q = sd_q) by (vm_compute; reflexivity).
  assert (Eq : sd_q = q) by exact (Hu sd_q Hsq).
  assert (P8 : prs (BV 4) up sd_sch 8 sd_h0 = sd_h0) by (vm_compute; reflexivity).
  assert (Hper : forall m, prs (BV 4) up sd_sch (m * 8) sd_h0 = sd_h0).
  { induction m as [| m IH]; [reflexivity |].
    replace (S m * 8) with (m * 8 + 8) by lia. rewrite prs_shift, IH.
    rewrite (prs_sch_ext (BV 4) up (fun t => sd_sch (m * 8 + t)) sd_sch (sd_sch_shift m)). exact P8. }
  split; [exact Hc |]. split.
  { intros p. split; [intros H; rewrite Eq; exact (Hu p H) | intros ->; exact Hsq]. }
  split; [rewrite Eq; exact HE |]. split; [exact sd_sch_fair |]. split; [exact Hper |].
  intros q' [N HN].
  pose proof (HN (N * 8) ltac:(lia)) as A. pose proof (HN (N * 8 + 1) ltac:(lia)) as B.
  rewrite prs_shift, Hper in B. rewrite Hper in A. rewrite <- A in B.
  rewrite (prs_sch_ext (BV 4) up (fun t => sd_sch (N * 8 + t)) sd_sch (sd_sch_shift N)) in B.
  vm_compute in B. discriminate B.
Qed.

(* ----- the positive 3-ring under both corrected local conditions ----- *)

Definition r3all : list R3 :=
  [(false, false, false); (true, false, false); (false, true, false); (true, true, false);
   (false, false, true); (true, false, true); (false, true, true); (true, true, true)].

Lemma r3all_all : forall s : R3, In s r3all.
Proof. intros [[a b] c]. destruct a, b, c; simpl; tauto. Qed.

Theorem ring_local_conditions :
  NoDup r3js /\
  NoLocalNeg R3 get3 set3 ring_F r3js /\
  OutDeg1 R3 get3 set3 ring_F r3js /\
  (forall x c, incl c r3js -> PosCycleAt R3 get3 set3 ring_F x c -> In 0 c) /\
  (forall h0, Settlement (rupd3 ring_F) (r_ok r3js) (r_flush r3js) (settled3 ring_F) h0) /\
  Fsync bool R3 r3js set3 ring_F (false, false, false) = (false, false, false) /\
  Fsync bool R3 r3js set3 ring_F (true, true, true) = (true, true, true) /\
  Fair r3js r3sg /\ (forall n, ~ settled3 ring_F (prs R3 (rupd3 ring_F) r3sg n r3h0)) /\
  ~ CanonicalFidelity (fun _ => slfp3 ring_F ofalse) (rupd3 ring_F) (r_ok r3js) (settled3 ring_F) r3h0.
Proof.
  destruct ring_needs_low_start as (_ & _ & _ & _ & _ & Hf & Hns & _).
  destruct ring_low_start_E as (_ & _ & _ & Hnf & _).
  assert (Hnd : NoDup r3js) by (repeat constructor; simpl; intuition discriminate).
  assert (Hneg : NoLocalNeg R3 get3 set3 ring_F r3js)
    by (apply (chk_neg _ _ _ r3all); [exact r3all_all | vm_compute; reflexivity]).
  assert (Hod : OutDeg1 R3 get3 set3 ring_F r3js)
    by (apply (outdeg_sound _ _ _ r3all); [exact r3all_all | vm_compute; reflexivity]).
  destruct (richard_t3 R3 r3js get3 set3 get3_set_eq get3_set_neq s3_ext ring_F Hnd Hneg Hod) as [_ Hset].
  split; [exact Hnd | split; [exact Hneg | split; [exact Hod |]]].
  split; [apply (chk_through _ _ _ r3all); [exact r3all_all | vm_compute; reflexivity] |].
  split; [exact Hset |]. split; [reflexivity | split; [reflexivity |]].
  split; [exact Hf | split; [exact Hns | exact Hnf]].
Qed.

(* ----- non-vacuity of global_to_local: the unbalanced negative 2-cycle ----- *)

(* x0 := not x1, x1 := x0 (SignedResolver.neg2_no_fixed_point): its certificate is one negative
   2-cycle, so the global condition holds and gives NoLocalPos. *)
Theorem global_to_local_instance :
  (forall c, incl c js2 -> ~ SgCycle neg_sg c false) /\ NoLocalPos SS2 get2 set2 neg_F js2.
Proof.
  assert (G : forall c, incl c js2 -> ~ SgCycle neg_sg c false).
  { intros c Hc [Hne [Hnd Hp]].
    pose proof (nl_complete 2 js2 c Hnd Hc (NoDup_incl_length Hnd Hc)) as Hin. vm_compute in Hin.
    repeat (destruct Hin as [E | Hin]; [subst c | ]); try contradiction.
    all: simpl in Hp; repeat match goal with
      | H : SgPath _ (_ :: _) _ |- _ => inversion H; subst; clear H
      | H : SgPath _ [] _ |- _ => inversion H; subst; clear H
      | H : In _ neg_sg |- _ => simpl in H
      | H : _ \/ _ |- _ => destruct H
      | H : False |- _ => destruct H
      | H : (_, _, _) = (_, _, _) |- _ => first [discriminate H | injection H; intros; subst; clear H | clear H]
      end; simpl in *; try discriminate. }
  split; [exact G |].
  destruct neg2_no_fixed_point as (_ & Hr & _).
  exact (global_to_local SS2 js2 get2 set2 get2_set_eq get2_set_neq s2_ext neg_F neg_sg Hr G).
Qed.
