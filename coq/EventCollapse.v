(* EventCollapse.v: events with equal governed steps are checked once (gsm's event parameters,
   theory section 11.12, "Ranges"). Axiom-free.

   gsm's Build with Abstract checks a parameterized event at every assignment of representative
   values to its parameters, with the range test min <= p <= max conjoined to its guard (so the
   checked registry is in the model of AbstractionGsm.v), and it checks the out-of-range
   assignments ONCE: they all give the same event, which does nothing before repair. This file
   is the theorem for that step, about the finite checks gsm computes.

   Collapse (general). cc1v_checkP and idemv_checkP are AbstractionGsm's cc1v_check and
   idemv_check with the parameter assignments of each kind taken from a list P k (the full
   check is P k = tup (reps N C) m, cc1v_checkP_full, idemv_checkP_full); cc1v_checkP_spec,
   idemv_checkP_spec give their exact meaning. Covers K k L L': every assignment in L has one in
   L' with the same governed step at every state with n variables (SameStep).
   - cover_cc1v, cover_idemv: if P k and Q k cover each other for every kind, the two checks
     return the same boolean. drop_cc1v, drop_idemv: an assignment whose step another one in the
     list has can be removed, and the result does not change.
   - cover_full_cc1v, cover_full_idemv: a list of representative assignments that covers all of
     them gives the full check's boolean.
   - cc1_valid_cover, idem_valid_cover, idem_runtime_cover, gsm_cover_exact: composed with
     cc1_valid_abs, idem_valid_abs, idem_runtime_abs, gsm_abs_exact, the reduced check passes iff
     the condition holds over every integer state and parameter value.

   Ranges (the instance). ranged n rg P conjoins to every event kind k of P the range test
   rtest n 0 (rg k) (min <= p_i <= max for each declared parameter i, gsm's rangedInstance): each
   variable's new value becomes "if the test holds then the event's value else the old value".
   - range_wf, range_frag, range_reads: the ranged registry is well formed and in the fragment
     when P is and the bounds are declared constants (gsm adds them to C, absConstants).
   - range_in_step: on assignments in range, the ranged event is P's event; range_cc1_in,
     range_idem_in: so CC1 and idempotence of the ranged registry give P's on the values in range.
   - range_out_step: on every assignment outside the ranges, the governed step is repair alone
     (the event does nothing before repair); range_same_step: all such assignments have one step.
   - range_prefix_step: a kind that reads only its declared parameters (reads) does not depend
     on the rest of the assignment (gsm's events have their own arity; the model pads to m).
   - RangeList N PL: PL k lies in the representative assignments, has, for each in-range one,
     one that agrees on the declared parameters, and has an out-of-range one if there is any.
     gsm_params is gsm's list (absEventList: the in-range assignments of the declared parameters
     and the first out-of-range one, padded to m), and gsm_params_ok shows it is a RangeList.
   - range_cc1v, range_idemv: for any RangeList, the reduced checks return the full checks'
     boolean. range_cc1_exact, range_idem_exact, range_idem_runtime, range_gsm_exact: the reduced
     check passes iff CC1 at every valid integer state for every two parameter values (iff runs
     from every valid state converge up to reordering), iff idempotence at every valid integer
     state, iff idempotence of the runtime step from every integer state.
   - Given repair within K steps (which gsm checks first), the out-of-range assignment can be
     dropped too: range_inonly_cc1v, range_inonly_idemv, range_inonly_cc1_exact (the out-of-range
     event is repair, which fixes valid states, so it commutes with every event and is idempotent
     at valid states).
   Non-vacuity.
   - crng_*: capped Restock(level) of AbstractionCutoff.v with gsm's declared range 0..10^9 for
     the level (constants 0, 5, 10^9, cutoff 3; gsm's TestParamsAbstract_Capped): 15
     representative assignments, of which gsm checks 10 (crng_counts); the reduced checks pass,
     so CC1 and idempotence hold for every integer stock and level, and every permutation of
     restocks converges at run time from every integer state.
   - setlvl_*: Set(level) with range 0..5 does not commute; the reduced check fails, so CC1 fails
     over Z, with a witness in range.
   Boundary.
   - slow_*: without repair within K steps the out-of-range assignment is needed: the in-range
     assignments alone pass, gsm's list fails, and CC1 fails over Z at the out-of-range Reset(-1)
     (slow_diverges). With the repair depth K = 2, gsm's list passes. *)

Require Import NC.Newman NC.Governance NC.SymmetryCutoff NC.AbstractionCutoff NC.Trace.
Require Import NC.AbstractionGsm.
From Coq Require Import List Arith Lia Bool ZArith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Lemma tup_len' : forall D k l, In l (tup D k) -> length l = k.
Proof. intros D k l H. apply tup_spec in H. apply H. Qed.

(* ============================================================================================ *)
(* The checks over a list of parameter assignments per kind.                                    *)
(* ============================================================================================ *)

Section Collapse.
  Variable C : list Z.
  Variable n m nk : nat.
  Variable ap : nat * list Z -> list Z -> list Z.
  Variable rp : list Z -> list Z.
  Variable vd : list Z -> bool.

  Local Notation G K := (govK ap rp K).
  Local Notation T N := (tup (reps N C) m).

  Definition cc1v_checkP (K N : nat) (Ib : nat -> nat -> bool) (P : nat -> list (list Z)) : bool :=
    forallb (fun s => implb (vd s)
      (forallb (fun k1 => forallb (fun k2 => implb (Ib k1 k2)
        (forallb (fun p1 => forallb (fun p2 =>
           leq (G K (k2, p2) (G K (k1, p1) s)) (G K (k1, p1) (G K (k2, p2) s)))
           (P k2)) (P k1)))
        (seq 0 nk)) (seq 0 nk)))
      (tup (reps N C) n).

  Definition idemv_checkP (K N k : nat) (L : list (list Z)) : bool :=
    forallb (fun s => implb (vd s)
      (forallb (fun p => leq (G K (k, p) (G K (k, p) s)) (G K (k, p) s)) L))
      (tup (reps N C) n).

  (* Over every representative assignment, they are gsm's checks of AbstractionGsm.v. *)
  Theorem cc1v_checkP_full : forall K N Ib,
    cc1v_checkP K N Ib (fun _ => T N) = cc1v_check C n m nk ap rp vd K N Ib.
  Proof. reflexivity. Qed.

  Theorem idemv_checkP_full : forall K N k, idemv_checkP K N k (T N) = idemv_check C n m ap rp vd K N k.
  Proof. reflexivity. Qed.

  Definition CC1VP (K N : nat) (I : nat -> nat -> Prop) (P : nat -> list (list Z)) : Prop :=
    forall s k1 p1 k2 p2, In s (tup (reps N C) n) -> vd s = true ->
      (k1 < nk)%nat -> (k2 < nk)%nat -> In p1 (P k1) -> In p2 (P k2) -> I k1 k2 ->
      G K (k2, p2) (G K (k1, p1) s) = G K (k1, p1) (G K (k2, p2) s).

  Definition IdemVP (K N k : nat) (L : list (list Z)) : Prop :=
    forall s p, In s (tup (reps N C) n) -> vd s = true -> In p L ->
      G K (k, p) (G K (k, p) s) = G K (k, p) s.

  Theorem cc1v_checkP_spec : forall K N Ib P,
    cc1v_checkP K N Ib P = true <-> CC1VP K N (fun a b => Ib a b = true) P.
  Proof.
    intros K N Ib P. unfold cc1v_checkP, CC1VP. rewrite forallb_forall. split.
    - intros H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI. specialize (H s Hs).
      rewrite implb_true in H. specialize (H Hv). rewrite forallb_forall in H.
      specialize (H k1 (proj2 (in_seq nk 0 k1) (conj (Nat.le_0_l _) H1))).
      rewrite forallb_forall in H. specialize (H k2 (proj2 (in_seq nk 0 k2) (conj (Nat.le_0_l _) H2))).
      rewrite implb_true in H. specialize (H HI). rewrite forallb_forall in H.
      specialize (H p1 Hp1). rewrite forallb_forall in H. apply leq_spec. exact (H p2 Hp2).
    - intros H s Hs. apply implb_true. intros Hv. apply forallb_forall. intros k1 H1.
      apply forallb_forall. intros k2 H2. apply implb_true. intros HI.
      apply forallb_forall. intros p1 Hp1. apply forallb_forall. intros p2 Hp2.
      apply in_seq in H1. apply in_seq in H2. apply leq_spec.
      apply H; [exact Hs | exact Hv | lia | lia | exact Hp1 | exact Hp2 | exact HI].
  Qed.

  Theorem idemv_checkP_spec : forall K N k L, idemv_checkP K N k L = true <-> IdemVP K N k L.
  Proof.
    intros K N k L. unfold idemv_checkP, IdemVP. rewrite forallb_forall. split.
    - intros H s p Hs Hv Hp. specialize (H s Hs). rewrite implb_true in H. specialize (H Hv).
      rewrite forallb_forall in H. apply leq_spec. exact (H p Hp).
    - intros H s Hs. apply implb_true. intros Hv. apply forallb_forall. intros p Hp.
      apply leq_spec. exact (H s p Hs Hv Hp).
  Qed.

  (* Two assignments of kind k with the same governed step at every state with n variables. *)
  Definition SameStep (K k : nat) (p q : list Z) : Prop :=
    forall s, length s = n -> G K (k, p) s = G K (k, q) s.

  (* Every assignment in L has one in L' with the same step. *)
  Definition Covers (K k : nat) (L L' : list (list Z)) : Prop :=
    forall p, In p L -> exists q, In q L' /\ SameStep K k p q.

  Lemma covers_incl : forall K k L L', incl L L' -> Covers K k L L'.
  Proof. intros K k L L' H p Hp. exists p. split; [exact (H p Hp) | intros s _; reflexivity]. Qed.

  Section WithShape.
    Hypothesis HS : Shaped n m nk ap rp vd.

    Lemma cc1vp_cover : forall K N I P Q, (forall k, (k < nk)%nat -> Covers K k (P k) (Q k)) ->
      CC1VP K N I Q -> CC1VP K N I P.
    Proof.
      intros K N I P Q Hc H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI.
      destruct (Hc k1 H1 p1 Hp1) as [q1 [Hq1 E1]]. destruct (Hc k2 H2 p2 Hp2) as [q2 [Hq2 E2]].
      assert (Ls : length s = n) by exact (tup_len' _ _ _ Hs).
      rewrite (E1 s Ls), (E2 s Ls).
      rewrite (E2 _ (G_len n m nk ap rp vd HS K (k1, q1) s Ls)).
      rewrite (E1 _ (G_len n m nk ap rp vd HS K (k2, q2) s Ls)).
      exact (H s k1 q1 k2 q2 Hs Hv H1 H2 Hq1 Hq2 HI).
    Qed.

    Lemma idemvp_cover : forall K N k L L', Covers K k L L' -> IdemVP K N k L' -> IdemVP K N k L.
    Proof.
      intros K N k L L' Hc H s p Hs Hv Hp. destruct (Hc p Hp) as [q [Hq E]].
      assert (Ls : length s = n) by exact (tup_len' _ _ _ Hs).
      rewrite (E s Ls), (E _ (G_len n m nk ap rp vd HS K (k, q) s Ls)). exact (H s q Hs Hv Hq).
    Qed.

    (* Lists of assignments with the same steps give the same CC1 check. *)
    Theorem cover_cc1v : forall K N Ib P Q,
      (forall k, (k < nk)%nat -> Covers K k (P k) (Q k)) ->
      (forall k, (k < nk)%nat -> Covers K k (Q k) (P k)) ->
      cc1v_checkP K N Ib P = cc1v_checkP K N Ib Q.
    Proof.
      intros K N Ib P Q H1 H2. apply eq_iff_eq_true. rewrite !cc1v_checkP_spec.
      split; [apply cc1vp_cover; exact H2 | apply cc1vp_cover; exact H1].
    Qed.

    (* And the same idempotence check. *)
    Theorem cover_idemv : forall K N k L L', Covers K k L L' -> Covers K k L' L ->
      idemv_checkP K N k L = idemv_checkP K N k L'.
    Proof.
      intros K N k L L' H1 H2. apply eq_iff_eq_true. rewrite !idemv_checkP_spec.
      split; [apply idemvp_cover; exact H2 | apply idemvp_cover; exact H1].
    Qed.

    (* In particular, an assignment whose step another one in the list has can be removed. *)
    Lemma covers_cons : forall K k p q L, In q L -> SameStep K k p q -> Covers K k (p :: L) L.
    Proof.
      intros K k p q L Hq E x [<- | Hx]; [exists q; split; [exact Hq | exact E]|].
      exists x. split; [exact Hx | intros s _; reflexivity].
    Qed.

    Theorem drop_cc1v : forall K N Ib P k0 p q, In q (P k0) -> SameStep K k0 p q ->
      cc1v_checkP K N Ib (fun k => if Nat.eqb k k0 then p :: P k else P k) = cc1v_checkP K N Ib P.
    Proof.
      intros K N Ib P k0 p q Hq E. apply cover_cc1v; intros k _;
        destruct (Nat.eqb_spec k k0) as [-> | _];
        try (apply covers_incl; intros x Hx; first [exact Hx | right; exact Hx]).
      exact (covers_cons K k0 p q (P k0) Hq E).
    Qed.

    Theorem drop_idemv : forall K N k p q L, In q L -> SameStep K k p q ->
      idemv_checkP K N k (p :: L) = idemv_checkP K N k L.
    Proof.
      intros K N k p q L Hq E. apply cover_idemv; [exact (covers_cons K k p q L Hq E)|].
      apply covers_incl. intros x Hx. right. exact Hx.
    Qed.

    (* A list of representative assignments that covers all of them gives the full check. *)
    Theorem cover_full_cc1v : forall K N Ib P,
      (forall k, (k < nk)%nat -> incl (P k) (T N)) ->
      (forall k, (k < nk)%nat -> Covers K k (T N) (P k)) ->
      cc1v_checkP K N Ib P = cc1v_check C n m nk ap rp vd K N Ib.
    Proof.
      intros K N Ib P Hi Hc. rewrite <- cc1v_checkP_full. apply cover_cc1v; [|exact Hc].
      intros k Hk. apply covers_incl. exact (Hi k Hk).
    Qed.

    Theorem cover_full_idemv : forall K N k L, incl L (T N) -> Covers K k (T N) L ->
      idemv_checkP K N k L = idemv_check C n m ap rp vd K N k.
    Proof.
      intros K N k L Hi Hc. rewrite <- idemv_checkP_full. apply cover_idemv; [|exact Hc].
      apply covers_incl. exact Hi.
    Qed.

    (* With the transfers: the reduced checks are exact over every integer state and value. *)
    Hypothesis HO : OrdInv C n ap rp vd.

    Theorem cc1_valid_cover : forall K N Ib P, (n + 2 * m <= N)%nat ->
      (forall k, (k < nk)%nat -> incl (P k) (T N)) ->
      (forall k, (k < nk)%nat -> Covers K k (T N) (P k)) ->
      (CC1VZ n m nk ap rp vd K (fun a b => Ib a b = true) <-> cc1v_checkP K N Ib P = true).
    Proof.
      intros K N Ib P HN Hi Hc. rewrite (cover_full_cc1v K N Ib P Hi Hc), cc1v_check_spec.
      exact (cc1_valid_abs C n m nk ap rp vd HS HO K N _ HN).
    Qed.

    Theorem idem_valid_cover : forall K N k L, (n + m <= N)%nat -> incl L (T N) -> Covers K k (T N) L ->
      (IdemVZ n m ap rp vd K k <-> idemv_checkP K N k L = true).
    Proof.
      intros K N k L HN Hi Hc. rewrite (cover_full_idemv K N k L Hi Hc), idemv_check_spec.
      exact (idem_valid_abs C n m nk ap rp vd HS HO K N k HN).
    Qed.

    Theorem idem_runtime_cover : forall K N k L, (n + m <= N)%nat -> TermD C n rp vd K N ->
      (k < nk)%nat -> incl L (T N) -> Covers K k (T N) L ->
      ((forall s p, length s = n -> length p = m ->
          govK (apR m nk ap rp K) rp K (k, p) (govK (apR m nk ap rp K) rp K (k, p) s) =
          govK (apR m nk ap rp K) rp K (k, p) s) <->
       idemv_checkP K N k L = true).
    Proof.
      intros K N k L HN HD Hk Hi Hc. rewrite (cover_full_idemv K N k L Hi Hc), idemv_check_spec.
      exact (idem_runtime_abs C n m nk ap rp vd K N k HS HO HN HD Hk).
    Qed.

    Theorem gsm_cover_exact : forall K N Ib P, (n + 2 * m <= N)%nat -> TermD C n rp vd K N ->
      (forall k, (k < nk)%nat -> incl (P k) (T N)) ->
      (forall k, (k < nk)%nat -> Covers K k (T N) (P k)) ->
      (cc1v_checkP K N Ib P = true <-> RunConvZ n m nk ap rp vd K (fun a b => Ib a b = true)).
    Proof.
      intros K N Ib P HN HD Hi Hc. rewrite (cover_full_cc1v K N Ib P Hi Hc), cc1v_check_spec.
      exact (gsm_abs_exact C n m nk ap rp vd K N _ HS HO HN HD).
    Qed.
  End WithShape.
End Collapse.

(* ============================================================================================ *)
(* The range test conjoined to every event kind's guard.                                        *)
(* ============================================================================================ *)

(* min <= p_i <= max for the parameters i, i + 1, ... (parameter i is variable n + i). *)
Fixpoint rtest (n i : nat) (r : list (Z * Z)) : form :=
  match r with
  | [] => FT
  | (lo, hi) :: r' =>
      FAnd (FAnd (FLe (Cst lo) (Vr (n + i))) (FLe (Vr (n + i)) (Cst hi))) (rtest n (S i) r')
  end.

Fixpoint inRi (i : nat) (r : list (Z * Z)) (p : list Z) : bool :=
  match r with
  | [] => true
  | (lo, hi) :: r' => Z.leb lo (nth i p 0%Z) && Z.leb (nth i p 0%Z) hi && inRi (S i) r' p
  end.

(* The assignment p lies in the declared ranges r. *)
Definition inR (r : list (Z * Z)) (p : list Z) : bool := inRi 0 r p.

(* Variable i's new value: the event's when the test holds, else the old one. *)
Fixpoint guardL (t : form) (i : nat) (c : list expr) : list expr :=
  match c with
  | [] => []
  | e :: c' => If t e (Vr i) :: guardL t (S i) c'
  end.

Fixpoint rngks (n : nat) (rg : nat -> list (Z * Z)) (k : nat) (ks : list (list expr)) :
  list (list expr) :=
  match ks with
  | [] => []
  | c :: ks' => guardL (rtest n 0 (rg k)) 0 c :: rngks n rg (S k) ks'
  end.

(* The registry gsm checks: kind k with its range test rg k conjoined to its guard. *)
Definition ranged (n : nat) (rg : nat -> list (Z * Z)) (P : prog) : prog :=
  mkProg (rngks n rg 0 (pk P)) (pr P) (pinv P).

(* Kind k reads only its declared parameters (the first length (rg k)). *)
Fixpoint readsk (n : nat) (rg : nat -> list (Z * Z)) (k : nat) (ks : list (list expr)) : bool :=
  match ks with
  | [] => true
  | c :: ks' => forallb (bndE (n + length (rg k))) c && readsk n rg (S k) ks'
  end.

Definition reads (n : nat) (rg : nat -> list (Z * Z)) (P : prog) : bool := readsk n rg 0 (pk P).

(* ---- Evaluation. ---- *)

Lemma rngks_len : forall n rg k ks, length (rngks n rg k ks) = length ks.
Proof. intros n rg k ks. revert k. induction ks as [|c ks IH]; intros k; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rngks_nth : forall n rg ks k j,
  nth_error (rngks n rg k ks) j = option_map (guardL (rtest n 0 (rg (k + j)%nat)) 0) (nth_error ks j).
Proof.
  intros n rg ks. induction ks as [|c ks IH]; intros k j; destruct j as [|j]; simpl; try reflexivity.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (S k + j)%nat with (k + S j)%nat by lia. reflexivity.
Qed.

Lemma readsk_spec : forall n rg ks k j c e, readsk n rg k ks = true -> nth_error ks j = Some c ->
  In e c -> bndE (n + length (rg (k + j)%nat)) e = true.
Proof.
  intros n rg ks. induction ks as [|c0 ks IH]; intros k j c e H Hj He; [destruct j; discriminate|].
  simpl in H. apply andb_true_iff in H as [H0 H1]. destruct j as [|j]; simpl in Hj.
  - injection Hj as <-. rewrite Nat.add_0_r. rewrite forallb_forall in H0. exact (H0 e He).
  - replace (k + S j)%nat with (S k + j)%nat by lia. exact (IH (S k) j c e H1 Hj He).
Qed.

Lemma app_nth_n : forall (s p : list Z) i, nth (length s + i) (s ++ p) 0%Z = nth i p 0%Z.
Proof.
  intros s p i. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma rtest_eval : forall s p r i, evalF (s ++ p) (rtest (length s) i r) = inRi i r p.
Proof.
  intros s p r. induction r as [|[lo hi] r IH]; intros i; simpl; [reflexivity|].
  rewrite IH, app_nth_n. reflexivity.
Qed.

Lemma guardL_true : forall env t c i, evalF env t = true ->
  map (evalE env) (guardL t i c) = map (evalE env) c.
Proof.
  intros env t c. induction c as [|e c IH]; intros i H; simpl; [reflexivity|].
  rewrite H, (IH (S i) H). reflexivity.
Qed.

Lemma guardL_false : forall env t c i, evalF env t = false ->
  map (evalE env) (guardL t i c) = map (fun j => nth j env 0%Z) (seq i (length c)).
Proof.
  intros env t c. induction c as [|e c IH]; intros i H; simpl; [reflexivity|].
  rewrite H, (IH (S i) H). reflexivity.
Qed.

Lemma seq_nth_app : forall (s p : list Z) pre, map (fun j => nth j (pre ++ s ++ p) 0%Z)
  (seq (length pre) (length s)) = s.
Proof.
  intros s p. induction s as [|a s IH]; intros pre; simpl; [reflexivity|].
  f_equal.
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - specialize (IH (pre ++ [a])). rewrite <- app_assoc in IH. simpl in IH.
    rewrite lenA in IH. simpl in IH. rewrite Nat.add_1_r in IH. exact IH.
Qed.

Lemma guardL_len : forall t c i, length (guardL t i c) = length c.
Proof. intros t c. induction c as [|e c IH]; intros i; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* Evaluation reads only the first N values of the environment. *)
Lemma eval_prefix : forall N env env', (forall i, (i < N)%nat -> nth i env 0%Z = nth i env' 0%Z) ->
  (forall e, bndE N e = true -> evalE env e = evalE env' e) /\
  (forall c, bndF N c = true -> evalF env c = evalF env' c).
Proof.
  intros N env env' H.
  apply (ef_mut (fun e => bndE N e = true -> evalE env e = evalE env' e)
                (fun c => bndF N c = true -> evalF env c = evalF env' c)); simpl;
    intros; repeat match goal with
      | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H end;
    try reflexivity.
  - apply H. apply Nat.ltb_lt. assumption.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1, H2 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
  - rewrite H0, H1 by assumption. reflexivity.
Qed.

Lemma firstn_nth_eq : forall j (l l' : list Z) i, firstn j l = firstn j l' -> (i < j)%nat ->
  nth i l 0%Z = nth i l' 0%Z.
Proof.
  induction j as [|j IH]; intros l l' i H Hi; [lia|].
  destruct l as [|a l], l' as [|b l']; simpl in H; try discriminate; [reflexivity|].
  injection H as -> H. destruct i as [|i]; simpl; [reflexivity|]. apply (IH l l' i H). lia.
Qed.

Lemma inRi_ext : forall r i (p p' : list Z), (forall j, (i <= j < i + length r)%nat -> nth j p 0%Z = nth j p' 0%Z) ->
  inRi i r p = inRi i r p'.
Proof.
  intros r. induction r as [|[lo hi] r IH]; intros i p p' H; simpl; [reflexivity|].
  simpl in H. rewrite (H i) by lia. rewrite (IH (S i) p p'); [reflexivity|]. intros j Hj. apply H. lia.
Qed.

Lemma inR_prefix : forall r (p p' : list Z), firstn (length r) p = firstn (length r) p' -> inR r p = inR r p'.
Proof.
  intros r p p' H. unfold inR. apply inRi_ext. intros j Hj. apply (firstn_nth_eq (length r)); [exact H | lia].
Qed.

Lemma firstn_len_app : forall (t u : list Z), firstn (length t) (t ++ u) = t.
Proof. intros t u. induction t as [|a t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma firstn_idem : forall j (l : list Z), firstn j (firstn j l) = firstn j l.
Proof.
  induction j as [|j IH]; intros l; [reflexivity|]. destruct l as [|a l]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* gsm's loop: keep the elements f accepts, and only the first one it rejects. *)
Fixpoint keep1 (f : list Z -> bool) (seen : bool) (l : list (list Z)) : list (list Z) :=
  match l with
  | [] => []
  | p :: l' => if f p then p :: keep1 f seen l'
               else if seen then keep1 f seen l' else p :: keep1 f true l'
  end.

Lemma keep1_incl : forall f b l x, In x (keep1 f b l) -> In x l.
Proof.
  intros f b l. revert b. induction l as [|p l IH]; intros b x H; simpl in *; [exact H|].
  destruct (f p); [destruct H as [H | H]; [left; exact H | right; exact (IH b x H)]|].
  destruct b; [right; exact (IH true x H)|]. destruct H as [H | H]; [left; exact H | right; exact (IH true x H)].
Qed.

Lemma keep1_in : forall f b l x, In x l -> f x = true -> In x (keep1 f b l).
Proof.
  intros f b l. revert b. induction l as [|p l IH]; intros b x H Hf; simpl in *; [exact H|].
  destruct H as [<- | H].
  - rewrite Hf. left. reflexivity.
  - destruct (f p); [right; exact (IH b x H Hf)|]. destruct b; [exact (IH true x H Hf)|].
    right. exact (IH true x H Hf).
Qed.

Lemma keep1_out : forall f l x, In x l -> f x = false -> exists y, In y (keep1 f false l) /\ f y = false.
Proof.
  intros f l. induction l as [|p l IH]; intros x H Hf; simpl in *; [contradiction|].
  destruct (f p) eqn:E.
  - destruct H as [<- | H]; [congruence|]. destruct (IH x H Hf) as [y [Hy Ry]].
    exists y. split; [right; exact Hy | exact Ry].
  - exists p. split; [left; reflexivity | exact E].
Qed.

(* ---- The ranged registry: shape, fragment, and its steps. ---- *)

Section Ranged.
  Variable C : list Z.
  Variable P : prog.
  Variable n m : nat.
  Variable rg : nat -> list (Z * Z).

  Local Notation Q := (ranged n rg P).
  Local Notation nk := (length (pk P)).

  Lemma bnd_rtest : forall N r i, (n + i + length r <= N)%nat -> bndF N (rtest n i r) = true.
  Proof.
    intros N r. induction r as [|[lo hi] r IH]; intros i H; simpl; [reflexivity|].
    simpl in H. assert (E : Nat.ltb (n + i) N = true) by (apply Nat.ltb_lt; lia).
    rewrite E, (IH (S i)) by lia. reflexivity.
  Qed.

  Lemma o_rtest : forall r i, (forall lo hi, In (lo, hi) r -> In lo C /\ In hi C) -> oF C (rtest n i r) = true.
  Proof.
    intros r. induction r as [|[lo hi] r IH]; intros i H; simpl; [reflexivity|].
    destruct (H lo hi (or_introl eq_refl)) as [Hl Hh].
    assert (El : existsb (Z.eqb lo) C = true) by (apply existsb_exists; exists lo; split; [exact Hl | apply Z.eqb_refl]).
    assert (Eh : existsb (Z.eqb hi) C = true) by (apply existsb_exists; exists hi; split; [exact Hh | apply Z.eqb_refl]).
    rewrite El, Eh, (IH (S i)); [reflexivity|]. intros a b Hab. apply H. right. exact Hab.
  Qed.

  Lemma bnd_guardL : forall N t c i, bndF N t = true -> forallb (bndE N) c = true ->
    (i + length c <= N)%nat -> forallb (bndE N) (guardL t i c) = true.
  Proof.
    intros N t c. induction c as [|e c IH]; intros i Ht Hc Hi; simpl; [reflexivity|].
    simpl in Hc, Hi. apply andb_true_iff in Hc as [He Hc].
    rewrite Ht, He, (IH (S i) Ht Hc) by lia. simpl. rewrite andb_true_r. apply Nat.ltb_lt. lia.
  Qed.

  Lemma o_guardL : forall t c i, oF C t = true -> forallb (oE C) c = true ->
    forallb (oE C) (guardL t i c) = true.
  Proof.
    intros t c. induction c as [|e c IH]; intros i Ht Hc; simpl; [reflexivity|].
    simpl in Hc. apply andb_true_iff in Hc as [He Hc]. rewrite Ht, He, (IH (S i) Ht Hc). reflexivity.
  Qed.

  (* The ranged registry is well formed. *)
  Theorem range_wf : wf P n m = true -> (forall k, (length (rg k) <= m)%nat) -> wf Q n m = true.
  Proof.
    intros Hw Hr. unfold wf in *. simpl. apply andb_true_iff in Hw as [Hw H4].
    apply andb_true_iff in Hw as [Hw H3]. apply andb_true_iff in Hw as [H1 H2].
    rewrite H2, H3, H4, !andb_true_r. clear H2 H3 H4. generalize 0%nat as k0. revert H1.
    generalize (pk P) as ks. induction ks as [|c ks IH]; intros H1 k0; simpl; [reflexivity|].
    simpl in H1. apply andb_true_iff in H1 as [Hc H1]. apply andb_true_iff in Hc as [Hl Hb].
    apply Nat.eqb_eq in Hl. rewrite guardL_len, Hl, Nat.eqb_refl, (IH H1). simpl.
    rewrite andb_true_r. apply bnd_guardL; [apply bnd_rtest; specialize (Hr k0); lia | exact Hb | lia].
  Qed.

  (* In the fragment, when P is and the bounds are declared constants. *)
  Theorem range_frag : ord_frag C P = true ->
    (forall k lo hi, In (lo, hi) (rg k) -> In lo C /\ In hi C) -> ord_frag C Q = true.
  Proof.
    intros Ho Hb. unfold ord_frag in *. simpl. apply andb_true_iff in Ho as [Ho H3].
    apply andb_true_iff in Ho as [H1 H2]. rewrite H2, H3, !andb_true_r. clear H2 H3.
    generalize 0%nat as k0. revert H1. generalize (pk P) as ks.
    induction ks as [|c ks IH]; intros H1 k0; simpl; [reflexivity|].
    simpl in H1. apply andb_true_iff in H1 as [Hc H1]. rewrite (IH H1), andb_true_r.
    apply o_guardL; [apply o_rtest; intros lo hi H; exact (Hb k0 lo hi H) | exact Hc].
  Qed.

  (* Each ranged kind still reads only its declared parameters. *)
  Theorem range_reads : wf P n m = true -> reads n rg P = true -> reads n rg Q = true.
  Proof.
    intros Hw. destruct (wf_parts P n m Hw) as [Hk _]. unfold reads. simpl.
    generalize 0%nat as k0. revert Hk. generalize (pk P) as ks.
    induction ks as [|c ks IH]; intros Hk k0 H; simpl; [reflexivity|].
    simpl in H. apply andb_true_iff in H as [Hc H].
    rewrite (IH (fun c' Hc' => Hk c' (or_intror Hc')) (S k0) H), andb_true_r.
    destruct (Hk c (or_introl eq_refl)) as [Hl _].
    apply bnd_guardL; [apply bnd_rtest; lia | exact Hc | lia].
  Qed.

  (* ---- The steps of the ranged registry. ---- *)

  Section Steps.
    Hypothesis Hw : wf P n m = true.

    Lemma kind_len : forall k c, nth_error (pk P) k = Some c -> length c = n.
    Proof.
      intros k c Hc. destruct (wf_parts P n m Hw) as [Hk _]. exact (proj1 (Hk c (nth_error_In _ _ Hc))).
    Qed.

    (* Outside the ranges, the event does nothing. *)
    Theorem range_out_step : forall k q s, (k < nk)%nat -> length q = m -> inR (rg k) q = false ->
      length s = n -> sap Q m (k, q) s = s.
    Proof.
      intros k q s Hk Hq Hr Hs. unfold sap. simpl. rewrite rngks_nth. simpl.
      destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      simpl. rewrite Hq, Nat.eqb_refl. rewrite guardL_false.
      - rewrite (kind_len k c Hc), <- Hs. exact (seq_nth_app s q []).
      - rewrite <- Hs, rtest_eval. exact Hr.
    Qed.

    (* In the ranges, it is P's event. *)
    Theorem range_in_step : forall k p s, inR (rg k) p = true -> length s = n ->
      sap Q m (k, p) s = sap P m (k, p) s.
    Proof.
      intros k p s Hr Hs. unfold sap. simpl. rewrite rngks_nth. simpl.
      destruct (nth_error (pk P) k) as [c|] eqn:Hc; [|reflexivity]. simpl.
      destruct (Nat.eqb (length p) m); [|reflexivity]. apply guardL_true.
      rewrite <- Hs, rtest_eval. exact Hr.
    Qed.

    (* Every assignment outside the ranges has the same governed step: repair alone. *)
    Theorem range_out_gov : forall K k q s, (k < nk)%nat -> length q = m -> inR (rg k) q = false ->
      length s = n -> govK (sap Q m) (srp Q) K (k, q) s = itr K (srp Q) s.
    Proof. intros K k q s Hk Hq Hr Hs. unfold govK. rewrite (range_out_step k q s Hk Hq Hr Hs). reflexivity. Qed.

    Theorem range_same_step : forall K k q1 q2, (k < nk)%nat -> length q1 = m -> length q2 = m ->
      inR (rg k) q1 = false -> inR (rg k) q2 = false -> SameStep n (sap Q m) (srp Q) K k q1 q2.
    Proof.
      intros K k q1 q2 Hk H1 H2 R1 R2 s Hs.
      rewrite (range_out_gov K k q1 s Hk H1 R1 Hs), (range_out_gov K k q2 s Hk H2 R2 Hs). reflexivity.
    Qed.

    (* A kind that reads only its declared parameters: the rest of the assignment is not read. *)
    Theorem range_prefix_step : reads n rg P = true -> forall k p p' s, length p = m -> length p' = m ->
      firstn (length (rg k)) p = firstn (length (rg k)) p' -> length s = n ->
      sap Q m (k, p) s = sap Q m (k, p') s.
    Proof.
      intros Hrd k p p' s Hp Hp' Hpre Hs. pose proof (range_reads Hw Hrd) as RQ. unfold reads in RQ. simpl in RQ.
      unfold sap. simpl. destruct (nth_error (rngks n rg 0 (pk P)) k) as [c|] eqn:Hc; [|reflexivity].
      simpl. rewrite Hp, Hp', Nat.eqb_refl. apply map_ext_in. intros e He.
      assert (Hn : forall i, (i < n + length (rg k))%nat -> nth i (s ++ p) 0%Z = nth i (s ++ p') 0%Z).
      { intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hl | Hl].
        - rewrite !app_nth1 by lia. reflexivity.
        - rewrite !app_nth2 by lia. apply (firstn_nth_eq (length (rg k))); [exact Hpre | lia]. }
      apply (proj1 (eval_prefix (n + length (rg k)) _ _ Hn)).
      exact (readsk_spec n rg _ 0 k c e RQ Hc He).
    Qed.

    Hypothesis Hrd : reads n rg P = true.
    Hypothesis Hr : forall k, (length (rg k) <= m)%nat.
    Hypothesis Hb : forall k lo hi, In (lo, hi) (rg k) -> In lo C /\ In hi C.
    Hypothesis Ho : ord_frag C P = true.

    Lemma range_shaped : Shaped n m nk (sap Q m) (srp Q) (svd Q).
    Proof.
      pose proof (prog_shaped Q n m (range_wf Hw Hr)) as H. simpl in H. rewrite rngks_len in H. exact H.
    Qed.

    Lemma range_ordinv : OrdInv C n (sap Q m) (srp Q) (svd Q).
    Proof. exact (ord_frag_sound C Q n m (range_wf Hw Hr) (range_frag Ho Hb)). Qed.

    (* What gsm's list of assignments must satisfy, per kind: inside the representative
       assignments; for each in-range one, one that agrees on the declared parameters; an
       out-of-range one if there is any. *)
    Definition RangeList (N : nat) (PL : nat -> list (list Z)) : Prop :=
      forall k, (k < nk)%nat ->
        incl (PL k) (tup (reps N C) m) /\
        (forall p, In p (tup (reps N C) m) -> inR (rg k) p = true ->
           exists p', In p' (PL k) /\ firstn (length (rg k)) p' = firstn (length (rg k)) p) /\
        (forall q, In q (tup (reps N C) m) -> inR (rg k) q = false ->
           exists q', In q' (PL k) /\ inR (rg k) q' = false).

    Lemma rangelist_covers : forall N PL K k, RangeList N PL -> (k < nk)%nat ->
      Covers n (sap Q m) (srp Q) K k (tup (reps N C) m) (PL k).
    Proof.
      intros N PL K k HL Hk p Hp. destruct (HL k Hk) as [Hi [Hin Hout]].
      pose proof (tup_len' _ _ _ Hp) as Lp. destruct (inR (rg k) p) eqn:E.
      - destruct (Hin p Hp E) as [p' [Hp' Pre]]. exists p'. split; [exact Hp'|].
        intros s Hs. unfold govK. rewrite (range_prefix_step Hrd k p p' s Lp (tup_len' _ _ _ (Hi p' Hp'))
                                             (eq_sym Pre) Hs). reflexivity.
      - destruct (Hout p Hp E) as [q' [Hq' E']]. exists q'. split; [exact Hq'|].
        exact (range_same_step K k p q' Hk Lp (tup_len' _ _ _ (Hi q' Hq')) E E').
    Qed.

    (* The reduced checks return the full checks' boolean. *)
    Theorem range_cc1v : forall K N Ib PL, RangeList N PL ->
      cc1v_checkP C n nk (sap Q m) (srp Q) (svd Q) K N Ib PL =
      cc1v_check C n m nk (sap Q m) (srp Q) (svd Q) K N Ib.
    Proof.
      intros K N Ib PL HL. apply (cover_full_cc1v C n m nk _ _ _ range_shaped).
      - intros k Hk. exact (proj1 (HL k Hk)).
      - intros k Hk. exact (rangelist_covers N PL K k HL Hk).
    Qed.

    Theorem range_idemv : forall K N k PL, RangeList N PL -> (k < nk)%nat ->
      idemv_checkP C n (sap Q m) (srp Q) (svd Q) K N k (PL k) =
      idemv_check C n m (sap Q m) (srp Q) (svd Q) K N k.
    Proof.
      intros K N k PL HL Hk. apply (cover_full_idemv C n m nk _ _ _ range_shaped).
      - exact (proj1 (HL k Hk)).
      - exact (rangelist_covers N PL K k HL Hk).
    Qed.

    (* Exact: the reduced CC1 check passes iff CC1 at every valid integer state, for every two
       parameter values. *)
    Theorem range_cc1_exact : forall K N Ib PL, (n + 2 * m <= N)%nat -> RangeList N PL ->
      (CC1VZ n m nk (sap Q m) (srp Q) (svd Q) K (fun a b => Ib a b = true) <->
       cc1v_checkP C n nk (sap Q m) (srp Q) (svd Q) K N Ib PL = true).
    Proof.
      intros K N Ib PL HN HL. rewrite (range_cc1v K N Ib PL HL), cc1v_check_spec.
      exact (cc1_valid_abs C n m nk _ _ _ range_shaped range_ordinv K N _ HN).
    Qed.

    (* Given repair within K steps over the representatives: iff runs from every valid integer
       state converge up to reordering of independent events. *)
    Theorem range_gsm_exact : forall K N Ib PL, (n + 2 * m <= N)%nat -> TermD C n (srp Q) (svd Q) K N ->
      RangeList N PL ->
      (cc1v_checkP C n nk (sap Q m) (srp Q) (svd Q) K N Ib PL = true <->
       RunConvZ n m nk (sap Q m) (srp Q) (svd Q) K (fun a b => Ib a b = true)).
    Proof.
      intros K N Ib PL HN HD HL. rewrite (range_cc1v K N Ib PL HL), cc1v_check_spec.
      exact (gsm_abs_exact C n m nk _ _ _ K N _ range_shaped range_ordinv HN HD).
    Qed.

    Theorem range_idem_exact : forall K N k PL, (n + m <= N)%nat -> RangeList N PL -> (k < nk)%nat ->
      (IdemVZ n m (sap Q m) (srp Q) (svd Q) K k <->
       idemv_checkP C n (sap Q m) (srp Q) (svd Q) K N k (PL k) = true).
    Proof.
      intros K N k PL HN HL Hk. rewrite (range_idemv K N k PL HL Hk), idemv_check_spec.
      exact (idem_valid_abs C n m nk _ _ _ range_shaped range_ordinv K N k HN).
    Qed.

    Theorem range_idem_runtime : forall K N k PL, (n + m <= N)%nat -> TermD C n (srp Q) (svd Q) K N ->
      RangeList N PL -> (k < nk)%nat ->
      ((forall s p, length s = n -> length p = m ->
          govK (apR m nk (sap Q m) (srp Q) K) (srp Q) K (k, p)
            (govK (apR m nk (sap Q m) (srp Q) K) (srp Q) K (k, p) s) =
          govK (apR m nk (sap Q m) (srp Q) K) (srp Q) K (k, p) s) <->
       idemv_checkP C n (sap Q m) (srp Q) (svd Q) K N k (PL k) = true).
    Proof.
      intros K N k PL HN HD HL Hk. rewrite (range_idemv K N k PL HL Hk), idemv_check_spec.
      exact (idem_runtime_abs C n m nk _ _ _ K N k range_shaped range_ordinv HN HD Hk).
    Qed.

    (* On the values in range, the ranged registry's guarantee is P's. *)
    Theorem range_cc1_in : forall K I, CC1VZ n m nk (sap Q m) (srp Q) (svd Q) K I ->
      forall s k1 p1 k2 p2, length s = n -> svd P s = true -> (k1 < nk)%nat -> (k2 < nk)%nat ->
        length p1 = m -> length p2 = m -> inR (rg k1) p1 = true -> inR (rg k2) p2 = true -> I k1 k2 ->
        govK (sap P m) (srp P) K (k2, p2) (govK (sap P m) (srp P) K (k1, p1) s) =
        govK (sap P m) (srp P) K (k1, p1) (govK (sap P m) (srp P) K (k2, p2) s).
    Proof.
      intros K I H s k1 p1 k2 p2 Hs Hv H1 H2 L1 L2 R1 R2 HI.
      assert (E : forall k p t, inR (rg k) p = true -> length t = n ->
                govK (sap P m) (srp P) K (k, p) t = govK (sap Q m) (srp Q) K (k, p) t).
      { intros k p t R Ht. unfold govK. rewrite (range_in_step k p t R Ht). reflexivity. }
      rewrite (E k1 p1 s R1 Hs), (E k2 p2 s R2 Hs).
      rewrite (E k2 p2 _ R2 (G_len n m nk _ _ _ range_shaped K (k1, p1) s Hs)).
      rewrite (E k1 p1 _ R1 (G_len n m nk _ _ _ range_shaped K (k2, p2) s Hs)).
      exact (H s k1 p1 k2 p2 Hs Hv H1 H2 L1 L2 HI).
    Qed.

    Theorem range_idem_in : forall K k, IdemVZ n m (sap Q m) (srp Q) (svd Q) K k ->
      forall s p, length s = n -> svd P s = true -> length p = m -> inR (rg k) p = true ->
        govK (sap P m) (srp P) K (k, p) (govK (sap P m) (srp P) K (k, p) s) =
        govK (sap P m) (srp P) K (k, p) s.
    Proof.
      intros K k H s p Hs Hv Hp R.
      assert (E : forall t, length t = n ->
                govK (sap P m) (srp P) K (k, p) t = govK (sap Q m) (srp Q) K (k, p) t).
      { intros t Ht. unfold govK. rewrite (range_in_step k p t R Ht). reflexivity. }
      rewrite (E s Hs), (E _ (G_len n m nk _ _ _ range_shaped K (k, p) s Hs)).
      exact (H s p Hs Hv Hp).
    Qed.

    (* ---- Given repair within K steps, the out-of-range assignment can be dropped too. ---- *)

    Definition RangeListIn (N : nat) (PL : nat -> list (list Z)) : Prop :=
      forall k, (k < nk)%nat ->
        incl (PL k) (tup (reps N C) m) /\
        (forall p, In p (tup (reps N C) m) -> inR (rg k) p = true ->
           exists p', In p' (PL k) /\ firstn (length (rg k)) p' = firstn (length (rg k)) p).

    Lemma itr_valid_fix : forall K t, svd Q t = true -> itr K (srp Q) t = t.
    Proof. intros K t Hv. apply itr_fix. unfold srp. rewrite Hv. reflexivity. Qed.

    (* At a valid state, an out-of-range event is the identity. *)
    Lemma range_out_valid : forall K k q t, (k < nk)%nat -> length q = m -> inR (rg k) q = false ->
      length t = n -> svd Q t = true -> govK (sap Q m) (srp Q) K (k, q) t = t.
    Proof.
      intros K k q t Hk Hq R Ht Hv. rewrite (range_out_gov K k q t Hk Hq R Ht). exact (itr_valid_fix K t Hv).
    Qed.

    Lemma inonly_prefix : forall N PL K k p, RangeListIn N PL -> (k < nk)%nat ->
      In p (tup (reps N C) m) -> inR (rg k) p = true ->
      exists p', In p' (PL k) /\ SameStep n (sap Q m) (srp Q) K k p p'.
    Proof.
      intros N PL K k p HL Hk Hp R. destruct (HL k Hk) as [Hi Hin].
      destruct (Hin p Hp R) as [p' [Hp' Pre]]. exists p'. split; [exact Hp'|].
      intros s Hs. unfold govK. rewrite (range_prefix_step Hrd k p p' s (tup_len' _ _ _ Hp)
                                           (tup_len' _ _ _ (Hi p' Hp')) (eq_sym Pre) Hs). reflexivity.
    Qed.

    Theorem range_inonly_cc1v : forall K N Ib PL, TermK (srp Q) (svd Q) n K -> RangeListIn N PL ->
      cc1v_checkP C n nk (sap Q m) (srp Q) (svd Q) K N Ib PL =
      cc1v_check C n m nk (sap Q m) (srp Q) (svd Q) K N Ib.
    Proof.
      intros K N Ib PL HT HL. rewrite <- cc1v_checkP_full. apply eq_iff_eq_true.
      rewrite !cc1v_checkP_spec. split.
      - intros H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 HI.
        assert (Ls : length s = n) by exact (tup_len' _ _ _ Hs).
        pose proof (tup_len' _ _ _ Hp1) as L1. pose proof (tup_len' _ _ _ Hp2) as L2.
        pose proof (G_len n m nk _ _ _ range_shaped K (k1, p1) s Ls) as G1.
        pose proof (G_len n m nk _ _ _ range_shaped K (k2, p2) s Ls) as G2.
        assert (V : forall e, svd Q (govK (sap Q m) (srp Q) K e s) = true).
        { intros e. apply HT. apply (sh_len_ap n m nk _ _ _ range_shaped). exact Ls. }
        destruct (inR (rg k1) p1) eqn:R1; [destruct (inR (rg k2) p2) eqn:R2|].
        + destruct (inonly_prefix N PL K k1 p1 HL H1 Hp1 R1) as [q1 [Hq1 E1]].
          destruct (inonly_prefix N PL K k2 p2 HL H2 Hp2 R2) as [q2 [Hq2 E2]].
          rewrite (E1 s Ls), (E2 s Ls).
          rewrite (E2 _ (G_len n m nk _ _ _ range_shaped K (k1, q1) s Ls)).
          rewrite (E1 _ (G_len n m nk _ _ _ range_shaped K (k2, q2) s Ls)).
          exact (H s k1 q1 k2 q2 Hs Hv H1 H2 Hq1 Hq2 HI).
        + rewrite (range_out_valid K k2 p2 s H2 L2 R2 Ls Hv).
          exact (range_out_valid K k2 p2 _ H2 L2 R2 G1 (V _)).
        + rewrite (range_out_valid K k1 p1 s H1 L1 R1 Ls Hv).
          exact (eq_sym (range_out_valid K k1 p1 _ H1 L1 R1 G2 (V _))).
      - apply (cc1vp_cover C n m nk _ _ _ range_shaped). intros k Hk. apply covers_incl.
        exact (proj1 (HL k Hk)).
    Qed.

    Theorem range_inonly_idemv : forall K N k PL, RangeListIn N PL -> (k < nk)%nat ->
      idemv_checkP C n (sap Q m) (srp Q) (svd Q) K N k (PL k) =
      idemv_check C n m (sap Q m) (srp Q) (svd Q) K N k.
    Proof.
      intros K N k PL HL Hk. rewrite <- idemv_checkP_full. apply eq_iff_eq_true.
      rewrite !idemv_checkP_spec. split.
      - intros H s p Hs Hv Hp. assert (Ls : length s = n) by exact (tup_len' _ _ _ Hs).
        destruct (inR (rg k) p) eqn:R.
        + destruct (inonly_prefix N PL K k p HL Hk Hp R) as [q [Hq E]].
          rewrite (E s Ls), (E _ (G_len n m nk _ _ _ range_shaped K (k, q) s Ls)). exact (H s q Hs Hv Hq).
        + pose proof (tup_len' _ _ _ Hp) as Lp.
          rewrite (range_out_valid K k p s Hk Lp R Ls Hv). exact (range_out_valid K k p s Hk Lp R Ls Hv).
      - apply (idemvp_cover C n m nk _ _ _ range_shaped). apply covers_incl. exact (proj1 (HL k Hk)).
    Qed.

    (* With gsm's check of repair within K steps (TermD) in place of TermK. *)
    Theorem range_inonly_cc1_exact : forall K N Ib PL, (n + 2 * m <= N)%nat ->
      TermD C n (srp Q) (svd Q) K N -> RangeListIn N PL ->
      (CC1VZ n m nk (sap Q m) (srp Q) (svd Q) K (fun a b => Ib a b = true) <->
       cc1v_checkP C n nk (sap Q m) (srp Q) (svd Q) K N Ib PL = true).
    Proof.
      intros K N Ib PL HN HD HL.
      pose proof (proj2 (term_abs C n m nk _ _ _ range_shaped range_ordinv K N ltac:(lia)) HD) as HT.
      rewrite (range_inonly_cc1v K N Ib PL HT HL), cc1v_check_spec.
      exact (cc1_valid_abs C n m nk _ _ _ range_shaped range_ordinv K N _ HN).
    Qed.
  End Steps.

  (* ---- gsm's list (params.go, absEventList). ---- *)

  (* For kind k: every assignment of representatives to its declared parameters in range, and
     the first one outside the ranges, padded to m with d. *)
  Definition gsm_params (N : nat) (d : Z) (k : nat) : list (list Z) :=
    map (fun t => t ++ repeat d (m - length (rg k)))
        (keep1 (inR (rg k)) false (tup (reps N C) (length (rg k)))).

  Theorem gsm_params_ok : forall N d, In d (reps N C) -> (forall k, (length (rg k) <= m)%nat) ->
    RangeList N (gsm_params N d).
  Proof.
    intros N d Hd Hr k _. set (j := length (rg k)). set (pad := repeat d (m - j)).
    assert (Pad : forall t, In t (tup (reps N C) j) -> In (t ++ pad) (tup (reps N C) m) /\
                  firstn j (t ++ pad) = t /\ inR (rg k) (t ++ pad) = inR (rg k) t).
    { intros t Ht. apply tup_spec in Ht. destruct Ht as [Lt It].
      assert (F : firstn j (t ++ pad) = t) by (rewrite <- Lt; apply firstn_len_app).
      split; [|split; [exact F|]].
      - apply tup_spec. split; [rewrite lenA, Lt; unfold pad; rewrite repeat_length; specialize (Hr k); fold j in Hr; lia|].
        intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exact (It x Hx)|].
        unfold pad in Hx. apply repeat_spec in Hx. subst x. exact Hd.
      - apply inR_prefix. fold j. rewrite F, <- Lt, firstn_all. reflexivity. }
    assert (Cut : forall p, In p (tup (reps N C) m) -> In (firstn j p) (tup (reps N C) j) /\
                  inR (rg k) (firstn j p) = inR (rg k) p).
    { intros p Hp. apply tup_spec in Hp. destruct Hp as [Lp Ip]. split.
      - apply tup_spec. split; [rewrite firstn_length, Lp; specialize (Hr k); fold j in Hr; lia|].
        intros x Hx. apply Ip. rewrite <- (firstn_skipn j p). apply in_or_app. left. exact Hx.
      - apply inR_prefix. fold j. apply firstn_idem. }
    split; [|split].
    - intros p' Hp'. unfold gsm_params in Hp'. fold j pad in Hp'. apply in_map_iff in Hp'.
      destruct Hp' as [t [<- Ht]]. exact (proj1 (Pad t (keep1_incl _ _ _ _ Ht))).
    - intros p Hp R. destruct (Cut p Hp) as [Ct Rt]. exists (firstn j p ++ pad). split.
      + unfold gsm_params. fold j pad. apply (in_map (fun t => t ++ pad)). apply keep1_in; [exact Ct | rewrite Rt; exact R].
      + exact (proj1 (proj2 (Pad _ Ct))).
    - intros q Hq R. destruct (Cut q Hq) as [Ct Rt]. rewrite <- Rt in R.
      destruct (keep1_out _ _ _ Ct R) as [y [Hy Ry]]. exists (y ++ pad). split.
      + unfold gsm_params. fold j pad. apply (in_map (fun t => t ++ pad)). exact Hy.
      + rewrite (proj2 (proj2 (Pad y (keep1_incl _ _ _ _ Hy)))). exact Ry.
  Qed.
End Ranged.

(* ============================================================================================ *)
(* Non-vacuity: capped Restock(level) with gsm's declared range 0..10^9 for the level.          *)
(* ============================================================================================ *)

(* gsm's TestParamsAbstract_Capped: stock with cap 5, Restock(level) with level in 0..10^9; the
   constants are the cap and the level's bounds, cutoff N = n + 2m = 3. *)
Definition crg (_ : nat) : list (Z * Z) := [(0%Z, 1000000000%Z)].
Definition crngC : list Z := [0%Z; 5%Z; 1000000000%Z].
Definition crng : prog := ranged 1 crg capped.

Theorem crng_frag : wf capped 1 1 = true /\ ord_frag crngC capped = true /\ reads 1 crg capped = true /\
  wf crng 1 1 = true /\ ord_frag crngC crng = true.
Proof. repeat split; reflexivity. Qed.

Lemma crg_len : forall k, (length (crg k) <= 1)%nat.
Proof. intros k. simpl. lia. Qed.

Lemma crg_bounds : forall k lo hi, In (lo, hi) (crg k) -> In lo crngC /\ In hi crngC.
Proof. intros k lo hi [H | []]. injection H as <- <-. split; simpl; tauto. Qed.

(* 15 representative levels; gsm checks 10: the 9 in range and one outside (gsm's
   Families[0].Instances = 10). *)
Theorem crng_counts : length (tup (reps 3 crngC) 1) = 15%nat /\
  length (gsm_params crngC 1 crg 3 0%Z 0) = 10%nat /\
  length (filter (inR (crg 0)) (tup (reps 3 crngC) 1)) = 9%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma crng_list : RangeList crngC capped 1 crg 3 (gsm_params crngC 1 crg 3 0%Z).
Proof. apply gsm_params_ok; [vm_compute; tauto | exact crg_len]. Qed.

Theorem crng_cc1v_check :
  cc1v_checkP crngC 1 1 (sap crng 1) (srp crng) (svd crng) 1 3 (fun _ _ => true)
    (gsm_params crngC 1 crg 3 0%Z) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem crng_idemv_check :
  idemv_checkP crngC 1 (sap crng 1) (srp crng) (svd crng) 1 3 0 (gsm_params crngC 1 crg 3 0%Z 0) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem crng_term : TermD crngC 1 (srp crng) (svd crng) 1 3.
Proof. intros s Hs. revert s Hs. apply forallb_forall. vm_compute. reflexivity. Qed.

(* Two out-of-range representative levels, one step: repair alone. *)
Theorem crng_out_same : forall s, length s = 1%nat ->
  govK (sap crng 1) (srp crng) 1 (0%nat, [(-1)%Z]) s = itr 1 (srp crng) s /\
  govK (sap crng 1) (srp crng) 1 (0%nat, [1000000001%Z]) s = itr 1 (srp crng) s.
Proof.
  intros s Hs. split; apply (range_out_gov capped 1 1 crg eq_refl); solve [exact Hs | reflexivity | simpl; lia].
Qed.

(* CC1 at every valid integer stock, for every two integer levels, from the reduced check. *)
Theorem crng_cc1_valid : CC1VZ 1 1 1 (sap crng 1) (srp crng) (svd crng) 1 (fun _ _ => True).
Proof.
  pose proof (proj2 (range_cc1_exact crngC capped 1 1 crg eq_refl eq_refl crg_len crg_bounds eq_refl
                       1 3 (fun _ _ => true) _ ltac:(lia) crng_list) crng_cc1v_check) as H.
  intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 eq_refl).
Qed.

(* So capped's restocks commute at every valid stock for every two levels in 0..10^9. *)
Theorem crng_in_range : forall s p1 p2, length s = 1%nat -> svd capped s = true ->
  (0 <= p1 <= 1000000000)%Z -> (0 <= p2 <= 1000000000)%Z ->
  govK (sap capped 1) (srp capped) 1 (0%nat, [p2]) (govK (sap capped 1) (srp capped) 1 (0%nat, [p1]) s) =
  govK (sap capped 1) (srp capped) 1 (0%nat, [p1]) (govK (sap capped 1) (srp capped) 1 (0%nat, [p2]) s).
Proof.
  intros s p1 p2 Hs Hv R1 R2.
  assert (IR : forall p, (0 <= p <= 1000000000)%Z -> inR (crg 0) [p] = true).
  { intros p [A B]. unfold inR. simpl. apply Z.leb_le in A. apply Z.leb_le in B. rewrite A, B. reflexivity. }
  apply (range_cc1_in capped 1 1 crg eq_refl crg_len 1 (fun _ _ => True)
           crng_cc1_valid s 0 [p1] 0 [p2] Hs Hv); auto.
Qed.

(* Restock is idempotent at every valid integer stock, for every integer level. *)
Theorem crng_idem : IdemVZ 1 1 (sap crng 1) (srp crng) (svd crng) 1 0.
Proof.
  apply (proj2 (range_idem_exact crngC capped 1 1 crg eq_refl eq_refl crg_len crg_bounds eq_refl
                  1 3 0 _ ltac:(lia) crng_list ltac:(simpl; lia))).
  exact crng_idemv_check.
Qed.

(* Every permutation of restocks converges at run time from every integer stock. *)
Theorem crng_runtime : forall s0, length s0 = 1%nat -> forall es1 es2, Permutation es1 es2 ->
  Forall (InSig 1 1) es1 ->
  runT (govK (apR 1 1 (sap crng 1) (srp crng) 1) (srp crng) 1) es1 s0 =
  runT (govK (apR 1 1 (sap crng 1) (srp crng) 1) (srp crng) 1) es2 s0.
Proof.
  pose proof (range_shaped capped 1 1 crg eq_refl crg_len) as HS. simpl in HS.
  pose proof (range_ordinv crngC capped 1 1 crg eq_refl crg_len crg_bounds eq_refl) as HO. simpl in HO.
  apply (gsm_abs_sound_all crngC 1 1 1 _ _ _ 1 3 HS HO ltac:(lia) crng_term).
  pose proof (range_cc1v crngC capped 1 1 crg eq_refl eq_refl crg_len 1 3 (fun _ _ => true) _ crng_list) as E.
  pose proof (eq_trans (eq_sym E) crng_cc1v_check) as E1. clear E. rename E1 into E.
  apply cc1v_check_spec in E.
  intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (E s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 eq_refl).
Qed.

(* Given repair within one step, the in-range levels alone decide it too. *)
Theorem crng_inonly_check :
  cc1v_checkP crngC 1 1 (sap crng 1) (srp crng) (svd crng) 1 3 (fun _ _ => true)
    (fun k => filter (inR (crg k)) (tup (reps 3 crngC) 1)) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================================================ *)
(* Non-vacuity of a failure: Set(level) with range 0..5 does not commute.                       *)
(* ============================================================================================ *)

(* One variable (stock); Set(level): stock := level; invariant stock <= 5; repair stock := 5. *)
Definition setlvl : prog := mkProg [[Vr 1]] [Cst 5%Z] (FLe (Vr 0) (Cst 5%Z)).
Definition srg (_ : nat) : list (Z * Z) := [(0%Z, 5%Z)].
Definition setC : list Z := [0%Z; 5%Z].
Definition srng : prog := ranged 1 srg setlvl.

Theorem setlvl_frag : wf setlvl 1 1 = true /\ ord_frag setC setlvl = true /\ reads 1 srg setlvl = true.
Proof. repeat split; reflexivity. Qed.

Lemma srg_len : forall k, (length (srg k) <= 1)%nat.
Proof. intros k. simpl. lia. Qed.

Lemma srg_bounds : forall k lo hi, In (lo, hi) (srg k) -> In lo setC /\ In hi setC.
Proof. intros k lo hi [H | []]. injection H as <- <-. split; simpl; tauto. Qed.

(* The reduced check fails. *)
Theorem setlvl_check_fails :
  cc1v_checkP setC 1 1 (sap srng 1) (srp srng) (svd srng) 1 3 (fun _ _ => true)
    (gsm_params setC 1 srg 3 0%Z) = false.
Proof. vm_compute. reflexivity. Qed.

(* So CC1 fails over Z (range_cc1_exact), with a witness in range: Set(1) then Set(2) from 0. *)
Theorem setlvl_not_cc1 : ~ CC1VZ 1 1 1 (sap srng 1) (srp srng) (svd srng) 1 (fun _ _ => True) /\
  govK (sap srng 1) (srp srng) 1 (0%nat, [2%Z]) (govK (sap srng 1) (srp srng) 1 (0%nat, [1%Z]) [0%Z]) = [2%Z] /\
  govK (sap srng 1) (srp srng) 1 (0%nat, [1%Z]) (govK (sap srng 1) (srp srng) 1 (0%nat, [2%Z]) [0%Z]) = [1%Z].
Proof.
  split; [|split; reflexivity]. intros H.
  assert (H' : CC1VZ 1 1 1 (sap srng 1) (srp srng) (svd srng) 1 (fun a b => (fun _ _ => true) a b = true)).
  { intros s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 _. exact (H s k1 p1 k2 p2 Hs Hv H1 H2 Hp1 Hp2 I). }
  apply (range_cc1_exact setC setlvl 1 1 srg eq_refl eq_refl srg_len srg_bounds eq_refl 1 3 _ _ ltac:(lia)
           (gsm_params_ok setC setlvl 1 srg 3 0%Z ltac:(vm_compute; tauto) srg_len)) in H'.
  pose proof (eq_trans (eq_sym H') setlvl_check_fails) as E. discriminate.
Qed.

(* ============================================================================================ *)
(* Boundary: without repair within K steps, the out-of-range assignment is needed.              *)
(* ============================================================================================ *)

(* Two variables (a, b); Reset(p), p in 0..10: (a, b) := (9, 9); invariant a <= 5 and b <= 5;
   repair: if a > 5 then a := 5, else b := 5 (two steps from (9, 9)). With K = 1, repair does not
   reach a valid state; the in-range assignments alone pass the check, gsm's list (with one
   out-of-range assignment) fails it, and CC1 fails over Z. With K = 2, gsm's list passes. *)
Definition slow : prog := mkProg
  [[Cst 9%Z; Cst 9%Z]]
  [If (FLt (Cst 5%Z) (Vr 0)) (Cst 5%Z) (Vr 0); If (FLt (Cst 5%Z) (Vr 0)) (Vr 1) (Cst 5%Z)]
  (FAnd (FLe (Vr 0) (Cst 5%Z)) (FLe (Vr 1) (Cst 5%Z))).
Definition wrg (_ : nat) : list (Z * Z) := [(0%Z, 10%Z)].
Definition slowC : list Z := [0%Z; 5%Z; 9%Z; 10%Z].
Definition wslow : prog := ranged 2 wrg slow.

Theorem slow_frag : wf slow 2 1 = true /\ ord_frag slowC slow = true /\ reads 2 wrg slow = true.
Proof. repeat split; reflexivity. Qed.

Theorem slow_checks :
  ~ TermK (srp wslow) (svd wslow) 2 1 /\
  cc1v_checkP slowC 2 1 (sap wslow 1) (srp wslow) (svd wslow) 1 4 (fun _ _ => true)
    (fun k => filter (inR (wrg k)) (tup (reps 4 slowC) 1)) = true /\
  cc1v_checkP slowC 2 1 (sap wslow 1) (srp wslow) (svd wslow) 1 4 (fun _ _ => true)
    (gsm_params slowC 1 wrg 4 0%Z) = false /\
  cc1v_checkP slowC 2 1 (sap wslow 1) (srp wslow) (svd wslow) 2 4 (fun _ _ => true)
    (gsm_params slowC 1 wrg 4 0%Z) = true.
Proof.
  split; [|split; [|split]]; try (vm_compute; reflexivity).
  intros H. specialize (H [9%Z; 9%Z] eq_refl). vm_compute in H. discriminate.
Qed.

(* The witness: Reset(0) and the out-of-range Reset(-1) at the valid state (0, 0). *)
Theorem slow_diverges : ~ CC1VZ 2 1 1 (sap wslow 1) (srp wslow) (svd wslow) 1 (fun _ _ => True) /\
  govK (sap wslow 1) (srp wslow) 1 (0%nat, [0%Z]) (govK (sap wslow 1) (srp wslow) 1 (0%nat, [(-1)%Z]) [0%Z; 0%Z]) = [5%Z; 9%Z] /\
  govK (sap wslow 1) (srp wslow) 1 (0%nat, [(-1)%Z]) (govK (sap wslow 1) (srp wslow) 1 (0%nat, [0%Z]) [0%Z; 0%Z]) = [5%Z; 5%Z].
Proof.
  split; [|split; reflexivity]. intros H.
  specialize (H [0%Z; 0%Z] 0%nat [(-1)%Z] 0%nat [0%Z] eq_refl eq_refl ltac:(lia) ltac:(lia) eq_refl eq_refl I).
  vm_compute in H. discriminate.
Qed.
