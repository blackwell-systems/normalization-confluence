(* LocalTwoToken.v: no closed asynchronous run with two unstable vertices under local conditions
   (gap 3 of REGIME-AUDIT.md, LossyNetworks P2, progress). Axiom-free.

   Setting: the lens model of LocalSigned.v and LocalFairSettlement.v (states Sh read through get
   and set on the vertex list js, resolvers Fv, the synchronous map F = Fsync, the asynchronous
   step rupd j). Conditions:
     (A) NoLocalCycle js: no cycle in any local interaction graph G(x);
     (B) OutDeg1 js: every vertex of every G(x) has out-degree at most one (Hamming
         non-expansiveness of F, LocalSigned.outdeg_nonexpansive).
   A "token" is an unstable vertex; ucnt x counts them (LocalFairSettlement.ucnt, non-increasing
   along asynchronous runs by ucnt_mono). LocalFairSettlement.one_token_closed excludes closed runs
   that change the state from a state with at most one token. This file does the same for two.

   The proof. Fix the unique fixed point p (Shih and Dong). Call a token at v "good" at x when
   x_v <> p_v (firing it moves toward p) and "bad" otherwise. Write D(x) for the set of
   coordinates where x and p differ.
     not_both_bad    with two tokens, at least one is good: if both were bad, F(x) would be two
                     steps further from p than x, against non-expansiveness.
     tight           with one good token b and one bad token v (a G1 state), F(x) and x are at
                     the same distance from p.
     tight_arc       at a tight state, every j in D(x) has an out-arc in G(x), and its target i has
                     F_i(x) <> p_i (otherwise the synchronous step from flip j x would be too far
                     from p).
     head_arc        (rigidity) at a G1 state the bad token never points into D(x): every vertex
                     of D(x) + {v} would then have an out-arc inside D(x) + {v}, and G(x) would
                     have a cycle.
     G1_T, G1_H      G1 is preserved by every move that keeps two tokens: the good token passes
                     to a good receiver, the bad token to a bad receiver (head_arc).
     swap_TH         at a G1 state, "fire the good token, then the bad one" can be replaced by
                     "fire the bad token, then the good one", with the same end state and two
                     tokens throughout.
     W_sort, W_main  so a closed two-token walk through G1 states can be rearranged: all
                     bad-token moves first, H^h T^h; rotated to start between the two blocks,
                     T^h H^h; and pulling each H forward turns it into (T H)^h. Each pair "T then H"
                     from a state with tokens {b, v} is exactly the synchronous step F. So the
                     closed walk gives a synchronous periodic orbit through a state that is not
                     fixed, against LocalFairSettlement.sync_orbit_fixed.
     run_bad_or_dec  if no state of a two-token run is G1, every move fires a good token and the
                     distance to p strictly decreases, so the run cannot close.

   Results.
     two_token_closed            (A), (B), and at most two unstable vertices at x: no closed
                                 asynchronous run from x changes the state.
     two_token_no_closed_change  the same, as NoClosedChange (fun x => ucnt x <= 2).
     two_token_fair_settlement   every fair schedule from a start with at most two unstable
                                 vertices settles at the unique fixed point.
     fair_settles_once_two_tokens
                                 every fair run that ever reaches a state with at most two
                                 unstable vertices settles there.
     two_token_instance          non-vacuity: Shih and Ho's network (LocalFairSettlement.sh_F) has
                                 a state with exactly two unstable vertices, one good and one bad,
                                 and every fair schedule from it settles at 1111.
   What is NOT proved here: three or more tokens. For k >= 3 a bad token can pass to a good
   receiver (research/gap3-fair-settlement/K2.md), so the token types are not invariant and the
   argument above does not apply as it stands. Gap 3 stays open. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.DistributedCycles NC.CanonicalExecution NC.SignedResolver NC.LocalSigned.
Require Import NC.LocalFairSettlement.
Import ListNotations.

(* ============================================================================================ *)
(* Part 0. List utilities.                                                                      *)
(* ============================================================================================ *)

Lemma ltt_filter_zero : forall (f : nat -> bool) l, (forall t, In t l -> f t = false) -> length (filter f l) = 0.
Proof.
  intros f. induction l as [| d l IH]; intros H; [reflexivity |]. simpl.
  rewrite (H d (or_introl eq_refl)). apply IH. intros t Ht. apply H. right. exact Ht.
Qed.

Lemma ltt_filter_le1 : forall (f : nat -> bool) l c, NoDup l ->
  (forall t, In t l -> f t = true -> t = c) -> length (filter f l) <= 1.
Proof.
  intros f. induction l as [| d l IH]; intros c Hn H; [simpl; lia |].
  inversion Hn as [| ? ? Hd Hl]; subst. simpl.
  destruct (f d) eqn:E.
  - assert (d = c) by (apply H; [left; reflexivity | exact E]). subst d.
    simpl. rewrite ltt_filter_zero; [lia |]. intros t Ht. destruct (f t) eqn:Et; [| reflexivity].
    exfalso. assert (t = c) by (apply H; [right; exact Ht | exact Et]). subst. contradiction.
  - apply (IH c Hl). intros t Ht Et. apply H; [right; exact Ht | exact Et].
Qed.

(* Numbers of bad-token moves (true, "H") and good-token moves (false, "T") in a label list. *)
Fixpoint nH (l : list bool) : nat := match l with [] => 0 | a :: r => (if a then 1 else 0) + nH r end.
Fixpoint nT (l : list bool) : nat := match l with [] => 0 | a :: r => (if a then 0 else 1) + nT r end.

Lemma nH_nT : forall l, nH l + nT l = length l.
Proof. induction l as [| a l IH]; [reflexivity |]. destruct a; simpl; lia. Qed.

(* ============================================================================================ *)
(* Part 1. The lens setting: two tokens.                                                         *)
(* ============================================================================================ *)

Section Lens.
  Variable Sh : Type.
  Variable js : list nat.
  Variable get : nat -> Sh -> bool.
  Variable set : nat -> bool -> Sh -> Sh.
  Hypothesis get_set_eq : forall j x s, In j js -> get j (set j x s) = x.
  Hypothesis get_set_neq : forall j k x s, k <> j -> get k (set j x s) = get k s.
  Hypothesis sh_ext : forall s t, (forall j, In j js -> get j s = get j t) -> s = t.
  Variable Fv : nat -> Sh -> bool.

  Local Notation F := (Fsync bool Sh js set Fv).
  Local Notation ru := (rupd bool Sh js set Fv).
  Local Notation xw := (xr bool Sh js set Fv).
  Local Notation lar := (larc Sh get set Fv).
  Local Notation flp := (flip Sh get set).
  Local Notation uc := (ucnt Sh js get Fv).

  (* t is unstable at x. *)
  Definition un (x : Sh) (t : nat) : bool := negb (Bool.eqb (get t x) (Fv t x)).

  Lemma uc_un : forall x, uc x = length (filter (un x) js).
  Proof. reflexivity. Qed.

  (* Exactly the two distinct tokens a and c. *)
  Definition TwoTok (x : Sh) (a c : nat) : Prop :=
    In a js /\ In c js /\ a <> c /\ un x a = true /\ un x c = true /\
    forall t, In t js -> t <> a -> t <> c -> un x t = false.

  Lemma two_sym : forall x a c, TwoTok x a c -> TwoTok x c a.
  Proof.
    intros x a c (Ha & Hc & N & Ua & Uc & Uo). unfold TwoTok.
    repeat split; try assumption.
    - intro Q. apply N. symmetry. exact Q.
    - intros t Ht N1 N2. exact (Uo t Ht N2 N1).
  Qed.

  Lemma two_in : forall x a c t, TwoTok x a c -> In t js -> un x t = true -> t = a \/ t = c.
  Proof.
    intros x a c t (_ & _ & _ & _ & _ & Uo) Ht Ut.
    destruct (Nat.eq_dec t a) as [E | Na]; [left; exact E |].
    destruct (Nat.eq_dec t c) as [E | Nc]; [right; exact E |].
    rewrite (Uo t Ht Na Nc) in Ut. discriminate Ut.
  Qed.

  Lemma uc_ge2 : forall x a c, TwoTok x a c -> 2 <= uc x.
  Proof.
    intros x a c (Ha & Hc & N & Ua & Uc & _). rewrite uc_un.
    apply (two_le_length _ a c); [apply filter_In; tauto | apply filter_In; tauto | exact N].
  Qed.

  Lemma uc_le1 : NoDup js -> forall x c, (forall t, In t js -> un x t = true -> t = c) -> uc x <= 1.
  Proof. intros Hnd x c H. rewrite uc_un. exact (ltt_filter_le1 (un x) js c Hnd H). Qed.

  Lemma uc_two : NoDup js -> forall x, uc x = 2 -> exists a c, TwoTok x a c.
  Proof.
    intros Hnd x H. rewrite uc_un in H.
    assert (Hsub : forall t, In t (filter (un x) js) -> In t js /\ un x t = true) by (intros t Ht; apply filter_In; exact Ht).
    assert (Hsup : forall t, In t js -> un x t = true -> In t (filter (un x) js)) by (intros t Ht Ut; apply filter_In; tauto).
    assert (Hnf : NoDup (filter (un x) js)) by (apply NoDup_filter; exact Hnd).
    destruct (filter (un x) js) as [| a [| c [| d l]]]; simpl in H; try discriminate H.
    destruct (Hsub a (or_introl eq_refl)) as [Ha Ua].
    destruct (Hsub c (or_intror (or_introl eq_refl))) as [Hc Uc].
    inversion Hnf as [| ? ? Na _]; subst.
    exists a, c. unfold TwoTok. repeat split; try assumption.
    - intro Q. subst c. apply Na. left. reflexivity.
    - intros t Ht Nta Ntc. destruct (un x t) eqn:Et; [| reflexivity]. exfalso.
      destruct (Hsup t Ht Et) as [Q | [Q | []]]; congruence.
  Qed.

  Lemma un_flip : forall a x t, In a js -> un (flp a x) t = xorb (un x t) (xorb (Nat.eqb a t) (lar x a t)).
  Proof.
    intros a x t Ha. unfold un, larc.
    rewrite (get_flip Sh js get set get_set_eq get_set_neq a t x Ha).
    destruct (get t x), (Fv t x), (Fv t (flp a x)), (Nat.eqb a t); reflexivity.
  Qed.

  Lemma noself : forall x a, AcyclicAt Sh js get set Fv x -> In a js -> lar x a a = false.
  Proof.
    intros x a Hac Ha. destruct (lar x a a) eqn:E; [| reflexivity]. exfalso.
    apply (Hac [a]); [intros u [<- | []]; exact Ha |].
    split; [discriminate | split; [constructor; [intros [] | constructor] |]].
    unfold cyc_ok, cpairs. cbn [cpf last forallb fst snd]. rewrite E. reflexivity.
  Qed.

  Lemma ru_fire : forall a x, In a js -> un x a = true -> ru a x = flp a x.
  Proof.
    intros a x Ha U. destruct (ru_cases Sh js get set get_set_eq get_set_neq sh_ext Fv a x Ha) as [[E _] | [_ E]];
      [| exact E].
    exfalso. unfold un in U. rewrite E, Bool.eqb_reflx in U. discriminate U.
  Qed.

  Lemma ru_noop : forall a x, un x a = false -> ru a x = x.
  Proof.
    intros a x U. destruct (in_dec Nat.eq_dec a js) as [Ha | Ha]; [| exact (rupd_out bool Sh js set Fv a x Ha)].
    destruct (ru_cases Sh js get set get_set_eq get_set_neq sh_ext Fv a x Ha) as [[_ E] | [N _]]; [exact E |].
    exfalso. unfold un in U. destruct (get a x), (Fv a x); simpl in U; congruence.
  Qed.

  Lemma un_true : forall x a, un x a = true -> Fv a x <> get a x.
  Proof. intros x a U E. unfold un in U. rewrite E, Bool.eqb_reflx in U. discriminate U. Qed.

  Lemma uc_xw_mono : NoDup js -> OutDeg1 Sh get set Fv js -> forall w x, uc (xw w x) <= uc x.
  Proof.
    intros Hnd Hod. induction w as [| a w IH]; intros x; [apply Nat.le_refl |].
    change (xw (a :: w) x) with (xw w (ru a x)).
    pose proof (IH (ru a x)). pose proof (ucnt_mono Sh js get set get_set_eq get_set_neq sh_ext Fv Hnd Hod a x). lia.
  Qed.

  (* Firing a token a of a two-token state: the token passes to a new vertex w, or the run loses
     at least one token (collision with c, or no out-arc). *)
  Lemma fire : NoDup js -> OutDeg1 Sh get set Fv js -> forall x a c, AcyclicAt Sh js get set Fv x -> TwoTok x a c ->
    (exists w, lar x a w = true /\ TwoTok (flp a x) w c) \/
    ((forall t, In t js -> un (flp a x) t = true -> t = c) /\ (lar x a c = true \/ un (flp a x) c = true)).
  Proof.
    intros Hnd Hod x a c Hac T. pose proof T as (Ha & Hc & Nac & Ua & Uc & Uo).
    assert (Self : lar x a a = false) by exact (noself x a Hac Ha).
    destruct (filter (lar x a) js) as [| w l] eqn:Ef.
    - (* no out-arc *)
      assert (No : forall t, In t js -> lar x a t = false).
      { intros t Ht. destruct (lar x a t) eqn:E; [| reflexivity]. exfalso.
        assert (In t (filter (lar x a) js)) by (apply filter_In; tauto). rewrite Ef in H. destruct H. }
      right. split.
      + intros t Ht U. rewrite (un_flip a x t Ha), (No t Ht) in U.
        destruct (Nat.eq_dec t a) as [-> | Na]; [rewrite Ua, Nat.eqb_refl in U; discriminate U |].
        destruct (Nat.eq_dec t c) as [E | Nc]; [exact E |].
        rewrite (Uo t Ht Na Nc), (proj2 (Nat.eqb_neq a t)) in U by (intro Q; apply Na; symmetry; exact Q).
        discriminate U.
      + right. rewrite (un_flip a x c Ha), (No c Hc), Uc, (proj2 (Nat.eqb_neq a c) Nac). reflexivity.
    - assert (Hw : In w (filter (lar x a) js)) by (rewrite Ef; left; reflexivity).
      apply filter_In in Hw. destruct Hw as [Hw Aw].
      assert (Uq : forall t, In t js -> lar x a t = true -> t = w)
        by (intros t Ht At; exact (od_unique Sh get set Fv js x a t w Hod Ha Ht Hw At Aw)).
      assert (Nwa : w <> a) by (intro Q; subst w; rewrite Self in Aw; discriminate Aw).
      assert (Ot : forall t, In t js -> t <> w -> lar x a t = false)
        by (intros t Ht Nt; destruct (lar x a t) eqn:E; [exfalso; exact (Nt (Uq t Ht E)) | reflexivity]).
      destruct (Nat.eq_dec w c) as [-> | Nwc].
      + (* collision *)
        right. split; [| left; exact Aw].
        intros t Ht U. rewrite (un_flip a x t Ha) in U.
        destruct (Nat.eq_dec t a) as [-> | Na]; [rewrite Ua, Nat.eqb_refl, Self in U; discriminate U |].
        destruct (Nat.eq_dec t c) as [E | Nc]; [exact E |].
        rewrite (Uo t Ht Na Nc), (Ot t Ht Nc), (proj2 (Nat.eqb_neq a t)) in U by (intro Q; apply Na; symmetry; exact Q).
        discriminate U.
      + left. exists w. split; [exact Aw |]. unfold TwoTok.
        split; [exact Hw | split; [exact Hc | split; [exact Nwc | split; [| split]]]].
        * rewrite (un_flip a x w Ha), Aw, (Uo w Hw Nwa Nwc), (proj2 (Nat.eqb_neq a w)) by (intro Q; apply Nwa; symmetry; exact Q).
          reflexivity.
        * rewrite (un_flip a x c Ha), (Ot c Hc (fun Q => Nwc (eq_sym Q))), Uc, (proj2 (Nat.eqb_neq a c) Nac). reflexivity.
        * intros t Ht Ntw Ntc. rewrite (un_flip a x t Ha).
          destruct (Nat.eq_dec t a) as [-> | Na]; [rewrite Ua, Nat.eqb_refl, Self; reflexivity |].
          rewrite (Uo t Ht Na Ntc), (Ot t Ht Ntw), (proj2 (Nat.eqb_neq a t)) by (intro Q; apply Na; symmetry; exact Q).
          reflexivity.
  Qed.

  (* With tokens {a, c}, the synchronous step fires both. *)
  Lemma F_two : forall x a c, TwoTok x a c -> F x = flp a (flp c x).
  Proof.
    intros x a c (Ha & Hc & Nac & Ua & Uc & Uo). apply sh_ext. intros t Ht.
    rewrite (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv x t Ht).
    rewrite (get_flip Sh js get set get_set_eq get_set_neq a t (flp c x) Ha).
    rewrite (get_flip Sh js get set get_set_eq get_set_neq c t x Hc).
    destruct (Nat.eq_dec t a) as [-> | Na].
    - rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq c a)) by (intro Q; apply Nac; symmetry; exact Q).
      unfold un in Ua. destruct (get a x), (Fv a x); simpl in *; congruence.
    - destruct (Nat.eq_dec t c) as [-> | Nc].
      + rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq a c)) by exact Nac.
        unfold un in Uc. destruct (get c x), (Fv c x); simpl in *; congruence.
      + rewrite (proj2 (Nat.eqb_neq a t)) by (intro Q; apply Na; symmetry; exact Q).
        rewrite (proj2 (Nat.eqb_neq c t)) by (intro Q; apply Nc; symmetry; exact Q).
        pose proof (Uo t Ht Na Nc) as U. unfold un in U.
        destruct (get t x), (Fv t x); simpl in *; congruence.
  Qed.

  Lemma dS_flip_good : NoDup js -> forall j z q, In j js -> get j z <> get j q ->
    S (dS Sh get js (flp j z) q) = dS Sh get js z q.
  Proof.
    intros Hnd j z q Hj N. unfold dS.
    rewrite (cnt_ext js (fun t => get t (flp j z)) (fun t => xorb (get t z) (Nat.eqb j t))
               (fun t => get t q) (fun t => get t q))
      by (intros t _; first [exact (get_flip Sh js get set get_set_eq get_set_neq j t z Hj) | reflexivity]).
    exact (cnt_flip_neq js (fun t => get t z) (fun t => get t q) j Hnd Hj N).
  Qed.

  Lemma dS_flip_bad : NoDup js -> forall j z q, In j js -> get j z = get j q ->
    dS Sh get js (flp j z) q = S (dS Sh get js z q).
  Proof.
    intros Hnd j z q Hj E. unfold dS.
    rewrite (cnt_ext js (fun t => get t (flp j z)) (fun t => xorb (get t z) (Nat.eqb j t))
               (fun t => get t q) (fun t => get t q))
      by (intros t _; first [exact (get_flip Sh js get set get_set_eq get_set_neq j t z Hj) | reflexivity]).
    exact (cnt_flip_eq js (fun t => get t z) (fun t => get t q) j Hnd Hj E).
  Qed.

  Lemma get_flip_other : forall j t z, In j js -> j <> t -> get t (flp j z) = get t z.
  Proof.
    intros j t z Hj N. rewrite (get_flip Sh js get set get_set_eq get_set_neq j t z Hj).
    rewrite (proj2 (Nat.eqb_neq j t) N). apply xorb_false_r.
  Qed.

  (* ========================================================================================== *)
  (* Part 2. Good and bad tokens relative to the fixed point p.                                 *)
  (* ========================================================================================== *)

  Section Pt.
    Hypothesis Hnd : NoDup js.
    Hypothesis Hod : OutDeg1 Sh get set Fv js.
    Hypothesis Hac : NoLocalCycle Sh get set Fv js.
    Variable p : Sh.
    Hypothesis Hp : F p = p.

    Definition dp (x : Sh) : nat := dS Sh get js x p.
    (* One good token b (x_b <> p_b) and one bad token v (x_v = p_v). *)
    Definition G1 (x : Sh) (b v : nat) : Prop := TwoTok x b v /\ get b x <> get b p /\ get v x = get v p.

    Lemma acx : forall x, AcyclicAt Sh js get set Fv x.
    Proof. intros x c Hc. exact (Hac x c Hc). Qed.

    Lemma Fp : forall t, In t js -> Fv t p = get t p.
    Proof.
      intros t Ht. rewrite <- (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv p t Ht), Hp. reflexivity.
    Qed.

    Lemma dF_p : forall x, dF Sh Fv js x p = dp (F x).
    Proof.
      intros x. unfold dF, dp, dS. apply cnt_ext; intros t Ht.
      - symmetry. exact (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv x t Ht).
      - exact (Fp t Ht).
    Qed.

    Lemma nonexp_p : forall x, dF Sh Fv js x p <= dp x.
    Proof.
      intros x. apply (proj1 (outdeg_nonexpansive Sh js get set get_set_eq get_set_neq sh_ext Fv js Hnd (incl_refl js)) Hod).
      intros j Hj Hn. exfalso. exact (Hn Hj).
    Qed.

    (* With two tokens, at least one is good. *)
    Theorem not_both_bad : forall x a c, TwoTok x a c -> get a x = get a p -> get c x = get c p -> False.
    Proof.
      intros x a c T Ea Ec. pose proof T as (Ha & Hc & Nac & _).
      pose proof (nonexp_p x) as L. rewrite dF_p, (F_two x a c T) in L. unfold dp in L.
      rewrite (dS_flip_bad Hnd a (flp c x) p Ha) in L
        by (rewrite (get_flip_other c a x Hc (fun Q => Nac (eq_sym Q))); exact Ea).
      rewrite (dS_flip_bad Hnd c x p Hc Ec) in L. lia.
    Qed.

    (* A G1 state is tight: F(x) is exactly as far from p as x. *)
    Lemma tight : forall x b v, G1 x b v -> dF Sh Fv js x p = dp x.
    Proof.
      intros x b v (T & Gb & Bv). pose proof T as (Hb & Hv & Nbv & _).
      rewrite dF_p, (F_two x b v (proj1 (conj T I))). unfold dp.
      pose proof (dS_flip_good Hnd b (flp v x) p Hb) as E1.
      rewrite (get_flip_other v b x Hv (fun Q => Nbv (eq_sym Q))) in E1. specialize (E1 Gb).
      rewrite (dS_flip_bad Hnd v x p Hv Bv) in E1. lia.
    Qed.

    (* At a tight state, every j in D(x) has an out-arc to a vertex i with F_i(x) <> p_i. *)
    Lemma tight_arc : forall x, dF Sh Fv js x p = dp x -> forall j, In j js -> get j x <> get j p ->
      exists i, In i js /\ lar x j i = true /\ Fv i x <> get i p.
    Proof.
      intros x Ht j Hj Nj. set (y := flp j x).
      pose proof (nonexp_p y) as H1.
      pose proof (dS_flip_good Hnd j x p Hj Nj) as H2. fold y in H2. fold (dp y) in H2. fold (dp x) in H2.
      pose proof (cnt_tri js (fun t => Fv t x) (fun t => Fv t y) (fun t => Fv t p)) as H3.
      pose proof (dF_flip Sh get set Fv js x j) as H4. fold y in H4. unfold dF in H4.
      pose proof (Hod x j Hj) as H5. unfold dF in H1, Ht.
      destruct (filter (lar x j) js) as [| i l] eqn:Ef; [simpl in H4; lia |].
      assert (Hi : In i (filter (lar x j) js)) by (rewrite Ef; left; reflexivity).
      apply filter_In in Hi. destruct Hi as [Hi Ai].
      exists i. split; [exact Hi | split; [exact Ai |]]. intro E.
      assert (Ey : forall t, In t js -> Fv t y = xorb (Fv t x) (Nat.eqb i t)).
      { intros t Ht0. destruct (Nat.eq_dec i t) as [<- | N].
        - rewrite Nat.eqb_refl. unfold larc in Ai. fold y in Ai.
          destruct (Fv i y), (Fv i x); simpl in *; congruence.
        - rewrite (proj2 (Nat.eqb_neq i t) N), xorb_false_r.
          apply (sink_flip Sh get set Fv x j t). destruct (lar x j t) eqn:A; [| reflexivity].
          exfalso. apply N. exact (od_unique Sh get set Fv js x j i t Hod Hj Hi Ht0 Ai A). }
      assert (C : cnt js (fun t => Fv t y) (fun t => Fv t p) = S (cnt js (fun t => Fv t x) (fun t => Fv t p))).
      { rewrite (cnt_ext js (fun t => Fv t y) (fun t => xorb (Fv t x) (Nat.eqb i t))
                   (fun t => Fv t p) (fun t => Fv t p)) by (intros t Ht0; first [exact (Ey t Ht0) | reflexivity]).
        apply cnt_flip_eq; [exact Hnd | exact Hi |]. rewrite (Fp i Hi). exact E. }
      lia.
    Qed.

    (* Rigidity: at a G1 state the bad token has no out-arc into D(x). *)
    Theorem head_arc : forall x b v w, G1 x b v -> In w js -> lar x v w = true -> get w x <> get w p -> False.
    Proof.
      intros x b v w G Hw Aw Nw. pose proof G as (T & Gb & Bv). pose proof T as (Hb & Hv & Nbv & Ub & Uv & Uo).
      pose proof (tight x b v G) as Ht.
      set (S' := filter (fun i => negb (Bool.eqb (get i x) (get i p)) || Nat.eqb i v) js).
      assert (InS : forall i, In i js -> (get i x <> get i p \/ i = v) -> In i S').
      { intros i Hi H. apply filter_In. split; [exact Hi |].
        destruct H as [H | ->]; [| rewrite Nat.eqb_refl, orb_true_r; reflexivity].
        destruct (get i x), (get i p); simpl; congruence. }
      assert (OutS : forall k, In k S' -> exists i, In i S' /\ lar x k i = true).
      { intros k Hk. apply filter_In in Hk. destruct Hk as [Hk Ek].
        destruct (Bool.bool_dec (get k x) (get k p)) as [Eq | Nk].
        - assert (k = v).
          { rewrite Eq, Bool.eqb_reflx in Ek. simpl in Ek. apply Nat.eqb_eq. exact Ek. }
          subst k. exists w. split; [apply InS; [exact Hw | left; exact Nw] | exact Aw].
        - destruct (tight_arc x Ht k Hk Nk) as [i [Hi [Ai Fi]]].
          exists i. split; [| exact Ai]. apply InS; [exact Hi |].
          destruct (Bool.bool_dec (get i x) (get i p)) as [Ei | Ni]; [right | left; exact Ni].
          assert (Ui : un x i = true).
          { unfold un. rewrite Ei. destruct (get i p), (Fv i x); simpl in *; congruence. }
          destruct (two_in x b v i T Hi Ui) as [-> | ->]; [exfalso; exact (Gb Ei) | reflexivity]. }
      assert (Ne : S' <> []) by (intro E; assert (In v S') by (apply InS; [exact Hv | right; reflexivity]); rewrite E in H; destruct H).
      destruct (cycle_or_sink (lar x) S' Ne) as [[c [Hc Hcy]] | [k [Hk Hs]]].
      - apply (Hac x c); [| exact Hcy]. intros u Hu. apply Hc in Hu. apply filter_In in Hu. tauto.
      - destruct (OutS k Hk) as [i [Hi Ai]]. rewrite (Hs i Hi) in Ai. discriminate Ai.
    Qed.

    Lemma G1_T : forall x b v c, G1 x b v -> TwoTok (flp b x) c v -> G1 (flp b x) c v.
    Proof.
      intros x b v c (T & Gb & Bv) T'. pose proof T as (Hb & Hv & Nbv & _).
      assert (Bv' : get v (flp b x) = get v p) by (rewrite (get_flip_other b v x Hb Nbv); exact Bv).
      split; [exact T' | split; [| exact Bv']].
      intro Ec. exact (not_both_bad (flp b x) c v T' Ec Bv').
    Qed.

    Lemma G1_H : forall x b v w, G1 x b v -> TwoTok (flp v x) b w -> G1 (flp v x) b w.
    Proof.
      intros x b v w G T'. pose proof G as (T & Gb & Bv). pose proof T as (Hb & Hv & Nbv & Ub & Uv & Uo).
      pose proof T' as (_ & Hw & Nbw & _ & Uw & _).
      assert (Nwv : w <> v).
      { intro Q. subst w. rewrite (un_flip v x v Hv), Uv, Nat.eqb_refl, (noself x v (acx x) Hv) in Uw. discriminate Uw. }
      split; [exact T' | split].
      - rewrite (get_flip_other v b x Hv (fun Q => Nbv (eq_sym Q))). exact Gb.
      - rewrite (get_flip_other v w x Hv (fun Q => Nwv (eq_sym Q))).
        assert (Aw : lar x v w = true).
        { rewrite (un_flip v x w Hv), (Uo w Hw (fun Q => Nbw (eq_sym Q)) Nwv),
            (proj2 (Nat.eqb_neq v w) (fun Q => Nwv (eq_sym Q))) in Uw. exact Uw. }
        destruct (Bool.bool_dec (get w x) (get w p)) as [E | N]; [exact E |].
        exfalso. exact (head_arc x b v w G Hw Aw N).
    Qed.

    Lemma G1_uniq : forall x b v b' v', G1 x b v -> G1 x b' v' -> b' = b /\ v' = v.
    Proof.
      intros x b v b' v' (T & Gb & Bv) (T' & Gb' & Bv'). pose proof T' as (Hb' & Hv' & _ & Ub' & Uv' & _).
      split.
      - destruct (two_in x b v b' T Hb' Ub') as [E | E]; [exact E |]. subst b'. exfalso. exact (Gb' Bv).
      - destruct (two_in x b v v' T Hv' Uv') as [E | E]; [| exact E]. subst v'. exfalso. exact (Gb Bv').
    Qed.

    (* At a G1 state, "good then bad" can be swapped into "bad then good". *)
    Lemma swap_core : forall x b v c w, G1 x b v -> TwoTok (flp v (flp b x)) c w -> exists w', TwoTok (flp v x) b w'.
    Proof.
      intros x b v c w G T2. pose proof G as (T & Gb & Bv). pose proof T as (Hb & Hv & Nbv & Ub & Uv & Uo).
      destruct (fire Hnd Hod x v b (acx x) (two_sym x b v T)) as [[w' [_ Tw]] | [Only [Col | Ubx]]].
      - exists w'. exact (two_sym _ _ _ Tw).
      - exfalso. exact (head_arc x b v b G Hb Col Gb).
      - exfalso.
        pose proof (uc_le1 Hnd (flp v x) b Only) as L1.
        pose proof (ucnt_mono Sh js get set get_set_eq get_set_neq sh_ext Fv Hnd Hod b (flp v x)) as L2.
        rewrite (ru_fire b (flp v x) Hb Ubx) in L2.
        rewrite (flip_comm Sh js get set get_set_eq get_set_neq sh_ext b v x Hb Hv) in L2.
        pose proof (uc_ge2 _ _ _ T2). lia.
    Qed.

    (* ======================================================================================== *)
    (* Part 3. Two-token walks through G1 states and their rearrangement.                       *)
    (* ======================================================================================== *)

    (* Labels: false = the good token moves ("T"), true = the bad token moves ("H"). *)
    Inductive W : Sh -> list bool -> Sh -> Prop :=
    | W0 : forall x, W x [] x
    | WT : forall x b v c l y, G1 x b v -> TwoTok (flp b x) c v -> W (flp b x) l y -> W x (false :: l) y
    | WH : forall x b v w l y, G1 x b v -> TwoTok (flp v x) b w -> W (flp v x) l y -> W x (true :: l) y.

    Lemma W_nil : forall x y, W x [] y -> y = x.
    Proof. intros x y H. inversion H. reflexivity. Qed.

    Lemma W_T : forall x l y, W x (false :: l) y ->
      exists b v c, G1 x b v /\ TwoTok (flp b x) c v /\ W (flp b x) l y.
    Proof. intros x l y H. inversion H; subst. eauto 6. Qed.

    Lemma W_H : forall x l y, W x (true :: l) y ->
      exists b v w, G1 x b v /\ TwoTok (flp v x) b w /\ W (flp v x) l y.
    Proof. intros x l y H. inversion H; subst. eauto 6. Qed.

    Lemma W_app : forall x l1 z, W x l1 z -> forall l2 y, W z l2 y -> W x (l1 ++ l2) y.
    Proof.
      intros x l1 z H. induction H as [x | x b v c l y G T Hw IH | x b v w l y G T Hw IH]; intros l2 y' H2.
      - exact H2.
      - exact (WT x b v c _ y' G T (IH l2 y' H2)).
      - exact (WH x b v w _ y' G T (IH l2 y' H2)).
    Qed.

    Lemma W_app_inv : forall l1 l2 x y, W x (l1 ++ l2) y -> exists z, W x l1 z /\ W z l2 y.
    Proof.
      induction l1 as [| a l1 IH]; intros l2 x y H; [exists x; split; [constructor | exact H] |].
      destruct a.
      - destruct (W_H x _ y H) as (b & v & w & G & T & Hw). destruct (IH l2 _ y Hw) as [z [H1 H2]].
        exists z. split; [exact (WH x b v w l1 z G T H1) | exact H2].
      - destruct (W_T x _ y H) as (b & v & c & G & T & Hw). destruct (IH l2 _ y Hw) as [z [H1 H2]].
        exists z. split; [exact (WT x b v c l1 z G T H1) | exact H2].
    Qed.

    Lemma W_dp : forall x l y, W x l y -> dp y + nT l = dp x + nH l.
    Proof.
      intros x l y H. induction H as [x | x b v c l y (T & Gb & Bv) _ Hw IH | x b v w l y (T & Gb & Bv) _ Hw IH].
      - simpl. lia.
      - pose proof T as (Hb & _). pose proof (dS_flip_good Hnd b x p Hb Gb) as E. fold (dp (flp b x)) (dp x) in E.
        simpl. lia.
      - pose proof T as (_ & Hv & _). pose proof (dS_flip_bad Hnd v x p Hv Bv) as E. fold (dp (flp v x)) (dp x) in E.
        simpl. lia.
    Qed.

    Lemma W_G1 : forall x l y, W x l y -> l <> [] -> exists b v, G1 x b v.
    Proof. intros x l y H N. destruct H; [congruence | eauto | eauto]. Qed.

    (* T H -> H T. *)
    Lemma swap_TH : forall x s y, W x (false :: true :: s) y -> W x (true :: false :: s) y.
    Proof.
      intros x s y H.
      destruct (W_T x _ y H) as (b & v & c & G & T1 & Hw).
      destruct (W_H _ _ y Hw) as (b' & v' & w & G' & T2 & Hw').
      destruct (G1_uniq _ _ _ _ _ (G1_T x b v c G T1) G') as [-> ->].
      pose proof G as ((Hb & Hv & _) & _).
      destruct (swap_core x b v c w G T2) as [w' Tw'].
      apply (WH x b v w' (false :: s) y G Tw').
      rewrite <- (flip_comm Sh js get set get_set_eq get_set_neq sh_ext b v x Hb Hv) in T2, Hw'.
      pose proof (G1_H x b v w' G Tw') as G2.
      destruct (fire Hnd Hod (flp v x) b w' (acx _) (proj1 G2)) as [[c' [_ Tc']] | [Only _]].
      - exact (WT (flp v x) b w' c' s y G2 Tc' Hw').
      - exfalso. pose proof (uc_le1 Hnd _ w' Only). pose proof (uc_ge2 _ _ _ T2). lia.
    Qed.

    Lemma W_pushT : forall a s x y, W x (false :: repeat true a ++ s) y -> W x (repeat true a ++ false :: s) y.
    Proof.
      induction a as [| a IH]; intros s x y H; [exact H |].
      apply swap_TH in H. destruct (W_H x _ y H) as (b & v & w & G & T & Hw).
      exact (WH x b v w _ y G T (IH s _ y Hw)).
    Qed.

    Lemma W_pullH : forall a s x y, W x (repeat false a ++ true :: s) y -> W x (true :: repeat false a ++ s) y.
    Proof.
      induction a as [| a IH]; intros s x y H; [exact H |].
      destruct (W_T x _ y H) as (b & v & c & G & T & Hw).
      apply swap_TH. exact (WT x b v c _ y G T (IH s _ y Hw)).
    Qed.

    (* Every G1 walk can be rearranged with all bad-token moves first. *)
    Lemma W_sort : forall x l y, W x l y -> W x (repeat true (nH l) ++ repeat false (nT l)) y.
    Proof.
      intros x l y H. induction H as [x | x b v c l y G T Hw IH | x b v w l y G T Hw IH].
      - constructor.
      - simpl. apply W_pushT. exact (WT x b v c _ y G T IH).
      - simpl. exact (WH x b v w _ y G T IH).
    Qed.

    (* T^h H^h is the synchronous orbit of length h. *)
    Lemma W_main : forall h z y, W z (repeat false h ++ repeat true h) y -> y = orb Sh js set Fv h z.
    Proof.
      induction h as [| h IH]; intros z y H; [exact (W_nil z y H) |].
      simpl in H. destruct (W_T z _ y H) as (b & v & c & G & T & Hw).
      apply W_pullH in Hw. destruct (W_H _ _ y Hw) as (b' & v' & w & G' & T' & Hw').
      destruct (G1_uniq _ _ _ _ _ (G1_T z b v c G T) G') as [-> ->].
      pose proof G as (Tz & _).
      rewrite <- (F_two z v b (two_sym z b v Tz)) in Hw'.
      rewrite (IH _ y Hw'). unfold orb. apply lfs_iter_succ_r.
    Qed.

    (* ======================================================================================== *)
    (* Part 4. From asynchronous runs to G1 walks.                                              *)
    (* ======================================================================================== *)

    Lemma conv : forall w x b v, G1 x b v -> uc (xw w x) = 2 ->
      exists l b' v', W x l (xw w x) /\ G1 (xw w x) b' v' /\ (l = [] -> xw w x = x).
    Proof.
      induction w as [| a w IH]; intros x b v G Hu.
      - exists [], b, v. split; [constructor | split; [exact G | reflexivity]].
      - change (xw (a :: w) x) with (xw w (ru a x)) in *.
        destruct (in_dec Nat.eq_dec a js) as [Ha | Ha];
          [| rewrite (rupd_out bool Sh js set Fv a x Ha) in *; exact (IH x b v G Hu)].
        destruct (un x a) eqn:Ua; [| rewrite (ru_noop a x Ua) in *; exact (IH x b v G Hu)].
        pose proof G as (T & Gb & Bv). pose proof T as (Hb & Hv & _).
        rewrite (ru_fire a x Ha Ua) in *.
        pose proof (uc_xw_mono Hnd Hod w (flp a x)) as L.
        destruct (two_in x b v a T Ha Ua) as [-> | ->].
        + destruct (fire Hnd Hod x b v (acx x) T) as [[c [_ Tc]] | [Only _]];
            [| pose proof (uc_le1 Hnd _ v Only); lia].
          pose proof (G1_T x b v c G Tc) as G'.
          destruct (IH _ c v G' Hu) as (l & b' & v' & Hw & Ge & _).
          exists (false :: l), b', v'. split; [exact (WT x b v c l _ G Tc Hw) | split; [exact Ge | discriminate]].
        + destruct (fire Hnd Hod x v b (acx x) (two_sym x b v T)) as [[w' [_ Tw]] | [Only _]];
            [| pose proof (uc_le1 Hnd _ b Only); lia].
          pose proof (G1_H x b v w' G (two_sym _ _ _ Tw)) as G'.
          destruct (IH _ b w' G' Hu) as (l & b' & v' & Hw & Ge & _).
          exists (true :: l), b', v'. split; [exact (WH x b v w' l _ G (two_sym _ _ _ Tw) Hw) | split; [exact Ge | discriminate]].
    Qed.

    (* Along a two-token run, either some state is G1 (and then the end state is), or every move
       fires a good token and the distance to p strictly decreases. *)
    Lemma run_bad_or_dec : forall w x a c, TwoTok x a c -> uc (xw w x) = 2 ->
      (exists b v, G1 (xw w x) b v) \/ (dp (xw w x) <= dp x /\ (xw w x <> x -> dp (xw w x) < dp x)).
    Proof.
      induction w as [| e w IH]; intros x a c T Hu.
      - right. split; [apply Nat.le_refl | intros N; exfalso; apply N; reflexivity].
      - destruct (Bool.bool_dec (get a x) (get a p)) as [Ea | Ga];
          destruct (Bool.bool_dec (get c x) (get c p)) as [Ec | Gc].
        + exfalso. exact (not_both_bad x a c T Ea Ec).
        + left. destruct (conv (e :: w) x c a (conj (two_sym x a c T) (conj Gc Ea)) Hu) as (l & b' & v' & _ & Ge & _).
          eauto.
        + left. destruct (conv (e :: w) x a c (conj T (conj Ga Ec)) Hu) as (l & b' & v' & _ & Ge & _).
          eauto.
        + change (xw (e :: w) x) with (xw w (ru e x)) in *.
          destruct (in_dec Nat.eq_dec e js) as [He | He];
            [| rewrite (rupd_out bool Sh js set Fv e x He) in *; exact (IH x a c T Hu)].
          destruct (un x e) eqn:Ue; [| rewrite (ru_noop e x Ue) in *; exact (IH x a c T Hu)].
          pose proof T as (Ha & Hc & _).
          rewrite (ru_fire e x He Ue) in *.
          assert (Ex : exists o, TwoTok x e o /\ get e x <> get e p).
          { destruct (two_in x a c e T He Ue) as [-> | ->]; [exists c; split; [exact T | exact Ga] |].
            exists a. split; [exact (two_sym x a c T) | exact Gc]. }
          destruct Ex as [o [To Ge]].
          pose proof (dS_flip_good Hnd e x p He Ge) as D. fold (dp (flp e x)) (dp x) in D.
          pose proof (uc_xw_mono Hnd Hod w (flp e x)) as L.
          destruct (fire Hnd Hod x e o (acx x) To) as [[w' [_ Tw]] | [Only _]];
            [| pose proof (uc_le1 Hnd _ o Only); lia].
          destruct (IH _ w' o Tw Hu) as [Hl | [H1 H2]]; [left; exact Hl | right].
          split; [lia | intros _; lia].
    Qed.

    (* No closed two-token run changes the state. *)
    Theorem two_token_closed_p : forall x, uc x = 2 -> forall w1 w2, xw (w1 ++ w2) x = x -> xw w1 x = x.
    Proof.
      intros x Hx w1 w2 Hw.
      destruct (sh_dec Sh js get sh_ext (xw w1 x) x) as [E | N]; [exact E | exfalso].
      rewrite (xr_app bool Sh js set Fv) in Hw. set (y := xw w1 x) in *.
      assert (Hy : uc y = 2).
      { pose proof (uc_xw_mono Hnd Hod w1 x) as M1. pose proof (uc_xw_mono Hnd Hod w2 y) as M2.
        fold y in M1. rewrite Hw in M2. lia. }
      assert (Hx' : uc (xw w2 y) = 2) by (rewrite Hw; exact Hx).
      destruct (uc_two Hnd x Hx) as (a & c & T).
      assert (Gx : exists b v, G1 x b v).
      { destruct (run_bad_or_dec w1 x a c T Hy) as [[b [v Gy]] | [_ D1]].
        - destruct (conv w2 y b v Gy Hx') as (l & b' & v' & _ & Ge & _). rewrite Hw in Ge. eauto.
        - specialize (D1 N). destruct (uc_two Hnd y Hy) as (a' & c' & T').
          destruct (run_bad_or_dec w2 y a' c' T' Hx') as [Gl | [D2 _]].
          + rewrite Hw in Gl. exact Gl.
          + rewrite Hw in D2. fold y in D1. lia. }
      destruct Gx as (b & v & G).
      destruct (conv w1 x b v G Hy) as (l1 & b1 & v1 & H1 & G1y & E1). fold y in H1, G1y, E1.
      destruct (conv w2 y b1 v1 G1y Hx') as (l2 & _ & _ & H2 & _ & _). rewrite Hw in H2.
      assert (Ne : l1 <> []) by (intro Q; exact (N (E1 Q))).
      pose proof (W_app x l1 y H1 l2 x H2) as Hc. set (L := l1 ++ l2) in Hc.
      pose proof (W_dp x L x Hc) as Bal.
      assert (Hpos : 1 <= nH L).
      { assert (Ln : 1 <= length L) by (unfold L; destruct l1; [congruence | simpl; lia]).
        pose proof (nH_nT L). lia. }
      apply W_sort in Hc. replace (nT L) with (nH L) in Hc by lia.
      destruct (W_app_inv _ _ x x Hc) as [z [Hz1 Hz2]].
      pose proof (W_main (nH L) z z (W_app z _ x Hz2 _ z Hz1)) as Eo.
      destruct (nH L) as [| h] eqn:Eh; [lia |].
      assert (Fz : F z = z)
        by exact (sync_orbit_fixed Sh js get set get_set_eq get_set_neq sh_ext Fv Hnd Hod z h (eq_sym Eo) 0 (acx _)).
      destruct (W_G1 z _ z (W_app z _ x Hz2 _ z Hz1)) as (b' & v' & ((Hb' & _ & _ & Ub' & _) & _)); [simpl; discriminate |].
      apply (un_true z b' Ub'). rewrite <- (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv z b' Hb'), Fz.
      reflexivity.
    Qed.
  End Pt.

  (* ========================================================================================== *)
  (* Part 5. Main results.                                                                      *)
  (* ========================================================================================== *)

  (* (A), (B), and at most two unstable vertices at x: no closed asynchronous run from x changes
     the state. *)
  Theorem two_token_closed : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall x, uc x <= 2 -> forall w1 w2, xw (w1 ++ w2) x = x -> xw w1 x = x.
  Proof.
    intros Hnd Hc Hod x Hx w1 w2 Hw.
    destruct (Nat.le_gt_cases (uc x) 1) as [H1 | H2].
    - exact (one_token_closed Sh js get set get_set_eq get_set_neq sh_ext Fv Hnd Hod x
               (acyclic_at_all Sh js get set Fv Hc x) H1 w1 w2 Hw).
    - destruct (shih_dong_E Sh js get set get_set_eq get_set_neq sh_ext Fv Hc x) as [q [Hq _]].
      exact (two_token_closed_p Hnd Hod Hc q Hq x ltac:(lia) w1 w2 Hw).
  Qed.

  Theorem two_token_no_closed_change : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    NoClosedChange Sh js set Fv (fun x => uc x <= 2).
  Proof. intros Hnd Hc Hod x w1 w2 Hx Hw. exact (two_token_closed Hnd Hc Hod x Hx w1 w2 Hw). Qed.

  (* (A) and (B): every fair schedule from a start with at most two unstable vertices settles at
     the unique fixed point. *)
  Theorem two_token_fair_settlement : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall q, F q = q -> forall sch, Fair js sch -> forall h0, uc h0 <= 2 -> Settles Sh ru sch h0 q.
  Proof.
    intros Hnd Hc Hod q Hq sch Hf h0 H0.
    assert (Hu : forall p, F p = p -> p = q).
    { intros p Hp. apply (local_fidelity Sh js get set get_set_eq get_set_neq sh_ext Fv); [| exact Hp | exact Hq].
      intros z c Hcc [Hcy _]. exact (Hc z c Hcc Hcy). }
    destruct (fair_settles_closed Sh js get set get_set_eq get_set_neq sh_ext Fv (fun y => uc y <= 2)
                (fun a y Hy => Nat.le_trans _ _ _ (ucnt_mono Sh js get set get_set_eq get_set_neq sh_ext Fv Hnd Hod a y) Hy)
                (two_token_no_closed_change Hnd Hc Hod) sch Hf h0 H0) as [q' [Hq' Hs]].
    rewrite <- (Hu q' Hq'). exact Hs.
  Qed.

  (* Every fair run that ever reaches a state with at most two unstable vertices settles at the
     unique fixed point. *)
  Theorem fair_settles_once_two_tokens : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall q, F q = q -> forall sch, Fair js sch -> forall h0 n,
    uc (prs Sh ru sch n h0) <= 2 -> Settles Sh ru sch h0 q.
  Proof.
    intros Hnd Hc Hod q Hq sch Hf h0 n Hn.
    destruct (two_token_fair_settlement Hnd Hc Hod q Hq (fun t => sch (n + t)) (fair_shift js sch n Hf)
                (prs Sh ru sch n h0) Hn) as [N HN].
    exists (n + N). intros m Hm. replace m with (n + (m - n)) by lia.
    rewrite prs_shift. apply HN. lia.
  Qed.
End Lens.

(* ============================================================================================ *)
(* Part 6. Non-vacuity.                                                                          *)
(* ============================================================================================ *)

(* Shih and Ho's network (LocalFairSettlement.sh_F) satisfies (A) and (B); at 1110 it has exactly
   two unstable vertices, 0 (agreeing with the fixed point 1111: a bad token) and 3 (a good
   token), so the G1 case occurs; and every fair schedule from 1110 settles at 1111. *)
Definition sh_x2 : BV 4 := (true, (true, (true, (false, tt)))).

Theorem two_token_instance :
  NoLocalCycle (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  OutDeg1 (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  ucnt (BV 4) (seq 0 4) (bget 4) sh_F sh_x2 = 2 /\
  sh_F 0 sh_x2 <> bget 4 0 sh_x2 /\ bget 4 0 sh_x2 = bget 4 0 sh_q /\
  sh_F 3 sh_x2 <> bget 4 3 sh_x2 /\ bget 4 3 sh_x2 <> bget 4 3 sh_q /\
  (forall sch, Fair (seq 0 4) sch -> Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sh_F) sch sh_x2 sh_q).
Proof.
  destruct shih_ho_instance as (Hnd & Hc & Hod & _ & _ & _ & Hq & _).
  split; [exact Hc | split; [exact Hod |]].
  split; [vm_compute; reflexivity |].
  split; [vm_compute; discriminate | split; [vm_compute; reflexivity |]].
  split; [vm_compute; discriminate | split; [vm_compute; discriminate |]].
  intros sch Hf. apply (two_token_fair_settlement (BV 4) (seq 0 4) (bget 4) (bset 4) (bget_bset_eq 4)
                          (bget_bset_neq 4) (bext 4) sh_F Hnd Hc Hod sh_q Hq sch Hf).
  vm_compute. lia.
Qed.
