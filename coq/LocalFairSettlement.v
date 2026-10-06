(* LocalFairSettlement.v: fair asynchronous settlement for Boolean resolver networks under local
   conditions (gap 3 of REGIME-AUDIT.md, LossyNetworks P2). Axiom-free.

   Setting: the lens model of LocalSigned.v (states Sh read through get and set on the vertex
   list js, resolvers Fv, the synchronous map F = Fsync, and the asynchronous step rupd j).
   Conditions:
     (A) NoLocalCycle js: no cycle in any local interaction graph G(x); AcyclicAt x is (A) at the
         single state x;
     (B) OutDeg1 js: every vertex of every G(x) has out-degree at most one. This is Hamming
         non-expansiveness of F (LocalSigned.outdeg_nonexpansive).
   ucnt x is the number of unstable vertices of x (the "tokens"). NoClosedChange P says that no
   closed asynchronous run from a state satisfying P ever changes the state: if a word w1 ++ w2
   leads from x back to x, then so does its prefix w1. On a finite state space this is acyclicity
   of the asynchronous state graph.

   Results.
     sync_orbit_fixed   (B), and (A) at ONE state of a synchronous periodic orbit (F^(L+1) x = x),
                        imply that x is a fixed point. So every synchronous periodic orbit through
                        a state with an acyclic local graph is a fixed point. The proof: along the
                        orbit, non-expansiveness and periodicity force the Hamming distance between
                        orbit points to be invariant under the shift, while a vertex u that flips
                        on the orbit and is a sink of G(x_t) inside the flipped set would make the
                        shifted distance strictly smaller. So G(x_t) has no such sink, hence a
                        cycle (LocalSigned.cycle_or_sink), contradicting (A) at x_t.
     sync_simple        (A) and (B) everywhere: a unique fixed point q, and every synchronous orbit
                        reaches q within 2^|js| steps (the iteration graph is simple). This is the
                        conclusion of Shih and Ho 1999, Theorem 3.1 (whose hypotheses are (A) and
                        F(V(x)) inside V(F(x)), which their Lemma 4.1 shows is (B)); the proof
                        here is a different one, and sync_orbit_fixed needs (A) only on the orbit.
     ucnt_mono          (B) alone: no asynchronous step increases the number of unstable vertices.
     one_token_closed   (B), (A) at x, and at most one unstable vertex at x: no closed
                        asynchronous run from x changes the state. (With one token, an
                        asynchronous move is the synchronous step, so a closed run is a
                        synchronous periodic orbit; sync_orbit_fixed applies.)
     fair_settles_closed
                        generic: if P is preserved by every asynchronous step and NoClosedChange P
                        holds, then every fair schedule from every start in P settles at a fixed
                        point (the analogue of FairFlushR). Proof by fair rounds and pigeonhole.
     fair_settlement_of_acyclic
                        (A) and NoClosedChange True: every fair schedule from every start settles
                        at the unique fixed point.
     one_token_fair_settlement, fair_settles_once_one_token
                        (A) and (B): every fair schedule from a start with at most one unstable
                        vertex settles at the unique fixed point; more generally, every fair run
                        that ever reaches a state with at most one unstable vertex settles there.
   What is NOT proved here: that (A) and (B) exclude closed asynchronous runs whose states all
   have at least two unstable vertices. That is the remaining part of the conjecture
   (research/gap3-fair-settlement: no such run for n <= 6 by SAT; the key lemma F2 of REPORT.md,
   section 5, for k >= 2 tokens). Gap 3 stays open.
   Boundary instances.
     shih_ho_instance   Shih and Ho's own 4-vertex example (their Section 3, item (5)): (A) and
                        (B) hold, the local arcs 0 -> 3 and 3 -> 0 both occur (at different states,
                        so the global interaction graph has a cycle and Robert's theorem does not
                        apply), the asynchronous state graph is acyclic (a rank certificate), so
                        every fair schedule from every start settles at 1111; it has states with
                        exactly one unstable vertex (non-vacuity of one_token_fair_settlement).
     outdeg_needed      (B) is needed: Shih and Dong's network sd_F has (A), out-degree 2 at 0000,
                        a synchronous periodic orbit of length 3, and a fair schedule that never
                        settles (LocalSigned.shih_dong_not_fair), so both the synchronous and the
                        asynchronous conclusions fail.
     no_neg_not_enough  the positive 3-ring: (B) and no local negative cycle, but a fair schedule
                        that never settles (LocalSigned.ring_local_conditions).
     no_pos_not_enough  the negative 3-ring x0 := x1, x1 := x2, x2 := not x0: (B) and no local
                        positive cycle, a closed asynchronous run that changes the state, no fixed
                        point, and no fair schedule settles from any start. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.DistributedCycles NC.CanonicalExecution NC.SignedResolver NC.LocalSigned.
Import ListNotations.

(* ============================================================================================ *)
(* Part 0. List utilities.                                                                      *)
(* ============================================================================================ *)

Lemma lfs_len_map : forall (A B : Type) (f : A -> B) l, length (map f l) = length l.
Proof. intros A B f. induction l as [| a l IH]; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Lemma lfs_len_seq : forall s n, length (seq s n) = n.
Proof. intros s n. revert s. induction n as [| n IH]; intros s; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Lemma lfs_map_eq : forall (B : Type) (f g : nat -> B) l, map f l = map g l -> forall j, In j l -> f j = g j.
Proof.
  intros B f g. induction l as [| a l IH]; intros E j Hj; [destruct Hj |].
  simpl in E. injection E as E1 E2. destruct Hj as [<- | Hj]; [exact E1 | exact (IH E2 j Hj)].
Qed.

Lemma lfs_seq_snoc : forall s n, seq s (S n) = seq s n ++ [s + n].
Proof.
  intros s n. revert s. induction n as [| n IH]; intros s.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - change (seq s (S (S n))) with (s :: seq (S s) (S n)). rewrite IH.
    replace (S s + n) with (s + S n) by lia. reflexivity.
Qed.

Lemma lfs_seq_app : forall n m s, seq s (n + m) = seq s n ++ seq (s + n) m.
Proof.
  induction n as [| n IH]; intros m s.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. replace (S s + n) with (s + S n) by lia. reflexivity.
Qed.

Lemma lfs_filter_filter : forall (p q : nat -> bool) l,
  length (filter q (filter p l)) <= length (filter q l).
Proof.
  intros p q. induction l as [| a l IH]; [reflexivity |]. simpl.
  destruct (p a); simpl; destruct (q a); simpl; lia.
Qed.

Lemma lfs_nodup_map : forall (A B : Type) (f : A -> B) l,
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f. induction l as [| a l IH]; intros Hi Hn; [constructor |].
  inversion Hn as [| ? ? Ha Hl]; subst. simpl. constructor.
  - intro H. apply in_map_iff in H. destruct H as [b [Eb Hb]].
    assert (a = b) by (apply Hi; [left; reflexivity | right; exact Hb | symmetry; exact Eb]).
    subst b. contradiction.
  - apply IH; [| exact Hl]. intros u v Hu Hv E. apply Hi; [right; exact Hu | right; exact Hv | exact E].
Qed.

Lemma lfs_nodup_snoc : forall (A : Type) (l : list A) a, NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
  intros A. induction l as [| b l IH]; intros a Hn Ha; [constructor; [intros [] | constructor] |].
  inversion Hn as [| ? ? Hb Hl]; subst. simpl. constructor.
  - intro H. apply in_app_or in H. destruct H as [H | [E | []]]; [contradiction |].
    apply Ha. left. symmetry. exact E.
  - apply IH; [exact Hl |]. intro H. apply Ha. right. exact H.
Qed.

(* All Boolean lists of length m. *)
Fixpoint blists (m : nat) : list (list bool) :=
  match m with
  | O => [[]]
  | S m' => flat_map (fun l => [false :: l; true :: l]) (blists m')
  end.

Lemma blists_len : forall m, length (blists m) = 2 ^ m.
Proof.
  assert (G : forall L : list (list bool),
             length (flat_map (fun l => [false :: l; true :: l]) L) = 2 * length L).
  { induction L as [| a L IH]; [reflexivity |]. simpl. rewrite IH. lia. }
  induction m as [| m IH]; [reflexivity |]. simpl blists. rewrite G, IH. simpl. lia.
Qed.

Lemma blists_all : forall l, In l (blists (length l)).
Proof.
  induction l as [| b l IH]; [left; reflexivity |]. simpl. apply in_flat_map.
  exists l. split; [exact IH |]. destruct b; simpl; auto.
Qed.

Lemma lfs_dec_ex_le : forall (P : nat -> Prop), (forall i, {P i} + {~ P i}) ->
  forall n, {exists i, i <= n /\ P i} + {forall i, i <= n -> ~ P i}.
Proof.
  intros P Pd. induction n as [| n IH].
  - destruct (Pd 0) as [H | H]; [left; exists 0; split; [lia | exact H] |].
    right. intros i Hi. replace i with 0 by lia. exact H.
  - destruct IH as [H | H]; [left; destruct H as [i [Hi Pi]]; exists i; split; [lia | exact Pi] |].
    destruct (Pd (S n)) as [Q | Q]; [left; exists (S n); split; [lia | exact Q] |].
    right. intros i Hi. destruct (Nat.eq_dec i (S n)) as [-> | N]; [exact Q |]. apply H. lia.
Qed.

Lemma lfs_iter_succ_r : forall (A : Type) (f : A -> A) m y, Nat.iter m f (f y) = Nat.iter (S m) f y.
Proof. intros A f. induction m as [| m IH]; intros y; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Lemma lfs_iter_add : forall (A : Type) (f : A -> A) n m y, Nat.iter (n + m) f y = Nat.iter n f (Nat.iter m f y).
Proof. intros A f. induction n as [| n IH]; intros m y; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

(* ============================================================================================ *)
(* Part 1. The lens setting.                                                                    *)
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

  (* (A) at one state. *)
  Definition AcyclicAt (x : Sh) : Prop := forall c, incl c js -> ~ IsCycle (lar x) c.
  (* The number of unstable vertices of x. *)
  Definition ucnt (x : Sh) : nat := cnt js (fun t => get t x) (fun t => Fv t x).
  (* No closed asynchronous run from a P-state changes the state. *)
  Definition NoClosedChange (P : Sh -> Prop) : Prop :=
    forall x w1 w2, P x -> xw (w1 ++ w2) x = x -> xw w1 x = x.
  (* The synchronous orbit. *)
  Definition orb (n : nat) (x : Sh) : Sh := Nat.iter n F x.

  Lemma get_F : forall s k, In k js -> get k (F s) = Fv k s.
  Proof. intros s k Hk. exact (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv s k Hk). Qed.

  Lemma acyclic_at_all : NoLocalCycle Sh get set Fv js -> forall x, AcyclicAt x.
  Proof. intros H x c Hc. exact (H x c Hc). Qed.

  Lemma ru_cases : forall v x, In v js ->
    (Fv v x = get v x /\ ru v x = x) \/ (Fv v x <> get v x /\ ru v x = flp v x).
  Proof.
    intros v x Hv. destruct (Bool.bool_dec (Fv v x) (get v x)) as [E | N].
    - left. split; [exact E |]. apply sh_ext. intros k Hk. destruct (Nat.eq_dec k v) as [-> | Nk].
      + rewrite (get_rupd_same bool Sh js get set get_set_eq Fv v x Hv). exact E.
      + exact (get_rupd_other bool Sh js get set get_set_neq Fv v k x Nk).
    - right. split; [exact N |]. apply sh_ext. intros k Hk.
      rewrite (get_flip Sh js get set get_set_eq get_set_neq v k x Hv).
      destruct (Nat.eq_dec k v) as [-> | Nk].
      + rewrite (get_rupd_same bool Sh js get set get_set_eq Fv v x Hv), Nat.eqb_refl.
        destruct (Fv v x), (get v x); simpl; congruence.
      + rewrite (get_rupd_other bool Sh js get set get_set_neq Fv v k x Nk).
        rewrite (proj2 (Nat.eqb_neq v k)) by (intro E; apply Nk; symmetry; exact E).
        destruct (get k x); reflexivity.
  Qed.

  Lemma fixed_ru : forall x, F x = x -> forall a, ru a x = x.
  Proof.
    intros x H a. destruct (in_dec Nat.eq_dec a js) as [Ha | Ha];
      [| exact (rupd_out bool Sh js set Fv a x Ha)].
    destruct (ru_cases a x Ha) as [[_ E] | [N _]]; [exact E |].
    exfalso. apply N. rewrite <- (get_F x a Ha), H. reflexivity.
  Qed.

  Lemma fixed_xw : forall x, F x = x -> forall w, xw w x = x.
  Proof.
    intros x H. induction w as [| a w IH]; [reflexivity |].
    change (xw (a :: w) x) with (xw w (ru a x)). rewrite (fixed_ru x H a). exact IH.
  Qed.

  (* ========================================================================================== *)
  (* Part 2. Synchronous periodic orbits.                                                       *)
  (* ========================================================================================== *)

  Lemma outdeg_filter : forall p, OutDeg1 Sh get set Fv js -> OutDeg1 Sh get set Fv (filter p js).
  Proof.
    intros p H x j Hj. apply filter_In in Hj. destruct Hj as [Hj _].
    pose proof (H x j Hj) as L. pose proof (lfs_filter_filter p (lar x j) js). lia.
  Qed.

  (* (B), and (A) at one state of a synchronous periodic orbit through x: x is a fixed point. *)
  Theorem sync_orbit_fixed : NoDup js -> OutDeg1 Sh get set Fv js ->
    forall x L, orb (S L) x = x -> forall t, AcyclicAt (orb t x) -> F x = x.
  Proof.
    intros Hnd Hod x L Hper t Hac.
    set (P := S L).
    set (X := fun i => orb i x).
    assert (XS : forall i, X (S i) = F (X i)) by reflexivity.
    assert (Xper : forall i, X (i + P) = X i).
    { assert (Hper' : Nat.iter P F x = x) by exact Hper.
      intros i. unfold X, orb. rewrite lfs_iter_add, Hper'. reflexivity. }
    set (vary := fun j => existsb (fun i => negb (Bool.eqb (get j (X i)) (get j x))) (seq 0 P)).
    set (U := filter vary js).
    assert (HUnd : NoDup U) by (apply NoDup_filter; exact Hnd).
    assert (HUjs : incl U js) by (intros j Hj; apply filter_In in Hj; tauto).
    assert (HodU : OutDeg1 Sh get set Fv U) by exact (outdeg_filter vary Hod).
    assert (Hconst : forall j, In j js -> ~ In j U -> forall i, get j (X i) = get j x).
    { intros j Hj HnU.
      assert (Hv : vary j = false).
      { destruct (vary j) eqn:E; [| reflexivity]. exfalso. apply HnU. apply filter_In. tauto. }
      assert (Hlt : forall i, i < P -> get j (X i) = get j x).
      { intros i Hi. destruct (Bool.bool_dec (get j (X i)) (get j x)) as [E | N]; [exact E |].
        exfalso. assert (vary j = true); [| congruence].
        apply existsb_exists. exists i. split; [apply in_seq; lia |].
        destruct (get j (X i)), (get j x); simpl; congruence. }
      assert (G : forall m i, i < m -> get j (X i) = get j x).
      { induction m as [| m IH]; intros i Hi; [lia |].
        destruct (Nat.lt_ge_cases i P) as [Hs | Hs]; [exact (Hlt i Hs) |].
        replace i with ((i - P) + P) by lia. rewrite Xper. apply IH. unfold P in *. lia. }
      intros i. exact (G (S i) i (Nat.lt_succ_diag_r i)). }
    assert (HagX : forall i k, AgreeOff Sh js get U (X i) (X k)).
    { intros i k j Hj Hn. rewrite (Hconst j Hj Hn i), (Hconst j Hj Hn k). reflexivity. }
    set (D := fun i k => dS Sh get U (X i) (X k)).
    assert (HdF : forall i k, dF Sh Fv U (X i) (X k) = D (S i) (S k)).
    { intros i k. unfold dF, D, dS. apply cnt_ext; intros u Hu; rewrite XS, get_F by (apply HUjs; exact Hu);
        reflexivity. }
    assert (Hlip : forall i k, D (S i) (S k) <= D i k).
    { intros i k. rewrite <- HdF.
      exact (proj1 (outdeg_nonexpansive Sh js get set get_set_eq get_set_neq sh_ext Fv U HUnd HUjs)
               HodU (X i) (X k) (HagX i k)). }
    assert (Hiter : forall m i k, D (m + i) (m + k) <= D i k).
    { induction m as [| m IH]; intros i k; [reflexivity |].
      pose proof (Hlip (m + i) (m + k)). pose proof (IH i k). simpl. lia. }
    assert (Heq : forall i k, D (S i) (S k) = D i k).
    { intros i k. pose proof (Hlip i k) as A1. pose proof (Hiter L (S i) (S k)) as A2.
      assert (E : D (L + S i) (L + S k) = D i k).
      { unfold D. replace (L + S i) with (i + P) by (unfold P; lia).
        replace (L + S k) with (k + P) by (unfold P; lia). rewrite !Xper. reflexivity. }
      lia. }
    destruct (list_eq_dec Nat.eq_dec U []) as [EU | HUne].
    { (* nothing varies on the orbit: x is fixed *)
      assert (E1 : X 1 = x).
      { apply sh_ext. intros j Hj. apply (Hconst j Hj). rewrite EU. intros []. }
      exact E1. }
    destruct (cycle_or_sink (lar (X t)) U HUne) as [[c [Hc Hcy]] | [u [Hu Hs]]].
    { exfalso. apply (Hac c); [intros a Ha; apply HUjs; apply Hc; exact Ha | exact Hcy]. }
    exfalso.
    assert (Hujs : In u js) by (apply HUjs; exact Hu).
    assert (Hvu : vary u = true) by (apply filter_In in Hu; tauto).
    apply existsb_exists in Hvu. destruct Hvu as [i0 [_ Hi0]].
    assert (Ni0 : get u (X i0) <> get u x)
      by (intro E; rewrite E, Bool.eqb_reflx in Hi0; discriminate Hi0).
    assert (Hs0 : exists s, get u (X s) <> get u (X t)).
    { destruct (Bool.bool_dec (get u (X t)) (get u x)) as [E | N].
      - exists i0. rewrite E. exact Ni0.
      - exists 0. intro E. apply N. symmetry. exact E. }
    destruct Hs0 as [s Ns].
    set (y := flp u (X t)).
    assert (Agy : AgreeOff Sh js get U (X s) y).
    { intros j Hj Hn. unfold y. rewrite (get_flip Sh js get set get_set_eq get_set_neq u j (X t) Hujs).
      rewrite (proj2 (Nat.eqb_neq u j)) by (intro E; subst j; contradiction).
      rewrite xorb_false_r. exact (HagX s t j Hj Hn). }
    pose proof (proj1 (outdeg_nonexpansive Sh js get set get_set_eq get_set_neq sh_ext Fv U HUnd HUjs)
                  HodU (X s) y Agy) as Hne.
    assert (E1 : dF Sh Fv U (X s) y = D s t).
    { rewrite <- Heq, <- HdF. unfold dF. apply cnt_ext; [reflexivity |].
      intros i Hi. unfold y. exact (sink_flip Sh get set Fv (X t) u i (Hs i Hi)). }
    assert (E2 : S (dS Sh get U (X s) y) = D s t).
    { unfold dS, D. rewrite (cnt_sym U (fun t0 => get t0 (X s)) (fun t0 => get t0 y)).
      rewrite (cnt_ext U (fun t0 => get t0 y) (fun t0 => xorb (get t0 (X t)) (Nat.eqb u t0))
                 (fun t0 => get t0 (X s)) (fun t0 => get t0 (X s))).
      2: { intros j _. unfold y. exact (get_flip Sh js get set get_set_eq get_set_neq u j (X t) Hujs). }
      2: { intros j _. reflexivity. }
      rewrite (cnt_flip_neq U (fun t0 => get t0 (X t)) (fun t0 => get t0 (X s)) u HUnd Hu).
      - apply cnt_sym.
      - intro E. apply Ns. symmetry. exact E. }
    lia.
  Qed.

  (* ----- pigeonhole on states ----- *)

  Definition vec (s : Sh) : list bool := map (fun j => get j s) js.

  Lemma nodup_states_bound : forall l : list Sh, NoDup l -> length l <= 2 ^ length js.
  Proof.
    intros l Hn. rewrite <- blists_len. rewrite <- (lfs_len_map Sh (list bool) vec l).
    apply NoDup_incl_length.
    - apply lfs_nodup_map; [| exact Hn]. intros a b _ _ E. apply sh_ext.
      exact (lfs_map_eq bool (fun j => get j a) (fun j => get j b) js E).
    - intros v Hv. apply in_map_iff in Hv. destruct Hv as [s [<- _]].
      replace (length js) with (length (vec s)) by (unfold vec; apply lfs_len_map). apply blists_all.
  Qed.

  Lemma sh_dec : forall s t : Sh, {s = t} + {s <> t}.
  Proof. exact (sh_eq_dec bool Sh bool_dec js get sh_ext). Defined.

  Lemma pigeon : forall g : nat -> Sh, exists i j, i < j <= 2 ^ length js /\ g i = g j.
  Proof.
    intros g. set (B := 2 ^ length js).
    assert (Hd : forall n, {exists i j, i < j <= n /\ g i = g j} + {forall i j, i < j <= n -> g i <> g j}).
    { induction n as [| n IH].
      - right. intros i j H. lia.
      - destruct IH as [H | H]; [left; destruct H as [i [j [Hij E]]]; exists i, j; split; [lia | exact E] |].
        destruct (lfs_dec_ex_le (fun i => g i = g (S n)) (fun i => sh_dec (g i) (g (S n))) n)
          as [Q | N].
        + left. destruct Q as [i [Hi E]]. exists i, (S n). split; [lia | exact E].
        + right. intros i j Hij. destruct (Nat.eq_dec j (S n)) as [-> | Nj]; [apply N; lia |].
          apply H. lia. }
    destruct (Hd B) as [H | H]; [exact H |]. exfalso.
    assert (Hn : forall n, n <= B -> NoDup (map g (seq 0 (S n)))).
    { induction n as [| n IH]; intros Hn.
      - simpl. constructor; [intros [] | constructor].
      - rewrite lfs_seq_snoc, map_app. apply lfs_nodup_snoc; [apply IH; lia |].
        intro Hin. apply in_map_iff in Hin. destruct Hin as [i [Ei Hi]]. apply in_seq in Hi.
        apply (H i (0 + S n)); [lia | exact Ei]. }
    pose proof (nodup_states_bound _ (Hn B (le_n _))) as L.
    rewrite lfs_len_map, lfs_len_seq in L. fold B in L. lia.
  Qed.

  (* Shih and Ho 1999, Theorem 3.1 (the iteration graph is simple), mechanized by a different
     proof: (A) and (B) give a unique fixed point q reached by every synchronous orbit within
     2^|js| steps. *)
  Theorem sync_simple : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall x, exists N q, N <= 2 ^ length js /\ orb N x = q /\ F q = q /\ (forall p, F p = p -> p = q).
  Proof.
    intros Hnd Hc Hod x.
    destruct (pigeon (fun i => orb i x)) as [i [j [Hij E]]].
    assert (Hq : F (orb i x) = orb i x).
    { refine (sync_orbit_fixed Hnd Hod (orb i x) (j - i - 1) _ 0 (acyclic_at_all Hc _)).
      cbv beta in E. unfold orb in *. rewrite <- lfs_iter_add. replace (S (j - i - 1) + i) with j by lia.
      symmetry. exact E. }
    exists i, (orb i x). split; [lia | split; [reflexivity | split; [exact Hq |]]].
    intros p Hp. apply (local_fidelity Sh js get set get_set_eq get_set_neq sh_ext Fv); [| exact Hp | exact Hq].
    intros z c Hcc [Hcy _]. exact (Hc z c Hcc Hcy).
  Qed.

  (* ========================================================================================== *)
  (* Part 3. Tokens: the number of unstable vertices.                                           *)
  (* ========================================================================================== *)

  (* (B): no asynchronous step increases the number of unstable vertices. *)
  Theorem ucnt_mono : NoDup js -> OutDeg1 Sh get set Fv js -> forall v x, ucnt (ru v x) <= ucnt x.
  Proof.
    intros Hnd Hod v x. destruct (in_dec Nat.eq_dec v js) as [Hv | Hv];
      [| rewrite (rupd_out bool Sh js set Fv v x Hv); lia].
    destruct (ru_cases v x Hv) as [[_ E] | [N E]]; rewrite E; [lia |].
    unfold ucnt.
    pose proof (cnt_tri js (fun t => get t (flp v x)) (fun t => Fv t x) (fun t => Fv t (flp v x))) as T.
    assert (E1 : S (cnt js (fun t => get t (flp v x)) (fun t => Fv t x)) = cnt js (fun t => get t x) (fun t => Fv t x)).
    { rewrite (cnt_ext js (fun t => get t (flp v x)) (fun t => xorb (get t x) (Nat.eqb v t))
                 (fun t => Fv t x) (fun t => Fv t x)).
      - apply cnt_flip_neq; [exact Hnd | exact Hv |]. intro Q. apply N. symmetry. exact Q.
      - intros t _. exact (get_flip Sh js get set get_set_eq get_set_neq v t x Hv).
      - intros t _. reflexivity. }
    assert (E2 : cnt js (fun t => Fv t x) (fun t => Fv t (flp v x)) <= 1).
    { change (cnt js (fun t => Fv t x) (fun t => Fv t (flp v x))) with (dF Sh Fv js x (flp v x)).
      rewrite dF_flip. exact (Hod x v Hv). }
    lia.
  Qed.

  (* With at most one unstable vertex, an asynchronous step is a no-op or the synchronous step. *)
  Lemma one_step_F : forall x, ucnt x <= 1 -> forall a, ru a x = x \/ ru a x = F x.
  Proof.
    intros x Hx a. destruct (in_dec Nat.eq_dec a js) as [Ha | Ha];
      [| left; exact (rupd_out bool Sh js set Fv a x Ha)].
    destruct (ru_cases a x Ha) as [[_ E] | [N E]]; [left; exact E | right].
    rewrite E. unfold ucnt in Hx.
    destruct (cnt js (fun t => get t x) (fun t => Fv t x)) as [| [| k]] eqn:C; [| | lia].
    - exfalso. apply N. symmetry. exact (cnt_zero js _ _ C a Ha).
    - destruct (cnt_one js _ _ C) as [j [Hj [Nj Oj]]].
      assert (Ej : j = a).
      { destruct (Nat.eq_dec j a) as [Q | Q]; [exact Q |]. exfalso. apply N. symmetry.
        apply (Oj a Ha). intro Q'. apply Q. symmetry. exact Q'. }
      subst j. apply sh_ext. intros k Hk. rewrite get_F by exact Hk.
      rewrite (get_flip Sh js get set get_set_eq get_set_neq a k x Ha).
      destruct (Nat.eq_dec k a) as [-> | Nk].
      + rewrite Nat.eqb_refl. destruct (Fv a x), (get a x); simpl; congruence.
      + rewrite (proj2 (Nat.eqb_neq a k)) by (intro Q; apply Nk; symmetry; exact Q).
        rewrite xorb_false_r. exact (Oj k Hk Nk).
  Qed.

  Lemma orbit_of_run : NoDup js -> OutDeg1 Sh get set Fv js ->
    forall w y, ucnt y <= 1 -> exists m, xw w y = orb m y.
  Proof.
    intros Hnd Hod. induction w as [| a w IH]; intros y Hy; [exists 0; reflexivity |].
    change (xw (a :: w) y) with (xw w (ru a y)).
    destruct (one_step_F y Hy a) as [E | E]; rewrite E.
    - exact (IH y Hy).
    - assert (Hy' : ucnt (F y) <= 1) by (rewrite <- E; pose proof (ucnt_mono Hnd Hod a y); lia).
      destruct (IH (F y) Hy') as [m Hm]. exists (S m). rewrite Hm. unfold orb.
      apply lfs_iter_succ_r.
  Qed.

  (* The single-token lemma, localized: (B), (A) at x and at most one unstable vertex at x. No
     closed asynchronous run from x changes the state. *)
  Theorem one_token_closed : NoDup js -> OutDeg1 Sh get set Fv js ->
    forall x, AcyclicAt x -> ucnt x <= 1 -> forall w1 w2, xw (w1 ++ w2) x = x -> xw w1 x = x.
  Proof.
    intros Hnd Hod x Hac Hx.
    destruct (sh_dec (F x) x) as [Hf | Hf]; [intros w1 _ _; exact (fixed_xw x Hf w1) |].
    induction w1 as [| a w1 IH]; intros w2 Hw; [reflexivity |].
    change (xw ((a :: w1) ++ w2) x) with (xw (w1 ++ w2) (ru a x)) in Hw.
    change (xw (a :: w1) x) with (xw w1 (ru a x)).
    destruct (one_step_F x Hx a) as [E | E]; rewrite E in *; [exact (IH w2 Hw) |].
    exfalso. apply Hf.
    assert (Hx' : ucnt (F x) <= 1) by (rewrite <- E; pose proof (ucnt_mono Hnd Hod a x); lia).
    destruct (orbit_of_run Hnd Hod (w1 ++ w2) (F x) Hx') as [m Hm].
    refine (sync_orbit_fixed Hnd Hod x m _ 0 Hac).
    unfold orb in *. rewrite <- lfs_iter_succ_r, <- Hm. exact Hw.
  Qed.

  (* ========================================================================================== *)
  (* Part 4. From no closed change to fair settlement.                                          *)
  (* ========================================================================================== *)

  Lemma prs_xw : forall sch b k h,
    prs Sh ru sch (b + k) h = xw (map sch (seq b k)) (prs Sh ru sch b h).
  Proof.
    intros sch b k h. induction k as [| k IH]; [rewrite Nat.add_0_r; reflexivity |].
    rewrite Nat.add_succ_r. simpl prs. rewrite IH, lfs_seq_snoc, map_app.
    rewrite (xr_app bool Sh js set Fv). reflexivity.
  Qed.

  (* A fair run that settles settles at a fixed point. *)
  Lemma settles_fixed : forall sch, Fair js sch -> forall h0 q, Settles Sh ru sch h0 q -> F q = q.
  Proof.
    intros sch [_ Hf] h0 q [N HN].
    apply (proj2 (fixed_iff Sh js get set get_set_eq get_set_neq sh_ext Fv q)).
    intros j Hj. destruct (Hf j N Hj) as [m [Hm Em]].
    pose proof (HN (S m) ltac:(lia)) as A. simpl in A. rewrite Em, (HN m Hm) in A.
    rewrite <- (get_rupd_same bool Sh js get set get_set_eq Fv j q Hj), A. reflexivity.
  Qed.

  Lemma round : forall sch, Fair js sch -> forall n, exists R, n <= R /\
    forall j, In j js -> exists t, n <= t < R /\ sch t = j.
  Proof.
    intros sch [_ Hf] n.
    assert (G : forall l, incl l js -> exists R, n <= R /\ forall j, In j l -> exists t, n <= t < R /\ sch t = j).
    { induction l as [| a l IH]; intros Hl; [exists n; split; [lia | intros j []] |].
      destruct (IH (fun u Hu => Hl u (or_intror Hu))) as [R [HR HcR]].
      destruct (Hf a n (Hl a (or_introl eq_refl))) as [m [Hm Em]].
      exists (Nat.max R (S m)). split; [lia |]. intros j [<- | Hj].
      - exists m. split; [lia | exact Em].
      - destruct (HcR j Hj) as [t [Ht Et]]. exists t. split; [lia | exact Et]. }
    exact (G js (incl_refl _)).
  Qed.

  Theorem fair_settles_closed : forall (P : Sh -> Prop), (forall a y, P y -> P (ru a y)) ->
    NoClosedChange P -> forall sch, Fair js sch -> forall h0, P h0 ->
    exists q, F q = q /\ Settles Sh ru sch h0 q.
  Proof.
    intros P HP Hnc sch Hfair h0 HP0.
    set (st := fun n => prs Sh ru sch n h0).
    assert (HPst : forall n, P (st n)) by (induction n as [| n IH]; [exact HP0 | exact (HP _ _ IH)]).
    assert (Hst : forall b k, st (b + k) = xw (map sch (seq b k)) (st b)) by (intros; apply prs_xw).
    assert (Hdec : forall n k, {exists t, n <= t < n + k /\ st t <> st (S t)} +
                               {forall t, n <= t < n + k -> st t = st (S t)}).
    { intros n. induction k as [| k IH]; [right; intros t Ht; lia |].
      destruct IH as [H | H]; [left; destruct H as [t [Ht Nt]]; exists t; split; [lia | exact Nt] |].
      destruct (sh_dec (st (n + k)) (st (S (n + k)))) as [E | N].
      - right. intros t Ht. destruct (Nat.eq_dec t (n + k)) as [-> | Nt]; [exact E | apply H; lia].
      - left. exists (n + k). split; [lia | exact N]. }
    assert (Main : forall f (vis : list Sh) n, NoDup vis -> length vis + f = S (2 ^ length js) ->
              (forall z, In z vis -> exists b t, b <= t /\ S t <= n /\ st b = z /\ st t <> st (S t)) ->
              exists q, F q = q /\ Settles Sh ru sch h0 q).
    { induction f as [| f IH]; intros vis n Hnd Hlen Hvis.
      { pose proof (nodup_states_bound vis Hnd). lia. }
      destruct (round sch Hfair n) as [R [HnR Hcov]].
      destruct (Hdec n (R - n)) as [[t0 [Ht0 Nt0]] | Hno].
      - destruct (in_dec sh_dec (st n) vis) as [Hin | Hout].
        + exfalso. destruct (Hvis _ Hin) as [b [t [Hbt [Htn [Eb Nt]]]]].
          assert (Hclosed : forall k, k <= n - b -> st (b + k) = st b).
          { intros k Hk.
            assert (W : xw (map sch (seq b k) ++ map sch (seq (b + k) (n - b - k))) (st b) = st b).
            { rewrite <- map_app, <- lfs_seq_app. replace (k + (n - b - k)) with (n - b) by lia.
              rewrite <- Hst. replace (b + (n - b)) with n by lia. rewrite Eb. reflexivity. }
            rewrite Hst. exact (Hnc (st b) _ _ (HPst b) W). }
          apply Nt. replace t with (b + (t - b)) by lia. replace (S (b + (t - b))) with (b + (S t - b)) by lia.
          rewrite !Hclosed by lia. reflexivity.
        + apply (IH (st n :: vis) R).
          * constructor; assumption.
          * simpl. lia.
          * intros z [<- | Hz].
            -- exists n, t0. split; [lia | split; [lia | split; [reflexivity | exact Nt0]]].
            -- destruct (Hvis z Hz) as [b [t [H1 [H2 H3]]]]. exists b, t. split; [exact H1 | split; [lia | exact H3]].
      - assert (Hc : forall k, k <= R - n -> st (n + k) = st n).
        { induction k as [| k IHk]; intros Hk; [rewrite Nat.add_0_r; reflexivity |].
          rewrite Nat.add_succ_r, <- (Hno (n + k)) by lia. apply IHk. lia. }
        assert (Hfix : F (st n) = st n).
        { apply (proj2 (fixed_iff Sh js get set get_set_eq get_set_neq sh_ext Fv (st n))).
          intros j Hj. destruct (Hcov j Hj) as [t [Ht Et]].
          assert (A : st (S t) = ru j (st n)).
          { change (st (S t)) with (ru (sch t) (st t)). rewrite Et.
            replace t with (n + (t - n)) by lia. rewrite Hc by lia. reflexivity. }
          assert (B : st (S t) = st n) by (replace (S t) with (n + S (t - n)) by lia; apply Hc; lia).
          rewrite <- (get_rupd_same bool Sh js get set get_set_eq Fv j (st n) Hj), <- A, B. reflexivity. }
        exists (st n). split; [exact Hfix |]. exists n. intros m Hm.
        replace m with (n + (m - n)) by lia. change (prs Sh ru sch (n + (m - n)) h0) with (st (n + (m - n))).
        rewrite Hst. apply fixed_xw. exact Hfix. }
    apply (Main (S (2 ^ length js)) [] 0); [constructor | reflexivity | intros z []].
  Qed.

  (* Acyclicity of the asynchronous state graph, with (A), gives fair settlement at the unique
     fixed point from every start (the E-side analogue of FairFlushR). *)
  Theorem fair_settlement_of_acyclic : NoLocalCycle Sh get set Fv js -> NoClosedChange (fun _ => True) ->
    forall q, F q = q -> (forall p, F p = p -> p = q) /\
    forall sch, Fair js sch -> forall h0, Settles Sh ru sch h0 q.
  Proof.
    intros Hc Hnc q Hq.
    assert (Hu : forall p, F p = p -> p = q).
    { intros p Hp. apply (local_fidelity Sh js get set get_set_eq get_set_neq sh_ext Fv); [| exact Hp | exact Hq].
      intros z c Hcc [Hcy _]. exact (Hc z c Hcc Hcy). }
    split; [exact Hu |]. intros sch Hf h0.
    destruct (fair_settles_closed (fun _ => True) (fun _ _ _ => I) Hnc sch Hf h0 I) as [q' [Hq' Hs]].
    rewrite <- (Hu q' Hq'). exact Hs.
  Qed.

  (* A rank that strictly decreases along every real asynchronous move certifies acyclicity. *)
  Lemma rank_closed : forall r : Sh -> nat, (forall a x, ru a x <> x -> r (ru a x) < r x) ->
    NoClosedChange (fun _ => True).
  Proof.
    intros r Hr.
    assert (Mono : forall w y, r (xw w y) <= r y /\ (xw w y <> y -> r (xw w y) < r y)).
    { induction w as [| a w IH]; intros y; [split; [apply Nat.le_refl | intros N; exfalso; apply N; reflexivity] |].
      change (xw (a :: w) y) with (xw w (ru a y)).
      destruct (sh_dec (ru a y) y) as [E | N].
      - rewrite E. exact (IH y).
      - pose proof (Hr a y N). destruct (IH (ru a y)) as [H1 _]. split; [lia | intros _; lia]. }
    intros x w1 w2 _ Hw. destruct (sh_dec (xw w1 x) x) as [E | N]; [exact E |]. exfalso.
    rewrite (xr_app bool Sh js set Fv) in Hw.
    destruct (Mono w1 x) as [_ H1]. destruct (Mono w2 (xw w1 x)) as [H2 _].
    pose proof (H1 N). rewrite Hw in H2. lia.
  Qed.

  (* ========================================================================================== *)
  (* Part 5. Fair settlement from at most one unstable vertex.                                  *)
  (* ========================================================================================== *)

  Theorem one_token_fair_settlement : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall q, F q = q -> forall sch, Fair js sch -> forall h0, ucnt h0 <= 1 -> Settles Sh ru sch h0 q.
  Proof.
    intros Hnd Hc Hod q Hq sch Hf h0 H0.
    assert (Hu : forall p, F p = p -> p = q).
    { intros p Hp. apply (local_fidelity Sh js get set get_set_eq get_set_neq sh_ext Fv); [| exact Hp | exact Hq].
      intros z c Hcc [Hcy _]. exact (Hc z c Hcc Hcy). }
    destruct (fair_settles_closed (fun y => ucnt y <= 1)
                (fun a y Hy => Nat.le_trans _ _ _ (ucnt_mono Hnd Hod a y) Hy)
                (fun x w1 w2 Hx Hw => one_token_closed Hnd Hod x (acyclic_at_all Hc x) Hx w1 w2 Hw)
                sch Hf h0 H0) as [q' [Hq' Hs]].
    rewrite <- (Hu q' Hq'). exact Hs.
  Qed.

  Lemma fair_shift : forall sch n, Fair js sch -> Fair js (fun t => sch (n + t)).
  Proof.
    intros sch n [H1 H2]. split; [intros t; apply H1 |].
    intros j m Hj. destruct (H2 j (n + m) Hj) as [k [Hk Ek]]. exists (k - n). split; [lia |].
    replace (n + (k - n)) with k by lia. exact Ek.
  Qed.

  (* Every fair run that ever reaches a state with at most one unstable vertex settles at the
     unique fixed point. *)
  Theorem fair_settles_once_one_token : NoDup js -> NoLocalCycle Sh get set Fv js -> OutDeg1 Sh get set Fv js ->
    forall q, F q = q -> forall sch, Fair js sch -> forall h0 n,
    ucnt (prs Sh ru sch n h0) <= 1 -> Settles Sh ru sch h0 q.
  Proof.
    intros Hnd Hc Hod q Hq sch Hf h0 n Hn.
    destruct (one_token_fair_settlement Hnd Hc Hod q Hq (fun t => sch (n + t)) (fair_shift sch n Hf)
                (prs Sh ru sch n h0) Hn) as [N HN].
    exists (n + N). intros m Hm. replace m with (n + (m - n)) by lia.
    rewrite prs_shift. apply HN. lia.
  Qed.
End Lens.

(* ============================================================================================ *)
(* Part 6. Boundary instances.                                                                   *)
(* ============================================================================================ *)

Fixpoint bnat (n : nat) : BV n -> nat :=
  match n return BV n -> nat with
  | O => fun _ => 0
  | S m => fun s => (if fst s then 1 else 0) + 2 * bnat m (snd s)
  end.

(* A decidable rank certificate on Boolean vectors. *)
Definition rank_ok_b (n : nat) (Fv : nat -> BV n -> bool) (r : BV n -> nat) : bool :=
  forallb (fun x => forallb (fun a =>
    if bv_eq_dec n (rupd bool (BV n) (seq 0 n) (bset n) Fv a x) x then true
    else Nat.ltb (r (rupd bool (BV n) (seq 0 n) (bset n) Fv a x)) (r x)) (seq 0 n)) (benum n).

Lemma rank_ok_sound : forall n Fv r, rank_ok_b n Fv r = true ->
  NoClosedChange (BV n) (seq 0 n) (bset n) Fv (fun _ => True).
Proof.
  intros n Fv r H.
  apply (rank_closed (BV n) (seq 0 n) (bget n) (bset n) (bext n) Fv r).
  intros a x N. destruct (in_dec Nat.eq_dec a (seq 0 n)) as [Ha | Ha];
    [| exfalso; exact (N (rupd_out bool (BV n) (seq 0 n) (bset n) Fv a x Ha))].
  unfold rank_ok_b in H. rewrite forallb_forall in H. pose proof (H x (benum_all n x)) as H1.
  rewrite forallb_forall in H1. pose proof (H1 a Ha) as H2.
  destruct (bv_eq_dec n (rupd bool (BV n) (seq 0 n) (bset n) Fv a x) x) as [E | _]; [contradiction |].
  apply Nat.ltb_lt. exact H2.
Qed.

(* ----- Shih and Ho's example: (A) and (B), a global 2-cycle, acyclic state graph ----- *)

(* Shih and Ho 1999, Section 3, item (5) (0-indexed, + is or):
   x0 := not x1 || not x2 || x3, x1 := 1, x2 := 1, x3 := not x0 || x1 || x2. *)
Definition sh_F (i : nat) (s : BV 4) : bool :=
  match i with
  | 0 => negb (bget 4 1 s) || negb (bget 4 2 s) || bget 4 3 s
  | 1 => true
  | 2 => true
  | 3 => negb (bget 4 0 s) || bget 4 1 s || bget 4 2 s
  | _ => false
  end.
Definition sh_q : BV 4 := (true, (true, (true, (true, tt)))).
(* The longest asynchronous path from each state (index bnat 4 s). *)
Definition sh_rank (s : BV 4) : nat := nth (bnat 4 s) [8; 5; 5; 4; 5; 4; 2; 3; 7; 6; 2; 1; 2; 1; 1; 0] 0.
Definition sh_x1 : BV 4 := (false, (true, (true, (false, tt)))).

Theorem shih_ho_instance :
  NoDup (seq 0 4) /\
  NoLocalCycle (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  OutDeg1 (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  larc (BV 4) (bget 4) (bset 4) sh_F (false, (false, (false, (false, tt)))) 0 3 = true /\
  larc (BV 4) (bget 4) (bset 4) sh_F (false, (true, (true, (false, tt)))) 3 0 = true /\
  NoClosedChange (BV 4) (seq 0 4) (bset 4) sh_F (fun _ => True) /\
  Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F sh_q = sh_q /\
  (forall p, Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F p = p -> p = sh_q) /\
  (forall sch, Fair (seq 0 4) sch -> forall h0, Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sh_F) sch h0 sh_q) /\
  ucnt (BV 4) (seq 0 4) (bget 4) sh_F sh_x1 = 1 /\
  (forall sch, Fair (seq 0 4) sch -> Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sh_F) sch sh_x1 sh_q).
Proof.
  assert (Hnd : NoDup (seq 0 4)) by (apply seq_NoDup).
  assert (Hc : NoLocalCycle (BV 4) (bget 4) (bset 4) sh_F (seq 0 4))
    by (apply (chk_none _ _ _ (benum 4)); [apply benum_all | vm_compute; reflexivity]).
  assert (Hod : OutDeg1 (BV 4) (bget 4) (bset 4) sh_F (seq 0 4))
    by (apply (outdeg_sound _ _ _ (benum 4)); [apply benum_all | vm_compute; reflexivity]).
  assert (Hnc : NoClosedChange (BV 4) (seq 0 4) (bset 4) sh_F (fun _ => True))
    by (apply (rank_ok_sound 4 sh_F sh_rank); vm_compute; reflexivity).
  assert (Hq : Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F sh_q = sh_q) by (vm_compute; reflexivity).
  destruct (fair_settlement_of_acyclic (BV 4) (seq 0 4) (bget 4) (bset 4) (bget_bset_eq 4) (bget_bset_neq 4)
              (bext 4) sh_F Hc Hnc sh_q Hq) as [Hu Hs].
  split; [exact Hnd | split; [exact Hc | split; [exact Hod |]]].
  split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]].
  split; [exact Hnc | split; [exact Hq | split; [exact Hu | split; [exact Hs |]]]].
  split; [vm_compute; reflexivity |].
  intros sch Hf. apply (one_token_fair_settlement (BV 4) (seq 0 4) (bget 4) (bset 4) (bget_bset_eq 4)
                          (bget_bset_neq 4) (bext 4) sh_F Hnd Hc Hod sh_q Hq sch Hf).
  vm_compute. lia.
Qed.

(* ----- (B) is needed: Shih and Dong's network ----- *)

Definition sd_o : BV 4 := (false, (true, (true, (false, tt)))).

Theorem outdeg_needed :
  NoLocalCycle (BV 4) (bget 4) (bset 4) sd_F (seq 0 4) /\
  ~ OutDeg1 (BV 4) (bget 4) (bset 4) sd_F (seq 0 4) /\
  orb (BV 4) (seq 0 4) (bset 4) sd_F 3 sd_o = sd_o /\
  Fsync bool (BV 4) (seq 0 4) (bset 4) sd_F sd_o <> sd_o /\
  Fair (seq 0 4) sd_sch /\
  (forall q, ~ Settles (BV 4) (rupd bool (BV 4) (seq 0 4) (bset 4) sd_F) sd_sch sd_h0 q) /\
  ~ NoClosedChange (BV 4) (seq 0 4) (bset 4) sd_F (fun _ => True).
Proof.
  destruct shih_dong_not_fair as (Hc & _ & _ & Hf & Hper & Hns).
  split; [exact Hc |]. split.
  { intros H. pose proof (H (false, (false, (false, (false, tt)))) 2 ltac:(simpl; tauto)) as L.
    vm_compute in L. lia. }
  split; [vm_compute; reflexivity |]. split; [vm_compute; discriminate |].
  split; [exact Hf | split; [exact Hns |]].
  intros H. assert (W : xr bool (BV 4) (seq 0 4) (bset 4) sd_F ([2] ++ [3; 0; 1; 3; 2; 0; 1]) sd_h0 = sd_h0)
    by (vm_compute; reflexivity).
  pose proof (H sd_h0 [2] [3; 0; 1; 3; 2; 0; 1] I W) as E. vm_compute in E. discriminate E.
Qed.

(* ----- no local negative cycle is not enough: the positive 3-ring ----- *)

Theorem no_neg_not_enough :
  NoLocalNeg R3 get3 set3 ring_F r3js /\ OutDeg1 R3 get3 set3 ring_F r3js /\
  Fair r3js r3sg /\ (forall q, ~ Settles R3 (rupd3 ring_F) r3sg r3h0 q).
Proof.
  destruct ring_local_conditions as (_ & Hn & Hod & _ & _ & _ & _ & Hf & Hns & _).
  split; [exact Hn | split; [exact Hod | split; [exact Hf |]]].
  intros q Hs. pose proof (settles_fixed R3 r3js get3 set3 get3_set_eq get3_set_neq s3_ext ring_F r3sg Hf r3h0 q Hs) as Hq.
  destruct Hs as [N HN]. apply (Hns N). rewrite (HN N (le_n _)).
  apply (settled_fixed bool R3 r3js get3 set3 get3_set_eq get3_set_neq s3_ext). exact Hq.
Qed.

(* ----- no local positive cycle is not enough: the negative 3-ring ----- *)

Definition ng_F (i : nat) (s : BV 3) : bool :=
  match i with
  | 0 => bget 3 1 s
  | 1 => bget 3 2 s
  | 2 => negb (bget 3 0 s)
  | _ => false
  end.
Definition ng_h : BV 3 := (false, (false, (false, tt))).

Theorem no_pos_not_enough :
  NoLocalPos (BV 3) (bget 3) (bset 3) ng_F (seq 0 3) /\
  OutDeg1 (BV 3) (bget 3) (bset 3) ng_F (seq 0 3) /\
  xr bool (BV 3) (seq 0 3) (bset 3) ng_F [2; 1; 0; 2; 1; 0] ng_h = ng_h /\
  xr bool (BV 3) (seq 0 3) (bset 3) ng_F [2] ng_h <> ng_h /\
  ~ NoClosedChange (BV 3) (seq 0 3) (bset 3) ng_F (fun _ => True) /\
  (forall p, Fsync bool (BV 3) (seq 0 3) (bset 3) ng_F p <> p) /\
  (forall sch, Fair (seq 0 3) sch -> forall h0 q, ~ Settles (BV 3) (rupd bool (BV 3) (seq 0 3) (bset 3) ng_F) sch h0 q).
Proof.
  assert (Hn : forall p, Fsync bool (BV 3) (seq 0 3) (bset 3) ng_F p <> p).
  { intros p H. apply bfixed_iff in H.
    assert (A : forallb (fun s => negb (ifixed_b 3 ng_F s)) (benum 3) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in A. pose proof (A p (benum_all 3 p)) as Ap. rewrite H in Ap. discriminate Ap. }
  assert (W : xr bool (BV 3) (seq 0 3) (bset 3) ng_F ([2] ++ [1; 0; 2; 1; 0]) ng_h = ng_h) by (vm_compute; reflexivity).
  split; [apply (chk_pos _ _ _ (benum 3)); [apply benum_all | vm_compute; reflexivity] |].
  split; [apply (outdeg_sound _ _ _ (benum 3)); [apply benum_all | vm_compute; reflexivity] |].
  split; [exact W | split; [vm_compute; discriminate |]].
  split; [intros H; pose proof (H ng_h [2] _ I W) as E; vm_compute in E; discriminate E |].
  split; [exact Hn |].
  intros sch Hf h0 q Hs.
  exact (Hn q (settles_fixed (BV 3) (seq 0 3) (bget 3) (bset 3) (bget_bset_eq 3) (bget_bset_neq 3) (bext 3)
                 ng_F sch Hf h0 q Hs)).
Qed.
