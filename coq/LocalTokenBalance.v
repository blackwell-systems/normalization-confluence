(* LocalTokenBalance.v: at most half of the unstable vertices of any state disagree with nothing,
   that is, at most half of the tokens are "bad" relative to a fixed point, under out-degree at
   most one (gap 3 of REGIME-AUDIT.md, LossyNetworks P2: a general imbalance law; gap 3 stays
   open). Axiom-free.

   Setting: the lens model of LocalSigned.v (states Sh read through get and set on the vertex
   list js, resolvers Fv, the synchronous map F = Fsync). A "token" is an unstable vertex
   (LocalFairSettlement.ucnt counts them). Fix any state p. A token at t is "good" at x when
   x_t <> p_t (firing it moves toward p) and "bad" when x_t = p_t; ng p x and nb p x count them.

   Results.
     ucnt_split        every token is good or bad: ucnt x = ng p x + nb p x.
     image_distance    the identity d(F x, p) + g = d(x, p) + b, for every state p (no
                       hypothesis): F(x) differs from x exactly at the tokens, a good token flips
                       toward p and a bad one away. In integers, d(F x, p) = d(x, p) - g + b.
     bad_le_good       (B), and F p = p: b <= g at every state, for every number of tokens.
                       Non-expansiveness with F(p) = p gives d(F x, p) <= d(x, p)
                       (LocalSigned.outdeg_nonexpansive), and image_distance turns it into b <= g.
                       Neither (A) nor the absence of self-loops is used.
     bad_half          the same as 2 b <= k, where k = ucnt x.
     bad_le_half       b <= k / 2 (floor): one token gives b = 0, two or three give b <= 1, four
                       or five give b <= 2.
     not_both_bad_k2   LocalTwoToken.not_both_bad recovered as the case k = 2: of two tokens at
                       least one is good.
     three_token_shape with exactly three tokens, (g, b) is (3, 0) or (2, 1). This is a counting
                       consequence only; it says nothing about closed runs with three tokens.
     token_balance_instance
                       non-vacuity on Shih and Ho's network (LocalFairSettlement.sh_F, which has
                       (A) and (B) and the fixed point 1111): two tokens (1, 1) at 1110, where the
                       bound is attained; three tokens (3, 0) at 0100 and (2, 1) at 1001.
   What is NOT proved here: anything about closed asynchronous runs with three or more tokens.
   The structural lemmas mined for that case are in research/gap3-fair-settlement/K3.md. Gap 3
   stays open. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.DistributedCycles NC.CanonicalExecution NC.SignedResolver NC.LocalSigned.
Require Import NC.LocalFairSettlement NC.LocalTwoToken.
Import ListNotations.

(* ============================================================================================ *)
(* Part 0. Counting.                                                                            *)
(* ============================================================================================ *)

Definition ltb_n (b : bool) : nat := if b then 1 else 0.

(* Two pairs of filters over the same list have equal total length when they agree pointwise. *)
Lemma ltb_len_balance : forall (a b c d : nat -> bool) l,
  (forall t, In t l -> ltb_n (a t) + ltb_n (b t) = ltb_n (c t) + ltb_n (d t)) ->
  length (filter a l) + length (filter b l) = length (filter c l) + length (filter d l).
Proof.
  intros a b c d. induction l as [| t l IH]; intros H; [reflexivity |]. simpl.
  pose proof (IH (fun s Hs => H s (or_intror Hs))) as E. pose proof (H t (or_introl eq_refl)) as Et.
  unfold ltb_n in Et. destruct (a t), (b t), (c t), (d t); simpl in *; lia.
Qed.

Lemma ltb_len_pos : forall (f : nat -> bool) l t, In t l -> f t = true -> 1 <= length (filter f l).
Proof.
  intros f l t Ht Ft. destruct (filter f l) as [| u r] eqn:E; [| simpl; lia].
  assert (In t (filter f l)) as Hin by (apply filter_In; split; assumption).
  rewrite E in Hin. destruct Hin.
Qed.

(* ============================================================================================ *)
(* Part 1. Good and bad tokens, and the image distance.                                         *)
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
  Local Notation uc := (ucnt Sh js get Fv).

  (* t is unstable at x (the same test as LocalTwoToken.un). *)
  Definition tk (x : Sh) (t : nat) : bool := negb (Bool.eqb (get t x) (Fv t x)).
  (* A good token disagrees with p, a bad token agrees with p. *)
  Definition gd (p x : Sh) (t : nat) : bool := tk x t && negb (Bool.eqb (get t x) (get t p)).
  Definition bd (p x : Sh) (t : nat) : bool := tk x t && Bool.eqb (get t x) (get t p).
  Definition ng (p x : Sh) : nat := length (filter (gd p x) js).
  Definition nb (p x : Sh) : nat := length (filter (bd p x) js).

  Lemma ucnt_split : forall p x, uc x = ng p x + nb p x.
  Proof.
    intros p x. unfold ucnt, cnt, ng, nb.
    pose proof (ltb_len_balance (fun t => negb (Bool.eqb (get t x) (Fv t x))) (fun _ => false)
                  (gd p x) (bd p x) js) as E.
    rewrite (ltt_filter_zero (fun _ => false) js (fun _ _ => eq_refl)) in E. rewrite <- E; [lia |].
    intros t _. unfold gd, bd, tk, ltb_n. destruct (get t x), (Fv t x), (get t p); reflexivity.
  Qed.

  (* d(F x, p) + g = d(x, p) + b, for every p. *)
  Theorem image_distance : forall p x, dS Sh get js (F x) p + ng p x = dS Sh get js x p + nb p x.
  Proof.
    intros p x. unfold dS, cnt, ng, nb. apply ltb_len_balance. intros t Ht.
    rewrite (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv x t Ht).
    unfold gd, bd, tk, ltb_n. destruct (get t x), (Fv t x), (get t p); reflexivity.
  Qed.

  (* ========================================================================================== *)
  (* Part 2. The imbalance law: at most half of the tokens are bad relative to a fixed point.   *)
  (* ========================================================================================== *)

  Section Fixed.
    Hypothesis Hnd : NoDup js.
    Hypothesis Hod : OutDeg1 Sh get set Fv js.
    Variable p : Sh.
    Hypothesis Hp : F p = p.

    Theorem bad_le_good : forall x, nb p x <= ng p x.
    Proof.
      intros x. pose proof (image_distance p x) as E.
      assert (L : dF Sh Fv js x p <= dS Sh get js x p).
      { apply (proj1 (outdeg_nonexpansive Sh js get set get_set_eq get_set_neq sh_ext Fv js Hnd (incl_refl js)) Hod).
        intros j Hj Hn. exfalso. exact (Hn Hj). }
      assert (Q : dF Sh Fv js x p = dS Sh get js (F x) p).
      { unfold dF, dS. apply cnt_ext; intros t Ht.
        - symmetry. exact (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv x t Ht).
        - rewrite <- (get_Fsync bool Sh js get set get_set_eq get_set_neq Fv p t Ht), Hp. reflexivity. }
      lia.
    Qed.

    Theorem bad_half : forall x, 2 * nb p x <= uc x.
    Proof. intros x. rewrite (ucnt_split p x). pose proof (bad_le_good x). lia. Qed.

    Theorem bad_le_half : forall x, nb p x <= uc x / 2.
    Proof.
      intros x. pose proof (bad_half x) as H.
      pose proof (Nat.div_mod (uc x) 2 ltac:(discriminate)) as E.
      pose proof (Nat.mod_upper_bound (uc x) 2 ltac:(discriminate)) as M. lia.
    Qed.

    (* LocalTwoToken.not_both_bad, as the case k = 2. *)
    Theorem not_both_bad_k2 : forall x a c, TwoTok Sh js get Fv x a c ->
      get a x = get a p -> get c x = get c p -> False.
    Proof.
      intros x a c T Ea Ec. pose proof T as (Ha & _ & _ & Ua & _).
      assert (G0 : ng p x = 0).
      { unfold ng. apply ltt_filter_zero. intros t Ht. unfold gd.
        destruct (tk x t) eqn:Ut; [| reflexivity]. simpl.
        destruct (two_in Sh js get Fv x a c t T Ht Ut) as [-> | ->].
        - rewrite Ea. destruct (get a p); reflexivity.
        - rewrite Ec. destruct (get c p); reflexivity. }
      assert (B1 : 1 <= nb p x).
      { unfold nb. apply (ltb_len_pos _ js a Ha). unfold bd. change (tk x a) with (un Sh get Fv x a).
        rewrite Ua, Ea. destruct (get a p); reflexivity. }
      pose proof (bad_le_good x). lia.
    Qed.

    (* With exactly three tokens: (3, 0) or (2, 1). *)
    Theorem three_token_shape : forall x, uc x = 3 ->
      (ng p x = 3 /\ nb p x = 0) \/ (ng p x = 2 /\ nb p x = 1).
    Proof. intros x H. rewrite (ucnt_split p x) in H. pose proof (bad_le_good x). lia. Qed.
  End Fixed.
End Lens.

(* ============================================================================================ *)
(* Part 3. Non-vacuity.                                                                          *)
(* ============================================================================================ *)

(* Shih and Ho's network with its fixed point 1111 (LocalFairSettlement.shih_ho_instance): two
   tokens (1, 1) at 1110 (the bound b <= g attained), three tokens (3, 0) at 0100 and (2, 1) at
   1001. *)
Definition sh_x30 : BV 4 := (false, (true, (false, (false, tt)))).
Definition sh_x21 : BV 4 := (true, (false, (false, (true, tt)))).

Theorem token_balance_instance :
  NoDup (seq 0 4) /\
  NoLocalCycle (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  OutDeg1 (BV 4) (bget 4) (bset 4) sh_F (seq 0 4) /\
  Fsync bool (BV 4) (seq 0 4) (bset 4) sh_F sh_q = sh_q /\
  ucnt (BV 4) (seq 0 4) (bget 4) sh_F sh_x2 = 2 /\
  ng (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x2 = 1 /\ nb (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x2 = 1 /\
  ucnt (BV 4) (seq 0 4) (bget 4) sh_F sh_x30 = 3 /\
  ng (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x30 = 3 /\ nb (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x30 = 0 /\
  ucnt (BV 4) (seq 0 4) (bget 4) sh_F sh_x21 = 3 /\
  ng (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x21 = 2 /\ nb (BV 4) (seq 0 4) (bget 4) sh_F sh_q sh_x21 = 1.
Proof.
  destruct shih_ho_instance as (Hnd & Hc & Hod & _ & _ & _ & Hq & _).
  split; [exact Hnd | split; [exact Hc | split; [exact Hod | split; [exact Hq |]]]].
  repeat split; vm_compute; reflexivity.
Qed.
