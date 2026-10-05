(* FederationEventsCyclesMulti.v: per-edge C1 checks compose into C1cyc for a target with several
   incoming edges (the combination step left open in FederationEventsCyclesCheck.v).

   FederationEventsCyclesCheck.v proves cyc_check_gc with each registry's shared part treated as
   one block: C1cyc quantifies over pairs of shared values h, h' of the whole block. gsm checks C1
   per edge: it overwrites ONE edge's variables with an image value of that edge's morphism and
   leaves the others alone. This file proves that the per-edge checks compose, and states what has
   to be checked jointly when a component is written by a resolver.

   Model. Registry k's shared part is a product of components indexed by the edges p with
   tgt p = k, each with a lens hget p / hset p (get-set laws between distinct components of the
   same target, and extensionality: two shared parts of k agreeing on every component of k are
   equal). Hp p is the image set of component p: the image of edge p's morphism over valid
   source states, or of a resolver over the joint source states (Part 3). The image set of the
   whole shared part of k is the product ProdImg k h : every component of k lies in its Hp.

     C1edge p  : for every event e of tgt p, every valid (x, h) with h in ProdImg, every v in Hp p,
                 the locals of sig e (x, hset p v h) equal the locals of sig e (x, h). Only
                 component p varies; the others stay at their (image) values in h. This is gsm's
                 per-edge C1.
     M1        : overwriting one component with an image value preserves validity on states whose
                 shared part is in ProdImg.

   Results.
     multi_edge_c1 (HEADLINE): C1edge p for every edge p, plus M1, imply C1cyc with
        Hs = ProdImg. The proof chains one component at a time from h to h'.
     multi_edge_c1_free : without any validity hypothesis, the per-edge check run over all
        locals x (valid or not) with h in ProdImg implies C1cyc.
     m1_necessary : M1 cannot be dropped. Two components, both image sets full, the only valid
        shared part is (false, false); the local outcome is "both components are true". Every
        per-edge C1 holds (from (false, false) one overwrite reaches at most one true), M1 fails,
        C1cyc fails at h = (false, false), h' = (true, true).
     resolver_joint_c1 : a component written by a resolver r from two sources. C1 must be checked
        with the component ranging over R = { r a b | a in Im1, b in Im2 }, the resolver's image.
        It decomposes into per-input checks only through r: varying a with b fixed, then b with a
        fixed, where every check evaluates r on the full input tuple (plus validity preserved by
        the first step).
     resolver_edge_insufficient : the per-edge images do not suffice for a resolver. r = plus,
        Im1 = Im2 = {0, 1}: C1cyc holds over {0, 1} (each edge's own image set), but R contains 2,
        C1cyc fails over R, and the per-input check through r fails too.
     multi_edge_gc / multi_edge_converges : per-edge C1 for every edge, M1, C2cyc over ProdImg,
        and "normal forms have each component in its image set" imply GC and convergence on the
        image of the normalizer (cyc_check_gc with Hs = ProdImg).
     multi_edge_instance (non-vacuity): a two-registry cycle in which BOTH targets have two
        incoming edges. A's components are fed by B's two locals; B's are fed by A's first local
        and by a closed slot (image {false}). B's event reads that closed slot, so the plain read
        footprint fails, while every per-edge C1, M1 and C2cyc hold; GC and convergence follow.
     resolver_instance (non-vacuity): every hypothesis of resolver_joint_c1 holds for r = plus,
        Im1 = {0}, Im2 = {0, 1} with an event that reads the resolver's output. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.Federation NC.FederationEventsCycles NC.FederationEventsCyclesCheck.
Import ListNotations.

(* ======================================================================================= *)
(* Part 1. Per-edge C1 composes into C1cyc on the product image set.                       *)
(* ======================================================================================= *)

Section Combine.
  Variables Lc Hc V Rg P E : Type.
  Variable rg_eq_dec : forall a b : Rg, {a = b} + {a <> b}.
  Variable p_eq_dec : forall a b : P, {a = b} + {a <> b}.
  Variable cvalid : Rg -> Lc * Hc -> Prop.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.

  (* Components of the shared parts: component p belongs to registry tgt p. *)
  Variable tgt : P -> Rg.
  Variable hget : P -> Hc -> V.
  Variable hset : P -> V -> Hc -> Hc.
  Hypothesis hget_hset_eq : forall p v h, hget p (hset p v h) = v.
  Hypothesis hget_hset_neq : forall p q v h, tgt q = tgt p -> q <> p ->
    hget q (hset p v h) = hget q h.
  Hypothesis h_ext : forall k h h', (forall p, tgt p = k -> hget p h = hget p h') -> h = h'.
  Variable pall : list P.
  Hypothesis pall_cover : forall p, In p pall.
  Variable Hp : P -> V -> Prop.

  (* The image set of registry k's whole shared part: the product of its components' images. *)
  Definition ProdImg (k : Rg) (h : Hc) : Prop := forall p, tgt p = k -> Hp p (hget p h).

  (* gsm's per-edge C1: only component p varies, over its image set. *)
  Definition C1edge (p : P) : Prop :=
    forall e x h v, reg e = tgt p -> cvalid (reg e) (x, h) -> ProdImg (reg e) h -> Hp p v ->
      fst (sig e (x, hset p v h)) = fst (sig e (x, h)).

  (* The same check with no validity condition on the base state. *)
  Definition C1edge_all (p : P) : Prop :=
    forall e x h v, reg e = tgt p -> ProdImg (reg e) h -> Hp p v ->
      fst (sig e (x, hset p v h)) = fst (sig e (x, h)).

  (* M1: overwriting one component with one of its image values preserves validity. *)
  Definition M1 : Prop :=
    forall p x h v, cvalid (tgt p) (x, h) -> ProdImg (tgt p) h -> Hp p v ->
      cvalid (tgt p) (x, hset p v h).

  (* Overwrite the components of k listed in l with their values in h'. *)
  Fixpoint upd (k : Rg) (h' : Hc) (l : list P) (h : Hc) : Hc :=
    match l with
    | [] => h
    | p :: l' => if rg_eq_dec (tgt p) k then hset p (hget p h') (upd k h' l' h)
                 else upd k h' l' h
    end.

  Lemma upd_get_in : forall k h h' l q, tgt q = k -> In q l -> hget q (upd k h' l h) = hget q h'.
  Proof.
    intros k h h' l q Hq. induction l as [| p l IH]; simpl; [intros [] |]. intros Hin.
    destruct (rg_eq_dec (tgt p) k) as [Ep | Np].
    - destruct (p_eq_dec q p) as [-> | Nq].
      + apply hget_hset_eq.
      + rewrite (hget_hset_neq _ _ _ _ (eq_trans Hq (eq_sym Ep)) Nq). apply IH.
        destruct Hin as [E' | H']; [congruence | exact H'].
    - destruct Hin as [E' | H']; [subst; congruence | apply IH; exact H'].
  Qed.

  Lemma upd_prod : forall k h h' l, ProdImg k h -> ProdImg k h' -> ProdImg k (upd k h' l h).
  Proof.
    intros k h h' l Hh Hh'. induction l as [| p l IH]; simpl; [exact Hh |].
    destruct (rg_eq_dec (tgt p) k) as [Ep | Np]; [| exact IH].
    intros q Hq. destruct (p_eq_dec q p) as [-> | Nq].
    - rewrite hget_hset_eq. apply Hh'. exact Hq.
    - rewrite (hget_hset_neq _ _ _ _ (eq_trans Hq (eq_sym Ep)) Nq). apply IH. exact Hq.
  Qed.

  Lemma upd_full : forall k h h', upd k h' pall h = h'.
  Proof.
    intros k h h'. apply (h_ext k). intros p Hp'. apply upd_get_in; [exact Hp' | apply pall_cover].
  Qed.

  (* The chain, for any validity predicate W of registry k closed under image overwrites. *)
  Lemma chainW : forall (W : Lc * Hc -> Prop) k e x h h', reg e = k ->
    (forall p x h v, tgt p = k -> W (x, h) -> ProdImg k h -> Hp p v -> W (x, hset p v h)) ->
    (forall p x h v, tgt p = k -> W (x, h) -> ProdImg k h -> Hp p v ->
       fst (sig e (x, hset p v h)) = fst (sig e (x, h))) ->
    W (x, h) -> ProdImg k h -> ProdImg k h' -> forall l,
      W (x, upd k h' l h) /\ fst (sig e (x, upd k h' l h)) = fst (sig e (x, h)).
  Proof.
    intros W k e x h h' Hre HW H1 Hv Hh Hh' l.
    induction l as [| p l [IHv IHe]]; simpl; [split; [exact Hv | reflexivity] |].
    destruct (rg_eq_dec (tgt p) k) as [Ep | Np]; [| split; assumption].
    pose proof (upd_prod k h h' l Hh Hh') as Hu.
    assert (Hpv : Hp p (hget p h')) by (apply Hh'; exact Ep).
    split.
    - exact (HW p x _ _ Ep IHv Hu Hpv).
    - rewrite (H1 p x _ _ Ep IHv Hu Hpv). exact IHe.
  Qed.

  (* HEADLINE: per-edge C1 for every edge, plus M1, give C1cyc for the whole shared part. *)
  Theorem multi_edge_c1 : (forall p, C1edge p) -> M1 -> C1cyc Lc Hc Rg cvalid E reg sig ProdImg.
  Proof.
    intros H1 HM e x h h' Hv Hh Hh'. rewrite <- (upd_full (reg e) h h').
    refine (proj2 (chainW (cvalid (reg e)) (reg e) e x h h' eq_refl _ _ Hv Hh Hh' pall)).
    - intros p x' h0 v Ep Hv' Hp0 Hpv. rewrite <- Ep in Hv', Hp0 |- *. exact (HM p x' h0 v Hv' Hp0 Hpv).
    - intros p x' h0 v Ep Hv' Hp0 Hpv. apply (H1 p e x' h0 v (eq_sym Ep) Hv' Hp0 Hpv).
  Qed.

  (* Without validity: the per-edge check over all locals implies C1cyc. *)
  Theorem multi_edge_c1_free : (forall p, C1edge_all p) -> C1cyc Lc Hc Rg cvalid E reg sig ProdImg.
  Proof.
    intros H1 e x h h' _ Hh Hh'. rewrite <- (upd_full (reg e) h h').
    refine (proj2 (chainW (fun _ => True) (reg e) e x h h' eq_refl _ _ I Hh Hh' pall)).
    - intros; exact I.
    - intros p x' h0 v Ep _ Hp0 Hpv. apply (H1 p e x' h0 v (eq_sym Ep) Hp0 Hpv).
  Qed.
End Combine.

(* ======================================================================================= *)
(* Part 2. M1 cannot be dropped.                                                            *)
(* One registry (unit), two components (bool: true = first), both images {false, true}.     *)
(* Valid iff the shared part is (false, false). The event's local outcome is "both true".   *)
(* ======================================================================================= *)

Definition ntgt (_ : bool) : unit := tt.
Definition ncv (_ : unit) (xh : bool * (bool * bool)) : Prop := snd xh = (false, false).
Definition nreg0 (_ : unit) : unit := tt.
Definition nsig (_ : unit) (xh : bool * (bool * bool)) : bool * (bool * bool) :=
  (fst (snd xh) && snd (snd xh), snd xh).
Definition nHp (_ : bool) (_ : bool) : Prop := True.

Theorem m1_necessary :
  (forall p, C1edge bool (bool * bool) bool unit bool unit ncv nreg0 nsig ntgt rget rset nHp p) /\
  ~ M1 bool (bool * bool) bool unit bool ncv ntgt rget rset nHp /\
  ~ C1cyc bool (bool * bool) unit ncv unit nreg0 nsig
      (ProdImg (bool * bool) bool unit bool ntgt rget nHp).
Proof.
  split.
  { intros p e x [a b] v _ Hv _ _. unfold ncv in Hv. simpl in Hv. inversion Hv; subst.
    destruct p, v; reflexivity. }
  split.
  { intro H. pose proof (H true false (false, false) true eq_refl (fun _ _ => I) I) as Hd.
    discriminate Hd. }
  intro H. pose proof (H tt false (false, false) (true, true) eq_refl (fun _ _ => I)
                         (fun _ _ => I)) as Hd.
  discriminate Hd.
Qed.

(* ======================================================================================= *)
(* Part 3. Resolvers: one component written jointly by two sources.                         *)
(* ======================================================================================= *)

Section Resolver.
  Variables Lc Hc Rg E V1 V2 : Type.
  Variable cvalid : Rg -> Lc * Hc -> Prop.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.
  Variable r : V1 -> V2 -> Hc.
  Variable Im1 : Rg -> V1 -> Prop.
  Variable Im2 : Rg -> V2 -> Prop.

  (* The resolver's image: what the component can hold at a normal form. *)
  Definition Rimg (k : Rg) (h : Hc) : Prop := exists a b, Im1 k a /\ Im2 k b /\ h = r a b.

  (* Per-input checks THROUGH the resolver: vary one input, the other fixed, evaluate r. *)
  Definition C1in1 : Prop :=
    forall e x a a' b, Im1 (reg e) a -> Im1 (reg e) a' -> Im2 (reg e) b ->
      cvalid (reg e) (x, r a b) -> fst (sig e (x, r a' b)) = fst (sig e (x, r a b)).
  Definition C1in2 : Prop :=
    forall e x a b b', Im1 (reg e) a -> Im2 (reg e) b -> Im2 (reg e) b' ->
      cvalid (reg e) (x, r a b) -> fst (sig e (x, r a b')) = fst (sig e (x, r a b)).
  Definition Mr1 : Prop :=
    forall k x a a' b, Im1 k a -> Im1 k a' -> Im2 k b -> cvalid k (x, r a b) ->
      cvalid k (x, r a' b).

  Theorem resolver_joint_c1 : C1in1 -> C1in2 -> Mr1 -> C1cyc Lc Hc Rg cvalid E reg sig Rimg.
  Proof.
    intros H1 H2 HM e x h h' Hv [a [b [Ha [Hb ->]]]] [a' [b' [Ha' [Hb' ->]]]].
    rewrite (H2 e x a' b b' Ha' Hb Hb' (HM _ x a a' b Ha Ha' Hb Hv)).
    exact (H1 e x a a' b Ha Ha' Hb Hv).
  Qed.
End Resolver.

Definition rsig (_ : unit) (xh : bool * nat) : bool * nat := (Nat.eqb (snd xh) 2, snd xh).
Definition rcv (_ : unit) (_ : bool * nat) : Prop := True.
Definition rreg (_ : unit) : unit := tt.
Definition rIm01 (_ : unit) (v : nat) : Prop := v = 0 \/ v = 1.
Definition rIm0 (_ : unit) (v : nat) : Prop := v = 0.

Theorem resolver_edge_insufficient :
  C1cyc bool nat unit rcv unit rreg rsig rIm01 /\
  Rimg nat unit nat nat plus rIm01 rIm01 tt 2 /\ ~ rIm01 tt 2 /\
  ~ C1in1 bool nat unit unit nat nat rcv rreg rsig plus rIm01 rIm01 /\
  ~ C1cyc bool nat unit rcv unit rreg rsig (Rimg nat unit nat nat plus rIm01 rIm01).
Proof.
  split.
  { intros [] x h h' _ [-> | ->] [-> | ->]; reflexivity. }
  split; [exists 1, 1; split; [right; reflexivity | split; [right; reflexivity | reflexivity]] |].
  split; [intros [H | H]; discriminate H |].
  split.
  { intro H. pose proof (H tt false 0 1 1 (or_introl eq_refl) (or_intror eq_refl)
                           (or_intror eq_refl) I) as Hd. discriminate Hd. }
  intro H.
  pose proof (H tt false 0 2 I (ex_intro _ 0 (ex_intro _ 0 (conj (or_introl eq_refl)
               (conj (or_introl eq_refl) eq_refl))))
             (ex_intro _ 1 (ex_intro _ 1 (conj (or_intror eq_refl)
               (conj (or_intror eq_refl) eq_refl))))) as Hd.
  discriminate Hd.
Qed.

Theorem resolver_instance :
  C1in1 bool nat unit unit nat nat rcv rreg rsig plus rIm0 rIm01 /\
  C1in2 bool nat unit unit nat nat rcv rreg rsig plus rIm0 rIm01 /\
  Mr1 bool nat unit nat nat rcv plus rIm0 rIm01 /\
  C1cyc bool nat unit rcv unit rreg rsig (Rimg nat unit nat nat plus rIm0 rIm01) /\
  ~ ReadFootprint bool nat unit rsig.
Proof.
  assert (H1 : C1in1 bool nat unit unit nat nat rcv rreg rsig plus rIm0 rIm01).
  { intros [] x a a' b Ha Ha' _ _. unfold rIm0 in Ha, Ha'. subst. reflexivity. }
  assert (H2 : C1in2 bool nat unit unit nat nat rcv rreg rsig plus rIm0 rIm01).
  { intros [] x a b b' Ha [-> | ->] [-> | ->] _; unfold rIm0 in Ha; subst; reflexivity. }
  assert (HM : Mr1 bool nat unit nat nat rcv plus rIm0 rIm01) by (intros k x a a' b _ _ _ _; exact I).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact HM |].
  split; [exact (resolver_joint_c1 bool nat unit unit nat nat rcv rreg rsig plus rIm0 rIm01
                   H1 H2 HM) |].
  intro H. pose proof (H tt false 0 2) as Hd. discriminate Hd.
Qed.

(* ======================================================================================= *)
(* Part 4. cyc_check_gc for multi-edge targets.                                             *)
(* ======================================================================================= *)

Section MultiGC.
  Variables Loc Sh Lc Hc Rg : Type.
  Variable rg_eq_dec : forall a b : Rg, {a = b} + {a <> b}.
  Variable enc : Rg -> nat.
  Variable lget : Rg -> Loc -> Lc.
  Variable lset : Rg -> Lc -> Loc -> Loc.
  Hypothesis lget_lset_eq : forall j x l, lget j (lset j x l) = x.
  Hypothesis lget_lset_neq : forall j k x l, k <> j -> lget k (lset j x l) = lget k l.
  Hypothesis l_ext : forall l l', (forall k, lget k l = lget k l') -> l = l'.
  Variable sget : Rg -> Sh -> Hc.
  Variable sset : Rg -> Hc -> Sh -> Sh.
  Hypothesis sget_sset_eq : forall j x h, sget j (sset j x h) = x.
  Hypothesis sget_sset_neq : forall j k x h, k <> j -> sget k (sset j x h) = sget k h.
  Variable cvalid : Rg -> Lc * Hc -> Prop.
  Variable E : Type.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.
  Variable I : E -> E -> Prop.
  Hypothesis sig_valid : forall e x, cvalid (reg e) x -> cvalid (reg e) (sig e x).
  Variable rho1 : Loc * Sh -> Loc * Sh.
  Variable Lsh : Loc -> Sh.
  Hypothesis rho1_valid : forall s, FValid Loc Sh Lc Hc Rg lget sget cvalid s -> rho1 s = s.
  Hypothesis nf_valid : forall t, FValid Loc Sh Lc Hc Rg lget sget cvalid (Nr Loc Sh rho1 Lsh t).

  (* The edges. *)
  Variables V P : Type.
  Variable p_eq_dec : forall a b : P, {a = b} + {a <> b}.
  Variable tgt : P -> Rg.
  Variable hget : P -> Hc -> V.
  Variable hset : P -> V -> Hc -> Hc.
  Hypothesis hget_hset_eq : forall p v h, hget p (hset p v h) = v.
  Hypothesis hget_hset_neq : forall p q v h, tgt q = tgt p -> q <> p ->
    hget q (hset p v h) = hget q h.
  Hypothesis h_ext : forall k h h', (forall p, tgt p = k -> hget p h = hget p h') -> h = h'.
  Variable pall : list P.
  Hypothesis pall_cover : forall p, In p pall.
  Variable Hp : P -> V -> Prop.
  (* Every normal form has each component in its image set. *)
  Hypothesis Hp_nf : forall t p, Hp p (hget p (sget (tgt p) (snd (Nr Loc Sh rho1 Lsh t)))).

  Let PI := ProdImg Hc V Rg P tgt hget Hp.

  Lemma prod_nf : forall t k, PI k (sget k (snd (Nr Loc Sh rho1 Lsh t))).
  Proof. intros t k p Hk. subst k. apply Hp_nf. Qed.

  Theorem multi_edge_converges :
    (forall p, C1edge Lc Hc V Rg P E cvalid reg sig tgt hget hset Hp p) ->
    M1 Lc Hc V Rg P cvalid tgt hget hset Hp ->
    C2cyc Lc Hc Rg cvalid E reg sig I PI ->
    forall t, Converges (Loc * Sh) E (Nr Loc Sh rho1 Lsh)
                (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig) (nreg Rg enc E reg) I
                (Nr Loc Sh rho1 Lsh t).
  Proof.
    intros H1 HM H2.
    exact (cyc_check_converges Loc Sh Lc Hc Rg rg_eq_dec enc lget lset lget_lset_eq lget_lset_neq
             l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg sig I sig_valid rho1 Lsh
             rho1_valid nf_valid PI prod_nf
             (multi_edge_c1 Lc Hc V Rg P E rg_eq_dec p_eq_dec cvalid reg sig tgt hget hset
                hget_hset_eq hget_hset_neq h_ext pall pall_cover Hp H1 HM) H2).
  Qed.

  Theorem multi_edge_gc :
    (forall p, C1edge Lc Hc V Rg P E cvalid reg sig tgt hget hset Hp p) ->
    M1 Lc Hc V Rg P cvalid tgt hget hset Hp ->
    C2cyc Lc Hc Rg cvalid E reg sig I PI ->
    forall s0, (exists t, s0 = Nr Loc Sh rho1 Lsh t) ->
      GC (Loc * Sh) E (Nr Loc Sh rho1 Lsh) (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig)
         (nreg Rg enc E reg) I s0.
  Proof.
    intros H1 HM H2 s0 [t ->]. apply gc_necessary. apply multi_edge_converges; assumption.
  Qed.
End MultiGC.

(* ======================================================================================= *)
(* Part 5. Non-vacuity: a cycle A <-> B where both targets have two incoming edges.         *)
(* Registries A = true, B = false; locals and shared parts are pairs of booleans.          *)
(*   EA1 : B.b1 -> A.s1      EA2 : B.b2 -> A.s2                                              *)
(*   EB1 : A.a1 -> B.t1      EB2 : closed slot, B.t2 := false (image {false})               *)
(* Events: RaiseA1, RaiseA2 (declared independent), PingA (writes both of A's components),  *)
(* ReadB (b2 := b2 || t2: reads B's closed slot).                                           *)
(* ======================================================================================= *)

Inductive medge : Type := EA1 | EA2 | EB1 | EB2.

Definition medge_eq_dec : forall a b : medge, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition mtgt (p : medge) : bool := match p with EA1 | EA2 => true | _ => false end.
Definition mfst (p : medge) : bool := match p with EA1 | EB1 => true | _ => false end.
Definition mhget (p : medge) (h : P2) : bool := rget (mfst p) h.
Definition mhset (p : medge) (v : bool) (h : P2) : P2 := rset (mfst p) v h.
Definition mHp (p : medge) (v : bool) : Prop := match p with EB2 => v = false | _ => True end.
Definition mall : list medge := [EA1; EA2; EB1; EB2].

Lemma mhget_hset_eq : forall p v h, mhget p (mhset p v h) = v.
Proof. intros p v h. apply rget_rset_eq. Qed.
Lemma mhget_hset_neq : forall p q v h, mtgt q = mtgt p -> q <> p ->
  mhget q (mhset p v h) = mhget q h.
Proof.
  intros [] [] v [a b] Ht Hn; try discriminate Ht; try reflexivity; exfalso; apply Hn; reflexivity.
Qed.
Lemma mh_ext : forall k h h', (forall p, mtgt p = k -> mhget p h = mhget p h') -> h = h'.
Proof.
  intros [] [a b] [a' b'] H.
  - pose proof (H EA1 eq_refl) as H1. pose proof (H EA2 eq_refl) as H2. cbv in H1, H2. subst.
    reflexivity.
  - pose proof (H EB1 eq_refl) as H1. pose proof (H EB2 eq_refl) as H2. cbv in H1, H2. subst.
    reflexivity.
Qed.
Lemma mall_cover : forall p, In p mall.
Proof. intros []; simpl; auto. Qed.

Inductive mev : Type := RaiseA1 | RaiseA2 | PingA2 | ReadB.

Definition mreg (e : mev) : bool := match e with ReadB => false | _ => true end.

Definition msig (e : mev) (xh : P2 * P2) : P2 * P2 :=
  match e, xh with
  | RaiseA1, ((a1, a2), h) => ((true, a2), h)
  | RaiseA2, ((a1, a2), h) => ((a1, true), h)
  | PingA2, (x, _) => (x, (true, true))
  | ReadB, ((b1, b2), (t1, t2)) => ((b1, b2 || t2), (t1, t2))
  end.

Definition mI (a b : mev) : Prop :=
  (a = RaiseA1 /\ b = RaiseA2) \/ (a = RaiseA2 /\ b = RaiseA1).

Definition mcv (_ : bool) (_ : P2 * P2) : Prop := True.

(* The repair: A's components are B's locals, B's are (A's first local, false). *)
Definition mLsh (l : Q4) : Q4 := (snd l, (fst (fst l), false)).
Definition mN : Q4 * Q4 -> Q4 * Q4 := Nr Q4 Q4 (fun s => s) mLsh.
Definition mcev : mev -> Q4 * Q4 -> Q4 * Q4 := cev Q4 Q4 P2 P2 bool rget rset rget rset mev mreg msig.
Definition mnreg : mev -> nat := nreg bool renc mev mreg.

Theorem multi_edge_instance :
  (forall p, C1edge P2 P2 bool bool medge mev mcv mreg msig mtgt mhget mhset mHp p) /\
  M1 P2 P2 bool bool medge mcv mtgt mhget mhset mHp /\
  C2cyc P2 P2 bool mcv mev mreg msig mI (ProdImg P2 bool bool medge mtgt mhget mHp) /\
  (forall t p, mHp p (mhget p (rget (mtgt p) (snd (mN t))))) /\
  ~ ReadFootprint P2 P2 mev msig /\
  (forall t, GC (Q4 * Q4) mev mN mcev mnreg mI (mN t) /\
             Converges (Q4 * Q4) mev mN mcev mnreg mI (mN t)).
Proof.
  assert (H1 : forall p, C1edge P2 P2 bool bool medge mev mcv mreg msig mtgt mhget mhset mHp p).
  { intros p e [x1 x2] [h1 h2] v Hr _ Hpr Hv.
    destruct p, e; try discriminate Hr; try reflexivity.
    pose proof (Hpr EB2 eq_refl) as H2. cbv in Hv, H2. subst. reflexivity. }
  assert (HM : M1 P2 P2 bool bool medge mcv mtgt mhget mhset mHp) by (intros p x h v _ _ _; exact I).
  assert (H2 : C2cyc P2 P2 bool mcv mev mreg msig mI (ProdImg P2 bool bool medge mtgt mhget mHp)).
  { intros a b [x1 x2] h _ [[-> ->] | [-> ->]] _ _; reflexivity. }
  assert (Hnf : forall t p, mHp p (mhget p (rget (mtgt p) (snd (mN t))))).
  { intros t []; simpl; try exact I; reflexivity. }
  split; [exact H1 |]. split; [exact HM |]. split; [exact H2 |]. split; [exact Hnf |].
  split.
  { intro H. pose proof (H ReadB (false, false) (true, true) (true, false)) as Hd.
    discriminate Hd. }
  intro t. split.
  - exact (multi_edge_gc Q4 Q4 P2 P2 bool bool_dec renc rget rset (rget_rset_eq P2)
             (rget_rset_neq P2) (r_ext P2) rget rset (rget_rset_eq P2) (rget_rset_neq P2) mcv
             mev mreg msig mI (fun _ _ _ => I) (fun s => s) mLsh (fun _ _ => eq_refl)
             (fun _ _ => I) bool medge medge_eq_dec mtgt mhget mhset mhget_hset_eq
             mhget_hset_neq mh_ext mall mall_cover mHp Hnf H1 HM H2 (mN t)
             (ex_intro _ t eq_refl)).
  - exact (multi_edge_converges Q4 Q4 P2 P2 bool bool_dec renc rget rset (rget_rset_eq P2)
             (rget_rset_neq P2) (r_ext P2) rget rset (rget_rset_eq P2) (rget_rset_neq P2) mcv
             mev mreg msig mI (fun _ _ _ => I) (fun s => s) mLsh (fun _ _ => eq_refl)
             (fun _ _ => I) bool medge medge_eq_dec mtgt mhget mhset mhget_hset_eq
             mhget_hset_neq mh_ext mall mall_cover mHp Hnf H1 HM H2 t).
Qed.
