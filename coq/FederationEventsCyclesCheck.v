(* FederationEventsCyclesCheck.v: a cheap, per-event check that implies the global condition GC
   on MONOTONE CYCLIC federations, mechanized axiom-free (roadmap item 6).

   FederationEventsCycles.v proves that on a monotone cycle event interleavings converge exactly
   when GC holds (independent events commute after full re-normalization on reachable states),
   and that GC is global. This file answers which locally checkable condition implies it.

   Model. gsm's normalizeCyclic: phase 1 (each component's own normalizer), reset every shared
   (morphism-controlled) variable to bottom, sweep repairs to the least fixed point. So the normal
   form is (l, Lsh l) where l are the phase-1 locals: the shared part of a normal form is a
   function of the locals alone (in FederationEventsCycles.v, Lsh l = kleene l js K bot).
   Here the federation is split into registries (any type Rg with decidable equality):
     - Loc, Sh       : all locals, all shared values, with per-registry lenses lget / lset and
                       sget / sset (the usual get-set laws, plus extensionality of Loc).
     - comp k s      : registry k's component state (its locals, its shared values).
     - sig e         : the component step of event e on registry reg e (Machine.Apply: event
                       then component normalizer), preserving component validity.
     - cev e s       : FedMachine.Apply before normalization: registry reg e's component is
                       replaced by sig e of it (locals AND shared values written).
     - Nr t          : (fst (rho1 t), Lsh (fst (rho1 t))), the cyclic normal form.
   The step is gstep e = Nr o cev e, exactly as in FederationEventsCycles.v.

   The check. Let Hs k be any set of shared values for registry k that contains the shared values
   of k at every normal form (for gsm: the images of the morphisms into k over valid source
   states, which is what its per-edge C1 already enumerates; or the values the Kleene iteration
   visits). Then
     C1cyc : for every event e of registry j, every valid component state (x, h) of j with h in
             Hs j, and every h' in Hs j: the LOCAL part of sig e (x, h') equals that of
             sig e (x, h). The local outcome of an event does not depend on which image value the
             shared part holds. This is gsm's C1 (ow (sig e (ow b v')) v' = ow (sig e b) v' for
             every image v' and valid consistent b) read on a cycle: the final overwrite on both
             sides fixes the shared part, so the equation says exactly that the locals agree.
     C2cyc : for every declared-independent pair a, b on one registry j, every valid (x, h) with
             h in Hs j: the locals of sig a (locals of sig b (x, h), h) and of
             sig b (locals of sig a (x, h), h) agree. This is the local part of gsm's C2
             (ow (sig a (ow (sig b b0) z)) z = ow (sig b (ow (sig a b0) z)) z).
   Writes to shared variables are unrestricted: the reset to bottom erases them.

   Results.
     cyc_check_step : on a valid state, gstep e s = (L, Lsh L) with L the locals after the event;
        the event's shared writes are erased.
     cyc_check_gc / cyc_check_converges (HEADLINE): C1cyc + C2cyc imply GC s0 and convergence of
        all trace-equivalent sequences, for every s0 in the image of the normalizer.
     cyc_check_gc_lfp : the same for gsm's Kleene normalizer Ncyc_with of
        FederationEventsCycles.v, with Hs k = the image of the repair into k over valid states;
        the hypothesis "Hs contains the normal-form values" is discharged from cyc_N_lfp.
     footprint_c1 : the plain read-footprint condition (an event's local outcome ignores shared
        values altogether) implies C1cyc for every Hs. It is strictly stronger
        (c1_localcc_insufficient's events read a shared variable and pass C1cyc).
     lfp_commute_gc : the global variant "N o ev e o N = N o ev e" plus raw commutation of
        independent events implies GC. Sufficient, but it quantifies over all raw states and
        needs N, so it is not a per-edge check; the latch fails it.
     cyc_check_instance : non-vacuity. The two-registry cycle of FederationEventsCycles.v with
        raise / clear events on both registries and an event PingA that also writes A's shared
        flag (allowed): every hypothesis of cyc_check_gc_lfp is discharged.
     check_rejects_latch : cyc_counterexample's LatchA federation is this model (cev = xstep);
        for every Hs containing the normal-form shared values, C1cyc fails; and the global
        variant of lfp_commute_gc fails too.
     monotone_c2_insufficient : candidate "monotone events + C2 commutation" is false. The latch
        is a monotone map on the component lattice, C2cyc holds (no declared pairs), each
        registry's own CC holds, and GC fails.
     c1_localcc_insufficient : candidate "C1 + each registry's own CC" is false, so C2cyc cannot
        be dropped. A genuine monotone cycle (every hypothesis of cyc_N_lfp discharged) where
        C1cyc holds, the two declared-independent events of B commute on B's full state, C2cyc
        fails, and Audit;Swap and Swap;Audit diverge from a normal form. Both events read a
        shared variable, so the read-footprint condition fails while C1cyc holds.

   So candidate A of the roadmap holds: per-event C1 and per-pair C2, evaluated over valid
   component states whose shared part is an image (or any superset, such as the values the Kleene
   iteration visits), imply GC on the image of N. *)

From Coq Require Import List Arith Bool Lia.
Require Import NC.Trace NC.Federation NC.FederationEventsCycles.
Import ListNotations.

(* ======================================================================================= *)
(* Part 1. The global variant: N o ev e o N = N o ev e.                                     *)
(* ======================================================================================= *)

Section LfpCommute.
  Variable S E : Type.
  Variable Nf : S -> S.
  Variable ev : E -> S -> S.
  Variable reg : E -> nat.
  Variable I : E -> E -> Prop.

  Theorem lfp_commute_gc :
    (forall e t, Nf (ev e (Nf t)) = Nf (ev e t)) ->
    (forall a b s, Ifd E reg I a b -> ev a (ev b s) = ev b (ev a s)) ->
    forall t, GC S E Nf ev reg I (Nf t).
  Proof.
    intros Hn Hc t. apply gc_necessary. apply gc_image. intros t' a b Hab.
    unfold gstep. rewrite !Hn. rewrite (Hc a b _ Hab). reflexivity.
  Qed.
End LfpCommute.

(* ======================================================================================= *)
(* Part 2. The per-event check on a cyclic federation split into registries.                *)
(* ======================================================================================= *)

Section Check.
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
  Definition comp (k : Rg) (s : Loc * Sh) : Lc * Hc := (lget k (fst s), sget k (snd s)).
  Definition FValid (s : Loc * Sh) : Prop := forall k, cvalid k (comp k s).

  Variable E : Type.
  Variable reg : E -> Rg.
  Variable sig : E -> Lc * Hc -> Lc * Hc.
  Variable I : E -> E -> Prop.
  Hypothesis sig_valid : forall e x, cvalid (reg e) x -> cvalid (reg e) (sig e x).

  Definition cev (e : E) (s : Loc * Sh) : Loc * Sh :=
    (lset (reg e) (fst (sig e (comp (reg e) s))) (fst s),
     sset (reg e) (snd (sig e (comp (reg e) s))) (snd s)).

  Definition nreg (e : E) : nat := enc (reg e).

  Variable rho1 : Loc * Sh -> Loc * Sh.
  Variable Lsh : Loc -> Sh.
  Definition Nr (t : Loc * Sh) : Loc * Sh := (fst (rho1 t), Lsh (fst (rho1 t))).
  Hypothesis rho1_valid : forall s, FValid s -> rho1 s = s.
  Hypothesis nf_valid : forall t, FValid (Nr t).

  Variable Hs : Rg -> Hc -> Prop.
  Hypothesis Hs_nf : forall t k, Hs k (sget k (snd (Nr t))).

  (* C1 on a cycle: the local outcome of an event ignores which image the shared part holds. *)
  Definition C1cyc : Prop :=
    forall e x h h', cvalid (reg e) (x, h) -> Hs (reg e) h -> Hs (reg e) h' ->
      fst (sig e (x, h')) = fst (sig e (x, h)).

  (* C2 on a cycle: declared-independent events of one registry commute on locals, with the
     shared part held at the same image value between them. *)
  Definition C2cyc : Prop :=
    forall a b x h, reg a = reg b -> I a b -> cvalid (reg a) (x, h) -> Hs (reg a) h ->
      fst (sig a (fst (sig b (x, h)), h)) = fst (sig b (fst (sig a (x, h)), h)).

  (* The plain read footprint: the local outcome never depends on the shared part. *)
  Definition ReadFootprint : Prop :=
    forall e x h h', fst (sig e (x, h')) = fst (sig e (x, h)).

  Theorem footprint_c1 : ReadFootprint -> C1cyc.
  Proof. intros H e x h h' _ _ _. apply H. Qed.

  Let gs := gstep (Loc * Sh) E Nr cev.

  Lemma cev_valid : forall e s, FValid s -> FValid (cev e s).
  Proof.
    intros e s Hv k. unfold comp, cev; simpl.
    destruct (rg_eq_dec k (reg e)) as [-> | Ne].
    - rewrite lget_lset_eq, sget_sset_eq, <- surjective_pairing. apply sig_valid. apply Hv.
    - rewrite (lget_lset_neq _ _ _ _ Ne), (sget_sset_neq _ _ _ _ Ne). apply Hv.
  Qed.

  Theorem cyc_check_step : forall e s, FValid s ->
    gs e s = (lset (reg e) (fst (sig e (comp (reg e) s))) (fst s),
              Lsh (lset (reg e) (fst (sig e (comp (reg e) s))) (fst s))).
  Proof.
    intros e s Hv. unfold gs, gstep, Nr. rewrite (rho1_valid _ (cev_valid e s Hv)).
    reflexivity.
  Qed.

  Lemma lset_comm : forall j k x y l, j <> k -> lset j x (lset k y l) = lset k y (lset j x l).
  Proof.
    intros j k x y l Ne. apply l_ext. intro m.
    destruct (rg_eq_dec m j) as [-> | Nj].
    - rewrite lget_lset_eq, (lget_lset_neq _ _ _ _ Ne), lget_lset_eq. reflexivity.
    - rewrite (lget_lset_neq _ _ _ _ Nj).
      destruct (rg_eq_dec m k) as [-> | Nk].
      + rewrite !lget_lset_eq. reflexivity.
      + rewrite !(lget_lset_neq _ _ _ _ Nk), (lget_lset_neq _ _ _ _ Nj). reflexivity.
  Qed.

  Lemma lset_lset : forall j x y l, lset j x (lset j y l) = lset j x l.
  Proof.
    intros j x y l. apply l_ext. intro m.
    destruct (rg_eq_dec m j) as [-> | Nj].
    - rewrite !lget_lset_eq. reflexivity.
    - rewrite !(lget_lset_neq _ _ _ _ Nj). reflexivity.
  Qed.

  Lemma pair_lsh : forall X Y, X = Y -> (X, Lsh X) = (Y, Lsh Y).
  Proof. intros X Y ->. reflexivity. Qed.

  (* The core: on a normal form, independent events commute after re-normalization. *)
  Lemma commute_nf : C1cyc -> C2cyc -> forall t a b, Ifd E nreg I a b ->
    gs a (gs b (Nr t)) = gs b (gs a (Nr t)).
  Proof.
    intros H1 H2 t a b Hab.
    set (s := Nr t).
    assert (Hv : FValid s) by apply nf_valid.
    assert (Hsv : forall k, Hs k (sget k (snd s))) by (intro k; apply Hs_nf).
    (* after one step: a normal form again *)
    assert (Vb : FValid (gs b s)) by exact (nf_valid (cev b s)).
    assert (Va : FValid (gs a s)) by exact (nf_valid (cev a s)).
    assert (Sb : forall k, Hs k (sget k (snd (gs b s)))) by (intro k; exact (Hs_nf (cev b s) k)).
    assert (Sa : forall k, Hs k (sget k (snd (gs a s)))) by (intro k; exact (Hs_nf (cev a s) k)).
    assert (Eb : fst (gs b s) = lset (reg b) (fst (sig b (comp (reg b) s))) (fst s))
      by (rewrite (cyc_check_step b s Hv); reflexivity).
    assert (Ea : fst (gs a s) = lset (reg a) (fst (sig a (comp (reg a) s))) (fst s))
      by (rewrite (cyc_check_step a s Hv); reflexivity).
    rewrite (cyc_check_step a (gs b s) Vb), (cyc_check_step b (gs a s) Va).
    apply pair_lsh.
    (* C1 at the second step: the second event reads its shared part at the new normal form;
       move it back to the shared value at s (both are images, the base is valid). *)
    unfold comp at 1 2.
    rewrite <- (H1 a _ _ (sget (reg a) (snd s)) (Vb (reg a)) (Sb (reg a)) (Hsv (reg a))).
    rewrite <- (H1 b _ _ (sget (reg b) (snd s)) (Va (reg b)) (Sa (reg b)) (Hsv (reg b))).
    rewrite Ea, Eb.
    destruct (rg_eq_dec (reg a) (reg b)) as [Eq | Ne].
    - (* same registry: then C2 *)
      assert (Iab : I a b).
      { destruct Hab as [Hn | Hi]; [exfalso; apply Hn; unfold nreg; rewrite Eq; reflexivity
                                   | exact Hi]. }
      pose proof (H2 a b (lget (reg a) (fst s)) (sget (reg a) (snd s)) Eq Iab (Hv (reg a))
                    (Hsv (reg a))) as H2ab.
      rewrite <- Eq. rewrite !lget_lset_eq, !lset_lset. unfold comp. rewrite H2ab.
      reflexivity.
    - (* different registries: lenses commute *)
      assert (Ne' : reg b <> reg a) by (intro E'; apply Ne; symmetry; exact E').
      rewrite (lget_lset_neq _ _ _ _ Ne), (lget_lset_neq _ _ _ _ Ne').
      apply lset_comm. exact Ne.
  Qed.

  (* Headline: C1cyc and C2cyc imply GC at every state in the image of the normalizer. *)
  Theorem cyc_check_converges : C1cyc -> C2cyc ->
    forall t, Converges (Loc * Sh) E Nr cev nreg I (Nr t).
  Proof. intros H1 H2. apply gc_image. intros t a b Hab. apply commute_nf; assumption. Qed.

  Theorem cyc_check_gc : C1cyc -> C2cyc ->
    forall s0, (exists t, s0 = Nr t) -> GC (Loc * Sh) E Nr cev nreg I s0.
  Proof.
    intros H1 H2 s0 [t ->]. apply gc_necessary. apply cyc_check_converges; assumption.
  Qed.
End Check.

(* ======================================================================================= *)
(* Part 3. The same result for gsm's Kleene normalizer, with Hs = images of the repair.      *)
(* ======================================================================================= *)

Section CheckLfp.
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

  (* The lattice and the repair, as in FederationEventsCycles.v. *)
  Variable le : Sh -> Sh -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Variable bot : Sh.
  Hypothesis bot_least : forall x, le bot x.
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, le x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable F : Loc -> Sh -> Sh.
  Variable u : Loc -> nat -> Sh -> Sh.
  Hypothesis u_incr : forall l j x, sound Loc Sh le F l x -> le x (u l j x).
  Hypothesis u_sound : forall l j x, sound Loc Sh le F l x -> sound Loc Sh le F l (u l j x).
  Hypothesis u_mono : forall l j x y, le x y -> le (u l j x) (u l j y).
  Hypothesis u_fixed : forall l j x, F l x = x -> u l j x = x.
  Variable rho1 : Loc * Sh -> Loc * Sh.
  Variable K : nat.
  Hypothesis K_big : height < K.
  Variable js : list nat.
  Hypothesis Hcov : Cover Loc Sh F u js.

  Let V := FValid Loc Sh Lc Hc Rg lget sget cvalid.
  Hypothesis rho1_valid : forall s, V s -> rho1 s = s.
  Hypothesis lfp_valid : forall t m, is_lfp le (F (fst (rho1 t))) m -> V (fst (rho1 t), m).

  (* Hs k: the values the repair writes into registry k's shared part from valid states (per
     edge: the morphism images over valid source states). *)
  Variable Hs : Rg -> Hc -> Prop.
  Hypothesis Hs_img : forall l h k, V (l, h) -> Hs k (sget k (F l h)).

  Let Nc := Ncyc_with Loc Sh bot sh_eq_dec u rho1 K js.

  Theorem cyc_check_gc_lfp :
    C1cyc Lc Hc Rg cvalid E reg sig Hs ->
    C2cyc Lc Hc Rg cvalid E reg sig I Hs ->
    forall t, GC (Loc * Sh) E Nc (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig)
                 (nreg Rg enc E reg) I (Nc t) /\
              Converges (Loc * Sh) E Nc (cev Loc Sh Lc Hc Rg lget lset sget sset E reg sig)
                 (nreg Rg enc E reg) I (Nc t).
  Proof.
    intros H1 H2 t.
    pose proof (cyc_N_lfp Loc Sh le le_refl le_trans bot bot_least rank rank_strict height
                  rank_bound sh_eq_dec F u u_incr u_sound u_mono u_fixed rho1 K K_big js Hcov)
      as Hl.
    assert (Hnv : forall t, FValid Loc Sh Lc Hc Rg lget sget cvalid
                    (Nr Loc Sh rho1 (fun l => kleene Loc Sh sh_eq_dec u l js K bot) t)).
    { intro t'. destruct (Hl t') as [_ Hm]. exact (lfp_valid t' _ Hm). }
    assert (Hhs : forall t k, Hs k (sget k (snd
                    (Nr Loc Sh rho1 (fun l => kleene Loc Sh sh_eq_dec u l js K bot) t)))).
    { intros t' k. destruct (Hl t') as [_ [Hf _]].
      unfold fixed_point in Hf. change (snd (Nr Loc Sh rho1 _ t')) with (snd (Nc t')).
      unfold Nc. rewrite <- Hf. apply Hs_img. exact (lfp_valid t' _ (proj2 (Hl t'))). }
    split.
    - exact (cyc_check_gc Loc Sh Lc Hc Rg rg_eq_dec enc lget lset lget_lset_eq lget_lset_neq
               l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg sig I sig_valid rho1
               (fun l => kleene Loc Sh sh_eq_dec u l js K bot) rho1_valid Hnv Hs Hhs H1 H2
               (Nc t) (ex_intro _ t eq_refl)).
    - exact (cyc_check_converges Loc Sh Lc Hc Rg rg_eq_dec enc lget lset lget_lset_eq
               lget_lset_neq l_ext sget sset sget_sset_eq sget_sset_neq cvalid E reg sig I
               sig_valid rho1 (fun l => kleene Loc Sh sh_eq_dec u l js K bot) rho1_valid Hnv Hs
               Hhs H1 H2 t).
  Qed.
End CheckLfp.

(* ======================================================================================= *)
(* Part 4. Two registries (A = true, B = false), with pair lenses.                          *)
(* ======================================================================================= *)

Definition rget {A : Type} (r : bool) (p : A * A) : A := if r then fst p else snd p.
Definition rset {A : Type} (r : bool) (x : A) (p : A * A) : A * A :=
  if r then (x, snd p) else (fst p, x).
Definition renc (r : bool) : nat := if r then 0 else 1.

Lemma rget_rset_eq : forall (A : Type) j (x : A) l, rget j (rset j x l) = x.
Proof. intros A [] x l; reflexivity. Qed.
Lemma rget_rset_neq : forall (A : Type) j k (x : A) l, k <> j -> rget k (rset j x l) = rget k l.
Proof. intros A [] [] x l H; try reflexivity; exfalso; apply H; reflexivity. Qed.
Lemma r_ext : forall (A : Type) (l l' : A * A), (forall k, rget k l = rget k l') -> l = l'.
Proof.
  intros A [a b] [a' b'] H. pose proof (H true) as H1. pose proof (H false) as H2.
  simpl in H1, H2. subst. reflexivity.
Qed.

Ltac bfc := repeat match goal with
  | x : _ * _ |- _ => destruct x
  | b : bool |- _ => destruct b
  end.

(* ----- non-vacuity on the cycle of FederationEventsCycles.v ----- *)
(* Component of A: (alarm la, shared flag sa); of B: (lb, sb). PingA raises A's alarm and also
   writes A's shared flag, which the reset to bottom erases (allowed by C1cyc). RaiseA and PingA
   are declared independent on A. *)

Inductive iev : Type := RaiseA' | ClearA' | PingA | RaiseB'' | ClearB'.

Definition ireg (e : iev) : bool :=
  match e with RaiseA' | ClearA' | PingA => true | _ => false end.

Definition isig (e : iev) (x : bool * bool) : bool * bool :=
  match e with
  | RaiseA' | RaiseB'' => (true, snd x)
  | ClearA' | ClearB' => (false, snd x)
  | PingA => (true, true)
  end.

Definition iI (a b : iev) : Prop := (a = RaiseA' /\ b = PingA) \/ (a = PingA /\ b = RaiseA').

Definition cv1 (_ : bool) (_ : bool * bool) : Prop := True.
Definition Hall (_ : bool) (_ : bool) : Prop := True.

Definition icev : iev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset iev ireg isig.
Definition inreg : iev -> nat := nreg bool renc iev ireg.

Theorem cyc_check_instance :
  C1cyc bool bool bool cv1 iev ireg isig Hall /\
  C2cyc bool bool bool cv1 iev ireg isig iI Hall /\
  snd (isig PingA (false, false)) = true /\
  (forall t, GC (B2 * B2) iev cN icev inreg iI (cN t) /\
             Converges (B2 * B2) iev cN icev inreg iI (cN t)) /\
  grun (B2 * B2) iev cN icev [PingA; ClearA'] ((false, false), (false, false)) =
    ((false, false), (false, false)).
Proof.
  assert (H1 : C1cyc bool bool bool cv1 iev ireg isig Hall).
  { intros [] x h h' _ _ _; reflexivity. }
  assert (H2 : C2cyc bool bool bool cv1 iev ireg isig iI Hall).
  { intros a b x h _ [[-> ->] | [-> ->]] _ _; reflexivity. }
  split; [exact H1 |]. split; [exact H2 |]. split; [reflexivity |]. split; [| reflexivity].
  exact (cyc_check_gc_lfp B2 B2 bool bool bool bool_dec renc rget rset (rget_rset_eq bool)
           (rget_rset_neq bool) (r_ext bool) rget rset (rget_rset_eq bool) (rget_rset_neq bool)
           cv1 iev ireg isig iI (fun _ _ _ => I) cle cle_refl cle_trans cbot cbot_least crank
           crank_strict 2 crank_bound ceq_dec cF cu cu_incr cu_sound cu_mono cu_fixed crho1 3
           ltac:(lia) cts cts_cover (fun _ _ => eq_refl) (fun _ _ _ _ => I) Hall
           (fun _ _ _ _ => I) H1 H2).
Qed.

(* ----- the latch of cyc_counterexample is rejected ----- *)

Definition xregr (e : xev) : bool := match e with LatchA => true | RaiseB' => false end.

Definition xsig (e : xev) (x : bool * bool) : bool * bool :=
  match e with
  | LatchA => (fst x || snd x, snd x)
  | RaiseB' => (true, snd x)
  end.

Definition xcev : xev -> B2 * B2 -> B2 * B2 := cev B2 B2 bool bool bool rget rset rget rset xev xregr xsig.
Definition xnreg : xev -> nat := nreg bool renc xev xregr.

Theorem check_rejects_latch :
  (forall e s, xcev e s = xstep e s) /\
  (forall Hs, (forall t k, Hs k (rget k (snd (cN t)))) ->
     ~ C1cyc bool bool bool cv1 xev xregr xsig Hs) /\
  ~ (forall e t, cN (xcev e (cN t)) = cN (xcev e t)) /\
  ~ GC (B2 * B2) xev cN xcev xnreg xI xs0.
Proof.
  split; [intros [] [[la lb] [sa sb]]; reflexivity |].
  split.
  { intros Hs Hn H1.
    assert (Ht : Hs true true) by exact (Hn ((false, true), (false, false)) true).
    assert (Hf : Hs true false) by exact (Hn xs0 true).
    pose proof (H1 LatchA false false true I Hf Ht) as Hd. discriminate Hd. }
  split.
  { intro H. pose proof (H LatchA ((false, true), (false, false))) as Hd. discriminate Hd. }
  intro H. apply gc_sufficient in H.
  assert (Ht : tequiv (Ifd xev xnreg xI) [LatchA; RaiseB'] [RaiseB'; LatchA]).
  { apply (teq_swap _ [] LatchA RaiseB' []). left. discriminate. }
  pose proof (H _ _ Ht) as Hd. discriminate Hd.
Qed.

(* ----- candidate "monotone events + C2 commutation" is false ----- *)
Theorem monotone_c2_insufficient :
  (forall e x y, cle x y -> cle (xsig e x) (xsig e y)) /\
  (forall Hs, C2cyc bool bool bool cv1 xev xregr xsig xI Hs) /\
  (forall a b y, xI a b -> xsig a (xsig b y) = xsig b (xsig a y)) /\
  ~ GC (B2 * B2) xev cN xcev xnreg xI xs0.
Proof.
  split; [intros [] [a b] [c d] [Ha Hb]; destruct a, b, c, d; simpl in *;
           try discriminate; split; reflexivity |].
  split; [intros Hs a b x h _ [] |].
  split; [intros a b y [] |].
  apply (proj2 (proj2 (proj2 check_rejects_latch))).
Qed.

(* ======================================================================================= *)
(* Part 5. C2cyc cannot be dropped: C1cyc and each registry's own CC hold on a monotone     *)
(* cycle, and two interleavings still diverge.                                               *)
(* Component of A: locals (a, -), shared (cb, -). Component of B: locals (sb, au), shared   *)
(* (sa, ca). Repair: A.cb := au || ca (fed by B); B.sa := false (the image of a closed slot,  *)
(* as in FederationEvents.c2_counterexample); B.ca := a || cb (fed by A). A -> B -> A.      *)
(* Swap exchanges B's slots sb and sa; Audit records sa xor sb. They commute on B's full     *)
(* state, but between them the reset to bottom erases what Swap moved into the shared slot.  *)
(* ======================================================================================= *)

Definition P2 : Type := (bool * bool)%type.
Definition Q4 : Type := (P2 * P2)%type.

Definition leb4 (x y : Q4) : bool :=
  implb (fst (fst x)) (fst (fst y)) && implb (snd (fst x)) (snd (fst y)) &&
  implb (fst (snd x)) (fst (snd y)) && implb (snd (snd x)) (snd (snd y)).
Definition le4 (x y : Q4) : Prop := leb4 x y = true.
Definition bot4 : Q4 := ((false, false), (false, false)).
Definition b2n (b : bool) : nat := if b then 1 else 0.
Definition rank4 (x : Q4) : nat :=
  b2n (fst (fst x)) + b2n (snd (fst x)) + b2n (fst (snd x)) + b2n (snd (snd x)).
Definition q4_eq_dec : forall x y : Q4, {x = y} + {x <> y}.
Proof. decide equality; decide equality; apply bool_dec. Defined.

Definition F4 (l : Q4) (h : Q4) : Q4 :=
  ((snd (snd l) || snd (snd h), false), (false, fst (fst l) || fst (fst h))).

Definition u4 (l : Q4) (j : nat) (h : Q4) : Q4 :=
  match j with
  | 0 => (fst (F4 l h), snd h)
  | 1 => (fst h, snd (F4 l h))
  | _ => h
  end.

Definition cN4 : Q4 * Q4 -> Q4 * Q4 := Ncyc_with Q4 Q4 bot4 q4_eq_dec u4 (fun s => s) 5 [0; 1].

Ltac bf4 := repeat match goal with
  | x : Q4 |- _ => destruct x
  | x : P2 |- _ => destruct x
  | x : _ * _ |- _ => destruct x
  | b : bool |- _ => destruct b
  end.

Lemma le4_refl : forall x, le4 x x. Proof. intros; bf4; reflexivity. Qed.
Lemma le4_trans : forall x y z, le4 x y -> le4 y z -> le4 x z.
Proof. unfold le4. intros x y z; bf4; intros; cbv in *; congruence. Qed.
Lemma bot4_least : forall x, le4 bot4 x. Proof. intros; bf4; reflexivity. Qed.
Lemma rank4_strict : forall x y, le4 x y -> x <> y -> rank4 x < rank4 y.
Proof.
  unfold le4. intros x y; bf4; simpl; intros H N; try discriminate;
    try (exfalso; apply N; reflexivity); unfold rank4, b2n; simpl; lia.
Qed.
Lemma rank4_bound : forall x, rank4 x <= 4.
Proof. intros; bf4; unfold rank4, b2n; simpl; lia. Qed.
Lemma u4_incr : forall l j x, sound Q4 Q4 le4 F4 l x -> le4 x (u4 l j x).
Proof.
  unfold sound, le4. intros l [| [| j]] x; [bf4; intros; cbv in *; congruence | bf4; intros; cbv in *; congruence |].
  intros _. apply le4_refl.
Qed.
Lemma u4_sound : forall l j x, sound Q4 Q4 le4 F4 l x -> sound Q4 Q4 le4 F4 l (u4 l j x).
Proof.
  unfold sound, le4. intros l [| [| j]] x; [bf4; intros; cbv in *; congruence | bf4; intros; cbv in *; congruence |].
  simpl. auto.
Qed.
Lemma u4_mono : forall l j x y, le4 x y -> le4 (u4 l j x) (u4 l j y).
Proof.
  intros l [| [| j]] x y; [| | simpl; auto]; unfold le4;
    bf4; intros; cbv in *; congruence.
Qed.
Lemma u4_fixed : forall l j x, F4 l x = x -> u4 l j x = x.
Proof.
  intros l [| [| j]] x H; cbn [u4]; try reflexivity; rewrite H; destruct x; reflexivity.
Qed.
Lemma cover4 : Cover Q4 Q4 F4 u4 [0; 1].
Proof.
  intros l x H. pose proof (H 0 (or_introl eq_refl)) as H0.
  pose proof (H 1 (or_intror (or_introl eq_refl))) as H1. clear H. revert H0 H1.
  bf4; intros H0 H1; cbv in *; congruence.
Qed.

Lemma cN4_lfp : forall t, fst (cN4 t) = fst t /\ is_lfp le4 (F4 (fst t)) (snd (cN4 t)).
Proof.
  apply (cyc_N_lfp Q4 Q4 le4 le4_refl le4_trans bot4 bot4_least rank4 rank4_strict 4
           rank4_bound q4_eq_dec F4 u4 u4_incr u4_sound u4_mono u4_fixed (fun s => s) 5
           ltac:(lia) [0; 1] cover4).
Qed.

Inductive wev4 : Type := SwapB | AuditB.

Definition reg4 (_ : wev4) : bool := false.

Definition sig4 (e : wev4) (x : P2 * P2) : P2 * P2 :=
  match e, x with
  | SwapB, ((sb, au), (sa, ca)) => ((sa, au), (sb, ca))
  | AuditB, ((sb, au), (sa, ca)) => ((sb, xorb sa sb), (sa, ca))
  end.

Definition I4 (_ _ : wev4) : Prop := True.
Definition cv4 (_ : bool) (_ : P2 * P2) : Prop := True.
Definition Hs4 (r : bool) (h : P2) : Prop := if r then True else fst h = false.

Definition cev4 : wev4 -> Q4 * Q4 -> Q4 * Q4 := cev Q4 Q4 P2 P2 bool rget rset rget rset wev4 reg4 sig4.
Definition nreg4 : wev4 -> nat := nreg bool renc wev4 reg4.

Definition s4 : Q4 * Q4 := cN4 (((false, false), (true, false)), bot4).

Theorem c1_localcc_insufficient :
  (forall t, is_lfp le4 (F4 (fst t)) (snd (cN4 t))) /\
  (forall t k, Hs4 k (rget k (snd (cN4 t)))) /\
  C1cyc P2 P2 bool cv4 wev4 reg4 sig4 Hs4 /\
  (forall a b y, I4 a b -> sig4 a (sig4 b y) = sig4 b (sig4 a y)) /\
  ~ C2cyc P2 P2 bool cv4 wev4 reg4 sig4 I4 Hs4 /\
  ~ ReadFootprint P2 P2 wev4 sig4 /\
  tequiv (Ifd wev4 nreg4 I4) [AuditB; SwapB] [SwapB; AuditB] /\
  grun (Q4 * Q4) wev4 cN4 cev4 [AuditB; SwapB] s4 =
    (((false, false), (false, true)), ((true, false), (false, true))) /\
  grun (Q4 * Q4) wev4 cN4 cev4 [SwapB; AuditB] s4 =
    (((false, false), (false, false)), ((false, false), (false, false))) /\
  ~ GC (Q4 * Q4) wev4 cN4 cev4 nreg4 I4 s4 /\
  ~ Converges (Q4 * Q4) wev4 cN4 cev4 nreg4 I4 s4.
Proof.
  assert (Ht : tequiv (Ifd wev4 nreg4 I4) [AuditB; SwapB] [SwapB; AuditB]).
  { apply (teq_swap _ [] AuditB SwapB []). right. exact I. }
  assert (Hn : ~ Converges (Q4 * Q4) wev4 cN4 cev4 nreg4 I4 s4).
  { intro H. pose proof (H _ _ Ht) as Hd. discriminate Hd. }
  split; [intro t; apply (proj2 (cN4_lfp t)) |].
  split.
  { intros t [|]; [exact I |]. destruct (cN4_lfp t) as [_ [Hf _]].
    unfold fixed_point in Hf. unfold Hs4, rget. rewrite <- Hf. reflexivity. }
  split.
  { intros [] [sb au] [sa ca] [sa' ca'] _ Hh Hh'; simpl in Hh, Hh'; subst; reflexivity. }
  split.
  { intros [] [] [[sb au] [sa ca]] _; simpl; try reflexivity; rewrite xorb_comm; reflexivity. }
  split.
  { intro H. pose proof (H AuditB SwapB (true, false) (false, false) eq_refl I I eq_refl) as Hd.
    discriminate Hd. }
  split.
  { intro H. pose proof (H SwapB (false, false) (false, false) (true, false)) as Hd.
    discriminate Hd. }
  split; [exact Ht |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| exact Hn].
  intro H. apply Hn. apply gc_sufficient. exact H.
Qed.
