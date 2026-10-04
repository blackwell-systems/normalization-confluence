(* CategoricalBridge.v: the categorical paper's structural core (Proposition 1 and Theorem 1) on one
   concrete federation model, bridging the three pieces that Categorical.v and FederationOrder.v
   prove separately.

   Paper-label map (categorical_structure_of_federated_convergence.tex):
   - prop:one (Proposition 1), with the "each component is a normal form" conjunct of L_F:
       cat_prop_one              L_F = eq(g, h) on the product of the valid sets
       cat_prop_one_product      the product of valid sets is the equalizer of id and the product
                                 normalizer (a product of Lemma 0 equalizers)
       cat_prop_one_limit        L_F is a single equalizer of two maps into a finite product, hence
                                 a finite limit in Set
       cat_LF_split              L_F = (product of valid sets) /\ Categorical.Consistent
   - thm:one (Theorem 1), on the paper's L_F, for every acyclic federation:
       consistentList_iff_LF     Categorical.v's intrinsic ConsistentList (over a topological
                                 order) is exactly the paper's L_F, under local idempotence and the
                                 shared-component condition (below)
       rhoFold_run               Categorical.v's fold rhoFold over a topological order computes
                                 FederationOrder.run on that order (the two models agree)
       rhoFold_order_independent rhoFold inherits order_independent: any two topological orders of
       rhoFold_order_perm        the same registries give the same registry values
       cat_thm_one_sound, cat_thm_one_complete, cat_thm_one_idempotent, cat_thm_one_image,
       cat_thm_one_fixed, cat_thm_one_order_independent
                                 Theorem 1 as stated: im(rho_F) = Fix(rho_F) = L_F, rho_F
                                 idempotent, independent of the topological order
       cat_thm_one_fold_image    the same for the positional fold: im(rhoFold) = L_F
   - Correction to thm:one's hypothesis: cat_thm_one_m1_counterexample. With M1 read as validity
     preservation under overwrite (the paper's Background definition) plus local idempotence,
     Theorem 1 fails: rho_F does not land in L_F and is not idempotent. The hypothesis that makes it
     true is the paper's own parenthetical in Section 3.3, "the local normalizer fixes the
     overwritten shared component" (sh_fixed below).

   Model. Registries are indexed by nat, a federated state is s : nat -> V, registry i has a local
   normalizer rho i, a source list src i, and (when it is a target, src i <> []) a shared component
   read by get i and overwritten by ovr i, and a resolver res i reading the source values in order.
   Processing i (stepN) overwrites the shared component with the resolver value and then normalizes
   locally; a source-free registry is just normalized. A single value type V for all registries is
   no loss of generality (take V a sum type). Everything is axiom-free. *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Import ListNotations.
Require Import NC.Categorical NC.FederationOrder.

(* A split of a mapped list is the image of a split of the list. *)
Lemma map_split {A B : Type} (f : A -> B) :
  forall (o : list A) (p : list B) (x : B) (sfx : list B),
    map f o = p ++ x :: sfx ->
    exists pre i r, o = pre ++ i :: r /\ p = map f pre /\ x = f i /\ sfx = map f r.
Proof.
  induction o as [| a o IH]; intros p x sfx H.
  - simpl in H. destruct (app_cons_not_nil p sfx x H).
  - destruct p as [| y p]; simpl in H; injection H as H1 H2.
    + exists [], a, o. split; [reflexivity | split; [reflexivity | split; [symmetry; exact H1 | symmetry; exact H2]]].
    + destruct (IH p x sfx H2) as [pre [i [r [Ho [Hp [Hx Hs]]]]]].
      exists (a :: pre), i, r. subst. split; [reflexivity | split; [reflexivity | split; reflexivity]].
Qed.

(* In a duplicate-free topological order, a source of i that lies in the order lies before i. *)
Lemma prec_mid :
  forall pre i r k, NoDup (pre ++ i :: r) -> prec k i (pre ++ i :: r) -> In k pre.
Proof.
  induction pre as [| x pre IH]; intros i r k Hnd H; simpl in *.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hi _].
    destruct H as [[_ Hin] | H]; [contradiction | exact (Hi (prec_in_r _ _ _ H))].
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
    destruct H as [[E _] | H]; [left; exact E | right; exact (IH i r k Hnd H)].
Qed.

Section Bridge.
  Context {V Sh : Type}.
  Variable src : nat -> list nat.
  Variable rho : nat -> V -> V.         (* local normalizer of each registry *)
  Variable get : nat -> V -> Sh.        (* a target's shared component *)
  Variable ovr : nat -> V -> Sh -> V.   (* overwrite a target's shared component *)
  Variable res : nat -> list V -> Sh.   (* resolver: source values (in src order) -> shared value *)

  (* Processing registry i against the current federated state s. *)
  Definition stepN (i : nat) (s : nat -> V) (x : V) : V :=
    match src i with
    | [] => rho i x
    | _ => rho i (ovr i x (res i (map s (src i))))
    end.

  (* stepN reads the state only through the sources (FederationOrder's f_local, discharged). *)
  Lemma stepN_local :
    forall i s1 s2 x, (forall k, In k (src i) -> s1 k = s2 k) -> stepN i s1 x = stepN i s2 x.
  Proof.
    intros i s1 s2 x H. unfold stepN. rewrite (map_ext_in s1 s2 (src i) H). reflexivity.
  Qed.

  (* ----- Proposition 1: the consistent set L_F ----- *)

  Definition isTarget (i : nat) : bool := match src i with [] => false | _ => true end.

  Lemma isTarget_true : forall i, isTarget i = true <-> src i <> [].
  Proof.
    intro i. unfold isTarget. destruct (src i); split; intro H;
      [discriminate H | contradiction H; reflexivity | discriminate | reflexivity].
  Qed.

  Definition targetsOf (o : list nat) : list nat := filter isTarget o.
  Definition shOf (s : nat -> V) (B : nat) : Sh := get B (s B).
  Definition resOf (s : nat -> V) (B : nat) : Sh := res B (map s (src B)).

  (* The product of the valid sets Phi_{R_i} = im(rho_i), over the registries of o. *)
  Definition ProdPhi (o : list nat) (s : nat -> V) : Prop := forall i, In i o -> InImage (rho i) (s i).

  (* The paper's L_F: a tuple of component normal forms where every target's shared component
     equals its resolver value. *)
  Definition LF (o : list nat) (s : nat -> V) : Prop :=
    ProdPhi o s /\ forall B, In B o -> src B <> [] -> get B (s B) = res B (map s (src B)).

  (* g and h of the paper: the tuples of shared components and of resolver values over targets. *)
  Definition gF (o : list nat) (s : nat -> V) : list Sh := sharedOf (targetsOf o) shOf s.
  Definition hF (o : list nat) (s : nat -> V) : list Sh := resolvedOf (targetsOf o) resOf s.

  Lemma consistent_targets :
    forall o s, Consistent (targetsOf o) shOf resOf s <->
      (forall B, In B o -> src B <> [] -> get B (s B) = res B (map s (src B))).
  Proof.
    intros o s. unfold Consistent, targetsOf, shOf, resOf. split.
    - intros H B Hin Ht. apply H. apply filter_In. split; [exact Hin | apply isTarget_true; exact Ht].
    - intros H B Hin. apply filter_In in Hin. destruct Hin as [Hin Ht].
      apply H; [exact Hin | apply isTarget_true; exact Ht].
  Qed.

  (* L_F splits as the component normal-form conjunct and Categorical.v's Consistent. *)
  Theorem cat_LF_split :
    forall o s, LF o s <-> ProdPhi o s /\ Consistent (targetsOf o) shOf resOf s.
  Proof.
    intros o s. unfold LF. rewrite consistent_targets. reflexivity.
  Qed.

  (* Proposition 1 (prop:one), exactly: on the product of the valid sets, L_F = eq(g, h). *)
  Theorem cat_prop_one : forall o s, ProdPhi o s -> (LF o s <-> gF o s = hF o s).
  Proof.
    intros o s Hp. rewrite cat_LF_split. unfold gF, hF.
    rewrite <- (consistent_iff_equalizer (targetsOf o) shOf resOf s). unfold Equalizer.
    split; [intros [_ H]; exact H | intro H; split; [exact Hp | exact H]].
  Qed.

  Hypothesis idem : forall i x, rho i (rho i x) = rho i x.

  (* The product of the Lemma 0 equalizers: under local idempotence the product of valid sets is
     the equalizer of the identity and the product normalizer, factorwise Lemma 0's eq(id, rho_i). *)
  Theorem cat_prop_one_product :
    forall o s, ProdPhi o s <-> map s o = map (fun i => rho i (s i)) o.
  Proof.
    intros o s. split.
    - intro H. apply pointwise_to_map. intros i Hi.
      apply (proj1 (fixed_is_equalizer (rho i) (s i))).
      apply (image_iff_fixed (rho i) (idem i)). exact (H i Hi).
    - intros H i Hi. apply (image_iff_fixed (rho i) (idem i)).
      apply (proj2 (fixed_is_equalizer (rho i) (s i))).
      exact (map_to_pointwise s (fun i => rho i (s i)) o H i Hi).
  Qed.

  (* L_F is the equalizer of two maps into a finite product, hence a finite limit in Set. *)
  Theorem cat_prop_one_limit :
    forall o s, LF o s <-> (map s o, gF o s) = (map (fun i => rho i (s i)) o, hF o s).
  Proof.
    intros o s. split.
    - intro H. assert (Hp : ProdPhi o s) by exact (proj1 H).
      rewrite (proj1 (cat_prop_one_product o s) Hp), (proj1 (cat_prop_one o s Hp) H). reflexivity.
    - intro H. injection H as H1 H2.
      assert (Hp : ProdPhi o s) by exact (proj2 (cat_prop_one_product o s) H1).
      exact (proj2 (cat_prop_one o s Hp) H2).
  Qed.

  (* ----- Theorem 1: the local hypotheses ----- *)

  (* Lens law: writing back the current shared component changes nothing. *)
  Hypothesis putget : forall i v, ovr i v (get i v) = v.
  (* The local normalizer fixes the overwritten shared component (paper, Section 3.3: this is what
     M1/R2 must supply; validity preservation alone does not, see cat_thm_one_m1_counterexample). *)
  Hypothesis sh_fixed : forall i v r, src i <> [] -> get i (rho i (ovr i v r)) = r.

  Lemma ovr_rho_idem :
    forall i x r, src i <> [] -> rho i (ovr i (rho i (ovr i x r)) r) = rho i (ovr i x r).
  Proof.
    intros i x r Ht.
    transitivity (rho i (ovr i (rho i (ovr i x r)) (get i (rho i (ovr i x r))))).
    - rewrite (sh_fixed i x r Ht). reflexivity.
    - rewrite putget. apply idem.
  Qed.

  Lemma stepN_idem : forall i s x, stepN i s (stepN i s x) = stepN i s x.
  Proof.
    intros i s x. unfold stepN. destruct (src i) as [| k l] eqn:E.
    - apply idem.
    - rewrite <- E. apply ovr_rho_idem. rewrite E. discriminate.
  Qed.

  (* A registry is fixed by its step iff it is a normal form agreeing with its resolver. *)
  Lemma stepN_fixed_iff :
    forall i s x, stepN i s x = x <->
      InImage (rho i) x /\ (src i <> [] -> get i x = res i (map s (src i))).
  Proof.
    intros i s x. unfold stepN. destruct (src i) as [| k l] eqn:E.
    - split.
      + intro H. split; [exists x; exact H | intro C; contradiction C; reflexivity].
      + intros [Hi _]. exact (proj1 (image_iff_fixed (rho i) (idem i) x) Hi).
    - rewrite <- E. assert (Ht : src i <> []) by (rewrite E; discriminate).
      split.
      + intro H. split.
        * exists (ovr i x (res i (map s (src i)))). exact H.
        * intros _. rewrite <- H at 1. apply sh_fixed. exact Ht.
      + intros [Hi Hg]. rewrite <- (Hg Ht), putget.
        exact (proj1 (image_iff_fixed (rho i) (idem i) x) Hi).
  Qed.

  Lemma LF_pointwise : forall o t, (forall i, In i o -> stepN i t (t i) = t i) <-> LF o t.
  Proof.
    intros o t. unfold LF, ProdPhi. split.
    - intro H. split.
      + intros i Hi. exact (proj1 (proj1 (stepN_fixed_iff i t (t i)) (H i Hi))).
      + intros B HB. exact (proj2 (proj1 (stepN_fixed_iff B t (t B)) (H B HB))).
    - intros [H1 H2] i Hi. apply stepN_fixed_iff. split; [exact (H1 i Hi) | exact (H2 i Hi)].
  Qed.

  Lemma LF_ext : forall o t u, (forall k, t k = u k) -> LF o t -> LF o u.
  Proof.
    intros o t u E H. apply LF_pointwise. pose proof (proj2 (LF_pointwise o t) H) as H0. clear H. rename H0 into H.
    intros i Hi. transitivity (stepN i t (t i)).
    - rewrite <- E. apply stepN_local. intros k _. symmetry. apply E.
    - rewrite (H i Hi). apply E.
  Qed.

  (* ----- the positional fold of Categorical.v, instantiated on (registry, value) pairs ----- *)

  (* Read registry k from a finalized prefix of tagged values, falling back to s0 (registries not
     in the order are external inputs). *)
  Definition look (p : list (nat * V)) (s0 : nat -> V) (k : nat) : V :=
    match find (fun e => Nat.eqb (fst e) k) p with Some e => snd e | None => s0 k end.

  Definition stepT (s0 : nat -> V) (p : list (nat * V)) (e : nat * V) : nat * V :=
    (fst e, stepN (fst e) (look p s0) (snd e)).

  Definition tag (o : list nat) (t : nat -> V) : list (nat * V) := map (fun i => (i, t i)) o.

  Lemma stepT_idem : forall s0 p x, stepT s0 p (stepT s0 p x) = stepT s0 p x.
  Proof. intros s0 p [i x]. unfold stepT. simpl. rewrite stepN_idem. reflexivity. Qed.

  Lemma look_tag_in : forall t s0 k pre, In k pre -> look (tag pre t) s0 k = t k.
  Proof.
    intros t s0 k pre. induction pre as [| x pre IH]; intro Hk; [destruct Hk |].
    unfold look in *. simpl. destruct (Nat.eqb_spec x k) as [-> | Hne]; [reflexivity |].
    apply IH. destruct Hk as [-> | Hk]; [contradiction Hne; reflexivity | exact Hk].
  Qed.

  Lemma look_tag_out : forall t s0 k pre, ~ In k pre -> look (tag pre t) s0 k = s0 k.
  Proof.
    intros t s0 k pre. induction pre as [| x pre IH]; intro Hk; [reflexivity |].
    unfold look in *. simpl. destruct (Nat.eqb_spec x k) as [-> | Hne].
    - contradiction Hk. left. reflexivity.
    - apply IH. intro H. apply Hk. right. exact H.
  Qed.

  (* Within a topological order, a registry's prefix reads its sources correctly. *)
  Lemma look_agree :
    forall o pre i r t s0,
      topo src o -> o = pre ++ i :: r -> (forall k, ~ In k o -> t k = s0 k) ->
      forall k, In k (src i) -> look (tag pre t) s0 k = t k.
  Proof.
    intros o pre i r t s0 [Hnd Ht] Ho Hext k Hk.
    destruct (in_dec Nat.eq_dec k o) as [Hko | Hko].
    - apply look_tag_in. subst o. apply (prec_mid pre i r k Hnd).
      apply Ht; [apply in_or_app; right; left; reflexivity | exact Hk | exact Hko].
    - rewrite look_tag_out; [symmetry; exact (Hext k Hko) |].
      intro Hp. apply Hko. subst o. apply in_or_app. left. exact Hp.
  Qed.

  Lemma run_out : forall o t k, ~ In k o -> run stepN o t k = t k.
  Proof.
    induction o as [| a o IH]; intros t k Hk; [reflexivity |].
    rewrite run_cons, IH by (intro H; apply Hk; right; exact H).
    apply step_other. intro E. apply Hk. left. symmetry. exact E.
  Qed.

  Lemma fold_run_gen :
    forall s0 o rest pre t,
      topo src o -> o = pre ++ rest -> (forall k, ~ In k o -> t k = s0 k) ->
      rhoF_from (stepT s0) (tag pre t) (tag rest t) = tag o (run stepN rest t).
  Proof.
    intros s0 o rest. induction rest as [| i r IH]; intros pre t Ho E Hext.
    - simpl. rewrite E, app_nil_r. reflexivity.
    - assert (Hnd : NoDup (pre ++ i :: r)) by (rewrite <- E; exact (proj1 Ho)).
      assert (Hipre : ~ In i pre).
      { intro H. apply (NoDup_remove_2 pre r i Hnd). apply in_or_app. left. exact H. }
      assert (Hir : ~ In i r).
      { intro H. apply (NoDup_remove_2 pre r i Hnd). apply in_or_app. right. exact H. }
      set (t' := step stepN t i).
      assert (Hstep : stepT s0 (tag pre t) (i, t i) = (i, t' i)).
      { unfold stepT, t'. simpl. rewrite step_self. f_equal.
        apply stepN_local. exact (look_agree o pre i r t s0 Ho E Hext). }
      assert (Hpre : tag pre t ++ [(i, t' i)] = tag (pre ++ [i]) t').
      { unfold tag. rewrite map_app. simpl. f_equal. apply map_ext_in. intros k Hk.
        unfold t'. rewrite step_other; [reflexivity |]. intro Ek. subst k. contradiction. }
      assert (Hr : tag r t = tag r t').
      { unfold tag. apply map_ext_in. intros k Hk.
        unfold t'. rewrite step_other; [reflexivity |]. intro Ek. subst k. contradiction. }
      change (tag (i :: r) t) with ((i, t i) :: tag r t). simpl rhoF_from.
      rewrite Hstep, Hpre, Hr, run_cons. fold t'.
      apply IH; [exact Ho | rewrite E, <- app_assoc; reflexivity |].
      intros k Hk. unfold t'. rewrite step_other; [exact (Hext k Hk) |].
      intro Ek. subst k. apply Hk. rewrite E. apply in_or_app. right. left. reflexivity.
  Qed.

  (* Bridge: Categorical.v's fold over a topological order computes FederationOrder.run on it. *)
  Theorem rhoFold_run :
    forall o s s0, topo src o -> (forall k, ~ In k o -> s k = s0 k) ->
      rhoFold (stepT s0) (tag o s) = tag o (run stepN o s).
  Proof. intros o s s0 Ho Hext. exact (fold_run_gen s0 o o [] s Ho eq_refl Hext). Qed.

  (* The fold's result read back as a federated state is run o s. *)
  Lemma look_rhoFold :
    forall o s k, topo src o -> look (rhoFold (stepT s) (tag o s)) s k = run stepN o s k.
  Proof.
    intros o s k Ho. rewrite (rhoFold_run o s s Ho (fun _ _ => eq_refl)).
    destruct (in_dec Nat.eq_dec k o) as [Hk | Hk].
    - apply look_tag_in. exact Hk.
    - rewrite look_tag_out by exact Hk. symmetry. apply run_out. exact Hk.
  Qed.

  (* rhoFold inherits order_independent: two topological orders of the same registries give the
     same federated state. *)
  Theorem rhoFold_order_independent :
    forall o1 o2 s, topo src o1 -> topo src o2 -> Permutation o1 o2 ->
      forall k, look (rhoFold (stepT s) (tag o1 s)) s k = look (rhoFold (stepT s) (tag o2 s)) s k.
  Proof.
    intros o1 o2 s H1 H2 HP k. rewrite !look_rhoFold by assumption.
    exact (order_independent src stepN stepN_local o1 o2 s H1 H2 HP k).
  Qed.

  (* Positional form: the fold on o2 is the fold on o1 rearranged into o2's order. *)
  Theorem rhoFold_order_perm :
    forall o1 o2 s, topo src o1 -> topo src o2 -> Permutation o1 o2 ->
      rhoFold (stepT s) (tag o2 s) = tag o2 (run stepN o1 s) /\
      Permutation (rhoFold (stepT s) (tag o1 s)) (rhoFold (stepT s) (tag o2 s)).
  Proof.
    intros o1 o2 s H1 H2 HP.
    assert (E : rhoFold (stepT s) (tag o2 s) = tag o2 (run stepN o1 s)).
    { rewrite (rhoFold_run o2 s s H2 (fun _ _ => eq_refl)). unfold tag. apply map_ext_in.
      intros k _. f_equal. symmetry. exact (order_independent src stepN stepN_local o1 o2 s H1 H2 HP k). }
    split; [exact E |]. rewrite E, (rhoFold_run o1 s s H1 (fun _ _ => eq_refl)).
    unfold tag. apply Permutation_map. exact HP.
  Qed.

  (* C3 bridge: Categorical.v's intrinsic ConsistentList, over a topological order, is exactly the
     paper's L_F. *)
  Theorem consistentList_iff_LF :
    forall o t s0, topo src o -> (forall k, ~ In k o -> t k = s0 k) ->
      (ConsistentList (stepT s0) (tag o t) <-> LF o t).
  Proof.
    intros o t s0 Ho Hext. rewrite <- LF_pointwise. split.
    - intros H i Hi. apply in_split in Hi. destruct Hi as [pre [r Eo]].
      assert (Hs := H (tag pre t) (i, t i) (tag r t)).
      assert (Ht : tag o t = tag pre t ++ (i, t i) :: tag r t) by (rewrite Eo; unfold tag; rewrite map_app; reflexivity).
      specialize (Hs Ht). unfold stepT in Hs. simpl in Hs. injection Hs as Hs.
      rewrite <- Hs at 2. symmetry. apply stepN_local. exact (look_agree o pre i r t s0 Ho Eo Hext).
    - intros H p x sfx Hsp. apply map_split in Hsp.
      destruct Hsp as [pre [i [r [Eo [Hp [Hx _]]]]]]. subst p x. unfold stepT. simpl. f_equal.
      transitivity (stepN i t (t i)).
      + apply stepN_local. exact (look_agree o pre i r t s0 Ho Eo Hext).
      + apply H. rewrite Eo. apply in_or_app. right. left. reflexivity.
  Qed.

  (* ----- Theorem 1 (thm:one) on the paper's L_F, inherited through the bridge ----- *)

  (* Lemma A: rho_F lands in L_F (from Categorical.rhoFold_sound). *)
  Theorem cat_thm_one_sound : forall o s, topo src o -> LF o (run stepN o s).
  Proof.
    intros o s Ho.
    apply (proj1 (consistentList_iff_LF o (run stepN o s) s Ho (fun k Hk => run_out o s k Hk))).
    rewrite <- (rhoFold_run o s s Ho (fun _ _ => eq_refl)).
    apply rhoFold_sound. apply stepT_idem.
  Qed.

  (* Lemma B: rho_F fixes L_F (from Categorical.rhoFold_complete). *)
  Theorem cat_thm_one_complete : forall o s, topo src o -> LF o s -> forall k, run stepN o s k = s k.
  Proof.
    intros o s Ho H k.
    assert (Hc : ConsistentList (stepT s) (tag o s))
      by exact (proj2 (consistentList_iff_LF o s s Ho (fun _ _ => eq_refl)) H).
    pose proof (rhoFold_complete (stepT s) (tag o s) Hc) as E.
    rewrite (rhoFold_run o s s Ho (fun _ _ => eq_refl)) in E.
    destruct (in_dec Nat.eq_dec k o) as [Hk | Hk].
    - pose proof (map_to_pointwise (fun i => (i, run stepN o s i)) (fun i => (i, s i)) o E k Hk) as P.
      injection P as P. exact P.
    - apply run_out. exact Hk.
  Qed.

  Theorem cat_thm_one_idempotent :
    forall o s, topo src o -> forall k, run stepN o (run stepN o s) k = run stepN o s k.
  Proof. intros o s Ho. apply cat_thm_one_complete; [exact Ho | apply cat_thm_one_sound; exact Ho]. Qed.

  (* im(rho_F) = L_F (states compared pointwise). *)
  Theorem cat_thm_one_image :
    forall o t, topo src o -> ((exists y, forall k, run stepN o y k = t k) <-> LF o t).
  Proof.
    intros o t Ho. split.
    - intros [y Hy]. exact (LF_ext o _ t Hy (cat_thm_one_sound o y Ho)).
    - intro H. exists t. apply cat_thm_one_complete; assumption.
  Qed.

  (* Fix(rho_F) = L_F. *)
  Theorem cat_thm_one_fixed :
    forall o t, topo src o -> ((forall k, run stepN o t k = t k) <-> LF o t).
  Proof.
    intros o t Ho. split.
    - intro H. exact (LF_ext o _ t H (cat_thm_one_sound o t Ho)).
    - apply cat_thm_one_complete. exact Ho.
  Qed.

  (* rho_F is independent of the chosen topological order. *)
  Theorem cat_thm_one_order_independent :
    forall o1 o2 s, topo src o1 -> topo src o2 -> Permutation o1 o2 ->
      forall k, run stepN o1 s k = run stepN o2 s k.
  Proof. exact (order_independent src stepN stepN_local). Qed.

  (* The positional fold of Categorical.v: im(rhoFold) = L_F, on tagged states. *)
  Theorem cat_thm_one_fold_image :
    forall o t s0, topo src o -> (forall k, ~ In k o -> t k = s0 k) ->
      ((exists y, rhoFold (stepT s0) y = tag o t) <-> LF o t).
  Proof.
    intros o t s0 Ho Hext. rewrite <- (consistentList_iff_LF o t s0 Ho Hext).
    apply rhoFold_image_iff_consistent. apply stepT_idem.
  Qed.
End Bridge.

(* ============================================================
   Non-vacuity: FederationOrder.v's three-registry shape (registry 2 reads 0 and 1). Values are
   pairs (shared, local); sources clamp both coordinates at 3, the target clamps only its local
   coordinate, and its resolver sums the sources' shared components. Every hypothesis (idem, putget,
   sh_fixed) is discharged, both topological orders apply, and L_F is a genuine constraint.
   ============================================================ *)

Definition nv_rho (i : nat) (v : nat * nat) : nat * nat :=
  match i with
  | 2 => (fst v, clamp3 (snd v))
  | _ => (clamp3 (fst v), clamp3 (snd v))
  end.
Definition nv_get (_ : nat) (v : nat * nat) : nat := fst v.
Definition nv_ovr (_ : nat) (v : nat * nat) (r : nat) : nat * nat := (r, snd v).
Definition nv_res (_ : nat) (l : list (nat * nat)) : nat := fold_right (fun v a => fst v + a) 0 l.

Lemma nv_idem : forall i x, nv_rho i (nv_rho i x) = nv_rho i x.
Proof.
  intros i [a b]. destruct i as [| [| [| i]]]; unfold nv_rho; simpl; rewrite ?clamp3_idem; reflexivity.
Qed.

Lemma nv_putget : forall i v, nv_ovr i v (nv_get i v) = v.
Proof. intros i [a b]. reflexivity. Qed.

Lemma nv_sh_fixed :
  forall i v r, ex_src i <> [] -> nv_get i (nv_rho i (nv_ovr i v r)) = r.
Proof.
  intros i [a b] r H. destruct i as [| [| [| i]]]; simpl in H;
    try (contradiction H; reflexivity). reflexivity.
Qed.

Definition nv_s0 (_ : nat) : nat * nat := (5, 9).

Definition nv_stepN := stepN ex_src nv_rho nv_ovr nv_res.

Example nv_run : run nv_stepN [0; 1; 2] nv_s0 2 = (6, 3).
Proof. reflexivity. Qed.

Lemma nv_sound : LF ex_src nv_rho nv_get nv_res [0; 1; 2] (run nv_stepN [0; 1; 2] nv_s0).
Proof. exact (cat_thm_one_sound ex_src nv_rho nv_get nv_ovr nv_res nv_idem nv_putget nv_sh_fixed _ _ ex_topo_012). Qed.

Lemma nv_s0_not_LF : ~ LF ex_src nv_rho nv_get nv_res [0; 1; 2] nv_s0.
Proof.
  intros [H _]. destruct (H 0 (or_introl eq_refl)) as [y Hy].
  unfold nv_rho, nv_s0 in Hy. destruct y as [a b]. simpl in Hy. injection Hy as Ha _.
  unfold clamp3 in Ha. pose proof (Nat.le_min_r a 3). lia.
Qed.

Example nv_orders_agree :
  forall k, run nv_stepN [0; 1; 2] nv_s0 k = run nv_stepN [1; 0; 2] nv_s0 k.
Proof.
  exact (cat_thm_one_order_independent ex_src nv_rho nv_ovr nv_res
           [0; 1; 2] [1; 0; 2] nv_s0 ex_topo_012 ex_topo_102 (perm_swap 1 0 [2])).
Qed.

Lemma nv_prop_one :
  ProdPhi nv_rho [0; 1; 2] (run nv_stepN [0; 1; 2] nv_s0) /\
  gF ex_src nv_get [0; 1; 2] (run nv_stepN [0; 1; 2] nv_s0) =
  hF ex_src nv_res [0; 1; 2] (run nv_stepN [0; 1; 2] nv_s0).
Proof.
  destruct nv_sound as [Hp Hc]. split; [exact Hp |].
  exact (proj1 (cat_prop_one ex_src nv_rho nv_get nv_res _ _ Hp) (conj Hp Hc)).
Qed.

(* ============================================================
   Counterexample to Theorem 1 with M1 read as validity preservation under overwrite (the
   Background's definition) plus local idempotence and the lens law. Registry 1 reads registry 0;
   values are (shared, local) booleans; registry 1's valid states are those with local = true, and
   its normalizer repairs local = false by setting local := true AND flipping the shared bit. M1
   holds (overwriting the shared bit of a valid state keeps it valid), rho_1 is idempotent, but
   rho_F does not land in L_F and is not idempotent: compensation undid the morphism's write.
   ============================================================ *)

Definition cx_src (i : nat) : list nat := match i with 1 => [0] | _ => [] end.
Definition cx_rho (i : nat) (v : bool * bool) : bool * bool :=
  match i with 1 => if snd v then v else (negb (fst v), true) | _ => v end.
Definition cx_get (_ : nat) (v : bool * bool) : bool := fst v.
Definition cx_ovr (_ : nat) (v : bool * bool) (r : bool) : bool * bool := (r, snd v).
Definition cx_res (_ : nat) (_ : list (bool * bool)) : bool := true.
Definition cx_stepN := stepN cx_src cx_rho cx_ovr cx_res.
Definition cx_s (_ : nat) : bool * bool := (false, false).

Lemma cx_topo : topo cx_src [0; 1].
Proof.
  split.
  - repeat constructor; simpl; intuition congruence.
  - intros i k Hi Hk Hko. simpl in Hi.
    destruct Hi as [<- | [<- | []]]; simpl in Hk; [contradiction |].
    destruct Hk as [<- | []]. simpl. intuition.
Qed.

Theorem cat_thm_one_m1_counterexample :
  (* M1 as validity preservation: overwriting a valid state's shared component keeps it valid *)
  (forall i v r, cx_rho i v = v -> cx_rho i (cx_ovr i v r) = cx_ovr i v r) /\
  (forall i x, cx_rho i (cx_rho i x) = cx_rho i x) /\
  (forall i v, cx_ovr i v (cx_get i v) = v) /\
  topo cx_src [0; 1] /\
  ~ LF cx_src cx_rho cx_get cx_res [0; 1] (run cx_stepN [0; 1] cx_s) /\
  run cx_stepN [0; 1] (run cx_stepN [0; 1] cx_s) 1 <> run cx_stepN [0; 1] cx_s 1.
Proof.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i [a b] r H. destruct i as [| [| i]]; simpl in *; try reflexivity.
    destruct b; [reflexivity |]. injection H as _ H. discriminate H.
  - intros i [a b]. destruct i as [| [| i]]; simpl; try reflexivity.
    destruct b; reflexivity.
  - intros i [a b]. reflexivity.
  - exact cx_topo.
  - intros [_ H]. specialize (H 1 (or_intror (or_introl eq_refl))). simpl in H.
    discriminate (H ltac:(discriminate)).
  - simpl. discriminate.
Qed.
