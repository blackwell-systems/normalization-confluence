(* Collapse.v: compositional collapse (federation paper, Section "Compositionality: Sub-Federations
   as Effective Registries"; categorical paper, Section "Compositionality for Free"), mechanized
   axiom-free, in corrected form where the paper's statement is false.

   Paper label -> Coq.
   Federation paper (normalization_confluence_in_federated_registry_networks.tex):
     def:subfed (convexity)        Convex, path (the federation's data-flow graph)
     def:effreg                    rhoJ (the sub-federated normalizer rho_Fed^J), InvJ, ConsJ
     thm:collapse, proof of (c), "a topological order visits J as a contiguous block"
                                   collapse_every_order_refuted     counterexample ("every order")
                                   collapse_block_order             corrected ("some order")
     thm:collapse (c), "N' acyclic if N is"
                                   collapse_contract_topo, collapse_contract_acyclic   exact
                                   collapse_convexity_needed        convexity cannot be dropped
                                   topoF_acyclic                    a topological order closed
                                                                    under sources has no cycle
     thm:collapse (a), WFC         collapse_a_wfc                   exact (one round of rho_J)
     thm:collapse (a), CC          collapse_a_refuted               counterexample (paper hypotheses,
                                                                    R_J's CC1 fails)
                                   collapse_a_guarded, collapse_a_guarded_perm   corrected (C1 + C2)
                                   collapse_a_guarded_exact         exact condition
     thm:collapse (b)              collapse_b_import_iff, collapse_b_export_iff   exact, M1 posed
                                                                    against the product of member
                                                                    validities
                                   collapse_b_import_refuted, collapse_b_export_refuted
                                                                    counterexamples, M1 posed against
                                                                    R_J's federal validity
                                   collapse_b_import_corrected, collapse_b_export_corrected
     thm:collapse (c), normal forms collapse_nf_agree               exact
                                   collapse_nf_factor               rho_Fed = before J, then rho_J,
                                                                    then propagate
     thm:collapse (c), convergence collapse_c_runs_agree, collapse_c_traceconv,
                                   collapse_c_exact                 exact (FedMachine runs)
                                   collapse_c_guarded_iff, collapse_c_guarded_exact,
                                   collapse_c_guarded_c1_c2         guarded GRS (C1 + C2)
                                   collapse_c_unguarded_iff         unguarded GRS
     cor:modular                   collapse_modular_c1, collapse_modular_c2,
                                   collapse_modular_converges       verify J once, then the rest
                                   collapse_hierarchical, collapse_regroup   nesting
                                   collapse_product_convex          the product case (E_J empty)
   Categorical paper (categorical_structure_of_federated_convergence.tex):
     thm:two, "a verified sub-federation collapses to an effective registry"
                                   collapse_nf_agree, collapse_a_wfc, collapse_c_guarded_iff
     Section 4, port refinement    port_interior_certificate, port_interior_invariant,
                                   port_c1_transfer, port_c2_transfer, port_sealed_write_refuted
   The contracted network N': srcC, orderC (graph); blocksC, Ncol, grhoC, gvalidC (normalizer, GRS).
   Non-vacuity: chain_common, chain_c1, chain_c2, chain_convex, chain_collapse_instance; the
   counterexamples bi_common, collapse_b_import_refuted, port_sealed_write_refuted satisfy Common.

   Model. The FederationEvents.v model (registries indexed by nat, federated states nat -> V, phase 1
   rho on every component, phase 2 the repairs f along a topological order o), as used by
   FederationGRS.v (WP5). The sub-federation is given by a boolean membership predicate inJ. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Newman NC.Governance NC.Trace NC.FederationEvents NC.FederationEventsConverse
  NC.GovernanceConverse NC.FederationGRS.
Import ListNotations.

(* ========================================================================================= *)
(* PART 1. The graph: convexity, a block topological order, and the contracted network.       *)
(* ========================================================================================= *)

Definition inb (k : nat) (l : list nat) : bool := existsb (Nat.eqb k) l.

Lemma inb_iff : forall k l, inb k l = true <-> In k l.
Proof.
  intros k l. unfold inb. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply Nat.eqb_eq in E. subst. exact Hx.
  - intros H. exists k. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma inb_false : forall k l, inb k l = false <-> ~ In k l.
Proof.
  intros k l. rewrite <- inb_iff. destruct (inb k l); split; intro H; try congruence; tauto.
Qed.

Section TopoGen.
  Variable src : nat -> list nat.

  (* Data flows from k to j when k is a source of j. *)
  Inductive path : nat -> nat -> Prop :=
  | p_one : forall k j, In k (src j) -> path k j
  | p_snoc : forall k m j, path k m -> In m (src j) -> path k j.

  Definition Closed (o : list nat) : Prop := forall j k, In j o -> In k (src j) -> In k o.

  Lemma path_app : forall k m j, path k m -> path m j -> path k j.
  Proof.
    intros k m j H1 H2. induction H2 as [m j E | m m' j H IH E].
    - apply (p_snoc k m j H1 E).
    - apply (p_snoc k m' j (IH H1) E).
  Qed.

  (* ----- topological orders ----- *)

  Lemma topoF_nodup : forall l, topoF src l -> NoDup l.
  Proof.
    induction l as [| a l IH]; intros H; [constructor |].
    destruct H as [Ha [_ Hr]]. constructor; [exact Ha | apply IH; exact Hr].
  Qed.

  Lemma topoF_suffix : forall p s, topoF src (p ++ s) -> topoF src s.
  Proof. induction p as [| a p IH]; intros s H; [exact H | apply IH; apply H]. Qed.

  (* A source of an earlier registry is not later. *)
  Lemma topoF_later : forall p s a k, topoF src (p ++ s) -> In a p -> In k (src a) -> ~ In k s.
  Proof.
    induction p as [| x p IH]; intros s a k H Ha Hk; [destruct Ha |].
    destruct H as [Hx [Hs Hr]]. destruct Ha as [<- | Ha].
    - intro Hin. apply (Hs k Hk). right. apply in_or_app. right. exact Hin.
    - exact (IH s a k Hr Ha Hk).
  Qed.

  Lemma topoF_self : forall l a, topoF src l -> In a l -> ~ In a (src a).
  Proof.
    intros l a H Ha Hs. destruct (in_split a l Ha) as [p [s ->]].
    pose proof (topoF_suffix p (a :: s) H) as [_ [Hk _]]. apply (Hk a Hs). left. reflexivity.
  Qed.

  Lemma topoF_filter : forall (q : nat -> bool) l, topoF src l -> topoF src (filter q l).
  Proof.
    intros q. induction l as [| a l IH]; intros H; [exact I |].
    destruct H as [Ha [Hs Hr]]. simpl. destruct (q a); [| apply IH; exact Hr].
    split; [| split; [| apply IH; exact Hr]].
    - intro Hin. apply filter_In in Hin. apply Ha. apply Hin.
    - intros k Hk [E | Hin]; apply (Hs k Hk); [left; exact E | right; apply filter_In in Hin; apply Hin].
  Qed.

  Lemma topoF_app_intro : forall l1 l2, topoF src l1 -> topoF src l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    (forall a k, In a l1 -> In k (src a) -> ~ In k l2) -> topoF src (l1 ++ l2).
  Proof.
    induction l1 as [| a l1 IH]; intros l2 H1 H2 Hd Hs; [exact H2 |].
    destruct H1 as [Ha [Hsa Hr]]. simpl. split; [| split].
    - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact (Ha Hin) |].
      exact (Hd a (or_introl eq_refl) Hin).
    - intros k Hk [E | Hin]; [apply (Hsa k Hk); left; exact E |].
      apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [apply (Hsa k Hk); right; exact Hin |].
      exact (Hs a k (or_introl eq_refl) Hk Hin).
    - apply IH; [exact Hr | exact H2 | intros x Hx; apply Hd; right; exact Hx |].
      intros a' k Ha'. apply Hs. right. exact Ha'.
  Qed.

  (* A topological order closed under sources has no cycle among its registries. *)
  Fixpoint idx (l : list nat) (v : nat) : nat :=
    match l with [] => 0 | a :: r => if Nat.eqb a v then 0 else S (idx r v) end.

  Lemma idx_in_prefix : forall p s k, In k p -> idx (p ++ s) k < length p.
  Proof.
    induction p as [| a p IH]; intros s k H; [destruct H |]. simpl.
    destruct (Nat.eqb a k) eqn:E; [lia |]. destruct H as [<- | H]; [rewrite Nat.eqb_refl in E; discriminate |].
    specialize (IH s k H). lia.
  Qed.

  Lemma idx_at : forall p s v, ~ In v p -> idx (p ++ v :: s) v = length p.
  Proof.
    induction p as [| a p IH]; intros s v H; simpl; [rewrite Nat.eqb_refl; reflexivity |].
    destruct (Nat.eqb a v) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply H; left; reflexivity |].
    rewrite IH; [reflexivity | intro H'; apply H; right; exact H'].
  Qed.

  Lemma edge_idx : forall l k j, topoF src l -> Closed l -> In j l -> In k (src j) ->
    In k l /\ idx l k < idx l j.
  Proof.
    intros l k j Ht Hc Hj Hk. split; [exact (Hc j k Hj Hk) |].
    destruct (in_split j l Hj) as [p [s Hl]]. subst l.
    assert (Hnd := topoF_nodup _ Ht). apply NoDup_remove_2 in Hnd.
    assert (Hjp : ~ In j p) by (intro H; apply Hnd; apply in_or_app; left; exact H).
    pose proof (topoF_suffix p (j :: s) Ht) as [_ [Hsj _]].
    assert (Hkp : In k p).
    { pose proof (Hc j k Hj Hk) as Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact Hin |].
      exfalso. exact (Hsj k Hk Hin). }
    rewrite idx_at by exact Hjp. apply idx_in_prefix. exact Hkp.
  Qed.

  Lemma path_idx : forall l k j, topoF src l -> Closed l -> path k j -> In j l ->
    In k l /\ idx l k < idx l j.
  Proof.
    intros l k j Ht Hc P. induction P as [k j E | k m j P IH E]; intros Hj.
    - exact (edge_idx l k j Ht Hc Hj E).
    - destruct (edge_idx l m j Ht Hc Hj E) as [Hm Hlt]. destruct (IH Hm) as [Hk Hlt'].
      split; [exact Hk | lia].
  Qed.

  Theorem topoF_acyclic : forall l, topoF src l -> Closed l -> forall v, In v l -> ~ path v v.
  Proof. intros l Ht Hc v Hv P. destruct (path_idx l v v Ht Hc P Hv) as [_ H]. lia. Qed.

End TopoGen.

Arguments p_one {src}.
Arguments p_snoc {src}.

Section Graph.
  Variable src : nat -> list nat.
  Variable inJ : nat -> bool.

  (* def:subfed: no directed path between two members of J passes through a vertex outside J. *)
  Definition Convex : Prop :=
    forall u m w, inJ u = true -> inJ w = true -> inJ m = false -> path src u m -> path src m w -> False.

  (* J occupies one contiguous block of l. *)
  Definition Contiguous (l : list nat) : Prop :=
    exists p b s, l = p ++ b ++ s /\ (forall v, In v b -> inJ v = true) /\
      (forall v, In v p -> inJ v = false) /\ (forall v, In v s -> inJ v = false).

  (* ----- descendants of J outside J, by one forward scan of a topological order ----- *)

  Fixpoint descF (D : list nat) (l : list nat) : list nat :=
    match l with
    | [] => D
    | a :: r =>
        descF (if negb (inJ a) && existsb (fun k => inJ k || inb k D) (src a) then a :: D else D) r
    end.

  Definition DInv (p D : list nat) : Prop :=
    (forall v, In v D -> In v p /\ inJ v = false /\ exists u, inJ u = true /\ path src u v) /\
    (forall a k, In a p -> inJ a = false -> In k (src a) -> inJ k = true \/ In k D -> In a D).

  Lemma descF_spec : forall l p D, topoF src (p ++ l) -> DInv p D -> DInv (p ++ l) (descF D l).
  Proof.
    induction l as [| a r IH]; intros p D Ht [H1 H2]; simpl.
    - rewrite app_nil_r. split; assumption.
    - replace (p ++ a :: r) with ((p ++ [a]) ++ r) in * by (rewrite <- app_assoc; reflexivity).
      apply IH; [exact Ht |].
      assert (Hpa : forall a' k, In a' p -> In k (src a') -> k <> a).
      { intros a' k Ha' Hk E. subst k. rewrite <- app_assoc in Ht.
        exact (topoF_later src p (a :: r) a' a Ht Ha' Hk (or_introl eq_refl)). }
      assert (Haa : ~ In a (src a)).
      { apply (topoF_self src (p ++ [a] ++ r)); [rewrite app_assoc; exact Ht |].
        apply in_or_app. right. left. reflexivity. }
      destruct (negb (inJ a) && existsb (fun k => inJ k || inb k D) (src a)) eqn:C.
      + apply andb_true_iff in C. destruct C as [Ca Cx]. apply negb_true_iff in Ca.
        apply existsb_exists in Cx. destruct Cx as [k [Hk Ck]]. apply orb_true_iff in Ck.
        split.
        * intros v [<- | Hv].
          -- split; [apply in_or_app; right; left; reflexivity | split; [exact Ca |]].
             destruct Ck as [Ck | Ck].
             ++ exists k. split; [exact Ck | apply p_one; exact Hk].
             ++ apply inb_iff in Ck. destruct (H1 k Ck) as [_ [_ [u [Hu Pu]]]].
                exists u. split; [exact Hu | exact (p_snoc u k a Pu Hk)].
          -- destruct (H1 v Hv) as [Hp Hr]. split; [apply in_or_app; left; exact Hp | exact Hr].
        * intros a' k' Ha' HJ Hk' Hor. apply in_app_or in Ha'. destruct Ha' as [Ha' | [<- | []]].
          -- right. apply (H2 a' k' Ha' HJ Hk'). destruct Hor as [Hor | [E | Hor]]; [left; exact Hor | | right; exact Hor].
             exfalso. exact (Hpa a' k' Ha' Hk' (eq_sym E)).
          -- left. reflexivity.
      + split.
        * intros v Hv. destruct (H1 v Hv) as [Hp Hr]. split; [apply in_or_app; left; exact Hp | exact Hr].
        * intros a' k' Ha' HJ Hk' Hor. apply in_app_or in Ha'. destruct Ha' as [Ha' | [<- | []]].
          -- exact (H2 a' k' Ha' HJ Hk' Hor).
          -- exfalso. rewrite HJ in C. simpl in C.
             assert (Hx : existsb (fun k => inJ k || inb k D) (src a) = true).
             { apply existsb_exists. exists k'. split; [exact Hk' |].
               destruct Hor as [Hor | Hor]; [rewrite Hor; reflexivity |].
               apply inb_iff in Hor. rewrite Hor. apply orb_true_r. }
             rewrite Hx in C. discriminate C.
  Qed.

  Variable o : list nat.
  Hypothesis Htopo : topoF src o.
  Hypothesis Hconv : Convex.

  Definition desc : list nat := descF [] o.

  Lemma desc_inv : DInv o desc.
  Proof.
    apply (descF_spec o [] []); [exact Htopo |].
    split; [intros v [] | intros a k [] ].
  Qed.

  Lemma desc_notJ : forall v, In v desc -> inJ v = false.
  Proof. intros v H. apply (proj1 desc_inv v H). Qed.

  Definition preJ : list nat := filter (fun v => negb (inJ v) && negb (inb v desc)) o.
  Definition blk : list nat := filter inJ o.
  Definition postJ : list nat := filter (fun v => inb v desc) o.
  Definition blockOrder : list nat := preJ ++ blk ++ postJ.

  Lemma in_preJ : forall v, In v preJ <-> In v o /\ inJ v = false /\ ~ In v desc.
  Proof.
    intros v. unfold preJ. rewrite filter_In, andb_true_iff, !negb_true_iff, inb_false. tauto.
  Qed.

  Lemma in_blk : forall v, In v blk <-> In v o /\ inJ v = true.
  Proof. intros v. unfold blk. rewrite filter_In. tauto. Qed.

  Lemma in_postJ : forall v, In v postJ <-> In v o /\ In v desc.
  Proof. intros v. unfold postJ. rewrite filter_In, inb_iff. tauto. Qed.

  Lemma perm_three : forall l,
    Permutation l (filter (fun v => negb (inJ v) && negb (inb v desc)) l ++ filter inJ l ++
                   filter (fun v => inb v desc) l).
  Proof.
    induction l as [| a l IH]; [apply Permutation_refl |]. simpl.
    destruct (inJ a) eqn:Ja; destruct (inb a desc) eqn:Da; simpl.
    - exfalso. apply inb_iff in Da. rewrite (desc_notJ a Da) in Ja. discriminate.
    - apply Permutation_cons_app. exact IH.
    - rewrite app_assoc. apply Permutation_cons_app. rewrite <- app_assoc. exact IH.
    - apply perm_skip. exact IH.
  Qed.

  (* Corrected form of the proof step of thm:collapse (c): for a convex J there is SOME
     topological order of N in which J is one contiguous block. *)
  Theorem collapse_block_order :
    topoF src blockOrder /\ Permutation o blockOrder /\ Contiguous blockOrder /\
    (forall v, In v blk <-> In v o /\ inJ v = true).
  Proof.
    assert (Hpre : forall a k, In a preJ -> In k (src a) -> inJ k = true \/ In k desc -> False).
    { intros a k Ha Hk Hor. apply in_preJ in Ha. destruct Ha as [Ho [HJ Hd]].
      apply Hd. exact (proj2 desc_inv a k Ho HJ Hk Hor). }
    split; [| split; [apply perm_three | split; [| exact in_blk]]].
    - unfold blockOrder. apply topoF_app_intro; [apply topoF_filter; exact Htopo | |
        | ].
      + apply topoF_app_intro; [apply topoF_filter; exact Htopo | apply topoF_filter; exact Htopo | |].
        * intros x Hx Hx'. apply in_blk in Hx. apply in_postJ in Hx'.
          rewrite (desc_notJ x (proj2 Hx')) in Hx. destruct Hx as [_ H]. discriminate.
        * intros a k Ha Hk Hk'. apply in_blk in Ha. apply in_postJ in Hk'.
          destruct (proj1 desc_inv k (proj2 Hk')) as [_ [HkJ [u [Hu Pu]]]].
          exact (Hconv u k a Hu (proj2 Ha) HkJ Pu (p_one k a Hk)).
      + intros x Hx Hx'. apply in_preJ in Hx. apply in_app_or in Hx'.
        destruct Hx' as [Hx' | Hx']; [apply in_blk in Hx'; destruct Hx as [_ [H _]]; destruct Hx' as [_ H']; congruence |].
        apply in_postJ in Hx'. destruct Hx as [_ [_ H]]. exact (H (proj2 Hx')).
      + intros a k Ha Hk Hk'. apply in_app_or in Hk'. destruct Hk' as [Hk' | Hk'].
        * apply in_blk in Hk'. exact (Hpre a k Ha Hk (or_introl (proj2 Hk'))).
        * apply in_postJ in Hk'. exact (Hpre a k Ha Hk (or_intror (proj2 Hk'))).
    - exists preJ, blk, postJ. split; [reflexivity |]. split; [| split].
      + intros v Hv. apply in_blk in Hv. apply Hv.
      + intros v Hv. apply in_preJ in Hv. apply Hv.
      + intros v Hv. apply in_postJ in Hv. apply desc_notJ. apply Hv.
  Qed.

  (* ----- the contracted network N' ----- *)

  Variable c : nat.            (* the vertex of N' standing for J *)
  Hypothesis HcJ : inJ c = true.

  Definition qv (v : nat) : nat := if inJ v then c else v.

  Definition srcC (j : nat) : list nat :=
    if inJ j then (if Nat.eqb j c then flat_map (fun m => filter (fun k => negb (inJ k)) (src m)) blk
                   else [])
    else map qv (src j).

  Definition orderC : list nat := preJ ++ c :: postJ.

  Lemma srcC_out : forall a k, inJ a = false -> In k (srcC a) -> inJ k = false -> In k (src a).
  Proof.
    intros a k Ha Hk HkJ. unfold srcC in Hk. rewrite Ha in Hk. apply in_map_iff in Hk.
    destruct Hk as [k0 [E Hk0]]. unfold qv in E. destruct (inJ k0) eqn:J0.
    - subst. rewrite HcJ in HkJ. discriminate.
    - subst. exact Hk0.
  Qed.

  Lemma srcC_c : forall k, In k (srcC c) -> exists m, In m blk /\ In k (src m) /\ inJ k = false.
  Proof.
    intros k Hk. unfold srcC in Hk. rewrite HcJ, Nat.eqb_refl in Hk. apply in_flat_map in Hk.
    destruct Hk as [m [Hm Hk]]. apply filter_In in Hk. destruct Hk as [Hk HJ].
    exists m. split; [exact Hm | split; [exact Hk | apply negb_true_iff; exact HJ]].
  Qed.

  Lemma topoF_mono_noJ : forall l, (forall v, In v l -> inJ v = false) -> topoF src l -> topoF srcC l.
  Proof.
    induction l as [| a l IH]; intros HJ H; [exact I |]. destruct H as [Ha [Hs Hr]].
    split; [exact Ha | split; [| apply IH; [intros v Hv; apply HJ; right; exact Hv | exact Hr]]].
    intros k Hk Hin. apply (Hs k); [| exact Hin].
    apply (srcC_out a k (HJ a (or_introl eq_refl)) Hk). apply HJ. exact Hin.
  Qed.

  (* thm:collapse (c): contracting a convex J yields an acyclic network: N' has a topological
     order (the J-block replaced by the single vertex c). *)
  Theorem collapse_contract_topo : topoF srcC orderC.
  Proof.
    pose proof collapse_block_order as [Hbo _].
    unfold blockOrder in Hbo.
    assert (Tpre : topoF src preJ) by (apply topoF_filter; exact Htopo).
    assert (Tpost : topoF src postJ) by (apply topoF_filter; exact Htopo).
    assert (Npre : forall v, In v preJ -> inJ v = false) by (intros v Hv; apply in_preJ in Hv; apply Hv).
    assert (Npost : forall v, In v postJ -> inJ v = false)
      by (intros v Hv; apply in_postJ in Hv; apply desc_notJ; apply Hv).
    unfold orderC. apply topoF_app_intro.
    - apply topoF_mono_noJ; assumption.
    - split; [| split; [| apply topoF_mono_noJ; assumption]].
      + intro H. rewrite (Npost c H) in HcJ. discriminate.
      + intros k Hk [E | Hin].
        * subst k. destruct (srcC_c c Hk) as [_ [_ [_ H]]]. rewrite HcJ in H. discriminate.
        * destruct (srcC_c k Hk) as [m [Hm [Hkm HkJ]]]. apply in_postJ in Hin.
          destruct (proj1 desc_inv k (proj2 Hin)) as [_ [_ [u [Hu Pu]]]].
          apply in_blk in Hm. exact (Hconv u k m Hu (proj2 Hm) HkJ Pu (p_one k m Hkm)).
    - intros x Hx [E | Hin].
      + subst x. rewrite (Npre c Hx) in HcJ. discriminate.
      + apply in_preJ in Hx. apply in_postJ in Hin. destruct Hx as [_ [_ H]]. exact (H (proj2 Hin)).
    - intros a k Ha Hk Hin. pose proof (Npre a Ha) as HaJ. apply in_preJ in Ha.
      destruct Ha as [Ho [_ Hd]]. unfold srcC in Hk. rewrite HaJ in Hk. apply in_map_iff in Hk.
      destruct Hk as [k0 [E Hk0]]. unfold qv in E. destruct (inJ k0) eqn:J0.
      + apply Hd. exact (proj2 desc_inv a k0 Ho HaJ Hk0 (or_introl J0)).
      + subst k0. destruct Hin as [E | Hin]; [subst k; rewrite HcJ in J0; discriminate |].
        apply in_postJ in Hin. apply Hd. exact (proj2 desc_inv a k Ho HaJ Hk0 (or_intror (proj2 Hin))).
  Qed.

  Hypothesis Hclosed : Closed src o.
  Hypothesis Hco : In c o.

  Lemma orderC_closed : Closed srcC orderC.
  Proof.
    assert (Hplace : forall k, In k o -> inJ k = false -> In k orderC).
    { intros k Hk HJ. unfold orderC. apply in_or_app. destruct (inb k desc) eqn:D.
      - right. right. apply in_postJ. split; [exact Hk | apply inb_iff; exact D].
      - left. apply in_preJ. split; [exact Hk | split; [exact HJ | apply inb_false; exact D]]. }
    intros j k Hj Hk. unfold orderC in Hj. apply in_app_or in Hj.
    assert (Hout : forall j, In j o -> inJ j = false -> In k (srcC j) -> In k orderC).
    { intros j' Hj' HJ' Hk'. unfold srcC in Hk'. rewrite HJ' in Hk'. apply in_map_iff in Hk'.
      destruct Hk' as [k0 [E Hk0]]. unfold qv in E. pose proof (Hclosed j' k0 Hj' Hk0) as Ho0.
      destruct (inJ k0) eqn:J0.
      - subst k. unfold orderC. apply in_or_app. right. left. reflexivity.
      - subst k0. apply Hplace; assumption. }
    destruct Hj as [Hj | [E | Hj]].
    - apply in_preJ in Hj. apply (Hout j); [apply Hj | apply Hj | exact Hk].
    - subst j. destruct (srcC_c k Hk) as [m [Hm [Hkm HkJ]]]. apply in_blk in Hm.
      apply Hplace; [exact (Hclosed m k (proj1 Hm) Hkm) | exact HkJ].
    - apply in_postJ in Hj. apply (Hout j); [apply Hj | apply desc_notJ; apply Hj | exact Hk].
  Qed.

  (* thm:collapse (c), "acyclic if N is", in the path sense: N' has no cycle. *)
  Theorem collapse_contract_acyclic : forall v, In v orderC -> ~ path srcC v v.
  Proof.
    apply (topoF_acyclic srcC orderC collapse_contract_topo orderC_closed).
  Qed.
End Graph.


(* The paper's proof says "a topological order of N visits [a convex J] as a contiguous block".
   Read as "every topological order", it is false: three independent registries, J = {0, 2}
   (convex: there are no paths at all), and the topological order [0; 1; 2] splits J. *)
Definition ind_src (_ : nat) : list nat := [].
Definition j02 (v : nat) : bool := match v with 0 | 2 => true | _ => false end.

Theorem collapse_every_order_refuted :
  topoF ind_src [0; 1; 2] /\ Convex ind_src j02 /\ ~ Contiguous j02 [0; 1; 2].
Proof.
  split; [simpl; intuition lia |]. split.
  - intros u m w _ _ _ P. destruct P as [k j H | k m' j _ H]; destruct H.
  - intros [p [b [s [E [Hb [Hp Hs]]]]]].
    destruct p as [| x p].
    + simpl in E. destruct b as [| x0 b]; simpl in E.
      * subst s. specialize (Hs 0 (or_introl eq_refl)). discriminate.
      * injection E as E0 E. destruct b as [| x1 b]; simpl in E.
        -- subst s. specialize (Hs 2 (or_intror (or_introl eq_refl))). discriminate.
        -- injection E as E1 E. subst x1. specialize (Hb 1 (or_intror (or_introl eq_refl))).
           discriminate.
    + injection E as E0 _. subst x. specialize (Hp 0 (or_introl eq_refl)). discriminate.
Qed.

(* Convexity cannot be dropped from "N' acyclic if N is": the chain 0 -> 1 -> 2 is acyclic,
   J = {0, 2} is not convex, and contracting J to 0 creates the cycle 0 -> 1 -> 0. *)
Definition chain_src (j : nat) : list nat := match j with 1 => [0] | 2 => [1] | _ => [] end.

Theorem collapse_convexity_needed :
  topoF chain_src [0; 1; 2] /\ ~ Convex chain_src j02 /\
  path (srcC chain_src j02 [0; 1; 2] 0) 0 0.
Proof.
  split; [simpl; intuition lia |]. split.
  - intro H. apply (H 0 1 2 eq_refl eq_refl eq_refl); apply p_one; simpl; tauto.
  - apply (p_snoc 0 1 0); [apply p_one |]; vm_compute; tauto.
Qed.

(* ========================================================================================= *)
(* PART 2. The effective registry and the collapsed normalizer (FederationEvents.v model).   *)
(* ========================================================================================= *)

Section Sem.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  Variable o : list nat.
  Hypothesis HC : Common V src f valid rho E reg sig o.
  (* Phase 1 reaches local validity (FederationGRS.v's HR; derived there from component WFC). *)
  Hypothesis HR : forall j x, valid j (rho j x).

  Variable inJ : nat -> bool.
  Hypothesis Hconv : Convex src inJ.

  Local Notation InvF := (Inv V valid).
  Local Notation ConsF := (Cons V f o).
  Local Notation NF := (N V f rho o).
  Local Notation frF := (frun V f).
  Local Notation feqF := (feq V).
  Local Notation B := (blk inJ o).
  Local Notation P := (preJ src inJ o).
  Local Notation Q := (postJ src inJ o).

  Lemma Htopo : topoF src o.
  Proof. exact (c_topo _ _ _ _ _ _ _ _ _ HC). Qed.

  Lemma topo_blk : topoF src B.
  Proof. apply topoF_filter. exact Htopo. Qed.

  Lemma rho_idem : forall j x, rho j (rho j x) = rho j x.
  Proof. intros. apply (c_rho _ _ _ _ _ _ _ _ _ HC). apply HR. Qed.

  (* ----- def:effreg: the effective registry R_J ----- *)

  (* Phase 1 on the members of J only; the import ports (non-members) are read, not changed. *)
  Definition phaseJ (t : nat -> V) : nat -> V := fun k => if inJ k then rho k (t k) else t k.

  (* rho_Fed^J, R_J's compensation: phase 1 on J, then the internal repairs along J's block. *)
  Definition rhoJ (t : nat -> V) : nat -> V := frF B (phaseJ t).

  (* R_J's validity: each member locally valid, every internal repair equation satisfied. *)
  Definition InvJ (t : nat -> V) : Prop := forall k, inJ k = true -> valid k (t k).
  Definition InvOut (t : nat -> V) : Prop := forall k, inJ k = false -> valid k (t k).
  Definition ConsJ (t : nat -> V) : Prop := forall j, In j B -> t j = f j t (t j).

  Lemma inv_split : forall t, InvF t <-> InvJ t /\ InvOut t.
  Proof.
    intros t. split; [intro H; split; intros k _; apply H |].
    intros [H1 H2] k. destruct (inJ k) eqn:J; [apply H1 | apply H2]; exact J.
  Qed.

  Lemma phaseJ_inv : forall t, InvOut t -> InvF (phaseJ t).
  Proof. intros t H k. unfold phaseJ. destruct (inJ k) eqn:J; [apply HR | apply H; exact J]. Qed.

  Lemma phaseJ_valid : forall t, InvF t -> feqF (phaseJ t) t.
  Proof.
    intros t H k. unfold phaseJ. destruct (inJ k); [apply (c_rho _ _ _ _ _ _ _ _ _ HC); apply H | reflexivity].
  Qed.

  Lemma frun_fixed : forall l t, (forall j, In j l -> t j = f j t (t j)) -> feqF (frF l t) t.
  Proof.
    induction l as [| a l IH]; intros t H; [intro k; reflexivity |].
    change (frF (a :: l) t) with (frF l (fstep V f t a)).
    assert (Hs : feqF (fstep V f t a) t).
    { intro k. unfold fstep, upd. destruct (Nat.eqb k a) eqn:Ek; [| reflexivity].
      apply Nat.eqb_eq in Ek. subst k. symmetry. apply H. left. reflexivity. }
    intro k. rewrite (frun_ext _ _ _ _ _ _ _ _ _ HC l _ _ Hs k). apply IH.
    intros j Hj. apply H. right. exact Hj.
  Qed.

  (* thm:collapse (a), WFC part: rho_J is a well-founded compensation for R_J, in one round:
     from any state with valid import ports it reaches R_J-validity, leaves the ports and every
     non-member unchanged, and fixes every R_J-valid state (so it is idempotent). *)
  Theorem collapse_a_wfc :
    (forall t, InvOut t -> InvF (rhoJ t) /\ ConsJ (rhoJ t) /\ (forall k, inJ k = false -> rhoJ t k = t k)) /\
    (forall t, InvF t -> ConsJ t -> feqF (rhoJ t) t) /\
    (forall t, InvOut t -> feqF (rhoJ (rhoJ t)) (rhoJ t)).
  Proof.
    assert (A : forall t, InvOut t -> InvF (rhoJ t) /\ ConsJ (rhoJ t) /\
                  (forall k, inJ k = false -> rhoJ t k = t k)).
    { intros t Ht. pose proof (phaseJ_inv t Ht) as Hp.
      assert (Hi : InvF (rhoJ t)) by (apply (frun_inv _ _ _ _ _ _ _ _ _ HC); exact Hp).
      split; [exact Hi | split].
      - intros j Hj.
        assert (Hs : rhoJ t j = f j (rhoJ t) (phaseJ t j))
          by exact (frun_solves _ _ _ _ _ _ _ _ _ HC B _ topo_blk j Hj).
        rewrite Hs at 2. rewrite (c_absorb _ _ _ _ _ _ _ _ _ HC); [exact Hs | exact Hi | exact Hi | apply Hp].
      - intros k Hk. unfold rhoJ. rewrite frun_out.
        + unfold phaseJ. rewrite Hk. reflexivity.
        + intro H. apply in_blk in H. rewrite Hk in H. destruct H as [_ H]. discriminate. }
    assert (Bx : forall t, InvF t -> ConsJ t -> feqF (rhoJ t) t).
    { intros t Hi Hc k. unfold rhoJ.
      rewrite (frun_ext _ _ _ _ _ _ _ _ _ HC B _ _ (phaseJ_valid t Hi) k). apply frun_fixed. exact Hc. }
    split; [exact A | split; [exact Bx |]].
    intros t Ht. destruct (A t Ht) as [Hi [Hc _]]. apply Bx; assumption.
  Qed.

  (* ----- R_J's events: the events of J's members, applied then compensated by rho_J ----- *)

  Definition applyJ (e : E) (t : nat -> V) : nat -> V := rhoJ (evstep V E reg sig e t).
  Definition runJ (es : list E) (t : nat -> V) : nat -> V := fold_left (fun s e => applyJ e s) es t.

  (* R_J as a federation of its own: the sub-federation on the block, with J's events. *)
  Definition EJ : Type := { e : E | inJ (reg e) = true }.
  Definition regJ (x : EJ) : nat := reg (proj1_sig x).
  Definition sigJ (x : EJ) : V -> V := sig (proj1_sig x).
  Definition IJ (x y : EJ) : Prop := I (proj1_sig x) (proj1_sig y).

  Lemma sub_common : Common V src f valid rho EJ regJ sigJ B.
  Proof.
    constructor.
    - exact (c_local _ _ _ _ _ _ _ _ _ HC).
    - exact topo_blk.
    - exact (c_m1 _ _ _ _ _ _ _ _ _ HC).
    - exact (c_absorb _ _ _ _ _ _ _ _ _ HC).
    - exact (c_rho _ _ _ _ _ _ _ _ _ HC).
    - intros x. exact (c_sig _ _ _ _ _ _ _ _ _ HC (proj1_sig x)).
    - intros [e He]. unfold regJ. simpl. apply in_blk. split; [exact (c_reg _ _ _ _ _ _ _ _ _ HC e) | exact He].
  Qed.

  (* The C1 and C2 obligations of the events of J's members (the sub-federation's certificate). *)
  Definition C1on (Pj : nat -> bool) : Prop :=
    forall e z z' b, Pj (reg e) = true -> Inv V valid z -> Inv V valid z' -> valid (reg e) b ->
      b = f (reg e) z' b -> f (reg e) z (sig e (f (reg e) z b)) = f (reg e) z (sig e b).

  Definition C2on (Pj : nat -> bool) : Prop :=
    forall e1 e2 z b, Pj (reg e1) = true -> reg e1 = reg e2 -> I e1 e2 -> Inv V valid z ->
      valid (reg e1) b -> b = f (reg e1) z b ->
      f (reg e1) z (sig e2 (f (reg e1) z (sig e1 b))) = f (reg e1) z (sig e1 (f (reg e1) z (sig e2 b))).

  Lemma sub_c1 : C1on inJ -> C1 V f valid EJ regJ sigJ.
  Proof. intros H [e He] z z' b. unfold regJ, sigJ. simpl. apply H. exact He. Qed.

  Lemma sub_c2 : C2on inJ -> C2 V f valid EJ regJ sigJ IJ.
  Proof. intros H [e1 He1] [e2 He2] z b. unfold regJ, sigJ, IJ. simpl. apply H. exact He1. Qed.

  Local Notation aJ := (applyF V f rho EJ regJ sigJ B).
  Local Notation rJ := (runF V f rho EJ regJ sigJ B).

  Lemma applyJ_sub : forall x t, InvF t -> feqF (applyJ (proj1_sig x) t) (aJ x t).
  Proof.
    intros x t Ht k. unfold applyJ, applyF, N, rhoJ.
    apply (frun_ext _ _ _ _ _ _ _ _ _ HC). intro m.
    assert (He : InvF (evstep V E reg sig (proj1_sig x) t))
      by exact (evstep_inv _ _ _ _ _ _ _ _ _ HC _ _ Ht).
    change (evstep V EJ regJ sigJ x t) with (evstep V E reg sig (proj1_sig x) t).
    unfold phaseJ. rewrite (c_rho _ _ _ _ _ _ _ _ _ HC m _ (He m)).
    destruct (inJ m); reflexivity.
  Qed.

  Lemma applyJ_inv : forall e t, InvF t -> InvF (applyJ e t).
  Proof.
    intros e t Ht. unfold applyJ. apply (proj1 collapse_a_wfc). intros k _.
    exact (evstep_inv _ _ _ _ _ _ _ _ _ HC _ _ Ht k).
  Qed.

  Lemma applyJ_ext : forall e t u, feqF t u -> feqF (applyJ e t) (applyJ e u).
  Proof.
    intros e t u H. unfold applyJ, rhoJ. apply (frun_ext _ _ _ _ _ _ _ _ _ HC).
    intro k. unfold phaseJ. rewrite (evstep_ext V E reg sig e t u H k). reflexivity.
  Qed.

  Lemma runJ_sub : forall xs t, InvF t -> feqF (runJ (map (@proj1_sig _ _) xs) t) (rJ xs t).
  Proof.
    induction xs as [| x xs IH]; intros t Ht; [intro k; reflexivity |].
    simpl. change (rJ (x :: xs) t) with (rJ xs (aJ x t)).
    intro k. rewrite (IH _ (applyJ_inv _ _ Ht) k).
    apply (runF_ext _ _ _ _ _ _ _ _ _ sub_common). apply applyJ_sub. exact Ht.
  Qed.

  (* thm:collapse (a), CC part, corrected (guarded model: events fire at R_J-valid states). Two
     events of J's members that are federally independent (different registries, or declared
     independent) commute through R_J, given only J's own certificate C1 and C2. *)
  Theorem collapse_a_guarded : C1on inJ -> C2on inJ ->
    forall t e1 e2, InvF t -> ConsJ t -> inJ (reg e1) = true -> inJ (reg e2) = true ->
      Ifed E reg I e1 e2 -> feqF (applyJ e2 (applyJ e1 t)) (applyJ e1 (applyJ e2 t)).
  Proof.
    intros H1 H2 t e1 e2 Ht Hc J1 J2 Hi.
    pose (x1 := exist (fun e => inJ (reg e) = true) e1 J1).
    pose (x2 := exist (fun e => inJ (reg e) = true) e2 J2).
    assert (Hcomm := fed_events_commute _ _ _ _ _ _ _ _ _ _ sub_common (sub_c1 H1) (sub_c2 H2)
                       t x1 x2 Ht Hc Hi).
    assert (I1 := applyF_inv _ _ _ _ _ _ _ _ _ sub_common x1 t Ht).
    assert (I2 := applyF_inv _ _ _ _ _ _ _ _ _ sub_common x2 t Ht).
    intro k.
    transitivity (applyJ e2 (aJ x1 t) k); [apply applyJ_ext; exact (applyJ_sub x1 t Ht) |].
    transitivity (aJ x2 (aJ x1 t) k); [exact (applyJ_sub x2 _ I1 k) |].
    transitivity (aJ x1 (aJ x2 t) k); [apply Hcomm |].
    symmetry.
    transitivity (applyJ e1 (aJ x2 t) k); [apply applyJ_ext; exact (applyJ_sub x2 t Ht) |].
    exact (applyJ_sub x1 _ I2 k).
  Qed.

  (* The same for any two orders of J's events (every same-registry pair declared independent):
     R_J's event system is order independent. *)
  Theorem collapse_a_guarded_perm : C1on inJ -> C2on inJ ->
    (forall x y : EJ, regJ x = regJ y -> IJ x y) ->
    forall xs1 xs2 : list EJ, Permutation xs1 xs2 -> forall t, InvF t -> ConsJ t ->
      feqF (runJ (map (@proj1_sig _ _) xs1) t) (runJ (map (@proj1_sig _ _) xs2) t).
  Proof.
    intros H1 H2 Htot xs1 xs2 Hp t Ht Hc k.
    rewrite (runJ_sub xs1 t Ht k), (runJ_sub xs2 t Ht k).
    exact (fed_permutations_converge _ _ _ _ _ _ _ _ _ _ sub_common (sub_c1 H1) (sub_c2 H2) Htot
             xs1 xs2 Hp t Ht Hc k).
  Qed.

  (* The exact condition for R_J (fed_exact on the sub-federation): R_J's event system converges
     from an R_J-valid state iff C1 and C2 hold at the witnesses reachable inside J. *)
  Theorem collapse_a_guarded_exact : forall s0, InvF s0 -> ConsJ s0 ->
    (TraceConv V f rho EJ regJ sigJ IJ B s0 <->
     C1R1 V f rho EJ regJ sigJ B s0 /\ C2R V f rho EJ regJ sigJ IJ B s0).
  Proof. intros s0 Hi Hc. exact (fed_exact _ _ _ _ _ _ _ _ _ _ sub_common s0 Hi Hc). Qed.

  (* ----- thm:collapse (b): boundary morphisms ----- *)

  (* M1 of the morphism (resolver) into registry j, as in N. *)
  Definition M1at (j : nat) : Prop := forall z x, InvF z -> valid j x -> valid j (f j z x).

  (* An import into the member j, reinterpreted as a morphism into R_J: overwrite R_J's
     component j from the source states z. *)
  Definition Fimp (j : nat) (z T : nat -> V) : nat -> V := upd V T j (f j z (T j)).
  Definition M1imp (j : nat) : Prop := forall z T, InvF z -> InvJ T -> InvJ (Fimp j z T).

  (* An export from J into a non-member k, reinterpreted as a morphism from R_J: its sources
     are read from R_J's state T on members and from z elsewhere. *)
  Definition merge (z T : nat -> V) : nat -> V := fun m => if inJ m then T m else z m.
  Definition M1exp (k : nat) : Prop :=
    forall z T x, InvOut z -> InvJ T -> valid k x -> valid k (f k (merge z T) x).

  (* thm:collapse (b), exact, with M1 posed against R_J's member validities (the product of the
     members' valid sets): an import satisfies M1 into R_J iff it does into its member. *)
  Theorem collapse_b_import_iff : forall j, inJ j = true -> (M1at j <-> M1imp j).
  Proof.
    intros j Hj. split.
    - intros H z T Hz HT k Hk. unfold Fimp, upd. destruct (Nat.eqb k j) eqn:Ek.
      + apply Nat.eqb_eq in Ek. subst k. apply H; [exact Hz | apply HT; exact Hk].
      + apply HT. exact Hk.
    - intros H z x Hz Hx.
      set (T := upd V (fun k => rho k x) j x).
      assert (HT : InvJ T).
      { intros k _. unfold T, upd. destruct (Nat.eqb k j) eqn:Ek; [apply Nat.eqb_eq in Ek; subst; exact Hx | apply HR]. }
      pose proof (H z T Hz HT j Hj) as Hv. unfold Fimp in Hv. rewrite upd_eq in Hv.
      unfold T in Hv. rewrite upd_eq in Hv. exact Hv.
  Qed.

  (* thm:collapse (b), exact for exports, same reading. *)
  Theorem collapse_b_export_iff : forall k, M1at k <-> M1exp k.
  Proof.
    intros k. split.
    - intros H z T x Hz HT Hx. apply H; [| exact Hx]. intro m. unfold merge.
      destruct (inJ m) eqn:J; [apply HT | apply Hz]; exact J.
    - intros H z x Hz Hx.
      assert (Hm : f k (merge z z) x = f k z x).
      { apply (c_local _ _ _ _ _ _ _ _ _ HC). intros m _. unfold merge. destruct (inJ m); reflexivity. }
      rewrite <- Hm. apply H; [intros m _; apply Hz | intros m _; apply Hz | exact Hx].
  Qed.

  (* With R_J's validity read as the paper's def:effreg does (member validities AND the internal
     morphism invariants), the paper's "iff" fails in both directions (collapse_b_import_refuted,
     collapse_b_export_refuted below). What holds instead: *)
  Definition FedJ (t : nat -> V) : Prop := InvJ t /\ ConsJ t.

  (* Import, corrected: after any import changes a port's source (a non-member i takes a new
     valid value and the morphism into j is applied), re-normalizing with rho_J restores R_J's
     federal validity and leaves every non-member unchanged. This is the reading the paper's
     proof of (b) uses ("sub-federated re-normalization preserves federal validity"). *)
  Theorem collapse_b_import_corrected : forall t i y j, InvF t -> valid i y ->
    let t' := fstep V f (upd V t i y) j in
    FedJ (rhoJ t') /\ (forall k, inJ k = false -> rhoJ t' k = t' k).
  Proof.
    intros t i y j Ht Hy t'.
    assert (Hu : InvF (upd V t i y)).
    { intro k. unfold upd. destruct (Nat.eqb k i) eqn:Ek; [apply Nat.eqb_eq in Ek; subst; exact Hy | apply Ht]. }
    assert (Ht' : InvF t') by (apply (fstep_inv _ _ _ _ _ _ _ _ _ HC); exact Hu).
    destruct (proj1 collapse_a_wfc t' (fun k _ => Ht' k)) as [Hi [Hc Ho]].
    split; [split; [intros k _; apply Hi | exact Hc] | exact Ho].
  Qed.

  (* Export, corrected: M1 of an export in N implies M1 of the export read from R_J's federally
     valid states (the converse fails: collapse_b_export_refuted). *)
  Definition M1expFed (k : nat) : Prop :=
    forall z x, InvF z -> ConsJ z -> valid k x -> valid k (f k z x).

  Theorem collapse_b_export_corrected : forall k, M1at k -> M1expFed k.
  Proof. intros k H z x Hz _ Hx. apply H; assumption. Qed.

  (* ----- thm:collapse (c): the contracted network N' and its normalizer ----- *)

  (* A network of blocks: each block is run as one node (a single registry is a block [j]). *)
  Definition nrun (bs : list (list nat)) (t : nat -> V) : nat -> V :=
    fold_left (fun s b => frF b s) bs t.

  Lemma frun_app : forall l1 l2 t, frF (l1 ++ l2) t = frF l2 (frF l1 t).
  Proof. intros. unfold frun. apply fold_left_app. Qed.

  Lemma nrun_concat : forall bs t, nrun bs t = frF (concat bs) t.
  Proof.
    induction bs as [| b bs IH]; intros t; [reflexivity |].
    simpl. unfold nrun in *. simpl. rewrite IH, frun_app. reflexivity.
  Qed.

  Lemma concat_singletons : forall l : list nat, concat (map (fun j => [j]) l) = l.
  Proof. induction l as [| a l IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

  (* N': every registry outside J is its own node; J is the single node R_J, run as its block. *)
  Definition blocksC : list (list nat) := map (fun j => [j]) P ++ B :: map (fun j => [j]) Q.
  Definition Ncol (t : nat -> V) : nat -> V := nrun blocksC (fun k => rho k (t k)).

  Lemma concat_blocksC : concat blocksC = blockOrder src inJ o.
  Proof.
    unfold blocksC, blockOrder. rewrite concat_app. simpl. rewrite !concat_singletons. reflexivity.
  Qed.

  (* Two topological orders of the same registries compute the same repair (solve_unique). *)
  Lemma frun_topo_eq : forall l1 l2 u, topoF src l1 -> topoF src l2 -> (forall k, In k l1 <-> In k l2) ->
    feqF (frF l1 u) (frF l2 u).
  Proof.
    intros l1 l2 u T1 T2 Hs.
    apply (solve_unique _ _ _ _ _ _ _ _ _ HC l1 _ _ u u T1).
    - intros k Hk. rewrite !frun_out; [reflexivity | rewrite <- Hs; exact Hk | exact Hk].
    - intros j Hj. exact (frun_solves _ _ _ _ _ _ _ _ _ HC l1 u T1 j Hj).
    - intros j Hj. apply Hs in Hj. exact (frun_solves _ _ _ _ _ _ _ _ _ HC l2 u T2 j Hj).
    - intros j _. reflexivity.
  Qed.

  Lemma Hbo : topoF src (blockOrder src inJ o) /\ Permutation o (blockOrder src inJ o).
  Proof. destruct (collapse_block_order src inJ o Htopo Hconv) as [H1 [H2 _]]. split; assumption. Qed.

  (* thm:collapse (c), normal forms: N' and N have the same normalizer (under
     Sigma_{R_J} = prod_{i in J} Sigma_{R_i}, here the shared federated state). *)
  Theorem collapse_nf_agree : forall t, feqF (Ncol t) (NF t).
  Proof.
    intros t. unfold Ncol, N. rewrite nrun_concat, concat_blocksC. destruct Hbo as [T P'].
    apply frun_topo_eq; [exact T | exact Htopo |].
    intros k. split; apply Permutation_in; [apply Permutation_sym |]; exact P'.
  Qed.

  (* The paper's factorization: rho_Fed on N is "phase 1, the registries before J, then R_J's
     compensation rho_J, then propagate past the boundary". *)
  Theorem collapse_nf_factor : forall t,
    feqF (NF t) (frF Q (rhoJ (frF P (fun k => rho k (t k))))).
  Proof.
    intros t k. rewrite <- (collapse_nf_agree t k). unfold Ncol. rewrite nrun_concat, concat_blocksC.
    unfold blockOrder. rewrite !frun_app. apply (frun_ext _ _ _ _ _ _ _ _ _ HC).
    unfold rhoJ. apply (frun_ext _ _ _ _ _ _ _ _ _ HC). intro m. unfold phaseJ.
    destruct (inJ m) eqn:J; [| reflexivity].
    rewrite frun_out; [symmetry; apply rho_idem |].
    intro H. apply in_preJ in H. destruct H as [_ [H _]]. congruence.
  Qed.

  (* N' federally valid: every node satisfied (the J-node: R_J's internal invariants). *)
  Definition ConsC (t : nat -> V) : Prop :=
    (forall j, In j P -> t j = f j t (t j)) /\ ConsJ t /\ (forall j, In j Q -> t j = f j t (t j)).

  Lemma consC_iff : forall t, ConsC t <-> ConsF t.
  Proof.
    intros t. destruct Hbo as [_ Hp]. unfold blockOrder in Hp. split.
    - intros [H1 [H2 H3]] j Hj. apply (Permutation_in j Hp) in Hj.
      apply in_app_or in Hj. destruct Hj as [Hj | Hj]; [apply H1; exact Hj |].
      apply in_app_or in Hj. destruct Hj as [Hj | Hj]; [apply H2; exact Hj | apply H3; exact Hj].
    - intros H. split; [| split]; intros j Hj; apply H; apply (Permutation_in j (Permutation_sym Hp));
        apply in_or_app; [left; exact Hj | right; apply in_or_app; left; exact Hj |
                          right; apply in_or_app; right; exact Hj].
  Qed.

  Definition applyC (e : E) (t : nat -> V) : nat -> V := Ncol (evstep V E reg sig e t).
  Definition runC (es : list E) (t : nat -> V) : nat -> V := fold_left (fun s e => applyC e s) es t.

  (* thm:collapse (c), convergence: every event run of N' equals the same run of N. *)
  Theorem collapse_c_runs_agree : forall es t, feqF (runC es t) (runF V f rho E reg sig o es t).
  Proof.
    induction es as [| e es IH]; intros t; [intro k; reflexivity |].
    simpl. change (runF V f rho E reg sig o (e :: es) t) with (runF V f rho E reg sig o es (applyF V f rho E reg sig o e t)).
    intro k. rewrite (IH (applyC e t) k). apply (runF_ext _ _ _ _ _ _ _ _ _ HC).
    intro m. apply collapse_nf_agree.
  Qed.

  (* Hence N' converges (every two trace-equivalent event orders agree) iff N does, and the
     exact condition is C1 and C2 at the reachable witnesses (fed_exact). *)
  Definition TraceConvC (s0 : nat -> V) : Prop :=
    forall es1 es2, tequiv (Ifed E reg I) es1 es2 -> feqF (runC es1 s0) (runC es2 s0).

  Theorem collapse_c_traceconv : forall s0, TraceConvC s0 <-> TraceConv V f rho E reg sig I o s0.
  Proof.
    intros s0. split; intros H es1 es2 Ht k.
    - rewrite <- (collapse_c_runs_agree es1 s0 k), <- (collapse_c_runs_agree es2 s0 k). apply H. exact Ht.
    - rewrite (collapse_c_runs_agree es1 s0 k), (collapse_c_runs_agree es2 s0 k). apply H. exact Ht.
  Qed.

  Theorem collapse_c_exact : forall s0, InvF s0 -> ConsC s0 ->
    (TraceConvC s0 <-> C1R1 V f rho E reg sig o s0 /\ C2R V f rho E reg sig I o s0).
  Proof.
    intros s0 Hi Hc. rewrite collapse_c_traceconv.
    exact (fed_exact _ _ _ _ _ _ _ _ _ _ HC s0 Hi (proj1 (consC_iff s0) Hc)).
  Qed.

  (* ----- cor:modular ----- *)

  (* Verifying J once and the rest once is verifying N: C1 and C2 split by the event's registry. *)
  Theorem collapse_modular_c1 :
    C1 V f valid E reg sig <-> C1on inJ /\ C1on (fun k => negb (inJ k)).
  Proof.
    split.
    - intros H. split; intros e z z' b _; apply H.
    - intros [H1 H2] e z z' b. destruct (inJ (reg e)) eqn:J; [apply H1; exact J | apply H2; rewrite J; reflexivity].
  Qed.

  Theorem collapse_modular_c2 :
    C2 V f valid E reg sig I <-> C2on inJ /\ C2on (fun k => negb (inJ k)).
  Proof.
    split.
    - intros H. split; intros e1 e2 z b _; apply H.
    - intros [H1 H2] e1 e2 z b. destruct (inJ (reg e1)) eqn:J; [apply H1; exact J | apply H2; rewrite J; reflexivity].
  Qed.

  (* Modular verification: J's certificate (C1, C2 on J's events) and the rest's certificate give
     R_J's guarded CC and the convergence of N' (and of N). *)
  Theorem collapse_modular_converges :
    C1on inJ -> C2on inJ -> C1on (fun k => negb (inJ k)) -> C2on (fun k => negb (inJ k)) ->
    (forall t e1 e2, InvF t -> ConsJ t -> inJ (reg e1) = true -> inJ (reg e2) = true ->
       Ifed E reg I e1 e2 -> feqF (applyJ e2 (applyJ e1 t)) (applyJ e1 (applyJ e2 t))) /\
    (forall s0, InvF s0 -> ConsC s0 -> TraceConvC s0).
  Proof.
    intros A1 A2 B1 B2. split; [exact (collapse_a_guarded A1 A2) |].
    intros s0 Hi Hc. apply (collapse_c_exact s0 Hi Hc).
    assert (H1 : C1 V f valid E reg sig) by (apply collapse_modular_c1; split; assumption).
    assert (H2 : C2 V f valid E reg sig I) by (apply collapse_modular_c2; split; assumption).
    exact (proj2 (static_c1_c2_gc _ _ _ _ _ _ _ _ _ _ HC H1 H2 s0 Hi (proj1 (consC_iff s0) Hc))).
  Qed.

  (* Hierarchical verification: any nesting of blocks is evaluated through its flattening, so a
     regrouping of consecutive nodes into one node leaves the normalizer unchanged ... *)
  Theorem collapse_regroup : forall bs1 bs2 bs3 t,
    nrun (bs1 ++ bs2 ++ bs3) t = nrun (bs1 ++ concat bs2 :: bs3) t.
  Proof.
    intros. rewrite !nrun_concat, !concat_app. simpl. reflexivity.
  Qed.

  (* ... and any block decomposition whose flattening is a topological order of N's registries
     (for example one obtained by collapsing convex sub-federations level by level) computes
     rho_Fed of N. *)
  Theorem collapse_hierarchical : forall bs t, topoF src (concat bs) ->
    (forall k, In k (concat bs) <-> In k o) -> feqF (nrun bs (fun k => rho k (t k))) (NF t).
  Proof.
    intros bs t T Hs. unfold N. rewrite nrun_concat. apply frun_topo_eq; [exact T | exact Htopo | exact Hs].
  Qed.
End Sem.

(* The product case of cor:modular (E_J empty, empty boundary): a J with no edge leaving it is
   convex, so the collapse applies. *)
Lemma path_first : forall src k j, path src k j -> exists x, In k (src x).
Proof.
  intros src k j P. induction P as [k j H | k m j _ IH _]; [exists j; exact H | exact IH].
Qed.

Lemma path_last : forall src k j, path src k j -> exists y, In y (src j).
Proof. intros src k j P. destruct P as [k j H | k m j _ H]; [exists k | exists m]; exact H. Qed.

Theorem collapse_product_convex : forall src inJ,
  (forall j k, In k (src j) -> inJ k = false) -> Convex src inJ.
Proof.
  intros src inJ H u m w Hu _ _ P _. destruct (path_first src u m P) as [x Hx].
  rewrite (H x u Hx) in Hu. discriminate.
Qed.

(* ========================================================================================= *)
(* PART 3. thm:collapse (c) for the federated GRS (FederationGRS.v): the guarded GRS of N'     *)
(* (events fire only at federally valid states) is the guarded GRS of N.                      *)
(* ========================================================================================= *)

Section RelIff.
  Context {A : Type} (R1 R2 : A -> A -> Prop).
  Hypothesis H : forall x y, R1 x y <-> R2 x y.

  Lemma star_iff : forall x y, star R1 x y -> star R2 x y.
  Proof.
    intros x y S. induction S as [x | x y z Hxy _ IH]; [apply star_refl |].
    apply (star_step R2 x y z); [apply H; exact Hxy | exact IH].
  Qed.

  Lemma nf_iff : forall x, normal_form R1 x -> normal_form R2 x.
  Proof. intros x N1 [y Hy]. apply N1. exists y. apply H. exact Hy. Qed.
End RelIff.

Lemma UN_iff : forall {A : Type} (R1 R2 : A -> A -> Prop), (forall x y, R1 x y <-> R2 x y) ->
  forall x, UN R1 x <-> UN R2 x.
Proof.
  intros A R1 R2 H x.
  assert (H' : forall x y, R2 x y <-> R1 x y) by (intros; symmetry; apply H).
  split; intros U n1 n2 S1 N1 S2 N2.
  - apply U; [apply (star_iff R2 R1 H') | apply (nf_iff R2 R1 H') | apply (star_iff R2 R1 H') |
              apply (nf_iff R2 R1 H')]; assumption.
  - apply U; [apply (star_iff R1 R2 H) | apply (nf_iff R1 R2 H) | apply (star_iff R1 R2 H) |
              apply (nf_iff R1 R2 H)]; assumption.
Qed.

Lemma step_iff : forall {St Ev : Type} (Eeq : forall x y : Ev, {x = y} + {x <> y})
  (ap : Ev -> St -> St) (r1 r2 : St -> St) (v1 v2 : St -> Prop) (en1 en2 : Ev -> St -> list Ev -> Prop),
  (forall s, r1 s = r2 s) -> (forall s, v1 s <-> v2 s) -> (forall e s B, en1 e s B <-> en2 e s B) ->
  forall x y, step Eeq ap r1 v1 en1 x y <-> step Eeq ap r2 v2 en2 x y.
Proof.
  intros St Ev Eeq ap r1 r2 v1 v2 en1 en2 Hr Hv He x y. split; intro S.
  - destruct S as [s B e Hin Hen | s B Hinv]; [apply st_apply; [exact Hin | apply He; exact Hen] |].
    rewrite Hr. apply st_comp. rewrite <- Hv. exact Hinv.
  - destruct S as [s B e Hin Hen | s B Hinv]; [apply st_apply; [exact Hin | apply He; exact Hen] |].
    rewrite <- Hr. apply st_comp. rewrite Hv. exact Hinv.
Qed.

Section GRSC.
  Variable V : Type.
  Variable src : nat -> list nat.
  Variable f : nat -> (nat -> V) -> V -> V.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable ap : E -> V -> V.
  Variable o : list nat.
  Variable n : nat.
  Variable d : V.
  Local Notation sg := (gsig V rho E reg ap).
  Hypothesis HC : Common V src f valid rho E reg sg o.
  Hypothesis HR : forall j x, valid j (rho j x).
  Hypothesis Hrange : forall k, In k o <-> k < n.
  Hypothesis Hsrc : forall j k, In k (src j) -> k < n.
  Hypothesis Hout : forall k x, n <= k -> valid k x.
  Hypothesis vdec : forall k x, {valid k x} + {~ valid k x}.
  Hypothesis Veq : forall x y : V, {x = y} + {x <> y}.
  Hypothesis Eeq : forall x y : E, {x = y} + {x <> y}.
  Variable inJ : nat -> bool.
  Hypothesis Hconv : Convex src inJ.

  Local Notation GA := (gapply V E reg ap n d).
  Local Notation GR := (grho V f rho o n d).
  Local Notation GV := (gvalid V f valid o n d).
  Local Notation toF := (toF V d).
  Local Notation fromF := (fromF V n).

  (* N' on lists: rho_Fed of the contracted network, and its federal validity. *)
  Definition grhoC (l : list V) : list V := fromF (Ncol V src f rho o inJ (toF l)).
  Definition gvalidC (l : list V) : Prop :=
    length l = n /\ Inv V valid (toF l) /\ ConsC V src f o inJ (toF l).
  Definition genabC (e : E) (l : list V) (B : list E) : Prop := In e B /\ gvalidC l.

  Lemma grhoC_eq : forall l, grhoC l = GR l.
  Proof.
    intros l. unfold grhoC, grho. apply fromF_ext. apply feq_feqn.
    exact (collapse_nf_agree V src f valid rho E reg sg o HC inJ Hconv (toF l)).
  Qed.

  Lemma gvalidC_iff : forall l, gvalidC l <-> GV l.
  Proof.
    intros l. unfold gvalidC, gvalid.
    rewrite (consC_iff V src f valid rho E reg sg o HC inJ Hconv). tauto.
  Qed.

  Local Notation GC := (step Eeq GA grhoC gvalidC free_enabled).
  Local Notation G := (step Eeq GA GR GV free_enabled).
  Local Notation GgC := (step Eeq GA grhoC gvalidC genabC).
  Local Notation Gg := (step Eeq GA GR GV (genab V f valid E o n d)).

  (* thm:collapse (c), guarded GRS: N' converges iff N does (the two GRSs coincide). *)
  Theorem collapse_c_guarded_iff : forall c, UN GgC c <-> UN Gg c.
  Proof.
    apply UN_iff. apply step_iff; [exact grhoC_eq | exact gvalidC_iff |].
    intros e s B. unfold genabC, genab. rewrite gvalidC_iff. tauto.
  Qed.

  Theorem collapse_c_unguarded_iff : forall c, UN GC c <-> UN G c.
  Proof.
    apply UN_iff. apply step_iff; [exact grhoC_eq | exact gvalidC_iff | tauto].
  Qed.

  (* The exact condition for N' (fed_guarded_exact through the collapse). *)
  Theorem collapse_c_guarded_exact : forall s0, gvalidC s0 ->
    ((forall B, UN GgC (s0, B)) <->
     C1R1 V f rho E reg sg o (toF s0) /\ C2R V f rho E reg sg (Itot E) o (toF s0)).
  Proof.
    intros s0 Hs0. rewrite <- (fed_guarded_exact V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout
                                vdec Veq Eeq s0 (proj1 (gvalidC_iff s0) Hs0)).
    split; intros H B; [apply collapse_c_guarded_iff | apply collapse_c_guarded_iff]; apply H.
  Qed.

  (* Corrected thm:collapse (c): with C1 and C2 (verifiable per block, cor:modular), N' converges. *)
  Theorem collapse_c_guarded_c1_c2 :
    C1 V f valid E reg sg -> C2 V f valid E reg sg (Itot E) ->
    forall s0, gvalidC s0 -> forall B, UN GgC (s0, B).
  Proof.
    intros H1 H2 s0 Hs0 B. apply collapse_c_guarded_iff.
    exact (fed_guarded_c1_c2 V src f valid rho E reg ap o n d HC HR Hrange Hsrc Hout vdec Veq Eeq
             H1 H2 s0 (proj1 (gvalidC_iff s0) Hs0) B).
  Qed.
End GRSC.

(* ========================================================================================= *)
(* PART 4. Counterexamples to thm:collapse (a) and (b) as stated.                             *)
(* ========================================================================================= *)

Definition all_true (_ : nat) : bool := true.

(* thm:collapse (a), CC part, as stated, is false. The audit federation (FederationGRS.v,
   fed_thm_fed_cc_refuted) is a tree whose components satisfy WFC and CC and whose morphism
   satisfies M1: exactly the theorem's "internally convergent" hypotheses. Take J = all of it
   (convex). R_J's events, applied then compensated by rho_J, do not commute at an R_J-valid
   state, so R_J does not satisfy CC (CC1 fails, in the guarded reading as well). *)
Definition au_t0 : nat -> bool * nat := toF (bool * nat) (false, 0) au_s0.
Local Notation au_f := (pf (bool * nat) bool nat snd pair src2 au_G).
Local Notation au_applyJ := (applyJ (bool * nat) au_f sp_rho cev ce_reg ce_sig [0; 1] all_true).

Theorem collapse_a_refuted :
  PaperTree (bool * nat) bool nat fst snd pair src2 au_G sp_valid sp_rho cev ce_reg ce_sig [0; 1]
    sp_rho au_Phi /\
  Convex src2 all_true /\
  Inv (bool * nat) sp_valid au_t0 /\ ConsJ (bool * nat) au_f [0; 1] all_true au_t0 /\
  au_applyJ CSell (au_applyJ CRecall au_t0) 1 <> au_applyJ CRecall (au_applyJ CSell au_t0) 1.
Proof.
  split; [exact au_paper |]. split; [| split; [| split]].
  - intros u m w _ _ Hm. discriminate Hm.
  - intros [| [| k]]; simpl; [exact I | lia | exact I].
  - intros j Hj. simpl in Hj. destruct Hj as [<- | [<- | []]]; reflexivity.
  - vm_compute. discriminate.
Qed.

(* thm:collapse (b), import direction, with R_J's federal validity (member validities AND the
   internal morphism invariants, def:effreg): false. Registry 2 (outside J) feeds 0, and 1 copies
   0; J = {0, 1} is convex, every hypothesis of the model holds and M1 holds everywhere, but
   overwriting R_J's port 0 from a new source value breaks R_J's internal invariant 1 = 0. *)
Definition bi_src (j : nat) : list nat := match j with 0 => [2] | 1 => [0] | _ => [] end.
Definition bi_f (j : nat) (z : nat -> nat) (x : nat) : nat :=
  match j with 0 => z 2 | 1 => z 0 | _ => x end.
Definition tt_valid (_ : nat) (_ : nat) : Prop := True.
Definition id_rho (_ : nat) (x : nat) : nat := x.
Definition j01 (v : nat) : bool := Nat.leb v 1.
Definition u_reg (_ : unit) : nat := 2.
Definition u_sig (_ : unit) (x : nat) : nat := x.

Lemma bi_common : Common nat bi_src bi_f tt_valid id_rho unit u_reg u_sig [2; 0; 1].
Proof.
  constructor.
  - intros [| [| [| j]]] z1 z2 x H; simpl; try reflexivity; apply H; simpl; tauto.
  - simpl. intuition lia.
  - intros. exact I.
  - intros [| [| [| j]]] z z' x _ _ _; reflexivity.
  - intros. reflexivity.
  - intros. exact I.
  - intros []. simpl. tauto.
Qed.

Theorem collapse_b_import_refuted :
  Common nat bi_src bi_f tt_valid id_rho unit u_reg u_sig [2; 0; 1] /\ Convex bi_src j01 /\
  M1at nat bi_f tt_valid 0 /\
  ~ (forall t y, Inv nat tt_valid t -> ConsJ nat bi_f [2; 0; 1] j01 t -> tt_valid 2 y ->
       FedJ nat bi_f tt_valid [2; 0; 1] j01 (fstep nat bi_f (upd nat t 2 y) 0)).
Proof.
  split; [exact bi_common |]. split; [| split].
  - intros u m w _ _ Hm P1 _. destruct (path_last bi_src u m P1) as [y Hy].
    destruct m as [| [| m]]; [discriminate Hm | discriminate Hm | destruct Hy].
  - intros z x _ _. exact I.
  - intros H. destruct (H (fun _ => 0) 5) as [_ Hc]; [intro; exact I | | exact I |].
    + intros j Hj. simpl in Hj. destruct Hj as [<- | [<- | []]]; reflexivity.
    + specialize (Hc 1 (or_intror (or_introl eq_refl))). vm_compute in Hc. discriminate Hc.
Qed.

(* thm:collapse (b), export direction, same reading: false. The export into 2 reads 0 and 1 and
   is valid exactly on states where 1 copies 0. Read from R_J's federally valid states it
   satisfies M1; in N (all locally valid source states) it does not. *)
Definition be_src (j : nat) : list nat := match j with 1 => [0] | 2 => [0; 1] | _ => [] end.
Definition be_f (j : nat) (z : nat -> nat) (x : nat) : nat :=
  match j with 1 => z 0 | 2 => if Nat.eqb (z 0) (z 1) then 0 else 1 | _ => x end.
Definition be_valid (j : nat) (x : nat) : Prop := match j with 2 => x = 0 | _ => True end.

Theorem collapse_b_export_refuted :
  M1expFed nat be_f be_valid [0; 1; 2] j01 2 /\ ~ M1at nat be_f be_valid 2.
Proof.
  split.
  - intros z x _ Hc _. simpl. assert (H1 := Hc 1 (or_intror (or_introl eq_refl))). simpl in H1.
    rewrite <- H1, Nat.eqb_refl. reflexivity.
  - intros H. specialize (H (fun k => if Nat.eqb k 1 then 1 else 0) 0).
    assert (Hz : Inv nat be_valid (fun k => if Nat.eqb k 1 then 1 else 0)).
    { intros [| [| [| k]]]; simpl; try exact I; reflexivity. }
    specialize (H Hz eq_refl). vm_compute in H. discriminate H.
Qed.

(* ========================================================================================= *)
(* PART 5. Port refinement (categorical paper, Section 4): input ports, sealed members, and    *)
(* the seam re-check.                                                                          *)
(* ========================================================================================= *)

Section Ports.
  Variable V : Type.
  Variable valid : nat -> V -> Prop.
  Variable rho : nat -> V -> V.
  Variable E : Type.
  Variable reg : E -> nat.
  Variable sig : E -> V -> V.
  Variable I : E -> E -> Prop.
  (* The verified sub-federation (src, f) and the network it is embedded in (src2, f2, o2). *)
  Variable src src2 : nat -> list nat.
  Variable f f2 : nat -> (nat -> V) -> V -> V.
  Variable o2 : list nat.
  Variable inJ port : nat -> bool.
  Hypothesis Hport : forall p, port p = true -> inJ p = true.
  (* The embedding drives only ports: every sealed member keeps its sources and its repair. *)
  Hypothesis Hsealed : forall j, inJ j = true -> port j = false ->
    src2 j = src j /\ forall z x, f2 j z x = f j z x.

  Definition sealed (j : nat) : bool := inJ j && negb (port j).

  (* The interior certificate transfers verbatim: C1 and C2 at sealed members are the same
     statements in the subsystem and in the embedding. *)
  Theorem port_c1_transfer : C1on V f valid E reg sig sealed <-> C1on V f2 valid E reg sig sealed.
  Proof.
    assert (Hf : forall e z x, sealed (reg e) = true -> f2 (reg e) z x = f (reg e) z x).
    { intros e z x H. unfold sealed in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply negb_true_iff in H2. apply (proj2 (Hsealed _ H1 H2)). }
    split; intros H e z z' b Hs Hz Hz' Hb Hc.
    - rewrite !Hf by exact Hs. rewrite Hf in Hc by exact Hs. exact (H e z z' b Hs Hz Hz' Hb Hc).
    - rewrite <- !Hf by exact Hs. rewrite <- Hf in Hc by exact Hs. exact (H e z z' b Hs Hz Hz' Hb Hc).
  Qed.

  Theorem port_c2_transfer : C2on V f valid E reg sig I sealed <-> C2on V f2 valid E reg sig I sealed.
  Proof.
    assert (Hf : forall e z x, sealed (reg e) = true -> f2 (reg e) z x = f (reg e) z x).
    { intros e z x H. unfold sealed in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply negb_true_iff in H2. apply (proj2 (Hsealed _ H1 H2)). }
    split; intros H e1 e2 z b Hs E12 Hi Hz Hb Hc.
    - rewrite !Hf by exact Hs. rewrite Hf in Hc by exact Hs. exact (H e1 e2 z b Hs E12 Hi Hz Hb Hc).
    - rewrite <- !Hf by exact Hs. rewrite <- Hf in Hc by exact Hs. exact (H e1 e2 z b Hs E12 Hi Hz Hb Hc).
  Qed.

  (* Assume-guarantee: the subsystem's certificate on its sealed interior, plus the seam re-check
     at the ports (C1, C2 for the port events under the embedding's repairs), is the full
     certificate of J inside the embedding; collapse_a_guarded then applies there. *)
  Theorem port_interior_certificate :
    C1on V f valid E reg sig sealed -> C1on V f2 valid E reg sig port ->
    C2on V f valid E reg sig I sealed -> C2on V f2 valid E reg sig I port ->
    C1on V f2 valid E reg sig inJ /\ C2on V f2 valid E reg sig I inJ.
  Proof.
    intros A1 P1 A2 P2. apply port_c1_transfer in A1. apply port_c2_transfer in A2. split.
    - intros e z z' b HJ. destruct (port (reg e)) eqn:Hp; [apply P1; exact Hp |].
      apply A1. unfold sealed. rewrite HJ, Hp. reflexivity.
    - intros e1 e2 z b HJ. destruct (port (reg e1)) eqn:Hp; [apply P2; exact Hp |].
      apply A2. unfold sealed. rewrite HJ, Hp. reflexivity.
  Qed.

  (* The interior guarantee survives embedding: in every normal form of the embedding (any
     federally valid state of it), every sealed member satisfies the subsystem's own repair
     equation, exactly as certified in isolation. *)
  Theorem port_interior_invariant :
    Common V src2 f2 valid rho E reg sig o2 ->
    forall t, Inv V valid t -> forall j, In j o2 -> sealed j = true ->
      N V f2 rho o2 t j = f j (N V f2 rho o2 t) (N V f2 rho o2 t j).
  Proof.
    intros HC2 t Ht j Hj Hs. unfold sealed in Hs. apply andb_true_iff in Hs. destruct Hs as [H1 H2].
    apply negb_true_iff in H2. rewrite <- (proj2 (Hsealed j H1 H2)).
    exact (N_cons _ _ _ _ _ _ _ _ _ HC2 t Ht j Hj).
  Qed.
End Ports.

(* A write to a sealed member must be rejected: J = {0, 1}, port 0, sealed 1 copying 0. An
   embedding in which registry 2 drives the sealed 1 is a well-formed federation, but in its
   normal form the subsystem's certified invariant (1 copies 0) fails. *)
Definition ps_src (j : nat) : list nat := match j with 1 => [0] | _ => [] end.
Definition ps_f (j : nat) (z : nat -> nat) (x : nat) : nat := match j with 1 => z 0 | _ => x end.
Definition ps_src2 (j : nat) : list nat := match j with 1 => [2] | _ => [] end.
Definition ps_f2 (j : nat) (z : nat -> nat) (x : nat) : nat := match j with 1 => z 2 | _ => x end.
Definition ps_t (k : nat) : nat := if Nat.eqb k 2 then 7 else 0.

Theorem port_sealed_write_refuted :
  Common nat ps_src2 ps_f2 tt_valid id_rho unit u_reg u_sig [0; 2; 1] /\
  N nat ps_f2 id_rho [0; 2; 1] ps_t 1 <>
    ps_f 1 (N nat ps_f2 id_rho [0; 2; 1] ps_t) (N nat ps_f2 id_rho [0; 2; 1] ps_t 1).
Proof.
  split.
  - constructor.
    + intros [| [| j]] z1 z2 x H; simpl; try reflexivity. apply H. simpl. tauto.
    + simpl. intuition lia.
    + intros. exact I.
    + intros [| [| j]] z z' x _ _ _; reflexivity.
    + intros. reflexivity.
    + intros. exact I.
    + intros []. simpl. tauto.
  - vm_compute. discriminate.
Qed.

(* ========================================================================================= *)
(* PART 6. Non-vacuity: a chain 0 -> 1 -> 2 with events on 0, J = {0, 1}, every hypothesis   *)
(* of PARTS 2 and 3 discharged, and the collapsed network computed.                            *)
(* ========================================================================================= *)

Definition ch_f (j : nat) (z : nat -> nat) (x : nat) : nat :=
  match j with 1 => z 0 | 2 => z 1 | _ => x end.
Definition b_reg (_ : bool) : nat := 0.
Definition b_ap (e : bool) (x : nat) : nat := if e then S x else S (S x).
Definition b_I (_ _ : bool) : Prop := True.
Local Notation ch_sg := (gsig nat id_rho bool b_reg b_ap).

Lemma chain_common : Common nat chain_src ch_f tt_valid id_rho bool b_reg ch_sg [0; 1; 2].
Proof.
  constructor.
  - intros [| [| [| j]]] z1 z2 x H; simpl; try reflexivity; apply H; simpl; tauto.
  - simpl. intuition lia.
  - intros. exact I.
  - intros [| [| [| j]]] z z' x _ _ _; reflexivity.
  - intros. reflexivity.
  - intros. exact I.
  - intros e. simpl. tauto.
Qed.

Lemma chain_c1 : C1 nat ch_f tt_valid bool b_reg ch_sg.
Proof. intros e z z' b _ _ _ _. reflexivity. Qed.

Lemma chain_c2 : C2 nat ch_f tt_valid bool b_reg ch_sg (Itot bool).
Proof. intros [] [] z b _ _ _ _ _; unfold gsig, id_rho, b_ap; simpl; lia. Qed.

Lemma chain_convex : Convex chain_src j01.
Proof.
  intros u m w _ _ Hm _ P. destruct (path_first chain_src m w P) as [x Hx].
  destruct x as [| [| [| x]]]; simpl in Hx; [destruct Hx | | | destruct Hx];
    destruct Hx as [<- | []]; discriminate Hm.
Qed.

Lemma range3 : forall k, In k [0; 1; 2] <-> k < 3.
Proof.
  intros k. split; [intros [<- | [<- | [<- | []]]]; lia |].
  intros H. destruct k as [| [| [| k]]]; simpl; try tauto. lia.
Qed.

Theorem chain_collapse_instance :
  Common nat chain_src ch_f tt_valid id_rho bool b_reg ch_sg [0; 1; 2] /\
  C1 nat ch_f tt_valid bool b_reg ch_sg /\ C2 nat ch_f tt_valid bool b_reg ch_sg (Itot bool) /\
  Convex chain_src j01 /\
  blockOrder chain_src j01 [0; 1; 2] = [0; 1; 2] /\ Contiguous j01 [0; 1; 2] /\
  orderC chain_src j01 [0; 1; 2] 0 = [0; 2] /\ srcC chain_src j01 [0; 1; 2] 0 2 = [0] /\
  (forall B, UN (step Bool.bool_dec (gapply nat bool b_reg b_ap 3 0)
                  (grhoC nat chain_src ch_f id_rho [0; 1; 2] 3 0 j01)
                  (gvalidC nat chain_src ch_f tt_valid [0; 1; 2] 3 0 j01)
                  (genabC nat chain_src ch_f tt_valid bool [0; 1; 2] 3 0 j01))
             ([0; 0; 0], B)).
Proof.
  split; [exact chain_common |]. split; [exact chain_c1 |]. split; [exact chain_c2 |].
  split; [exact chain_convex |]. split; [vm_compute; reflexivity |].
  split.
  { exists [], [0; 1], [2]. split; [reflexivity |].
    split; [intros v [<- | [<- | []]]; reflexivity |].
    split; [intros v [] | intros v [<- | []]; reflexivity]. }
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  intros B. apply (collapse_c_guarded_c1_c2 nat chain_src ch_f tt_valid id_rho bool b_reg b_ap
                     [0; 1; 2] 3 0 chain_common (fun _ _ => I) range3).
  - intros j k H. destruct j as [| [| [| j]]]; simpl in H; try destruct H; try (destruct H as [<- | []]); lia.
  - intros. exact I.
  - intros. left. exact I.
  - exact Nat.eq_dec.
  - exact chain_convex.
  - exact chain_c1.
  - exact chain_c2.
  - split; [reflexivity | split; [intros k; exact I |]].
    split; [| split]; intros j _; destruct j as [| [| [| j]]]; reflexivity.
Qed.
