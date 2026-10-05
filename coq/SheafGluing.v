(* SheafGluing.v: the positive sheaf assembly of the categorical paper (Cat section 5, "Convergence
   Certificates Form a Sheaf", prop:gluing), mechanized on a concrete finite site with no category
   theory library. Axiom-free.

   The site. Registries are indexed by nat. An open set is a sub-federation, a finite list U of
   registries; a cover of W is a finite list C of sub-federations whose union (concat C) is W.

   The presheaf of consistent states. A state is s : nat -> V; a section over U is a state that is
   consistent on U, read only through U: every registry of U holds a normal form (InImage (rho i)),
   and every target B whose constraint lies inside U (B in U and src B included in U: the rule's
   footprint lies in U, as the paper's presheaf says) has its shared component equal to its
   resolver value (Sec). Sections are compared on U only (Agree U), so a section over U is a state
   up to agreement on U. Restriction to U' included in U is the identity on states (sec_restrict).
   R1 (source-determinacy: a resolver reads only its sources) makes Sec U depend on the values in U
   alone, so that F is a presheaf of U-states (sec_local); without R1 it need not be (r1_failure,
   last conjunct).

   Results (plain statements).
   - separation: two states that restrict to the same sections on every member of a cover agree on
     the union. No hypothesis.
   - gluing, sheaf_condition: under R1, if the cover REFINES the constraints (every target whose
     constraint lies inside the union has its whole footprint, the target and all its sources, inside
     one member; Refines), then a family of sections over the members that agree on the overlaps
     (Compatible) glues (glue) to a section over the union that restricts to each of them, unique on
     the union by separation. Refines asks nothing of the overlaps themselves: in the chain instance
     the overlap {1} contains no constraint (chain_glues).
   - sheaf_exact: on a refining cover, a family is the restriction of a global section iff it is
     compatible and consists of local sections.
   - gluing_iff_local_global: for fixed data under R1, gluing holds on a cover C iff every state
     whose restriction to each member of C is a section is a section over the union.
   - sheaf_iff_refines (exact, uniform in the data): gluing holds on C for EVERY federation on the
     graph satisfying R1 iff C refines the constraints. Qualifier in the statement: V inhabited and
     two distinct shared values (the refuting federation needs them).
   - Counterexamples, each breaking one hypothesis: triangle_fails (Refines broken: an edge 0 -> 2
     lies in no member although the two members overlap), r1_failure (R1 broken: Refines holds,
     the family is compatible, no global section exists, and F is not a presheaf of U-states),
     gluing_cex_overlap (Cohomology.v's gluing_order_dependent: compatibility of CERTIFICATES on the
     overlap broken, two writers of one variable; the state-level valid sets agree).

   Certificates (the normalizers). On the CategoricalBridge.v model (stepN, run over a topological
   order, resolvers reading the source values in order, so R1 holds by construction: resL_R1), the
   certificate of U is rhoU o U = run over the members of U in o's order, registries outside U read
   as external inputs.
   - cert_restrict_closed: if U is closed under sources, the global normalizer restricted to U is
     U's certificate: run o s = rhoU o U s on U, for every order o. No other hypothesis.
   - cert_restrict: for EVERY U, run o s = rhoU o U (patch U s (run o s)) on U: the global normal
     form on U is U's certificate run on the state whose external inputs are replaced by their
     global normal forms (o topological). cert_pointwise is the case U = [i].
   - cert_restrict_iff (exact): in a source-closed federation o, the restriction equation
     run o s = rhoU o U s on U holds for every data satisfying Theorem 1's hypotheses (idempotence,
     the lens law, SC) iff U is closed under sources.
   - sec_iff_LF, cert_retraction: on a closed U, the sections are CategoricalBridge's L_F of U's
     order, and under idempotence, the lens law and SC (the corrected Theorem 1 hypothesis) U's
     certificate lands in the sections and fixes them (cat_thm_one_sound, cat_thm_one_complete).
   - cert_glue, cert_sheaf: on a cover by closed members, the certificates form a compatible family
     of local sections over a refining cover, their gluing is the certificate of the union (and the
     global normalizer there), it lands in the sections over the union and fixes them.
   - cert_needs_sc: with M1 (validity preservation) in place of SC, the certificate of a closed
     sub-federation misses its sections (CategoricalBridge's cat_thm_one_m1_counterexample).
   - collapse_restrict: Collapse.v's convex form. For a convex J, the federated normal form on J is
     rho_J run after the upstream block P (from collapse_nf_factor and collapse_nf_agree): convexity
     is what makes the patched inputs of cert_restrict computable before J as one block.

   The boundary (what is not claimed here). The sheaf condition for certificates is proved on covers
   by sub-federations closed under sources. On other covers a sub-federation's certificate depends on
   external inputs, and only the relative restriction equation (cert_restrict) is proved: no sheaf
   condition for these relative certificates is stated. The site is the registry-level one (open sets
   are sets of registries); the paper's variable-level site, where two subsystems may write one
   variable, enters only through gluing_cex_overlap, since a federation has one writer per registry
   (a multi-source target merges its writers by its resolver). The monotone-overlap regime (cycles,
   least fixed points) is not covered: everything here is acyclic. The event layer (C1, C2) is not
   part of the certificates.

   Non-vacuity: chain_glues (three-registry chain 0 -> 1 -> 2 covered by {0,1} and {1,2}),
   triangle_fails, r1_failure, sheaf_iff_refines_instance, vs_cert_sheaf (closed cover {0,1},
   {0,2} of a fork 0 -> 1, 0 -> 2, computing the glued certificate), chain_cert_nonclosed,
   cert_restrict_iff_instance, collapse_restrict_instance. *)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Require Import NC.Categorical NC.FederationOrder NC.CategoricalBridge.
Require NC.Cohomology NC.FederationEvents NC.Collapse.

(* ========================================================================================= *)
(* Membership on finite lists of registries.                                                  *)
(* ========================================================================================= *)

Definition memb (k : nat) (l : list nat) : bool := existsb (Nat.eqb k) l.

Lemma memb_iff : forall k l, memb k l = true <-> In k l.
Proof.
  intros k l. unfold memb. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply Nat.eqb_eq in E. subst. exact Hx.
  - intro H. exists k. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma memb_false : forall k l, memb k l = false <-> ~ In k l.
Proof.
  intros k l. rewrite <- memb_iff. destruct (memb k l); split; intro H; try congruence; tauto.
Qed.

Lemma in_concat_ex : forall (C : list (list nat)) k, In k (concat C) -> exists U, In U C /\ In k U.
Proof.
  induction C as [| U C IH]; simpl; intros k H; [destruct H |].
  apply in_app_or in H. destruct H as [H | H].
  - exists U. split; [left; reflexivity | exact H].
  - destruct (IH k H) as [U' [H1 H2]]. exists U'. split; [right; exact H1 | exact H2].
Qed.

Lemma in_concat_intro : forall (C : list (list nat)) U k, In U C -> In k U -> In k (concat C).
Proof.
  induction C as [| U' C IH]; simpl; intros U k HU Hk; [destruct HU |].
  apply in_or_app. destruct HU as [E | HU].
  - left. subst. exact Hk.
  - right. exact (IH U k HU Hk).
Qed.

(* ========================================================================================= *)
(* PART 1. Families over a cover, gluing of functions, separation.                            *)
(* ========================================================================================= *)

Section Glue.
  Context {V : Type}.

  (* Two states agree on U: they are the same section over U. *)
  Definition Agree (U : list nat) (s t : nat -> V) : Prop := forall k, In k U -> s k = t k.

  (* A family over a cover: one state per member, each read on its member. *)
  Definition Family : Type := list (list nat * (nat -> V)).
  Definition cover (fam : Family) : list (list nat) := map fst fam.
  Definition Union (C : list (list nat)) : list nat := concat C.

  (* Agreement on overlaps. *)
  Definition Compatible (fam : Family) : Prop :=
    forall U s U' s', In (U, s) fam -> In (U', s') fam ->
      forall k, In k U -> In k U' -> s k = s' k.

  (* t restricts to every member of the family. *)
  Definition Restricts (fam : Family) (t : nat -> V) : Prop :=
    forall U s, In (U, s) fam -> Agree U t s.

  (* The glued state: on k, the value of the first member containing k (d outside the union). *)
  Fixpoint glue (fam : Family) (d : nat -> V) (k : nat) : V :=
    match fam with
    | [] => d k
    | (U, s) :: r => if memb k U then s k else glue r d k
    end.

  Lemma in_union : forall fam k, In k (Union (cover fam)) -> exists U s, In (U, s) fam /\ In k U.
  Proof.
    intros fam k H. destruct (in_concat_ex (cover fam) k H) as [U [HU Hk]].
    unfold cover in HU. apply in_map_iff in HU. destruct HU as [[U' s] [E Hin]]. simpl in E.
    subst U'. exists U, s. split; assumption.
  Qed.

  Lemma compatible_tail : forall a fam, Compatible (a :: fam) -> Compatible fam.
  Proof. intros a fam H U s U' s' H1 H2. apply H; right; assumption. Qed.

  Theorem glue_restricts : forall fam d, Compatible fam -> Restricts fam (glue fam d).
  Proof.
    induction fam as [| [U0 s0] fam IH]; intros d Hc U s Hin k Hk; [destruct Hin |].
    simpl. destruct (memb k U0) eqn:E.
    - apply memb_iff in E. destruct Hin as [Heq | Hin].
      + injection Heq as E1 E2. subst. reflexivity.
      + exact (Hc U0 s0 U s (or_introl eq_refl) (or_intror Hin) k E Hk).
    - destruct Hin as [Heq | Hin].
      + injection Heq as E1 E2. subst. apply memb_false in E. contradiction.
      + exact (IH d (compatible_tail _ _ Hc) U s Hin k Hk).
  Qed.

  (* A family that is the restriction of one state is compatible. *)
  Lemma restricts_compatible : forall fam t, Restricts fam t -> Compatible fam.
  Proof.
    intros fam t H U s U' s' H1 H2 k Hk Hk'. rewrite <- (H U s H1 k Hk). exact (H U' s' H2 k Hk').
  Qed.

  (* Separation: sections over the union are determined by their restrictions. *)
  Theorem separation : forall fam t1 t2, Restricts fam t1 -> Restricts fam t2 ->
    Agree (Union (cover fam)) t1 t2.
  Proof.
    intros fam t1 t2 H1 H2 k Hk. destruct (in_union fam k Hk) as [U [s [Hin HkU]]].
    rewrite (H1 U s Hin k HkU), (H2 U s Hin k HkU). reflexivity.
  Qed.
End Glue.

(* ========================================================================================= *)
(* PART 2. The presheaf of consistent states and the sheaf condition.                         *)
(* ========================================================================================= *)

Section States.
  Context {V Sh : Type}.
  Variable src : nat -> list nat.          (* the sources of each registry *)
  Variable rho : nat -> V -> V.            (* local normalizer; its image is the valid set *)
  Variable get : nat -> V -> Sh.           (* a target's shared component *)
  Variable res : nat -> (nat -> V) -> Sh.  (* a target's resolver, reading the federated state *)

  (* R1, source-determinacy: a resolver reads only its sources. *)
  Definition R1 : Prop :=
    forall B s t, (forall k, In k (src B) -> s k = t k) -> res B s = res B t.

  (* B's constraint lies inside U: B is a target and its footprint (B and its sources) is in U. *)
  Definition Internal (U : list nat) (B : nat) : Prop := In B U /\ src B <> [] /\ incl (src B) U.

  (* F(U): states consistent on U. *)
  Definition Sec (U : list nat) (s : nat -> V) : Prop :=
    (forall i, In i U -> InImage (rho i) (s i)) /\
    (forall B, Internal U B -> get B (s B) = res B s).

  Definition LocalSections (fam : @Family V) : Prop := forall U s, In (U, s) fam -> Sec U s.

  (* The cover refines the constraints: every constraint inside the union lies inside a member. *)
  Definition Refines (C : list (list nat)) : Prop :=
    forall B, Internal (Union C) B -> exists U, In U C /\ Internal U B.

  (* Restriction maps: a section over U restricts to a section over any U' included in U. *)
  Theorem sec_restrict : forall U U' s, incl U' U -> Sec U s -> Sec U' s.
  Proof.
    intros U U' s Hi [Hn He]. split.
    - intros i H. apply Hn. apply Hi. exact H.
    - intros B [HB [Hs Hsrc]]. apply He. split; [apply Hi; exact HB | split; [exact Hs |]].
      intros k Hk. apply Hi. apply Hsrc. exact Hk.
  Qed.

  (* Under R1, F(U) depends on the values in U only: F is a presheaf of U-states. *)
  Theorem sec_local : R1 -> forall U s t, Agree U s t -> Sec U s -> Sec U t.
  Proof.
    intros HR U s t Hst [Hn He]. split.
    - intros i Hi. rewrite <- (Hst i Hi). apply Hn. exact Hi.
    - intros B HB. pose proof (He B HB) as E. destruct HB as [HBU [_ Hsrc]].
      rewrite <- (Hst B HBU), E. apply HR. intros k Hk. apply Hst. apply Hsrc. exact Hk.
  Qed.

  (* Gluing: a compatible family of local sections over a refining cover glues to a section over
     the union restricting to each member. *)
  Theorem gluing : R1 -> forall fam d, Compatible fam -> LocalSections fam -> Refines (cover fam) ->
    Sec (Union (cover fam)) (glue fam d) /\ Restricts fam (glue fam d).
  Proof.
    intros HR fam d Hc Hl Hr. pose proof (glue_restricts fam d Hc) as Hg.
    assert (Hsec : forall U s, In (U, s) fam -> Sec U (glue fam d)).
    { intros U s Hin. apply (sec_local HR U s); [| exact (Hl U s Hin)].
      intros k Hk. symmetry. exact (Hg U s Hin k Hk). }
    split; [split | exact Hg].
    - intros i Hi. destruct (in_union fam i Hi) as [U [s [Hin HiU]]].
      exact (proj1 (Hsec U s Hin) i HiU).
    - intros B HB. destruct (Hr B HB) as [U [HU HBU]].
      unfold cover in HU. apply in_map_iff in HU. destruct HU as [[U' s] [E Hin]]. simpl in E.
      subst U'. exact (proj2 (Hsec U s Hin) B HBU).
  Qed.

  (* The sheaf condition: existence (gluing) and uniqueness on the union (separation). *)
  Theorem sheaf_condition : R1 -> forall fam (d : nat -> V), Compatible fam -> LocalSections fam ->
    Refines (cover fam) ->
    (exists t, Sec (Union (cover fam)) t /\ Restricts fam t) /\
    (forall t1 t2, Restricts fam t1 -> Restricts fam t2 -> Agree (Union (cover fam)) t1 t2).
  Proof.
    intros HR fam d Hc Hl Hr. split.
    - exists (glue fam d). exact (gluing HR fam d Hc Hl Hr).
    - exact (separation fam).
  Qed.

  (* Exact form on a refining cover: a family is the restriction of a global section iff it is a
     compatible family of local sections. *)
  Theorem sheaf_exact : R1 -> forall fam, Refines (cover fam) -> forall d : nat -> V,
    (exists t, Sec (Union (cover fam)) t /\ Restricts fam t) <->
    (Compatible fam /\ LocalSections fam).
  Proof.
    intros HR fam Hr d. split.
    - intros [t [Ht Hres]]. split; [exact (restricts_compatible fam t Hres) |].
      intros U s Hin. apply (sec_local HR U t); [exact (Hres U s Hin) |].
      apply (sec_restrict (Union (cover fam))); [| exact Ht].
      intros k Hk. apply (in_concat_intro (cover fam) U k); [| exact Hk].
      unfold cover. apply in_map_iff. exists (U, s). split; [reflexivity | exact Hin].
    - intros [Hc Hl]. exists (glue fam d). exact (gluing HR fam d Hc Hl Hr).
  Qed.

  (* Exact form for fixed data, any cover: gluing holds iff local consistency on every member
     implies consistency on the union. *)
  Theorem gluing_iff_local_global : R1 -> forall C,
    (forall fam d, cover fam = C -> Compatible fam -> LocalSections fam ->
       Sec (Union C) (glue fam d)) <->
    (forall t, (forall U, In U C -> Sec U t) -> Sec (Union C) t).
  Proof.
    intros HR C. split.
    - intros H t Ht.
      set (fam := map (fun U => (U, t)) C).
      assert (Hcov : cover fam = C).
      { unfold fam, cover. rewrite map_map. simpl. apply map_id. }
      assert (Hc : Compatible fam).
      { intros U s U' s' H1 H2 k _ _. unfold fam in H1, H2. apply in_map_iff in H1, H2.
        destruct H1 as [U1 [E1 _]]. destruct H2 as [U2 [E2 _]].
        injection E1 as _ E1. injection E2 as _ E2. subst s s'. reflexivity. }
      assert (Hl : LocalSections fam).
      { intros U s Hin. unfold fam in Hin. apply in_map_iff in Hin. destruct Hin as [U1 [E1 HU1]].
        injection E1 as E1 E2. subst U1 s. exact (Ht U HU1). }
      apply (sec_local HR (Union C) (glue fam t)); [| exact (H fam t Hcov Hc Hl)].
      rewrite <- Hcov. apply separation; [exact (glue_restricts fam t Hc) |].
      intros U s Hin k _. unfold fam in Hin. apply in_map_iff in Hin. destruct Hin as [U1 [E1 _]].
      injection E1 as _ E1. subst s. reflexivity.
    - intros H fam d Hcov Hc Hl. subst C. apply H. intros U HU.
      unfold cover in HU. apply in_map_iff in HU. destruct HU as [[U' s] [E Hin]]. simpl in E.
      subst U'. apply (sec_local HR U s); [| exact (Hl U s Hin)].
      intros k Hk. symmetry. exact (glue_restricts fam d Hc U s Hin k Hk).
  Qed.
End States.

(* ----- the exact, data-uniform form ----- *)

Definition GluesFor {V Sh : Type} (src : nat -> list nat) (rho : nat -> V -> V)
  (get : nat -> V -> Sh) (res : nat -> (nat -> V) -> Sh) (C : list (list nat)) : Prop :=
  forall (fam : @Family V) d, cover fam = C -> Compatible fam ->
    LocalSections src rho get res fam -> Sec src rho get res (Union C) (glue fam d).

Definition internalb (src : nat -> list nat) (U : list nat) (B : nat) : bool :=
  memb B U && negb (match src B with [] => true | _ => false end) &&
  forallb (fun k => memb k U) (src B).

Lemma internalb_iff : forall src U B, internalb src U B = true <-> Internal src U B.
Proof.
  intros src U B. unfold internalb, Internal. rewrite !andb_true_iff, forallb_forall, memb_iff.
  split.
  - intros [[HB Hs] Hf]. split; [exact HB | split].
    + destruct (src B); [discriminate Hs | discriminate].
    + intros k Hk. apply memb_iff. exact (Hf k Hk).
  - intros [HB [Hs Hf]]. split; [split; [exact HB |] |].
    + destruct (src B); [contradiction Hs; reflexivity | reflexivity].
    + intros k Hk. apply memb_iff. exact (Hf k Hk).
Qed.

(* Gluing holds on C for every federation on the graph satisfying R1 iff C refines the
   constraints. The refuting federation: valid sets everything, and one constant constraint that
   no state satisfies, on the target whose footprint lies in no member. *)
Theorem sheaf_iff_refines :
  forall (V Sh : Type) (v0 : V) (a b : Sh), a <> b ->
  forall (src : nat -> list nat) (C : list (list nat)),
    (forall (rho : nat -> V -> V) (get : nat -> V -> Sh) (res : nat -> (nat -> V) -> Sh),
        R1 src res -> GluesFor src rho get res C) <-> Refines src C.
Proof.
  intros V Sh v0 a b Hab src C. split.
  - intros H B HB.
    destruct (existsb (fun U => internalb src U B) C) eqn:E.
    + apply existsb_exists in E. destruct E as [U [HU Hi]].
      exists U. split; [exact HU | apply internalb_iff; exact Hi].
    + exfalso.
      set (res := fun (B' : nat) (_ : nat -> V) => if Nat.eqb B' B then b else a).
      set (fam := map (fun U => (U, fun _ : nat => v0)) C).
      assert (Hcov : cover fam = C).
      { unfold fam, cover. rewrite map_map. simpl. apply map_id. }
      assert (HR : R1 src res) by (intros B' s t _; reflexivity).
      assert (Hc : Compatible fam).
      { intros U s U' s' H1 H2 k _ _. unfold fam in H1, H2. apply in_map_iff in H1, H2.
        destruct H1 as [U1 [E1 _]]. destruct H2 as [U2 [E2 _]].
        injection E1 as _ E1. injection E2 as _ E2. subst s s'. reflexivity. }
      assert (Hl : LocalSections src (fun _ x => x) (fun _ _ => a) res fam).
      { intros U s Hin. unfold fam in Hin. apply in_map_iff in Hin.
        destruct Hin as [U1 [E1 HU1]]. injection E1 as E1 E2. subst U s. split.
        - intros i _. exists v0. reflexivity.
        - intros B' HB'. unfold res. destruct (Nat.eqb_spec B' B) as [-> | Hne]; [| reflexivity].
          exfalso. assert (Hx : existsb (fun U => internalb src U B) C = true).
          { apply existsb_exists. exists U1. split; [exact HU1 | apply internalb_iff; exact HB']. }
          congruence. }
      pose proof (H (fun _ x => x) (fun _ _ => a) res HR fam (fun _ => v0) Hcov Hc Hl) as Hs.
      destruct Hs as [_ He]. specialize (He B HB). unfold res in He. cbv beta in He.
      rewrite Nat.eqb_refl in He. exact (Hab He).
  - intros Hr rho get res HR fam d Hcov Hc Hl. subst C.
    exact (proj1 (gluing src rho get res HR fam d Hc Hl Hr)).
Qed.

(* ========================================================================================= *)
(* PART 3. State-level instances and counterexamples.                                         *)
(* ========================================================================================= *)

(* The three-registry chain 0 -> 1 -> 2: registry 1 copies 0, registry 2 copies 1; every value
   must be a clamp3 normal form (at most 3). *)
Definition ch_src (i : nat) : list nat := match i with 1 => [0] | 2 => [1] | _ => [] end.
Definition ch_rho (_ : nat) (x : nat) : nat := clamp3 x.
Definition ch_get (_ : nat) (v : nat) : nat := v.
Definition ch_res (B : nat) (s : nat -> nat) : nat := match B with 1 => s 0 | 2 => s 1 | _ => 0 end.
Definition ch_fam : @Family nat := [([0; 1], fun _ => 2); ([1; 2], fun _ => 2)].

Lemma ch_R1 : R1 ch_src ch_res.
Proof.
  intros B s t H. destruct B as [| [| [| B]]]; simpl; try reflexivity; apply H; simpl; auto.
Qed.

Lemma chain_refines : Refines ch_src [[0; 1]; [1; 2]].
Proof.
  intros B [HB [Hs _]]. simpl in HB.
  destruct HB as [<- | [<- | [<- | [<- | []]]]].
  - contradiction Hs. reflexivity.
  - exists [0; 1]. split; [left; reflexivity |]. split; [simpl; tauto |].
    split; [discriminate |]. intros k [<- | []]. simpl. tauto.
  - exists [0; 1]. split; [left; reflexivity |]. split; [simpl; tauto |].
    split; [discriminate |]. intros k [<- | []]. simpl. tauto.
  - exists [1; 2]. split; [right; left; reflexivity |]. split; [simpl; tauto |].
    split; [discriminate |]. intros k [<- | []]. simpl. tauto.
Qed.

(* Non-vacuity of the gluing theorem: the chain covered by two overlapping pairs. The overlap {1}
   contains no constraint, so Refines asks nothing of overlaps; the glued section is all 2, and the
   union's consistency is a genuine constraint (the identity state is not a section). *)
Theorem chain_glues :
  R1 ch_src ch_res /\ Compatible ch_fam /\ LocalSections ch_src ch_rho ch_get ch_res ch_fam /\
  Refines ch_src (cover ch_fam) /\
  (forall B, ~ Internal ch_src [1] B) /\
  Sec ch_src ch_rho ch_get ch_res [0; 1; 1; 2] (glue ch_fam (fun _ => 0)) /\
  Restricts ch_fam (glue ch_fam (fun _ => 0)) /\
  (forall k, In k [0; 1; 2] -> glue ch_fam (fun _ => 0) k = 2) /\
  ~ Sec ch_src ch_rho ch_get ch_res [0; 1; 1; 2] (fun k => k).
Proof.
  assert (Hc : Compatible ch_fam).
  { intros U s U' s' H1 H2 k _ _.
    destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
      injection E1 as E1a E1b; injection E2 as E2a E2b; subst; reflexivity. }
  assert (Hl : LocalSections ch_src ch_rho ch_get ch_res ch_fam).
  { intros U s [E | [E | []]]; injection E as Ea Eb; subst; split;
      try (intros i _; exists 2; reflexivity);
      intros B [HB [Hs _]]; simpl in HB; destruct HB as [<- | [<- | []]];
      try (contradiction Hs; reflexivity); reflexivity. }
  pose proof (gluing ch_src ch_rho ch_get ch_res ch_R1 ch_fam (fun _ => 0) Hc Hl chain_refines)
    as [Hs Hr].
  split; [exact ch_R1 |]. split; [exact Hc |]. split; [exact Hl |]. split; [exact chain_refines |].
  split; [| split; [exact Hs | split; [exact Hr | split]]].
  - intros B [HB [_ Hinc]]. destruct HB as [<- | []].
    destruct (Hinc 0 (or_introl eq_refl)) as [E | []]. discriminate E.
  - intros k [<- | [<- | [<- | []]]]; reflexivity.
  - intros [_ He].
    assert (Hi : Internal ch_src [0; 1; 1; 2] 1).
    { split; [simpl; tauto | split; [discriminate |]]. intros k [<- | []]. simpl. tauto. }
    specialize (He 1 Hi). discriminate He.
Qed.

(* Refines broken. The triangle 0 -> 1, 0 -> 2, 1 -> 2 (registry 2's resolver adds its two
   sources) covered by {0,1} and {1,2}: the members overlap at 1, the family is compatible and
   locally consistent, but the edge 0 -> 2 lies in no member and no global section restricts to the
   family. *)
Definition tr_src (i : nat) : list nat := match i with 1 => [0] | 2 => [0; 1] | _ => [] end.
Definition tr_res (B : nat) (s : nat -> nat) : nat :=
  match B with 1 => s 0 | 2 => s 0 + s 1 | _ => 0 end.
Definition tr_fam : @Family nat := [([0; 1], fun _ => 1); ([1; 2], fun _ => 1)].

Theorem triangle_fails :
  R1 tr_src tr_res /\ Compatible tr_fam /\ LocalSections tr_src ch_rho ch_get tr_res tr_fam /\
  In 1 [0; 1] /\ In 1 [1; 2] /\
  ~ Refines tr_src (cover tr_fam) /\
  ~ (exists t, Sec tr_src ch_rho ch_get tr_res (Union (cover tr_fam)) t /\ Restricts tr_fam t).
Proof.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros B s t H. destruct B as [| [| [| B]]]; simpl; try reflexivity.
    + apply H. simpl. auto.
    + rewrite (H 0), (H 1); simpl; auto.
  - intros U s U' s' H1 H2 k _ _.
    destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
      injection E1 as E1a E1b; injection E2 as E2a E2b; subst; reflexivity.
  - intros U s [E | [E | []]]; injection E as Ea Eb; subst; split;
      try (intros i _; exists 1; reflexivity);
      intros B [HB [Hs Hinc]]; simpl in HB; destruct HB as [<- | [<- | []]];
      try (contradiction Hs; reflexivity); try reflexivity;
      destruct (Hinc 0 (or_introl eq_refl)) as [E | [E | []]]; discriminate E.
  - simpl. tauto.
  - simpl. tauto.
  - intro H.
    assert (Hi : Internal tr_src (Union (cover tr_fam)) 2).
    { split; [simpl; tauto | split; [discriminate |]].
      intros k [<- | [<- | []]]; simpl; tauto. }
    destruct (H 2 Hi) as [U [HU [HBU [_ Hinc]]]]. simpl in HU.
    destruct HU as [<- | [<- | []]].
    + destruct HBU as [E | [E | []]]; discriminate E.
    + destruct (Hinc 0 (or_introl eq_refl)) as [E | [E | []]]; discriminate E.
  - intros [t [[_ He] Hr]].
    assert (Hi : Internal tr_src (Union (cover tr_fam)) 2).
    { split; [simpl; tauto | split; [discriminate |]].
      intros k [<- | [<- | []]]; simpl; tauto. }
    specialize (He 2 Hi). unfold ch_get, tr_res in He.
    rewrite (Hr [0; 1] (fun _ => 1) (or_introl eq_refl) 0 (or_introl eq_refl)) in He.
    rewrite (Hr [0; 1] (fun _ => 1) (or_introl eq_refl) 1 (or_intror (or_introl eq_refl))) in He.
    rewrite (Hr [1; 2] (fun _ => 1) (or_intror (or_introl eq_refl)) 2
               (or_intror (or_introl eq_refl))) in He.
    discriminate He.
Qed.

(* R1 broken. The chain graph, but registry 2's resolver reads registry 0, which is not one of its
   declared sources. The cover {0,1}, {1,2} refines the declared constraints and the family is
   compatible and locally consistent, yet no global section restricts to it; and F is not a
   presheaf of U-states: two states agreeing on {1,2} differ in being sections over {1,2}. *)
Definition bad_res (B : nat) (s : nat -> nat) : nat := match B with 1 => s 0 | 2 => s 0 | _ => 0 end.
Definition id_rho (_ : nat) (x : nat) : nat := x.
Definition bad_sb (k : nat) : nat := match k with 1 => 0 | _ => 7 end.
Definition bad_sb' (k : nat) : nat := match k with 0 => 0 | 1 => 0 | _ => 7 end.
Definition bad_fam : @Family nat := [([0; 1], fun _ => 0); ([1; 2], bad_sb)].

Theorem r1_failure :
  ~ R1 ch_src bad_res /\ Refines ch_src (cover bad_fam) /\ Compatible bad_fam /\
  LocalSections ch_src id_rho ch_get bad_res bad_fam /\
  ~ (exists t, Sec ch_src id_rho ch_get bad_res (Union (cover bad_fam)) t /\ Restricts bad_fam t) /\
  (Agree [1; 2] bad_sb bad_sb' /\ Sec ch_src id_rho ch_get bad_res [1; 2] bad_sb /\
   ~ Sec ch_src id_rho ch_get bad_res [1; 2] bad_sb').
Proof.
  assert (Hi2 : forall U, In 1 U -> In 2 U -> Internal ch_src U 2).
  { intros U H1 H2. split; [exact H2 | split; [discriminate |]]. intros k [<- | []]. exact H1. }
  assert (Hsb : Sec ch_src id_rho ch_get bad_res [1; 2] bad_sb).
  { split; [intros i _; exists (bad_sb i); reflexivity |].
    intros B [HB [Hs Hinc]]. destruct HB as [<- | [<- | []]]; [| reflexivity].
    destruct (Hinc 0 (or_introl eq_refl)) as [E | [E | []]]; discriminate E. }
  split; [| split; [| split; [| split; [| split]]]].
  - intro H. assert (E := H 2 bad_sb bad_sb').
    assert (E' : bad_res 2 bad_sb = bad_res 2 bad_sb') by (apply E; intros k [<- | []]; reflexivity).
    discriminate E'.
  - exact chain_refines.
  - intros U s U' s' H1 H2 k Hk Hk'.
    destruct H1 as [E1 | [E1 | []]]; destruct H2 as [E2 | [E2 | []]];
      injection E1 as E1a E1b; injection E2 as E2a E2b; subst; try reflexivity;
      simpl in Hk, Hk'; destruct Hk as [<- | [<- | []]]; destruct Hk' as [E | [E | []]];
      try discriminate E; reflexivity.
  - intros U s [E | [E | []]]; injection E as Ea Eb; subst; [| exact Hsb].
    split; [intros i _; exists 0; reflexivity |].
    intros B [HB [Hs _]]. destruct HB as [<- | [<- | []]]; [contradiction Hs |]; reflexivity.
  - intros [t [[_ He] Hr]].
    specialize (He 2 (Hi2 (Union (cover bad_fam)) ltac:(simpl; tauto) ltac:(simpl; tauto))).
    unfold ch_get, bad_res in He.
    rewrite (Hr [0; 1] (fun _ => 0) (or_introl eq_refl) 0 (or_introl eq_refl)) in He.
    rewrite (Hr [1; 2] bad_sb (or_intror (or_introl eq_refl)) 2
               (or_intror (or_introl eq_refl))) in He.
    discriminate He.
  - split; [intros k [<- | [<- | []]]; reflexivity |]. split; [exact Hsb |].
    intros [_ He]. specialize (He 2 (Hi2 [1; 2] ltac:(simpl; tauto) ltac:(simpl; tauto))).
    discriminate He.
Qed.

(* Non-vacuity of sheaf_iff_refines: its right side holds for the chain cover, so gluing holds
   there for every federation on the chain graph satisfying R1. *)
Theorem sheaf_iff_refines_instance :
  forall (rho : nat -> nat -> nat) (get : nat -> nat -> nat) (res : nat -> (nat -> nat) -> nat),
    R1 ch_src res -> GluesFor ch_src rho get res [[0; 1]; [1; 2]].
Proof.
  exact (proj2 (sheaf_iff_refines nat nat 0 0 1 ltac:(discriminate) ch_src [[0; 1]; [1; 2]])
           chain_refines).
Qed.

(* Certificate compatibility on the overlap, broken: Cohomology.v's gluing counterexample. Two
   subsystems write one variable s in {0,1,2}. Their state sections on the overlap agree (the same
   valid set, the fixed points of rA and of rB), but their certificates (the normalizers) disagree
   on the overlap, so no certificate restricts to both, and the union is order-dependent. A
   federation has one writer per registry, so its certificates on a closed cover are always
   compatible (cert_glue below). *)
Theorem gluing_cex_overlap :
  (forall n, Cohomology.rA n = n <-> Cohomology.rB n = n) /\
  Cohomology.rA 1 <> Cohomology.rB 1 /\
  ~ (exists G : nat -> nat, forall n, G n = Cohomology.rA n /\ G n = Cohomology.rB n) /\
  Cohomology.rA (Cohomology.rB 1) <> Cohomology.rB (Cohomology.rA 1).
Proof.
  split; [| split; [| split]].
  - intro n. destruct n as [| [| [| n]]]; cbn; split; intro H;
      first [exact H | discriminate H | reflexivity].
  - exact Cohomology.disagree_as_normalizers.
  - intros [G HG]. destruct (HG 1) as [H1 H2]. rewrite H1 in H2. discriminate H2.
  - exact Cohomology.gluing_order_dependent.
Qed.

(* ========================================================================================= *)
(* PART 4. Certificates: the normalizers restrict and glue.                                   *)
(* ========================================================================================= *)

Lemma run_out_gen {W : Type} (f : nat -> (nat -> W) -> W -> W) :
  forall o t k, ~ In k o -> run f o t k = t k.
Proof.
  induction o as [| a o IH]; intros t k Hk; [reflexivity |].
  rewrite run_cons, IH by (intro H; apply Hk; right; exact H).
  apply step_other. intro E. apply Hk. left. symmetry. exact E.
Qed.

Section Topo.
  Variable src : nat -> list nat.

  Lemma topo_tail : forall a o, topo src (a :: o) -> topo src o.
  Proof.
    intros a o [Hnd Ht]. apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
    split; [exact Hnd |]. intros i k Hi Hk Hko.
    pose proof (Ht i k (or_intror Hi) Hk (or_intror Hko)) as P. simpl in P.
    destruct P as [[E _] | P]; [subst a; contradiction | exact P].
  Qed.

  Lemma topo_head_src : forall a o k, topo src (a :: o) -> In k (src a) -> ~ In k (a :: o).
  Proof.
    intros a o k [Hnd Ht] Hk Hin. pose proof (Ht a k (or_introl eq_refl) Hk Hin) as P. simpl in P.
    apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha _].
    destruct P as [[_ H] | P]; [exact (Ha H) | exact (Ha (prec_in_r _ _ _ P))].
  Qed.

  Lemma prec_irrefl : forall i o, NoDup o -> ~ prec i i o.
  Proof.
    intros i o. induction o as [| a o IH]; intros Hnd P; [exact P |].
    simpl in P. apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
    destruct P as [[E H] | P]; [subst a; exact (Ha H) | exact (IH Hnd P)].
  Qed.

  Lemma topo_self : forall o i, topo src o -> In i o -> ~ In i (src i).
  Proof. intros o i [Hnd Ht] Hi Hs. exact (prec_irrefl i o Hnd (Ht i i Hi Hs Hi)). Qed.

  Lemma nodup_filter_gen : forall (p : nat -> bool) o, NoDup o -> NoDup (filter p o).
  Proof.
    intros p. induction o as [| a o IH]; intros H; [constructor |].
    apply NoDup_cons_iff in H. destruct H as [Ha H]. simpl. destruct (p a); [| apply IH; exact H].
    constructor; [| apply IH; exact H]. intro Hin. apply filter_In in Hin. apply Ha. apply Hin.
  Qed.

  Lemma prec_filter : forall (p : nat -> bool) k i o,
    prec k i o -> p k = true -> p i = true -> prec k i (filter p o).
  Proof.
    intros p k i. induction o as [| a o IH]; intros P Hk Hi; [exact P |].
    simpl in P. simpl. destruct P as [[E H] | P].
    - subst a. rewrite Hk. simpl. left. split; [reflexivity | apply filter_In; split; assumption].
    - destruct (p a); [simpl; right |]; apply IH; assumption.
  Qed.

  Lemma topo_filter : forall (p : nat -> bool) o, topo src o -> topo src (filter p o).
  Proof.
    intros p o [Hnd Ht]. split; [apply nodup_filter_gen; exact Hnd |].
    intros i k Hi Hk Hko. apply filter_In in Hi. apply filter_In in Hko.
    apply prec_filter; [apply Ht; [apply Hi | exact Hk | apply Hko] | apply Hko | apply Hi].
  Qed.
End Topo.

Lemma filter_single_none : forall i o, ~ In i o -> filter (fun k => memb k [i]) o = [].
Proof.
  intros i o. induction o as [| a o IH]; intro H; [reflexivity |]. simpl.
  destruct (Nat.eqb_spec a i) as [-> | Hne]; [exfalso; apply H; left; reflexivity |].
  simpl. apply IH. intro X. apply H. right. exact X.
Qed.

Lemma filter_single : forall i o, NoDup o -> In i o -> filter (fun k => memb k [i]) o = [i].
Proof.
  intros i o. induction o as [| a o IH]; intros Hnd Hi; [destruct Hi |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd]. simpl.
  destruct (Nat.eqb_spec a i) as [-> | Hne].
  - simpl. f_equal. apply filter_single_none. exact Ha.
  - simpl. apply IH; [exact Hnd |]. destruct Hi as [E | Hi]; [contradiction | exact Hi].
Qed.

Section Certificates.
  Context {V Sh : Type}.
  Variable src : nat -> list nat.
  Variable rho : nat -> V -> V.
  Variable get : nat -> V -> Sh.
  Variable ovr : nat -> V -> Sh -> V.
  Variable res : nat -> list V -> Sh.

  Local Notation stepF := (stepN src rho ovr res).

  (* The bridge's resolvers read the source values in order: R1 holds by construction. *)
  Definition resL (B : nat) (s : nat -> V) : Sh := res B (map s (src B)).

  Lemma resL_R1 : R1 src resL.
  Proof. intros B s t H. unfold resL. f_equal. apply map_ext_in. exact H. Qed.

  (* A sub-federation closed under sources (the upstream blocks of Theorem 2). *)
  Definition ClosedIn (U : list nat) : Prop := forall i k, In i U -> In k (src i) -> In k U.

  (* U's certificate: the federated normalizer run over the members of U in o's order; registries
     outside U are external inputs, read as they are. *)
  Definition rhoU (o U : list nat) (s : nat -> V) : nat -> V :=
    run stepF (filter (fun k => memb k U) o) s.

  (* s on U, t elsewhere. *)
  Definition patch (U : list nat) (s t : nat -> V) : nat -> V :=
    fun k => if memb k U then s k else t k.

  Lemma run_agree_closed : forall U, ClosedIn U -> forall o s t, Agree U s t ->
    Agree U (run stepF o s) (run stepF (filter (fun k => memb k U) o) t).
  Proof.
    intros U HU. induction o as [| a o IH]; intros s t H; [exact H |].
    simpl filter. rewrite run_cons. destruct (memb a U) eqn:Ea.
    - rewrite run_cons. apply IH. intros k Hk. destruct (Nat.eq_dec k a) as [-> | Hne].
      + rewrite !step_self. apply memb_iff in Ea. rewrite (H a Ea).
        apply stepN_local. intros m Hm. apply H. exact (HU a m Ea Hm).
      + rewrite !step_other by exact Hne. apply H. exact Hk.
    - apply IH. intros k Hk. rewrite step_other; [apply H; exact Hk |].
      intro E. subst k. apply memb_false in Ea. contradiction.
  Qed.

  (* Restriction of certificates, closed case: the global normalizer restricted to a source-closed
     U is U's certificate, for any order. *)
  Theorem cert_restrict_closed : forall U, ClosedIn U -> forall o s,
    Agree U (run stepF o s) (rhoU o U s).
  Proof. intros U HU o s. apply run_agree_closed; [exact HU | intros k _; reflexivity]. Qed.

  Lemma run_agree_gen : forall U o s t, topo src o -> Agree U s t ->
    (forall k, ~ In k U -> t k = run stepF o s k) ->
    Agree U (run stepF o s) (run stepF (filter (fun k => memb k U) o) t).
  Proof.
    intros U. induction o as [| a o IH]; intros s t Ho H Hout; [exact H |].
    pose proof (topo_tail src a o Ho) as Ho'.
    simpl filter. rewrite run_cons in *. destruct (memb a U) eqn:Ea.
    - apply memb_iff in Ea. rewrite run_cons. apply IH; [exact Ho' | |].
      + intros k Hk. destruct (Nat.eq_dec k a) as [-> | Hne].
        * rewrite !step_self. rewrite (H a Ea). apply stepN_local. intros m Hm.
          destruct (in_dec Nat.eq_dec m U) as [HmU | HmU]; [apply H; exact HmU |].
          rewrite (Hout m HmU).
          pose proof (topo_head_src src a o m Ho Hm) as Hn.
          rewrite run_out_gen by (intro X; apply Hn; right; exact X).
          symmetry. apply step_other. intro E. apply Hn. left. symmetry. exact E.
        * rewrite !step_other by exact Hne. apply H. exact Hk.
      + intros k Hk. rewrite step_other by (intro E; subst k; contradiction).
        apply Hout. exact Hk.
    - apply IH; [exact Ho' | | exact Hout].
      intros k Hk. rewrite step_other; [apply H; exact Hk |].
      intro E. subst k. apply memb_false in Ea. contradiction.
  Qed.

  (* Restriction of certificates, any U: the global normal form on U is U's certificate run on the
     state whose external inputs are replaced by their global normal forms. *)
  Theorem cert_restrict : forall o U s, topo src o ->
    Agree U (run stepF o s) (rhoU o U (patch U s (run stepF o s))).
  Proof.
    intros o U s Ho. apply run_agree_gen; [exact Ho | |].
    - intros k Hk. unfold patch. apply memb_iff in Hk. rewrite Hk. reflexivity.
    - intros k Hk. unfold patch. apply memb_false in Hk. rewrite Hk. reflexivity.
  Qed.

  (* The pointwise form (U = [i]): each registry's global normal form is one step from the global
     normal forms of its sources. *)
  Theorem cert_pointwise : forall o i s, topo src o -> In i o ->
    run stepF o s i = stepF i (patch [i] s (run stepF o s)) (s i).
  Proof.
    intros o i s Ho Hi.
    rewrite (cert_restrict o [i] s Ho i (or_introl eq_refl)).
    unfold rhoU. rewrite (filter_single i o (proj1 Ho) Hi).
    transitivity (step stepF (patch [i] s (run stepF o s)) i i); [reflexivity |].
    rewrite step_self. f_equal. unfold patch. simpl. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (* On a closed U inside o, the sections over U are CategoricalBridge's L_F of U's order. *)
  Theorem sec_iff_LF : forall o U s, ClosedIn U -> incl U o ->
    (Sec src rho get resL U s <-> LF src rho get res (filter (fun k => memb k U) o) s).
  Proof.
    intros o U s HU Hio. unfold LF, ProdPhi. split.
    - intros [Hn He]. split.
      + intros i Hi. apply filter_In in Hi. apply Hn. apply memb_iff. apply Hi.
      + intros B HB Hs. apply filter_In in HB. destruct HB as [_ HB]. apply memb_iff in HB.
        exact (He B (conj HB (conj Hs (fun k Hk => HU B k HB Hk)))).
    - intros [Hp He]. split.
      + intros i Hi. apply Hp. apply filter_In. split; [apply Hio; exact Hi | apply memb_iff; exact Hi].
      + intros B [HB [Hs _]]. apply He; [| exact Hs].
        apply filter_In. split; [apply Hio; exact HB | apply memb_iff; exact HB].
  Qed.

  Definition certFamily (o : list nat) (C : list (list nat)) (s : nat -> V) : @Family V :=
    map (fun U => (U, rhoU o U s)) C.

  Lemma cover_certFamily : forall o C s, cover (certFamily o C s) = C.
  Proof. intros o C s. unfold cover, certFamily. rewrite map_map. simpl. apply map_id. Qed.

  Lemma closed_union : forall C, (forall U, In U C -> ClosedIn U) -> ClosedIn (Union C).
  Proof.
    intros C H i k Hi Hk. destruct (in_concat_ex C i Hi) as [U [HU HiU]].
    exact (in_concat_intro C U k HU (H U HU i k HiU Hk)).
  Qed.

  (* A cover by closed members refines every constraint. *)
  Lemma closed_refines : forall C, (forall U, In U C -> ClosedIn U) -> Refines src C.
  Proof.
    intros C H B [HB [Hs _]]. destruct (in_concat_ex C B HB) as [U [HU HBU]].
    exists U. split; [exact HU |]. split; [exact HBU | split; [exact Hs |]].
    intros k Hk. exact (H U HU B k HBU Hk).
  Qed.

  (* Gluing of certificates on a closed cover: the local certificates agree on overlaps, and their
     gluing is the certificate of the union and the global normalizer there. *)
  Theorem cert_glue : forall o C d s, (forall U, In U C -> ClosedIn U) ->
    Compatible (certFamily o C s) /\
    Agree (Union C) (glue (certFamily o C s) d) (rhoU o (Union C) s) /\
    Agree (Union C) (glue (certFamily o C s) d) (run stepF o s).
  Proof.
    intros o C d s HC.
    assert (Hc : Compatible (certFamily o C s)).
    { intros U t U' t' H1 H2 k Hk Hk'. unfold certFamily in H1, H2. apply in_map_iff in H1, H2.
      destruct H1 as [U1 [E1 HU1]]. destruct H2 as [U2 [E2 HU2]].
      injection E1 as E1a E1b. injection E2 as E2a E2b. subst U U' t t'.
      rewrite <- (cert_restrict_closed U1 (HC U1 HU1) o s k Hk).
      exact (cert_restrict_closed U2 (HC U2 HU2) o s k Hk'). }
    assert (Hrun : Agree (Union C) (glue (certFamily o C s) d) (run stepF o s)).
    { intros k Hk. rewrite <- (cover_certFamily o C s) in Hk.
      destruct (in_union _ k Hk) as [U [t [Hin HkU]]].
      rewrite (glue_restricts _ d Hc U t Hin k HkU).
      unfold certFamily in Hin. apply in_map_iff in Hin. destruct Hin as [U1 [E1 HU1]].
      injection E1 as E1a E1b. subst U t.
      symmetry. exact (cert_restrict_closed U1 (HC U1 HU1) o s k HkU). }
    split; [exact Hc | split; [| exact Hrun]].
    intros k Hk. rewrite (Hrun k Hk).
    exact (cert_restrict_closed (Union C) (closed_union C HC) o s k Hk).
  Qed.

  (* ----- under the corrected Theorem 1 hypothesis ----- *)

  Hypothesis idem : forall i x, rho i (rho i x) = rho i x.
  Hypothesis putget : forall i v, ovr i v (get i v) = v.
  (* SC (shared-component stability), Theorem 1's hypothesis; M1/R2 is not enough
     (cert_needs_sc). *)
  Hypothesis SC : forall i v r, src i <> [] -> get i (rho i (ovr i v r)) = r.

  (* A closed sub-federation's certificate is the retraction onto its sections: it lands in F(U)
     and fixes F(U). *)
  Theorem cert_retraction : forall o U, topo src o -> ClosedIn U -> incl U o ->
    (forall s, Sec src rho get resL U (rhoU o U s)) /\
    (forall s, Sec src rho get resL U s -> forall k, rhoU o U s k = s k).
  Proof.
    intros o U Ho HU Hio. pose proof (topo_filter src (fun k => memb k U) o Ho) as Hf. split.
    - intro s. apply (proj2 (sec_iff_LF o U _ HU Hio)). unfold rhoU.
      exact (cat_thm_one_sound src rho get ovr res idem putget SC _ s Hf).
    - intros s Hs k. unfold rhoU.
      apply (cat_thm_one_complete src rho get ovr res idem putget SC _ s Hf).
      exact (proj1 (sec_iff_LF o U s HU Hio) Hs).
  Qed.

  (* The certificate sheaf on a closed cover: the local certificates form a compatible family of
     local sections over a refining cover; their gluing lands in the sections over the union, and
     fixes every section over the union (it is the certificate of the union, by cert_glue). *)
  Theorem cert_sheaf : forall o C d s, topo src o -> incl (Union C) o ->
    (forall U, In U C -> ClosedIn U) ->
    Compatible (certFamily o C s) /\
    LocalSections src rho get resL (certFamily o C s) /\
    Refines src (cover (certFamily o C s)) /\
    Sec src rho get resL (Union C) (glue (certFamily o C s) d) /\
    (Sec src rho get resL (Union C) s -> Agree (Union C) (glue (certFamily o C s) d) s).
  Proof.
    intros o C d s Ho Hio HC.
    destruct (cert_glue o C d s HC) as [Hc [HW _]].
    assert (HCW := closed_union C HC).
    destruct (cert_retraction o (Union C) Ho HCW Hio) as [Hsnd Hcmp].
    split; [exact Hc | split; [| split; [| split]]].
    - intros U t Hin. unfold certFamily in Hin. apply in_map_iff in Hin.
      destruct Hin as [U1 [E1 HU1]]. injection E1 as E1a E1b. subst U t.
      apply (cert_retraction o U1 Ho (HC U1 HU1)).
      intros k Hk. apply Hio. exact (in_concat_intro C U1 k HU1 Hk).
    - rewrite cover_certFamily. exact (closed_refines C HC).
    - apply (sec_local src rho get resL resL_R1 (Union C) (rhoU o (Union C) s)); [| exact (Hsnd s)].
      intros k Hk. symmetry. exact (HW k Hk).
    - intros Hs k Hk. rewrite (HW k Hk). exact (Hcmp s Hs k).
  Qed.
End Certificates.

(* ----- the restriction equation is exact: it holds for all data iff U is closed ----- *)

(* The refuting data: non-targets normalize to true; targets copy their resolver value; the
   resolver of i0 is the conjunction of its sources, every other resolver is constantly true. *)
Definition w_rho (src : nat -> list nat) (i : nat) (x : bool) : bool :=
  match src i with [] => true | _ => x end.
Definition w_get (_ : nat) (v : bool) : bool := v.
Definition w_ovr (_ : nat) (_ : bool) (r : bool) : bool := r.
Definition w_res (i0 : nat) (i : nat) (l : list bool) : bool :=
  if Nat.eqb i i0 then forallb (fun x => x) l else true.

Lemma w_step_target : forall src i0 i t x, src i <> [] ->
  stepN src (w_rho src) w_ovr (w_res i0) i t x = w_res i0 i (map t (src i)).
Proof.
  intros src i0 i t x H. unfold stepN, w_rho, w_ovr.
  destruct (src i) as [| a l]; [contradiction H; reflexivity | reflexivity].
Qed.

Lemma w_step_other : forall src i0 i t x, i <> i0 ->
  stepN src (w_rho src) w_ovr (w_res i0) i t x = true.
Proof.
  intros src i0 i t x H. unfold stepN, w_rho, w_ovr, w_res.
  destruct (src i) as [| a l]; [reflexivity |].
  rewrite (proj2 (Nat.eqb_neq i i0) H). reflexivity.
Qed.

Lemma forallb_false_in : forall (f : bool -> bool) l x, In x l -> f x = false -> forallb f l = false.
Proof.
  intros f l x. induction l as [| a l IH]; intros Hin Hx; [destruct Hin |].
  simpl. destruct Hin as [-> | Hin]; [rewrite Hx; reflexivity |].
  rewrite (IH Hin Hx). apply andb_false_r.
Qed.

Theorem cert_restrict_iff :
  forall (src : nat -> list nat) (o U : list nat), topo src o -> ClosedIn src o -> incl U o ->
    ((forall (V Sh : Type) (rho : nat -> V -> V) (get : nat -> V -> Sh)
        (ovr : nat -> V -> Sh -> V) (res : nat -> list V -> Sh),
        (forall i x, rho i (rho i x) = rho i x) ->
        (forall i v, ovr i v (get i v) = v) ->
        (forall i v r, src i <> [] -> get i (rho i (ovr i v r)) = r) ->
        forall s, Agree U (run (stepN src rho ovr res) o s) (rhoU src rho ovr res o U s))
     <-> ClosedIn src U).
Proof.
  intros src o U Ho Hco HUo. split.
  - intros H i k Hi Hk. destruct (in_dec Nat.eq_dec k U) as [Y | N]; [exact Y | exfalso].
    assert (Hidem : forall j x, w_rho src j (w_rho src j x) = w_rho src j x).
    { intros j x. unfold w_rho. destruct (src j); reflexivity. }
    assert (Hpg : forall j v, w_ovr j v (w_get j v) = v) by reflexivity.
    assert (Hsc : forall j v r, src j <> [] -> w_get j (w_rho src j (w_ovr j v r)) = r).
    { intros j v r Hj. unfold w_get, w_rho, w_ovr.
      destruct (src j); [contradiction Hj; reflexivity | reflexivity]. }
    set (s := fun _ : nat => false).
    pose proof (H bool bool (w_rho src) w_get w_ovr (w_res i) Hidem Hpg Hsc s i Hi) as E.
    assert (Hio : In i o) by (apply HUo; exact Hi).
    assert (Hti : src i <> []) by (intro X; rewrite X in Hk; exact Hk).
    (* the global normal form at i is true *)
    rewrite (cert_pointwise src (w_rho src) w_ovr (w_res i) o i s Ho Hio) in E.
    rewrite w_step_target in E by exact Hti. unfold w_res at 1 in E. rewrite Nat.eqb_refl in E.
    assert (Hall : forallb (fun x => x)
               (map (patch [i] s (run (stepN src (w_rho src) w_ovr (w_res i)) o s)) (src i)) = true).
    { apply forallb_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [m [<- Hm]].
      assert (Hmi : m <> i) by (intro X; subst m; exact (topo_self src o i Ho Hio Hm)).
      unfold patch. simpl. rewrite (proj2 (Nat.eqb_neq m i) Hmi). simpl.
      assert (Hmo : In m o) by exact (Hco i m Hio Hm).
      rewrite (cert_pointwise src (w_rho src) w_ovr (w_res i) o m s Ho Hmo).
      apply w_step_other. exact Hmi. }
    rewrite Hall in E.
    (* U's certificate at i reads the raw external input k, which is false *)
    unfold rhoU in E.
    set (o' := filter (fun j => memb j U) o) in E.
    assert (Ho' : topo src o') by exact (topo_filter src _ o Ho).
    assert (Hio' : In i o') by (apply filter_In; split; [exact Hio | apply memb_iff; exact Hi]).
    rewrite (cert_pointwise src (w_rho src) w_ovr (w_res i) o' i s Ho' Hio') in E.
    rewrite w_step_target in E by exact Hti. unfold w_res in E. rewrite Nat.eqb_refl in E.
    assert (Hki : k <> i) by (intro X; subst k; exact (N Hi)).
    assert (Hf : patch [i] s (run (stepN src (w_rho src) w_ovr (w_res i)) o' s) k = false).
    { unfold patch. simpl. rewrite (proj2 (Nat.eqb_neq k i) Hki). simpl.
      rewrite run_out_gen; [reflexivity |].
      intro X. apply filter_In in X. apply N. apply memb_iff. apply X. }
    rewrite (forallb_false_in _ _ _ (in_map _ _ _ Hk) Hf) in E. discriminate E.
  - intros HU V Sh rho get ovr res _ _ _ s. exact (cert_restrict_closed src rho ovr res U HU o s).
Qed.

(* SC is needed: with M1 (validity preservation under overwrite), idempotence and the lens law,
   the certificate of the closed sub-federation {0,1} misses its sections. *)
Theorem cert_needs_sc :
  (forall i v r, cx_rho i v = v -> cx_rho i (cx_ovr i v r) = cx_ovr i v r) /\
  (forall i x, cx_rho i (cx_rho i x) = cx_rho i x) /\
  (forall i v, cx_ovr i v (cx_get i v) = v) /\
  ClosedIn cx_src [0; 1] /\ topo cx_src [0; 1] /\
  ~ (forall i v r, cx_src i <> [] -> cx_get i (cx_rho i (cx_ovr i v r)) = r) /\
  ~ Sec cx_src cx_rho cx_get (resL cx_src cx_res) [0; 1]
      (rhoU cx_src cx_rho cx_ovr cx_res [0; 1] [0; 1] cx_s).
Proof.
  destruct cat_thm_one_m1_counterexample as [Hm1 [Hid [Hpg _]]].
  split; [exact Hm1 | split; [exact Hid | split; [exact Hpg | split; [| split; [| split]]]]].
  - intros i k Hi Hk. destruct Hi as [<- | [<- | []]]; simpl in Hk; [destruct Hk |].
    destruct Hk as [<- | []]. left. reflexivity.
  - exact cx_topo.
  - intro H. specialize (H 1 (false, false) true ltac:(discriminate)). discriminate H.
  - intros [_ He].
    assert (Hi : Internal cx_src [0; 1] 1).
    { split; [simpl; tauto | split; [discriminate |]]. intros k [<- | []]. simpl. tauto. }
    specialize (He 1 Hi). vm_compute in He. discriminate He.
Qed.

(* Collapse.v's convex form: for a convex J, the federated normal form on J is rho_J run after the
   upstream block P (collapse_nf_factor, which rests on collapse_nf_agree). *)
Theorem collapse_restrict :
  forall (V : Type) (src : nat -> list nat) (f : nat -> (nat -> V) -> V -> V)
    (valid : nat -> V -> Prop) (rho : nat -> V -> V) (E : Type) (reg : E -> nat)
    (sig : E -> V -> V) (o : list nat),
    FederationEvents.Common V src f valid rho E reg sig o ->
    (forall j x, valid j (rho j x)) ->
    forall inJ : nat -> bool, Collapse.Convex src inJ ->
    forall t k, inJ k = true ->
      FederationEvents.N V f rho o t k =
      Collapse.rhoJ V f rho o inJ
        (FederationEvents.frun V f (Collapse.preJ src inJ o) (fun m => rho m (t m))) k.
Proof.
  intros V src f valid rho E reg sig o HC HR inJ Hconv t k Hk.
  rewrite (Collapse.collapse_nf_factor V src f valid rho E reg sig o HC HR inJ Hconv t k).
  apply FederationEvents.frun_out. intro Hq. apply Collapse.in_postJ in Hq. destruct Hq as [_ Hd].
  pose proof (Collapse.desc_notJ src inJ o (FederationEvents.c_topo _ _ _ _ _ _ _ _ _ HC) k Hd).
  congruence.
Qed.

(* ========================================================================================= *)
(* PART 5. Certificate instances.                                                             *)
(* ========================================================================================= *)

(* A fork 0 -> 1, 0 -> 2. Values are (shared, local); registry 0 clamps both coordinates at 3,
   the targets clamp their local coordinate, and a target's resolver is its source's shared
   value (CategoricalBridge's nv_get, nv_ovr, nv_res). *)
Definition vs_src (i : nat) : list nat := match i with 1 => [0] | 2 => [0] | _ => [] end.
Definition vs_rho (i : nat) (v : nat * nat) : nat * nat :=
  match i with 0 => (clamp3 (fst v), clamp3 (snd v)) | _ => (fst v, clamp3 (snd v)) end.
Definition vs_s0 (_ : nat) : nat * nat := (5, 9).

Lemma vs_idem : forall i x, vs_rho i (vs_rho i x) = vs_rho i x.
Proof. intros [| i] [a b]; unfold vs_rho; simpl; rewrite ?clamp3_idem; reflexivity. Qed.

Lemma vs_putget : forall i v, nv_ovr i v (nv_get i v) = v.
Proof. intros i [a b]. reflexivity. Qed.

Lemma vs_sc : forall i v r, vs_src i <> [] -> nv_get i (vs_rho i (nv_ovr i v r)) = r.
Proof. intros [| i] [a b] r H; [contradiction H; reflexivity | reflexivity]. Qed.

Lemma vs_topo : topo vs_src [0; 1; 2].
Proof.
  split.
  - repeat constructor; simpl; intuition congruence.
  - intros i k Hi Hk Hko. simpl in Hi.
    destruct Hi as [<- | [<- | [<- | []]]]; simpl in Hk; try contradiction;
      destruct Hk as [<- | []]; simpl; intuition.
Qed.

Lemma vs_closed : forall U, In U [[0; 1]; [0; 2]] -> ClosedIn vs_src U.
Proof.
  intros U [<- | [<- | []]] i k Hi Hk; destruct Hi as [<- | [<- | []]]; simpl in Hk;
    try contradiction; destruct Hk as [<- | []]; left; reflexivity.
Qed.

(* Non-vacuity of the certificate sheaf: the closed cover {0,1}, {0,2} of the fork (overlap {0})
   discharges every hypothesis; the glued certificate is (3,3) everywhere, while the start state is
   not a section. *)
Theorem vs_cert_sheaf :
  Compatible (certFamily vs_src vs_rho nv_ovr nv_res [0; 1; 2] [[0; 1]; [0; 2]] vs_s0) /\
  Sec vs_src vs_rho nv_get (resL vs_src nv_res) [0; 1; 0; 2]
    (glue (certFamily vs_src vs_rho nv_ovr nv_res [0; 1; 2] [[0; 1]; [0; 2]] vs_s0) vs_s0) /\
  (forall k, In k [0; 1; 2] ->
     glue (certFamily vs_src vs_rho nv_ovr nv_res [0; 1; 2] [[0; 1]; [0; 2]] vs_s0) vs_s0 k = (3, 3)) /\
  ~ Sec vs_src vs_rho nv_get (resL vs_src nv_res) [0; 1; 0; 2] vs_s0.
Proof.
  assert (Hio : incl (Union [[0; 1]; [0; 2]]) [0; 1; 2]).
  { intros k Hk. simpl in Hk. simpl. intuition. }
  destruct (cert_sheaf vs_src vs_rho nv_get nv_ovr nv_res vs_idem vs_putget vs_sc
              [0; 1; 2] [[0; 1]; [0; 2]] vs_s0 vs_s0 vs_topo Hio vs_closed)
    as [Hc [_ [_ [Hs _]]]].
  split; [exact Hc | split; [exact Hs | split]].
  - intros k [<- | [<- | [<- | []]]]; vm_compute; reflexivity.
  - intros [Hn _]. destruct (Hn 0 (or_introl eq_refl)) as [[a b] Hy].
    unfold vs_rho, vs_s0 in Hy. simpl in Hy. injection Hy as Ha _.
    unfold clamp3 in Ha. pose proof (Nat.le_min_r a 3). lia.
Qed.

(* Non-vacuity of cert_restrict and of the exactness of the closed case: on the chain with the
   same data, U = {1,2} is not closed; its certificate reads the raw input of 0 and misses the
   global normal form at 1, while the patched equation holds. *)
Theorem chain_cert_nonclosed :
  topo ch_src [0; 1; 2] /\ ClosedIn ch_src [0; 1; 2] /\ incl [1; 2] [0; 1; 2] /\
  ~ ClosedIn ch_src [1; 2] /\ ClosedIn ch_src [0; 1] /\
  rhoU ch_src vs_rho nv_ovr nv_res [0; 1; 2] [1; 2] vs_s0 1 = (5, 3) /\
  run (stepN ch_src vs_rho nv_ovr nv_res) [0; 1; 2] vs_s0 1 = (3, 3) /\
  Agree [1; 2] (run (stepN ch_src vs_rho nv_ovr nv_res) [0; 1; 2] vs_s0)
    (rhoU ch_src vs_rho nv_ovr nv_res [0; 1; 2] [1; 2]
       (patch [1; 2] vs_s0 (run (stepN ch_src vs_rho nv_ovr nv_res) [0; 1; 2] vs_s0))).
Proof.
  assert (Ht : topo ch_src [0; 1; 2]).
  { split.
    - repeat constructor; simpl; intuition congruence.
    - intros i k Hi Hk Hko. simpl in Hi.
      destruct Hi as [<- | [<- | [<- | []]]]; simpl in Hk; try contradiction;
        destruct Hk as [<- | []]; simpl; intuition. }
  split; [exact Ht | split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - intros i k Hi Hk. destruct Hi as [<- | [<- | [<- | []]]]; simpl in Hk; try contradiction;
      destruct Hk as [<- | []]; simpl; tauto.
  - intros k Hk. simpl in Hk. simpl. intuition.
  - intro H. destruct (H 1 0 (or_introl eq_refl) (or_introl eq_refl)) as [E | [E | []]];
      discriminate E.
  - intros i k Hi Hk. destruct Hi as [<- | [<- | []]]; simpl in Hk; try contradiction;
      destruct Hk as [<- | []]; simpl; tauto.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact (cert_restrict ch_src vs_rho nv_ovr nv_res [0; 1; 2] [1; 2] vs_s0 Ht).
Qed.

(* Non-vacuity of cert_restrict_iff: its hypotheses hold on the chain for U = {0,1} (closed, so the
   left side holds) and for U = {1,2} (not closed, so it fails). *)
Theorem cert_restrict_iff_instance :
  (forall (V Sh : Type) (rho : nat -> V -> V) (get : nat -> V -> Sh)
     (ovr : nat -> V -> Sh -> V) (res : nat -> list V -> Sh),
     (forall i x, rho i (rho i x) = rho i x) ->
     (forall i v, ovr i v (get i v) = v) ->
     (forall i v r, ch_src i <> [] -> get i (rho i (ovr i v r)) = r) ->
     forall s, Agree [0; 1] (run (stepN ch_src rho ovr res) [0; 1; 2] s)
                (rhoU ch_src rho ovr res [0; 1; 2] [0; 1] s)) /\
  ~ (forall (V Sh : Type) (rho : nat -> V -> V) (get : nat -> V -> Sh)
       (ovr : nat -> V -> Sh -> V) (res : nat -> list V -> Sh),
       (forall i x, rho i (rho i x) = rho i x) ->
       (forall i v, ovr i v (get i v) = v) ->
       (forall i v r, ch_src i <> [] -> get i (rho i (ovr i v r)) = r) ->
       forall s, Agree [1; 2] (run (stepN ch_src rho ovr res) [0; 1; 2] s)
                  (rhoU ch_src rho ovr res [0; 1; 2] [1; 2] s)).
Proof.
  destruct chain_cert_nonclosed as [Ht [Hco [_ [Hn12 [Hc01 _]]]]].
  split.
  - apply (proj2 (cert_restrict_iff ch_src [0; 1; 2] [0; 1] Ht Hco ltac:(intros k Hk; simpl in *; intuition))).
    exact Hc01.
  - intro H. apply Hn12.
    exact (proj1 (cert_restrict_iff ch_src [0; 1; 2] [1; 2] Ht Hco
                    ltac:(intros k Hk; simpl in *; intuition)) H).
Qed.

(* Non-vacuity of collapse_restrict: Collapse.v's chain instance (convex J = {0,1}). *)
Theorem collapse_restrict_instance :
  forall t k, Collapse.j01 k = true ->
    FederationEvents.N nat Collapse.ch_f Collapse.id_rho [0; 1; 2] t k =
    Collapse.rhoJ nat Collapse.ch_f Collapse.id_rho [0; 1; 2] Collapse.j01
      (FederationEvents.frun nat Collapse.ch_f (Collapse.preJ Collapse.chain_src Collapse.j01 [0; 1; 2])
         (fun m => Collapse.id_rho m (t m))) k.
Proof.
  exact (collapse_restrict _ _ _ _ _ _ _ _ _ Collapse.chain_common (fun _ _ => I)
           Collapse.j01 Collapse.chain_convex).
Qed.
