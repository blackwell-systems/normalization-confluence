(* Newman's Lemma, mechanized and fully self-contained (no external libraries).

   A strongly-normalizing, locally confluent abstract rewrite system is
   confluent, and therefore has unique normal forms. This is precisely the
   inference the normalization-confluence paper invokes (Cor. "Unique Normal
   Forms"): from Termination (WFC) + Local Confluence (CC), conclude global
   confluence via Newman's Lemma. This file machine-checks that step for an
   arbitrary relation; Governance.v instantiates it to the paper's rewrite
   system. Checked by coqc (Rocq 9.3). *)

Section ARS.
  Context {A : Type}.
  Variable R : A -> A -> Prop.

  (* Reflexive-transitive closure, in 1n (list-like) shape for clean induction. *)
  Inductive star : A -> A -> Prop :=
  | star_refl : forall x, star x x
  | star_step : forall x y z, R x y -> star y z -> star x z.

  Lemma star_one : forall x y, R x y -> star x y.
  Proof. intros x y H. eapply star_step; [exact H | apply star_refl]. Qed.

  Lemma star_trans : forall x y z, star x y -> star y z -> star x z.
  Proof.
    intros x y z Hxy. revert z.
    induction Hxy as [x | x y0 z0 Rxy0 Hy0 IH]; intros z Hz.
    - exact Hz.
    - eapply star_step; [exact Rxy0 | apply IH; exact Hz].
  Qed.

  (* Strong normalization: no infinite forward R-chain. Equivalently, every
     element is accessible under the transpose of R. This is the constructive
     form of "terminating". *)
  Definition SN (x : A) : Prop := Acc (fun a b => R b a) x.

  Definition joinable (y z : A) : Prop := exists w, star y w /\ star z w.

  Definition locally_confluent : Prop :=
    forall x y z, R x y -> R x z -> joinable y z.

  (* Confluence localized at x: any two reducts of x are joinable. *)
  Definition CR (x : A) : Prop :=
    forall y z, star x y -> star x z -> joinable y z.

  Definition confluent : Prop := forall x, CR x.

  (* Newman's Lemma. The proof is well-founded induction on SN: split each
     divergence into its first steps R x x1, R x x2, close them by local
     confluence, then twice invoke the induction hypothesis (available at x1
     and x2, the R-successors of x) to merge the tails. *)
  Theorem newman : locally_confluent -> forall x, SN x -> CR x.
  Proof.
    intros LC x SNx.
    induction SNx as [x _ IH].
    intros y z Sxy Sxz.
    destruct Sxy as [x | x x1 y Rxx1 Sx1y].
    - (* x = y: y reduces nowhere new; join at z via x ->* z. *)
      exists z. split; [exact Sxz | apply star_refl].
    - destruct Sxz as [x | x x2 z Rxx2 Sx2z].
      + (* x = z: symmetric, join at y. *)
        exists y. split; [apply star_refl | eapply star_step; [exact Rxx1 | exact Sx1y]].
      + (* R x x1 and R x x2: close the peak by local confluence. *)
        destruct (LC x x1 x2 Rxx1 Rxx2) as [w [Sx1w Sx2w]].
        (* IH at x1: merge x1 ->* y and x1 ->* w. *)
        destruct (IH x1 Rxx1 y w Sx1y Sx1w) as [u [Syu Swu]].
        (* IH at x2: merge x2 ->* z and x2 ->* u (via w ->* u). *)
        destruct (IH x2 Rxx2 z u Sx2z (star_trans _ _ _ Sx2w Swu)) as [v [Szv Suv]].
        exists v. split.
        * exact (star_trans _ _ _ Syu Suv).
        * exact Szv.
  Qed.

  Corollary confluent_of_SN :
    locally_confluent -> (forall x, SN x) -> confluent.
  Proof. intros LC HSN x. apply newman; [exact LC | apply HSN]. Qed.

  (* Normal forms and their uniqueness under termination + confluence. *)
  Definition normal_form (x : A) : Prop := ~ exists y, R x y.

  Lemma star_from_nf : forall x y, normal_form x -> star x y -> x = y.
  Proof.
    intros x y NFx S. destruct S as [x | x a y Rxa _].
    - reflexivity.
    - exfalso. apply NFx. exists a. exact Rxa.
  Qed.

  Theorem unique_normal_forms :
    confluent ->
    forall x n1 n2,
      star x n1 -> normal_form n1 ->
      star x n2 -> normal_form n2 ->
      n1 = n2.
  Proof.
    intros CONF x n1 n2 Sxn1 NF1 Sxn2 NF2.
    destruct (CONF x n1 n2 Sxn1 Sxn2) as [w [Sn1w Sn2w]].
    assert (n1 = w) by (apply star_from_nf; assumption).
    assert (n2 = w) by (apply star_from_nf; assumption).
    subst. reflexivity.
  Qed.

End ARS.
