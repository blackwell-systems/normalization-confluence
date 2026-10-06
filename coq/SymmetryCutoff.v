(* SymmetryCutoff.v: symmetry reduction for keyed collections (roadmap item 8, step 1; gsm roadmap
   item 1a). Check one item, conclude for all. Axiom-free.

   Model. An item registry is (a, r, v, Phi): a per-item event function a : E -> A -> A, a per-item
   repair step r, a per-item invariant v : A -> bool and a WFC potential Phi, with repair leaving
   valid items alone (r_fix). The collection registry over n items (the lift) has states
   l : list A of length n (position k is the item with key k), events (k, e) = "e at k" acting on
   item k only (aL), repair acting pointwise on every item (rL = map r), and the invariant the
   conjunction of the item invariants (validL). It is an instance of Governance.v's rewrite system
   with free delivery, so GovernanceConverse.cc_exact_from applies to both registries.

   Cutoffs (n = number of items).
   - wfc_cutoff: for n >= 1, the collection has a WFC potential iff the item does. Cutoff 1.
   - same_item_reduces: two events on the same item commute in the collection at l iff they
     commute in the item registry at l's item.
   - cross_item_reduces: two events on different items k1 <> k2 commute at l iff
     g e1 (rstar s1) = g e1 s1 and g e2 (rstar s2) = g e2 s2 (repair-then-event equals event alone
     on each item). cross_valid_commute: at every valid state this holds with no hypothesis.
     cc2_star: CC2 on the item's reachable states implies it on those states.
   - cc2_cutoff: CC2 for the collection from l0 iff CC2 for the item from each l0[k]. Cutoff 1.
   - cc1_cutoff: CC1 for the collection (events in range) from l0 iff, for each item, CC1 and, when
     there are at least two items, CC2star. So CC1 alone has cutoff 2 (cc1_cutoff_uniform2), and
     the cutoff is tight: cc1_cutoff_tight is an item with CC1 at one item that fails CC1 at two.
   - cc_lift_iff, un_cutoff: CC1 and CC2 together, hence unique normal forms (cc_exact_from), have
     cutoff 1: every buffer from l0 has a unique normal form iff every buffer from each item's start
     does. un_cutoff_uniform (start repeat s0 n), un_cutoff_global (every start).
     un_in_to_item: the converse direction already follows from buffers whose events are in range.
   - alo_cutoff, alo_cutoff_exact: at-least-once convergence (AtLeastOnceExact.ALOConv) of the
     lifted step from l0 iff of the item step from each l0[k]; with alo_exact, CommReach and
     IdemReach reduce per item. alo_gov_cutoff: the same for governed steps from a valid start.
     cross_commute: events on different items commute at every state. idem_reduces, declared_cutoff:
     idempotence and declared commutation (cross-item pairs declared for free) reduce per item.
   - c1_cutoff, c2_cutoff: federation conditions C1 and C2 (FederationEvents.v) for a target
     collection whose morphism maps items pointwise reduce to one item, given absorption (c_absorb)
     and event validity (c_sig).

   Hypotheses made checkable (section Symmetry). For an arbitrary registry over lists of length n:
   - IdGov: independent (an event at k writes only k and reads only k; repair at k reads and
     writes only k; the invariant is the conjunction of item invariants) and identically governed
     (rules invariant under the transpositions of keys, hence under every permutation).
   - idgov_lift: for n >= 1, IdGov iff the registry is the lift of its one-item restriction
     (IsLift). lift_idgov: every lift satisfies IdGov.
   - symcheck_decides: on finite descriptions (enumerated item states and events), the boolean
     symcheck decides IdGov (sound and complete).
   - symmetry_sound: if IdGov holds and the one-item restriction satisfies r_fix and WFC, the
     registry has unique normal forms from l0 for every in-range buffer iff the one-item registry
     does from each item's start.

   Boundaries.
   - aggregate_diverges, agg_item_un, agg_not_idgov: an aggregate invariant (total reserved at most
     1) with the same increment and a repair that cancels a reservation on every positive item: the
     one-item registry has unique normal forms from every state, the two-item registry diverges,
     and IdGov fails (the invariant is not a conjunction of item invariants), so the check refuses
     it. itemwise_converges: with the per-item invariant the same rules converge at every n.
   - nonidentical_misleads, nonidentical_not_idgov: items governed by different rules; checking
     item 0 passes, the collection diverges, and IdGov fails.
   - inventory_any_n, inventory_repair_fires, inventory_idgov: per-product inventory (restock,
     reserve, release, a backorder flag maintained by repair) converges for any number of products
     through the cutoff, and repair does fire. *)

Require Import NC.Newman NC.Governance NC.GovernanceConverse NC.Trace NC.AtLeastOnce NC.AtLeastOnceExact.
From Coq Require Import List Arith Lia Bool Setoid.
Import ListNotations.

(* ============================================================================================ *)
(* Lists: modify one position, swap two positions, positionwise equality.                       *)
(* ============================================================================================ *)

Section ListOps.
  Context {A : Type}.

  Fixpoint modk (f : A -> A) (k : nat) (l : list A) : list A :=
    match l with
    | [] => []
    | x :: t => match k with
                | 0 => f x :: t
                | S k' => x :: modk f k' t
                end
    end.

  Lemma modk_length : forall f k l, length (modk f k l) = length l.
  Proof. intros f k l; revert k; induction l as [|x l IH]; intros [|k]; simpl; auto. Qed.

  Lemma modk_nth_same : forall f k l, nth_error (modk f k l) k = option_map f (nth_error l k).
  Proof. intros f k l; revert k; induction l as [|x l IH]; intros [|k]; simpl; auto. Qed.

  Lemma modk_nth_other : forall f k l j, j <> k -> nth_error (modk f k l) j = nth_error l j.
  Proof.
    intros f k l; revert k; induction l as [|x l IH]; intros [|k] [|j] H; simpl; auto;
      try congruence; apply IH; lia.
  Qed.

  Lemma modk_nth : forall f k l j,
    nth_error (modk f k l) j = option_map (if Nat.eqb j k then f else fun x => x) (nth_error l j).
  Proof.
    intros f k l j. destruct (Nat.eqb_spec j k) as [-> | Hne].
    - apply modk_nth_same.
    - rewrite (modk_nth_other f k l j Hne). destruct (nth_error l j); reflexivity.
  Qed.

  Lemma list_ext : forall l1 l2 : list A, (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
  Proof.
    induction l1 as [|x l1 IH]; intros [|y l2] H.
    - reflexivity.
    - specialize (H 0); discriminate.
    - specialize (H 0); discriminate.
    - pose proof (H 0) as H0; simpl in H0; injection H0 as ->. f_equal.
      apply IH. intro i. exact (H (S i)).
  Qed.

  Lemma nth_map' {B : Type} : forall (f : A -> B) l i,
    nth_error (map f l) i = option_map f (nth_error l i).
  Proof. intros f l; induction l as [|x l IH]; intros [|i]; simpl; auto. Qed.

  Lemma len_map' {B : Type} : forall (f : A -> B) l, length (map f l) = length l.
  Proof. intros f l; induction l; simpl; auto. Qed.

  Lemma nth_repeat' : forall (x : A) n i, nth_error (repeat x n) i = if Nat.ltb i n then Some x else None.
  Proof. intros x n; induction n as [|n IH]; intros [|i]; simpl; auto. Qed.

  Lemma len_repeat' : forall (x : A) n, length (repeat x n) = n.
  Proof. intros x n; induction n; simpl; auto. Qed.

  Lemma map_repeat' {B : Type} : forall (f : A -> B) x n, map f (repeat x n) = repeat (f x) n.
  Proof. intros f x n; induction n; simpl; f_equal; auto. Qed.

  Lemma nth_some_lt : forall l k (x : A), nth_error l k = Some x -> k < length l.
  Proof. intros l k x H. apply nth_error_Some. congruence. Qed.

  Lemma nth_lt_some : forall l k, k < length l -> exists x : A, nth_error l k = Some x.
  Proof.
    intros l k H. destruct (nth_error l k) as [x|] eqn:E; [exists x; reflexivity |].
    apply nth_error_Some in H. contradiction.
  Qed.

  (* The transposition of keys i and j, and the list with positions i and j exchanged. *)
  Definition tau (i j m : nat) : nat :=
    if Nat.eqb m i then j else if Nat.eqb m j then i else m.

  Definition swap (i j : nat) (l : list A) : list A :=
    match nth_error l i, nth_error l j with
    | Some x, Some y => modk (fun _ => y) i (modk (fun _ => x) j l)
    | _, _ => l
    end.

  Lemma swap_length : forall i j l, length (swap i j l) = length l.
  Proof.
    intros i j l. unfold swap. destruct (nth_error l i), (nth_error l j); auto.
    rewrite !modk_length. reflexivity.
  Qed.

  Lemma swap_nth : forall i j l m, i < length l -> j < length l ->
    nth_error (swap i j l) m = nth_error l (tau i j m).
  Proof.
    intros i j l m Hi Hj.
    destruct (nth_lt_some l i Hi) as [x Hx]. destruct (nth_lt_some l j Hj) as [y Hy].
    unfold swap, tau. rewrite Hx, Hy, !modk_nth.
    destruct (Nat.eqb_spec m i) as [E1 | E1]; destruct (Nat.eqb_spec m j) as [E2 | E2]; subst.
    - rewrite Hy in *. injection Hx as ->. reflexivity.
    - rewrite Hx, Hy. reflexivity.
    - rewrite Hy, Hx. reflexivity.
    - destruct (nth_error l m); reflexivity.
  Qed.

  Lemma tau_lt : forall i j m n, i < n -> j < n -> m < n -> tau i j m < n.
  Proof.
    intros i j m n Hi Hj Hm. unfold tau.
    destruct (Nat.eqb m i); [exact Hj|]. destruct (Nat.eqb m j); [exact Hi | exact Hm].
  Qed.

  Lemma tau_invol : forall i j m, tau i j (tau i j m) = m.
  Proof.
    intros i j m. unfold tau.
    destruct (Nat.eqb_spec m i) as [-> | H1].
    - destruct (Nat.eqb_spec j i) as [-> | H2]; [reflexivity|].
      rewrite Nat.eqb_refl. reflexivity.
    - destruct (Nat.eqb_spec m j) as [-> | H2].
      + rewrite Nat.eqb_refl. reflexivity.
      + destruct (Nat.eqb_spec m i); [contradiction|]. destruct (Nat.eqb_spec m j); [contradiction|].
        reflexivity.
  Qed.

  Lemma tau_eqb : forall i j m k, Nat.eqb (tau i j m) (tau i j k) = Nat.eqb m k.
  Proof.
    intros i j m k. destruct (Nat.eqb_spec m k) as [-> | H].
    - apply Nat.eqb_refl.
    - apply Nat.eqb_neq. intro E. apply H. rewrite <- (tau_invol i j m), E. apply tau_invol.
  Qed.

  Lemma tau_0kk : forall k, tau 0 k k = 0.
  Proof. intros k. unfold tau. destruct (Nat.eqb_spec k 0) as [-> | H]; [reflexivity|].
    rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma swap_repeat : forall i j (x : A) n, i < n -> j < n -> swap i j (repeat x n) = repeat x n.
  Proof.
    intros i j x n Hi Hj. apply list_ext. intro m.
    rewrite swap_nth by (rewrite len_repeat'; assumption). rewrite !nth_repeat'.
    unfold tau. destruct (Nat.eqb_spec m i) as [-> | H1].
    - apply Nat.ltb_lt in Hi, Hj. rewrite Hi, Hj. reflexivity.
    - destruct (Nat.eqb_spec m j) as [-> | H2]; [|reflexivity].
      apply Nat.ltb_lt in Hi, Hj. rewrite Hi, Hj. reflexivity.
  Qed.
End ListOps.

Fixpoint itr {X : Type} (m : nat) (f : X -> X) (x : X) : X :=
  match m with 0 => x | S m' => itr m' f (f x) end.

Lemma itr_add : forall {X : Type} m j (f : X -> X) x, itr (m + j) f x = itr j f (itr m f x).
Proof. intros X m; induction m as [|m IH]; intros j f x; simpl; auto. Qed.

Lemma itr_fix : forall {X : Type} m (f : X -> X) x, f x = x -> itr m f x = x.
Proof. intros X m; induction m as [|m IH]; intros f x H; simpl; [reflexivity|]. rewrite H. auto. Qed.

Lemma itr_map : forall {X : Type} m (f : X -> X) l, itr m (map f) l = map (itr m f) l.
Proof.
  intros X m; induction m as [|m IH]; intros f l; simpl.
  - symmetry. apply map_id.
  - rewrite IH, map_map. reflexivity.
Qed.

(* Keyed events: decidable equality. *)
Definition kdec {E : Type} (edec : forall x y : E, {x = y} + {x <> y}) (x y : nat * E) :
  {x = y} + {x <> y}.
Proof.
  destruct x as [k1 e1], y as [k2 e2].
  destruct (Nat.eq_dec k1 k2) as [Hk | Hk]; [destruct (edec e1 e2) as [He | He] |].
  - left; subst; reflexivity.
  - right; intro H; injection H; auto.
  - right; intro H; injection H; auto.
Defined.

Lemma remove1_pair : forall {E : Type} (edec : forall x y : E, {x = y} + {x <> y}) k e B,
  remove1 (kdec edec) (k, e) (map (pair k) B) = map (pair k) (remove1 edec e B).
Proof.
  intros E edec k e B. induction B as [|x B IH]; [reflexivity|].
  change (map (pair k) (x :: B)) with ((k, x) :: map (pair k) B). cbn [remove1].
  destruct (kdec edec (k, x) (k, e)) as [H1 | H1]; destruct (edec x e) as [H2 | H2].
  - reflexivity.
  - injection H1; intros; contradiction.
  - subst; contradiction.
  - cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma remove1_incl : forall {E : Type} (dec : forall x y : E, {x = y} + {x <> y}) e B x,
  In x (remove1 dec e B) -> In x B.
Proof.
  intros E dec e B x. induction B as [|y B IH]; simpl; [auto|].
  destruct (dec y e); [auto|]. intros [H | H]; auto.
Qed.

(* Potential of a collection: the sum of the item potentials. *)
Fixpoint sumPhi {A : Type} (Phi : A -> nat) (l : list A) : nat :=
  match l with [] => 0 | x :: t => Phi x + sumPhi Phi t end.

Lemma sum_wfc : forall {A : Type} (r : A -> A) (v : A -> bool) (Phi : A -> nat),
  (forall s, v s = true -> r s = s) -> (forall s, v s <> true -> Phi (r s) < Phi s) ->
  forall l, forallb v l <> true -> sumPhi Phi (map r l) < sumPhi Phi l.
Proof.
  intros A r v Phi Hfix Hw. assert (Hle : forall l, sumPhi Phi (map r l) <= sumPhi Phi l).
  { induction l as [|x l IH]; simpl; [lia|]. destruct (v x) eqn:Hv.
    - rewrite (Hfix x Hv). lia.
    - assert (Phi (r x) < Phi x) by (apply Hw; congruence). lia. }
  induction l as [|x l IH]; intros H; simpl in *; [exfalso; apply H; reflexivity|].
  destruct (v x) eqn:Hv; simpl in H.
  - rewrite (Hfix x Hv). specialize (IH H). lia.
  - assert (Phi (r x) < Phi x) by (apply Hw; congruence). specialize (Hle l). lia.
Qed.

Lemma sumPhi_in : forall {A : Type} (Phi : A -> nat) l x, In x l -> Phi x <= sumPhi Phi l.
Proof. intros A Phi l; induction l as [|y l IH]; intros x H; simpl in *; [contradiction|].
  destruct H as [-> | H]; [lia | specialize (IH x H); lia]. Qed.

(* ============================================================================================ *)
(* WFC: cutoff 1.                                                                                *)
(* ============================================================================================ *)

Section WFCCutoff.
  Context {A : Type}.
  Variable r : A -> A.
  Variable v : A -> bool.
  Hypothesis r_fix : forall s, v s = true -> r s = s.

  Theorem wfc_cutoff : forall n, 1 <= n ->
    (exists PhiL : list A -> nat,
       forall l, length l = n -> forallb v l <> true -> PhiL (map r l) < PhiL l) <->
    (exists Phi : A -> nat, forall s, v s <> true -> Phi (r s) < Phi s).
  Proof.
    intros n Hn. split.
    - intros [PhiL H]. exists (fun s => PhiL (repeat s n)). intros s Hs.
      rewrite <- map_repeat'. apply H; [apply len_repeat'|].
      destruct n as [|n]; [lia|]. simpl. destruct (v s); [contradiction | discriminate].
    - intros [Phi H]. exists (sumPhi Phi). intros l _ Hl. exact (sum_wfc r v Phi r_fix H l Hl).
  Qed.
End WFCCutoff.

(* ============================================================================================ *)
(* At-least-once delivery, idempotence and declared independence: cutoff 1.                      *)
(* ============================================================================================ *)

Section ALOCutoff.
  Context {A E : Type}.
  Variable edec : forall x y : E, {x = y} + {x <> y}.
  Variable st : E -> A -> A.       (* the item step (for governed steps: apply, then repair) *)
  Variable Ev : E -> Prop.         (* item events in range *)

  (* The lifted step: e at k acts on item k only. *)
  Definition lst (x : nat * E) (l : list A) : list A := modk (st (snd x)) (fst x) l.
  Definition EvL (n : nat) (x : nat * E) : Prop := fst x < n /\ Ev (snd x).
  Definition projk (k : nat) (d : list (nat * E)) : list E :=
    map snd (filter (fun x => Nat.eqb k (fst x)) d).

  Lemma run_proj : forall d l k,
    nth_error (runT lst d l) k = option_map (runT st (projk k d)) (nth_error l k).
  Proof.
    induction d as [|[k' e] d IH]; intros l k.
    - simpl. destruct (nth_error l k); reflexivity.
    - rewrite runT_cons, IH. unfold lst, projk; simpl. rewrite modk_nth.
      destruct (nth_error l k) as [s|]; [|reflexivity].
      destruct (Nat.eqb k k'); simpl; reflexivity.
  Qed.

  Lemma in_projk : forall k d e, In e (projk k d) <-> In (k, e) d.
  Proof.
    intros k d e. unfold projk. rewrite in_map_iff. split.
    - intros [[k' e'] [He Hin]]. simpl in He. subst e'. apply filter_In in Hin.
      destruct Hin as [Hin Hk]. simpl in Hk. apply Nat.eqb_eq in Hk. rewrite Hk. exact Hin.
    - intros H. exists (k, e). split; [reflexivity|]. apply filter_In. split; [exact H|].
      apply Nat.eqb_refl.
  Qed.

  Lemma nodup_projk : forall k o, NoDup o -> NoDup (projk k o).
  Proof.
    intros k o. induction o as [|[k' e] o IH]; intros H; [constructor|].
    inversion H as [|x l Hn Hd]; subst. unfold projk; simpl.
    destruct (Nat.eqb_spec k k') as [<- | Hk]; simpl.
    - constructor; [| exact (IH Hd)]. intros Hin. apply Hn. apply (in_projk k o e). exact Hin.
    - exact (IH Hd).
  Qed.

  Lemma projk_pair : forall (k : nat) (d : list E), projk k (map (pair k) d) = d.
  Proof.
    intros k d. induction d as [|e d IH]; [reflexivity|]. unfold projk in *; simpl.
    rewrite Nat.eqb_refl. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma nodup_pair : forall (k : nat) (d : list E), NoDup d -> NoDup (map (pair k) d).
  Proof.
    intros k d H. induction H as [|e d Hn Hd IH]; simpl; constructor; [|exact IH].
    intros Hin. apply in_map_iff in Hin. destruct Hin as [e' [E' Hin]]. injection E' as ->.
    contradiction.
  Qed.

  Lemma in_pair : forall (k : nat) (d : list E) (x : nat * E), In x (map (pair k) d) <-> fst x = k /\ In (snd x) d.
  Proof.
    intros k d [k' e]. rewrite in_map_iff. simpl. split.
    - intros [e' [E' Hin]]. injection E' as -> ->. split; [reflexivity | exact Hin].
    - intros [-> Hin]. exists e. split; [reflexivity | exact Hin].
  Qed.

  (* At-least-once convergence of the collection from l0 iff of each item from its start. *)
  Theorem alo_cutoff : forall l0,
    ALOConv lst (EvL (length l0)) l0 <->
    (forall k s0, nth_error l0 k = Some s0 -> ALOConv st Ev s0).
  Proof.
    intros l0. split.
    - intros H k s0 Hk d o Hd Ho Heq.
      assert (Hlt : k < length l0) by (eapply nth_some_lt; exact Hk).
      assert (Hg : runT lst (map (pair k) d) l0 = runT lst (map (pair k) o) l0).
      { apply H.
        - apply Forall_forall. intros x Hx. apply in_pair in Hx. destruct Hx as [Hx1 Hx2].
          split; [rewrite Hx1; exact Hlt|]. rewrite Forall_forall in Hd. apply Hd. exact Hx2.
        - apply nodup_pair. exact Ho.
        - intros x. rewrite !in_pair. rewrite Heq. reflexivity. }
      pose proof (f_equal (fun m => nth_error m k) Hg) as Ek. simpl in Ek.
      rewrite !run_proj, !projk_pair, Hk in Ek. simpl in Ek. injection Ek. auto.
    - intros H d o Hd Ho Heq. apply list_ext. intros k. rewrite !run_proj.
      destruct (nth_error l0 k) as [s0|] eqn:Hk; [|reflexivity]. simpl. f_equal.
      apply (H k s0 Hk).
      + apply Forall_forall. intros e He. apply in_projk in He. rewrite Forall_forall in Hd.
        exact (proj2 (Hd _ He)).
      + apply nodup_projk. exact Ho.
      + intros e. rewrite !in_projk. apply Heq.
  Qed.

  (* With AtLeastOnceExact.alo_exact on both sides: commutation and idempotence at reachable
     states reduce per item. *)
  Theorem alo_cutoff_exact : forall l0,
    (CommReach lst (EvL (length l0)) l0 /\ forall x, IdemReach lst (EvL (length l0)) l0 x) <->
    (forall k s0, nth_error l0 k = Some s0 ->
       CommReach st Ev s0 /\ forall e, IdemReach st Ev s0 e).
  Proof.
    intros l0. rewrite <- (alo_exact (kdec edec) lst (EvL (length l0)) l0), alo_cutoff.
    split; intros H k s0 Hk; apply (alo_exact edec st Ev s0); exact (H k s0 Hk).
  Qed.

  Corollary alo_cutoff_uniform : forall n s0, 1 <= n ->
    ALOConv lst (EvL n) (repeat s0 n) <-> ALOConv st Ev s0.
  Proof.
    intros n s0 Hn. rewrite <- (len_repeat' s0 n) at 1. rewrite alo_cutoff. split.
    - intros H. apply (H 0). rewrite nth_repeat'. destruct n; [lia | reflexivity].
    - intros H k s Hk. rewrite nth_repeat' in Hk. destruct (Nat.ltb k n); [|discriminate].
      injection Hk as <-. exact H.
  Qed.

  (* Events on different items commute at every state, with no hypothesis. *)
  Theorem cross_commute : forall l k1 e1 k2 e2, k1 <> k2 ->
    lst (k1, e1) (lst (k2, e2) l) = lst (k2, e2) (lst (k1, e1) l).
  Proof.
    intros l k1 e1 k2 e2 Hk. apply list_ext. intros j. unfold lst; simpl. rewrite !modk_nth.
    destruct (nth_error l j); [|reflexivity]. simpl.
    destruct (Nat.eqb_spec j k1), (Nat.eqb_spec j k2); subst; try contradiction; reflexivity.
  Qed.

  (* Idempotence of e at k at l iff of e at item k. *)
  Theorem idem_reduces : forall l k e s, nth_error l k = Some s ->
    (lst (k, e) (lst (k, e) l) = lst (k, e) l <-> st e (st e s) = st e s).
  Proof.
    intros l k e s Hs. split.
    - intros H. pose proof (f_equal (fun m => nth_error m k) H) as Ek. simpl in Ek.
      unfold lst in Ek; simpl in Ek. rewrite !modk_nth_same, Hs in Ek. simpl in Ek.
      injection Ek. auto.
    - intros H. apply list_ext. intros j. unfold lst; simpl. rewrite !modk_nth.
      destruct (Nat.eqb_spec j k) as [-> | Hj]; rewrite ?Hs; simpl; [rewrite H; reflexivity|].
      destruct (nth_error l j); reflexivity.
  Qed.

  (* Declared independence: declare every cross-item pair, and the item's declared pairs on each
     item. The declared pairs of the collection commute at every state iff the item's do. *)
  Definition IL (I : E -> E -> Prop) (x y : nat * E) : Prop :=
    fst x <> fst y \/ (fst x = fst y /\ I (snd x) (snd y)).

  Theorem declared_cutoff : forall (I : E -> E -> Prop) n, 1 <= n ->
    (forall l x y, length l = n -> fst x < n -> fst y < n -> IL I x y ->
       lst y (lst x l) = lst x (lst y l)) <->
    (forall s e1 e2, I e1 e2 -> st e2 (st e1 s) = st e1 (st e2 s)).
  Proof.
    intros I n Hn. split.
    - intros H s e1 e2 HI.
      pose proof (H (repeat s n) (0, e1) (0, e2) (len_repeat' s n) Hn Hn
                    (or_intror (conj eq_refl HI))) as E0.
      pose proof (f_equal (fun m => nth_error m 0) E0) as Ek. unfold lst in Ek.
      destruct n as [|n]; [lia|]. simpl in Ek. injection Ek. auto.
    - intros H l [k1 e1] [k2 e2] _ _ _ HI. unfold IL in HI; simpl in HI.
      destruct (Nat.eq_dec k1 k2) as [<- | Hk].
      + destruct HI as [HI | [_ HI]]; [contradiction|]. apply list_ext. intros j.
        unfold lst; simpl. rewrite !modk_nth. destruct (nth_error l j); [|reflexivity]. simpl.
        destruct (Nat.eqb j k1); [rewrite H by exact HI|]; reflexivity.
      + symmetry. apply cross_commute. exact Hk.
  Qed.
End ALOCutoff.

(* ============================================================================================ *)
(* The collection registry (the lift) and the convergence cutoffs.                              *)
(* ============================================================================================ *)

Section Lift.
  Context {A E : Type}.
  Variable edec : forall x y : E, {x = y} + {x <> y}.
  Variable a : E -> A -> A.        (* per-item event *)
  Variable r : A -> A.             (* per-item repair step *)
  Variable v : A -> bool.          (* per-item invariant *)
  Variable Phi : A -> nat.         (* per-item WFC potential *)

  Definition valid1 (s : A) : Prop := v s = true.
  Hypothesis wfc : forall s, ~ valid1 s -> Phi (r s) < Phi s.
  (* Repair leaves valid items alone (a repair triggered by another item does not touch this one). *)
  Hypothesis r_fix : forall s, valid1 s -> r s = s.

  Definition rstar (s : A) : A := itr (Phi s) r s.
  Definition g (e : E) (s : A) : A := rstar (a e s).

  Definition aL (x : nat * E) (l : list A) : list A := modk (a (snd x)) (fst x) l.
  Definition rL (l : list A) : list A := map r l.
  Definition validL (l : list A) : Prop := forallb v l = true.
  Definition PhiL (l : list A) : nat := sumPhi Phi l.
  Definition rstarL (l : list A) : list A := map rstar l.
  Definition gL (x : nat * E) (l : list A) : list A := rstarL (aL x l).

  Local Notation istep := (step edec a r valid1 free_enabled).
  Local Notation lstep := (step (kdec edec) aL rL validL free_enabled).
  Local Notation ireach := (reach a r valid1).
  Local Notation lreach := (reach aL rL validL).

  Lemma nv_false : forall s, ~ valid1 s -> v s = false.
  Proof. intros s H. unfold valid1 in H. destruct (v s); [contradiction | reflexivity]. Qed.

  Lemma itr_valid : forall m s, Phi s <= m -> valid1 (itr m r s).
  Proof.
    induction m as [|m IH]; intros s H; simpl.
    - destruct (v s) eqn:Hv; [exact Hv|]. exfalso.
      assert (Hn : ~ valid1 s) by (unfold valid1; congruence). pose proof (wfc s Hn). lia.
    - destruct (v s) eqn:Hv.
      + rewrite (r_fix s Hv). rewrite itr_fix by (apply r_fix; exact Hv). exact Hv.
      + apply IH. assert (Hn : ~ valid1 s) by (unfold valid1; congruence).
        pose proof (wfc s Hn). lia.
  Qed.

  Lemma rstar_valid : forall s, valid1 (rstar s).
  Proof. intros s. apply itr_valid. lia. Qed.

  Lemma itr_stable : forall m s, Phi s <= m -> itr m r s = rstar s.
  Proof.
    intros m s H. replace m with (Phi s + (m - Phi s)) by lia. rewrite itr_add.
    unfold rstar. apply itr_fix. apply r_fix. apply rstar_valid.
  Qed.

  Lemma rstar_fix : forall s, valid1 s -> rstar s = s.
  Proof. intros s H. unfold rstar. apply itr_fix. apply r_fix. exact H. Qed.

  Lemma rstar_idem : forall s, rstar (rstar s) = rstar s.
  Proof. intros s. apply rstar_fix. apply rstar_valid. Qed.

  Lemma rstar_g : forall e s, rstar (g e s) = g e s.
  Proof. intros e s. apply rstar_idem. Qed.

  Lemma rstar_r : forall s, ~ valid1 s -> rstar (r s) = rstar s.
  Proof.
    intros s H. pose proof (wfc s H) as Hl. unfold rstar at 2.
    destruct (Phi s) as [|m] eqn:Ep; [lia|]. simpl. symmetry. apply itr_stable. lia.
  Qed.

  Lemma i_itr_reach : forall m s B, star istep (s, B) (itr m r s, B).
  Proof.
    induction m as [|m IH]; intros s B; simpl; [apply star_refl|].
    destruct (v s) eqn:Hv.
    - rewrite (r_fix s Hv). apply IH.
    - eapply star_step; [apply st_comp; unfold valid1; congruence | apply IH].
  Qed.

  Lemma i_reach : forall s B, star istep (s, B) (rstar s, B).
  Proof. intros s B. apply i_itr_reach. Qed.

  Lemma validL_in : forall l s, validL l -> In s l -> valid1 s.
  Proof. intros l s H Hs. unfold validL in H. rewrite forallb_forall in H. apply H. exact Hs. Qed.

  Lemma validL_nth : forall l k s, validL l -> nth_error l k = Some s -> valid1 s.
  Proof. intros l k s H Hk. apply (validL_in l). exact H. eapply nth_error_In. exact Hk. Qed.

  Lemma invalid_nth : forall l k s, nth_error l k = Some s -> ~ valid1 s -> ~ validL l.
  Proof. intros l k s Hk Hs HV. apply Hs. exact (validL_nth l k s HV Hk). Qed.

  Lemma rL_fix : forall l, validL l -> rL l = l.
  Proof.
    intros l H. unfold rL. rewrite <- (map_id l) at 2. apply map_ext_in. intros s Hs.
    apply r_fix. exact (validL_in l s H Hs).
  Qed.

  Lemma rstarL_itr : forall l, rstarL l = itr (PhiL l) rL l.
  Proof.
    intros l. unfold rstarL, rL. rewrite itr_map. apply map_ext_in. intros s Hs.
    symmetry. apply itr_stable. apply sumPhi_in. exact Hs.
  Qed.

  Lemma l_itr_reach : forall m l B, star lstep (l, B) (itr m rL l, B).
  Proof.
    induction m as [|m IH]; intros l B; simpl; [apply star_refl|].
    destruct (forallb v l) eqn:Hv.
    - rewrite (rL_fix l Hv). apply IH.
    - eapply star_step; [apply st_comp; unfold validL; congruence | apply IH].
  Qed.

  Lemma l_reach : forall l B, star lstep (l, B) (rstarL l, B).
  Proof. intros l B. rewrite rstarL_itr. apply l_itr_reach. Qed.

  Lemma rstarL_valid : forall l, validL (rstarL l).
  Proof.
    intros l. unfold validL, rstarL. apply forallb_forall. intros s Hs.
    apply in_map_iff in Hs. destruct Hs as [t [<- _]]. apply rstar_valid.
  Qed.

  Lemma wfcL : forall l, ~ validL l -> PhiL (rL l) < PhiL l.
  Proof.
    intros l H. apply (sum_wfc r v Phi r_fix); [| exact H].
    intros s Hs. apply wfc. exact Hs.
  Qed.

  Lemma gL_nth : forall k e l j,
    nth_error (gL (k, e) l) j = option_map (if Nat.eqb j k then g e else rstar) (nth_error l j).
  Proof.
    intros k e l j. unfold gL, rstarL, aL; simpl. rewrite nth_map', modk_nth.
    destruct (nth_error l j); simpl; [|reflexivity]. destruct (Nat.eqb j k); reflexivity.
  Qed.

  Lemma rL_nth : forall l j, nth_error (rL l) j = option_map r (nth_error l j).
  Proof. intros l j. apply nth_map'. Qed.

  Lemma lreach_len : forall l0 l, lreach l0 l -> length l = length l0.
  Proof.
    intros l0 l H. induction H as [| x l H IH | l H IH Hinv]; [reflexivity | |].
    - unfold aL. rewrite modk_length. exact IH.
    - unfold rL. rewrite len_map'. exact IH.
  Qed.

  (* Projection: an item of a reachable collection state is reachable in the item registry. *)
  Lemma lreach_proj : forall l0 l, lreach l0 l ->
    forall k s, nth_error l k = Some s -> exists s0, nth_error l0 k = Some s0 /\ ireach s0 s.
  Proof.
    intros l0 l H. induction H as [| [k' e] l H IH | l H IH Hinv]; intros k s Hs.
    - exists s. split; [exact Hs | constructor].
    - unfold aL in Hs; simpl in Hs. rewrite modk_nth in Hs.
      destruct (nth_error l k) as [t|] eqn:Ht; [|discriminate].
      destruct (IH k t Ht) as [s0 [H0 Hr]]. exists s0. split; [exact H0|].
      destruct (Nat.eqb k k'); simpl in Hs; injection Hs as <-; [apply r_apply|]; exact Hr.
    - rewrite rL_nth in Hs. destruct (nth_error l k) as [t|] eqn:Ht; [|discriminate].
      simpl in Hs; injection Hs as <-. destruct (IH k t Ht) as [s0 [H0 Hr]].
      exists s0. split; [exact H0|]. destruct (v t) eqn:Hv.
      + rewrite (r_fix t Hv). exact Hr.
      + apply r_comp; [exact Hr | unfold valid1; congruence].
  Qed.

  (* Lifting: an item state reachable from l0[k] is item k of a reachable collection state. *)
  Lemma ireach_lift : forall s0 s, ireach s0 s ->
    forall l0 k, nth_error l0 k = Some s0 -> exists l, lreach l0 l /\ nth_error l k = Some s.
  Proof.
    intros s0 s H. induction H as [| e s H IH | s H IH Hinv]; intros l0 k H0.
    - exists l0. split; [constructor | exact H0].
    - destruct (IH l0 k H0) as [l [Hl Hk]]. exists (aL (k, e) l). split; [apply r_apply; exact Hl|].
      unfold aL; simpl. rewrite modk_nth_same, Hk. reflexivity.
    - destruct (IH l0 k H0) as [l [Hl Hk]]. exists (rL l). split.
      + apply r_comp; [exact Hl|]. exact (invalid_nth l k s Hk Hinv).
      + rewrite rL_nth, Hk. reflexivity.
  Qed.

  (* ---- The conditions, in the form of GovernanceConverse.cc_exact_from. ---- *)

  Definition CC1i (s0 : A) : Prop :=
    forall s e1 e2, ireach s0 s -> g e2 (g e1 s) = g e1 (g e2 s).
  Definition CC2i (s0 : A) : Prop :=
    forall s e, ireach s0 s -> ~ valid1 s -> g e s = g e (r s).
  (* Repair then event equals event alone: CC2 iterated along the whole repair. *)
  Definition CC2star (s0 : A) : Prop :=
    forall s e, ireach s0 s -> g e (rstar s) = g e s.

  Definition CC1L (l0 : list A) : Prop :=
    forall l x1 x2, lreach l0 l -> gL x2 (gL x1 l) = gL x1 (gL x2 l).
  (* CC1 over the events in range (keys below the number of items). *)
  Definition CC1in (l0 : list A) : Prop :=
    forall l k1 e1 k2 e2, lreach l0 l -> k1 < length l0 -> k2 < length l0 ->
      gL (k2, e2) (gL (k1, e1) l) = gL (k1, e1) (gL (k2, e2) l).
  Definition CC2L (l0 : list A) : Prop :=
    forall l x, lreach l0 l -> ~ validL l -> gL x l = gL x (rL l).

  Theorem cc2_star : forall s0, CC2i s0 -> CC2star s0.
  Proof.
    intros s0 H2 s e Hs. remember (Phi s) as p eqn:Ep. revert s Ep Hs.
    induction p as [p IH] using (well_founded_induction lt_wf). intros s Ep Hs.
    destruct (v s) eqn:Hv; [rewrite (rstar_fix s Hv); reflexivity|].
    assert (Hn : ~ valid1 s) by (unfold valid1; congruence).
    assert (Hr : ireach s0 (r s)) by (apply r_comp; assumption).
    assert (Hlt : Phi (r s) < p) by (subst p; apply wfc; exact Hn).
    rewrite <- (rstar_r s Hn). rewrite (IH _ Hlt (r s) eq_refl Hr).
    symmetry. apply H2; assumption.
  Qed.

  Lemma gL2_nth : forall k1 e1 k2 e2 l j,
    nth_error (gL (k2, e2) (gL (k1, e1) l)) j =
    option_map (fun s => (if Nat.eqb j k2 then g e2 else rstar)
                           ((if Nat.eqb j k1 then g e1 else rstar) s)) (nth_error l j).
  Proof. intros. rewrite !gL_nth. destruct (nth_error l j); reflexivity. Qed.

  (* Two events on the same item: the collection pair commutes iff the item pair does. *)
  Theorem same_item_reduces : forall l k e1 e2 s, nth_error l k = Some s ->
    (gL (k, e2) (gL (k, e1) l) = gL (k, e1) (gL (k, e2) l) <-> g e2 (g e1 s) = g e1 (g e2 s)).
  Proof.
    intros l k e1 e2 s Hs. split.
    - intros H. pose proof (f_equal (fun m => nth_error m k) H) as Ek. simpl in Ek.
      rewrite !gL2_nth, Hs, Nat.eqb_refl in Ek. simpl in Ek. injection Ek. auto.
    - intros H. apply list_ext. intros j. rewrite !gL2_nth.
      destruct (Nat.eqb_spec j k) as [-> | Hj]; rewrite ?Hs; simpl; [rewrite H; reflexivity|].
      destruct (nth_error l j); reflexivity.
  Qed.

  (* Two events on different items: the pair commutes iff on each item, repair then event equals
     event alone. *)
  Theorem cross_item_reduces : forall l k1 e1 k2 e2 s1 s2, k1 <> k2 ->
    nth_error l k1 = Some s1 -> nth_error l k2 = Some s2 ->
    (gL (k2, e2) (gL (k1, e1) l) = gL (k1, e1) (gL (k2, e2) l) <->
     g e1 (rstar s1) = g e1 s1 /\ g e2 (rstar s2) = g e2 s2).
  Proof.
    intros l k1 e1 k2 e2 s1 s2 Hk H1 H2. split.
    - intros H. split.
      + pose proof (f_equal (fun m => nth_error m k1) H) as Ek. simpl in Ek.
        rewrite !gL2_nth, H1, Nat.eqb_refl in Ek. destruct (Nat.eqb_spec k1 k2); [contradiction|].
        simpl in Ek. injection Ek as Ek. rewrite rstar_g in Ek. symmetry. exact Ek.
      + pose proof (f_equal (fun m => nth_error m k2) H) as Ek. simpl in Ek.
        rewrite !gL2_nth, H2, Nat.eqb_refl in Ek. destruct (Nat.eqb_spec k2 k1); [congruence|].
        simpl in Ek. injection Ek as Ek. rewrite rstar_g in Ek. exact Ek.
    - intros [E1 E2]. apply list_ext. intros j. rewrite !gL2_nth.
      destruct (Nat.eqb_spec j k1) as [-> | Hj1].
      + destruct (Nat.eqb_spec k1 k2); [contradiction|]. rewrite H1. simpl.
        rewrite rstar_g, E1. reflexivity.
      + destruct (Nat.eqb_spec j k2) as [-> | Hj2].
        * rewrite H2. simpl. rewrite rstar_g, E2. reflexivity.
        * destruct (nth_error l j); reflexivity.
  Qed.

  (* At a valid state, events on different items commute with no hypothesis. *)
  Theorem cross_valid_commute : forall l k1 e1 k2 e2, k1 <> k2 -> validL l ->
    gL (k2, e2) (gL (k1, e1) l) = gL (k1, e1) (gL (k2, e2) l).
  Proof.
    intros l k1 e1 k2 e2 Hk HV.
    destruct (nth_error l k1) as [s1|] eqn:H1; destruct (nth_error l k2) as [s2|] eqn:H2.
    - apply (proj2 (cross_item_reduces l k1 e1 k2 e2 s1 s2 Hk H1 H2)).
      rewrite (rstar_fix s1 (validL_nth l k1 s1 HV H1)), (rstar_fix s2 (validL_nth l k2 s2 HV H2)).
      split; reflexivity.
    - apply list_ext. intros j. rewrite !gL2_nth.
      destruct (Nat.eqb_spec j k1) as [-> | Hj1]; [destruct (Nat.eqb_spec k1 k2); [contradiction|];
        rewrite H1; simpl; rewrite rstar_g, (rstar_fix s1 (validL_nth l k1 s1 HV H1)); reflexivity|].
      destruct (Nat.eqb_spec j k2) as [-> | Hj2]; [rewrite H2; reflexivity|].
      destruct (nth_error l j); reflexivity.
    - apply list_ext. intros j. rewrite !gL2_nth.
      destruct (Nat.eqb_spec j k1) as [-> | Hj1]; [rewrite H1; reflexivity|].
      destruct (Nat.eqb_spec j k2) as [-> | Hj2]; [rewrite H2; simpl;
        rewrite rstar_g, (rstar_fix s2 (validL_nth l k2 s2 HV H2)); reflexivity|].
      destruct (nth_error l j); reflexivity.
    - apply list_ext. intros j. rewrite !gL2_nth.
      destruct (Nat.eqb_spec j k1) as [-> | Hj1]; [rewrite H1; reflexivity|].
      destruct (Nat.eqb_spec j k2) as [-> | Hj2]; [rewrite H2; reflexivity|].
      destruct (nth_error l j); reflexivity.
  Qed.

  (* CC2: cutoff 1. *)
  Theorem cc2_cutoff : forall l0,
    CC2L l0 <-> (forall k s0, nth_error l0 k = Some s0 -> CC2i s0).
  Proof.
    intros l0. split.
    - intros H k s0 H0 s e Hs Hn. destruct (ireach_lift s0 s Hs l0 k H0) as [l [Hl Hk]].
      pose proof (f_equal (fun m => nth_error m k) (H l (k, e) Hl (invalid_nth l k s Hk Hn))) as Ek.
      simpl in Ek. rewrite !gL_nth, rL_nth, Hk, Nat.eqb_refl in Ek. simpl in Ek.
      injection Ek. auto.
    - intros H l [k e] Hl HnL. apply list_ext. intros j. rewrite !gL_nth, rL_nth.
      destruct (nth_error l j) as [s|] eqn:Hj; [|reflexivity]. simpl. f_equal.
      destruct (lreach_proj l0 l Hl j s Hj) as [s0 [H0 Hs]].
      destruct (v s) eqn:Hv; [rewrite (r_fix s Hv); reflexivity|].
      assert (Hn : ~ valid1 s) by (unfold valid1; congruence).
      destruct (Nat.eqb j k); [exact (H j s0 H0 s e Hs Hn) | symmetry; apply rstar_r; exact Hn].
  Qed.

  (* The positionwise content of CC1 at one item. *)
  Lemma pos_comm : forall s0 s j k1 e1 k2 e2, ireach s0 s -> CC1i s0 ->
    (k1 <> k2 -> CC2star s0) ->
    (if Nat.eqb j k2 then g e2 else rstar) ((if Nat.eqb j k1 then g e1 else rstar) s) =
    (if Nat.eqb j k1 then g e1 else rstar) ((if Nat.eqb j k2 then g e2 else rstar) s).
  Proof.
    intros s0 s j k1 e1 k2 e2 Hs H1 H2.
    destruct (Nat.eqb_spec j k1) as [-> | Hj1]; destruct (Nat.eqb_spec k1 k2) as [<- | Hk];
      rewrite ?Nat.eqb_refl.
    - apply H1. exact Hs.
    - destruct (Nat.eqb_spec k1 k2); [contradiction|].
      rewrite rstar_g. symmetry. exact (H2 Hk s e1 Hs).
    - destruct (Nat.eqb_spec j k1); [contradiction|]. reflexivity.
    - destruct (Nat.eqb_spec j k2) as [-> | Hj2].
      + rewrite rstar_g. exact (H2 (fun E => Hk E) s e2 Hs).
      + reflexivity.
  Qed.

  (* CC1 and CC2 together: cutoff 1. *)
  Theorem cc_lift_iff : forall l0,
    (CC1L l0 /\ CC2L l0) <-> (forall k s0, nth_error l0 k = Some s0 -> CC1i s0 /\ CC2i s0).
  Proof.
    intros l0. split.
    - intros [H1 H2] k s0 H0. split; [| exact (proj1 (cc2_cutoff l0) H2 k s0 H0)].
      intros s e1 e2 Hs. destruct (ireach_lift s0 s Hs l0 k H0) as [l [Hl Hk]].
      exact (proj1 (same_item_reduces l k e1 e2 s Hk) (H1 l (k, e1) (k, e2) Hl)).
    - intros H. split; [| apply cc2_cutoff; intros k s0 H0; exact (proj2 (H k s0 H0))].
      intros l [k1 e1] [k2 e2] Hl. apply list_ext. intros j. rewrite !gL2_nth.
      destruct (nth_error l j) as [s|] eqn:Hj; [|reflexivity]. simpl. f_equal.
      destruct (lreach_proj l0 l Hl j s Hj) as [s0 [H0 Hs]].
      destruct (H j s0 H0) as [C1 C2].
      apply (pos_comm s0); [exact Hs | exact C1 | intros _; exact (cc2_star s0 C2)].
  Qed.

  (* Unique normal forms: cutoff 1. Every event buffer from l0 has a unique normal form iff every
     event buffer from each item's start does. *)
  Theorem un_cutoff : forall l0,
    (forall B, UN lstep (l0, B)) <->
    (forall k s0, nth_error l0 k = Some s0 -> forall B, UN istep (s0, B)).
  Proof.
    intros l0.
    pose proof (cc_exact_from (kdec edec) aL rL rstarL validL PhiL wfcL l_reach rstarL_valid l0)
      as HL.
    split.
    - intros H k s0 H0.
      apply (proj2 (cc_exact_from edec a r rstar valid1 Phi wfc i_reach rstar_valid s0)).
      destruct (proj1 HL H) as [C1 C2].
      exact (proj1 (cc_lift_iff l0) (conj C1 C2) k s0 H0).
    - intros H. apply (proj2 HL).
      assert (Hc : forall k s0, nth_error l0 k = Some s0 -> CC1i s0 /\ CC2i s0).
      { intros k s0 H0.
        exact (proj1 (cc_exact_from edec a r rstar valid1 Phi wfc i_reach rstar_valid s0)
                 (H k s0 H0)). }
      destruct (proj2 (cc_lift_iff l0) Hc) as [C1 C2]. split; [exact C1 | exact C2].
  Qed.

  Corollary un_cutoff_uniform : forall n s0, 1 <= n ->
    (forall B, UN lstep (repeat s0 n, B)) <-> (forall B, UN istep (s0, B)).
  Proof.
    intros n s0 Hn. rewrite un_cutoff. split.
    - intros H. apply (H 0). rewrite nth_repeat'. destruct n; [lia | reflexivity].
    - intros H k s Hk. rewrite nth_repeat' in Hk. destruct (Nat.ltb k n); [|discriminate].
      injection Hk as <-. exact H.
  Qed.

  Corollary un_cutoff_global :
    (forall l B, UN lstep (l, B)) <-> (forall s B, UN istep (s, B)).
  Proof.
    split.
    - intros H s. apply (proj1 (un_cutoff_uniform 1 s (le_n 1))). apply H.
    - intros H l. apply un_cutoff. intros k s0 _. apply H.
  Qed.

  (* CC1 alone (events in range): cutoff 2. With two or more items, CC1 also asks, for each item,
     that repair then event equal event alone. *)
  Theorem cc1_cutoff : forall l0,
    CC1in l0 <->
    (forall k s0, nth_error l0 k = Some s0 -> CC1i s0 /\ (2 <= length l0 -> CC2star s0)).
  Proof.
    intros l0. split.
    - intros H k s0 H0. assert (Hk : k < length l0) by (eapply nth_some_lt; exact H0). split.
      + intros s e1 e2 Hs. destruct (ireach_lift s0 s Hs l0 k H0) as [l [Hl Hkl]].
        exact (proj1 (same_item_reduces l k e1 e2 s Hkl) (H l k e1 k e2 Hl Hk Hk)).
      + intros H2 s e Hs. destruct (ireach_lift s0 s Hs l0 k H0) as [l [Hl Hkl]].
        set (j := if Nat.eqb k 0 then 1 else 0).
        assert (Hjk : j <> k) by (unfold j; destruct (Nat.eqb_spec k 0); lia).
        assert (Hj : j < length l0) by (unfold j; destruct (Nat.eqb k 0); lia).
        assert (Hjl : j < length l) by (rewrite (lreach_len l0 l Hl); exact Hj).
        destruct (nth_lt_some l j Hjl) as [t Ht].
        pose proof (proj1 (cross_item_reduces l k e j e s t (fun E => Hjk (eq_sym E)) Hkl Ht)
                      (H l k e j e Hl Hk Hj)) as [E1 _].
        exact E1.
    - intros H l k1 e1 k2 e2 Hl Hk1 Hk2. apply list_ext. intros j. rewrite !gL2_nth.
      destruct (nth_error l j) as [s|] eqn:Hj; [|reflexivity]. simpl. f_equal.
      destruct (lreach_proj l0 l Hl j s Hj) as [s0 [H0 Hs]].
      destruct (H j s0 H0) as [C1 C2].
      apply (pos_comm s0); [exact Hs | exact C1 |]. intros Hne. apply C2. lia.
  Qed.

  Corollary cc1_cutoff_one : forall s0, CC1in [s0] <-> CC1i s0.
  Proof.
    intros s0. rewrite cc1_cutoff. split.
    - intros H. exact (proj1 (H 0 s0 eq_refl)).
    - intros H [|k] s Hk; simpl in Hk; [injection Hk as <- | destruct k; discriminate].
      split; [exact H | simpl; lia].
  Qed.

  Corollary cc1_cutoff_uniform2 : forall n s0, 2 <= n ->
    CC1in (repeat s0 n) <-> CC1in (repeat s0 2).
  Proof.
    intros n s0 Hn. rewrite !cc1_cutoff, !len_repeat'.
    assert (G : forall m, 2 <= m -> (forall k s, nth_error (repeat s0 m) k = Some s ->
                  CC1i s /\ (2 <= m -> CC2star s)) <-> CC1i s0 /\ CC2star s0).
    { intros m Hm. split.
      - intros H. destruct (H 0 s0) as [C1 C2]; [rewrite nth_repeat'; destruct m; [lia|reflexivity]|].
        split; [exact C1 | exact (C2 Hm)].
      - intros [C1 C2] k s Hk. rewrite nth_repeat' in Hk. destruct (Nat.ltb k m); [|discriminate].
        injection Hk as <-. split; [exact C1 | intros _; exact C2]. }
    rewrite (G n Hn), (G 2 (le_n 2)). reflexivity.
  Qed.

  Corollary cc2_cutoff_uniform : forall n s0, 1 <= n -> CC2L (repeat s0 n) <-> CC2i s0.
  Proof.
    intros n s0 Hn. rewrite cc2_cutoff. split.
    - intros H. apply (H 0). rewrite nth_repeat'. destruct n; [lia | reflexivity].
    - intros H k s Hk. rewrite nth_repeat' in Hk. destruct (Nat.ltb k n); [|discriminate].
      injection Hk as <-. exact H.
  Qed.

  (* ---- The converse from buffers whose events are in range, by simulating item runs. ---- *)

  Lemma sim_step : forall c c', istep c c' -> forall L k, nth_error L k = Some (fst c) ->
    exists L', lstep (L, map (pair k) (snd c)) (L', map (pair k) (snd c')) /\
               nth_error L' k = Some (fst c').
  Proof.
    intros c c' H. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst;
      intros L k HL; simpl in *.
    - exists (aL (k, e) L). split.
      + rewrite <- remove1_pair. apply st_apply; apply in_map; exact Hin.
      + unfold aL; simpl. rewrite modk_nth_same, HL. reflexivity.
    - exists (rL L). split.
      + apply st_comp. exact (invalid_nth L k s HL Hinv).
      + rewrite rL_nth, HL. reflexivity.
  Qed.

  Lemma sim_star : forall c c', star istep c c' -> forall L k, nth_error L k = Some (fst c) ->
    exists L', star lstep (L, map (pair k) (snd c)) (L', map (pair k) (snd c')) /\
               nth_error L' k = Some (fst c').
  Proof.
    intros c c' H. induction H as [c | c c1 c2 H1 _ IH]; intros L k HL.
    - exists L. split; [apply star_refl | exact HL].
    - destruct (sim_step c c1 H1 L k HL) as [L1 [S1 E1]].
      destruct (IH L1 k E1) as [L2 [S2 E2]]. exists L2. split; [eapply star_step; eassumption | exact E2].
  Qed.

  Lemma inf_nf : forall s B, normal_form istep (s, B) -> B = [] /\ valid1 s.
  Proof.
    intros s B H. split.
    - destruct B as [|e B]; [reflexivity|]. exfalso. apply H.
      exists (a e s, remove1 edec e (e :: B)). apply st_apply; left; reflexivity.
    - destruct (v s) eqn:Hv; [exact Hv|]. exfalso. apply H. exists (r s, B).
      apply st_comp. unfold valid1; congruence.
  Qed.

  Lemma lnf_valid : forall l, validL l -> normal_form lstep (l, []).
  Proof.
    intros l HV [y H]. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst.
    - destruct Hin.
    - contradiction.
  Qed.

  Theorem un_in_to_item : forall l0,
    (forall B, Forall (fun x => fst x < length l0) B -> UN lstep (l0, B)) ->
    forall k s0, nth_error l0 k = Some s0 -> forall B, UN istep (s0, B).
  Proof.
    intros l0 H k s0 Hk B [t1 B1] [t2 B2] S1 N1 S2 N2.
    destruct (inf_nf t1 B1 N1) as [-> V1]. destruct (inf_nf t2 B2 N2) as [-> V2].
    destruct (sim_star _ _ S1 l0 k Hk) as [L1 [T1 K1]].
    destruct (sim_star _ _ S2 l0 k Hk) as [L2 [T2 K2]]. simpl in *.
    assert (Hin : Forall (fun x => fst x < length l0) (map (pair k) B)).
    { apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [e [<- _]].
      simpl. eapply nth_some_lt; exact Hk. }
    pose proof (H _ Hin (rstarL L1, []) (rstarL L2, [])
                  (star_trans _ _ _ _ T1 (l_reach L1 []))
                  (lnf_valid _ (rstarL_valid L1))
                  (star_trans _ _ _ _ T2 (l_reach L2 []))
                  (lnf_valid _ (rstarL_valid L2))) as EL.
    injection EL as EL. pose proof (f_equal (fun m => nth_error m k) EL) as Ek. simpl in Ek.
    unfold rstarL in Ek. rewrite !nth_map', K1, K2 in Ek. simpl in Ek. injection Ek as Ek.
    rewrite (rstar_fix t1 V1), (rstar_fix t2 V2) in Ek. subst. reflexivity.
  Qed.

  (* ---- At-least-once for governed steps: from a valid start the governed collection step is
     the lift of the governed item step. ---- *)

  Lemma gL_lst : forall x l, validL l -> gL x l = lst g x l.
  Proof.
    intros [k e] l HV. apply list_ext. intros j. rewrite gL_nth. unfold lst; simpl.
    rewrite modk_nth. destruct (nth_error l j) as [s|] eqn:Hj; [|reflexivity]. simpl.
    destruct (Nat.eqb j k); [reflexivity|]. rewrite (rstar_fix s (validL_nth l j s HV Hj)).
    reflexivity.
  Qed.

  Lemma lst_g_valid : forall x l, validL l -> validL (lst g x l).
  Proof.
    intros [k e] l HV. unfold validL, lst. apply forallb_forall. intros s Hs.
    apply In_nth_error in Hs. destruct Hs as [j Hj]. simpl in Hj. rewrite modk_nth in Hj.
    destruct (nth_error l j) as [t|] eqn:Ht; [|discriminate]. simpl in Hj.
    destruct (Nat.eqb j k); injection Hj as <-; [apply rstar_valid | exact (validL_nth l j t HV Ht)].
  Qed.

  Lemma run_bridge : forall d l, validL l -> runT gL d l = runT (lst g) d l.
  Proof.
    induction d as [|x d IH]; intros l HV; [reflexivity|]. rewrite !runT_cons, gL_lst by exact HV.
    apply IH. apply lst_g_valid. exact HV.
  Qed.

  Theorem alo_gov_cutoff : forall (Ev : E -> Prop) l0, validL l0 ->
    ALOConv gL (EvL Ev (length l0)) l0 <->
    (forall k s0, nth_error l0 k = Some s0 -> ALOConv g Ev s0).
  Proof.
    intros Ev l0 HV. rewrite <- (alo_cutoff g Ev l0). unfold ALOConv.
    split; intros H d o Hd Ho Heq; [rewrite <- !run_bridge by exact HV | rewrite !run_bridge by exact HV];
      apply H; assumption.
  Qed.
End Lift.

(* ============================================================================================ *)
(* Federation: C1 and C2 for a target collection whose morphism maps items pointwise.            *)
(* ============================================================================================ *)

Section FedCutoff.
  Context {Z A E : Type}.
  Variable ow : Z -> A -> A.      (* item morphism repair: overwrite from the source item *)
  Variable sig : E -> A -> A.     (* item event of the target (event then item normalizer) *)
  Variable vz : Z -> Prop.        (* valid source item *)
  Variable va : A -> Prop.        (* valid target item *)
  Variable I : E -> E -> Prop.    (* declared independence on the item *)
  (* FederationEvents.Common's c_absorb and c_sig, per item. *)
  Hypothesis absorb : forall z z' x, vz z -> vz z' -> va x -> ow z (ow z' x) = ow z x.
  Hypothesis sig_valid : forall e x, va x -> va (sig e x).

  Fixpoint owL (zs : list Z) (xs : list A) : list A :=
    match zs, xs with
    | z :: zs', x :: xs' => ow z x :: owL zs' xs'
    | _, _ => []
    end.
  Definition sigL (x : nat * E) (xs : list A) : list A := modk (sig (snd x)) (fst x) xs.

  Lemma owL_nth : forall zs xs j, nth_error (owL zs xs) j =
    match nth_error zs j, nth_error xs j with Some z, Some x => Some (ow z x) | _, _ => None end.
  Proof.
    induction zs as [|z zs IH]; intros [|x xs] [|j]; simpl; auto.
    destruct (nth_error zs j); reflexivity.
  Qed.

  Lemma owL_repeat : forall z x n, owL (repeat z n) (repeat x n) = repeat (ow z x) n.
  Proof. intros z x n; induction n; simpl; f_equal; auto. Qed.

  (* C1 (FederationEvents.C1) for one target item with one source item. *)
  Definition C1i : Prop :=
    forall e z z' b, vz z -> vz z' -> va b -> b = ow z' b -> ow z (sig e (ow z b)) = ow z (sig e b).
  Definition C1c (n : nat) : Prop :=
    forall k e zs zs' bs, k < n -> length zs = n -> length zs' = n -> length bs = n ->
      Forall vz zs -> Forall vz zs' -> Forall va bs -> bs = owL zs' bs ->
      owL zs (sigL (k, e) (owL zs bs)) = owL zs (sigL (k, e) bs).

  (* C2 (FederationEvents.C2): declared pairs; in the collection every cross-item pair is
     declared, and same-item pairs are declared as on the item. *)
  Definition C2i : Prop :=
    forall e1 e2 z b, I e1 e2 -> vz z -> va b -> b = ow z b ->
      ow z (sig e2 (ow z (sig e1 b))) = ow z (sig e1 (ow z (sig e2 b))).
  Definition C2c (n : nat) : Prop :=
    forall k1 e1 k2 e2 zs bs, k1 < n -> k2 < n -> length zs = n -> length bs = n ->
      Forall vz zs -> Forall va bs -> bs = owL zs bs -> (k1 <> k2 \/ I e1 e2) ->
      owL zs (sigL (k2, e2) (owL zs (sigL (k1, e1) bs))) =
      owL zs (sigL (k1, e1) (owL zs (sigL (k2, e2) bs))).

  Lemma fa_nth : forall {X : Type} (P : X -> Prop) l j x, Forall P l -> nth_error l j = Some x -> P x.
  Proof. intros X P l j x H Hj. rewrite Forall_forall in H. apply H. eapply nth_error_In; exact Hj. Qed.

  Theorem c1_cutoff : forall n, 1 <= n -> (C1c n <-> C1i).
  Proof.
    intros n Hn. split.
    - intros H e z z' b Hz Hz' Hb Hc.
      assert (Hrep : forall (X : Type) (P : X -> Prop) x, P x -> Forall P (repeat x n)).
      { intros X P x Px. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst. exact Px. }
      pose proof (H 0 e (repeat z n) (repeat z' n) (repeat b n) Hn (len_repeat' z n)
                    (len_repeat' z' n) (len_repeat' b n) (Hrep _ _ _ Hz) (Hrep _ _ _ Hz')
                    (Hrep _ _ _ Hb) ltac:(rewrite owL_repeat, <- Hc; reflexivity)) as E0.
      rewrite !owL_repeat in E0. unfold sigL in E0. destruct n as [|n]; [lia|]. simpl in E0.
      injection E0. auto.
    - intros H k e zs zs' bs Hk Lz Lz' Lb Vz Vz' Vb Hc. unfold C1i in H. apply list_ext. intros j.
      unfold sigL; simpl. rewrite !owL_nth, !modk_nth, !owL_nth.
      destruct (nth_error zs j) as [z|] eqn:Hzj; [|reflexivity].
      destruct (nth_error bs j) as [b|] eqn:Hbj; [|reflexivity]. simpl.
      assert (Hj : j < n) by (rewrite <- Lb; eapply nth_some_lt; exact Hbj).
      destruct (nth_lt_some zs' j ltac:(lia)) as [z' Hz'j].
      assert (Hcb : b = ow z' b).
      { pose proof (f_equal (fun m => nth_error m j) Hc) as Ej. simpl in Ej.
        rewrite owL_nth, Hz'j, Hbj in Ej. injection Ej. auto. }
      destruct (Nat.eqb j k); f_equal.
      + apply (H e z z' b); [exact (fa_nth vz zs j z Vz Hzj) | exact (fa_nth vz zs' j z' Vz' Hz'j)
                 | exact (fa_nth va bs j b Vb Hbj) | exact Hcb].
      + apply absorb; [exact (fa_nth vz zs j z Vz Hzj) | exact (fa_nth vz zs j z Vz Hzj)
                      | exact (fa_nth va bs j b Vb Hbj)].
  Qed.

  Theorem c2_cutoff : forall n, 1 <= n -> (C2c n <-> C2i).
  Proof.
    intros n Hn. split.
    - intros H e1 e2 z b HI Hz Hb Hc.
      assert (Hrep : forall (X : Type) (P : X -> Prop) x, P x -> Forall P (repeat x n)).
      { intros X P x Px. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst. exact Px. }
      pose proof (H 0 e1 0 e2 (repeat z n) (repeat b n) Hn Hn (len_repeat' z n) (len_repeat' b n)
                    (Hrep _ _ _ Hz) (Hrep _ _ _ Hb)
                    ltac:(rewrite owL_repeat, <- Hc; reflexivity) (or_intror HI)) as E0.
      unfold sigL in E0. destruct n as [|n]; [lia|]. simpl in E0. injection E0. auto.
    - intros H k1 e1 k2 e2 zs bs Hk1 Hk2 Lz Lb Vz Vb Hc HI. unfold C2i in H. apply list_ext. intros j.
      unfold sigL; simpl. rewrite !owL_nth, !modk_nth, !owL_nth, !modk_nth.
      destruct (nth_error zs j) as [z|] eqn:Hzj; [|reflexivity].
      destruct (nth_error bs j) as [b|] eqn:Hbj; [|reflexivity]. simpl.
      assert (Vzj : vz z) by exact (fa_nth vz zs j z Vz Hzj).
      assert (Vbj : va b) by exact (fa_nth va bs j b Vb Hbj).
      assert (Hcb : b = ow z b).
      { pose proof (f_equal (fun m => nth_error m j) Hc) as Ej. simpl in Ej.
        rewrite owL_nth, Hzj, Hbj in Ej. injection Ej. auto. }
      f_equal.
      destruct (Nat.eqb_spec j k1) as [-> | Hj1]; destruct (Nat.eqb_spec k1 k2) as [<- | Hk].
      + destruct HI as [HI | HI]; [contradiction|]. apply H; assumption.
      + destruct (Nat.eqb_spec k1 k2); [contradiction|].
        rewrite (absorb z z (sig e1 b)) by auto. rewrite <- Hcb. reflexivity.
      + destruct (Nat.eqb_spec j k1); [contradiction|]. reflexivity.
      + destruct (Nat.eqb_spec j k2) as [-> | Hj2]; [|reflexivity].
        rewrite (absorb z z (sig e2 b)) by auto. rewrite <- Hcb. reflexivity.
  Qed.
End FedCutoff.

(* ============================================================================================ *)
(* The hypotheses, made precise and checkable.                                                   *)
(* ============================================================================================ *)

Section Symmetry.
  Context {A E : Type}.
  Variable n : nat.
  Variable aG : nat * E -> list A -> list A.   (* any registry over n items *)
  Variable rG : list A -> list A.
  Variable vG : list A -> bool.

  (* Independent and identically governed. *)
  Record IdGov : Prop := {
    ig_len : forall k e l, length l = n -> k < n -> length (aG (k, e) l) = n;
    (* an event at k writes only k *)
    ig_write : forall k e l j, length l = n -> k < n -> j <> k ->
      nth_error (aG (k, e) l) j = nth_error l j;
    (* an event at k reads only k *)
    ig_read : forall k e l l', length l = n -> length l' = n -> k < n ->
      nth_error l k = nth_error l' k -> nth_error (aG (k, e) l) k = nth_error (aG (k, e) l') k;
    (* the same rules for every key: invariance under exchanging two keys *)
    ig_perm : forall i j k e l, i < n -> j < n -> k < n -> length l = n ->
      aG (k, e) (swap i j l) = swap i j (aG (tau i j k, e) l);
    ig_rlen : forall l, length l = n -> length (rG l) = n;
    (* repair at k reads and writes only k *)
    ig_rread : forall l l' k, length l = n -> length l' = n -> k < n ->
      nth_error l k = nth_error l' k -> nth_error (rG l) k = nth_error (rG l') k;
    ig_rperm : forall i j l, i < n -> j < n -> length l = n -> rG (swap i j l) = swap i j (rG l);
    (* the invariant is the conjunction of the item invariants (no aggregate) *)
    ig_valid : forall l, length l = n -> vG l = forallb (fun s => vG (repeat s n)) l
  }.

  (* The one-item restriction. *)
  Definition xa (e : E) (s : A) : A := hd s (aG (0, e) (repeat s n)).
  Definition xr (s : A) : A := hd s (rG (repeat s n)).
  Definition xv (s : A) : bool := vG (repeat s n).

  Definition IsLift : Prop :=
    forall l, length l = n ->
      (forall k e, k < n -> aG (k, e) l = modk (xa e) k l) /\ rG l = map xr l /\ vG l = forallb xv l.

  Lemma hd_nth : forall (L : list A) s, 1 <= length L -> nth_error L 0 = Some (hd s L).
  Proof. intros [|x L] s H; simpl in *; [lia | reflexivity]. Qed.

  (* For n >= 1: independent and identically governed iff the lift of the one-item restriction. *)
  Theorem idgov_lift : 1 <= n -> (IdGov <-> IsLift).
  Proof.
    intros Hn. split.
    - intros G l Hl. split; [| split].
      + intros k e Hk. apply list_ext. intros j. rewrite modk_nth.
        destruct (Nat.eqb_spec j k) as [-> | Hj].
        * destruct (nth_lt_some l k ltac:(lia)) as [s Hs]. rewrite Hs. simpl.
          set (R := repeat s n).
          assert (HR : length R = n) by apply len_repeat'.
          assert (HRk : nth_error R k = Some s) by (unfold R; rewrite nth_repeat'; apply Nat.ltb_lt in Hk; rewrite Hk; reflexivity).
          rewrite (ig_read G k e l R Hl HR Hk ltac:(rewrite Hs, HRk; reflexivity)).
          pose proof (ig_perm G 0 k k e R Hn Hk Hk HR) as P.
          unfold R in P. rewrite (swap_repeat 0 k s n Hn Hk), tau_0kk in P. fold R in P. rewrite P.
          rewrite swap_nth by (rewrite (ig_len G 0 e R HR Hn); lia). rewrite tau_0kk.
          unfold xa. fold R. apply hd_nth. rewrite (ig_len G 0 e R HR Hn). exact Hn.
        * rewrite (ig_write G k e l j Hl Hk Hj). destruct (nth_error l j); reflexivity.
      + apply list_ext. intros j. rewrite nth_map'.
        destruct (nth_error l j) as [s|] eqn:Hs.
        * assert (Hj : j < n) by (rewrite <- Hl; eapply nth_some_lt; exact Hs).
          set (R := repeat s n). assert (HR : length R = n) by apply len_repeat'.
          assert (HRj : nth_error R j = Some s) by (unfold R; rewrite nth_repeat'; apply Nat.ltb_lt in Hj; rewrite Hj; reflexivity).
          rewrite (ig_rread G l R j Hl HR Hj ltac:(rewrite Hs, HRj; reflexivity)).
          pose proof (ig_rperm G 0 j R Hn Hj HR) as P.
          unfold R in P. rewrite (swap_repeat 0 j s n Hn Hj) in P. fold R in P. rewrite P.
          rewrite swap_nth by (rewrite (ig_rlen G R HR); lia). rewrite tau_0kk. simpl.
          unfold xr. fold R. apply hd_nth. rewrite (ig_rlen G R HR). exact Hn.
        * apply nth_error_None. rewrite (ig_rlen G l Hl). rewrite <- Hl. apply nth_error_None. exact Hs.
      + exact (ig_valid G l Hl).
    - intros L. constructor.
      + intros k e l Hl Hk. rewrite (proj1 (L l Hl) k e Hk), modk_length. exact Hl.
      + intros k e l j Hl Hk Hj. rewrite (proj1 (L l Hl) k e Hk). apply modk_nth_other. exact Hj.
      + intros k e l l' Hl Hl' Hk Heq. rewrite (proj1 (L l Hl) k e Hk), (proj1 (L l' Hl') k e Hk).
        rewrite !modk_nth_same, Heq. reflexivity.
      + intros i j k e l Hi Hj Hk Hl.
        assert (Hs : length (swap i j l) = n) by (rewrite swap_length; exact Hl).
        rewrite (proj1 (L _ Hs) k e Hk), (proj1 (L l Hl) (tau i j k) e (tau_lt i j k n Hi Hj Hk)).
        apply list_ext. intros m.
        rewrite swap_nth by (rewrite modk_length; lia). rewrite !modk_nth.
        rewrite swap_nth by lia. rewrite tau_eqb. reflexivity.
      + intros l Hl. rewrite (proj1 (proj2 (L l Hl))), len_map'. exact Hl.
      + intros l l' k Hl Hl' Hk Heq. rewrite (proj1 (proj2 (L l Hl))), (proj1 (proj2 (L l' Hl'))).
        rewrite !nth_map', Heq. reflexivity.
      + intros i j l Hi Hj Hl.
        assert (Hs : length (swap i j l) = n) by (rewrite swap_length; exact Hl).
        rewrite (proj1 (proj2 (L _ Hs))), (proj1 (proj2 (L l Hl))). apply list_ext. intros m.
        rewrite nth_map', !swap_nth by (rewrite ?len_map'; lia). rewrite nth_map'. reflexivity.
      + intros l Hl. exact (proj2 (proj2 (L l Hl))).
  Qed.

  (* ---- A decision procedure on finite descriptions. ---- *)
  Variable adec : forall x y : A, {x = y} + {x <> y}.
  Variable enumA : list A.
  Hypothesis enumA_full : forall s, In s enumA.
  Variable enumE : list E.
  Hypothesis enumE_full : forall e, In e enumE.

  Fixpoint tuples (m : nat) : list (list A) :=
    match m with
    | 0 => [[]]
    | S m' => flat_map (fun s => map (cons s) (tuples m')) enumA
    end.

  Lemma tuples_spec : forall m l, In l (tuples m) <-> length l = m.
  Proof.
    induction m as [|m IH]; intros l; simpl.
    - split; [intros [<- | []]; reflexivity | destruct l; [left; reflexivity | discriminate]].
    - rewrite in_flat_map. split.
      + intros [s [_ Hs]]. apply in_map_iff in Hs. destruct Hs as [t [<- Ht]]. simpl.
        f_equal. apply IH. exact Ht.
      + destruct l as [|s t]; [discriminate|]. intros Hl. exists s. split; [apply enumA_full|].
        apply in_map. apply IH. simpl in Hl. lia.
  Qed.

  Definition beql (l1 l2 : list A) : bool := if list_eq_dec adec l1 l2 then true else false.

  Lemma beql_spec : forall l1 l2, beql l1 l2 = true <-> l1 = l2.
  Proof. intros l1 l2. unfold beql. destruct (list_eq_dec adec l1 l2); split; congruence. Qed.

  Definition check_at (l : list A) : bool :=
    forallb (fun k => forallb (fun e => beql (aG (k, e) l) (modk (xa e) k l)) enumE) (seq 0 n)
    && beql (rG l) (map xr l) && Bool.eqb (vG l) (forallb xv l).

  Definition symcheck : bool := forallb check_at (tuples n).

  Theorem symcheck_spec : symcheck = true <-> IsLift.
  Proof.
    unfold symcheck, IsLift. rewrite forallb_forall. split.
    - intros H l Hl. pose proof (H l (proj2 (tuples_spec n l) Hl)) as C. unfold check_at in C.
      apply andb_true_iff in C. destruct C as [C V]. apply andb_true_iff in C. destruct C as [C R].
      split; [| split].
      + intros k e Hk. rewrite forallb_forall in C.
        pose proof (C k ltac:(apply in_seq; lia)) as Ck. rewrite forallb_forall in Ck.
        apply beql_spec. apply Ck. apply enumE_full.
      + apply beql_spec. exact R.
      + apply eqb_true_iff. exact V.
    - intros H l Hl. apply tuples_spec in Hl. destruct (H l Hl) as [Ha [Hr Hv]].
      unfold check_at. apply andb_true_iff. split; [apply andb_true_iff; split |].
      + apply forallb_forall. intros k Hk. apply in_seq in Hk. apply forallb_forall. intros e _.
        apply beql_spec. apply Ha. lia.
      + apply beql_spec. exact Hr.
      + apply eqb_true_iff. exact Hv.
  Qed.

  (* Sound and complete: on finite descriptions the check decides the hypotheses. *)
  Theorem symcheck_decides : 1 <= n -> (symcheck = true <-> IdGov).
  Proof. intros Hn. rewrite symcheck_spec. symmetry. apply idgov_lift. exact Hn. Qed.
End Symmetry.

(* Every lift is independent and identically governed. *)
Theorem lift_idgov : forall {A E : Type} (a : E -> A -> A) (r : A -> A) (v : A -> bool) n,
  1 <= n -> IdGov n (aL a) (rL r) (fun l => forallb v l).
Proof.
  intros A E a r v n Hn. apply idgov_lift; [exact Hn|]. intros l Hl.
  assert (Hx : forall (f : A -> A) s, hd s (map f (repeat s n)) = f s)
    by (intros f s; destruct n; [lia | reflexivity]).
  assert (Hv : forall s, forallb v (repeat s n) = v s).
  { intros s. destruct n as [|m]; [lia|]. clear Hn Hx l Hl.
    induction m as [|m IHm]; [apply andb_true_r|].
    change (forallb v (repeat s (S (S m)))) with (v s && forallb v (repeat s (S m))).
    rewrite IHm. apply andb_diag. }
  split; [| split].
  - intros k e Hk. unfold aL, xa; simpl. f_equal. clear Hk.
    destruct n as [|m]; [lia|]. reflexivity.
  - unfold rL, xr. apply map_ext. intros s. symmetry. apply Hx.
  - unfold xv. clear Hl. induction l as [|s l IH]; [reflexivity|]. simpl. rewrite IH.
    f_equal. symmetry. apply Hv.
Qed.

(* ============================================================================================ *)
(* Soundness of the reduction for a registry that passes the check.                             *)
(* ============================================================================================ *)

Section Transfer.
  Context {A E : Type}.
  Variable edec : forall x y : E, {x = y} + {x <> y}.
  Variable n : nat.
  Variable aG : nat * E -> list A -> list A.
  Variable rG : list A -> list A.
  Variable vG : list A -> bool.

  Local Notation a1 := (xa n aG).
  Local Notation r1 := (xr n rG).
  Local Notation v1 := (xv n vG).
  Definition Gstep := step (kdec edec) aG rG (fun l => vG l = true) free_enabled.
  Local Notation Lstep := (step (kdec edec) (aL a1) (rL r1) (validL v1) free_enabled).

  Definition InC (c : list A * list (nat * E)) : Prop :=
    length (fst c) = n /\ Forall (fun x => fst x < n) (snd c).

  Hypothesis HL : IsLift n aG rG vG.

  Lemma step_agree : forall c d, InC c -> (Gstep c d <-> Lstep c d).
  Proof.
    intros [l B] d Hc. split; intros H.
    - inversion H as [s B0 [k e] Hin Hen E1 E2 | s B0 Hinv E1 E2]; subst;
        destruct Hc as [Hl HB]; simpl in Hl, HB; destruct (HL l Hl) as [Ha [Hr Hv]].
      + pose proof (proj1 (Forall_forall _ _) HB _ Hin) as Hk. simpl in Hk.
        assert (Eq : aG (k, e) l = aL a1 (k, e) l) by (unfold aL; simpl; apply Ha; exact Hk).
        rewrite Eq. apply st_apply; assumption.
      + rewrite Hr. apply st_comp. unfold validL. rewrite <- Hv. exact Hinv.
    - inversion H as [s B0 [k e] Hin Hen E1 E2 | s B0 Hinv E1 E2]; subst;
        destruct Hc as [Hl HB]; simpl in Hl, HB; destruct (HL l Hl) as [Ha [Hr Hv]].
      + pose proof (proj1 (Forall_forall _ _) HB _ Hin) as Hk. simpl in Hk.
        assert (Eq : aG (k, e) l = aL a1 (k, e) l) by (unfold aL; simpl; apply Ha; exact Hk).
        rewrite <- Eq. apply st_apply; assumption.
      + assert (Eq : rG l = rL r1 l) by exact Hr. rewrite <- Eq. apply st_comp.
        rewrite Hv. exact Hinv.
  Qed.

  Lemma inc_step : forall c d, InC c -> Lstep c d -> InC d.
  Proof.
    intros [l B] d [Hl HB] H. simpl in *.
    inversion H as [s B0 [k e] Hin Hen E1 E2 | s B0 Hinv E1 E2]; subst; split; simpl.
    - unfold aL. rewrite modk_length. exact Hl.
    - apply Forall_forall. intros x Hx. apply remove1_incl in Hx.
      rewrite Forall_forall in HB. exact (HB x Hx).
    - unfold rL. rewrite len_map'. exact Hl.
    - exact HB.
  Qed.

  Lemma star_agree : forall c d, InC c -> (star Gstep c d <-> star Lstep c d).
  Proof.
    intros c d Hc. split; intros S.
    - revert Hc. induction S as [c | c c1 c2 H1 _ IH]; intros Hc; [apply star_refl|].
      pose proof (proj1 (step_agree c c1 Hc) H1) as H1'.
      eapply star_step; [exact H1' | apply IH; exact (inc_step c c1 Hc H1')].
    - revert Hc. induction S as [c | c c1 c2 H1 _ IH]; intros Hc; [apply star_refl|].
      eapply star_step; [exact (proj2 (step_agree c c1 Hc) H1) | apply IH; exact (inc_step c c1 Hc H1)].
  Qed.

  Lemma nf_agree : forall c, InC c -> (normal_form Gstep c <-> normal_form Lstep c).
  Proof.
    intros c Hc. split; intros N [d H]; apply N; exists d; apply (step_agree c d Hc); exact H.
  Qed.

  Lemma inc_star : forall c d, InC c -> star Lstep c d -> InC d.
  Proof.
    intros c d Hc S. induction S as [c | c c1 c2 H1 _ IH]; [exact Hc|]. apply IH.
    exact (inc_step c c1 Hc H1).
  Qed.

  Theorem un_agree : forall c, InC c -> (UN Gstep c <-> UN Lstep c).
  Proof.
    intros c Hc. split; intros U n1 n2 S1 N1 S2 N2.
    - apply U; [apply (star_agree c n1 Hc); exact S1 | apply (nf_agree n1 (inc_star c n1 Hc S1)); exact N1
               | apply (star_agree c n2 Hc); exact S2 | apply (nf_agree n2 (inc_star c n2 Hc S2)); exact N2].
    - pose proof (proj1 (star_agree c n1 Hc) S1) as S1'. pose proof (proj1 (star_agree c n2 Hc) S2) as S2'.
      apply U; [exact S1' | apply (nf_agree n1 (inc_star c n1 Hc S1')); exact N1
               | exact S2' | apply (nf_agree n2 (inc_star c n2 Hc S2')); exact N2].
  Qed.
End Transfer.

(* The end-to-end statement gsm relies on. A registry over n >= 1 items that is independent and
   identically governed (decided by symcheck on finite descriptions), whose one-item restriction
   leaves valid items alone under repair and has a WFC potential, has unique normal forms from l0
   for every buffer of in-range events iff the one-item registry has unique normal forms from each
   item's start. *)
Theorem symmetry_sound : forall {A E : Type} (edec : forall x y : E, {x = y} + {x <> y}) n
  (aG : nat * E -> list A -> list A) (rG : list A -> list A) (vG : list A -> bool),
  1 <= n -> IdGov n aG rG vG ->
  (forall s, xv n vG s = true -> xr n rG s = s) ->
  (exists Phi : A -> nat, forall s, xv n vG s <> true -> Phi (xr n rG s) < Phi s) ->
  forall l0, length l0 = n ->
  ((forall B, Forall (fun x => fst x < n) B -> UN (Gstep edec aG rG vG) (l0, B)) <->
   (forall k s0, nth_error l0 k = Some s0 ->
      forall B, UN (step edec (xa n aG) (xr n rG) (valid1 (xv n vG)) free_enabled) (s0, B))).
Proof.
  intros A E edec n aG rG vG Hn G Hfix [Phi Hw] l0 Hl0.
  assert (HL : IsLift n aG rG vG) by (apply idgov_lift; assumption).
  split.
  - intros H. apply (un_in_to_item edec (xa n aG) (xr n rG) (xv n vG) Phi Hw Hfix l0).
    intros B HB. rewrite Hl0 in HB. apply (un_agree edec n aG rG vG HL); [split; assumption|].
    apply H. exact HB.
  - intros H B HB. apply (un_agree edec n aG rG vG HL); [split; assumption|].
    apply (proj2 (un_cutoff edec (xa n aG) (xr n rG) (xv n vG) Phi Hw Hfix l0)). exact H.
Qed.

(* ============================================================================================ *)
(* Tightness: CC1 alone has cutoff 2, not 1.                                                     *)
(* ============================================================================================ *)

Definition udec (x y : unit) : {x = y} + {x <> y}.
Proof. left. destruct x, y. reflexivity. Defined.

(* One event; state 1 is invalid and repairs to 0; the event moves 0 to 1 and anything else to 2. *)
Definition tk_a (_ : unit) (s : nat) : nat := match s with 0 => 1 | _ => 2 end.
Definition tk_v (s : nat) : bool := negb (Nat.eqb s 1).
Definition tk_r (s : nat) : nat := if Nat.eqb s 1 then 0 else s.
Definition tk_Phi (s : nat) : nat := if Nat.eqb s 1 then 1 else 0.

Lemma tk_wfc : forall s, ~ valid1 tk_v s -> tk_Phi (tk_r s) < tk_Phi s.
Proof.
  intros s H. unfold valid1, tk_v, tk_Phi, tk_r in *.
  destruct (Nat.eqb_spec s 1); simpl in *; [subst; simpl; lia | contradiction].
Qed.

Lemma tk_fix : forall s, valid1 tk_v s -> tk_r s = s.
Proof.
  intros s H. unfold valid1, tk_v, tk_r in *. destruct (Nat.eqb s 1); [discriminate | reflexivity].
Qed.

(* CC1 holds at one item, fails at two items, and the item fails CC2. *)
Theorem cc1_cutoff_tight :
  CC1in tk_a tk_r tk_v tk_Phi [0] /\ ~ CC1in tk_a tk_r tk_v tk_Phi [0; 0] /\
  ~ CC2i tk_a tk_r tk_v tk_Phi 0.
Proof.
  assert (R1 : reach tk_a tk_r (valid1 tk_v) 0 1) by exact (r_apply _ _ _ 0 tt 0 (r_init _ _ _ 0)).
  split; [| split].
  - apply (cc1_cutoff_one tk_a tk_r tk_v tk_Phi tk_wfc tk_fix). intros s [] [] _. reflexivity.
  - intros H.
    destruct (proj1 (cc1_cutoff tk_a tk_r tk_v tk_Phi tk_wfc tk_fix [0; 0]) H 0 0 eq_refl)
      as [_ C2].
    pose proof (C2 ltac:(simpl; lia) 1 tt R1) as E. vm_compute in E. discriminate E.
  - intros H. pose proof (H 1 tt R1 ltac:(unfold valid1; vm_compute; discriminate)) as E.
    vm_compute in E. discriminate E.
Qed.

(* ============================================================================================ *)
(* Boundary 1: aggregates. Total reserved across items at most 1.                                *)
(* ============================================================================================ *)

(* The item: Reserve adds one reservation; at most 1 reserved; repair cancels one reservation. *)
Definition ag_a (_ : unit) (s : nat) : nat := S s.
Definition ag_v (s : nat) : bool := Nat.leb s 1.
Definition ag_r (s : nat) : nat := if Nat.leb s 1 then s else pred s.
Definition ag_Phi (s : nat) : nat := s - 1.

Lemma ag_wfc : forall s, ~ valid1 ag_v s -> ag_Phi (ag_r s) < ag_Phi s.
Proof.
  intros s H. unfold valid1, ag_v, ag_r, ag_Phi in *.
  destruct (Nat.leb_spec s 1); [contradiction|]. lia.
Qed.

Lemma ag_fix : forall s, valid1 ag_v s -> ag_r s = s.
Proof. intros s H. unfold valid1, ag_v, ag_r in *. rewrite H. reflexivity. Qed.

Lemma ag_itr : forall m t, 1 <= t -> t - 1 <= m -> itr m ag_r t = 1.
Proof.
  induction m as [|m IH]; intros t H1 H2; simpl; [lia|].
  unfold ag_r at 2. destruct (Nat.leb_spec t 1).
  - assert (t = 1) by lia. subst. apply itr_fix. reflexivity.
  - apply IH; lia.
Qed.

Lemma ag_rstar : forall t, 1 <= t -> rstar ag_r ag_Phi t = 1.
Proof. intros t H. apply ag_itr; [exact H | unfold ag_Phi; lia]. Qed.

(* The one-item registry has unique normal forms from every state and every buffer. *)
Theorem agg_item_un : forall s0 B,
  UN (step udec ag_a ag_r (valid1 ag_v) free_enabled) (s0, B).
Proof.
  intros s0. refine (proj2 (cc_exact_from udec ag_a ag_r (rstar ag_r ag_Phi) (valid1 ag_v) ag_Phi
                              ag_wfc _ _ s0) _).
  - exact (i_reach udec ag_a ag_r ag_v ag_Phi ag_fix).
  - exact (rstar_valid ag_r ag_v ag_Phi ag_wfc ag_fix).
  - split.
    + intros s [] [] _. reflexivity.
    + intros s [] _ Hn. unfold valid1, ag_v in Hn. destruct (Nat.leb_spec s 1); [contradiction|].
      unfold ag_a, ag_r. destruct (Nat.leb_spec s 1); [lia|].
      rewrite !ag_rstar by lia. reflexivity.
Qed.

(* With the per-item invariant (each item at most 1), the same rules converge at every n. *)
Theorem itemwise_converges : forall l B,
  UN (step (kdec udec) (aL ag_a) (rL ag_r) (validL ag_v) free_enabled) (l, B).
Proof.
  apply (proj2 (un_cutoff_global udec ag_a ag_r ag_v ag_Phi ag_wfc ag_fix)). exact agg_item_un.
Qed.

(* The aggregate registry: the same Reserve, the invariant on the total, and a repair that cancels
   a reservation on every positive item. *)
Definition agg_a (x : nat * unit) (l : list nat) : list nat := modk S (fst x) l.
Definition agg_v (l : list nat) : bool := Nat.leb (fold_right plus 0 l) 1.
Definition agg_r (l : list nat) : list nat := map pred l.
Definition aggstep := step (kdec udec) agg_a agg_r (fun l => agg_v l = true) free_enabled.

(* On one item the aggregate registry has the item's rules. *)
Theorem agg_one_item : forall s,
  agg_v [s] = ag_v s /\ (agg_v [s] = false -> agg_r [s] = [ag_r s]) /\
  (forall e, agg_a (0, e) [s] = [ag_a e s]).
Proof.
  intros s. unfold agg_v, ag_v, agg_r, ag_r, agg_a, ag_a; simpl. rewrite Nat.add_0_r.
  split; [reflexivity | split; [| reflexivity]]. intros H. rewrite H. reflexivity.
Qed.

Lemma agg_apply : forall l B e l' B' c, In e B -> agg_a e l = l' ->
  remove1 (kdec udec) e B = B' -> star aggstep (l', B') c -> star aggstep (l, B) c.
Proof.
  intros l B e l' B' c Hin <- <- S. eapply star_step; [| exact S]. apply st_apply; exact Hin.
Qed.

Lemma agg_comp : forall l B l' c, agg_v l = false -> agg_r l = l' ->
  star aggstep (l', B) c -> star aggstep (l, B) c.
Proof.
  intros l B l' c Hv <- S. eapply star_step; [| exact S]. apply st_comp. congruence.
Qed.

Lemma agg_nf : forall l, agg_v l = true -> normal_form aggstep (l, []).
Proof.
  intros l Hv [y H]. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst;
    [destruct Hin | contradiction].
Qed.

(* Two items diverge: the one-item check passes, the collection does not converge. *)
Theorem aggregate_diverges : ~ UN aggstep ([0; 0], [(0, tt); (0, tt); (1, tt)]).
Proof.
  intros U.
  assert (S1 : star aggstep ([0; 0], [(0, tt); (0, tt); (1, tt)]) ([0; 0], [])).
  { apply (agg_apply _ _ (0, tt) [1; 0] [(0, tt); (1, tt)]); [simpl; auto | reflexivity | reflexivity |].
    apply (agg_apply _ _ (0, tt) [2; 0] [(1, tt)]); [simpl; auto | reflexivity | reflexivity |].
    apply (agg_comp _ _ [1; 0]); [reflexivity | reflexivity |].
    apply (agg_apply _ _ (1, tt) [1; 1] []); [simpl; auto | reflexivity | reflexivity |].
    apply (agg_comp _ _ [0; 0]); [reflexivity | reflexivity | apply star_refl]. }
  assert (S2 : star aggstep ([0; 0], [(0, tt); (0, tt); (1, tt)]) ([1; 0], [])).
  { apply (agg_apply _ _ (1, tt) [0; 1] [(0, tt); (0, tt)]); [simpl; auto | reflexivity | reflexivity |].
    apply (agg_apply _ _ (0, tt) [1; 1] [(0, tt)]); [simpl; auto | reflexivity | reflexivity |].
    apply (agg_comp _ _ [0; 0]); [reflexivity | reflexivity |].
    apply (agg_apply _ _ (0, tt) [1; 0] []); [simpl; auto | reflexivity | reflexivity | apply star_refl]. }
  pose proof (U _ _ S1 (agg_nf [0; 0] eq_refl) S2 (agg_nf [1; 0] eq_refl)) as E. discriminate E.
Qed.

(* The check refuses the aggregate: the invariant is not a conjunction of item invariants. *)
Theorem agg_not_idgov : ~ IdGov 2 agg_a agg_r agg_v.
Proof.
  intros G. pose proof (ig_valid 2 agg_a agg_r agg_v G [1; 0] eq_refl) as E.
  vm_compute in E. discriminate E.
Qed.

(* ============================================================================================ *)
(* Boundary 2: items governed by different rules.                                                *)
(* ============================================================================================ *)

(* Item 0 ignores its events; item 1 is set to 1 or 2 by them. *)
Definition ni_a (x : nat * bool) (l : list nat) : list nat :=
  modk (fun s => if Nat.eqb (fst x) 0 then s else if snd x then 1 else 2) (fst x) l.
Definition ni_r (l : list nat) : list nat := l.
Definition ni_v (_ : list nat) : bool := true.
Definition nistep := step (kdec bool_dec) ni_a ni_r (fun l => ni_v l = true) free_enabled.

Lemma ni_nf : forall l, normal_form nistep (l, []).
Proof.
  intros l [y H]. inversion H as [s B e Hin Hen E1 E2 | s B Hinv E1 E2]; subst;
    [destruct Hin | apply Hinv; reflexivity].
Qed.

(* Checking item 0 says "converges"; the collection diverges. *)
Theorem nonidentical_misleads :
  (forall B, UN (step bool_dec (fun _ (s : nat) => s) (fun s => s) (fun _ => True) free_enabled) (0, B))
  /\ ~ UN nistep ([0; 0], [(1, true); (1, false)]).
Proof.
  split.
  - intros B. refine (proj2 (cc_exact_from bool_dec (fun _ (s : nat) => s) (fun s => s) (fun s => s)
                               (fun _ => True) (fun _ => 0) _ _ _ 0) _ B).
    + intros s H. exfalso. apply H. exact I.
    + intros s B'. apply star_refl.
    + intros s. exact I.
    + split; [reflexivity | intros s e _ H; exfalso; apply H; exact I].
  - intros U.
    assert (S1 : star nistep ([0; 0], [(1, true); (1, false)]) ([0; 2], [])).
    { eapply star_step; [apply st_apply; left; reflexivity |]. simpl.
      eapply star_step; [apply st_apply; left; reflexivity |]. simpl. apply star_refl. }
    assert (S2 : star nistep ([0; 0], [(1, true); (1, false)]) ([0; 1], [])).
    { eapply star_step; [apply st_apply; right; left; reflexivity |]. simpl.
      eapply star_step; [apply st_apply; left; reflexivity |]. simpl. apply star_refl. }
    pose proof (U _ _ S1 (ni_nf _) S2 (ni_nf _)) as E. discriminate E.
Qed.

(* The check refuses it: the rules are not invariant under exchanging the two keys. *)
Theorem nonidentical_not_idgov : ~ IdGov 2 ni_a ni_r ni_v.
Proof.
  intros G. pose proof (ig_perm 2 ni_a ni_r ni_v G 0 1 1 true [0; 0]) as E.
  specialize (E ltac:(lia) ltac:(lia) ltac:(lia) eq_refl). vm_compute in E. discriminate E.
Qed.

(* ============================================================================================ *)
(* Non-vacuity: per-product inventory, verified for any number of products.                     *)
(* ============================================================================================ *)

Inductive inv_ev : Type := Restock | Reserve | Release.

Definition inv_dec (x y : inv_ev) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* Item state: (stock, reservations, releases, backordered). The backorder flag must equal
   "reservations exceed stock plus releases"; repair recomputes it. *)
Definition inv_flag (q rs rl : nat) : bool := Nat.ltb (q + rl) rs.
Definition inv_a (e : inv_ev) (s : nat * nat * nat * bool) : nat * nat * nat * bool :=
  match s with
  | (q, rs, rl, b) =>
      match e with
      | Restock => (S q, rs, rl, b)
      | Reserve => (q, S rs, rl, b)
      | Release => (q, rs, S rl, b)
      end
  end.
Definition inv_v (s : nat * nat * nat * bool) : bool :=
  match s with (q, rs, rl, b) => Bool.eqb b (inv_flag q rs rl) end.
Definition inv_r (s : nat * nat * nat * bool) : nat * nat * nat * bool :=
  match s with (q, rs, rl, _) => (q, rs, rl, inv_flag q rs rl) end.
Definition inv_Phi (s : nat * nat * nat * bool) : nat := if inv_v s then 0 else 1.

Lemma inv_fix : forall s, valid1 inv_v s -> inv_r s = s.
Proof.
  intros [[[q rs] rl] b] H. unfold valid1, inv_v in H. apply eqb_prop in H. subst. reflexivity.
Qed.

Lemma inv_r_valid : forall s, inv_v (inv_r s) = true.
Proof. intros [[[q rs] rl] b]. simpl. apply eqb_reflx. Qed.

Lemma inv_wfc : forall s, ~ valid1 inv_v s -> inv_Phi (inv_r s) < inv_Phi s.
Proof.
  intros s H. unfold inv_Phi. rewrite inv_r_valid. unfold valid1 in H.
  destruct (inv_v s); [contradiction | lia].
Qed.

Lemma inv_rstar : forall s, rstar inv_r inv_Phi s = inv_r s.
Proof.
  intros s. unfold rstar, inv_Phi. destruct (inv_v s) eqn:Hv; simpl.
  - symmetry. apply inv_fix. exact Hv.
  - reflexivity.
Qed.

Lemma inv_r_a_r : forall e s, inv_r (inv_a e (inv_r s)) = inv_r (inv_a e s).
Proof. intros [] [[[q rs] rl] b]; reflexivity. Qed.

Lemma inv_a_comm : forall e1 e2 s, inv_a e2 (inv_a e1 s) = inv_a e1 (inv_a e2 s).
Proof. intros [] [] [[[q rs] rl] b]; reflexivity. Qed.

Theorem inventory_item_un : forall s0 B,
  UN (step inv_dec inv_a inv_r (valid1 inv_v) free_enabled) (s0, B).
Proof.
  intros s0. refine (proj2 (cc_exact_from inv_dec inv_a inv_r (rstar inv_r inv_Phi) (valid1 inv_v)
                              inv_Phi inv_wfc _ _ s0) _).
  - exact (i_reach inv_dec inv_a inv_r inv_v inv_Phi inv_fix).
  - exact (rstar_valid inv_r inv_v inv_Phi inv_wfc inv_fix).
  - split.
    + intros s e1 e2 _. rewrite !inv_rstar, !inv_r_a_r, inv_a_comm. reflexivity.
    + intros s e _ _. rewrite !inv_rstar, inv_r_a_r. reflexivity.
Qed.

(* Any catalog: every start of any length, every buffer of keyed events. *)
Theorem inventory_any_n : forall l0 B,
  UN (step (kdec inv_dec) (aL inv_a) (rL inv_r) (validL inv_v) free_enabled) (l0, B).
Proof.
  apply (proj2 (un_cutoff_global inv_dec inv_a inv_r inv_v inv_Phi inv_wfc inv_fix)).
  exact inventory_item_un.
Qed.

(* Repair does fire: a reservation without stock leaves the flag stale. *)
Theorem inventory_repair_fires :
  reach inv_a inv_r (valid1 inv_v) (0, 0, 0, false) (0, 1, 0, false) /\
  ~ valid1 inv_v (0, 1, 0, false).
Proof.
  split.
  - exact (r_apply _ _ _ _ Reserve _ (r_init _ _ _ _)).
  - unfold valid1. vm_compute. discriminate.
Qed.

(* The inventory collection passes the hypotheses check at every n >= 1. *)
Theorem inventory_idgov : forall n, 1 <= n ->
  IdGov n (aL inv_a) (rL inv_r) (fun l => forallb inv_v l).
Proof. intros n Hn. apply lift_idgov. exact Hn. Qed.
