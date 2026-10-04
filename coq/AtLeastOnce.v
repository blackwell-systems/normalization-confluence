(* AtLeastOnce.v: exactly-once delivery as a checked property, mechanized axiom-free.

   The convergence results (Trace.v, CausalReplay.v, Governance.v) take a delivery order with no
   duplicates: every replica sees each event exactly once. Real transports promise at-least-once
   delivery, so an event can be redelivered, possibly much later. This file proves when a
   duplicate is absorbed, and gives a divergence witness when it is not.

   Setting. A governed step (step e) applies event e and repairs to a normal form, as in
   Governance.v, CausalReplay.v (gstep) and GovernanceWF.v. States range over an invariant domain
   D that every governed step preserves (the valid states, or every state). An at-least-once
   delivery is a list of events that may contain duplicates. Its exactly-once projection
   (dedup d) keeps the first delivery of each event, in delivery order. Event equality is
   decidable (events are identifiers).

   Results.
   - alo_absorbed: the general, local form. A delivery d reaches the same state as its exactly-once
     projection when every redelivered event a is idempotent (step a (step a s) = step a s) and
     commutes with each event delivered between the redelivery and the previous copy of a.
   - alo_commuting_exactly_once, alo_commuting_converges: the all-orders case. If all events
     commute and every duplicated event is idempotent, an at-least-once delivery reaches the same
     state as every exactly-once delivery of the same events, in any order, and any two
     at-least-once deliveries of the same events agree. Built on Trace.run_tequiv.
   - causal_alo_exactly_once, causal_alo_converges: the causal case. Only concurrent events need
     to commute (as in CausalReplay.causal_convergence), provided redelivery is itself causally
     consistent: no copy of a is delivered after any copy of an event b with hb a b. Then every
     duplicate is absorbed and the run equals every causally consistent exactly-once run. Built on
     CausalReplay.causal_tequiv and Trace.run_tequiv.
   - non_idempotent_diverges: for ANY event whose governed step is not idempotent at some state,
     delivering it twice from that state diverges from delivering it once. The concrete witness
     inc_duplicate_diverges is a capped counter increment (repair clamps to the cap).
   - late_duplicate_diverges: the naive causal statement (idempotent duplicates are absorbed under
     causal delivery of the first copies) is FALSE. Add and Remove on a flag are both idempotent
     and every concurrent pair commutes, yet a late redelivery of Add after its causal successor
     Remove ends with the flag set, while exactly-once delivery ends with it cleared. This is why
     the causal theorem requires redelivery to be causally consistent.
   - mx_alo_converges, fl_causal_alo_converges: non-vacuity instances discharging every hypothesis
     (a clamped max-register; and a flag with add and causally later remove next to a clamped
     max-register, where not all events commute). *)

From Coq Require Import List Arith Lia.
From Coq Require Import Sorting.Permutation.
Require Import NC.Trace NC.CausalReplay.
Import ListNotations.

(* ----- the exactly-once projection: keep the first delivery of each event ----- *)

Section Dedup.
  Context {E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.

  Definition dedup_step (acc : list E) (a : E) : list E :=
    if in_dec dec a acc then acc else acc ++ [a].

  Definition dedup (d : list E) : list E := fold_left dedup_step d [].

  Lemma dedup_snoc : forall p a,
    dedup (p ++ [a]) = if in_dec dec a (dedup p) then dedup p else dedup p ++ [a].
  Proof. intros p a. unfold dedup. rewrite fold_left_app. reflexivity. Qed.

  Lemma dedup_In : forall d x, In x (dedup d) <-> In x d.
  Proof.
    induction d as [| a p IH] using rev_ind; intros x; [simpl; tauto |].
    rewrite dedup_snoc. destruct (in_dec dec a (dedup p)) as [Ha | Ha].
    - rewrite IH, in_app_iff. simpl. split; [tauto |].
      intros [H | [H | []]]; [exact H | subst; apply IH; exact Ha].
    - rewrite !in_app_iff, IH. tauto.
  Qed.

  Lemma dedup_NoDup : forall d, NoDup (dedup d).
  Proof.
    induction d as [| a p IH] using rev_ind; [constructor |].
    rewrite dedup_snoc. destruct (in_dec dec a (dedup p)) as [Ha | Ha]; [exact IH |].
    apply (Permutation_NoDup (Permutation_cons_append (dedup p) a)).
    constructor; [exact Ha | exact IH].
  Qed.

  (* A delivery with no duplicates is its own exactly-once projection. *)
  Lemma dedup_nodup_id : forall d, NoDup d -> dedup d = d.
  Proof.
    induction d as [| a p IH] using rev_ind; intros Hnd; [reflexivity |].
    rewrite dedup_snoc. apply NoDup_remove in Hnd. rewrite app_nil_r in Hnd.
    destruct Hnd as [Hnd Ha]. rewrite (IH Hnd).
    destruct (in_dec dec a p) as [Hin | _]; [exfalso; apply Ha; exact Hin | reflexivity].
  Qed.

  (* Split at the LAST occurrence of an event. *)
  Lemma in_split_last : forall p (a : E), In a p -> exists l m, p = l ++ a :: m /\ ~ In a m.
  Proof.
    induction p as [| x p IH] using rev_ind; intros a Ha; [destruct Ha |].
    destruct (dec x a) as [Exa | Nxa].
    - subst x. exists p, []. split; [reflexivity | intros []].
    - apply in_app_or in Ha. destruct Ha as [Ha | [Ha | []]]; [| congruence].
      destruct (IH a Ha) as [l [m [Ep Hm]]]. exists l, (m ++ [x]). split.
      + subst p. rewrite <- app_assoc. reflexivity.
      + intro H. apply in_app_or in H. destruct H as [H | [H | []]]; [exact (Hm H) | congruence].
  Qed.

  (* a is delivered more than once in d. *)
  Definition dup (a : E) (d : list E) : Prop := exists l m r, d = l ++ a :: m ++ a :: r.
End Dedup.

Arguments dedup {E} dec d.

(* ----- absorption: the general local condition ----- *)

Section Absorption.
  Context {S E : Type}.
  Variable dec : forall x y : E, {x = y} + {x <> y}.
  Variable step : E -> S -> S.          (* governed step: apply, then repair to normal form *)
  Variable D : S -> Prop.               (* invariant domain (valid states, or every state) *)
  Hypothesis step_D : forall e s, D s -> D (step e s).

  Definition idem (a : E) : Prop := forall s, D s -> step a (step a s) = step a s.
  Definition comm (a b : E) : Prop := forall s, D s -> step a (step b s) = step b (step a s).

  (* Every redelivered event is idempotent and commutes with every event delivered since its
     previous copy. *)
  Definition absorbs (d : list E) : Prop :=
    forall l a m r, d = l ++ a :: m ++ a :: r -> ~ In a m -> idem a /\ forall b, In b m -> comm a b.

  Lemma runT_Dall : forall l s, D s -> D (runT step l s).
  Proof. induction l as [| e l IH]; intros s Hs; [exact Hs | apply IH, step_D, Hs]. Qed.

  Lemma comm_past : forall a m s, (forall b, In b m -> comm a b) -> D s ->
    step a (runT step m s) = runT step m (step a s).
  Proof.
    intros a m. induction m as [| b m IH]; intros s Hm Hs; [reflexivity |].
    rewrite !runT_cons. rewrite IH; [| intros b' Hb'; apply Hm; right; exact Hb' | apply step_D, Hs].
    rewrite (Hm b (or_introl eq_refl) s Hs). reflexivity.
  Qed.

  Lemma absorbs_prefix : forall p x, absorbs (p ++ [x]) -> absorbs p.
  Proof.
    intros p x H l a m r Ed Hm. apply (H l a m (r ++ [x])); [| exact Hm].
    subst p. rewrite <- app_assoc. simpl. rewrite <- app_assoc. reflexivity.
  Qed.

  (* A redelivery of a, idempotent and commuting with everything since a's last copy, is a no-op. *)
  Lemma redelivery_noop : forall p a s, absorbs (p ++ [a]) -> In a p -> D s ->
    step a (runT step p s) = runT step p s.
  Proof.
    intros p a s Hab Ha Hs. destruct (in_split_last dec p a Ha) as [l [m [Ep Hm]]]. subst p.
    destruct (Hab l a m []) as [Hid Hc]; [rewrite <- app_assoc; reflexivity | exact Hm |].
    rewrite runT_app, runT_cons.
    rewrite (comm_past a m _ Hc (step_D a _ (runT_Dall l s Hs))).
    rewrite (Hid _ (runT_Dall l s Hs)). reflexivity.
  Qed.

  (* General form: an at-least-once delivery that absorbs its duplicates reaches the same state as
     its exactly-once projection. *)
  Theorem alo_absorbed : forall d s, absorbs d -> D s -> runT step d s = runT step (dedup dec d) s.
  Proof.
    induction d as [| a p IH] using rev_ind; intros s Hab Hs; [reflexivity |].
    rewrite dedup_snoc, runT_app. simpl.
    destruct (in_dec dec a (dedup dec p)) as [Ha | Ha].
    - rewrite (redelivery_noop p a s Hab (proj1 (dedup_In dec p a) Ha) Hs).
      exact (IH s (absorbs_prefix p a Hab) Hs).
    - rewrite runT_app. simpl. rewrite (IH s (absorbs_prefix p a Hab) Hs). reflexivity.
  Qed.

  (* ----- the all-orders (commuting) case ----- *)

  Lemma commuting_absorbs : forall d,
    (forall a b, In a d -> In b d -> comm a b) -> (forall a, dup a d -> idem a) -> absorbs d.
  Proof.
    intros d Hc Hi l a m r Ed Hm. split.
    - apply Hi. exists l, m, r. exact Ed.
    - intros b Hb. apply Hc; subst d; apply in_or_app; right; [left; reflexivity |].
      right. apply in_or_app. left. exact Hb.
  Qed.

  (* If all events commute and every duplicated event is idempotent, an at-least-once delivery
     reaches the same state as EVERY exactly-once delivery of the same events. *)
  Theorem alo_commuting_exactly_once : forall d o s,
    (forall a b, In a d -> In b d -> comm a b) ->
    (forall a, dup a d -> idem a) ->
    NoDup o -> (forall x, In x o <-> In x d) -> D s ->
    runT step d s = runT step o s.
  Proof.
    intros d o s Hc Hi Hnd Ho Hs.
    rewrite (alo_absorbed d s (commuting_absorbs d Hc Hi) Hs).
    assert (HP : Permutation (dedup dec d) o).
    { apply NoDup_Permutation; [apply dedup_NoDup | exact Hnd |].
      intros x. rewrite dedup_In, Ho. tauto. }
    apply (run_tequiv step (fun _ _ => True) (fun e => In e d) D D (fun _ H => H)
             (fun e s0 _ Hs0 => step_D e s0 Hs0)
             (fun a b s0 Ha Hb _ Hs0 => Hc a b Ha Hb s0 Hs0)); [| | exact Hs].
    - apply (perm_tequiv_total (fun _ _ => True) (fun e => In e d)); [intros; exact I | exact HP |].
      apply Forall_forall. intros x Hx. apply dedup_In in Hx. exact Hx.
    - apply Forall_forall. intros x Hx. apply dedup_In in Hx. exact Hx.
  Qed.

  (* Any two at-least-once deliveries of the same events agree. *)
  Theorem alo_commuting_converges : forall d1 d2 s,
    (forall a b, In a d1 -> In b d1 -> comm a b) ->
    (forall a, dup a d1 -> idem a) -> (forall a, dup a d2 -> idem a) ->
    (forall x, In x d1 <-> In x d2) -> D s ->
    runT step d1 s = runT step d2 s.
  Proof.
    intros d1 d2 s Hc Hi1 Hi2 Heq Hs.
    assert (Hc2 : forall a b, In a d2 -> In b d2 -> comm a b)
      by (intros a b Ha Hb; apply Hc; apply Heq; assumption).
    rewrite (alo_commuting_exactly_once d1 (dedup dec d2) s Hc Hi1 (dedup_NoDup dec d2)
               (fun x => iff_trans (dedup_In dec d2 x) (iff_sym (Heq x))) Hs).
    symmetry. exact (alo_absorbed d2 s (commuting_absorbs d2 Hc2 Hi2) Hs).
  Qed.

  (* ----- the causal case ----- *)

  Variable hb : E -> E -> Prop.   (* happens-before *)

  (* Causally consistent at-least-once delivery: every copy of a cause precedes every copy of
     its effects. A redelivered duplicate must still be causally consistent where it lands. *)
  Definition causal_alo (d : list E) : Prop :=
    forall a b, hb a b -> forall l r, d = l ++ r -> In b l -> ~ In a r.

  (* Compensation commutativity only for concurrent pairs, as in CausalReplay.v. *)
  Definition cc_concurrent : Prop := forall a b, concurrent hb a b -> comm a b.

  Lemma causal_alo_absorbs : forall d,
    cc_concurrent -> causal_alo d -> (forall a, dup a d -> idem a) -> absorbs d.
  Proof.
    intros d Hcc Hca Hi l a m r Ed Hm. split; [apply Hi; exists l, m, r; exact Ed |].
    intros b Hb. apply Hcc. split; [| split].
    - intro Eab. subst b. exact (Hm Hb).
    - intro Hab. apply (Hca a b Hab (l ++ a :: m) (a :: r)).
      + rewrite Ed, <- app_assoc. reflexivity.
      + apply in_or_app. right. right. exact Hb.
      + left. reflexivity.
    - intro Hba. apply (Hca b a Hba (l ++ [a]) (m ++ a :: r)).
      + rewrite Ed, <- app_assoc. reflexivity.
      + apply in_or_app. right. left. reflexivity.
      + apply in_or_app. left. exact Hb.
  Qed.

  Lemma prec_app_r : forall (a b : E) q t, prec a b q -> prec a b (q ++ t).
  Proof.
    induction q as [| x q IH]; intros t H; simpl in *; [contradiction |].
    destruct H as [[Ex Hin] | H]; [left; split; [exact Ex | apply in_or_app; left; exact Hin] |].
    right. exact (IH t H).
  Qed.

  Lemma prec_snoc : forall (a b : E) q, In a q -> prec a b (q ++ [b]).
  Proof.
    induction q as [| x q IH]; intros Ha; simpl in *; [contradiction |].
    destruct Ha as [Ex | Ha]; [left; split; [exact Ex | apply in_or_app; right; left; reflexivity] |].
    right. exact (IH Ha).
  Qed.

  Lemma causal_alo_prefix : forall p x, causal_alo (p ++ [x]) -> causal_alo p.
  Proof.
    intros p x H a b Hab l r Ed Hb Ha. apply (H a b Hab l (r ++ [x])).
    - rewrite Ed, <- app_assoc. reflexivity.
    - exact Hb.
    - apply in_or_app. left. exact Ha.
  Qed.

  (* The exactly-once projection of a causally consistent at-least-once delivery is causal. *)
  Theorem causal_alo_dedup_causal : forall d,
    (forall a, ~ hb a a) -> causal_alo d -> causal hb (dedup dec d).
  Proof.
    intros d Hirr. induction d as [| x p IH] using rev_ind; intros Hca.
    - split; [constructor | intros a b _ []].
    - split; [apply dedup_NoDup |]. intros a b Hab Ha Hb.
      pose proof (IH (causal_alo_prefix p x Hca)) as [_ Hp].
      rewrite dedup_In in Ha, Hb. rewrite dedup_snoc.
      apply in_app_or in Ha. apply in_app_or in Hb.
      destruct Ha as [Ha | [Ha | []]]; destruct Hb as [Hb | [Hb | []]].
      + assert (H : prec a b (dedup dec p)) by (apply Hp; [exact Hab | | ]; apply dedup_In; assumption).
        destruct (in_dec dec x (dedup dec p)); [exact H | apply prec_app_r, H].
      + subst b. destruct (in_dec dec x (dedup dec p)) as [Hx | Hx].
        * apply Hp; [exact Hab | apply dedup_In; exact Ha | exact Hx].
        * apply prec_snoc. apply dedup_In. exact Ha.
      + subst a. exfalso. apply (Hca x b Hab p [x]); [reflexivity | exact Hb | left; reflexivity].
      + subst a b. exfalso. exact (Hirr x Hab).
  Qed.

  (* Causal case: with commutation required only for concurrent pairs, a causally consistent
     at-least-once delivery whose duplicated events are idempotent reaches the same state as
     EVERY causally consistent exactly-once delivery of the same events. *)
  Theorem causal_alo_exactly_once : forall d o s,
    (forall a, ~ hb a a) -> cc_concurrent ->
    causal_alo d -> (forall a, dup a d -> idem a) ->
    causal hb o -> (forall x, In x o <-> In x d) -> D s ->
    runT step d s = runT step o s.
  Proof.
    intros d o s Hirr Hcc Hca Hi Ho Heq Hs.
    rewrite (alo_absorbed d s (causal_alo_absorbs d Hcc Hca Hi) Hs).
    assert (HP : Permutation (dedup dec d) o).
    { apply NoDup_Permutation; [apply dedup_NoDup | exact (proj1 Ho) |].
      intros x. rewrite dedup_In, Heq. tauto. }
    apply (run_tequiv step (concurrent hb) (fun _ => True) D D (fun _ H => H)
             (fun e s0 _ Hs0 => step_D e s0 Hs0)
             (fun a b s0 _ _ Hab Hs0 => Hcc a b Hab s0 Hs0)); [| | exact Hs].
    - exact (causal_tequiv hb _ _ (causal_alo_dedup_causal d Hirr Hca) Ho HP).
    - apply Forall_forall. intros; exact I.
  Qed.

  (* Any two causally consistent at-least-once deliveries of the same events agree. *)
  Theorem causal_alo_converges : forall d1 d2 s,
    (forall a, ~ hb a a) -> cc_concurrent ->
    causal_alo d1 -> causal_alo d2 ->
    (forall a, dup a d1 -> idem a) -> (forall a, dup a d2 -> idem a) ->
    (forall x, In x d1 <-> In x d2) -> D s ->
    runT step d1 s = runT step d2 s.
  Proof.
    intros d1 d2 s Hirr Hcc Hc1 Hc2 Hi1 Hi2 Heq Hs.
    rewrite (causal_alo_exactly_once d1 (dedup dec d2) s Hirr Hcc Hc1 Hi1
               (causal_alo_dedup_causal d2 Hirr Hc2)
               (fun x => iff_trans (dedup_In dec d2 x) (iff_sym (Heq x))) Hs).
    symmetry. exact (alo_absorbed d2 s (causal_alo_absorbs d2 Hcc Hc2 Hi2) Hs).
  Qed.

  (* ----- necessity of idempotence: any non-idempotent event diverges when duplicated ----- *)

  Theorem non_idempotent_diverges : forall a s,
    step a (step a s) <> step a s -> runT step [a; a] s <> runT step [a] s.
  Proof. intros a s H. exact H. Qed.
End Absorption.

Arguments idem {S E} step D a.
Arguments comm {S E} step D a b.
Arguments absorbs {S E} step D d.
Arguments causal_alo {E} hb d.
Arguments cc_concurrent {S E} step D hb.

(* ============================================================
   Counterexamples. Axiom-free.
   ============================================================ *)

(* A non-idempotent governed event: increment a counter, repair clamps it to the cap 10. Every
   pair of events commutes (there is one event), so exactly-once delivery converges, yet a
   duplicate delivery from 0 ends at 2 while exactly-once ends at 1. *)
Definition inc_step (_ : unit) (n : nat) : nat := Nat.min (S n) 10.

Theorem inc_not_idempotent : ~ idem inc_step (fun _ => True) tt.
Proof. intro H. specialize (H 0 I). discriminate H. Qed.

Theorem inc_duplicate_diverges :
  runT inc_step [tt; tt] 0 = 2 /\ runT inc_step [tt] 0 = 1 /\
  runT inc_step [tt; tt] 0 <> runT inc_step [tt] 0.
Proof. split; [reflexivity | split; [reflexivity |]]. apply non_idempotent_diverges. discriminate. Qed.

(* The naive causal statement is false. Reuse CausalReplay's flag-with-counter machine (r_apply,
   r_hb: Add happens before Remove). Add and Remove are idempotent and every concurrent pair
   commutes (r_cmrdt), and the first deliveries [Add; Remove] are causally consistent. A late
   redelivery of Add after Remove sets the flag again, while exactly-once delivery clears it. The
   duplicate overtakes its causal successor, so the delivery is not causal_alo. *)
Theorem late_duplicate_diverges :
  idem r_apply (fun _ => True) Add /\ idem r_apply (fun _ => True) Remove /\
  cc_concurrent r_apply (fun _ => True) r_hb /\
  causal r_hb [Add; Remove] /\
  runT r_apply [Add; Remove; Add] (false, 0) <> runT r_apply [Add; Remove] (false, 0) /\
  ~ causal_alo r_hb [Add; Remove; Add].
Proof.
  split; [intros s _; reflexivity |]. split; [intros s _; reflexivity |].
  split; [intros a b Hc s _; exact (r_cmrdt a b s Hc) |].
  split; [| split; [discriminate |]].
  - split; [repeat constructor; simpl; intuition discriminate |].
    intros a b [Ea Eb] Ha Hb. subst. simpl. left. split; [reflexivity | left; reflexivity].
  - intro H. apply (H Add Remove (conj eq_refl eq_refl) [Add; Remove] [Add]);
      [reflexivity | right; left; reflexivity | left; reflexivity].
Qed.

(* ============================================================
   Non-vacuity instances. Axiom-free.
   ============================================================ *)

(* All-orders instance: a max-register whose repair clamps to the cap 100. Event k writes
   max k s, then repair clamps. Every event is idempotent and all events commute. *)
Definition mx_step (k n : nat) : nat := Nat.min (Nat.max k n) 100.

Lemma mx_idem : forall k, idem mx_step (fun _ => True) k.
Proof. intros k n _. unfold mx_step. lia. Qed.

Lemma mx_comm : forall a b, comm mx_step (fun _ => True) a b.
Proof. intros a b n _. unfold mx_step. lia. Qed.

Theorem mx_alo_converges : forall d o s,
  NoDup o -> (forall x, In x o <-> In x d) ->
  runT mx_step d s = runT mx_step o s.
Proof.
  intros d o s Hnd Ho.
  apply (alo_commuting_exactly_once Nat.eq_dec mx_step (fun _ => True) (fun _ _ _ => I));
    [intros; apply mx_comm | intros; apply mx_idem | exact Hnd | exact Ho | exact I].
Qed.

Example mx_example :
  runT mx_step [5; 200; 5; 3; 200; 5] 0 = runT mx_step [3; 5; 200] 0.
Proof. reflexivity. Qed.

(* Causal instance: a flag with add and a causally later remove, plus a clamped max-register.
   Add and Remove do not commute, so the all-orders theorem does not apply; every concurrent pair
   commutes and every event is idempotent, so causally consistent redelivery is absorbed. *)
Inductive fev := FAdd | FRemove | FMax (k : nat).

Definition fev_dec : forall x y : fev, {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition fl_step (e : fev) (s : bool * nat) : bool * nat :=
  match e with
  | FAdd => (true, snd s)
  | FRemove => (false, snd s)
  | FMax k => (fst s, Nat.min (Nat.max k (snd s)) 100)
  end.

Definition fl_hb (a b : fev) : Prop := a = FAdd /\ b = FRemove.

Lemma fl_irrefl : forall a, ~ fl_hb a a.
Proof. intros a [E1 E2]. subst. discriminate. Qed.

Lemma fl_idem : forall e, idem fl_step (fun _ => True) e.
Proof. intros [| | k] [b n] _; simpl; [reflexivity | reflexivity |]. f_equal. lia. Qed.

Lemma fl_cc : cc_concurrent fl_step (fun _ => True) fl_hb.
Proof.
  intros a b [Hne [Hab Hba]] [f n] _.
  destruct a as [| | i], b as [| | j]; simpl; try reflexivity.
  all: try (exfalso; apply Hab; split; reflexivity).
  all: try (exfalso; apply Hba; split; reflexivity).
  all: try (exfalso; apply Hne; reflexivity).
  f_equal. lia.
Qed.

Lemma fl_not_all_commute : ~ comm fl_step (fun _ => True) FAdd FRemove.
Proof. intro H. specialize (H (false, 0) I). discriminate H. Qed.

Theorem fl_causal_alo_converges : forall d o s,
  causal_alo fl_hb d -> causal fl_hb o -> (forall x, In x o <-> In x d) ->
  runT fl_step d s = runT fl_step o s.
Proof.
  intros d o s Hd Ho Heq.
  apply (causal_alo_exactly_once fev_dec fl_step (fun _ => True) (fun _ _ _ => I) fl_hb);
    [exact fl_irrefl | exact fl_cc | exact Hd | intros; apply fl_idem | exact Ho | exact Heq | exact I].
Qed.

(* Add, two redeliveries of a max write, and a redelivery of Add before Remove arrives: the run
   equals the exactly-once run in a different causally consistent order. *)
Example fl_example :
  runT fl_step [FAdd; FMax 7; FAdd; FMax 3; FMax 7; FRemove; FMax 3] (false, 0) =
  runT fl_step [FMax 3; FMax 7; FAdd; FRemove] (false, 0).
Proof. reflexivity. Qed.
