(* DifferenceAbstraction.v: abstraction for difference constraints with saturating writes
   (roadmap item 8, step 2, the arithmetic route; gsm roadmap item 1b). Axiom-free.

   Model (gsm's, exactly). A registry has n integer variables, variable i declared in the range
   [lo_i, hi_i]. Rules are gsm's combinators: expressions V, Lit, Add, Sub; comparisons Le, Lt, Eq,
   Ne, Ge, Gt; And, Or, Not; an event is a guard and a list of assignments applied left to right
   (a no-op when the guard is false); an invariant is a predicate and a repair transform, and one
   repair step applies the first violated invariant's repair. Every write saturates at the target's
   declared bounds (gsm's SetInt, clampZ). Events take no parameters. The governed step is
   dgov K k = K repair steps after the event; gsm's runtime step drun normalizes first. The states
   are the lists in range (InBox).

   The difference fragment (dfrag P A gam mu). Every comparison a op b normalizes (norm) to
   x_i - x_j op c with |c| <= gam, or to x_i op a with a an anchor (a constant in A); every write
   is x_k := x_j + c (increment, decrement, copy with offset) or x_k := a with a an anchor; every
   transform adds offsets summing to at most mu; every bound lo_i, hi_i is an anchor. Saturation
   is a comparison of x_j + c with an anchor, so bounds behave like constants.

   The region relation (near W, Rel, RelS). Two states, with the anchors, are related at threshold
   W when every pairwise difference of their values (anchors included) is equal in both, or above
   W in both, or below -W in both. At W = 0 this is the order type (near0_compare, rel0_oiso).
   - A rule step keeps the relation, lowering W by the offsets it adds; guards with constants of
     size at most W evaluate the same (atom_same, pred_same, clamp_near, write_rel, dgov_rel).
   - One state against a related one: validity at W >= gam (valid_pair), repair within K steps
     at W >= gam + K mu (term_pair), idempotence at W >= gam + 3(K+1) mu (idem_pair), CC1 of a
     pair at W >= gam + 4(K+1) mu (cc1_pair). The two sides of CC1 run as one joint relation, so
     equality of the final states transfers (eq_transfer).
   - Compression (compress_d): every state in range is related at W to a representative state, a
     state in range with every variable within the radius n(W + 1) of an anchor (RepS, RepS_spec).
     Proof: a block of values with no anchor and W + 1 free integers below and above it (found by
     pigeonhole) moves down by 1 (shift_step); the sum of the values decreases.

   Theorems (A: a finite representative cutoff, each an iff, for every W at least the threshold).
   - dterm_abs: repair within K steps from every state in range iff from every representative.
   - dcc1v_abs: CC1 for the pairs of I at every valid state in range iff at every valid
     representative (gsm's CC1); dcc1_abs: at every state.
   - didemv_abs: idempotence at every valid state.
   - dgsm_exact: given repair within K steps over the representatives, CC1 for I at the valid
     representatives iff trace-equivalent runs agree from every valid state in range;
     dgsm_sound, dgsm_sound_all: gsm's runtime from every state in range; dbuild_sound: the fragment
     check and the two boolean checks (dterm_check, dcc1v_check, with exact specifications) give
     it end to end; dcheck_fail_real: a failing check is a real failure.
   The domain: |RepS| is the product over variables of the number of values of [lo_i, hi_i] within
   n(W + 1) of an anchor (RepS_length), each at most |A| (2 n (W + 1) + 1) (dom_length): at most
   (|A| (2 n (W + 1) + 1))^n, independent of the widths of the ranges. Every representative is a
   state in range, so a failing representative is a failure of the declared machine.

   The comparison fragment recovered: with gam = mu = 0 every threshold is 0, RelS 0 is exactly
   AbstractionCutoff's order isomorphisms fixing the anchors (rel0_oiso), and the radius is n, the
   cutoff of term_abs and cc1_abs for m = 0; reps n C lies in the domain (reps_in_dom).

   Non-vacuity (all over ranges up to 10^9).
   - wallet_*: balance in [-1000, 10^9], deposit 5, deposit 20, withdraw 10 when balance >= 10, a
     fee of 3, overdraft repair to 0; 657 representatives; deposits converge from every balance;
     deposit against withdraw diverges at balance 5 (0 against 10), a real failure the check reports.
   - capinv_*: stock in [0, 10^9], cap 10^6, restock 3 and 7, ship 2; 233 representatives; restocks
     converge; restock against ship diverges one below the cap.
   - reserve_*: reserved <= stock in [0, 10^6]^2 with reserve 2, reserve 3, release 1, restock 3 and
     a guarded reserve; 102^2 representative states; the reserves converge, and so do restock and
     release; reserve against release diverges at (5, 5).
   - inventory_d_*: gsm's documented example over [0, 10^9]^3 at threshold 0: 13^3 states.
   Boundaries.
   - gap_*: the guard y - x >= 2 is in the fragment; the order-pattern check of AbstractionCutoff
     over {0, 1} passes and the registry diverges at (0, 2); the new check fails, as it must.
   - tri_*: triangle_diverges' guard z < x + y is not a difference constraint (tri_not_difference);
     dfrag refuses it for every anchor set and threshold, and it diverges at (2, 3, 4).
   - sum_*: x := y + y (a sum of two variable reads) is refused; the representative check at the
     threshold it would get passes, and the registry diverges at (0, 1000, 2000).
   - granularity_needs_chain: two increments by 3 in one event need a threshold of at least 6:
     states related at threshold 5 differ on CC1. *)

Require Import NC.Newman NC.Governance NC.SymmetryCutoff NC.AbstractionCutoff NC.Trace.
From Coq Require Import List Arith Lia Bool ZArith.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

(* ============================================================================================ *)
(* The rule language: gsm's combinators (V, Lit, Add, Sub; comparisons; And, Or, Not; guarded     *)
(* events of sequential assignments; invariants with repairs), with saturating Int writes.       *)
(* ============================================================================================ *)

Inductive dexp : Type :=
| DV (i : nat)
| DL (c : Z)
| DAdd (a b : dexp)
| DSub (a b : dexp).

Inductive cop : Type := CLe | CLt | CEq | CNe | CGe | CGt.

Inductive dpred : Type :=
| DTrue
| DCmp (o : cop) (a b : dexp)
| DAnd (p q : dpred)
| DOr (p q : dpred)
| DNot (p : dpred).

(* An assignment writes variable k; a transform is a list of assignments, applied left to right,
   each seeing the previous ones. *)
Definition assign : Type := (nat * dexp)%type.
Definition transform : Type := list assign.

(* A registry: the declared range [lo_i, hi_i] of each variable, the events (guard, effect), and
   the invariants (holds, repair). *)
Record dprog : Type := mkD {
  dlo : list Z;
  dhi : list Z;
  dev : list (dpred * transform);
  dinv : list (dpred * transform) }.

Fixpoint evalD (s : list Z) (e : dexp) : Z :=
  match e with
  | DV i => nth i s 0%Z
  | DL c => c
  | DAdd a b => (evalD s a + evalD s b)%Z
  | DSub a b => (evalD s a - evalD s b)%Z
  end.

Definition cmpZ (o : cop) (x y : Z) : bool :=
  match o with
  | CLe => Z.leb x y
  | CLt => Z.ltb x y
  | CEq => Z.eqb x y
  | CNe => negb (Z.eqb x y)
  | CGe => Z.leb y x
  | CGt => Z.ltb y x
  end.

Fixpoint evalP (s : list Z) (p : dpred) : bool :=
  match p with
  | DTrue => true
  | DCmp o a b => cmpZ o (evalD s a) (evalD s b)
  | DAnd p q => evalP s p && evalP s q
  | DOr p q => evalP s p || evalP s q
  | DNot p => negb (evalP s p)
  end.

(* gsm's SetInt: a write saturates at the declared bounds. *)
Definition clampZ (lo hi v : Z) : Z := if Z.ltb v lo then lo else if Z.ltb hi v then hi else v.

Fixpoint upd (s : list Z) (k : nat) (v : Z) : list Z :=
  match s, k with
  | [], _ => []
  | _ :: s', O => v :: s'
  | x :: s', S k' => x :: upd s' k' v
  end.

Section Sem.
  Variable P : dprog.

  Definition nv : nat := length (dlo P).

  Definition write (s : list Z) (a : assign) : list Z :=
    upd s (fst a) (clampZ (nth (fst a) (dlo P) 0%Z) (nth (fst a) (dhi P) 0%Z) (evalD s (snd a))).

  Definition applyT (t : transform) (s : list Z) : list Z := fold_left write t s.

  (* An event is a no-op when its guard is false. *)
  Definition evt (ev : dpred * transform) (s : list Z) : list Z :=
    if evalP s (fst ev) then applyT (snd ev) s else s.

  Definition dvalid (s : list Z) : bool := forallb (fun iv => evalP s (fst iv)) (dinv P).

  (* One repair step: the first violated invariant's repair (s when valid). *)
  Definition drepair (s : list Z) : list Z :=
    match find (fun iv => negb (evalP s (fst iv))) (dinv P) with
    | Some iv => applyT (snd iv) s
    | None => s
    end.

  Definition dap (k : nat) (s : list Z) : list Z :=
    match nth_error (dev P) k with Some ev => evt ev s | None => s end.

  (* The governed step: the event, then K repair steps. *)
  Definition dgov (K k : nat) (s : list Z) : list Z := itr K drepair (dap k s).

  (* gsm's runtime step: normalize, then the governed step. *)
  Definition drun (K k : nat) (s : list Z) : list Z := dgov K k (itr K drepair s).

  (* The states of the registry: every variable within its declared range. *)
  Definition InBox (s : list Z) : Prop :=
    length s = nv /\ forall i, (i < nv)%nat ->
      (nth i (dlo P) 0 <= nth i s 0 <= nth i (dhi P) 0)%Z.
End Sem.

(* ============================================================================================ *)
(* The difference fragment.                                                                     *)
(* ============================================================================================ *)

(* A difference term (p, q, c) denotes x_p - x_q + c, a missing variable reading as 0. *)
Definition dterm : Type := (option nat * option nat * Z)%type.

Definition optv (s : list Z) (o : option nat) : Z := match o with Some i => nth i s 0%Z | None => 0%Z end.

Definition evT (s : list Z) (d : dterm) : Z :=
  match d with (p, q, c) => (optv s p - optv s q + c)%Z end.

Definition merge (a b : option nat) : option (option nat) :=
  match a, b with
  | None, x => Some x
  | x, None => Some x
  | Some _, Some _ => None
  end.

Definition addT (x y : dterm) : option dterm :=
  match x, y with
  | (p1, q1, c1), (p2, q2, c2) =>
      match merge p1 p2, merge q1 q2 with
      | Some p, Some q => Some (p, q, (c1 + c2)%Z)
      | _, _ => None
      end
  end.

Definition negT (x : dterm) : dterm := match x with (p, q, c) => (q, p, (- c)%Z) end.

(* The normal form of an expression as a difference term: at most one variable with sign +1 and
   at most one with sign -1. None: outside the fragment (a sum of two variables, a negated
   variable added to another negated one). *)
Fixpoint norm (e : dexp) : option dterm :=
  match e with
  | DV i => Some (Some i, None, 0%Z)
  | DL c => Some (None, None, c)
  | DAdd a b => match norm a, norm b with Some x, Some y => addT x y | _, _ => None end
  | DSub a b => match norm a, norm b with Some x, Some y => addT x (negT y) | _, _ => None end
  end.

Lemma optv_merge : forall s a b o, merge a b = Some o -> optv s o = (optv s a + optv s b)%Z.
Proof. intros s [a|] [b|] o H; simpl in H; try discriminate; injection H as <-; simpl; lia. Qed.

Lemma addT_eval : forall s x y d, addT x y = Some d -> evT s d = (evT s x + evT s y)%Z.
Proof.
  intros s [[p1 q1] c1] [[p2 q2] c2] d H. simpl in H.
  destruct (merge p1 p2) as [p|] eqn:Hp; [|discriminate].
  destruct (merge q1 q2) as [q|] eqn:Hq; [|discriminate].
  injection H as <-. simpl. rewrite (optv_merge s _ _ _ Hp), (optv_merge s _ _ _ Hq). lia.
Qed.

Lemma negT_eval : forall s x, evT s (negT x) = (- evT s x)%Z.
Proof. intros s [[p q] c]. simpl. lia. Qed.

Theorem norm_eval : forall s e d, norm e = Some d -> evalD s e = evT s d.
Proof.
  intros s e. induction e as [i | c | a IHa b IHb | a IHa b IHb]; intros d H; simpl in H.
  - injection H as <-. simpl. lia.
  - injection H as <-. simpl. lia.
  - destruct (norm a) as [x|]; [|discriminate]. destruct (norm b) as [y|]; [|discriminate].
    simpl. rewrite (IHa x eq_refl), (IHb y eq_refl). symmetry. exact (addT_eval s x y d H).
  - destruct (norm a) as [x|]; [|discriminate]. destruct (norm b) as [y|]; [|discriminate].
    simpl. rewrite (IHa x eq_refl), (IHb y eq_refl). rewrite (addT_eval s x (negT y) d H), negT_eval. lia.
Qed.

Lemma cmpZ_sub : forall o x y, cmpZ o x y = cmpZ o (x - y) 0.
Proof.
  intros o x y. destruct o; simpl.
  - destruct (Z.leb_spec x y); destruct (Z.leb_spec (x - y) 0); lia.
  - destruct (Z.ltb_spec x y); destruct (Z.ltb_spec (x - y) 0); lia.
  - destruct (Z.eqb_spec x y); destruct (Z.eqb_spec (x - y) 0); simpl; lia.
  - destruct (Z.eqb_spec x y); destruct (Z.eqb_spec (x - y) 0); simpl; lia.
  - destruct (Z.leb_spec y x); destruct (Z.leb_spec 0 (x - y)); lia.
  - destruct (Z.ltb_spec y x); destruct (Z.ltb_spec 0 (x - y)); lia.
Qed.

Definition inZ (A : list Z) (z : Z) : bool := existsb (Z.eqb z) A.

Lemma inZ_spec : forall A z, inZ A z = true <-> In z A.
Proof.
  intros A z. unfold inZ. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply Z.eqb_eq in E. subst. exact Hx.
  - intros H. exists z. split; [exact H | apply Z.eqb_refl].
Qed.

Section Frag.
  Variable n : nat.         (* number of variables *)
  Variable A : list Z.      (* anchors: the bounds and the absolute constants *)
  Variable gam mu : Z.      (* largest difference-guard constant; largest offset per transform *)

  (* A comparison a op b, read as (a - b) op 0: a difference x_i - x_j against a constant of size
     at most gam, or a variable against an anchor. *)
  Definition atom_ok (d : option dterm) : bool :=
    match d with
    | Some (Some i, Some j, c) => Nat.ltb i n && Nat.ltb j n && Z.leb (Z.abs c) gam
    | Some (Some i, None, c) => Nat.ltb i n && inZ A (- c)
    | Some (None, Some j, c) => Nat.ltb j n && inZ A c
    | Some (None, None, _) => true
    | None => false
    end.

  Fixpoint pok (p : dpred) : bool :=
    match p with
    | DTrue => true
    | DCmp _ a b => atom_ok (norm (DSub a b))
    | DAnd p q | DOr p q => pok p && pok q
    | DNot p => pok p
    end.

  (* Writes: x_k := x_j + c (increment, decrement, copy with offset) or x_k := c with c an anchor. *)
  Definition aok (a : assign) : bool :=
    Nat.ltb (fst a) n &&
    match norm (snd a) with
    | Some (Some j, None, _) => Nat.ltb j n
    | Some (None, None, c) => inZ A c
    | _ => false
    end.

  (* The offset a write adds. *)
  Definition aloss (a : assign) : Z :=
    match norm (snd a) with Some (Some _, None, c) => Z.abs c | _ => 0%Z end.

  Definition tloss (t : transform) : Z := fold_right (fun a acc => (aloss a + acc)%Z) 0%Z t.

  Definition tok (t : transform) : bool := forallb aok t && Z.leb (tloss t) mu.
End Frag.

(* The fragment check: bounds well formed and among the anchors, every rule in the fragment. *)
Definition bnd_ok (P : dprog) (A : list Z) : bool :=
  Nat.eqb (length (dlo P)) (length (dhi P)) &&
  forallb (fun i => Z.leb (nth i (dlo P) 0%Z) (nth i (dhi P) 0%Z) &&
                    inZ A (nth i (dlo P) 0%Z) && inZ A (nth i (dhi P) 0%Z)) (seq 0 (nv P)).

Definition dfrag (P : dprog) (A : list Z) (gam mu : Z) : bool :=
  bnd_ok P A && Z.leb 0 gam && Z.leb 0 mu &&
  forallb (fun ev => pok (nv P) A gam (fst ev) && tok (nv P) A mu (snd ev)) (dev P) &&
  forallb (fun iv => pok (nv P) A gam (fst iv) && tok (nv P) A mu (snd iv)) (dinv P).

(* ============================================================================================ *)
(* The region relation: differences equal, or both beyond W on the same side.                    *)
(* ============================================================================================ *)

Definition near (W d d' : Z) : Prop :=
  d = d' \/ (W < d /\ W < d')%Z \/ (d < - W /\ d' < - W)%Z.

Lemma near_refl : forall W d, near W d d.
Proof. intros W d. left. reflexivity. Qed.

Lemma near_sym : forall W d d', near W d d' -> near W d' d.
Proof. intros W d d' [H | [H | H]]; [left | right; left | right; right]; lia. Qed.

Lemma near_trans : forall W d1 d2 d3, (0 <= W)%Z -> near W d1 d2 -> near W d2 d3 -> near W d1 d3.
Proof. intros W d1 d2 d3 HW [H1 | [H1 | H1]] [H2 | [H2 | H2]]; unfold near; lia. Qed.

Lemma near_mono : forall W W' d d', (W' <= W)%Z -> near W d d' -> near W' d d'.
Proof. intros W W' d d' Hw [H | [H | H]]; unfold near; lia. Qed.

Lemma near_neg : forall W d d', near W d d' -> near W (- d) (- d').
Proof. intros W d d' [H | [H | H]]; unfold near; lia. Qed.

(* An offset c moves the threshold by |c|. *)
Lemma near_shift : forall W d d' c, near W d d' -> near (W - Z.abs c) (d + c) (d' + c).
Proof. intros W d d' c [H | [H | H]]; unfold near; lia. Qed.

(* A comparison against a constant of size at most W has the same outcome. *)
Lemma near_cmp : forall W d d' c o, near W d d' -> (- W <= c <= W)%Z ->
  cmpZ o (d + c) 0 = cmpZ o (d' + c) 0.
Proof.
  intros W d d' c o [H | [H | H]] Hc; [subst; reflexivity | |];
    destruct o; simpl;
    repeat match goal with
           | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
           | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
           | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
           end; simpl; try reflexivity; lia.
Qed.

(* With threshold 0, near is equality of signs: the order type. *)
Lemma near0_compare : forall d d', near 0 d d' <-> Z.compare d 0 = Z.compare d' 0.
Proof.
  intros d d'. unfold near. split.
  - intros [H | [H | H]]; [subst; reflexivity | |];
      destruct (Z.compare_spec d 0); destruct (Z.compare_spec d' 0); try reflexivity; lia.
  - intros H. destruct (Z.compare_spec d 0) as [E | E | E]; destruct (Z.compare_spec d' 0) as [E' | E' | E'];
      try discriminate; lia.
Qed.

(* The relation on a list of value pairs (a value in the first run, its counterpart in the second). *)
Definition Rel (W : Z) (L : list (Z * Z)) : Prop :=
  forall x y, In x L -> In y L -> near W (fst x - fst y) (snd x - snd y).

Lemma Rel_incl : forall W L L', incl L' L -> Rel W L -> Rel W L'.
Proof. intros W L L' Hi H x y Hx Hy. apply H; apply Hi; assumption. Qed.

Lemma Rel_mono : forall W W' L, (W' <= W)%Z -> Rel W L -> Rel W' L.
Proof. intros W W' L Hw H x y Hx Hy. apply (near_mono W); [exact Hw | apply H; assumption]. Qed.

(* A new pair related to every pair of L. *)
Lemma Rel_cons : forall W L v v', Rel W L ->
  (forall y, In y L -> near W (v - fst y) (v' - snd y)) -> Rel W ((v, v') :: L).
Proof.
  intros W L v v' H Hv x y [<- | Hx] [<- | Hy]; simpl.
  - replace (v - v)%Z with 0%Z by lia. replace (v' - v')%Z with 0%Z by lia. apply near_refl.
  - apply Hv. exact Hy.
  - replace (fst x - v)%Z with (- (v - fst x))%Z by lia. replace (snd x - v')%Z with (- (v' - snd x))%Z by lia.
    apply near_neg. apply Hv. exact Hx.
  - apply H; assumption.
Qed.

Definition anc (A : list Z) : list (Z * Z) := map (fun a => (a, a)) A.

Definition AncIn (A : list Z) (L : list (Z * Z)) : Prop := forall a, In a A -> In (a, a) L.

(* The relation between two states, with the anchors. *)
Definition RelS (W : Z) (A s s' : list Z) : Prop :=
  length s = length s' /\ Rel W (combine s s' ++ anc A).

Lemma in_anc : forall A a, In a A -> In (a, a) (anc A).
Proof. intros A a H. unfold anc. apply in_map_iff. exists a. split; [reflexivity | exact H]. Qed.

Lemma in_anc_inv : forall A x, In x (anc A) -> In (fst x) A /\ snd x = fst x.
Proof. intros A x H. unfold anc in H. apply in_map_iff in H. destruct H as [a [<- Ha]]. simpl. split; [exact Ha | reflexivity]. Qed.

Lemma in_combine_nth : forall (s s' : list Z) i, length s = length s' -> (i < length s)%nat ->
  In (nth i s 0%Z, nth i s' 0%Z) (combine s s').
Proof.
  induction s as [|x s IH]; intros [|y s'] i Hl Hi; simpl in *; try lia.
  destruct i as [|i]; [left; reflexivity | right; apply IH; lia].
Qed.

Lemma in_combine_ex : forall (s s' : list Z) x, In x (combine s s') -> length s = length s' ->
  exists i, (i < length s)%nat /\ x = (nth i s 0%Z, nth i s' 0%Z).
Proof.
  induction s as [|a s IH]; intros [|b s'] x Hx Hl; simpl in *; try contradiction; try lia.
  destruct Hx as [<- | Hx]; [exists 0%nat; split; [lia | reflexivity]|].
  destruct (IH s' x Hx ltac:(lia)) as [i [Hi E]]. exists (S i). split; [lia | exact E].
Qed.

Lemma combine_upd : forall (s s' : list Z) k v v',
  incl (combine (upd s k v) (upd s' k v')) ((v, v') :: combine s s').
Proof.
  induction s as [|x s IH]; intros [|y s'] k v v' z Hz; destruct k as [|k]; simpl in *; try contradiction.
  - destruct Hz as [<- | Hz]; [left; reflexivity | right; right; exact Hz].
  - destruct Hz as [<- | Hz]; [right; left; reflexivity|].
    destruct (IH s' k v v' z Hz) as [E | E]; [left; exact E | right; right; exact E].
Qed.

Lemma upd_len : forall s k v, length (upd s k v) = length s.
Proof. induction s as [|x s IH]; intros [|k] v; simpl; auto. Qed.

Lemma upd_nth_eq : forall s k v, (k < length s)%nat -> nth k (upd s k v) 0%Z = v.
Proof.
  induction s as [|x s IH]; intros [|k] v H; simpl in *; try lia; try reflexivity. apply IH. lia.
Qed.

Lemma upd_nth_neq : forall s k i v, i <> k -> nth i (upd s k v) 0%Z = nth i s 0%Z.
Proof.
  induction s as [|x s IH]; intros [|k] [|i] v H; simpl; try reflexivity; try lia. apply IH. lia.
Qed.


Lemma combine_len : forall (s s' : list Z), length s = length s' -> length (combine s s') = length s.
Proof. induction s as [|x s IH]; intros [|y s'] H; simpl in *; try lia. rewrite IH; lia. Qed.

Lemma find_ext_in : forall {X : Type} (f g : X -> bool) l, (forall x, In x l -> f x = g x) ->
  find f l = find g l.
Proof.
  intros X f g l. induction l as [|x l IH]; intros H; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). destruct (g x); [reflexivity|]. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma forallb_ext_in : forall {X : Type} (f g : X -> bool) l, (forall x, In x l -> f x = g x) ->
  forallb f l = forallb g l.
Proof.
  intros X f g l. induction l as [|x l IH]; intros H; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma aloss_nonneg : forall a, (0 <= aloss a)%Z.
Proof. intros [k e]. unfold aloss. simpl. destruct (norm e) as [[[[p|] [q|]] c]|]; lia. Qed.

Lemma tloss_nonneg : forall t, (0 <= tloss t)%Z.
Proof. induction t as [|a t IH]; simpl; [lia|]. pose proof (aloss_nonneg a). lia. Qed.

(* ============================================================================================ *)
(* One run against another: every rule keeps the relation, with the threshold lowered by the     *)
(* offsets it adds.                                                                             *)
(* ============================================================================================ *)

Section Transfer.
  Variable P : dprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : dfrag P A gam mu = true.

  Local Notation n := (nv P).

  Lemma frag_parts :
    bnd_ok P A = true /\ (0 <= gam)%Z /\ (0 <= mu)%Z /\
    (forall ev, In ev (dev P) -> pok n A gam (fst ev) = true /\ tok n A mu (snd ev) = true) /\
    (forall iv, In iv (dinv P) -> pok n A gam (fst iv) = true /\ tok n A mu (snd iv) = true).
  Proof.
    unfold dfrag in HF. apply andb_true_iff in HF as [H H5]. apply andb_true_iff in H as [H H4].
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    rewrite forallb_forall in H4, H5. apply Z.leb_le in H2, H3.
    split; [exact H1 | split; [exact H2 | split; [exact H3 | split]]].
    - intros ev Hev. specialize (H4 ev Hev). apply andb_true_iff in H4. exact H4.
    - intros iv Hiv. specialize (H5 iv Hiv). apply andb_true_iff in H5. exact H5.
  Qed.

  Lemma gam_nonneg : (0 <= gam)%Z.
  Proof. apply frag_parts. Qed.

  Lemma mu_nonneg : (0 <= mu)%Z.
  Proof. apply frag_parts. Qed.

  Lemma bnd_parts : length (dhi P) = n /\ forall i, (i < n)%nat ->
    (nth i (dlo P) 0 <= nth i (dhi P) 0)%Z /\ In (nth i (dlo P) 0%Z) A /\ In (nth i (dhi P) 0%Z) A.
  Proof.
    destruct frag_parts as [H _]. unfold bnd_ok in H. apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1. rewrite forallb_forall in H2. split; [unfold nv; lia|].
    intros i Hi. assert (Hs : In i (seq 0 n)) by (apply in_seq; lia).
    specialize (H2 i Hs). apply andb_true_iff in H2 as [H2 Hh]. apply andb_true_iff in H2 as [Hle Hl].
    apply Z.leb_le in Hle. apply inZ_spec in Hl, Hh. split; [exact Hle | split; assumption].
  Qed.

  Section Pair.
    Variable s s' : list Z.
    Variable L : list (Z * Z).
    Hypothesis Ls : length s = n.
    Hypothesis Ls' : length s' = n.
    Hypothesis Hc : incl (combine s s') L.
    Hypothesis HA : AncIn A L.

    Lemma var_in : forall i, (i < n)%nat -> In (nth i s 0%Z, nth i s' 0%Z) L.
    Proof. intros i Hi. apply Hc. apply in_combine_nth; lia. Qed.

    Lemma atom_same : forall W d o, Rel W L -> (gam <= W)%Z -> atom_ok n A gam (Some d) = true ->
      cmpZ o (evT s d) 0 = cmpZ o (evT s' d) 0.
    Proof.
      intros W [[[i|] [j|]] c] o HR Hw Hok; simpl in Hok |- *; pose proof gam_nonneg as G.
      - apply andb_true_iff in Hok as [Hok Hc']. apply andb_true_iff in Hok as [Hi Hj].
        apply Nat.ltb_lt in Hi, Hj. apply Z.leb_le in Hc'.
        pose proof (HR _ _ (var_in i Hi) (var_in j Hj)) as N. simpl in N.
        apply (near_cmp W _ _ c o N). lia.
      - apply andb_true_iff in Hok as [Hi Ha]. apply Nat.ltb_lt in Hi. apply inZ_spec in Ha.
        pose proof (HR _ _ (var_in i Hi) (HA _ Ha)) as N. simpl in N.
        match goal with |- cmpZ o ?x 0 = cmpZ o ?y 0 =>
          replace x with (nth i s 0 - - c + 0)%Z by lia; replace y with (nth i s' 0 - - c + 0)%Z by lia end.
        apply (near_cmp W _ _ 0 o N). lia.
      - apply andb_true_iff in Hok as [Hj Ha]. apply Nat.ltb_lt in Hj. apply inZ_spec in Ha.
        pose proof (HR _ _ (HA _ Ha) (var_in j Hj)) as N. simpl in N.
        match goal with |- cmpZ o ?x 0 = cmpZ o ?y 0 =>
          replace x with (c - nth j s 0 + 0)%Z by lia; replace y with (c - nth j s' 0 + 0)%Z by lia end.
        apply (near_cmp W _ _ 0 o N). lia.
      - reflexivity.
    Qed.

    Lemma pred_same : forall W p, Rel W L -> (gam <= W)%Z -> pok n A gam p = true -> evalP s p = evalP s' p.
    Proof.
      intros W p HR Hw. induction p as [| o a b | p IHp q IHq | p IHp q IHq | p IHp]; intros Hok; simpl.
      - reflexivity.
      - change (atom_ok n A gam (norm (DSub a b)) = true) in Hok. rewrite (cmpZ_sub o (evalD s a)), (cmpZ_sub o (evalD s' a)).
        destruct (norm (DSub a b)) as [d|] eqn:E; [|discriminate].
        pose proof (norm_eval s (DSub a b) d E) as E1. pose proof (norm_eval s' (DSub a b) d E) as E2.
        simpl in E1, E2. rewrite E1, E2. apply (atom_same W d o HR Hw Hok).
      - simpl in Hok. apply andb_true_iff in Hok as [H1 H2]. rewrite IHp, IHq by assumption. reflexivity.
      - simpl in Hok. apply andb_true_iff in Hok as [H1 H2]. rewrite IHp, IHq by assumption. reflexivity.
      - simpl in Hok. rewrite IHp by assumption. reflexivity.
    Qed.
  End Pair.

  (* A saturating write x := x_j + c keeps the relation with the threshold lowered by |c|. *)
  Lemma clamp_near : forall W L x x' lo hi c, Rel W L -> In (x, x') L -> In (lo, lo) L -> In (hi, hi) L ->
    (Z.abs c <= W)%Z ->
    forall y, In y L -> near (W - Z.abs c) (clampZ lo hi (x + c) - fst y) (clampZ lo hi (x' + c) - snd y).
  Proof.
    intros W L x x' lo hi c HR Hx Hlo Hhi Hc y Hy.
    pose proof (near_cmp W _ _ c CLt (HR _ _ Hx Hlo) ltac:(lia)) as E1. simpl in E1.
    pose proof (near_cmp W _ _ c CGt (HR _ _ Hx Hhi) ltac:(lia)) as E2. simpl in E2.
    unfold clampZ.
    assert (R1 : Z.ltb (x + c) lo = Z.ltb (x - lo + c) 0).
    { destruct (Z.ltb_spec (x + c) lo); destruct (Z.ltb_spec (x - lo + c) 0); lia. }
    assert (R1' : Z.ltb (x' + c) lo = Z.ltb (x' - lo + c) 0).
    { destruct (Z.ltb_spec (x' + c) lo); destruct (Z.ltb_spec (x' - lo + c) 0); lia. }
    assert (R2 : Z.ltb hi (x + c) = Z.ltb 0 (x - hi + c)).
    { destruct (Z.ltb_spec hi (x + c)); destruct (Z.ltb_spec 0 (x - hi + c)); lia. }
    assert (R2' : Z.ltb hi (x' + c) = Z.ltb 0 (x' - hi + c)).
    { destruct (Z.ltb_spec hi (x' + c)); destruct (Z.ltb_spec 0 (x' - hi + c)); lia. }
    rewrite R1, R1', R2, R2'. simpl in E1, E2. rewrite <- E1, <- E2.
    destruct (Z.ltb (x - lo + c) 0).
    - apply (near_mono W); [lia|]. exact (HR _ _ Hlo Hy).
    - destruct (Z.ltb 0 (x - hi + c)).
      + apply (near_mono W); [lia|]. exact (HR _ _ Hhi Hy).
      + pose proof (near_shift W _ _ c (HR _ _ Hx Hy)) as N. simpl in N.
        replace (x + c - fst y)%Z with (x - fst y + c)%Z by lia.
        replace (x' + c - snd y)%Z with (x' - snd y + c)%Z by lia. exact N.
  Qed.

  Lemma write_rel : forall W s s' L a, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> aok n A a = true -> (aloss a <= W)%Z ->
    length (write P s a) = n /\ length (write P s' a) = n /\
    Rel (W - aloss a) (combine (write P s a) (write P s' a) ++ L).
  Proof.
    intros W s s' L [k e] Ls Ls' HA HR Hok Hw. unfold write, aok, aloss in *. simpl in *.
    rewrite !upd_len. split; [exact Ls | split; [exact Ls'|]].
    apply andb_true_iff in Hok as [Hk Hok]. apply Nat.ltb_lt in Hk.
    destruct (proj2 bnd_parts k Hk) as [_ [Hlo Hhi]].
    set (M := combine s s' ++ L).
    assert (HAM : AncIn A M) by (intros z Hz; apply in_or_app; right; apply HA; exact Hz).
    assert (Inc : incl (combine (upd s k (clampZ (nth k (dlo P) 0%Z) (nth k (dhi P) 0%Z) (evalD s e)))
                                (upd s' k (clampZ (nth k (dlo P) 0%Z) (nth k (dhi P) 0%Z) (evalD s' e))) ++ L)
                       ((clampZ (nth k (dlo P) 0%Z) (nth k (dhi P) 0%Z) (evalD s e),
                         clampZ (nth k (dlo P) 0%Z) (nth k (dhi P) 0%Z) (evalD s' e)) :: M)).
    { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz].
      - destruct (combine_upd s s' k _ _ z Hz) as [E | E]; [left; exact E | right; apply in_or_app; left; exact E].
      - right. apply in_or_app. right. exact Hz. }
    destruct (norm e) as [[[[j|] [q|]] c]|] eqn:E; try discriminate.
    - apply Nat.ltb_lt in Hok. rewrite (norm_eval s e _ E), (norm_eval s' e _ E). simpl in *.
      rewrite (norm_eval s e _ E), (norm_eval s' e _ E) in Inc. simpl in Inc.
      replace (nth j s 0 - 0 + c)%Z with (nth j s 0 + c)%Z in * by lia.
      replace (nth j s' 0 - 0 + c)%Z with (nth j s' 0 + c)%Z in * by lia.
      apply (Rel_incl _ _ _ Inc). apply Rel_cons; [apply (Rel_mono W); [pose proof (Z.abs_nonneg c); lia | exact HR]|].
      apply (clamp_near W M); [exact HR | | apply HAM; exact Hlo | apply HAM; exact Hhi | exact Hw].
      apply in_or_app. left. apply in_combine_nth; lia.
    - apply inZ_spec in Hok. rewrite (norm_eval s e _ E), (norm_eval s' e _ E). simpl in *.
      rewrite (norm_eval s e _ E), (norm_eval s' e _ E) in Inc. simpl in Inc.
      replace (0 - 0 + c)%Z with c in * by lia. replace (W - 0)%Z with W by lia.
      apply (Rel_incl _ _ _ Inc). apply Rel_cons; [exact HR|].
      assert (Hv : In (clampZ (nth k (dlo P) 0%Z) (nth k (dhi P) 0%Z) c) A).
      { unfold clampZ. destruct (Z.ltb c (nth k (dlo P) 0%Z)); [exact Hlo|].
        destruct (Z.ltb (nth k (dhi P) 0%Z) c); [exact Hhi | exact Hok]. }
      intros y Hy. exact (HR _ _ (HAM _ Hv) Hy).
  Qed.

  Lemma applyT_rel : forall t W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> forallb (aok n A) t = true -> (tloss t <= W)%Z ->
    length (applyT P t s) = n /\ length (applyT P t s') = n /\
    Rel (W - tloss t) (combine (applyT P t s) (applyT P t s') ++ L).
  Proof.
    induction t as [|a t IH]; intros W s s' L Ls Ls' HA HR Hok Hw; simpl in *.
    - replace (W - 0)%Z with W by lia. split; [exact Ls | split; [exact Ls' | exact HR]].
    - apply andb_true_iff in Hok as [Ha Ht]. pose proof (tloss_nonneg t) as T.
      destruct (write_rel W s s' L a Ls Ls' HA HR Ha ltac:(lia)) as [L1 [L1' R1]].
      destruct (IH (W - aloss a)%Z _ _ L L1 L1' HA R1 Ht ltac:(lia)) as [L2 [L2' R2]].
      unfold applyT in *. simpl. split; [exact L2 | split; [exact L2'|]].
      replace (W - (aloss a + tloss t))%Z with (W - aloss a - tloss t)%Z by lia. exact R2.
  Qed.

  Lemma tok_parts : forall t, tok n A mu t = true -> forallb (aok n A) t = true /\ (tloss t <= mu)%Z.
  Proof. intros t H. unfold tok in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H2. split; assumption. Qed.

  Lemma transform_rel : forall t W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> tok n A mu t = true -> (mu <= W)%Z ->
    length (applyT P t s) = n /\ length (applyT P t s') = n /\
    Rel (W - mu) (combine (applyT P t s) (applyT P t s') ++ L).
  Proof.
    intros t W s s' L Ls Ls' HA HR Ht Hw. destruct (tok_parts t Ht) as [Ha Hl].
    destruct (applyT_rel t W s s' L Ls Ls' HA HR Ha ltac:(lia)) as [L1 [L1' R1]].
    split; [exact L1 | split; [exact L1' | apply (Rel_mono (W - tloss t)); [lia | exact R1]]].
  Qed.

  Lemma incl_head : forall (s s' : list Z) (L : list (Z * Z)), incl (combine s s') (combine s s' ++ L).
  Proof. intros s s' L z Hz. apply in_or_app. left. exact Hz. Qed.

  Lemma anc_tail : forall (s s' : list Z) (L : list (Z * Z)), AncIn A L -> AncIn A (combine s s' ++ L).
  Proof. intros s s' L H z Hz. apply in_or_app. right. apply H. exact Hz. Qed.

  (* Validity and the repair step. *)
  Lemma dvalid_same : forall W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam <= W)%Z -> dvalid P s = dvalid P s'.
  Proof.
    intros W s s' L Ls Ls' HA HR Hw. unfold dvalid.
    destruct frag_parts as [_ [_ [_ [_ Hi]]]].
    assert (E : forall iv, In iv (dinv P) -> evalP s (fst iv) = evalP s' (fst iv)).
    { intros iv Hiv. apply (pred_same s s' _ Ls Ls' (incl_head s s' L) (anc_tail s s' L HA) W);
        [exact HR | exact Hw | apply (Hi iv Hiv)]. }
    apply forallb_ext_in. exact E.
  Qed.

  Lemma drepair_rel : forall W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam + mu <= W)%Z ->
    length (drepair P s) = n /\ length (drepair P s') = n /\
    Rel (W - mu) (combine (drepair P s) (drepair P s') ++ L).
  Proof.
    intros W s s' L Ls Ls' HA HR Hw. pose proof gam_nonneg. pose proof mu_nonneg.
    destruct frag_parts as [_ [_ [_ [_ Hi]]]]. unfold drepair.
    rewrite (find_ext_in (fun iv => negb (evalP s (fst iv))) (fun iv => negb (evalP s' (fst iv)))).
    - destruct (find (fun iv => negb (evalP s' (fst iv))) (dinv P)) as [iv|] eqn:Ef.
      + apply find_some in Ef. destruct Ef as [Hiv _].
        apply (transform_rel (snd iv) W s s' L Ls Ls' HA HR); [apply (Hi iv Hiv) | lia].
      + split; [exact Ls | split; [exact Ls' | apply (Rel_mono W); [lia | exact HR]]].
    - intros iv Hiv. f_equal.
      apply (pred_same s s' _ Ls Ls' (incl_head s s' L) (anc_tail s s' L HA) W); [exact HR | lia | apply (Hi iv Hiv)].
  Qed.

  Lemma itr_rel : forall j W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam + Z.of_nat j * mu <= W)%Z ->
    length (itr j (drepair P) s) = n /\ length (itr j (drepair P) s') = n /\
    Rel (W - Z.of_nat j * mu) (combine (itr j (drepair P) s) (itr j (drepair P) s') ++ L).
  Proof.
    induction j as [|j IH]; intros W s s' L Ls Ls' HA HR Hw; cbn [itr].
    - split; [exact Ls | split; [exact Ls' | apply (Rel_mono W); [lia | exact HR]]].
    - pose proof mu_nonneg.
      destruct (drepair_rel W s s' L Ls Ls' HA HR ltac:(lia)) as [L1 [L1' R1]].
      destruct (IH (W - mu)%Z _ _ L L1 L1' HA R1 ltac:(lia)) as [L2 [L2' R2]].
      split; [exact L2 | split; [exact L2'|]].
      apply (Rel_mono (W - mu - Z.of_nat j * mu)); [lia | exact R2].
  Qed.

  Lemma dap_rel : forall k W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam + mu <= W)%Z ->
    length (dap P k s) = n /\ length (dap P k s') = n /\
    Rel (W - mu) (combine (dap P k s) (dap P k s') ++ L).
  Proof.
    intros k W s s' L Ls Ls' HA HR Hw. pose proof gam_nonneg. pose proof mu_nonneg.
    destruct frag_parts as [_ [_ [_ [He _]]]]. unfold dap.
    destruct (nth_error (dev P) k) as [ev|] eqn:Ek.
    - pose proof (He ev (nth_error_In _ _ Ek)) as [Hg Ht]. unfold evt.
      rewrite (pred_same s s' _ Ls Ls' (incl_head s s' L) (anc_tail s s' L HA) W (fst ev) HR ltac:(lia) Hg).
      destruct (evalP s' (fst ev)).
      + apply (transform_rel (snd ev) W s s' L Ls Ls' HA HR Ht). lia.
      + split; [exact Ls | split; [exact Ls' | apply (Rel_mono W); [lia | exact HR]]].
    - split; [exact Ls | split; [exact Ls' | apply (Rel_mono W); [lia | exact HR]]].
  Qed.

  (* The governed step lowers the threshold by (K + 1) mu. *)
  Lemma dgov_rel : forall K k W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam + Z.of_nat (S K) * mu <= W)%Z ->
    length (dgov P K k s) = n /\ length (dgov P K k s') = n /\
    Rel (W - Z.of_nat (S K) * mu) (combine (dgov P K k s) (dgov P K k s') ++ L).
  Proof.
    intros K k W s s' L Ls Ls' HA HR Hw. pose proof mu_nonneg.
    destruct (dap_rel k W s s' L Ls Ls' HA HR ltac:(lia)) as [L1 [L1' R1]].
    destruct (itr_rel K (W - mu)%Z _ _ L L1 L1' HA R1 ltac:(lia)) as [L2 [L2' R2]].
    unfold dgov. split; [exact L2 | split; [exact L2'|]].
    replace (W - Z.of_nat (S K) * mu)%Z with (W - mu - Z.of_nat K * mu)%Z by lia. exact R2.
  Qed.

  Lemma dgov2_rel : forall K k1 k2 W s s' L, length s = n -> length s' = n -> AncIn A L ->
    Rel W (combine s s' ++ L) -> (gam + 2 * Z.of_nat (S K) * mu <= W)%Z ->
    length (dgov P K k2 (dgov P K k1 s)) = n /\ length (dgov P K k2 (dgov P K k1 s')) = n /\
    Rel (W - 2 * Z.of_nat (S K) * mu)
        (combine (dgov P K k2 (dgov P K k1 s)) (dgov P K k2 (dgov P K k1 s')) ++ L).
  Proof.
    intros K k1 k2 W s s' L Ls Ls' HA HR Hw. pose proof mu_nonneg.
    destruct (dgov_rel K k1 W s s' L Ls Ls' HA HR ltac:(nia)) as [L1 [L1' R1]].
    destruct (dgov_rel K k2 _ _ _ L L1 L1' HA R1 ltac:(nia)) as [L2 [L2' R2]].
    split; [exact L2 | split; [exact L2'|]].
    replace (W - 2 * Z.of_nat (S K) * mu)%Z with (W - Z.of_nat (S K) * mu - Z.of_nat (S K) * mu)%Z by lia.
    exact R2.
  Qed.

  (* ---- The pairwise transfers: one state against a related one. ---- *)

  Lemma rels_parts : forall W s s', RelS W A s s' -> length s = n -> length s' = n /\
    Rel W (combine s s' ++ anc A).
  Proof. intros W s s' [Hl HR] Ls. split; [lia | exact HR]. Qed.

  Lemma dup_rel : forall W s s', Rel W (combine s s' ++ anc A) -> Rel W (combine s s' ++ combine s s' ++ anc A).
  Proof.
    intros W s s' HR. apply (Rel_incl _ _ _ ltac:(intros z Hz; apply in_app_or in Hz;
      destruct Hz as [Hz | Hz]; [apply in_or_app; left; exact Hz | exact Hz]) HR).
  Qed.

  Lemma swap_incl : forall (X Y Z : list (Z * Z)), incl (X ++ Y ++ Z) (Y ++ X ++ Z).
  Proof.
    intros X Y Z z Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz].
    - apply in_or_app. right. apply in_or_app. left. exact Hz.
    - apply in_app_or in Hz. destruct Hz as [Hz | Hz]; [apply in_or_app; left; exact Hz|].
      apply in_or_app. right. apply in_or_app. right. exact Hz.
  Qed.

  Lemma ancA : AncIn A (anc A).
  Proof. intros a Ha. apply in_anc. exact Ha. Qed.

  Theorem valid_pair : forall W s s', RelS W A s s' -> length s = n -> (gam <= W)%Z ->
    dvalid P s = dvalid P s'.
  Proof.
    intros W s s' H Ls Hw. destruct (rels_parts W s s' H Ls) as [Ls' HR].
    exact (dvalid_same W s s' (anc A) Ls Ls' ancA HR Hw).
  Qed.

  Theorem term_pair : forall K W s s', RelS W A s s' -> length s = n -> (gam + Z.of_nat K * mu <= W)%Z ->
    dvalid P (itr K (drepair P) s) = dvalid P (itr K (drepair P) s').
  Proof.
    intros K W s s' H Ls Hw. destruct (rels_parts W s s' H Ls) as [Ls' HR].
    destruct (itr_rel K W s s' (anc A) Ls Ls' ancA HR Hw) as [L1 [L1' R1]].
    exact (dvalid_same _ _ _ (anc A) L1 L1' ancA R1 ltac:(lia)).
  Qed.

  (* Equality of two final states transfers when the threshold is still nonnegative. *)
  Lemma eq_transfer : forall W a a' b b' L, (0 <= W)%Z -> length a = n -> length a' = n ->
    length b = n -> length b' = n -> incl (combine a a') L -> incl (combine b b') L -> Rel W L ->
    (a = b <-> a' = b').
  Proof.
    intros W a a' b b' L HW La La' Lb Lb' Ha Hb HR.
    assert (Hi : forall i, (i < n)%nat -> (nth i a 0 = nth i b 0 <-> nth i a' 0 = nth i b' 0)%Z).
    { intros i Hi. pose proof (HR _ _ (Ha _ (in_combine_nth a a' i ltac:(lia) ltac:(lia)))
                                     (Hb _ (in_combine_nth b b' i ltac:(lia) ltac:(lia)))) as N.
      simpl in N. destruct N as [N | [N | N]]; lia. }
    split; intros E.
    - apply (nth_ext a' b' 0%Z 0%Z); [lia|]. intros i Hi'. apply Hi; [lia|]. rewrite E. reflexivity.
    - apply (nth_ext a b 0%Z 0%Z); [lia|]. intros i Hi'. apply Hi; [lia|]. rewrite E. reflexivity.
  Qed.

  Lemma incl_mid : forall (X Y Z : list (Z * Z)), incl Y (X ++ Y ++ Z).
  Proof. intros X Y Z z Hz. apply in_or_app. right. apply in_or_app. left. exact Hz. Qed.

  (* CC1 of a pair of events: threshold gam + 4 (K + 1) mu. *)
  Theorem cc1_pair : forall K k1 k2 W s s', RelS W A s s' -> length s = n ->
    (gam + 4 * Z.of_nat (S K) * mu <= W)%Z ->
    (dgov P K k2 (dgov P K k1 s) = dgov P K k1 (dgov P K k2 s) <->
     dgov P K k2 (dgov P K k1 s') = dgov P K k1 (dgov P K k2 s')).
  Proof.
    intros K k1 k2 W s s' H Ls Hw. destruct (rels_parts W s s' H Ls) as [Ls' HR].
    pose proof mu_nonneg. pose proof gam_nonneg.
    set (a := dgov P K k2 (dgov P K k1 s)). set (a' := dgov P K k2 (dgov P K k1 s')).
    destruct (dgov2_rel K k1 k2 W s s' (combine s s' ++ anc A) Ls Ls' (anc_tail s s' _ ancA) (dup_rel W s s' HR)
                ltac:(nia)) as [La [La' Ra]].
    fold a a' in La, La', Ra.
    assert (R2 : Rel (W - 2 * Z.of_nat (S K) * mu) (combine s s' ++ combine a a' ++ anc A)).
    { apply (Rel_incl _ _ _ (swap_incl _ _ _) Ra). }
    destruct (dgov2_rel K k2 k1 _ s s' (combine a a' ++ anc A) Ls Ls' (anc_tail a a' _ ancA) R2 ltac:(nia))
      as [Lb [Lb' Rb]].
    apply (eq_transfer (W - 2 * Z.of_nat (S K) * mu - 2 * Z.of_nat (S K) * mu) a a' _ _ _ ltac:(nia)
             La La' Lb Lb' (incl_mid _ _ _) (incl_head _ _ _) Rb).
  Qed.

  (* Idempotence of an event: threshold gam + 3 (K + 1) mu. *)
  Theorem idem_pair : forall K k W s s', RelS W A s s' -> length s = n ->
    (gam + 3 * Z.of_nat (S K) * mu <= W)%Z ->
    (dgov P K k (dgov P K k s) = dgov P K k s <-> dgov P K k (dgov P K k s') = dgov P K k s').
  Proof.
    intros K k W s s' H Ls Hw. destruct (rels_parts W s s' H Ls) as [Ls' HR].
    pose proof mu_nonneg. pose proof gam_nonneg.
    set (a := dgov P K k (dgov P K k s)). set (a' := dgov P K k (dgov P K k s')).
    destruct (dgov2_rel K k k W s s' (combine s s' ++ anc A) Ls Ls' (anc_tail s s' _ ancA) (dup_rel W s s' HR)
                ltac:(nia)) as [La [La' Ra]].
    fold a a' in La, La', Ra.
    assert (R2 : Rel (W - 2 * Z.of_nat (S K) * mu) (combine s s' ++ combine a a' ++ anc A)).
    { apply (Rel_incl _ _ _ (swap_incl _ _ _) Ra). }
    destruct (dgov_rel K k _ s s' (combine a a' ++ anc A) Ls Ls' (anc_tail a a' _ ancA) R2 ltac:(nia))
      as [Lb [Lb' Rb]].
    apply (eq_transfer (W - 2 * Z.of_nat (S K) * mu - Z.of_nat (S K) * mu) a a' _ _ _ ltac:(nia)
             La La' Lb Lb' (incl_mid _ _ _) (incl_head _ _ _) Rb).
  Qed.
End Transfer.


(* ============================================================================================ *)
(* The representative domain and the compression.                                               *)
(* ============================================================================================ *)

(* The integers -R .. R. *)
Definition zr (R : Z) : list Z := map (fun i => Z.of_nat i - R)%Z (seq 0 (Z.to_nat (2 * R + 1))).

Lemma zr_spec : forall R d, (0 <= R)%Z -> (In d (zr R) <-> (- R <= d <= R)%Z).
Proof.
  intros R d HR. unfold zr. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply in_seq in Hi. destruct Hi as [_ Hi].
    assert (Z.of_nat i < 2 * R + 1)%Z by (rewrite <- (Z2Nat.id (2 * R + 1)) by lia; apply Nat2Z.inj_lt; lia).
    lia.
  - intros Hd. exists (Z.to_nat (d + R)). split; [rewrite Z2Nat.id by lia; lia|].
    apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.

(* The values within R of an anchor. *)
Definition dom (A : list Z) (R : Z) : list Z :=
  nodup Z.eq_dec (flat_map (fun a => map (fun d => a + d)%Z (zr R)) A).

Lemma dom_spec : forall A R v, (0 <= R)%Z ->
  (In v (dom A R) <-> exists a, In a A /\ (Z.abs (v - a) <= R)%Z).
Proof.
  intros A R v HR. unfold dom. rewrite nodup_In, in_flat_map. split.
  - intros [a [Ha Hv]]. apply in_map_iff in Hv. destruct Hv as [d [<- Hd]]. apply zr_spec in Hd; [|exact HR].
    exists a. split; [exact Ha | lia].
  - intros [a [Ha Hv]]. exists a. split; [exact Ha|]. apply in_map_iff. exists (v - a)%Z.
    split; [lia | apply zr_spec; lia].
Qed.

Lemma dom_length : forall A R, (0 <= R)%Z -> (length (dom A R) <= length A * Z.to_nat (2 * R + 1))%nat.
Proof.
  intros A R HR. unfold dom. eapply Nat.le_trans; [apply NoDup_incl_length; [apply NoDup_nodup|]|].
  - instantiate (1 := flat_map (fun a => map (fun d => a + d)%Z (zr R)) A). intros x Hx. apply nodup_In in Hx. exact Hx.
  - assert (Z0 : length (zr R) = Z.to_nat (2 * R + 1)) by (unfold zr; rewrite lenM, lenS; reflexivity).
    induction A as [|a A IH]; cbn [flat_map length]; [lia|]. rewrite lenA, lenM, Z0.
    rewrite Nat.mul_succ_l. lia.
Qed.

(* Per-variable domains: the values of dom within the variable's range. *)
Fixpoint domsF (A : list Z) (R : Z) (los his : list Z) : list (list Z) :=
  match los, his with
  | lo :: los', hi :: his' =>
      filter (fun v => Z.leb lo v && Z.leb v hi) (dom A R) :: domsF A R los' his'
  | _, _ => []
  end.

Fixpoint tupL (Ds : list (list Z)) : list (list Z) :=
  match Ds with
  | [] => [[]]
  | D :: Ds' => flat_map (fun x => map (cons x) (tupL Ds')) D
  end.

Lemma tupL_doms : forall A R los his s, length los = length his ->
  (In s (tupL (domsF A R los his)) <->
   length s = length los /\ forall i, (i < length los)%nat ->
     (nth i los 0 <= nth i s 0 <= nth i his 0)%Z /\ In (nth i s 0%Z) (dom A R)).
Proof.
  intros A R. induction los as [|lo los IH]; intros [|hi his] s Hl; simpl in Hl; try discriminate; simpl.
  - split.
    + intros [<- | []]. split; [reflexivity | intros i Hi; lia].
    + intros [Hs _]. destruct s; [left; reflexivity | discriminate].
  - rewrite in_flat_map. split.
    + intros [x [Hx Hs]]. apply in_map_iff in Hs. destruct Hs as [t [<- Ht]].
      apply (IH his t ltac:(lia)) in Ht. destruct Ht as [Ht1 Ht2].
      apply filter_In in Hx. destruct Hx as [Hx Hb]. apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1, B2. split; [simpl; lia|].
      intros [|i] Hi; simpl; [split; [lia | exact Hx]|]. apply Ht2. lia.
    + intros [Hs Hi]. destruct s as [|x t]; [discriminate|]. exists x. split.
      * destruct (Hi 0%nat ltac:(lia)) as [B Hx]. simpl in B, Hx. apply filter_In.
        split; [exact Hx|]. apply andb_true_iff. split; apply Z.leb_le; lia.
      * apply in_map. apply (IH his t ltac:(lia)). split; [simpl in Hs; lia|].
        intros i Hi'. exact (Hi (S i) ltac:(lia)).
Qed.

(* The radius n (W + 1), and the representative states: in range, each variable within the radius
   of an anchor. *)
Definition radius (P : dprog) (W : Z) : Z := (Z.of_nat (nv P) * (W + 1))%Z.

Definition RepS (P : dprog) (A : list Z) (W : Z) : list (list Z) :=
  tupL (domsF A (radius P W) (dlo P) (dhi P)).

Lemma bnd_ok_parts : forall P A, bnd_ok P A = true -> length (dhi P) = nv P /\ forall i, (i < nv P)%nat ->
  (nth i (dlo P) 0 <= nth i (dhi P) 0)%Z /\ In (nth i (dlo P) 0%Z) A /\ In (nth i (dhi P) 0%Z) A.
Proof.
  intros P A H. unfold bnd_ok in H. apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. rewrite forallb_forall in H2. split; [unfold nv; lia|].
  intros i Hi. assert (Hs : In i (seq 0 (nv P))) by (apply in_seq; lia).
  specialize (H2 i Hs). apply andb_true_iff in H2 as [H2 Hh]. apply andb_true_iff in H2 as [Hle Hl].
  apply Z.leb_le in Hle. apply inZ_spec in Hl, Hh. split; [exact Hle | split; assumption].
Qed.

Theorem RepS_spec : forall P A W s, bnd_ok P A = true -> (0 <= W)%Z ->
  (In s (RepS P A W) <-> InBox P s /\
     forall i, (i < nv P)%nat -> exists a, In a A /\ (Z.abs (nth i s 0 - a) <= radius P W)%Z).
Proof.
  intros P A W s Hb HW. destruct (bnd_ok_parts P A Hb) as [Lh _].
  assert (HR : (0 <= radius P W)%Z) by (unfold radius; nia).
  unfold RepS. rewrite (tupL_doms A (radius P W) (dlo P) (dhi P) s ltac:(unfold nv in Lh; lia)).
  unfold InBox, nv. split.
  - intros [Hs Hi]. split; [split; [exact Hs|]|]; intros i Hi'; destruct (Hi i Hi') as [B D];
      [exact B | apply dom_spec in D; [exact D | exact HR]].
  - intros [[Hs Hb'] Hi]. split; [exact Hs|]. intros i Hi'. split; [exact (Hb' i Hi')|].
    apply dom_spec; [exact HR | exact (Hi i Hi')].
Qed.

(* The number of representative states: the product of the per-variable domain sizes. *)
Lemma RepS_length : forall P A W,
  length (RepS P A W) = fold_right Nat.mul 1%nat (map (@length Z) (domsF A (radius P W) (dlo P) (dhi P))).
Proof.
  intros P A W. unfold RepS. generalize (domsF A (radius P W) (dlo P) (dhi P)) as Ds.
  induction Ds as [|D Ds IH]; simpl; [reflexivity|]. rewrite <- IH.
  induction D as [|x D IHD]; simpl; [reflexivity|]. rewrite lenA, lenM, IHD. reflexivity.
Qed.

(* ---- RelS is an equivalence (for W >= 0). ---- *)

Lemma in_combine_diag : forall (s : list Z) x, In x (combine s s) -> snd x = fst x.
Proof.
  induction s as [|v s IH]; intros x Hx; simpl in Hx; [contradiction|].
  destruct Hx as [<- | Hx]; [reflexivity | exact (IH x Hx)].
Qed.

Theorem RelS_refl : forall W A s, RelS W A s s.
Proof.
  intros W A s. split; [reflexivity|]. intros x y Hx Hy.
  assert (D : forall z, In z (combine s s ++ anc A) -> snd z = fst z).
  { intros z Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz];
      [exact (in_combine_diag s z Hz) | exact (proj2 (in_anc_inv A z Hz))]. }
  rewrite (D x Hx), (D y Hy). apply near_refl.
Qed.

Lemma in_combine3 : forall (s s' s'' : list Z) x z, length s = length s' -> length s' = length s'' ->
  In (x, z) (combine s s'') -> exists y, In (x, y) (combine s s') /\ In (y, z) (combine s' s'').
Proof.
  induction s as [|a s IH]; intros [|b s'] [|c s''] x z H1 H2 Hin; simpl in *; try contradiction; try lia.
  destruct Hin as [E | Hin].
  - injection E as <- <-. exists b. split; left; reflexivity.
  - destruct (IH s' s'' x z ltac:(lia) ltac:(lia) Hin) as [y [Hy1 Hy2]]. exists y. split; right; assumption.
Qed.

Theorem RelS_trans : forall W A s s' s'', (0 <= W)%Z -> RelS W A s s' -> RelS W A s' s'' -> RelS W A s s''.
Proof.
  intros W A s s' s'' HW [L1 R1] [L2 R2]. split; [lia|].
  assert (M : forall x, In x (combine s s'' ++ anc A) -> exists y,
             In (fst x, y) (combine s s' ++ anc A) /\ In (y, snd x) (combine s' s'' ++ anc A)).
  { intros [x z] Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    - destruct (in_combine3 s s' s'' x z L1 L2 Hx) as [y [Hy1 Hy2]]. exists y.
      split; apply in_or_app; left; assumption.
    - destruct (in_anc_inv A _ Hx) as [Ha E]. simpl in Ha, E. subst z. exists x.
      split; apply in_or_app; right; apply in_anc; exact Ha. }
  intros x y Hx Hy. destruct (M x Hx) as [x' [Hx1 Hx2]]. destruct (M y Hy) as [y' [Hy1 Hy2]].
  pose proof (R1 _ _ Hx1 Hy1) as N1. pose proof (R2 _ _ Hx2 Hy2) as N2. simpl in N1, N2.
  exact (near_trans W _ _ _ HW N1 N2).
Qed.

(* ---- The pigeonhole step. ---- *)

Lemma pigeon : forall (l : list Z) (b w : Z) (k : nat), (0 < w)%Z -> (length l < k)%nat ->
  exists j, (j < k)%nat /\ forall x, In x l -> ~ (b + Z.of_nat j * w <= x < b + Z.of_nat (S j) * w)%Z.
Proof.
  intros l b w k Hw Hk.
  set (H := map (fun x => Z.to_nat ((x - b) / w)) l).
  assert (Idx : forall x j, (b + Z.of_nat j * w <= x < b + Z.of_nat (S j) * w)%Z ->
                  Z.to_nat ((x - b) / w) = j).
  { intros x j Hx. rewrite Nat2Z.inj_succ in Hx.
    rewrite <- (Z.div_unique (x - b) w (Z.of_nat j) (x - b - w * Z.of_nat j)); [apply Nat2Z.id | left; nia | lia]. }
  destruct (existsb (fun j => negb (existsb (Nat.eqb j) H)) (seq 0 k)) eqn:E.
  - apply existsb_exists in E. destruct E as [j [Hj Hn]]. apply in_seq in Hj.
    exists j. split; [lia|]. intros x Hx Hw'. apply negb_true_iff in Hn.
    assert (Hin : In j H) by (unfold H; apply in_map_iff; exists x; split; [apply Idx; exact Hw' | exact Hx]).
    assert (T : existsb (Nat.eqb j) H = true) by (apply existsb_exists; exists j; split; [exact Hin | apply Nat.eqb_refl]).
    congruence.
  - exfalso.
    assert (Inc : incl (seq 0 k) H).
    { intros j Hj. destruct (existsb (Nat.eqb j) H) eqn:F.
      - apply existsb_exists in F. destruct F as [j' [Hj' F]]. apply Nat.eqb_eq in F. subst. exact Hj'.
      - assert (T : existsb (fun j => negb (existsb (Nat.eqb j) H)) (seq 0 k) = true)
          by (apply existsb_exists; exists j; split; [exact Hj | rewrite F; reflexivity]).
        congruence. }
    pose proof (NoDup_incl_length (seq_NoDup k 0) Inc) as L. unfold H in L. rewrite lenM, lenS in L. lia.
Qed.

Definition zsum (l : list Z) : Z := fold_right Z.add 0%Z l.

Lemma zsum_lt : forall (g : Z -> Z) l x, (forall v, In v l -> (g v <= v)%Z) -> In x l -> (g x < x)%Z ->
  (zsum (map g l) < zsum l)%Z.
Proof.
  intros g l. induction l as [|v l IH]; intros x Hle Hx Hg; simpl in *; [contradiction|].
  assert (Hle' : forall u, In u l -> (g u <= u)%Z) by (intros u Hu; apply Hle; right; exact Hu).
  destruct Hx as [<- | Hx].
  - assert (zsum (map g l) <= zsum l)%Z.
    { clear IH. induction l as [|u l IHl]; simpl; [lia|].
      pose proof (Hle' u (or_introl eq_refl)). assert (zsum (map g l) <= zsum l)%Z
        by (apply IHl; [intros w Hw; apply Hle; destruct Hw as [<- | Hw]; [left; reflexivity | right; right; exact Hw]
                       | intros w Hw; apply Hle'; right; exact Hw]). lia. }
    unfold zsum in *. lia.
  - pose proof (IH x Hle' Hx Hg). pose proof (Hle v (or_introl eq_refl)). unfold zsum in *. lia.
Qed.

Lemma zsum_ge : forall l m, length l = length m -> (forall i, (i < length l)%nat -> (nth i m 0 <= nth i l 0)%Z) ->
  (zsum m <= zsum l)%Z.
Proof.
  induction l as [|x l IH]; intros [|y m] Hl H; simpl in *; try lia.
  pose proof (H 0%nat ltac:(lia)) as H0. simpl in H0.
  assert (zsum m <= zsum l)%Z by (apply IH; [lia | intros i Hi; exact (H (S i) ltac:(lia))]). unfold zsum in *. lia.
Qed.

Lemma combine_map : forall (g : Z -> Z) s, combine s (map g s) = map (fun v => (v, g v)) s.
Proof. intros g s. induction s as [|v s IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* One shift: a block of values with no anchor, with W + 1 free integers below and above it, moves
   down by 1. The relation holds between the state and the shifted one. *)
Lemma shift_step : forall P A W s i, bnd_ok P A = true -> (0 <= W)%Z -> InBox P s -> (i < nv P)%nat ->
  (forall a, In a A -> (radius P W < Z.abs (nth i s 0 - a))%Z) ->
  exists s', InBox P s' /\ RelS W A s s' /\ (zsum s' < zsum s)%Z.
Proof.
  intros P A W s i Hb HW [Hs Hbox] Hi Hfar. destruct (bnd_ok_parts P A Hb) as [Lh Hbd].
  set (n := nv P) in *. set (v := nth i s 0%Z). set (R := radius P W).
  assert (Rn : R = (Z.of_nat n * (W + 1))%Z) by reflexivity.
  assert (Hv : In v s) by (unfold v; apply nth_In; lia).
  assert (Lb : (length (filter (fun x => Z.ltb x v) s) < n)%nat).
  { rewrite <- Hs. pose proof (filter_lt (fun x => Z.ltb x v) (fun _ => true) s v (fun _ _ _ => eq_refl)
                                 Hv eq_refl (Z.ltb_irrefl v)) as H. rewrite filter_all in H. exact H. }
  assert (La : (length (filter (fun x => Z.ltb v x) s) < n)%nat).
  { rewrite <- Hs. pose proof (filter_lt (fun x => Z.ltb v x) (fun _ => true) s v (fun _ _ _ => eq_refl)
                                 Hv eq_refl (Z.ltb_irrefl v)) as H. rewrite filter_all in H. exact H. }
  (* A free window below v, and one above. *)
  destruct (pigeon (filter (fun x => Z.ltb x v) s) (v - R) (W + 1) n ltac:(lia) Lb) as [j [Hj Hwj]].
  destruct (pigeon (filter (fun x => Z.ltb v x) s) (v + 1) (W + 1) n ltac:(lia) La) as [j' [Hj' Hwj']].
  set (p := (v - R + Z.of_nat (S j) * (W + 1))%Z).
  set (q := (v + 1 + Z.of_nat j' * (W + 1))%Z).
  assert (Hp : (v - R + W + 1 <= p <= v)%Z) by (unfold p; rewrite Nat2Z.inj_succ; nia).
  assert (Hq : (v + 1 <= q <= v + R - W)%Z) by (unfold q; nia).
  (* Values of the state: below p means at most p - W - 2; at or above q means at least q + W + 1. *)
  assert (Below : forall x, In x s -> (x < p)%Z -> (x <= p - W - 2)%Z).
  { intros x Hx Hxp. destruct (Z.le_gt_cases x (p - W - 2)) as [H | H]; [exact H | exfalso].
    apply (Hwj x); [apply filter_In; split; [exact Hx | apply Z.ltb_lt; lia]|].
    unfold p in *. rewrite Nat2Z.inj_succ in *. nia. }
  assert (Above : forall x, In x s -> (q <= x)%Z -> (q + W + 1 <= x)%Z).
  { intros x Hx Hxq. destruct (Z.le_gt_cases (q + W + 1) x) as [H | H]; [exact H | exfalso].
    apply (Hwj' x); [apply filter_In; split; [exact Hx | apply Z.ltb_lt; lia]|].
    unfold q in *. rewrite Nat2Z.inj_succ. nia. }
  (* Anchors are outside [p - W - 1, q + W]. *)
  assert (Anc : forall a, In a A -> (a <= p - W - 2 \/ q + W + 1 <= a)%Z).
  { intros a Ha. pose proof (Hfar a Ha). destruct (Z.le_gt_cases a v); [left | right]; lia. }
  set (g := fun x => if Z.leb p x && Z.ltb x q then (x - 1)%Z else x).
  assert (Gin : forall x, (p <= x < q)%Z -> g x = (x - 1)%Z).
  { intros x Hx. unfold g. replace (Z.leb p x && Z.ltb x q) with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  assert (Gout : forall x, ~ (p <= x < q)%Z -> g x = x).
  { intros x Hx. unfold g. destruct (Z.leb_spec p x); destruct (Z.ltb_spec x q); simpl; try reflexivity. lia. }
  assert (Gle : forall x, (g x <= x)%Z).
  { intros x. destruct (Z.le_gt_cases p x); destruct (Z.le_gt_cases q x);
      [rewrite Gout by lia | rewrite Gin by lia | rewrite Gout by lia | rewrite Gout by lia]; lia. }
  assert (GA : forall a, In a A -> g a = a) by (intros a Ha; apply Gout; pose proof (Anc a Ha); lia).
  (* Every value of s ++ A in the block, or W + 1 away from it. *)
  assert (Sep : forall x, In x (s ++ A) -> (p <= x < q)%Z \/ (x <= p - W - 2)%Z \/ (q + W + 1 <= x)%Z).
  { intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
    - destruct (Z.lt_ge_cases x p) as [H | H]; [right; left; apply Below; assumption|].
      destruct (Z.lt_ge_cases x q) as [H' | H']; [left; lia | right; right; apply Above; assumption].
    - right. apply Anc. exact Hx. }
  exists (map g s). split; [|split].
  - split; [rewrite lenM; exact Hs|]. intros k Hk.
    rewrite (nth_indep (map g s) 0%Z (g 0%Z)) by (rewrite lenM; lia). rewrite map_nth.
    destruct (Hbox k Hk) as [Hl Hh]. destruct (Hbd k Hk) as [_ [HlA _]]. split; [|pose proof (Gle (nth k s 0%Z)); lia].
    destruct (Z.le_gt_cases p (nth k s 0%Z)) as [H1 | H1]; [destruct (Z.lt_ge_cases (nth k s 0%Z) q) as [H2 | H2]|].
    + rewrite Gin by lia. pose proof (Anc _ HlA). lia.
    + rewrite Gout by lia. exact Hl.
    + rewrite Gout by lia. exact Hl.
  - split; [rewrite lenM; reflexivity|].
    assert (E : combine s (map g s) ++ anc A = map (fun x => (x, g x)) (s ++ A)).
    { rewrite combine_map, map_app. f_equal. unfold anc. apply map_ext_in. intros a Ha. rewrite (GA a Ha). reflexivity. }
    rewrite E. intros x y Hx Hy. apply in_map_iff in Hx, Hy.
    destruct Hx as [x0 [<- Hx]]. destruct Hy as [y0 [<- Hy]]. simpl.
    destruct (Sep x0 Hx) as [X | [X | X]]; destruct (Sep y0 Hy) as [Y | [Y | Y]];
      repeat first [rewrite (Gin x0) by lia | rewrite (Gout x0) by lia | rewrite (Gin y0) by lia | rewrite (Gout y0) by lia];
      unfold near; lia.
  - apply (zsum_lt g s v); [intros x _; apply Gle | exact Hv | rewrite Gin by lia; lia].
Qed.

Lemma forallb_false_ex : forall {X : Type} (f : X -> bool) l, forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros X f l. induction l as [|x l IH]; intros H; simpl in H; [discriminate|].
  destruct (f x) eqn:E; simpl in H.
  - destruct (IH H) as [y [Hy Hf]]. exists y. split; [right; exact Hy | exact Hf].
  - exists x. split; [left; reflexivity | exact E].
Qed.

(* Compression: every state in range is related to a representative state. *)
Theorem compress_d : forall P A W s, bnd_ok P A = true -> (0 <= W)%Z -> InBox P s ->
  exists s', In s' (RepS P A W) /\ RelS W A s s'.
Proof.
  intros P A W s Hb HW Hs. destruct (bnd_ok_parts P A Hb) as [Lh Hbd].
  remember (Z.to_nat (zsum s - zsum (dlo P))) as m eqn:Em. revert s Hs Em.
  induction m as [m IH] using (well_founded_induction lt_wf). intros s Hs Em.
  destruct (forallb (fun i => existsb (fun a => Z.leb (Z.abs (nth i s 0%Z - a)) (radius P W)) A) (seq 0 (nv P))) eqn:E.
  - exists s. split; [|apply RelS_refl]. apply RepS_spec; [exact Hb | exact HW|]. split; [exact Hs|].
    intros i Hi. rewrite forallb_forall in E. specialize (E i ltac:(apply in_seq; lia)).
    apply existsb_exists in E. destruct E as [a [Ha E]]. apply Z.leb_le in E. exists a. split; assumption.
  - assert (Far : exists i, (i < nv P)%nat /\ forall a, In a A -> (radius P W < Z.abs (nth i s 0%Z - a))%Z).
    { apply forallb_false_ex in E. destruct E as [i [Hi E]]. apply in_seq in Hi. exists i. split; [lia|].
      intros a Ha. destruct (Z.leb_spec (Z.abs (nth i s 0%Z - a)) (radius P W)) as [H | H]; [|exact H].
      exfalso. assert (T : existsb (fun a => Z.leb (Z.abs (nth i s 0%Z - a)) (radius P W)) A = true)
        by (apply existsb_exists; exists a; split; [exact Ha | apply Z.leb_le; exact H]). congruence. }
    destruct Far as [i [Hi Hfar]].
    destruct (shift_step P A W s i Hb HW Hs Hi Hfar) as [s1 [Hs1 [R1 Lt]]].
    assert (G1 : (zsum (dlo P) <= zsum s1)%Z).
    { destruct Hs1 as [L1 B1]. apply zsum_ge; [unfold nv in L1; lia|]. intros k Hk. apply B1. lia. }
    destruct (IH (Z.to_nat (zsum s1 - zsum (dlo P))) ltac:(lia) s1 Hs1 eq_refl) as [s2 [H2 R2]].
    exists s2. split; [exact H2 | exact (RelS_trans W A s s1 s2 HW R1 R2)].
Qed.


(* ============================================================================================ *)
(* Saturation keeps every state in range.                                                       *)
(* ============================================================================================ *)

Lemma clamp_in : forall lo hi v, (lo <= hi)%Z -> (lo <= clampZ lo hi v <= hi)%Z.
Proof.
  intros lo hi v H. unfold clampZ. destruct (Z.ltb_spec v lo); [lia|]. destruct (Z.ltb_spec hi v); lia.
Qed.

Section Box.
  Variable P : dprog.
  Variable A : list Z.
  Hypothesis HB : bnd_ok P A = true.

  Lemma write_box : forall s a, InBox P s -> InBox P (write P s a).
  Proof.
    intros s [k e] [Hs Hb]. destruct (bnd_ok_parts P A HB) as [_ Hbd]. unfold write; simpl.
    split; [rewrite upd_len; exact Hs|]. intros i Hi.
    destruct (Nat.eq_dec i k) as [-> | Hne].
    - rewrite upd_nth_eq by lia. apply clamp_in. apply (Hbd k Hi).
    - rewrite upd_nth_neq by exact Hne. apply Hb. exact Hi.
  Qed.

  Lemma applyT_box : forall t s, InBox P s -> InBox P (applyT P t s).
  Proof.
    induction t as [|a t IH]; intros s Hs; [exact Hs|]. unfold applyT; simpl. apply IH. apply write_box. exact Hs.
  Qed.

  Lemma drepair_box : forall s, InBox P s -> InBox P (drepair P s).
  Proof.
    intros s Hs. unfold drepair. destruct (find _ (dinv P)) as [iv|]; [apply applyT_box|]; exact Hs.
  Qed.

  Lemma itr_box : forall j s, InBox P s -> InBox P (itr j (drepair P) s).
  Proof. induction j as [|j IH]; intros s Hs; [exact Hs|]. cbn [itr]. apply IH, drepair_box, Hs. Qed.

  Lemma dap_box : forall k s, InBox P s -> InBox P (dap P k s).
  Proof.
    intros k s Hs. unfold dap. destruct (nth_error (dev P) k) as [ev|]; [|exact Hs].
    unfold evt. destruct (evalP s (fst ev)); [apply applyT_box|]; exact Hs.
  Qed.

  Lemma dgov_box : forall K k s, InBox P s -> InBox P (dgov P K k s).
  Proof. intros K k s Hs. unfold dgov. apply itr_box, dap_box, Hs. Qed.

  Lemma drun_box : forall K k s, InBox P s -> InBox P (drun P K k s).
  Proof. intros K k s Hs. unfold drun. apply dgov_box, itr_box, Hs. Qed.
End Box.

Lemma drepair_fix : forall P s, dvalid P s = true -> drepair P s = s.
Proof.
  intros P s H. unfold drepair, dvalid in *.
  replace (find (fun iv => negb (evalP s (fst iv))) (dinv P)) with (@None (dpred * transform)); [reflexivity|].
  induction (dinv P) as [|iv l IH]; simpl in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. rewrite H1. simpl. apply IH. exact H2.
Qed.

Lemma itr_valid_fix : forall P j s, dvalid P s = true -> itr j (drepair P) s = s.
Proof. intros P j s H. apply itr_fix. apply drepair_fix. exact H. Qed.

(* ============================================================================================ *)
(* The conditions gsm checks, over the declared ranges and over the representatives.             *)
(* ============================================================================================ *)

Definition nke (P : dprog) : nat := length (dev P).

(* Repair reaches a valid state within K steps. *)
Definition DTermBox (P : dprog) (K : nat) : Prop :=
  forall s, InBox P s -> dvalid P (itr K (drepair P) s) = true.
Definition DTermRep (P : dprog) (A : list Z) (W : Z) (K : nat) : Prop :=
  forall s, In s (RepS P A W) -> dvalid P (itr K (drepair P) s) = true.

(* CC1 for the pairs of I at every valid state (gsm's CC1). *)
Definition DCC1VBox (P : dprog) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, InBox P s -> dvalid P s = true -> forall k1 k2, (k1 < nke P)%nat -> (k2 < nke P)%nat -> I k1 k2 ->
    dgov P K k2 (dgov P K k1 s) = dgov P K k1 (dgov P K k2 s).
Definition DCC1VRep (P : dprog) (A : list Z) (W : Z) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, In s (RepS P A W) -> dvalid P s = true -> forall k1 k2, (k1 < nke P)%nat -> (k2 < nke P)%nat ->
    I k1 k2 -> dgov P K k2 (dgov P K k1 s) = dgov P K k1 (dgov P K k2 s).

(* CC1 at every state. *)
Definition DCC1Box (P : dprog) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, InBox P s -> forall k1 k2, (k1 < nke P)%nat -> (k2 < nke P)%nat -> I k1 k2 ->
    dgov P K k2 (dgov P K k1 s) = dgov P K k1 (dgov P K k2 s).
Definition DCC1Rep (P : dprog) (A : list Z) (W : Z) (K : nat) (I : nat -> nat -> Prop) : Prop :=
  forall s, In s (RepS P A W) -> forall k1 k2, (k1 < nke P)%nat -> (k2 < nke P)%nat -> I k1 k2 ->
    dgov P K k2 (dgov P K k1 s) = dgov P K k1 (dgov P K k2 s).

(* Idempotence of kind k at every valid state. *)
Definition DIdemVBox (P : dprog) (K k : nat) : Prop :=
  forall s, InBox P s -> dvalid P s = true -> dgov P K k (dgov P K k s) = dgov P K k s.
Definition DIdemVRep (P : dprog) (A : list Z) (W : Z) (K k : nat) : Prop :=
  forall s, In s (RepS P A W) -> dvalid P s = true -> dgov P K k (dgov P K k s) = dgov P K k s.

(* The thresholds. *)
Definition wterm (gam mu : Z) (K : nat) : Z := (gam + Z.of_nat K * mu)%Z.
Definition widem (gam mu : Z) (K : nat) : Z := (gam + 3 * Z.of_nat (S K) * mu)%Z.
Definition wcc1 (gam mu : Z) (K : nat) : Z := (gam + 4 * Z.of_nat (S K) * mu)%Z.

Section Cutoff.
  Variable P : dprog.
  Variable A : list Z.
  Variable gam mu : Z.
  Hypothesis HF : dfrag P A gam mu = true.

  Lemma HB : bnd_ok P A = true.
  Proof. exact (proj1 (frag_parts P A gam mu HF)). Qed.

  Lemma rep_box : forall W s, (0 <= W)%Z -> In s (RepS P A W) -> InBox P s.
  Proof. intros W s HW H. apply (RepS_spec P A W s HB HW) in H. apply H. Qed.

  Lemma box_len : forall s, InBox P s -> length s = nv P.
  Proof. intros s [H _]. exact H. Qed.

  (* Repair within K steps: threshold gam + K mu. *)
  Theorem dterm_abs : forall K W, (wterm gam mu K <= W)%Z -> (DTermBox P K <-> DTermRep P A W K).
  Proof.
    intros K W Hw. unfold wterm in Hw. pose proof (gam_nonneg P A gam mu HF) as G0. pose proof (mu_nonneg P A gam mu HF) as M0.
    split.
    - intros H s Hs. apply H. apply (rep_box W); [nia | exact Hs].
    - intros H s Hs. destruct (compress_d P A W s HB ltac:(nia) Hs) as [s' [Hr R]].
      rewrite (term_pair P A gam mu HF K W s s' R (box_len s Hs) Hw). apply H. exact Hr.
  Qed.

  (* CC1 for I at every valid state: threshold gam + 4 (K + 1) mu. *)
  Theorem dcc1v_abs : forall K W I, (wcc1 gam mu K <= W)%Z -> (DCC1VBox P K I <-> DCC1VRep P A W K I).
  Proof.
    intros K W I Hw. unfold wcc1 in Hw. pose proof (gam_nonneg P A gam mu HF) as G0. pose proof (mu_nonneg P A gam mu HF) as M0.
    split.
    - intros H s Hs. apply H. apply (rep_box W); [nia | exact Hs].
    - intros H s Hs Hv k1 k2 H1 H2 HI. destruct (compress_d P A W s HB ltac:(nia) Hs) as [s' [Hr R]].
      apply (cc1_pair P A gam mu HF K k1 k2 W s s' R (box_len s Hs) Hw). apply H; try assumption.
      rewrite <- (valid_pair P A gam mu HF W s s' R (box_len s Hs) ltac:(nia)). exact Hv.
  Qed.

  (* CC1 for I at every state: threshold gam + 4 (K + 1) mu. *)
  Theorem dcc1_abs : forall K W I, (wcc1 gam mu K <= W)%Z -> (DCC1Box P K I <-> DCC1Rep P A W K I).
  Proof.
    intros K W I Hw. unfold wcc1 in Hw. pose proof (gam_nonneg P A gam mu HF) as G0. pose proof (mu_nonneg P A gam mu HF) as M0.
    split.
    - intros H s Hs. apply H. apply (rep_box W); [nia | exact Hs].
    - intros H s Hs k1 k2 H1 H2 HI. destruct (compress_d P A W s HB ltac:(nia) Hs) as [s' [Hr R]].
      apply (cc1_pair P A gam mu HF K k1 k2 W s s' R (box_len s Hs) Hw). apply H; assumption.
  Qed.

  (* Idempotence at every valid state: threshold gam + 3 (K + 1) mu. *)
  Theorem didemv_abs : forall K k W, (widem gam mu K <= W)%Z -> (DIdemVBox P K k <-> DIdemVRep P A W K k).
  Proof.
    intros K k W Hw. unfold widem in Hw. pose proof (gam_nonneg P A gam mu HF) as G0. pose proof (mu_nonneg P A gam mu HF) as M0.
    split.
    - intros H s Hs. apply H. apply (rep_box W); [nia | exact Hs].
    - intros H s Hs Hv. destruct (compress_d P A W s HB ltac:(nia) Hs) as [s' [Hr R]].
      apply (idem_pair P A gam mu HF K k W s s' R (box_len s Hs) Hw). apply H; [exact Hr|].
      rewrite <- (valid_pair P A gam mu HF W s s' R (box_len s Hs) ltac:(nia)). exact Hv.
  Qed.

  (* ---- gsm's guarantee. ---- *)

  (* From every valid state in range, trace-equivalent sequences of events reach the same state. *)
  Definition DRunConv (K : nat) (I : nat -> nat -> Prop) : Prop :=
    forall s, InBox P s -> dvalid P s = true -> forall es1 es2, tequiv I es1 es2 ->
      Forall (fun k => (k < nke P)%nat) es1 -> runT (dgov P K) es1 s = runT (dgov P K) es2 s.

  Lemma term_rep_box : forall K W, (wcc1 gam mu K <= W)%Z -> DTermRep P A W K -> DTermBox P K.
  Proof.
    intros K W Hw H. pose proof (mu_nonneg P A gam mu HF). apply (proj2 (dterm_abs K W ltac:(unfold wterm, wcc1 in *; nia))).
    exact H.
  Qed.

  (* Given repair within K steps over the representatives, CC1 for I at the valid representative
     states holds iff every two trace-equivalent runs from every valid state in range agree. *)
  Theorem dgsm_exact : forall K W I, (wcc1 gam mu K <= W)%Z -> DTermRep P A W K ->
    (DCC1VRep P A W K I <-> DRunConv K I).
  Proof.
    intros K W I Hw HD. pose proof (term_rep_box K W Hw HD) as HT.
    rewrite <- (dcc1v_abs K W I Hw). split.
    - intros H s Hs Hv es1 es2 Hte Hev.
      apply (run_tequiv (dgov P K) I (fun k => (k < nke P)%nat) (fun t => InBox P t /\ dvalid P t = true)
                        (fun t => InBox P t /\ dvalid P t = true)); try assumption.
      + intros t Ht. exact Ht.
      + intros e t _ [Ht _]. split; [apply (dgov_box P A HB), Ht | apply HT, (dap_box P A HB), Ht].
      + intros a b t Ha Hb HI [Ht Hv']. symmetry. exact (H t Ht Hv' a b Ha Hb HI).
      + split; assumption.
    - intros H s Hs Hv k1 k2 H1 H2 HI.
      pose proof (H s Hs Hv [k1; k2] [k2; k1] (teq_swap I [] k1 k2 [] HI)) as E.
      apply E. constructor; [exact H1|]. constructor; [exact H2|]. constructor.
  Qed.

  (* gsm's runtime (normalize, then the governed step): from EVERY state in range, trace-equivalent
     sequences reach the same state, given the two representative checks. *)
  Theorem dgsm_sound : forall K W I, (wcc1 gam mu K <= W)%Z -> DTermRep P A W K -> DCC1VRep P A W K I ->
    forall s, InBox P s -> forall es1 es2, tequiv I es1 es2 -> Forall (fun k => (k < nke P)%nat) es1 ->
      runT (drun P K) es1 s = runT (drun P K) es2 s.
  Proof.
    intros K W I Hw HD HC s Hs es1 es2 Hte Hev.
    pose proof (term_rep_box K W Hw HD) as HT. pose proof (proj2 (dcc1v_abs K W I Hw) HC) as HZ.
    apply (run_tequiv (drun P K) I (fun k => (k < nke P)%nat) (InBox P) (InBox P)); try assumption.
    - intros t Ht. exact Ht.
    - intros e t _ Ht. apply (drun_box P A HB). exact Ht.
    - intros a b t Ha Hb HI Ht. unfold drun.
      set (u := itr K (drepair P) t).
      assert (Hu : InBox P u) by (apply (itr_box P A HB), Ht).
      assert (Vu : dvalid P u = true) by (apply HT, Ht).
      assert (V1 : forall k, dvalid P (dgov P K k u) = true) by (intros k; apply HT, (dap_box P A HB), Hu).
      rewrite (itr_valid_fix P K _ (V1 b)), (itr_valid_fix P K _ (V1 a)).
      symmetry. exact (HZ u Hu Vu a b Ha Hb HI).
  Qed.

  (* Every pair checked: any permutation. *)
  Theorem dgsm_sound_all : forall K W, (wcc1 gam mu K <= W)%Z -> DTermRep P A W K ->
    DCC1VRep P A W K (fun _ _ => True) ->
    forall s, InBox P s -> forall es1 es2, Permutation es1 es2 -> Forall (fun k => (k < nke P)%nat) es1 ->
      runT (drun P K) es1 s = runT (drun P K) es2 s.
  Proof.
    intros K W Hw HD HC s Hs es1 es2 Hp Hev.
    apply (dgsm_sound K W (fun _ _ => True) Hw HD HC s Hs); [|exact Hev].
    apply (perm_tequiv_total (fun _ _ => True) (fun k => (k < nke P)%nat)); [| exact Hp | exact Hev].
    intros a b _ _. exact I.
  Qed.
End Cutoff.

(* ============================================================================================ *)
(* The finite checks.                                                                           *)
(* ============================================================================================ *)

Lemma implb_t : forall a b, implb a b = true <-> (a = true -> b = true).
Proof. intros [|] [|]; simpl; split; intros H; try reflexivity; try discriminate; auto. Qed.

Definition dterm_check (P : dprog) (A : list Z) (W : Z) (K : nat) : bool :=
  forallb (fun s => dvalid P (itr K (drepair P) s)) (RepS P A W).

Definition dcc1v_check (P : dprog) (A : list Z) (W : Z) (K : nat) (Ib : nat -> nat -> bool) : bool :=
  forallb (fun s => implb (dvalid P s)
    (forallb (fun k1 => forallb (fun k2 => implb (Ib k1 k2)
       (leq (dgov P K k2 (dgov P K k1 s)) (dgov P K k1 (dgov P K k2 s))))
       (seq 0 (nke P))) (seq 0 (nke P))))
    (RepS P A W).

Definition didemv_check (P : dprog) (A : list Z) (W : Z) (K k : nat) : bool :=
  forallb (fun s => implb (dvalid P s) (leq (dgov P K k (dgov P K k s)) (dgov P K k s))) (RepS P A W).

Theorem dterm_check_spec : forall P A W K, dterm_check P A W K = true <-> DTermRep P A W K.
Proof. intros P A W K. unfold dterm_check, DTermRep. rewrite forallb_forall. reflexivity. Qed.

Theorem dcc1v_check_spec : forall P A W K Ib,
  dcc1v_check P A W K Ib = true <-> DCC1VRep P A W K (fun a b => Ib a b = true).
Proof.
  intros P A W K Ib. unfold dcc1v_check, DCC1VRep. rewrite forallb_forall. split.
  - intros H s Hs Hv k1 k2 H1 H2 HI. specialize (H s Hs). rewrite implb_t in H. specialize (H Hv).
    rewrite forallb_forall in H. specialize (H k1 ltac:(apply in_seq; lia)).
    rewrite forallb_forall in H. specialize (H k2 ltac:(apply in_seq; lia)).
    rewrite implb_t in H. apply leq_spec. exact (H HI).
  - intros H s Hs. apply implb_t. intros Hv. apply forallb_forall. intros k1 H1. apply forallb_forall.
    intros k2 H2. apply implb_t. intros HI. apply in_seq in H1. apply in_seq in H2. apply leq_spec.
    apply H; [exact Hs | exact Hv | lia | lia | exact HI].
Qed.

Theorem didemv_check_spec : forall P A W K k, didemv_check P A W K k = true <-> DIdemVRep P A W K k.
Proof.
  intros P A W K k. unfold didemv_check, DIdemVRep. rewrite forallb_forall. split.
  - intros H s Hs Hv. specialize (H s Hs). rewrite implb_t in H. apply leq_spec. exact (H Hv).
  - intros H s Hs. apply implb_t. intros Hv. apply leq_spec. exact (H s Hs Hv).
Qed.

(* Build for the difference fragment, end to end: the fragment check and the two representative
   checks at the threshold wcc1 give gsm's runtime guarantee from every state in range. *)
Theorem dbuild_sound : forall P A gam mu K Ib, dfrag P A gam mu = true ->
  dterm_check P A (wcc1 gam mu K) K = true -> dcc1v_check P A (wcc1 gam mu K) K Ib = true ->
  forall s, InBox P s -> forall es1 es2, tequiv (fun a b => Ib a b = true) es1 es2 ->
    Forall (fun k => (k < nke P)%nat) es1 -> runT (drun P K) es1 s = runT (drun P K) es2 s.
Proof.
  intros P A gam mu K Ib HF HT HC.
  exact (dgsm_sound P A gam mu HF K (wcc1 gam mu K) _ (Z.le_refl _)
           (proj1 (dterm_check_spec P A _ K) HT) (proj1 (dcc1v_check_spec P A _ K Ib) HC)).
Qed.

(* A failure of the check is a real failure: its witness is a state in range. *)
Theorem dcheck_fail_real : forall P A gam mu K Ib, dfrag P A gam mu = true ->
  dcc1v_check P A (wcc1 gam mu K) K Ib = false ->
  ~ DCC1VBox P K (fun a b => Ib a b = true).
Proof.
  intros P A gam mu K Ib HF HC H.
  apply (dcc1v_abs P A gam mu HF K (wcc1 gam mu K) _ (Z.le_refl _)) in H.
  apply dcc1v_check_spec in H. congruence.
Qed.


(* ============================================================================================ *)
(* The comparison fragment as the special case: threshold 0 is the order type.                  *)
(* ============================================================================================ *)

(* With no arithmetic (gam = mu = 0) every threshold is 0, and the relation at threshold 0 is
   exactly AbstractionCutoff's order isomorphisms fixing the anchors. *)
Theorem rel0_oiso : forall A s s', length s = length s' ->
  (RelS 0 A s s' <-> exists f, OIso A s f /\ map f s = s').
Proof.
  intros A s s' Hl. split.
  - intros [_ HR].
    set (f := fun v => match find (fun pr => Z.eqb (fst pr) v) (combine s s') with
                       | Some pr => snd pr | None => v end).
    assert (Mem : forall x, In x (s ++ A) -> In (x, f x) (combine s s' ++ anc A)).
    { intros x Hx. unfold f. destruct (find (fun pr => Z.eqb (fst pr) x) (combine s s')) as [pr|] eqn:E.
      - apply find_some in E. destruct E as [Hp E]. apply Z.eqb_eq in E. destruct pr as [a b]. simpl in E. subst a.
        apply in_or_app. left. exact Hp.
      - apply in_app_or in Hx. destruct Hx as [Hx | Hx].
        + exfalso. apply In_nth with (d := 0%Z) in Hx. destruct Hx as [i [Hi Ei]].
          pose proof (find_none _ _ E _ (in_combine_nth s s' i Hl Hi)) as F. simpl in F.
          rewrite Ei, Z.eqb_refl in F. discriminate.
        + apply in_or_app. right. apply in_anc. exact Hx. }
    assert (Fix : forall c, In c A -> f c = c).
    { intros c Hc. pose proof (HR _ _ (Mem c (in_or_app _ _ _ (or_intror Hc)))
                                     (in_or_app _ _ _ (or_intror (in_anc A c Hc)))) as N.
      simpl in N. destruct N as [N | [N | N]]; lia. }
    exists f. split; [split|].
    + intros x y Hx Hy. pose proof (HR _ _ (Mem x Hx) (Mem y Hy)) as N. simpl in N.
      apply near0_compare in N. rewrite (Z.compare_sub (f x)), (Z.compare_sub x). symmetry. exact N.
    + exact Fix.
    + apply (nth_ext _ _ 0%Z 0%Z); [rewrite lenM; exact Hl|]. intros i Hi. rewrite lenM in Hi.
      rewrite (nth_indep (map f s) 0%Z (f 0%Z)) by (rewrite lenM; exact Hi). rewrite map_nth.
      pose proof (HR _ _ (Mem (nth i s 0%Z) (in_or_app _ _ _ (or_introl (nth_In s 0%Z Hi))))
                       (in_or_app _ _ _ (or_introl (in_combine_nth s s' i Hl Hi)))) as N.
      simpl in N. destruct N as [N | [N | N]]; lia.
  - intros [f [[Hc Hfix] <-]]. split; [rewrite lenM; reflexivity|].
    assert (E : combine s (map f s) ++ anc A = map (fun x => (x, f x)) (s ++ A)).
    { rewrite combine_map, map_app. f_equal. unfold anc. apply map_ext_in. intros a Ha. rewrite (Hfix a Ha). reflexivity. }
    rewrite E. intros x y Hx Hy. apply in_map_iff in Hx, Hy.
    destruct Hx as [x0 [<- Hx]]. destruct Hy as [y0 [<- Hy]]. simpl. apply near0_compare.
    rewrite <- (Z.compare_sub (f x0)), <- (Z.compare_sub x0). symmetry. apply Hc; assumption.
Qed.

(* The representatives of the comparison fragment lie in the domain: reps N C is within N of a
   constant, so threshold 0 with radius n recovers the cutoff n of term_abs and cc1_abs (m = 0),
   made two-sided around every constant. *)
Theorem reps_in_dom : forall N c C, incl (reps N (c :: C)) (dom (c :: C) (Z.of_nat N)).
Proof.
  intros N c C x Hx. apply dom_spec; [lia|]. unfold reps in Hx.
  apply in_app_or in Hx. destruct Hx as [Hx | Hx]; [exists x; split; [exact Hx | lia]|].
  apply in_app_or in Hx. destruct Hx as [Hx | Hx].
  - apply in_flat_map in Hx. destruct Hx as [a [Ha Hx]]. apply in_map_iff in Hx. destruct Hx as [i [<- Hi]].
    apply in_seq in Hi. exists a. split; [exact Ha | lia].
  - apply in_map_iff in Hx. destruct Hx as [i [<- Hi]]. apply in_seq in Hi.
    destruct (mn_spec c C) as [Hm _]. exists (mn (c :: C)). split; [exact Hm | lia].
Qed.

(* A boolean check of the relation, for concrete pairs. *)
Definition nearb (W d d' : Z) : bool :=
  Z.eqb d d' || (Z.ltb W d && Z.ltb W d') || (Z.ltb d (- W) && Z.ltb d' (- W)).

Lemma nearb_spec : forall W d d', nearb W d d' = true <-> near W d d'.
Proof.
  intros W d d'. unfold nearb, near. rewrite !orb_true_iff, !andb_true_iff, Z.eqb_eq, !Z.ltb_lt. tauto.
Qed.

Definition relb (W : Z) (L : list (Z * Z)) : bool :=
  forallb (fun x => forallb (fun y => nearb W (fst x - fst y) (snd x - snd y)) L) L.

Lemma relb_spec : forall W L, relb W L = true <-> Rel W L.
Proof.
  intros W L. unfold relb, Rel. rewrite forallb_forall. split.
  - intros H x y Hx Hy. specialize (H x Hx). rewrite forallb_forall in H. apply nearb_spec. exact (H y Hy).
  - intros H x Hx. apply forallb_forall. intros y Hy. apply nearb_spec. exact (H x y Hx Hy).
Qed.

(* ============================================================================================ *)
(* Non-vacuity.                                                                                 *)
(* ============================================================================================ *)

Definition inboxb (P : dprog) (s : list Z) : bool :=
  Nat.eqb (length s) (nv P) &&
  forallb (fun i => Z.leb (nth i (dlo P) 0%Z) (nth i s 0%Z) && Z.leb (nth i s 0%Z) (nth i (dhi P) 0%Z)) (seq 0 (nv P)).

Lemma inboxb_spec : forall P s, inboxb P s = true <-> InBox P s.
Proof.
  intros P s. unfold inboxb, InBox. rewrite andb_true_iff, Nat.eqb_eq, forallb_forall. split.
  - intros [H1 H2]. split; [exact H1|]. intros i Hi. specialize (H2 i ltac:(apply in_seq; lia)).
    apply andb_true_iff in H2 as [A1 A2]. apply Z.leb_le in A1, A2. split; assumption.
  - intros [H1 H2]. split; [exact H1|]. intros i Hi. apply in_seq in Hi.
    destruct (H2 i ltac:(lia)) as [A1 A2]. apply andb_true_iff. split; apply Z.leb_le; assumption.
Qed.

Definition H9 : Z := 1000000000%Z.

(* ---- A wallet: balance in [-1000, 10^9] (-1000 the overdraft floor). Events: deposit 5,
   deposit 20, withdraw 10 when balance >= 10, a fee of 3 (may overdraw). Invariant balance >= 0;
   repair: balance := 0. ---- *)
Definition wallet_d : dprog :=
  mkD [(-1000)%Z] [H9]
      [(DTrue, [(0%nat, DAdd (DV 0) (DL 5))]);
       (DTrue, [(0%nat, DAdd (DV 0) (DL 20))]);
       (DCmp CGe (DV 0) (DL 10), [(0%nat, DSub (DV 0) (DL 10))]);
       (DTrue, [(0%nat, DSub (DV 0) (DL 3))])]
      [(DCmp CGe (DV 0) (DL 0), [(0%nat, DL 0)])].

Definition wallet_A : list Z := [(-1000)%Z; H9; 0%Z; 10%Z].

(* Deposits are the checked pairs. *)
Definition deposits (a b : nat) : bool := Nat.ltb a 2 && Nat.ltb b 2.

Theorem wallet_frag : dfrag wallet_d wallet_A 0 20 = true /\ wcc1 0 20 1 = 160%Z.
Proof. split; reflexivity. Qed.

Theorem wallet_reps : length (RepS wallet_d wallet_A 160) = 657%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem wallet_checks : dterm_check wallet_d wallet_A 160 1 = true /\
  dcc1v_check wallet_d wallet_A 160 1 deposits = true.
Proof. split; vm_compute; reflexivity. Qed.

(* Deposits commute at every balance in range, and the runtime converges from every balance. *)
Theorem wallet_deposits_converge : forall s, InBox wallet_d s ->
  forall es1 es2, tequiv (fun a b => deposits a b = true) es1 es2 ->
  Forall (fun k => (k < nke wallet_d)%nat) es1 ->
  runT (drun wallet_d 1) es1 s = runT (drun wallet_d 1) es2 s.
Proof.
  destruct wallet_checks as [HT HC].
  exact (dbuild_sound wallet_d wallet_A 0 20 1 deposits eq_refl HT HC).
Qed.

(* Deposit and withdraw do not commute: the check over all pairs fails, and at balance 5 the two
   orders give 0 and 10. A real divergence, at a state in range. *)
Theorem wallet_withdraw_diverges :
  dcc1v_check wallet_d wallet_A 160 1 (fun _ _ => true) = false /\
  InBox wallet_d [5%Z] /\ dvalid wallet_d [5%Z] = true /\
  dgov wallet_d 1 2 (dgov wallet_d 1 0 [5%Z]) = [0%Z] /\
  dgov wallet_d 1 0 (dgov wallet_d 1 2 [5%Z]) = [10%Z].
Proof.
  split; [vm_compute; reflexivity|]. split; [apply inboxb_spec; reflexivity|].
  split; [reflexivity | split; vm_compute; reflexivity].
Qed.

(* The repair fires: a fee at balance 1 overdraws, and the repair restores 0. *)
Theorem wallet_repair_fires : dap wallet_d 3 [1%Z] = [(-2)%Z] /\ dvalid wallet_d [(-2)%Z] = false /\
  dgov wallet_d 1 3 [1%Z] = [0%Z].
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* ---- Capped inventory: stock in [0, 10^9], cap 10^6 (invariant stock <= 10^6, repair to the cap).
   Events: restock 3, restock 7, ship 2 when stock >= 2. ---- *)
Definition M6 : Z := 1000000%Z.

Definition capinv_d : dprog :=
  mkD [0%Z] [H9]
      [(DTrue, [(0%nat, DAdd (DV 0) (DL 3))]);
       (DTrue, [(0%nat, DAdd (DV 0) (DL 7))]);
       (DCmp CGe (DV 0) (DL 2), [(0%nat, DSub (DV 0) (DL 2))])]
      [(DCmp CLe (DV 0) (DL M6), [(0%nat, DL M6)])].

Definition capinv_A : list Z := [0%Z; H9; M6; 2%Z].

Definition restocks (a b : nat) : bool := Nat.ltb a 2 && Nat.ltb b 2.

Theorem capinv_frag : dfrag capinv_d capinv_A 0 7 = true /\ wcc1 0 7 1 = 56%Z.
Proof. split; reflexivity. Qed.

Theorem capinv_reps : length (RepS capinv_d capinv_A 56) = 233%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem capinv_checks : dterm_check capinv_d capinv_A 56 1 = true /\
  dcc1v_check capinv_d capinv_A 56 1 restocks = true /\
  dcc1v_check capinv_d capinv_A 56 1 (fun _ _ => true) = false.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

Theorem capinv_restocks_converge : forall s, InBox capinv_d s ->
  forall es1 es2, tequiv (fun a b => restocks a b = true) es1 es2 ->
  Forall (fun k => (k < nke capinv_d)%nat) es1 ->
  runT (drun capinv_d 1) es1 s = runT (drun capinv_d 1) es2 s.
Proof.
  destruct capinv_checks as [HT [HC _]].
  exact (dbuild_sound capinv_d capinv_A 0 7 1 restocks eq_refl HT HC).
Qed.

(* Restock and ship do not commute one below the cap. *)
Theorem capinv_ship_diverges :
  dgov capinv_d 1 2 (dgov capinv_d 1 0 [999999%Z]) = [999998%Z] /\
  dgov capinv_d 1 0 (dgov capinv_d 1 2 [999999%Z]) = [M6].
Proof. split; vm_compute; reflexivity. Qed.

(* ---- Reservations: (stock, reserved) in [0, 10^6]^2, invariant reserved <= stock, repair
   reserved := stock. Events: restock 3, reserve 2, reserve 3, release 1 (saturating at 0), and
   reserve 1 if reserved < stock. ---- *)
Definition reserve_d : dprog :=
  mkD [0%Z; 0%Z] [M6; M6]
      [(DTrue, [(0%nat, DAdd (DV 0) (DL 3))]);
       (DTrue, [(1%nat, DAdd (DV 1) (DL 2))]);
       (DTrue, [(1%nat, DAdd (DV 1) (DL 3))]);
       (DTrue, [(1%nat, DSub (DV 1) (DL 1))]);
       (DCmp CLt (DV 1) (DV 0), [(1%nat, DAdd (DV 1) (DL 1))])]
      [(DCmp CLe (DV 1) (DV 0), [(1%nat, DV 0)])].

Definition reserve_A : list Z := [0%Z; M6].

(* Checked pairs: the two reserves, and restock with release. *)
Definition reserve_I (a b : nat) : bool :=
  (Nat.eqb a 1 && Nat.eqb b 2) || (Nat.eqb a 2 && Nat.eqb b 1) ||
  (Nat.eqb a 0 && Nat.eqb b 3) || (Nat.eqb a 3 && Nat.eqb b 0).

Theorem reserve_frag : dfrag reserve_d reserve_A 0 3 = true /\ wcc1 0 3 1 = 24%Z.
Proof. split; reflexivity. Qed.

Theorem reserve_reps : length (RepS reserve_d reserve_A 24) = (102 * 102)%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem reserve_checks : dterm_check reserve_d reserve_A 24 1 = true /\
  dcc1v_check reserve_d reserve_A 24 1 reserve_I = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem reserve_converges : forall s, InBox reserve_d s ->
  forall es1 es2, tequiv (fun a b => reserve_I a b = true) es1 es2 ->
  Forall (fun k => (k < nke reserve_d)%nat) es1 ->
  runT (drun reserve_d 1) es1 s = runT (drun reserve_d 1) es2 s.
Proof.
  destruct reserve_checks as [HT HC].
  exact (dbuild_sound reserve_d reserve_A 0 3 1 reserve_I eq_refl HT HC).
Qed.

(* Reserve and release do not commute when everything is reserved: at (5, 5). Nor does the
   guarded reserve with release. *)
Theorem reserve_release_diverges :
  dgov reserve_d 1 3 (dgov reserve_d 1 1 [5%Z; 5%Z]) = [5%Z; 4%Z] /\
  dgov reserve_d 1 1 (dgov reserve_d 1 3 [5%Z; 5%Z]) = [5%Z; 5%Z] /\
  dgov reserve_d 1 3 (dgov reserve_d 1 4 [5%Z; 5%Z]) = [5%Z; 4%Z] /\
  dgov reserve_d 1 4 (dgov reserve_d 1 3 [5%Z; 5%Z]) = [5%Z; 5%Z].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- The comparison fragment over wide ranges: gsm's documented inventory (stock, ship_a,
   ship_b in [0, 10^9]; receive_x copies ship_x into stock when higher; cap 5). gam = mu = 0, so
   the threshold is 0 and the radius is n = 3. ---- *)
Definition inventory_d : dprog :=
  mkD [0%Z; 0%Z; 0%Z] [H9; H9; H9]
      [(DCmp CLt (DV 0) (DV 1), [(0%nat, DV 1)]);
       (DCmp CLt (DV 0) (DV 2), [(0%nat, DV 2)])]
      [(DCmp CLe (DV 0) (DL 5), [(0%nat, DL 5)])].

Definition inventory_A : list Z := [0%Z; H9; 5%Z].

Theorem inventory_d_frag : dfrag inventory_d inventory_A 0 0 = true /\ wcc1 0 0 1 = 0%Z /\
  radius inventory_d 0 = 3%Z.
Proof. split; [|split]; reflexivity. Qed.

Theorem inventory_d_reps : length (RepS inventory_d inventory_A 0) = 2197%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem inventory_d_checks : dterm_check inventory_d inventory_A 0 1 = true /\
  dcc1v_check inventory_d inventory_A 0 1 (fun _ _ => true) = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem inventory_d_converges : forall s, InBox inventory_d s ->
  forall es1 es2, Permutation es1 es2 -> Forall (fun k => (k < nke inventory_d)%nat) es1 ->
  runT (drun inventory_d 1) es1 s = runT (drun inventory_d 1) es2 s.
Proof.
  destruct inventory_d_checks as [HT HC].
  apply (dgsm_sound_all inventory_d inventory_A 0 0 eq_refl 1 0 (Z.le_refl _)
           (proj1 (dterm_check_spec _ _ _ _) HT)).
  pose proof (proj1 (dcc1v_check_spec _ _ _ _ _) HC) as H.
  intros s Hs Hv k1 k2 H1 H2 _. exact (H s Hs Hv k1 k2 H1 H2 eq_refl).
Qed.

(* ============================================================================================ *)
(* Boundaries.                                                                                  *)
(* ============================================================================================ *)

(* ---- The order-pattern check misses a difference guard; the new check reports it. Variables
   (x, y) in [0, 10^9]; A: if y - x >= 2 then x := y; B: if y - x >= 2 then y := x. ---- *)
Definition gap_g : dpred := DCmp CGe (DSub (DV 1) (DV 0)) (DL 2).
Definition gap_d : dprog :=
  mkD [0%Z; 0%Z] [H9; H9] [(gap_g, [(0%nat, DV 1)]); (gap_g, [(1%nat, DV 0)])] [].
Definition gap_A : list Z := [0%Z; H9].

Theorem gap_frag : dfrag gap_d gap_A 2 0 = true /\ wcc1 2 0 0 = 2%Z.
Proof. split; reflexivity. Qed.

(* The check over the representatives fails, as it must. *)
Theorem gap_check_fails : dcc1v_check gap_d gap_A 2 0 (fun _ _ => true) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem gap_diverges : InBox gap_d [0%Z; 2%Z] /\
  dgov gap_d 0 1 (dgov gap_d 0 0 [0%Z; 2%Z]) = [2%Z; 2%Z] /\
  dgov gap_d 0 0 (dgov gap_d 0 1 [0%Z; 2%Z]) = [0%Z; 0%Z].
Proof.
  split; [apply inboxb_spec; reflexivity | split; vm_compute; reflexivity].
Qed.

(* The same rule in AbstractionCutoff's language: the order-pattern check over reps 2 [] = {0, 1}
   passes (y - x >= 2 never holds there), the rule is outside ord_frag, and over the integers it
   diverges at (0, 2). *)
Definition gapP : prog :=
  mkProg [[If (FLe (Pl (Vr 0) (Cst 2%Z)) (Vr 1)) (Vr 1) (Vr 0); Vr 1];
          [Vr 0; If (FLe (Pl (Vr 0) (Cst 2%Z)) (Vr 1)) (Vr 0) (Vr 1)]]
         [Vr 0; Vr 1] FT.

Theorem gap_order_check_passes : abs_check [] 2 0 2 (sap gapP 0) (srp gapP) (svd gapP) 0 2 = true /\
  ord_frag [] gapP = false /\
  govK (sap gapP 0) (srp gapP) 0 (1%nat, []) (govK (sap gapP 0) (srp gapP) 0 (0%nat, []) [0%Z; 2%Z]) = [2%Z; 2%Z] /\
  govK (sap gapP 0) (srp gapP) 0 (0%nat, []) (govK (sap gapP 0) (srp gapP) 0 (1%nat, []) [0%Z; 2%Z]) = [0%Z; 0%Z].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- triangle_diverges in this language: the guard x < y < z < x + y compares z with a sum of two
   variables, which is not a difference constraint, so the fragment check refuses it; at (2, 3, 4)
   the registry diverges. ---- *)
Definition tri_g : dpred :=
  DAnd (DCmp CLt (DV 0) (DV 1)) (DAnd (DCmp CLt (DV 1) (DV 2)) (DCmp CLt (DV 2) (DAdd (DV 0) (DV 1)))).
Definition tri_d : dprog :=
  mkD [0%Z; 0%Z; 0%Z] [10%Z; 10%Z; 10%Z] [(tri_g, [(0%nat, DV 1)]); (tri_g, [(1%nat, DV 0)])] [].

Theorem tri_not_difference : norm (DSub (DV 2) (DAdd (DV 0) (DV 1))) = None.
Proof. reflexivity. Qed.

Theorem tri_refused : forall A g m, dfrag tri_d A g m = false.
Proof.
  intros A g m. unfold dfrag. cbn. destruct (Z.leb 0 g); cbn; rewrite ?andb_false_r; reflexivity.
Qed.

Theorem tri_diverges :
  dgov tri_d 0 1 (dgov tri_d 0 0 [2%Z; 3%Z; 4%Z]) = [3%Z; 3%Z; 4%Z] /\
  dgov tri_d 0 0 (dgov tri_d 0 1 [2%Z; 3%Z; 4%Z]) = [2%Z; 2%Z; 4%Z].
Proof. split; vm_compute; reflexivity. Qed.

(* ---- Outside the fragment: a write of a sum of two variable reads (x := y + y). Variables
   x, w in [0, 10^9], y in [1000, 10^9]. A: x := y + y; B: if x = w then x := x + 1. The
   representative check over the anchors {0, 1000, 10^9} at the threshold the formula would give
   (the sum counted as an offset-free write: 4) passes; the registry diverges at (0, 1000, 2000),
   where every value is far from every anchor. ---- *)
Definition sum_d : dprog :=
  mkD [0%Z; 1000%Z; 0%Z] [H9; H9; H9]
      [(DTrue, [(0%nat, DAdd (DV 1) (DV 1))]);
       (DCmp CEq (DV 0) (DV 2), [(0%nat, DAdd (DV 0) (DL 1))])] [].
Definition sum_A : list Z := [0%Z; 1000%Z; H9].
Definition sum_I (a b : nat) : bool := Nat.eqb a 0 && Nat.eqb b 1.

Theorem sum_refused : forall A g m, dfrag sum_d A g m = false.
Proof. intros A g m. unfold dfrag. cbn. rewrite ?andb_false_r. reflexivity. Qed.

Theorem sum_check_passes : dcc1v_check sum_d sum_A 4 0 sum_I = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sum_diverges : InBox sum_d [0%Z; 1000%Z; 2000%Z] /\
  dgov sum_d 0 1 (dgov sum_d 0 0 [0%Z; 1000%Z; 2000%Z]) = [2001%Z; 1000%Z; 2000%Z] /\
  dgov sum_d 0 0 (dgov sum_d 0 1 [0%Z; 1000%Z; 2000%Z]) = [2000%Z; 1000%Z; 2000%Z].
Proof.
  split; [apply inboxb_spec; reflexivity | split; vm_compute; reflexivity].
Qed.

(* ---- The threshold must cover chained increments. Variables (x, y, z) in [0, 100]; A adds 3 to
   x twice (offset 6 in one event); B: if x = y then z := z + 1. The states (0, 6, 0) and (0, 7, 0)
   are related at threshold 5 = 2 * 3 - 1, and CC1 of A and B fails at the first and holds at the
   second: a threshold below the chained offset 6 does not transfer CC1. ---- *)
Definition chain_d : dprog :=
  mkD [0%Z; 0%Z; 0%Z] [100%Z; 100%Z; 100%Z]
      [(DTrue, [(0%nat, DAdd (DV 0) (DL 3)); (0%nat, DAdd (DV 0) (DL 3))]);
       (DCmp CEq (DV 0) (DV 1), [(2%nat, DAdd (DV 2) (DL 1))])] [].
Definition chain_A : list Z := [0%Z; 100%Z].

Theorem granularity_needs_chain : dfrag chain_d chain_A 0 6 = true /\
  RelS 5 chain_A [0%Z; 6%Z; 0%Z] [0%Z; 7%Z; 0%Z] /\
  dgov chain_d 0 1 (dgov chain_d 0 0 [0%Z; 6%Z; 0%Z]) <> dgov chain_d 0 0 (dgov chain_d 0 1 [0%Z; 6%Z; 0%Z]) /\
  dgov chain_d 0 1 (dgov chain_d 0 0 [0%Z; 7%Z; 0%Z]) = dgov chain_d 0 0 (dgov chain_d 0 1 [0%Z; 7%Z; 0%Z]).
Proof.
  split; [reflexivity|]. split; [split; [reflexivity | apply relb_spec; vm_compute; reflexivity]|].
  split; [vm_compute; discriminate | vm_compute; reflexivity].
Qed.
