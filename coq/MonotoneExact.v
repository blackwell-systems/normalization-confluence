(* MonotoneExact.v: exact conditions on monotone cycles, closing REGIME-AUDIT section 9 rows
   "Validity of the lfp" and "Finite reachability of the lfp by iteration".

   Setting: the network model of MonotoneFederation.v (components (shared, local), repair
   operator Phi built from morphisms and resolvers, Phase-1 locals l fixed), with the Kleene
   iteration of Federation.v and the chaotic iteration of Chaotic.v / FederationEventsCycles.v.

   (a) Validity of the least fixed point. MonotoneFederation proves a sufficient condition
       (net_lfp_valid, net_Ncyc_correct: every component valid with bottom shared values).
       Exact form:
         lfp_valid_iff_reached     if the lfp m is reached by Kleene iteration from bottom
                                   (m = Phi^K(bot) for some K), then, under R2 and valid locals,
                                   m is federally valid  <->  SOME Kleene iterate is valid.
         lfp_valid_exact           the same under ACC (no reachability hypothesis needed).
         Ncyc_valid_exact          for gsm's cyclic normalizer (finite height), per input t:
                                   the normal form is federally valid <-> some Kleene iterate
                                   from bottom, at t's Phase-1 locals, is valid.
         fixed_valid_iff_images    at any fixed point (no lfp, no R2): federally valid <-> every
                                   target's image at that fixed point's own source states is
                                   valid (the one combination gsm would have to check).
       Bottom validity is the case k = 0 (net_lfp_valid_recovered). It is not necessary:
       bottom_validity_not_necessary (bottom invalid, lfp valid). The reachability qualifier is
       needed: lfp_valid_iff_needs_reach (on the chain w+1 every iterate is valid, R2 holds, and
       the lfp w, never reached, is invalid).
   (b) gsm's check. gsm (federation_monotone.go, verifyMonotoneVisited) checks, for every target,
       every combination of VISITED source states and every visited target state, that the
       target with the image written is valid; a component's visited states are its valid local
       parts with ANY shared value (a component no morphism writes: its valid states). That is
       GsmCheck below. gsm_check_fixed_valid: GsmCheck makes EVERY fixed point of Phi l
       federally valid (valid locals; no R2, no monotonicity, no reachability needed), hence the
       lfp (gsm_check_lfp_valid) and gsm's cyclic normal form (gsm_check_Ncyc_valid, without
       bottom validity). So gsm's check is sound (no gsm bug), and its run-time panic on an
       invalid fixed point is unreachable for pure closures. It is not necessary:
       gsm_check_not_necessary (gsm rejects; bottom valid; lfp valid). The two sufficient
       conditions (bottom validity, GsmCheck) are incomparable (the two instances).
   (c) Finite reachability.
         kleene_reach_exact        the Kleene chain reaches the lfp in finitely many steps <->
                                   it is eventually constant <-> productive Kleene steps from
                                   bottom are strongly normalizing <-> no infinite strictly
                                   ascending chain along the Kleene chain (Acc of chain_asc at
                                   bottom). Constructive without decidability: kleene_reach_nn.
         Corollaries: ACC (kleene_reach_of_acc), ACC below any fixed point
                                   (kleene_reach_of_acc_below), finite height
                                   (kleene_reach_of_finite_height). Neither ACC nor ACC below
                                   the lfp is necessary: acc_not_necessary.
         chaotic_reach_exact       on the network: some finite chaotic schedule reaches the lfp
                                   <-> Kleene reaches it <-> gsm's round-robin sweeps reach it,
                                   and the round-robin needs no more rounds than Kleene needs
                                   steps (rounds_reach_by_kleene). "Every schedule terminates"
                                   (strong normalization of chaotic steps) is strictly
                                   stronger: chaotic_sn_strictly_stronger. *)

From Coq Require Import List Arith Bool Lia.
From Coq Require Import Wellfounded.Inclusion.
Require Import NC.Newman NC.Federation NC.Chaotic NC.ChaoticACC NC.FederationEventsCycles NC.MonotoneFederation.
Import ListNotations.

(* ======================================================================================= *)
(* Part 1. (c) Finite reachability of the lfp by Kleene iteration: the exact condition.     *)
(* ======================================================================================= *)

Lemma iter_stable : forall {L : Type} (f : L -> L) (bot : L) K,
  f (iter f bot K) = iter f bot K -> forall i, iter f bot (i + K) = iter f bot K.
Proof.
  intros L f bot K H i. induction i as [| i IH]; [reflexivity |].
  simpl. rewrite IH. exact H.
Qed.

Section KleeneExact.
  Context {L : Type}.
  Variable le : L -> L -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Hypothesis le_antisym : forall x y, le x y -> le y x -> x = y.
  Variable f : L -> L.
  Hypothesis f_mono : forall x y, le x y -> le (f x) (f y).
  Variable bot : L.
  Hypothesis bot_least : forall x, le bot x.

  (* A productive Kleene step. *)
  Definition kstep (x y : L) : Prop := y = f x /\ x <> y.

  (* Strict ascent between two elements of the Kleene chain: "ACC along the chain" is
     Acc chain_asc bot. *)
  Definition chain_asc (y x : L) : Prop :=
    ascends le y x /\ (exists k, x = iter f bot k) /\ (exists k, y = iter f bot k).

  Lemma iter_le_mono : forall i j, i <= j -> le (iter f bot i) (iter f bot j).
  Proof.
    intros i j H. induction H as [| j H IH]; [apply le_refl |].
    eapply le_trans; [exact IH | apply (iter_ascending le f f_mono bot bot_least)].
  Qed.

  Lemma stab_kstep_sn : forall K, f (iter f bot K) = iter f bot K -> SN kstep bot.
  Proof.
    intros K HK.
    assert (H : forall d i, i + d = K -> SN kstep (iter f bot i)).
    { induction d as [| d IH]; intros i Hi.
      - rewrite Nat.add_0_r in Hi. subst i. constructor. intros y [-> Hne].
        exfalso. apply Hne. symmetry. exact HK.
      - constructor. intros y [-> _]. change (SN kstep (iter f bot (S i))). apply IH. lia. }
    apply (H K 0). lia.
  Qed.

  Lemma sn_stab : (forall x, {f x = x} + {f x <> x}) ->
    SN kstep bot -> {K : nat | f (iter f bot K) = iter f bot K}.
  Proof.
    intros dec Hsn.
    assert (H : forall x, SN kstep x -> forall n, x = iter f bot n ->
                {K : nat | f (iter f bot K) = iter f bot K}).
    { intros x Hx. induction Hx as [x _ IH]. intros n Hn.
      destruct (dec (iter f bot n)) as [E | NE]; [exists n; exact E |].
      apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
      subst x. split; [reflexivity | intro E; apply NE; symmetry; exact E]. }
    exact (H bot Hsn 0 eq_refl).
  Defined.

  Lemma sn_stab_nn : SN kstep bot -> ~ ~ exists K, f (iter f bot K) = iter f bot K.
  Proof.
    intros Hsn Hno.
    assert (H : forall x, SN kstep x -> forall n, x = iter f bot n -> False).
    { intros x Hx. induction Hx as [x _ IH]. intros n Hn.
      apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
      subst x. split; [reflexivity |].
      intro E. apply Hno. exists n. symmetry. exact E. }
    exact (H bot Hsn 0 eq_refl).
  Qed.

  Lemma chain_asc_next : forall K, f (iter f bot K) = iter f bot K ->
    forall i y, i <= K -> chain_asc y (iter f bot i) ->
    exists j, i < j /\ j <= K /\ y = iter f bot j.
  Proof.
    intros K HK i y Hi [[Hle Hne] [_ [j ->]]].
    destruct (le_lt_dec K j) as [HjK | HjK].
    - assert (E : iter f bot j = iter f bot K).
      { replace j with ((j - K) + K) by lia. apply iter_stable. exact HK. }
      rewrite E in Hle, Hne |- *. exists K. split; [| split; [lia | reflexivity]].
      destruct (Nat.eq_dec i K) as [-> | Ne]; [exfalso; apply Hne; reflexivity | lia].
    - destruct (le_lt_dec j i) as [Hji | Hij].
      + exfalso. apply Hne. apply le_antisym; [exact Hle | apply iter_le_mono; exact Hji].
      + exists j. split; [exact Hij | split; [lia | reflexivity]].
  Qed.

  Lemma stab_chain_acc : forall K, f (iter f bot K) = iter f bot K -> Acc chain_asc bot.
  Proof.
    intros K HK.
    assert (H : forall d i, i <= K -> K - i <= d -> Acc chain_asc (iter f bot i)).
    { induction d as [| d IH]; intros i Hi Hd; constructor; intros y Hy;
        destruct (chain_asc_next K HK i y Hi Hy) as [j [Hij [HjK ->]]].
      - lia.
      - apply IH; lia. }
    exact (H K 0 ltac:(lia) ltac:(lia)).
  Qed.

  Lemma chain_acc_stab : (forall x, {f x = x} + {f x <> x}) ->
    Acc chain_asc bot -> {K : nat | f (iter f bot K) = iter f bot K}.
  Proof.
    intros dec Hacc.
    assert (H : forall x, Acc chain_asc x -> forall n, x = iter f bot n ->
                {K : nat | f (iter f bot K) = iter f bot K}).
    { intros x Hx. induction Hx as [x _ IH]. intros n Hn.
      destruct (dec (iter f bot n)) as [E | NE]; [exists n; exact E |].
      apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
      subst x. split; [split |].
      - apply (iter_ascending le f f_mono bot bot_least).
      - intro E. apply NE. symmetry. exact E.
      - split; [exists n; reflexivity | exists (S n); reflexivity]. }
    exact (H bot Hacc 0 eq_refl).
  Defined.

  (* (c), the exact condition for Kleene iteration. Given the stabilization test (the only
     test an implementation runs), the following are equivalent:
       the lfp is reached at a finite stage; the chain is eventually constant; productive
       Kleene steps from bottom are strongly normalizing; there is no infinite strictly
       ascending chain along the Kleene chain. *)
  Theorem kleene_reach_exact : (forall x, {f x = x} + {f x <> x}) ->
    ((exists K, is_lfp le f (iter f bot K)) <-> (exists K, f (iter f bot K) = iter f bot K)) /\
    ((exists K, f (iter f bot K) = iter f bot K) <-> SN kstep bot) /\
    ((exists K, f (iter f bot K) = iter f bot K) <-> Acc chain_asc bot).
  Proof.
    intros dec. split; [| split].
    - split; intros [K HK]; exists K; [exact (proj1 HK) | apply (kleene_lfp le f f_mono bot bot_least K HK)].
    - split; [intros [K HK]; exact (stab_kstep_sn K HK) |].
      intros H. destruct (sn_stab dec H) as [K HK]. exists K. exact HK.
    - split; [intros [K HK]; exact (stab_chain_acc K HK) |].
      intros H. destruct (chain_acc_stab dec H) as [K HK]. exists K. exact HK.
  Qed.

  (* The same, for a given least fixed point m: the Kleene chain hits m iff it stabilizes. *)
  Theorem kleene_reaches_iff : forall m, is_lfp le f m ->
    (exists K, iter f bot K = m) <-> (exists K, f (iter f bot K) = iter f bot K).
  Proof.
    intros m Hm. split.
    - intros [K HK]. exists K. rewrite HK. exact (proj1 Hm).
    - intros [K HK]. exists K.
      apply (lfp_unique le le_antisym f); [apply (kleene_lfp le f f_mono bot bot_least K HK) | exact Hm].
  Qed.

  (* Without decidability (fully constructive): stabilization implies both, and either
     makes non-stabilization absurd. *)
  Theorem kleene_reach_nn :
    ((exists K, f (iter f bot K) = iter f bot K) -> SN kstep bot /\ Acc chain_asc bot) /\
    (SN kstep bot -> ~ ~ exists K, f (iter f bot K) = iter f bot K) /\
    (Acc chain_asc bot -> ~ ~ exists K, f (iter f bot K) = iter f bot K).
  Proof.
    split; [intros [K HK]; split; [exact (stab_kstep_sn K HK) | exact (stab_chain_acc K HK)] |].
    split; [exact sn_stab_nn |].
    intros Hacc Hno.
    assert (H : forall x, Acc chain_asc x -> forall n, x = iter f bot n -> False).
    { intros x Hx. induction Hx as [x _ IH]. intros n Hn.
      apply (IH (iter f bot (S n))) with (n := S n); [| reflexivity].
      subst x. split; [split |].
      - apply (iter_ascending le f f_mono bot bot_least).
      - intro E. apply Hno. exists n. symmetry. exact E.
      - split; [exists n; reflexivity | exists (S n); reflexivity]. }
    exact (H bot Hacc 0 eq_refl).
  Qed.

  (* Corollaries: the sufficient conditions, recovered. *)
  Corollary chain_acc_of_acc : well_founded (ascends le) -> Acc chain_asc bot.
  Proof.
    intros W. apply (Acc_incl _ _ (ascends le)); [intros y x [H _]; exact H | apply W].
  Qed.

  Corollary chain_acc_of_acc_below : forall m, f m = m ->
    well_founded (ascends_below le m) -> Acc chain_asc bot.
  Proof.
    intros m Hm W. apply (Acc_incl _ _ (ascends_below le m)); [| apply W].
    intros y x [Ha [_ [k ->]]]. split; [| exact Ha].
    apply (iter_below_fixed le f f_mono bot bot_least m Hm k).
  Qed.

  Corollary kleene_reach_of_acc : (forall x, {f x = x} + {f x <> x}) ->
    well_founded (ascends le) -> {K : nat | is_lfp le f (iter f bot K)}.
  Proof.
    intros dec W. destruct (chain_acc_stab dec (chain_acc_of_acc W)) as [K HK].
    exists K. apply (kleene_lfp le f f_mono bot bot_least K HK).
  Defined.

  Corollary kleene_reach_of_acc_below : (forall x, {f x = x} + {f x <> x}) ->
    forall m, f m = m -> well_founded (ascends_below le m) -> {K : nat | is_lfp le f (iter f bot K)}.
  Proof.
    intros dec m Hm W. destruct (chain_acc_stab dec (chain_acc_of_acc_below m Hm W)) as [K HK].
    exists K. apply (kleene_lfp le f f_mono bot bot_least K HK).
  Defined.

  Corollary kleene_reach_of_finite_height : (forall x, {f x = x} + {f x <> x}) ->
    forall (rank : L -> nat) (H : nat),
    (forall x y, le x y -> x <> y -> rank x < rank y) -> (forall x, rank x <= H) ->
    {K : nat | is_lfp le f (iter f bot K)}.
  Proof.
    intros dec rank H Hs Hb. exact (kleene_reach_of_acc dec (finite_height_acc le rank H Hs Hb)).
  Defined.
End KleeneExact.

(* Neither ACC nor ACC below the lfp is necessary: on the chain w+2 (MonotoneFederation.W),
   the constant operator w reaches its lfp w in one step (Kleene, and every chaotic schedule),
   though the chain 0 < 1 < 2 < ... lies below w. *)
Definition fOm (_ : W) : W := Om.

Lemma no_acc_below_Om : ~ well_founded (ascends_below wle Om).
Proof.
  intros Wf.
  assert (H : forall x, Acc (ascends_below wle Om) x -> forall k, x = Fin k -> False).
  { intros x Hx. induction Hx as [x _ IH]. intros k ->.
    apply (IH (Fin (S k))) with (k := S k); [| reflexivity].
    split; [reflexivity |]. split.
    - unfold wle. simpl. apply Nat.leb_le. lia.
    - intro E. injection E. lia. }
  exact (H (Fin 0) (Wf (Fin 0)) 0 eq_refl).
Qed.

Theorem acc_not_necessary :
  (forall x y, wle x y -> wle (fOm x) (fOm y)) /\
  is_lfp wle fOm Om /\ iter fOm (Fin 0) 1 = Om /\
  SN (kstep fOm) (Fin 0) /\ Acc (chain_asc wle fOm (Fin 0)) (Fin 0) /\
  SN (Chaotic.step unit (fun _ => fOm)) (Fin 0) /\
  ~ well_founded (ascends_below wle Om) /\ ~ well_founded (ascends wle).
Proof.
  assert (Hm : forall x y, wle x y -> wle (fOm x) (fOm y)) by (intros; reflexivity).
  assert (Hst : fOm (iter fOm (Fin 0) 1) = iter fOm (Fin 0) 1) by reflexivity.
  split; [exact Hm |].
  split; [split; [reflexivity | intros x Hx; unfold fixed_point, fOm in Hx; subst x; apply wle_refl] |].
  split; [reflexivity |].
  split; [exact (stab_kstep_sn fOm (Fin 0) 1 Hst) |].
  split; [exact (stab_chain_acc wle wle_refl wle_trans wle_antisym fOm Hm (Fin 0) wbot_least 1 Hst) |].
  split.
  { constructor. intros y [[] [-> _]]. constructor. intros z [[] [-> Hne]].
    exfalso. apply Hne. reflexivity. }
  split; [exact no_acc_below_Om |].
  intros Wf. apply no_acc_below_Om. exact (acc_below_of_acc wle Om Wf).
Qed.

(* And the continuous operator of MonotoneFederation.kleene_sup_instance, whose lfp w is never
   reached, fails the exact condition: productive Kleene steps from bottom do not terminate. *)
Theorem kleene_sup_not_sn : ~ SN (kstep wPhic) (Fin 0) /\ ~ Acc (chain_asc wle wPhic (Fin 0)) (Fin 0).
Proof.
  assert (Hit : forall k, iter wPhic (Fin 0) k = Fin k).
  { induction k as [| k IH]; [reflexivity | simpl; rewrite IH; reflexivity]. }
  assert (Hns : ~ exists K, wPhic (iter wPhic (Fin 0) K) = iter wPhic (Fin 0) K).
  { intros [K HK]. rewrite Hit in HK. simpl in HK. injection HK. lia. }
  destruct (kleene_reach_nn wle wle_refl wle_trans wle_antisym wPhic wPhic_mono (Fin 0) wbot_least)
    as [_ [H1 H2]].
  split; intro H; [exact (H1 H Hns) | exact (H2 H Hns)].
Qed.

(* ======================================================================================= *)
(* Part 2. (a) and (b): validity of the least fixed point on the network, and gsm's check.  *)
(* ======================================================================================= *)

Section NetExact.
  Context {SV Lc Loc Sh : Type}.
  Variable leS : SV -> SV -> Prop.
  Hypothesis leS_refl : forall a, leS a a.
  Hypothesis leS_trans : forall a b c, leS a b -> leS b c -> leS a c.
  Hypothesis leS_antisym : forall a b, leS a b -> leS b a -> a = b.
  Variable botS : SV.
  Hypothesis botS_least : forall a, leS botS a.
  Variable n : nat.
  Variable get : nat -> Sh -> SV.
  Variable tab : (nat -> SV) -> Sh.
  Hypothesis get_tab : forall g j, j < n -> get j (tab g) = g j.
  Hypothesis sh_ext : forall x y, (forall j, j < n -> get j x = get j y) -> x = y.
  Variable lst : Loc -> nat -> SV * Lc.
  Variable V : nat -> SV * Lc -> Prop.
  Variable srcs : nat -> list nat.
  Variable Gam : nat -> list (SV * Lc) -> SV.
  Hypothesis srcs_range : forall j i, j < n -> In i (srcs j) -> i < n.

  Local Notation PhiN := (Phi get tab lst srcs Gam).
  Local Notation nuN := (nu get tab lst srcs Gam).
  Local Notation LV := (LValid n get lst V).
  Local Notation FV := (FedValid n get tab lst V srcs Gam).
  Local Notation NLE := (nle leS n get).
  Local Notation BOT := (nbot botS tab).
  Local Notation LocV := (LocValid n lst V).
  Local Notation MonoN := (Mono leS n get tab lst srcs Gam).
  Local Notation R2N := (R2 n V srcs Gam).
  Local Notation sweepN := (sweep Loc Sh nuN).

  Lemma NLE_refl : forall x, NLE x x.
  Proof. exact (nle_refl leS leS_refl n get). Qed.
  Lemma NLE_trans : forall x y z, NLE x y -> NLE y z -> NLE x z.
  Proof. exact (nle_trans leS leS_trans n get). Qed.
  Lemma NLE_antisym : forall x y, NLE x y -> NLE y x -> x = y.
  Proof. exact (nle_antisym leS leS_antisym n get sh_ext). Qed.
  Lemma BOT_least : forall x, NLE BOT x.
  Proof. exact (nbot_least leS botS botS_least n get tab get_tab). Qed.

  Lemma entry_target : forall l x j, srcs j <> [] ->
    entry get lst srcs Gam l x j = Gam j (map (comp get lst l x) (srcs j)).
  Proof. intros l x j H. unfold entry. destruct (srcs j); [contradiction | reflexivity]. Qed.

  Lemma entry_source : forall l x j, srcs j = [] -> entry get lst srcs Gam l x j = fst (lst l j).
  Proof. intros l x j H. unfold entry. rewrite H. reflexivity. Qed.

  Lemma fixed_comp : forall l x j, j < n -> PhiN l x = x ->
    comp get lst l x j = (entry get lst srcs Gam l x j, snd (lst l j)).
  Proof.
    intros l x j Hj H. unfold comp. f_equal.
    rewrite <- (Phi_get n get tab get_tab lst srcs Gam l x j Hj). rewrite H. reflexivity.
  Qed.

  Lemma fixed_source_comp : forall l x j, j < n -> PhiN l x = x -> srcs j = [] ->
    comp get lst l x j = lst l j.
  Proof.
    intros l x j Hj H Hs. rewrite (fixed_comp l x j Hj H), (entry_source l x j Hs).
    symmetry. apply surjective_pairing.
  Qed.

  (* The image condition at one shared assignment x: every target, given x's own source
     states, produces a valid state. *)
  Definition ImageValidAt (l : Loc) (x : Sh) : Prop :=
    forall j, j < n -> srcs j <> [] ->
      V j (Gam j (map (comp get lst l x) (srcs j)), snd (lst l j)).

  (* (a), pointwise: a fixed point is federally valid exactly when every target's image at that
     fixed point's own source states is valid. No R2, no monotonicity. *)
  Theorem fixed_valid_iff_images : forall l x, LocV l -> PhiN l x = x ->
    (FV l x <-> ImageValidAt l x).
  Proof.
    intros l x Hl Hx. split.
    - intros [Hv _] j Hj Hne. specialize (Hv j Hj).
      rewrite (fixed_comp l x j Hj Hx), (entry_target l x j Hne) in Hv. exact Hv.
    - intros Hi. split; [| exact Hx]. intros j Hj.
      destruct (list_eq_dec Nat.eq_dec (srcs j) []) as [Hs | Hne].
      + rewrite (fixed_source_comp l x j Hj Hx Hs). apply Hl. exact Hj.
      + rewrite (fixed_comp l x j Hj Hx), (entry_target l x j Hne). apply Hi; assumption.
  Qed.

  Lemma iter_valid_from : R2N -> forall l, LocV l -> forall k,
    LV l (iter (PhiN l) BOT k) -> forall i, LV l (iter (PhiN l) BOT (i + k)).
  Proof.
    intros HR l Hl k Hk i. induction i as [| i IH]; [exact Hk |].
    simpl. exact (Phi_valid n get tab get_tab lst V srcs Gam srcs_range HR l _ Hl IH).
  Qed.

  (* (a), exact: if the least fixed point is reached by Kleene iteration from bottom, it is
     federally valid iff some Kleene iterate is valid. *)
  Theorem lfp_valid_iff_reached : R2N -> forall l, LocV l ->
    forall m, is_lfp NLE (PhiN l) m -> (exists K, iter (PhiN l) BOT K = m) ->
    (FV l m <-> exists k, LV l (iter (PhiN l) BOT k)).
  Proof.
    intros HR l Hl m [Hfix _] [K <-]. split.
    - intros [Hv _]. exists K. exact Hv.
    - intros [k Hk]. split; [| exact Hfix].
      destruct (le_lt_dec k K) as [HkK | HKk].
      + pose proof (iter_valid_from HR l Hl k Hk (K - k)) as H.
        replace (K - k + k) with K in H by lia. exact H.
      + rewrite <- (iter_stable (PhiN l) BOT K Hfix (k - K)).
        replace (k - K + K) with k by lia. exact Hk.
  Qed.

  (* Under ACC the reachability hypothesis is automatic. *)
  Theorem lfp_valid_exact : R2N -> MonoN -> well_founded (ascends NLE) ->
    (forall x y : Sh, {x = y} + {x <> y}) ->
    forall l, LocV l -> forall m, is_lfp NLE (PhiN l) m ->
    (FV l m <-> exists k, LV l (iter (PhiN l) BOT k)).
  Proof.
    intros HR Hm Hacc Hdec l Hl m Hlfp. apply (lfp_valid_iff_reached HR l Hl m Hlfp).
    destruct (kleene_acc_stabilizes NLE (PhiN l) (Hm l) BOT BOT_least Hacc
                (fun x => Hdec (PhiN l x) x)) as [K HK].
    exists K. apply (lfp_unique NLE NLE_antisym (PhiN l));
      [apply (kleene_lfp NLE (PhiN l) (Hm l) BOT BOT_least K HK) | exact Hlfp].
  Qed.

  (* The existing sufficient condition (MonotoneFederation.net_lfp_valid) is the case k = 0. *)
  Corollary net_lfp_valid_recovered : R2N -> MonoN -> well_founded (ascends NLE) ->
    (forall x y : Sh, {x = y} + {x <> y}) ->
    forall l, LocV l -> LV l BOT -> forall m, is_lfp NLE (PhiN l) m -> FV l m.
  Proof.
    intros HR Hm Hacc Hdec l Hl Hb m Hlfp.
    apply (proj2 (lfp_valid_exact HR Hm Hacc Hdec l Hl m Hlfp)). exists 0. exact Hb.
  Qed.

  (* ---- (b) gsm's check, stated exactly. ---- *)

  (* The states gsm's verifyMonotoneVisited enumerates for component i (visitedStates): a
     component some morphism writes ranges over its valid local parts with any shared value; a
     component no morphism writes ranges over its valid states. *)
  Definition Vis (i : nat) (u : SV * Lc) : Prop :=
    match srcs i with
    | [] => V i u
    | _ => exists t, V i t /\ snd u = snd t
    end.

  (* gsm's validity check: for every target, every combination of visited source states and
     every visited target state, the target with the (source-determined) image written is
     valid ("makes target invalid ... from sources ..., a combination the monotone-cycle
     iteration can visit"). *)
  Definition GsmCheck : Prop :=
    forall j, j < n -> srcs j <> [] ->
      forall f : nat -> SV * Lc, (forall i, In i (srcs j) -> Vis i (f i)) ->
      forall t, Vis j t -> V j (Gam j (map f (srcs j)), snd t).

  (* (b): gsm's check makes every fixed point federally valid, at any valid locals. *)
  Theorem gsm_check_fixed_valid : GsmCheck -> forall l x, LocV l -> PhiN l x = x -> FV l x.
  Proof.
    intros HG l x Hl Hx. apply (proj2 (fixed_valid_iff_images l x Hl Hx)).
    intros j Hj Hne. apply (HG j Hj Hne (comp get lst l x)).
    - intros i Hi. pose proof (srcs_range j i Hj Hi) as Hin. unfold Vis.
      destruct (srcs i) as [| a r] eqn:E.
      + rewrite (fixed_source_comp l x i Hin Hx E). apply Hl. exact Hin.
      + exists (lst l i). split; [apply Hl; exact Hin | reflexivity].
    - unfold Vis. destruct (srcs j) as [| a r] eqn:E; [contradiction |].
      exists (lst l j). split; [apply Hl; exact Hj | reflexivity].
  Qed.

  Corollary gsm_check_lfp_valid : GsmCheck -> forall l, LocV l ->
    forall m, is_lfp NLE (PhiN l) m -> FV l m.
  Proof. intros HG l Hl m [Hf _]. exact (gsm_check_fixed_valid HG l m Hl Hf). Qed.

  (* ---- (c) on the network: chaotic schedules versus Kleene. ---- *)

  Lemma nu_below_Phi : forall l j x, NLE x (PhiN l x) -> NLE (nuN l j x) (PhiN l x).
  Proof.
    intros l j x H k Hk. unfold nu. rewrite (get_nupd n get tab get_tab) by exact Hk.
    destruct (Nat.eqb k j) eqn:E; [apply Nat.eqb_eq in E; subst; apply leS_refl | apply H; exact Hk].
  Qed.

  Lemma sweep_sound : MonoN -> forall l js x, NLE x (PhiN l x) ->
    NLE (sweepN l js x) (PhiN l (sweepN l js x)) /\ NLE x (sweepN l js x).
  Proof.
    intros Hm l js. induction js as [| a js IH]; intros x Hx; [split; [exact Hx | apply NLE_refl] |].
    simpl. destruct (IH (nuN l a x) (nu_sound leS leS_refl leS_trans n get tab get_tab lst srcs Gam Hm l a x Hx))
      as [H1 H2].
    split; [exact H1 |].
    eapply NLE_trans; [apply (nu_incr leS leS_refl n get tab get_tab lst srcs Gam l a x Hx) | exact H2].
  Qed.

  (* A chaotic schedule of length k from a sound state below the k-th Kleene iterate stays
     below the matching iterate: Kleene dominates every schedule. *)
  Lemma sweep_below_iter : MonoN -> forall l js x k, NLE x (PhiN l x) ->
    NLE x (iter (PhiN l) BOT k) -> NLE (sweepN l js x) (iter (PhiN l) BOT (length js + k)).
  Proof.
    intros Hm l js. induction js as [| a js IH]; intros x k Hs Hx; [exact Hx |].
    replace (length (a :: js) + k) with (length js + Datatypes.S k) by (simpl; lia).
    change (sweepN l (a :: js) x) with (sweepN l js (nuN l a x)). apply IH.
    - exact (nu_sound leS leS_refl leS_trans n get tab get_tab lst srcs Gam Hm l a x Hs).
    - simpl. eapply NLE_trans; [apply nu_below_Phi; exact Hs | apply Hm; exact Hx].
  Qed.

  Lemma sweep_below_fixed : MonoN -> forall l js x p, PhiN l p = p -> NLE x p ->
    NLE (sweepN l js x) p.
  Proof.
    intros Hm l js. induction js as [| a js IH]; intros x p Hp Hx; [exact Hx |].
    simpl. apply IH; [exact Hp |].
    rewrite <- (nu_fixed n get tab get_tab sh_ext lst srcs Gam l a p Hp).
    apply (nu_mono leS n get tab get_tab lst srcs Gam Hm). exact Hx.
  Qed.

  Lemma sweep_coord_ge : MonoN -> forall l js x, NLE x (PhiN l x) ->
    forall k, k < n -> In k js -> leS (get k (PhiN l x)) (get k (sweepN l js x)).
  Proof.
    intros Hm l js. induction js as [| a js IH]; intros x Hs k Hk Hin; [destruct Hin |].
    simpl. pose proof (nu_sound leS leS_refl leS_trans n get tab get_tab lst srcs Gam Hm l a x Hs) as Hs'.
    pose proof (nu_incr leS leS_refl n get tab get_tab lst srcs Gam l a x Hs) as Hinc.
    destruct Hin as [<- | Hin].
    - assert (E : get a (nuN l a x) = get a (PhiN l x)).
      { unfold nu. rewrite (get_nupd n get tab get_tab) by exact Hk. rewrite Nat.eqb_refl. reflexivity. }
      rewrite <- E. apply (proj2 (sweep_sound Hm l js _ Hs')). exact Hk.
    - eapply leS_trans; [apply (Hm l x (nuN l a x) Hinc); exact Hk | apply IH; assumption].
  Qed.

  (* One round-robin sweep (gsm's normalizeCyclic round) dominates one Kleene step. *)
  Lemma sweep_round_ge_Phi : MonoN -> forall l x, NLE x (PhiN l x) ->
    NLE (PhiN l x) (sweepN l (seq 0 n) x).
  Proof.
    intros Hm l x Hs k Hk. apply sweep_coord_ge; [exact Hm | exact Hs | exact Hk |].
    apply in_seq. lia.
  Qed.

  Definition round (l : Loc) (x : Sh) : Sh := sweepN l (seq 0 n) x.

  Lemma rounds_ge_iter : MonoN -> forall l r,
    NLE (iter (PhiN l) BOT r) (iter (round l) BOT r) /\
    NLE (iter (round l) BOT r) (PhiN l (iter (round l) BOT r)).
  Proof.
    intros Hm l r. induction r as [| r [IH1 IH2]]; [split; [apply NLE_refl | apply BOT_least] |].
    simpl. split.
    - eapply NLE_trans; [apply Hm; exact IH1 |]. apply sweep_round_ge_Phi; assumption.
    - exact (proj1 (sweep_sound Hm l (seq 0 n) _ IH2)).
  Qed.

  Lemma rounds_below_fixed : MonoN -> forall l p, PhiN l p = p ->
    forall r, NLE (iter (round l) BOT r) p.
  Proof.
    intros Hm l p Hp r. induction r as [| r IH]; [apply BOT_least |].
    simpl. unfold round. apply sweep_below_fixed; assumption.
  Qed.

  Lemma sweep_app : forall l a b x, sweepN l (a ++ b) x = sweepN l b (sweepN l a x).
  Proof. intros l a. induction a as [| j a IH]; intros b x; [reflexivity | simpl; apply IH]. Qed.

  Fixpoint reps (r : nat) : list nat := match r with 0 => [] | Datatypes.S r => reps r ++ seq 0 n end.

  Lemma sweep_reps : forall l r, sweepN l (reps r) BOT = iter (round l) BOT r.
  Proof.
    intros l r. induction r as [| r IH]; [reflexivity |].
    simpl. rewrite sweep_app, IH. reflexivity.
  Qed.

  (* gsm's round-robin needs no more rounds than Kleene needs steps. *)
  Theorem rounds_reach_by_kleene : MonoN -> forall l m, is_lfp NLE (PhiN l) m ->
    forall k, iter (PhiN l) BOT k = m -> iter (round l) BOT k = m.
  Proof.
    intros Hm l m [Hf _] k Hk. apply NLE_antisym.
    - apply (rounds_below_fixed Hm l m Hf).
    - rewrite <- Hk. exact (proj1 (rounds_ge_iter Hm l k)).
  Qed.

  (* (c) on the network, exact: some finite chaotic schedule reaches the lfp iff Kleene
     iteration reaches it iff gsm's round-robin sweeps reach it. *)
  Theorem chaotic_reach_exact : MonoN -> forall l m, is_lfp NLE (PhiN l) m ->
    ((exists js, sweepN l js BOT = m) <-> (exists k, iter (PhiN l) BOT k = m)) /\
    ((exists k, iter (PhiN l) BOT k = m) <-> (exists r, iter (round l) BOT r = m)).
  Proof.
    intros Hm l m Hlfp.
    assert (Kc : forall js, sweepN l js BOT = m -> iter (PhiN l) BOT (length js) = m).
    { intros js Hjs. apply NLE_antisym.
      - apply (iter_below_fixed NLE (PhiN l) (Hm l) BOT BOT_least m (proj1 Hlfp)).
      - rewrite <- Hjs. rewrite <- (Nat.add_0_r (length js)).
        apply sweep_below_iter; [exact Hm | apply BOT_least | apply NLE_refl]. }
    assert (Rc : forall r, iter (round l) BOT r = m -> exists js, sweepN l js BOT = m).
    { intros r Hr. exists (reps r). rewrite sweep_reps. exact Hr. }
    split; split.
    - intros [js Hjs]. exists (length js). apply Kc. exact Hjs.
    - intros [k Hk]. apply (Rc k). exact (rounds_reach_by_kleene Hm l m Hlfp k Hk).
    - intros [k Hk]. exists k. exact (rounds_reach_by_kleene Hm l m Hlfp k Hk).
    - intros [r Hr]. destruct (Rc r Hr) as [js Hjs]. exists (length js). apply Kc. exact Hjs.
  Qed.

  (* ---- The cyclic normalizer (finite height), as in MonotoneFederation.net_Ncyc_correct. ---- *)
  Variable rank : Sh -> nat.
  Hypothesis rank_strict : forall x y, NLE x y -> x <> y -> rank x < rank y.
  Variable height : nat.
  Hypothesis rank_bound : forall x, rank x <= height.
  Variable sh_eq_dec : forall x y : Sh, {x = y} + {x <> y}.
  Variable rho1 : Loc * Sh -> Loc * Sh.
  Variable K : nat.
  Hypothesis K_big : height < K.

  Local Notation NnetN := (Nnet botS n get tab lst srcs Gam sh_eq_dec rho1 K).

  Lemma Nnet_lfp : MonoN -> forall t,
    fst (NnetN t) = fst (rho1 t) /\ is_lfp NLE (PhiN (fst (rho1 t))) (snd (NnetN t)).
  Proof.
    intros Hm t.
    exact (cyc_N_lfp Loc Sh NLE NLE_refl NLE_trans BOT BOT_least rank rank_strict height rank_bound
             sh_eq_dec PhiN nuN (nu_incr leS leS_refl n get tab get_tab lst srcs Gam)
             (nu_sound leS leS_refl leS_trans n get tab get_tab lst srcs Gam Hm)
             (nu_mono leS n get tab get_tab lst srcs Gam Hm)
             (nu_fixed n get tab get_tab sh_ext lst srcs Gam) rho1 K K_big (seq 0 n)
             (nu_cover n get tab get_tab sh_ext lst srcs Gam) t).
  Qed.

  (* (a) for gsm's normalizer, exact and per input: the cyclic normal form of t is federally
     valid iff some Kleene iterate from bottom, at t's Phase-1 locals, is valid. *)
  Theorem Ncyc_valid_exact : MonoN -> R2N -> (forall t, LocV (fst (rho1 t))) ->
    forall t, FV (fst (NnetN t)) (snd (NnetN t)) <->
              exists k, LV (fst (rho1 t)) (iter (PhiN (fst (rho1 t))) BOT k).
  Proof.
    intros Hm HR Hl t. destruct (Nnet_lfp Hm t) as [Hf Hlfp]. rewrite Hf.
    exact (lfp_valid_exact HR Hm (finite_height_acc NLE rank height rank_strict rank_bound)
             sh_eq_dec (fst (rho1 t)) (Hl t) _ Hlfp).
  Qed.

  (* (b) for gsm's normalizer: gsm's check makes every normal form federally valid, with no
     bottom-validity (and no R2) hypothesis. *)
  Theorem gsm_check_Ncyc_valid : MonoN -> GsmCheck -> (forall t, LocV (fst (rho1 t))) ->
    forall t, FV (fst (NnetN t)) (snd (NnetN t)).
  Proof.
    intros Hm HG Hl t. destruct (Nnet_lfp Hm t) as [Hf Hlfp]. rewrite Hf.
    exact (gsm_check_lfp_valid HG (fst (rho1 t)) (Hl t) _ Hlfp).
  Qed.
End NetExact.

(* ======================================================================================= *)
(* Part 3. Instances: bottom validity and gsm's check are each sufficient, not necessary,   *)
(* and incomparable; the reachability qualifier is needed; SN of chaotic steps is stronger. *)
(* ======================================================================================= *)

(* (i) Bottom invalid, gsm's check passes, the lfp is valid. The 2-cycle on bool * bool of
   MonotoneFederation (valid iff the flag is set), with constant-true morphisms. *)
Definition ctGam (_ : nat) (_ : list (bool * unit)) : bool := true.
Definition PhiC : unit -> bool * bool -> bool * bool := Phi bget btab lone bsrcs ctGam.

Lemma PhiC_true : forall l x, PhiC l x = (true, true).
Proof. intros l [a b]. reflexivity. Qed.

Lemma ct_mono : Mono bleq 2 bget btab lone bsrcs ctGam.
Proof.
  intros l x y _. fold PhiC. rewrite !PhiC_true. apply nle2_iff. split; apply bleq_refl.
Qed.

Definition rho1c (t : unit * (bool * bool)) : unit * (bool * bool) := t.

Theorem bottom_validity_not_necessary :
  Mono bleq 2 bget btab lone bsrcs ctGam /\ R2 2 Vflag bsrcs ctGam /\
  LocValid 2 lone Vflag tt /\ GsmCheck 2 Vflag bsrcs ctGam /\
  ~ LValid 2 bget lone Vflag tt (nbot false btab) /\
  is_lfp (nle bleq 2 bget) (PhiC tt) (true, true) /\
  FedValid 2 bget btab lone Vflag bsrcs ctGam tt (true, true) /\
  LValid 2 bget lone Vflag tt (iter (PhiC tt) (nbot false btab) 1) /\
  (forall t, FedValid 2 bget btab lone Vflag bsrcs ctGam
               (fst (Nnet false 2 bget btab lone bsrcs ctGam beq2_dec rho1c 3 t))
               (snd (Nnet false 2 bget btab lone bsrcs ctGam beq2_dec rho1c 3 t))).
Proof.
  assert (HG : GsmCheck 2 Vflag bsrcs ctGam) by (intros j _ _ f _ t _; reflexivity).
  assert (Hl : LocValid 2 lone Vflag tt) by (intros j _; reflexivity).
  split; [exact ct_mono |].
  split; [intros j _ _ f _ t _; reflexivity |].
  split; [exact Hl |]. split; [exact HG |].
  split; [intros Hv; specialize (Hv 0 ltac:(lia)); discriminate Hv |].
  split.
  { split; [reflexivity |]. intros x Hx. unfold fixed_point in Hx. rewrite PhiC_true in Hx.
    subst x. apply nle2_iff. split; apply bleq_refl. }
  split; [split; [intros [| [| j]] Hj; [reflexivity | reflexivity | lia] | reflexivity] |].
  split; [intros [| [| j]] Hj; [reflexivity | reflexivity | lia] |].
  intros t.
  apply (gsm_check_Ncyc_valid bleq bleq_refl bleq_trans false bleq_bot 2 bget btab
           bget_tab bsh_ext lone Vflag bsrcs ctGam bsrcs_range brank brank_strict 2 brank_bound
           beq2_dec rho1c 3 ltac:(lia) ct_mono HG).
  intros [[] x] j _. reflexivity.
Qed.

(* (ii) gsm's check fails, bottom is valid, the lfp is valid. The 2-cycle of identity morphisms,
   valid iff the flag is CLEAR: gsm's check visits the source state with the flag set, whose
   image is invalid, although the iteration never leaves (false, false). *)
Definition Vclear (_ : nat) (t : bool * unit) : Prop := fst t = false.
Definition lclear (_ : unit) (_ : nat) : bool * unit := (false, tt).
Definition PhiI : unit -> bool * bool -> bool * bool := Phi bget btab lclear bsrcs idGam.

Lemma PhiI_swap : forall l x, PhiI l x = (snd x, fst x).
Proof. intros l [a b]. reflexivity. Qed.

Lemma clear_mono : Mono bleq 2 bget btab lclear bsrcs idGam.
Proof.
  intros l x y H. fold PhiI. rewrite !PhiI_swap. apply nle2_iff in H. apply nle2_iff.
  simpl. tauto.
Qed.

Theorem gsm_check_not_necessary :
  Mono bleq 2 bget btab lclear bsrcs idGam /\ R2 2 Vclear bsrcs idGam /\
  LocValid 2 lclear Vclear tt /\ LValid 2 bget lclear Vclear tt (nbot false btab) /\
  is_lfp (nle bleq 2 bget) (PhiI tt) (false, false) /\
  FedValid 2 bget btab lclear Vclear bsrcs idGam tt (false, false) /\
  ~ GsmCheck 2 Vclear bsrcs idGam.
Proof.
  split; [exact clear_mono |].
  split.
  { intros [| [| j]] Hj Hne f Hf t Ht; unfold Vclear; simpl;
      [apply (Hf 1); left; reflexivity | apply (Hf 0); left; reflexivity | lia]. }
  split; [intros j _; reflexivity |].
  split; [intros [| [| j]] Hj; [reflexivity | reflexivity | lia] |].
  split; [split; [reflexivity | intros x _; apply nle2_iff; split; apply bleq_bot] |].
  split; [split; [intros [| [| j]] Hj; [reflexivity | reflexivity | lia] | reflexivity] |].
  intros HG.
  assert (Hv : Vis Vclear bsrcs 0 (false, tt)) by (exists (false, tt); split; reflexivity).
  pose proof (HG 0 ltac:(lia) ltac:(discriminate) (fun _ => (true, tt))) as H.
  specialize (H ltac:(intros i [<- | []]; exists (false, tt); split; reflexivity) (false, tt) Hv).
  discriminate H.
Qed.

(* (iii) The reachability qualifier of lfp_valid_iff_reached is needed. One component on the
   chain w+2 with a self-loop whose morphism is the continuous successor wPhic, valid iff the
   shared value is not w: R2 holds and every Kleene iterate n is valid, but the lfp w is never
   reached and is invalid. (gsm's check rejects this network: the visited shared value w maps
   to the invalid w, so GsmCheck fails, consistently with gsm_check_lfp_valid.) *)
Definition wget (_ : nat) (x : W) : W := x.
Definition wtab (g : nat -> W) : W := g 0.
Definition wlst (_ : unit) (_ : nat) : W * unit := (Fin 0, tt).
Definition wsrcs (_ : nat) : list nat := [0].
Definition wGam (_ : nat) (ts : list (W * unit)) : W :=
  match ts with [t] => wPhic (fst t) | _ => Fin 0 end.
Definition Vw (_ : nat) (t : W * unit) : Prop := fst t <> Om.
Definition PhiW : unit -> W -> W := Phi wget wtab wlst wsrcs wGam.

Lemma PhiW_eq : forall l x, PhiW l x = wPhic x.
Proof. reflexivity. Qed.

Lemma nle1_iff : forall x y, nle wle 1 wget x y <-> wle x y.
Proof.
  intros x y. split; [intros H; exact (H 0 ltac:(lia)) | intros H [| j] Hj; [exact H | lia]].
Qed.

Theorem lfp_valid_iff_needs_reach :
  Mono wle 1 wget wtab wlst wsrcs wGam /\ R2 1 Vw wsrcs wGam /\ LocValid 1 wlst Vw tt /\
  is_lfp (nle wle 1 wget) (PhiW tt) Om /\
  (forall k, iter (PhiW tt) (nbot (Fin 0) wtab) k = Fin k) /\
  (forall k, LValid 1 wget wlst Vw tt (iter (PhiW tt) (nbot (Fin 0) wtab) k)) /\
  ~ FedValid 1 wget wtab wlst Vw wsrcs wGam tt Om /\
  ~ GsmCheck 1 Vw wsrcs wGam.
Proof.
  assert (Hit : forall k, iter (PhiW tt) (nbot (Fin 0) wtab) k = Fin k).
  { induction k as [| k IH]; [reflexivity |]. simpl. rewrite IH. reflexivity. }
  destruct kleene_sup_instance as [[Hfix Hleast] _].
  split.
  { intros l x y H. fold PhiW. rewrite !PhiW_eq. apply nle1_iff. apply nle1_iff in H.
    apply wPhic_mono. exact H. }
  split.
  { intros [| j] Hj Hne f Hf t _; [| lia]. unfold Vw. simpl.
    specialize (Hf 0 (or_introl eq_refl)). unfold Vw in Hf.
    destruct (fst (f 0)) as [k | |]; simpl; [discriminate | contradiction | discriminate]. }
  split; [intros [| j] Hj; [discriminate | lia] |].
  split.
  { split; [exact Hfix |]. intros x Hx. unfold fixed_point in Hx. rewrite PhiW_eq in Hx.
    apply nle1_iff. apply Hleast. exact Hx. }
  split; [exact Hit |].
  split; [intros k; rewrite Hit; intros [| j] Hj; [discriminate | lia] |].
  split; [intros [Hv _]; exact (Hv 0 ltac:(lia) eq_refl) |].
  intros HG.
  assert (Hv : Vis Vw wsrcs 0 (Om, tt)) by (exists (Fin 0, tt); split; [discriminate | reflexivity]).
  exact (HG 0 ltac:(lia) ltac:(discriminate) (fun _ => (Om, tt))
            ltac:(intros i [<- | []]; exact Hv) (Om, tt) Hv eq_refl).
Qed.

(* (iv) "Every chaotic schedule terminates" (SN of productive coordinate updates from bottom)
   is strictly stronger than "the lfp is reached" (chaotic_reach_exact). Two components on the
   chain w+2: component 1 is a source with shared value 1; component 0 reads (a, b) = (its own
   shared value, component 1's) through g: while b = 0 it takes the successor of a, once b > 0
   it jumps to w. Kleene and gsm's round-robin reach the lfp (w, 1) in two steps, but updating
   component 0 alone climbs 0 < 1 < 2 < ... forever. *)
Definition gW (a b : W) : W :=
  match b with
  | Fin 0 => wPhic a
  | _ => match a with Om1 => Om1 | _ => Om end
  end.

Definition pget (j : nat) (x : W * W) : W := match j with 0 => fst x | _ => snd x end.
Definition ptab (g : nat -> W) : W * W := (g 0, g 1).
Definition plst (_ : unit) (j : nat) : W * unit := match j with 0 => (Fin 0, tt) | _ => (Fin 1, tt) end.
Definition psrcs (j : nat) : list nat := match j with 0 => [0; 1] | _ => [] end.
Definition pGam (_ : nat) (ts : list (W * unit)) : W :=
  match ts with [ta; tb] => gW (fst ta) (fst tb) | _ => Fin 0 end.
Definition PhiP : unit -> W * W -> W * W := Phi pget ptab plst psrcs pGam.
Definition nuP : unit -> nat -> W * W -> W * W := nu pget ptab plst psrcs pGam.

Lemma PhiP_eq : forall l x, PhiP l x = (gW (fst x) (snd x), Fin 1).
Proof. intros l [a b]. reflexivity. Qed.

Lemma nle2w_iff : forall x y, nle wle 2 pget x y <-> wle (fst x) (fst y) /\ wle (snd x) (snd y).
Proof.
  intros x y. split.
  - intros H. split; [apply (H 0) | apply (H 1)]; lia.
  - intros [H0 H1] [| [| j]] Hj; [exact H0 | exact H1 | lia].
Qed.

Lemma gW_mono : forall a a' b b', wle a a' -> wle b b' -> wle (gW a b) (gW a' b').
Proof.
  intros a a' b b' Ha Hb.
  destruct b as [[| b] | |], b' as [[| b'] | |]; unfold wle in Hb; simpl in Hb; try discriminate;
    simpl; try (apply wPhic_mono; exact Ha);
    destruct a as [a | |], a' as [a' | |]; unfold wle in *; simpl in *; try discriminate; reflexivity.
Qed.

Lemma PhiP_mono : Mono wle 2 pget ptab plst psrcs pGam.
Proof.
  intros l x y H. fold PhiP. rewrite !PhiP_eq. apply nle2w_iff in H. apply nle2w_iff.
  simpl. split; [apply gW_mono; tauto | apply wle_refl].
Qed.

Lemma nuP_climb : forall k, nuP tt 0 (Fin k, Fin 0) = (Fin (S k), Fin 0).
Proof. reflexivity. Qed.

Theorem chaotic_sn_strictly_stronger :
  Mono wle 2 pget ptab plst psrcs pGam /\
  is_lfp (nle wle 2 pget) (PhiP tt) (Om, Fin 1) /\
  iter (PhiP tt) (nbot (Fin 0) ptab) 2 = (Om, Fin 1) /\
  sweep unit (W * W) nuP tt [0; 1; 0; 1] (nbot (Fin 0) ptab) = (Om, Fin 1) /\
  ~ SN (Chaotic.step nat (nuP tt)) (nbot (Fin 0) ptab).
Proof.
  split; [exact PhiP_mono |].
  split.
  { split; [reflexivity |]. intros [a b] Hx. unfold fixed_point in Hx. rewrite PhiP_eq in Hx.
    simpl in Hx. injection Hx as Ha Hb. subst b. apply nle2w_iff. simpl. split; [| apply wle_refl].
    destruct a as [a | |]; simpl in Ha; [discriminate | reflexivity | reflexivity]. }
  split; [reflexivity |]. split; [reflexivity |].
  intros Hsn.
  assert (H : forall x, SN (Chaotic.step nat (nuP tt)) x -> forall k, x = (Fin k, Fin 0) -> False).
  { intros x Hx. induction Hx as [x _ IH]. intros k ->.
    apply (IH (Fin (S k), Fin 0)) with (k := S k); [| reflexivity].
    exists 0. split; [symmetry; apply nuP_climb | intro E; injection E; lia]. }
  exact (H _ Hsn 0 eq_refl).
Qed.
