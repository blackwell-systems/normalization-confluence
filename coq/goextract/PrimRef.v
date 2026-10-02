(* The reference side of gogen's prim check (primcheck/).

   ExtrGo.v maps some Rocq constants and inductives to fixed Go definitions
   (gogen/prims.go). Those Go definitions are trusted unless checked. This file
   names each mapped constant once (ref_<prim>), and adds probes that build and
   match every mapped inductive's constructors. It is extracted twice:
     - ExtractPrimMapped.v, under ExtrGo.v: every ref_<prim> is the Go prim
       itself, and the probes run on the int64 representation;
     - ExtractPrimPlain.v, with no directives: every ref_<prim> and probe is the
       Rocq definition, computed on the inductive representation (unary nat,
       binary positive).
   primcheck compares the two on many inputs. A prim or a mapped constructor
   whose Go meaning differs from its Rocq definition shows up as a mismatch.

   It must not Require ExtrGo.v, so that the plain extraction sees no directive;
   it uses the same references ExtrGo.v maps, in the same Require context. *)
From Coq Require Import PeanoNat Peano_dec EqNat Euclid.
From Coq Require Import BinNat BinInt.
From Coq Require Import List.
Import ListNotations.

(* ===== one reference per mapped constant ===== *)

Definition ref_andb := andb.

Definition ref_nat_add := plus.
Definition ref_nat_sub := minus.
Definition ref_nat_mul := mult.
Definition ref_nat_eqb := Nat.eqb.
Definition ref_nat_compare := Nat.compare.
Definition ref_nat_ltb (a b : nat) : bool := if Compare_dec.lt_dec a b then true else false.
Definition ref_nat_div2 := Nat.div2.
Definition ref_nat_pred := pred.
Definition ref_nat_max := max.
Definition ref_nat_min := min.
Definition ref_nat_eq_nat_decide (a b : nat) : bool := if EqNat.eq_nat_decide a b then true else false.
Definition ref_nat_eq_nat_dec (a b : nat) : bool := if Peano_dec.eq_nat_dec a b then true else false.
Definition ref_nat_leb := Compare_dec.leb.
Definition ref_nat_le_lt_dec (a b : nat) : bool := if Compare_dec.le_lt_dec a b then true else false.

Definition ref_pos_add := Pos.add.
Definition ref_pos_succ := Pos.succ.
Definition ref_pos_pred := Pos.pred.
Definition ref_pos_sub := Pos.sub.
Definition ref_pos_mul := Pos.mul.
Definition ref_pos_min := Pos.min.
Definition ref_pos_max := Pos.max.
Definition ref_pos_compare := Pos.compare.
Definition ref_pos_compare_cont := Pos.compare_cont.

Definition ref_n_add := N.add.
Definition ref_n_succ := N.succ.
Definition ref_n_pred := N.pred.
Definition ref_n_sub := N.sub.
Definition ref_n_mul := N.mul.
Definition ref_n_min := N.min.
Definition ref_n_max := N.max.
Definition ref_n_div := N.div.
Definition ref_n_modulo := N.modulo.
Definition ref_n_compare := N.compare.

Definition ref_z_add := Z.add.
Definition ref_z_succ := Z.succ.
Definition ref_z_pred := Z.pred.
Definition ref_z_sub := Z.sub.
Definition ref_z_mul := Z.mul.
Definition ref_z_opp := Z.opp.
Definition ref_z_abs := Z.abs.
Definition ref_z_min := Z.min.
Definition ref_z_max := Z.max.
Definition ref_z_compare := Z.compare.
Definition ref_z_of_n := Z.of_N.
Definition ref_z_abs_n := Z.abs_N.

(* ===== probes: build and match every mapped constructor ===== *)

(* nat: O and S, built and matched. *)
Fixpoint probe_nat (n : nat) : nat * bool :=
  match n with
  | O => (O, true)
  | S k => let (d, _) := probe_nat k in (S (S d), false)
  end.

(* positive: the bits, least significant first, and back. *)
Fixpoint probe_pos_bits (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: probe_pos_bits q
  | xI q => true :: probe_pos_bits q
  end.

Fixpoint probe_pos_mk (bits : list bool) : positive :=
  match bits with
  | [] => xH
  | false :: t => xO (probe_pos_mk t)
  | true :: t => xI (probe_pos_mk t)
  end.

(* N and Z: the constructor and its argument, and back. *)
Definition probe_n (n : N) : nat * positive :=
  match n with N0 => (0, xH) | Npos p => (1, p) end.

Definition probe_n_mk (tag : nat) (p : positive) : N :=
  match tag with 0 => N0 | _ => Npos p end.

Definition probe_z (z : Z) : nat * positive :=
  match z with Z0 => (0, xH) | Zpos p => (1, p) | Zneg p => (2, p) end.

Definition probe_z_mk (tag : nat) (p : positive) : Z :=
  match tag with 0 => Z0 | 1 => Zpos p | _ => Zneg p end.

(* bool and sumbool: constructors and matches. *)
Definition probe_bool (b : bool) : nat := if b then 1 else 0.
Definition probe_sumbool (a b : nat) : nat := if Compare_dec.lt_dec a b then 1 else 0.
