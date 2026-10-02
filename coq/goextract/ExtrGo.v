(* Extraction directives for gogen (goextract/gogen), the Go back end.

   They map exactly the constants Stdlib's ExtrOcamlBasic, ExtrOcamlNatInt and
   ExtrOcamlZInt map for the OCaml checkers, with the same references and the
   same Require context. Each constant maps to a distinct prim_* symbol, and each
   mapped inductive to a go_* type with its own constructor names. gogen gives
   every symbol a fixed Go meaning (prims and mapped types in gogen), and refuses
   any prim_* or go_* name it does not know.

   Nothing else is mapped. In particular PeanoNat's Nat.add, Nat.mul and Nat.pow,
   and Z.of_nat, Z.to_nat, Z.leb, Z.ltb and Z.eqb, stay as their Rocq
   definitions, as in the OCaml extraction.

   Require this file, then set Extraction Language JSON, then extract. *)
From Coq Require Extraction.
From Coq Require Import PeanoNat Peano_dec EqNat Euclid.
From Coq Require Import BinNat BinInt.

(* ExtrOcamlBasic (the parts the checkers use). *)
Extract Inductive bool => "go_bool" [ "true" "false" ].
Extract Inductive sumbool => "go_bool" [ "true" "false" ].
Extract Inlined Constant andb => "prim_andb".

(* ExtrOcamlNatInt. *)
Extract Inductive nat => "go_nat" [ "nat_0" "nat_succ" ] "nat_case".
Extract Constant plus => "prim_nat_add".
Extract Constant minus => "prim_nat_sub".
Extract Constant mult => "prim_nat_mul".
Extract Inlined Constant Nat.eqb => "prim_nat_eqb".
Extract Constant Nat.compare => "prim_nat_compare".
Extract Inlined Constant Compare_dec.lt_dec => "prim_nat_ltb".
Extract Constant Nat.div2 => "prim_nat_div2".

(* ExtrOcamlZInt. *)
Extract Inductive positive => "go_pos" [ "pos_xI" "pos_xO" "pos_xH" ] "pos_case".
Extract Inductive Z => "go_z" [ "z_0" "z_pos" "z_neg" ] "z_case".
Extract Inductive N => "go_n" [ "n_0" "n_pos" ] "n_case".
Extract Constant Pos.add => "prim_pos_add".
Extract Constant Pos.succ => "prim_pos_succ".
Extract Constant Pos.pred => "prim_pos_pred".
Extract Constant Pos.sub => "prim_pos_sub".
Extract Constant Pos.mul => "prim_pos_mul".
Extract Constant Pos.min => "prim_pos_min".
Extract Constant Pos.max => "prim_pos_max".
Extract Constant Pos.compare => "prim_pos_compare".
Extract Constant Pos.compare_cont => "prim_pos_compare_cont".
Extract Constant N.add => "prim_n_add".
Extract Constant N.succ => "prim_n_succ".
Extract Constant N.pred => "prim_n_pred".
Extract Constant N.sub => "prim_n_sub".
Extract Constant N.mul => "prim_n_mul".
Extract Constant N.min => "prim_n_min".
Extract Constant N.max => "prim_n_max".
Extract Constant N.div => "prim_n_div".
Extract Constant N.modulo => "prim_n_modulo".
Extract Constant N.compare => "prim_n_compare".
Extract Constant Z.add => "prim_z_add".
Extract Constant Z.succ => "prim_z_succ".
Extract Constant Z.pred => "prim_z_pred".
Extract Constant Z.sub => "prim_z_sub".
Extract Constant Z.mul => "prim_z_mul".
Extract Constant Z.opp => "prim_z_opp".
Extract Constant Z.abs => "prim_z_abs".
Extract Constant Z.min => "prim_z_min".
Extract Constant Z.max => "prim_z_max".
Extract Constant Z.compare => "prim_z_compare".
Extract Constant Z.of_N => "prim_z_of_n".
Extract Constant Z.abs_N => "prim_z_abs_n".
