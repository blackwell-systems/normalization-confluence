(* SPIKE (spike/go-extraction): extract check_fast as JSON (MiniML) for the Go
   generator in goextract/gogen.

   The directives map exactly the constants ExtrOcamlBasic and ExtrOcamlNatInt
   map for the OCaml checker (same references, same Require context), to symbols
   the generator replaces with fixed Go definitions (prims in gogen/main.go).
   Nothing else is mapped: in particular PeanoNat's Nat.add, Nat.mul and Nat.pow
   stay recursive, as in the OCaml extraction. *)
From Stdlib Require Extraction.
From Stdlib Require Import PeanoNat Peano_dec EqNat Euclid.
Require Import NC.TableFast.

Extraction Language JSON.

(* ExtrOcamlBasic (the parts check_fast uses). *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inlined Constant andb => "prim_andb".

(* ExtrOcamlNatInt. *)
Extract Inductive nat => "nat" [ "0" "nat_succ" ] "nat_case".
Extract Constant plus => "prim_add".
Extract Constant minus => "prim_sub".
Extract Constant mult => "prim_mul".
Extract Inlined Constant Nat.eqb => "prim_eqb".
Extract Constant Nat.compare => "prim_compare".
Extract Inlined Constant Compare_dec.lt_dec => "prim_ltb".
Extract Constant Nat.div2 => "prim_div2".

Extraction "goextract/fast_core.json" check_fast.
