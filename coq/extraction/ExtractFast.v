(* SPIKE (spike/checker-perf): extract the fast table oracle, check_fast
   (TableFast.v), proven equal to check_tables (check_fast_eq). Same extraction
   directives as Extract.v, nothing added. *)
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
Require Import NC.TableFast.

Extraction "extraction/fast_core.ml" check_fast.
