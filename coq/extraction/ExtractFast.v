(* SPIKE (spike/checker-perf): extract the fast table oracle, check_fast
   (TableFast.v), proven equal to check_tables (check_fast_eq). Same extraction
   directives as Extract.v, nothing added. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
From Coq Require Import ExtrOcamlZInt.
Require Import NC.TableFast.

Extraction "extraction/fast_core.ml" check_fast.
