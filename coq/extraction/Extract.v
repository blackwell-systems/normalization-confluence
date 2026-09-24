(* Extract the verified checker to OCaml. nat is mapped to OCaml int for speed;
   the boolean checker and its closedness test are the extracted entry points. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
Require Import NC.Checker.

Extraction "extraction/checker_core.ml" check_commuting closed.
