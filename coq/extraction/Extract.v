(* Extract the verified checkers to OCaml. nat is mapped to OCaml int for speed.
   Two entry points, both machine-checked axiom-free:
     - check_commuting / closed (Checker.v): certify a machine's output STEP TABLES
       converge (the table oracle).
     - check (AstChecker.v): certify a combinator machine straight from its RULES
       (the AST oracle) -- it recomputes each event's step function by evaluating
       the expression trees, so it does not trust gsm to have produced correct
       tables at all.
     - compensationFree (AstChecker.v): certify that a machine is in the CRDT
       fragment (no in-domain state ever needs repair), so the CRDT classification
       is checked from the rules, not asserted. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
Require Import NC.Checker.
Require Import NC.AstChecker.

Extraction "extraction/checker_core.ml" check_commuting closed check compensationFree.
