(* Extract the verified checkers to OCaml. nat and Z are mapped to OCaml int for
   speed. The mapping is exact only while values stay inside OCaml's 63-bit int:
   the front ends cap every input integer at 2^31-1 in magnitude and the input
   file at 64 MiB, so no sum the checker computes (bnd adds at most one leaf bound
   per input token) can reach 2^62, and check rejects any machine whose expression
   values could leave 32-bit range (check_no_overflow).
   Two entry points, both machine-checked axiom-free:
     - check_commuting / closed (Checker.v): certify a machine's output STEP TABLES
       converge (the table oracle).
     - check (AstChecker.v): certify a combinator machine straight from its RULES
       (the AST oracle) -- it recomputes each event's step function by evaluating
       the expression trees, so it does not trust gsm to have produced correct
       tables at all.
     - bounded, signSafe (AstChecker.v): the fragment checks (32-bit arithmetic;
       no possibly negative write into a two-valued variable with minimum 0),
       which check already includes; extracted so the front end can name the
       reason.
     - compensationFree (AstChecker.v): certify that a machine is in the CRDT
       fragment (no in-domain state ever needs repair), so the CRDT classification
       is checked from the rules, not asserted. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
From Coq Require Import ExtrOcamlZInt.
Require Import NC.Checker.
Require Import NC.AstChecker.

Extraction "extraction/checker_core.ml" check_commuting closed check bounded signSafe compensationFree.
