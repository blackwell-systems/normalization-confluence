(* Extract the verified checkers to OCaml. nat and Z are mapped to OCaml int for
   speed. The mapping is exact only while values stay inside OCaml's 63-bit int:
   the front ends cap every input integer at 2^31-1 in magnitude and the input
   file at 64 MiB, so no sum the checker computes (bnd adds at most one leaf bound
   per input token) can reach 2^62, and check rejects any machine whose expression
   values could leave 32-bit range (check_no_overflow).
   Entry points, all machine-checked axiom-free:
     - check_fast (TableFast.v): certify a machine's STEP TABLES against
       Build's property (the table oracle): normal forms land on valid states,
       every step lands on a valid state, and every declared pair commutes on the
       valid states and the zero state. check_fast_eq proves it equal to
       check_tables (TableCheck.v), so check_tables_converges holds for it
       (check_fast_converges). It builds its own cells and lookup trie from the
       lists.
     - checkBuild (AstChecker.v): certify a combinator machine straight from its
       RULES against Build's property (the rules oracle): repair terminates from
       every state, and every declared pair commutes on the valid states and the
       zero state under gsm's step (checkBuild_converges). It recomputes each
       event's step function by evaluating the expression trees, so it does not
       trust gsm to have produced correct tables at all.
     - wfc, bounded, signSafe (AstChecker.v): parts of checkBuild, extracted so
       the front end can name the reason for a rejection.
     - compensationFree (AstChecker.v): certify that a machine is in the CRDT
       fragment (no in-domain state ever needs repair), so the CRDT classification
       is checked from the rules, not asserted.
   check_commuting/closed (Checker.v) and check (AstChecker.v) remain proven but
   are no longer extracted: they decide stricter properties than Build's. A
   version-1 tables file is checked by check_fast with every pair declared and
   every state valid, which is exactly check_commuting && closed. *)
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlNatInt.
From Coq Require Import ExtrOcamlZInt.
Require Import NC.TableFast.
Require Import NC.AstChecker.

Extraction "extraction/checker_core.ml" check_fast checkBuild wfc bounded signSafe compensationFree.
