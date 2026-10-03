(* Extract the verified checkers as MiniML JSON for gogen: the same entry points
   as extraction/Extract.v (check_fn and check_fast, the table oracle;
   checkBuildC, the rules oracle, checkBuildT and checkBuild, which it is
   proven equal to, and the parts its front end reports), with ExtrGo.v's directives in
   place of ExtrOcamlBasic, ExtrOcamlNatInt and ExtrOcamlZInt. gogen turns
   oracle_core.json into oracle/oracle_gen.go. *)
From Coq Require Import Extraction.
Require Import NC.goextract.ExtrGo.
Require Import NC.TableFast.
Require Import NC.TableFn.
Require Import NC.AstChecker.
Require Import NC.AstTables.
Require Import NC.AstCompact.

Extraction Language JSON.
Extraction "goextract/oracle_core.json" check_fn check_fast checkBuildC checkBuildT checkBuild wfc bounded signSafe compensationFree.
