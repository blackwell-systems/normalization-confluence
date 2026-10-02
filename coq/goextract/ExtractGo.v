(* Extract the verified checkers as MiniML JSON for gogen (goextract/gogen):
   - fast_core.json: check_fast (TableFast.v), the table oracle;
   - ast_core.json: checkBuild and the parts its front end reports (wfc,
     bounded, signSafe, compensationFree) (AstChecker.v), the rules oracle, plus
     check_tables and of_list (TableCheck.v);
   the same entry points as Extract.v and ExtractFast.v, with the directives of
   ExtrGo.v in place of ExtrOcamlBasic, ExtrOcamlNatInt and ExtrOcamlZInt. *)
From Coq Require Import Extraction.
Require Import NC.goextract.ExtrGo.
Require Import NC.TableCheck.
Require Import NC.TableFast.
Require Import NC.AstChecker.

Extraction Language JSON.
Extraction "goextract/fast_core.json" check_fast.
Extraction "goextract/ast_core.json" check_tables of_list checkBuild wfc bounded signSafe compensationFree.
