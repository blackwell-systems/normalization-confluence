(* Fixture.v under ExtrGo.v, for gogen's end-to-end test (fixture/). *)
From Coq Require Import Extraction.
Require Import NC.goextract.ExtrGo.
Require Import NC.goextract.Fixture.

Extraction Language JSON.
Extraction "goextract/fixture.json" fx_let fx_nat_wild fx_z_wild fx_pos_rel fx_list_wild fx_over fx_closures fx_partial.
