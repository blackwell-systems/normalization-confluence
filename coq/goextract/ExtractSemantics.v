(* Semantics.v under ExtrGo.v, for semantics/ (gogen's semantic regression test). *)
From Coq Require Import Extraction.
Require Import NC.goextract.ExtrGo.
Require Import NC.goextract.Semantics.

Extraction Language JSON.
Extraction "goextract/semantics.json" t_clos t_swap t_mut t_shadow t_zdiv t_nat t_pa t_poly t_big t_and t_cmp t_z t_n t_pos t_dec t_rec t_opt t_comp t_sort t_unused t_exn.
