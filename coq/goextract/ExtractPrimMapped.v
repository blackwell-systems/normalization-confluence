(* PrimRef.v under ExtrGo.v's directives: every ref_<prim> is the Go prim and
   every probe runs on gogen's int64 representation. See PrimRef.v. *)
From Coq Require Import Extraction.
Require Import NC.goextract.ExtrGo.
Require Import NC.goextract.PrimRef.

Extraction Language JSON.
Extraction "goextract/primref_mapped.json"
  ref_andb ref_nat_add ref_nat_sub ref_nat_mul ref_nat_eqb ref_nat_compare ref_nat_ltb ref_nat_div2
  ref_pos_add ref_pos_succ ref_pos_pred ref_pos_sub ref_pos_mul ref_pos_min ref_pos_max ref_pos_compare ref_pos_compare_cont
  ref_n_add ref_n_succ ref_n_pred ref_n_sub ref_n_mul ref_n_min ref_n_max ref_n_div ref_n_modulo ref_n_compare
  ref_z_add ref_z_succ ref_z_pred ref_z_sub ref_z_mul ref_z_opp ref_z_abs ref_z_min ref_z_max ref_z_compare ref_z_of_n ref_z_abs_n
  probe_nat probe_pos_bits probe_pos_mk probe_n probe_n_mk probe_z probe_z_mk probe_bool probe_sumbool.
