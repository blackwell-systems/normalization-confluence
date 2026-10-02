(* Everything gogen translates, extracted once more as OCaml for guard.sh.
   JSON extraction prints a coinductive type as an ordinary inductive and a
   cofixpoint as a recursive value, so gogen cannot tell them apart and its Go
   would recurse forever. OCaml extraction marks them with Lazy, which guard.sh
   refuses. Keep the entry points in step with ExtractGo.v, ExtractPrimMapped.v
   ExtractFixture.v and ExtractSemantics.v. *)
From Coq Require Import Extraction.
Require Import NC.TableFast.
Require Import NC.TableFn.
Require Import NC.AstChecker.
Require Import NC.goextract.PrimRef.
Require Import NC.goextract.Fixture.
Require Import NC.goextract.Semantics.

Extraction Language OCaml.
Recursive Extraction
  check_fn check_fast checkBuild wfc bounded signSafe compensationFree
  ref_andb ref_nat_add ref_nat_sub ref_nat_mul ref_nat_eqb ref_nat_compare ref_nat_ltb ref_nat_div2
  ref_nat_pred ref_nat_max ref_nat_min ref_nat_eq_nat_decide ref_nat_eq_nat_dec ref_nat_leb ref_nat_le_lt_dec
  ref_pos_add ref_pos_succ ref_pos_pred ref_pos_sub ref_pos_mul ref_pos_min ref_pos_max ref_pos_compare ref_pos_compare_cont
  ref_n_add ref_n_succ ref_n_pred ref_n_sub ref_n_mul ref_n_min ref_n_max ref_n_div ref_n_modulo ref_n_compare
  ref_z_add ref_z_succ ref_z_pred ref_z_sub ref_z_mul ref_z_opp ref_z_abs ref_z_min ref_z_max ref_z_compare ref_z_of_n ref_z_abs_n
  probe_nat probe_pos_bits probe_pos_mk probe_n probe_n_mk probe_z probe_z_mk probe_bool probe_sumbool
  fx_let fx_nat_wild fx_z_wild fx_pos_rel fx_list_wild fx_over fx_closures fx_partial
  t_clos t_swap t_mut t_shadow t_zdiv t_nat t_pa t_poly t_big t_and t_cmp t_z t_n t_pos t_dec t_rec t_opt t_comp t_sort t_unused t_exn.
