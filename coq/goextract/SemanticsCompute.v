(* Rocq's own values for Semantics.v, the reference semantics/semantics_test.go
   compares the generated Go with. make json writes this file's output to
   semantics/compute.out. *)
Require Import NC.goextract.Semantics.
From Coq Require Import ZArith.
Compute t_clos.
Compute t_swap.
Compute t_mut.
Compute t_shadow.
Compute t_zdiv.
Compute t_nat.
Compute t_pa.
Compute t_poly.
Compute t_big.
Compute t_and.
Compute t_cmp.
Compute t_z.
Compute t_n.
Compute t_pos.
Compute t_dec.
Compute t_rec.
Compute t_opt.
Compute t_comp.
Compute t_sort.
Compute t_unused.
Compute t_exn.
