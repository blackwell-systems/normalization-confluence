(* guard.sh's self-test: a coinductive type and a cofixpoint, which gogen cannot
   translate (JSON extraction prints them as an ordinary inductive and a
   recursive value, and the Go would recurse forever). guard.sh must refuse it. *)
From Coq Require Import Extraction.
CoInductive stream := SCons : nat -> stream -> stream.
CoFixpoint ones : stream := SCons 1 ones.
Definition shd (s : stream) : nat := match s with SCons x _ => x end.
Definition r_coind : nat := shd ones.
Extraction Language OCaml.
Recursive Extraction r_coind.
