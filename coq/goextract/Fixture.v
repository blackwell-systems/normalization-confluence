(* Programs that exercise the parts of gogen the checkers' extraction does not
   reach (a let outside tail position, wildcard and variable patterns on mapped
   numbers, over-application, closures built inside a tail-recursive loop), so
   every emission path is run by a test (fixture/fixture_test.go). Extracted
   under ExtrGo.v by ExtractFixture.v. *)
From Coq Require Import List.
From Coq Require Import BinInt.
Import ListNotations.

(* A let whose value is used outside tail position. *)
Definition fx_let (n : nat) : nat := S (let m := n + n in m * m).

(* Wildcard and variable patterns on mapped numbers. *)
Definition fx_nat_wild (n : nat) : nat := match n with 3 => 1 | _ => 0 end.
Definition fx_z_wild (z : Z) : nat := match z with Z0 => 0 | Zpos _ => 1 | _ => 2 end.
Definition fx_pos_rel (p : positive) : positive :=
  match p with xH => xH | q => Pos.succ q end.

(* A wildcard on an ordinary inductive. *)
Definition fx_list_wild (l : list nat) : nat := match l with [] => 0 | _ => 1 end.

(* A global of arity one returning a function, applied to two arguments. *)
Definition fx_pick (b : bool) : nat -> nat := if b then S else (fun x => x).
Definition fx_over (n : nat) : nat := fx_pick true n + fx_pick false n.

(* Closures built in a tail-recursive loop must keep their own iteration's n. *)
Fixpoint fx_mkfs (n : nat) (acc : list (nat -> nat)) : list (nat -> nat) :=
  match n with 0 => acc | S k => fx_mkfs k ((fun x => x + n) :: acc) end.
Definition fx_closures (n : nat) : list nat := map (fun f => f 0) (fx_mkfs n []).

(* A partially applied global and constructor passed as functions. *)
Definition fx_partial (l : list nat) : list (nat * nat) := map (pair 7) (map (Nat.add 2) l).
