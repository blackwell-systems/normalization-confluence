(* Programs whose Go translation must compute what Rocq computes: closures in
   loops, tail calls that swap arguments, mutual recursion, shadowing,
   unmapped Z/N/positive/nat arithmetic (division, modulo, pow, sqrt, log2,
   bit operations), partial and over-application, polymorphism, many-argument
   constructors with default branches, andb, comparisons, values at the int64
   edges, sumbool, records of functions, options, unused
   arguments and absurd branches. semantics/semantics_test.go compares the
   generated Go with SemanticsCompute.v's Compute output (semantics/compute.out).
   From the adversarial review of the Go oracle. *)
From Coq Require Import List BinInt BinNat BinPos PeanoNat Bool ZArith.
Import ListNotations.
Open Scope list_scope.

(* 1. closures in a loop capturing pattern-bound and let-bound values *)
Fixpoint mk (l : list nat) (acc : list (nat -> nat)) : list (nat -> nat) :=
  match l with
  | [] => acc
  | x :: t => let y := x * 3 in mk t ((fun z => z + x + y) :: acc)
  end.
Definition t_clos : list nat := map (fun f => f 100) (mk [1;2;3;4] []).

(* 2. tail call swapping arguments *)
Fixpoint swapper (n a b : nat) : nat * nat :=
  match n with 0 => (a, b) | S k => swapper k b (a + 1) end.
Definition t_swap : list nat := let (a, b) := swapper 7 1 20 in [a; b].

(* 3. mutual recursion *)
Fixpoint ev (n : nat) : bool := match n with 0 => true | S k => od k end
with od (n : nat) : bool := match n with 0 => false | S k => ev k end.
Definition t_mut : list bool := [ev 10; od 10; ev 7; od 7].

(* 4. shadowing *)
Definition shadow (x : nat) : nat := let x := x + 1 in (fun x => x * 2) (x + 10).
Definition t_shadow : list nat := [shadow 5].

(* 5. Z division and modulo on negatives (unmapped, extracted as definitions) *)
Definition t_zdiv : list Z := [Z.div (-7) 2; Z.modulo (-7) 2; Z.div 7 (-2); Z.modulo 7 (-2); Z.quot (-7) 2; Z.rem (-7) 2; Z.div (-7) 0; Z.modulo (-7) 0].

(* 6. nat sub truncation, pred, Nat.div/modulo *)
Definition t_nat : list nat := [3 - 5; pred 0; Nat.div 7 2; Nat.modulo 7 0; Nat.div 7 0; Nat.pow 2 5; Nat.sqrt 17; Nat.log2 1000].

(* 7. partial application and over-application *)
Definition f3 (a b c : nat) : nat := a * 100 + b * 10 + c.
Definition pa := f3 1.
Definition t_pa : list nat := [pa 2 3; (f3 4 5) 6; fold_left (fun acc g => acc + g 1 2) (map f3 [1;2]) 0 ].
(* map over partially applied global; tests closure creation order *)

(* 8. polymorphism at several instantiations *)
Definition twice {A} (f : A -> A) (x : A) : A := f (f x).
Definition t_poly : list nat := [twice S 3; if twice negb true then 1 else 0; length (twice (fun l => 0 :: l) [])].

(* 9. many-arg constructor and default branch *)
Inductive big := B (a b c d e f g h : nat) | C0 | C1 (x : nat) | C2.
Definition bigf (x : big) : nat := match x with B a b c d e f g h => a+b+c+d+e+f+g+h | C1 x => x | _ => 99 end.
Definition t_big : list nat := [bigf (B 1 2 3 4 5 6 7 8); bigf C0; bigf (C1 4); bigf C2].

(* 10. andb laziness / tail andb with self call *)
Fixpoint allpos (l : list Z) : bool := match l with [] => true | x :: t => Z.ltb 0 x && allpos t end.
Definition t_and : list bool := [allpos [1;2;3]%Z; allpos [1;-2;3]%Z; andb false (allpos [])].

(* 11. comparisons *)
Definition t_cmp : list bool := [Nat.ltb 3 3; Nat.leb 3 3; Z.leb (-1) 0; Z.eqb 5 5; Pos.eqb 4 4; N.ltb 2 3; Z.gtb 1 2].

(* 12. Z arithmetic boundaries near 2^62 *)
Definition t_z : list Z := [Z.mul 4611686018427387904 1; Z.sub (-4611686018427387904) 4611686018427387904; Z.abs (-9223372036854775807); Z.opp 9223372036854775807; Z.pow 2 62; Z.shiftl 1 62; Z.land 12 10; Z.lor 12 10; Z.lxor 12 10].

(* 13. N and positive *)
Definition t_n : list N := [N.sub 3 5; N.div 17 0; N.modulo 17 0; N.pred 0; N.of_nat 9; N.double 21; N.pow 3 4].
Definition t_pos : list positive := [Pos.sub 3 5; Pos.pred 1; Pos.add 4 5; Pos.mul 6 7; Pos.of_nat 0; Pos.of_succ_nat 4; Pos.pow 2 10].

(* 14. sumbool-driven matches *)
Definition t_dec : list nat := [if Nat.eq_dec 3 3 then 1 else 0; if Z.eq_dec 3 4 then 1 else 0; if Z_lt_dec (-1) 0 then 1 else 0].

(* 15. records with function fields *)
Record R := { rf : nat -> nat; rv : nat }.
Definition useR (r : R) := rf r (rv r).
Definition t_rec : list nat := [useR {| rf := fun x => x * x; rv := 9 |}].

(* 16. string-like inductive and option chains *)
Definition nth_err := @nth_error nat.
Definition t_opt : list nat := [match nth_err [5;6;7] 2 with Some x => x | None => 0 end; match nth_err [5] 4 with Some x => x | None => 42 end].

(* 17. let-bound closure applied multiple times + tail loop with accumulator closure *)
Fixpoint compose_n (n : nat) (f : nat -> nat) : nat -> nat :=
  match n with 0 => f | S k => compose_n k (fun x => f (x + n)) end.
Definition t_comp : list nat := [compose_n 5 (fun x => x) 0; compose_n 3 S 10].

(* 18. rev, app, sort-ish *)
Fixpoint ins (x : nat) (l : list nat) := match l with [] => [x] | y :: t => if Nat.leb x y then x :: l else y :: ins x t end.
Definition t_sort : list nat := fold_right ins [] [5;3;9;1;3;0;7].

(* 20. unused arguments, an absurd branch never taken. (A local fixpoint in
   argument position extracts to expr:fix, which gogen refuses: see
   gogen/testdata/refuse.) *)
Definition r_unused (_ _ : nat) : nat := 7.
Definition t_unused : list nat := [r_unused 1 2].
Definition hd_safe (l : list nat) : l <> [] -> nat :=
  match l return l <> [] -> nat with [] => fun H => False_rect _ (H eq_refl) | x :: _ => fun _ => x end.
Definition t_exn : list nat := [hd_safe [4] (fun H => match H with end)].
