(* Runnable front-end for the AST oracle: reads a combinator MACHINE (its rules,
   not its output tables) and certifies convergence by recomputing each event's
   step function straight from the expression trees, using the Coq-extracted,
   machine-checked Checker_core.checkBuildT (AstTables.v: it evaluates the rules
   once per state and event into step tables and scans them as check_fast does;
   checkBuildT_eq proves it equal to checkBuild). It checks the property gsm's Build
   checks: repair terminates from every state (WFC), and every declared pair of
   events commutes on every valid state and on the zero state, under gsm's step
   (apply the event if its guard holds, then normalize).

   Usage: astchecker <machine-file> [<pairs-file>]

   The optional pairs file names the event pairs declared independent (gsm's
   Registry.Independent), by event index in the machine file's order:
     pairs all                    every pair (the default without a pairs file)
     pairs k a1 b1 ... ak bk      only these pairs
   It is a separate file so the machine format, and every digest computed over
   it, stays unchanged. Without it every pair is checked, which is the stronger
   property, so a verdict without a pairs file holds for any declaration.

   Machine file format (S-expressions, whitespace-insensitive):

     (doms 4 4 2)
     (mins 0 -3 0)
     (inv (le (var 0) (lit 3))
          (do (set 0 (lit 3))))
     (ev   (do (set 0 (add (var 0) (lit 1)))))
     (evwhen (lt (var 1) (lit 3))
             (do (set 1 (add (var 1) (lit 1)))))

   doms gives each variable's domain size; mins (optional, default all 0) each
   variable's logical minimum; inv a predicate and its repair transform; ev an
   unguarded event; evwhen a guarded event, which fires only when its guard
   holds. The format has no comment syntax.

   expr  ::= (var i) | (lit n) | (add e e) | (sub e e)     ; n may be negative
   pred  ::= (le e e) | (lt e e) | (eq e e) | (and p...) | (or p...) | (not p)
   xform ::= (do (set i e)...)

   A variable's values live in min .. min+domain-1; the state stores the raw
   0..domain-1 offset. Arithmetic is signed (gsm's Go int); a write clamps into
   the variable's range. check refuses a machine where an expression could exceed
   2^31-1 in magnitude, or where a write could store a negative value into a
   two-valued variable with minimum 0 (a gsm Bool stores value <> 0 there).

   Input validation (the extracted code is only meaningful on well-formed input):
   integers are decimal with an optional leading '-'; indices, domains and
   pair entries are at most 2^31-1; a literal or minimum beyond that (up to 19
   digits) is refused as outside the certified fragment (exit 1), not rejected;
   indices and domains are non-negative; every domain is at least 1; the
   product of the domains (the number of states) is at most 2^24; mins gives
   exactly one entry per variable; every variable index names a declared variable;
   doms and mins appear at most once and doms appears before any rule; the file is
   at most 64 MiB; the pairs file is well formed and names existing events. Exit
   0 = verified convergent, 1 = not verified, 2 = usage/parse error. *)


open Checker_core
open Ast_front

let () =
  let argc = Array.length Sys.argv in
  if argc < 2 || argc > 3 then
    (prerr_endline "usage: astchecker <machine-file> [<pairs-file>]"; exit 2);
  let content =
    try read_all Sys.argv.(1)
    with _ -> (prerr_endline "cannot read machine file"; exit 2)
  in
  let m =
    try build_machine (parse_all (tokenize content))
    with Failure msg -> (prerr_endline ("parse error: " ^ msg); exit 2)
  in
  let nv = List.length m.doms and ni = List.length m.invs and ne = List.length m.evs in
  let pairs =
    if argc = 3 then
      (try read_pairs Sys.argv.(2) ne
       with Failure msg -> (prerr_endline ("pairs file error: " ^ msg); exit 2)
          | Sys_error msg -> (prerr_endline ("cannot read pairs file: " ^ msg); exit 2))
    else None
  in
  if !out_of_fragment then
    (Printf.printf
       "FAIL: outside the certified fragment: a literal, minimum or maximum exceeds |2147483647| (gsm's Go int could wrap)\n";
     exit 1);
  (* Machine-readable classification line, parsed by consumers to cross-check a producer's CRDT-fragment claim. Certified
     by the extracted, axiom-free compensationFree, not asserted. *)
  Printf.printf "compensation_free=%b\n" (compensationFree m);
  if not (bounded m) then
    (Printf.printf
       "FAIL: outside the certified fragment: some expression can exceed |2147483647| (gsm's Go int could wrap)\n";
     exit 1);
  if not (signSafe m) then
    (Printf.printf
       "FAIL: outside the certified fragment: a write can store a negative value into a two-valued variable with min 0 (a gsm Bool stores value <> 0, the model clamps)\n";
     exit 1);
  let declared = match pairs with None -> "every pair" | Some l -> Printf.sprintf "%d declared pairs" (List.length l) in
  if checkBuildT m pairs then
    (Printf.printf
       "OK: %d vars, %d invariants, %d events, %s; machine verified convergent from its RULES (repair terminates from every state; declared pairs commute on valid states and the zero state)\n"
       nv ni ne declared;
     exit 0);
  (* checkBuildT checks WFC itself, so wfc runs only to name the reason. *)
  if not (wfc m) then
    (Printf.printf
       "FAIL: compensation does not terminate (WFC): repair from some state never reaches a valid state\n";
     exit 1);
  Printf.printf
    "FAIL: machine does NOT converge (a declared pair does not commute on a valid state or the zero state)\n";
  exit 1
