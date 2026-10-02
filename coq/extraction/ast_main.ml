(* Runnable front-end for the AST oracle: reads a combinator MACHINE (its rules,
   not its output tables) and certifies convergence by recomputing each event's
   step function straight from the expression trees, using the Coq-extracted,
   machine-checked Checker_core.checkBuild. It checks the property gsm's Build
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
   indices and domains are non-negative; every domain is at least 1; mins gives
   exactly one entry per variable; every variable index names a declared variable;
   doms and mins appear at most once and doms appears before any rule; the file is
   at most 64 MiB; the pairs file is well formed and names existing events. Exit
   0 = verified convergent, 1 = not verified, 2 = usage/parse error. *)

open Checker_core

(* ---- tiny S-expression reader ---- *)

type sexp = Atom of string | List of sexp list

let tokenize (s : string) : string list =
  let buf = Buffer.create 16 in
  let out = ref [] in
  let flush () =
    if Buffer.length buf > 0 then (out := Buffer.contents buf :: !out; Buffer.clear buf)
  in
  String.iter (fun c ->
    match c with
    | '(' -> flush (); out := "(" :: !out
    | ')' -> flush (); out := ")" :: !out
    | ' ' | '\t' | '\n' | '\r' -> flush ()
    | c -> Buffer.add_char buf c) s;
  flush ();
  List.rev !out

let parse_all (toks : string list) : sexp list =
  let rec parse toks =
    match toks with
    | [] -> failwith "unexpected end of input"
    | "(" :: rest ->
      let items, rest' = parse_list rest in
      let s, rest'' = (List items), rest' in
      s, rest''
    | ")" :: _ -> failwith "unexpected )"
    | a :: rest -> (Atom a), rest
  and parse_list toks =
    match toks with
    | ")" :: rest -> [], rest
    | [] -> failwith "unterminated ("
    | _ ->
      let item, rest = parse toks in
      let items, rest' = parse_list rest in
      item :: items, rest'
  in
  let rec top toks acc =
    match toks with
    | [] -> List.rev acc
    | _ -> let s, rest = parse toks in top rest (s :: acc)
  in
  top toks []

(* ---- build the extracted AST from S-expressions ---- *)

let max_abs = 2147483647

(* A decimal integer: optional '-', then 1 to 10 digits, magnitude <= 2^31-1. No
   '+', no '_', no 0x/0o/0b prefixes (int_of_string accepts all of those). *)
let int_of s =
  let n = String.length s in
  let start = if n > 0 && s.[0] = '-' then 1 else 0 in
  if n = start || n - start > 10 then failwith ("expected decimal integer, got " ^ s);
  String.iteri (fun i c ->
    if i >= start && (c < '0' || c > '9') then failwith ("expected decimal integer, got " ^ s)) s;
  let v = int_of_string s in
  if abs v > max_abs then failwith ("integer out of range (|n| <= 2147483647): " ^ s);
  v

(* A literal or minimum: a decimal integer of up to 19 digits (a Go int64). One
   beyond 2^31-1 in magnitude is well-formed input outside the certified
   fragment: it sets out_of_fragment, and main refuses to certify the machine
   (exit 1) without running the checker on it. *)
let out_of_fragment = ref false

let value_of s =
  let n = String.length s in
  let start = if n > 0 && s.[0] = '-' then 1 else 0 in
  if n = start || n - start > 19 then failwith ("expected decimal integer, got " ^ s);
  String.iteri (fun i c ->
    if i >= start && (c < '0' || c > '9') then failwith ("expected decimal integer, got " ^ s)) s;
  if n - start > 10 then (out_of_fragment := true; 0)
  else
    let v = int_of_string s in
    if abs v > max_abs then (out_of_fragment := true; 0) else v

let nat_of s =
  let v = int_of s in
  if v < 0 then failwith ("expected non-negative integer, got " ^ s);
  v

(* Variable indices are checked against the declared variable count. *)
let nvars = ref (-1)

let var_index s =
  let i = nat_of s in
  if !nvars < 0 then failwith "doms must come before any rule";
  if i >= !nvars then failwith (Printf.sprintf "variable index %d out of range (%d variables)" i !nvars);
  i

let rec build_expr = function
  | List [Atom "var"; Atom i] -> EVar (var_index i)
  | List [Atom "lit"; Atom n] -> ELit (value_of n)
  | List [Atom "add"; a; b] -> EAdd (build_expr a, build_expr b)
  | List [Atom "sub"; a; b] -> ESub (build_expr a, build_expr b)
  | _ -> failwith "malformed expr"

let rec build_pred = function
  | List [Atom "le"; a; b] -> PLe (build_expr a, build_expr b)
  | List [Atom "lt"; a; b] -> PLt (build_expr a, build_expr b)
  | List [Atom "eq"; a; b] -> PEq (build_expr a, build_expr b)
  | List (Atom "and" :: ps) -> PAnd (List.map build_pred ps)
  | List (Atom "or" :: ps) -> POr (List.map build_pred ps)
  | List [Atom "not"; p] -> PNot (build_pred p)
  | _ -> failwith "malformed pred"

let build_assign = function
  | List [Atom "set"; Atom i; e] -> (var_index i, build_expr e)
  | _ -> failwith "malformed assign"

let build_transform = function
  | List (Atom "do" :: assigns) -> List.map build_assign assigns
  | _ -> failwith "malformed transform (expected (do ...))"

(* An unguarded event has an always-true guard (PAnd [] evaluates to forallb over
   the empty list = true). *)
let always_true : pred = PAnd []

let build_ints conv = List.map (function Atom a -> conv a | _ -> failwith "expected integer")

let build_machine (forms : sexp list) : machine =
  nvars := -1; out_of_fragment := false;
  let doms = ref None and mins = ref None
  and invs = ref [] and evs = ref [] in
  let once r v what = match !r with
    | None -> r := Some v
    | Some _ -> failwith (what ^ " given twice") in
  List.iter (fun form ->
    match form with
    | List (Atom "doms" :: ds) ->
      let ds = build_ints nat_of ds in
      List.iter (fun d -> if d < 1 then failwith "every domain must be at least 1") ds;
      once doms ds "doms"; nvars := List.length ds
    | List (Atom "mins" :: ms) -> once mins (build_ints value_of ms) "mins"
    | List [Atom "inv"; p; t] -> invs := (build_pred p, build_transform t) :: !invs
    | List [Atom "ev"; t] -> evs := (always_true, build_transform t) :: !evs
    | List [Atom "evwhen"; g; t] -> evs := (build_pred g, build_transform t) :: !evs
    | _ -> failwith "unknown top-level form (expected doms/mins/inv/ev/evwhen)") forms;
  let doms = match !doms with Some ds -> ds | None -> failwith "missing doms" in
  let n = List.length doms in
  let mins = match !mins with
    | Some ms -> ms
    | None -> List.map (fun _ -> 0) doms   (* default: every variable min = 0 *)
  in
  if List.length mins <> n then failwith "mins must give one minimum per variable";
  List.iteri (fun i d ->
    if abs (List.nth mins i + d - 1) > max_abs then out_of_fragment := true) doms;
  { doms; mins; invs = List.rev !invs; evs = List.rev !evs }

(* ---- main ---- *)

let read_all path =
  let ic = open_in path in
  let len = in_channel_length ic in
  if len > 64 * 1024 * 1024 then (close_in ic; failwith "input larger than 64 MiB");
  let s = really_input_string ic len in
  close_in ic; s

(* The pairs file: "pairs all" or "pairs k a1 b1 ... ak bk", event indices below
   the machine's event count. *)
let read_pairs path nevents =
  let content = read_all path in
  let toks = List.filter (fun t -> t <> "")
      (String.split_on_char ' ' (String.map (fun c -> if c = '\n' || c = '\t' || c = '\r' then ' ' else c) content)) in
  match toks with
  | ["pairs"; "all"] -> None
  | "pairs" :: k :: rest ->
    let k = nat_of k in
    if List.length rest <> 2 * k then
      failwith (Printf.sprintf "expected %d pair entries, got %d" (2 * k) (List.length rest));
    let rec go = function
      | a :: b :: tl ->
        let a = nat_of a and b = nat_of b in
        if a >= nevents || b >= nevents then
          failwith (Printf.sprintf "declared pair (%d, %d) names an event past the %d events" a b nevents);
        (a, b) :: go tl
      | [] -> []
      | _ -> failwith "odd number of pair entries" in
    Some (go rest)
  | _ -> failwith "expected 'pairs all' or 'pairs k a1 b1 ...'"

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
  if not (wfc m) then
    (Printf.printf
       "FAIL: compensation does not terminate (WFC): repair from some state never reaches a valid state\n";
     exit 1);
  let declared = match pairs with None -> "every pair" | Some l -> Printf.sprintf "%d declared pairs" (List.length l) in
  if checkBuild m pairs then
    (Printf.printf
       "OK: %d vars, %d invariants, %d events, %s; machine verified convergent from its RULES (repair terminates from every state; declared pairs commute on valid states and the zero state)\n"
       nv ni ne declared;
     exit 0)
  else
    (Printf.printf
       "FAIL: machine does NOT converge (a declared pair does not commute on a valid state or the zero state)\n";
     exit 1)
