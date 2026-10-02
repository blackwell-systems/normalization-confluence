(* Runnable front-end for the AST oracle: reads a combinator MACHINE (its rules,
   not its output tables) and certifies convergence by recomputing each event's
   step function straight from the expression trees, using the Coq-extracted,
   machine-checked Checker_core.check.

   Machine file format (S-expressions, whitespace-insensitive):

     (doms 4 4 2)                          ; domain size of each variable
     (mins 0 -3 0)                         ; logical minimum of each variable (optional; default 0s)
     (inv (le (var 0) (lit 3))             ; invariant: predicate ...
          (do (set 0 (lit 3))))            ;   ... and its repair transform
     (ev   (do (set 0 (add (var 0) (lit 1)))))        ; unguarded event
     (evwhen (lt (var 1) (lit 3))          ; guarded event: fires only when the guard holds
             (do (set 1 (add (var 1) (lit 1)))))

   expr  ::= (var i) | (lit n) | (add e e) | (sub e e)     ; n may be negative
   pred  ::= (le e e) | (lt e e) | (eq e e) | (and p...) | (or p...) | (not p)
   xform ::= (do (set i e)...)

   A variable's values live in min .. min+domain-1; the state stores the raw
   0..domain-1 offset. Arithmetic is signed (gsm's Go int); a write clamps into
   the variable's range. check refuses a machine where an expression could exceed
   2^31-1 in magnitude, or where a write could store a negative value into a
   two-valued variable with minimum 0 (a gsm Bool stores value <> 0 there).

   Input validation (the extracted code is only meaningful on well-formed input):
   integers are decimal with an optional leading '-', at most 2^31-1 in magnitude;
   indices and domains are non-negative; every domain is at least 1; mins gives
   exactly one entry per variable; every variable index names a declared variable;
   doms and mins appear at most once and doms appears before any rule; the file is
   at most 64 MiB. Exit 0 = verified convergent, 1 = not verified, 2 = usage/parse error. *)

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
  | List [Atom "lit"; Atom n] -> ELit (int_of n)
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
  nvars := -1;
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
    | List (Atom "mins" :: ms) -> once mins (build_ints int_of ms) "mins"
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
    if abs (List.nth mins i + d - 1) > max_abs then
      failwith (Printf.sprintf "variable %d: max out of range" i)) doms;
  { doms; mins; invs = List.rev !invs; evs = List.rev !evs }

(* ---- main ---- *)

let read_all path =
  let ic = open_in path in
  let len = in_channel_length ic in
  if len > 64 * 1024 * 1024 then (close_in ic; failwith "input larger than 64 MiB");
  let s = really_input_string ic len in
  close_in ic; s

let () =
  if Array.length Sys.argv < 2 then
    (prerr_endline "usage: astchecker <machine-file>"; exit 2);
  let content =
    try read_all Sys.argv.(1)
    with _ -> (prerr_endline "cannot read machine file"; exit 2)
  in
  let m =
    try build_machine (parse_all (tokenize content))
    with Failure msg -> (prerr_endline ("parse error: " ^ msg); exit 2)
  in
  let nv = List.length m.doms and ni = List.length m.invs and ne = List.length m.evs in
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
  if check m then
    (Printf.printf
       "OK: %d vars, %d invariants, %d events; machine verified convergent from its RULES (events preserve validity and commute on all valid states)\n"
       nv ni ne;
     exit 0)
  else
    (Printf.printf
       "FAIL: machine does NOT converge (an event breaks an invariant it cannot repair, or two events do not commute on some valid state)\n";
     exit 1)
