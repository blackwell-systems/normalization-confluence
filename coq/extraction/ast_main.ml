(* Runnable front-end for the AST oracle: reads a combinator MACHINE (its rules,
   not its output tables) and certifies convergence by recomputing each event's
   step function straight from the expression trees, using the Coq-extracted,
   machine-checked Checker_core.check.

   Machine file format (S-expressions, whitespace-insensitive):

     (doms 4 4 2)                          ; domain size of each variable
     (mins 0 0 0)                          ; logical minimum of each variable (optional; default 0s)
     (inv (le (var 0) (lit 3))             ; invariant: predicate ...
          (do (set 0 (lit 3))))            ;   ... and its repair transform
     (ev   (do (set 0 (add (var 0) (lit 1)))))        ; unguarded event
     (evwhen (lt (var 1) (lit 3))          ; guarded event: fires only when the guard holds
             (do (set 1 (add (var 1) (lit 1)))))

   expr  ::= (var i) | (lit n) | (add e e) | (sub e e)
   pred  ::= (le e e) | (lt e e) | (eq e e) | (and p...) | (or p...) | (not p)
   xform ::= (do (set i e)...)

   A variable's values live in min .. min+domain-1; the state stores the raw
   0..domain-1 offset. Exit 0 = verified convergent, 1 = not, 2 = usage/parse error. *)

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

let int_of s = try int_of_string s with _ -> failwith ("expected integer, got " ^ s)

let rec build_expr = function
  | List [Atom "var"; Atom i] -> EVar (int_of i)
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
  | List [Atom "set"; Atom i; e] -> (int_of i, build_expr e)
  | _ -> failwith "malformed assign"

let build_transform = function
  | List (Atom "do" :: assigns) -> List.map build_assign assigns
  | _ -> failwith "malformed transform (expected (do ...))"

(* An unguarded event has an always-true guard (PAnd [] evaluates to forallb over
   the empty list = true). *)
let always_true : pred = PAnd []

let build_ints = function
  | ds -> List.map (function Atom a -> int_of a | _ -> failwith "expected integer") ds

let build_machine (forms : sexp list) : machine =
  let doms = ref [] and mins = ref None and invs = ref [] and evs = ref [] in
  List.iter (fun form ->
    match form with
    | List (Atom "doms" :: ds) -> doms := build_ints ds
    | List (Atom "mins" :: ms) -> mins := Some (build_ints ms)
    | List [Atom "inv"; p; t] -> invs := (build_pred p, build_transform t) :: !invs
    | List [Atom "ev"; t] -> evs := (always_true, build_transform t) :: !evs
    | List [Atom "evwhen"; g; t] -> evs := (build_pred g, build_transform t) :: !evs
    | _ -> failwith "unknown top-level form (expected doms/mins/inv/ev/evwhen)") forms;
  let mins = match !mins with
    | Some ms -> ms
    | None -> List.map (fun _ -> 0) !doms   (* default: every variable min = 0 *)
  in
  { doms = !doms; mins; invs = List.rev !invs; evs = List.rev !evs }

(* ---- main ---- *)

let read_all path =
  let ic = open_in path in
  let len = in_channel_length ic in
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
  if check m then
    (Printf.printf
       "OK: %d vars, %d invariants, %d events; machine verified convergent from its RULES (events preserve validity and commute on all valid states)\n"
       nv ni ne;
     exit 0)
  else
    (Printf.printf
       "FAIL: machine does NOT converge (an event breaks an invariant it cannot repair, or two events do not commute on some valid state)\n";
     exit 1)
