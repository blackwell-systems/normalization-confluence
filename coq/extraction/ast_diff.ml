(* Differential test of the two extracted rules oracles: checkBuildT (step
   tables from the rules, scanned as check_fast does; what astchecker runs)
   against checkBuild (the pairwise rules check). checkBuildT_eq proves them
   equal on every machine and every declaration; this checks the extraction.

   Usage:
     astdiff <machine-file> [<pairs-file>]   one machine, read as astchecker reads it
     astdiff --random <count> <seed>         random machines, built directly
     astdiff --wide <count> <seed>           random machines with 16 to 20 events
                                             and 256 to about 2000 states

   The random machines are not limited to what the front end admits: domains
   may be 0, variable indices may name no variable, and declared pairs may name
   events past the last, since the theorem covers every machine. Each run
   prints the verdict counts (accepted, and rejected by the first failing part)
   and stops at the first disagreement, printing the machine. Exit 0 = no
   disagreement, 3 = a disagreement, 2 = usage or parse error. *)

open Checker_core
open Ast_front

let verdict m p =
  if not (bounded m) then "bounded" else if not (signSafe m) then "signSafe"
  else if not (wfc m) then "wfc" else if checkBuild m p then "accept" else "pairs"

let show_expr =
  let rec go = function
    | EVar i -> Printf.sprintf "(var %d)" i
    | ELit n -> Printf.sprintf "(lit %d)" n
    | EAdd (a, b) -> Printf.sprintf "(add %s %s)" (go a) (go b)
    | ESub (a, b) -> Printf.sprintf "(sub %s %s)" (go a) (go b) in
  go

let rec show_pred = function
  | PLe (a, b) -> Printf.sprintf "(le %s %s)" (show_expr a) (show_expr b)
  | PLt (a, b) -> Printf.sprintf "(lt %s %s)" (show_expr a) (show_expr b)
  | PEq (a, b) -> Printf.sprintf "(eq %s %s)" (show_expr a) (show_expr b)
  | PAnd ps -> "(and" ^ String.concat "" (List.map (fun p -> " " ^ show_pred p) ps) ^ ")"
  | POr ps -> "(or" ^ String.concat "" (List.map (fun p -> " " ^ show_pred p) ps) ^ ")"
  | PNot p -> "(not " ^ show_pred p ^ ")"

let show_xform t = "(do" ^ String.concat "" (List.map (fun (i, e) -> Printf.sprintf " (set %d %s)" i (show_expr e)) t) ^ ")"

let show m p =
  let ints l = String.concat " " (List.map string_of_int l) in
  Printf.sprintf "(doms %s)\n(mins %s)\n%s%s; pairs: %s\n" (ints m.doms) (ints m.mins)
    (String.concat "" (List.map (fun (q, t) -> Printf.sprintf "(inv %s %s)\n" (show_pred q) (show_xform t)) m.invs))
    (String.concat "" (List.map (fun (g, t) -> Printf.sprintf "(evwhen %s %s)\n" (show_pred g) (show_xform t)) m.evs))
    (match p with None -> "all" | Some l -> String.concat " " (List.map (fun (a, b) -> Printf.sprintf "%d %d" a b) l))

(* ---- random machines ---- *)

let pick l = List.nth l (Random.int (List.length l))

let rec rexpr nv d =
  if d <= 0 || Random.int 10 < 4 then
    (if Random.int 10 < 6 then EVar (Random.int (nv + (if Random.int 20 = 0 then 2 else 0)))
     else ELit (if Random.int 40 = 0 then pick [2147483647; -2147483647; 1073741824] else Random.int 9 - 4))
  else (if Random.bool () then EAdd (rexpr nv (d - 1), rexpr nv (d - 1)) else ESub (rexpr nv (d - 1), rexpr nv (d - 1)))

let rec rpred nv d =
  let r = Random.int 20 in
  if d <= 0 || r < 12 then
    (let a = rexpr nv 1 and b = rexpr nv 1 in match Random.int 3 with 0 -> PLe (a, b) | 1 -> PLt (a, b) | _ -> PEq (a, b))
  else if r < 15 then PNot (rpred nv (d - 1))
  else
    (let ps = List.init (Random.int 3) (fun _ -> rpred nv (d - 1)) in if Random.bool () then PAnd ps else POr ps)

let rxform nv = List.init (1 + Random.int 2) (fun _ -> (Random.int nv, rexpr nv 2))

let rmachine () =
  let nv = 1 + Random.int 3 in
  let doms = List.init nv (fun _ -> if Random.int 50 = 0 then 0 else 1 + Random.int 4) in
  let mins = List.init nv (fun _ -> if Random.bool () then 0 else Random.int 6 - 3) in
  let invs = List.init (Random.int 3) (fun _ -> (rpred nv 1, rxform nv)) in
  let evs = List.init (1 + Random.int 4) (fun _ ->
    ((if Random.bool () then PAnd [] else rpred nv 1), rxform nv)) in
  let ne = List.length evs in
  let p =
    if Random.bool () then None
    else Some (List.init (Random.int 4) (fun _ -> (Random.int (ne + (if Random.int 10 = 0 then 1 else 0)), Random.int ne))) in
  { doms; mins; invs; evs }, p

(* Wide machines: 16 to 20 events (so each cell has a second 16-entry column
   block) over 8 to 10 variables of domain 2 or 3 (256 to about 2000 states,
   so the cell trie is at least two levels deep), with declared pairs half the
   time. The events mostly set or bump one variable, so some machines converge
   and some do not. *)
let rmachine_wide () =
  let nv = 8 + Random.int 3 in
  let doms = List.init nv (fun i -> if i < 2 && Random.bool () then 3 else 2) in
  let mins = List.init nv (fun _ -> 0) in
  let lit () = ELit (Random.int 2) in
  let invs = List.init (Random.int 3) (fun _ ->
    let a = Random.int nv and b = Random.int nv in
    (PLe (EVar a, EVar b), [(b, EVar a)])) in
  let ev () =
    let i = Random.int nv in
    let eff = match Random.int 4 with
      | 0 -> [(i, EAdd (EVar i, ELit 1))]
      | 1 -> [(i, EVar (Random.int nv))]
      | _ -> [(i, lit ())] in
    ((if Random.int 4 = 0 then PEq (EVar (Random.int nv), lit ()) else PAnd []), eff) in
  let evs = List.init (16 + Random.int 5) (fun _ -> ev ()) in
  let ne = List.length evs in
  let p = if Random.bool () then None
    else Some (List.init (1 + Random.int 40) (fun _ -> (Random.int ne, Random.int ne))) in
  { doms; mins; invs; evs }, p

(* ---- main ---- *)

let counts = Hashtbl.create 8

let compare_one m p =
  let o = checkBuild m p and t = checkBuildT m p in
  if o <> t then
    (Printf.printf "DISAGREE: checkBuild=%b checkBuildT=%b on\n%s" o t (show m p); exit 3);
  let v = verdict m p in
  Hashtbl.replace counts v (1 + try Hashtbl.find counts v with Not_found -> 0)

let report () =
  Printf.printf "agree: %s\n"
    (String.concat ", " (List.map (fun k -> Printf.sprintf "%s %d" k (try Hashtbl.find counts k with Not_found -> 0))
                           ["accept"; "pairs"; "wfc"; "signSafe"; "bounded"]))

let () =
  match Array.to_list Sys.argv with
  | [_; "--random"; count; seed] ->
    Random.init (int_of_string seed);
    for _ = 1 to int_of_string count do let m, p = rmachine () in compare_one m p done;
    report ()
  | [_; "--wide"; count; seed] ->
    Random.init (int_of_string seed);
    for _ = 1 to int_of_string count do let m, p = rmachine_wide () in compare_one m p done;
    report ()
  | _ :: file :: rest when List.length rest <= 1 ->
    let m =
      try build_machine (parse_all (tokenize (read_all file)))
      with Failure msg -> (prerr_endline ("parse error: " ^ msg); exit 2) | Sys_error msg -> (prerr_endline msg; exit 2) in
    let p = match rest with
      | [pf] -> (try read_pairs pf (List.length m.evs) with Failure msg -> (prerr_endline ("pairs file error: " ^ msg); exit 2))
      | _ -> None in
    compare_one m p; report ()
  | _ -> prerr_endline "usage: astdiff <machine-file> [<pairs-file>] | astdiff --random|--wide <count> <seed>"; exit 2
