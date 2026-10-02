(* Runnable front-end for the table oracle. Reads a machine's step tables and
   reports whether they have the property gsm's Build checks, using the
   Coq-extracted, machine-checked check_tables (TableCheck.v). Exit 0 = verified
   convergent, 1 = not, 2 = input error.

   Tables file format, version 2 (whitespace-separated tokens; this is what gsm's
   Machine.WriteConvergenceTables emits):
     gsm-tables 2
     n nE
     nf <n state ids>                        normal form of each state
     pairs all | pairs k a1 b1 ... ak bk     the event pairs declared independent
     <event 0: n next-states>
     ...
     <event nE-1: n next-states>
   where entry (e, s) is the normalized state reached by applying event e in state
   s. State 0 is the zero state (Machine.NewState). A state s is valid when
   nf[s] = s. check_tables requires: every declared pair names events below nE;
   every nf entry is a valid state; every step from every state is a valid state;
   and every declared pair commutes on every valid state and on state 0
   (check_tables_converges).

   Version 1 (no header line, no nf, no pairs):
     n nE
     <nE rows of n next-states>
   is checked as version 2 with every state valid (nf = identity) and every pair
   declared, which is exactly the original check (every pair commutes on every
   state, and every step stays in range).

   Input validation: every number is a non-negative decimal integer below 2^31,
   the token count is exact, n >= 1 (there is always a zero state), declared
   pairs name events below nE, and the file is at most 1 GiB. Exit 2 on any
   violation, so a malformed file is never read as a different machine. *)

let fail_input msg = prerr_endline ("input error: " ^ msg); exit 2

let read_all path =
  let ic = try open_in path with Sys_error e -> fail_input e in
  let len = in_channel_length ic in
  if len > 1024 * 1024 * 1024 then fail_input "input larger than 1 GiB";
  let s = really_input_string ic len in
  close_in ic; s

(* A non-negative decimal integer below 2^31. int_of_string would also accept
   '-', '+', '_' and 0x/0o/0b prefixes. *)
let nat_of s =
  let n = String.length s in
  if n = 0 || n > 10 then fail_input ("expected non-negative decimal integer, got " ^ s);
  String.iter (fun c -> if c < '0' || c > '9' then fail_input ("expected non-negative decimal integer, got " ^ s)) s;
  let v = int_of_string s in
  if v > 2147483647 then fail_input ("integer out of range: " ^ s);
  v

let () =
  if Array.length Sys.argv <> 2 then (prerr_endline "usage: checker <tables-file>"; exit 2);
  let content = read_all Sys.argv.(1) in
  let norm = String.map (fun c -> if c = '\n' || c = '\t' || c = '\r' then ' ' else c) content in
  let toks = Array.of_list (List.filter (fun s -> s <> "") (String.split_on_char ' ' norm)) in
  let len = Array.length toks in
  let pos = ref 0 in
  let next what =
    if !pos >= len then fail_input ("unexpected end of input, expected " ^ what);
    let t = toks.(!pos) in incr pos; t in
  let keyword k = let t = next k in if t <> k then fail_input ("expected " ^ k ^ ", got " ^ t) in
  let nat what = nat_of (next what) in
  let v2 = len > 0 && toks.(0) = "gsm-tables" in
  if v2 then begin
    keyword "gsm-tables";
    let ver = next "format version" in
    if ver <> "2" then fail_input ("unsupported tables format version " ^ ver)
  end;
  let n = nat "n" in
  let ne = nat "nE" in
  if n < 1 then fail_input "n must be at least 1 (state 0 is the zero state)";
  (* Bound the work before allocating: every remaining token is one entry. *)
  if n * ne > len then fail_input (Printf.sprintf "expected %d step entries (n=%d, nE=%d)" (n * ne) n ne);
  let nf, pairs =
    if v2 then begin
      keyword "nf";
      let nf = List.init n (fun _ -> nat "nf entry") in
      keyword "pairs";
      let pairs =
        if !pos < len && toks.(!pos) = "all" then (incr pos; None)
        else begin
          let k = nat "pair count or all" in
          if 2 * k > len - !pos then fail_input (Printf.sprintf "expected %d pair entries" (2 * k));
          Some (List.init k (fun _ ->
            let a = nat "pair event" in
            let b = nat "pair event" in
            if a >= ne || b >= ne then
              fail_input (Printf.sprintf "declared pair (%d, %d) names an event past nE=%d" a b ne);
            (a, b)))
        end
      in
      nf, pairs
    end else
      List.init n (fun s -> s), None
  in
  if len - !pos <> n * ne then
    fail_input (Printf.sprintf "expected %d step entries (n=%d, nE=%d), got %d" (n * ne) n ne (len - !pos));
  let rows = List.init ne (fun _ -> Checker_core.of_list (List.init n (fun _ -> nat "step entry"))) in
  let declared = match pairs with None -> "every pair" | Some l -> Printf.sprintf "%d declared pairs" (List.length l) in
  if Checker_core.check_tables n ne (Checker_core.of_list nf) rows pairs then
    (Printf.printf
       "OK: %d states, %d events, %s; tables verified convergent (normal forms and steps land on valid states; declared pairs commute on valid states and the zero state)\n"
       n ne declared;
     exit 0)
  else
    (Printf.printf
       "FAIL: tables do NOT converge (a normal form or step leaves the valid states, or a declared pair does not commute on a valid state or the zero state)\n";
     exit 1)
