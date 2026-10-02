(* Runnable front-end for the verified checker. Reads a machine's step tables and
   reports whether they are convergent (per-event step functions commute, and stay
   in range), using the Coq-extracted, machine-checked check. Exit 0 = verified
   convergent, 1 = not.

   Tables file format (whitespace-separated integers):
     n nE
     <event 0: n next-states>
     <event 1: n next-states>
     ...
   where entry (e, s) is the normalized state reached by applying event e in
   state s. This is what gsm's Machine.WriteConvergenceTables emits.

   Input validation: every token is a non-negative decimal integer below 2^31,
   there are exactly 2 + n*nE of them, and the file is at most 1 GiB. Exit 2 on
   any violation, so a malformed file is never read as a different machine. *)

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
  if Array.length Sys.argv < 2 then (prerr_endline "usage: checker <tables-file>"; exit 2);
  let content = read_all Sys.argv.(1) in
  let norm = String.map (fun c -> if c = '\n' || c = '\t' || c = '\r' then ' ' else c) content in
  let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' norm) in
  let arr = Array.of_list (List.map nat_of toks) in
  if Array.length arr < 2 then fail_input "missing header (n nE)";
  let n = arr.(0) and ne = arr.(1) in
  if Array.length arr <> 2 + n * ne then
    fail_input (Printf.sprintf "expected %d step entries (n=%d, nE=%d), got %d" (n * ne) n ne (Array.length arr - 2));
  let idx = ref 2 in
  let step =
    List.init ne (fun _ ->
      List.init n (fun _ -> let v = arr.(!idx) in incr idx; v))
  in
  if Checker_core.check_commuting n ne step && Checker_core.closed n ne step then
    (Printf.printf "OK: %d states, %d events; tables verified convergent (commuting + closed)\n" n ne; exit 0)
  else
    (Printf.printf "FAIL: tables do NOT converge (a step pair does not commute, or a step leaves range)\n"; exit 1)
