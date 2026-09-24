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
   state s. This is what gsm's Machine.WriteConvergenceTables emits. *)

let read_all path =
  let ic = open_in path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic; s

let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: checker <tables-file>"; exit 2);
  let content = read_all Sys.argv.(1) in
  let norm = String.map (fun c -> if c = '\n' || c = '\t' || c = '\r' then ' ' else c) content in
  let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' norm) in
  let arr = Array.of_list (List.map int_of_string toks) in
  let n = arr.(0) and ne = arr.(1) in
  let idx = ref 2 in
  let step =
    List.init ne (fun _ ->
      List.init n (fun _ -> let v = arr.(!idx) in incr idx; v))
  in
  if Checker_core.check_commuting n ne step && Checker_core.closed n ne step then
    (Printf.printf "OK: %d states, %d events; tables verified convergent (commuting + closed)\n" n ne; exit 0)
  else
    (Printf.printf "FAIL: tables do NOT converge (a step pair does not commute, or a step leaves range)\n"; exit 1)
