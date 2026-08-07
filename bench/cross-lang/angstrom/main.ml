(* Angstrom JSON leaf-scalar counter benchmark.
   Counts: number=1, string=1, true/false/null=1.
   Object keys are NOT counted, only values.
   No DOM built; count accumulated as int.
   Strict RFC-8259: rejects leading zeros, trailing dot/e, bad escapes,
   unescaped control bytes.
   Non-allocating: no intermediate lists; running sum threaded via recursion.
   Bulk-scans safe string bytes with take_while. *)

open Angstrom

let is_ws = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false
let skip_ws = skip_while is_ws

let is_digit = function '0'..'9' -> true | _ -> false
let is_digit_nonzero = function '1'..'9' -> true | _ -> false
let is_hex = function '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false

(* String: bulk-scan safe runs with take_while, then branch on special byte.
   Returns 1 leaf. *)
let json_string_value : int t =
  char '"' *>
  fix (fun loop ->
    take_while (fun c -> Char.code c >= 0x20 && c <> '"' && c <> '\\') *>
    any_char >>= function
    | '"' ->
      return 1
    | '\\' ->
      any_char >>= (fun esc ->
        match esc with
        | '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' -> loop
        | 'u' ->
          satisfy is_hex *> satisfy is_hex *> satisfy is_hex *> satisfy is_hex *>
          loop
        | _ ->
          fail (Printf.sprintf "bad escape char %d" (Char.code esc)))
    | c ->
      fail (Printf.sprintf "unescaped control byte %d" (Char.code c))
  )

(* Number: strict RFC-8259 grammar, returns 1 leaf. *)
let json_number_value : int t =
  option () (char '-' *> return ()) *>
  (peek_char_fail >>= fun c ->
    match c with
    | '0' ->
      advance 1 *>
      (peek_char >>= function
        | Some d when is_digit d -> fail "leading zero in number"
        | _ -> return ())
    | c when is_digit_nonzero c ->
      advance 1 *> skip_while is_digit
    | _ ->
      fail "expected digit in number") *>
  option () (
    peek_char >>= function
    | Some '.' ->
      advance 1 *>
      (peek_char_fail >>= fun c ->
        if is_digit c then advance 1 *> skip_while is_digit
        else fail "expected digit after decimal point")
    | _ -> return ()
  ) *>
  option () (
    peek_char >>= function
    | Some 'e' | Some 'E' ->
      advance 1 *>
      option () (
        peek_char >>= function
        | Some '+' | Some '-' -> advance 1
        | _ -> return ()
      ) *>
      (peek_char_fail >>= fun c ->
        if is_digit c then advance 1 *> skip_while is_digit
        else fail "expected digit in exponent")
    | _ -> return ()
  ) *>
  return 1

let json_true  : int t = string "true"  *> return 1
let json_false : int t = string "false" *> return 1
let json_null  : int t = string "null"  *> return 1

(* json_value uses fix for recursion.
   Arrays and objects use non-allocating recursive folds -- no lists built. *)
let json_value : int t =
  fix (fun json_value ->

    let key_value =
      skip_ws *>
      json_string_value *>
      skip_ws *>
      char ':' *>
      json_value
    in

    (* Non-allocating fold: parse additional comma-separated values,
       threading the running sum. No list is built. *)
    let rec more_elems acc =
      (skip_ws *> char ',' *> json_value >>= fun n -> more_elems (acc + n))
      <|> return acc
    in

    (* Same for object members. *)
    let rec more_members acc =
      (skip_ws *> char ',' *> key_value >>= fun n -> more_members (acc + n))
      <|> return acc
    in

    let json_array =
      char '[' *>
      skip_ws *>
      (peek_char_fail >>= function
        | ']' -> advance 1 *> return 0
        | _ ->
          json_value >>= fun n0 ->
          more_elems n0 >>= fun total ->
          skip_ws *>
          char ']' *>
          return total)
    in

    let json_object =
      char '{' *>
      skip_ws *>
      (peek_char_fail >>= function
        | '}' -> advance 1 *> return 0
        | _ ->
          key_value >>= fun n0 ->
          more_members n0 >>= fun total ->
          skip_ws *>
          char '}' *>
          return total)
    in

    skip_ws *>
    (peek_char_fail >>= function
      | '"' -> json_string_value
      | '{' -> json_object
      | '[' -> json_array
      | 't' -> json_true
      | 'f' -> json_false
      | 'n' -> json_null
      | _   -> json_number_value)
  )

let document : int t =
  json_value <* skip_ws <* end_of_input

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "usage: %s <json-file>\n" Sys.argv.(0);
    exit 1
  end;
  let path = Sys.argv.(1) in
  let basename = Filename.basename path in

  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  let input = Bytes.unsafe_to_string buf in

  let check_count =
    match parse_string ~consume:All document input with
    | Ok c -> c
    | Error e -> Printf.eprintf "parse error: %s\n" e; exit 1
  in

  let runs = 20 in
  let samples = ref [] in
  let final_count = ref check_count in

  (* CPU time (user + sys): monotonic, unlike gettimeofday's NTP-adjustable wall
     clock; for single-threaded CPU-bound runs the two agree up to scheduling. *)
  let cpu_now () =
    let t = Unix.times () in
    t.Unix.tms_utime +. t.Unix.tms_stime
  in
  for _ = 1 to runs do
    let t0 = cpu_now () in
    let c =
      match parse_string ~consume:All document (Sys.opaque_identity input) with
      | Ok c -> c
      | Error e -> Printf.eprintf "parse error in run: %s\n" e; exit 1
    in
    let t1 = cpu_now () in
    samples := ((t1 -. t0) *. 1000.0) :: !samples;
    final_count := Sys.opaque_identity c
  done;

  let sorted = List.sort compare !samples in
  let best_ms = List.hd sorted in
  let med_ms = List.nth sorted (List.length sorted / 2) in
  Printf.printf "angstrom %s count=%d best_ms=%.3f med_ms=%.3f\n"
    basename !final_count best_ms med_ms
