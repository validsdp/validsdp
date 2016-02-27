let input_file = ref None

type bench_kind = Print | CholeskyFloatArray | CholeskyFloat | Ldlt

let bench_kind = ref Print

let set_print () = bench_kind := Print
let set_cholesky_array () = bench_kind := CholeskyFloatArray
let set_cholesky () = bench_kind := CholeskyFloat
let set_ldlt () = bench_kind := Ldlt
                     
let set_input_file filename =
  match !input_file with
  | None -> input_file := Some filename
  | Some _ ->
     raise (Arg.Bad ("Only accepts one input file: superfluous file \""
                     ^ filename ^ "\""))

let cholesky_float_array m =
  let sz = Array.length m in
  let r = Array.make_matrix sz sz 0. in
  for j = 0 to sz - 1 do
    for i = 0 to j - 1 do
      let s = ref (m.(i).(j)) in
      for k = 0 to i - 1 do
        s := !s -. r.(i).(k) *. r.(j).(k)
      done;
      r.(j).(i) <- !s /. r.(i).(i)
    done;
    let s = ref (m.(j).(j)) in
    for k = 0 to j - 1 do
      s := !s -. r.(j).(k) *. r.(j).(k)
    done;
    r.(j).(j) <- sqrt !s
  done

let cholesky_float m =
  let rec seq_stilde k c a b = match k, a, b with
    | 0, _, _ -> c
    | _, [], _ -> c
    | _, _, [] -> c
    | _, a1 :: a2, b1 :: b2 -> seq_stilde (k - 1) (c -. (a1 *. b1)) a2 b2 in
  let seq_ytilded k c a b bk = seq_stilde k c a b /. bk in
  let seq_ytildes k c a = sqrt (seq_stilde k c a a) in
  let rec seq_store s n v = match n, s with
    | _, [] -> []
    | 0, _ :: t -> v :: t
    | _, h :: t -> h :: seq_store t (n - 1) v in
  let rec store m i j v = match i, m with
    | _, [] -> []
    | 0, h :: t -> seq_store h j v :: t
    | _, h :: t -> h :: store t (i - 1) j v in
  let rec inner_loop j a r i =
    if i < j then
      let r = store r j i (seq_ytilded i (List.nth (List.nth a i) j)
                                       (List.nth r i) (List.nth r j)
                                       (List.nth (List.nth r i) i)) in
      inner_loop j a r (i + 1)
    else
      r in
  let rec outer_loop n a r j =
    if j < n then
      let r = inner_loop j a r 0 in
      let r = store r j j (seq_ytildes j (List.nth (List.nth a j) j)
                                       (List.nth r j)) in
      outer_loop n a r (j + 1)
    else
      r in
  let sz = List.length m in
  outer_loop sz m m 0

let ldlt m =
  let sz = Array.length m in
  let l = Array.make_matrix sz sz Q.zero in
  let d = Array.make sz Q.zero in
  try
    for j = 0 to sz - 1 do
      for i = 0 to j - 1 do
        let s = ref m.(i).(j) in
        for k = 0 to i - 1 do
          s := Q.(!s - l.(k).(i) * l.(k).(j) * d.(k))
        done;
        l.(i).(j) <- Q.(!s / d.(i))
      done;
      let s = ref m.(j).(j) in
      for k = 0 to j - 1 do
        s := Q.(!s - l.(k).(j) * l.(k).(j) * d.(k))
      done;
      if Q.leq !s Q.zero then raise Exit;
      d.(j) <- !s
    done;
    true
  with Exit -> false
             
let bench mxs =
  let to_array m = Array.map Array.of_list (Array.of_list m) in
  let to_Q m = Array.map (Array.map Q.of_float) m in
  let print (size, nb, time) =
    Format.printf
      "size = %d, nb = %d, avg_time = %f s@."
      size nb (time /. float nb) in
  let bench (prev_size, nb, time) (s, _, m) =
    let nb, time =
      if s = prev_size then nb, time else
        let () = print (prev_size, nb, time) in
        0, 0. in
    let t =
      match !bench_kind with
      | Print -> 0.
      | CholeskyFloatArray ->
         let m = to_array m in
         snd (Utils.profile (fun () -> cholesky_float_array m))
      | CholeskyFloat -> snd (Utils.profile (fun () -> cholesky_float m))
      | Ldlt ->
         let m = to_Q (to_array m) in
         snd (Utils.profile (fun () -> ldlt m)) in
    s, nb + 1, time +. t in
  print
    (List.fold_left
       bench
       ((let s, _, _ = List.hd mxs in s), 0, 0.)
       mxs)
             
let print_coq =
  let cpt = ref (-1) in
  fun fmt (s, b, m) ->
  let print_float fmt f =
    let m, e = frexp f in
    let m = m *. 2. ** 53. in
    let e = e - 53 in
    Format.fprintf fmt "Float radix2 (%.0f) (%d)" m e in
  incr cpt;
  Format.fprintf
    fmt
    "@[<v>(* size %d, %s *)@ \
     @[<v 2>Definition m%d := map (map b64_normalize)@ [:: @[%a@]].@]@ @]@."
    s (if b then "positive definite" else "unknown") !cpt
    (Utils.pp_list
       ~sep:";@ "
       (fun fmt l ->
        Format.fprintf
          fmt "[:: @[%a@]]" (Utils.pp_list ~sep:";@ " print_float) l))
    m

let print mxs = List.iter (print_coq Format.std_formatter) mxs
    
let _ =
  let usage_msg = Printf.sprintf
    "Usage: %s [options] <input_filename>" Sys.argv.(0) in
  try
    let speclist = Arg.align [
      ("-p", Arg.Unit set_print,
       "  Print matrices for Coq (default)");
      ("-a", Arg.Unit set_cholesky_array,
       "  Benchmarks for CholeskyFloatArray");
      ("-c", Arg.Unit set_cholesky,
       "  Benchmarks for CholeskyFloat");
      ("-l", Arg.Unit set_ldlt,
       "  Benchmarks for LDLT");
    ] in
    Arg.parse speclist set_input_file usage_msg;
    (* try to set terminal width for format *)
    let cols = Sys.command "exit `stty size | cut -d\" \" -f2`" in
    if cols >= 32 then Format.set_margin cols;
    match !input_file with
    | None ->
      Printf.eprintf "%s: No input file provided.\n" Sys.argv.(0);
      Arg.usage speclist usage_msg
    | Some f ->
       let mxs = Parse.file f in
       let mxs = List.sort (fun (s1, _, _) (s2, _, _) -> compare s1 s2) mxs in
       match !bench_kind with
       | Print -> print mxs
       | _ -> bench mxs
  with Report.Error -> exit 2
