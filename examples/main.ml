let input_file = ref None
let output_file = ref None

let set_input_file filename =
  match !input_file with
  | None -> input_file := Some filename
  | Some _ ->
     raise (Arg.Bad ("Only accepts one input file: superfluous file \""
                     ^ filename ^ "\""))

let set_output_file s = output_file := Some s

let _ =
  let usage_msg = Printf.sprintf
    "Usage: %s [options] <input_filename>" Sys.argv.(0) in
  let speclist = Arg.align [
    ("-o", Arg.String set_output_file,
     "<filename>  Output results to file <filename> (default is standard ouput)");
  ] in
  try 
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
       Format.printf "parsed\n"
       (* Utils.with_out_ch *)
       (*   !output_file *)
       (*   (fun out_ch -> *)
       (*    let ff = Format.formatter_of_out_channel out_ch in *)
       (*    Format.fprintf ff "%a@." Why.pp ast) *)
  with Report.Error -> exit 2
