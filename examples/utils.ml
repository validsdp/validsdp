let output_filename_string = function Some s -> s | None -> "stdout"

let with_out_ch output_filename f =
  let out_ch =
    match output_filename with
    | None -> stdout
    | Some filename ->
      try open_out filename
      with Sys_error s ->
        Report.error_loc Location.dummy "%s." s in
  let res = f out_ch in
  begin
    match output_filename with
    | None -> ()
    | Some _ ->
      try close_out out_ch
      with Sys_error s ->
        Report.error_loc Location.dummy "%s." s
  end;
  res

let with_in_ch input_filename f =
  let in_ch =
    match input_filename with
    | None -> stdin
    | Some filename ->
      try open_in filename
      with Sys_error s ->
        Report.error_loc Location.dummy "%s." s in
  let res = f in_ch in
  begin
    match input_filename with
    | None -> ()
    | Some _ ->
      try close_in in_ch
      with Sys_error s ->
        Report.error_loc Location.dummy "%s." s
  end;
  res
