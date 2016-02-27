let file filename =
  let ast = Utils.with_in_ch (Some filename) (fun in_ch ->
    let lexbuf = Lexing.from_channel in_ch in
    try
      Location.filename := filename;
      Parser.file Lexer.token lexbuf 
    with
    | Lexer.Lexing_error s ->
      let loc = Location.get_current_from_lexbuf lexbuf in
      Report.error_loc loc "%s." s
    | Failure _
    | Parsing.Parse_error ->
      let loc = Location.get_current_from_lexbuf lexbuf in
      Report.error_loc loc "Syntax error.") in
  ast
