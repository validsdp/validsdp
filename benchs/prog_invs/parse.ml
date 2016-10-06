let file filename =
  let ch = open_in filename in
  let lexbuf = Lexing.from_channel ch in
  let res = Parser.file Lexer.token lexbuf in
  close_in ch;
  res
