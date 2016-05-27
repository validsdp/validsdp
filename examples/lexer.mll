{
open Parser

exception Lexing_error of string
}

let digit = ['0'-'9']
let hex_digit = ['0'-'9' 'a'-'f']
let blank = [' ' '\r' '\t']
let nl = ['\r']?['\n']
               
rule token = parse
  | nl { Lexing.new_line lexbuf; token lexbuf }
  | blank+ { token lexbuf }
  | '[' { LBRA }
  | ']' { RBRA }
  | "size =" { SIZE }
  | "r =" { R }
  | ',' { COMMA }
  | ';' { SEMICOL }
  | "yes" { YES }
  | "no" { NO }
  | ( ['1'-'9'] digit* ) as s { INT s }
  | '/' { QUOT }
  | ('-'? "0x1." hex_digit+ 'p' ('+' | '-') digit+) as s { FLOAT (float_of_string s) }
  | eof { EOF }
  | _ { raise (Lexing_error "unknown char") }
