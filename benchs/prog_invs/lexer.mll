{
open Parser

exception Lexing_error of string
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let blank = [' ' '\r' '\t']
let nl = ['\r']?['\n']

rule token = parse
  | nl { Lexing.new_line lexbuf; token lexbuf }
  | blank+ { token lexbuf }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }
  | '/' { DIV }
  | '^' { POW }
  | '(' { LPAR }
  | ')' { RPAR }
  | "Let" { LET }
  | ":=" { DEF }
  | '.' { DOT }
  | 'x'(('0' | (['1'-'9'] digit*)) as n) { VAR (int_of_string n) }
  | ('0' | (['1'-'9'] digit*)) as n { INT n }
  | (alpha (alpha|digit|['_'])*) as n { NAME n }
  | eof { EOF }
  | _ { token lexbuf }
