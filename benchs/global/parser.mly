%{
%}

%token <int> VAR
%token <string> NAME INT
%token DEF DOT LPAR RPAR LET
%token PLUS MINUS TIMES DIV UMINUS POW
%token EOF

%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS
%nonassoc POW

%type <(string * Osdp.Polynomial.Q.t) list> file
%start file

%%

file:
| EOF { [] }
| def file { $1 :: $2 }
| garbage file { $2 }
| DEF file { $2 }

def:
| LET NAME def2 { $2, $3 }

def2:
| garbage def2 { $2 }
| DEF poly DOT { $2 }

poly:
| INT { (* Format.printf "read INT %s@." $1; *) Osdp.Polynomial.Q.const (Q.of_string $1) }
| VAR { (* Format.printf "read VAR %d@." $1; *) Osdp.Polynomial.Q.var $1 }
| LPAR poly RPAR { $2 }
| poly PLUS poly { (* Format.printf "read +@."; *) Osdp.Polynomial.Q.add $1 $3 }
| poly MINUS poly { (* Format.printf "read -@."; *) Osdp.Polynomial.Q.sub $1 $3 }
| poly TIMES poly { (* Format.printf "read *@."; *) Osdp.Polynomial.Q.mult $1 $3 }
| poly DIV INT { (* Format.printf "read /@."; *) Osdp.Polynomial.Q.mult_scalar (Q.inv (Q.of_string $3)) $1 }
| poly POW INT { (* Format.printf "read ^%s@." $3; *) Osdp.Polynomial.Q.power $1 (int_of_string $3) }
| MINUS poly %prec UMINUS { (* Format.printf "read u-@."; *) Osdp.Polynomial.Q.sub Osdp.Polynomial.Q.zero $2 }

garbage:
| VAR { }
| NAME { }
| INT { }
| DOT { }
| LPAR { }
| RPAR { }
| PLUS { }
| MINUS { }
| TIMES { }
| DIV { }
| UMINUS { }
| POW { }
