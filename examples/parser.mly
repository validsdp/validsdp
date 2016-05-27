%{
%}

%token LBRA RBRA COMMA SEMICOL SIZE R QUOT YES NO
%token <string> INT
%token <float> FLOAT
%token EOF

%type <(int * bool * float list list * Q.t) list> file
%start file

%%

file:
| EOF { [] }
| matrix file { $1 :: $2 }

matrix:
| SIZE INT matbody R rat posdef { int_of_string $2, $6, $3, $5 }

posdef:
| YES { true }
| NO { false }

matbody:
| LBRA lines RBRA { $2 }

lines:
| line { [ $1 ] }
| line SEMICOL lines { $1 :: $3 }

line:
| FLOAT { [ $1 ] }
| FLOAT COMMA line { $1 :: $3 }

rat:
| INT QUOT INT { Q.of_string ($1 ^ "/" ^ $3) }
