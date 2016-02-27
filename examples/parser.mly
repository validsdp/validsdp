%{
%}

%token LBRA RBRA COMMA SEMICOL SIZE YES NO
%token <int> INT
%token <float> FLOAT
%token EOF

%type <(int * bool * float list list) list> file
%start file

%%

file:
| EOF { [] }
| matrix file { $1 :: $2 }

matrix:
| SIZE INT matbody posdef { $2, $4, $3 }         

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
