%{
  open ParserUtils
  open Printf
%}

%token LP 
%token LCNF
%token <int> LVAR
%token <int> LINT
%token LEND

%start system
%type<unit> system

%%

system: properties clauses LEND { 
	let clauses = ParserUtils.check_properties $1 $2 in
	let s = ParserUtils.do_sat clauses in
	let _ = if s then (printf "\nSATISFIABLE\n\n")
	  else (printf "\nUNSATISFIABLE\n\n") in
	()
}
;

properties: LP LCNF LVAR LVAR {
  [$3; $4]
}
;

clauses: LVAR { [$1] }
| LVAR clauses { $1::$2 }
;