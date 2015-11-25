{
  open Printf
  open ParserUtils
  open Sys_parser
}

let whitespace = [' ' '\t']

rule lexer = parse
  | whitespace { lexer lexbuf }
  | "c" { lineComments lexbuf }
  | "p" { LP }
  | "cnf" { LCNF }
  | ['-']?['0'-'9']+ { LVAR (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { LEND }
  | '\n' { incr linenum; lexer lexbuf }
  | _ as x { failwith (sprintf "Error: I don't know what %c means, but I saw it on line %d" x !linenum) }

  and lineComments = parse
    | '\n' { incr linenum; lexer lexbuf }
    | _ { lineComments lexbuf }