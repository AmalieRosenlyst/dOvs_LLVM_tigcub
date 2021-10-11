(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

{
  open Tigerparser.Parser  
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
    
  let stringToInt str lexbuf =
    try int_of_string str 
    with Failure _ -> error lexbuf ("Constant " ^ str ^ " can't be converted to integer value.")

}

let digit=['0'-'9']
let letter=['a'-'z' 'A'-'Z']
let nonPrintChar=['\000'-'\031' '\127'-'\255']
let printChar=[^ '\000'-'\031' '\127'-'\255']
let hatChars = ['\000'-'\031' '\127']
let char = ['!' '[' ']' '_' '@' '?' '\\' '^' '?']
let formats = [' ' '\n' '\t' '\012' '\011'] (*the allowed format characters*)

(* add more named regexps here *)
let ids=(letter)('_'|letter|digit)*
let integer=(digit)+
let errorId=(digit)+(letter)+
let con_char=(digit|letter|char)


(* an entrypoint with a few starting regexps *)
rule token = parse
  [' ' '\t' ]         { token lexbuf }     (* skip blanks *)
| eof                 { EOF }
| "array"             { ARRAY }
| "if"                { IF }
| "while"             { WHILE }
| "for"               { FOR }
| "to"                { TO }
| "break"             { BREAK }
| "let"               { LET }
| "in"                { IN }
| "end"               { END }
| "function"          { FUNCTION }
| "var"               { VAR }
| "type"              { TYPE }
| "then"              { THEN }
| "else"              { ELSE }
| "do"                { DO }
| "of"                { OF }
| "nil"               { NIL }
| errorId as i        { error lexbuf ("Invalid ID - can't start with number'" ^ (i) ^ "'")}
| ids as i            { ID i }
| integer as i        { INT (stringToInt i lexbuf) }
| ','                 { COMMA }
| ';'                 { SEMICOLON }
| ":="                { ASSIGN }
| ":"                 { COLON }
| "("                 { LPAREN }
| ")"                 { RPAREN }
| "["                 { LBRACK }
| "]"                 { RBRACK }
| "{"                 { LBRACE }
| "}"                 { RBRACE }
| "."                 { DOT }
| "+"                 { PLUS }
| "-"                 { MINUS }
| "\n"                { Lexing.new_line lexbuf; token lexbuf }
| "/*"                { multi_line_comment 0 lexbuf}
| "*/" as t           { error lexbuf ("End comment before start comment not allowed '" ^ t ^ "'")}
| "*"                 { TIMES }
| "/"                 { DIVIDE }
| "="                 { EQ }
| "<="                { LE }
| ">="                { GE }
| "<>"                { NEQ }     (* dobbelttjek NEQ*)
| "<"                 { LT }
| ">"                 { GT }
| "&"                 { AND }
| "|"                 { OR }
| "^"                 { CARET }   (* Does this exist in Tiger? *)
| '"'                 { escape_string lexbuf.lex_start_p "" lexbuf }
| _ as t              { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") }

and multi_line_comment level = parse
  eof       { error lexbuf ("File ended before the comment did.\n") } (*^ lexbuf.lex_curr_p*)
| "/*"      { multi_line_comment (level + 1) lexbuf }
| "\n"      {Lexing.new_line lexbuf; multi_line_comment level lexbuf}
| "*/"      { if level = 0 then token lexbuf else multi_line_comment (level - 1) lexbuf }
| _         { multi_line_comment level lexbuf }

(* Idea: Accumulate the result string as we matches fractions of the string *) 
(* Important: printChar includes "" why below only works reading ONE character at the time *)
and escape_string position accStr = parse
  eof                           { error lexbuf ("File ended before the string did. \n") }
 |"\\n"                         { escape_string position (accStr^"\n") lexbuf }  
 | "\\t"                        { escape_string position (accStr^"\t") lexbuf } 
 | "\\"(digit digit digit as d) { if (int_of_string(d) < 256)
                                  then
                                  let dd = (Char.chr(int_of_string(d))) 
                                  in escape_string position (accStr^(String.make 1 dd )) lexbuf 
                                  else error lexbuf ("Invalid character '" ^ (d ) ^  "'")} 
 | '\"'                         { lexbuf.lex_start_p <- position; STRING accStr } (* End of string and returning string token *)             
 | "\\^"                        { escapeControlChar position accStr lexbuf } (* \^[ \^?*)
 | "\\"(letter as c)            { error lexbuf ("Invalid escape sequence " ^ (String.make 1 c) )} (*\ee*)
 | "\\\\"                       { escape_string position (accStr^"\\") lexbuf } 
 | printChar as c               { escape_string position (accStr^(String.make 1 c)) lexbuf } 
 | "\\\""                       { escape_string position (accStr^"\"") lexbuf }     (*TODO: Hvad håndterer den her - Kh Amalie ?? - Den håndtere om “  \” “ en gyldig streng :) Knus Anna*) 
 | "\\\n"                       { Lexing.new_line lexbuf; formatString position accStr lexbuf } (*TODO: Hvorfor er denne linje, 120, ikke dækket af 121? Kh Anna *)
 | "\\"formats                         { formatString position accStr lexbuf }
 | _ as c                       { error lexbuf ("Invalid character in string '" ^ (String.make 1 c) ^ "'") } 

and formatString startPos accStr = parse
  eof                   {error lexbuf ("File ended in format string: " ^ accStr)}
| "\n"                  {Lexing.new_line lexbuf; formatString startPos accStr lexbuf }
| formats               { formatString startPos accStr lexbuf}
| "\\"                  { escape_string startPos accStr lexbuf }
| _ as c                { error lexbuf ("Invalid format character '" ^ (String.make 1 c) ^ "'")}

 and escapeControlChar startPos accStr = parse
 eof                  { error lexbuf ("File ended in middle of string: " ^ accStr) }
| con_char as c       { let asciiCode = Char.code (Char.uppercase_ascii c) - 64 in 
                         if (asciiCode = -1) (* Skal det stå mindre end eller ligmed her i stedet for -1 - Anna *)
                         then escape_string startPos (accStr ^ (String.make 1 (Char.chr 127)))  lexbuf 
                         else escape_string startPos (accStr ^ (String.make 1 (Char.chr asciiCode)))  lexbuf }
| _ as c              { error lexbuf ("Illegal control character '^" ^ (String.make 1 c) ^ "'") }

(*  {"file": "pos/batch/handin1/string_test.tig", "feature-sets": ["lex0"]},*)