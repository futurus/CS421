{
(* Vu Nguyen
   CS421 - Programming Languages and Compilers
   MP7
*)

open Mp7common;;

let line_count = ref 1
let char_count = ref 1

let cinc n = char_count := !char_count + n
let linc n = line_count := (char_count := 1; !line_count + n)

}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric   = ['0' - '9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let letter    = ['a' - 'z' 'A' - 'Z' '_']

let open_comm = "(*"
let close_comm = "*)"

rule token = parse
  | ['\n']          { linc 1; token lexbuf (* skip over newline *) }  
  | [' ' '\t']      { cinc 1; token lexbuf (* skip over whitespace *) }   
  | eof             { EOF } 

(* your rules go here *)
(* keywords *)
  | "~"               { cinc 1; NEG }
  | "+"               { cinc 1; PLUS }
  | "-"               { cinc 1; MINUS }
  | "*"               { cinc 1; TIMES }
  | "/"               { cinc 1; DIV }
  | "+."              { cinc 2; DPLUS }
  | "-."              { cinc 2; DMINUS }
  | "*."              { cinc 2; DTIMES }
  | "/."              { cinc 2; DDIV }
  | "^"               { cinc 1; CARAT }
  | "<"               { cinc 1; LT }
  | ">"               { cinc 1; GT }
  | "<="              { cinc 2; LEQ }
  | ">="              { cinc 2; GEQ }
  | "="               { cinc 1; EQUALS }
  | "<>"              { cinc 2; NEQ }
  | "|"               { cinc 1; PIPE }
  | "=>"              { cinc 2; ARROW }
  | ";"               { cinc 1; SEMI }
  | "::"              { cinc 2; DCOLON }
  | "@"               { cinc 1; AT }
  | "nil"             { cinc 3; NIL }
  | "let"             { cinc 3; LET }
  | "local"           { cinc 5; LOCAL }
  | "val"             { cinc 3; VAL }
  | "rec"             { cinc 3; REC }
  | "and"             { cinc 3; AND }
  | "end"             { cinc 3; END }
  | "in"              { cinc 2; IN }
  | "if"              { cinc 2; IF }
  | "then"            { cinc 4; THEN }
  | "else"            { cinc 4; ELSE }
  | "fun"             { cinc 3; FUN }
  | "fn"              { cinc 2; FN }
  | "op"              { cinc 2; OP }
  | "mod"             { cinc 3; MOD }
  | "raise"           { cinc 5; RAISE }
  | "handle"          { cinc 6; HANDLE }
  | "with"            { cinc 4; WITH }
  | "not"             { cinc 3; NOT }
  | "andalso"         { cinc 7; ANDALSO }
  | "orelse"          { cinc 6; ORELSE }
  | "["               { cinc 1; LBRAC }
  | "]"               { cinc 1; RBRAC }
  | "("               { cinc 1; LPAREN }
  | ")"               { cinc 1; RPAREN }
  | ","               { cinc 1; COMMA }
  | "_"               { cinc 1; UNDERSCORE }

(* ints and reals *)
  | (numeric+) as i                               { cinc (String.length i); INT (int_of_string i)}
  | ((numeric+'.'numeric+)('e'(numeric)+)?) as f  { cinc (String.length f); REAL (float_of_string f)}

(* booleans and unit *)
  | "true"  { cinc 4; BOOL true }
  | "false" { cinc 4; BOOL false }
  | "()"    { cinc 2; UNIT }

(* identifiers *)
  | ((lowercase|uppercase)+(numeric|letter|"'")*) as s     { cinc (String.length s); IDENT s }

(* comments: line 99*)
  | ((";;")([^'\n']*)) as comm  { cinc (String.length comm); token lexbuf }
  | open_comm                   { cinc 2; st_comment 1 (!char_count - 2) lexbuf }
  | close_comm                  { raise (CloseComm {line_num = !line_count; char_num = (!char_count)} ) 
  (* (Failure "unmatched comment") *) }

(* strings: line 109 *)
  | "\""                { cinc 1; st_string "" lexbuf }

and st_comment count cmt_str_char = parse
  | open_comm           { cinc 2; st_comment (count + 1) cmt_str_char lexbuf }
  | close_comm          { cinc 2; match count with 
                          | 1 -> token lexbuf (* proper closure of outer most comment pair *)
                          | n -> st_comment (n - 1) cmt_str_char lexbuf (* closing 1 level *)
                        }
  | eof                 { raise (OpenComm {line_num = !line_count; char_num = cmt_str_char} ) (* file end before close_comment *) }
  | _                   { cinc 1; st_comment count cmt_str_char lexbuf (* ignore all char, keep going at current level *) }

and st_string str = parse
  | "\""                { cinc 1; STRING str }
  | "\\"                { cinc 1; esc_string str lexbuf }
  | _ as chr            { cinc 1; st_string (str ^ (String.make 1 chr)) lexbuf }

and esc_string str = parse
  | "\\"                { cinc 1; st_string (str ^ "\\") lexbuf }
  | "\""                { cinc 1; st_string (str ^ "\"") lexbuf }
  | "t"                 { cinc 1; st_string (str ^ "\t") lexbuf }
  | "n"                 { cinc 1; st_string (str ^ "\n") lexbuf }
  | "r"                 { cinc 1; st_string (str ^ "\r") lexbuf }
  | "b"                 { cinc 1; st_string (str ^ "\b") lexbuf }
  | " "                 { cinc 1; st_string (str ^  " ") lexbuf }
  | ((['0'-'1']['0'-'9']['0'-'9'])|(['2']['0'-'4']['0'-'9'])|(['2']['5']['0'-'5'])) as ddd { cinc 3; st_string (str ^ String.make 1 (char_of_int (int_of_string ddd))) lexbuf }
  | ['\n' '\t'] as wth  { cinc 1; st_string (str ^ "\\" ^ String.make 1 wth) lexbuf } 


{(* do not modify this function: *)
let lextest s = token (Lexing.from_string s)

let opcom r = OPCOM(r.line_num,r.char_num)
let clcom r = CLCOM(r.line_num,r.char_num)
let sclcom r = SCLCOM(r.line_num,r.char_num)

let get_all_tokens s =
    let _ = char_count := 1 in
    let _ = line_count := 1 in
    let b = Lexing.from_string (s^"\n") in
    let rec g () = 
    match token b with EOF -> []
    | t -> t :: g () in
    g ()

let try_get_all_tokens s =
    try Some (get_all_tokens s) with Failure "unmatched comment" -> None
    	     			      	 | OpenComm r -> None
    	     			      	 | CloseComm r -> None
    	     			      	 | SuperCloseComm r -> None
let try_comm_get_all_tokens s =
    try Some (get_all_tokens s) with Failure "unmatched comment" -> None
    	     			      	 | OpenComm r -> Some ([opcom r])
    	     			      	 | CloseComm r -> Some ([clcom r])
    	     			      	 | SuperCloseComm r -> Some ([sclcom r])

 }

