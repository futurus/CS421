/* Use the expression datatype defined in expressions.ml: */
%{
    open Mp8common
    let ifsug x y z		= IfExp(x, y, z)
    let andalso x y 	= ifsug (x) (y) (ConstExp(BoolConst false))
    let orelse x y 		= ifsug (x) (ConstExp(BoolConst true)) (y)
	let ltsug x y 		= BinOpAppExp(GreaterOp, y, x)
	let lesug x y 		= orelse (ltsug x y) (BinOpAppExp(EqOp, x, y))
	let gesug x y 		= orelse (ltsug y x) (BinOpAppExp(EqOp, x, y))
	let nesug x y 		= ifsug (BinOpAppExp(EqOp, x, y)) (ConstExp(BoolConst false)) (ConstExp(BoolConst true))
%}

/* Define the tokens of the language: */
%token <int> INT
%token <float> REAL
%token <bool> BOOL
%token <string> STRING IDENT
%token <(int*int)> OPCOM CLCOM
%token NEG PLUS MINUS TIMES DIV DPLUS DMINUS DTIMES DDIV CARAT LT GT LEQ GEQ
       EQUALS NEQ PIPE ARROW SEMI DCOLON AT NIL LET LOCAL VAL REC AND END IN
       IF THEN ELSE FUN FN OP MOD RAISE HANDLE WITH NOT ANDALSO ORELSE
       HD TL FST SND
       LBRAC RBRAC LPAREN RPAREN COMMA UNDERSCORE
       UNIT ERROR EOF

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <Mp8common.dec> main

%%

main:
    | expression SEMI                             	{ Val("it", $1) }
  	| dec SEMI                                    	{ $1 }

dec:
    | atomic_dec									{ $1 }
  	| dec atomic_dec                              	{ Seq($1, $2) }

atomic_dec:
    | VAL IDENT EQUALS expression 					{ Val($2, $4) }
    | VAL UNDERSCORE EQUALS expression 				{ Val("", $4) }
    | LOCAL dec IN dec END 							{ Local($2, $4) }
    | rec_dec 										{ $1 }
    | fun_dec										{ $1 }

rec_dec:
	| VAL REC IDENT IDENT rec_dec_tail 				{ Rec($3, $4, $5) }

rec_dec_tail:
	| EQUALS expression 							{ $2 }
	| IDENT rec_dec_tail 							{ FnExp($1, $2) }

fun_dec:
	| FUN IDENT IDENT fun_dec_tail 					{ Rec($2, $3, $4) }

fun_dec_tail:
	| EQUALS expression 							{ $2 }
	| IDENT fun_dec_tail 							{ FnExp($1, $2) }

expression:
	| andalso_exp									{ $1 }
	| p_expression HANDLE exp_matches				{ match $3 with (intopt, exp, matches) -> HandleExp($1, intopt, exp, matches) }

andalso_exp:
	| p_andalso_exp ANDALSO orelse_exp 				{ andalso $1 $3 }
	| orelse_exp									{ $1 }

orelse_exp:
	| p_orelse_exp ORELSE rel_exp 					{ orelse $1 $3 }
	| rel_exp										{ $1 }

rel_exp:
  	| p_rel_exp GT cons_exp							{ BinOpAppExp(GreaterOp, $1, $3) }
  	| p_rel_exp EQUALS cons_exp						{ BinOpAppExp(EqOp, $1, $3) }
  	| p_rel_exp LT cons_exp							{ ltsug $1 $3 }
  	| p_rel_exp LEQ cons_exp						{ lesug $1 $3 }
  	| p_rel_exp GEQ cons_exp						{ gesug $1 $3 }
  	| p_rel_exp NEQ cons_exp						{ nesug $1 $3 }
  	| cons_exp	     								{ $1 }

cons_exp:
	| p_add_exp DCOLON cons_exp						{ BinOpAppExp(ConsOp, $1, $3) }
	| add_exp										{ $1 }

add_exp:
	| p_add_exp plus_minus mult_exp					{ BinOpAppExp($2,$1,$3) }
	| mult_exp										{ $1 }

mult_exp:
	| p_mult_exp times_div app_exp 					{ BinOpAppExp($2,$1,$3) }
	| nonop_exp										{ $1 }

nonop_exp:
	| raise_if_let_fun_monop_exp					{ $1 }
	| app_raise_exp									{ $1 }

app_raise_exp:
	| app_exp 										{ $1 }
	| monop_raise 									{ $1 }
	| p_app_exp monop_raise 						{ AppExp($1, $2) }

monop_raise:
    | monop RAISE nonop_exp							{ MonOpAppExp($1, RaiseExp($3)) }
  	| RAISE nonop_exp								{ RaiseExp($2) }

app_exp:
	| atomic_expression 							{ $1 }
	| p_app_exp nonapp_exp 							{ AppExp($1, $2) }

nonapp_exp:
	| atomic_expression 							{ $1 }
	| raise_if_let_fun_monop_exp 					{ $1 }

raise_if_let_fun_monop_exp:
	| IF expression THEN expression ELSE expression { IfExp($2, $4, $6) }
	| LET dec IN expression END 					{ LetExp($2, $4) }
	| FN IDENT ARROW expression 					{ FnExp($2, $4) }
	| monop											{ FnExp("x", MonOpAppExp($1, VarExp "x")) }
	| monop raise_if_let_fun_monop_exp				{ MonOpAppExp($1, $2) }

exp_matches:
    | exp_match										{ (match $1 with (intopt, exp) -> (intopt, exp, [])) }
  	| h_exp_match PIPE exp_matches					{ (match ($1,$3) with (intopt, exp), (intoptn, expn, rest) -> (intopt, exp, ((intoptn, expn)::rest))) }

exp_match:
    | pattern ARROW expression						{ ($1, $3) }

h_exp_match:
    | pattern ARROW p_expression					{ ($1, $3) }

pattern:
  	| UNDERSCORE									{ None }
  	| INT											{ Some $1 }

p_expression:
	| p_andalso_exp 								{ $1 }

p_andalso_exp:
	| p_andalso_exp ANDALSO p_orelse_exp 			{ andalso $1 $3 }
	| p_orelse_exp									{ $1 }

p_orelse_exp:
	| p_orelse_exp ORELSE p_rel_exp 				{ orelse $1 $3 }
	| p_rel_exp										{ $1 }

p_rel_exp:
  	| p_rel_exp GT p_cons_exp						{ BinOpAppExp(GreaterOp, $1, $3) }
  	| p_rel_exp EQUALS p_cons_exp					{ BinOpAppExp(EqOp, $1, $3) }
  	| p_rel_exp LT p_cons_exp						{ ltsug $1 $3 }
  	| p_rel_exp LEQ p_cons_exp						{ lesug $1 $3 }
  	| p_rel_exp GEQ p_cons_exp						{ gesug $1 $3 }
  	| p_rel_exp NEQ p_cons_exp						{ nesug $1 $3 }
  	| p_cons_exp	     							{ $1 }

p_cons_exp:
	| p_add_exp DCOLON p_cons_exp					{ BinOpAppExp(ConsOp, $1, $3) }
	| p_add_exp										{ $1 }

p_add_exp:
	| p_add_exp plus_minus p_mult_exp				{ BinOpAppExp($2,$1,$3) }
	| p_mult_exp									{ $1 }

p_mult_exp:
	| p_mult_exp times_div p_app_exp 				{ BinOpAppExp($2,$1,$3) }
	| p_app_exp 									{ $1 }

p_app_exp:
	| atomic_expression 							{ $1 }
	| p_app_exp atomic_expression 					{ AppExp($1, $2) }

atomic_expression:
	| constant_expression							{ ConstExp $1 }
	| IDENT											{ VarExp $1 }
	| paren_expression 								{ $1 }
	| list_expression 								{ $1 }
	| monop atomic_expression						{ MonOpAppExp ($1, $2) }
	| op_exp										{ $1 }	

op_exp:
	| OP binop 										{ FnExp("x", FnExp("y", BinOpAppExp($2, VarExp "x", VarExp "y"))) }
	| OP LT 										{ FnExp("x", FnExp("y", ltsug (VarExp "x") (VarExp "y"))) }
	| OP LEQ 										{ FnExp("x", FnExp("y", lesug (VarExp "x") (VarExp "y"))) }
	| OP GEQ 										{ FnExp("x", FnExp("y", gesug (VarExp "x") (VarExp "y"))) }
	| OP NEQ 										{ FnExp("x", FnExp("y", nesug (VarExp "x") (VarExp "y"))) }

paren_expression:
	| LPAREN paren_expression_end 					{ $2 }

paren_expression_end:
	| expression RPAREN								{ $1 }
	| expression COMMA paren_expression_end 		{ BinOpAppExp(CommaOp, $1, $3) }

list_expression:
	| LBRAC list_contents 							{ $2 }

list_contents:
	| RBRAC											{ ConstExp NilConst }
	| expression RBRAC 								{ BinOpAppExp(ConsOp, $1, ConstExp NilConst) }
	| expression COMMA list_contents				{ BinOpAppExp(ConsOp, $1, $3) }

constant_expression:
	| INT 											{ IntConst $1 }
	| BOOL 											{ BoolConst $1 }
	| REAL 											{ RealConst $1 }
	| STRING 										{ StringConst $1 }
	| NIL											{ NilConst }
	| UNIT 											{ UnitConst }

monop:
	| HD											{ HdOp }
	| TL											{ TlOp }
	| NEG											{ IntNegOp }
	| FST											{ FstOp }
	| SND											{ SndOp }

plus_minus:
    | PLUS											{ IntPlusOp }
  	| MINUS											{ IntMinusOp }
  	| DPLUS											{ RealPlusOp }
  	| DMINUS										{ RealMinusOp }
  	| CARAT											{ ConcatOp }

times_div:
    | TIMES											{ IntTimesOp }
  	| DIV											{ IntDivOp }
  	| DTIMES										{ RealTimesOp }
  	| DDIV											{ RealDivOp }

binop:
    | PLUS 											{ IntPlusOp }        
   	| MINUS 										{ IntMinusOp }   
   	| TIMES 										{ IntTimesOp }
   	| DIV 											{ IntDivOp }
   	| DPLUS 										{ RealPlusOp }
   	| DMINUS 										{ RealMinusOp }
   	| DTIMES 										{ RealTimesOp }
   	| DDIV 											{ RealDivOp }
   	| CARAT 										{ ConcatOp }
   	| DCOLON 										{ ConsOp }
   	| EQUALS 										{ EqOp }
   	| GT 											{ GreaterOp }
