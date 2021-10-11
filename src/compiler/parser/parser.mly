(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)
%{
  open Tigercommon.Absyn   
  open ParserAux 
  open Tigercommon.Symbol
%}

%token EOF
%token <string> ID 
%token <int> INT 
%token <string> STRING 
%token COMMA COLON SEMICOLON 
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE 
%token DOT PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE    
%token AND OR ASSIGN ARRAY IF THEN ELSE WHILE FOR TO DO
%token LET IN END OF BREAK NIL FUNCTION VAR TYPE CARET 

%nonassoc ASSIGN
%right THEN 
%left DO ELSE 
%left OR
%left AND                   (* binds closer than OR *)
%nonassoc EQ NEQ LT LE GT GE OF 
%left PLUS MINUS
%left TIMES DIVIDE
%right UNARY
%right CARET
%nonassoc TYPE FUNCTION

%start <Tigercommon.Absyn.exp> program  
(* Observe that we need to use fully qualified types for the start symbol *)

%%
(* Expressions *)

%inline binOp_base:
| PLUS      { PlusOp }
| MINUS     { MinusOp }
| DIVIDE    { DivideOp }
| TIMES     { TimesOp }
| EQ        { EqOp }
| NEQ       { NeqOp }
| LT        { LtOp }
| LE        { LeOp }
| GT        { GtOp }
| GE        { GeOp }
| CARET     { ExponentOp }


exp_base:
| NIL                                                       { NilExp }
| i=INT                                                     { IntExp i }
| s=STRING                                                  { StringExp s }
| v=var                                                     { VarExp v } 
| l=exp oper=binOp_base r=exp                               { OpExp {left=l; oper=oper; right=r} }
| v=var ASSIGN e=exp                                        { AssignExp {var = v; exp=e} } 
| WHILE t=exp DO e=exp                                      { WhileExp {test=t; body=e}}
| IF t=exp THEN e1=exp ELSE e2=exp                          { IfExp {test=t; thn=e1; els = Some e2} } 
| IF t=exp THEN e1=exp                                      { IfExp {test=t; thn=e1; els=None} }
| FOR i=ID ASSIGN e1=exp TO e2=exp DO e3 = exp              { ForExp { var= symbol i; escape= ref true; lo=e1; hi=e2; body=e3 }} 
| BREAK                                                     { BreakExp }
| funn = ID LPAREN x = separated_list(COMMA, exp) RPAREN    { CallExp {func= symbol funn; args = x}  }
| LPAREN l=seqEx RPAREN                                     { SeqExp l }     
| LET d=decs IN e=seqEx END                                 { LetExp {decls=d; body=(SeqExp e) ^! $startpos(e) } }                           
| i=ID LBRACE f=separated_list(COMMA, symbolExp ) RBRACE    { RecordExp {fields=f; typ= (symbol i)} }  
| typeId=ID LBRACK e=exp RBRACK OF e2=exp                          { ArrayExp{typ = symbol typeId; size=e; init=e2} }                            // type-id[e1] of e2 
| e1=exp OR e2=exp                                          { IfExp{test=e1; thn = (IntExp 1)^! $startpos; els= Some e2}}
| e1=exp AND e2=exp                                         { IfExp{test=e1; thn= e2; els= Some ((IntExp 0)^! $startpos)} }
| MINUS e=exp                                               { OpExp {left= ((IntExp 0 )^! $startpos) ; oper=MinusOp; right=e} }%prec UNARY 

symbolExp:
| id=ID EQ e=exp       {symbol id, e}

var:
| v=var_base ls = list(lvaluePartSpec)  { makeLvaluePartSpec (v ^@ $startpos) $startpos ls }


%inline var_base:
| i=ID                          { SimpleVar (symbol i)}

/*
type lvaluePartSpec
  = FieldPart of symbol
  | SubscriptPart of exp
;;
*/
lvaluePartSpec:
| DOT i=ID                { FieldPart (symbol i) }
| LBRACK e=exp RBRACK     { SubscriptPart e }

seqEx:
| listexp = separated_list(SEMICOLON, exp)  {listexp}

/*---Decls---*/
decs:
| ds = list(decl)     { ds }

decl:    
| VAR i=ID typ=option(symbolpos) ASSIGN e=exp             {VarDec {name= symbol i; escape= ref true; typ = typ; init=e; pos= $startpos}}
| lis=nonempty_list(fundecldata)                          {FunctionDec lis }
| decs=nonempty_list(tydecldata)                          {TypeDec decs}
 

%inline symbolpos:
|  COLON id=ID               {symbol id, $startpos(id)}


%inline fundecldata:
| FUNCTION i=ID                      
          LPAREN args=separated_list(COMMA,fielddata) 
          RPAREN typ=option(symbolpos) EQ e=exp    {Fdecl{name= symbol i; params=args; result= typ ; body=e; pos= $startpos(i) }  }


%inline tydecldata: //type ID  =  ty
| TYPE id=ID EQ ty=ty     {Tdecl {name= symbol id; ty; pos= $startpos(id)}}

/*---Types---*/
ty: 
| id=ID                                              { NameTy (symbol id, $startpos)}     //int 
| LBRACE lis=separated_list(COMMA, fielddata) RBRACE { RecordTy lis }                     //{hd: int, tree: intlist}
| ARRAY OF typeID=ID                                 { ArrayTy (symbol typeID, $startpos(typeID))}//array of int

fielddata: //{i: int, __ }
| id=ID COLON typeID=ID         { Field {name= (symbol id); escape=ref true; typ= (symbol typeID, $startpos(typeID)); pos= $startpos }}


(* Top-level *)
program: e = exp EOF { e }


exp:
| e=exp_base  { e ^! $startpos }