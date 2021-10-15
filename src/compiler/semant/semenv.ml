(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon 
module S = Symbol 
module Ty = Types

type enventry 
  = VarEntry of Types.ty 
  | FunEntry of { formals: Types.ty list; result: Types.ty }
  (* | NoEntry *)




(* Enter the std libary somehow *)
(* let nextVenv = S.enter( baseVenv, (S.symbol "print"), FunEntry {formals=[STRING];result=VOID}) *)

let functions = 
[(S.symbol "print");
(S.symbol "ord");
(S.symbol "getchar");
(S.symbol "flush");
(S.symbol "chr");
(S.symbol "size");
(S.symbol "substring");
(S.symbol "concat");
(S.symbol "not");
(S.symbol "exit")]

let entries = [FunEntry {formals=[STRING];result=VOID};             (*print*)
FunEntry{formals=[STRING] ; result=INT };            (*ord*)
  FunEntry{formals=[]; result=STRING };                (*getchar*)
  FunEntry{formals=[]; result=VOID };                  (*flush*)
  FunEntry{formals=[INT] ; result=STRING };            (*chr*)
  FunEntry{formals=[STRING] ; result= INT};            (*size*)
  FunEntry{formals=[STRING;INT;INT] ; result= STRING}; (*subString*)
  FunEntry{formals=[STRING;STRING] ; result= STRING};  (*concat*)
  FunEntry{formals=[INT] ; result= INT};               (*not*)
  FunEntry{formals=[INT] ; result= VOID}               (*exit*)
]

let add env a b = S.enter(env,a,b)
(* let baseVenv2 = List.fold_left2 add S.empty functions entries *)

let baseTenv = List.fold_left2 add S.empty [S.symbol "int"; S.symbol "string"; S.symbol "void"] [Ty.INT;STRING;VOID]


let baseVenv =  List.fold_left2 add S.empty functions entries 
(* symbol "print" FunEntry{[STRING];VOID} *)
(* symbol "getchar" FunEntry{[];STRING} *)
(* symbol "ord" FunEntry{[STRING]; INT} *)
(* symbol "substring" FunEntry{[STRING; INT; INT];STRING} *)
(* symbol "" FunEntry{[];} *)

(* let enter (venv,symbol, enventry)  = S.enter (venv, symbol, enventry) 

let lookUp (venv, symbol) = S.look (venv,symbol)

let size venv = S.numItems venv *)

