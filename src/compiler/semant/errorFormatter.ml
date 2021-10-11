(**************************************************************************)
(* AU Compilation. Assignment submissions can modify this file            *)
(**************************************************************************)


open Tigercommon
open Ppcommon

let string_of_type = Prtypes.string_of_type

let errorIntRequired ty = 
  "INT required, " ^ string_of_type ty ^ " provided"

let errorVoid =
  "cannot assign, void is not a value"

(* mangler *)
let errorNil id = 
  "need to give " ^ string_of_symbol id 
  ^ " a type when assigning the value nil"

(* mangler *)
let errorInferNilType = "cannot infer type of nil expression"

(* mangler *)
let errorTypeDoesNotExist tyname = 
  "type-id " ^ string_of_symbol tyname ^ " does not exist"

(* mangler *)
let errorRecordType ty = 
  "type " ^ string_of_type ty ^ " is not a record type"

(* mangler *)
let errorRecordFields = "record fields do not match"

(* mangler *)
let errorRecordNonExistingField id ty = 
  "the field " ^ string_of_symbol id ^ " does not exist on record of type "
  ^ string_of_type ty 

(* mangler *)
let errorRecordFieldName id expectedid = 
  "the name of the field was " ^ string_of_symbol id ^ ", but expected " 
  ^ string_of_symbol expectedid 

(* mangler *)
let errorUsingFunctionAsVariable id =
  "cannot use function " ^ string_of_symbol id ^ " as a variable"

let errorUsingVariableAsFunction id =
  "cannot use variable " ^ string_of_symbol id ^ " as a function"

let errorVariableUndefined id = 
  "undefined variable "  ^ string_of_symbol id 

(* mangler *)
let errorVariableUnassignable id = 
  "cannot assign to the for-variable " ^ string_of_symbol id


let errorFunctionUndefined id = 
  "undefined function "  ^ string_of_symbol id 

let errorFunctionArguments id = 
  "wrong number of arguments supplied for " ^ string_of_symbol id 

(* mangler *)
let errorFunctionReturn bodyTy funTy = 
  "the type of the body is " ^ string_of_type bodyTy ^ " but " 
  ^ string_of_type funTy ^ " is required"

(* mangler *)
let errorCoercible fromType toType = 
  "type "  ^ string_of_type fromType ^ " cannot be coerced into " 
  ^ string_of_type toType 

(* mangler *)
let errorEqNeqComparison tyLeft tyRight = 
  "unable to compare types of " ^ string_of_type tyLeft ^ " and " 
  ^ string_of_type tyRight 

let errorOtherComparison t1 t2 = 
  "only strings and ints can be compared with that \
   particular binary operator, " ^ (string_of_type t1) ^ ", " ^ 
  (string_of_type t2) ^ " provided"

let errorArith = 
  "only ints can be used in arithmetic expressions"  


let errorIfTypeNotInt ifTy =
  "if branch should have type int but has type "
  ^ string_of_type ifTy
  
(* mangler *)
let errorIfThenShouldBeVoid thenTy = 
  "then branch should have type void but has type " 
  ^ string_of_type thenTy

let errorIfBranchesNotSameType thenTy elseTy = 
  "then branch has type " ^ string_of_type thenTy 
  ^ " and else branch has type "  ^ string_of_type elseTy 
  ^ " which should be the same type"

(* mangler *)
let errorForShouldBeVoid bodyTy = 
  "the body of the for-loop has type " ^ string_of_type bodyTy 
  ^  " but it should have type void"

let errorWhileShouldBeVoid bodyTy = 
  "the body of the while-loop has type " ^ string_of_type bodyTy 
  ^  " but it should have type void"

(* mangler *)
let errorArrayType ty = 
  "type " ^ string_of_type ty ^ " is not an array type"

(* mangler *)
let errorArrayInitType ty actTy = 
  "type of array initialization is " ^ string_of_type ty 
  ^ " but should be " ^ string_of_type actTy

(* mangler *)
let errorTypeDeclLoop names = 
  "illegal circular type declaration: " ^ 
  (String.concat "::" (List.map string_of_symbol names ))

(* mangler *)
let errorDuplicate name = 
  "duplicate definition " ^ string_of_symbol name 

let errorAsignType expTy varTy = 
  "expression has type " ^ string_of_type expTy
  ^ " but should match type of var " ^string_of_type varTy

  let errorExpTypeMustNotBeVoid = 
    "expression must not have type void"

(* mangler *)
let errorBreak = "illegal use of break"

(* mangler *)
let errorA ty name = "error " ^ string_of_type ty ^ " and " ^ string_of_symbol name

(* As a sanity check for the completeness of your type checking, make sure 
   that all of the above functions are used at least once.  *)
