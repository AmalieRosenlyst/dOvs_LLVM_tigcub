(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)
open Tigercommon
module S = Symbol
module A = Absyn
module E = Semenv
module Err = Errenv
module EFmt = ErrorFormatter
module Ty = Types
module PT = Prtypes
module TA = Tabsyn
module O = Oper
(** Context record contains the environments we use in our translation *)

type context =
  { venv: E.enventry S.table (* Γ from our formal typing rules *)
  ; err: Err.errenv (* error environment *) 
  ; tenv: Ty.ty S.table
}

type binOpType = Arith | Comp

exception NotImplemented
(* the final code should work without this exception *)

exception NotSem0 (* for handling AST cases outside of Sem 0 feature set *)

open Ty

let symToTyp (tenv: Ty.ty S.table)  s = 
  match S.look(tenv,s) with
  | Some t -> t
  | _ -> raise NotSem0

let rec transExp ({err; venv;tenv} : context) e =
  let rec trexp (A.Exp {exp_base; pos}) =
    let (^!) exp_base ty = TA.Exp {exp_base;pos;ty} in
    match exp_base with
    | A.IntExp n ->  TA.IntExp n ^! INT 
    | A.StringExp s -> TA.StringExp s ^! STRING 
    (* the above cases have been implemented in class *)
    | A.OpExp {left; oper; right} -> 
      let  
        (left, lty) = getExpAndType(left) 
        and (right,rty) = getExpAndType(right) 
        and opType = getArithOrComp(oper) in
        (match (lty,rty,opType) with
        | (INT,INT,_) -> TA.OpExp{left ; oper; right} ^! INT
        | (STRING,STRING,Comp) -> TA.OpExp{left; oper; right} ^! INT
        | (STRING,STRING,Arith) -> Err.error err pos EFmt.errorArith; TA.ErrorExp ^! ERROR 
        | (x,y,_) -> Err.error err pos (EFmt.errorOtherComparison x y); TA.ErrorExp ^! ERROR )
        
    | A.CallExp {func; args} -> 
      let entryInEnv = S.look(venv,func) in (match entryInEnv with
      | Some (FunEntry fe) -> 
        (let tyArgs = fe.formals and args2 = List.map getExpAndType args 
          in (
            if(List.length args != List.length tyArgs) then (Err.error err pos (EFmt.errorFunctionArguments func); TA.ErrorExp ^! ERROR)
            else ( 
              let (exps, typs) = List.split args2 
              in( let typesMatch = List.for_all2 (fun x y -> x == y) tyArgs typs in 
                if(typesMatch) 
                  then (TA.CallExp{func; args=exps} ^! fe.result)
                  else (Err.error err pos ("Types of arguments dont match"); TA.ErrorExp ^! ERROR) 
                )
                 )                                     
             )
          )
      | Some (VarEntry _) -> Err.error err pos (EFmt.errorUsingVariableAsFunction func) ; TA.ErrorExp ^! ERROR 
      | _ -> Err.error err pos (EFmt.errorFunctionUndefined func); TA.ErrorExp ^! ERROR)
    | A.SeqExp exp_list -> 
      let taExps =List.map trexp exp_list in
      if(List.length taExps == 0 ) then TA.SeqExp taExps ^! VOID 
      else if(List.length taExps == 1) 
        then (
          let (only,_) = getExpAndType(List.hd exp_list) in (match only with
          | _ -> only ) (* (4) -> 4 *)
        ) 
      else
        (let (last) = List.nth exp_list ((List.length exp_list)-1) in 
        let (_,lasttype) = getExpAndType(last) in 
        TA.SeqExp taExps ^! lasttype )      
    | A.IfExp {test; thn; els= Some e} -> 
      let 
        (e0, ty0) = getExpAndType(test)
        and (e1, ty1) = getExpAndType(thn)
        and (e2, ty2) = getExpAndType(e) 
      in (match ty0 with
       | INT ->  if (ty1 ==ty2) 
        then TA.IfExp{test=e0; thn=e1;els= Some e2} ^! ty1
         else (Err.error err pos (EFmt.errorIfBranchesNotSameType ty1 ty2); TA.ErrorExp ^! ERROR )
       | _ -> (Err.error err pos (EFmt.errorIfTypeNotInt ty0); TA.ErrorExp ^! ERROR )
      )
    | A.WhileExp {test; body} -> 
      let (e1, t)  = getExpAndType(test)
      and (e2, t2) = getExpAndType(body) in 
      if (t <> INT) then (Err.error err pos (EFmt.errorIntRequired t); TA.ErrorExp ^! ERROR )
      else if (t2 <> VOID) then (Err.error err pos (EFmt.errorWhileShouldBeVoid t2); TA.ErrorExp ^! ERROR )
      else (TA.WhileExp{test=e1; body=e2} ^! VOID)
    | A.LetExp{decls; body} ->
      let rec evalDecls acc (aaa : context) l = match l with
      | [] -> (acc,(aaa:context))
      | hd::t -> (let (c,ta) = transDecl(aaa:context) hd in evalDecls (acc @ [ta] ) c t ) 
      in let (taDecls,newEnv) = evalDecls [] {err; venv;tenv} decls in 
      let taBody = transExp newEnv body in
        let tabodytyp = (match taBody with
        | TA.Exp t -> t.ty) in
        TA.LetExp{decls= taDecls; body=taBody } ^! tabodytyp
    | A.VarExp v -> 
      let tavar = trvar(v) and typ = getTypeOfVar(v) in TA.VarExp tavar ^! typ
    | A.AssignExp {var; exp} -> 
      let (e,t1) = getExpAndType(exp)
      and (varr) = trvar(var) and tau = getTypeOfVar(var)
      in
        if(t1 == VOID || tau == VOID) then (Err.error err pos (EFmt.errorVoid); TA.ErrorExp ^! ERROR )
        else if (t1 <> tau) then (Err.error err pos (EFmt.errorAsignType t1 tau); TA.ErrorExp ^! ERROR )
        else TA.AssignExp{var=varr; exp=e} ^! VOID
    | _ -> raise NotSem0 (* the rest of the cases do not need handling in Sem0 / Assignment 3 *)
  and trvar (A.Var{var_base;pos}) = 
    match var_base with 
    | A.SimpleVar id -> (*TA.SimpleVar id*)
      let entry = S.look (venv, id) in
      (match entry with
        | Some VarEntry ty -> (TA.Var{var_base= TA.SimpleVar id;pos; ty})
        | None -> (Err.error err pos (EFmt.errorVariableUndefined id); (TA.Var{var_base= TA.SimpleVar id;pos; ty=ERROR}))
        | _ -> raise NotSem0) 
    | A.FieldVar _ -> raise NotSem0
    | A.SubscriptVar _ -> raise NotSem0
  and getExpAndType (exp : A.exp) =
      let taExp = trexp(exp) in
      match taExp with
      | TA.Exp t -> (taExp,t.ty)
  and getTypeOfVar (A.Var{var_base;pos}) = match var_base with 
      | A.SimpleVar id ->
        let shit = S.look (venv, id)  in 
      (match shit with
        | Some VarEntry ve -> ve 
        | _ -> Err.error err pos (EFmt.errorVariableUndefined id); ERROR  )
      | _ -> raise NotImplemented
  and getArithOrComp (o: O.oper) =
      match o with
      | O.DivideOp | O.ExponentOp | O.MinusOp | O.TimesOp | O.PlusOp -> Arith
      | O.EqOp | O.GeOp | O.GtOp | O.LeOp | O.LtOp | O.NeqOp -> Comp
  in
  trexp e
  
  and transDecl ({err; venv; tenv} : context) dec =
  match dec with
  | A.VarDec {name; escape; typ; init; pos} -> 
    let exp = transExp {err; venv;tenv} init in   (* translate the body*)
    let tpy, posTy = (match typ with
    | Some (t, posTy) -> symToTyp tenv t, posTy
    | _ -> raise NotSem0) in
    let exptype = (                    (*fetch the type of body*)
      match exp with 
        | TA.Exp t -> t.ty
    ) in if (exptype <> tpy)
           then Err.error err posTy (EFmt.errorAsignType exptype tpy);
         if (tpy == VOID) 
            then Err.error err posTy (EFmt.errorExpTypeMustNotBeVoid);
         let entry = E.VarEntry exptype in
         let updatedEnv = S.enter (venv, name, entry) in 
           ({err; venv =updatedEnv;tenv},
            TA.VarDec{name;escape;typ=exptype;init=exp;pos})
  | _ -> raise NotImplemented

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  try (transExp {venv= E.baseVenv; err; tenv = E.baseTenv} e, err)
  with NotSem0 -> (*aaaaaaaaaaaa *)
    Err.error err Lexing.dummy_pos
      "found language feature that is not part of sem0" ;
    ( TA.Exp
        { exp_base= TA.IntExp 0 (* dummy value *)
        ; pos= Lexing.dummy_pos
        ; ty= Ty.ERROR }
    , err )