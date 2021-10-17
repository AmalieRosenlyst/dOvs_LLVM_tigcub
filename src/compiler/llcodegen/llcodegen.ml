(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon
open Tigerhoist

(* Module aliases *)
module H = Habsyn
module S = Symbol
module Ty = Types
module B = Cfgbuilder

exception NotImplemented (* the final code should compile without this exception *)

exception NotLLVM0

(* --- Helper functions and declarations --- *)

let ( <$> ) f g x = f (g x) (* function application *)
let ( $> ) b1 b2 = b2 <$> b1 (* convenient for sequencing buildlets *)
let ty_of_exp (H.Exp {ty; _}) = ty (* type extractors *)
let ptr_i8 = Ll.Ptr Ll.I8 (* generic pointer type *)

(** [fresh s] generates fresh symbol starting with prefix [s] *)
let fresh : string -> S.symbol =
  let open Freshsymbols in
  let env = empty in
  gensym env

(** [aiws s i] adds instruction [i] with a fresh symbol starting with prefix
    [s] *)
let aiwf s i =
  let t = fresh s in
  (B.add_insn (Some t, i), Ll.Id t)

(* --- Our selfmade helper functions --- *)

(* let oper_typ (oper: Oper.oper) =
   match oper with 
   | (PlusOp | MinusOp | TimesOp | DivideOp | ExponentOp) -> ("bop", oper)
   | (EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp ) -> ("cnd", oper)
   | _ -> raise NotImplemented *)

(* --- end of helper functions --- *)

(* Mapping Tiger built-in types to LLVM types *)
let ty_to_llty = function
  | Ty.INT -> Ll.I64
  | Ty.STRING -> ptr_i8
  | Ty.VOID -> Ll.Void
  | _ -> raise NotLLVM0

(* Suggested structure of the context for the translation *)
type context = {gdecls: (Ll.gid * Ll.gdecl) list ref; locals: Ll.ty S.table}


(* --- Main workhorse functions of the code generation --- *)

(** [cgExp ctxt exp] returns a pair of a buildlet and an operand *)
let rec cgExp (ctxt : context) (Exp {exp_base; ty; _} : H.exp) :
    B.buildlet * Ll.operand =
  let cgE = cgExp ctxt in
  (* for recursive calls with the same context *)
  let open Ll in
  match exp_base with
  | H.IntExp n -> (B.id_buildlet, Ll.Const n)
  | H.StringExp s -> raise NotImplemented
  | H.OpExp {left; oper; right} ->
      let build_right, op_right = cgE right in
      let build_left, op_left = cgE left in (
        match oper with 
        | PlusOp | MinusOp | TimesOp | DivideOp | ExponentOp -> (
          let bion = (match oper with
          | PlusOp -> Ll.Add
          | MinusOp -> Ll.Sub
          | TimesOp -> Ll.Mul
          | DivideOp -> Ll.SDiv (* Giver problemer med divison med 0 *)
          | ExponentOp -> raise NotImplemented 
          | _ -> raise NotImplemented) 
        in (* hvad der skal ske afhænger af right operand, brug runtime.c *)
              let i = Ll.Binop (bion, Ll.I64, op_left, op_right) in
              let newid = fresh "temp" in
              let b_insn = B.add_insn (Some newid, i) in
              let b_binop = B.seq_buildlets [build_left; build_right; b_insn] in
              (b_binop, Ll.Id newid)
        )
        | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp -> (
          let cnd = (match oper with 
          | EqOp -> Ll.Eq      
          | NeqOp -> Ll.Ne
          | LtOp -> Ll.Slt
          | LeOp -> Ll.Sle
          | GtOp -> Ll.Sgt
          | GeOp -> Ll.Sge 
          | _ -> raise NotImplemented (* TODO: throw exception *)
          ) in 
          let i = Ll.Icmp (cnd, Ll.I64, op_left, op_right) in (* TODO: should it be I1 or something? *)
          
          let newid = fresh "temp" in
          let newid2 = fresh "temp" in
          let b_insn = B.add_insn (Some newid, i) in  (* "save" cmp instr in newid  *)
          let new_op = Id newid in                    (* make operand to newid.... *)
          let bu = Ll.Zext (Ll.I1, new_op, Ll.I64) in (* from i1 to i61 of new_op=icmp,  *)        (* TODO: hvilken operand skal være her ? *)
          let c_insn = B.add_insn (Some newid2, bu) in (* add the "result" of bu to newid2  *)
          let b_cmp = B.seq_buildlets[build_left; build_right; b_insn; c_insn] in 
          (b_cmp, Ll.Id newid2)  (* newid2 have the result as i64 *)
        )
        )
  | H.CallExp {func; lvl_diff= 0; args} ->
      (* lvl_diff returned from the hoisting phase for Tiger Cub is always zero *)
      raise NotImplemented
  | H.SeqExp exps -> raise NotImplemented
  | H.IfExp {test; thn; els= Some e} -> (* TODO: use the aiwf function *)
      (* Generate code for test *)
      let (guard_buildlet, guard_op) = cgE test in
      let (then_buildlet, then_op) = cgE thn in
      let (else_buildlet, else_op) = cgE e in
      
      let label2 = fresh "then" in                (* then↓ *)
      let label3 = fresh "else" in                              (*↓else*)
      let merge_label = fresh "merge" in            (*   merge      *)

      let id_alloc = fresh "alloc" in
      let res_op = Id id_alloc in
      let alloc = B.add_alloca(id_alloc, ty_to_llty ty) in 

      (* make guard_op into i1 *)
      let ione = Icmp (Ne, I64, guard_op, Const 0) in
      let (cmp_build, cmp_op) = aiwf "cmp" ione in 
      let conbr = Cbr (cmp_op, label2, label3) in    (* conditional branch based on test to either then or else *)
      let term = B.term_block conbr in                    (* brancher på resultatet af guarden, og terminerer basic blocken *)
      let g_buildlet = B.seq_buildlets [alloc; guard_buildlet; cmp_build; term] in
      
      let then_b = B.start_block(label2) in
      let then_res = Store (ty_to_llty ty, then_op, res_op) in 
      let then_res_ins = B.add_insn (None, then_res) in
      let then_br = Br(merge_label) in
      let term2 = B.term_block(then_br) in 
      let t_buildlet = B.seq_buildlets [g_buildlet; then_b; then_buildlet; then_res_ins; term2] in

      let else_b = B.start_block(label3) in 
      let else_res = Store (ty_to_llty ty, else_op, res_op) in
      let else_res_ins = B.add_insn (None, else_res) in
      let else_br = Br(merge_label) in (* kan slettes, laves også i forrige block*)
      let term3 = B.term_block(else_br) in (* same goes here :'( *)
      let e_buildlet = B.seq_buildlets [t_buildlet; else_b; else_buildlet; else_res_ins; term3] in

      let merge_b = B.start_block(merge_label) in 
      let load = Load(ty_to_llty ty, res_op) in 
      let (load_build, load_op) = aiwf "load" load in
      
      let if_buildlet = B.seq_buildlets [e_buildlet; merge_b; load_build] in
      (if_buildlet, load_op) 
  | H.WhileExp {test; body} -> 
    let (test_buildlet, test_op) = cgE test in 
    let (body_buildlet, body_op) = cgE body in 
    
      (*need to: branch on test to body or return
        in body: do some computation, update som variables, do not alloc everytime
      *)
    (*Make labels so we can jump *)
    let guard_lab = fresh "guard" in    (*Where we test if test still holds*)
    let loop_lab = fresh "loop" in      (*go do the loop again*)
    let merge_lab = fresh "merge" in    (*break free *)
    
    let unbr = Ll.Br (guard_lab) in
    let end_whatever = B.term_block (unbr) in

    let start_g = B.start_block (guard_lab) in              (* block som (re)evaluere test *)
    let comp = Ll.Icmp (Ne, I64, test_op, Const 0) in       (* tjek om test <> 0 (dvs true eller false) *)
    let (g_cmp_build, g_cmp_op) = aiwf "cmp" comp in        (* add tjek_inst og "læg" resultatet i op *)
    let br = Ll.Cbr (g_cmp_op, loop_lab, merge_lab) in      (* branch på test til loop eller done *)
    let end_g = B.term_block (br) in                        (* terminer guard block med branch inst *)
    let gua_buildlet = B.seq_buildlets [end_whatever; start_g; test_buildlet; g_cmp_build; end_g] in
    
    (* Do whatever body contains *)

    let start_l = B.start_block (loop_lab) in (* start the loop block *)
    let l_br = Ll.Br (guard_lab) in           (* branch back to guard *)
    let end_l = B.term_block (l_br) in        (* end with going back to start *)
    let loo_buildlet = B.seq_buildlets [gua_buildlet; start_l; body_buildlet; end_l] in

    let start_m = B.start_block(merge_lab) in   (* make a block to end the while-Exp *)
    
    let while_buildet = B.seq_buildlets [loo_buildlet; start_m] in
    (* TODO: Test den her med while.tig *)
      (* load  *)
      (* Branch on  *)
      (* Jump to own label ? *)

      (* (composed_buildlet, op_res) *)
    
    (while_buildet, Null)   (* returns VOID...  *)
  | H.LetExp {vardecl= VarDec {name; typ; init; _}; body; _} ->
    (*1. we generate the code for the initializer expression e1.*)
    let (init_buildlet, init_op) = cgE init in
        
    (*2. the result of the initialization is stored on the stack 
        in the memory reserved for variable x.*)
    let x_typ = ty_to_llty typ in
    let x_ptr = name in            (* mby bare fresh new ? or name  *)
    let x_ptr_op = Ll.Id x_ptr in  (* mby bare fresh new ? ID.name -> operand *)

    let all = Ll.Alloca x_typ in 
    
    (* let alloc = B.add_alloca(name, x_typ) in *)  (* TODO skal den tilføjes til første block*)
    
    let store_ins = Ll.Store(x_typ, init_op, x_ptr_op) in (*TODO er det rigtig rækkefølge*)
    
    let alloc_build = B.add_insn(Some x_ptr,all) in  (* skal x_ptr ikke bruges til noget *)
    let store_build = B.add_insn(None,store_ins) in  (* vi behøver ikke ref til det*)

    (*3. we generate the code for the body of the declaration e2.*)
    let extended = {ctxt with locals = (S.enter(ctxt.locals,x_ptr,x_typ))} in 
    let (body_buildlet, body_op) = cgExp extended body in 
    
    let composed = B.seq_buildlets[init_buildlet ;alloc_build; store_build; body_buildlet] in 
    (composed, body_op)
    
  | H.VarExp v -> cgVar ctxt v
  | H.AssignExp
      {var= Var {var_base= H.AccessVar (0, varname); ty= varty; pos}; exp} ->
      (* first argument of the AccessVar is always zero in Tiger Cub *)
      let (exp_build, exp_op) = cgE exp in (
        let (var_build, var_op) = cgVar ctxt (H.Var{var_base=H.AccessVar (0, varname);ty = varty;pos}) in 


        let x_typ = ty_to_llty varty in
        (* let x_ptr = varname in             *)
        (* let x_ptr_op = Ll.Id x_ptr in    *)

        (* we want to store exp_op in the var *)
        let store_ins = Ll.Store(x_typ, exp_op, var_op) in 
        let store_build = B.add_insn(None, store_ins) in


        let composed = B.seq_buildlets[var_build; exp_build; store_build] in
        (composed, Null))
      (* );


      raise NotImplemented *)
  (* the rest of the cases do not need handling in LLVM0/ Assignment 4 *)
  | _ -> raise NotLLVM0

and cgVar (ctxt : context) (H.Var {var_base; _}) =
  match var_base with
  | H.AccessVar (0, varname) -> 
    (* first argument of the AccessVar is always zero in Tiger Cub *)
    let varType = S.look(ctxt.locals, varname) in (match varType with
    | Some x -> 
      let name_op = Ll.Id varname in (*make operand of id*)
      let load_inst = Ll.Load(x,name_op) in (* inst to load something of type x from name?*)
      let newId = fresh "temp" in             (* new place to put stuff*)
      let load_b = B.add_insn(Some newId , load_inst) in (* put the load_inst into newid *)
      (load_b,Ll.Id newId)
    | None -> raise NotImplemented)

  | _ -> raise NotLLVM0

(** [cgTigerMain] returns a triple of the form (gdecls, llty, cfg) that
    corresponds to the global declarations, the llvm return type of this
    function, and the CFG of the main body *)
let cgTigerMain ty body locals =
  (* TODO: rewrite this function to include the following
          1) allocation of the locals
          2) call to cgExp with appropriate initalization of the context
          3) code generation of return from the function, and
          4) generating the final CFG and all gdecls
  *)
  let ctxt = {gdecls= ref []; locals= S.empty} in
  let build_body, op = cgExp ctxt body in
  let tr =
    match ty with
    | Ty.INT -> Ll.Ret (Ll.I64, Some op) (* TODO add types *)
    | Ty.VOID -> Ll.Ret (Ll.Void, None)
    (* | Ty.STRING -> Ll.Ret (Ll.Struct eehh, Some op) *)
    | _ -> raise NotImplemented
  in
  let tigermain_builder = B.seq_buildlets [build_body; B.term_block tr] in
  let cfg = tigermain_builder B.empty_cfg_builder |> B.get_cfg in
  (* obs: ocaml pipe operator |> *)
  (!(ctxt.gdecls), ty_to_llty ty, cfg)

(* --- No changes needed in the code below --- *)

(* For the starting assignment observe how the pattern matching expects there
   to be a function that is expected to be "tigermain" generated by the
   hoisting translation *)

let codegen_prog = function
  | H.Program
      { tdecls= []
      ; fdecls=
          [ H.Fdecl
              { name= fname
              ; args= []
              ; result
              ; body
              ; parent_opt= None
              ; locals
              ; _ } ] }
    when S.name fname = "tigermain" ->
      let gdecls, ret_ll_ty, tigermain_cfg =
        cgTigerMain result body locals
      in
      let open Ll in
      { tdecls= []
      ; gdecls
      ; fdecls=
          [ ( fname
            , { fty= ([ptr_i8], ret_ll_ty)
              ; param= [S.symbol "dummy"]
              ; cfg= tigermain_cfg } ) ] }
  | _ -> raise NotLLVM0
