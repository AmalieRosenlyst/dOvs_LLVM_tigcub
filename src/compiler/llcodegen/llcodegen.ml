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
      let build_left, op_left = cgE left in
      let bop =
        match oper with 
          PlusOp -> Ll.Add
        | MinusOp -> Ll.Sub
        | TimesOp -> Ll.Mul
        | DivideOp -> Ll.SDiv
        | ExponentOp -> raise NotImplemented  (* hvad der skal ske afhænger af right operand, brug runtime.c *)
        | EqOp -> raise NotImplemented       (* sub b a => icmp c 0 *)
        | NeqOp -> raise NotImplemented
        | LtOp -> raise NotImplemented
        | LeOp -> raise NotImplemented
        | GtOp -> raise NotImplemented
        | GeOp -> raise NotImplemented
        | _ -> raise NotImplemented
      in
      (* let thingy = 
        match bop with
        | Ll.bop -> raise NotImplemented
        | Ll.cnd -> raise NotImplemented
       in *)
      let i = Ll.Binop (bop, Ll.I64, op_left, op_right) in
      let newid = fresh "temp" in
      let b_insn = B.add_insn (Some newid, i) in
      let b_binop = B.seq_buildlets [build_left; build_right; b_insn] in
      (b_binop, Ll.Id newid)
  | H.CallExp {func; lvl_diff= 0; args} ->
      (* lvl_diff returned from the hoisting phase for Tiger Cub is always zero *)
      raise NotImplemented
  | H.SeqExp exps -> raise NotImplemented
  | H.IfExp {test; thn; els= Some e} -> 
      (* Generate code for test *)
      let (guard_buildlet, guard_op) = cgE test in
      let (then_buildlet, then_op) = cgE thn in
      let (else_buildlet, else_op) = cgE e in
      
      let label1 = fresh "basic" in
      let basic_b = B.start_block label1 in

      (* let B.term_block in *)

      let id_alloc = fresh "alloc" in
      let alloc = B.add_alloca(id_alloc, ty_to_llty ty) in 
      (* let conb = B.add_insn() *)
      (* add conditional branch that jumpt to either then or else *)
      let label2 = fresh "then" in
      let then_b = B.start_block(label2) in

      let label3 = fresh "else" in
      let else_b = B.start_block(label3) in 
      (then_buildlet, then_op)
      (* Skal vi terminere alle de blocks vi har lavet??? *)
  | H.WhileExp {test; body} -> raise NotImplemented
  | H.LetExp {vardecl= VarDec {name; typ; init; _}; body; _} ->
      raise NotImplemented
  | H.VarExp v -> cgVar ctxt v
  | H.AssignExp
      {var= Var {var_base= H.AccessVar (0, varname); ty= varty; _}; exp} ->
      (* first argument of the AccessVar is always zero in Tiger Cub *)
      raise NotImplemented
  (* the rest of the cases do not need handling in LLVM0/ Assignment 4 *)
  | _ -> raise NotLLVM0

and cgVar (ctxt : context) (H.Var {var_base; _}) =
  match var_base with
  | H.AccessVar (0, varname) -> raise NotImplemented
      (* first argument of the AccessVar is always zero in Tiger Cub *)
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
    | Ty.INT -> Ll.Ret (Ll.I64, Some op)
    | _ -> raise NotImplemented
  in
  let tigermain_builder = B.seq_buildlets [build_body; B.term_block tr] in
  let cfg = tigermain_builder B.empty_cfg_builder |> B.get_cfg in
  (* obs: ocaml pipe operator |> *)
  (!(ctxt.gdecls), Ll.I64, cfg)

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
