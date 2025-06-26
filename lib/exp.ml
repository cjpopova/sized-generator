(* expression labels *)
module ExpLabel = Key.Make (struct let x="lab" end)
type exp_label = ExpLabel.t

(* variables *)
module Var = Key.Make (struct let x="x" end)
type var = Var.t

(* expression datatype <- this is the grammar we can generate. notice that subexpressions are labelled and not pure exps*)
type exp =
  | Hole
  | Var of var
  | ValInt of int (* CJP: replace/add datatypes*)
  | ValBool of bool
  (* | StdLibRef of string *)
  | Lambda of ((var list) * exp_label)
  | App of (exp_label * (exp_label list)) (* CJP: Applications renamed from Call*)
  | Letrec of (var * (var list) * exp_label)
  | Let of (var * exp_label * exp_label) (* This is the old let, which probably isn't generated anywhere*)

  (* expression nodes *)
type exp_node = {
    exp : exp;
    ty : Type.flat_ty; (* CJP: this used to be a type label*)
    prev : exp_label option;
  }

type program = {
    (* the head node of the program *)
    mutable head : exp_label;

    (* std_lib : (string * Type.flat_ty) list; *)

    (* variable operations *)
    new_var : unit -> var;

    (* ty : Type.registry; *) (* CJP not sure if we need this*)
    (*
    (* type operations *)
    new_ty : Type.ty -> Type.ty_label;
    get_ty : Type.ty_label -> Type.ty;
     *)
    (*
    (* type parameter operations *)
    new_ty_params : Type.extvar -> Type.ty_params_label;
    get_ty_params : Type.ty_params_label -> Type.ty_label list;
    add_ty_param : Type.ty_params_label -> Type.ty_label -> unit;
    (* all params labels that are associated with the given extvar *)
    extvar_ty_params : Type.extvar -> Type.ty_params_label list;
    ty_params_extvar : Type.ty_params_label -> Type.extvar;
     *)

    (* expression operations *)
    new_exp : exp_node -> exp_label;
    get_exp : exp_label -> exp_node;
    set_exp : exp_label -> exp_node -> unit; (* given a label and a node, fill that the expression (hole) w/ that label w/ the node*)

    (* FIXME *)
    rename_child : (exp_label * exp_label) -> exp_label -> unit;
  }

let make_program ty =
  let exp_tbl : exp_node ExpLabel.Tbl.t = ExpLabel.Tbl.create 100 in
  
  (* let ty_registry = Type.make () in *)

  let new_var () = Var.make() in

  let new_exp node =
    let lab = ExpLabel.make() in
    ExpLabel.Tbl.add exp_tbl lab node;
    lab in
  let get_exp lab = ExpLabel.Tbl.find exp_tbl lab in
  let set_exp lab node = ExpLabel.Tbl.replace exp_tbl lab node in

  (* Justin: I hate this so much *)
  (* Ben: a necessary evil *)
  let rename_child (a, b) e =
    let rename e' = if e' == a then b else e' in

    let node = get_exp e in
    let set e' = set_exp e {exp=e'; ty=node.ty; prev=node.prev} in
    match node.exp with
    | Let (x, rhs, body) ->
       set (Let (x, rename rhs, rename body))
    | Lambda (params, body) ->
      set (Lambda (params, rename body))
    | App (func, args) ->
      set (App (rename func, (List.map rename args)))
    | _ -> () in

  let head = new_exp {exp=Hole; ty=ty; prev=None} in

  {
    head = head;

    (* std_lib = std_lib; *)

    (* ty = ty_registry; *)
    new_var = new_var;
    
    new_exp = new_exp;
    get_exp = get_exp;
    set_exp = set_exp;

    rename_child = rename_child;
  }
