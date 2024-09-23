type literal =
  | IntLit of int
  | BoolLit of bool
  | StringLit of string

type expr =
  | Val of literal
  | Var of string
  | App of expr * expr
  | Fun of string * expr
  | Let of string * expr * expr

type prim_type =
  | IntType
  | BoolType
  | StringType

type simple_type =
  | TypeVar of string
  | PrimType of prim_type
  | FunType of simple_type * simple_type

module NameSet = Set.Make(String)

type datatype =
  | SimpleType of simple_type
  | Forall of NameSet.t * simple_type

let lit_to_string = function
  | IntLit i -> string_of_int i
  | BoolLit b -> string_of_bool b
  | StringLit s -> s

let rec expr_to_string = function
  | Val lit -> lit_to_string lit
  | Var s -> s
  | App (f, x) -> "(" ^ expr_to_string f ^ " " ^ expr_to_string x ^ ")"
  | Fun (var, body) -> "λ" ^ var ^ "." ^ expr_to_string body
  | Let (name, defn, exp) ->
     "let " ^ name ^ " = " ^ expr_to_string defn ^ " in " ^ expr_to_string exp

let nameset_to_string ns =
  let bindings = NameSet.elements ns
  in "(" ^ String.concat ", " bindings ^ ")"

let primitive_type_to_string = function
  | IntType -> "int"
  | StringType -> "string"
  | BoolType -> "bool"

let rec simple_type_to_string = function
  | TypeVar s -> s
  | PrimType p -> primitive_type_to_string p
  | FunType (argtype, rettype) ->
     "(" ^ simple_type_to_string argtype ^ " → " ^ simple_type_to_string rettype ^ ")"

let type_to_string = function
  | SimpleType t -> simple_type_to_string t
  | Forall (bindings, body) ->
     "Λ" ^ nameset_to_string bindings ^ "." ^ simple_type_to_string body

let rec free_vars_in_simple_type = function
  | TypeVar s -> NameSet.singleton s
  | PrimType _ -> NameSet.empty
  | FunType (argtype, rettype) ->
     NameSet.union (free_vars_in_simple_type argtype) (free_vars_in_simple_type rettype)

let free_vars_in_type = function
  | SimpleType t -> free_vars_in_simple_type t
  | Forall (bindings, body) ->
     let body_vars = free_vars_in_simple_type body
     in NameSet.diff body_vars bindings

module StringMap = Map.Make(String)

type substitution = simple_type StringMap.t

let empty_substitution = StringMap.empty

let compose_substs s1 s2 =
  let always_second_wins _ _ v2 = Some v2
  in StringMap.union always_second_wins s1 s2

let get_type_in_subst name subst =
  match StringMap.find_opt name subst with
  | Some t -> t
  | None -> TypeVar name

let rec apply_filtered_subst subst = function
  | TypeVar var -> get_type_in_subst var subst
  | PrimType prim -> PrimType prim
  | FunType (argt, rett) -> FunType (apply_filtered_subst subst argt, apply_filtered_subst subst rett)

let apply_subst_to_type subst dt =
  let free_vars = free_vars_in_type dt in
  let is_free_var = fun name _ ->
    match NameSet.find_opt name free_vars with
    | Some _ -> true
    | None -> false in
  let filtered_subst = StringMap.filter is_free_var subst in
  match dt with
  | Forall (bindings, body) -> Forall (bindings, apply_filtered_subst filtered_subst body)
  | SimpleType t -> SimpleType (apply_filtered_subst filtered_subst t)
  
type context = datatype StringMap.t

let remove_from_context ctx name =
  StringMap.remove name ctx

let apply_subst_to_context subst ctx =
  StringMap.map (apply_subst_to_type subst) ctx

let context_range ctx =
  let add_name_to_set = fun name _ set -> NameSet.add name set
  in StringMap.fold add_name_to_set ctx NameSet.empty

let generalize_simple_type ctx simple_type =
  let generalized_bindings = NameSet.diff (free_vars_in_simple_type simple_type) (context_range ctx) in
  Forall (generalized_bindings, simple_type)

let get_literal_type = function
  | IntLit _ -> Some IntType
  | BoolLit _ -> Some BoolType
  | StringLit _ -> Some StringType

type substitution_result =
  | Applies of substitution
  | FailsOccurCheck of string * simple_type
  | InnerError of simple_type * simple_type * substitution_result

let bind_var (name_to_bind : string) (t : simple_type) : substitution_result =
  let free_variables = free_vars_in_simple_type t in
  let name_occurs = NameSet.mem name_to_bind free_variables in
  if name_occurs
  then FailsOccurCheck (name_to_bind, t)
  else match t with
       | TypeVar n ->
          if n = name_to_bind
          then Applies empty_substitution
          else Applies (StringMap.singleton name_to_bind t)
       | _ -> Applies (StringMap.singleton name_to_bind t)
  
(* let rec most_general_unifier (t1 : simple_type) (t2 : simple_type) : substitution_result = *)
(*   match (t1, t2) with *)
(*   | (TypeVar n, rhs) -> *)
(*      bind_var n rhs *)
(*   | (lhs, TypeVar n) -> *)
(*      bind_var n lhs *)
(*   | (PrimType p1, PrimType p2) -> *)
(*      if p1 = p2 then Some empty_substitution else None *)
(*   | (FunType (a1, r1), FunType (a2, r2)) -> *)
(*      let s1 = most_general_unifier a1 a2 in *)
(*      (match s1 with *)
(*      | None -> None *)
(*      | Some s1 -> *)
(*         let s2 = most_general_unifier (apply_filtered_subst s1 r1) (apply_filtered_subst s1 r2) in *)
(*         match s2 with *)
(*         | None -> None *)
(*         | Some s2 -> Some (compose_substs s1 s2)) *)
(*   | _ -> None *)
     

(* let apply_w ctx = function *)
(*   | Val lit -> (empty_substitution, Some (get_literal_type lit)) *)
(*   | Var name -> (empty_substitution, StringMap.find_opt name ctx) *)
(*   | App (f, x) -> *)
(*      let (s1, t1) = apply_w ctx f in *)
(*      let (s2, t2) = apply_w (apply_subst_to_context s1 ctx) x in *)
(*      let s3 = *)
     


                       
