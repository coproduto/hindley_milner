let expr =
  let open Algorithm_w in
  Fun ("x",
       App (App ((Var "add_int"), (Var "x")), Val (IntLit 1))
    )

let () = expr |> Algorithm_w.expr_to_string |> print_endline
  
let identity_function_type =
  let open Algorithm_w in
  Forall (NameSet.singleton "a", FunType (TypeVar "a", TypeVar "a"))

let () = identity_function_type |> Algorithm_w.type_to_string |> print_endline

let apply_function_type =
  let open Algorithm_w in
  Forall (
      NameSet.singleton "a",
      FunType (
          TypeVar "a",
          FunType (FunType (TypeVar "a", TypeVar "b"), TypeVar "b")
        )
    )

let () = apply_function_type |> Algorithm_w.type_to_string |> print_endline

let () =
  identity_function_type
  |> Algorithm_w.free_vars_in_type
  |> Algorithm_w.nameset_to_string
  |> print_endline

let () =
  apply_function_type
  |> Algorithm_w.free_vars_in_type
  |> Algorithm_w.nameset_to_string
  |> print_endline

let concretized_apply_type =
  let open Algorithm_w in
  let subst = StringMap.singleton "b" (PrimType IntType) in
  apply_subst_to_type subst apply_function_type

let () =
  concretized_apply_type
  |> Algorithm_w.type_to_string
  |> print_endline

let () =
  concretized_apply_type
  |> Algorithm_w.free_vars_in_type
  |> Algorithm_w.nameset_to_string
  |> print_endline
