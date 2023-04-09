(* 1번 *)
type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

let pgm1 = LET ("x", CONST 1, VAR "x")
let pgm2 = 
  LET ("f", PROC ("x", VAR "x"), 
    IF (CALL (VAR "f", ISZERO (CONST 0)), 
        CALL (VAR "f", CONST 11), 
        CALL (VAR "f", CONST 22)))
let pgm3 = 
  LET ("f", PROC ("x", VAR "x"), 
    LET ("g", PROC ("x", CONST 1), 
      IF (CALL (VAR "f", CALL (VAR "g", ISZERO (CONST 0))), 
          CALL (VAR "f", CALL (VAR "g", CONST 11)), 
          CALL (VAR "f", CALL (VAR "g", CONST 22)))))

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> 
  match e with
  | CONST n -> [ty, TyInt]
  | VAR x -> [ty, TEnv.find tenv x]
  | ADD (e1, e2) -> [ty, TyInt] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | SUB (e1, e2) -> [ty, TyInt] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | MUL (e1, e2) -> [ty, TyInt] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | DIV (e1, e2) -> [ty, TyInt] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
  | READ -> [ty, TyInt]
  | ISZERO e1 -> [ty, TyBool] @ (gen_equations tenv e1 TyInt)
  | IF (e1, e2, e3) -> (gen_equations tenv e1 TyBool) @ (gen_equations tenv e2 ty) @ (gen_equations tenv e3 ty)
  | LET (x, e1, e2) -> 
    let a = fresh_tyvar() in
      (gen_equations tenv e1 a) @ (gen_equations (TEnv.extend (x, a) tenv) e2 ty)
  | LETREC (f, x, e1, e2) ->
    let a1 = fresh_tyvar() in
    let a2 = fresh_tyvar() in
      (gen_equations (TEnv.extend (x, a1) (TEnv.extend (f, TyFun (a1, a2)) tenv)) e1 a2) @ (gen_equations (TEnv.extend (f, TyFun (a1, a2)) tenv) e2 ty)
  | PROC (x, e1) ->
    let a1 = fresh_tyvar() in
    let a2 = fresh_tyvar() in
      [ty, TyFun (a1, a2)] @ (gen_equations (TEnv.extend (x, a1) tenv) e1 a2)
  | CALL (e1, e2) ->
    let a = fresh_tyvar() in
      (gen_equations tenv e1 (TyFun (a, ty))) @ (gen_equations tenv e2 a);;
  
let rec occurence_check : tyvar -> typ -> bool
= fun alpha t ->
  match t with
  | TyInt -> false
  | TyBool -> false
  | TyFun (t1, t2) -> (occurence_check alpha t1) || (occurence_check alpha t2)
  | TyVar a -> if a = alpha then true
               else false;;
  
let rec unify : (typ * typ) -> Subst.t -> Subst.t
= fun (lt, rt) s ->
  match lt, rt with
  | (TyInt, TyInt) -> s
  | (TyBool, TyBool) -> s
  | (TyVar a1, TyVar a2) -> if a1 = a2 then s
                            else (Subst.extend a1 (TyVar a2) s)
  | (TyVar a, t) -> if (occurence_check a t) then raise TypeError
                    else Subst.extend a t s
  | (t, TyVar a) -> unify (TyVar a, t) s
  | (TyFun (t1, t2), TyFun (t1p, t2p)) ->
    let sp = unify (t1, t1p) s in
    let spp = unify (Subst.apply t2 sp, Subst.apply t2p sp) sp in
      spp
  | _-> raise TypeError;;
    
let rec unifyall : typ_eqn -> Subst.t -> Subst.t
= fun eqns s ->
  match eqns with
  | [] -> s
  | hd::tl ->
    begin
      match hd with
      | (t1, t2) ->
        let sp = unify (Subst.apply t1 s, Subst.apply t2 s) s in
          (unifyall tl sp)
    end
    
let solve : typ_eqn -> Subst.t
=fun eqns -> unifyall eqns Subst.empty
  
  
let rec lookup_env : var -> (var * exp) list -> exp
= fun x env ->
  match env with
  | [] -> VAR x
  | (y, e)::tl -> if y = x then e
                  else lookup_env x tl;;
                  
let rec extend_env : (var * exp) -> (var * exp) list -> (var * exp) list
= fun (x, e) env -> (x, e) :: env;;
  
let rec is_there : var -> exp -> bool
= fun x e ->
  match e with
  | CONST n -> false
  | VAR y -> if x = y then true
             else false
  | ADD (e1, e2) -> (is_there x e1) || (is_there x e2)
  | SUB (e1, e2) -> (is_there x e1) || (is_there x e2)
  | MUL (e1, e2) -> (is_there x e1) || (is_there x e2)
  | DIV (e1, e2) -> (is_there x e1) || (is_there x e2)
  | READ -> false
  | ISZERO e1 -> is_there x e1
  | IF (e1, e2, e3) -> (is_there x e1) || (is_there x e2) || (is_there x e3)
  | LET (y, e1, e2) -> if x = y then is_there x e1
                       else (is_there x e1) || (is_there x e2)
  | LETREC (f, y, e1, e2) -> if f = x then false    (*변수 이름이랑 함수 이름 같으면 안되나?*)
                             else if x = y then is_there x e2
                             else (is_there x e1) || (is_there x e2)
  | PROC (y, e1) -> if x = y then false
                    else is_there x e1
  | CALL (e1, e2) -> (is_there x e1) || (is_there x e2);;

  
let rec eval : exp -> (var * exp) list -> exp
= fun e env ->
  match e with
  | CONST n -> CONST n
  | VAR x -> lookup_env x env
  | ADD (e1, e2) -> ADD (eval e1 env, eval e2 env)
  | SUB (e1, e2) -> SUB (eval e1 env, eval e2 env)
  | MUL (e1, e2) -> MUL (eval e1 env, eval e2 env)
  | DIV (e1, e2) -> DIV (eval e1 env, eval e2 env)
  | READ -> READ
  | ISZERO e1 -> ISZERO (eval e1 env)
  | IF (e1, e2, e3) -> IF (eval e1 env, eval e2 env, eval e3 env)
  | LET (x, e1, e2) ->
    let e1 = eval e1 env in
    if is_there x e2 then
      let new_env = extend_env (x, e1) env in
        eval e2 new_env
    else LET (x, e1, eval e2 env)
  | LETREC (f, x, e1, e2) -> 
    (*이거 다시 생각해보기*)
    let new_env = extend_env (f, VAR f) env in
      let new_new_env = extend_env (x, VAR x) new_env in
        LETREC (f, x, eval e1 new_new_env, eval e2 new_env)
  | PROC (x, e1) -> 
    let new_env = extend_env (x, VAR x) env in
      PROC (x, eval e1 new_env)
  | CALL (e1, e2) -> CALL (eval e1 env, eval e2 env);;

let rec expand : exp -> exp 
=fun e -> eval e [];;

let typeof : exp -> typ 
=fun exp ->
  let exp = expand exp in
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;




(* 2번 *)
type lambda = 
  | V of var
  | P of var * lambda
  | C of lambda * lambda
and var = string

let rec lookup_env : var -> var list -> bool
= fun x env ->
  match env with
  | [] -> false
  | y::tl -> if x = y then true else lookup_env x tl;;

let rec extend_env : var -> var list -> var list
= fun x env -> x :: env;;

let rec any_free : lambda -> var list -> bool
= fun lam env ->
  match lam with
  | V x -> lookup_env x env
  | P (x, l) ->
    let new_env = extend_env x env in
      any_free l new_env
  | C (l1, l2) -> (any_free l1 env) && (any_free l2 env)

let check : lambda -> bool
= fun lam -> any_free lam [];;
