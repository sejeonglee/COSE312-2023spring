type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

(*
  let f = proc (x) (x - 11)
  in (f (f 77))
*)
let proc1 = 
  LET ("f", PROC ("x", SUB (VAR "x", CONST 11)),
    CALL (VAR "f", CALL (VAR "f", CONST 77)))

(*
  ((proc (f) (f (f 77))) (proc (x) (x-11)))
*)
let proc2 = 
  CALL (PROC ("f", CALL (VAR "f", CALL (VAR "f", CONST 77))), 
        PROC ("x", SUB (VAR "x", CONST 11)))

(*
  let x = 1
  in let f = proc (y) (x + y)
     in let x = 2
        in let g = proc (y) (x + y)
        in  (f 1) + (g 1)
*)
let let1 = 
  LET ("x", CONST 1, 
    LET ("f", PROC ("y", ADD (VAR "x", VAR "y")),
      LET ("x", CONST 2, 
         LET ("g", PROC ("y", ADD (VAR "x", VAR "y")), 
            (ADD (CALL (VAR "f", CONST 1), 
                  CALL (VAR "g", CONST 1)))))))

(*
  letrec double(x) = if (x = 0) then 0 else (double (x-1) + 2
  in (double 6)
*)
let double = 
  LETREC ("double", "x", IF (EQUAL (VAR "x", CONST 0), 
                            CONST 0, 
                            ADD (CALL (VAR "double", SUB (VAR "x", CONST 1)) , 
                                 CONST 2)), 
    CALL (VAR "double", CONST 6))

(*
  letrec even(x) = if (x = 0) then true else odd(x-1)
         odd(x) = if (x = 0) then false else even(x-1)
  in (even 13)
*)
let evenodd = 
  LETMREC (("even", "x", IF (EQUAL (VAR "x", CONST 0), TRUE, CALL (VAR "odd",  SUB (VAR "x", CONST 1)))),
           ("odd" , "x", IF (EQUAL (VAR "x", CONST 0), FALSE, CALL (VAR "even", SUB (VAR "x", CONST 1)))),
  CALL (VAR "odd", CONST 13))

(*
letrec factorial(x) = 
         if (x = 0) then 1 
         else factorial(x-1) * x
in letrec loop n = 
     if (n = 0) then ()
     else (print (factorial n); loop (n-1))
   in (loop 10)
*)
let fact = 
LETREC ("factorial", "x", 
          IF (EQUAL (VAR "x", CONST 0), CONST 1, 
              MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")), 
  LETREC ("loop", "n", 
    IF (EQUAL (VAR "n", CONST 0), UNIT, 
        SEQ (PRINT (CALL (VAR "factorial", VAR "n")), 
             CALL (VAR "loop", SUB(VAR "n", CONST 1)))), 
      CALL (VAR "loop", CONST 10)))
           
(*
in letrec range(n) = 
      if (n = 1) then (cons 1 nil)
      else n::(range (n-1))
in (range 10)
*)
let range = 
LETREC ("range", "n", 
            IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
                CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1)))), 
     CALL (VAR "range", CONST 10))
(*
letrec reverse(l) = 
  if (isnil l) then []
  else (reverse (tl l)) @ (cons hd l)
in (reverse (cons (1, cons (2, cons (3, nil)))))
*)
let reverse = 
LETREC ("reverse", "l", 
          IF (ISNIL (VAR "l"), NIL, 
              APPEND (CALL (VAR "reverse", TAIL (VAR "l")), 
                      CONS (HEAD (VAR "l"), NIL))), 
     CALL (VAR "reverse", 
           CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL)))))


let zfact = 
  LET ("fix", 
    PROC ("f", 
      CALL (PROC ("x", CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))), 
            PROC ("x", CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
    LET ("f", CALL (VAR "fix", 
            PROC ("f", PROC ("x", 
          IF (EQUAL (VAR "x", CONST 0), CONST 1, 
              MUL (CALL (VAR "f", SUB (VAR "x", CONST 1)), VAR "x"))))), 
           CALL (VAR "f", CONST 10)))

let zrange = 
  LET ("fix", 
    PROC ("f", 
      CALL (PROC ("x", CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))), 
            PROC ("x", CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),


    LET ("f", CALL (VAR "fix", 
            PROC ("range", PROC ("n", 
               IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
                 CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1))))))), 
           CALL (VAR "f", CONST 10)))


type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of (var * var * exp) * (var * var * exp) * env
and env = (var * value) list

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ List.fold_left (fun s x -> s ^ ", " ^ x) "" (List.map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics
exception NotImplemented

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let rec  eval : exp -> env -> value
=fun exp env -> 
  match exp with
    | UNIT -> Unit
    | TRUE -> Bool true
    | FALSE -> Bool false
    | CONST n -> Int n
    | VAR x -> lookup_env x env
    | ADD (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2 -> Int (n1 + n2)
          | _ -> raise UndefinedSemantics
      end
    | SUB (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2 -> Int (n1 - n2)
          | _ -> raise UndefinedSemantics
      end
    | MUL (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2 -> Int (n1 * n2)
          | _ -> raise UndefinedSemantics
      end
    | DIV (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2 -> if (n2 = 0) then raise (Failure "Div by zero error!")
                              else Int (n1 / n2)
          | _ -> raise UndefinedSemantics
      end
    | EQUAL (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2   -> Bool (n1 = n2)
          | Bool b1, Bool b2 -> Bool (b1 = b2)
          | _ -> raise UndefinedSemantics
      end
    | LESS (a, b) -> 
      begin
        match (eval a env), (eval b env) with
          | Int n1, Int n2 -> Bool (n1 < n2)
          | _ -> raise UndefinedSemantics
      end
    | NOT e -> 
      begin
        match (eval e env) with
          | Bool e -> if e then Bool false else Bool true
          | _ -> raise UndefinedSemantics
      end
    | NIL -> List []
    | CONS (hd, tl) -> 
      begin
        match (eval hd env), (eval tl env) with
          | v, List s -> List (v :: s)
          | _ -> raise UndefinedSemantics
      end
    | APPEND (hd, tl) ->
      begin
        match (eval hd env), (eval tl env) with
          | List s1, List s2 -> List (s1 @ s2)
          | _ -> raise UndefinedSemantics
      end
    | HEAD l -> 
      begin
        match (eval l env) with
          | List (hd::tl) -> hd
          | _ -> raise UndefinedSemantics
      end
    | TAIL l -> 
      begin
        match (eval l env) with
          | List (hd::tl) -> List tl
          | _ -> raise UndefinedSemantics
      end
    | ISNIL l ->
      begin
        match (eval l env) with
          | List [] -> Bool true
          | List (hd::tl) -> Bool false
          | _ -> raise UndefinedSemantics
      end
    | IF (e1, e2, e3) ->
      begin
        match (eval e1 env) with
          | Bool true -> (eval e2 env)
          | Bool false -> (eval e3 env)
          | _ -> raise UndefinedSemantics
      end
    | LET (x, e1, e2) ->
      let v = (eval e1 env)
        in (eval e2 (extend_env (x, v) env))
    | LETREC (f, x, e1, e2) -> 
      let new_env = extend_env (f, RecProcedure (f, x, e1, env)) env
        in (eval e2 new_env)
    | LETMREC ((f, x, e1), (g, y, e2), e) ->
      let new_env = extend_env (f, MRecProcedure ((f, x, e1), (g, y, e2), env)) env
        in let new_new_env = extend_env (g, MRecProcedure ((g, y, e2), (f, x, e1), env)) new_env
          in (eval e new_new_env)
    | PROC (x, e) -> Procedure (x, e, env)
    | CALL (e1, e2) -> 
      begin
        match (eval e1 env) with
          | Procedure (x, e, envp) ->
            let v = (eval e2 env)
              in (eval e (extend_env (x, v) envp))
          | RecProcedure (f, x, e, envp) ->
            let v = (eval e2 env)
              in let new_env = (extend_env (x, v) envp)
                in let new_new_env = (extend_env (f, RecProcedure (f, x, e, envp)) new_env)
                  in (eval e new_new_env)
          | MRecProcedure ((f, x, fe), (g, y, ge), envp) ->
            let v = (eval e2 env)
              in let new_env = (extend_env (x, v) envp)
                in let new_new_env = (extend_env (f, MRecProcedure ((f, x, fe), (g, y, ge), envp)) new_env)
                  in let new_new_new_env = (extend_env (g, MRecProcedure ((g, y, ge), (f, x, fe), envp)) new_new_env)
                    in (eval fe new_new_new_env)
          | _ -> raise UndefinedSemantics
      end
    | PRINT e -> print_endline (string_of_value (eval e env)); eval UNIT env
    | SEQ (e1, e2) -> let _ = (eval e1 env) in (eval e2 env)

let runml : program -> value
=fun pgm -> eval pgm empty_env ;;
