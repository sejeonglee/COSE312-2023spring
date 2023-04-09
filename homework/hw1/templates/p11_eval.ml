exception NotImplemented

type formula =
  | True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp

and exp = Num of int | Plus of exp * exp | Minus of exp * exp

let eval : formula -> bool =
 fun f ->
  let rec eval_exp (e : exp) : int =
    match e with
    | Num i -> i
    | Plus (e1, e2) -> eval_exp e1 + eval_exp e2
    | Minus (e1, e2) -> eval_exp e1 - eval_exp e2
  in
  let rec eval_fml (fml : formula) : bool =
    match fml with
    | True -> true
    | False -> false
    | Not f -> not (eval_fml f)
    | AndAlso (f1, f2) -> eval_fml f1 && eval_fml f2
    | OrElse (f1, f2) -> eval_fml f1 || eval_fml f2
    | Imply (f1, f2) -> not (eval_fml f1 && not (eval_fml f2))
    | Equal (e1, e2) -> eval_exp e1 == eval_exp e2
  in
  eval_fml f
;;

(* TODO *)

eval (Imply (Imply (True, False), True));;

eval (Equal (Num 1, Plus (Num 1, Num 2)))
