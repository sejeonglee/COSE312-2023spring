exception NotImplemented

type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let diff : aexp * string -> aexp =
 fun (exp, x) ->
  let rec diff_exp (exp : aexp) : aexp =
    match exp with
    | Const _ -> Const 0
    | Var s -> if s = x then Const 1 else Const 0
    | Power (s, i) ->
        if s = x then
          match i with
          | 0 -> Const 0
          | 1 -> Const 1
          | n -> Times [ Const n; Power (s, n - 1) ]
        else Const 0
    | Sum [] -> Const 0
    | Sum (hd :: tl) -> (
        match diff_exp (Sum tl) with
        | Sum lst -> Sum (diff_exp hd :: lst)
        | _ -> Sum [ diff_exp hd ])
    | Times [] -> Const 0
    | Times (hd :: tl) ->
        Sum [ Times (diff_exp hd :: tl); Times [ hd; diff_exp (Times tl) ] ]
  in
  diff_exp exp
;;

(* TODO *)

diff (Sum [ Power ("x", 2); Times [ Const 2; Var "x" ]; Const 1 ], "x");;

diff (Power ("x", 1), "x");;

diff (Times [], "x");;

diff (Times [ Const 2 ], "x");;

diff (Times [ Const 2; Var "x" ], "x");;

diff (Sum [ Const 2; Power ("x", 2) ], "x");;

diff (Sum [ Power ("x", 2) ], "x");;

diff (Power ("x", 2), "x")
