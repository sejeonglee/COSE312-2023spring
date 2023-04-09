exception NotImplemented

type exp =
  | X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp

let calculator : exp -> int =
 fun exp ->
  let rec substitute (e : exp) (v : exp) : exp =
    match e with
    | X -> v
    | INT n -> INT n
    | ADD (x, y) -> ADD (substitute x v, substitute y v)
    | SUB (x, y) -> SUB (substitute x v, substitute y v)
    | MUL (x, y) -> MUL (substitute x v, substitute y v)
    | DIV (x, y) -> DIV (substitute x v, substitute y v)
    | SIGMA (f, t, e) -> SIGMA (substitute f v, substitute t v, e)
  in
  let rec cal (e : exp) : int =
    match e with
    | X -> 0
    | INT n -> n
    | ADD (x, y) -> cal x + cal y
    | SUB (x, y) -> cal x - cal y
    | MUL (x, y) -> cal x * cal y
    | DIV (x, y) ->
        if cal y = 0 then raise (Failure "Division by Zero") else cal x / cal y
    | SIGMA (lower_bound, upper_bound, e) ->
        if cal lower_bound <= cal upper_bound then
          cal
            (ADD
               ( substitute e lower_bound,
                 SIGMA (ADD (lower_bound, INT 1), upper_bound, e) ))
        else 0
  in
  cal exp
;;

calculator (SIGMA (INT 1, INT 10, SUB (MUL (X, X), INT 1)))
