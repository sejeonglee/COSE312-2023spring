(* 1번 *)
let rec fastrev : 'a list -> 'a list
= fun lst -> (* TODO *)
  let rec rev : 'a list -> 'a list -> 'a list = fun src dest->
    match src with
      | [] -> dest
      | hd::tl -> rev tl (hd :: dest) in rev lst [];;

(* 2번 *)
let rec check : int -> 'a list -> 'a list = fun toCheck lst ->
  match lst with
    | [] -> [toCheck]
    | hd::tl -> if (toCheck = hd) then []
                else check toCheck tl;;

let rec app : 'a list -> 'a list -> 'a list
= fun l1 l2 -> (* TODO *)
  match l1 with
    | [] -> l2
    | hd::tl -> app tl (l2 @ (check hd l2));;

(* 3번 *)
let rec check : int -> 'a list -> 'a list = fun toCheck lst ->
  match lst with
    | [] -> [toCheck]
    | hd::tl -> if (toCheck = hd) then []
                else check toCheck tl;;

let rec uniq : 'a list -> 'a list
= fun lst -> (* TODO *)
  let rec tmp : 'a list -> 'a list -> 'a list = fun src dest ->
    match src with
      | [] -> dest
      | hd::tl -> tmp tl (dest @ check hd dest) in tmp lst [];;

(* 4번 *)
let rec reduce : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
= fun f xs ys c -> (*TODO*)
  match xs, ys with
    | [], [] -> c
    | [], _ -> raise (Failure "This case is not reachable")
    | _, [] -> raise (Failure "This case is not reachable")
    | h1::t1, h2::t2 -> reduce f t1 t2 (f h1 h2 c);;

(* 5번 *)
type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec diff : aexp * string -> aexp
= fun (exp, x) -> (*TODO*)
  match exp with
    | Sum [] -> Const 0
    | Times [] -> Const 0
    | Const n -> Const 0
    | Var v -> if (v = x) then Const 1
               else Const 0
    | Power (v, n) -> if (v = x) then Times [Const n; Power (x, n - 1)]
                      else Const 0
    | Times (hd::tl) -> Sum (Times (diff (hd, x)::tl) :: [Times [hd; diff (Times tl, x)]])
    | Sum (hd::tl) -> Sum (diff (hd, x) :: [diff (Sum tl, x)]);;

(* 6번 *)
type exp = 
  X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp

let rec assign : exp -> exp -> exp = fun exp i ->
  match exp with
    | X -> i
    | INT n -> INT n
    | ADD (x, y) -> ADD (assign x i, assign y i)
    | SUB (x, y) -> SUB (assign x i, assign y i)
    | MUL (x, y) -> MUL (assign x i, assign y i)
    | DIV (x, y) -> DIV (assign x i, assign y i)
    | SIGMA (f, t, e) -> SIGMA (assign f i, assign t i, e);;

let rec calculator : exp -> int
= fun exp -> (*TODO*)
  match exp with
    | X -> raise (Failure "This case is unreachable")
    | INT n -> n
    | ADD (x, y) -> (calculator x) + (calculator y)
    | SUB (x, y) -> (calculator x) - (calculator y)
    | MUL (x, y) -> (calculator x) * (calculator y)
    | DIV (x, y) -> if ((calculator y) = 0) then raise (Failure "Div by zero error")
                    else (calculator x) / (calculator y)
    | SIGMA (f, t, e) -> if ((calculator f) > (calculator t)) then 0
                          else calculator (ADD (assign e f, SIGMA (ADD (f, INT 1), t, e)));;

(* 7번 *)
type vector = float list

type matrix = float list list

type layer = 
  | Input
  | Hidden of (matrix * vector)
  | Output of (matrix * vector)

type network = layer list

let rec addvec : vector -> vector -> vector
= fun v1 v2 -> (*TODO*)
  match v1, v2 with
    | _, [] -> []
    | [], _ -> []
    | h1::t1, h2::t2 -> (h1 +. h2) :: addvec t1 t2;;

let rec mulvec : vector -> vector -> float
= fun v1 v2 ->
  match v1, v2 with
    | _, [] -> 0.
    | [], _ -> 0.
    | h1::t1, h2::t2 -> (h1 *. h2) +. mulvec t1 t2;;

let rec mulmat: matrix -> vector -> vector
= fun m v -> (*TODO*)
  match m with
    | [] -> []
    | hd::tl -> mulvec hd v :: mulmat tl v;;

let rec lrp : matrix -> matrix = fun m ->
  match m with
    | [] -> []
    | hd::tl -> match hd with
                  | [] -> []
                  | h::t -> if (t = []) then []
                            else t :: (lrp tl);;
let rec prl : matrix -> vector = fun m ->
  match m with
    | [] -> []
    | hd::tl -> match hd with
                  | [] -> []
                  | h::t -> h :: (prl tl);;
let rec transpose : matrix -> matrix
= fun m-> (*TODO*)
  match m with
    | [] -> []
    | hd::tl -> (prl m) :: (transpose (lrp m));;

let rec argmax : float list -> int
= fun l -> (*TODO*)
  let rec num : float list -> int -> float -> int -> int = fun l i m midx ->
    match l with
      | [] -> midx
      | hd::tl -> if (i = 0) then num tl (i + 1) hd i
                  else num tl (i + 1) (if hd > m then hd else m) (if hd > m then i else midx) in num l 0 0.0 0;;

let rec activation : vector -> vector = fun v ->
  match v with
    | [] -> []
    | hd::tl -> (if (hd > 0.0) then hd else 0.0) :: (activation tl);;

let rec cal : layer -> vector -> vector = fun l v ->
  match l with 
    | Input -> v
    | Hidden (w, b) -> activation (addvec (mulmat (transpose w) v) b)
    | Output (w, b) -> addvec (mulmat (transpose w) v) b;;

let rec nneval : network -> vector -> int
= fun net v -> (*TODO*)
  match net with
    | [] -> argmax v
    | hd::tl -> nneval tl (cal hd v);;
