(*P1*)
let prime : int -> bool
= fun n -> 
    let rec iter : int -> int -> bool = fun n i -> 
      if n < 2 then false
      else if i = n then true
      else if (n mod i) = 0 then false
      else iter n (i + 1) in iter n 2;;

(*P2*)
let range : int -> int -> int list
= fun n1 n2 ->
  let rec iter : int -> int -> int list -> int list = fun n1 n2 l->
    if n1 > n2 then l
    else n1 :: iter (n1 + 1) n2 l in iter n1 n2 [];;

(*P3*)
let dfact : int -> int
= fun n -> 
  let rec iter : int -> int -> int = fun n i ->
    if i <= 1 then 1
    else i * iter n (i - 2) in iter n n;;

(*P4*)
let iter : int * (int -> int) -> (int -> int)
= fun (n,f) -> 
	let rec func : (int -> int) -> int -> (int -> int) = fun f n ->
		if n = 0 then (fun x -> x)
    else (fun x -> (func f (n - 1)) (f x)) in func f n;;
    
(*P5*)
type nat = ZERO | SUCC of nat

let natadd : nat -> nat -> nat
= fun n1 n2 -> (*TODO*)
  let rec adder n1 n2 n =
    if n = n1 then n2 
    else SUCC (adder n1 n2 (SUCC n)) in adder n1 n2 ZERO;;

let natmul : nat -> nat -> nat
= fun n1 n2 -> (*TODO*)
  let rec muler n1 n2 n =
    if n = n1 then ZERO
    else natadd n2 (muler n1 n2 (SUCC n)) in muler n1 n2 ZERO;;

(*P6*)
type btree = 
  | Leaf of int
  | Left of btree
  | Right of btree
  | LeftRight of btree * btree;;

let mirror : btree -> btree
= fun tree -> (*TODO*)
  let rec mirroror tree =
    match tree with
      | Leaf num -> Leaf num
      | Left b -> Right (mirroror b)
      | Right b -> Left (mirroror b)
      | LeftRight (left, right) -> LeftRight (mirroror right, mirroror left) in mirroror tree;;

(*P7*)
type formula = 
  | True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp

and exp = 
  | Num of int
  | Plus of exp * exp
  | Minus of exp * exp

let rec expr : exp -> int = fun e ->
  match e with
    | Num (num) -> num
    | Plus (left, right) -> expr (left) + expr (right)
    | Minus (left, right) -> expr (left) - expr (right);;

let eval : formula -> bool
= fun f -> (*TODO*)
  let rec div f =
    match f with
      | True -> true
      | False -> false
      | Not (ev) -> if (div ev) then false else true
      | AndAlso (left, right) -> (div left) && (div right)
      | OrElse (left, right) -> (div left) || (div right)
      | Imply (left, right) -> (div (Not left)) || (div right)
      | Equal (left, right) -> (expr left) = (expr right) in div f;;

(*P8*)
let all : ('a -> bool) -> 'a list -> bool
= fun f lst -> (*TODO*)
  let rec cond f lst =
    match lst with
      | [] -> true
      | hd::tl -> if (f hd) then cond f tl
                  else false in cond f lst;;

(*P9*)
let drop : ('a -> bool) -> 'a list -> 'a list
= fun f lst -> (*TODO*)
  let rec cond f lst =
    match lst with
      | [] -> []
      | hd::tl -> if (f hd) then [] @ (cond f tl) 
                  else hd::tl in cond f lst;;

(*P10*)
let rec length : int list -> int = fun lst ->
  match lst with
    | [] -> 1
    | hd::tl -> 10 * (length tl);;
    
let lst2int : int list -> int
= fun lst -> (*TODO*)
  let rec tmp lst =
    match lst with
      | [] -> 0
      | hd::tl -> hd * (length tl) + (tmp tl) in tmp lst;;


(*P11*)
let concat : 'a list list -> 'a list
= fun lst -> (*TODO*)
  let rec div lst =
    match lst with
      | [] -> []
      | h::t -> h @ (div t) in div lst;;
