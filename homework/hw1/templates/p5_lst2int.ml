exception NotImplemented

let lst2int : int list -> int =
 fun lst ->
  let rec get_digit : int list -> int =
   fun l ->
    let rec digits_of_n : int -> int =
     fun n -> if n / 10 == 0 then 10 else digits_of_n (n / 10) * 10
    in
    match l with
    | [] -> 1
    | [ n ] -> digits_of_n n
    | hd :: tl -> digits_of_n hd * get_digit tl
  in
  let rec add_digit : int list -> int =
   fun l ->
    match l with [] -> 0 | hd :: tl -> (hd * get_digit tl) + add_digit tl
  in
  add_digit lst
;;

lst2int [ 2; 3; 4; 5 ];;

lst2int [ 1 ];;

lst2int [ 1; 2; 3; 4; 5; 5; 6; 7 ];;

lst2int [ 23; 45 ];;

lst2int [ 2 ]
