exception NotImplemented

let max : int list -> int =
 fun lst ->
  let rec max_local : int * int list -> int =
   fun (n, l) ->
    match l with
    | [] -> n
    | hd :: tl -> max_local ((if hd > n then hd else n), tl)
  in
  max_local (min_int, lst)

let min : int list -> int =
 fun lst ->
  let rec min_local : int * int list -> int =
   fun (n, l) ->
    match l with
    | [] -> n
    | hd :: tl -> min_local ((if hd < n then hd else n), tl)
  in
  min_local (max_int, lst)
;;

(* TODO *)

max [ 1; 3; 5; 2 ];;

min [ 1; 3; 5; 2 ]
