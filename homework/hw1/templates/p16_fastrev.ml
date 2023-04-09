exception NotImplemented

let range : int -> int -> int list =
 fun n1 n2 ->
  let rec range_rec n1 n2 =
    if n1 > n2 then [] else n1 :: range_rec (n1 + 1) n2
  in
  range_rec n1 n2

let fastrev : 'a list -> 'a list =
 fun lst ->
  let rec reverse (a : 'a list) (b : 'a list) : 'a list =
    match a with [] -> b | hd :: tl -> reverse tl (hd :: b)
  in
  reverse lst []
;;

(* TODO *)

fastrev (range 1 100000)
