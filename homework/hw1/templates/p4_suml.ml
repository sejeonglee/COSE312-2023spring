exception NotImplemented

let rec suml : int list list -> int =
 fun l ->
  let rec sum : int list -> int =
   fun li -> match li with [] -> 0 | hd :: tl -> hd + sum tl
  in
  match l with [] -> 0 | hd :: tl -> sum hd + suml tl
;;

(* TODO *)

suml [ [ 1; 2; 3 ]; []; [ -1; 5; 2 ]; [ 7 ] ]
