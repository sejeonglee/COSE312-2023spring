exception NotImplemented

let rec sigma : (int -> int) -> int -> int -> int =
 fun f a b -> if a <= b then f a + sigma f (a + 1) b else 0
;;

(* TODO *)

sigma (fun x -> x) 1 10;;

sigma (fun x -> x * x) 1 7
