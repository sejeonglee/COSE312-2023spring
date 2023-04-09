exception NotImplemented

let binarize : int -> int list =
 fun n ->
  let rec div : int * int list -> int * int list =
   fun (n, l) -> if n > 0 then div (n / 2, (n mod 2) :: l) else (n, l)
  in
  match div (n, []) with _, l -> l
;;

binarize 2;;

binarize 3;;

binarize 8;;

binarize 17;;

binarize 16;;

binarize 15
