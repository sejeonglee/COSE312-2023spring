exception NotImplemented;;

let range : int -> int -> int list
= fun n1 n2 -> let rec range_rec n1 n2 =
  if n1 > n2 then []
  else n1::(range_rec (n1+1) n2) in
  range_rec n1 n2;;(*TODO*)

range 3 7;;
range 7 3;;