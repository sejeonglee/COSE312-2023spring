exception NotImplemented

let dropWhile : ('a -> bool) -> 'a list -> 'a list =
 fun test lst ->
  let rec construct (f : 'a -> bool) (q : 'a list) =
    match q with
    | [] -> []
    | hd :: tl -> if f hd then construct f tl else hd :: construct f tl
  in
  construct test lst
;;

dropWhile (fun x -> x mod 2 = 0) [ 2; 4; 7; 9 ];;

dropWhile (fun x -> x > 5) [ 1; 3; 7 ];;

dropWhile (fun x -> x > 5) []
