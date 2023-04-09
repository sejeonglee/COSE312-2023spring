exception NotImplemented;;

let prime : int -> bool
= fun n -> 
  let divisible : int * int -> bool = fun (n, m) -> (n mod m == 0) in
  let rec iter : int -> bool = fun m ->
    if m == 1 then true else
    if divisible (n,m) then false else iter (m-1)
    in iter (n - 1);;
      


prime 2;;
prime 3;;
prime 4;;
prime 17;;
