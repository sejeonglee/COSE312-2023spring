exception NotImplemented;;

let pascal : int * int -> int
= fun (n, m) -> let rec binomial_coef n k =
  if k<0 || k>n then 0
  else (
    if n==0 then 1
    else (binomial_coef (n-1) (k-1) + binomial_coef (n-1) k)
  ) in binomial_coef n m;; (* TODO *)


pascal (0,0);;
pascal (1, 0);;
pascal (1, 1);;
pascal (2, 1);;
pascal (4, 2);;