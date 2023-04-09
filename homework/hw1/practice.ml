let rec binomial_coef n k =
  if k<0 || k>n then 0
  else (
    if n==0 then 1
    else (binomial_coef (n-1) (k-1) + binomial_coef (n-1) k)
  );;

let divisible : int * int -> bool = fun (n, m) -> (n mod m == 0);;


binomial_coef 0 0;;
binomial_coef 1 1;;
binomial_coef 1 0;;
binomial_coef 2 1;;
binomial_coef 3 1;;