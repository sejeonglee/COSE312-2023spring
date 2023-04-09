exception NotImplemented

type nat = ZERO | SUCC of nat

let rec natadd : nat -> nat -> nat =
 fun n1 n2 -> match n1 with ZERO -> n2 | SUCC n -> natadd n (SUCC n2)

(* TODO *)

let natmul : nat -> nat -> nat =
 fun n1 n2 ->
  let rec n_add : nat -> nat -> nat =
   fun t n -> match t with ZERO -> n | SUCC v -> n_add v (natadd n2 n)
  in
  match n1 with ZERO -> ZERO | SUCC n -> n_add n n2

let two = SUCC (SUCC ZERO)

let three = SUCC (SUCC (SUCC ZERO));;

natadd two three;;

natadd ZERO three;;

natadd ZERO ZERO;;

natadd two ZERO;;

natmul two three;;

natmul ZERO three;;

natmul ZERO ZERO;;

natmul two ZERO;;

natmul two (SUCC ZERO);;

natmul (SUCC ZERO) (SUCC ZERO)
