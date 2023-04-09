exception NotImplemented

let rec fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b =
 fun f lst init ->
  match lst with [] -> init | hd :: tl -> f hd (fold_right f tl init)

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a =
 fun f init lst ->
  match lst with [] -> init | hd :: tl -> fold_left f (f init hd) tl

let rec length : 'a list -> int = fun l -> fold_right (fun a b -> b + 1) l 0;;

(* TODO *)

length [ 1; 2; 3 ]

let rec reverse : 'a list -> 'a list =
 fun l -> fold_left (fun rev_list v -> v :: rev_list) [] l
;;

(* TODO *)

reverse [ 1; 2; 3 ]

let rec is_all_pos : 'a list -> bool =
 fun l -> fold_left (fun cur_bool n -> n > 0 && cur_bool) true l
;;

(* TODO *)

is_all_pos [ 1; 2; 3 ];;

is_all_pos [ 1; -2; 3 ]

let rec map : ('a -> 'b) -> 'a list -> 'b list =
 fun f l -> fold_right (fun v accum_lst -> f v :: accum_lst) l []
;;

map (fun x -> x + 1) [ 1; 2; 3 ]

(* TODO *)

let rec filter : ('a -> bool) -> 'a list -> 'a list =
 fun p l ->
  fold_right
    (fun v filtered_lst -> if p v then v :: filtered_lst else filtered_lst)
    l []
;;

(* TODO *)

filter (fun x -> x > 0) [ 1; 2; 3 ];;

filter (fun x -> x > 0) [ 1; -2; 3 ]
