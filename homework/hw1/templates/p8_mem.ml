exception NotImplemented

type btree = Empty | Node of int * btree * btree

let mem : int -> btree -> bool =
 fun n t ->
  let rec seek : int -> btree -> bool =
   fun n t ->
    match t with
    | Empty -> false
    | Node (value, t1, t2) ->
        if value == n then true else seek n t1 || seek n t2
  in
  seek n t

let t1 = Node (1, Empty, Empty)

let t2 = Node (1, Node (2, Empty, Empty), Node (3, Empty, Empty));;

mem 1 t1;;

(*true*)
mem 2 t1;;

(*false*)
mem 1 t2;;

(*true*)
mem 3 t2;;

(*true*)
mem 4 t2 (*false*)
