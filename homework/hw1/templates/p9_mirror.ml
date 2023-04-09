exception NotImplemented

type btree =
  | Leaf of int
  | Left of btree
  | Right of btree
  | LeftRight of btree * btree

let rec mirror : btree -> btree =
 fun tree ->
  match tree with
  | Leaf n -> Leaf n
  | Left t -> Right (mirror t)
  | Right t -> Left (mirror t)
  | LeftRight (tl, tr) -> LeftRight (mirror tr, mirror tl)
;;

(*TODO*)

mirror (Left (LeftRight (Leaf 1, Leaf 2)))
