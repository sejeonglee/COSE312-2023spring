exception NotImplemented

let uniq : 'a list -> 'a list =
 fun lst ->
  let rec find (l : 'a list) (v : 'a) : bool =
    match l with [] -> false | hd :: tl -> if hd == v then true else find tl v
  in
  let rec traverse (q : 'a list) (uniq_lst : 'a list) : 'a list =
    match q with
    | [] -> uniq_lst
    | hd :: tl ->
        if find uniq_lst hd then traverse tl uniq_lst
        else traverse tl (uniq_lst @ [ hd ])
  in
  traverse lst []
;;

uniq [ 5; 6; 5; 4 ] (*[5;6;4]*)
