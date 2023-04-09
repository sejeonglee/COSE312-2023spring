open Util

type symbol = T of string | N of string | Epsilon | End
type production = symbol * symbol list
type cfg = symbol list * symbol list * symbol * production list

let string_of_symbol s =
  match s with T x -> x | N x -> x | Epsilon -> "epsilon" | End -> "$"

let string_of_prod (lhs, rhs) =
  string_of_symbol lhs ^ " -> "
  ^ string_of_list ~first:"" ~last:"" ~sep:" " string_of_symbol rhs

module FIRST = struct
  type t = (symbol, symbol BatSet.t) BatMap.t

  let empty = BatMap.empty

  let find : symbol -> t -> symbol BatSet.t =
   fun s t -> try BatMap.find s t with _ -> BatSet.empty

  let add : symbol -> symbol -> t -> t =
   fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t

  let add_set : symbol -> symbol BatSet.t -> t -> t =
   fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string =
   fun t ->
    BatMap.foldi
      (fun s ss str ->
        str ^ string_of_symbol s ^ " |-> "
        ^ string_of_set string_of_symbol ss
        ^ "\n")
      t ""
end

module FOLLOW = struct
  type t = (symbol, symbol BatSet.t) BatMap.t

  let empty = BatMap.empty

  let find : symbol -> t -> symbol BatSet.t =
   fun s t -> try BatMap.find s t with _ -> BatSet.empty

  let add : symbol -> symbol -> t -> t =
   fun s1 s2 t -> BatMap.add s1 (BatSet.add s2 (find s1 t)) t

  let add_set : symbol -> symbol BatSet.t -> t -> t =
   fun s1 ss t -> BatSet.fold (fun s2 -> add s1 s2) ss t

  let tostring : t -> string =
   fun t ->
    BatMap.foldi
      (fun s ss str ->
        str ^ string_of_symbol s ^ " |-> "
        ^ string_of_set string_of_symbol ss
        ^ "\n")
      t ""
end

module ParsingTable = struct
  type t = (symbol * symbol, (symbol * symbol list) BatSet.t) BatMap.t

  let empty = BatMap.empty

  let find (nonterm, term) t =
    try BatMap.find (nonterm, term) t with _ -> BatSet.empty

  let add (nonterm, term) prod t =
    BatMap.add (nonterm, term) (BatSet.add prod (find (nonterm, term) t)) t

  let tostring : t -> string =
   fun t ->
    BatMap.foldi
      (fun (nonterm, term) prods str ->
        str ^ string_of_symbol nonterm ^ ", " ^ string_of_symbol term ^ " |-> "
        ^ string_of_set string_of_prod prods
        ^ "\n")
      t ""

  let foldi = BatMap.foldi
  let for_all = BatMap.for_all
end

let compute_first_set : cfg -> FIRST.t =
 fun grammar ->
  let _, terms, _, prods = grammar in
  let update first_set =
    List.fold_left
      (fun set prod ->
        let lhs, rhs = prod in
        let rec traverse_prod_rhs (rhs : symbol list) : FIRST.t =
          match rhs with
          | [] -> FIRST.add lhs Epsilon set
          | s :: ss ->
              FIRST.add_set lhs
                (BatSet.remove Epsilon (FIRST.find s set))
                (if not (BatSet.find_opt Epsilon (FIRST.find s set) = None) then
                   traverse_prod_rhs ss
                 else set)
        in

        traverse_prod_rhs rhs)
      first_set prods
  in
  let initial_first_set =
    List.fold_left
      (fun set symbol -> FIRST.add symbol symbol set)
      FIRST.empty
      (terms @ [ Epsilon; End ])
  in
  let current_first_set = ref (update initial_first_set) in
  let break_flag = ref true in
  while !break_flag do
    let updated_first_set = update !current_first_set in
    if FIRST.tostring !current_first_set = FIRST.tostring updated_first_set then
      break_flag := false
    else ();
    current_first_set := updated_first_set
  done;
  !current_first_set

let compute_follow_set : cfg -> FOLLOW.t =
 fun grammar ->
  let _, _, start, prods = grammar in
  let first_set = compute_first_set grammar in
  let initial_follow_set = FOLLOW.add start End FOLLOW.empty in
  let rec get_first_of_str (beta : symbol list) =
    match beta with
    | [] -> BatSet.singleton Epsilon
    | s :: ss ->
        let first_s = FIRST.find s first_set in
        if not (BatSet.find_opt Epsilon first_s = None) then
          BatSet.union (BatSet.remove Epsilon first_s) (get_first_of_str ss)
        else first_s
  in
  let update follow_set =
    List.fold_left
      (fun fold_set prod ->
        let a, rhs = prod in
        let rec traverse_prod_rhs (rhs : symbol list) (set : FOLLOW.t) :
            FOLLOW.t =
          match rhs with
          | [] -> set
          | b :: beta -> (
              match b with
              | N _ ->
                  if List.length beta = 0 then
                    FOLLOW.add_set b (FOLLOW.find a set) set (* CASE 3*)
                  else
                    let first_beta = get_first_of_str beta in
                    let case2_set =
                      FOLLOW.add_set b (BatSet.remove Epsilon first_beta) set
                    in
                    let case4_set =
                      if not (BatSet.find_opt Epsilon first_beta = None) then
                        FOLLOW.add_set b (FOLLOW.find a case2_set) case2_set
                      else case2_set
                    in
                    traverse_prod_rhs beta case4_set
              | _ -> traverse_prod_rhs beta set)
        in
        traverse_prod_rhs rhs fold_set)
      follow_set prods
  in
  let current_follow_set = ref (update initial_follow_set) in
  let break_flag = ref true in
  while !break_flag do
    let updated_follow_set = update !current_follow_set in
    if FOLLOW.tostring !current_follow_set = FOLLOW.tostring updated_follow_set
    then break_flag := false
    else ();
    current_follow_set := updated_follow_set
  done;
  !current_follow_set

let construct_parsing_table : cfg -> ParsingTable.t =
 fun grammar ->
  let _, _, _, prods = grammar in
  let first_set = compute_first_set grammar in
  let follow_set = compute_follow_set grammar in
  let rec get_first_of_str (alpha : symbol list) =
    match alpha with
    | [] -> BatSet.singleton Epsilon
    | s :: ss ->
        let first_s = FIRST.find s first_set in
        if not (BatSet.find_opt Epsilon first_s = None) then
          BatSet.union (BatSet.remove Epsilon first_s) (get_first_of_str ss)
        else first_s
  in
  let rec traverse_prods (prods : production list) (table : ParsingTable.t) :
      ParsingTable.t =
    match prods with
    | [] -> table
    | prod :: tl ->
        let a, alpha = prod in
        let first_alpha = get_first_of_str alpha in

        let case1_table =
          BatSet.fold
            (fun s t ->
              if BatSet.is_empty (ParsingTable.find (a, s) t) then
                ParsingTable.add (a, s) prod t
              else raise (Failure "Not LL1"))
            (BatSet.remove Epsilon first_alpha)
            table
        in
        let follow_A = FOLLOW.find a follow_set in
        let case2_1_table =
          if not (BatSet.find_opt Epsilon first_alpha = None) then
            BatSet.fold
              (fun b t ->
                if BatSet.is_empty (ParsingTable.find (a, b) t) then
                  ParsingTable.add (a, b) prod t
                else raise (Failure "Not LL1"))
              follow_A case1_table
          else case1_table
        in
        (if
           (not (BatSet.find_opt Epsilon first_alpha = None))
           && not (BatSet.find_opt End follow_A = None)
         then ParsingTable.add (a, End) prod case2_1_table
         else case2_1_table)
        |> traverse_prods tl
  in
  traverse_prods prods ParsingTable.empty

let check_LL1 : cfg -> bool =
 fun grammar ->
  (* print_string (FIRST.tostring (compute_first_set grammar)); *)
  (* print_string (FOLLOW.tostring (compute_follow_set grammar)); *)
  (* print_string (ParsingTable.tostring (construct_parsing_table grammar)); *)
  try
    ignore (construct_parsing_table grammar);
    true
  with Failure _ -> false

(* TODO *)

let parse : cfg -> symbol list -> bool =
 fun grammar str ->
  let _, _, start, _ = grammar in
  let parsing_table = construct_parsing_table grammar in
  match str with
  | [] -> true
  | first_w :: _ -> (
      let a = ref first_w in
      let stack = ref [ start ] in
      let w = ref str in
      try
        while not (List.length !stack = 0) do
          (* print_string
               ("stack: "
               ^ string_of_list string_of_symbol !stack
               ^ "  | input: "
               ^ string_of_list string_of_symbol !w
               ^ "  | a: " ^ string_of_symbol !a);
             print_newline (); *)
          match !stack with
          | [] -> ()
          | x :: tl -> (
              if x = !a then (
                stack := tl;
                w := List.tl !w;
                a := List.hd !w)
              else
                match x with
                | T _ -> raise (Failure "Parse Error")
                | _ ->
                    (if
                       BatSet.is_empty (ParsingTable.find (x, !a) parsing_table)
                     then raise (Failure "Parse Error")
                     else
                       let prod =
                         BatSet.choose (ParsingTable.find (x, !a) parsing_table)
                       in
                       let _, rhs = prod in
                       stack := rhs @ tl);
                    ())
        done;
        true
      with Failure _ -> false)
