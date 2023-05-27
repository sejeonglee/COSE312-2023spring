let live_def_set : Spvm.linstr -> Spvm.id BatSet.t =
 fun label_instruction ->
  let _, instruction = label_instruction in
  match instruction with
  | Spvm.FUNC_DEF (id, _, _)
  | Spvm.CALL (id, _, _)
  | Spvm.LIST_EMPTY id
  | Spvm.TUPLE_EMPTY id
  | Spvm.ITER_LOAD (id, _, _)
  | Spvm.ITER_LENGTH (id, _)
  | Spvm.ASSIGNV (id, _, _, _)
  | Spvm.ASSIGNC (id, _, _, _)
  | Spvm.ASSIGNU (id, _, _)
  | Spvm.COPY (id, _)
  | Spvm.COPYC (id, _)
  | Spvm.COPYS (id, _)
  | Spvm.COPYN id
  | Spvm.READ id
  | Spvm.INT_OF_STR (id, _)
  | Spvm.IS_INSTANCE (id, _, _)
  | Spvm.RANGE (id, _, _)
  | Spvm.ITER_STORE (id, _, _) (*혹시 a[x]를 따로 하나의 객체로 볼 수 있나?*)
  | Spvm.TUPLE_INSERT (id, _) ->
      BatSet.singleton id
  | Spvm.LIST_APPEND (_, _) (*보류*)
  | Spvm.LIST_INSERT (_, _) (*보류*)
  | Spvm.LIST_REV _ (*보류*) | Spvm.WRITE _ | Spvm.ASSERT _ | Spvm.UJUMP _
  | Spvm.CJUMP (_, _)
  | Spvm.CJUMPF (_, _)
  | Spvm.RETURN _ | Spvm.SKIP | Spvm.HALT ->
      BatSet.empty

let rec live_use_set : Spvm.linstr -> Spvm.id BatSet.t =
 fun label_instruction ->
  let _, instruction = label_instruction in
  match instruction with
  | Spvm.FUNC_DEF (_, _, linstrs) ->
      List.fold_right
        (fun linst set -> BatSet.union set (live_use_set linst))
        linstrs BatSet.empty
  | Spvm.CALL (_, name, ids) ->
      BatSet.union (BatSet.singleton name)
        (List.fold_right
           (fun id set -> BatSet.union set (BatSet.singleton id))
           ids BatSet.empty)
  | Spvm.ITER_LOAD (id3, id1, id2) | Spvm.ITER_STORE (id3, id1, id2) ->
      BatSet.union (BatSet.singleton id2)
        (BatSet.union (BatSet.singleton id3) (BatSet.singleton id1))
  | Spvm.RANGE (_, id1, id2)
  | Spvm.ASSIGNV (_, _, id1, id2)
  | Spvm.TUPLE_INSERT (id1, id2)
  | Spvm.LIST_APPEND (id1, id2)
  | Spvm.LIST_INSERT (id1, id2) ->
      BatSet.union (BatSet.singleton id1) (BatSet.singleton id2)
  | Spvm.RETURN id
  | Spvm.ITER_LENGTH (_, id)
  | Spvm.ASSIGNC (_, _, id, _)
  | Spvm.ASSIGNU (_, _, id)
  | Spvm.COPY (_, id)
  | Spvm.CJUMP (id, _)
  | Spvm.CJUMPF (id, _)
  | Spvm.WRITE id
  | Spvm.LIST_REV id
  | Spvm.INT_OF_STR (_, id)
  | Spvm.IS_INSTANCE (_, id, _)
  | Spvm.ASSERT id ->
      BatSet.singleton id
  | Spvm.LIST_EMPTY _ | Spvm.TUPLE_EMPTY _
  | COPYC (_, _)
  | COPYS (_, _)
  | Spvm.COPYN _ | Spvm.UJUMP _ | Spvm.READ _ | Spvm.SKIP | Spvm.HALT ->
      BatSet.empty
(* | _ -> BatSet.empty *)

let get_live_in_out_map_pre :
    Spvm.program ->
    (Spvm.label, Spvm.id BatSet.t) BatMap.t
    * (Spvm.label, Spvm.id BatSet.t) BatMap.t =
 fun pgm ->
  let rec initialize_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_set = BatSet.empty in
        let new_map = BatMap.add label new_set map in
        initialize_maps new_map tl
  in
  let rec initialize_succ_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_map = BatMap.add label [] map in
        initialize_succ_maps new_map tl
  in
  let in_map = ref (initialize_maps BatMap.empty pgm) in
  let out_map = ref (initialize_maps BatMap.empty pgm) in
  let rec make_successor_map pgm map =
    match pgm with
    | [] -> map
    | (cur_label, instruction) :: tl -> (
        let cur_list =
          match tl with
          | [] -> BatMap.find cur_label map
          | (next_inst_label, _) :: _ ->
              next_inst_label :: BatMap.find cur_label map
        in
        let map = BatMap.update cur_label cur_label cur_list map in
        match instruction with
        | Spvm.UJUMP next_label
        | Spvm.CJUMP (_, next_label)
        | Spvm.CJUMPF (_, next_label) ->
            let new_map =
              BatMap.update cur_label cur_label (next_label :: cur_list) map
            in
            make_successor_map tl new_map
        | _ -> make_successor_map tl map)
  in
  let successor_map =
    make_successor_map pgm (initialize_succ_maps BatMap.empty pgm)
  in
  let rec iterate pgm in_map out_map =
    match pgm with
    | [] -> (in_map, out_map)
    | (label, instruction) :: tl ->
        let in_map, out_map = iterate tl in_map out_map in
        let use_set = live_use_set (label, instruction) in
        let def_set = live_def_set (label, instruction) in
        let in_set =
          BatSet.union use_set (BatSet.diff (BatMap.find label out_map) def_set)
        in

        let new_in_map = BatMap.add label in_set in_map in
        let new_out_set =
          List.fold_left
            (fun acc succ_label ->
              let in_set = BatMap.find succ_label new_in_map in
              BatSet.union acc in_set)
            BatSet.empty
            (BatMap.find label successor_map)
        in
        let new_out_map = BatMap.add label new_out_set out_map in
        (new_in_map, new_out_map)
  in
  let loop_flag = ref true in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if BatMap.equal BatSet.equal !in_map new_in_map then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map
  done;
  (!in_map, !out_map)

let get_fn_closure_variables :
    Spvm.program -> (Spvm.id, Spvm.id BatSet.t) BatMap.t =
 fun pgm ->
  let ret_map = BatMap.empty in
  let rec get_fn_closure_variables' pgm ret_map =
    match pgm with
    | [] -> ret_map
    | (_, instruction) :: tl -> (
        match instruction with
        | Spvm.FUNC_DEF (id, args, body) ->
            let live_in_map, _ = get_live_in_out_map_pre body in
            let first_label, _ = List.hd body in
            let closures = BatMap.find first_label live_in_map in
            let closures_args_deleted =
              List.fold_right
                (fun arg closure_set -> BatSet.remove arg closure_set)
                args closures
            in
            BatMap.add id closures_args_deleted ret_map
        | _ -> get_fn_closure_variables' tl ret_map)
  in
  get_fn_closure_variables' pgm ret_map

let get_live_in_out_map :
    Spvm.program ->
    (Spvm.label, Spvm.id BatSet.t) BatMap.t
    * (Spvm.label, Spvm.id BatSet.t) BatMap.t =
 fun pgm ->
  let rec initialize_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_set = BatSet.empty in
        let new_map = BatMap.add label new_set map in
        initialize_maps new_map tl
  in
  let rec initialize_succ_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_map = BatMap.add label [] map in
        initialize_succ_maps new_map tl
  in
  let in_map = ref (initialize_maps BatMap.empty pgm) in
  let out_map = ref (initialize_maps BatMap.empty pgm) in
  let rec make_successor_map pgm map =
    match pgm with
    | [] -> map
    | (cur_label, instruction) :: tl -> (
        let cur_list =
          match tl with
          | [] -> BatMap.find cur_label map
          | (next_inst_label, _) :: _ ->
              next_inst_label :: BatMap.find cur_label map
        in
        let map = BatMap.update cur_label cur_label cur_list map in
        match instruction with
        | Spvm.UJUMP next_label
        | Spvm.CJUMP (_, next_label)
        | Spvm.CJUMPF (_, next_label) ->
            let new_map =
              BatMap.update cur_label cur_label (next_label :: cur_list) map
            in
            make_successor_map tl new_map
        | _ -> make_successor_map tl map)
  in
  let successor_map =
    make_successor_map pgm (initialize_succ_maps BatMap.empty pgm)
  in
  let rec iterate_reverse pgm closures =
    match pgm with
    | [] -> closures
    | (_, instruction) :: tl -> (
        match instruction with
        | Spvm.COPY (alias, f_id_cand)
          when not (BatMap.find_opt f_id_cand closures = None) ->
            let closure_set = BatMap.find f_id_cand closures in
            let new_closures = BatMap.add alias closure_set closures in
            iterate_reverse tl new_closures
        | _ -> iterate_reverse tl closures)
  in
  let closures = iterate_reverse pgm (get_fn_closure_variables pgm) in
  let rec iterate pgm in_map out_map =
    match pgm with
    | [] -> (in_map, out_map)
    | (label, instruction) :: tl ->
        let in_map, out_map = iterate tl in_map out_map in
        let use_set =
          match instruction with
          | Spvm.CALL (_, f_id, _) ->
              let closure_set =
                try BatMap.find f_id closures with Not_found -> BatSet.empty
              in
              BatSet.union closure_set (live_use_set (label, instruction))
          | _ -> live_use_set (label, instruction)
        in
        let def_set = live_def_set (label, instruction) in
        let in_set =
          BatSet.union use_set (BatSet.diff (BatMap.find label out_map) def_set)
        in

        let new_in_map = BatMap.add label in_set in_map in
        let new_out_set =
          List.fold_left
            (fun acc succ_label ->
              let in_set = BatMap.find succ_label new_in_map in
              BatSet.union acc in_set)
            BatSet.empty
            (BatMap.find label successor_map)
        in
        let new_out_map = BatMap.add label new_out_set out_map in
        (new_in_map, new_out_map)
  in
  let loop_flag = ref true in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if BatMap.equal BatSet.equal !in_map new_in_map then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map
  done;
  (!in_map, !out_map)

type definition = Spvm.id * Spvm.label

let string_of_definition (id, label) =
  "id, label: " ^ id ^ ", " ^ string_of_int label ^ "\n"

let rda_gen_kill_set : Spvm.linstr -> definition BatSet.t =
 fun label_instruction ->
  let label, instruction = label_instruction in
  match instruction with
  | Spvm.FUNC_DEF (name, _, _)
  | Spvm.CALL (name, _, _)
  | Spvm.LIST_EMPTY name
  | Spvm.TUPLE_EMPTY name
  | Spvm.ITER_LOAD (name, _, _)
  | Spvm.ITER_LENGTH (name, _)
  | Spvm.ASSIGNV (name, _, _, _)
  | Spvm.ASSIGNC (name, _, _, _)
  | Spvm.ASSIGNU (name, _, _)
  | Spvm.COPY (name, _)
  | Spvm.COPYC (name, _)
  | Spvm.COPYS (name, _)
  | Spvm.COPYN name
  | Spvm.READ name
  | Spvm.INT_OF_STR (name, _)
  | Spvm.IS_INSTANCE (name, _, _) ->
      BatSet.singleton (name, label) (* | ITER_STORE  Todo: *)
  | _ -> BatSet.empty

let get_rda_in_out_map :
    Spvm.program ->
    (Spvm.label, definition BatSet.t) BatMap.t
    * (Spvm.label, definition BatSet.t) BatMap.t =
 fun pgm ->
  let rec initialize_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_set = BatSet.empty in
        let new_map = BatMap.add label new_set map in
        initialize_maps new_map tl
  in
  let rec initialize_prec_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_map = BatMap.add label [] map in
        initialize_prec_maps new_map tl
  in
  let in_map = ref (initialize_maps BatMap.empty pgm) in
  let out_map = ref (initialize_maps BatMap.empty pgm) in
  let rec make_predecessor_map pgm map prev_label =
    match pgm with
    | [] -> map
    | (succ_label, instruction) :: tl -> (
        let cur_list = BatMap.find succ_label map in
        let map =
          if not (prev_label = 0) then
            BatMap.update succ_label succ_label (prev_label :: cur_list) map
          else map
        in
        match instruction with
        | Spvm.UJUMP label | Spvm.CJUMP (_, label) | Spvm.CJUMPF (_, label) ->
            let found_list = BatMap.find label map in
            let new_map =
              BatMap.update label label (succ_label :: found_list) map
            in
            make_predecessor_map tl new_map succ_label
        | _ -> make_predecessor_map tl map succ_label)
  in
  let predecessor_map =
    make_predecessor_map pgm (initialize_prec_maps BatMap.empty pgm) 0
  in
  let rec iterate pgm in_map out_map =
    match pgm with
    | [] -> (in_map, out_map)
    | (label, instruction) :: tl ->
        let gen_set = rda_gen_kill_set (label, instruction) in
        let new_in_set =
          List.fold_left
            (fun acc succ_label ->
              let out_set = BatMap.find succ_label out_map in
              BatSet.union acc out_set)
            BatSet.empty
            (BatMap.find label predecessor_map)
        in
        let new_in_map = BatMap.add label new_in_set in_map in
        let killed_new_in_set =
          let gen_list = BatSet.to_list gen_set in
          if List.length gen_list = 0 then new_in_set
          else
            BatSet.of_list
              (List.filter
                 (fun def -> not (fst def = fst (List.hd gen_list)))
                 (BatSet.to_list new_in_set))
        in

        let out_set = BatSet.union gen_set killed_new_in_set in
        let new_out_map = BatMap.add label out_set out_map in
        iterate tl new_in_map new_out_map
  in
  let loop_flag = ref true in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if
      BatMap.equal BatSet.equal !in_map new_in_map
      && BatMap.equal BatSet.equal !out_map new_out_map
    then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map
  done;
  (!in_map, !out_map)

let loop_optimization (pgm : Spvm.program) : Spvm.program =
  let rda_in_set, _ = get_rda_in_out_map pgm in
  let label_to_order = ref BatMap.empty in
  let whole_pgm = ref pgm in
  List.iteri
    (fun i (label, _) -> label_to_order := BatMap.add label i !label_to_order)
    pgm;
  let codes_in_loop pgm end_label =
    let rec find_to_loop_end' loop pgm =
      match pgm with
      | [] -> failwith ("not found end_label: " ^ string_of_int end_label)
      | (label, instruction) :: tl ->
          let current_loop = loop @ [ (label, instruction) ] in
          if label = end_label then current_loop
          else find_to_loop_end' current_loop tl
    in
    find_to_loop_end' [] pgm
  in
  let reorder_loop loop_pgm loop_start_label loop_end_label =
    let end_order = BatMap.find loop_end_label !label_to_order in
    let end_rda_set = BatMap.find loop_end_label rda_in_set in
    let rec reorder_loop' before_pgm after_pgm =
      match after_pgm with
      | [] -> before_pgm
      | (label, instruction) :: tl -> (
          match instruction with
          | Spvm.COPY (_, op_id)
          | Spvm.ASSIGNC (_, _, op_id, _)
          | Spvm.ASSIGNU (_, _, op_id) ->
              let in_set = BatMap.find label rda_in_set in
              let def_label = List.assoc op_id (BatSet.to_list in_set) in
              let def_order = BatMap.find def_label !label_to_order in
              let end_use_label =
                List.assoc op_id (BatSet.to_list end_rda_set)
              in
              let end_use_order = BatMap.find end_use_label !label_to_order in
              let loop_start_order =
                BatMap.find loop_start_label !label_to_order
              in
              if
                def_order < loop_start_order
                && not
                     (end_use_order > loop_start_order
                     && end_use_order < end_order)
              then reorder_loop' ((label, instruction) :: before_pgm) tl
              else reorder_loop' (before_pgm @ [ (label, instruction) ]) tl
          | _ -> reorder_loop' (before_pgm @ [ (label, instruction) ]) tl)
    in
    reorder_loop' [] loop_pgm
  in
  let cut_before_loop pgm start_label =
    let rec cut_before_loop' pgm =
      match pgm with
      | [] -> failwith ("not found start_label: " ^ string_of_int start_label)
      | (label, _) :: tl ->
          if label = start_label then pgm else cut_before_loop' tl
    in
    cut_before_loop' pgm
  in

  let rec find_loops pgm =
    match pgm with
    | [] -> !whole_pgm
    | (label, instruction) :: tl -> (
        print_endline ("label: " ^ string_of_int label);
        print_endline (Spvm.string_of_program !whole_pgm);
        match instruction with
        | Spvm.UJUMP to_label
        | Spvm.CJUMP (_, to_label)
        | Spvm.CJUMPF (_, to_label) ->
            if
              BatMap.find label !label_to_order
              > BatMap.find to_label !label_to_order
            then (
              let loop = cut_before_loop !whole_pgm to_label in
              let loop = codes_in_loop loop label in
              let loop = reorder_loop loop to_label label in
              let before_loop_codes =
                fst
                  (List.partition
                     (fun (label, _) ->
                       BatMap.find label !label_to_order
                       < BatMap.find to_label !label_to_order)
                     !whole_pgm)
              in
              whole_pgm := before_loop_codes @ loop @ tl;
              find_loops tl)
            else find_loops tl
        | _ -> find_loops tl)
  in
  find_loops pgm

let deadcode_elimination : Spvm.program -> Spvm.program =
 fun pgm ->
  let _, live_out_set = get_live_in_out_map pgm in

  let rec deadcode_elimination' pgm =
    match pgm with
    | [] -> []
    | (label, instruction) :: tl -> (
        match instruction with
        | Spvm.COPY (id, _) | Spvm.COPYC (id, _) | Spvm.COPYS (id, _) ->
            if BatSet.mem id (BatMap.find label live_out_set) then
              (label, instruction) :: deadcode_elimination' tl
            else deadcode_elimination' tl
        | Spvm.COPYN id ->
            if BatSet.mem id (BatMap.find label live_out_set) then
              (label, instruction) :: deadcode_elimination' tl
            else deadcode_elimination' tl
        | _ -> (label, instruction) :: deadcode_elimination' tl)
  in
  deadcode_elimination' pgm

let simple_propagation : Spvm.program -> Spvm.program =
 fun pgm ->
  let _, live_out_set = get_live_in_out_map pgm in
  let rec simple_propagation' pgm =
    match pgm with
    | [] -> []
    | (label, instruction) :: tl -> (
        match tl with
        | [] -> (label, instruction) :: []
        | (next_label, next_instruction) :: ttl -> (
            match next_instruction with
            | Spvm.COPY (obj, mid_cand) -> (
                match instruction with
                | COPY (mid, value) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.COPY (obj, value))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | COPYC (mid, value) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.COPYC (obj, value))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | COPYN mid ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then (next_label, Spvm.COPYN obj) :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | COPYS (mid, value) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.COPYS (obj, value))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | TUPLE_EMPTY mid ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.TUPLE_EMPTY obj)
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | LIST_EMPTY mid ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.LIST_EMPTY obj)
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | CALL (mid, f, args) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.CALL (obj, f, args))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | RANGE (mid, hi, lo) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.RANGE (obj, hi, lo))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | ITER_LOAD (mid, a, y) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.ITER_LOAD (obj, a, y))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                      (* | ITER_STORE (mid, midx, y) ->
                         if
                           mid = mid_cand
                           && not (BatSet.mem mid (BatMap.find label live_out_set))
                         then
                           (next_label, Spvm.ITER_STORE (obj, a, y))
                           :: simple_propagation' ttl
                         else (label, instruction) :: simple_propagation' tl *)
                      (*보류 - 얘는 COPY랑이 아닌 ITER_LOAD랑 짝*)
                | ITER_LENGTH (mid, value) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.ITER_LENGTH (obj, value))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | ASSIGNV (mid, bop, a, b) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.ASSIGNV (obj, bop, a, b))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | ASSIGNC (mid, bop, a, b) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.ASSIGNC (obj, bop, a, b))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | ASSIGNU (mid, uop, a) ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then
                      (next_label, Spvm.ASSIGNU (obj, uop, a))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | READ mid ->
                    if
                      mid = mid_cand
                      && not (BatSet.mem mid (BatMap.find label live_out_set))
                    then (next_label, Spvm.READ obj) :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | _ -> (label, instruction) :: simple_propagation' tl)
            | INT_OF_STR (obj, mid) -> (
                match instruction with
                | COPY (mid2, value) ->
                    if
                      mid = mid2
                      && not
                           (BatSet.mem mid
                              (BatMap.find next_label live_out_set))
                    then
                      (next_label, Spvm.INT_OF_STR (obj, value))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | _ -> (label, instruction) :: simple_propagation' tl)
            | IS_INSTANCE (obj, mid, type_s) -> (
                match instruction with
                | COPY (mid2, value) ->
                    if
                      mid = mid2
                      && not
                           (BatSet.mem mid
                              (BatMap.find next_label live_out_set))
                    then
                      (next_label, Spvm.IS_INSTANCE (obj, value, type_s))
                      :: simple_propagation' ttl
                    else (label, instruction) :: simple_propagation' tl
                | _ -> (label, instruction) :: simple_propagation' tl)
            | _ -> (label, instruction) :: simple_propagation' tl))
  in
  simple_propagation' pgm

let two_dist_propagation : Spvm.program -> Spvm.program =
 fun pgm ->
  let rec two_dist_propagation' pgm =
    match pgm with
    | [] -> []
    | (label, instruction) :: tl -> (
        match tl with
        | [] -> (label, instruction) :: []
        | (next_label, next_instruction) :: ttl -> (
            match ttl with
            | [] -> [ (label, instruction); (next_label, next_instruction) ]
            | (next2_label, next2_instruction) :: tttl -> (
                match instruction with
                | Spvm.COPY (mid_lst, lst) -> (
                    match next_instruction with
                    | Spvm.LIST_INSERT (mid_lst2, value) -> (
                        match next2_instruction with
                        | Spvm.COPY (obj, mid_lst3) ->
                            if mid_lst = mid_lst2 && mid_lst2 = mid_lst3 then
                              (next_label, Spvm.LIST_INSERT (lst, value))
                              :: two_dist_propagation'
                                   ((next2_label, Spvm.COPY (obj, lst)) :: tttl)
                            else
                              (label, instruction)
                              :: two_dist_propagation'
                                   ((next_label, next_instruction)
                                   :: (next2_label, next2_instruction)
                                   :: tttl)
                        | _ ->
                            (label, instruction)
                            :: two_dist_propagation'
                                 ((next_label, next_instruction)
                                 :: (next2_label, next2_instruction)
                                 :: tttl))
                    | Spvm.TUPLE_INSERT (mid_lst2, value) -> (
                        match next2_instruction with
                        | Spvm.COPY (obj, mid_lst3) ->
                            if mid_lst = mid_lst2 && mid_lst2 = mid_lst3 then
                              (next_label, Spvm.TUPLE_INSERT (lst, value))
                              :: two_dist_propagation'
                                   ((next2_label, Spvm.COPY (obj, lst)) :: tttl)
                            else
                              (label, instruction)
                              :: two_dist_propagation'
                                   ((next_label, next_instruction)
                                   :: (next2_label, next2_instruction)
                                   :: tttl)
                        | _ ->
                            (label, instruction)
                            :: two_dist_propagation'
                                 ((next_label, next_instruction)
                                 :: (next2_label, next2_instruction)
                                 :: tttl))
                    | _ ->
                        (label, instruction)
                        :: two_dist_propagation'
                             ((next_label, next_instruction)
                             :: (next2_label, next2_instruction)
                             :: tttl))
                | _ ->
                    (label, instruction)
                    :: two_dist_propagation'
                         ((next_label, next_instruction)
                         :: (next2_label, next2_instruction)
                         :: tttl))))
  in
  two_dist_propagation' pgm

let find_by_label : Spvm.program -> Spvm.label -> Spvm.instr =
 fun pgm label ->
  let rec find_by_label' pgm label =
    match pgm with
    | [] -> failwith "not found"
    | (pg_label, pg_inst) :: tl ->
        if pg_label = label then pg_inst else find_by_label' tl label
  in
  find_by_label' pgm label

type constant_type = TOP | BOTTOM | STR of string | INT of int | NONE

let string_of_constant_type : constant_type -> string =
 fun c ->
  match c with
  | TOP -> "TOP"
  | BOTTOM -> "BOTTOM"
  | STR s -> "STR " ^ s
  | INT i -> "INT " ^ string_of_int i
  | NONE -> "NONE"

type exp_type = ID of Spvm.id | EINT of int | ESTR of string

let get_constant_in_out_map :
    Spvm.program ->
    (Spvm.label, (Spvm.id, constant_type) BatMap.t) BatMap.t
    * (Spvm.label, (Spvm.id, constant_type) BatMap.t) BatMap.t =
 fun pgm ->
  let rec initialize_maps map pgm =
    (*\lambda x.bottom 으로 해야하지만 그냥 default를 사용하자*)
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_env = BatMap.empty in
        let label_added_map = BatMap.add label new_env map in
        initialize_maps label_added_map tl
  in
  let rec initialize_prec_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_map = BatMap.add label [] map in
        initialize_prec_maps new_map tl
  in
  let rec make_predecessor_map pgm map prev_label =
    match pgm with
    | [] -> map
    | (succ_label, instruction) :: tl -> (
        let cur_list = BatMap.find succ_label map in
        let map =
          if not (prev_label = 0) then
            BatMap.update succ_label succ_label (prev_label :: cur_list) map
          else map
        in
        match instruction with
        | Spvm.UJUMP label | Spvm.CJUMP (_, label) | Spvm.CJUMPF (_, label) ->
            let found_list = BatMap.find label map in
            let new_map =
              BatMap.update label label (succ_label :: found_list) map
            in
            make_predecessor_map tl new_map succ_label
        | _ -> make_predecessor_map tl map succ_label)
  in
  let transfer_function (inst : Spvm.instr)
      (d : (Spvm.id, constant_type) BatMap.t) =
    let eval_exp (e : exp_type) map : constant_type =
      match e with
      | ID id -> BatMap.find_default BOTTOM id map
      | ESTR s -> STR s
      | EINT i -> INT i
    in
    match inst with
    | Spvm.COPY (obj, copy_id) -> (
        match BatMap.find_default BOTTOM copy_id d with
        | INT v -> BatMap.add obj (INT v) d
        | STR s -> BatMap.add obj (STR s) d
        | TOP -> BatMap.add obj TOP d
        | _ -> BatMap.add obj BOTTOM d)
    | Spvm.COPYC (obj, c) -> BatMap.add obj (INT c) d
    | Spvm.COPYS (obj, s) -> BatMap.add obj (STR s) d
    | Spvm.COPYN obj -> BatMap.add obj NONE d
    | Spvm.ASSIGNV (obj, bop, a, b) -> (
        match (eval_exp (ID a) d, eval_exp (ID b) d) with
        | INT v1, INT v2 -> (
            match bop with
            | Spvm.ADD -> BatMap.add obj (INT (v1 + v2)) d
            | Spvm.SUB -> BatMap.add obj (INT (v1 - v2)) d
            | Spvm.MUL -> BatMap.add obj (INT (v1 * v2)) d
            | Spvm.DIV -> BatMap.add obj (INT (v1 / v2)) d
            | Spvm.MOD -> BatMap.add obj (INT (v1 mod v2)) d
            | Spvm.POW ->
                BatMap.add obj
                  (INT (int_of_float (float_of_int v1 ** float_of_int v2)))
                  d
            | Spvm.LT -> BatMap.add obj (INT (if v1 < v2 then 1 else 0)) d
            | Spvm.LE -> BatMap.add obj (INT (if v1 <= v2 then 1 else 0)) d
            | Spvm.GT -> BatMap.add obj (INT (if v1 > v2 then 1 else 0)) d
            | Spvm.GE -> BatMap.add obj (INT (if v1 >= v2 then 1 else 0)) d
            | Spvm.EQ -> BatMap.add obj (INT (if v1 = v2 then 1 else 0)) d
            | Spvm.NEQ -> BatMap.add obj (INT (if v1 <> v2 then 1 else 0)) d
            | Spvm.AND ->
                BatMap.add obj (INT (if v1 = 1 && v2 = 1 then 1 else 0)) d
            | Spvm.OR ->
                BatMap.add obj (INT (if v1 = 1 || v2 = 1 then 1 else 0)) d)
        | _ -> BatMap.add obj TOP d)
    | Spvm.ASSIGNC (obj, bop, a, n) -> (
        match (eval_exp (ID a) d, eval_exp (EINT n) d) with
        | INT v1, INT v2 -> (
            match bop with
            | Spvm.ADD -> BatMap.add obj (INT (v1 + v2)) d
            | Spvm.SUB -> BatMap.add obj (INT (v1 - v2)) d
            | Spvm.MUL -> BatMap.add obj (INT (v1 * v2)) d
            | Spvm.DIV -> BatMap.add obj (INT (v1 / v2)) d
            | Spvm.MOD -> BatMap.add obj (INT (v1 mod v2)) d
            | Spvm.POW ->
                BatMap.add obj
                  (INT (int_of_float (float_of_int v1 ** float_of_int v2)))
                  d
            | Spvm.LT -> BatMap.add obj (INT (if v1 < v2 then 1 else 0)) d
            | Spvm.LE -> BatMap.add obj (INT (if v1 <= v2 then 1 else 0)) d
            | Spvm.GT -> BatMap.add obj (INT (if v1 > v2 then 1 else 0)) d
            | Spvm.GE -> BatMap.add obj (INT (if v1 >= v2 then 1 else 0)) d
            | Spvm.EQ -> BatMap.add obj (INT (if v1 = v2 then 1 else 0)) d
            | Spvm.NEQ -> BatMap.add obj (INT (if v1 <> v2 then 1 else 0)) d
            | Spvm.AND ->
                BatMap.add obj (INT (if v1 = 1 && v2 = 1 then 1 else 0)) d
            | Spvm.OR ->
                BatMap.add obj (INT (if v1 = 1 || v2 = 1 then 1 else 0)) d)
        | _ -> BatMap.add obj TOP d)
    | Spvm.ASSIGNU (obj, op, a) -> (
        match eval_exp (ID a) d with
        | INT v -> (
            match op with
            | Spvm.UPLUS -> BatMap.add obj (INT v) d
            | Spvm.UMINUS -> BatMap.add obj (INT (-v)) d
            | Spvm.NOT -> BatMap.add obj (INT (if v = 1 then 0 else 1)) d)
        | _ -> BatMap.add obj TOP d)
    | Spvm.INT_OF_STR (obj, a) -> (
        match eval_exp (ID a) d with
        | STR s -> (
            try BatMap.add obj (INT (int_of_string s)) d
            with Failure _ -> BatMap.add obj BOTTOM d)
        | _ -> BatMap.add obj TOP d)
    | _ -> d
  in
  let in_map = ref (initialize_maps BatMap.empty pgm) in
  let out_map = ref (initialize_maps BatMap.empty pgm) in
  let predecessor_map =
    make_predecessor_map pgm (initialize_prec_maps BatMap.empty pgm) 0
  in
  let rec iterate pgm in_map out_map =
    match pgm with
    | [] -> (in_map, out_map)
    | (label, instruction) :: tl ->
        let new_in_map_line =
          List.fold_left
            (fun acc predec_label ->
              let predec_out_map = BatMap.find predec_label out_map in
              BatMap.merge
                (fun _ accv outv ->
                  if accv = None || accv = Some BOTTOM then outv
                  else if outv = None || outv = Some BOTTOM then accv
                  else if accv = outv then accv
                  else Some TOP)
                acc predec_out_map)
            BatMap.empty
            (BatMap.find label predecessor_map)
        in
        let new_in_map = BatMap.add label new_in_map_line in_map in
        let new_out_map_line = transfer_function instruction new_in_map_line in
        let new_out_map = BatMap.add label new_out_map_line out_map in
        iterate tl new_in_map new_out_map
  in

  let loop_flag = ref true in
  let iter_count = ref 0 in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if
      BatMap.equal (BatMap.equal (fun a b -> a = b)) !in_map new_in_map
      || !iter_count > 1000
    then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map;

    iter_count := !iter_count + 1
  done;
  (!in_map, !out_map)

let constant_folding : Spvm.program -> Spvm.program =
 fun whole_pgm ->
  let rec constant_folding' pgm =
    let in_map, _ = get_constant_in_out_map whole_pgm in
    match pgm with
    | [] -> []
    | (label, inst) :: tl -> (
        let in_map_line = BatMap.find label in_map in
        match inst with
        | Spvm.COPY (obj, copy_id) -> (
            match BatMap.find_default BOTTOM copy_id in_map_line with
            | INT v -> (label, Spvm.COPYC (obj, v)) :: constant_folding' tl
            | STR s -> (label, Spvm.COPYS (obj, s)) :: constant_folding' tl
            | NONE -> (label, Spvm.COPYN obj) :: constant_folding' tl
            | _ -> (label, inst) :: constant_folding' tl)
        | ASSIGNV (obj, bop, id1, copy_id) -> (
            match BatMap.find_default BOTTOM copy_id in_map_line with
            | INT v ->
                (label, Spvm.ASSIGNC (obj, bop, id1, v)) :: constant_folding' tl
            | _ -> (label, inst) :: constant_folding' tl)
        | ASSIGNC (obj, bop, copy_id, c) -> (
            match BatMap.find_default BOTTOM copy_id in_map_line with
            | INT v ->
                ( label,
                  Spvm.COPYC
                    ( obj,
                      match bop with
                      | Spvm.ADD -> v + c
                      | Spvm.SUB -> v - c
                      | Spvm.MUL -> v * c
                      | Spvm.DIV -> v * c
                      | Spvm.MOD -> v mod c
                      | Spvm.POW ->
                          int_of_float (float_of_int v ** float_of_int c)
                      | Spvm.LT -> if v < c then 1 else 0
                      | Spvm.LE -> if v <= c then 1 else 0
                      | Spvm.GT -> if v > c then 1 else 0
                      | Spvm.GE -> if v >= c then 1 else 0
                      | Spvm.EQ -> if v = c then 1 else 0
                      | Spvm.NEQ -> if v <> c then 1 else 0
                      | Spvm.AND -> if v = 1 && c = 1 then 1 else 0
                      | Spvm.OR -> if v = 1 || c = 1 then 1 else 0 ) )
                :: constant_folding' tl
            | _ -> (label, inst) :: constant_folding' tl)
        | ASSIGNU (obj, uop, copy_id) -> (
            match BatMap.find_default BOTTOM copy_id in_map_line with
            | INT v ->
                ( label,
                  Spvm.COPYC
                    ( obj,
                      match uop with
                      | Spvm.UPLUS -> v
                      | Spvm.UMINUS -> -v
                      | Spvm.NOT -> if v = 1 then 0 else 1 ) )
                :: constant_folding' tl
            | _ -> (label, inst) :: constant_folding' tl)
        | INT_OF_STR (obj, copy_id) -> (
            match BatMap.find_default BOTTOM copy_id in_map_line with
            | STR s -> (
                try
                  (label, Spvm.COPYC (obj, int_of_string s))
                  :: constant_folding' tl
                with Failure _ -> (label, inst) :: constant_folding' tl)
            | _ -> (label, inst) :: constant_folding' tl)
        | _ -> (label, inst) :: constant_folding' tl)
  in
  constant_folding' whole_pgm

type expression =
  | EBOP of Spvm.bop * Spvm.id * Spvm.id
  | EBOPC of Spvm.bop * Spvm.id * int
  | EUOP of Spvm.uop * Spvm.id
  | ECOPY of Spvm.id
  | EITER of Spvm.id * Spvm.id
  | NOT_E

let string_of_expression : expression -> string =
 fun c ->
  match c with
  | EBOP (_, id1, id2) -> "EBOP  " ^ id1 ^ " " ^ id2
  | EBOPC (_, id, c) -> "EBOPC  " ^ id ^ " " ^ string_of_int c
  | EUOP (_, id) -> "EUOP " ^ " " ^ id
  | ECOPY id -> "ECOPY " ^ id
  | EITER (id1, id2) -> "EITER " ^ id1 ^ " " ^ id2
  | NOT_E -> "NOT_E"

let transform_to_expression : Spvm.instr -> expression =
 fun inst ->
  match inst with
  | Spvm.COPY (_, copy_id) -> ECOPY copy_id
  | Spvm.ASSIGNV (_, bop, id1, id2) -> EBOP (bop, id1, id2)
  | Spvm.ASSIGNC (_, bop, id, c) -> EBOPC (bop, id, c)
  | Spvm.ASSIGNU (_, uop, id) -> EUOP (uop, id)
  | Spvm.ITER_LOAD (_, id1, id2) -> EITER (id1, id2)
  | _ -> NOT_E

let get_available_in_out_map :
    Spvm.program ->
    (Spvm.label, expression BatSet.t) BatMap.t
    * (Spvm.label, expression BatSet.t) BatMap.t =
 fun pgm ->
  let rec initialize_maps map pgm =
    match pgm with
    | [] -> map
    | (label, instr) :: tl ->
        let new_set =
          match transform_to_expression instr with
          | NOT_E -> BatSet.empty
          | e -> BatSet.singleton e
        in
        let new_map = BatMap.add label new_set map in
        initialize_maps new_map tl
  in
  let rec initialize_prec_maps map pgm =
    match pgm with
    | [] -> map
    | (label, _) :: tl ->
        let new_map = BatMap.add label [] map in
        initialize_prec_maps new_map tl
  in
  let in_map = ref (initialize_maps BatMap.empty pgm) in
  let out_map = ref (initialize_maps BatMap.empty pgm) in
  let rec make_predecessor_map pgm map prev_label =
    match pgm with
    | [] -> map
    | (succ_label, instruction) :: tl -> (
        let cur_list = BatMap.find succ_label map in
        let map =
          if not (prev_label = 0) then
            BatMap.update succ_label succ_label (prev_label :: cur_list) map
          else map
        in
        match instruction with
        | Spvm.UJUMP label | Spvm.CJUMP (_, label) | Spvm.CJUMPF (_, label) ->
            let found_list = BatMap.find label map in
            let new_map =
              BatMap.update label label (succ_label :: found_list) map
            in
            make_predecessor_map tl new_map succ_label
        | _ -> make_predecessor_map tl map succ_label)
  in
  let predecessor_map =
    make_predecessor_map pgm (initialize_prec_maps BatMap.empty pgm) 0
  in
  let rec iterate pgm in_map out_map =
    match pgm with
    | [] -> (in_map, out_map)
    | (label, instruction) :: tl ->
        let in_map, out_map = iterate tl in_map out_map in
        let new_in_set =
          List.fold_left
            (fun acc succ_label ->
              let out_set = BatMap.find succ_label out_map in
              if BatSet.is_empty acc then out_set
              else BatSet.intersect acc out_set)
            BatSet.empty
            (BatMap.find label predecessor_map)
        in
        let new_in_map = BatMap.add label new_in_set in_map in
        let gen_set =
          match transform_to_expression instruction with
          | NOT_E -> BatSet.empty
          | e -> BatSet.singleton e
        in
        let found_in_set = BatMap.find label in_map in
        let lhs =
          match instruction with
          | COPY (id, _)
          | COPYC (id, _)
          | COPYS (id, _)
          | COPYN id
          | ITER_LENGTH (id, _)
          | ITER_LOAD (id, _, _)
          | INT_OF_STR (id, _)
          | IS_INSTANCE (id, _, _)
          | ITER_STORE (id, _, _)
          | LIST_EMPTY id
          | TUPLE_EMPTY id
          | CALL (id, _, _)
          | RANGE (id, _, _)
          | ASSIGNV (id, _, _, _)
          | ASSIGNC (id, _, _, _)
          | ASSIGNU (id, _, _) ->
              Some id
          | _ -> None
        in

        let found_in_killed =
          BatSet.filter
            (fun e ->
              if lhs = None then true
              else
                match e with
                | EBOP (_, id1, id2) ->
                    (not (id1 = Option.get lhs)) && not (id2 = Option.get lhs)
                | EBOPC (_, id, _) -> not (id = Option.get lhs)
                | EUOP (_, id) -> not (id = Option.get lhs)
                | ECOPY id -> not (id = Option.get lhs)
                | EITER (id, _) -> not (id = Option.get lhs)
                | _ -> true)
            found_in_set
        in
        let new_out_set = BatSet.union gen_set found_in_killed in
        let new_out_map = BatMap.update label label new_out_set out_map in
        (new_in_map, new_out_map)
  in
  let loop_flag = ref true in
  let loop_count = ref 0 in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if
      BatMap.equal BatSet.equal !in_map new_in_map
      && BatMap.equal BatSet.equal !out_map new_out_map
      || !loop_count > 10000
    then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map;
    loop_count := !loop_count + 1
  done;
  (!in_map, !out_map)

let subexp_elimination : Spvm.program -> Spvm.program =
 fun whole_pgm ->
  let seek_map = (BatMap.empty : (expression, Spvm.id) BatMap.t) in
  let avail_in_map, avail_out_map = get_available_in_out_map whole_pgm in
  let rec subexp_elimination' pgm seek_map =
    match pgm with
    | [] -> []
    | (label, instruction) :: tl -> (
        let avail_out_set = BatMap.find label avail_out_map in
        let avail_in_set = BatMap.find label avail_in_map in
        if not (BatSet.diff avail_out_set avail_in_set = BatSet.empty) then
          let register_exp = transform_to_expression instruction in
          let register_id =
            match instruction with
            | COPY (id, _)
            | ITER_LOAD (id, _, _)
            | ASSIGNC (id, _, _, _)
            | ASSIGNV (id, _, _, _)
            | ASSIGNU (id, _, _) ->
                Some id
            | _ -> None
          in
          let new_seek_map =
            if Option.is_none register_id then seek_map
            else BatMap.add register_exp (Option.get register_id) seek_map
          in
          (label, instruction) :: subexp_elimination' tl new_seek_map
        else
          match transform_to_expression instruction with
          | NOT_E -> (label, instruction) :: subexp_elimination' tl seek_map
          | e ->
              if BatSet.mem e avail_in_set then
                let obj_id =
                  match instruction with
                  | COPY (id, _) -> id
                  | ITER_LOAD (id, _, _)
                  | ASSIGNC (id, _, _, _)
                  | ASSIGNV (id, _, _, _)
                  | ASSIGNU (id, _, _) ->
                      id
                  | _ -> raise (Failure "Not a register")
                in

                (label, Spvm.COPY (obj_id, BatMap.find e seek_map))
                :: subexp_elimination' tl seek_map
              else (label, instruction) :: subexp_elimination' tl seek_map)
  in
  subexp_elimination' whole_pgm seek_map

let optimize_one_step : Spvm.program -> Spvm.program =
 fun pgm ->
  let steps =
    [
      constant_folding;
      deadcode_elimination;
      simple_propagation;
      two_dist_propagation;
      subexp_elimination;
      (* loop_optimization; *)
    ]
  in
  List.fold_left (fun pgm step -> step pgm) pgm steps

let optimize_functions : Spvm.program -> Spvm.program =
 fun pgm ->
  let rec find_funcs pgm =
    match pgm with
    | [] -> []
    | (label, instruction) :: tl -> (
        match instruction with
        | Spvm.FUNC_DEF (id, args, body) ->
            (label, Spvm.FUNC_DEF (id, args, optimize_one_step body))
            :: find_funcs tl
        | _ -> (label, instruction) :: find_funcs tl)
  in
  find_funcs pgm

let optimize : Spvm.program -> Spvm.program =
 fun pgm ->
  (* let live_in_set, live_out_set = get_live_in_out_map pgm in
     print_endline "In set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set (fun s -> s))
          live_in_set);
     print_endline "Out set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set (fun s -> s))
          live_out_set); *)
  (*let pgm = constant_folding pgm in

    let const_in_map, const_out_map = get_constant_in_out_map pgm in
    print_endline "In set:";
    print_endline
    (Lib.Util.string_of_map string_of_int
    (Lib.Util.string_of_map (fun s -> s) string_of_constant_type)
    const_in_map);
       print_endline "Out set:";
       print_endline
       (Lib.Util.string_of_map string_of_int
       (Lib.Util.string_of_map (fun s -> s) string_of_constant_type)
       const_out_map);
       pgm *)
  (* let closures = get_fn_closure_variables pgm in
     print_endline
     ("Closures: "
     ^ Lib.Util.string_of_map
     (fun x -> x)
     (Lib.Util.string_of_set (fun s -> s))
     closures);
     pgm *)

  (* let pgm = !modified_pgm in *)
  (* let rda_in_set, rda_out_set = get_rda_in_out_map pgm in
     print_endline "In set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set (fun d ->
               fst d ^ " is defined at " ^ string_of_int (snd d)))
          rda_in_set);
     print_endline "Out set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set (fun d ->
               fst d ^ " is defined at " ^ string_of_int (snd d) ^ "\n"))
          rda_out_set); *)

  (* let pgm =
       two_dist_propagation
         (simple_propagation (deadcode_elimination (constant_folding pgm)))
     in
     let avail_in_map, avail_out_map = get_available_in_out_map pgm in
     print_endline "In set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set string_of_expression)
          avail_in_map);
     print_endline "Out set:";
     print_endline
       (Lib.Util.string_of_map string_of_int
          (Lib.Util.string_of_set string_of_expression)
          avail_out_map);
     subexp_elimination pgm *)
  let pgm = optimize_one_step pgm in
  let pgm = loop_optimization pgm in
  pgm
(* let modified_pgm = ref pgm in
   let loop_flag = ref true in
   while !loop_flag do
     let new_pgm = optimize_functions (optimize_one_step !modified_pgm) in
     if Spvm.string_of_program new_pgm = Spvm.string_of_program !modified_pgm
     then loop_flag := false;
     modified_pgm := new_pgm
   done;
   !modified_pgm *)
(* TODO *)
