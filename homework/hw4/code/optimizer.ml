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
  | Spvm.LIST_REV _ (*보류*)
  | Spvm.WRITE _ | Spvm.ASSERT _ | Spvm.UJUMP _
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
  | Spvm.CALL (_, _, ids) ->
      List.fold_right
        (fun id set -> BatSet.union set (BatSet.singleton id))
        ids BatSet.empty
  | Spvm.RANGE (_, id1, id2)
  | Spvm.ASSIGNV (_, _, id1, id2)
  | Spvm.TUPLE_INSERT (id1, id2)
  | Spvm.LIST_APPEND (id1, id2)
  | Spvm.LIST_INSERT (id1, id2) ->
      BatSet.union (BatSet.singleton id1) (BatSet.singleton id2)
  | Spvm.RETURN id
  | Spvm.ITER_LOAD (_, _, id)
  | Spvm.ITER_STORE (_, _, id)
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

let rda_gen_kill_set : Spvm.linstr -> Spvm.label BatSet.t =
 fun label_instruction ->
  let label, instruction = label_instruction in
  match instruction with
  | Spvm.FUNC_DEF (_, _, _)
  | Spvm.CALL (_, _, _)
  | Spvm.LIST_EMPTY _ | Spvm.TUPLE_EMPTY _
  | Spvm.ITER_LOAD (_, _, _)
  | Spvm.ITER_LENGTH (_, _)
  | Spvm.ASSIGNV (_, _, _, _)
  | Spvm.ASSIGNC (_, _, _, _)
  | Spvm.ASSIGNU (_, _, _)
  | Spvm.COPY (_, _)
  | Spvm.COPYC (_, _)
  | Spvm.COPYS (_, _)
  | Spvm.COPYN _ | Spvm.READ _
  | Spvm.INT_OF_STR (_, _)
  | Spvm.IS_INSTANCE (_, _, _) ->
      BatSet.singleton label
  | _ -> BatSet.empty

let get_rda_in_out_map :
    Spvm.program ->
    (Spvm.label, Spvm.label BatSet.t) BatMap.t
    * (Spvm.label, Spvm.label BatSet.t) BatMap.t =
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
          if prev_label != 0 then
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
        let out_set = BatSet.union gen_set (BatMap.find label in_map) in
        let new_out_map = BatMap.add label out_set out_map in
        let new_in_set =
          List.fold_left
            (fun acc succ_label ->
              let out_set = BatMap.find succ_label out_map in
              BatSet.union acc out_set)
            BatSet.empty
            (BatMap.find label predecessor_map)
        in
        let new_in_map = BatMap.add label new_in_set in_map in
        iterate tl new_in_map new_out_map
  in
  let loop_flag = ref true in
  while !loop_flag do
    let new_in_map, new_out_map = iterate pgm !in_map !out_map in
    if BatMap.equal BatSet.equal !in_map new_in_map then loop_flag := false;
    in_map := new_in_map;
    out_map := new_out_map
  done;
  (!in_map, !out_map)

let deadcode_elimination : Spvm.program -> Spvm.program =
 fun pgm ->
  print_endline "Deadcode Elimination";
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

let find_by_label : Spvm.program -> Spvm.label -> Spvm.instr =
 fun pgm label ->
  let rec find_by_label' pgm label =
    match pgm with
    | [] -> failwith "not found"
    | (pg_label, pg_inst) :: tl ->
        if pg_label = label then pg_inst else find_by_label' tl label
  in
  find_by_label' pgm label

let constant_folding : Spvm.program -> Spvm.program =
 fun whole_pgm ->
  let modified_pgm = ref whole_pgm in
  let rec constant_folding' pgm =
    let rda_in_set, _ = get_rda_in_out_map whole_pgm in
    match pgm with
    | [] -> ()
    | (label, inst) :: tl ->
        print_endline ("Label: " ^ string_of_int label);
        (match inst with
        | Spvm.COPYC (id, c) ->
            modified_pgm :=
              List.map
                (fun (pg_label, pg_inst) ->
                  (* pg label은 바꿔야 하는 label*)
                  if not (BatSet.mem label (BatMap.find pg_label rda_in_set))
                  then (pg_label, pg_inst)
                  else if
                    not
                      (List.fold_left
                         (fun found_bool find_label ->
                           if find_label = label then found_bool || false
                           else
                             let inst =
                               find_by_label !modified_pgm find_label
                             in
                             match inst with
                             | COPY (obj, _)
                             | COPYC (obj, _)
                             | COPYS (obj, _)
                             | INT_OF_STR (obj, _)
                             | IS_INSTANCE (obj, _, _)
                             | ASSIGNC (obj, _, _, _)
                             | ASSIGNV (obj, _, _, _)
                             | ASSIGNU (obj, _, _)
                             | ITER_LOAD (obj, _, _)
                             | ITER_LENGTH (obj, _)
                             | CALL (obj, _, _)
                             | LIST_EMPTY obj
                             | TUPLE_EMPTY obj
                             | RANGE (obj, _, _) ->
                                 found_bool || obj = id
                             | _ -> found_bool || false)
                         false
                         (BatSet.elements (BatMap.find pg_label rda_in_set)))
                  then
                    match pg_inst with
                    | Spvm.COPY (obj, copy_id) ->
                        if copy_id = id then (pg_label, Spvm.COPYC (obj, c))
                        else (pg_label, pg_inst)
                    | Spvm.ASSIGNV (obj, bop, op1, op2) ->
                        if op2 = id then
                          (pg_label, Spvm.ASSIGNC (obj, bop, op1, c))
                        else (pg_label, pg_inst)
                    | Spvm.ASSIGNC (obj, bop, op1, opn) ->
                        if op1 = id then
                          let result =
                            match bop with
                            | Spvm.ADD -> opn + c
                            | Spvm.SUB -> opn - c
                            | Spvm.MUL -> opn * c
                            | Spvm.DIV -> opn * c
                            | Spvm.MOD -> opn mod c
                            | Spvm.POW ->
                                int_of_float (float_of_int opn ** float_of_int c)
                            | Spvm.LT -> if opn < c then 1 else 0
                            | Spvm.LE -> if opn <= c then 1 else 0
                            | Spvm.GT -> if opn > c then 1 else 0
                            | Spvm.GE -> if opn >= c then 1 else 0
                            | Spvm.EQ -> if opn = c then 1 else 0
                            | Spvm.NEQ -> if opn <> c then 1 else 0
                            | Spvm.AND -> if opn = 1 && c = 1 then 1 else 0
                            | Spvm.OR -> if opn = 1 || c = 1 then 1 else 0
                          in
                          (pg_label, Spvm.COPYC (obj, result))
                        else (pg_label, pg_inst)
                    | _ -> (pg_label, pg_inst)
                  else (pg_label, pg_inst))
                !modified_pgm
        | Spvm.COPYS (id, c) ->
            modified_pgm :=
              List.map
                (fun (pg_label, pg_inst) ->
                  if not (BatSet.mem label (BatMap.find pg_label rda_in_set))
                  then (pg_label, pg_inst)
                  else
                    match pg_inst with
                    | Spvm.COPY (obj, copy_id) ->
                        if copy_id = id then (pg_label, Spvm.COPYS (obj, c))
                        else (pg_label, pg_inst)
                    | Spvm.INT_OF_STR (obj, copy_id) ->
                        if copy_id = id then
                          (pg_label, Spvm.COPYC (obj, int_of_string c))
                        else (pg_label, pg_inst)
                    | _ -> (pg_label, pg_inst))
                !modified_pgm
        | _ -> ());
        constant_folding' tl
  in
  constant_folding' whole_pgm;
  !modified_pgm

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
  let modified_pgm = ref pgm in
  let loop_flag = ref true in
  while !loop_flag do
    print_endline "Optimizing...";
    let new_pgm = deadcode_elimination (constant_folding !modified_pgm) in
    if Spvm.string_of_program new_pgm = Spvm.string_of_program !modified_pgm
    then loop_flag := false;
    modified_pgm := new_pgm
  done;
  !modified_pgm
(* let pgm = deadcode_elimination (constant_folding pgm) in
   print_endline "Second Phase";
   let rda_in_set, rda_out_set = get_rda_in_out_map pgm in
   print_endline "In set:";
   print_endline
     (Lib.Util.string_of_map string_of_int
        (Lib.Util.string_of_set string_of_int)
        rda_in_set);
   print_endline "Out set:";
   print_endline
     (Lib.Util.string_of_map string_of_int
        (Lib.Util.string_of_set string_of_int)
        rda_out_set);
   let pgm = constant_folding pgm in
   pgm *)
(* TODO *)
