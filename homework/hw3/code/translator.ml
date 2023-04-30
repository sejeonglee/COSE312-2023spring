(* open Spy *)
(* open Lib.Util *)
(* open Spvm *)

let temp_var_index = ref 0
let label_index = ref 1

let new_temp_var () =
  temp_var_index := !temp_var_index + 1;
  ".t" ^ string_of_int !temp_var_index

let new_label () =
  label_index := !label_index + 1;
  !label_index

let range_like lst =
  let rec range_rec lst i =
    match lst with [] -> [] | _ :: tl -> i :: range_rec tl (i + 1)
  in
  range_rec lst 0

exception Not_Implemented of string
exception Error of string (* raise when syntax is beyond Spy *)

let rec translate : Spy.program -> Spvm.program =
 fun src_pg ->
  let rec translate_expr : Spy.expr -> Spvm.id * Spvm.linstr list =
   fun expr ->
    match expr with
    | Spy.BoolOp (boolop, expr_lst) ->
        let bop = match boolop with Spy.And -> Spvm.AND | Spy.Or -> Spvm.OR in
        let rec translate_boolop ?prev (expr_lst : Spy.expr list) :
            Spvm.id * Spvm.linstr list =
          match expr_lst with
          | [] -> (Option.get prev, [])
          | hd :: tl ->
              let id, code = translate_expr hd in
              let t_condition = new_temp_var () in
              let final_condition, tl_code =
                translate_boolop ~prev:t_condition tl
              in
              ( final_condition,
                code
                @ [
                    ( new_label (),
                      if Option.is_none prev then Spvm.COPY (t_condition, id)
                      else Spvm.ASSIGNV (t_condition, bop, id, Option.get prev)
                    );
                  ]
                @ tl_code )
        in
        translate_boolop expr_lst
    | Spy.Compare (exp_l, op, exp_r) ->
        let id_l, code_l = translate_expr exp_l in
        let id_r, code_r = translate_expr exp_r in
        let id = new_temp_var () in
        let operator =
          match op with
          | Spy.Eq -> Spvm.EQ
          | Spy.NotEq -> Spvm.NEQ
          | Spy.Lt -> Spvm.LT
          | Spy.LtE -> Spvm.LE
          | Spy.Gt -> Spvm.GT
          | Spy.GtE -> Spvm.GE
        in
        ( id,
          code_l @ code_r
          @ [ (new_label (), Spvm.ASSIGNV (id, operator, id_l, id_r)) ] )
    | Spy.UnaryOp (op, exp) ->
        let id, code = translate_expr exp in
        let id' = new_temp_var () in
        let operator =
          match op with
          | Spy.USub -> Spvm.UMINUS
          | Spy.Not -> Spvm.NOT
          | Spy.UAdd -> Spvm.UPLUS
        in
        (id', code @ [ (new_label (), Spvm.ASSIGNU (id', operator, id)) ])
    | Spy.BinOp (exp_l, op, exp_r) ->
        let id_l, code_l = translate_expr exp_l in
        let id_r, code_r = translate_expr exp_r in
        let id = new_temp_var () in
        let operator =
          match op with
          | Spy.Add -> Spvm.ADD
          | Spy.Sub -> Spvm.SUB
          | Spy.Mult -> Spvm.MUL
          | Spy.Div -> Spvm.DIV
          | Spy.Mod -> Spvm.MOD
          | Spy.Pow -> Spvm.POW
        in
        ( id,
          code_l @ code_r
          @ [ (new_label (), Spvm.ASSIGNV (id, operator, id_l, id_r)) ] )
    | Spy.Constant c -> (
        match c with
        | Spy.CInt n ->
            let id = new_temp_var () in
            let label = new_label () in
            (id, [ (label, Spvm.COPYC (id, n)) ])
        | Spy.CBool b ->
            let id = new_temp_var () in
            let label = new_label () in
            (id, [ (label, Spvm.COPYC (id, if b then 1 else 0)) ])
        | Spy.CString s ->
            let id = new_temp_var () in
            let label = new_label () in
            (id, [ (label, Spvm.COPYS (id, s)) ])
        | Spy.CNone ->
            let id = new_temp_var () in
            let label = new_label () in
            (id, [ (label, Spvm.COPYN id) ]))
    | Spy.Tuple exp_list ->
        let tuple_id = new_temp_var () in
        let tuple = Spvm.TUPLE_EMPTY tuple_id in
        let rec translate_tuple : Spy.expr list -> Spvm.linstr list =
         fun exp_list ->
          match exp_list with
          | [] -> []
          | hd :: tl ->
              translate_tuple tl
              @
              let id, code = translate_expr hd in
              code @ [ (new_label (), Spvm.TUPLE_INSERT (tuple_id, id)) ]
        in

        (tuple_id, [ (new_label (), tuple) ] @ translate_tuple exp_list)
    | Spy.List exp_list ->
        let list_id = new_temp_var () in
        let list = Spvm.LIST_EMPTY list_id in
        let rec translate_list : Spy.expr list -> Spvm.linstr list =
         fun exp_list ->
          match exp_list with
          | [] -> []
          | hd :: tl ->
              translate_list tl
              @
              let id, code = translate_expr hd in
              code @ [ (new_label (), Spvm.LIST_INSERT (list_id, id)) ]
        in

        (list_id, [ (new_label (), list) ] @ translate_list exp_list)
    | Spy.Name name -> (name, [])
    | Spy.Call (name_exp, params_exp) -> (
        let name_id, name_code = translate_expr name_exp in
        if Str.string_match (Str.regexp ".+\\.append") name_id 0 then
          let lst_id = List.hd (Str.split (Str.regexp "\\.") name_id) in
          let params_list = List.map translate_expr params_exp in
          let param_id_list = List.map fst params_list in
          let param_code =
            List.fold_right (fun a lst -> snd a @ lst) params_list []
          in
          let append_param_id = List.hd param_id_list in
          let none_id = new_temp_var () in
          let label = new_label () in
          ( none_id,
            name_code @ param_code
            @ [
                (label, Spvm.LIST_APPEND (lst_id, append_param_id));
                (new_label (), Spvm.COPYN none_id);
              ] )
        else
          match name_id with
          | "isinstance" ->
              let params_list = List.map translate_expr params_exp in
              let param_id_list = List.map fst params_list in
              let param_code =
                List.fold_right (fun a lst -> snd a @ lst) params_list []
              in
              let fst_param_id = List.hd param_id_list in
              let snd_param_id = List.hd (List.tl param_id_list) in
              let id = new_temp_var () in
              let label = new_label () in
              ( id,
                name_code @ param_code
                @ [ (label, Spvm.IS_INSTANCE (id, fst_param_id, snd_param_id)) ]
              )
          | "len" ->
              let id = new_temp_var () in
              let params_list = List.map translate_expr params_exp in
              let param_id_list = List.map fst params_list in
              let fst_param_id = List.hd param_id_list in
              ( id,
                name_code
                @ [ (new_label (), Spvm.ITER_LENGTH (id, fst_param_id)) ] )
          | "range" ->
              let params_list = List.map translate_expr params_exp in
              let param_id_list = List.map fst params_list in
              let param_code =
                List.fold_right (fun a lst -> snd a @ lst) params_list []
              in
              if List.length param_id_list == 1 then
                let fst_param_id = new_temp_var () in
                let snd_param_id = List.hd param_id_list in
                let id = new_temp_var () in
                let label = new_label () in
                ( id,
                  name_code @ param_code
                  @ [
                      (new_label (), Spvm.COPYC (fst_param_id, 0));
                      (label, Spvm.RANGE (id, fst_param_id, snd_param_id));
                    ] )
              else
                let fst_param_id = List.hd param_id_list in
                let snd_param_id = List.hd (List.tl param_id_list) in
                let id = new_temp_var () in
                let label = new_label () in
                ( id,
                  name_code @ param_code
                  @ [ (label, Spvm.RANGE (id, fst_param_id, snd_param_id)) ] )
          | "input" ->
              let id = new_temp_var () in
              let label = new_label () in
              (id, name_code @ [ (label, Spvm.READ id) ])
          | "int" ->
              let id = new_temp_var () in
              let params_list = List.map translate_expr params_exp in
              let param_id_list = List.map fst params_list in
              let fst_param_id = List.hd param_id_list in
              ( id,
                name_code
                @ [ (new_label (), Spvm.INT_OF_STR (id, fst_param_id)) ] )
          | "print" ->
              let new_line_t = new_temp_var () in
              let none_id = new_temp_var () in
              ( none_id,
                (List.map
                   (fun param ->
                     let param_t, param_code = translate_expr param in
                     let space_t = new_temp_var () in
                     param_code
                     @ [
                         (new_label (), Spvm.COPYS (space_t, " "));
                         (new_label (), Spvm.WRITE param_t);
                         (new_label (), Spvm.WRITE space_t);
                       ])
                   params_exp
                |> List.flatten)
                @ [
                    (new_label (), Spvm.COPYS (new_line_t, "\n"));
                    (new_label (), Spvm.WRITE new_line_t);
                    (new_label (), Spvm.COPYN none_id);
                  ] )
          | _ ->
              let params_list = List.map translate_expr params_exp in
              let param_id_list = List.map fst params_list in
              let param_code =
                List.fold_right (fun a lst -> snd a @ lst) params_list []
              in
              let id = new_temp_var () in
              let label = new_label () in
              ( id,
                name_code @ param_code
                @ [
                    (new_label (), Spvm.SKIP);
                    (label, Spvm.CALL (id, name_id, param_id_list));
                  ] ))
    | Spy.Attribute (exp, id) ->
        let exp_id, exp_code = translate_expr exp in
        let attribute_t_id = exp_id ^ "." ^ id in
        ( attribute_t_id,
          exp_code @ [ (new_label (), Spvm.COPYN attribute_t_id) ] )
    | Spy.Subscript (exp_out, exp_in) ->
        let exp_out_id, exp_out_code = translate_expr exp_out in
        let exp_in_id, exp_in_code = translate_expr exp_in in
        let t_id = new_temp_var () in
        ( t_id,
          exp_out_code @ exp_in_code
          @ [ (new_label (), Spvm.ITER_LOAD (t_id, exp_out_id, exp_in_id)) ] )
    | Spy.Lambda (id_lst, exp) ->
        let f_id = new_temp_var () in
        let exp_id, exp_code = translate_expr exp in
        ( f_id,
          [
            ( new_label (),
              Spvm.FUNC_DEF
                (f_id, id_lst, exp_code @ [ (new_label (), Spvm.RETURN exp_id) ])
            );
          ] )
    | IfExp (condition_exp, true_exp, false_expr) ->
        let condition_id, condition_code = translate_expr condition_exp in
        let true_id, true_code = translate_expr true_exp in
        let false_id, false_code = translate_expr false_expr in
        let true_label = new_label () in
        let false_label = new_label () in
        let end_label = new_label () in
        let id = new_temp_var () in
        ( id,
          condition_code @ true_code @ false_code
          @ [
              (new_label (), Spvm.CJUMPF (condition_id, false_label));
              (true_label, Spvm.SKIP);
              (new_label (), Spvm.COPY (id, true_id));
              (new_label (), Spvm.UJUMP end_label);
              (false_label, Spvm.SKIP);
              (new_label (), Spvm.COPY (id, false_id));
              (new_label (), Spvm.UJUMP end_label);
              (end_label, Spvm.SKIP);
            ] )
    | ListComp (expr, comp_lst) ->
        let list_id = new_temp_var () in
        let list_cursor = new_temp_var () in
        let rec condition_list_apply lst loop_label exit_label =
          match lst with
          | [] -> []
          | hd :: tl ->
              let hd_id, hd_code = translate_expr hd in
              let cond_code =
                [ (new_label (), Spvm.CJUMPF (hd_id, loop_label)) ]
              in
              hd_code @ cond_code
              @ condition_list_apply tl loop_label exit_label
        in
        let rec translate_for lst =
          match lst with
          | [] ->
              let expr_id, expr_code = translate_expr expr in
              expr_code
              @ [
                  (new_label (), Spvm.LIST_APPEND (list_id, expr_id));
                  ( new_label (),
                    Spvm.ASSIGNC (list_cursor, Spvm.ADD, list_cursor, 1) );
                ]
          | (for_v, for_it, cond_lst) :: tl ->
              let v_id, v_code = translate_expr for_v in
              let it_id, it_code = translate_expr for_it in
              let loop_label = new_label () in
              let exit_label = new_label () in

              let index_id = new_temp_var () in
              let next_index_id = new_temp_var () in
              let n_id = new_temp_var () in
              let loop_condition_id = new_temp_var () in

              let if_cond_code =
                condition_list_apply cond_lst loop_label exit_label
              in
              let loop_code = translate_for tl in
              it_code @ v_code
              @ [
                  (new_label (), Spvm.ITER_LENGTH (n_id, it_id));
                  (new_label (), Spvm.COPYC (index_id, -1));
                  (loop_label, Spvm.SKIP);
                  ( new_label (),
                    Spvm.ASSIGNC (next_index_id, Spvm.ADD, index_id, 1) );
                  (new_label (), Spvm.COPY (index_id, next_index_id));
                  ( new_label (),
                    Spvm.ASSIGNV (loop_condition_id, Spvm.LT, index_id, n_id) );
                  (new_label (), Spvm.CJUMPF (loop_condition_id, exit_label));
                  (new_label (), Spvm.ITER_LOAD (v_id, it_id, index_id));
                ]
              @ if_cond_code @ loop_code
              @ [
                  (new_label (), Spvm.UJUMP loop_label); (exit_label, Spvm.SKIP);
                ]
        in
        ( list_id,
          [
            (new_label (), Spvm.LIST_EMPTY list_id);
            (new_label (), Spvm.COPYC (list_cursor, 0));
          ]
          @ translate_for comp_lst )
   (* | _ -> (new_temp_var (), [ (new_label (), Spvm.SKIP) ]) *)
  in

  let rec translate_stmt ?break_label ?continue_label (stmt : Spy.stmt) :
      Spvm.program =
    match stmt with
    | Assign (lhs_list, rhs) -> (
        let rec assign_nested (l : Spy.expr) (r : Spvm.id * Spvm.linstr list) =
          match l with
          | Spy.Name name ->
              let l_id, l_code = translate_expr l in
              ( l_id,
                snd r @ l_code @ [ (new_label (), Spvm.COPY (name, fst r)) ] )
          | Spy.Tuple exp_list ->
              let rec assign_tuple (exp_list : Spy.expr list)
                  (r_tuple : Spvm.id * Spvm.linstr list) (i : int) =
                match exp_list with
                | [] -> ("end", [])
                | hd :: tl ->
                    let hd_id, hd_code = translate_expr hd in
                    let index = new_temp_var () in
                    let nested_r = new_temp_var () in
                    let nested_code =
                      [
                        (new_label (), Spvm.COPYC (index, i));
                        ( new_label (),
                          Spvm.ITER_LOAD (nested_r, fst r_tuple, index) );
                      ]
                    in
                    ( hd_id,
                      snd (assign_nested hd (nested_r, nested_code))
                      @ snd (assign_tuple tl r_tuple (i + 1))
                      @ hd_code )
              in
              let tuple_assined_code = snd (assign_tuple exp_list r 0) in
              let l_id, l_code = translate_expr l in
              (l_id, snd r @ tuple_assined_code @ l_code)
          | Spy.List exp_list ->
              let rec assign_list (exp_list : Spy.expr list)
                  (r_list : Spvm.id * Spvm.linstr list) (i : int) =
                match exp_list with
                | [] -> ("end", [])
                | hd :: tl ->
                    let hd_id, hd_code = translate_expr hd in
                    let index = new_temp_var () in
                    let nested_r = new_temp_var () in
                    let nested_code =
                      [
                        (new_label (), Spvm.COPYC (index, i));
                        ( new_label (),
                          Spvm.ITER_LOAD (nested_r, fst r_list, index) );
                      ]
                    in
                    ( hd_id,
                      snd (assign_nested hd (nested_r, nested_code))
                      @ snd (assign_list tl r_list (i + 1))
                      @ hd_code )
              in
              let list_assined_code = snd (assign_list exp_list r 0) in
              let l_id, l_code = translate_expr l in
              (l_id, snd r @ list_assined_code @ l_code)
          | Spy.Subscript (exp_out, exp_in) ->
              let exp_out_id, exp_out_code = translate_expr exp_out in
              let exp_in_id, exp_in_code = translate_expr exp_in in
              let t_id = new_temp_var () in
              ( t_id,
                snd r @ exp_out_code @ exp_in_code
                @ [
                    ( new_label (),
                      Spvm.ITER_STORE (exp_out_id, exp_in_id, fst r) );
                  ] )
          | _ -> raise (Not_Implemented "assign_nested")
        in
        let rec chain_lst list =
          match list with
          | [] -> translate_expr rhs
          | hd :: tl -> assign_nested hd (chain_lst tl)
        in
        match chain_lst lhs_list with _, code -> code)
    | Expr exp ->
        let _, code = translate_expr exp in
        code
    | If (condition, true_program, false_program) ->
        let condition_id, condition_code = translate_expr condition in
        let false_label = new_label () in
        let false_code =
          List.flatten
            (List.map
               (translate_stmt ~break_label:(Option.get break_label)
                  ~continue_label:(Option.get continue_label))
               false_program)
        in
        let true_label = new_label () in
        let true_code =
          List.flatten
            (List.map
               (translate_stmt ~break_label:(Option.get break_label)
                  ~continue_label:(Option.get continue_label))
               true_program)
        in
        let end_label = new_label () in
        condition_code
        @ [
            (new_label (), Spvm.CJUMP (condition_id, true_label));
            (false_label, Spvm.SKIP);
          ]
        @ false_code
        @ [ (new_label (), Spvm.UJUMP end_label); (true_label, Spvm.SKIP) ]
        @ true_code
        @ [ (end_label, Spvm.SKIP) ]
    | While (condition, loop_program) ->
        let condition_id, condition_code = translate_expr condition in
        let loop_label = new_label () in
        let exit_label = new_label () in
        let loop_code =
          List.flatten
            (List.map
               (translate_stmt ~break_label:exit_label
                  ~continue_label:loop_label)
               loop_program)
        in
        [ (loop_label, Spvm.SKIP) ]
        @ condition_code
        @ [ (new_label (), Spvm.CJUMPF (condition_id, exit_label)) ]
        @ loop_code
        @ [ (new_label (), Spvm.UJUMP loop_label); (exit_label, Spvm.SKIP) ]
    | AugAssign (exp_l, op, exp_r) -> (
        let bop =
          match op with
          | Spy.Add -> Spvm.ADD
          | Spy.Sub -> Spvm.SUB
          | Spy.Mult -> Spvm.MUL
          | Spy.Div -> Spvm.DIV
          | Spy.Mod -> Spvm.MOD
          | Spy.Pow -> Spvm.POW
        in
        match exp_l with
        | Spy.Name _ ->
            let left_id, left_code = translate_expr exp_l in
            let right_id, right_code = translate_expr exp_r in

            left_code @ right_code
            @ [ (new_label (), Spvm.ASSIGNV (left_id, bop, left_id, right_id)) ]
        | Spy.Subscript (exp_out, exp_in) ->
            let exp_out_id, exp_out_code = translate_expr exp_out in
            let exp_in_id, exp_in_code = translate_expr exp_in in
            let right_id, right_code = translate_expr exp_r in
            let st_id = new_temp_var () in
            let t_id = new_temp_var () in
            right_code @ exp_out_code @ exp_in_code
            @ [
                (new_label (), Spvm.ITER_LOAD (st_id, exp_out_id, exp_in_id));
                (new_label (), Spvm.ASSIGNV (t_id, bop, st_id, right_id));
                (new_label (), Spvm.ITER_STORE (exp_out_id, exp_in_id, t_id));
              ]
        | _ -> raise (Not_Implemented "AugAssign"))
    | Break ->
        if Option.is_none break_label then
          raise (Not_Implemented "break point is not given")
        else [ (new_label (), Spvm.UJUMP (Option.get break_label)) ]
    | Continue ->
        if Option.is_none continue_label then
          raise (Not_Implemented "continue point is not given")
        else [ (new_label (), Spvm.UJUMP (Option.get continue_label)) ]
    | For (exp_i, exp_it, for_program) ->
        let exp_i_id, exp_i_code = translate_expr exp_i in
        let exp_it_id, exp_it_code = translate_expr exp_it in
        let loop_label = new_label () in
        let exit_label = new_label () in
        let loop_code =
          List.flatten
            (List.map
               (translate_stmt ~break_label:exit_label
                  ~continue_label:loop_label)
               for_program)
        in
        let index_id = new_temp_var () in
        let next_index_id = new_temp_var () in
        let n_id = new_temp_var () in
        let condition_id = new_temp_var () in
        exp_it_code @ exp_i_code
        @ [
            (new_label (), Spvm.ITER_LENGTH (n_id, exp_it_id));
            (new_label (), Spvm.COPYC (index_id, -1));
            (loop_label, Spvm.SKIP);
            (new_label (), Spvm.ASSIGNC (next_index_id, Spvm.ADD, index_id, 1));
            (new_label (), Spvm.COPY (index_id, next_index_id));
            (new_label (), Spvm.ASSIGNV (condition_id, Spvm.LT, index_id, n_id));
            (new_label (), Spvm.CJUMPF (condition_id, exit_label));
            (new_label (), Spvm.ITER_LOAD (exp_i_id, exp_it_id, index_id));
          ]
        @ loop_code
        @ [ (new_label (), Spvm.UJUMP loop_label); (exit_label, Spvm.SKIP) ]
    | FunctionDef (func_id, args, func_program) ->
        let none_id = new_temp_var () in
        let func_code =
          List.flatten
            (List.map
               (translate_stmt ~break_label:(Option.get break_label)
                  ~continue_label:(Option.get continue_label))
               func_program)
          @ [
              (new_label (), Spvm.COPYN none_id);
              (new_label (), Spvm.RETURN none_id);
            ]
        in

        [ (new_label (), Spvm.FUNC_DEF (func_id, args, func_code)) ]
    | Return exp -> (
        match exp with
        | None ->
            let none_id = new_temp_var () in
            [
              (new_label (), Spvm.COPYN none_id);
              (new_label (), Spvm.RETURN none_id);
            ]
        | Some exp ->
            let exp_id, exp_code = translate_expr exp in
            exp_code @ [ (new_label (), Spvm.RETURN exp_id) ])
    | Assert exp ->
        let exp_id, exp_code = translate_expr exp in
        exp_code @ [ (new_label (), Spvm.ASSERT exp_id) ]
    | Pass ->
        let label = new_label () in
        [ (label, Spvm.SKIP) ]
  in
  match src_pg with
  | [] -> [ (new_label (), Spvm.HALT) ]
  | hd :: tl ->
      let code_hd = translate_stmt ~break_label:0 ~continue_label:0 hd in
      code_hd @ translate tl