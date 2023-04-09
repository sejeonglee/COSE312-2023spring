open Regex

exception Not_implemented

let regex2nfa : Regex.t -> Nfa.t =
 fun input_regex ->
  let rec process (regex : Regex.t) : Nfa.t =
    let empty_nfa = Nfa.create_new_nfa () in
    match regex with
    | Empty ->
        let new_state, new_nfa = Nfa.create_state empty_nfa in
        Nfa.add_final_state new_nfa new_state
    | Epsilon ->
        let state, nfa = Nfa.create_state empty_nfa in
        let nfa = Nfa.add_final_state nfa state in
        let nfa = Nfa.add_epsilon_edge nfa (Nfa.get_initial_state nfa, state) in
        nfa
    | Alpha a ->
        let state, nfa = Nfa.create_state empty_nfa in
        let nfa = Nfa.add_final_state nfa state in
        let nfa = Nfa.add_edge nfa (Nfa.get_initial_state nfa, a, state) in
        nfa
    | OR (r1, r2) ->
        let nfa_r1 = process r1 in
        let nfa_r2 = process r2 in
        let initial1 = Nfa.get_initial_state nfa_r1 in
        let initial2 = Nfa.get_initial_state nfa_r2 in
        let final1 = BatSet.to_list (Nfa.get_final_states nfa_r1) in
        let final2 = BatSet.to_list (Nfa.get_final_states nfa_r2) in
        let initial = Nfa.get_initial_state empty_nfa in
        let final, nfa = Nfa.create_state empty_nfa in
        let nfa = Nfa.add_final_state nfa final in
        let nfa = Nfa.add_states nfa (Nfa.get_states nfa_r1) in
        let nfa = Nfa.add_states nfa (Nfa.get_states nfa_r2) in
        let nfa = Nfa.add_edges nfa (Nfa.get_edges nfa_r1) in
        let nfa = Nfa.add_edges nfa (Nfa.get_edges nfa_r2) in
        let nfa =
          Nfa.add_edges nfa
            ( [],
              [ (initial, initial1); (initial, initial2) ]
              @ List.map (fun s -> (s, final)) (final1 @ final2) )
        in
        nfa
    | CONCAT (r1, r2) ->
        let nfa_r1 = process r1 in
        let nfa_r2 = process r2 in
        let initial1 = Nfa.get_initial_state nfa_r1 in
        let initial2 = Nfa.get_initial_state nfa_r2 in
        let final1 = BatSet.to_list (Nfa.get_final_states nfa_r1) in
        let final2 = BatSet.to_list (Nfa.get_final_states nfa_r2) in
        let initial = Nfa.get_initial_state empty_nfa in
        let final, nfa = Nfa.create_state empty_nfa in
        let nfa = Nfa.add_final_state nfa final in
        let nfa = Nfa.add_states nfa (Nfa.get_states nfa_r1) in
        let nfa = Nfa.add_states nfa (Nfa.get_states nfa_r2) in
        let nfa = Nfa.add_edges nfa (Nfa.get_edges nfa_r1) in
        let nfa = Nfa.add_edges nfa (Nfa.get_edges nfa_r2) in
        let nfa =
          Nfa.add_edges nfa
            ( [],
              [ (initial, initial1) ]
              @ List.map (fun s -> (s, initial2)) final1
              @ List.map (fun s -> (s, final)) final2 )
        in
        nfa
    | STAR r ->
        let nfa_r = process r in
        let initial_r = Nfa.get_initial_state nfa_r in
        let final_r = BatSet.to_list (Nfa.get_final_states nfa_r) in
        let initial = Nfa.get_initial_state empty_nfa in
        let final, nfa = Nfa.create_state empty_nfa in
        let nfa = Nfa.add_final_state nfa final in
        let nfa = Nfa.add_states nfa (Nfa.get_states nfa_r) in
        let nfa = Nfa.add_edges nfa (Nfa.get_edges nfa_r) in
        let nfa =
          Nfa.add_edges nfa
            ( [],
              [ (initial, initial_r); (initial, final) ]
              @ List.map (fun s -> (s, initial_r)) final_r
              @ List.map (fun s -> (s, final)) final_r )
        in
        nfa
  in

  process input_regex

let nfa2dfa : Nfa.t -> Dfa.t =
 fun nfa ->
  let rec epsilon_closure (nfa : Nfa.t) (states : Nfa.states) : Dfa.state =
    let cur_states = states in
    let next_states =
      BatSet.fold
        (fun nfa_state dfa_states ->
          BatSet.union (Nfa.get_next_state_epsilon nfa nfa_state) dfa_states)
        states states
    in
    if BatSet.equal cur_states next_states then cur_states
    else epsilon_closure nfa next_states
  in
  let d0 = epsilon_closure nfa (BatSet.singleton (Nfa.get_initial_state nfa)) in
  let d = ref (BatSet.singleton d0) in
  let dfa = ref (Dfa.create_new_dfa d0) in
  let w = ref (BatSet.singleton d0) in
  if not (BatSet.disjoint d0 (Nfa.get_final_states nfa)) then
    dfa := Dfa.add_final_state !dfa d0;
  while not (BatSet.is_empty !w) do
    let q = BatSet.any !w in
    w := BatSet.remove q !w;
    let ta =
      epsilon_closure nfa
        (BatSet.fold
           (fun nfa_state t ->
             BatSet.union (Nfa.get_next_state nfa nfa_state Regex.A) t)
           q BatSet.empty)
    in
    if not (BatSet.exists (fun s -> s = ta) !d) (*D*) then w := BatSet.add ta !w
    else ();
    d := BatSet.add ta !d;
    if BatSet.disjoint ta (Nfa.get_final_states nfa) then
      dfa := Dfa.add_state !dfa ta
    else dfa := Dfa.add_final_state !dfa ta;
    dfa := Dfa.add_edge !dfa (q, Regex.A, ta);
    let tb =
      epsilon_closure nfa
        (BatSet.fold
           (fun nfa_state t ->
             BatSet.union (Nfa.get_next_state nfa nfa_state Regex.B) t)
           q BatSet.empty)
    in
    if not (BatSet.exists (fun s -> s = tb) !d) (*D*) then w := BatSet.add tb !w
    else ();
    d := BatSet.add tb !d;
    if BatSet.disjoint tb (Nfa.get_final_states nfa) then
      dfa := Dfa.add_state !dfa tb
    else dfa := Dfa.add_final_state !dfa tb;
    dfa := Dfa.add_edge !dfa (q, Regex.B, tb)
  done;
  !dfa

(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t =
 fun regex ->
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
  dfa

let run_dfa : Dfa.t -> alphabet list -> bool =
 fun dfa s_list ->
  let rec run_dfa' : Dfa.state -> alphabet list -> bool =
   fun state s_list ->
    match s_list with
    | [] -> Dfa.is_final_state dfa state
    | hd :: tl ->
        let next_state = Dfa.get_next_state dfa state hd in
        if BatSet.is_empty next_state then false else run_dfa' next_state tl
  in
  run_dfa' (Dfa.get_initial_state dfa) s_list
(* TODO *)
