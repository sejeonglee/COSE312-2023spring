type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of (id -> loc)
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

let empty_env = []
let extend_env : binding -> env -> env 
= fun b e -> b :: e
let rec lookup_env_loc : id -> env -> loc
= fun x e ->
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env"))
  | LocBind (y, l)::tl -> if y = x then l else lookup_env_loc x tl
  | ProcBind _ :: tl -> lookup_env_loc x tl
let rec lookup_env_proc : id -> env -> proc
= fun f e ->
  match e with
  | [] -> raise (Failure ("variable " ^ f ^ " is not bound in env")) 
  | ProcBind (y, p)::tl -> if y = f then p else lookup_env_proc f tl
  | LocBind _ :: tl -> lookup_env_proc f tl
  
  
let empty_mem = []
let extend_mem (l, v) m = (l, v)::m
let rec lookup_mem l m =
  match m with
  | [] -> raise (Failure ("This location is not bound"))
  | (i, v)::tl -> if i = l then v else lookup_mem l tl


let extend_rec : id -> loc -> (id * loc) list -> (id * loc) list
= fun x l r ->
  (x, l)::r
let rec lookup_rec : (id * loc) list -> id -> loc
= fun r x ->
  match r with
  | [] -> raise (Failure ("This location is not bound in the record"))
  | (y, l)::tl -> if y = x then l else lookup_rec tl x
let rec recorder : (id * loc) list -> (id -> loc)
= fun r ->
  match r with
  | [] -> raise (Failure ("This record is empty"))
  | hd::tl -> lookup_rec r
  

let rec string_of_value v = 
  match v with
  | Unit -> "Unit"
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Record f -> "Record"
  
  
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | NUM i -> (Num i, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR x -> let l = lookup_env_loc x env
               in let v = lookup_mem l mem
                 in (v, mem)
  | ADD (x, y) ->
    let res1, mem1 = eval env mem x
      in let res2, mem2 = eval env mem1 y
        in begin 
            match res1, res2 with
            | Num n1, Num n2 -> (Num (n1 + n2), mem2)
            | _ -> raise UndefinedSemantics
          end
  | SUB (x, y) ->
    let res1, mem1 = eval env mem x
      in let res2, mem2 = eval env mem1 y
        in begin
            match res1, res2 with
            | Num n1, Num n2 -> (Num (n1 - n2), mem2)
            | _ -> raise UndefinedSemantics
          end
  | MUL (x, y) -> 
    let res1, mem1 = eval env mem x
      in let res2, mem2 = eval env mem1 y
        in begin
            match res1, res2 with
            | Num n1, Num n2 -> (Num (n1 * n2), mem2)
            | _ -> raise UndefinedSemantics
          end
  | DIV (x, y) -> 
    let res1, mem1 = eval env mem x
      in let res2, mem2 = eval env mem1 y
        in begin
            match res1, res2 with
            | Num n1, Num n2 -> if (n2 = 0) then raise (Failure ("Div by zero error!"))
                                else (Num (n1 / n2), mem2)
            | _ -> raise UndefinedSemantics
          end
  | EQUAL (x, y) ->
    let v1, mem1 = eval env mem x
      in let v2, mem2 = eval env mem1 y
        in begin
            match v1, v2 with
            | Num n1, Num n2 -> (Bool (n1 = n2), mem2)
            | Bool b1, Bool b2 -> (Bool (b1 = b2), mem2)
            | Unit, Unit -> (Bool true, mem2)
            | _ -> raise UndefinedSemantics
          end
  | LESS (x, y) ->
    let v1, mem1 = eval env mem x
      in let v2, mem2 = eval env mem1 y
        in begin
            match v1, v2 with
            | Num n1, Num n2 -> (Bool (n1 < n2), mem2)
            | _ -> raise UndefinedSemantics
          end
  | NOT e ->
    let v, mem1 = eval env mem e
      in begin
          match v with
          | Bool b -> if b then (Bool false), mem else (Bool true), mem
          | _ -> raise UndefinedSemantics
        end
  | SEQ (x, y) ->
    let _, mem1 = eval env mem x
      in eval env mem1 y
  | IF (e, e1, e2) ->
    let b, mem1 = eval env mem e
      in begin
          match b with
          | Bool true -> (eval env mem1 e1)
          | Bool false -> (eval env mem1 e2)
          | _ -> raise UndefinedSemantics
        end
  | WHILE (e1, e2) ->
    let b, memp = eval env mem e1 in
      begin
        match b with
        | Bool true ->
          let v1, mem1 = eval env memp e2
            in (eval env mem1 (WHILE (e1, e2)))
        | Bool false -> (Unit, memp)
        | _ -> raise UndefinedSemantics
      end
  | LETV (x, e1, e2) ->
    let v, mem1 = eval env mem e1
      in let l = new_location()
        in let new_env = extend_env (LocBind (x, l)) env
          in let new_mem = extend_mem (l, v) mem1
            in (eval new_env new_mem e2)
  | LETF (f, xl, e1, e2) ->
    let new_env = extend_env (ProcBind(f, (xl, e1, env))) env
      in (eval new_env mem e2)
  | CALLV (f, el) -> 
    let p = lookup_env_proc f env in
      let vl, tmp_mem = 
        begin
          let rec vlist = fun l1 tmplist tm-> 
            begin
              match l1 with
              | [] -> tmplist, tm
              | hd::tl ->
                let v, mem1 = (eval env tm hd) in
                  let new_l = tmplist @ [v] in
                    (vlist tl new_l mem1)
            end in vlist el [] mem
        end in
        begin
          match p with
          | (idl, body, envp) ->
            let f_env, f_mem = 
              begin
                let rec binder = fun l1 l2 te tm -> 
                  begin
                    match l1, l2 with
                    | [], [] -> te, tm
                    | h1::t1, h2::t2 ->
                      let l = new_location() in
                        let new_env = extend_env (LocBind (h1, l)) te in
                          let new_mem = extend_mem (l, h2) tm in
                            binder t1 t2 new_env new_mem
                    | _ -> raise UndefinedSemantics
                  end in binder idl vl envp tmp_mem 
              end in
                let new_f_env = extend_env (ProcBind (f, (idl, body, envp))) f_env in
                  (eval new_f_env f_mem body)
        end
  | CALLR (f, yl) ->
    let p = lookup_env_proc f env in
      begin
        match p with
        | (idl, body, envp) ->
          let f_env = 
            begin
              let rec binder = fun l1 l2 te ->
                begin
                  match l1, l2 with
                  | [], [] -> te
                  | h1::t1, h2::t2 -> 
                    let l = lookup_env_loc h2 env in
                      let new_env = extend_env (LocBind (h1, l)) te in
                        binder t1 t2 new_env
                  | _ -> raise UndefinedSemantics
                end in binder idl yl envp
            end in
              let new_f_env = extend_env (ProcBind (f, (idl, body, envp))) f_env in
                (eval new_f_env mem body)
      end
  | RECORD r ->
    begin
      match r with
      | [] -> (Unit, mem)
      | hd::tl -> 
        let xl, vl, tmp_mem = 
          begin
            let rec vlist = fun l1 xl vl tm ->
              begin
                match l1 with
                | [] -> xl, vl, tm
                | hd::tl -> 
                  begin
                    match hd with
                    | (x, ex) ->
                      let v, mem1 = (eval env tm ex) in
                        let xl = (xl @ [x]) in
                          let vl = (vl @ [v]) in
                            (vlist tl xl vl mem1)
                  end
              end in (vlist r [] [] mem)
          end in
            let record, f_mem = 
              let rec binder = fun l1 l2 t_rec tm ->
                begin
                  match l1, l2 with
                  | [], [] -> t_rec, tm
                  | h1::t1, h2::t2 -> 
                    let l = new_location() in
                      let new_rec = extend_rec h1 l t_rec in
                        let new_mem = extend_mem (l, h2) tm in
                          binder t1 t2 new_rec new_mem
                  | _ -> raise UndefinedSemantics
                end in (binder xl vl [] tmp_mem) in
              (Record (recorder record)), f_mem
    end
  | FIELD (rekord, x) ->
    let r, memp = (eval env mem rekord) in
      begin
        match r with
        | Record f ->
          let l = f x in
            let v = lookup_mem l memp in
              (v, memp)
        | _ -> raise UndefinedSemantics 
      end
  | ASSIGN (x, ex) ->
    let v, memp = (eval env mem ex) in
      let l = lookup_env_loc x env in
        let new_mem = extend_mem (l, v) memp in
          (v, new_mem)
  | ASSIGNF (rekord, x, ex) ->
    let r, mem1 = (eval env mem rekord) in
      begin
        match r with
        | Record f ->
          let v, mem2 = (eval env mem1 ex) in
            let l = f x in
              let new_mem = extend_mem (l, v) mem2 in
                (v, new_mem)
        | _ -> raise UndefinedSemantics
      end
  | WRITE ex ->
    let v, memp = eval env mem ex in
      let s = string_of_value v in
        print_endline s;
        (v, memp)
let runb : exp -> value 
=fun exp ->
  let (v,_) = eval empty_env empty_mem exp in 
    v;;
