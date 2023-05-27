open Frontend

let filename = Sys.argv.(1)
let json = Yojson.Basic.from_file filename
let ast = Json2ast.to_module json
let _ = print_endline "\n*** Source Program **"
let _ = print_endline (Ast2string.string_of_module ast)
let spy = Py2spy.translate ast
let original_inst = Translator.translate spy

(* let original_inst =
   [
     (0, Spvm.SKIP);
     (1, Spvm.COPYC ("a", 1));
     (2, Spvm.COPYC ("b", 2));
     (3, Spvm.ASSIGNV ("c", Spvm.ADD, "a", "b"));
     (4, Spvm.ASSIGNV ("d", Spvm.ADD, "a", "b"));
     (5, Spvm.ASSIGNV ("e", Spvm.ADD, "a", "b"));
     (6, Spvm.WRITE "c");
     (7, Spvm.WRITE "d");
     (8, Spvm.WRITE "e");
     (9, Spvm.HALT);
   ] *)

let inst = Optimizer.optimize original_inst
let _ = print_endline "\n*** Target Program (Original)**"
let _ = print_endline (Spvm.string_of_program original_inst)
let _ = print_endline "\n*** Target Program **"
let _ = print_endline (Spvm.string_of_program inst)
let _ = Spvm.execute original_inst
let _ = Spvm.execute inst
