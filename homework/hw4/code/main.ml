open Frontend

let filename = Sys.argv.(1)

let json = Yojson.Basic.from_file filename

let ast = Json2ast.to_module json

let _ = print_endline "\n*** Source Program **"

let _ = print_endline (Ast2string.string_of_module ast)

let spy = Py2spy.translate ast

let original_inst = Translator.translate spy

let inst = Optimizer.optimize original_inst

let _ = print_endline "\n*** Target Program (Original)**"

let _ = print_endline (Spvm.string_of_program original_inst)

let _ = print_endline "\n*** Target Program **"

let _ = print_endline (Spvm.string_of_program inst)

let _ = Spvm.execute original_inst

let _ = Spvm.execute inst
