open Ocamlbuild_plugin

module Pack = Ocamlbuild_pack

let menhir () =
  if !Options.ocamlyacc = N then V"MENHIR" else !Options.ocamlyacc
let menhir_tags mly =
  tags_of_pathname mly ++"ocaml"++"parser"++"menhir"

let menhir_produce_messages env build =
  let messages, mly = env "%.messages", env "%.mly" in
  let open Pack in
  Ocaml_compiler.prepare_compile build mly;
  Cmd(S[menhir (); T (menhir_tags mly);
        A "--list-errors"; P mly; Sh ">"; Px messages])

let menhir_compile_messages env build =
  let mly = env "%.mly" in
  let messages = env "%.messages" in
  let target = env "%_messages.ml" in
  Cmd(S[menhir (); T (menhir_tags mly); P mly;
        A "--compile-errors"; P messages;
        Sh ">"; Px target])

let menhir_update_messages env build =
  let mly = env "%.mly" in
  let messages = env "%.messages" in
  let tmp = Filename.temp_file "menhir" ".messages" in
  Seq [
    Cmd(S[menhir (); T (menhir_tags mly); P mly;
          A "--update-errors"; P messages;
          Sh ">"; P tmp]);
    Cmd(S[A "mv"; P tmp; P (Pathname.concat Pathname.pwd messages)]);
  ]

let _ = dispatch begin function
    | Before_options ->
      Options.use_ocamlfind := true;
      Options.use_menhir := true;
    | After_rules ->
      flag ["menhir"; "parser"; "menhir_table"] (A "--table");
      rule "menhir: .mly -> .messages"
        ~prod:"%.messages"
        ~deps:["%.mly"]
        menhir_produce_messages;
      rule "menhir: .mly & .messages -> _messages.ml"
        ~prod:"%_messages.ml"
        ~deps:["%.mly"; "%.messages"]
        menhir_compile_messages;
      rule "menhir: .mly & .messages -> .messages & .messages.update"
        ~stamp:"%.messages.update"
        ~deps:["%.mly"; "%.messages"]
        menhir_update_messages;
    | _ -> ()
end
