open OpamParserTypes
let main _lex _lexbuf fn =
  assert (fn = "dune.opam" ||
          (* For travis *)
          fn = "jbuilder.opam");
  { file_contents = []
  ; file_name     = fn
  }
