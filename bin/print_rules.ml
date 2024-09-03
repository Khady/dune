open Import

let doc = "Dump rules."

let man =
  [ `S "DESCRIPTION"
  ; `P
      {|Dump Dune rules for the given targets.
           If no targets are given, dump all the rules.|}
  ; `P
      {|By default the output is a list of S-expressions,
           one S-expression per rule. Each S-expression is of the form:|}
  ; `Pre
      "  ((deps    (<dependencies>))\n\
      \   (targets (<targets>))\n\
      \   (context <context-name>)\n\
      \   (action  <action>))"
  ; `P
      {|$(b,<context-name>) is the context is which the action is executed.
           It is omitted if the action is independent from the context.|}
  ; `P
      {|$(b,<action>) is the action following the same syntax as user actions,
           as described in the manual.|}
  ; `Blocks Common.help_secs
  ]
;;

let info = Cmd.info "rules" ~doc ~man

let print_rule_makefile ppf (rule : Dune_engine.Reflection.Rule.t) =
  let action =
    Action.For_shell.Progn
      [ Mkdir (Path.to_string (Path.build rule.targets.root))
      ; Action.for_shell rule.action
      ]
  in
  (* Makefiles seem to allow directory targets, so we include them. *)
  let targets =
    Filename.Set.union rule.targets.files rule.targets.dirs
    |> Filename.Set.to_list_map ~f:(fun basename ->
      Path.Build.relative rule.targets.root basename |> Path.build)
  in
  Format.fprintf
    ppf
    "@[<hov 2>@{<makefile-stuff>%a:%t@}@]@,@<0>\t@{<makefile-action>%a@}\n"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space (fun ppf p ->
       Format.pp_print_string ppf (Path.to_string p)))
    targets
    (fun ppf ->
      Path.Set.iter rule.expanded_deps ~f:(fun dep ->
        Format.fprintf ppf "@ %s" (Path.to_string dep)))
    Pp.to_fmt
    (Action_to_sh.pp action)
;;

module Ninja = struct
  module Simplified = struct
    type destination =
      | Dev_null
      | File of string

    type source = string

    type t =
      | Run of string * string list
      | Chdir of string
      | Setenv of string * string
      | Redirect_out of t list * Action.Outputs.t * destination
      | Redirect_in of t list * Action.Inputs.t * source
      | Pipe of t list list * Action.Outputs.t
      | Sh of string
      | Concurrent of t list list
  end

  open Simplified

  let echo s =
    let lines = String.split_lines s in
    if String.is_suffix s ~suffix:"\n"
    then List.map lines ~f:(fun s -> Run ("echo", [ "'" ^ s ^ "'" ]))
    else (
      match List.rev lines with
      | [] -> [ Run ("echo", [ "-n" ]) ]
      | last :: rest ->
        List.fold_left
          rest
          ~init:[ Run ("echo", [ "-n"; "'" ^ last ^ "'" ]) ]
          ~f:(fun acc s -> Run ("echo", [ "'" ^ s ^ "'" ]) :: acc))
  ;;

  let cat ps = Run ("cat", ps)
  let mkdir p = Run ("mkdir", [ "-p"; p ])

  let interpret_perm (perm : Action.File_perm.t) fn acc =
    match perm with
    | Normal -> acc
    | Executable -> Run ("chmod", [ "+x"; fn ]) :: acc
  ;;

  let simplify act =
    let rec loop (act : Action.For_shell.t) acc =
      match act with
      | Run (prog, args) -> Run (prog, Array.Immutable.to_list args) :: acc
      | With_accepted_exit_codes (_, t) -> loop t acc
      | Dynamic_run (prog, args) -> Run (prog, args) :: acc
      | Chdir (p, act) -> loop act (Chdir p :: mkdir p :: acc)
      | Setenv (k, v, act) -> loop act (Setenv (k, v) :: acc)
      | Redirect_out (outputs, fn, perm, act) ->
        interpret_perm perm fn (Redirect_out (block act, outputs, File fn) :: acc)
      | Redirect_in (inputs, fn, act) -> Redirect_in (block act, inputs, fn) :: acc
      | Ignore (outputs, act) -> Redirect_out (block act, outputs, Dev_null) :: acc
      | Progn l -> List.fold_left l ~init:acc ~f:(fun acc act -> loop act acc)
      | Concurrent l -> Concurrent (List.map ~f:block l) :: acc
      | Echo xs -> echo (String.concat xs ~sep:"")
      | Cat x -> cat x :: acc
      | Copy (x, y) -> Run ("cp", [ x; y ]) :: acc
      | Symlink (x, y) -> Run ("ln", [ "-s"; x; y ]) :: Run ("rm", [ "-f"; y ]) :: acc
      | Hardlink (x, y) -> Run ("ln", [ x; y ]) :: Run ("rm", [ "-f"; y ]) :: acc
      | Bash x -> Run ("bash", [ "-e"; "-u"; "-o"; "pipefail"; "-c"; x ]) :: acc
      | Write_file (x, perm, y) ->
        interpret_perm perm x (Redirect_out (echo y, Stdout, File x) :: acc)
      | Rename (x, y) -> Run ("mv", [ x; y ]) :: acc
      | Remove_tree x -> Run ("rm", [ "-rf"; x ]) :: acc
      | Mkdir x -> mkdir x :: acc
      | Pipe (outputs, l) -> Pipe (List.map ~f:block l, outputs) :: acc
      | Extension _ -> Sh "# extensions are not supported" :: acc
    and block act =
      match List.rev (loop act []) with
      | [] -> [ Run ("true", []) ]
      | l -> l
    in
    block act
  ;;

  let rec encode (act : t) =
    match act with
    | Run (prog, args) -> prog :: args
    | Chdir dir -> [ "cd"; dir ]
    | Setenv (k, v) -> [ "export"; k ^ "=" ^ v ]
    | Sh s -> [ s ]
    | Concurrent _ -> assert false
    | Pipe (l, outputs) ->
      let first_pipe, end_ =
        match outputs with
        | Stdout -> " | ", ""
        | Outputs -> " 2>&1 | ", ""
        | Stderr -> " 2> >( ", " 1>&2 )"
      in
      (match l with
       | [] -> assert false
       | first :: l ->
         List.concat
           [ encode_block first
           ; [ first_pipe ]
           ; List.concat (List.map l ~f:encode_block)
           ; [ end_ ]
           ])
    | Redirect_out (l, outputs, dest) ->
      let body = encode_block l in
      List.concat
        [ body
        ; [ (match outputs with
             | Stdout -> ">"
             | Stderr -> "2>"
             | Outputs -> "&>")
          ]
        ; [ (match dest with
             | Dev_null -> "/dev/null"
             | File fn -> fn)
          ]
        ]
    | Redirect_in (l, inputs, src) ->
      let body = encode_block l in
      List.concat
        [ body
        ; [ (match inputs with
             | Stdin -> "<")
          ]
        ; [ src ]
        ]

  and encode_block l =
    let cmds = List.map ~f:encode l in
    let cmds = List.intersperse cmds ~sep:[ "&&" ] in
    List.concat [ [ "(" ]; List.concat cmds; [ ")" ] ]
  ;;

  let name_of_outputs outputs =
    let s = String.concat ~sep:"" outputs in
    Digest.string s |> Digest.to_string
  ;;

  let make_rule ~inputs ~outputs act =
    let act = simplify act in
    let name = name_of_outputs outputs in
    let command = encode_block act in
    let rule = Ninja_utils.rule ~description:[] ~command name in
    let build = Ninja_utils.build name ~inputs ~outputs in
    [ rule; build ]
  ;;
end

let print_rule_ninja ppf (rule : Dune_engine.Reflection.Rule.t) =
  let action =
    Action.For_shell.Progn
      [ Mkdir (Path.to_string (Path.build rule.targets.root))
      ; Action.for_shell rule.action
      ]
  in
  (* Makefiles seem to allow directory targets, so we include them. *)
  let targets =
    Filename.Set.union rule.targets.files rule.targets.dirs
    |> Filename.Set.to_list_map ~f:(fun basename ->
      Path.Build.relative rule.targets.root basename |> Path.build)
  in
  let inputs = Path.Set.to_list_map ~f:Path.to_string rule.expanded_deps in
  let outputs = List.map ~f:Path.to_string targets in
  let ninja = Ninja.make_rule ~inputs ~outputs action in
  let ninja = List.to_seq ninja in
  Ninja_utils.format ppf ninja
;;

(* Format.fprintf
    ppf
    "@[<hov 2>@{<makefile-stuff>%a:%t@}@]@,@<0>\t@{<makefile-action>%a@}\n"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space (fun ppf p ->
       Format.pp_print_string ppf (Path.to_string p)))
    targets
    (fun ppf ->
      Path.Set.iter rule.expanded_deps ~f:(fun dep ->
        Format.fprintf ppf "@ %s" (Path.to_string dep)))
    Pp.to_fmt
    (Action_to_sh.pp action) *)

let rec encode : Action.For_shell.t -> Dune_lang.t =
  let module Outputs = Dune_lang.Action.Outputs in
  let module File_perm = Dune_lang.Action.File_perm in
  let module Inputs = Dune_lang.Action.Inputs in
  let open Dune_lang in
  let program = Encoder.string in
  let string = Encoder.string in
  let path = Encoder.string in
  let target = Encoder.string in
  function
  | Run (a, xs) ->
    List (atom "run" :: program a :: List.map (Array.Immutable.to_list xs) ~f:string)
  | With_accepted_exit_codes (pred, t) ->
    List
      [ atom "with-accepted-exit-codes"
      ; Predicate_lang.encode Dune_sexp.Encoder.int pred
      ; encode t
      ]
  | Dynamic_run (a, xs) -> List (atom "run_dynamic" :: program a :: List.map xs ~f:string)
  | Chdir (a, r) -> List [ atom "chdir"; path a; encode r ]
  | Setenv (k, v, r) -> List [ atom "setenv"; string k; string v; encode r ]
  | Redirect_out (outputs, fn, perm, r) ->
    List
      [ atom (sprintf "with-%s-to%s" (Outputs.to_string outputs) (File_perm.suffix perm))
      ; target fn
      ; encode r
      ]
  | Redirect_in (inputs, fn, r) ->
    List [ atom (sprintf "with-%s-from" (Inputs.to_string inputs)); path fn; encode r ]
  | Ignore (outputs, r) ->
    List [ atom (sprintf "ignore-%s" (Outputs.to_string outputs)); encode r ]
  | Progn l -> List (atom "progn" :: List.map l ~f:encode)
  | Concurrent l -> List (atom "concurrent" :: List.map l ~f:encode)
  | Echo xs -> List (atom "echo" :: List.map xs ~f:string)
  | Cat xs -> List (atom "cat" :: List.map xs ~f:path)
  | Copy (x, y) -> List [ atom "copy"; path x; target y ]
  | Symlink (x, y) -> List [ atom "symlink"; path x; target y ]
  | Hardlink (x, y) -> List [ atom "hardlink"; path x; target y ]
  | Bash x -> List [ atom "bash"; string x ]
  | Write_file (x, perm, y) ->
    List [ atom ("write-file" ^ File_perm.suffix perm); target x; string y ]
  | Rename (x, y) -> List [ atom "rename"; target x; target y ]
  | Remove_tree x -> List [ atom "remove-tree"; target x ]
  | Mkdir x -> List [ atom "mkdir"; target x ]
  | Pipe (outputs, l) ->
    List (atom (sprintf "pipe-%s" (Outputs.to_string outputs)) :: List.map l ~f:encode)
  | Extension ext -> List [ atom "ext"; Dune_sexp.Quoted_string (Sexp.to_string ext) ]
;;

let encode_path p =
  let make constr arg =
    Dune_sexp.List [ Dune_sexp.atom constr; Dune_sexp.atom_or_quoted_string arg ]
  in
  let open Path in
  match p with
  | In_build_dir p -> make "In_build_dir" (Path.Build.to_string p)
  | In_source_tree p -> make "In_source_tree" (Path.Source.to_string p)
  | External p -> make "External" (Path.External.to_string p)
;;

let encode_file_selector file_selector =
  let open Dune_sexp.Encoder in
  let module File_selector = Dune_engine.File_selector in
  let dir = File_selector.dir file_selector in
  let predicate = File_selector.predicate file_selector in
  let only_generated_files = File_selector.only_generated_files file_selector in
  record
    [ "dir", encode_path dir
    ; "predicate", Predicate_lang.Glob.encode predicate
    ; "only_generated_files", bool only_generated_files
    ]
;;

let encode_alias alias =
  let open Dune_sexp.Encoder in
  let dir = Dune_engine.Alias.dir alias in
  let name = Dune_engine.Alias.name alias in
  record
    [ "dir", encode_path (Path.build dir)
    ; "name", Dune_sexp.atom_or_quoted_string (Dune_util.Alias_name.to_string name)
    ]
;;

let encode_dep_set deps =
  Dune_sexp.List
    (Dep.Set.to_list_map
       deps
       ~f:
         (let open Dune_sexp.Encoder in
          function
          | File_selector g -> pair string encode_file_selector ("glob", g)
          | Env e -> pair string string ("Env", e)
          | File f -> pair string encode_path ("File", f)
          | Alias a -> pair string encode_alias ("Alias", a)
          | Universe -> string "Universe"))
;;

let print_rule_sexp ppf (rule : Dune_engine.Reflection.Rule.t) =
  let sexp_of_action action = Action.for_shell action |> encode in
  let paths ps =
    Dune_sexp.Encoder.list
      (fun p ->
        Path.Build.relative rule.targets.root p
        |> Path.Build.to_string
        |> Dune_sexp.atom_or_quoted_string)
      (Filename.Set.to_list ps)
  in
  let sexp =
    Dune_sexp.Encoder.record
      (List.concat
         [ [ "deps", encode_dep_set rule.deps
           ; ( "targets"
             , Dune_sexp.Encoder.record
                 [ "files", paths rule.targets.files
                 ; "directories", paths rule.targets.dirs
                 ] )
           ]
         ; (match Path.Build.extract_build_context rule.targets.root with
            | None -> []
            | Some (c, _) -> [ "context", Dune_sexp.atom_or_quoted_string c ])
         ; [ "action", sexp_of_action rule.action ]
         ])
  in
  Format.fprintf ppf "%a@," Dune_lang.Deprecated.pp_split_strings sexp
;;

module Syntax = struct
  type t =
    | Makefile
    | Sexp
    | Ninja

  let term =
    let doc = "Output the rules in specified syntax." in
    let+ syntax =
      Arg.(
        value
        & opt (enum [ "sexp", Sexp; "makefile", Makefile; "ninja", Ninja ]) Sexp
        & info [ "s"; "syntax" ] ~doc)
    in
    syntax
  ;;

  let print_rule = function
    | Makefile -> print_rule_makefile
    | Sexp -> print_rule_sexp
    | Ninja -> print_rule_ninja
  ;;

  let print_rules syntax ppf rules =
    Dune_lang.Deprecated.prepare_formatter ppf;
    Format.pp_open_vbox ppf 0;
    Format.pp_print_list (print_rule syntax) ppf rules;
    Format.pp_print_flush ppf ()
  ;;
end

let term =
  let+ builder = Common.Builder.term
  and+ out =
    Arg.(
      value
      & opt (some string) None
      & info [ "o" ] ~docv:"FILE" ~doc:"Output to a file instead of stdout.")
  and+ recursive =
    Arg.(
      value
      & flag
      & info
          [ "r"; "recursive" ]
          ~doc:
            "Print all rules needed to build the transitive dependencies of the given \
             targets.")
  and+ syntax = Syntax.term
  and+ targets = Arg.(value & pos_all dep [] & Arg.info [] ~docv:"TARGET") in
  let common, config = Common.init builder in
  let out = Option.map ~f:Path.of_string out in
  Scheduler.go ~common ~config (fun () ->
    let open Fiber.O in
    let* setup = Import.Main.setup () in
    build_exn (fun () ->
      let open Memo.O in
      let* setup = setup in
      let* request =
        match targets with
        | [] ->
          Target.all_direct_targets None
          >>| Path.Build.Map.foldi ~init:[] ~f:(fun p _ acc -> Path.build p :: acc)
          >>| Action_builder.paths
        | _ ->
          Memo.return (Target.interpret_targets (Common.root common) config setup targets)
      in
      let+ rules = Dune_engine.Reflection.eval ~request ~recursive in
      let print oc =
        let ppf = Format.formatter_of_out_channel oc in
        Syntax.print_rules syntax ppf rules
      in
      match out with
      | None -> print stdout
      | Some fn -> Io.with_file_out fn ~f:print))
;;

let command = Cmd.v info term
