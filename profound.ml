(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax

let set_verbosity v =
  let open Log in
  begin match v with
  | 0 -> loglevel := FATAL
  | 1 -> loglevel := ERROR
  | 2 -> loglevel := WARN
  | 3 -> loglevel := INFO
  | 4 -> loglevel := DEBUG
  | _ -> loglevel := TRACE
  end

let infile = ref None
let set_infile fn =
  begin match !infile with
  | Some ofn ->
      Printf.eprintf "Cannot specify more than one input file\n%!" ;
      exit 1
  | None ->
      if Sys.file_exists fn then
        infile := Some fn
      else begin
        Log.(log FATAL "Could not find input file %S" fn) ;
        exit 2
      end
  end

let set_max_hist n =
  let m = max 0 (min n 20) in
  if m <> n then
    Log.(log WARN "Cannot display %d history lines; displaying %d instead" n m) ;
  Syntax_tex.max_hist := m

let parse_opts () =
  let open Arg in
  let opts = [
    "-i", String set_infile, "<file> Read theorem from <file>" ;
    "-v", Int set_verbosity, "<num> Set vebosity to <num>" ;
    "-log", String Log.to_file, "<file> Log output to file (default: stdout)" ;
    "-hist-lines", Int set_max_hist, "<num> Set the number of history lines to display to <num>" ;
    "-version", Unit (fun () ->
      Printf.printf "Profound %s [build of %s]\n" Version.str Version.built ;
      exit 0
    ), " Display a version string" ;
    "-vnum", Unit (fun () ->
      Printf.printf "%s%!" Version.str ;
      exit 0
    ), " Display a version number (no newline at end)" ;
  ] in
  let opts = align opts in
  let umsg = "Usage: profound [options] (theorem | -i file)" in
  let imm_txt = ref None in
  let add_txt txt = match !imm_txt with
    | Some _ ->
        Printf.eprintf "Only a single theorem at a time!\n%!" ;
        raise (Bad txt)
    | None ->
        imm_txt := Some txt
  in
  parse opts add_txt umsg ;
  begin match !infile, !imm_txt with
  | Some inf, Some txt ->
      Log.(log ERROR "Ignoring input file %S" inf) ;
      Gui.Imm txt
  | Some fin, None ->
      Gui.File fin
  | None, Some txt ->
      Gui.Imm txt
  | None, None ->
      Printf.eprintf "Need an input file or theorem\n%!" ;
      Arg.usage opts umsg ;
      exit 1
  end
        
let main () =
  Log.to_stdout () ;
  Log.(log INFO "Profound %s [%s] START" Version.str Version.built) ;
  let mode = parse_opts () in
  ignore (GMain.init ()) ;
  Log.(log INFO "GTK+ Initialized") ;
  Gui.run mode ;
  Log.(log INFO "Done") ;
  Log.reset ()

let () =
  if !Sys.interactive then
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
  else
    main ()
