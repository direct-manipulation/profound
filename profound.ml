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
      infile := Some fn
  end

let parse_opts () =
  let open Arg in
  let opts = [
    "-i", String set_infile, "<file> Read theorem from <file>" ;
    "-v", Int set_verbosity, "<num> Set vebosity to <num>" ;
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
      txt
  | Some inf, None ->
      input_file inf
  | None, Some txt ->
      txt
  | None, None ->
      Printf.eprintf "Need an input file or theorem\n%!" ;
      Arg.usage opts umsg ;
      exit 1
  end
        
let main () =
  let txt = parse_opts () in
  Log.to_stdout () ;
  Log.(log INFO "Profound %s START" Version.str) ;
  ignore (GMain.init ()) ;
  Log.(log INFO "GTK+ Initialized") ;
  let frm =
    begin match Syntax_prs.parse_form txt with
    | Prs.Read (f, _) -> f
    | Prs.Fail _ ->
        Printf.eprintf "Could not parse: %S\n%!" Sys.argv.(1) ;
        exit 1
    end in
  Window.startup frm ;
  Log.(log INFO "Done")

let () =
  if !Sys.interactive then
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
  else
    main ()
