(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax

module P = Form_p
module L = Form_l

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
    "-log", String Log.to_file, "<file> Log output to file (default: stdout)" ;
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
  Log.to_stdout () ;
  let txt = String.trim (parse_opts ()) in
  Log.(log INFO "Profound %s [%s] START" Version.str Version.built) ;
  ignore (GMain.init ()) ;
  Log.(log INFO "GTK+ Initialized") ;
  let frm =
    begin match Syntax_prs.parse_form [] txt with
    | Ok f -> f
    | Bad _ ->
        Log.(log FATAL "Could not parse theorem. Text follows:\n%s" txt) ;
        exit 1
    end in
  Window.startup frm ;
  Log.(log INFO "Done") ;
  Log.reset ()

let () =
  if !Sys.interactive then
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
  else
    main ()
