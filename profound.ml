(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax

let verbosity = ref 0

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
    "-v", Set_int verbosity, "<num> Set vebosity to <num>" ;
  ] in
  let opts = align opts in
  let umsg = "Usage: profound [-S] FILE.cth" in
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
  Log.to_file "profound.log" ;
  Log.(log INFO "Profound %s START" Version.str) ;
  let txt = parse_opts () in
  let frm =
    begin match Syntax_prs.parse_form txt with
    | Prs.Read (f, _) -> f
    | Prs.Fail _ ->
        Printf.eprintf "Could not parse: %S\n%!" Sys.argv.(1) ;
        exit 1
    end in
  Syntax_tex.wash_forms [frm] ;
  Log.(log INFO "Done")

let () =
  if !Sys.interactive then
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
  else
    main ()
