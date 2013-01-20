(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type logdest =
  | Ether
  | Channel of unit BatIO.output

type loglevel =
  | FATAL | ERROR | WARN | INFO | DEBUG | TRACE

let lev_string = function
  | FATAL -> "FATAL"
  | ERROR -> "ERROR"
  | WARN -> "WARN"
  | INFO -> "INFO"
  | DEBUG -> "DEBUG"
  | TRACE -> "TRACE"

let loglevel = ref WARN
let logging = ref false
let logdest = ref Ether

let reset () =
  loglevel := WARN ;
  logging := false ;
  logdest := Ether

let to_stdout () =
  logging := true ;
  logdest := Channel stdout

let file_channels : (string, unit BatIO.output) Map.t ref = ref Map.empty

let to_file f =
  logging := true ;
  if Map.mem f !file_channels then
    logdest := Channel (Map.find f !file_channels)
  else begin
    let ch = open_out_bin f in
    file_channels := Map.add f ch !file_channels ;
    logdest := Channel ch
  end

let log lev fmt =
  begin match !logdest with
  | Channel ouch
      when lev <= !loglevel && !logging ->
      begin
        Printf.fprintf ouch "[%s] " (lev_string lev) ;
        Printf.fprintf ouch (fmt ^^ "\n%!")
      end
  | _ ->
      Printf.ifprintf () fmt
  end

