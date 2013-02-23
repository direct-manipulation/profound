(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

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
let logdest = ref stdout

let log ?force lev fmt =
  let ouch =
    begin match force with
    | Some ch -> Some ch
    | None ->
        if !logging && lev <= !loglevel
        then Some !logdest
        else None
    end in
  begin match ouch with
  | Some ch ->
      Printf.fprintf ch "[%s] " (lev_string lev) ;
      Printf.fprintf ch (fmt ^^ "\n%!")
  | None ->
      Printf.ifprintf () fmt
  end

let file_channels : (string, unit BatIO.output) Map.t ref = ref Map.empty

let reset () =
  loglevel := WARN ;
  logging := false ;
  logdest := stdout ;
  Map.iter (fun nm ch ->
    log ~force:stdout TRACE "Closing %S" nm ;
    close_out ch
  ) !file_channels ;
  file_channels := Map.empty

let to_stdout () =
  logging := true ;
  logdest := stdout

let to_file f =
  logging := true ;
  log ~force:stdout TRACE "Logging to %S" f ;
  if Map.mem f !file_channels then
    logdest := Map.find f !file_channels
  else begin
    let ch = open_out_bin f in
    file_channels := Map.add f ch !file_channels ;
    logdest := ch
  end
