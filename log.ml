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

let log ?force lev fmt =
  let ouch =
    begin match force with
    | Some ch -> Some ch
    | None ->
        begin match !logdest with
        | Channel ouch when lev <= !loglevel && !logging ->
            Some ouch
        | _ -> None
        end
    end in
  begin match ouch with
  | Some ch ->
      Printf.fprintf ch "[%s] " (lev_string lev) ;
      Printf.fprintf ch (fmt ^^ "\n%!")
  | None ->
      Printf.ifprintf () fmt
  end

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
  log ~force:stdout TRACE "Logging to %S" f ;
  if Map.mem f !file_channels then
    logdest := Channel (Map.find f !file_channels)
  else begin
    let ch = open_out_bin f in
    file_channels := Map.add f ch !file_channels ;
    logdest := Channel ch
  end
