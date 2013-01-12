(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

type t = string

let stab : (string, t) Hashtbl.t = Hashtbl.create 19

let intern (s : string) : t =
  try Hashtbl.find stab s with
  | Not_found ->
      Hashtbl.replace stab s s ;
      s

let rep s = s

let clear () = Hashtbl.clear stab
