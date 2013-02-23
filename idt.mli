(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

(** Interning strings *)

type idt = private {
  src : string ;
  tex : string ;
  salt : int ;
}
type t = idt

val clear : unit -> unit

val intern  : ?salt:int -> string -> t
val refresh : t -> t

val src_rep : t -> string
val tex_rep : t -> string


