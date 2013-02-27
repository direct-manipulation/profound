(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type box =
    | NOBOX
    | H | V of int | HV of int | HOV of int

type doc =
  | String of string
  | StringAs of int * string
  | Fmt of (Format.formatter -> unit)
  | Break of int * int
  | Group of box * doc list
  | Newline

val space : int -> doc
val cut : doc

val doc_map_strings : (elen:int -> string -> doc) -> doc -> doc

val pp_doc : Format.formatter -> doc -> unit

val lin_doc_buffer : Buffer.t -> doc -> unit
val lin_doc : doc -> string

type wrapping = Transparent | Opaque

type exp =
  | Atom of doc
  | Wrap of wrapping * doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp list

and assoc = Left | Right | Non

val bracket : ?ld:doc -> ?rd:doc -> exp -> doc
