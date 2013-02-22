(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax
open Syntax_tex
open Traversal
open Rules

open Idt

let read_form f =
  let txt = String.trim (input_file f) in
  Syntax_prs.(match parse_form txt with
  | Prs.Read f -> f
  | Prs.Fail _ ->
      Log.(log FATAL "Could not read a form from %S" f) ;
      failwith "read_form")

let f0 = read_form "examples/cls-2.p"
let f1 = go_top (make_lnk SRC (descend [0 ; 0] f0))
let f2 = go_top (make_lnk SNK (descend [1 ; 0] f1))
let (fcx0, fcx1, l1, fcx2, l2) = match_links f2
let f3 = cleanup (subst fcx0 (_Par (subst fcx1 l1) (subst fcx2 l2)))
let f4 = resolve_mpar_ fcx1 l1 fcx2 l2
let f5 = cleanup (subst fcx0 f4)
let f6 = resolve_mpar f2

