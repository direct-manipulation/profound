(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type term =
  | Idx of int
  | App of Idt.t * term list

type sign = ASSERT | REFUTE

type form = private
  | Atom of sign * Idt.t * term list
  | Conn of conn * form list
  | Subst of fcx * form

and fcx = frame Deque.t

and frame = {
  fconn : fconn;
  fleft : form list;
  fright : form list;
}

and conn =
  | Tens | One | Plus | Zero | Par | Bot | With | Top
  | All of Idt.t | Ex of Idt.t
  | Bang | Qm
  | Mpar | Mark of mkind

and fconn = TENS | PLUS | PAR | WITH | ALL of Idt.t | EX of Idt.t | BANG | QM

and mkind = ARG | SRC | SNK

type sub = Shift of int | Dot of sub * term

val sub_idx : sub -> int -> term
val sub_term : sub -> term -> term
val sub_form : sub -> form -> form
val sub_fcx : sub -> fcx -> fcx * sub
val seq : sub -> sub -> sub

val atom : sign -> Idt.t -> term list -> form
val conn : conn -> form list -> form
val subst : fcx -> form -> form

val fconn_of_conn : conn -> fconn
val conn_of_fconn : fconn -> conn
val fconn : fconn -> form list -> form

val unsubst : form -> fcx * form
val unframe : frame -> form -> form
val head1 : form -> form

type traversal_error =
  | At_leaf
  | At_top
  | At_edge
  | No_such_child

exception Traversal of traversal_error

val go_down : int -> form -> form
val go_up : form -> form
val go_top : form -> form
val go_left : form -> form
val go_right : form -> form

type trail = int list
val descend : trail -> form -> form

exception Stuck
exception Already_marked

val make_lnk : mkind -> form -> form
val unlnk : form -> form
val resolve_mpar : form -> form

exception Rule_int of form
val rule_int : trail -> trail -> form -> form

