(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Syntax

type history

val init : form -> history

val is_history_of : history -> form -> bool

val render : history -> form list * form * form list

type action = {
  enabled : history -> bool ;
  perform : history -> (history, string) Result.t ;
}

type t = action

val action_undo          : action
val action_redo          : action
val action_descend       : action
val action_ascend        : action
val action_ascend_to_top : action
val action_left          : action
val action_right         : action
val action_mark_source   : action
val action_unmark_source : action
val action_complete_link : action
val action_reset         : action
val action_zero          : action
val action_weaken        : action
val action_derelict      : action
val action_contract      : action

val action_witness       : read:(Idt.t -> Idt.t list -> term)
                        -> action
val action_cut           : read:(Idt.t list -> form)
                        -> action
