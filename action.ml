(******************************************************************************)
(* action.ml --- gui                                                          *)
(*                                                                            *)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)
(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Syntax
open Result

module Src = Syntax_fmt.Src

type mmode =
  | Unmarked
  | Marked

type snap = {
  mmode : mmode ;
  form : form ;
}

type history = {
  work : snap ;
  dirty : bool ;
  past : snap list ;
  present : snap ;
  future  : snap list ;
}
(* work and present are the same formula, just with (possibly)
   different cursor positions and/or marks *)

let init f =
  let cur = {
    form = f ;
    mmode = Unmarked ;
  } in {
    work = cur ; dirty = false ;
    past = [] ; present = cur ; future = []
  }

let is_history_of hi f =
  let cand =
    begin match hi.past with
    | [] -> hi.present.form
    | _ -> (List.last hi.past).form
    end in
  aeq_forms cand f

let strip_mmode snap = snap.form
let render hi =
  let past = List.map strip_mmode hi.past in
  let cur  = strip_mmode hi.work in
  let fut  = List.map strip_mmode hi.future in
  (past, cur, fut)

type action_error =
  | Parsing_witness of string
exception Action_failure of action_error
let actfail err = raise (Action_failure err)
let explain = function
  | Parsing_witness msg -> "cannot parse term: " ^ msg

let tinker ~fn hi =
  try 
    let work = fn hi.work in
    Ok { hi with dirty = true ; work }
  with
  | Traversal.Traversal_failure err -> Bad (Traversal.explain err)
  | Rules.Rule_failure err -> Bad (Rules.explain err)
  | Action_failure err -> Bad (explain err)

let commit ~fn hi =
  try
    let present = fn hi.work in
    let past = hi.work :: hi.past in
    Ok { work = present ; dirty = false ; past ; present ; future = [] }
  with
  | Traversal.Traversal_failure err -> Bad (Traversal.explain err)
  | Rules.Link_matching err -> Bad (Rules.explain_link_error err)
  | Rules.Rule_failure err -> Bad (Rules.explain err)
  | Action_failure err -> Bad (explain err)

type action = {
  enabled : history -> bool ;
  perform : history -> (history, string) Result.t
}

type t = action

let action_undo = {
  enabled = (fun hi -> hi.dirty || hi.past <> []) ;
  perform = begin fun hi ->
    if hi.dirty then
      Ok { hi with dirty = false ; work = hi.present }
    else begin
      match hi.past with
      | p :: past ->
          Ok {
            work = p ;
            dirty = false ;
            past ;
            present = p ;
            future = hi.present :: hi.future
          }
      | _ ->
          Bad "no previous states"
    end
  end }

let action_redo = {
  enabled = (fun hi -> hi.future <> []) ;
  perform = begin fun hi ->
    begin match hi.future with
    | f :: future ->
        Ok {
          work = f ;
          dirty = false ;
          past = hi.present :: hi.past ;
          present = f ;
          future ;
        }
    | _ -> Bad "no future states"
    end
  end }

let action_descend = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (_, _ :: _) -> true
    | _ -> false
  end ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_down 0 snap.form in
        { snap with form }
    end
  end }

let action_ascend = {
  enabled = begin fun hi ->
    let (fcx, _) = unsubst hi.work.form in
    not (Fcx.is_empty fcx)
  end ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap -> 
        let form = Traversal.go_up snap.form in
        { snap with form }
    end
  end }

let action_ascend_to_top = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_top snap.form in
        { snap with form }
    end
  end }

let action_left = {
  enabled = begin fun hi ->
    let (fcx, _) = unsubst hi.work.form in
    match Fcx.rear fcx with
    | Some (_, {left = _ :: _ ; _}) -> true
    | _ -> false
  end ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_left snap.form in
        { snap with form }
    end
  end }

let action_right = {
  enabled = begin fun hi ->
    let (fcx, _) = unsubst hi.work.form in
    match Fcx.rear fcx with
    | Some (_, {right = _ :: _ ; _}) -> true
    | _ -> false
  end ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_right snap.form in
        { snap with form }
    end
  end }

let action_mark_source = {
  enabled = (fun hi -> hi.work.mmode = Unmarked) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let (fcx, f) = unsubst snap.form in
        Log.(log DEBUG "Marking: %s" (Src.form_to_string (fcx_vars fcx) f)) ;
        let form = subst fcx (mark SRC f) in
        let mmode = Marked in
        { form ; mmode }
    end
  end }

let action_unmark_source = {
  enabled = begin fun hi ->
    hi.work.mmode = Marked && begin
      let (_, f) = unsubst hi.work.form in
      match f with
      | Mark (SRC, _) -> true
      | _ -> false
    end
  end ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let (fcx, f) = unsubst snap.form in
        let f = unmark f in
        let form = subst fcx f in
        let mmode = Unmarked in
        { form ; mmode }
    end
  end }

let action_zero = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (Plus, []) -> false
    | _ -> not (has_mark f)
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, _) = unsubst snap.form in
        let form = subst fcx _Zero in
        { snap with form }
    end
  end }

let action_weaken = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (Qm, [f]) -> not (has_mark f)
    | _ -> false
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, _) = unsubst snap.form in
        let form = subst fcx _Bot in
        { snap with form }
    end
  end }

let action_derelict = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (Qm, [_]) -> true
    | _ -> false
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, form) = unsubst snap.form in
        match form with
        | Conn (Qm, [form]) ->
            let form = subst fcx form in
            { snap with form }
        | _ -> assert false
    end
  end }

let action_contract = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (Qm, [f]) -> not (has_mark f)
    | _ -> false
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, form) = unsubst snap.form in
        let (fcx, fr) =
          begin match Fcx.rear fcx with
          | Some (fcx, ({conn = Par ; right ; _} as fr)) ->
              (fcx, {fr with right = form :: right})
          | _ ->
              (fcx, {conn = Par ; left = [] ; right = [form]})
          end in
        let fcx = Fcx.snoc fcx fr in
        let form = subst fcx form in
        { snap with form }
    end
  end }

let action_witness ~read = {
  enabled = begin fun hi ->
    let (_, f) = unsubst hi.work.form in
    match f with
    | Conn (Qu (Ex, _), _) -> true
    | _ -> false
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, form) = unsubst snap.form in
        match form with
        | Conn (Qu (Ex, x), [fb]) ->
            let t = read x (fcx_vars fcx) in
            let ss = Dot (Shift 0, t)in
            let form = subst fcx (sub_form ss fb) in
            { snap with form }
        | _ -> assert false
    end
  end }

let action_complete_link = {
  enabled = begin fun hi ->
    hi.work.mmode = Marked
    && not (has_mark (focus hi.work.form))
  end ;
  perform = begin fun hi ->
    commit hi ~fn:begin
      fun snap ->
        let (fcx, f) = unsubst snap.form in
        let form = subst fcx (mark SNK f) in
        let form = Rules.resolve_mpar form in
        { mmode = Unmarked ; form }
    end
  end }

let action_reset = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.cleanup snap.form in
        { mmode = Unmarked ; form }
    end
  end }
