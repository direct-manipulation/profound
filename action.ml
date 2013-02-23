(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Syntax
open Result

type mmode =
  | No_marks
  | Marked of Traversal.trail

type snap = {
  trail : int list ;
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
(* work and present are the same formula, just with different marks *)

let init f =
  let cur = {
    form = f ;
    trail = [] ;
    mmode = No_marks ;
  } in
  { work = cur ; dirty = false ; past = [] ; present = cur ; future = [] }

let tinker ~fn hi =
  try 
    let work = fn hi.work in
    let present = if hi.future = [] then work else hi.present in
    Ok { hi with dirty = true ; work ; present }
  with
  | Traversal.Traversal_failure err -> Bad (Traversal.explain err)
  | Rules.Rule_failure err -> Bad (Rules.explain err)

let commit ~fn hi =
  try
    let present = fn hi.work in
    let past = hi.work :: hi.past in
    Ok { work = present ; dirty = false ; past ; present ; future = [] }
  with
  | Traversal.Traversal_failure err -> Bad (Traversal.explain err)
  | Rules.Rule_failure err -> Bad (Rules.explain err)

type trigger = {
  keysym  : Gdk.keysym ;
  keymods : Gdk.Tags.modifier list ;
  prio    : int ;
  desc    : string ;
}

class virtual action = object (self)
  method coerce : action = (self :> action)
  method virtual perform : history -> (history, string) Result.t
  method virtual triggers : history -> trigger list
end

let action_undo = object (self)
  inherit action as super
  method perform hi =
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
  method triggers hi = []
end

let action_redo = object (self)
  inherit action as super
  method perform hi =
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
  method triggers hi = []
end

let action_descend = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_down 0 snap.form in
        let trail = 0 :: snap.trail in
        { snap with trail ; form }
    end
  method triggers hi = []
end

let action_descend_along tr = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.descend tr snap.form in
        let trail = List.rev_append tr snap.trail in
        { snap with trail ; form }
    end
  method triggers hi = []
end

let action_ascend = object (self)
  inherit action as self
  method perform hi = 
    tinker hi ~fn:begin
      fun snap -> 
        let form = Traversal.go_up snap.form in
        let trail = List.tl snap.trail in
        { snap with trail ; form }
    end
  method triggers hi = []
end
      
let action_ascend_to_top = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_top snap.form in
        let trail = [] in
        { snap with trail ; form }
    end
  method triggers hi = []
end

let action_left = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_left snap.form in
        let trail = (List.hd snap.trail - 1) :: List.tl snap.trail in
        { snap with trail ; form }
    end
  method triggers hi = []
end

let action_right = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_right snap.form in
        let trail = (List.hd snap.trail + 1) :: List.tl snap.trail in
        { snap with trail ; form }
    end
  method triggers hi = []
end

let action_mark_source = object (self)
  inherit action as super
  method perform hi =
    assert (hi.work.mmode = No_marks) ;
    tinker hi ~fn:begin
      fun snap ->
        let form = Rules.make_lnk SRC snap.form in
        let mmode = Marked snap.trail in
        { snap with form ; mmode }
    end
  method triggers hi = []
end

let action_unmark_source = object (self)
  inherit action as super
  method perform hi =
    tinker hi ~fn:begin
      fun snap ->
        assert begin
          match snap.mmode with
          | No_marks -> false
          | Marked trail -> trail = snap.trail
        end ;
        let (fcx, f) = unsubst snap.form in
        match f with
        | Conn (Mark SRC, [f]) ->
            let form = subst fcx f in
            let mmode = No_marks in
            { snap with form ; mmode }
        | _ ->
            assert false
    end
  method triggers hi = []
end
