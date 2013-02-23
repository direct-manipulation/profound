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
(* work and present are the same formula, just with (possibly)
   different cursor positions and/or marks *)

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
    Ok { hi with dirty = true ; work }
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


type action = {
  enabled : history -> bool ;
  perform : history -> (history, string) Result.t
}

(* actions *)

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
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_down 0 snap.form in
        let trail = 0 :: snap.trail in
        { snap with trail ; form }
    end
  end }

let action_ascend = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap -> 
        let form = Traversal.go_up snap.form in
        let trail = List.tl snap.trail in
        { snap with trail ; form }
    end
  end }

let action_ascend_to_top = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_top snap.form in
        let trail = [] in
        { snap with trail ; form }
    end
  end }

let action_left = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_left snap.form in
        let trail = (List.hd snap.trail - 1) :: List.tl snap.trail in
        { snap with trail ; form }
    end
  end }

let action_right = {
  enabled = (fun _ -> true) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Traversal.go_right snap.form in
        let trail = (List.hd snap.trail + 1) :: List.tl snap.trail in
        { snap with trail ; form }
    end
  end }

let action_mark_source = {
  enabled = (fun hi -> hi.work.mmode = No_marks) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let form = Rules.make_lnk SRC snap.form in
        let mmode = Marked snap.trail in
        { snap with form ; mmode }
    end
  end }

let action_unmark_source = {
  enabled = (fun hi ->
    match hi.work.mmode with
    | No_marks -> false
    | Marked trail -> trail = hi.work.trail ) ;
  perform = begin fun hi ->
    tinker hi ~fn:begin
      fun snap ->
        let (fcx, f) = unsubst snap.form in
        match f with
        | Conn (Mark SRC, [f]) ->
            let form = subst fcx f in
            let mmode = No_marks in
            { snap with form ; mmode }
        | _ ->
            assert false
    end
  end }

(* key processing *)

let mods_of ms =
  List.fold_left begin
    fun mfl -> function
      | `CONTROL -> mfl lor 0b1
      | `SHIFT   -> mfl lor 0b10
      | _        -> mfl
  end 0 ms
type key = {code : Gdk.keysym ; mods : int}
let key k = {
  code = GdkEvent.Key.keyval k ;
  mods = mods_of (GdkEvent.Key.state k) ;
}

type adesc = {
  action : action ;
  desc   : string ;
  prio   : int ;
}
type kmap = (key, adesc list) Map.t

let rec act_insert a las ras =
  begin match ras with
  | [] -> List.rev_append las [a]
  | ra :: ras ->
      let cmp = Int.compare a.prio ra.prio in
      if cmp <= 0 then List.rev_append las (a :: ras)
      else act_insert a (ra :: las) ras
  end
let add_action km (k, act) =
  begin match Map.Exceptionless.find k km with
  | Some acts ->
      let acts = act_insert act [] acts in
      Map.add k acts km
  | None ->
      Map.add k [act] km
  end
let make_kmap bindings : kmap =
  List.fold_left add_action Map.empty bindings

let explain_keys kmap hi =
  let msgs : string list ref = ref [] in
  let rec scan_ads key ads =
    begin match ads with
    | [] -> ()
    | ad :: ads ->
        if ad.action.enabled hi then
          if ad.desc = "" then ()
          else msgs := ad.desc :: !msgs
        else scan_ads key ads
    end in
  Map.iter scan_ads kmap ;
  String.concat ", " !msgs

let handle_key (kmap : kmap) key hi =
  begin match Map.Exceptionless.find key kmap with
  | None -> Bad ""
  | Some ads ->
      let rec scan = function
        | [] -> Bad ""
        | ad :: ads ->
            if ad.action.enabled hi
            then ad.action.perform hi
            else scan ads
      in
      scan ads
  end
