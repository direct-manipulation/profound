(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
open Log

open Syntax

type traversal_error =
  | At_leaf
  | At_top
  | At_edge
  | No_such_child of int

exception Traversal_failure of traversal_error
let travfail err = raise (Traversal_failure err)
let explain = function
  | At_leaf -> "cannot descend further"
  | At_top -> "cannot ascend further"
  | At_edge -> "no siblings in that direction"
  | No_such_child n ->
      Printf.sprintf "could not descend to child #%d -- THIS IS A BUG (please report)" (n + 1)

let rec split3_ err n ls rs =
  begin match rs with
  | [] -> travfail err
  | x :: rs ->
      if n = 0 then (ls, x, rs)
      else split3_ err (n - 1) (x :: ls) rs
  end

let split3 n xs =
  split3_ (No_such_child n) n [] xs

let go_down n f =
  let (fcx, f) = unsubst f in
  let (fr, f) =
    begin match f with
    | Mark _
    | Atom _ ->
        travfail At_leaf
    | Conn (c, fs) ->
        let (lfs, f, rfs) = split3 n fs in
        assert (fs = List.rev_append lfs (f :: rfs)) ;
        let fr = {
          conn = c ;
          left = lfs ;
          right = rfs ;
        } in
        (fr, f)
    | Subst _ -> assert false
    end in
  let fcx = Fcx.snoc fcx fr in
  subst fcx f

let go_up f =
  let (fcx, f) = unsubst f in
  begin match Fcx.rear fcx with
  | Some (fcx, fr) ->
      subst fcx (unframe fr f)
  | None -> travfail At_top
  end

let rec go_top f =
  begin match f with
  | Subst _ -> go_top (go_up f)
  | _ -> f
  end

let go_left f =
  let (fcx, f) = unsubst f in
  begin match Fcx.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.left with
      | lf :: lfs ->
          let fr = { fr with
                     left = lfs ;
                     right = f :: fr.right ;
                   } in
          let fcx = Fcx.snoc fcx fr in
          subst fcx lf
      | [] -> travfail At_edge
      end
  | None -> travfail At_edge
  end

let go_right f =
  let (fcx, f) = unsubst f in
  begin match Fcx.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.right with
      | rf :: rfs ->
          let fr = { fr with
                     right = rfs ;
                     left = f :: fr.left ;
                   } in
          let fcx = Fcx.snoc fcx fr in
          subst fcx rf
      | [] -> travfail At_edge
      end
  | None -> travfail At_edge
  end

type trail = int list

let rec descend (tr : trail) f =
  begin match tr with
  | [] -> f
  | cr :: tr ->
      let f = go_down cr f in
      descend tr f
  end

let rec cleanup f =
  begin match head1 f with
  | Atom _ as f -> f
  | Mark (_, f) -> cleanup f
  | Conn (c, fs) ->
      let fs = List.map cleanup fs in
      conn c fs
  | Subst _ -> assert false
  end
