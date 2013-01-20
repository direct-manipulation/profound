(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)
open Batteries
open Log

open Syntax

type traversal_error =
  | At_leaf
  | At_top
  | At_edge
  | No_such_child

exception Traversal of traversal_error
let travfail err = raise (Traversal err)

let rec split3 n xs =
  try begin match List.split_at n xs with
  | l, (u :: r) -> (l, u, r)
  | _ -> travfail No_such_child
  end with _ -> travfail No_such_child

let go_down n f =
  let (fcx, f) =
    begin match f with
    | Subst (fcx, f) -> (fcx, f)
    | _ -> (Deque.empty, f)
    end in
  let (fr, f) =
    begin match f with
    | Atom _ -> travfail At_leaf
    | Conn (c, fs) ->
        let (lfs, f, rfs) = split3 n fs in
        let fr = {
          fconn = fconn_of_conn c ;
          fleft = lfs ;
          fright = rfs ;
        } in
        (fr, f)
    | Subst _ -> assert false
    end in
  let fcx = Deque.snoc fcx fr in
  subst fcx f

let go_up f =
  let (fcx, f) = unsubst f in
  begin match Deque.rear fcx with
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
  begin match Deque.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.fleft with
      | lf :: lfs ->
          let fr = { fr with
            fleft = lfs ;
            fright = f :: fr.fright ;
          } in
          let fcx = Deque.snoc fcx fr in
          subst fcx lf
      | [] -> travfail At_edge
      end
  | None -> travfail At_top
  end

let go_right f =
  let (fcx, f) = unsubst f in
  begin match Deque.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.fright with
      | rf :: rfs ->
          let fr = { fr with
            fright = rfs ;
            fleft = f :: fr.fleft ;
          } in
          let fcx = Deque.snoc fcx fr in
          subst fcx rf
      | [] -> travfail At_edge
      end
  | None -> travfail At_top
 end

type trail = int list

let rec descend (tr : trail) f =
  begin match tr with
  | [] -> f
  | cr :: tr ->
      let f = go_down cr f in
      descend tr f
  end
