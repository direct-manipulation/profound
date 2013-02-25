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
  | No_such_child of int

exception Traversal_failure of traversal_error
let travfail err = raise (Traversal_failure err)
let explain = function
  | At_leaf -> "cannot descend further"
  | At_top -> "cannot ascend further"
  | At_edge -> "no siblings in that direction"
  | No_such_child n ->
      Printf.sprintf "could not descend to child #%d -- THIS IS A BUG (please report)" (n + 1)

let rec split3 n xs =
  try begin match List.split_at n xs with
  | l, (u :: r) -> (l, u, r)
  | _ -> travfail (No_such_child n)
  end with _ -> travfail (No_such_child n)

let go_down n f =
  let (fcx, f) = unsubst f in
  let (fr, f) =
    begin match f with
    | Conn (Mark _, _)
    | Atom _ ->
        travfail At_leaf
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
  let fcx = Cx.snoc fcx fr in
  subst fcx f

let go_up f =
  let (fcx, f) = unsubst f in
  begin match Cx.rear fcx with
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
  begin match Cx.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.fleft with
      | lf :: lfs ->
          let fr = { fr with
            fleft = lfs ;
            fright = f :: fr.fright ;
          } in
          let fcx = Cx.snoc fcx fr in
          subst fcx lf
      | [] -> travfail At_edge
      end
  | None -> travfail At_edge
  end

let go_right f =
  let (fcx, f) = unsubst f in
  begin match Cx.rear fcx with
  | Some (fcx, fr) ->
      begin match fr.fright with
      | rf :: rfs ->
          let fr = { fr with
            fright = rfs ;
            fleft = f :: fr.fleft ;
          } in
          let fcx = Cx.snoc fcx fr in
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
  | Conn (Mark _, [f]) ->
      cleanup f
  | Conn (c, fs) ->
      let fs = List.map cleanup fs in
      conn c fs
  | Subst _ -> assert false
  end

let rec find_marked f =
  begin match f with
  | Atom _ -> None
  | Subst _ -> assert false
  | Conn (Mark _, _) -> Some (Cx.empty, f)
  | Conn (c, fs) ->
      begin match find_marked_arg [] fs with
      | Some (lfs, fcx, f, rfs) ->
          let fr = {
            fconn = fconn_of_conn c ;
            fleft = lfs ;
            fright = rfs ;
          } in
          let fcx = Cx.cons fr fcx in
          Some (fcx, f)
      | None -> None
      end
  end

and find_marked_arg lfs rfs =
  begin match rfs with
  | [] -> None
  | f :: rfs ->
      begin match find_marked f with
      | Some (fcx, f) ->
          Some (lfs, fcx, f, rfs)
      | None ->
          find_marked_arg (f :: lfs) rfs
      end
  end

let find_frame_mate fr0 fcx1 f1 =
  let rec scan_left lfs rfs =
    begin match lfs with
    | [] -> None
    | lf :: lfs ->
        begin match find_marked lf with
        | Some (fcx2, f2) ->
            Some (lfs, fcx2, f2, rfs, fcx1, f1, fr0.fright)
        | None ->
            scan_left lfs (lf :: rfs)
        end
    end
  and scan_right lfs rfs =
    begin match rfs with
    | [] -> None
    | rf :: rfs ->
        begin match find_marked rf with
        | Some (fcx2, f2) ->
            Some (fr0.fleft, fcx1, f1, lfs, fcx2, f2, rfs)
        | None ->
            scan_right (rf :: lfs) rfs
        end
    end
  in
  begin match scan_left fr0.fleft [] with
  | None -> scan_right [] fr0.fright
  | res -> res
  end

let rec find_fcx_mate fcx0 fcx1 f1 =
  begin match Cx.rear fcx0 with
  | Some (fcx0, fr0) ->
      begin match find_frame_mate fr0 fcx1 f1 with
      | Some (lfs, fcx1, f1, mfs, fcx2, f2, rfs) ->
          let fr0 = { fr0 with
            fleft = lfs ;
            fright = List.rev_append mfs rfs ;
          } in
          let fcx0 = Cx.snoc fcx0 fr0 in
          Some (fcx0, fcx1, f1, fcx2, f2)
      | None ->
          let fcx1 = Cx.cons fr0 fcx1 in
          find_fcx_mate fcx0 fcx1 f1
      end
  | None -> None
  end

type link_matching_error =
  | First_mark_not_found
  | Second_mark_not_found
  | Invalid_marks
  | Bad_ancestor
exception Link_matching of link_matching_error
let linkfail err = raise (Link_matching err)
let explain_link_error = function
  | First_mark_not_found ->
      "Source was not found -- THIS IS A BUG (please report)"
  | Second_mark_not_found ->
      "Sink was not found -- THIS IS A BUG (please report)"
  | Invalid_marks ->
      "Marks were not valid -- THIS IS A BUG (please report)"
  | Bad_ancestor ->
      "Common ancestor of source and sink is not a par -- did you forget a contraction?"

let match_links f : fcx * fcx * form * fcx * form =
  begin match find_marked f with
  | Some (fcx0, f1) ->
      begin match find_fcx_mate fcx0 Cx.empty f1 with
      | Some (fcx0, fcx1, f1, fcx2, f2 as res) ->
          begin match Cx.rear fcx0 with
          | Some (_, {fconn = PAR ; _}) -> ()
          | _ -> linkfail Bad_ancestor
          end ;
          begin match f1, f2 with
          | Conn (Mark SRC, _), Conn (Mark SNK, _)
          | Conn (Mark SNK, _), Conn (Mark SRC, _) -> ()
          | _ -> linkfail Invalid_marks
          end ;
          res
      | None -> linkfail Second_mark_not_found
      end
  | None ->
      linkfail First_mark_not_found
  end
