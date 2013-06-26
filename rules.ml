(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
open Log

open Syntax

open Traversal

type rule_error =
  | Stuck
  | Promotion
  | Already_marked

exception Rule_failure of rule_error
let rulefail err = raise (Rule_failure err)
let explain = function
  | Stuck -> "got stuck resolving link -- THIS IS A BUG (please report)"
  | Promotion -> "link violates exponential boundaries"
  | Already_marked -> "trying to mark a marked formula -- THIS IS A BUG (please report)"

let is_qm fcx f =
  begin match Fcx.front fcx with
  | Some ({conn = Qm ; _}, _) -> true
  | Some _ -> false
  | None ->
      begin match f with
      | Conn (Qm, _) -> true
      | _ -> false
      end
  end

let rec bang_free fcx =
  begin match Fcx.front fcx with
  | None -> true
  | Some ({conn = Bang ; _}, _) -> false
  | Some (_, fcx) -> bang_free fcx
  end

let maybe_eq t1 t2 =
  if t1 = t2 then conn Tens [] else
    atom ASSERT equals [t1 ; t2]

let rec equate ts1 ts2 =
  begin match ts1, ts2 with
  | [], [] ->
      conn Tens []
  | [t1], [t2] ->
      maybe_eq t1 t2
  | (t1 :: ts1), (t2 :: ts2) ->
      conn Tens [ maybe_eq t1 t2
                ; equate ts1 ts2 ]
  | _ ->
      conn Par []
  end

let main_arg f =
  begin match f with
  | Subst (_, f) -> f
  | _ -> f
  end

let is_src f =
  begin match f with
  | Mark (SRC, _) -> true
  | _ -> false
  end

let maybe_refresh fr fcx f =
  let (x, rx) =
    begin match fr.conn with
    | Qu (q, x) -> (x, fun () -> Qu (q, Idt.refresh x))
    | _ -> assert false
    end in
  if var_occurs x (subst fcx f)
  then { fr with conn = rx () }
  else fr

let rec find_marked f =
  begin match f with
  | Atom _ -> None
  | Subst _ -> assert false
  | Mark _ -> Some (Fcx.empty, f)
  | Conn (c, fs) ->
      begin match find_marked_arg [] fs with
      | Some (lfs, fcx, f, rfs) ->
          let fr = {
            conn = c ;
            left = lfs ;
            right = rfs ;
          } in
          let fcx = Fcx.cons fr fcx in
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
            Some (lfs, fcx2, f2, rfs, fcx1, f1, fr0.right)
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
            Some (fr0.left, fcx1, f1, lfs, fcx2, f2, rfs)
        | None ->
            scan_right (rf :: lfs) rfs
        end
    end
  in
  begin match scan_left fr0.left [] with
  | None -> scan_right [] fr0.right
  | res -> res
  end

let rec find_fcx_mate fcx0 fcx1 f1 =
  begin match Fcx.rear fcx0 with
  | Some (fcx0, fr0) ->
      begin match find_frame_mate fr0 fcx1 f1 with
      | Some (lfs, fcx1, f1, mfs, fcx2, f2, rfs) ->
          let fr0 = { fr0 with
                      left = lfs ;
                      right = List.rev_append mfs rfs ;
                    } in
          let fcx0 = Fcx.snoc fcx0 fr0 in
          Some (fcx0, fcx1, f1, fcx2, f2)
      | None ->
          let fcx1 = Fcx.cons fr0 fcx1 in
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
      "no common par of ? ancestor of source and sink"

let rec lowest_qm f r =
  begin match Fcx.rear f with
  | Some (f, ({conn = Qm ; _} as fr)) -> (f, Fcx.cons fr r)
  | Some (f, fr) -> lowest_qm f (Fcx.cons fr r)
  | None -> linkfail Bad_ancestor
  end

let unravel gcx fcx1 f1 fcx2 f2 =
  begin match Fcx.rear gcx with
  | Some (gcx, fr) ->
      let fr1 = {fr with right = subst fcx2 (unmark f2) :: fr.right} in
      let fr2 = {fr with left = subst fcx1 (unmark f1) :: fr.left} in
      let fcx1 = Fcx.cons fr1 fcx1 in
      let fcx2 = Fcx.cons fr2 fcx2 in
      (Fcx.append gcx fcx1, Fcx.append gcx fcx2)
  | None -> assert false
  end

let maybe_contract fcx0 fcx1 f1 fcx2 f2 =
  begin match Fcx.rear fcx0 with
  | Some (_, {conn = Par ; _}) ->
      (fcx0, fcx1, f1, fcx2, f2)
  | _ ->
      Log.(log DEBUG "Had to contract") ;
      let (fcx0, gcx) = lowest_qm fcx0 Fcx.empty in
      let fcx0 = Fcx.snoc fcx0 { conn = Par ; left = [] ; right = [] } in
      let (fcx1, fcx2) = unravel gcx fcx1 f1 fcx2 f2 in
      (fcx0, fcx1, f1, fcx2, f2)
  end

(* let __debug = atom ASSERT (Idt.intern  "__debug") [] *)

let match_links f =
  begin match find_marked f with
  | Some (fcx0, f1) ->
      begin match find_fcx_mate fcx0 Fcx.empty f1 with
      | Some (fcx0, fcx1, f1, fcx2, f2) ->
          (* Log.(log DEBUG "match_links PRE begin") ; *)
          (* Log.(log DEBUG " f0 = %s" (Syntax_tex.form_to_string [] (subst fcx0 __debug))) ; *)
          (* Log.(log DEBUG " f1 = %s" (Syntax_tex.form_to_string (fcx_vars fcx0) (subst fcx1 f1))) ; *)
          (* Log.(log DEBUG " f2 = %s" (Syntax_tex.form_to_string (fcx_vars fcx0) (subst fcx2 f2))) ; *)
          (* Log.(log DEBUG "match_links PRE end") ; *)
          let (fcx0, fcx1, f1, fcx2, f2) as res = maybe_contract fcx0 fcx1 f1 fcx2 f2 in
          (* Log.(log DEBUG "match_links POST begin") ; *)
          (* Log.(log DEBUG " f0 = %s" (Syntax_tex.form_to_string [] (subst fcx0 __debug))) ; *)
          (* Log.(log DEBUG " f1 = %s" (Syntax_tex.form_to_string (fcx_vars fcx0) (subst fcx1 f1))) ; *)
          (* Log.(log DEBUG " f2 = %s" (Syntax_tex.form_to_string (fcx_vars fcx0) (subst fcx2 f2))) ; *)
          (* Log.(log DEBUG "match_links POST end") ; *)
          (* begin match Fcx.rear fcx0 with *)
          (* | Some (_, {conn = PAR ; _}) -> () *)
          (* | _ -> linkfail Invalid_marks *)
          (* end ; *)
          begin match f1, f2 with
          | Mark (SRC, _), Mark (SNK, _)
          | Mark (SNK, _), Mark (SRC, _) -> ()
          | _ -> linkfail Invalid_marks
          end ;
          res
      | None -> linkfail Second_mark_not_found
      end
  | None ->
      linkfail First_mark_not_found
  end

let rec resolve_mpar_ fcx1 f1 fcx2 f2 =
  begin match Fcx.front fcx1, Fcx.front fcx2 with
  | None, None ->
      let f1 = unmark f1 in
      let f2 = unmark f2 in
      begin match f1, f2 with
      | Atom (s1, p1, ts1), Atom (s2, p2, ts2)
        when s1 <> s2 && p1 = p2 ->
          equate ts1 ts2
      | _ ->
          conn Par [f1 ; f2]
      end
  (* negative cases *)
  | Some ({conn = Par ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({conn = Par ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({conn = With ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      let u2 = go_top (subst fcx2 (unmark f2)) in
      let dist f = conn Par [f ; u2] in
      let fr = { fr with
                 left = List.map dist fr.left ;
                 right = List.map dist fr.right ;
               } in
      unframe fr f0
  | _, Some ({conn = With ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unmark f1)) in
      let dist f = conn Par [u1 ; f] in
      let fr = { fr with
                 left = List.map dist fr.left ;
                 right = List.map dist fr.right ;
               } in
      unframe fr f0
  | Some ({conn = Qu (All, x) ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({conn = Qu (All, x) ; _} as fr, fcx2) ->
      let fr = maybe_refresh fr fcx1 f1 in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({conn = Qm ; _} as fr, fcx1), Some ({conn = Qm ; _}, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({conn = Qm ; _}, fcx1), _ when bang_free fcx2 ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | _, Some ({conn = Qm ; _}, fcx2) when bang_free fcx1 ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  (* positive cases *)
  | Some ({conn = Tens ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({conn = Tens ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({conn = Plus ; _}, fcx1), _ ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | _, Some ({conn = Plus ; _}, fcx2) ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | Some ({conn = Qu (Ex, x1) ; _} as fr1, fcx1d),
    Some ({conn = Qu (Ex, x2) ; _} as fr2, fcx2d) ->
      if is_src f1 then begin
        let fr2 = maybe_refresh fr2 fcx1 f1 in
        let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
        let f1 = sub_form ss f1 in
        let f0 = resolve_mpar_ fcx1 f1 fcx2d f2 in
        unframe fr2 f0
      end else begin
        let fr1 = maybe_refresh fr1 fcx2 f2 in
        let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
        let f2 = sub_form ss f2 in
        let f0 = resolve_mpar_ fcx1d f1 fcx2 f2 in
        unframe fr1 f0
      end
  | Some ({conn = Qu (Ex, x) ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({conn = Qu (Ex, x) ; _} as fr, fcx2) ->
      let fr = maybe_refresh fr fcx1 f1 in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({conn = Bang ; _} as fr, fcx1), _ ->
      if not (is_qm fcx2 f2) then rulefail Promotion ;
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({conn = Bang ; _} as fr, fcx2) ->
      if not (is_qm fcx1 f1) then rulefail Promotion ;
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  (* The following are supposedly unreachable states *)
  (* They are just present to silence the exhaustiveness checker *)
  | Some ({conn = Qm ; _}, _), _
  | _, Some ({conn = Qm ; _}, _) ->
      rulefail Stuck
  | _, Some ({conn = Lto ; _}, _)
  | Some ({conn = Lto ; _}, _), _ ->
      rulefail Stuck
  end

let resolve_mpar f =
  let (fcx0, fcx1, f1, fcx2, f2) = match_links (go_top f) in
  let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
  go_top (subst fcx0 f0)
