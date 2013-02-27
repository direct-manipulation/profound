(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

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
  begin match Cx.front fcx with
  | Some ({fconn = QM ; _}, _) -> true
  | Some _ -> false
  | None ->
      begin match f with
      | Conn (Qm, _) -> true
      | _ -> false
      end
  end

let rec bang_free fcx =
  begin match Cx.front fcx with
  | None -> true
  | Some ({fconn = BANG ; _}, _) -> false
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
  | Conn (Mark SRC, _) -> true
  | Conn (Mark SNK, _) -> false
  | _ -> assert false
  end

let maybe_refresh fr fcx f =
  let (x, rx) =
    begin match fr.fconn with
    | QU (q, x) -> (x, fun () -> QU (q, Idt.refresh x))
    | _ -> assert false
    end in
  if var_occurs x (subst fcx f)
  then { fr with fconn = rx () }
  else fr

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
      "no common par of ? ancestor of source and sink"

let rec lowest_qm f r =
  begin match Cx.rear f with
  | Some (f, ({fconn = QM ; _} as fr)) -> (f, Cx.cons fr r)
  | Some (f, fr) -> lowest_qm f (Cx.cons fr r)
  | None -> linkfail Bad_ancestor
  end

let unravel gcx fcx1 f1 fcx2 f2 =
  begin match Cx.rear gcx with
  | Some (gcx, fr) ->
      let fr1 = {fr with fright = subst fcx2 (unmark f2) :: fr.fright} in
      let fr2 = {fr with fleft = subst fcx1 (unmark f1) :: fr.fleft} in
      let fcx1 = Cx.cons fr1 fcx1 in
      let fcx2 = Cx.cons fr2 fcx2 in
      (Cx.append gcx fcx1, Cx.append gcx fcx2)
  | None -> assert false
  end

let maybe_contract fcx0 fcx1 f1 fcx2 f2 =
  begin match Cx.rear fcx0 with
  | Some (_, {fconn = PAR ; _}) ->
      (fcx0, fcx1, f1, fcx2, f2)
  | _ ->
      Log.(log DEBUG "Had to contract") ;
      let (fcx0, gcx) = lowest_qm fcx0 Cx.empty in
      let fcx0 = Cx.snoc fcx0 { fconn = PAR ; fleft = [] ; fright = [] } in
      let (fcx1, fcx2) = unravel gcx fcx1 f1 fcx2 f2 in
      (fcx0, fcx1, f1, fcx2, f2)
  end

(* let __debug = atom ASSERT (Idt.intern  "__debug") [] *)

let match_links f =
  begin match find_marked f with
  | Some (fcx0, f1) ->
      begin match find_fcx_mate fcx0 Cx.empty f1 with
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
          (* begin match Cx.rear fcx0 with *)
          (* | Some (_, {fconn = PAR ; _}) -> () *)
          (* | _ -> linkfail Invalid_marks *)
          (* end ; *)
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

let rec resolve_mpar_ fcx1 f1 fcx2 f2 =
  begin match Cx.front fcx1, Cx.front fcx2 with
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
  | Some ({fconn = PAR ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = PAR ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = WITH ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      let u2 = go_top (subst fcx2 (unmark f2)) in
      let dist f = conn Par [f ; u2] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | _, Some ({fconn = WITH ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unmark f1)) in
      let dist f = conn Par [u1 ; f] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | Some ({fconn = QU (All, x) ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = QU (All, x) ; _} as fr, fcx2) ->
      let fr = maybe_refresh fr fcx1 f1 in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = QM ; _}, fcx1), _ when bang_free fcx2 ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | _, Some ({fconn = QM ; _}, fcx2) when bang_free fcx1 ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  (* positive cases *)
  | Some ({fconn = TENS ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = TENS ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = PLUS ; _}, fcx1), _ ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | _, Some ({fconn = PLUS ; _}, fcx2) ->
      resolve_mpar_ fcx1 f1 fcx2 f2
  | Some ({fconn = QU (Ex, x1) ; _} as fr1, fcx1d),
    Some ({fconn = QU (Ex, x2) ; _} as fr2, fcx2d) ->
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
  | Some ({fconn = QU (Ex, x) ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = QU (Ex, x) ; _} as fr, fcx2) ->
      let fr = maybe_refresh fr fcx1 f1 in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = BANG ; _} as fr, fcx1), _ ->
      if not (is_qm fcx2 f2) then rulefail Promotion ;
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = BANG ; _} as fr, fcx2) ->
      if not (is_qm fcx1 f1) then rulefail Promotion ;
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  (* The following are supposedly unreachable states *)
  (* They are just present to silence the exhaustiveness checker *)
  | Some ({fconn = QM ; _}, _), _
  | _, Some ({fconn = QM ; _}, _) ->
      rulefail Stuck
  | _, Some ({fconn = LTO ; _}, _)
  | Some ({fconn = LTO ; _}, _), _ ->
      rulefail Stuck
  end

let resolve_mpar f =
  let (fcx0, fcx1, f1, fcx2, f2) = match_links (go_top f) in
  let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
  go_top (subst fcx0 f0)
