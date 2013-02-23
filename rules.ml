(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Log

open Syntax
open Syntax_tex

open Traversal

type rule_error =
  | Stuck
  | Promotion
  | Not_par
  | Already_marked

exception Rule_failure of rule_error
let rulefail err = raise (Rule_failure err)

let is_qm fcx f =
  begin match Deque.front fcx with
  | Some ({fconn = QM ; _}, _) -> true
  | Some _ -> false
  | None ->
      begin match f with
      | Conn (Qm, _) -> true
      | _ -> false
      end
  end

let rec bang_free fcx =
  begin match Deque.front fcx with
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

exception Found of form

let find_form pred f0 =
  let rec find_loop f0 =
    let (fcx, f) = unsubst f0 in
    if pred f then raise (Found f0) else
      begin match f with
      | Conn (Mark _, _)
      | Atom _ -> ()
      | Conn (_, fs) ->
          for i = 0 to List.length fs - 1 do
            find_loop (go_down i f0)
          done
      | Subst _ -> assert false
      end
  in
  try find_loop f0 ; raise Not_found with
  | Found f -> f

let find_lnk f =
  let f = find_form (function Conn (Mark (SRC | SNK), _) -> true | _ -> false) f in
  unsubst f

let has_lnk f =
  try ignore (find_lnk f) ; true with Not_found -> false

let make_lnk dir f =
  let (fcx, f) = unsubst f in
  if has_lnk f then rulefail Already_marked ;
  subst fcx (conn (Mark dir) [f])

let unlnk f =
  begin match f with
  | Conn (Mark (SRC | SNK), [f]) -> f
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
    | EX x -> (x, fun () -> EX (Idt.refresh x))
    | ALL x -> (x, fun () -> ALL (Idt.refresh x))
    | _ -> assert false
    end in
  let test ~dep t =
    begin match t with
    | Idx n -> dep = n
    | App (f, _) -> f = x
    end in
  if test_fcx test fcx f
  then { fr with fconn = rx () }
  else fr

let rec resolve_mpar_ fcx1 f1 fcx2 f2 =
  begin match Deque.front fcx1, Deque.front fcx2 with
  | None, None ->
      let f1 = unlnk f1 in
      let f2 = unlnk f2 in
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
      let u2 = go_top (subst fcx2 (unlnk f2)) in
      let dist f = conn Par [f ; u2] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | _, Some ({fconn = WITH ; _} as fr, fcx2) ->
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unlnk f1)) in
      let dist f = conn Par [u1 ; f] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | Some ({fconn = ALL x ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = ALL x ; _} as fr, fcx2) ->
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
  | Some ({fconn = EX x1 ; _} as fr1, fcx1d),
    Some ({fconn = EX x2 ; _} as fr2, fcx2d) ->
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
  | Some ({fconn = EX x ; _} as fr, fcx1), _ ->
      let fr = maybe_refresh fr fcx2 f2 in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = EX x ; _} as fr, fcx2) ->
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
  end

let resolve_mpar f =
  let (fcx0, fcx1, f1, fcx2, f2) = Traversal.match_links (go_top f) in
  let f0 = resolve_mpar_ fcx1 f1 fcx2 f2 in
  go_top (subst fcx0 f0)
