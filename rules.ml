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
  if t1 = t2 then conn One [] else
    atom ASSERT equals [t1 ; t2]

let rec equate ts1 ts2 =
  begin match ts1, ts2 with
  | [], [] ->
      conn One []
  | [t1], [t2] ->
      maybe_eq t1 t2
  | (t1 :: ts1), (t2 :: ts2) ->
      conn Tens [ maybe_eq t1 t2
                ; equate ts1 ts2 ]
  | _ ->
      conn Bot []
  end

let rec reduce_choices fcx f =
  begin match Deque.front fcx with
  | None -> (fcx, f)
  | Some ({fconn = PLUS ; _}, fcx) ->
      reduce_choices fcx f
  | Some ({fconn = (ALL _ | EX _) ; _} as fr, fcx) ->
      let (fcx, f) = reduce_choices fcx f in
      if free_fcx 0 fcx f then
        (Deque.cons fr fcx, f)
      else
        let ss = Dot (Shift 0, Idx min_int) in
        let (fcx, ss) = sub_fcx ss fcx in
        let f = sub_form ss f in
        (fcx, f)
  | Some (fr, fcx) ->
      let (fcx, f) = reduce_choices fcx f in
      (Deque.cons fr fcx, f)
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
      | Conn ((Mpar | Mark _ ), _)
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

let is_mpar f =
  begin match f with
  | Conn (Par, [f ; g]) ->
      has_lnk f && has_lnk g
  | _ -> false
  end

let find_mpar f =
  let f = try find_form is_mpar f with Not_found -> rulefail Not_par in
  let (fcx, f) = unsubst f in
  begin match f with
  | Conn (Par, [f ; g]) -> (fcx, f, g)
  | _ -> assert false
  end

let link_normal_form f =
  let (fcx0, f, g) = find_mpar f in
  let (fcx1, f) = find_lnk f in
  let (fcx2, g) = find_lnk g in
  subst fcx0 (conn Mpar [subst fcx1 f ; subst fcx2 g])

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

let rec resolve_mpar fcx1 f1 fcx2 f2 =
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
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = PAR ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = WITH ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      let u2 = go_top (subst fcx2 (unlnk f2)) in
      let dist f = conn Par [f ; u2] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | _, Some ({fconn = WITH ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unlnk f1)) in
      let dist f = conn Par [u1 ; f] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | Some ({fconn = ALL x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = ALL (salt x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = ALL x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = ALL (salt x) } in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = QM ; _}, fcx1), _ when bang_free fcx2 ->
      resolve_mpar fcx1 f1 fcx2 f2
  | _, Some ({fconn = QM ; _}, fcx2) when bang_free fcx1 ->
      resolve_mpar fcx1 f1 fcx2 f2
  (* positive cases *)
  | Some ({fconn = TENS ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = TENS ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = PLUS ; _}, fcx1), _ ->
      resolve_mpar fcx1 f1 fcx2 f2
  | _, Some ({fconn = PLUS ; _}, fcx2) ->
      resolve_mpar fcx1 f1 fcx2 f2
  | Some ({fconn = EX x1 ; _} as fr1, fcx1d),
    Some ({fconn = EX x2 ; _} as fr2, fcx2d) ->
      if is_src f1 then begin
        let fr2 = { fr2 with fconn = EX (salt x2) } in
        let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
        let f1 = sub_form ss f1 in
        let f0 = resolve_mpar fcx1 f1 fcx2d f2 in
        unframe fr2 f0
      end else begin
        let fr1 = { fr1 with fconn = EX (salt x1) } in
        let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
        let f2 = sub_form ss f2 in
        let f0 = resolve_mpar fcx1d f1 fcx2 f2 in
        unframe fr1 f0
      end
  | Some ({fconn = EX x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = EX (salt x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = EX x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = EX (salt x) } in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = BANG ; _} as fr, fcx1), _ ->
      if not (is_qm fcx2 f2) then rulefail Promotion ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = BANG ; _} as fr, fcx2) ->
      if not (is_qm fcx1 f1) then rulefail Promotion ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  (* The following are supposedly unreachable states *)
  (* They are just present to silence the exhaustiveness checker *)
  | Some ({fconn = QM ; _}, _), _
  | _, Some ({fconn = QM ; _}, _) ->
      rulefail Stuck
  end
let resolve_mpar_internal = resolve_mpar

let resolve_mpar f =
  let f = link_normal_form (go_top f) in
  let (fcx, f) = unsubst f in
  begin match f with
  | Conn (Mpar, [f1 ; f2]) ->
      let (fcx1, f1) = unsubst f1 in
      (* let (fcx1, f1) = reduce_choices fcx1 f1 in *)
      let (fcx2, f2) = unsubst f2 in
      (* let (fcx2, f2) = reduce_choices fcx2 f2 in *)
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      go_top (subst fcx f0)
  | _ -> assert false
  end

let rule_int tr1 tr2 f =
  let f = make_lnk SRC (descend tr1 f) in
  let f = go_top f in
  let f = make_lnk SNK (descend tr2 f) in
  let f = go_top f in
  f
