(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type idt = Idt.t

type term =
  | Idx   of int
  | App   of idt * term list

type sign = ASSERT | REFUTE

type form =
  | Atom  of sign * idt * term list
  | Conn  of conn * form list
  | Subst of fcx * form

and fcx = frame Deque.t

and frame = {
  fconn  : fconn ;
  fleft  : form list ;
  fright : form list ;
}

and conn =
  | Tens | One | Plus | Zero | Par | Bot | With | Top
  | All of idt | Ex of idt
  | Bang | Qm
  | Mpar
  | Mark of mkind

and fconn = 
  | TENS | PLUS | PAR | WITH
  | ALL of idt | EX of idt
  | BANG | QM

and mkind =
  | ARG | SRC | SNK

type sub =
  | Shift of int
  | Dot of sub * term

let rec sub_idx ss n =
  begin match ss with
  | Shift j -> Idx (j + n)
  | Dot (_, t) when n = 0 -> t
  | Dot (ss, _) -> sub_idx ss (n - 1)
  end

and sub_term ss t =
  begin match t with
  | Idx n -> sub_idx ss n
  | App (f, ts) -> App (f, List.map (sub_term ss) ts)
  end

and sub_form ss f =
  begin match f with
  | Atom (s, p, ts) ->
      Atom (s, p, List.map (sub_term ss) ts)
  | Conn ((All x | Ex x) as c, fs) ->
      Conn (c, List.map (sub_form (bump ss)) fs)
  | Conn (c, fs) ->
      Conn (c, List.map (sub_form ss) fs)
  | Subst (fcx, f) ->
      let (fcx, ss) = sub_fcx ss fcx in
      Subst (fcx, sub_form ss f)
  end

and sub_fcx ss fcx =
  begin match Deque.front fcx with
  | Some ({ fconn = (ALL _ | EX _) ; _ } as fr, fcx) ->
      let (fcx, ss) = sub_fcx (bump ss) fcx in
      (Deque.cons fr fcx, ss)
  | Some (fr, fcx) ->
      let fr = { fr with
        fleft = List.map (sub_form ss) fr.fleft ;
        fright = List.map (sub_form ss) fr.fright ;
      } in
      let (fcx, ss) = sub_fcx ss fcx in
      (Deque.cons fr fcx, ss)
  | None ->
      (Deque.empty, ss)
  end

and bump ss = Dot (seq (Shift 1) ss, Idx 0)

and seq ss tt =
  begin match ss, tt with
  | Shift j, Shift k -> Shift (j + k)
  | ss, Shift 0 -> ss
  | Shift 0, tt -> tt
  | Dot (ss, _), Shift j ->
      seq ss (Shift (j - 1))
  | _, Dot (tt, t) ->
      Dot (seq ss tt, sub_term ss t)
  end

let rec free_term x t =
  begin match t with
  | Idx k -> x = k
  | App (_, ts) ->
      List.exists (free_term x) ts
  end

and free_form x f =
  begin match f with
  | Atom (_, _, ts) ->
      List.exists (free_term x) ts
  | Conn ((Ex _ | All _), fs) ->
      List.exists (free_form (x + 1)) fs
  | Conn (c, fs) ->
      List.exists (free_form x) fs
  | Subst (fcx, f) ->
      free_fcx x fcx f
  end

and free_fcx x fcx f =
  begin match Deque.front fcx with
  | None -> free_form x f
  | Some ({fconn = (EX _ | ALL _) ; _}, fcx) ->
      free_fcx (x + 1) fcx f
  | Some (fr, fcx) ->
      List.exists (free_form x) fr.fleft
      || List.exists (free_form x) fr.fright
      || free_fcx x fcx f
  end

let atom s p ts = Atom (s, p, ts)

let mk_kon c fs =
  begin match fs with
  | [] -> Conn (c, [])
  | _ -> assert false
  end

let mk_tens fs =
  begin match fs with
  | [Conn (One, []) ; f]
  | [f ; Conn(One, [])] ->
      f
  | [f ; g] ->
      Conn (Tens, [f ; g])
  | _ -> assert false
  end

let mk_plus fs =
  begin match fs with
  | [Conn (Zero, []) ; f]
  | [f ; Conn (Zero, [])] ->
      f
  | [Conn (One, []) ; Conn (One, [])] ->
      Conn (One, [])
  | [f ; g] ->
      Conn (Plus, [f ; g])
  | _ -> assert false
  end

let mk_par fs =
  begin match fs with
  | [Conn (Bot, []) ; f]
  | [f ; Conn (Bot, [])] ->
      f
  | [f ; Conn (Top, [])]
  | [Conn (Top, []) ; f] ->
      Conn (Top, [])
  | [f ; g] ->
      Conn (Par, [f ; g])
  | _ -> assert false
  end

let mk_with fs =
  begin match fs with
  | [Conn (Top, []) ; f]
  | [f ; Conn (Top, [])] ->
      f
  | [Conn (One, []) ; Conn (One, [])] ->
      Conn (One, [])
  | [f ; g] ->
      Conn (With, [f ; g])
  | _ -> assert false
  end

let mk_bang fs =
  begin match fs with
  | [Conn (One, [])]
  | [Conn (Top, [])] ->
      Conn (One, [])
  | [f] ->
      Conn (Bang, [f])
  | _ -> assert false
  end

let mk_qm fs =
  begin match fs with
  | [Conn (Bot, [])]
  | [Conn (Zero, [])] ->
      Conn (Bot, [])
  | [f] ->
      Conn (Qm, [f])
  | _ -> assert false
  end

let mk_quant q fs =
  begin match fs with
  | [f] ->
      if free_form 0 f || true then
        Conn (q, [f])
      else
        sub_form (Dot (Shift 0, Idx min_int)) f
  | _ -> assert false
  end

let mk_mpar fs =
  begin match fs with
  | [_ ; _] -> Conn (Mpar, fs)
  | _ -> assert false
  end

let mk_mark m fs =
  begin match fs with
  | [_] -> Conn (m, fs)
  | _ -> assert false
  end

let conn c =
  begin match c with
  | Tens   -> mk_tens
  | Plus   -> mk_plus
  | Par    -> mk_par
  | With   -> mk_with
  | Bang   -> mk_bang
  | Qm     -> mk_qm
  | All _
  | Ex _   -> mk_quant c
  | Mpar   -> mk_mpar
  | Mark _ -> mk_mark c
  | One | Zero | Bot | Top ->
      mk_kon c
  end

type traversal_error =
  | At_leaf
  | At_top
  | At_edge
  | No_such_child

exception Traversal of traversal_error
let travfail err = raise (Traversal err)

let fconn_of_conn = function
  | Tens -> TENS | Plus -> PLUS
  | Par -> PAR | With -> WITH
  | All x -> ALL x | Ex x -> EX x
  | Bang -> BANG | Qm -> QM
  | _ -> travfail At_leaf

let conn_of_fconn = function
  | TENS -> Tens | PLUS -> Plus
  | PAR -> Par | WITH -> With
  | ALL x -> All x | EX x -> Ex x
  | BANG -> Bang | QM -> Qm

let fconn fc = conn (conn_of_fconn fc)

let rec split3 n xs =
  try begin match List.split_at n xs with
  | l, (u :: r) -> (l, u, r)
  | _ -> travfail No_such_child
  end with _ -> travfail No_such_child

let subst fcx f =
  begin match f with
  | Subst (fcx1, f) ->
      Subst (Deque.append fcx fcx1, f)
  | _ ->
      if Deque.is_empty fcx then f
      else Subst (fcx, f)
  end

let subst1 fr f = subst (Deque.of_list [fr]) f

let rec unsubst f k =
  begin match f with
  | Subst (fcx, f) ->
      unsubst f begin
        fun fcx' f ->
          k (Deque.append fcx fcx') f
      end
  | _ -> k Deque.empty f
  end
let unsubst f = unsubst f (fun fcx f -> (fcx, f))

let unframe fr f =
  fconn fr.fconn (fr.fleft @ (f :: fr.fright))

let head1 f =
  match f with
  | Subst (fcx, f) ->
      begin match Deque.front fcx with
      | Some (fr, fcx) -> unframe fr (subst fcx f)
      | None -> assert false
      end
  | _ -> f

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

exception Stuck

let rec equate ts1 ts2 =
  begin match ts1, ts2 with
  | [], [] -> Conn (One, [])
  | [t1], [t2] ->
      Atom (ASSERT, Idt.intern "=", [t1 ; t2])
  | (t1 :: ts1), (t2 :: ts2) ->
      Conn (Tens, [ Atom (ASSERT, Idt.intern "=", [t1 ; t2])
                  ; equate ts1 ts2 ])
  | _ ->
      Conn (Bot, [])
  end

let freshen =
  let last = ref 0 in
  fun x ->
    incr last ;
    Idt.intern (Idt.rep x ^ "_{" ^ string_of_int !last ^ "}")

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
      | Conn (_, fs) ->
          for i = 0 to List.length fs - 1 do
            find_loop (go_down i f0)
          done
      | Atom _ -> ()
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
  let f = find_form is_mpar f in
  let (fcx, f) = unsubst f in
  begin match f with
  | Conn (Par, [f ; g]) -> (fcx, f, g)
  | _ -> assert false
  end

let link_normal_form f =
  let (fcx0, f, g) = find_mpar f in
  let (fcx1, f) = find_lnk f in
  let (fcx2, g) = find_lnk g in
  subst fcx0 (Conn (Mpar, [subst fcx1 f ; subst fcx2 g]))

exception Already_marked

let make_lnk dir f =
  let (fcx, f) = unsubst f in
  assert (try ignore (find_lnk f) ; false with Not_found -> true) ;
  begin match f with
  | Conn (Mark (SRC | SNK), _) -> raise Already_marked
  | _ ->
      let f = Conn (Mark dir, [f]) in
      subst fcx f
  end

let unlnk f =
  begin match f with
  | Conn (Mark (SRC | SNK), [f]) -> f
  | _ -> assert false
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
          Conn (Par, [f1 ; f2])
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
      let dist f = Conn (Par, [f ; u2]) in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | _, Some ({fconn = WITH ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unlnk f1)) in
      let dist f = Conn (Par, [u1 ; f]) in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | Some ({fconn = ALL x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = ALL (freshen x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = ALL x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = ALL (freshen x) } in
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
        let fr2 = { fr2 with fconn = EX (freshen x2) } in
        let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
        let f1 = sub_form ss f1 in
        let f0 = resolve_mpar fcx1 f1 fcx2d f2 in
        unframe fr2 f0
      end else begin
        let fr1 = { fr1 with fconn = EX (freshen x1) } in
        let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
        let f2 = sub_form ss f2 in
        let f0 = resolve_mpar fcx1d f1 fcx2 f2 in
        unframe fr1 f0
      end
  | Some ({fconn = EX x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = EX (freshen x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = EX x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = EX (freshen x) } in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = BANG ; _} as fr, fcx1), _ ->
      if not (is_qm fcx2 f2) then raise Stuck ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = BANG ; _} as fr, fcx2) ->
      if not (is_qm fcx1 f1) then raise Stuck ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  (* The following are supposedly unreachable states *)
  (* They are just present to silence the exhaustiveness checker *)
  | Some ({fconn = QM ; _}, _), _
  | _, Some ({fconn = QM ; _}, _) ->
      raise Stuck
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

exception Rule_int of form

let rule_int tr1 tr2 f =
  let f = make_lnk SRC (descend tr1 f) in
  let f = go_top f in
  let f = make_lnk SNK (descend tr2 f) in
  let f = go_top f in
  f

module Pp = struct
  open Buffer
  open Printf

  let add_idt buf i = add_string buf (Idt.rep i)

  let salt =
    let last = ref 0 in
    fun x -> incr last ; Idt.intern (Idt.rep x ^ string_of_int !last)

  let rec adj cx x =
    if List.mem x cx then
      adj cx (salt x)
    else
      (x :: cx, x)

  let rec pp_term cx buf t =
    begin match t with
    | Idx n ->
        add_idt buf (List.nth cx n)
    | App (f, []) ->
        add_idt buf f
    | App (f, ts) ->
        add_idt buf f ;
        add_string buf "(" ;
        pp_terms cx buf ts ;
        add_string buf ")"
    end

  and pp_terms cx buf ts =
    begin match ts with
    | [t] ->
        pp_term cx buf t
    | t :: ts ->
        pp_term cx buf t ;
        add_string buf "," ;
        pp_terms cx buf ts
    | [] -> assert false
    end

  let rec pp_form cx buf f =
    begin match f with
    | Atom (ASSERT, p, ts) ->
        begin match Idt.rep p, ts with
        | "=", [s ; t] ->
            pp_term cx buf s ;
            add_string buf " = " ;
            pp_term cx buf t
        | _ -> pp_term cx buf (App (p, ts))
        end
    | Atom (REFUTE, p, ts) ->
        begin match Idt.rep p, ts with
        | "=", [s ; t] ->
            pp_term cx buf s ;
            add_string buf " \\neq " ;
            pp_term cx buf t
        | _ -> 
            add_string buf "\\lnot " ;
            pp_term cx buf (App (p, ts)) ;
        end
    | Conn (Mark ARG, [f]) ->
        add_string buf "\\fbox{$" ;
        pp_form cx buf f ;
        add_string buf "$}"
    | Conn (Mark (SRC | SNK as dir), [f]) ->
        add_string buf "\\left[" ;
        (* bprintf buf "\\left[\\mathfrak{u}{%s}" *)
        (*   (match dir with SRC -> "\\uparrow" | _ -> "\\downarrow") ; *)
        pp_form cx buf f ;
        bprintf buf "\\right]^{\\smash{%s}}"
          (match dir with SRC -> "\\Uparrow" | _ -> "\\Downarrow")
    | Conn (p, [f ; g]) ->
        pp_bracket ~p cx buf f ;
        add_string buf (bin_string p) ;
        pp_bracket ~p cx buf g
    | Conn ((All x | Ex x) as p, [f]) ->
        add_string buf (un_string p) ;
        pp_bracket ~p (x :: cx) buf f
    | Conn (p, [f]) ->
        add_string buf (un_string p) ;
        pp_bracket ~p cx buf f ;
    | Conn (p, []) ->
        add_string buf (kon_string p)
    | Conn _ -> assert false
    | Subst (fcx, f) ->
        let f = Conn (Mark ARG, [f]) in
        let f = go_top (Subst (fcx, f)) in
        pp_form cx buf f
    end

  and extend cx fcx =
    begin match Deque.front fcx with
    | Some ({ fconn = (ALL x | EX x) ; _}, fcx) ->
        extend (x :: cx) fcx
    | Some (_, fcx) ->
        extend cx fcx
    | None -> cx
    end

  and pp_bracket ~p cx buf f =
    begin match head1 f with
    | Conn (Mark _, [_]) ->
        pp_form cx buf f
    | Conn (q, _) ->
        if p = q || (is_un p && is_un q) || prec p < prec q then
          pp_form cx buf f
        else begin
          add_string buf "\\left(" ;
          pp_form cx buf f ;
          add_string buf "\\right)"
        end
    | _ ->
        pp_form cx buf f
    end

  and is_un = function
    | All _ | Ex _ | Bang | Qm -> true
    | _ -> false

  and bin_string = function
    | Tens -> " \\TENS "
    | Plus -> " \\PLUS "
    | Par  -> " \\PAR "
    | With -> " \\WITH "
    | Mpar -> " \\MPAR "
    | _ -> assert false

  and un_string = function
    | All x -> "\\ALL " ^ Idt.rep x ^ ". "
    | Ex x -> "\\EX " ^ Idt.rep x ^ ". "
    | Bang -> "\\BANG "
    | Qm -> "\\QM "
    | _ -> assert false

  and kon_string = function
    | One -> "\\ONE"
    | Zero -> "\\ZERO"
    | Bot -> "\\BOT"
    | Top -> "\\TOP"
    | _ -> assert false

  and prec = function
    | Mpar -> 1 (* 0 *)
    | Par -> 1
    | Plus -> 1 (* 2 *)
    | With -> 1 (* 3 *)
    | Tens -> 1 (* 4 *)
    | Ex _ | All _ -> 0
    | Bang | Qm -> 6
    | One | Zero | Top | Bot | Mark _ -> max_int

  let wash_forms ?(cx = []) fs =
    let buf = Buffer.create 19 in
    add_string buf "{}" ;
    List.iter begin
      fun f ->
        pp_form cx buf f ;
        add_string buf "\\\\" ;
    end fs ;
    let ch = open_out "/tmp/foo.tex" in
    output_string ch (Buffer.contents buf) ;
    close_out ch ;
    Sys.command "( cd /tmp && pdflatex bar.tex && pdfcrop --margin 3 bar.pdf bar-c.pdf ) >/dev/null 2>&1"
end
        


module C : sig val forms : form list ref end = struct

  open Idt

  let idx n = Idx n
  let app f ts = App (intern f, ts)

  let negate_sign = function
    | ASSERT -> REFUTE
    | REFUTE -> ASSERT

  let dual_conn = function
    | Tens -> Par | One -> Bot
    | Plus -> With | Zero -> Top
    | Par -> Tens | Bot -> One
    | With -> Plus | Top -> Zero
    | All x -> Ex x | Ex x -> All x
    | Bang -> Qm | Qm -> Bang
    | Mpar | Mark _ -> invalid_arg "dual: found MPAR or MARK"

  let rec dual f =
    begin match f with
    | Conn (c, fs) ->
        Conn (dual_conn c, List.map dual fs)
    | Atom (s, p, ts) ->
        Atom (negate_sign s, p, ts)
    | Subst (fcx, f) ->
        subst (dual_fcx fcx) (dual f)
    end

  and dual_fcx fcx =
    Deque.map dual_frame fcx

  and dual_frame fr = {
    fconn = fconn_of_conn (dual_conn (conn_of_fconn fr.fconn)) ;
    fleft = List.map dual fr.fleft ;
    fright = List.map dual fr.fright ;
  }

  let tens     = conn Tens
  let one      = conn One []
  let plus     = conn Plus
  let zero     = conn Zero []
  let par      = conn Par
  let bot      = conn Bot []
  let wth      = conn With
  let top      = conn Top []
  let all x f  = conn (All (intern x)) [f]
  let ex x f   = conn (Ex (intern x)) [f]
  let bang f   = conn Bang [f]
  let qm f     = conn Qm [f]
  let mpar f g = conn Mpar [f; g]

  let atom p ts = Atom (ASSERT, intern p, ts)
  let natm p ts = Atom (REFUTE, intern p, ts)

  let a  = atom "a" []
  let a' = natm "a" []
  let b  = atom "b" []
  let b' = natm "b" []
  let c  = atom "c" []
  let c' = natm "c" []
  let d  = atom "d" []
  let d' = natm "d" []

  let forms = ref []
  let push f = forms := f :: !forms ; f
  let ( |> ) x f = f x

  (*
    let f0 = par [qm a' ; bang (bang a)] |> push
    let i0 = rule_int [0 ; 0] [1; 0 ; 0] f0 |> push
    let r0 = go_top (resolve_mpar i0) |> push
  *)


  let f0 = par [tens [a ; b] ;
                par [wth [a' ; b'] ;
                     plus [a' ; b']]] |> push
  let f0 = rule_int [0 ; 0] [1 ; 0 ; 0] f0 |> push
  let f0 = resolve_mpar f0 |> push
  (* let f0 = rule_int [0 ; 1 ; 1]  [0 ; 1 ; 0 ; 1] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)
  (* let f0 = rule_int [0 ; 0] [1 ; 1] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)
  (* let f0 = rule_int [1 ; 0] [1 ; 1 ; 0] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)

  (* let f0 = par [ex "x" (all "y" (plus [natm "p" [idx 1] ; *)
  (*                                      atom "p" [idx 0]])) ; *)
  (*               ex "x" (all "y" (ex "z" (plus [natm "p" [idx 2] ; *)
  (*                                      atom "p" [idx 1]])))] |> push *)
  (* let f0 = make_lnk SRC (descend [0 ; 0 ; 0 ; 0] f0) *)
  (* let f0 = go_top f0 *)
  (* let f0 = make_lnk SNK (descend [1 ; 0 ; 0 ; 0 ; 1] f0) *)
  (* let f0 = go_top f0 |> push *)
  (* let r0 = resolve_mpar f0 |> push *)

end

let _ = Pp.wash_forms !C.forms
