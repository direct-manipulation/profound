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

let fconn_of_conn = function
  | Tens -> TENS | Plus -> PLUS
  | Par -> PAR | With -> WITH
  | All x -> ALL x | Ex x -> EX x
  | Bang -> BANG | Qm -> QM
  | _ -> invalid_arg "fconn_of_conn"

let conn_of_fconn = function
  | TENS -> Tens | PLUS -> Plus
  | PAR -> Par | WITH -> With
  | ALL x -> All x | EX x -> Ex x
  | BANG -> Bang | QM -> Qm

let fconn fc = conn (conn_of_fconn fc)

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

