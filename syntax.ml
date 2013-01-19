(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries_uni

type idt = Idt.t

module Base = struct

  type term =
    | Idx   of int
    | App   of idt * term list

  type sign = PLUS | MINUS

  type form =
    | Atom  of sign * idt * term list
    | Conn  of conn * form list
    | Subst of fcx * form

  and fcx = frame Deque.t

  and frame = {
    fconn  : conn ;
    fleft  : form list ;
    fright : form list ;
  }

  and conn =
    | TENS | ONE | PLUS | ZERO | PAR | BOT | WITH | TOP
    | ALL of idt | EX of idt
    | MPAR

  let mk_bin c fs =
    begin match fs with
    | [_ ; _] -> Conn (c, fs)
    | _ -> assert false
    end

  let mk_tens = mk_bin TENS
  let mk_plus = mk_bin PLUS
  let mk_par  = mk_bin PAR
  let mk_with = mk_bin WITH

  let mk_kon c fs =
    begin match fs with
    | [] -> Conn (c, [])
    | _ -> assert false
    end

  let mk_one = mk_kon ONE
  let mk_zero = mk_kon ZERO
  let mk_bot = mk_kon BOT
  let mk_top = mk_kon TOP

  let mk_quant q x fs =
    begin match fs with
    | [_] -> Conn (q x, fs)
    | _ -> assert false
    end

  let mk_all = mk_quant (fun x -> ALL x)
  let mk_ex  = mk_quant (fun x -> EX x)

  let mk_mpar = mk_bin MPAR

  let mk = function
    | TENS -> mk_tens
    | ONE -> mk_one
    | PLUS -> mk_plus
    | ZERO -> mk_zero
    | PAR -> mk_par
    | BOT -> mk_bot
    | WITH -> mk_with
    | TOP -> mk_top
    | ALL x -> mk_all x
    | EX x -> mk_ex x
    | MPAR -> mk_mpar

  exception Leaf
  exception Bad_index

  let rec split3 n xs =
    try begin match List.split_at n xs with
    | l, (u :: r) -> (l, u, r)
    | _ -> raise Bad_index
    end with _ -> raise Bad_index

  let place fcx f =
    begin match f with
    | Subst (fcx1, f) ->
        Subst (Deque.append fcx fcx1, f)
    | _ ->
        if Deque.is_empty fcx then f
        else Subst (fcx, f)
    end

  let place1 fr f = place (Deque.of_list [fr]) f

  let unframe fr f =
    mk fr.fconn (fr.fleft @ (f :: fr.fright))

  let head1 f =
    match f with
    | Subst (fcx, f) ->
        begin match Deque.front fcx with
        | Some (fr, fcx) -> unframe fr (place fcx f)
        | None -> assert false
        end
    | _ -> f

  let go_down ?(n = 0) f =
    begin match head1 f with
    | Atom _ -> raise Leaf
    | Conn (c, fs) ->
        let (lfs, f, rfs) = split3 n fs in
        let fr = {
          fconn = c ;
          fleft = lfs ;
          fright = rfs ;
        } in
        place1 fr f
    | Subst _ -> assert false
    end
        

  exception No_context

  let go_up f =
    begin match f with
    | Subst (fcx, f) ->
        begin match Deque.rear fcx with
        | Some (fcx, fr) ->
            Subst (fcx, unframe fr f)
        | None -> assert false
        end
    | _ -> raise No_context
    end

  exception At_edge

  let go_left f =
    begin match f with
    | Subst (fcx, f) ->
        begin match Deque.rear fcx with
        | Some (fcx, fr) ->
            begin match fr.fleft with
            | lf :: lfs ->
                let fr = { fr with
                  fleft = lfs ;
                  fright = f :: fr.fright ;
                } in
                let fcx = Deque.snoc fcx fr in
                Subst (fcx, lf)
            | [] -> raise At_edge
            end
        | None -> assert false
        end
    | _ -> raise No_context
    end

  let go_right f =
    begin match f with
    | Subst (fcx, f) ->
        begin match Deque.rear fcx with
        | Some (fcx, fr) ->
            begin match fr.fright with
            | rf :: rfs ->
                let fr = { fr with
                  fright = rfs ;
                  fleft = f :: fr.fleft ;
                } in
                let fcx = Deque.snoc fcx fr in
                Subst (fcx, rf)
            | [] -> raise At_edge
            end
        | None -> assert false
        end
    | _ -> raise No_context
    end

end

include Base
