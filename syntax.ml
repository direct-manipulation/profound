(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

module Dq = BatDeque
module List = BatList

type idt = Idt.t

module Base = struct

  type term =
    | Idx   of int
    | App   of idt * term list

  type spar = FLIP | SAME

  type conn = {
    cid : idt ;
    smap : spar list ;
  }

  type quant = {
    q : [`Forall | `Exits] ;
    hint : idt option ;
  }

  type form =
    | Atom  of idt * term list
    | Conn  of conn * form list
    | Quant of quant * form
    | Subst of fcx * form

  and fcx = frame Dq.t

  and frame =
    | CONN of conn * form list * form list
    | QUANT of quant

  exception Leaf
  exception Bad_index

  let rec split3 n xs =
    try begin match List.split_at n xs with
    | l, (u :: r) -> (l, u, r)
    | _ -> raise Bad_index
    end with _ -> raise Bad_index

  let place fcx f =
    if Dq.is_empty fcx then f else Subst (fcx, f)

  let unframe fr f =
    match fr with
    | CONN (c, lfs, rfs) -> Conn (c, lfs @ (f :: rfs))
    | QUANT q -> Quant (q, f)

  let head1 f =
    match f with
    | Subst (fcx, f) ->
        begin match Dq.front fcx with
        | Some (fr, fcx) -> unframe fr (place fcx f)
        | None -> assert false
        end
    | _ -> f

  let flip = function
    | SAME -> FLIP
    | FLIP -> SAME

  let rec sign_parity cur fcx =
    begin match Dq.front fcx with
    | None -> cur
    | Some (CONN (c, lfs, rfs), fcx) ->
        let cur =
          begin match List.nth c.smap (List.length lfs) with
          | SAME -> cur
          | FLIP -> flip cur
          end in
        sign_parity cur fcx
    | Some (QUANT _, fcx) ->
        sign_parity cur fcx
    end        

  let rec descend ~ns f k =
    begin match ns with
    | [] -> k Dq.empty f
    | n :: ns ->
        begin match head1 f with
        | Atom _ -> raise Leaf
        | Conn (c, fs) ->
            let (lfs, f, rfs) = split3 n fs in
            descend ~ns f begin
              fun fcx f -> k (Dq.cons (CONN (c, lfs, rfs)) fcx) f
            end
        | Quant (q, f) ->
            descend ~ns f begin
              fun fcx f -> k (Dq.cons (QUANT q) fcx) f
            end
        | Subst _ -> assert false
        end
    end
  let descend ?(ns = []) f = descend ~ns f (fun fcx f -> (fcx, f))

end

include Base
