(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

type idt = Idt.t

module Base = struct

  type term =
    | Idx   of int
    | App   of idt * term list

  type conn = {
    cid : idt ;
    smap : (int -> [`Same | `Flip]) ;
  }

  type form =
    | Atom  of idt * term list
    | Conn  of conn * form list
    | Quant of idt * form
    | Subst of ctx * form

  and ctx = frame list

  and frame =
    | CONN  of conn * form list * form list
    | QUANT of idt

  exception Leaf
  exception Bad_index

  let rec split_at xs n k =
    match xs, n with
    | [], _ -> raise Bad_index
    | x :: xs, 0 -> k ([], x, xs)
    | x :: xs, n ->
        split_at xs (n - 1) begin
          fun (l, u, r) -> k (x :: l, u, r)
        end
  let split_at xs n = split_at xs n (fun x -> x)

  let rec descend f ns k =
    match f, ns with
    | _, [] -> k ([], f)
    | Atom _, _
    | Subst _, _  -> raise Leaf
    | Conn (c, fs), (n :: ns) ->
        let lfs, f, rfs = split_at fs n in
        descend f ns begin
          fun (cx, f) ->
            k (CONN (c, lfs, rfs) :: cx, f)
        end
    | Quant (q, f), (n :: ns) ->
        descend f ns begin
          fun (cx, f) ->
            k (QUANT q :: cx, f)
        end
  let descend f ns = descend f ns (fun x -> x)

end

include Base
