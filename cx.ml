(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

module type S = sig
  type 'a cx

  val empty : 'a cx

  val front : 'a cx -> ('a * 'a cx) option
  val rear  : 'a cx -> ('a cx * 'a) option

  val cons  : 'a -> 'a cx -> 'a cx
  val snoc  : 'a cx -> 'a -> 'a cx

  val append : 'a cx -> 'a cx -> 'a cx

  val of_list : 'a list -> 'a cx
  val to_list : 'a cx -> 'a list

  val size  : 'a cx -> int
  val is_empty : 'a cx -> bool
end

module F : S = struct
  include (FingerTree : module type of FingerTree with type 'a t := 'a FingerTree.t)
  type 'a cx = 'a FingerTree.t
  let cons x sq = FingerTree.cons sq x
  let front sq =
    begin match FingerTree.front sq with
    | Some (sq, x) -> Some (x, sq)
    | None -> None
    end
end

module D : S = struct
  include (Deque : module type of Deque with type 'a t := 'a Deque.t)
  type 'a cx = 'a Deque.t
end

(* include F *)
include D

type 'a t = 'a cx
