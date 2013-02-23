(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type idt = {
  src : string ;
  tex : string ;
  salt : int ;
}

type t = idt

module WeakT = Weak.Make (
  struct
    type t = idt
    let hash : t -> int = Hashtbl.hash
    let equal : t -> t -> bool = Pervasives.(=)
  end
)

let _stab : WeakT.t = WeakT.create 19

let clear () = WeakT.clear _stab

let rec all_digits_spin n s =
  n = 0 || (Char.is_digit s.[n - 1] && all_digits_spin (n - 1) s)
let all_digits s = all_digits_spin (String.length s) s

let infer_salt s =
  begin match String.Exceptionless.rsplit ~by:"_" s with
  | Some (src, salt) when all_digits salt ->
      begin
        try (src, Int.of_string salt)
        with Failure _ -> (s, 0)
      end
  | _ -> (s, 0)
  end

let intern ?salt src =
  let (src, salt) =
    begin match salt with
    | None -> infer_salt src
    | Some salt ->
        assert (salt >= 0) ;
        (src, salt)
    end in
  let tex = String.nreplace ~str:src ~sub:"_" ~by:"\\_" in
  let i = { src ; tex ; salt } in
  WeakT.merge _stab i

let refresh i =
  let rec spin salt =
    let j = { i with salt } in
    if WeakT.mem _stab j
    then spin (salt + 1)
    else WeakT.merge _stab j
  in
  spin (i.salt + 1)

let src_rep i =
  if i.salt = 0 then i.src else
    i.src ^ "_" ^ string_of_int i.salt

let tex_rep i =
  if i.salt = 0 then i.tex else
    i.tex ^ "_{" ^ string_of_int i.salt ^ "}"
