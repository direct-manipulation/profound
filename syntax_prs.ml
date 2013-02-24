(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax
open Result

let rec index_term cx = function
  | Idx n -> Idx n
  | App (c, []) ->
      begin match index_find cx c with
      | None -> App (c, [])
      | Some n -> Idx n
      end
  | App (f, ts) ->
      App (f, List.map (index_term cx) ts)

and index_find ?(dep = 0) cx c =
  begin match cx with
  | [] -> None
  | x :: _ when c = x -> Some dep
  | _ :: cx -> index_find ~dep:(dep + 1) cx c
  end

let rec index_form cx f =
  begin match f with
  | Syntax.Atom (s, p, ts) ->
      atom s p (List.map (index_term cx) ts)
  | Conn ((All x | Ex x) as q, fs) ->
      let fs = List.map (index_form (x :: cx)) fs in
      conn q fs
  | Conn (c, fs) ->
      conn c (List.map (index_form cx) fs)
  | Subst _ -> assert false
  end


let parse_thing prs ind cx str =
  let lb = Lexing.from_string str in
  let token lb =
    Log.(log DEBUG "Trying to read a token...") ;
    let res = Form_l.token lb in
    Log.(log DEBUG "Read another token!") ;
    res in
  try
    let t = prs token lb in
    Ok (ind cx t)
  with Form_p.Error -> Bad "reading term"

let parse_form cx str = parse_thing Form_p.one_form index_form cx str
let parse_term cx str = parse_thing Form_p.one_term index_term cx str
