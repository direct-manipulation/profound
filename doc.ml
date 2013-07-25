(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Batteries
open Format

type box =
  | NOBOX
  | H | V of int | HV of int | HOV of int

type doc =
  | String of string
  | StringAs of int * string
  | Fmt of (formatter -> unit)
  | Break of int * int
  | Group of box * doc list
  | Newline

let space n = Break (n, 0)
let cut = Break (0, 0)

let string0 str =
  Fmt (fun ff -> pp_print_as ff 0 str)

let rec doc_map_strings fn = function
  | String s -> fn ~elen:(String.length s) s
  | StringAs (elen, s) -> fn ~elen s
  | Group (b, ds) -> Group (b, List.map (doc_map_strings fn) ds)
  | (Fmt _ | Break _ | Newline) as d -> d

let rec pp_doc ff = function
  | String s ->
      let fmt : (unit, formatter, unit) format = Obj.magic s in
      Format.fprintf ff fmt
  | StringAs (n, s) ->
      pp_print_as ff n s
  | Fmt fmt -> fmt ff
  | Break (nsp, offs) ->
      pp_print_break ff nsp offs
  | Group (b, ds) ->
      begin match b with
      | NOBOX -> ()
      | H -> pp_open_hbox ff ()
      | V ind -> pp_open_vbox ff ind
      | HV ind -> pp_open_hvbox ff ind
      | HOV ind -> pp_open_hovbox ff ind
      end ;
      List.iter (pp_doc ff) ds ;
      begin match b with
      | NOBOX -> ()
      | _ -> pp_close_box ff ()
      end
  | Newline ->
      pp_force_newline ff ()

let lin_doc_buffer buf d =
  let rec output = function
    | String s | StringAs (_, s) -> Buffer.add_string buf s
    | Fmt fmt -> Format.bprintf buf "%t" fmt
    | Group (_, ds) -> List.iter output ds
    | Break (0, _) -> ()
    | Break _ | Newline -> Buffer.add_char buf ' '
  in
  output d

let lin_doc d =
  let buf = Buffer.create 10 in
  lin_doc_buffer buf d ;
  Buffer.contents buf

type wrapping = Transparent | Opaque

type exp =
  | Atom of doc
  | Wrap of wrapping * doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp list

and assoc = Left | Right | Non

let rec ( >? ) prec be = match be with
  | Appl (subprec, _) when prec > subprec -> true
  | Wrap (Transparent, _, be, _) -> prec >? be
  | _ -> false

let rec ( >=? ) prec be = match be with
  | Appl (subprec, _) when prec >= subprec -> true
  | Wrap (Transparent, _, be, _) -> prec >=? be
  | _ -> false

let rec is_prefix = function
  | Appl (_, Prefix _) -> true
  | Wrap (Transparent, _, be, _) -> is_prefix be
  | _ -> false

let rec is_postfix = function
  | Appl (_, Postfix _) -> true
  | Wrap (Transparent, _, be, _) -> is_postfix be
  | _ -> false

let rec infix_incompat_for tasc pr asc = function
  | Appl (spr, (Prefix _ | Postfix _))
    when pr >= spr -> true
  | Appl (spr, Infix (_, sasc, _))
    when pr = spr && not (asc = tasc && sasc = tasc) -> true
  | Wrap (Transparent, _, be, _) ->
      infix_incompat_for tasc pr asc be
  | _ -> false

type dinfo = PRE of int | POST of int | NVM

let rec reprec e =
  begin match e with
  | Atom _ -> (e, NVM)
  | Appl (p, Infix (d, asc, es)) ->
      let es = List.map (fun e -> fst (reprec e)) es in
      (Appl (p, Infix (d, asc, es)), NVM)
  | Appl (p, Prefix (d, e)) ->
      begin
        let (e, di) = reprec e in
        let p = begin match di with
          | PRE q -> min p q
          | _ -> p
        end in
        (Appl (p, Prefix (d, e)), PRE p)
      end
  | Appl (p, Postfix (d, e)) ->
      begin
        let (e, di) = reprec e in
        let p = begin
          match di with
          | POST q -> min p q
          | _ -> p
        end in
        (Appl (p, Postfix (d, e)), POST p)
      end
  | Wrap (wt, b, e, a) ->
      let (e, di) = reprec e in
      let di = begin match wt with
        | Transparent -> di
        | Opaque -> NVM
      end in
      (Wrap (wt, b, e, a), di)
  end

let delimit ?(cond=true) ~ld ~rd d =
  if not cond then d else Group (H, [ld ; d ; rd])

let rec bracket ~ld ~rd = function
  | Atom d -> d
  | Wrap (_, ld1, be, rd1) ->
      delimit ~ld:ld1 ~rd:rd1 (bracket ~ld ~rd be)
  | Appl (prec, appl) -> begin
      match appl with
      | Prefix (oprep, be) ->
          let opd = bracket ~ld ~rd be in
          Group begin HOV 2, [
              oprep ;
              delimit opd ~ld ~rd
                ~cond:(prec >? be && not (is_prefix be)) ;
            ] end
      | Postfix (oprep, be) ->
          let opd = bracket ~ld ~rd be in
          Group begin H, [
              delimit opd ~ld ~rd
                ~cond:(prec >? be && not (is_postfix be)) ;
              oprep
            ] end
      | Infix (oprep, asc, l :: es) ->
          let (ms, r) = List.split_at (List.length es - 1) es in
          assert (r <> []) ;
          let r = List.hd r in
          let l = delimit (bracket ~ld ~rd l) ~ld ~rd
              ~cond:(prec >? l
                     || infix_incompat_for Left prec asc l) in
          let r = delimit (bracket ~ld ~rd r) ~ld ~rd
              ~cond:(prec >? r
                     || infix_incompat_for Right prec asc r) in
          let ms = List.map
              begin fun e ->
                [oprep ; delimit (bracket ~ld ~rd e) ~ld ~rd ~cond:(prec >=? e)]
              end ms in
          let ms = List.concat ms in
          Group (HOV 0, l :: ms @ [oprep ; r])
      | Infix (_, _, []) -> invalid_arg "bracket"
    end

let bracket ?(ld = String "(") ?(rd = String ")") e =
  let (e, _) = reprec e in
  bracket ~ld ~rd e
