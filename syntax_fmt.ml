(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)


open Batteries
open Buffer
open Printf

open Syntax
open Traversal

type prec_enum =
  | PREC_MIN
  | PREC_QUANTIFIER
  | PREC_LTO
  | PREC_PAR
  | PREC_PLUS
  | PREC_WITH
  | PREC_TENS
  | PREC_EQ
  | PREC_MAX
external (!!) : prec_enum -> int = "%identity"

type fmt_error =
  | No_unit
  | Cannot_be_unary
  | Must_be_unary
let explain = function
  | No_unit -> "connective has no unit"
  | Cannot_be_unary -> "connective cannot be unary"
  | Must_be_unary -> "connective msut be unary"
exception Fmt_failure of fmt_error
let fmtfail err = raise (Fmt_failure err)


let rec monoid ~conn ?un ~prec ~assoc es =
  begin match es with
  | [] ->
      begin match un with
      | Some un -> Doc.Atom un
      | None -> fmtfail No_unit
      end
  | [_] ->
      fmtfail Cannot_be_unary
  | es -> Doc.(Appl (prec, Infix (conn, assoc, es)))
  end

module type SPEC = sig
  open Idt
  open Doc
  val i_var    : idt -> doc
  val i_pred   : idt -> doc
  val i_con    : idt -> doc

  val op_eq    : doc
  val op_neq   : doc

  val op_negate : doc

  val op_tens  : doc
  val op_one   : doc
  val op_plus  : doc
  val op_zero  : doc
  val op_par   : doc
  val op_top   : doc
  val op_with  : doc
  val op_bot   : doc
  val op_lto   : doc
  val op_bang  : doc
  val op_qm    : doc
  val op_quant : quant -> doc

  val src_l    : doc
  val src_r    : doc
  val snk_l    : doc
  val snk_r    : doc
  val cur_l    : doc
  val cur_r    : doc
end

module Fmt (Spec : SPEC) =
struct
  open Spec

  let rec comma_list_ lds rds =
    begin match rds with
    | [] -> List.rev lds
    | [d] -> List.rev (d :: lds)
    | d :: rds ->
        Doc.(comma_list_ (String "," :: space 1 :: d :: lds) rds)
    end

  let comma_list ds = comma_list_ [] ds

  let fmt_app f ts =
    begin match ts with
    | [] -> f
    | ts ->
        Doc.(Group begin HOV 1,
                         List.concat [ [f ; space 1 ; String "("]
                                     ; comma_list ts
                                     ; [String ")"] ]
             end)
    end

  let rec fmt_term cx t =
    begin match t with
    | Idx n ->
        begin match List.Exceptionless.at cx n with
        | `Ok idt -> i_var idt
        | _ -> Doc.String ("`" ^ string_of_int n)
        end
    | App (f, ts) ->
        fmt_app (i_con f) (List.map (fmt_term cx) ts)
    end

  let rec fmt_form cx f =
    begin match f with
    | Syntax.Atom (s, p, [t1 ; t2]) when p = Syntax.equals ->
        begin
          let t1 = fmt_term cx t1 in
          let t2 = fmt_term cx t2 in
          let op = begin
            match s with
            | ASSERT -> Spec.op_eq
            | _ -> Spec.op_neq
          end in
          Doc.(Appl (!!PREC_EQ, Infix (op, Left, [Atom t1 ; Atom t2])))
        end
    | Syntax.Atom (sign, p, ts) ->
        begin
          let p = i_pred p in
          let ts = List.map (fmt_term cx) ts in
          let pts = fmt_app p ts in
          match sign with
          | ASSERT -> Doc.Atom (pts)
          | REFUTE -> Doc.(Atom (Group (H, [Spec.op_negate ; pts])))
        end
    | Conn (Tens, fs) ->
        monoid (List.map (fmt_form cx) fs)
          ~conn:op_tens ~un:op_one
          ~prec:!!PREC_TENS ~assoc:Doc.Left
    | Conn (Plus, fs) ->
        monoid (List.map (fmt_form cx) fs)
          ~conn:op_plus ~un:op_zero
          ~prec:!!PREC_PLUS ~assoc:Doc.Left
    | Conn (Par, fs) ->
        monoid (List.map (fmt_form cx) fs)
          ~conn:op_par ~un:op_bot
          ~prec:!!PREC_PAR ~assoc:Doc.Left
    | Conn (With, fs) ->
        monoid (List.map (fmt_form cx) fs)
          ~conn:op_with ~un:op_top
          ~prec:!!PREC_WITH ~assoc:Doc.Left
    | Conn (Lto, fs) ->
        monoid (List.map (fmt_form cx) fs)
          ~conn:op_lto
          ~prec:!!PREC_LTO ~assoc:Doc.Right
    | Conn (Bang, [f]) ->
        Doc.(Appl (!!PREC_MAX, Prefix (op_bang, fmt_form cx f)))
    | Conn (Qm, [f]) ->
        Doc.(Appl (!!PREC_MAX, Prefix (op_qm, fmt_form cx f)))
    | Conn (Qu (q, x), [f]) ->
        let q = Doc.(Group (NOBOX, [
            op_quant q ; space 1 ;
            i_var x ; String "." ; space 1 ;
          ])) in
        Doc.(Appl (!!PREC_MIN, Prefix (q, fmt_form (x :: cx) f)))
    | Mark (m, f) ->
        let (ld, rd) =
          begin match m with
          | SRC -> (src_l, src_r)
          | SNK -> (snk_l, snk_r)
          | ARG -> (cur_l, cur_r)
          end in
        Doc.(Wrap (Opaque, ld, fmt_form cx f, rd))
    | Conn ((Bang | Qm | Qu _), _) ->
        fmtfail Must_be_unary
    | Subst (fcx, f) ->
        let f = mark ARG f in
        let f = go_top (subst fcx f) in
        fmt_form cx f
    end

  let fmt_form cx f = Doc.bracket (fmt_form cx f)

  let term_to_string cx t = Doc.lin_doc (fmt_term cx t)
  let form_to_string cx t = Doc.lin_doc (fmt_form cx t)

  let pp_term ?(cx = []) ff t = Doc.pp_doc ff (fmt_term cx t)
  let pp_form ?(cx = []) ff t = Doc.pp_doc ff (fmt_form cx t)

end


module Src = Fmt (struct
    open Doc
    (* val i_var    : idt -> doc *)
    let i_var x = String (Idt.src_rep x)
    (* val i_pred   : idt -> doc *)
    (* val i_con    : idt -> doc *)
    let i_pred = i_var
    let i_con = i_var

    let op_eq = Group (NOBOX, [String " =" ; space 1])
    let op_neq = Group (NOBOX, [String " <>" ; space 1])

    let op_negate = Group (NOBOX, [String "~" ; space 1])

    (* val op_tens  : doc *)
    let op_tens = Group (NOBOX, [String " *" ; space 1])
    (* val op_one   : doc *)
    let op_one = String "1"
    (* val op_plus  : doc *)
    let op_plus = Group (NOBOX, [String " +" ; space 1])
    (* val op_zero  : doc *)
    let op_zero = String "0"
    (* val op_par   : doc *)
    let op_par = Group (NOBOX, [String " |" ; space 1])
    (* val op_top   : doc *)
    let op_top = String "#T"
    (* val op_with  : doc *)
    let op_with = Group (NOBOX, [String " &" ; space 1])
    (* val op_bot   : doc *)
    let op_bot = String "#F"
    (* val op_lto   : doc *)
    let op_lto = Group (NOBOX, [String " -o" ; space 1])
    (* val op_bang  : doc *)
    let op_bang = String "!"
    (* val op_qm    : doc *)
    let op_qm = String "?"
    (* val op_quant : quant -> doc *)
    let op_quant = function
      | All -> String "\\A"
      | Ex -> String "\\E"

    (* val src_l    : doc *)
    let src_l = Group (NOBOX, [String "{src:" ; space 1])
    (* val src_r    : doc *)
    let src_r = String "}"
    (* val snk_l    : doc *)
    let snk_l = Group (NOBOX, [String "{snk:" ; space 1])
    (* val snk_r    : doc *)
    let snk_r = src_r
    (* val cur_l    : doc *)
    let cur_l = String "{"
    (* val cur_r    : doc *)
    let cur_r = src_r
  end)
