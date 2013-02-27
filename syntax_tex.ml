(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Buffer
open Printf

open Syntax
open Traversal

module Tex = Syntax_fmt.Fmt (struct
  open Doc
  (* val i_var    : idt -> doc *)
  let i_var x = String (Idt.tex_rep x)
  (* val i_pred   : idt -> doc *)
  let i_pred x = String (Idt.tex_rep x)
  (* val i_con    : idt -> doc *)
  let i_con x = String ("\\mathsf{" ^ Idt.tex_rep x ^ "}")

  let op_eq = Group (NOBOX, [String " =" ; space 1])
  let op_neq = Group (NOBOX, [String " \\neq" ; space 1])

  (* val op_tens  : doc *)
  let op_tens = Group (NOBOX, [String " \\TENS" ; space 1])
  (* val op_one   : doc *)
  let op_one = String "\\ONE"
  (* val op_plus  : doc *)
  let op_plus = Group (NOBOX, [String " \\PLUS" ; space 1])
  (* val op_zero  : doc *)
  let op_zero = String "\\ZERO"
  (* val op_par   : doc *)
  let op_par = Group (NOBOX, [String " \\PAR" ; space 1])
  (* val op_top   : doc *)
  let op_top = String "\\TOP"
  (* val op_with  : doc *)
  let op_with = Group (NOBOX, [String " \\WITH" ; space 1])
  (* val op_bot   : doc *)
  let op_bot = String "\\BOT"
  (* val op_lto   : doc *)
  let op_lto = Group (NOBOX, [String " \\LTO" ; space 1])
  (* val op_bang  : doc *)
  let op_bang = String "\\BANG"
  (* val op_qm    : doc *)
  let op_qm = String "\\QM"
  (* val op_quant : quant -> doc *)
  let op_quant = function
    | All -> String "\\ALL"
    | Ex -> String "\\EX"

  (* val src_l    : doc *)
  let src_l = String "\\src{"
  (* val src_r    : doc *)
  let src_r = String "}"
  (* val snk_l    : doc *)
  let snk_l = String "\\snk{"
  (* val snk_r    : doc *)
  let snk_r = src_r
  (* val cur_l    : doc *)
  let cur_l = String "\\cur{"
  (* val cur_r    : doc *)
  let cur_r = src_r
end)


let max_hist = ref 3

let wash_command = ref ""

let set_dpi d =
  Log.(log INFO "Setting DPI to %d" d) ;
  if d < 75 || d > 240 then
    Log.(log WARN "Unusual DPI: %d" d) ;
  wash_command := Printf.sprintf
    "( cd tex  && latex '\\nonstopmode\\input wash_form.tex' && dvipng -D %d -T tight -bg transparent -z 9 wash_form.dvi ) %s" d
    (* "" *)
    ">/dev/null 2>&1"

let () = set_dpi 120

let pp_top cx buf f =
  let (fcx, f) = unsubst f in
  let f = mark ARG f in
  let f = go_top (subst fcx f) in
  let doc = Tex.fmt_form [] f in
  Doc.lin_doc_buffer buf doc

let wash_fut cx buf fut =
  let rec bounded_display n fut =
    begin match n, fut with
    | _, [] -> ()
    | 0, (_ :: _) ->
        add_string buf "\\\\\n$\\pmb\\vdots$"
    | n, ff :: fut ->
        bounded_display (n - 1) fut ;
        add_string buf "\\\\\n\\his{" ;
        pp_top cx buf ff ;
        add_string buf "}\n"
    end in
  bounded_display !max_hist fut

let wash_past cx buf past =
  let rec bounded_display n past =
    begin match n, past with
    | _, [] -> ()
    | 0, (_ :: _) ->
        add_string buf "$\\pmb\\vdots$\\\\\n"
    | n, pf :: past ->
        add_string buf "\\history{" ;
        pp_top cx buf pf ;
        add_string buf "}\\\\\n" ;
        bounded_display (n - 1) past ;
    end in
  bounded_display !max_hist past

let wash_forms ?(cx = []) (past, present, future) =
  let buf = Buffer.create 19 in
  wash_fut cx buf future ;
  add_string buf "\\present{" ;
  pp_top cx buf present ;
  add_string buf "}\n" ;
  wash_past cx buf past ;
  let ch = open_out "/tmp/profound-render.tex" in
  output_string ch (Buffer.contents buf) ;
  close_out ch ;
  if Sys.command !wash_command <> 0 then begin
    Log.(log FATAL "Cannot run LaTeX and/or dvipng successfully") ;
    exit 4 (* random exit code *)
  end
