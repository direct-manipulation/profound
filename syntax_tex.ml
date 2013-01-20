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

let add_idt buf i = add_string buf (Idt.rep i)

let rec pp_term cx buf t =
  begin match t with
  | Idx n ->
      add_idt buf (List.nth cx n)
  | App (f, []) ->
      add_idt buf f
  | App (f, ts) ->
      add_idt buf f ;
      add_string buf "(" ;
      pp_terms cx buf ts ;
      add_string buf ")"
  end

and pp_terms cx buf ts =
  begin match ts with
  | [t] ->
      pp_term cx buf t
  | t :: ts ->
      pp_term cx buf t ;
      add_string buf "," ;
      pp_terms cx buf ts
  | [] -> assert false
  end

let rec pp_form cx buf f =
  begin match f with
  | Atom (ASSERT, p, ts) ->
      begin match Idt.rep p, ts with
      | "=", [s ; t] ->
          pp_term cx buf s ;
          add_string buf " = " ;
          pp_term cx buf t
      | _ -> pp_term cx buf (App (p, ts))
      end
  | Atom (REFUTE, p, ts) ->
      begin match Idt.rep p, ts with
      | "=", [s ; t] ->
          pp_term cx buf s ;
          add_string buf " \\neq " ;
          pp_term cx buf t
      | _ -> 
          add_string buf "\\lnot " ;
          pp_term cx buf (App (p, ts)) ;
      end
  | Conn (Mark ARG, [f]) ->
      add_string buf "\\fbox{$" ;
      pp_form cx buf f ;
      add_string buf "$}"
  | Conn (Mark (SRC | SNK as dir), [f]) ->
      add_string buf "\\left[" ;
        (* bprintf buf "\\left[\\mathfrak{u}{%s}" *)
        (*   (match dir with SRC -> "\\uparrow" | _ -> "\\downarrow") ; *)
      pp_form cx buf f ;
      bprintf buf "\\right]^{\\smash{%s}}"
        (match dir with SRC -> "\\Uparrow" | _ -> "\\Downarrow")
  | Conn (p, [f ; g]) ->
      pp_bracket ~p cx buf f ;
      add_string buf (bin_string p) ;
      pp_bracket ~p cx buf g
  | Conn ((All x | Ex x) as p, [f]) ->
      add_string buf (un_string p) ;
      pp_bracket ~p (x :: cx) buf f
  | Conn (p, [f]) ->
      add_string buf (un_string p) ;
      pp_bracket ~p cx buf f ;
  | Conn (p, []) ->
      add_string buf (kon_string p)
  | Conn _ -> assert false
  | Subst (fcx, f) ->
      let f = conn (Mark ARG) [f] in
      let f = go_top (subst fcx f) in
      pp_form cx buf f
  end

and extend cx fcx =
  begin match Deque.front fcx with
  | Some ({ fconn = (ALL x | EX x) ; _}, fcx) ->
      extend (x :: cx) fcx
  | Some (_, fcx) ->
      extend cx fcx
  | None -> cx
  end

and pp_bracket ~p cx buf f =
  begin match head1 f with
  | Conn (Mark _, [_]) ->
      pp_form cx buf f
  | Conn (q, _) ->
      if p = q || (is_un p && is_un q) || prec p < prec q then
        pp_form cx buf f
      else begin
        add_string buf "\\left(" ;
        pp_form cx buf f ;
        add_string buf "\\right)"
      end
  | _ ->
      pp_form cx buf f
  end

and is_un = function
  | All _ | Ex _ | Bang | Qm -> true
  | _ -> false

and bin_string = function
  | Tens -> " \\TENS "
  | Plus -> " \\PLUS "
  | Par  -> " \\PAR "
  | With -> " \\WITH "
  | Mpar -> " \\MPAR "
  | _ -> assert false

and un_string = function
  | All x -> "\\ALL " ^ Idt.rep x ^ ". "
  | Ex x -> "\\EX " ^ Idt.rep x ^ ". "
  | Bang -> "\\BANG "
  | Qm -> "\\QM "
  | _ -> assert false

and kon_string = function
  | One -> "\\ONE"
  | Zero -> "\\ZERO"
  | Bot -> "\\BOT"
  | Top -> "\\TOP"
  | _ -> assert false

and prec = function
  | Mpar -> 1 (* 0 *)
  | Par -> 1
  | Plus -> 1 (* 2 *)
  | With -> 1 (* 3 *)
  | Tens -> 1 (* 4 *)
  | Ex _ | All _ -> 0
  | Bang | Qm -> 6
  | One | Zero | Top | Bot | Mark _ -> max_int

let wash_forms ?(cx = []) fs =
  let buf = Buffer.create 19 in
  add_string buf "{}" ;
  List.iter begin
    fun f ->
      pp_form cx buf f ;
      add_string buf "\\\\" ;
  end fs ;
  let ch = open_out "/tmp/profound-render.tex" in
  output_string ch (Buffer.contents buf) ;
  close_out ch ;
  Sys.command "( cd tex && rubber --into /tmp -d bar.tex && pdfcrop --margin 3 /tmp/bar.pdf /tmp/bar-c.pdf ) >/dev/null 2>&1"


