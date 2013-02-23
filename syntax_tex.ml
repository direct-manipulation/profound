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

let add_idt buf i = add_string buf (Idt.tex_rep i)

let add_fun kon buf f =
  if kon then add_string buf "\\mathsf{" ;
  add_idt buf f ;
  if kon then add_string buf "}"

let rec pp_term ?(kon = true) cx buf t =
  begin match t with
  | Idx n ->
      add_idt buf (List.nth cx n)
  | App (f, []) ->
      add_fun kon buf f
  | App (f, ts) ->
      add_fun kon buf f ;
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
      begin match p.Idt.src, ts with
      | "=", [s ; t] ->
          pp_term cx buf s ;
          add_string buf " = " ;
          pp_term cx buf t
      | _ -> pp_term ~kon:false cx buf (App (p, ts))
      end
  | Atom (REFUTE, p, ts) ->
      begin match p.Idt.src, ts with
      | "=", [s ; t] ->
          pp_term cx buf s ;
          add_string buf " \\neq " ;
          pp_term cx buf t
      | _ -> 
          add_string buf "\\lnot " ;
          pp_term ~kon:false cx buf (App (p, ts)) ;
      end
  | Conn (Mark ARG, [f]) ->
      add_string buf "\\hl{\\left\\{" ;
      pp_form cx buf f ;
      add_string buf "\\right\\}}"
  | Conn (Mark (SRC | SNK as dir), [f]) ->
      bprintf buf "{\\color{%s}"
        (match dir with SRC -> "src" | _ -> "dst") ;
      pp_form cx buf f ;
      add_string buf "}"
  | Conn (p, []) ->
      add_string buf (kon_string p)
  | Conn ((All x | Ex x) as p, [f]) ->
      add_un buf p ;
      pp_check_bracket ~p (x :: cx) buf f
  | Conn (p, [f]) ->
      add_un buf p ;
      pp_check_bracket ~p cx buf f ;
  | Conn (p, f :: gs) ->
      pp_check_bracket ~p cx buf f ;
      List.iter begin
        fun g ->
          add_string buf (bin_string p) ;
          pp_check_bracket ~p cx buf g
      end gs
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

and needs_bracket p f =
  begin match head1 f with
  | Conn (Mark _, _)
  | Atom _
  | Conn ((Tens | Plus | With | Par), []) -> false
  | Conn (q, _) ->
      not (p = q || (is_un p && is_un q) || prec p < prec q)
  | Subst _ -> assert false
  end

and pp_check_bracket ~p cx buf f =
  begin match head1 f with
  | Conn (Mark _, [fb]) ->
      if needs_bracket p fb
      then pp_bracket cx buf f
      else pp_form cx buf f
  | f ->
      if needs_bracket p f
      then pp_bracket cx buf f
      else pp_form cx buf f
  end

and pp_bracket cx buf f =
  add_string buf "\\left(" ;
  pp_form cx buf f ;
  add_string buf "\\right)"

and is_un = function
  | All _ | Ex _ | Bang | Qm -> true
  | _ -> false

and bin_string = function
  | Tens -> " \\TENS "
  | Plus -> " \\PLUS "
  | Par  -> " \\PAR "
  | With -> " \\WITH "
  | _ -> assert false

and add_un buf = function
  | All x ->
      add_string buf "\\ALL " ;
      add_idt buf x ;
      add_string buf ". "
  | Ex x ->
      add_string buf "\\EX " ;
      add_idt buf x ;
      add_string buf ". "
  | Bang -> add_string buf "\\BANG "
  | Qm -> add_string buf "\\QM "
  | _ -> assert false

and kon_string = function
  | Tens -> "\\ONE"
  | Plus -> "\\ZERO"
  | Par -> "\\BOT"
  | With -> "\\TOP"
  | _ -> assert false

and prec = function
  | Par -> 1
  | Plus -> 1 (* 2 *)
  | With -> 1 (* 3 *)
  | Tens -> 1 (* 4 *)
  | Ex _ | All _ -> 0
  | Bang | Qm -> 6
  | Mark _ -> max_int

let wash_command = ref ""

let set_dpi d =
  Log.(log INFO "Setting DPI to %d" d) ;
  if d < 75 || d > 240 then
    Log.(log WARN "Unusual DPI: %d" d) ;
  wash_command := Printf.sprintf
    "( cd tex  && latex '\\nonstopmode\\input wash_form.tex' && dvipng -D %d -T tight -bg transparent -z 9 wash_form.dvi ) %s"
    d ">/dev/null 2>&1"

let () = set_dpi 120

let wash_forms ?(cx = []) cur his =
  let buf = Buffer.create 19 in
  add_string buf "\\cur{" ;
  pp_form cx buf cur ;
  add_string buf "}\n" ;
  List.iter begin
    fun f ->
      add_string buf "\\his{" ;
      pp_form cx buf f ;
      add_string buf "}\n" ;
  end his ;
  let ch = open_out "/tmp/profound-render.tex" in
  output_string ch (Buffer.contents buf) ;
  close_out ch ;
  if Sys.command !wash_command <> 0 then begin
    Log.(log FATAL "Cannot run LaTeX and/or dvipng successfully") ;
    exit 4 (* random exit code *)
  end

