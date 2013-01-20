(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Log

open Syntax
open Traversal

let is_qm fcx f =
  begin match Deque.front fcx with
  | Some ({fconn = QM ; _}, _) -> true
  | Some _ -> false
  | None ->
      begin match f with
      | Conn (Qm, _) -> true
      | _ -> false
      end
  end

let rec bang_free fcx =
  begin match Deque.front fcx with
  | None -> true
  | Some ({fconn = BANG ; _}, _) -> false
  | Some (_, fcx) -> bang_free fcx
  end

exception Stuck

let rec equate ts1 ts2 =
  begin match ts1, ts2 with
  | [], [] -> conn One []
  | [t1], [t2] ->
      atom ASSERT (Idt.intern "=") [t1 ; t2]
  | (t1 :: ts1), (t2 :: ts2) ->
      conn Tens [ atom ASSERT (Idt.intern "=") [t1 ; t2]
                ; equate ts1 ts2 ]
  | _ ->
      conn Bot []
  end

let freshen =
  let last = ref 0 in
  fun x ->
    incr last ;
    Idt.intern (Idt.rep x ^ "_{" ^ string_of_int !last ^ "}")

let rec reduce_choices fcx f =
  begin match Deque.front fcx with
  | None -> (fcx, f)
  | Some ({fconn = PLUS ; _}, fcx) ->
      reduce_choices fcx f
  | Some ({fconn = (ALL _ | EX _) ; _} as fr, fcx) ->
      let (fcx, f) = reduce_choices fcx f in
      if free_fcx 0 fcx f then
        (Deque.cons fr fcx, f)
      else
        let ss = Dot (Shift 0, Idx min_int) in
        let (fcx, ss) = sub_fcx ss fcx in
        let f = sub_form ss f in
        (fcx, f)
  | Some (fr, fcx) ->
      let (fcx, f) = reduce_choices fcx f in
      (Deque.cons fr fcx, f)
  end

let main_arg f =
  begin match f with
  | Subst (_, f) -> f
  | _ -> f
  end

exception Found of form

let find_form pred f0 =
  let rec find_loop f0 =
    let (fcx, f) = unsubst f0 in
    if pred f then raise (Found f0) else
      begin match f with
      | Conn (_, fs) ->
          for i = 0 to List.length fs - 1 do
            find_loop (go_down i f0)
          done
      | Atom _ -> ()
      | Subst _ -> assert false
      end
  in
  try find_loop f0 ; raise Not_found with
  | Found f -> f

let find_lnk f =
  let f = find_form (function Conn (Mark (SRC | SNK), _) -> true | _ -> false) f in
  unsubst f

let has_lnk f =
  try ignore (find_lnk f) ; true with Not_found -> false

let is_mpar f =
  begin match f with
  | Conn (Par, [f ; g]) ->
      has_lnk f && has_lnk g
  | _ -> false
  end

let find_mpar f =
  let f = find_form is_mpar f in
  let (fcx, f) = unsubst f in
  begin match f with
  | Conn (Par, [f ; g]) -> (fcx, f, g)
  | _ -> assert false
  end

let link_normal_form f =
  let (fcx0, f, g) = find_mpar f in
  let (fcx1, f) = find_lnk f in
  let (fcx2, g) = find_lnk g in
  subst fcx0 (conn Mpar [subst fcx1 f ; subst fcx2 g])

exception Already_marked

let make_lnk dir f =
  let (fcx, f) = unsubst f in
  assert (try ignore (find_lnk f) ; false with Not_found -> true) ;
  begin match f with
  | Conn (Mark (SRC | SNK), _) -> raise Already_marked
  | _ ->
      let f = conn (Mark dir) [f] in
      subst fcx f
  end

let unlnk f =
  begin match f with
  | Conn (Mark (SRC | SNK), [f]) -> f
  | _ -> assert false
  end

let is_src f =
  begin match f with
  | Conn (Mark SRC, _) -> true
  | Conn (Mark SNK, _) -> false
  | _ -> assert false
  end

let rec resolve_mpar fcx1 f1 fcx2 f2 =
  begin match Deque.front fcx1, Deque.front fcx2 with
  | None, None ->
      let f1 = unlnk f1 in
      let f2 = unlnk f2 in
      begin match f1, f2 with
      | Atom (s1, p1, ts1), Atom (s2, p2, ts2)
        when s1 <> s2 && p1 = p2 ->
          equate ts1 ts2
      | _ ->
          conn Par [f1 ; f2]
      end
  (* negative cases *)
  | Some ({fconn = PAR ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = PAR ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = WITH ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      let u2 = go_top (subst fcx2 (unlnk f2)) in
      let dist f = conn Par [f ; u2] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | _, Some ({fconn = WITH ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      let u1 = go_top (subst fcx1 (unlnk f1)) in
      let dist f = conn Par [u1 ; f] in
      let fr = { fr with
        fleft = List.map dist fr.fleft ;
        fright = List.map dist fr.fright ;
      } in
      unframe fr f0
  | Some ({fconn = ALL x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = ALL (freshen x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = ALL x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = ALL (freshen x) } in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = QM ; _}, fcx1), _ when bang_free fcx2 ->
      resolve_mpar fcx1 f1 fcx2 f2
  | _, Some ({fconn = QM ; _}, fcx2) when bang_free fcx1 ->
      resolve_mpar fcx1 f1 fcx2 f2
  (* positive cases *)
  | Some ({fconn = TENS ; _} as fr, fcx1), _ ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = TENS ; _} as fr, fcx2) ->
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = PLUS ; _}, fcx1), _ ->
      resolve_mpar fcx1 f1 fcx2 f2
  | _, Some ({fconn = PLUS ; _}, fcx2) ->
      resolve_mpar fcx1 f1 fcx2 f2
  | Some ({fconn = EX x1 ; _} as fr1, fcx1d),
    Some ({fconn = EX x2 ; _} as fr2, fcx2d) ->
      if is_src f1 then begin
        let fr2 = { fr2 with fconn = EX (freshen x2) } in
        let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
        let f1 = sub_form ss f1 in
        let f0 = resolve_mpar fcx1 f1 fcx2d f2 in
        unframe fr2 f0
      end else begin
        let fr1 = { fr1 with fconn = EX (freshen x1) } in
        let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
        let f2 = sub_form ss f2 in
        let f0 = resolve_mpar fcx1d f1 fcx2 f2 in
        unframe fr1 f0
      end
  | Some ({fconn = EX x ; _} as fr, fcx1), _ ->
      let fr = { fr with fconn = EX (freshen x) } in
      let (fcx2, ss) = sub_fcx (Shift 1) fcx2 in
      let f2 = sub_form ss f2 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = EX x ; _} as fr, fcx2) ->
      let fr = { fr with fconn = EX (freshen x) } in
      let (fcx1, ss) = sub_fcx (Shift 1) fcx1 in
      let f1 = sub_form ss f1 in
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | Some ({fconn = BANG ; _} as fr, fcx1), _ ->
      if not (is_qm fcx2 f2) then raise Stuck ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  | _, Some ({fconn = BANG ; _} as fr, fcx2) ->
      if not (is_qm fcx1 f1) then raise Stuck ;
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      unframe fr f0
  (* The following are supposedly unreachable states *)
  (* They are just present to silence the exhaustiveness checker *)
  | Some ({fconn = QM ; _}, _), _
  | _, Some ({fconn = QM ; _}, _) ->
      raise Stuck
  end
let resolve_mpar_internal = resolve_mpar

let resolve_mpar f =
  let f = link_normal_form (go_top f) in
  let (fcx, f) = unsubst f in
  begin match f with
  | Conn (Mpar, [f1 ; f2]) ->
      let (fcx1, f1) = unsubst f1 in
      (* let (fcx1, f1) = reduce_choices fcx1 f1 in *)
      let (fcx2, f2) = unsubst f2 in
      (* let (fcx2, f2) = reduce_choices fcx2 f2 in *)
      let f0 = resolve_mpar fcx1 f1 fcx2 f2 in
      go_top (subst fcx f0)
  | _ -> assert false
  end

exception Rule_int of form

let rule_int tr1 tr2 f =
  let f = make_lnk SRC (descend tr1 f) in
  let f = go_top f in
  let f = make_lnk SNK (descend tr2 f) in
  let f = go_top f in
  f

module Pp = struct
  open Buffer
  open Printf

  let add_idt buf i = add_string buf (Idt.rep i)

  let salt =
    let last = ref 0 in
    fun x -> incr last ; Idt.intern (Idt.rep x ^ string_of_int !last)

  let rec adj cx x =
    if List.mem x cx then
      adj cx (salt x)
    else
      (x :: cx, x)

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
    let ch = open_out "/tmp/foo.tex" in
    output_string ch (Buffer.contents buf) ;
    close_out ch ;
    Sys.command "( cd /tmp && pdflatex bar.tex && pdfcrop --margin 3 bar.pdf bar-c.pdf ) >/dev/null 2>&1"
end
        


module C : sig val forms : form list ref end = struct

  open Idt

  let idx n = Idx n
  let app f ts = App (intern f, ts)

  let negate_sign = function
    | ASSERT -> REFUTE
    | REFUTE -> ASSERT

  let dual_conn = function
    | Tens -> Par | One -> Bot
    | Plus -> With | Zero -> Top
    | Par -> Tens | Bot -> One
    | With -> Plus | Top -> Zero
    | All x -> Ex x | Ex x -> All x
    | Bang -> Qm | Qm -> Bang
    | Mpar | Mark _ -> invalid_arg "dual: found MPAR or MARK"

  let rec dual f =
    begin match f with
    | Conn (c, fs) ->
        conn (dual_conn c) (List.map dual fs)
    | Atom (s, p, ts) ->
        atom (negate_sign s) p ts
    | Subst (fcx, f) ->
        subst (dual_fcx fcx) (dual f)
    end

  and dual_fcx fcx =
    Deque.map dual_frame fcx

  and dual_frame fr = {
    fconn = fconn_of_conn (dual_conn (conn_of_fconn fr.fconn)) ;
    fleft = List.map dual fr.fleft ;
    fright = List.map dual fr.fright ;
  }

  let tens     = conn Tens
  let one      = conn One []
  let plus     = conn Plus
  let zero     = conn Zero []
  let par      = conn Par
  let bot      = conn Bot []
  let wth      = conn With
  let top      = conn Top []
  let all x f  = conn (All (intern x)) [f]
  let ex x f   = conn (Ex (intern x)) [f]
  let bang f   = conn Bang [f]
  let qm f     = conn Qm [f]
  let mpar f g = conn Mpar [f; g]

  let natm p ts = atom REFUTE (intern p) ts
  let atom p ts = atom ASSERT (intern p) ts

  let a  = atom "a" []
  let a' = natm "a" []
  let b  = atom "b" []
  let b' = natm "b" []
  let c  = atom "c" []
  let c' = natm "c" []
  let d  = atom "d" []
  let d' = natm "d" []

  let forms = ref []
  let push f = forms := f :: !forms ; f
  let ( |> ) x f = f x

  (*
    let f0 = par [qm a' ; bang (bang a)] |> push
    let i0 = rule_int [0 ; 0] [1; 0 ; 0] f0 |> push
    let r0 = go_top (resolve_mpar i0) |> push
  *)


  let f0 = par [tens [a ; b] ;
                par [wth [a' ; b'] ;
                     plus [a' ; b']]] |> push
  let f0 = rule_int [0 ; 0] [1 ; 0 ; 0] f0 |> push
  let f0 = resolve_mpar f0 |> push
  (* let f0 = rule_int [0 ; 1 ; 1]  [0 ; 1 ; 0 ; 1] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)
  (* let f0 = rule_int [0 ; 0] [1 ; 1] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)
  (* let f0 = rule_int [1 ; 0] [1 ; 1 ; 0] f0 |> push *)
  (* let f0 = resolve_mpar f0 |> push *)

  (* let f0 = par [ex "x" (all "y" (plus [natm "p" [idx 1] ; *)
  (*                                      atom "p" [idx 0]])) ; *)
  (*               ex "x" (all "y" (ex "z" (plus [natm "p" [idx 2] ; *)
  (*                                      atom "p" [idx 1]])))] |> push *)
  (* let f0 = make_lnk SRC (descend [0 ; 0 ; 0 ; 0] f0) *)
  (* let f0 = go_top f0 *)
  (* let f0 = make_lnk SNK (descend [1 ; 0 ; 0 ; 0 ; 1] f0) *)
  (* let f0 = go_top f0 |> push *)
  (* let r0 = resolve_mpar f0 |> push *)

end

let _ = Pp.wash_forms !C.forms

