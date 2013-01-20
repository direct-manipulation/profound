(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax
open Syntax_tex
open Traversal
open Rules

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
  let f0 = rule_int [0 ; 1 ; 1]  [0 ; 1 ; 0 ; 1] f0 |> push
  let f0 = resolve_mpar f0 |> push
  let f0 = rule_int [0 ; 0] [1 ; 1] f0 |> push
  let f0 = resolve_mpar f0 |> push
  let f0 = rule_int [1 ; 0] [1 ; 1 ; 0] f0 |> push
  let f0 = resolve_mpar f0 |> push

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

let _ = Syntax_tex.wash_forms !C.forms

