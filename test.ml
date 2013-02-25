open Batteries

open Syntax
open Syntax_tex
open Traversal
open Rules

open Idt

(* let rec lowest_qm f r = *)
(*   begin match Cx.rear f with *)
(*   | Some (f, ({fconn = QM ; _} as fr)) -> (f, Cx.cons fr r) *)
(*   | Some (f, fr) -> lowest_qm f (Cx.cons fr r) *)
(*   | None -> failwith "lowest_qm" *)
(*   end *)

(* let unravel gcx fcx1 f1 fcx2 f2 = *)
(*   begin match Cx.rear gcx with *)
(*   | Some (gcx, fr) -> *)
(*       let fr1 = {fr with fright = subst fcx2 (unlnk f2) :: fr.fright} in *)
(*       let fr2 = {fr with fleft = subst fcx1 (unlnk f1) :: fr.fleft} in *)
(*       let fcx1 = Cx.cons fr1 fcx1 in *)
(*       let fcx2 = Cx.cons fr2 fcx2 in *)
(*       (Cx.append gcx fcx1, Cx.append gcx fcx2) *)
(*   | None -> failwith "unravel" *)
(*   end *)

(* let maybe_contract fcx0 fcx1 f1 fcx2 f2 = *)
(*   begin match Cx.rear fcx0 with *)
(*   | Some (_, {fconn = PAR ; _}) -> *)
(*       (fcx0, fcx1, f1, fcx2, f2) *)
(*   | _ -> *)
(*       let (fcx0, gcx) = lowest_qm fcx0 Cx.empty in *)
(*       let fcx0 = Cx.snoc fcx0 { fconn = PAR ; fleft = [] ; fright = [] } in *)
(*       let (fcx1, fcx2) = unravel gcx fcx1 f1 fcx2 f2 in *)
(*       (fcx0, fcx1, f1, fcx2, f2) *)
(*   end *)

let f0 =
  begin match Syntax_io.form_of_string [] "a | ?(b + c) | d" with
  | Ok f -> f
  | Bad msg -> failwith msg
  end

(* let f1 = go_top (make_lnk SRC (descend [1 ; 0 ; 0] f0)) *)
(* let f2 = go_top (make_lnk SNK (descend [1 ; 0 ; 1] f1)) *)
(* let (gcx0, g1) = Option.get (find_marked f2) *)
(* let (gcx0, gcx1, g1, gcx2, g2) = Option.get (find_fcx_mate gcx0 Cx.empty g1) *)

(* let (hcx0, hcx1, h1, hcx2, h2) = maybe_contract gcx0 gcx1 g1 gcx2 g2 *)

(* let th0 = [ *)
(*   "gcx0", Cx.to_list gcx0 ; *)
(*   "gcx1", Cx.to_list gcx1 ; *)
(*   "gcx2", Cx.to_list gcx2 ; *)
(*   "hcx0", Cx.to_list hcx0 ; *)
(*   "hcx1", Cx.to_list hcx1 ; *)
(*   "hcx2", Cx.to_list hcx2 ; *)
(* ] *)
(* let th1 = [ *)
(*   "h1", go_top (subst hcx1 h1) ; *)
(*   "h2", go_top (subst hcx2 h2) ; *)
(* ] *)
