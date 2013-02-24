(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

type idt = Idt.t

let equals = Idt.intern "="

type term =
  | Idx   of int
  | App   of idt * term list

type sign = ASSERT | REFUTE

type form =
  | Atom  of sign * idt * term list
  | Conn  of conn * form list
  | Subst of fcx * form

and fcx = frame Cx.t

and frame = {
  fconn  : fconn ;
  fleft  : form list ;
  fright : form list ;
}

and quant = All | Ex

and conn =
  | Tens | Plus | Par | With
  | Qu of quant * idt
  | Bang | Qm
  | Mark of mkind

and fconn = 
  | TENS | PLUS | PAR | WITH
  | QU of quant * idt
  | BANG | QM

and mkind =
  | ARG | SRC | SNK

type test = dep:int -> term -> bool

let rec test_term_ dep test t =
  test ~dep t ||
  begin match t with
  | Idx _ -> false
  | App (_, ts) -> List.exists (test_term_ dep test) ts
  end

and test_form_ dep test f =
  begin match f with
  | Atom (_, _, ts) ->
      List.exists (test_term_ dep test) ts
  | Conn (Qu _, fs) ->
      List.exists (test_form_ (dep + 1) test) fs
  | Conn (c, fs) ->
      List.exists (test_form_ dep test) fs
  | Subst (fcx, f) ->
      test_fcx_ dep test fcx f
  end

and test_fcx_ dep test fcx f =
  begin match Cx.front fcx with
  | None -> test_form_ dep test f
  | Some ({fconn = QU _ ; _}, fcx) ->
      test_fcx_ (dep + 1) test fcx f
  | Some (fr, fcx) ->
      List.exists (test_form_ dep test) fr.fleft
      || List.exists (test_form_ dep test) fr.fright
      || test_fcx_ dep test fcx f
  end

let test_term test t = test_term_ 0 test t
let test_form test f = test_form_ 0 test f
let test_fcx test fcx f = test_fcx_ 0 test fcx f

let atom s p ts = Atom (s, p, ts)

let subst fcx f =
  begin match f with
  | Subst (fcx1, f) ->
      Subst (Cx.append fcx fcx1, f)
  | _ ->
      if Cx.is_empty fcx then f
      else Subst (fcx, f)
  end


let _One  = Conn (Tens, [])
let _Zero = Conn (Plus, [])
let _Bot  = Conn (Par, [])
let _Top  = Conn (With, [])

exception No_spec

let monoid_normalize ?spec c un f g =
  if f = un then g
  else if g = un then f
  else begin match f, g with
  | Conn (c1, fs), Conn (c2, gs) when c1 = c && c2 = c ->
      Conn (c, fs @ gs)
  | Conn (c1, fs), _ when c1 = c ->
      Conn (c, fs @ [g])
  | f, Conn (c2, gs) when c2 = c ->
      Conn (c, f :: gs)
  | _ ->
      begin match spec with
      | Some spec ->
          (try spec f g with No_spec -> Conn (c, [f ; g]))
      | None -> Conn (c, [f ; g])
      end
  end

let rec _Tens f g = monoid_normalize Tens _One f g

and _Plus f g = monoid_normalize ~spec:_Plus_spec Plus _Zero f g
and _Plus_spec f g =
  begin match f, g with
  | Conn (Tens, []), Conn (Tens, []) -> _One
  | _ -> raise No_spec
  end

and _Par f g = monoid_normalize ~spec:_Par_spec Par _Bot f g
and _Par_spec f g =
  begin match f, g with
  | Conn (With, []), f
  | f, Conn (With, []) -> _Top
  | _ -> raise No_spec
  end

and _With f g = monoid_normalize ~spec:_With_spec With _Top f g
and _With_spec f g =
  begin match f, g with
  | Conn (Tens, []), Conn (Tens, []) -> _One
  | _ -> raise No_spec
  end

let _Bang f =
  begin match f with
  | Conn (Tens, [])
  | Conn (With, []) ->
      _One
  | _ ->
      Conn (Bang, [f])
  end

let _Qm f =
  begin match f with
  | Conn (Par, [])
  | Conn (Plus, []) ->
      _Bot
  | _ ->
      Conn (Qm, [f])
  end

let fresh_for x f =
  let test ~dep t =
    begin match t with
    | App (f, _) -> f = x
    | _ -> false
    end in
  if test_form test f then
    (Idt.refresh x, f)
  else
    (x, f)

let _Q q x f =
  begin match f with
  | Conn (Tens, []) -> _One
  | f ->
      begin
        let x =
          if test_form (fun ~dep -> function App (f, _) -> f = x | _ -> false) f
          then Idt.refresh x
          else x in
        Conn (Qu (q, x), [f])
      end
  end

let _All x f = _Q All x f
let _Ex x f = _Q Ex x f

let _Mark m f = Conn (Mark m, [f])

let mk_un fn fs =
  begin match fs with
  | [f] -> fn f
  | _ -> assert false
  end

let conn c =
  begin match c with
  | Tens      -> List.fold_left _Tens _One
  | Plus      -> List.fold_left _Plus _Zero
  | Par       -> List.fold_left _Par  _Bot
  | With      -> List.fold_left _With _Top
  | Bang      -> mk_un _Bang
  | Qm        -> mk_un _Qm
  | Qu (q, x) -> mk_un (_Q q x)
  | Mark m    -> mk_un (_Mark m)
  end

type sub =
  | Shift of int
  | Dot of sub * term

let rec sub_idx ss n =
  begin match ss with
  | Shift j -> Idx (j + n)
  | Dot (_, t) when n = 0 -> t
  | Dot (ss, _) -> sub_idx ss (n - 1)
  end

and sub_term ss t =
  begin match t with
  | Idx n -> sub_idx ss n
  | App (f, ts) -> App (f, List.map (sub_term ss) ts)
  end

and sub_form ss f =
  begin match f with
  | Atom (s, p, [t1 ; t2]) when p = equals ->
      let t1 = sub_term ss t1 in
      let t2 = sub_term ss t2 in
      if t1 = t2 then
        if s = ASSERT then _One else _Bot
      else atom s p [t1 ; t2]
  | Atom (s, p, ts) ->
      atom s p (List.map (sub_term ss) ts)
  | Conn (Qu (q, x), [f]) ->
      _Q q x (sub_form (bump ss) f)
  | Conn (Qu _, _) -> assert false
  | Conn (c, fs) ->
      conn c (List.map (sub_form ss) fs)
  | Subst (fcx, f) ->
      let (fcx, ss) = sub_fcx ss fcx in
      subst fcx (sub_form ss f)
  end

and sub_fcx ss fcx =
  begin match Cx.front fcx with
  | Some ({ fconn = QU _ ; _ } as fr, fcx) ->
      let (fcx, ss) = sub_fcx (bump ss) fcx in
      (Cx.cons fr fcx, ss)
  | Some (fr, fcx) ->
      let fr = { fr with
        fleft = List.map (sub_form ss) fr.fleft ;
        fright = List.map (sub_form ss) fr.fright ;
      } in
      let (fcx, ss) = sub_fcx ss fcx in
      (Cx.cons fr fcx, ss)
  | None ->
      (Cx.empty, ss)
  end

and bump ss = Dot (seq (Shift 1) ss, Idx 0)

and seq ss tt =
  begin match ss, tt with
  | Shift j, Shift k -> Shift (j + k)
  | ss, Shift 0 -> ss
  | Shift 0, tt -> tt
  | Dot (ss, _), Shift j ->
      seq ss (Shift (j - 1))
  | _, Dot (tt, t) ->
      Dot (seq ss tt, sub_term ss t)
  end

let rec fcx_vars fcx =
  begin match Cx.rear fcx with
  | Some (fcx, {fconn = QU (_, x) ; _}) ->
      x :: fcx_vars fcx
  | Some (fcx, _) ->
      fcx_vars fcx
  | None ->
      []
  end

let fconn_of_conn = function
  | Tens -> TENS | Plus -> PLUS
  | Par -> PAR | With -> WITH
  | Qu (q, x) -> QU (q, x)
  | Bang -> BANG | Qm -> QM
  | _ -> invalid_arg "fconn_of_conn"

let conn_of_fconn = function
  | TENS -> Tens | PLUS -> Plus
  | PAR -> Par | WITH -> With
  | QU (q, x) -> Qu (q, x)
  | BANG -> Bang | QM -> Qm

let fconn fc = conn (conn_of_fconn fc)

let subst1 fr f = subst (Cx.of_list [fr]) f

let rec unsubst f =
  begin match f with
  | Subst (fcx, f) -> (fcx, f)
  | _ -> (Cx.empty, f)
  end

let unframe fr f =
  fconn fr.fconn (List.rev_append fr.fleft (f :: fr.fright))

let head1 f =
  match f with
  | Subst (fcx, f) ->
      begin match Cx.front fcx with
      | Some (fr, fcx) -> unframe fr (subst fcx f)
      | None -> assert false
      end
  | _ -> f

