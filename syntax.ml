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
  | Mark  of mkind * form

and fcx = frame Cx.t

and frame = {
  conn  : conn ;
  left  : form list ;
  right : form list ;
}

and quant = All | Ex

and conn =
  | Tens | Plus | Par | With | Lto
  | Qu of quant * idt
  | Bang | Qm

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
  | Mark (_, f) ->
      test_form_ dep test f
  | Subst (fcx, f) ->
      test_fcx_ dep test fcx f
  end

and test_fcx_ dep test fcx f =
  begin match Cx.front fcx with
  | None -> test_form_ dep test f
  | Some ({conn = Qu _ ; _}, fcx) ->
      test_fcx_ (dep + 1) test fcx f
  | Some (fr, fcx) ->
      List.exists (test_form_ dep test) fr.left
      || List.exists (test_form_ dep test) fr.right
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

let _Lto f g =
  begin match f, g with
  | Conn (Tens, []), _ -> g
  | _ -> Conn (Lto, [f ; g])
  end

let rec mk_lto fs =
  begin match fs with
  | [] -> _Bot
  | [f] -> f
  | f :: gs -> _Lto f (mk_lto gs)
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
  | f -> Conn (Qu (q, x), [f])
  end

let _All x f = _Q All x f
let _Ex x f = _Q Ex x f

exception Cannot_mark

let rec has_mark ?m f =
  begin match f with
  | Mark (n, f) ->
      begin match m with
      | Some n' -> n = n' || has_mark ?m f
      | None -> true
      end
  | Conn (q, fs) -> List.exists (has_mark ?m) fs
  | Atom _ -> false
  | Subst (fcx, f) -> has_mark_fcx ?m fcx || has_mark ?m f
  end

and has_mark_fcx ?m fcx =
  begin match Cx.front fcx with
  | Some ({left ; right ; _}, fcx) ->
      List.exists (has_mark ?m) left
      || List.exists (has_mark ?m) right
      || has_mark_fcx ?m fcx
  | None -> false
  end

let mark m f = 
  if has_mark ~m f then raise Cannot_mark ;
  Mark (m, f)

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
  | Lto       -> mk_lto
  | Bang      -> mk_un _Bang
  | Qm        -> mk_un _Qm
  | Qu (q, x) -> mk_un (_Q q x)
  end

let unmark f =
  begin match f with
  | Mark (_, f) -> f
  | _ -> f
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
      let f = sub_form (bump ss) f in
      let x = maybe_refresh x f in
      _Q q x f
  | Conn (Qu _, _) -> assert false
  | Conn (c, fs) ->
      conn c (List.map (sub_form ss) fs)
  | Mark (m, f) ->
      Mark (m, sub_form ss f)
  | Subst (fcx, f) ->
      let (fcx, ss) = sub_fcx ss fcx in
      subst fcx (sub_form ss f)
  end

and sub_fcx ss fcx =
  begin match Cx.front fcx with
  | Some ({ conn = Qu (q, x) ; _ } as fr, fcx) ->
      let (fcx, ss) = sub_fcx (bump ss) fcx in
      let x = maybe_refresh_fcx x fcx in 
      let fr = { fr with conn = Qu (q, x) } in
      (Cx.cons fr fcx, ss)
  | Some (fr, fcx) ->
      let fr = { fr with
        left = List.map (sub_form ss) fr.left ;
        right = List.map (sub_form ss) fr.right ;
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

and maybe_refresh x f =
  if var_occurs x f then
    Idt.refresh x
  else x

and maybe_refresh_fcx x fcx =
  if var_occurs_fcx x fcx then
    Idt.refresh x
  else x

and var_occurs x f =
  begin match f with
  | Subst (fcx, f) ->
      var_occurs_fcx x fcx
      || var_occurs x f
  | Conn (Qu (_, y), _) when x = y ->
      true
  | Conn (_, fs) ->
      List.exists (var_occurs x) fs
  | Mark (_, f) ->
      var_occurs x f
  | Atom (_, p, ts) ->
      p = x
      || List.exists (test_term (identifier_is_free x)) ts
  end
    
and var_occurs_fcx x fcx =
  begin match Cx.front fcx with
  | None -> false
  | Some ({conn = Qu (_, y) ; _}, _) when x = y ->
      true
  | Some ({conn = _ ; left ; right}, fcx) ->
      List.exists (var_occurs x) left
      || List.exists (var_occurs x) right
      || var_occurs_fcx x fcx
  end

and identifier_is_free x ~dep = function
  | App (f, _) -> x = f
  | _ -> false  

let rec fcx_vars fcx =
  begin match Cx.rear fcx with
  | Some (fcx, {conn = Qu (_, x) ; _}) ->
      x :: fcx_vars fcx
  | Some (fcx, _) ->
      fcx_vars fcx
  | None ->
      []
  end

let subst1 fr f = subst (Cx.of_list [fr]) f

let rec unsubst f =
  begin match f with
  | Subst (fcx, f) -> (fcx, f)
  | _ -> (Cx.empty, f)
  end

let unframe fr f =
  conn fr.conn (List.rev_append fr.left (f :: fr.right))

let head1 f =
  match f with
  | Subst (fcx, f) ->
      begin match Cx.front fcx with
      | Some (fr, fcx) -> unframe fr (subst fcx f)
      | None -> assert false
      end
  | _ -> f

let focus f =
  let (_fcx, f) = unsubst f in
  f

let aeq_conn c1 c2 =
  begin match c1, c2 with
  | Qu (All, _), Qu (All, _)
  | Qu (Ex, _), Qu (Ex, _) -> true
  | _ -> c1 = c2
  end

let rec aeq_forms f1 f2 =
  begin match head1 f1, head1 f2 with
  | Atom (s1, p1, t1s), Atom (s2, p2, t2s)
    when s1 = s2 && p1 = p2 ->
      List.for_all2 (=) t1s t2s
  | Conn (c1, f1s), Conn (c2, f2s)
    when aeq_conn c1 c2 ->
      List.length f1s = List.length f2s
      && List.for_all2 aeq_forms f1s f2s
  | Subst _, _
  | _, Subst _ -> assert false
  | _ -> false
  end
