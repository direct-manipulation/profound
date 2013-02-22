(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax
open Prs

type 'a lprs = 'a prs Lazy.t

let ident = regex (Pcre.regexp "\\G[A-Za-z][A-Za-z0-9_]*") <$> Idt.intern

let rec form : form lprs = lazy begin
  resolve (use token)
end

and token = lazy begin
  alt [
    (fuzzy "\\tensor" <|> fuzzy "*")
    <!> Appl (50, Infix (Left, _Tens)) ;

    (fuzzy "\\one" <|> fuzzy "1")
    <!> Atom _One ;

    (fuzzy "\\plus" <|> fuzzy "+")
    <!> Appl (20, Infix (Left, _Plus)) ;

    (fuzzy "\\zero" <|> fuzzy "0")
    <!> Atom _Zero ;

    fuzzy "!" <!> Appl (60, Prefix _Bang) ;

    (fuzzy "\\par" <|> fuzzy "|" <|> fuzzy ",")
    <!> Appl (30, Infix (Left, _Par)) ;

    (fuzzy "\\bot" <|> fuzzy "#F")
    <!> Atom _Bot ;

    (fuzzy "\\with" <|> fuzzy "&")
    <!> Appl (40, Infix (Left, _With)) ;

    (fuzzy "\\top" <|> fuzzy "#T")
    <!> Atom _Top ;

    fuzzy "?" <!> Appl (60, Prefix _Qm) ;

    (fuzzy "\\A" <|> fuzzy "\\E")
    <*> sep1 (fuzzy ",") ident
    <<< fuzzy "."
    <$> (fun (q, vs) ->
           let qf v f = match q with
             | "\\A" -> _All v f
             | _ -> _Ex v f
           in
           let rec mk vs f = match vs with
             | [] -> f
             | v :: vs -> mk vs (qf v f)
           in
           Appl (10, Prefix (mk (List.rev vs)))) ;

    ident <*> use params
    <$> (fun (p, ts) -> Atom (atom ASSERT p ts)) ;

    (fuzzy "\\lnot" <|> fuzzy "~") >>>
      ident <*> use params
    <$> (fun (p, ts) -> Atom (atom REFUTE p ts)) ;

    (fuzzy "(" >>> use form <<< fuzzy ")")
    <$> (fun f -> Atom f) ;
  ]
end

and params = lazy begin
  alt [
    fuzzy "(" >>> sep1 (fuzzy ",") (use term) <<< fuzzy ")" ;
    return []
  ]
end

and term = lazy begin
  ident <*> use params
  <$> (fun (f, ts) -> App (f, ts))
end

let term = Lazy.force term

let rec index_term cx = function
  | Idx n -> Idx n
  | App (c, []) ->
      begin match index_find cx c with
      | None -> App (c, [])
      | Some n -> Idx n
      end
  | App (f, ts) ->
      App (f, List.map (index_term cx) ts)

and index_find ?(dep = 0) cx c =
  begin match cx with
  | [] -> None
  | x :: _ when c = x -> Some dep
  | _ :: cx -> index_find ~dep:(dep + 1) cx c
  end

let rec index_form cx f =
  begin match f with
  | Syntax.Atom (s, p, ts) ->
      atom s p (List.map (index_term cx) ts)
  | Conn ((All x | Ex x) as q, fs) ->
      let fs = List.map (index_form (x :: cx)) fs in
      conn q fs
  | Conn (c, fs) ->
      conn c (List.map (index_form cx) fs)
  | Subst _ -> assert false
  end

let parse_term cx str = Prs.parse_full (term <$> index_term cx) str 0

let parse_form str = Prs.parse_full (Lazy.force form <$> index_form []) str 0
