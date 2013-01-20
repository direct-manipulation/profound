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
    <!> Appl (50, Infix (Left, fun f g -> conn Tens [f ; g])) ;

    (fuzzy "\\one" <|> fuzzy "1")
    <!> Atom (conn One []) ;

    (fuzzy "\\plus" <|> fuzzy "+")
    <!> Appl (20, Infix (Left, fun f g -> conn Plus [f ; g])) ;

    (fuzzy "\\zero" <|> fuzzy "0")
    <!> Atom (conn Zero []) ;

    fuzzy "!" <!> Appl (60, Prefix (fun f -> conn Bang [f])) ;

    (fuzzy "\\par" <|> fuzzy "|" <|> fuzzy ",")
    <!> Appl (30, Infix (Left, fun f g -> conn Par [f ; g])) ;

    (fuzzy "\\bot" <|> fuzzy "#F")
    <!> Atom (conn Bot []) ;

    (fuzzy "\\with" <|> fuzzy "&")
    <!> Appl (40, Infix (Left, fun f g -> conn With [f ; g])) ;

    (fuzzy "\\top" <|> fuzzy "#T")
    <!> Atom (conn Top []) ;

    fuzzy "?" <!> Appl (60, Prefix (fun f -> conn Qm [f])) ;

    (fuzzy "\\A" <|> fuzzy "\\E")
    <*> sep1 (fuzzy ",") ident
    <<< fuzzy "."
    <$> (fun (q, vs) ->
           let qf v f = match q with
             | "\\A" -> conn (All v) [f]
             | _ -> conn (Ex v) [f]
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

(* let parse_form str = Prs.parse (Lazy.force form) str 0 *)
let parse_form str = Prs.parse (Lazy.force form <$> index_form []) str 0
