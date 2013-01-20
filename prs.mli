(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)
type 'a prs
and 'a resp =
  | Read of 'a
  | Fail of int * string
val parse : 'a prs -> string -> int -> ('a * int) resp
val fuzzy : string -> string prs
val exact : string -> string prs
val regex : ?skipws:bool -> Pcre.regexp -> string prs
val return : 'a -> 'a prs
val fail : string -> 'a prs
val eoi : unit prs
val ( >>= ) : 'a prs -> ('a -> 'b prs) -> 'b prs
val bind : 'a prs -> ('a -> 'b prs) -> 'b prs
val ( <$> ) : 'a prs -> ('a -> 'b) -> 'b prs
val ( <!> ) : 'a prs -> 'b -> 'b prs
val ( >>> ) : 'a prs -> 'b prs -> 'b prs
val ( <<< ) : 'a prs -> 'b prs -> 'a prs
val ( <*> ) : 'a prs -> 'b prs -> ('a * 'b) prs
val ( <::> ) : 'a prs -> 'a list prs -> 'a list prs
val star : 'a prs -> 'a list prs
val star1 : 'a prs -> 'a list prs
val sep : 'a prs -> 'b prs -> 'b list prs
val sep1 : 'a prs -> 'b prs -> 'b list prs
val alt : 'a prs list -> 'a prs
val use : 'a prs Lazy.t -> 'a prs
val lookahead : 'a prs -> 'a prs
val attempt : 'a prs -> 'a prs
val ( <|> ) : 'a prs -> 'a prs -> 'a prs
val optional : 'a prs -> 'a option prs
val ( <?> ) : 'a prs -> ('a -> bool) -> 'a prs
val ( <$?> ) : 'a prs -> ('a -> 'b option) -> 'b prs
type assoc = Left | Right
type 'a item = Atom of 'a | Appl of int * 'a appl
and 'a appl =
    Prefix of ('a -> 'a)
  | Postfix of ('a -> 'a)
  | Infix of assoc * ('a -> 'a -> 'a)
val resolve : 'a item prs -> 'a prs
val lift1 : ('a -> 'b) -> 'a prs -> 'b prs
val lift2 : ('a -> 'b -> 'c) -> 'a prs -> 'b prs -> 'c prs
val lift3 : ('a -> 'b -> 'c -> 'd) -> 'a prs -> 'b prs -> 'c prs -> 'd prs
val lift4 :
  ('a -> 'b -> 'c -> 'd -> 'e) ->
  'a prs -> 'b prs -> 'c prs -> 'd prs -> 'e prs
val lift5 :
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
  'a prs -> 'b prs -> 'c prs -> 'd prs -> 'e prs -> 'f prs
