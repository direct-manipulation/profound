type doc =
  | String of string
  | StringAs of int * string
  | Fmt of (Format.formatter -> unit)
  | Cat of doc list
  | Break of int * int
  | HBox of doc
  | VBox of int * doc
  | HVBox of int * doc
  | HOVBox of int * doc
  | Newline

val doc_map : (int -> string -> doc) -> doc -> doc

val pp_doc : Format.formatter -> doc -> unit

val lin_doc_buffer : Buffer.t -> doc -> unit
val lin_doc : doc -> string

type exp =
  | Atom of doc
  | Wrap of doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp * exp

and assoc = Left | Right | Non

val bracket : exp -> doc
