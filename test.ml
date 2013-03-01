open Batteries

open Syntax
open Traversal
open Rules

open Idt

let form str = Syntax_io.form_of_string [] str

let display f =
  let (fcx, f) = unsubst f in
  (Fcx.to_list fcx, f)
