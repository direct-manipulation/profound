open Batteries

open Syntax
open Traversal
open Rules

open Idt

let form str =
  begin match Syntax_io.form_of_string [] str with
  | Ok f -> f
  | Bad msg -> failwith msg
  end

