open Batteries

open Syntax
open Traversal
open Rules

open Idt

let pretty_form ?tr str =
  begin match Syntax_io.form_of_string [] str with
  | Ok f ->
      let f =
        begin match tr with
        | Some tr -> descend tr f
        | None -> f
        end in
      Syntax_fmt.Src.form_to_string [] f
  | Bad msg -> failwith msg
  end
