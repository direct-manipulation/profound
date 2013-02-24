(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

{
  let newline lb =
    Lexing.(
      lb.lex_curr_p <- { lb.lex_curr_p with
        pos_bol = lb.lex_curr_p.pos_cnum ;
        pos_lnum = lb.lex_curr_p.pos_lnum + 1 ;
      }
    )
}

let ident_initial = ['A'-'Z' 'a'-'z']
let ident_body    = ident_initial | ['_']
let ident         = ident_initial ident_body*

let space         = ' ' | '\t'
let newline       = '\r''\n' | '\n'

rule token = parse
| '%'              { line_comment lexbuf }

| space            { token lexbuf }
| newline          { newline lexbuf ; token lexbuf }

| "~" | "\\lnot"   { Form_p.LNOT }

| '*' | "\\tensor" { Form_p.TENSOR }
| '1' | "\\one"    { Form_p.ONE }
| '+' | "\\plus"   { Form_p.PLUS }
| '0' | "\\zero"   { Form_p.ZERO }

| '|' | "\\par"    { Form_p.PAR }
| "#F" | "\\bot"   { Form_p.BOT }
| "&" | "\\with"   { Form_p.WITH }
| "#T" | "\\top"   { Form_p.TOP }

| '!'              { Form_p.BANG }
| '?'              { Form_p.QM }

| "\\A"            { Form_p.FORALL }
| "\\E"            { Form_p.EXISTS }

| ','              { Form_p.COMMA }
| '.'              { Form_p.DOT }
| '('              { Form_p.LPAREN }
| ')'              { Form_p.RPAREN }

and line_comment = parse
| newline          { newline lexbuf ; token lexbuf }
| _                { line_comment lexbuf }
