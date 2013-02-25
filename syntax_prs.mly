(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)
%{

  let rec make_quant q vs f =
    begin match vs with
    | [] -> f
    | v :: vs -> q v (make_quant q vs f)
    end

%}

%token  EOS PREC_MIN PREC_MAX
%token  <Idt.t> IDENT
%token  LPAREN COMMA RPAREN
%token  LNOT
%token  TENSOR PLUS PAR WITH
%token  ONE ZERO BOT TOP
%token  BANG QM FORALL EXISTS DOT

%nonassoc PREC_MIN
%left     PAR
%left     WITH
%left     PLUS
%left     TENSOR
%nonassoc PREC_MAX

%start  <Syntax.term> one_term
%start  <Syntax.form> one_form

%%

term:
| head=IDENT args=terms      { Syntax.(App (head, args)) }
| LPAREN t=term RPAREN       { t }

form:
| head=IDENT args=terms      { Syntax.(atom ASSERT head args) }
| LNOT head=IDENT args=terms { Syntax.(atom REFUTE head args) }
| f=form TENSOR g=form         { Syntax.(_Tens f g) }
| ONE                        { Syntax._One }
| f=form PLUS g=form         { Syntax.(_Plus f g) }
| ZERO                       { Syntax._Zero }
| f=form PAR g=form          { Syntax.(_Par f g) }
| BOT                        { Syntax._Bot }
| f=form WITH g=form         { Syntax.(_With f g) }
| TOP                        { Syntax._Top }
| BANG f=form
  %prec PREC_MAX             { Syntax.(_Bang f) }
| QM f=form
  %prec PREC_MAX             { Syntax.(_Qm f) }
| FORALL vs=vars DOT f=form
  %prec PREC_MIN             { Syntax.(make_quant _All_capture vs f) }
| EXISTS vs=vars DOT f=form
  %prec PREC_MIN             { Syntax.(make_quant _Ex_capture vs f) }
| LPAREN f=form RPAREN       { f }

one_term:
| t=term EOS                 { t }

one_form:
| f=form EOS                 { f }

%inline terms:
| ts = plist(term)           { ts }

(* combinators *)

%inline plist(X):
| xs = loption (delimited (LPAREN, separated_nonempty_list (COMMA, X), RPAREN)) { xs }

%inline vars:
| vs = separated_nonempty_list (COMMA, IDENT) { vs }

