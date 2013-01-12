open Format

type doc =
  | String of string
  | StringAs of int * string
  | Fmt of (formatter -> unit)
  | Cat of doc list
  | Break of int * int
  | HBox of doc
  | VBox of int * doc
  | HVBox of int * doc
  | HOVBox of int * doc
  | Newline

let string0 str =
  Fmt (fun ff -> pp_print_as ff 0 str)

let rec doc_map fn = function
  | String s -> fn (String.length s) s
  | StringAs (n, s) -> fn n s
  | Cat ds -> Cat (List.map (doc_map fn) ds)
  | HBox d -> HBox (doc_map fn d)
  | VBox (n, d) -> VBox (n, doc_map fn d)
  | HVBox (n, d) -> HVBox (n, doc_map fn d)
  | HOVBox (n, d) -> HOVBox (n, doc_map fn d)
  | (Fmt _ | Break _ | Newline) as d -> d

let rec pp_doc ff = function
  | String s ->
      let fmt : (unit, formatter, unit) format = Obj.magic s in
      Format.fprintf ff fmt
  | StringAs (n, s) ->
      pp_print_as ff n s
  | Fmt fmt -> fmt ff
  | Cat ds ->
      List.iter (pp_doc ff) ds
  | Break (nsp, offs) ->
      pp_print_break ff nsp offs
  | HBox d ->
      pp_open_hbox ff () ;
      pp_doc ff d ;
      pp_close_box ff ()
  | VBox (ind, d) ->
      pp_open_vbox ff ind ;
      pp_doc ff d ;
      pp_close_box ff ()
  | HVBox (ind, d) ->
      pp_open_hvbox ff ind ;
      pp_doc ff d ;
      pp_close_box ff ()
  | HOVBox (ind, d) ->
      pp_open_hovbox ff ind ;
      pp_doc ff d ;
      pp_close_box ff ()
  | Newline ->
      pp_force_newline ff ()

let lin_doc_buffer buf d =
  let rec output = function
    | String s | StringAs (_, s) -> Buffer.add_string buf s
    | Fmt fmt -> Format.bprintf buf "%t" fmt
    | Cat ds -> List.iter output ds
    | HBox d | VBox (_, d) | HVBox (_, d) | HOVBox (_, d) -> output d
    | Break (0, _) -> ()
    | Break _ | Newline -> Buffer.add_char buf ' '
  in
  output d

let lin_doc d =
  let buf = Buffer.create 10 in
  lin_doc_buffer buf d ;
  Buffer.contents buf

type exp =
  | Atom of doc
  | Wrap of doc * exp * doc
  | Appl of int * bappl

and bappl =
  | Prefix of doc * exp
  | Postfix of doc * exp
  | Infix of doc * assoc * exp * exp

and assoc = Left | Right | Non

let rec ( >? ) prec be = match be with
  | Appl (subprec, _) when prec > subprec -> true
  | Wrap (_, be, _) -> prec >? be
  | _ -> false

let rec is_prefix = function
  | Appl (_, Prefix _) -> true
  | Wrap (_, be, _) -> is_prefix be
  | _ -> false

let rec is_postfix = function
  | Appl (_, Postfix _) -> true
  | Wrap (_, be, _) -> is_postfix be
  | _ -> false

let rec infix_incompat_for tasc pr asc = function
  | Appl (spr, (Prefix _ | Postfix _))
      when pr >= spr -> true
  | Appl (spr, Infix (_, sasc, _, _))
      when pr = spr && not (asc = tasc && sasc = tasc) -> true
  | Wrap (_, be, _) ->
      infix_incompat_for tasc pr asc be
  | _ -> false

let reprec =
  let module M = struct
    type dinfo = PRE of int | POST of int | NVM
  end in
  let open M in
  let rec dig e = match e with
    | Atom _ -> (e, NVM)
    | Appl (p, Infix (d, asc, l, r)) ->
        let (l, _) = dig l in
        let (r, _) = dig r in
        (Appl (p, Infix (d, asc, l, r)), NVM)
    | Appl (p, Prefix (d, e)) -> begin
        let (e, di) = dig e in
        let p = match di with
          | PRE q -> min p q
          | _ -> p
        in
        (Appl (p, Prefix (d, e)), PRE p)
      end
    | Appl (p, Postfix (d, e)) -> begin
        let (e, di) = dig e in
        let p = match di with
          | POST q -> min p q
          | _ -> p
        in
        (Appl (p, Postfix (d, e)), POST p)
      end
    | Wrap (b, e, a) ->
        let (e, di) = dig e in
        (Wrap (b, e, a), di)
  in
  fun e -> fst (dig e)

let bracket =
  let rec bracket_if cond be =
    if cond then
      HBox (Cat [String "<bra>" ; pp be ; String "</bra>"])
    else pp be
  and pp = function
    | Atom d -> d
    | Wrap (bef, be, aft) ->
        HBox (Cat [bef ; pp be ; aft])
    | Appl (prec, appl) -> begin
        match appl with
          | Prefix (oprep, be) ->
              HOVBox begin 2, Cat [
                oprep ;
                bracket_if (prec >? be && not (is_prefix be)) be
              ] end
          | Postfix (oprep, be) ->
              HBox begin Cat [
                bracket_if (prec >? be && not (is_postfix be)) be ;
                oprep
              ] end
          | Infix (oprep, asc, lbe, rbe) ->
              HOVBox begin 0, Cat [
                bracket_if (prec >? lbe ||
                              infix_incompat_for Left prec asc lbe) lbe ;
                oprep ;
                bracket_if (prec >? rbe ||
                              infix_incompat_for Right prec asc rbe) rbe ;
              ] end
      end
  in
  fun e -> pp (reprec e)
