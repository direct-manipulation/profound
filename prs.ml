(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

type 'a prs = { prs : pst -> 'a resp }

and pst = {
  input        : string ;
  mutable off  : int ;
}

and 'a resp =
  | Read of 'a
  | Fail of int * string

let parse p input off =
  let pst = { input ; off } in
  match p.prs pst with
    | Read a -> Read (a, pst.off)
    | Fail (pos, msg) -> Fail (pos, msg)

let wsprex = Pcre.regexp ~flags:[`MULTILINE] "\\s*"

let skip rex pos str =
  if pos >= String.length str then raise Not_found ;
  let offs = Pcre.pcre_exec ~rex ~pos str in
  offs.(1)

let fuzzy word =
  let rex = Pcre.regexp ("\\G" ^ Pcre.quote word) in {
    prs = fun pst -> try begin
      let off = pst.off in
      let off = skip wsprex off pst.input in
      let next_off = skip rex off pst.input in
      pst.off <- next_off ;
      Read (String.sub pst.input off (next_off - off))
    end with Not_found -> Fail (pst.off, "fuzzy: " ^ word)
  }

let exact word =
  let rex = Pcre.regexp ("\\G" ^ Pcre.quote word) in {
    prs = fun pst -> try begin
      let off = pst.off in
      let next_off = skip rex off pst.input in
      pst.off <- next_off ;
      Read (String.sub pst.input off (next_off - off))
    end with Not_found -> Fail (pst.off, "exact: " ^ word)
  }

let regex ?(skipws = true) rex = {
  prs = fun pst -> try begin
    let off = pst.off in
    let off = (if skipws
               then skip wsprex off pst.input
               else off) in
    let next_off = skip rex off pst.input in
    pst.off <- next_off ;
    Read (String.sub pst.input off (next_off - off))
  end with Not_found -> Fail (pst.off, "regex")
}

let eoi = {
  prs = fun pst -> try begin
    let off = skip wsprex pst.off pst.input in
    pst.off <- off ;
    Read ()
  end with Not_found -> Fail (pst.off, "eoi")
}

let return x = { prs = fun pst -> Read x }

let fail msg = { prs = fun pst -> Fail (pst.off, msg) }

let ( >>= ) p qf = {
  prs = fun pst ->
    match p.prs pst with
      | Read a -> (qf a).prs pst
      | Fail (pos, msg) -> Fail (pos, msg)
}

let bind = ( >>= )

let ( <$> ) p fn = {
  prs = fun pst ->
    match p.prs pst with
      | Read a -> Read (fn a)
      | Fail (pos, msg) -> Fail (pos, msg)
}

let ( <!> ) p x = {
  prs = fun pst ->
    match p.prs pst with
      | Read _ -> Read x
      | Fail (pos, msg) -> Fail (pos, msg)
}

let ( >>> ) p q = {
  prs = fun pst ->
    match p.prs pst with
      | Read _ -> q.prs pst
      | Fail (pos, msg) -> Fail (pos, msg)
}

let ( <<< ) p q = {
  prs = fun pst ->
    match p.prs pst with
      | Read a -> begin match q.prs pst with
          | Read _ -> Read a
          | Fail (pos, msg) -> Fail (pos, msg)
        end
      | Fail (pos, msg) -> Fail (pos, msg)
}

let ( <*> ) p q = {
  prs = fun pst ->
    match p.prs pst with
      | Read a -> begin match q.prs pst with
          | Read b -> Read (a, b)
          | Fail (pos, msg) -> Fail (pos, msg)
        end
      | Fail (pos, msg) -> Fail (pos, msg)
}

let ( <::> ) p q = {
  prs = fun pst ->
    match p.prs pst with
      | Read a -> begin match q.prs pst with
          | Read bs -> Read (a :: bs)
          | Fail (pos, msg) -> Fail (pos, msg)
        end
      | Fail (pos, msg) -> Fail (pos, msg)
}

let star p =
  let rec q = {
    prs = fun pst ->
      match p.prs pst with
        | Fail _ -> Read []
        | Read x -> begin
            match q.prs pst with
              | Read xs -> Read (x :: xs)
              | Fail _ -> failwith "impossible failure"
          end
  } in
  q

let star1 p = p <::> star p

let sep s p =
  let rec q = {
    prs = fun pst ->
      match p.prs pst with
        | Fail _ -> Read []
        | Read x -> begin match s.prs pst with
            | Fail _ -> Read [x]
            | Read _ -> begin match q.prs pst with
                | Read xs -> Read (x :: xs)
                | Fail _ -> failwith "impossible failure"
              end
          end
  } in
  q

let sep1 s p = p <::> star (s >>> p)

let rec alt = function
  | [p] -> p
  | p :: ps ->
      let q = alt ps in {
        prs = fun pst ->
          match p.prs pst with
            | Read x -> Read x
            | Fail _ -> q.prs pst
      }
  | [] -> invalid_arg "alt"

let use lp = { prs = fun pst -> (Lazy.force lp).prs pst }

let lookahead p = {
  prs = fun pst ->
    let off = pst.off in
    let res = p.prs pst in
    pst.off <- off ;
    res
}

let attempt p = {
  prs = fun pst ->
    let off = pst.off in
    match p.prs pst with
      | Read x -> Read x
      | Fail (pos, msg) ->
          pst.off <- off ;
          Fail (pos, msg)
}

let ( <|> ) p q = {
  prs = fun pst ->
    let off = pst.off in
    match p.prs pst with
      | Read x -> Read x
      | Fail _ ->
          pst.off <- off ;
          q.prs pst
}

let optional p = {
  prs = fun pst ->
    let off = pst.off in
    match p.prs pst with
      | Read x -> Read (Some x)
      | Fail (pos, msg) ->
          pst.off <- off ;
          Read None
}

let ( <?> ) p chk = {
  prs = fun pst ->
    let off = pst.off in
    match p.prs pst with
      | Read x when chk x -> Read x
      | _ ->
          pst.off <- off ; Fail (off, "<?>")
}

let ( <$?> ) p wrp = {
  prs = fun pst ->
    let off = pst.off in
    match p.prs pst with
      | Read x -> begin match wrp x with
          | Some x -> Read x
          | None -> pst.off <- off ; Fail (off, "<$?>")
        end
      | _ ->
          pst.off <- off ; Fail (off, "<?>")
}

let lift1 f ap =
  ap >>= fun a ->
    return (f a)

let lift2 f ap bp =
  ap >>= fun a ->
    bp >>= fun b ->
      return (f a b)

let lift3 f ap bp cp =
  ap >>= fun a ->
    bp >>= fun b ->
      cp >>= fun c ->
        return (f a b c)

let lift4 f ap bp cp dp =
  ap >>= fun a ->
    bp >>= fun b ->
      cp >>= fun c ->
        dp >>= fun d ->
          return (f a b c d)

let lift5 f ap bp cp dp ep =
  ap >>= fun a ->
    bp >>= fun b ->
      cp >>= fun c ->
        dp >>= fun d ->
          ep >>= fun e ->
            return (f a b c d e)

type assoc = Left | Right

type 'a item =
  | Atom of 'a
  | Appl of int * 'a appl

and 'a appl =
  | Prefix  of         ('a -> 'a)
  | Postfix of         ('a -> 'a)
  | Infix   of assoc * ('a -> 'a -> 'a)

let resolve ip =
  let rec next stack =
    attempt (ip >>= decide stack) <|> use (finish stack)

  and decide stack item =
    match item with
    | Atom _ | Appl (_, Prefix _) -> begin
        match stack with
          | Atom _ :: _ -> fail "missing operator"
          | _ -> next (item :: stack)
      end
    | Appl (opr, Infix (oasc, _)) -> begin
        let rec normalize stack = match stack with
          | _ :: Appl (ppr, _) :: _
              when opr < ppr ->
              normalize (reduce_one stack)
          | _ :: Appl (ppr, Infix (Left, _)) :: _
              when oasc = Left && opr <= ppr ->
              normalize (reduce_one stack)
          | _ -> stack
        in
        let stack = normalize stack in
        match stack with
          | Atom _ :: _ -> next (item :: stack)
          | _ :: _ -> fail "missing operator"
          | [] -> fail "insufficient argumetns"
      end
    | Appl (opr, Postfix _) -> begin
        let rec normalize stack = match stack with
          | _ :: Appl (ppr, _) :: _
              when opr < ppr ->
              normalize (reduce_one stack)
          | _ -> stack
        in
        let stack = normalize stack in
        match stack with
          | Atom _ :: _ ->
              next (reduce_one (item :: stack))
          | _ :: _ -> fail "missing operator"
          | [] -> fail "insufficient argumetns"
      end

  and reduce_one stack =
    match stack with
    | Appl (_, Postfix px) :: Atom a :: stack
    | Atom a :: Appl (_, Prefix px) :: stack ->
        Atom (px a) :: stack
    | Atom b :: Appl (_, Infix (_, ix)) :: Atom a :: stack ->
        Atom (ix a b) :: stack
    | _ -> failwith "reduce_one"

  and finish stack = lazy begin
    let rec spin = function
      | [] -> fail "missing required argument"
      | [Atom a] -> return a
      | stack -> spin (reduce_one stack)
    in
    spin stack
  end in
  next []
