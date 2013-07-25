(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2013  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Ocamlbuild_plugin ;;

let major = 0
let minor = 4
let patch = 3
let tag   = ""

(******************************************************************************)

(* sanity checks on versions *)
let major = max 0 major
let minor = max 0 minor
let patch = max 0 patch

let version_string =
  Printf.sprintf "%d.%d.%d%s" major minor patch
    (match tag with
     | "" -> ""
     | t -> "-" ^ tag)

let version_file_contents =
  let buf = Buffer.create 255 in
  let printf fmt = Printf.bprintf buf (fmt ^^ "\n") in
  printf "(* DO NOT EDIT *)" ;
  printf "(* this file is automatically generated by myocamlbuild.ml *)" ;
  printf "let major : int = %d;;" major ;
  printf "let minor : int = %d;;" minor ;
  printf "let patch : int = %d;;" patch ;
  (* printf "let tag   : string = %S;;" tag *)
  printf "let str = %S;;" version_string ;
  Buffer.contents buf

let version_file = "version.ml"

let maybe_make_version_file () =
  if not begin
    Sys.file_exists version_file
    && Digest.file version_file = Digest.string version_file_contents
  end then begin
    Printf.printf "Recreating %S\n" version_file ;
    let oc = open_out version_file in
    output_string oc version_file_contents ;
    close_out oc
  end

let _ =
  maybe_make_version_file () ;
  dispatch begin function
  | After_rules ->
      flag ["ocaml" ; "menhir"] (S [A "--explain" ; A "--strict"]) ;
      flag ["ocaml" ; "compile"] (A "-annot") ;
      flag ["ocaml" ; "compile"] (A "-g") ;
      flag ["ocaml" ; "compile"] (S [A "-w" ; A "@3@5@6@8..12@14@20@26@28@29"]) ;
      flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
  | _ -> ()
  end
