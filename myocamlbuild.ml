open Ocamlbuild_plugin ;;

let major = 0
let minor = 3
let patch = 1                           (* must be at least 1 -- this is enforced *)
let tag   = "itp13"

let patch = max patch 1

let built =
  let open Unix in
  let now = gmtime (gettimeofday ()) in
  Printf.sprintf "%4d-%02d-%02d %02d:%02d:%02dZ"
    (now.tm_year + 1900) (now.tm_mon + 1) now.tm_mday
    now.tm_hour now.tm_min now.tm_sec

let need_to_make_version = ref true

let make_version msg =
  Printf.printf "Generating version.ml (%s)...%!" msg ;
  if Sys.file_exists "version.ml" then Sys.remove "version.ml" ;
  let och = open_out "version.ml" in
  Printf.fprintf och "(* This file is automatically generated!\n" ;
  Printf.fprintf och "   To change version numbers, edit myocamlbuild.ml *)\n" ;
  Printf.fprintf och "let major = %d;;\n" major ;
  Printf.fprintf och "let minor = %d;;\n" minor ;
  Printf.fprintf och "let patch = %d;;\n" patch ;
  Printf.fprintf och "let built = \"%s\";;\n" built ;
  Printf.fprintf och "let tag   = \"%s\";;\n\n" tag ;
  Printf.fprintf och "let str   = \"%d.%d.%d%s%s\";;\n\n"
    major minor patch
    (if tag = "" then "" else "-") tag ;
  flush och ;
  close_out och ;
  Printf.printf " done\n%!"

let _ =
  if not (Sys.file_exists "version.ml") then (
    need_to_make_version := false ;
    make_version "initial"
  ) ;
  dispatch begin function
   | After_rules ->
       if !need_to_make_version then make_version "recompilation" ;
       flag ["ocaml" ; "menhir"] (S [A "--explain" ; A "--strict"]) ;
       flag ["ocaml" ; "compile"] (A "-annot") ;
       flag ["ocaml" ; "compile"] (A "-g") ;
       flag ["ocaml" ; "compile"] (S [A "-w" ; A "@3@5@8@11@12@26@28@29"]) ;
       flag ["ocaml" ; "native" ; "compile"] (A "-nodynlink") ;
   | _ -> ()
end
