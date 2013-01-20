(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

module Must = struct
  include Idt
  include Syntax
end

let () =
  Log.to_file "profound.log" ;
  Log.(log INFO "Profound %s START" Version.str)
;;

let () =
  if not !Sys.interactive then
    Printf.printf "Profound %s non-interactive mode.\n" Version.str
  else
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
