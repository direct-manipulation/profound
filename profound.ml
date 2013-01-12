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
  if not !Sys.interactive then
    Printf.eprintf "Hello, world.\n"
  else
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
