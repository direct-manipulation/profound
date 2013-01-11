let () =
  if not !Sys.interactive then
    Printf.eprintf "Hello, world.\n"
  else
    Printf.printf "Profound %s [%s]\n" Version.str Version.built
