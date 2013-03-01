(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Syntax

let wash_file = "tex/wash_form1.png"

type mode =
  | Imm  of string
  | File of string

module type Param = sig
  val mode : mode
end

module Run (Param : Param) =
struct

  let initial_state = match Param.mode with
  | Imm str ->
      begin match Syntax_io.form_of_string [] str with
      | Ok f -> Action.init f
      | Bad msg ->
          Log.(log FATAL "Parsing error [%s] parsing:" msg) ;
          Log.(log FATAL "\t%s" str) ;
          exit 1
      end
  | File fin ->
      Syntax_io.(
        try load_file fin with
        | Parsing msg ->
            Log.(log FATAL "Parsing error [%s] parsing file:" msg) ;
            Log.(log FATAL "\t%S" fin) ;
            exit 1
      )
  ;;
  
  let state = ref initial_state

  let main_win =
    let win = GWindow.window
      ~title:"Profound"
      ~border_width:3
      ~deletable:true () in
    let sw = Gdk.Screen.width () in
    let sh = Gdk.Screen.height () in
    (* [HACK] *)
    Log.(log INFO "Screen: %d x %d" sw sh) ;
    if sw > 1920 || sh > 1080 then Syntax_tex.set_dpi 240 ;
    win#misc#set_size_request ~width:(sw * 3/5) ~height:(sh * 4/5) () ;
    win#misc#modify_bg [`NORMAL, `NAME "ivory" ] ;
    ignore (win#event#connect#delete ~callback:(fun _ -> false)) ;
    ignore (win#connect#destroy ~callback:GMain.Main.quit) ;
    win

  let awaiting_quit = ref false

  let quit () =
    awaiting_quit := true ;
    main_win#destroy () ;
    !state

  let (disp, stat) =
    let box = GPack.vbox ~packing:main_win#add () in
    let sw = GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:box#add () in
    let disp = GMisc.image
      ~packing:sw#add_with_viewport () in
    ignore (GMisc.separator `HORIZONTAL ~packing:(box#pack ~expand:false) ()) ;
    let sbar = GMisc.statusbar
      ~packing:(box#pack ~expand:false) () in
    let stat = sbar#new_context "default" in
    (disp, stat)

  let flash fmt =
    Printf.ksprintf (fun txt ->
      if not !awaiting_quit then
        stat#flash ~delay:1500 txt
    ) fmt

  exception Cancelled_action

  let read_thing ~title ~label ~parse =
    let dwin = GWindow.dialog
      ~parent:main_win ~title
      ~modal:true
      ~position:`CENTER_ON_PARENT
      () in
    dwin#vbox#misc#set_size_request ~width:300 () ;
    dwin#add_button_stock `OK `OK ;
    dwin#add_button_stock `CANCEL `CANCEL ;
    dwin#set_default_response `CANCEL ;
    let _lab = GMisc.label
      ~xalign:0.
      ~packing:(dwin#vbox#pack ~expand:false)
      ~text:label
      () in
    let ebox = GEdit.entry
      ~text:""
      ~width:80
      ~packing:(dwin#vbox#pack ~expand:true)
      () in
    ebox#misc#grab_focus () ;
    let handler key =
      begin
        let ks = GdkEvent.Key.keyval key in
        if ks = GdkKeysyms._Return then (dwin#response `OK ; true)
        else if ks = GdkKeysyms._Escape then (dwin#response `CANCEL ; true)
        else false
      end in
    ignore (dwin#event#connect#key_press ~callback:handler) ;
    let resp = dwin#run () in
    let txt = String.trim ebox#text in
    dwin#destroy () ;
    begin match resp with
    | `OK ->
        begin match parse txt with
        | Ok t -> t
        | Bad msg ->
            flash "Failed to parse %S: %s" txt msg ;
            raise Cancelled_action
        end
    | _ ->
        raise Cancelled_action
    end      

  let read_term x cx =
    let title = "Term input" in
    let label = Printf.sprintf "Enter a witness for %s:" (Idt.src_rep x) in
    let parse txt = Syntax_io.term_of_string cx txt in
    read_thing ~title ~label ~parse

  let read_form cx =
    let title = "Formula input" in
    let label = "Enter a cut formula:" in
    let parse txt = Syntax_io.form_of_string cx txt in
    read_thing ~title ~label ~parse

  (* key processing *)

  type key = {
    code : Gdk.keysym ;
    c : bool ;
    s : bool ;
  }

  type adesc = {
    action : Action.t ;
    desc   : string ;
  }

  type kmap = (key, adesc list) Map.t

  let add_action km key act : kmap =
    begin match Map.Exceptionless.find key km with
    | Some acts ->
        Map.add key (act :: acts) km
    | None ->
        Map.add key [act] km
    end

  let (klist, kmap) =
    Action.(GdkKeysyms.(
      let c = true in
      let s = true in
      let klist = ref [] in
      let kmap = ref Map.empty in
      let add ?(e = false) ?(c = false) ?(s = false) code ad =
        let key = { code ; c ; s } in
        if ad.desc <> "" then klist := ad :: !klist ;
        kmap := add_action !kmap key ad
      in
      add _Down      { action = action_descend
                     ; desc   = ""                     } ;
      add _Up        { action = action_ascend
                     ; desc   = ""                     } ;
      add ~s _Up     { action = action_ascend_to_top
                     ; desc   = ""                     } ;
      add _Left      { action = action_left
                     ; desc   = ""                     } ;
      add _Right     { action = action_right
                     ; desc   = ""                     } ;
      add _Return    { action = action_mark_source
                     ; desc   = "Enter=mark"           } ;
      add _Return    { action = action_unmark_source
                     ; desc   = "Enter=unmark"         } ;
      add _Return    { action = action_complete_link
                     ; desc   = "Enter=link"           } ;
      add _Escape    { action = action_reset
                     ; desc   = "Esc=reset"            } ;
      add _Delete    { action = action_zero
                     ; desc   = "Del=kill"             } ;
      add ~s _Delete { action = action_weaken
                     ; desc   = "Shift-Del=weaken"     } ;
      add ~s _Return { action = action_contract
                     ; desc   = "Shift-Enter=contract" } ;
      add ~s _question { action = action_derelict
                       ; desc = "?=derelict"           } ;
      add ~s _Return { action = action_witness ~read:read_term
                     ; desc   = "Shift-Enter=witness"  } ;
      add ~c _Return { action = action_cut ~read:read_form
                     ; desc   = "^Enter=cut"           } ;
      add ~c _z      { action = action_undo
                     ; desc   = "^Z=undo"              } ;
      add ~c _Down   { action = action_undo
                     ; desc   = ""                     } ;
      add ~c _y      { action = action_redo
                     ; desc   = "^Y=redo"              } ;
      add ~c ~s _Z   { action = action_redo
                     ; desc   = ""                     } ;
      add ~c _Up     { action = action_redo
                     ; desc   = ""                     } ;
      let action_more_history = {
        enabled = (fun _ -> true) ;
        perform = (fun hi ->
          incr Syntax_tex.max_hist ;
          Log.(log INFO "Now showing %d history line(s)" !Syntax_tex.max_hist) ;
          hi
        ) } in
      add ~s _plus   { action = action_more_history
                     ; desc   = ""                     } ;
      let action_less_history = {
        enabled = (fun _ -> !Syntax_tex.max_hist >= 1) ;
        perform = (fun hi ->
          decr Syntax_tex.max_hist ;
          Log.(log INFO "Now showing %d history line(s)" !Syntax_tex.max_hist) ;
          hi
        ) } in
      add _minus     { action = action_less_history
                     ; desc   = ""                     } ;
      begin match Param.mode with
      | Imm _ ->
          let action_quit = {
            enabled = (fun _ -> true) ;
            perform = (fun _ -> quit ()) ;
          } in
          add ~c _q { action = action_quit ; desc = "" }
      | File fin ->
          let action_quit = {
            enabled = (fun _ -> true) ;
            perform = begin fun hi ->
              Syntax_io.save_file fin hi ;
              quit ()
            end
          } in
          add ~c _q { action = action_quit ; desc   = "" } ;
          let action_save = {
            enabled = (fun _ -> true) ;
            perform = begin fun hi ->
              Syntax_io.save_file fin hi ;
              hi
            end
          } in
          add ~c _s { action = action_save ; desc = "" }
      end ;
      (List.rev !klist, !kmap)
    ))

  exception Handled

  let explain_keys () =
    let buf = Buffer.create 19 in
    List.iter begin function
      | {desc ; action} when desc <> "" && action.Action.enabled !state  -> 
          Buffer.add_string buf (desc ^ "; ")
      | _ -> ()
    end klist ;
    Buffer.add_string buf "^Q quit" ;
    Buffer.contents buf

  let redisplay () =
    if not !awaiting_quit then begin
      Syntax_tex.wash_forms (Action.render !state) ;
      let pix = GdkPixbuf.from_file wash_file in
      stat#pop () ;
      ignore (stat#push (explain_keys ())) ;
      disp#set_pixbuf pix
    end

  let () = redisplay ()

  let handle_key kt =
    let kst = GdkEvent.Key.state kt in
    let key = { code = GdkEvent.Key.keyval kt
              ; c = List.mem `CONTROL kst
              ; s = List.mem `SHIFT kst } in
    begin match Map.Exceptionless.find key kmap with
    | Some ads ->
        begin try (
          List.iter begin
            fun ad ->
              let act = ad.action in
              if act.Action.enabled !state then begin
                try
                  state := act.Action.perform !state ;
                  redisplay () ;
                  raise Handled
                with
                | Action.Action err -> flash "%s" (Action.explain err)
              end else ()
          end ads ;
          false
        ) with
        | Cancelled_action ->
            Log.(log DEBUG "Action was cancelled") ;
            true
        | Handled -> true
        end
    | None -> false
    end

  let _ = main_win#event#connect#key_press ~callback:handle_key

  let () = main_win#show ()

  let () = GMain.Main.main ()
end


let run mode =
  let module Param = struct let mode = mode end in
  let module R = Run (Param) in
  ()
