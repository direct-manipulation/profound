(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries

open Syntax

let wash_file = "tex/wash_form1.png"

let form_to_pixbuf cur his =
  if Syntax_tex.wash_forms cur (List.map fst his) <> 0 then None else
    try
      let img = GdkPixbuf.from_file wash_file in
      Some img
    with _ -> None

type mark_mode =
  | NO_MARKS
  | HAS_SRC
  | HAS_BOTH

type gui = {
  mutable mmode : mark_mode ;
  mutable cur : form ;
  mutable hist : (form * mark_mode) list ;
  mutable win : GWindow.window ;
  mutable img : GMisc.image ;
  mutable stxt : GMisc.statusbar_context ;
}

let gui : gui = {
  mmode = NO_MARKS ;
  cur = atom ASSERT (Idt.intern "a") [] ;
  hist = [] ;
  win = Obj.magic 0 ;
  img = Obj.magic 0 ;
  stxt = Obj.magic 0 ;
}

let redisplay () =
  gui.stxt#pop () ;
  begin match form_to_pixbuf gui.cur gui.hist with
  | None -> ()
  | Some pix ->
      gui.img#set_pixbuf pix ;
      let _ = gui.stxt#push begin
        match gui.mmode with
        | NO_MARKS -> "Select a subformula with ENTER to mark a source"
        | HAS_SRC -> "Select a subformula to mark a sink"
        | HAS_BOTH -> "INTERNAL ERROR!"
      end in
      ()
  end

let mod_to_string m =
  begin match m with
  | `BUTTON1 -> "BUTTON1"
  | `BUTTON2 -> "BUTTON2"
  | `BUTTON3 -> "BUTTON3"
  | `BUTTON4 -> "BUTTON4"
  | `BUTTON5 -> "BUTTON5"
  | `CONTROL -> "CONTROL"
  | `HYPER -> "HYPER"
  | `LOCK -> "LOCK"
  | `META -> "META"
  | `MOD1 -> "MOD1"
  | `MOD2 -> "MOD2"
  | `MOD3 -> "MOD3"
  | `MOD4 -> "MOD4"
  | `MOD5 -> "MOD5"
  | `RELEASE -> "RELEASE"
  | `SHIFT -> "SHIFT"
  | `SUPER -> "SUPER"
  end

let log_mods mods =
  Log.(log DEBUG "Mods: [%s]"
         (String.concat "," (List.map mod_to_string mods)))

let kmap = ref Map.empty

let rec y_or_n handle_y key =
  let open GdkKeysyms in
  let ksym = GdkEvent.Key.keyval key in
  if ksym = _y || ksym = _Y then begin
    handle_y () ;
    gui.stxt#pop () ;
    true
  end else if ksym = _n || ksym = _N then begin
    ignore (gui.win#event#connect#key_press ~callback:handle_key) ;
    gui.stxt#pop () ;
    true
  end else begin
    false
  end

and handle_key key =
  begin 
    let ksym = GdkEvent.Key.keyval key in
    Log.(log DEBUG "handle_key/ksym: 0x%04x" ksym) ;
    let mods = GdkEvent.Key.state key in
    log_mods mods ;
    Map.mem ksym !kmap && (Map.find ksym !kmap) mods
  end

let key_down _ =
  Traversal.(
    try
      let f = Traversal.go_down 0 gui.cur in
      gui.cur <- f ;
      redisplay () ;
      true
    with
    | Traversal At_leaf ->
        gui.stxt#flash "Cannot descend further" ;
        true
    | Traversal _ -> false)

let key_up mods =
  Traversal.(
  let go_fn = if List.mem `SHIFT mods then go_top else go_up in
  try
    let f = go_fn gui.cur in
    gui.cur <- f ;
    redisplay () ;
    true
  with
  | Traversal At_top ->
      gui.stxt#flash "Cannot ascend further" ;
      true
  | Traversal _ -> false)

let key_left _ =
  Traversal.(try begin
    let f = go_left gui.cur in
    gui.cur <- f ;
    redisplay () ;
    true
  end with Traversal _ -> false)

let key_right _ =
  Traversal.(try begin
    let f = go_right gui.cur in
    gui.cur <- f ;
    redisplay () ;
    true
  end with Traversal _ -> false)

exception Silently_fail

let key_enter mods =
  Traversal.(try begin
    if List.mem `SHIFT mods then begin
      let (fcx, f) = unsubst gui.cur in
      match f with
      | Conn (Ex x, [fb]) -> begin
          let dwin = GWindow.dialog
            ~parent:gui.win
            ~title:"Enter a witness"
            ~modal:true
            ~position:`CENTER_ON_PARENT () in
          dwin#vbox#misc#set_size_request ~width:640 () ;
          dwin#add_button_stock `OK `OK ;
          dwin#add_button_stock `CANCEL `CANCEL ;
          let lab = GMisc.label ~xalign:0.
            ~packing:(dwin#vbox#pack ~expand:false) () in
          let msg = "Enter a witness for " ^ (Idt.rep x) ^ "\n" in
          lab#set_text msg ;
          let ebox = GEdit.entry ~text:""
            ~width:80
            ~packing:(dwin#vbox#pack ~expand:false) () in
          let handler key = begin
            let open GdkKeysyms in
            let ks = GdkEvent.Key.keyval key in
            if ks = _Return then (dwin#response `OK ; true)
            else if ks = _Escape then (dwin#response `CANCEL ; true)
            else false
          end in
          ignore (dwin#event#connect#key_press ~callback:handler) ;
          let resp = dwin#run () in
          let txt = String.trim ebox#text in
          dwin#destroy () ;
          begin match resp with
          | `OK ->
              begin match Syntax_prs.parse_term (fcx_vars fcx) txt with
              | Prs.Read (t, lpos) when lpos = String.length txt ->
                  let ss = Dot (Shift 0, t) in
                  let fb = sub_form ss fb in
                  let f = subst fcx fb in
                  gui.hist <- (gui.cur, gui.mmode) :: gui.hist ;
                  gui.cur <- f ;
                  redisplay ()
              | _ ->
                  gui.stxt#flash (Printf.sprintf "Could not parse: %S" txt) ;
                  ()
              end
          | _ -> gui.stxt#flash "Cancelled witness"
          end ;
          true
      end
      | _ -> false
    end else begin
      let (fcx, f) = unsubst gui.cur in
      match f with
      | Conn (Mark SRC, [_]) when gui.mmode = HAS_SRC ->
          Log.(log DEBUG "Hit enter on a source-marked subformula") ;
          gui.cur <- subst fcx (Rules.unlnk f) ;
          gui.mmode <- NO_MARKS ;
          redisplay () ;
          true
      | _ ->
          let (mrk, mmode) = match gui.mmode with
          | NO_MARKS -> (SRC, HAS_SRC)
          | HAS_SRC -> (SNK, HAS_BOTH)
          | HAS_BOTH ->
              Log.(log ERROR "Apparently both marks exist -- this is impossible!") ;
              raise Silently_fail
          in
          let (f0, m0, h0) = (gui.cur, gui.mmode, gui.hist) in
          try (
            gui.cur <- Rules.make_lnk mrk gui.cur ;
            begin match mmode with
            | HAS_BOTH ->
                gui.cur <- Rules.resolve_mpar gui.cur ;
                gui.hist <- (f0, gui.mmode) :: gui.hist ;
                gui.mmode <- NO_MARKS
            | _ ->
                gui.mmode <- mmode
            end ;
            redisplay () ;
            true
          ) with Rules.Rule_failure _ ->
            gui.stxt#flash "Cannot make this subformula" ;
            gui.cur <- f0 ;
            gui.mmode <- m0 ;
            gui.hist <- h0 ;
            false
    end
  end with
  | Silently_fail -> false
  | Traversal _ -> false)

let key_z mods =
  Traversal.(try begin
    if List.mem `CONTROL mods then begin
      match gui.hist with
      | [] -> false
      | (cur, mmode) :: hist ->
          gui.cur <- cur ;
          gui.mmode <- mmode ;
          gui.hist <- hist ;
          redisplay () ;
          true
    end else false
  end with
  | Traversal _ -> false)

let key_q mods =
  Traversal.(try begin
    if List.mem `CONTROL mods then begin
      match gui.hist with
      | [] ->
          GMain.Main.quit () ; true
      | _ -> begin
        ignore (gui.stxt#push
                  "Quit without saving [y/n]?") ;
        ignore (gui.win#event#connect#key_press ~callback:(y_or_n GMain.Main.quit)) ;
        true
      end
    end else false
  end with
  | Traversal _ -> false)

let () =
  let open GdkKeysyms in
  kmap := List.fold_left begin
    fun kmap (k, act) ->
      Map.add k act kmap
  end Map.empty [
    _Down, key_down ;
    _Up, key_up ;
    _Left, key_left ;
    _Right, key_right ;
    _Return, key_enter ;
    _KP_Enter, key_enter ;
    _z, key_z ;
    _Z, key_z ;
    _q, key_q ;
    _Q, key_q ;
  ]

let startup f =
  gui.cur <- f ;
  let win = GWindow.window
    ~title:(Printf.sprintf "Profound %s" Version.str)
    ~border_width:3
    ~deletable:true () in
  gui.win <- win ;
  win#misc#modify_bg [`NORMAL, `NAME "ivory" ] ;
  ignore (win#event#connect#delete ~callback:(fun _ -> false)) ;
  ignore (win#connect#destroy ~callback:GMain.Main.quit) ;
  let box = GPack.vbox ~packing:win#add () in
  let sw = GBin.scrolled_window
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
    ~packing:box#add () in
  let img = GMisc.image
    ~packing:sw#add_with_viewport () in
  gui.img <- img ;
  ignore (GMisc.separator `HORIZONTAL ~packing:(box#pack ~expand:false) ()) ;
  let sbar = GMisc.statusbar
    ~packing:(box#pack ~expand:false) () in
  let stxt = sbar#new_context "default" in
  gui.stxt <- stxt ;
  ignore (win#event#connect#key_press ~callback:handle_key) ;
  redisplay () ;
  win#show () ;
  GMain.Main.main ()
