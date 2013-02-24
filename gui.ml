(******************************************************************************)
(* Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>                     *)
(* Copyright (C) 2013  INRIA                                                  *)
(* See LICENSE for licensing details.                                         *)
(******************************************************************************)

open Batteries
open Syntax


let read_term main_win x cx =
  let dwin = GWindow.dialog
    ~parent:main_win
    ~title:"Witness input"
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
    ~text:(Printf.sprintf "Enter a witness for " ^ (Idt.src_rep x) ^ ":")
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
      begin match Syntax_prs.parse_term cx txt with
      | Ok t -> Some t
      | _ -> None
      end
  | _ -> None
  end      
  
