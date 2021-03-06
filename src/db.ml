(* Copyright (c) 2022 The Proofgold Lite developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash

let max_entries_in_dir = 65536
let stop_after_byte = 100000000
let defrag_limit = 1024
let dbdir = ref ""

let remove_file_if_exists f =
  if Sys.file_exists f then Sys.remove f

let bootstrapdb dir =
  let fullcall = Printf.sprintf "%s %s/dua" !Config.curl !Config.bootstrapurl in
  let rec bootstrapdb_p d p fullp =
    try
      let n = String.length p in
      let i = String.index p '/' in
      let d2 = Filename.concat d (String.sub p 0 i) in
      if Sys.file_exists d2 then
        if Sys.is_directory d2 then
          bootstrapdb_p d2 (String.sub p (i+1) (n - (i+1))) fullp
        else
          raise (Failure (d2 ^ " is a file not a directory"))
      else
        begin
          Unix.mkdir d2 0b111111000;
          bootstrapdb_p d2 (String.sub p (i+1) (n - (i+1))) fullp
        end
    with Not_found ->
      let fn = Filename.concat d p in
      if not (Sys.file_exists fn) then
        let f = open_out_bin fn in
        let fullcall = Printf.sprintf "%s %s/db/%s" !Config.curl !Config.bootstrapurl fullp in
        let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
        try
          set_binary_mode_in inc true;
          while true do
            let by = input_byte inc in
            output_byte f by
          done
        with _ ->
          ignore (Unix.close_process_full (inc,outc,errc));
          close_out_noerr f
  in
  let bootstrapdb_l l =
    try
      let n = String.length l in
      let i = String.index l '\t' in
      if (i+4 < n && String.sub l (i+1) 3 = "db/") then
        let p = String.sub l (i+4) (n - (i+4)) in
        bootstrapdb_p dir p p
    with Not_found -> ()
  in
  let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
  try
    while true do
      let l = input_line inc in
      bootstrapdb_l l
    done
  with _ ->
    ignore (Unix.close_process_full (inc,outc,errc))

exception NoBootstrapURL

let dbconfig dir =
  dbdir := dir;
  if Sys.file_exists dir then
    if Sys.is_directory dir then
      ()
    else
      raise (Failure (dir ^ " is a file not a directory"))
  else if not !Config.liteserver || !Config.ltcoffline || (not (!Config.independentbootstrap) && !Config.bootstrapurl = "") then
    raise NoBootstrapURL
  else
    begin
      Unix.mkdir dir 0b111111000;
      if !Config.independentbootstrap then
        Utils.forward_from_ltc_block := Some("26c874bca3122a06ec9b6582d4b62f38cfbf9a490da15698fe9a33c7d5a35cde")
      else
        bootstrapdb dir
    end

let use_backup_index d =
  if Sys.file_exists (Filename.concat d "index2") then (** this indicates that something probably went wrong writing into data in this subdir; replace the probably broken index with the backup index2 **)
    Sys.rename (Filename.concat d "index2") (Filename.concat d "index")
  
let load_index d =
  use_backup_index d;
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let c = ref (ch,None) in
    let r = ref [] in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  let (p,c2) = sei_int32 seic c2 in
	  r := (h,Int32.to_int p)::!r;
	  c := c2
	done;
	[]
      with
      | End_of_file ->
	  close_in_noerr ch;
	  !r
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    []

let load_index_to_hashtable ht d =
  use_backup_index d;
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let c = ref (ch,None) in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  let (p,c2) = sei_int32 seic c2 in
	  Hashtbl.add ht h (d,Int32.to_int p);
	  c := c2
	done
      with
      | End_of_file ->
	  close_in_noerr ch
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    ()

let load_index_to_hashtable2 ht d =
  use_backup_index d;
  let dind = Filename.concat d "index" in
  let datf = Filename.concat d "data" in
  if Sys.file_exists dind && Sys.file_exists datf then
    let ch = open_in_bin datf in
    let datfl = in_channel_length ch in
    close_in_noerr ch;
    let ch = open_in_bin dind in
    let c = ref (ch,None) in
    let kl = ref [] in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  let (p,c2) = sei_int32 seic c2 in
          kl := List.merge (fun (_,p1) (_,p2) -> compare p1 p2)
                  !kl
                  [(h,Int32.to_int p)];
	  c := c2
	done;
      with
      | End_of_file ->
         begin
	   close_in_noerr ch;
           let rec put_into_ht (h,p) hl =
             match hl with
             | [] ->
                Hashtbl.add ht h (d,p,datfl - 1);
             | (h2,p2)::hr ->
                Hashtbl.add ht h (d,p,p2 - 1);
                put_into_ht (h2,p2) hr
           in
           match !kl with
           | [] -> ()
           | (h,p)::hr -> put_into_ht (h,p) hr
         end
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    ()

let count_index d =
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let i = (in_channel_length ch) / 24 in
    close_in_noerr ch;
    i
  else
    0

let rec db_iter_subdirs d f =
  if Sys.file_exists d && Sys.is_directory d then
    begin
      f d;
      List.iter
	(fun sd ->
	  let dk = Filename.concat d sd in
	  db_iter_subdirs dk f)
	["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";
	 "10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";
	 "20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";
	 "30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";
	 "40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";
	 "50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";
	 "60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";
	 "70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";
	 "80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";
	 "90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";
	 "a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";
	 "b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";
	 "c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";
	 "d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";
	 "e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";
	 "f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"]
    end

let input_int32 ch =
  let m3 = input_byte ch in
  let m2 = input_byte ch in
  let m1 = input_byte ch in
  let m0 = input_byte ch in
  Int32.logor
    (Int32.shift_left (Int32.of_int m3) 24)
    (Int32.of_int ((m2 lsl 16) lor (m1 lsl 8) lor m0))
  
let input_hashval ch =
  let x7 = input_int32 ch in
  let x6 = input_int32 ch in
  let x5 = input_int32 ch in
  let x4 = input_int32 ch in
  let x3 = input_int32 ch in
  let x2 = input_int32 ch in
  let x1 = input_int32 ch in
  let x0 = input_int32 ch in
  (x7,x6,x5,x4,x3,x2,x1,x0)
  
let find_in_index d k =
  use_backup_index d;
  let dind = Filename.concat d "index" in
  if Sys.file_exists dind then
    let ch = open_in_bin dind in
    let l = in_channel_length ch in
    let b = ref 0 in
    let e = ref (l / 36) in
    let r = ref None in
    begin
      try
	while !r = None do
	  if !b < !e then
	    let m = !b + (!e - !b) / 2 in
	    begin
	      seek_in ch (m*36);
              let h = input_hashval ch in
	      let chk = compare h k in
	      if chk = 0 then
		let p = input_int32 ch in
                r := Some(Int32.to_int p)
	      else if chk > 0 then
		e := m
	      else
		b := m+1
	    end
	  else
	    raise End_of_file
	done;
	close_in_noerr ch;
	match !r with
	| Some(p) -> p
	| None -> raise Not_found
      with
      | End_of_file ->
	  close_in_noerr ch;
	  raise Not_found
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    raise Not_found

let count_deleted d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let i = (in_channel_length ch) / 32 in
    close_in_noerr ch;
    i
  else
    0

let find_in_deleted d k =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    let r = ref false in
    begin
      try
	while not !r do
	  let (h,c2) = sei_hashval seic !c in
	  if h = k then r := true;
	  c := c2
	done;
	close_in_noerr ch;
	()
      with
      | End_of_file ->
	  close_in_noerr ch;
	  raise Not_found
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    raise Not_found

let load_deleted d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    let r = ref [] in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  r := h::!r;
	  c := c2
	done;
	[]
      with
      | End_of_file ->
	close_in_noerr ch;
	!r
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    []

let load_deleted_to_hashtable ht d =
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    let ch = open_in_bin ddel in
    let c = ref (ch,None) in
    begin
      try
	while true do
	  let (h,c2) = sei_hashval seic !c in
	  Hashtbl.add ht h ();
	  c := c2
	done
      with
      | End_of_file ->
	  close_in_noerr ch
      | exc ->
	  close_in_noerr ch;
	  raise exc
    end
  else
    ()

let undelete d k =
  let dl = load_deleted d in
  let ddel = Filename.concat d "deleted" in
  let chd = open_out_gen [Open_wronly;Open_trunc;Open_creat;Open_binary] 0b110110000 ddel in
  try
    List.iter
      (fun h ->
	if not (h = k) then
	  let cd2 = seo_hashval seoc h (chd,None) in
	  seocf cd2)
      dl;
    close_out_noerr chd
  with exc ->
    close_out_noerr chd;
    raise exc

let rec dbfind_a d i k kh =
  try
    let p = find_in_index d k in
    (d,p)
  with Not_found ->
    if i < 32 then
      let dk' = Filename.concat d (String.sub kh i 2) in
      try
	if Sys.is_directory dk' then
	  dbfind_a dk' (i+2) k kh
	else
	  raise Not_found
      with _ -> raise Not_found
    else
      raise Not_found

let dbfind d k =
  let fd = Filename.concat !dbdir d in
  try
    if Sys.is_directory fd then
      dbfind_a fd 0 k (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  with _ -> raise Not_found

let file_length f =
  if Sys.file_exists f then
    let ch = open_in_bin f in
    let l = in_channel_length ch in
    close_in_noerr ch;
    l
  else
    0

let rec dbfind_next_space_a d i k =
  use_backup_index d;
  if count_index d < max_entries_in_dir then
    let dd = Filename.concat d "data" in
    let p = file_length dd in
    if p < stop_after_byte then
      (d,p)
    else
      dbfind_next_space_b d i k
  else
    dbfind_next_space_b d i k
and dbfind_next_space_b d i k =
  let dk' = Filename.concat d (String.sub k i 2) in
  if Sys.file_exists dk' then
    if Sys.is_directory dk' then
      dbfind_next_space_a dk' (i+2) k
    else
      raise (Failure (dk' ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir dk' 0b111111000;
      (dk',0)
    end

let dbfind_next_space d k =
  let fd = Filename.concat !dbdir d in
  if Sys.file_exists fd then
    if Sys.is_directory fd then
      dbfind_next_space_a fd 0 (hashval_hexstring k)
    else
      raise (Failure (fd ^ " is a file not a directory"))
  else
    begin
      Unix.mkdir fd 0b111111000;
      (fd,0)
    end

let defrag d seival seoval =
  let ind = ref (load_index d) in
  let ddel = Filename.concat d "deleted" in
  if Sys.file_exists ddel then
    begin
      let del : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
      load_deleted_to_hashtable del d;
      let indf = Filename.concat d "index" in
      let datf = Filename.concat d "data" in
      let chd = open_in_bin datf in
      let l = in_channel_length chd in
      let dat =
	ref (List.map
	       (fun (k,p) ->
		 if Hashtbl.mem del k then
		   None
		 else if p < l then
		   begin
		     seek_in chd p;
		     let (v,_) = seival (chd,None) in
		     Some(v)
		   end
		 else
		   begin
		     close_in_noerr chd;
		     raise (Failure ("Corrupted data file " ^ datf))
		   end)
	       !ind)
      in
      close_in_noerr chd;
      remove_file_if_exists ddel;
      let chd = open_out_gen [Open_wronly;Open_trunc;Open_binary] 0b110110000 datf in
      let newind = ref [] in
      try
	while not (!ind = []) do
	  match (!ind,!dat) with
	  | ((k,_)::ir,Some(v)::dr) ->
	      ind := ir;
	      dat := dr;
	      if not (Hashtbl.mem del k) then
		let p = pos_out chd in
		newind := List.merge (fun (h',p') (k',q') -> compare h' k') !newind [(k,p)];
		let cd2 = seoval v (chd,None) in
		seocf cd2;
	  | ((k,_)::ir,None::dr) ->
	      ind := ir;
	      dat := dr
	  | _ ->
	      raise (Failure ("impossible"))
	done;
	let chi = open_out_gen [Open_wronly;Open_trunc;Open_binary] 0b110110000 indf in
	begin
	  try
	    List.iter (fun (k,p) ->
	      let ci2 = seo_hashval seoc k (chi,None) in
	      let ci2 = seo_int32 seoc (Int32.of_int p) ci2 in
	      seocf ci2)
	      !newind;
	    close_out_noerr chi;
	    close_out_noerr chd
	  with exc ->
	    close_out_noerr chi;
	    raise exc
	end
      with exc ->
	close_out_noerr chd;
	raise exc
    end

module type dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
    val dbpurge : unit -> unit
  end

module type dbtypebincp = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
    val dbpurge : unit -> unit
    val dbbincp : hashval -> Buffer.t -> unit
  end
    
module type dbtypekeyiter = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  sig
    val dbinit : unit -> unit
    val dbget : hashval -> M.t
    val dbexists : hashval -> bool
    val dbput : hashval -> M.t -> unit
    val dbdelete : hashval -> unit
    val dbpurge : unit -> unit
    val dbkeyiter : (hashval -> unit) -> unit
  end

module Dbbasic : dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let cache1 : (hashval,M.t) Hashtbl.t ref = ref (Hashtbl.create !Config.db_max_in_cache)
    let cache2 : (hashval,M.t) Hashtbl.t ref = ref (Hashtbl.create !Config.db_max_in_cache)

    let add_to_cache (k,v) =
      if Hashtbl.length !cache1 < !Config.db_max_in_cache then
	Hashtbl.add !cache1 k v
      else
	let h = !cache2 in
	cache2 := !cache1;
	Hashtbl.clear h;
	Hashtbl.add h k v;
	cache1 := h

    let del_from_cache k =
      Hashtbl.remove !cache1 k;
      Hashtbl.remove !cache2 k

    let dbinit () = () (*** does nothing in Dbbasic; on the contrary Dbbasic2 loads the index into RAM ***)

    let dbexists k =
      try
	if Hashtbl.mem !cache1 k then
	  true
	else if Hashtbl.mem !cache2 k then
	  begin
	    let v = Hashtbl.find !cache2 k in
	    add_to_cache (k,v);
	    true
	  end
	else
	  begin
	    let (di,_) = withlock (fun () -> dbfind M.basedir k) in
	    try
	      withlock (fun () -> find_in_deleted di k);
	      raise Exit
	    with
	    | Not_found ->
	       true
	  end
      with
      | Exit -> false
      | Not_found -> false

    let dbget k =
      try
	Hashtbl.find !cache1 k
      with Not_found ->
	try
	  let v = Hashtbl.find !cache2 k in
	  withlock (fun () -> add_to_cache (k,v));
	  v
	with Not_found ->
              let (di,p) = withlock (fun () -> dbfind M.basedir k) in
              try
	        withlock (fun () -> find_in_deleted di k);
	        raise Exit
              with
              | Exit -> raise Not_found
              | Not_found ->
	         let datf = Filename.concat di "data" in
	         withlock
	           (fun () ->
	             if Sys.file_exists datf then
	               let c = open_in_bin datf in
	               let l = in_channel_length c in
	               try
		         if p >= l then
		           begin
		             close_in_noerr c;
		             raise (Failure ("Corrupted data file " ^ datf))
		           end;
		         seek_in c p;
		         let (v,_) = M.seival (c,None) in
		         close_in_noerr c;
		         add_to_cache (k,v);
		         v
	               with exc ->
		         close_in_noerr c;
		         raise exc
	             else
	               raise Not_found)

    let dbput k v =
      try
	withlock
	  (fun () ->
	    let (di,p) = dbfind M.basedir k in
	    try
	      find_in_deleted di k;
	      undelete di k
	    with Not_found -> () (*** otherwise, it's already there, do nothing ***)
	  )
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	let indl = withlock (fun () -> load_index d') in
	let indl2 = List.merge (fun (h',p') (k',q') -> compare h' k') (List.rev indl) [(k,p)] in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
	    close_out_noerr ch;
            let indexfilename1 = Filename.concat d' "index" in
            let indexfilename2 = Filename.concat d' "index2" in
            if Sys.file_exists indexfilename1 then Sys.rename indexfilename1 indexfilename2;
	    let ch = open_out_bin indexfilename1 in
	    List.iter
	      (fun (h,q) ->
		let c = seo_hashval seoc h (ch,None) in
		let c = seo_int32 seoc (Int32.of_int q) c in
		seocf c)
	      indl2;
	    close_out_noerr ch;
            if Sys.file_exists indexfilename2 then Sys.remove indexfilename2)

    let dbdelete k =
      try
	let (di,p) = withlock (fun () -> dbfind M.basedir k) in
	try
	  withlock (fun () -> find_in_deleted di k); (*** if has already been deleted, do nothing ***)
	with Not_found ->
	  let ddel = Filename.concat di "deleted" in
	  withlock
	    (fun () ->
	      let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	      let c = seo_hashval seoc k (ch,None) in
	      seocf c;
	      close_out_noerr ch);
	  del_from_cache k;
	  let nd = count_deleted di in
	  if nd = count_index di then (*** easy case: all entries in the dir have been deleted; a common case would likely be when a dir has 1 entry and it gets deleted ***)
	    begin
	      remove_file_if_exists ddel;
	      remove_file_if_exists (Filename.concat di "index");
	      remove_file_if_exists (Filename.concat di "data")
	    end
	  else if count_deleted di > defrag_limit then
	    withlock (fun () -> defrag di M.seival M.seoval);
      with
      | Not_found -> () (*** not an entry, do nothing ***)

    let dbpurge () =
      withlock
	(fun () ->
	  db_iter_subdirs (Filename.concat !dbdir M.basedir) (fun di -> defrag di M.seival M.seoval))

  end

module Dbbasic2 : dbtype = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let indextable : (hashval,(string * int)) Hashtbl.t = Hashtbl.create 10000
    let deletedtable : (hashval,unit) Hashtbl.t = Hashtbl.create 100

    let rec dbinit_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      dbinit_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
	  load_index_to_hashtable indextable d;
	  load_deleted_to_hashtable deletedtable d
	end

    let dbinit () =
      dbinit_a (Filename.concat !dbdir M.basedir)

    let dbexists k =
      Hashtbl.mem indextable k && not (Hashtbl.mem deletedtable k)

    let dbget k =
      let (di,p) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l then
		  begin
		    close_in_noerr c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
		let (v,_) = M.seival (c,None) in
		close_in_noerr c;
		v
	      with exc ->
		close_in_noerr c;
		raise exc
	    else
	      raise Not_found)

    let dbput k v =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  begin
	    Hashtbl.remove deletedtable k;
	    withlock (fun () -> undelete di k)
	  end
	else
	  () (*** it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
	    close_out_noerr ch;
            let indexfilename1 = Filename.concat d' "index" in
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 indexfilename1 in
	    let c = seo_hashval seoc k (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int p) c in
	    seocf c;
	    close_out_noerr ch;
	    Hashtbl.add indextable k (d',p)
	  )

    let dbdelete k =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  () (*** if has already been deleted, do nothing ***)
	else
	  let ddel = Filename.concat di "deleted" in
	  withlock
	    (fun () ->
	      let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	      let c = seo_hashval seoc k (ch,None) in
	      seocf c;
	      close_out_noerr ch;
	      Hashtbl.add deletedtable k ())
      with
      | Not_found -> () (*** not an entry, do nothing ***)

    let dbpurge () =
      withlock
	(fun () ->
	  db_iter_subdirs (Filename.concat !dbdir M.basedir) (fun di -> defrag di M.seival M.seoval))

  end

module Dbbasic2bincp : dbtypebincp = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let indextable : (hashval,(string * int * int)) Hashtbl.t = Hashtbl.create 10000
    let deletedtable : (hashval,unit) Hashtbl.t = Hashtbl.create 100

    let rec dbinit_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      dbinit_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
	  load_index_to_hashtable2 indextable d;
	  load_deleted_to_hashtable deletedtable d
	end

    let dbinit () =
      dbinit_a (Filename.concat !dbdir M.basedir)

    let dbexists k =
      Hashtbl.mem indextable k && not (Hashtbl.mem deletedtable k)

    let dbget k =
      let (di,p,_) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l then
		  begin
		    close_in_noerr c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
		let (v,_) = M.seival (c,None) in
		close_in_noerr c;
		v
	      with exc ->
		close_in_noerr c;
		raise exc
	    else
	      raise Not_found)

    let dbbincp k sb =
      let (di,p,endpt) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l || endpt >= l || endpt < p then
		  begin
		    close_in_noerr c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
                for i = p to endpt do
                  Buffer.add_char sb (Char.chr (input_byte c))
                done;
                close_in_noerr c
	      with exc ->
		close_in_noerr c;
		raise exc
	    else
	      raise Not_found)

    let dbput k v =
      try
	let (di,p,_) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  begin
	    Hashtbl.remove deletedtable k;
	    withlock (fun () -> undelete di k)
	  end
	else
	  () (*** it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
            let endpt = pos_out ch in
	    close_out_noerr ch;
            let indexfilename1 = Filename.concat d' "index" in
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 indexfilename1 in
	    let c = seo_hashval seoc k (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int p) c in
	    seocf c;
	    close_out_noerr ch;
	    Hashtbl.add indextable k (d',p,p + endpt - 1)
	  )

    let dbdelete k =
      try
	let (di,p,_) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  () (*** if has already been deleted, do nothing ***)
	else
	  let ddel = Filename.concat di "deleted" in
	  withlock
	    (fun () ->
	      let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	      let c = seo_hashval seoc k (ch,None) in
	      seocf c;
	      close_out_noerr ch;
	      Hashtbl.add deletedtable k ())
      with
      | Not_found -> () (*** not an entry, do nothing ***)

    let dbpurge () =
      withlock
	(fun () ->
	  db_iter_subdirs (Filename.concat !dbdir M.basedir) (fun di -> defrag di M.seival M.seoval))

  end
    
module Dbbasic2keyiter : dbtypekeyiter = functor (M:sig type t val basedir : string val seival : (seict -> t * seict) val seoval : (t -> seoct -> seoct) end) ->
  struct
    let mutexdb : Mutex.t = Mutex.create()

    let withlock f =
      try
	Mutex.lock mutexdb;
	let r = f() in
	Mutex.unlock mutexdb;
	r
      with e ->
	Mutex.unlock mutexdb;
	raise e

    let indextable : (hashval,(string * int)) Hashtbl.t = Hashtbl.create 10000
    let deletedtable : (hashval,unit) Hashtbl.t = Hashtbl.create 100

    let rec dbinit_a d =
      if Sys.file_exists d && Sys.is_directory d then
	begin
	  List.iter
	    (fun h ->
	      dbinit_a (Filename.concat d h))
	    ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"];
	  load_index_to_hashtable indextable d;
	  load_deleted_to_hashtable deletedtable d
	end

    let dbinit () =
      dbinit_a (Filename.concat !dbdir M.basedir)

    let dbexists k =
      Hashtbl.mem indextable k && not (Hashtbl.mem deletedtable k)

    let dbget k =
      let (di,p) = Hashtbl.find indextable k in
      if Hashtbl.mem deletedtable k then
	raise Not_found
      else
	let datf = Filename.concat di "data" in
	withlock
	  (fun () ->
	    if Sys.file_exists datf then
	      let c = open_in_bin datf in
	      let l = in_channel_length c in
	      try
		if p >= l then
		  begin
		    close_in_noerr c;
		    raise (Failure ("Corrupted data file " ^ datf))
		  end;
		seek_in c p;
		let (v,_) = M.seival (c,None) in
		close_in_noerr c;
		v
	      with exc ->
		close_in_noerr c;
		raise exc
	    else
	      raise Not_found)

    let dbput k v =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  begin
	    Hashtbl.remove deletedtable k;
	    withlock (fun () -> undelete di k)
	  end
	else
	  () (*** it's already there, do nothing ***)
      with Not_found ->
	let (d',p) = withlock (fun () -> dbfind_next_space M.basedir k) in
	withlock
	  (fun () ->
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "data") in
	    let c = M.seoval v (ch,None) in
	    seocf c;
	    close_out_noerr ch;
	    let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 (Filename.concat d' "index") in
	    let c = seo_hashval seoc k (ch,None) in
	    let c = seo_int32 seoc (Int32.of_int p) c in
	    seocf c;
	    close_out_noerr ch;
	    Hashtbl.add indextable k (d',p)
	  )

    let dbdelete k =
      try
	let (di,p) = Hashtbl.find indextable k in
	if Hashtbl.mem deletedtable k then
	  () (*** if has already been deleted, do nothing ***)
	else
	  let ddel = Filename.concat di "deleted" in
	  withlock
	    (fun () ->
	      let ch = open_out_gen [Open_append;Open_creat;Open_binary] 0b110110000 ddel in
	      let c = seo_hashval seoc k (ch,None) in
	      seocf c;
	      close_out_noerr ch;
	      Hashtbl.add deletedtable k ())
      with
      | Not_found -> () (*** not an entry, do nothing ***)

    let dbpurge () =
      withlock
	(fun () ->
	  db_iter_subdirs (Filename.concat !dbdir M.basedir) (fun di -> defrag di M.seival M.seoval))

    let dbkeyiter f =
      Hashtbl.iter
	(fun k _ -> if not (Hashtbl.mem deletedtable k) then f k)
	indextable

  end


module DbBlacklist = Dbbasic2 (struct type t = bool let basedir = "blacklist" let seival = sei_bool seic let seoval = seo_bool seoc end)

module DbArchived = Dbbasic2 (struct type t = bool let basedir = "archived" let seival = sei_bool seic let seoval = seo_bool seoc end)
