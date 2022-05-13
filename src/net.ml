(* Copyright (c) 2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Utils
open Ser
open Hashaux
open Sha256
open Hash
open Db

let shutdown_close s =
  try
    Unix.shutdown s Unix.SHUTDOWN_ALL;
    Unix.close s;
  with exc ->
    try
      Unix.close s;
    with _ ->
      ()

(** associate (lbk,ltx) -- litecoin block id, litcoin burn tx id -- with various info.
 outlinevals associates pair with
   proofgold block id, litecoin median time, litoshis burned, first litecoin utxo being spent by burn tx, optional previous (lbh,ltx) pair, stake modifier (for the next block) and proofgold block height
   This is all data that can be computed via the ltc blockchain.
 validheadervals associates pair with (if proofgold header has been validated and all previous headers have been validated)
   targetinfo, timestamp, newledgerroot, newtheorytreeroot, newsignatreeroot
   This information is all in the header, so the hash table is to make it easily accessible and to record that previous headers have been validated.
 validblockvals associates pair with () (if proofgold block has been validated and all previous blocks have been validated)
   just to record that we have the block (header and delta) and all have been validated.
 outlinesucc associates pair with several pairs that point back to this one.
 blockburns associates a proofgold block id with all the (lbh,ltx) burns supporting it.
    Typically there will be only one such burn, but this cannot be enforced.
 **)

module Db_outlinevals = Dbbasic (struct type t = hashval * int64 * int64 * (hashval * int32) * (hashval * hashval) option * hashval * int64 let basedir = "outlinevals" let seival = sei_prod7 sei_hashval sei_int64 sei_int64 (sei_prod sei_hashval sei_int32) (sei_option (sei_prod sei_hashval sei_hashval)) sei_hashval sei_int64 seic let seoval = seo_prod7 seo_hashval seo_int64 seo_int64 (seo_prod seo_hashval seo_int32) (seo_option (seo_prod seo_hashval seo_hashval)) seo_hashval seo_int64 seoc end)

module Db_validheadervals = Dbbasic (struct type t = Z.t * int64 * hashval * hashval option * hashval option let basedir = "validheadervals" let seival = sei_prod5 sei_big_int_256 sei_int64 sei_hashval (sei_option sei_hashval) (sei_option sei_hashval) seic let seoval = seo_prod5 seo_big_int_256 seo_int64 seo_hashval (seo_option seo_hashval) (seo_option seo_hashval) seoc end)

module Db_validblockvals = Dbbasic (struct type t = bool let basedir = "validblockvals" let seival = sei_bool seic let seoval = seo_bool seoc end)

module Db_outlinesucc = Dbbasic (struct type t = hashval * hashval let basedir = "outlinesucc" let seival = sei_prod sei_hashval sei_hashval seic let seoval = seo_prod seo_hashval seo_hashval seoc end)

module Db_blockburns = Dbbasic (struct type t = (hashval * hashval) let basedir = "blockburns" let seival = sei_prod sei_hashval sei_hashval seic let seoval = seo_prod seo_hashval seo_hashval seoc end)

let get_outlinesucc (h,k) =
  let hk = hashpair h k in
  let osl = ref [] in
  let i = ref 0l in
  try
    while true do
      let (lbk,ltx) = Db_outlinesucc.dbget (hashtag hk !i) in
      osl := (lbk,ltx) :: !osl;
      i := Int32.add !i 1l
    done;
    raise Exit
  with _ -> !osl

let insert_outlinesucc (h,k) (lbk1,ltx1) =
  let hk = hashpair h k in
  let i = ref 0l in
  try
    while true do
      let (lbk,ltx) = Db_outlinesucc.dbget (hashtag hk !i) in
      if (lbk,ltx) = (lbk1,ltx1) then raise Exit;
      i := Int32.add !i 1l
    done
  with
  | Not_found -> Db_outlinesucc.dbput (hashtag hk !i) (lbk1,ltx1)
  | _ -> ()

let get_blockburns h =
  let bbl = ref [] in
  let i = ref 0l in
  try
    while true do
      let (lbk,ltx) = Db_blockburns.dbget (hashtag h !i) in
      bbl := (lbk,ltx) :: !bbl;
      i := Int32.add !i 1l
    done;
    raise Exit
  with _ -> !bbl

let insert_blockburn h (lbk1,ltx1) =
  let i = ref 0l in
  try
    while true do
      let (lbk,ltx) = Db_blockburns.dbget (hashtag h !i) in
      if (lbk,ltx) = (lbk1,ltx1) then raise Exit;
      i := Int32.add !i 1l
    done
  with
  | Not_found -> Db_blockburns.dbput (hashtag h !i) (lbk1,ltx1)
  | _ -> ()
           
let missingheaders = ref [];;
let missingdeltas = ref [];;

let netblkh : int64 ref = ref 0L

type msgtype =
  | Version
  | Verack
  | Addr
  | Inv
  | GetSTx
  | GetHeaders
  | GetHeader
  | GetBlock
  | GetBlockdelta
  | STx
  | Block
  | Headers
  | Blockdelta
  | GetAddr
  | Alert
  | Ping
  | Pong
  | GetCTreeElement
  | GetHConsElement
  | GetAsset
  | CTreeElement
  | HConsElement
  | Asset
  | GetInvNbhd
  | GetElementsBelow
  | CompleteCTree
  | CompleteHList
  | POWChallenge
  | POWChallengeResponse

let msgtype_of_int i =
  try
    List.nth
      [Version;Verack;Addr;Inv;GetSTx;GetHeaders;GetHeader;GetBlock;GetBlockdelta;
       STx;Block;Headers;Blockdelta;GetAddr;Alert;Ping;Pong;
       GetCTreeElement;GetHConsElement;GetAsset;CTreeElement;HConsElement;Asset;GetInvNbhd;
       GetElementsBelow;CompleteCTree;CompleteHList;
       POWChallenge;POWChallengeResponse]
      i
  with Failure(_) -> raise Not_found

let int_of_msgtype mt =
  match mt with
  | Version -> 0
  | Verack -> 1
  | Addr -> 2
  | Inv -> 3
  | GetSTx -> 4
  | GetHeaders -> 5
  | GetHeader -> 6
  | GetBlock -> 7
  | GetBlockdelta -> 8
  | STx -> 9
  | Block -> 10
  | Headers -> 11
  | Blockdelta -> 12
  | GetAddr -> 13
  | Alert -> 14
  | Ping -> 15
  | Pong -> 16
  | GetCTreeElement -> 17
  | GetHConsElement -> 18
  | GetAsset -> 19
  | CTreeElement -> 20
  | HConsElement -> 21
  | Asset -> 22
  | GetInvNbhd -> 23
  | GetElementsBelow -> 24
  | CompleteCTree -> 25
  | CompleteHList -> 26
  | POWChallenge -> 27
  | POWChallengeResponse -> 28

let inv_of_msgtype mt =
  try
    int_of_msgtype
      (match mt with
      | GetSTx -> STx
      | GetBlock -> Block
      | GetHeaders -> Headers
      | GetHeader -> Headers
      | GetBlockdelta -> Blockdelta
      | GetCTreeElement -> CTreeElement
      | GetHConsElement -> HConsElement
      | GetAsset -> Asset
      | _ -> raise Not_found)
  with Not_found -> (-1)

let string_of_msgtype mt =
  match mt with
  | Version -> "Version"
  | Verack -> "Verack"
  | Addr -> "Addr"
  | Inv -> "Inv"
  | GetSTx -> "GetSTx"
  | GetHeaders -> "GetHeaders"
  | GetHeader -> "GetHeader"
  | GetBlock -> "GetBlock"
  | GetBlockdelta -> "GetBlockdelta"
  | STx -> "STx"
  | Block -> "Block"
  | Headers -> "Headers"
  | Blockdelta -> "Blockdelta"
  | GetAddr -> "GetAddr"
  | Alert -> "Alert"
  | Ping -> "Ping"
  | Pong -> "Pong"
  | GetCTreeElement -> "GetCTreeElement"
  | GetHConsElement -> "GetHConsElement"
  | GetAsset -> "GetAsset"
  | CTreeElement -> "CTreeElement"
  | HConsElement -> "HConsElement"
  | Asset -> "Asset"
  | GetInvNbhd -> "GetInvNbhd"
  | GetElementsBelow -> "GetElementsBelow"
  | CompleteCTree -> "CompleteCTree"
  | CompleteHList -> "CompleteHList"
  | POWChallenge -> "POWChallenge"
  | POWChallengeResponse -> "POWChallengeResponse"

let myaddr () =
  match !Config.ip with
  | Some(ip) -> 
      if !Config.ipv6 then
	"[" ^ ip ^ "]:" ^ (string_of_int !Config.port)
      else
	ip ^ ":" ^ (string_of_int !Config.port)
  | None ->
      if !Config.socks = None then (** if socks is not set, then do not reveal the hidden service address **)
	""
      else
	match !Config.onion with
	| None -> ""
	| Some(onionaddr) ->
           match !Config.proxyip with
           | Some (ip) ->
	      ip ^ ":" ^ (string_of_int !Config.port)
           | None ->
              onionaddr ^ ":" ^ (string_of_int !Config.onionremoteport)

let fallbacknodes = [
(* ":21805" *)
]

let testnetfallbacknodes = [
(* ":21804" *)
]

let getfallbacknodes () =
  if !Config.testnet then
    testnetfallbacknodes
  else
    fallbacknodes

exception BannedPeer
let bannedpeers : (string,unit) Hashtbl.t = Hashtbl.create 1000
let banpeer n = Hashtbl.add bannedpeers n ()
let clearbanned () = Hashtbl.clear bannedpeers

let knownpeers : (string,int64) Hashtbl.t = Hashtbl.create 1000
let newpeers : string list ref = ref []

let addknownpeer lasttm n =
  if not (n = "") && not (n = myaddr()) && not (List.mem n (getfallbacknodes())) && not (Hashtbl.mem bannedpeers n) then
    try
      let _ (* oldtm *) = Hashtbl.find knownpeers n in
      Hashtbl.replace knownpeers n lasttm
    with Not_found ->
      Hashtbl.add knownpeers n lasttm;
      let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
      if Sys.file_exists peerfn then
	let s = open_out_gen [Open_append;Open_wronly] 0o644 peerfn in
	output_string s n;
	output_char s '\n';
	output_string s (Int64.to_string lasttm);
	output_char s '\n';
	close_out_noerr s
      else
	let s = open_out peerfn in
	output_string s n;
	output_char s '\n';
	output_string s (Int64.to_string lasttm);
	output_char s '\n';
	close_out_noerr s

let removeknownpeer n =
  if not (n = "") && not (n = myaddr()) && not (List.mem n (getfallbacknodes())) then
    Hashtbl.remove knownpeers n

let getknownpeers () =
  let cnt = ref 0 in
  let peers = ref [] in
  let currtm = Int64.of_float (Unix.time()) in
  Hashtbl.iter (fun n lasttm -> if !cnt < 1000 && Int64.sub currtm lasttm < 604800L then (incr cnt; peers := n::!peers)) knownpeers;
  !peers

let loadknownpeers () =
  let currtm = Int64.of_float (Unix.time()) in
  let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
  let kcnt = ref 0 in
  if Sys.file_exists peerfn then
    let s = open_in peerfn in
    try
      while true do
	let n = input_line s in
	let lasttm = Int64.of_string (input_line s) in
	if Int64.sub currtm lasttm < 604800L then
          begin
            try
              let lasttm2 = Hashtbl.find knownpeers n in
              if !kcnt = 0 then kcnt := 1; (* so it appears we know at least one peer since we do *)
              if lasttm > lasttm2 then Hashtbl.replace knownpeers n lasttm
            with Not_found ->
              incr kcnt; Hashtbl.replace knownpeers n lasttm
          end
      done;
      !kcnt
    with End_of_file -> (close_in_noerr s; !kcnt)
  else
    0

let saveknownpeers () =
  let peerfn = Filename.concat (if !Config.testnet then Filename.concat !Config.datadir "testnet" else !Config.datadir) "peers" in
  let s = open_out peerfn in
  Hashtbl.iter
    (fun n lasttm ->
      if not (n = "") then
        begin
          output_string s n;
          output_char s '\n';
          output_string s (Int64.to_string lasttm);
          output_char s '\n'
        end)
    knownpeers;
  close_out_noerr s

exception GettingRemoteData
exception RequestRejected
exception IllformedMsg
exception ProtocolViolation of string
exception SelfConnection
exception DupConnection

let openlistener ip port numconns =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let ia = Unix.inet_addr_of_string ip in
  Unix.bind s (Unix.ADDR_INET(ia, port));
  Unix.listen s numconns;
  s

let openonionlistener onionaddr localport remoteport numconns =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.bind s (Unix.ADDR_INET(Unix.inet_addr_loopback, localport));
  Unix.listen s numconns;
  s

let connectpeer ip port =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  try
    let ia = Unix.inet_addr_of_string ip in
    Unix.connect s (Unix.ADDR_INET(ia, port));
    s
  with exn ->
    Unix.close s;
    raise exn

let log_msg m =
  let h = string_hexstring m in
  log_string (Printf.sprintf "\nmsg: %s\n" h)

let connectonionpeer proxyport onionaddr port =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  try
    Unix.connect s (Unix.ADDR_INET(Unix.inet_addr_loopback, proxyport));
    let sin = Unix.in_channel_of_descr s in
    let sout = Unix.out_channel_of_descr s in
    set_binary_mode_in sin true;
    set_binary_mode_out sout true;
    output_byte sout 4;
    output_byte sout 1;
    (** port, big endian **)
    output_byte sout ((port asr 8) land 255);
    output_byte sout (port land 255);
    (** fake ip for socks4a **)
    output_byte sout 0;
    output_byte sout 0;
    output_byte sout 0;
    output_byte sout 1;
    output_byte sout 0; (** empty string **)
    (** onion addr **)
    for i = 0 to String.length onionaddr - 1 do
      output_byte sout (Char.code onionaddr.[i])
    done;
    output_byte sout 0; (** terminate string **)
    flush sout;
    try
      let by = input_byte sin in
      if not (by = 0) then raise (Failure "server did not give initial null byte");
      let by = input_byte sin in
      if by = 0x5b then raise (Failure "request rejected or failed");
      if by = 0x5c then raise (Failure "request failed because client is not running identd (or not reachable from the server)");
      if by = 0x5d then raise (Failure "request failed because client's identd could not confirm the user ID string in the request");
      if not (by = 0x5a) then raise (Failure "bad status byte from server");
      let rport1 = input_byte sin in
      let rport0 = input_byte sin in
      let rport = rport1 * 256 + rport0 in
      let ip0 = input_byte sin in
      let ip1 = input_byte sin in
      let ip2 = input_byte sin in
      let ip3 = input_byte sin in
      log_msg (Printf.sprintf "Connected to %s:%d via socks4a with %d.%d.%d.%d:%d\n" onionaddr port ip0 ip1 ip2 ip3 rport);
      (s,sin,sout)
    with e ->
      Unix.close s;
      log_msg (Printf.sprintf "Failed to connect to %s:%d : %s\n" onionaddr port (Printexc.to_string e));
      raise Exit
  with exn ->
    Unix.close s;
    raise exn

let extract_ipv4 ip =
  let x = Array.make 4 0 in
  let j = ref 0 in
  for i = 0 to String.length ip - 1 do
    let c = Char.code ip.[i] in
    if c = 46 && !j < 3 then
      incr j
    else if c >= 48 && c < 58 then
      x.(!j) <- x.(!j) * 10 + (c-48)
    else
      raise (Failure "Not an ipv4 address")
  done;
  (x.(0),x.(1),x.(2),x.(3))

let rec extract_ipv4_and_port ipp i l =
  if i+2 < l then
    if ipp.[i] = ':' then
      (String.sub ipp 0 i,int_of_string (String.sub ipp (i+1) (l-(i+1))))
    else
      extract_ipv4_and_port ipp (i+1) l
  else
    raise (Failure "not an ipv4 address with a port number")

let rec extract_ipv6_and_port ipp i l =
  if i+3 < l then
    if ipp.[i] = ']' then
      if ipp.[i+1] = ':' then
	(String.sub ipp 0 i,int_of_string (String.sub ipp (i+2) (l-(i+2))))
      else
	raise (Failure "not an ipv4 address with a port number")
    else
      extract_ipv6_and_port ipp (i+1) l
  else
    raise (Failure "not an ipv6 address with a port number")

let extract_ip_and_port ipp =
  let l = String.length ipp in
  if l = 0 then
    raise (Failure "Not an ip address with a port number")
  else if ipp.[0] = '[' then
    let (ip,port) = extract_ipv6_and_port ipp 1 l in
    (ip,port,true)
  else
    let (ip,port) = extract_ipv4_and_port ipp 0 l in
    (ip,port,false)

let extract_onion_and_port n =
  let dot = String.index n '.' in
  let col = String.index n ':' in
  if dot < col && String.sub n dot (col - dot) = ".onion" then
    begin
      try
	(String.sub n 0 col,int_of_string (String.sub n (col+1) (String.length n - (col+1))))
      with _ -> raise Not_found
    end
  else
    raise Not_found

let connectpeer_socks4 proxyport ip port =
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  try
    Unix.connect s (Unix.ADDR_INET(Unix.inet_addr_loopback, proxyport));
    let sin = Unix.in_channel_of_descr s in
    let sout = Unix.out_channel_of_descr s in
    set_binary_mode_in sin true;
    set_binary_mode_out sout true;
    output_byte sout 4;
    output_byte sout 1;
    (** port, big endian **)
    output_byte sout ((port asr 8) land 255);
    output_byte sout (port land 255);
    (** ip **)
    let (x0,x1,x2,x3) = extract_ipv4 ip in
    output_byte sout x0;
    output_byte sout x1;
    output_byte sout x2;
    output_byte sout x3;
    output_byte sout 0;
    flush sout;
    let _ (* z *) = input_byte sin in
    let cd = input_byte sin in
    if not (cd = 90) then raise RequestRejected;
    for i = 1 to 6 do
      ignore (input_byte sin)
    done;
    (s,sin,sout)
  with exn ->
    Unix.close s;
    raise exn
      
type connstate = {
    conntime : float;
    realaddr : string;
    connmutex : Mutex.t;
    sendqueue : (hashval * hashval option * msgtype * string) Queue.t;
    sendqueuenonempty : Condition.t;
    mutable nonce : int64 option;
    mutable handshakestep : int;
    mutable srvs : int64;
    mutable peertimeskew : int;
    mutable protvers : int32;
    mutable useragent : string;
    mutable addrfrom : string;
    mutable banned : bool;
    mutable lastmsgtm : float;
    mutable sentinv : (int * hashval,float) Hashtbl.t;
    mutable rinv : (int * hashval,unit) Hashtbl.t;
    mutable invreq : (int * hashval,float) Hashtbl.t;
    mutable invreqhooks : (int * hashval,unit -> unit) Hashtbl.t;
    mutable itemhooks : (int * hashval,unit -> unit) Hashtbl.t;
    mutable first_header_height : int64; (*** how much header history is stored at the node ***)
    mutable first_full_height : int64; (*** how much block/ctree history is stored at the node ***)
    mutable last_height : int64; (*** how up to date the node is ***)
    mutable strength : int option; (*** strength of the connection (only for listener node) ***)
    mutable powchallenge : (int32 * hashval) option; (*** strength of the connection ***)
    mutable powtarget : int32; (*** powtarget for tie breakers ***)
    mutable sendershouldclose : bool;
  }

let send_inv_fn : (int -> out_channel -> connstate -> unit) ref = ref (fun _ _ _ -> ())
let msgtype_handler : (msgtype,in_channel * out_channel * connstate * string -> unit) Hashtbl.t = Hashtbl.create 50

let send_msg_real c mh replyto mt ms =
  let magic = if !Config.testnet then 0x50666754l else 0x5066674dl in (*** Magic Number for testnet: PfgT and for mainnet: PfgM ***)
  let msl = String.length ms in
  seocf (seo_int32 seoc magic (c,None));
  begin
    match replyto with
    | None ->
	output_byte c 0
    | Some(h) ->
	output_byte c 1;
	seocf (seo_hashval seoc h (c,None))
  end;
  output_byte c (int_of_msgtype mt);
  seocf (seo_int32 seoc (Int32.of_int msl) (c,None));
  seocf (seo_hashval seoc mh (c,None));
  for j = 0 to msl-1 do
    output_byte c (Char.code ms.[j])
  done;
  flush c (* This flush often causes the entire process to die if the connection turns out to be closed. That shouldn't happen, but it does. The solution? Keep restarting your node. Sorry. *)

let send_msg c mh replyto mt ms =
  send_msg_real c mh replyto mt ms
                (**
  let f = open_out_gen [Open_wronly;Open_creat;Open_append] 0o644 (!Config.datadir ^ (if !Config.testnet then "/testnet/sentlog" else "/sentlog")) in
  seocf (seo_int64 seoc (Int64.of_float (Unix.time())) (f,None));
  send_msg_real f mh replyto mt ms;
  close_out_noerr f **)

let queue_msg_real cs replyto mt m =
  (*  log_string (Printf.sprintf "enqueue %s\n" (string_of_msgtype mt)); *)
  let mh = sha256str m in
  Mutex.lock cs.connmutex;
  Queue.add (mh,replyto,mt,m) cs.sendqueue;
  Mutex.unlock cs.connmutex;
  Condition.signal cs.sendqueuenonempty;
  mh

let queue_msg cs mt m = queue_msg_real cs None mt m
let queue_reply cs h mt m = queue_msg_real cs (Some(h)) mt m

(***
 Throw IllformedMsg if something's wrong with the format or if it reads the first byte but times out before reading the full message.
 If IllformedMsg is thrown, the connection should be severed.
 ***)
let rec_msg blkh c =
  let (mag0,mag1,mag2,mag3) = if !Config.testnet then (0x50,0x66,0x67,0x54) else (0x50,0x66,0x67,0x4d) in
  let by0 = input_byte c in
  if not (by0 = mag0) then raise IllformedMsg;
  try
    let by1 = input_byte c in
    if not (by1 = mag1) then raise IllformedMsg;
    let by2 = input_byte c in
    if not (by2 = mag2) then raise IllformedMsg;
    let by3 = input_byte c in
    if not (by3 = mag3) then raise IllformedMsg;
    let replyto =
      let by4 = input_byte c in
      if by4 = 0 then (*** not a reply ***)
	None
      else if by4 = 1 then
	let (h,_) = sei_hashval seic (c,None) in
	(Some(h))
      else
	raise IllformedMsg
    in
    let mt =
      try
	msgtype_of_int (input_byte c)
      with Not_found -> raise IllformedMsg
    in
    let (msl,_) = sei_int32 seic (c,None) in
    if msl > Int32.add 8192l (Int32.of_int (maxblockdeltasize blkh)) then raise IllformedMsg;
    let msl = Int32.to_int msl in
    let (mh,_) = sei_hashval seic (c,None) in
    let sb = Buffer.create msl in
    for j = 0 to msl-1 do
      let by = input_byte c in
      Buffer.add_char sb (Char.chr by)
    done;
    let ms = Buffer.contents sb in
    if not (mh = sha256str ms) then raise IllformedMsg;
    (replyto,mh,mt,ms)
  with
  | _ -> (*** consider it an IllformedMsg no matter what the exception raised was ***)
      raise IllformedMsg

let netlistenerth : Thread.t option ref = ref None
let onionlistenerth : Thread.t option ref = ref None
let netseekerth : Thread.t option ref = ref None
let netconns : (Thread.t * Thread.t * (Unix.file_descr * in_channel * out_channel * connstate option ref)) list ref = ref []
let netconnsmutex : Mutex.t = Mutex.create()
let this_nodes_nonce = ref 0L

let peeraddr gcs =
  match gcs with
  | Some(cs) -> cs.addrfrom
  | None -> "[dead]"

let network_time () =
  let mytm = Int64.of_float (Unix.time()) in
  let offsets = ref [] in
  List.iter (fun (_,_,(_,_,_,gcs)) -> match !gcs with Some(cs) -> offsets := List.merge compare [cs.peertimeskew] !offsets | None -> ()) !netconns;
  if !offsets = [] then
    (mytm,0)
  else
    let m = (List.length !offsets) lsr 1 in
    let mskew = List.nth !offsets m in
    (Int64.add mytm (Int64.of_int mskew),mskew)

let sync_last_height = ref 0L

let find_weakest_conn_except f =
  let weakestconn = ref None in
  List.iter
    (fun (clth,csth,(s,sin,sout,gcs)) ->
      match !gcs with
      | None -> ()
      | Some(cs) ->
         if not (f cs) then
           match !weakestconn with
           | None ->
              let str2 = match cs.strength with None -> -1 | Some(str2) -> str2 in
              weakestconn := Some((s,sin,sout,gcs),str2,cs.powtarget)
           | Some(_,str,powtar) ->
              let str2 = match cs.strength with None -> -1 | Some(str2) -> str2 in
              if str2 < str then
                weakestconn := Some((s,sin,sout,gcs),str2,cs.powtarget)
              else if str2 = str && powtar < cs.powtarget then (** higher powtarget numbers means less pow, i.e., weaker connection **)
                weakestconn := Some((s,sin,sout,gcs),str2,cs.powtarget))
    !netconns;
  !weakestconn

let drop_weakest_conn () =
  match find_weakest_conn_except (fun cs1 -> cs1.handshakestep < 5 || not (cs1.powchallenge = None)) with
  | None -> ()
  | Some((s,sin,sout,gcs),_,_) ->
     try
       match !gcs with
       | None -> ()
       | Some(cs) ->
          cs.sendershouldclose <- true;
          Condition.signal cs.sendqueuenonempty;
          gcs := None
     with _ ->
       gcs := None

let recently_requested (i,h) nw ir =
  try
    let tm = Hashtbl.find ir (i,h) in
    if nw -. tm < 991.0 then
      true
    else
      (Hashtbl.remove ir (i,h);
       false)
  with Not_found -> false

let recently_sent (i,h) nw isnt =
  try
    let tm = Hashtbl.find isnt (i,h) in
    if nw -. tm < 353.0 then
      true
    else
      (Hashtbl.remove isnt (i,h);
       false)
  with Not_found -> false
  
let find_and_send_requestmissingblocks cs =
  if not (!missingheaders = [] && !missingdeltas = []) then
    let i = int_of_msgtype GetHeader in
    let ii = int_of_msgtype Headers in
    let di = int_of_msgtype GetBlockdelta in
    let dii = int_of_msgtype Blockdelta in
    let tm = Unix.time() in
    if not cs.banned then
      begin
	let rhl = ref [] in
	let mhl = ref !missingheaders in
	let j = ref 0 in
	while (!j < 255 && not (!mhl = [])) do
	  match !mhl with
	  | [] -> raise Exit (*** impossible ***)
	  | (blkh,h)::mhr ->
	      mhl := mhr;
	      if (((blkh >= cs.first_header_height) && (blkh <= cs.last_height)) || Hashtbl.mem cs.rinv (ii,h)) && not (recently_requested (i,h) tm cs.invreq) then
		begin
		  incr j;
		  rhl := h::!rhl
		end
	done;
	if not (!rhl = []) then
	  begin
	    let msb = Buffer.create 100 in
	    seosbf (seo_int8 seosb !j (msb,None));
	    List.iter
	      (fun h ->
		Hashtbl.replace cs.invreq (i,h) tm;
		seosbf (seo_hashval seosb h (msb,None)))
	      !rhl;
	    let ms = Buffer.contents msb in
	    let _ (* mh *) = queue_msg cs GetHeaders ms in
	    ()
	  end;
	match !missingdeltas with
	| ((blkh,h)::_) ->
	    if (((blkh >= cs.first_full_height) && (blkh <= cs.last_height)) || Hashtbl.mem cs.rinv (dii,h)) && not (recently_requested (di,h) tm cs.invreq) then
	      begin
		let msb = Buffer.create 100 in
		seosbf (seo_hashval seosb h (msb,None));
		let ms = Buffer.contents msb in
		Hashtbl.replace cs.invreq (di,h) tm;
		ignore (queue_msg cs GetBlockdelta ms)
	      end
	| _ -> ()
      end;;

let send_addrs yesterday cs =
  let currpeers = ref [] in
  let oldpeers = ref [] in
  Hashtbl.iter
    (fun nodeaddr lasttm ->
      if not (nodeaddr = "") then
	if lasttm > yesterday then
	  currpeers := nodeaddr::!currpeers
	else
	  oldpeers := nodeaddr::!oldpeers)
    knownpeers;
  let cpl = List.length !currpeers in
  if cpl > 65535 then
    begin
      oldpeers := [];
      for j = 65535 to cpl do
	match !currpeers with
	| (_::r) -> currpeers := r
	| [] -> ()
      done
    end;
  let cpl = List.length !currpeers in
  let opl = List.length !oldpeers in
  for j = 65535 to cpl + opl do
    match !oldpeers with
    | (_::r) -> oldpeers := r
    | [] -> ()
  done;
  let opl = List.length !oldpeers in
  let l = !currpeers @ !oldpeers in
  let ll = cpl + opl in
  let addrmsg = Buffer.create 10000 in
  let c = ref (seo_varintb seosb ll (addrmsg,None)) in
  List.iter
    (fun s ->
      let cn = seo_string seosb s !c in
      c := cn)
    l;
  seosbf !c;
  ignore (queue_msg cs Addr (Buffer.contents addrmsg));;
  
let handle_msg replyto mt sin sout cs mh m =
  match replyto with
  | Some(h) ->
      begin
	log_string (Printf.sprintf "ignoring claimed replyto %s although replies were never supported and are now fully deprecated\n" (hashval_hexstring h));
      end
  | None ->
      if cs.handshakestep < 5 then
	begin
	  match mt with
	  | Version ->
	      let (((vers,srvs,tm,addr_recv,addr_from,n),(ua,fhh,ffh,lh,relay,lastchkpt)),_) =
		sei_prod
		  (sei_prod6 sei_int32 sei_int64 sei_int64 sei_string sei_string sei_int64)
		  (sei_prod6 sei_string sei_int64 sei_int64 sei_int64 sei_bool (sei_option (sei_prod sei_int64 sei_hashval)))
		  seis (m,String.length m,None,0,0)
	      in
	      begin
		if n = !this_nodes_nonce then
		  raise SelfConnection
		else if (try ignore (List.find (fun (_,_,(_,_,_,gcs)) -> match !gcs with Some(cs) -> cs.nonce = Some(n) | None -> false) !netconns); true with Not_found -> false) then
		  raise DupConnection;
		cs.nonce <- Some(n); (** remember the nonce to prevent duplicate connections to the same node **)
		let minvers = if vers > Version.protocolversion then Version.protocolversion else vers in
		let mytm = Int64.of_float (Unix.time()) in
		let tmskew = Int64.sub tm mytm in
		if tmskew > 7200L then
		  raise (ProtocolViolation("Peer rejected due to excessive time skew"))
		else
		  let tmskew = Int64.to_int tmskew in
		  if cs.handshakestep = 1 then
		    begin
		      ignore (queue_msg cs Verack "");
		      let vm = Buffer.create 100 in
		      seosbf
			(seo_prod
			   (seo_prod6 seo_int32 seo_int64 seo_int64 seo_string seo_string seo_int64)
			   (seo_prod6 seo_string seo_int64 seo_int64 seo_int64 seo_bool (seo_option (seo_prod seo_int64 seo_hashval)))
			   seosb
			   ((minvers,0L,mytm,addr_from,myaddr(),!this_nodes_nonce),
			    (Version.useragent,0L,0L,!sync_last_height,true,None))
			   (vm,None));
		      ignore (queue_msg cs Version (Buffer.contents vm));
		      cs.handshakestep <- 3;
                      cs.srvs <- srvs;
		      cs.peertimeskew <- tmskew;
		      cs.useragent <- ua;
		      cs.protvers <- minvers;
		      cs.addrfrom <- addr_from;
		      cs.first_header_height <- fhh;
		      cs.first_full_height <- ffh;
                      cs.strength <- Some(Int64.to_int (Int64.logand tm 15L));
		      cs.last_height <- lh
		    end
		  else if cs.handshakestep = 4 then
		    begin
		      ignore (queue_msg cs Verack "");
		      cs.handshakestep <- 5;
                      cs.srvs <- srvs;
		      cs.peertimeskew <- tmskew;
		      cs.useragent <- ua;
		      cs.protvers <- minvers;
		      cs.addrfrom <- addr_from;
		      cs.first_header_height <- fhh;
		      cs.first_full_height <- ffh;
		      cs.last_height <- lh;
		      addknownpeer mytm addr_from;
		      !send_inv_fn 4096 sout cs;
		      find_and_send_requestmissingblocks cs;
		    end
		  else
		    raise (ProtocolViolation "Handshake failed")
	      end
	  | Verack ->
	      begin
		if cs.handshakestep = 2 then
		  cs.handshakestep <- 4
		else if cs.handshakestep = 3 then
		  begin
		    let mytm = Int64.of_float (Unix.time()) in
		    cs.handshakestep <- 5;
		    addknownpeer mytm cs.addrfrom;
                    let str1 = match cs.strength with None -> -1 | Some(str1) -> str1 in
                    (** handshake has finished, but the connection might now be dropped or challenged **)
                    if List.length !netconns > !Config.maxconns then
                      begin
                        match find_weakest_conn_except (fun cs1 -> cs1.nonce = cs.nonce) with
                        | None ->
                           begin (** Send addrs message and close connection **)
	                     let yesterday = Int64.sub mytm 86400L in
                             send_addrs yesterday cs;
			     cs.sendershouldclose <- true;
                             Condition.signal cs.sendqueuenonempty;
                           end
                        | Some((s2,sin2,sout2,gcs2),str2,powtar2) ->
                           if str2 < str1 then (** drop weaker conn **)
                             begin
                               begin
                                 match !gcs2 with
                                 | None -> ()
                                 | Some(cs2) ->
                                    cs2.sendershouldclose <- true;
                                    Condition.signal cs2.sendqueuenonempty
                               end;
                               !send_inv_fn 32 sout cs;
		               find_and_send_requestmissingblocks cs;
                             end
                           else if str2 = str1 && 0l < powtar2 then (** Send POW Challenge **)
                             begin
                               let powch = Buffer.create 33 in
                               let r = rand_md256 () in
                               let powtar2b = Int32.div (Int32.mul powtar2 9l) 10l in
                               seosbf (seo_prod seo_int32 seo_hashval seosb (powtar2b,r) (powch,None));
                               cs.powchallenge <- Some(powtar2b,r);
                               log_string (Printf.sprintf "sending POWChallenge with %ld\n" powtar2b);
                               ignore (queue_msg cs POWChallenge (Buffer.contents powch))
                             end
                           else
                             begin (** Send addrs message and close connection **)
	                       let yesterday = Int64.sub mytm 86400L in
                               send_addrs yesterday cs;
                               cs.sendershouldclose <- true;
                               Condition.signal cs.sendqueuenonempty
                             end
                      end
                    else
                      begin
		        !send_inv_fn 32 sout cs;
		        find_and_send_requestmissingblocks cs;
                      end
		  end
		else
		  raise (ProtocolViolation("Unexpected Verack"))
	      end
	  | _ -> raise (ProtocolViolation "Handshake failed")
	end
      else
	try
	  begin
	    let f = Hashtbl.find msgtype_handler mt in
	    try
	      f(sin,sout,cs,m);
            with
            | Unix.Unix_error(Unix.ENOMEM,_,_) ->
               log_string (Printf.sprintf "Out of memory. Trying to exit gracefully.\n");
               Printf.printf "Out of memory. Trying to exit gracefully.\n";
               !exitfn 9
            | e ->
	       log_string (Printf.sprintf "Call to handler for message type %s raised %s\n" (string_of_msgtype mt) (Printexc.to_string e));
	  end;
	  find_and_send_requestmissingblocks cs;
	with Not_found ->
	  match mt with
	  | Version -> raise (ProtocolViolation "Version message after handshake")
	  | Verack -> raise (ProtocolViolation "Verack message after handshake")
	  | _ -> log_string (Printf.sprintf "No handler found for message type %s." (string_of_msgtype mt))

let connlistener (s,sin,sout,gcs) =
  log_string (Printf.sprintf "connlistener thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let connlistener_end cs =
    cs.sendershouldclose <- true;
    Condition.signal cs.sendqueuenonempty; (* signal the connsender so it knows to die *)
    Thread.exit ()
  in
  let connlistener_end_2 () =
    begin
      match !gcs with
      | Some(cs) ->
         begin
           try
             cs.sendershouldclose <- true;
             Condition.signal cs.sendqueuenonempty; (* signal the connsender so it knows to die *)
           with _ -> ()
         end
      | _ -> ()
    end;
    log_string (Printf.sprintf "connlistener thread %d exit %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
    Thread.exit ()
  in
  try
    while true do
      let (replyto,mh,mt,m) = rec_msg !netblkh sin in
      match !gcs with
      | Some(cs) ->
         if cs.sendershouldclose then
           Thread.exit()
         else
           begin
             try
	       let tm = Unix.time() in
  (* log_string (Printf.sprintf "got msg %s from %s at time %f\n" (string_of_msgtype mt) cs.realaddr tm); *)
               (*            let f = open_out_gen [Open_wronly;Open_creat;Open_append] 0o644
                            (!Config.datadir ^ (if !Config.testnet then "/testnet/reclog_" else "/reclog_") ^ (string_hexstring cs.addrfrom)) in
            output_value f tm;
            output_value f (replyto,mh,mt,m);
            close_out_noerr f; *)
	       cs.lastmsgtm <- tm;
	       if Hashtbl.mem knownpeers cs.addrfrom then Hashtbl.replace knownpeers cs.addrfrom (Int64.of_float tm);
	       handle_msg replyto mt sin sout cs mh m;
	       if cs.banned then raise (ProtocolViolation("banned"));
             with
             | Unix.Unix_error(c,x,y) -> (*** close connection ***)
	        log_string (Printf.sprintf "Unix error exception raised in connection listener for %s:\n%s %s %s\nClosing connection\n" (peeraddr !gcs) (Unix.error_message c) x y);
                connlistener_end cs
             | End_of_file -> (*** close connection ***)
	        log_string (Printf.sprintf "Channel for connection %s in connlistener raised End_of_file (1). Closing connection\n" (peeraddr !gcs));
                connlistener_end cs
             | ProtocolViolation(x) -> (*** close connection ***)
	        log_string (Printf.sprintf "Protocol violation by connection %s: %s in connlistener\nClosing connection\n" (peeraddr !gcs) x);
                connlistener_end cs
             | IllformedMsg -> (*** close connection ***)
	        log_string (Printf.sprintf "Ill formed message by connection %s in connlistener\nClosing connection\n" (peeraddr !gcs));
                connlistener_end cs
             | SelfConnection -> (*** detected a self-connection attempt, close ***)
	        log_string (Printf.sprintf "Stopping potential self-connection in connlistener\n");
                connlistener_end cs
             | DupConnection -> (*** detected a duplicate connection attempt, close ***)
	        log_string (Printf.sprintf "Stopping potential duplicate connection in connlistener\n");
                connlistener_end cs
             | Sys_error(str) ->
	        log_string (Printf.sprintf "Stopping connection listener for %s due to Sys_error %s" (peeraddr !gcs) str);
                connlistener_end cs
             | exc -> (*** report all other exceptions and close conn ***)
	        log_string (Printf.sprintf "Unhandled exception raised in connection listener for %s:\n%s\n" (peeraddr !gcs) (Printexc.to_string exc));
                connlistener_end cs
           end
      | None ->
         log_string (Printf.sprintf "conn listener gcs disappeared; ending thread\n");
	 shutdown_close s;
	 close_in_noerr sin;
	 close_out_noerr sout;
         Thread.exit()
    done
  with
  | Unix.Unix_error(c,x,y) -> (*** close connection ***)
     log_string (Printf.sprintf "Unix error exception raised in connection listener for %s:\n%s %s %s\nClosing connection\n" (peeraddr !gcs) (Unix.error_message c) x y);
     connlistener_end_2 ()
  | End_of_file -> (*** close connection ***)
     log_string (Printf.sprintf "Channel for connection %s raised End_of_file in connlistener (2). Closing connection\n" (peeraddr !gcs));
     connlistener_end_2 ()
  | ProtocolViolation(x) -> (*** close connection ***)
     log_string (Printf.sprintf "Protocol violation by connection %s in connlistener: %s\nClosing connection\n" (peeraddr !gcs) x);
     connlistener_end_2 ()
  | IllformedMsg -> (*** close connection ***)
    log_string (Printf.sprintf "Ill formed message by connection %s in connlistener\nClosing connection\n" (peeraddr !gcs));
    connlistener_end_2 ()
  | Sys_error(str) ->
     log_string (Printf.sprintf "Stopping connection listener for %s due to Sys_error %s" (peeraddr !gcs) str);
     connlistener_end_2 ()
  | exc ->
    log_string (Printf.sprintf "Unhandled outer exception raised in connection listener for %s:\n%s\n" (peeraddr !gcs) (Printexc.to_string exc));
    connlistener_end_2 ()

let connsender (s,sin,sout,gcs) =
  log_string (Printf.sprintf "connsender thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  match !gcs with
  | None ->
     log_string (Printf.sprintf "connsender was called without gcs being set to a connection state already.\nThis should never happen.\nKilling connection immediately.\n");
     shutdown_close s;
     log_string (Printf.sprintf "connsender thread %d exit %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
     Thread.exit ()
  | Some(cs) ->
     let connsender_end () =
       try
	 Mutex.unlock cs.connmutex;
	 gcs := None;
	 shutdown_close s;
         log_string (Printf.sprintf "connsender thread %d exit %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
         Thread.exit ()
       with _ ->
        Thread.exit ()
      in
      try
	Mutex.lock cs.connmutex;
	while true do
	  try
	    while true do
              if !gcs = None || cs.sendershouldclose then connsender_end();
	      let (mh,replyto,mt,m) = Queue.take cs.sendqueue in
	      send_msg sout mh replyto mt m
	    done;
	  with
	  | Queue.Empty ->
	     if cs.sendershouldclose then
	       connsender_end()
	     else
	       Condition.wait cs.sendqueuenonempty cs.connmutex
	done
      with
      | Unix.Unix_error(c,x,y) -> (*** close connection ***)
	 log_string (Printf.sprintf "Unix error exception raised in connection sender for %s:\n%s %s %s\nClosing connection\n" (peeraddr !gcs) (Unix.error_message c) x y);
	 connsender_end()
      | End_of_file -> (*** close connection ***)
	 log_string (Printf.sprintf "Channel for connection %s raised End_of_file in connection sender. Closing connection\n" (peeraddr !gcs));
	 connsender_end()
      | ProtocolViolation(x) -> (*** close connection ***)
	 log_string (Printf.sprintf "Protocol violation by connection sender %s: %s\nClosing connection\n" (peeraddr !gcs) x);
	 connsender_end()
      | SelfConnection -> (*** detected a self-connection attempt, close ***)
	 log_string (Printf.sprintf "Stopping potential self-connection in connection sender\n");
	 connsender_end()
      | Sys_error(str) ->
	 log_string (Printf.sprintf "Stopping connection sender for %s due to Sys_error %s" (peeraddr !gcs) str);
	  connsender_end()
      | exc -> (*** report all other exceptions and close connection ***)
	 log_string (Printf.sprintf "Stopping connection sender for %s:\n%s\n" (peeraddr !gcs) (Printexc.to_string exc));
	 connsender_end()

let remove_dead_conns () =
  let tmminus10min = Unix.time() -. 600.0 in
  List.iter
    (fun (clth,csth,(s,sin,sout,gcs)) ->
      match !gcs with
      | Some(cs) ->
         if cs.sendershouldclose then
           gcs := None
	 else if (cs.handshakestep < 5 || (not (cs.powchallenge = None))) && cs.conntime < tmminus10min then (*** if the handshake/pow challenge has not completed in 600s, then kill conn ***)
	   begin
             cs.sendershouldclose <- true;
             Condition.signal cs.sendqueuenonempty; (* signal the connsender so it knows to die *)
             gcs := None
	   end
      | _ -> ())
    !netconns;
  Mutex.lock netconnsmutex;
  netconns :=
    List.filter
      (fun (_,_,(_,_,_,gcs)) ->
	match !gcs with
	| None -> false
	| Some(cs) -> true)
      !netconns;
  Mutex.unlock netconnsmutex

exception EnoughConnections

let initialize_conn_accept ra s =
  if List.length !netconns <= !Config.maxconns then
    begin
      let sin = Unix.in_channel_of_descr s in
      let sout = Unix.out_channel_of_descr s in
      set_binary_mode_in sin true;
      set_binary_mode_out sout true;
      let tm = Unix.time() in
      let cs = { conntime = tm; realaddr = ra; connmutex = Mutex.create(); sendqueue = Queue.create(); sendqueuenonempty = Condition.create(); nonce = None; handshakestep = 1; srvs = 0L; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; banned = false; lastmsgtm = tm; sentinv = Hashtbl.create 100; rinv = Hashtbl.create 1000; invreq = Hashtbl.create 100; invreqhooks = Hashtbl.create 100; itemhooks = Hashtbl.create 100; first_header_height = 0L; first_full_height = 0L; last_height = 0L; strength = None; powchallenge = None; powtarget = 524288l; sendershouldclose = false } in
      let sgcs = (s,sin,sout,ref (Some(cs))) in
      let clth = Thread.create connlistener sgcs in
      let csth = Thread.create connsender sgcs in
      Mutex.lock netconnsmutex;
      netconns := (clth,csth,sgcs)::!netconns;
      Mutex.unlock netconnsmutex
    end
  else
    begin
      shutdown_close s;
      raise EnoughConnections
    end

let reqstrength = ref None

let reqstrength_modtime tmf =
  let tm = Int64.of_float tmf in
  let tm = Int64.sub tm (Int64.logand tm 15L) in (** 0 out 4 lowest bits **)
  let nc = List.length !netconns in
  let reqstr = (** be nice if already connected **)
    match !reqstrength with
    | Some(rstr) when rstr >= 0 && rstr < 16 -> rstr
    | _ ->
       if nc = 0 then
         14
       else if nc = 1 then
         7
       else if nc < 3 then
         3
       else if nc < 6 then
         2
       else if nc < 8 then
         1
       else
         0
  in
  reqstrength := None;
  Int64.logor tm (Int64.of_int reqstr)
  
let initialize_conn_2 n s sin sout =
  (*** initiate handshake ***)
  let vers = Version.protocolversion in
  let srvs = 1L in
  let srvs = if !Config.fullnode then Int64.logor srvs 2L else srvs in
  let tmf = Unix.time() in
  let tm = reqstrength_modtime tmf in
  let fhh = 0L in
  let ffh = 0L in
  let lh = !sync_last_height in
  let relay = true in
  let lastchkpt = None in
  let vm = Buffer.create 100 in
  seosbf
    (seo_prod
       (seo_prod6 seo_int32 seo_int64 seo_int64 seo_string seo_string seo_int64)
       (seo_prod6 seo_string seo_int64 seo_int64 seo_int64 seo_bool (seo_option (seo_prod seo_int64 seo_hashval)))
       seosb
       ((vers,srvs,tm,n,myaddr(),!this_nodes_nonce),
	(Version.useragent,fhh,ffh,lh,relay,lastchkpt))
       (vm,None));
  let cs = { conntime = tmf; realaddr = n; connmutex = Mutex.create(); sendqueue = Queue.create(); sendqueuenonempty = Condition.create(); nonce = None; handshakestep = 2; srvs = 0L; peertimeskew = 0; protvers = Version.protocolversion; useragent = ""; addrfrom = ""; banned = false; lastmsgtm = tmf; sentinv = Hashtbl.create 100; rinv = Hashtbl.create 1000; invreq = Hashtbl.create 100; invreqhooks = Hashtbl.create 100; itemhooks = Hashtbl.create 100; first_header_height = fhh; first_full_height = ffh; last_height = lh; strength = None; powchallenge = None; powtarget = 524288l; sendershouldclose = false } in
  ignore (queue_msg cs Version (Buffer.contents vm));
  let sgcs = (s,sin,sout,ref (Some(cs))) in
  let clth = Thread.create connlistener sgcs in
  let csth = Thread.create connsender sgcs in
  Mutex.lock netconnsmutex;
  netconns := (clth,csth,sgcs)::!netconns;
  Mutex.unlock netconnsmutex;
  (clth,csth,sgcs)

let initialize_conn n s =
  let sin = Unix.in_channel_of_descr s in
  let sout = Unix.out_channel_of_descr s in
  set_binary_mode_in sin true;
  set_binary_mode_out sout true;
  initialize_conn_2 n s sin sout

let record_peer n =
  if not (n = "") && not (Hashtbl.mem bannedpeers n) && not (Hashtbl.mem knownpeers n) then
    begin
      try
        let (_,_) = extract_onion_and_port n in
        addknownpeer (Int64.of_float (Unix.time())) n
      with
      | Not_found ->
         try
           let (_,_,_) = extract_ip_and_port n in
           addknownpeer (Int64.of_float (Unix.time())) n
         with Failure(_) -> ()
    end
      
let tryconnectpeer n =
  if not (n = "") then
    begin
      if List.length !netconns >= !Config.maxconns then raise EnoughConnections;
      if Hashtbl.mem bannedpeers n then raise BannedPeer;
      try
        Some(List.find (fun (_,_,(_,_,_,gcs)) -> n = peeraddr !gcs) !netconns);
      with Not_found ->
        try
          let (onionaddr,port) = extract_onion_and_port n in
          try
	    let (s,sin,sout) = connectonionpeer !Config.socksport onionaddr port in
	    Some(initialize_conn_2 n s sin sout)
          with _ -> None
        with Not_found ->
          let (ip,port,v6) = extract_ip_and_port n in
          begin
	    try
	      match !Config.socks with
	      | None ->
	         let s = connectpeer ip port in
	         Some (initialize_conn n s)
	      | Some(4) ->
	         let (s,sin,sout) = connectpeer_socks4 !Config.socksport ip port in
	         Some (initialize_conn_2 n s sin sout)
	      | Some(5) ->
	         raise (Failure "socks5 is not yet supported")
	      | Some(z) ->
	         raise (Failure ("do not know what socks" ^ (string_of_int z) ^ " means"))
	    with
	    | RequestRejected ->
	       log_string (Printf.sprintf "RequestRejected %s\n" n);
	       None
	    | _ ->
	       None
          end
    end
  else
    None

let netlistener l =
  log_string (Printf.sprintf "netlistener thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  while true do
    try
      Thread.delay 10.0;
      log_string (Printf.sprintf "netlistener thread %d waiting to accept %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
      let (s,a) = Unix.accept l in
      let ra =
	begin
	  match a with
	  | Unix.ADDR_UNIX(x) ->
	      log_string (Printf.sprintf "got local connection %s\n" x);
	      "local " ^ x
	  | Unix.ADDR_INET(x,y) ->
	      log_string (Printf.sprintf "got remote connection %s %d\n" (Unix.string_of_inet_addr x) y);
	      (Unix.string_of_inet_addr x) ^ " " ^ (string_of_int y)
	end
      in
      remove_dead_conns();
      initialize_conn_accept ra s
    with
    | EnoughConnections -> log_string (Printf.sprintf "Rejecting connection because of maxconns.\n");
    | _ -> ()
  done

let onionlistener l =
  log_string (Printf.sprintf "onionlistener thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  while true do
    try
      log_string (Printf.sprintf "onionlistener thread %d waiting to accept %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
      let (s,a) = Unix.accept l in
      let ra =
	begin
	  match a with
	  | Unix.ADDR_UNIX(x) ->
	      log_string (Printf.sprintf "got local connection %s\n" x);
	      "local " ^ x
	  | Unix.ADDR_INET(x,y) ->
	      log_string (Printf.sprintf "got remote connection %s %d\n" (Unix.string_of_inet_addr x) y);
	      (Unix.string_of_inet_addr x) ^ " " ^ (string_of_int y)
	end
      in
      remove_dead_conns();
      initialize_conn_accept ra s
    with
    | EnoughConnections -> log_string (Printf.sprintf "Rejecting connection because of maxconns.\n");
    | _ -> ()
  done

let netseeker_loop () =
  while true do
    try
      remove_dead_conns();
      if List.length !netconns < max 1 (!Config.maxconns lsr 1) then
	begin
	  Hashtbl.iter
	    (fun n oldtm ->
	      try (*** don't try to connect to the same peer twice ***)
		ignore (List.find
			  (fun (_,_,(_,_,_,gcs)) -> peeraddr !gcs = n)
			  !netconns)
	      with Not_found ->
                ignore (tryconnectpeer n)
	      )
	    knownpeers;
	  match !newpeers with
	  | [] -> ()
	  | (n::r) ->
	      newpeers := r;
	      if not (Hashtbl.mem knownpeers n) then
		begin
		  try (*** don't try to connect to the same peer twice ***)
		    ignore (List.find
			      (fun (_,_,(_,_,_,gcs)) -> peeraddr !gcs = n)
			      !netconns)
		  with Not_found ->
		    ignore (tryconnectpeer n)
		end
	end;
      if !netconns = [] then
	begin
	  List.iter
	    (fun n -> ignore (tryconnectpeer n))
	    (if !Config.testnet then testnetfallbacknodes else fallbacknodes)
	end;
      (*** occasionally send a GetAddr request ***)
      let i = int_of_msgtype GetAddr in
      let h0 = (0l,0l,0l,0l,0l,0l,0l,0l) in
      let tm = Unix.time() in
      List.iter
	(fun (_,_,(_,_,_,gcs)) ->
	  match !gcs with
	    None -> ()
	  | Some(cs) ->
	      if cs.handshakestep = 5 && not (recently_requested (i,h0) tm cs.invreq) then
	        begin
		  ignore (queue_msg cs GetAddr "");
		  Hashtbl.replace cs.invreq (i,h0) tm
		end
	  )
	!netconns;
      if !newpeers = [] || List.length !netconns = !Config.maxconns then
	Thread.delay 600.
      else
	Thread.delay 60.
    with
    | BannedPeer -> Thread.delay 60.
    | EnoughConnections -> Thread.delay 600.
    | exn ->
       log_string (Printf.sprintf "netseeker_loop thread %d exception %s\n" (Thread.id (Thread.self())) (Printexc.to_string exn));
       Thread.delay 60.
  done

let netseeker2 () =
  let alreadytried : (string,unit) Hashtbl.t = Hashtbl.create 10 in
  List.iter
    (fun (_,_,(_,_,_,gcs)) -> Hashtbl.add alreadytried (peeraddr !gcs) ())
    !netconns;
  Hashtbl.iter
    (fun n oldtm ->
      try (*** don't try to connect to the same peer twice ***)
        Hashtbl.find alreadytried n
      with Not_found ->
        Hashtbl.add alreadytried n ();
        try
          ignore (tryconnectpeer n)
        with
        | BannedPeer -> ()
        | EnoughConnections -> ())
    knownpeers

let netseeker () =
  netseekerth := Some(Thread.create netseeker_loop ())

let broadcast_requestdata mt h =
  let i = int_of_msgtype mt in
  let msb = Buffer.create 20 in
  seosbf (seo_hashval seosb h (msb,None));
  let ms = Buffer.contents msb in
  let tm = Unix.time() in
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
       match !gcs with
       | Some(cs) ->
           if not (recently_requested (i,h) tm cs.invreq) &&
	     (Hashtbl.mem cs.rinv (inv_of_msgtype mt,h))
(*	    || mt = GetCTreeElement || mt = GetHConsElement || mt = GetAsset *)
	   then
             begin
               ignore (queue_msg cs mt ms);
	       Hashtbl.replace cs.invreq (i,h) tm
             end
       | None -> ())
    !netconns;;

let broadcast_requestinv mt h =
  let i = int_of_msgtype mt in
  let msb = Buffer.create 20 in
  seosbf (seo_prod seo_int8 seo_hashval seosb (i,h) (msb,None));
  let ms = Buffer.contents msb in
  let tm = Unix.time() in
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
       match !gcs with
       | Some(cs) ->
           if not (recently_requested (i,h) tm cs.invreq) &&
	     (Hashtbl.mem cs.rinv (inv_of_msgtype mt,h))
(*	    || mt = GetCTreeElement || mt = GetHConsElement || mt = GetAsset *)
	   then
             begin
               ignore (queue_msg cs GetInvNbhd ms);
	       Hashtbl.replace cs.invreq (i,h) tm
             end
       | None -> ())
    !netconns;;

let sync_request_p cs mt h =
  if mt = GetHeader || mt = GetBlockdelta then
    begin
      let blkh = ref None in
      let lbl = get_blockburns h in
      try
        List.iter
          (fun (lbh,ltx) ->
            let (_,_,_,_,_,_,currhght) =
              Db_outlinevals.dbget (hashpair lbh ltx)
            in
            blkh := Some(currhght);
            raise Exit)
          lbl;
        raise Exit
      with Exit ->
        match !blkh with
        | Some(blkh) ->
           if mt = GetHeader then
             blkh >= cs.first_header_height && blkh <= cs.last_height
           else
             blkh >= cs.first_full_height && blkh <= cs.last_height
        | None -> false
    end
  else
    false

let find_and_send_requestdata mt h =
  let i = int_of_msgtype mt in
  let msb = Buffer.create 20 in
  seosbf (seo_hashval seosb h (msb,None));
  let ms = Buffer.contents msb in
  let tm = Unix.time() in
  let alrreq = ref false in
  try
    List.iter
      (fun (lth,sth,(fd,sin,sout,gcs)) ->
	match !gcs with
	| Some(cs) ->
            if not cs.banned && (Hashtbl.mem cs.rinv (inv_of_msgtype mt,h) || sync_request_p cs mt h) then
	      if recently_requested (i,h) tm cs.invreq then
		begin
                  log_string (Printf.sprintf "already recently sent request %s %s from %s\n" (string_of_msgtype mt) (hashval_hexstring h) cs.addrfrom);
		  alrreq := true
		end
	      else
		begin
                  log_string (Printf.sprintf "sending request %s %s to %s\n" (string_of_msgtype mt) (hashval_hexstring h) cs.addrfrom);
		  let _ (* mh *) = queue_msg cs mt ms in
		  Hashtbl.replace cs.invreq (i,h) tm;
		  raise Exit
		end
	| None -> ())
      !netconns;
    if not !alrreq then raise Not_found
  with Exit ->
    ();;

let broadcast_inv tosend =
  let invmsg = Buffer.create 10000 in
  let c = ref (seo_int32 seosb (Int32.of_int (List.length tosend)) (invmsg,None)) in
  List.iter
    (fun (i,h) ->
      c := seo_prod seo_int8 seo_hashval seosb (i,h) !c)
    tosend;
  let invmsgstr = Buffer.contents invmsg in
  (*  log_string (Printf.sprintf "broadcast_inv Created invmsgstr %s\n" (string_hexstring invmsgstr)); *)
  List.iter
    (fun (lth,sth,(fd,sin,sout,gcs)) ->
      match !gcs with
      | Some(cs) ->
         (*	  log_string (Printf.sprintf "broadcast_inv sending to %s\n" cs.addrfrom); *)
	  ignore (queue_msg cs Inv invmsgstr)
      | None -> ())
    !netconns;;

Hashtbl.add msgtype_handler POWChallenge
  (fun (sin,sout,cs,ms) ->
    log_string (Printf.sprintf "got POWChallenge\n");
    if List.length !netconns >= !Config.min_conns_pow then (** if enough conns already, don't bother with POWChallenge; just close connection **)
      begin
        log_string (Printf.sprintf "ignoring POWChallenge and closing connection due to %d >= %d (min_conns_pow)\n" (List.length !netconns) !Config.min_conns_pow);
        cs.sendershouldclose <- true;
	Condition.wait cs.sendqueuenonempty cs.connmutex
      end
    else
      let ((powtar,r),_) = sei_prod sei_int32 sei_hashval seis (ms,String.length ms,None,0,0) in
      log_string (Printf.sprintf "got POWChallenge with %ld\n" powtar);
      if !Config.min_conn_pow_target < powtar then (** only try if node thinks it isn't too hard **)
        begin
          let n = ref 0 in
          try
            while true do
              if !n >= !Config.max_conn_pow_tries then
                raise Not_found;
              let (_,_,_,_,_,_,_,x) = hashtag r (Int32.of_int !n) in
              if 0l <= x && x < powtar then raise Exit;
              incr n;
            done
          with
          | Exit ->
             begin
               let powchrepl = Buffer.create 5 in
               seosbf (seo_int32 seosb (Int32.of_int !n) (powchrepl,None));
               log_string (Printf.sprintf "sending POWChallengeResponse with %d\n" !n);
               ignore (queue_msg cs POWChallengeResponse (Buffer.contents powchrepl))
             end
          | Not_found -> (** drop connection **)
             log_string (Printf.sprintf "POWChallenge failed since max_conn_pow_tries reached: %d\n" !n);
             cs.sendershouldclose <- true;
	     Condition.wait cs.sendqueuenonempty cs.connmutex
        end
      else (** drop connection **)
        begin
          cs.sendershouldclose <- true;
	  Condition.wait cs.sendqueuenonempty cs.connmutex
        end);;

Hashtbl.add msgtype_handler POWChallengeResponse
  (fun (sin,sout,cs,ms) ->
    log_string (Printf.sprintf "got POWChallengeResponse\n");
    match cs.powchallenge with
    | None -> (** there is no outstanding POW challenge, drop connection **)
       cs.sendershouldclose <- true;
       Condition.signal cs.sendqueuenonempty;
    | Some(powtar,r) ->
       let (n,_) = sei_int32 seis (ms,String.length ms,None,0,0) in
       log_string (Printf.sprintf "got POWChallengeResponse with %ld\n" n);
       let (_,_,_,_,_,_,_,x) = hashtag r n in
       if 0l <= x && x < powtar then
         begin
           log_string (Printf.sprintf "POWChallengeResponse with %ld verified\n" n);
           cs.powchallenge <- None;
           cs.powtarget <- powtar;
	   !send_inv_fn 32 sout cs;
	   find_and_send_requestmissingblocks cs;
           if List.length !netconns > !Config.maxconns then drop_weakest_conn ();
         end
       else
         begin
           cs.sendershouldclose <- true;
           Condition.signal cs.sendqueuenonempty
         end);;

Hashtbl.add msgtype_handler GetAddr
    (fun (sin,sout,cs,ms) ->
      let i = int_of_msgtype Addr in
      let tm = Unix.time() in
      if not (recently_sent (i,(0l,0l,0l,0l,0l,0l,0l,0l)) tm cs.sentinv) then (*** ignore GetAddr message if we recently sent addresses ***)
	begin
	  Hashtbl.replace cs.sentinv (i,(0l,0l,0l,0l,0l,0l,0l,0l)) tm;
	  let tm64 = Int64.of_float tm in
	  let yesterday = Int64.sub tm64 86400L in
          send_addrs yesterday cs;
	end);;

Hashtbl.add msgtype_handler Addr
    (fun (sin,sout,cs,ms) ->
      let i = int_of_msgtype GetAddr in
      let tm = Unix.time() in
      if recently_requested (i,(0l,0l,0l,0l,0l,0l,0l,0l)) tm cs.invreq then (*** ignore Addr message unless it was recently requested ***)
	let c = ref (ms,String.length ms,None,0,0) in
	let (n,cn) = sei_varintb seis !c in (*** < 65536 other addresses ***)
	c := cn;
	for j = 1 to n do
	  let (nodeaddr,cn) = sei_string seis !c in
          c := cn;
	  if not (Hashtbl.mem knownpeers nodeaddr) then newpeers := nodeaddr::!newpeers
	done);;

Hashtbl.add msgtype_handler Ping
  (fun (sin,sout,cs,ms) ->
    let tm = Unix.time() in
    if tm -. cs.lastmsgtm >= 3600.0 then
      ignore (queue_msg cs Pong ""));;

Hashtbl.add msgtype_handler Pong (fun _ -> ());;

let send_inv_to_one tosend cs =
  let invmsg = Buffer.create 10000 in
  let c = ref (seo_int32 seosb (Int32.of_int (List.length tosend)) (invmsg,None)) in
  List.iter
    (fun (i,h) ->
      let cn = seo_prod seo_int8 seo_hashval seosb (i,h) !c in
      c := cn)
    tosend;
  ignore (queue_msg cs Inv (Buffer.contents invmsg));;

let liberally_accept_elements_tm = ref None;;

let liberally_accept_elements_until tm = liberally_accept_elements_tm := Some(tm);;

let liberally_accept_elements_p tm =
  match !liberally_accept_elements_tm with
  | Some(ltm) -> if tm < ltm then true else (liberally_accept_elements_tm := None; false)
  | None -> false;;

let localnewheader_sent : (hashval,int) Hashtbl.t = Hashtbl.create 100
let localnewdelta_sent : (hashval,int) Hashtbl.t = Hashtbl.create 100

let disconnect_completely () =
  List.iter
    (fun (clth,csth,(s,sin,sout,g)) ->
      (try
         shutdown_close s;
         close_in_noerr sin;
         close_out_noerr sout;
       with _ -> ());
      g := None)
    !netconns;
  netconns := []
                
let initnetwork sout =
  begin
    try
      let notlistening = ref true in
      begin
	match !Config.ip with
	| Some(ip) ->
	    let l = openlistener ip !Config.port 5 in
	    let efn = !exitfn in
	    exitfn := (fun n -> shutdown_close l; efn n);
	    Printf.fprintf sout "Listening for incoming connections via ip %s on port %d.\n" ip !Config.port;
	    flush sout;
	    notlistening := false;
	    netlistenerth := Some(Thread.create netlistener l)
	| None -> ()
      end;
      begin
	match !Config.onion with
	| Some(onionaddr) ->
	    let l = openonionlistener onionaddr !Config.onionlocalport !Config.onionremoteport 5 in
	    let efn = !exitfn in
	    exitfn := (fun n -> shutdown_close l; efn n);
	    Printf.fprintf sout "Listening for incoming connections via tor hidden service %s using port %d.\n" onionaddr !Config.onionremoteport;
	    flush sout;
	    notlistening := false;
	    onionlistenerth := Some(Thread.create onionlistener l)
	| None -> ()
      end;
      if !notlistening then
	begin
	  Printf.fprintf sout "Not listening for incoming connections.\n";
	  Printf.fprintf sout "If you want Proofgold to listen for incoming connections set ip to your ip address\n";
	  Printf.fprintf sout "using ip=... in proofgold.conf or -ip=... on the command line.\n";
	  Printf.fprintf sout "By default ip listeners use port 21805.\n";
	  Printf.fprintf sout "This can be changed by setting port=... in proofgold.conf or -port=... on the command line.\n";
	  Printf.fprintf sout "To listen as a tor hidden service set onion address\n";
	  Printf.fprintf sout "using onion=... in proofgold.conf or -onion=... on the command line.\n";
	  Printf.fprintf sout "By default onion listeners listen via the advertised port 21808.\n";
	  Printf.fprintf sout "This can be changed by setting onionremoteport=... in proofgold.conf or -onionremoteport=... on the command line.\n";
	  Printf.fprintf sout "By default onion listeners use the local (unadvertised) port 21807.\n";
	  Printf.fprintf sout "This can be changed by setting onionlocalport=... in proofgold.conf or -onionlocalport=... on the command line.\n";
	  flush sout
	end
    with _ -> ()
  end;
  ignore (loadknownpeers());
  let efn = !exitfn in
  exitfn := (fun n -> (try saveknownpeers() with _ -> ()); efn n);
  netseeker ()

