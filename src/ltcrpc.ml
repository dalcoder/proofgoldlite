(* Copyright (c) 2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hashaux
open Hash
open Sha256
open Json
open Net
open Db

let ltcdust = 2940L

let knownbootstrapurl : (string,unit) Hashtbl.t = Hashtbl.create 10
let ignorebootstrapurl : (string,unit) Hashtbl.t = Hashtbl.create 10
let bootstrapurls : string list ref = ref []
let ltcrpcauthstr : string option ref = ref None

let ltcrpcauth () =
  match !ltcrpcauthstr with
  | Some(s) -> s
  | None ->
     let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
     let s = Utils.base64encode (string_bytelist userpass) in
     ltcrpcauthstr := Some(s);
     s

let ltcrpc_connect () =
  match !Config.ltcrpconion with
  | Some(onionaddr) ->
     begin
       let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
       try
         Unix.connect s (Unix.ADDR_INET(Unix.inet_addr_loopback, !Config.socksport));
         let sin = Unix.in_channel_of_descr s in
         let sout = Unix.out_channel_of_descr s in
         set_binary_mode_in sin true;
         set_binary_mode_out sout true;
         output_byte sout 4;
         output_byte sout 1;
         (** port, big endian **)
         output_byte sout ((!Config.ltcrpcport asr 8) land 255);
         output_byte sout (!Config.ltcrpcport land 255);
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
           let _ (* ip0 *) = input_byte sin in
           let _ (* ip1 *) = input_byte sin in
           let _ (* ip2 *) = input_byte sin in
           let _ (* ip3 *) = input_byte sin in
           Printf.fprintf sout "POST / HTTP/1.1\n";
           Printf.fprintf sout "Host: %s:%d\n" onionaddr rport;
           Printf.fprintf sout "Authorization: Basic %s\n" (ltcrpcauth());
           Printf.fprintf sout "User-Agent: Proofgold/0.2.8\n";
           Printf.fprintf sout "Accept: */*\n";
           Printf.fprintf sout "content-type: text/plain;\n";
           (s,sin,sout)
         with e ->
           Unix.close s;
           Utils.log_string (Printf.sprintf "Failed to connect to %s:%d : %s\n" onionaddr !Config.ltcrpcport (Printexc.to_string e));
           raise Exit
       with exn ->
         Unix.close s;
         raise exn         
     end
  | None ->
     let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
     try
       let ia = Unix.inet_addr_of_string !Config.ltcrpcip in
       Unix.connect s (Unix.ADDR_INET(ia, !Config.ltcrpcport));
       let sin = Unix.in_channel_of_descr s in
       let sout = Unix.out_channel_of_descr s in
       set_binary_mode_in sin true;
       set_binary_mode_out sout true;
       Printf.fprintf sout "POST / HTTP/1.1\n";
       Printf.fprintf sout "Host: %s:%d\n" !Config.ltcrpcip !Config.ltcrpcport;
       Printf.fprintf sout "Authorization: Basic %s\n" (ltcrpcauth());
       Printf.fprintf sout "User-Agent: Proofgold/0.2.8\n";
       Printf.fprintf sout "Accept: */*\n";
       Printf.fprintf sout "content-type: text/plain;\n";
       (s,sin,sout)
     with exn ->
           Unix.close s;
           raise exn

let skip_to_blankline sin =
  try
    while true do
      let l = input_line sin in
      if l = "" || l = "\r" then raise Exit
    done
  with Exit -> ()

let alertcandidatetxs : string list ref = ref []

let swapcandidatetxs : string list ref = ref []
type swapbuyoffertype =
  | SimpleSwapBuyOffer of string * addr * int64 * int64

let swapbuyoffers : (hashval * float * swapbuyoffertype) list ref = ref []

let unburned_headers : (hashval,(hashval * hashval) -> unit) Hashtbl.t = Hashtbl.create 100
let unburned_deltas : (hashval,(hashval * hashval) -> unit) Hashtbl.t = Hashtbl.create 100

module DbInvalidatedBlocks = Dbbasic2 (struct type t = bool let basedir = "invalidatedblocks" let seival = sei_bool seic let seoval = seo_bool seoc end)

type poburn =
  | Poburn of md256 * md256 * int64 * int64 * hashval * int32 (** ltc block hash id, ltc tx hash id, ltc block median time, number of litoshis burned, txid of firsttxid input spent, vout of first input spent **)

let hashpoburn p =
  match p with
  | Poburn(h,k,x,y,txid,vout) -> hashtag (hashpair (hashpair h k) (hashpair (hashpair (hashint64 x) (hashint64 y)) (hashtag txid vout))) 194l

let seo_poburn o p c =
  match p with
  | Poburn(h,k,x,y,txid,vout) ->
      let c = seo_md256 o h c in
      let c = seo_md256 o k c in
      let c = seo_int64 o x c in
      let c = seo_int64 o y c in
      let c = seo_hashval o txid c in
      let c = seo_int32 o vout c in
      c

let sei_poburn i c =
  let (h,c) = sei_md256 i c in
  let (k,c) = sei_md256 i c in
  let (x,c) = sei_int64 i c in
  let (y,c) = sei_int64 i c in
  let (txid,c) = sei_hashval i c in
  let (vout,c) = sei_int32 i c in
  (Poburn(h,k,x,y,txid,vout),c)

(*** mainnet ***)
let ltc_oldest_to_consider = ref (hexstring_hashval "ccca3ef9b5dcb0a01de0d776ae6d3bde0febda0b581553e768d91d1029e82cd5") (** block on June 8 2020 **)
let ltc_oldest_to_consider_time = ref 1591626833L (** median time on June 8 2020 **)
let ltc_oldest_to_consider_height = ref 1855917L (** block height on June 8 2020 **)

(*** testnet ***)
let ltctestnet () =
  ltc_oldest_to_consider := hexstring_hashval "0c1b15b7531f59417705457be47152d4278471036e4745f135c41600c9c94742";
  ltc_oldest_to_consider_time := 1591290167L;
  ltc_oldest_to_consider_height := 1494039L

let ltc_bestblock = ref (0l,0l,0l,0l,0l,0l,0l,0l)

let burntx : (hashval,string) Hashtbl.t = Hashtbl.create 100

type ltcpfgstatus = LtcPfgStatusPrev of hashval | LtcPfgStatusNew of (int64 * (hashval * hashval * hashval * int64 * int64) list) list

let ltcrpc_url () =
  match !Config.ltcrpconion with
  | Some(o) ->
      "http://" ^ o ^ ":" ^ (string_of_int !Config.ltcrpcport) ^ "/"
  | None ->
      "http://" ^ !Config.ltcrpcip ^ ":" ^ (string_of_int !Config.ltcrpcport) ^ "/"

let seo_ltcpfgstatus o s c =
  match s with
  | LtcPfgStatusPrev(h) ->
      let c = o 1 0 c in
      seo_hashval o h c
  | LtcPfgStatusNew(l) ->
      let c = o 1 1 c in
      seo_list (seo_prod seo_int64 (seo_list (seo_prod5 seo_hashval seo_hashval seo_hashval seo_int64 seo_int64))) o l c

let sei_ltcpfgstatus i c =
  let (x,c) = i 1 c in
  if x = 0 then
    let (h,c) = sei_hashval i c in
    (LtcPfgStatusPrev(h),c)
  else
    let (l,c) = sei_list (sei_prod sei_int64 (sei_list (sei_prod5 sei_hashval sei_hashval sei_hashval sei_int64 sei_int64))) i c in
    (LtcPfgStatusNew(l),c)

let ltcpfgstatush : (hashval,ltcpfgstatus) Hashtbl.t = Hashtbl.create 1000

module DbLtcPfgStatus = Dbbasic2 (struct type t = ltcpfgstatus let basedir = "ltcpfgstatus" let seival = sei_ltcpfgstatus seic let seoval = seo_ltcpfgstatus seoc end)

(*** h is the id of an ltcblock, so it should always uniquely determine the ltcpfgstatus (all proofgold blockid burns from the past week in order). ***)
let rec ltcpfgstatus_dbget h =
  try
    let z =
      try
	Hashtbl.find ltcpfgstatush h
      with Not_found ->
	let z = DbLtcPfgStatus.dbget h in
	Hashtbl.add ltcpfgstatush h z;
	z
    in
    match z with
    | LtcPfgStatusPrev(k) ->
	ltcpfgstatus_dbget k
    | LtcPfgStatusNew(l) -> (h,l)
  with Not_found -> (!ltc_oldest_to_consider,[])

let json_assoc_string k al =
  match List.assoc k al with
  | JsonStr(x) -> x
  | _ -> raise Not_found

let json_assoc_int64 k al =
  match List.assoc k al with
  | JsonNum(x) -> Int64.of_string x
  | _ -> raise Not_found

let json_assoc_int k al =
  match List.assoc k al with
  | JsonNum(x) -> int_of_string x
  | _ -> raise Not_found

let litecoins_of_litoshis v =
  let w = Int64.div v 100000000L in
  let d = Int64.to_string (Int64.rem v 100000000L) in
  let dl = String.length d in
  let ez = ref 0 in
  begin
    try
      for i = dl-1 downto 0 do
	if d.[i] = '0' then
	  incr ez
	else
	  raise Exit
      done
    with Exit -> ()
  end;
  let b = Buffer.create 20 in
  Buffer.add_string b (Int64.to_string w);
  Buffer.add_char b '.';
  for i = 1 to 11 - dl do
    Buffer.add_char b '0'
  done;
  for i = 0 to dl - (1 + !ez) do
    Buffer.add_char b d.[i]
  done;
  Buffer.contents b

let litoshis_of_litecoins s =
  let f = ref 0L in
  let w = ref true in
  let c = ref 0L in
  let d = ref 10000000L in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    let cc = Char.code s.[!i] in
    incr i;
    if !w then
      if cc = 46 then
	w := false
      else if cc >= 48 && cc < 58 then
	f := Int64.add (Int64.mul !f 10L) (Int64.of_int (cc-48))
      else
	raise (Failure ("cannot interpret " ^ s ^ " as a number of litecoins"))
    else
      if cc >= 48 && cc < 58 then
	begin
	  c := Int64.add !c (Int64.mul !d (Int64.of_int (cc-48)));
	  d := Int64.div !d 10L
	end
      else
	raise (Failure ("cannot interpret " ^ s ^ " as a number of litecoins"))
  done;
  Int64.add (Int64.mul !f 100000000L) !c

let json_assoc_litoshis k al =
  match List.assoc k al with
  | JsonNum(x) -> litoshis_of_litecoins x
  | _ -> raise Not_found

let ltc_getbestblockhash () =
  try
    if !Config.ltcoffline then
      begin
	Printf.printf "call getbestblockhash in ltc\n>> "; flush stdout;
	let h = read_line() in
	h
      end
    else
      begin
        let call = "{\"jsonrpc\": \"1.0\", \"id\":\"gbbh\", \"method\": \"getbestblockhash\", \"params\": [] }" in
        try
          if !Config.ltcrpcavoidcurl then
            begin
              let (s,sin,sout) = ltcrpc_connect () in
              Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
              Printf.fprintf sout "%s\n" call;
              flush sout;
              skip_to_blankline sin;
              let l = input_line sin in
              shutdown_close s;
              match parse_jsonval l with
              | (JsonObj(al),_) -> json_assoc_string "result" al
              | _ ->
                 (Utils.log_string (Printf.sprintf "problem return from ltc getbestblockhash:\n%s\n" l));
	         raise Exit (* retry using curl *)
            end
          else
            raise Exit
        with
        | Exit -> (* fall back on curl *)
           let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
           let url = ltcrpc_url() in
           let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
           let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
           let l = input_line inc in
           ignore (Unix.close_process_full (inc,outc,errc));
           match parse_jsonval l with
           | (JsonObj(al),_) -> json_assoc_string "result" al
           | _ ->
              (Utils.log_string (Printf.sprintf "problem return from ltc getbestblockhash:\n%s\n" l));
	      raise Not_found
      end
  with _ ->
    raise Not_found

let proofgold_candidate_p h =
  String.length h = 64 && h.[0] = '5' && h.[1] = '0' && h.[2] = '6' && h.[3] = '6'

let proofgold_swap_candidate_p h =
  String.length h = 64 && h.[0] = '5' && h.[1] = '0' && h.[2] = '5' && h.[3] = '3'

let proofgold_alert_candidate_p h =
  String.length h = 64 && h.[0] = '5' && h.[1] = '0' && h.[2] = '4' && h.[3] = '1'

let ltc_getblockheight h =
  try
    let l =
      if !Config.ltcoffline then
	begin
	  Printf.printf "call getblock %s in ltc\n>> " h; flush stdout;
	  read_line()
	end
      else
        begin
	  let call = "{\"jsonrpc\": \"1.0\", \"id\":\"gb\", \"method\": \"getblock\", \"params\": [\"" ^ h ^ "\"] }" in
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with
          | Exit -> (* fall back on curl *)
	     let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
	     let url = ltcrpc_url() in
	     let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
	     let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
	     let l = input_line inc in
	     ignore (Unix.close_process_full (inc,outc,errc));
	     l
        end
    in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
	begin
	  match List.assoc "result" al with
	  | JsonObj(bl) ->
	      begin
		let hght = json_assoc_int64 "height" bl in
                hght
	      end
	  | _ ->
	      (Utils.log_string (Printf.sprintf "problem return from ltc getblock:\n%s\n" l));
	      raise Not_found
	end
    | _ ->
	(Utils.log_string (Printf.sprintf "problem return from ltc getblock:\n%s\n" l));
	raise Not_found
  with _ ->
    raise Not_found
  
let ltc_getblock h =
  try
    let l =
      if !Config.ltcoffline then
	begin
	  Printf.printf "call getblock %s in ltc\n>> " h; flush stdout;
	  read_line()
	end
      else
        begin
	  let call = "{\"jsonrpc\": \"1.0\", \"id\":\"gb\", \"method\": \"getblock\", \"params\": [\"" ^ h ^ "\"] }" in
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with Exit -> (* fall back on curl *)
	    let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
	    let url = ltcrpc_url() in
	    let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
	    let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
	    let l = input_line inc in
	    ignore (Unix.close_process_full (inc,outc,errc));
	    l
        end
    in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
	begin
	  match List.assoc "result" al with
	  | JsonObj(bl) ->
	      begin
		let pbh = json_assoc_string "previousblockhash" bl in
		let nbh =
                  try
                    Some(json_assoc_string "nextblockhash" bl)
                  with Not_found -> None
                in
		let tm = json_assoc_int64 "mediantime" bl in
		let hght = json_assoc_int64 "height" bl in
		let txl = ref [] in
		match List.assoc "tx" bl with
		| JsonArr(txs) ->
		    begin
		      List.iter
			(fun jtxh ->
			  match jtxh with
			  | JsonStr(txh) when proofgold_candidate_p txh -> txl := txh::!txl
                          | JsonStr(txh) when proofgold_swap_candidate_p txh -> swapcandidatetxs := txh::!swapcandidatetxs
                          | JsonStr(txh) when proofgold_alert_candidate_p txh ->
                             alertcandidatetxs := txh::!alertcandidatetxs
			  | _ -> ())
			txs;
		      (pbh,tm,hght,!txl,nbh)
		    end
		| _ ->
		    (Utils.log_string (Printf.sprintf "problem return from ltc getblock:\n%s\n" l));
		    raise Not_found
	      end
	  | _ ->
	      (Utils.log_string (Printf.sprintf "problem return from ltc getblock:\n%s\n" l));
	      raise Not_found
	end
    | _ ->
	(Utils.log_string (Printf.sprintf "problem return from ltc getblock:\n%s\n" l));
	raise Not_found
  with _ ->
    raise Not_found

type ltcutxo =
  | LtcP2shSegwit of (string * int * string * string * string * int64)
  | LtcBech32 of (string * int * string * string * int64)

let ltc_listunspent_gen addrl =
  try
    let l =
      if !Config.ltcoffline then
	begin
	  Printf.printf "call listunspent in ltc\n>> "; flush stdout;
	  read_line()
	end
      else
        begin
	  let addrlb = Buffer.create 40 in
	  let fstaddr = ref true in
	  List.iter
	    (fun a ->
	      if !fstaddr then fstaddr := false else Buffer.add_char addrlb ',';
	      Buffer.add_char addrlb '"';
	      Buffer.add_string addrlb a;
	      Buffer.add_char addrlb '"')
            addrl;
          let call = "{\"jsonrpc\": \"1.0\", \"id\":\"lu\", \"method\": \"listunspent\", \"params\": [1,9999999,[" ^ (Buffer.contents addrlb) ^ "]] }" in
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with Exit -> (* fall back on curl *)
	    let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
	    let url = ltcrpc_url() in
            let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
	    let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
	    let l = input_line inc in
	    ignore (Unix.close_process_full (inc,outc,errc));
	    l
        end
    in
    let utxol = ref [] in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
	begin
	  match List.assoc "result" al with
	  | JsonArr(ul) ->
	      begin
		List.iter
		  (fun u ->
		    match u with
		    | JsonObj(bl) ->
			begin
			  try
			    let ltcaddr = json_assoc_string "address" bl in
			    if ltcaddr = "" then raise Not_found;
			    if ltcaddr.[0] = 'M' || (!Config.testnet && ltcaddr.[0] = 'Q') then (*** p2sh segwit ***)
			      let txh = json_assoc_string "txid" bl in
			      let vout = json_assoc_int "vout" bl in
			      let rs = json_assoc_string "redeemScript" bl in
			      let spk = json_assoc_string "scriptPubKey" bl in
			      let amt = json_assoc_litoshis "amount" bl in
			      utxol := LtcP2shSegwit(txh,vout,ltcaddr,rs,spk,amt)::!utxol
			    else if ltcaddr.[0] = 'l' || (!Config.testnet && ltcaddr.[0] = 't') then (*** bech32 ***)
			      let txh = json_assoc_string "txid" bl in
			      let vout = json_assoc_int "vout" bl in
			      let spk = json_assoc_string "scriptPubKey" bl in
			      let amt = json_assoc_litoshis "amount" bl in
			      utxol := LtcBech32(txh,vout,ltcaddr,spk,amt)::!utxol
			    else
			      raise Not_found
			  with Not_found ->
			    ()
			end
		    | _ -> ())
		  ul;
		!utxol
	      end
	  | _ ->
	      (Utils.log_string (Printf.sprintf "problem return from ltc listunspent:\n%s\n" l));
	      raise Not_found
	end
    | _ ->
	(Utils.log_string (Printf.sprintf "problem return from ltc listunspent:\n%s\n" l));
	raise Not_found
  with _ ->
    raise Not_found

let ltc_listunspent () = ltc_listunspent_gen !Config.ltcaddresses
      
exception InsufficientLtcFunds

let le_num24 x =
  let strb = Buffer.create 3 in
  Buffer.add_char strb (Char.chr (x land 255));
  Buffer.add_char strb (Char.chr ((x lsr 8) land 255));
  Buffer.add_char strb (Char.chr ((x lsr 16) land 255));
  Buffer.contents strb

let findpfgtx txs1 txs2 =
  let i = ref (-1) in
  let rtxid = ref (0l,0l,0l,0l,0l,0l,0l,0l) in
  let txs = ref "" in
  let pfgid ri =
    let (_,_,_,_,_,_,_,x) = ri in
    Int32.logand x 0xffffl = 0x6650l
  in
  while not (pfgid !rtxid) do
    incr i;
    if !i >= 16777216 then raise Not_found; (** probably will never happen **)
    txs := txs1 ^ (le_num24 !i) ^ txs2;
    rtxid := Sha256.sha256dstr !txs
  done;
  (!i,!rtxid,!txs);;

let findpfgswaptx txs1 txs2 =
  let i = ref (-1) in
  let rtxid = ref (0l,0l,0l,0l,0l,0l,0l,0l) in
  let txs = ref "" in
  let pfgswapid ri =
    let (_,_,_,_,_,_,_,x) = ri in
    Int32.logand x 0xffffl = 0x5350l
  in
  while not (pfgswapid !rtxid) do
    incr i;
    if !i >= 16777216 then raise Not_found; (** probably will never happen **)
    txs := txs1 ^ (le_num24 !i) ^ txs2;
    rtxid := Sha256.sha256dstr !txs
  done;
  (!i,!rtxid,!txs);;

let blnum32 x =
  [Int32.to_int (Int32.logand x 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 8) 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 16) 255l);
   Int32.to_int (Int32.logand (Int32.shift_right_logical x 24) 255l)]

let blnum64 x =
  [Int64.to_int (Int64.logand x 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 8) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 16) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 24) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 32) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 40) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 48) 255L);
   Int64.to_int (Int64.logand (Int64.shift_right_logical x 56) 255L)]

let ltc_createburntx_spec u h1 h2 toburn =
  let toburn_plus_fee = Int64.add toburn !Config.ltctxfee in
  let createburntx txid vout spk amt redeemfn =
    let changeamt = Int64.sub amt toburn_plus_fee in
    let txs1b = Buffer.create 100 in
    let txs2b = Buffer.create 100 in
    let txs3b = Buffer.create 100 in
    Buffer.add_string txs1b "\001"; (*** assume one input ***)
    let txidrh = hashval_rev (hexstring_hashval txid) in
    ignore (seo_hashval seosb txidrh (txs1b,None));
    List.iter (fun z -> Buffer.add_char txs1b (Char.chr z)) (blnum32 (Int32.of_int vout));
    let txs1 = Buffer.contents txs1b in
    redeemfn txs1b;
    if changeamt >= ltcdust then (** only create change if it is not dust **)
      Buffer.add_string txs2b "\255\255\255\255\002"
    else
      Buffer.add_string txs2b "\255\255\255\255\001";
    List.iter (fun z -> Buffer.add_char txs2b (Char.chr z)) (blnum64 toburn);
    let extradata = "" in
    let extradata = (*** before the May 2019 hard fork, do not burn enough to require pushing more than 75 bytes in the burn tx (and wait an extra day before burning more than 75 bytes even after the hard fork time, out of abundance of caution) ***)
      if 67 + String.length extradata > 80 then (** ltc will not relay OP_RETURN with more than 80 bytes; increase this if it changes **)
	""
      else
	extradata
    in
    let datalen = 67 + String.length extradata in
    if datalen > 252 then raise (Failure "too much data to burn");
    if datalen < 76 then
      begin
	Buffer.add_char txs2b (Char.chr (datalen+2));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr datalen); (*** PUSH datalen ***)
      end
    else if datalen > 65535 then
      raise (Failure "too much data to burn")
    else if datalen > 255 then
      begin
	Buffer.add_char txs2b (Char.chr (datalen+3));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr 77); (*** PUSH datalen ***)
	Buffer.add_char txs2b (Char.chr (datalen mod 256));
	Buffer.add_char txs2b (Char.chr (datalen / 256));
      end
    else 
      begin
	Buffer.add_char txs2b (Char.chr (datalen+3));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr 76); (*** PUSH datalen ***)
	Buffer.add_char txs2b (Char.chr datalen);
      end;
    ignore (seo_hashval seosb h1 (txs2b,None));
    ignore (seo_hashval seosb h2 (txs2b,None));
    for i = 0 to (String.length extradata) - 1 do
      Buffer.add_char txs2b extradata.[i]
    done;
    if changeamt >= ltcdust then
      begin
        List.iter (fun z -> Buffer.add_char txs3b (Char.chr z)) (blnum64 changeamt);
        let spks = hexstring_string spk in
        Buffer.add_char txs3b (Char.chr (String.length spks));
        Buffer.add_string txs3b spks;
      end;
    Buffer.add_string txs3b "\000\000\000\000"; (*** locktime ***)
    let txs2 = Buffer.contents txs2b in
    let txs3 = Buffer.contents txs3b in
    let (i,rtxid,txs) = findpfgtx ("\002\000\000\000" ^ (Buffer.contents txs1b) ^ txs2) txs3 in
    let txsb = Buffer.create 100 in
    Buffer.add_string txsb "\002\000\000\000";
    Buffer.add_string txsb txs1;
    Buffer.add_string txsb "\000";
    Buffer.add_string txsb txs2;
    Buffer.add_string txsb (le_num24 i);
    Buffer.add_string txsb txs3;
    let s = Buffer.contents txsb in
    Hashtbl.add burntx h2 s;
    s
  in
  match u with
  | LtcP2shSegwit(txid,vout,_,rs,spk,amt) ->
     let rs2 = hexstring_string rs in
     let rsl = String.length rs2 in
     if rsl < 1 || rsl > 75 then raise Not_found;
     createburntx
       txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b (Char.chr (1 + rsl));
	 Buffer.add_char txs1b (Char.chr rsl);
	 Buffer.add_string txs1b rs2)
  | LtcBech32(txid,vout,ltcaddr,spk,amt) ->
     createburntx
       txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b '\000')
       
let ltc_createburntx h1 h2 toburn =
  let utxol = ltc_listunspent () in
  let toburn_plus_fee = Int64.add toburn !Config.ltctxfee in
  try
    Hashtbl.find burntx h2
  with Not_found ->
    try
      (Utils.log_string (Printf.sprintf "Searching for an unspent litecoin tx with at least %Ld litoshis.\n" toburn_plus_fee));
      let u = (*** only consider single spends ***)
	List.find
	  (fun u ->
	    match u with
	    | LtcP2shSegwit(txid,vout,_,_,_,amt) -> amt >= toburn_plus_fee
	    | LtcBech32(txid,vout,_,_,amt) -> amt >= toburn_plus_fee)
	  utxol
      in
      ltc_createburntx_spec u h1 h2 toburn
    with Not_found -> raise InsufficientLtcFunds

let ltc_signrawtransaction txs =
  try
    let l =
      if !Config.ltcoffline then
	begin
	  Printf.printf "call signrawtransaction %s in ltc\n>> " txs; flush stdout;
	  read_line()
	end
      else
	let call =
	  if !Config.ltcversion >= 17 then
	    "{\"jsonrpc\": \"1.0\", \"id\":\"srtx\", \"method\": \"signrawtransactionwithwallet\", \"params\": [\"" ^ txs ^ "\"] }"
	  else
	    "{\"jsonrpc\": \"1.0\", \"id\":\"srtx\", \"method\": \"signrawtransaction\", \"params\": [\"" ^ txs ^ "\"] }"
	in
        begin
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with Exit -> (* fall back on curl *)
	    let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
	    let url = ltcrpc_url() in
	    let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
	    let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
	    let l = input_line inc in
	    ignore (Unix.close_process_full (inc,outc,errc));
	    l
        end
    in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
	begin 
	  match List.assoc "result" al with
	  | JsonObj(bl) -> json_assoc_string "hex" bl
	  | _ ->
	      (Utils.log_string (Printf.sprintf "problem return from ltc signrawtransaction:\n%s\n" l));
	      raise Not_found
	end
    | _ ->
	(Utils.log_string (Printf.sprintf "problem return from ltc signrawtransaction:\n%s\n" l));
	raise Not_found
  with _ -> raise Not_found

let ltc_sendrawtransaction txs =
  try
    let l =
      if !Config.ltcoffline then
	begin
	  Printf.printf "call sendrawtransaction %s in ltc\n>> " txs; flush stdout;
	  read_line()
	end
      else
        let call = "{\"jsonrpc\": \"1.0\", \"id\":\"srtx\", \"method\": \"sendrawtransaction\", \"params\": [\"" ^ txs ^ "\"] }" in
        begin
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with Exit -> (* fall back on curl *)
	    let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
	    let url = ltcrpc_url() in
	    let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
	    let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
	    let l = input_line inc in
	    ignore (Unix.close_process_full (inc,outc,errc));
	    l
        end
    in
    match parse_jsonval l with
    | (JsonObj(al),_) -> json_assoc_string "result" al
    | _ ->
	(Utils.log_string (Printf.sprintf "problem return from ltc sendrawtransaction:\n%s\n" l));
	raise Not_found
  with _ -> raise Not_found

exception NotAnLtcBurnTx

let donotretrypeer : (string,unit) Hashtbl.t = Hashtbl.create 100;;

let ltc_getburntransactioninfo h =
  let l =
    if !Config.ltcoffline then
      begin
	Printf.printf "call getrawtransaction %s in ltc\n>> " h; flush stdout;
	read_line()
      end
    else
      let call = "{\"jsonrpc\": \"1.0\", \"id\":\"grtx\", \"method\": \"getrawtransaction\", \"params\": [\"" ^ h ^ "\",1] }" in
      begin
        try
          if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
          else
            raise Exit
        with Exit -> (* fall back on curl *)
          let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
          let url = ltcrpc_url() in
          let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
          let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
          let l = input_line inc in
          ignore (Unix.close_process_full (inc,outc,errc));
          l
      end
  in
  try
    begin
      match parse_jsonval l with
      | (JsonObj(al),_) ->
         begin
	   match List.assoc "result" al with
	   | JsonObj(bl) ->
	      begin
	        match List.assoc "vout" bl with
	        | JsonArr(JsonObj(vout1)::_) ->
		   let litoshisburned = json_assoc_litoshis "value" vout1 in
		   begin
		     match List.assoc "scriptPubKey" vout1 with
		     | JsonObj(cl) ->
		        let hex = json_assoc_string "hex" cl in
		        if String.length hex >= 132 && hex.[0] = '6' && hex.[1] = 'a' && hex.[2] = '4' then
			  begin
			    let hex =
			      if hex.[3] = 'c' then (*** pushing up to 255 bytes ***)
			        String.sub hex 6 ((String.length hex) - 6)
			      else if hex.[3] = 'd' then (*** pushing up to 64K bytes ***)
			        String.sub hex 8 ((String.length hex) - 8)
			      else
			        String.sub hex 4 ((String.length hex) - 4)
			    in
			    let lprevtx = hexstring_hashval (String.sub hex 0 64) in
			    let dnxt = hexstring_hashval (String.sub hex 64 64) in
			    begin
			      let hexl = String.length hex in
			      if hexl > 132 then
			        let extradata = hexstring_string (String.sub hex 128 ((String.length hex) - 128)) in
			        if extradata.[0] = 'o' then
				  begin
				    if List.length !netconns < !Config.maxconns then
				      begin
				        let onionaddr = Buffer.create 10 in
				        try
					  for i = 1 to ((String.length extradata) - 1) do
					    if extradata.[i] = '.' then
					      begin
					        let peer = Printf.sprintf "%s.onion:20808" (Buffer.contents onionaddr) in
                                                if not (Hashtbl.mem donotretrypeer peer) then
                                                  begin
                                                    Hashtbl.add donotretrypeer peer ();
                                                    try
                                                      ignore (tryconnectpeer peer);
						      ignore (addknownpeer (Int64.of_float (Unix.time())) peer);
                                                    with BannedPeer -> ()
                                                  end;
					        raise Exit
					      end
					    else if extradata.[i] = ':' then
					      begin
					        if i+2 < String.length extradata then
						  begin
						    let port = (Char.code extradata.[i+1]) * 256 + (Char.code extradata.[i+2]) in
						    let peer = Printf.sprintf "%s.onion:%d" (Buffer.contents onionaddr) port in
                                                    if not (Hashtbl.mem donotretrypeer peer) then
                                                      begin
                                                        Hashtbl.add donotretrypeer peer ();
                                                        try
						          ignore (tryconnectpeer peer);
						          ignore (addknownpeer (Int64.of_float (Unix.time())) peer);
                                                        with BannedPeer -> ()
                                                      end
						  end
					        else
						  raise Exit
					      end
					    else
					      Buffer.add_char onionaddr extradata.[i]
					  done
				        with Exit -> ()
				      end
				  end
			        else if extradata.[0] = 'I' then
				  begin
				    if List.length !netconns < !Config.maxconns && ((String.length extradata) > 4) then
				      begin
				        let ip0 = Char.code extradata.[1] in
				        let ip1 = Char.code extradata.[2] in
				        let ip2 = Char.code extradata.[3] in
				        let ip3 = Char.code extradata.[4] in
				        let peer = Printf.sprintf "%d.%d.%d.%d:20805" ip0 ip1 ip2 ip3 in
                                        if not (Hashtbl.mem donotretrypeer peer) then
                                          begin
                                            Hashtbl.add donotretrypeer peer ();
                                            try
					      ignore (tryconnectpeer peer);
					      ignore (addknownpeer (Int64.of_float (Unix.time())) peer);
                                            with BannedPeer -> ()
                                          end
				      end
				  end
			        else if extradata.[0] = 'i' then
				  begin
				    if List.length !netconns < !Config.maxconns && ((String.length extradata) > 6) then
				      begin
				        let ip0 = Char.code extradata.[1] in
				        let ip1 = Char.code extradata.[2] in
				        let ip2 = Char.code extradata.[3] in
				        let ip3 = Char.code extradata.[4] in
				        let port = (Char.code extradata.[5]) * 256 + Char.code extradata.[6] in
				        let peer = Printf.sprintf "%d.%d.%d.%d:%d" ip0 ip1 ip2 ip3 port in
                                        if not (Hashtbl.mem donotretrypeer peer) then
                                          begin
                                            Hashtbl.add donotretrypeer peer ();
                                            try
					      ignore (tryconnectpeer peer);
					      ignore (addknownpeer (Int64.of_float (Unix.time())) peer);
                                            with BannedPeer -> ()
                                          end
				      end
				  end
			    end;
			    let lblkh =
			      begin
			        try
				  match List.assoc "blockhash" bl with
				  | JsonStr(lblkh) -> Some(lblkh)
				  | _ -> None
			        with Not_found -> None
			      end
			    in
			    let confs =
			      begin
			        try
				  match List.assoc "confirmations" bl with
				  | JsonNum(c) -> Some(int_of_string c)
				  | _ -> None
			        with _ -> None
			      end
			    in
                            match List.assoc "vin" bl with
	                    | JsonArr(JsonObj(vin1)::_) ->
                               let txid1 = json_assoc_string "txid" vin1 in
                               let vout1 = json_assoc_int "vout" vin1 in
			       (litoshisburned,lprevtx,dnxt,lblkh,confs,txid1,vout1)
                            | _ ->
	                       (* (Utils.log_string (Printf.sprintf "problem getting first utxo spent by ltc getrawtransaction:\n%s\n" l)); *)
			       raise NotAnLtcBurnTx
			  end
		        else
			  begin
                            (*			    (Utils.log_string (Printf.sprintf "problem return from ltc getrawtransaction:\n%s\n" l)); *)
			    raise NotAnLtcBurnTx
			  end
		     | _ ->
                        (*		        (Utils.log_string (Printf.sprintf "problem return from ltc getrawtransaction:\n%s\n" l)); *)
		        raise NotAnLtcBurnTx
		   end
	        | _ ->
                   (*		   (Utils.log_string (Printf.sprintf "problem return from ltc getrawtransaction:\n%s\n" l)); *)
		   raise NotAnLtcBurnTx
	      end
	   | _ ->
              (*	      (Utils.log_string (Printf.sprintf "problem return from ltc getrawtransaction:\n%s\n" l)); *)
	      raise NotAnLtcBurnTx
         end
      | _ ->
         (*         (Utils.log_string (Printf.sprintf "problem return from ltc getrawtransaction:\n%s\n" l)); *)
         raise NotAnLtcBurnTx
    end
  with JsonParseFail(_,_) -> raise NotAnLtcBurnTx

module DbLtcBurnTx = Dbbasic2 (struct type t = int64 * hashval * hashval * hashval * int32 let basedir = "ltcburntx" let seival = sei_prod5 sei_int64 sei_hashval sei_hashval sei_hashval sei_int32 seic let seoval = seo_prod5 seo_int64 seo_hashval seo_hashval seo_hashval seo_int32 seoc end)

module DbLtcBlock = Dbbasic2 (struct type t = hashval * int64 * int64 * hashval list let basedir = "ltcblock" let seival = sei_prod4 sei_hashval sei_int64 sei_int64 (sei_list sei_hashval) seic let seoval = seo_prod4 seo_hashval seo_int64 seo_int64 (seo_list seo_hashval) seoc end)

let rec merge_pfg_status bds =
  match bds with
  | [] -> []
  | (dh1,l1)::(dh2,l2)::bdr when dh1 = dh2 -> merge_pfg_status ((dh1,l1 @ l2)::bdr)
  | (dh1,l1)::bdr -> (dh1,l1)::merge_pfg_status bdr

let rec ltc_process_block h =
  let hh = hexstring_hashval h in
  if not (hh = !ltc_oldest_to_consider) && not (DbLtcBlock.dbexists hh) then
    begin
      let (prev,tm,hght,txhs,_) = ltc_getblock h in
      ltc_process_block prev;
      let prevh = hexstring_hashval prev in
      let genl = ref [] in
      let succl = ref [] in
      let txhhs = ref [] in
      List.iter
	(fun txh ->
	  let txhh = hexstring_hashval txh in
	  let handle txid1 vout1 burned lprevtx dnxt =
              insert_blockburn dnxt (hh,txhh);
	      if lprevtx = (0l,0l,0l,0l,0l,0l,0l,0l) then
		begin
		  (Utils.log_string (Printf.sprintf "Adding burn %s for genesis header %s\n" txh (hashval_hexstring dnxt)));
		  txhhs := txhh :: !txhhs;
		  genl := (txhh,burned,dnxt)::!genl;
		  if not (Db_outlinevals.dbexists (hashpair hh txhh)) then
		    begin
		      Db_outlinevals.dbput (hashpair hh txhh) (dnxt,tm,burned,(txid1,vout1),None,hashpair hh txhh,1L);
		      (*** since the burn is presumably new, add to missing lists; this should never happen since the genesis phase has passed. ***)
		      missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(1L,dnxt)] !missingheaders;
		      missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(1L,dnxt)] !missingdeltas;
		      begin
			try
			  Hashtbl.find unburned_headers dnxt (hh,txhh);
			  Hashtbl.remove unburned_headers dnxt
			with _ -> ()
		      end;
		      begin
			try
			  Hashtbl.find unburned_deltas dnxt (hh,txhh);
			  Hashtbl.remove unburned_deltas dnxt
			with _ -> ()
		      end
		    end
		end
	      else
		begin
		  try
                    if not (DbLtcBurnTx.dbexists lprevtx) then raise NotAnLtcBurnTx; (** if we do not already know about the alleged previous burn tx, then do not accept the new one. **)
		    let (_,_,dprev,lprevblkh,_,_,_) = ltc_getburntransactioninfo (hashval_hexstring lprevtx) in
		    (Utils.log_string (Printf.sprintf "Adding burn %s for header %s (txid1 %s vout1 %ld)\n" txh (hashval_hexstring dnxt) (hashval_hexstring txid1) vout1));
		    DbLtcBurnTx.dbput txhh (burned,lprevtx,dnxt,txid1,vout1);
		    txhhs := txhh :: !txhhs;
		    succl := (dprev,txhh,burned,dnxt)::!succl;
		    if not (Db_outlinevals.dbexists (hashpair hh txhh)) then
		      begin
			try
			  match lprevblkh with
			  | Some(lprevblkh) ->
			      let lprevblkh = hexstring_hashval lprevblkh in
			      let (_,_,_,_,_,_,dhght) = Db_outlinevals.dbget (hashpair lprevblkh lprevtx) in
			      let currhght = Int64.add 1L dhght in
			      Db_outlinevals.dbput (hashpair hh txhh) (dnxt,tm,burned,(txid1,vout1),Some(lprevblkh,lprevtx),hashpair hh txhh,currhght);
			      (*** since the burn is presumably new, add to missing lists (unless it was staked by the current node which is handled in staking module) ***)
			      missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dnxt)] !missingheaders;
			      missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dnxt)] !missingdeltas;
			      begin
				try
				  Hashtbl.find unburned_headers dnxt (hh,txhh);
				  Hashtbl.remove unburned_headers dnxt
				with _ -> ()
			      end;
			      begin
				try
				  Hashtbl.find unburned_deltas dnxt (hh,txhh);
				  Hashtbl.remove unburned_deltas dnxt
				with _ -> ()
			      end;
			  | None -> ()
			with Not_found -> ()
		      end
		  with
                  | NotAnLtcBurnTx ->
		     DbLtcBurnTx.dbdelete txhh
                  | Not_found ->
		     Utils.log_string (Printf.sprintf "Could not find parent ltc burn tx %s for burn %s for header %s\n" (hashval_hexstring lprevtx) txh (hashval_hexstring dnxt))
		end
	    in
	    try
	      let (burned,lprevtx,dnxt,txid1,vout1) = DbLtcBurnTx.dbget txhh in
	      handle txid1 vout1 burned lprevtx dnxt
	    with Not_found ->
	      begin
		try
		  let (burned,lprevtx,dnxt,_,_,txid1,vout1) = ltc_getburntransactioninfo txh in
                  let txid1 = hexstring_hashval txid1 in
                  let vout1 = Int32.of_int vout1 in
		  DbLtcBurnTx.dbput txhh (burned,lprevtx,dnxt,txid1,vout1);
		  handle txid1 vout1 burned lprevtx dnxt
		with NotAnLtcBurnTx ->
		  Utils.log_string (Printf.sprintf "Ignoring tx %s which does not appear to be a Proofgold burn tx\n" txh)
	      end)
	txhs;
      begin
	let (prevkey,pbds) = ltcpfgstatus_dbget prevh in
	let change = ref false in
	let bds = ref [] in
	if not (!genl = []) then
	  begin
	    if tm > Int64.add !Config.genesistimestamp 604800L then
	      begin
		(Utils.log_string (Printf.sprintf "Ignoring unexpected genesis blocks burned during what appears to be after the genesis phase:\n"));
		List.iter (fun (txhh,burned,dnxt) -> Printf.printf "%s %Ld %s\n" (hashval_hexstring txhh) burned (hashval_hexstring dnxt)) !genl
	      end
	    else (*** there has already been a genesis block created during the genesis phase, but a competing one (or more) was created; include it too ***)
	      begin
		(Utils.log_string (Printf.sprintf "%d genesis block(s) found.\n" (List.length !genl)));
		let pbdl = List.map (fun (txhh,burned,dnxt) -> (dnxt,hh,txhh,tm,hght)) !genl in
		change := true;
		bds := [(1L,pbdl)]
	      end
	  end;
	List.iter
	  (fun (dhght,pbdl) ->
	    let pbdl2 =
	      List.filter
		(fun (bh,lbh,ltx,ltm,lhght) -> if Int64.sub tm ltm <= 604800L || Int64.sub hght lhght <= 4032L then true else (change := true; false)) (*** only allow building on blocks from the past week (either <= 604800 seconds in ltc median block time or 4032 ltc blocks) ***)
		pbdl
	    in
	    if not (pbdl2 = []) then
	      begin
		let pbdl2b = List.sort (fun (_,_,_,_,lhght1) (_,_,_,_,lhght2) -> compare lhght1 lhght2) pbdl2 in
		bds := (dhght,pbdl2b) :: !bds;
	      end;
	    let pbdl3 = ref [] in
	    List.iter
	      (fun (bh,lbh,ltx,ltm,lhght) ->
		List.iter
		  (fun (dprev,txhh,burned,dnxt) ->
		    if bh = dprev then
		      begin
			pbdl3 := (dnxt,hh,txhh,tm,hght)::!pbdl3;
			change := true
		      end)
		  !succl)
	      pbdl2;
	    if not (!pbdl3 = []) then
	      begin
		pbdl3 := List.sort (fun (_,_,_,_,lhght1) (_,_,_,_,lhght2) -> compare lhght1 lhght2) !pbdl3;
		bds := (Int64.add dhght 1L,!pbdl3) :: !bds
	      end)
	  (List.rev pbds);
	if !change then
	  begin
	    let bds2 = List.sort (fun (dh1,_) (dh2,_) -> compare dh2 dh1) !bds in
	    let bds3 = merge_pfg_status bds2 in
	    DbLtcPfgStatus.dbput hh (LtcPfgStatusNew(bds3))
	  end
	else if not (prevkey = !ltc_oldest_to_consider) then
	  DbLtcPfgStatus.dbput hh (LtcPfgStatusPrev(prevkey)) (*** pointer to last ltc block where proofgold status changed ***)
      end;
      DbLtcBlock.dbput hh (prevh,tm,hght,!txhhs);
      let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
      let f = open_out (Filename.concat datadir "lastltcblock") in
      Printf.fprintf f "%s\n" h;
      close_out_noerr f
    end

let ltc_medtime () =
  try
    let (_,mtm,_,_) = DbLtcBlock.dbget !ltc_bestblock in
    mtm
  with Not_found -> Int64.of_float (Unix.time())

let ltc_synced () =
  try
    Utils.log_string (Printf.sprintf "Checking if ltc synced; bestblock %s\n" (hashval_hexstring !ltc_bestblock));
    let (_,tm,_,_) = DbLtcBlock.dbget !ltc_bestblock in
    Utils.log_string (Printf.sprintf "tm of ltc bestblock %Ld offset from now %f\n" tm (Unix.time() -. Int64.to_float tm));
    if Unix.time() -. Int64.to_float tm < 3600.0 then
      true
    else
      false
  with Not_found -> false

let ltc_tx_confirmed h =
  try
    let l =
      if !Config.ltcoffline then
        begin
	  Printf.printf "call getrawtransaction %s in ltc\n>> " h; flush stdout;
	  read_line()
        end
      else
        let call = "{\"jsonrpc\": \"1.0\", \"id\":\"grtx\", \"method\": \"getrawtransaction\", \"params\": [\"" ^ h ^ "\",1] }" in
        begin
          try
            if !Config.ltcrpcavoidcurl then
              begin
                let (s,sin,sout) = ltcrpc_connect () in
                Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                Printf.fprintf sout "%s\n" call;
                flush sout;
                skip_to_blankline sin;
                let l = input_line sin in
                shutdown_close s;
                l
              end
            else
              raise Exit
          with Exit -> (* fall back on curl *)
            let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
            let url = ltcrpc_url() in
            let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
            let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
            let l = input_line inc in
            ignore (Unix.close_process_full (inc,outc,errc));
            l
        end
    in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
       begin
	 match List.assoc "result" al with
	 | JsonObj(bl) ->
	    begin
	      match List.assoc "confirmations" bl with
	      | JsonNum(c) -> Some(int_of_string c)
	      | _ -> None
            end
         | _ -> None
       end
    | _ -> None
  with _ -> None

let ltc_tx_poburn h =
  try
    let (u,h1,h2,lblkh,confs,txid1,vout1) = ltc_getburntransactioninfo h in
    match lblkh with
    | Some(lbh) ->
	let (prev,tm,hght,txhs,_) = ltc_getblock lbh in
	Poburn(hexstring_md256 lbh,hexstring_md256 h,tm,u,hexstring_hashval txid1,Int32.of_int vout1)
    | _ -> raise Not_found
  with _ -> raise Not_found

let ltc_best_chaintips () =
  let (lastchangekey,ctips0l) = ltcpfgstatus_dbget !ltc_bestblock in
  let ctips1l =
    List.map (fun (_,ctips) -> List.filter (fun (h,_,_,_,_) -> not (DbBlacklist.dbexists h) && not (DbInvalidatedBlocks.dbexists h)) ctips) ctips0l
  in
  let ctips2l = List.filter (fun ctips -> not (ctips = [])) ctips1l in
  List.map (fun ctips -> List.map (fun (h,_,_,_,_) -> h) ctips) ctips2l

let find_pfg_header_ltc_burn h =
  let tried : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
  let rec find_pfg_header_ltc_burn_rec lbhl =
    match lbhl with
    | [] -> raise Not_found
    | lbh::lbhr ->
	if Hashtbl.mem tried lbh then
	  find_pfg_header_ltc_burn_rec lbhr
	else
	  let (lastchangekey,ctips0l) = ltcpfgstatus_dbget lbh in
	  let ctips1l =
	    List.map (fun (_,ctips) -> List.filter (fun (h,_,_,_,_) -> not (DbBlacklist.dbexists h) && not (DbInvalidatedBlocks.dbexists h)) ctips) ctips0l
	  in
	  let ctips2l = List.filter (fun ctips -> not (ctips = [])) ctips1l in
	  match ctips2l with
	  | [] -> raise Not_found
	  | (bestctips::_) ->
	      try
		let (dbh,lbh,ltx,ltm,lhght) = List.find (fun (dbh,_,_,_,_) -> dbh = h) bestctips in
		let (burned,lprevtx,dnxt,_,_) = DbLtcBurnTx.dbget ltx in
		let pob = ltc_tx_poburn (hashval_hexstring ltx) in
		let optionprevdalblock =
		  if lprevtx = (0l,0l,0l,0l,0l,0l,0l,0l) then
		    None
		  else
		    let (_,_,dprev,_,_) = DbLtcBurnTx.dbget lprevtx in
		    Some(dprev)
		in
		(pob,optionprevdalblock)
	      with Not_found ->
		let lbhlr = ref lbhl in
		List.iter
		  (fun (_,lbh,_,_,_) ->
		    try
		      let (prevlbh,_,_,_) = DbLtcBlock.dbget lbh in
		      lbhlr := prevlbh :: !lbhlr
		    with Not_found -> ())
		  bestctips;
		Hashtbl.add tried lbh ();
		find_pfg_header_ltc_burn_rec !lbhlr
  in
  find_pfg_header_ltc_burn_rec [!ltc_bestblock]

let rec delete_to_ltc_block kfrom k =
  try
    let (prevh,_,_,_) = DbLtcBlock.dbget k in
    DbLtcPfgStatus.dbdelete k;
    DbLtcBlock.dbdelete k;
    if k = kfrom then
      begin
	DbLtcPfgStatus.dbpurge ();
	DbLtcBlock.dbpurge ()
      end
    else
      delete_to_ltc_block kfrom prevh
  with Not_found ->
    let (prev,_,_,_,_) = ltc_getblock (hashval_hexstring k) in
    let prevh = hexstring_hashval prev in
    DbLtcPfgStatus.dbdelete k;
    if k = kfrom then
      begin
	DbLtcPfgStatus.dbpurge ();
	DbLtcBlock.dbpurge ()
      end
    else
      delete_to_ltc_block kfrom prevh

let retractltcblock h =
  let k = hexstring_hashval h in
  let hnow = ltc_getbestblockhash () in
  let know = hexstring_hashval hnow in
  delete_to_ltc_block k know

let rec ltc_forward_from_block lbh =
  ltc_process_block lbh;
  let (prev,tm,hght,txhs,nbh) = ltc_getblock lbh in
  match nbh with
  | Some(nbh) -> ltc_forward_from_block nbh
  | None -> ()

(** if the oldest possible ltc block has not been processed (initial sync), then start from there **)
let rec ltc_forward_from_oldest_possible () =
  let h = !ltc_oldest_to_consider in
  let (_,_,_,_,nbh) = ltc_getblock (hashval_hexstring h) in
  match nbh with
  | None -> ()
  | Some(nbh) ->
     if not (DbLtcBlock.dbexists (hexstring_hashval nbh)) then ltc_forward_from_block nbh

let rec ltc_forward_from_oldest () =
  let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
  let fn = Filename.concat datadir "lastltcblock" in
  if Sys.file_exists fn then
    let f = open_in (Filename.concat datadir "lastltcblock") in
    try
      let l = input_line f in
      close_in_noerr f;
      ltc_forward_from_block l
    with _ ->
      close_in_noerr f;
      ltc_forward_from_oldest_possible()
  else
    begin
      try
        if !Config.independentbootstrap then
	  ltc_forward_from_oldest_possible()
        else
          begin
            let fullcall = Printf.sprintf "%s %s/lastltcblock" !Config.curl !Config.bootstrapurl in
            let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
            try
              let l = input_line inc in
              ignore (Unix.close_process_full (inc,outc,errc));
              if String.length l = 64 then
                ltc_forward_from_block l
              else
                raise Exit
            with _ ->
              ignore (Unix.close_process_full (inc,outc,errc));
              raise Exit
          end
      with Exit ->
        ltc_forward_from_oldest_possible()
    end

(** swap orders coordinated via ltc **)
let ltc_createswapoffertx_spec u pbeta litoshis atoms =
  let createswapoffertx lbeta txid vout spk amt redeemfn =
    let changeamt = Int64.sub amt (Int64.add litoshis !Config.ltctxfee) in
    let txs1b = Buffer.create 100 in
    let txs2b = Buffer.create 100 in
    let txs3b = Buffer.create 100 in
    Buffer.add_string txs1b "\001"; (*** assume one input ***)
    let txidrh = hashval_rev (hexstring_hashval txid) in
    ignore (seo_hashval seosb txidrh (txs1b,None));
    List.iter (fun z -> Buffer.add_char txs1b (Char.chr z)) (blnum32 (Int32.of_int vout));
    let txs1 = Buffer.contents txs1b in
    redeemfn txs1b;
    if changeamt >= ltcdust then (** only create change if it is not dust **)
      Buffer.add_string txs2b "\255\255\255\255\003"
    else
      Buffer.add_string txs2b "\255\255\255\255\002";
    List.iter (fun z -> Buffer.add_char txs2b (Char.chr z)) (blnum64 0L); (** burning nothing here **)
    let (bp,b0,b1,b2,b3,b4) = pbeta in
    if not (bp = 0) then raise (Failure "Proofgold address for swap must be p2pkh");
    let datasb = Buffer.create 28 in
    let c = seo_md160 seosb (b0,b1,b2,b3,b4) (datasb,None) in
    seosbf (seo_int64 seosb atoms c);
    let data = Buffer.contents datasb in
    let datalen = 4 + String.length data in (** 1 'header byte' + 3 extra bytes for the nonce **)
    if datalen >= 76 then raise (Failure "swap order too big; should never happen");
    Buffer.add_char txs2b (Char.chr (datalen+2));
    Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
    Buffer.add_char txs2b (Char.chr datalen); (*** PUSH datalen ***)
    Buffer.add_char txs2b '\000'; (** header byte giving the type of swap offer **)
    for i = 0 to (String.length data) - 1 do
      Buffer.add_char txs2b data.[i]
    done;
    List.iter (fun z -> Buffer.add_char txs3b (Char.chr z)) (blnum64 litoshis);
    let spks = hexstring_string spk in
    Buffer.add_char txs3b (Char.chr (String.length spks));
    Buffer.add_string txs3b spks;
    if changeamt >= ltcdust then
      begin
        List.iter (fun z -> Buffer.add_char txs3b (Char.chr z)) (blnum64 changeamt);
        let spks = hexstring_string spk in
        Buffer.add_char txs3b (Char.chr (String.length spks));
        Buffer.add_string txs3b spks;
      end;
    Buffer.add_string txs3b "\000\000\000\000"; (*** locktime ***)
    let txs2 = Buffer.contents txs2b in
    let txs3 = Buffer.contents txs3b in
    let (i,rtxid,txs) = findpfgswaptx ("\002\000\000\000" ^ (Buffer.contents txs1b) ^ txs2) txs3 in
    let txsb = Buffer.create 100 in
    Buffer.add_string txsb "\002\000\000\000";
    Buffer.add_string txsb txs1;
    Buffer.add_string txsb "\000";
    Buffer.add_string txsb txs2;
    Buffer.add_string txsb (le_num24 i);
    Buffer.add_string txsb txs3;
    let txs = Buffer.contents txsb in
    let txss = ltc_signrawtransaction (string_hexstring txs) in
    ltc_sendrawtransaction txss
  in
  match u with
  | LtcP2shSegwit(txid,vout,ltcaddr,rs,spk,amt) ->
     let rs2 = hexstring_string rs in
     let rsl = String.length rs2 in
     if rsl < 1 || rsl > 75 then raise Not_found;
     createswapoffertx
       ltcaddr txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b (Char.chr (1 + rsl));
	 Buffer.add_char txs1b (Char.chr rsl);
	 Buffer.add_string txs1b rs2)
  | LtcBech32(txid,vout,ltcaddr,spk,amt) ->
     createswapoffertx
       ltcaddr txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b '\000')
       
let ltc_createswapoffertx pbeta litoshis atoms =
  let utxol = ltc_listunspent_gen !Config.ltctradeaddresses in
  let minamt_plus_fee = Int64.add litoshis !Config.ltctxfee in
  if not (p2pkhaddr_p pbeta) then raise (Failure "Proofgold address for swap must be p2pkh");
  try
    (Utils.log_string (Printf.sprintf "Searching for an unspent litecoin tx with at least %Ld litoshis.\n" minamt_plus_fee));
    let u = (*** only consider single spends ***)
      List.find
	(fun u ->
	  match u with
	  | LtcP2shSegwit(txid,vout,_,_,_,amt) -> false (* only allow bech32 here *)
	  | LtcBech32(txid,vout,_,_,amt) -> (* skip those with vout=1 since those might be swap offers waiting to be filled *)
             not (vout = 1) && amt >= minamt_plus_fee)
	utxol
    in
    ltc_createswapoffertx_spec u pbeta litoshis atoms
  with Not_found -> raise InsufficientLtcFunds

let ltc_cancelswapbuyoffer txid =
  if !Config.ltcoffline then raise (Failure "ltcoffline");
  let l =
    begin
      let call = "{\"jsonrpc\": \"1.0\", \"id\":\"gtxout\", \"method\": \"gettxout\", \"params\": [\"" ^ txid ^ "\",1] }" in
      begin
        try
          if !Config.ltcrpcavoidcurl then
            begin
              let (s,sin,sout) = ltcrpc_connect () in
              Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
              Printf.fprintf sout "%s\n" call;
              flush sout;
              skip_to_blankline sin;
              let l = input_line sin in
              shutdown_close s;
              l
            end
          else
            raise Exit
        with Exit -> (* fall back on curl *)
          let url = ltcrpc_url() in
          let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
          let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
          let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
          let l = input_line inc in
          ignore (Unix.close_process_full (inc,outc,errc));
          l
      end
    end
  in
  try
    let createmovetransaction txid vout spk litoshis = (* one input one output *)
      let txsb = Buffer.create 100 in
      Buffer.add_string txsb "\002\000\000\000\001"; (* version 2 one input *)
      let txidrh = hashval_rev (hexstring_hashval txid) in
      ignore (seo_hashval seosb txidrh (txsb,None));
      List.iter (fun z -> Buffer.add_char txsb (Char.chr z)) (blnum32 (Int32.of_int vout));
      Buffer.add_char txsb '\000'; (* empty sig *)
      Buffer.add_string txsb "\255\255\255\255";
      Buffer.add_char txsb '\001'; (* one output *)
      List.iter (fun z -> Buffer.add_char txsb (Char.chr z)) (blnum64 litoshis);
      let spks = hexstring_string spk in
      Buffer.add_char txsb (Char.chr (String.length spks));
      Buffer.add_string txsb spks;
      Buffer.add_string txsb "\000\000\000\000"; (* locktime *)
      let txs = Buffer.contents txsb in
      let txss = ltc_signrawtransaction (string_hexstring txs) in
      ignore (ltc_sendrawtransaction txss)
    in
    match parse_jsonval l with
    | (JsonObj(al),_) ->
       begin
	 match List.assoc "result" al with
	 | JsonObj(bl) ->
	    let litoshis = json_assoc_litoshis "value" bl in
            if litoshis > !Config.ltctxfee then
              begin
                match List.assoc "scriptPubKey" bl with
		| JsonObj(cl) ->
		   let hex = json_assoc_string "hex" cl in
                   createmovetransaction txid 1 hex (Int64.sub litoshis !Config.ltctxfee)
                | _ -> ()
              end
         | _ -> ()
       end
    | _ -> ()
  with _ -> ()

let ltc_getswaptransactioninfo h =
  let hh = hexstring_hashval h in
  if not (List.exists (fun (hh2,_,_) -> hh2 = hh) !swapbuyoffers) then (** if don't already have **)
    begin
      let l =
        if !Config.ltcoffline then
          begin
	    Printf.printf "call getrawtransaction %s in ltc\n>> " h; flush stdout;
	    read_line()
          end
        else
          let call = "{\"jsonrpc\": \"1.0\", \"id\":\"grtx\", \"method\": \"getrawtransaction\", \"params\": [\"" ^ h ^ "\",1] }" in
          begin
            try
              if !Config.ltcrpcavoidcurl then
                begin
                  let (s,sin,sout) = ltcrpc_connect () in
                  Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
                  Printf.fprintf sout "%s\n" call;
                  flush sout;
                  skip_to_blankline sin;
                  let l = input_line sin in
                  shutdown_close s;
                  l
                end
              else
                raise Exit
            with Exit -> (* fall back on curl *)
              let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
              let url = ltcrpc_url() in
              let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
              let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
              let l = input_line inc in
              ignore (Unix.close_process_full (inc,outc,errc));
              l
          end
      in
      try
        begin
          match parse_jsonval l with
          | (JsonObj(al),_) ->
             begin
	       match List.assoc "result" al with
	       | JsonObj(bl) ->
	          begin
	            match List.assoc "vout" bl with
	            | JsonArr(JsonObj(vout1)::JsonObj(vout2)::_) ->
		       let litoshis = json_assoc_litoshis "value" vout2 in
                       begin
		         match List.assoc "scriptPubKey" vout2 with
                         | JsonObj(cl) ->
                            if json_assoc_string "type" cl = "witness_v0_keyhash" then
                              begin
                                match List.assoc "addresses" cl with
                                | JsonArr([JsonStr(lbeta)]) ->
		                   begin
                                     begin
		                       try
			                 match List.assoc "confirmations" bl with
			                 | JsonNum(c) ->
                                            if int_of_string c <= 2 then raise Exit (** wait until three confirmations **)
			                 | _ ->
                                            raise Exit
		                       with exc ->
                                         raise Exit
		                     end;
		                     match List.assoc "scriptPubKey" vout1 with
		                     | JsonObj(cl) ->
		                        let hex = json_assoc_string "hex" cl in
		                        if String.length hex >= 8 && hex.[0] = '6' && hex.[1] = 'a' then
			                  begin
                                            let knd = String.sub hex 4 2 in
                                            if knd = "00" && String.length hex >= 60 then
                                              begin
			                        let hex = String.sub hex 6 ((String.length hex) - 6) in
                                                let datastr = hexstring_string hex in
                                                let c = (datastr,String.length datastr,None,0,0) in
                                                let ((b0,b1,b2,b3,b4),c) = sei_md160 seis c in
                                                let (atoms,_) = sei_int64 seis c in
                                                let pbeta = (0,b0,b1,b2,b3,b4) in
                                                let price = Int64.to_float litoshis *. 1000.0 /. Int64.to_float atoms in
                                                (Utils.log_string (Printf.sprintf "New Simple Swap Buy Offer: %s %s %s %Ld %Ld %f\n" h lbeta (Cryptocurr.addr_pfgaddrstr pbeta) atoms litoshis price));
                                                swapbuyoffers := List.merge (fun (_,p1,_) (_,p2,_) -> compare p2 p1) [(hh,price,SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis))] !swapbuyoffers;
                                                swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
			                      end
                                            else
                                              swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
			                  end
		                        else
			                  begin
                                            swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
			                  end
		                     | _ ->
                                        swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
		                   end
                                | _ ->
                                   swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
                              end
                            else
                              swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
                         | _ ->
                            swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
                       end
	            | _ ->
                       swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
	          end
	       | _ ->
                  swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
             end
          | _ ->
             swapcandidatetxs := List.filter (fun sh -> not (sh = h)) !swapcandidatetxs
        end
      with _ -> ()
    end

let ltc_unspent txid vout =
  if !Config.ltcoffline then raise (Failure "ltcoffline");
  let l =
    begin
      let call = "{\"jsonrpc\": \"1.0\", \"id\":\"gtxout\", \"method\": \"gettxout\", \"params\": [\"" ^ txid ^ "\"," ^ (string_of_int vout) ^ "] }" in
      try
        if !Config.ltcrpcavoidcurl then
          begin
            let (s,sin,sout) = ltcrpc_connect () in
            Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
            Printf.fprintf sout "%s\n" call;
            flush sout;
            skip_to_blankline sin;
            let l = input_line sin in
            shutdown_close s;
            l
          end
        else
          raise Exit
      with Exit -> (* fall back on curl *)
        let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
        let url = ltcrpc_url() in
        let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
        let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
        let l = input_line inc in
        ignore (Unix.close_process_full (inc,outc,errc));
        l
    end
  in
  try
    match parse_jsonval l with
    | (JsonObj(al),_) ->
       begin
	 match List.assoc "result" al with
	 | JsonObj(bl) -> true
         | _ -> false
       end
    | _ -> false
  with _ -> false
  
let ltc_scanforswapbuyoffers n =
  let rec scanforswapbuyoffers_r n h =
    if n > 0 then
      let (pbh,_,_,_,_) = ltc_getblock h in
      scanforswapbuyoffers_r (n-1) pbh
  in
  scanforswapbuyoffers_r n (ltc_getbestblockhash ())
    
let findpfgalerttx txs1 txs2 =
  let i = ref (-1) in
  let rtxid = ref (0l,0l,0l,0l,0l,0l,0l,0l) in
  let txs = ref "" in
  let pfgswapid ri =
    let (_,_,_,_,_,_,_,x) = ri in
    Int32.logand x 0xffffl = 0x4150l
  in
  while not (pfgswapid !rtxid) do
    incr i;
    if !i >= 16777216 then raise Not_found; (** probably will never happen **)
    txs := txs1 ^ (le_num24 !i) ^ txs2;
    rtxid := Sha256.sha256dstr !txs
  done;
  (!i,!rtxid,!txs);;

let ltc_createalerttx_spec u k msg =
  let toburn_plus_fee = !Config.ltctxfee in
  let createalerttx txid vout spk amt redeemfn =
    let changeamt = Int64.sub amt toburn_plus_fee in
    let txs1b = Buffer.create 100 in
    let txs2b = Buffer.create 100 in
    let txs3b = Buffer.create 100 in
    Buffer.add_string txs1b "\001"; (*** assume one input ***)
    let txidrh = hashval_rev (hexstring_hashval txid) in
    ignore (seo_hashval seosb txidrh (txs1b,None));
    List.iter (fun z -> Buffer.add_char txs1b (Char.chr z)) (blnum32 (Int32.of_int vout));
    let txs1 = Buffer.contents txs1b in
    redeemfn txs1b;
    if changeamt >= ltcdust then (** only create change if it is not dust **)
      Buffer.add_string txs2b "\255\255\255\255\002"
    else
      Buffer.add_string txs2b "\255\255\255\255\001";
    List.iter (fun z -> Buffer.add_char txs2b (Char.chr z)) (blnum64 0L);
    let datalen = 4 + String.length msg in
    if datalen > 252 then raise (Failure "too much data to burn");
    if datalen < 76 then
      begin
	Buffer.add_char txs2b (Char.chr (datalen+2));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr datalen); (*** PUSH datalen ***)
      end
    else if datalen > 65535 then
      raise (Failure "too much data to burn")
    else if datalen > 255 then
      begin
	Buffer.add_char txs2b (Char.chr (datalen+3));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr 77); (*** PUSH datalen ***)
	Buffer.add_char txs2b (Char.chr (datalen mod 256));
	Buffer.add_char txs2b (Char.chr (datalen / 256));
      end
    else 
      begin
	Buffer.add_char txs2b (Char.chr (datalen+3));
	Buffer.add_char txs2b (Char.chr 0x6a); (*** OP_RETURN ***)
	Buffer.add_char txs2b (Char.chr 76); (*** PUSH datalen ***)
	Buffer.add_char txs2b (Char.chr datalen);
      end;
    Buffer.add_char txs2b k;
    for i = 0 to (String.length msg) - 1 do
      Buffer.add_char txs2b msg.[i]
    done;
    if changeamt >= ltcdust then
      begin
        List.iter (fun z -> Buffer.add_char txs3b (Char.chr z)) (blnum64 changeamt);
        let spks = hexstring_string spk in
        Buffer.add_char txs3b (Char.chr (String.length spks));
        Buffer.add_string txs3b spks;
      end;
    Buffer.add_string txs3b "\000\000\000\000"; (*** locktime ***)
    let txs2 = Buffer.contents txs2b in
    let txs3 = Buffer.contents txs3b in
    let (i,rtxid,txs) = findpfgalerttx ("\002\000\000\000" ^ (Buffer.contents txs1b) ^ txs2) txs3 in
    let txsb = Buffer.create 100 in
    Buffer.add_string txsb "\002\000\000\000";
    Buffer.add_string txsb txs1;
    Buffer.add_string txsb "\000";
    Buffer.add_string txsb txs2;
    Buffer.add_string txsb (le_num24 i);
    Buffer.add_string txsb txs3;
    let s = Buffer.contents txsb in
    s
  in
  match u with
  | LtcP2shSegwit(txid,vout,_,rs,spk,amt) ->
     let rs2 = hexstring_string rs in
     let rsl = String.length rs2 in
     if rsl < 1 || rsl > 75 then raise Not_found;
     createalerttx
       txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b (Char.chr (1 + rsl));
	 Buffer.add_char txs1b (Char.chr rsl);
	 Buffer.add_string txs1b rs2)
  | LtcBech32(txid,vout,ltcaddr,spk,amt) ->
     createalerttx
       txid vout spk amt
       (fun txs1b ->
	 Buffer.add_char txs1b '\000')

let rec broadcast_alert_via_ltc k msg =
  let utxol = ltc_listunspent () in
  let toburn_plus_fee = !Config.ltctxfee in
  try
    (Utils.log_string (Printf.sprintf "Searching for an unspent litecoin tx with at least %Ld litoshis.\n" toburn_plus_fee));
    let u = (*** only consider single spends ***)
      List.find
	(fun u ->
	  match u with
	  | LtcP2shSegwit(txid,vout,_,_,_,amt) -> amt >= toburn_plus_fee
	  | LtcBech32(txid,vout,_,_,amt) -> amt >= toburn_plus_fee)
	utxol
    in
    let s = string_hexstring (ltc_createalerttx_spec u k msg) in
    let s = ltc_signrawtransaction s in
    ltc_sendrawtransaction s
  with Not_found -> raise InsufficientLtcFunds

let ltc_process_alert_tx_real h init =
  let l =
    if !Config.ltcoffline then
      begin
	Printf.printf "call getrawtransaction %s in ltc\n>> " h; flush stdout;
	read_line()
      end
    else
      let call = "{\"jsonrpc\": \"1.0\", \"id\":\"grtx\", \"method\": \"getrawtransaction\", \"params\": [\"" ^ h ^ "\",1] }" in
      begin
        try
          if !Config.ltcrpcavoidcurl then
            begin
              let (s,sin,sout) = ltcrpc_connect () in
              Printf.fprintf sout "Content-Length: %d\n\n" (String.length call);
              Printf.fprintf sout "%s\n" call;
              flush sout;
              skip_to_blankline sin;
              let l = input_line sin in
              shutdown_close s;
              l
            end
          else
            raise Exit
        with Exit -> (* fall back on curl *)
          let userpass = !Config.ltcrpcuser ^ ":" ^ !Config.ltcrpcpass in
          let url = ltcrpc_url() in
          let fullcall = !Config.curl ^ " --user " ^ userpass ^ " --data-binary '" ^ call ^ "' -H 'content-type: text/plain;' " ^ url in
          let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
          let l = input_line inc in
          ignore (Unix.close_process_full (inc,outc,errc));
          l
      end
  in
  try
    begin
      match parse_jsonval l with
      | (JsonObj(al),_) ->
         begin
	   match List.assoc "result" al with
	   | JsonObj(bl) ->
	      begin
	        match List.assoc "vout" bl with
	        | JsonArr(JsonObj(vout1)::_) ->
		   begin
		     match List.assoc "scriptPubKey" vout1 with
		     | JsonObj(cl) ->
		        let hex = json_assoc_string "hex" cl in
		        if String.length hex >= 10 && hex.[0] = '6' && hex.[1] = 'a' then
			  begin
			    let hex =
			      if hex.[2] = '4' && hex.[3] = 'c' then (*** pushing up to 255 bytes ***)
			        String.sub hex 6 ((String.length hex) - 6)
			      else if hex.[2] = '4' && hex.[3] = 'd' then (*** pushing up to 64K bytes ***)
			        String.sub hex 8 ((String.length hex) - 8)
			      else
			        String.sub hex 4 ((String.length hex) - 4)
			    in
                            let datastr = hexstring_string hex in
			    let datastrl = String.length datastr in
                            if datastrl > 3 then
                              if datastr.[0] = 'A' then (** alert **)
                                let msg = String.sub datastr 1 (datastrl - 4) in
                                begin
                                  if not init then Utils.log_string (Printf.sprintf "\nALERT: %s\n" msg);
                                  if not !Config.daemon then
                                    (Printf.printf "\nALERT: %s\n" msg; flush stdout);
                                end
                              else if datastr.[0] = 'L' then (** listener node **)
                                begin
                                  let n = String.sub datastr 1 (datastrl - 4) in
                                  if not init then Utils.log_string (Printf.sprintf "\nALERT: Listener node: %s\n" n);
                                  record_peer n
                                end
                              else if datastr.[0] = 'B' then (** bootstrap url **)
                                begin
                                  let url = String.sub datastr 1 (datastrl - 4) in
                                  if not init then Utils.log_string (Printf.sprintf "\nALERT: Bootstrap url: %s\n" url);
                                  if not (Hashtbl.mem knownbootstrapurl url) then
                                    if Hashtbl.mem ignorebootstrapurl url then
                                      begin
                                        if not !Config.daemon then
                                          (Printf.printf "Ignoring bootstrap url %s due to warning.\n" url; flush stdout)
                                      end
                                    else
                                      begin
                                        Hashtbl.add knownbootstrapurl url ();
                                        bootstrapurls := url::!bootstrapurls;
                                        if not !Config.daemon then
                                          (Printf.printf "Found bootstrap url %s.\n" url; flush stdout)
                                      end
                                end
                              else if datastr.[0] = 'b' then (** warning away from bootstrap url **)
                                begin
                                  let url = String.sub datastr 1 (datastrl - 4) in
                                  if not init then Utils.log_string (Printf.sprintf "\nALERT: Warning away from bootstrap url: %s\n" url);
                                  Hashtbl.add ignorebootstrapurl url ();
                                  if not !Config.daemon then
                                    (Printf.printf "Warned away from bootstrap url %s.\n" url; flush stdout)
                                end
                          end
                     | _ -> ()
                   end
                | _ -> ()
              end
           | _ -> ()
         end
      | _ -> ()
    end
  with _ -> ()

let ltc_process_alert_tx h = ltc_process_alert_tx_real h false

let search_ltc_bootstrap_url () =
  let fn = Printf.sprintf "%s/ltcbootstrap" !Config.datadir in
  let lbh =
    if Sys.file_exists fn then
      begin
        try
          let f = open_in fn in
          let l = input_line f in
          l
        with End_of_file ->
          ltc_getbestblockhash()
      end
    else
      begin
        ltc_getbestblockhash()
      end
  in
  (*  let currtm = Unix.time () in *)
  let h = ref lbh in
  try
    while true do
      let f = open_out fn in
      Printf.fprintf f "%s\n" !h;
      close_out f;
      let (prev,tm,hght,_,_) = ltc_getblock !h in
      if hght <= 2153500L then raise Exit;
      List.iter
        (fun ltx -> ltc_process_alert_tx_real ltx true)
        !alertcandidatetxs;
      alertcandidatetxs := [];
      h := prev;
      match !bootstrapurls with
      | (url::_) -> Config.bootstrapurl := url; raise Exit
      | _ -> ()
    done
  with Exit -> ()
