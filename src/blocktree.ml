(* Copyright (c) 2022 The Proofgold Lite developers *)
(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint
open Utils
open Ser
open Hashaux
open Sha256
open Hash
open Htree
open Net
open Db
open Mathdata
open Assets
open Signat
open Tx
open Ctre
open Block
open Ltcrpc

type swapmatchoffertype =
  | SimpleSwapMatchOffer of hashval * hashval * md160 * hashval * int64 * int64 * md160 * md160 * md160 * int

let swapmatchoffers : (float ref * swapmatchoffertype) list ref = ref [];;

let unconfswapredemptions : (hashval * int64 * stx) list ref = ref [];;

let tmp_delta_roots : (hashval * hashval) list ref = ref [];;

let swapmatchoffer_ltccontracttx ltctxh (y4,y3,y2,y1,y0) litoshisout =
  let ltccontracttxb = Buffer.create 200 in
  Buffer.add_string ltccontracttxb "\002\000\000\000\001";
  let hr = hashval_rev ltctxh in
  ignore (seo_hashval seosb hr (ltccontracttxb,None));
  Buffer.add_string ltccontracttxb "\001\000\000\000\000\255\255\255\255";
  Buffer.add_string ltccontracttxb "\001"; (* one output *)
  List.iter (fun z -> Buffer.add_char ltccontracttxb (Char.chr z)) (blnum64 litoshisout);
  Buffer.add_string ltccontracttxb "\022\000\020";
  ignore (seo_md160 seosb (y4,y3,y2,y1,y0) (ltccontracttxb,None));
  Buffer.add_string ltccontracttxb "\000\000\000\000"; (* locktime *)
  Buffer.contents ltccontracttxb
  
(** analyze outputs of tauout to see if it's a swap match offer;
    if it is, extract info and save it **)
let analyze_swapmatchoffer_tx stxh txh tauout =
  match tauout with
  | [(caddr,(None,Currency(atms)));((yp,y4,y3,y2,y1,y0),(Some((xb,x4,x3,x2,x1,x0),fakeltcfee,rew),Currency(_)))] when p2shaddr_p caddr && yp = 0 && fakeltcfee <= 4000L && not rew && not xb ->
     if not (List.exists (fun (_,smo) -> match smo with SimpleSwapMatchOffer(stxh2,_,_,_,_,_,_,_,_,_) -> stxh2 = stxh) !swapmatchoffers) then (** already have **)
       begin
         let realltcfee = Int64.mul 100L fakeltcfee in
         List.iter
           (fun (h,pr,sbo) -> (* h is the ltc tx id *)
             match sbo with
             | SimpleSwapBuyOffer(lbeta,(zp,z4,z3,z2,z1,z0),atoms,litoshis) when zp = 0 ->
                if atms >= atoms then (** paying enough atoms for buy offer **)
                  begin
                    let litoshisout = Int64.sub litoshis realltcfee in
                    if litoshisout > 0L then (* create ltc tx to spend (h,vout=1) to bech32 address given by alphal1 without output being litoshiout *)
                      let ltccontracttx = swapmatchoffer_ltccontracttx h (y4,y3,y2,y1,y0) litoshisout in
                      let ltccontracttxid = hashval_rev (Sha256.sha256dstr ltccontracttx) in
                      let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid (z4,z3,z2,z1,z0) (x4,x3,x2,x1,x0) 48l in (** spendable by pbeta if ltc tx with id ltccontracttx has >= 3 confirmations; spendable by alphap if contract has >= 48 confirmations *)
                      if p2shaddr_addr caddr2 = caddr then (** found it **)
                        let ctm = ref (Unix.time()) in
                        log_string (Printf.sprintf "Simple Swap Match %f %s %s %s %Ld %Ld %f\n" !ctm (hashval_hexstring stxh) (hashval_hexstring txh) (hashval_hexstring h) atoms litoshis pr);
                        swapmatchoffers := (ctm,SimpleSwapMatchOffer(stxh,h,caddr2,hashpair txh (hashint32 0l),atms,litoshis,(y4,y3,y2,y1,y0),(x4,x3,x2,x1,x0),(z4,z3,z2,z1,z0),Int64.to_int fakeltcfee))::!swapmatchoffers
                  end
	     | _ -> ())
           !swapbuyoffers
       end
  | _ -> ();;

let localpreferred : (hashval,unit) Hashtbl.t = Hashtbl.create 10;;

let processing : int64 option ref = ref None;;

let stxpoolfee : (hashval,int64) Hashtbl.t = Hashtbl.create 1000;;
let stxpooltm : (hashval,int64) Hashtbl.t = Hashtbl.create 1000;;
let stxpool : (hashval,stx) Hashtbl.t = Hashtbl.create 1000;;
let published_stx : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let unconfirmed_spent_assets : (hashval,hashval) Hashtbl.t = Hashtbl.create 100;;

let artificialledgerroot = ref None;;
let artificialblockheight = ref (-1L);;
let artificialbestblock = ref None;;

let recentheaders : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;
let blockinvalidated : (hashval,unit) Hashtbl.t = Hashtbl.create 1000;;

let delayed_headers : (hashval * hashval,Z.t -> unit) Hashtbl.t = Hashtbl.create 100;;
let delayed_deltas : (hashval * hashval,hashval option -> hashval option -> Z.t -> unit) Hashtbl.t = Hashtbl.create 100;;

(** Lite client communication **)
type liteservmsg =
  | LSState of int64 * hashval * hashval * hashval * hashval * (int64 * int64 * (hashval * int32) * (hashval * hashval) option * hashval) * (Z.t * int64 * hashval * hashval option * hashval option)
  | LSCTree of ctree
  | LSTTree of ttree
  | LSSTree of stree
  | LSSuccess
  | LSFailed

type liteclientmsg =
  | LCStateRequest
  | LCCTreeRequest of hashval * addr
  | LCTTreeRequest of hashval
  | LCSTreeRequest of hashval
  | LCSendTx of stx

let seo_liteservmsg o lsm c =
  match lsm with
  | LSState(blkh,dbh,lbk,ltx,currledgerroot,(tm1,burned,lutxo,prev,stkmod),vhv) ->
     let c = o 2 0 c in
     seo_prod7 seo_int64 seo_hashval seo_hashval seo_hashval seo_hashval
       (seo_prod5 seo_int64 seo_int64 (seo_prod seo_hashval seo_int32) (seo_option (seo_prod seo_hashval seo_hashval)) seo_hashval)
       (seo_prod5 seo_big_int_256 seo_int64 seo_hashval (seo_option seo_hashval) (seo_option seo_hashval))
       o (blkh,dbh,lbk,ltx,currledgerroot,(tm1,burned,lutxo,prev,stkmod),vhv) c
  | LSCTree(tr) ->
     let c = o 2 1 c in
     seo_ctree o tr c
  | LSTTree(tr) ->
     let c = o 2 3 c in
     let c = o 1 1 c in
     let c = o 2 0 c in
     seo_htree seo_theory o tr c
  | LSSTree(tr) ->
     let c = o 2 3 c in
     let c = o 1 1 c in
     let c = o 2 1 c in
     seo_htree (seo_prod (seo_option seo_hashval) seo_signa) o tr c
  | LSSuccess ->
     let c = o 2 2 c in
     c
  | LSFailed ->
     let c = o 2 3 c in
     let c = o 1 0 c in
     c

let sei_liteservmsg i c =
  let (x,c) = i 2 c in
  if x = 0 then
    let ((blkh,dbh,lbk,ltx,currledgerroot,ov,vhv),c) =
      sei_prod7 sei_int64 sei_hashval sei_hashval sei_hashval sei_hashval
        (sei_prod5 sei_int64 sei_int64 (sei_prod sei_hashval sei_int32) (sei_option (sei_prod sei_hashval sei_hashval)) sei_hashval)
        (sei_prod5 sei_big_int_256 sei_int64 sei_hashval (sei_option sei_hashval) (sei_option sei_hashval))
        i c
    in
    (LSState(blkh,dbh,lbk,ltx,currledgerroot,ov,vhv),c)
  else if x = 1 then
    let (tr,c) = sei_ctree i c in
    (LSCTree(tr),c)
  else if x = 2 then
    (LSSuccess,c)
  else
    let (x,c) = i 1 c in
    if x = 0 then
      (LSFailed,c)
    else
      let (x,c) = i 2 c in
      if x = 0 then
        let (tr,c) = sei_htree sei_theory i c in
        (LSTTree(tr),c)
      else if x = 1 then
        let (tr,c) = sei_htree (sei_prod (sei_option sei_hashval) sei_signa) i c in
        (LSSTree(tr),c)
      else
        raise (Failure "not liteservmsg")

let seo_liteclientmsg o lcm c =
  match lcm with
  | LCStateRequest ->
     o 2 0 c
  | LCCTreeRequest(lr,alpha) ->
     let c = o 2 1 c in
     seo_prod seo_hashval seo_addr o (lr,alpha) c
  | LCSendTx(stau) ->
     let c = o 2 2 c in
     seo_stx o stau c
  | LCTTreeRequest(h) ->
     let c = o 2 3 c in
     let c = o 2 0 c in
     seo_hashval o h c
  | LCSTreeRequest(h) ->
     let c = o 2 3 c in
     let c = o 2 1 c in
     seo_hashval o h c

let sei_liteclientmsg i c =
  let (x,c) = i 2 c in
  if x = 0 then
    (LCStateRequest,c)
  else if x = 1 then
    let ((lr,alpha),c) = sei_prod sei_hashval sei_addr i c in
    (LCCTreeRequest(lr,alpha),c)
  else if x = 2 then
    let (stau,c) = sei_stx i c in
    (LCSendTx(stau),c)
  else
    let (x,c) = i 2 c in
    if x = 0 then
      let (h,c) = sei_hashval i c in
      (LCTTreeRequest(h),c)
    else if x = 1 then
      let (h,c) = sei_hashval i c in
      (LCSTreeRequest(h),c)
    else
      raise (Failure "not liteservmsg")

let lite_req_ctree ledgerroot alpha =
  let reqctree (s,sin,sout) =
    seocf (seo_liteclientmsg seoc (LCCTreeRequest(ledgerroot,alpha)) (sout,None));
    flush sout;
    let (lsm,_) = sei_liteservmsg seic (sin,None) in
    shutdown_close s;
    match lsm with
    | LSCTree(tr) -> Some(tr)
    | _ -> None
  in
  match !Config.liteserveronion with
  | Some(onion) ->
     begin
       let (s,sin,sout) = connectonionpeer !Config.socksport onion !Config.liteserverport in
       reqctree (s,sin,sout)
     end
  | None ->
     match !Config.liteserverip with
     | Some(ip) ->
        begin
          let s = connectpeer ip !Config.liteserverport in
          let sin = Unix.in_channel_of_descr s in
          let sout = Unix.out_channel_of_descr s in
          set_binary_mode_in sin true;
          set_binary_mode_out sout true;
          reqctree (s,sin,sout)
        end
     | None -> raise (Failure "Either liteserveronion or liteserverip must be set.")

let lite_sendtx stau =
  let sendtx (s,sin,sout) =
    seocf (seo_liteclientmsg seoc (LCSendTx(stau)) (sout,None));
    flush sout;
    let (lsm,_) = sei_liteservmsg seic (sin,None) in
    shutdown_close s;
    match lsm with
    | LSSuccess -> ()
    | _ -> log_string (Printf.sprintf "lite server did not return success after sendtx")
  in
  match !Config.liteserveronion with
  | Some(onion) ->
     begin
       let (s,sin,sout) = connectonionpeer !Config.socksport onion !Config.liteserverport in
       sendtx (s,sin,sout)
     end
  | None ->
     match !Config.liteserverip with
     | Some(ip) ->
        begin
          let s = connectpeer ip !Config.liteserverport in
          let sin = Unix.in_channel_of_descr s in
          let sout = Unix.out_channel_of_descr s in
          set_binary_mode_in sin true;
          set_binary_mode_out sout true;
          sendtx (s,sin,sout)
        end
     | None -> raise (Failure "Either liteserveronion or liteserverip must be set.")

let thytree : (hashval,ttree) Hashtbl.t = Hashtbl.create 1000;;
let sigtree : (hashval,stree) Hashtbl.t = Hashtbl.create 1000;;

let add_thytree thyroot otht =
  match thyroot,otht with
  | Some(r),Some(tht) -> if not (Hashtbl.mem thytree r) then Hashtbl.add thytree r tht
  | _,_ -> ()

let add_sigtree sigroot osigt =
  match sigroot,osigt with
  | Some(r),Some(sigt) -> if not (Hashtbl.mem sigtree r) then Hashtbl.add sigtree r sigt
  | _,_ -> ()

let rec lookup_thytree thyroot =
  match thyroot with
  | None -> None
  | Some(r) ->
      try
	Some(Hashtbl.find thytree r)
      with Not_found ->
	try
	  let (prevroot,added) = DbTheoryTree.dbget r in
	  let oldthytree = lookup_thytree prevroot in
	  let newthytree = ref oldthytree in
	  List.iter
	    (fun h ->
	      try
		let th = DbTheory.dbget h in
		newthytree := Some(ottree_insert !newthytree (hashval_bitseq h) th)
	      with Not_found ->
		raise (Failure("fatal error trying to build theory tree; unknown theory " ^ (hashval_hexstring h))))
	    added;
	  let newroot = ottree_hashroot !newthytree in
	  if newroot = thyroot then
	    begin
	      add_thytree thyroot !newthytree;
	      !newthytree
	    end
	  else
	    raise (Failure("fatal error trying to build theory tree; theory tree root mismatch expected " ^ (hashval_hexstring r) ^ " but got " ^ (match newroot with None -> "None" | Some(h) -> hashval_hexstring h)))
	with
        | Not_found ->
           if not !Config.liteserver then
             begin
               let req_ttree (s,sin,sout) =
                 seocf (seo_liteclientmsg seoc (LCTTreeRequest(r)) (sout,None));
                 flush sout;
                 let (lsm,_) = sei_liteservmsg seic (sin,None) in
                 shutdown_close s;
                 match lsm with
                 | LSTTree(tr) ->
                    Hashtbl.add thytree r tr;
                    Some(tr)
                 | _ ->
                    raise (Failure (Printf.sprintf "Problem getting theory tree with root %s from the Proofgold Lite server." (hashval_hexstring r)))
               in
               match !Config.liteserveronion with
               | Some(onion) ->
                  begin
                    let (s,sin,sout) = connectonionpeer !Config.socksport onion !Config.liteserverport in
                    req_ttree (s,sin,sout)
                  end
               | None ->
                  match !Config.liteserverip with
                  | Some(ip) ->
                     begin
                       let s = connectpeer ip !Config.liteserverport in
                       let sin = Unix.in_channel_of_descr s in
                       let sout = Unix.out_channel_of_descr s in
                       set_binary_mode_in sin true;
                       set_binary_mode_out sout true;
                       req_ttree (s,sin,sout)
                     end
                  | None -> raise (Failure "Either liteserveronion or liteserverip must be set.")
             end
           else
	     raise (Failure("could not find theory tree with root " ^ (hashval_hexstring r) ^ " in the database"))

let rec lookup_sigtree sigroot =
  match sigroot with
  | None -> None
  | Some(r) ->
      try
	Some(Hashtbl.find sigtree r)
      with Not_found ->
	try
	  let (prevroot,added) = DbSignaTree.dbget r in
	  let oldsigtree = lookup_sigtree prevroot in
	  let newsigtree = ref oldsigtree in
	  List.iter
	    (fun h ->
	      try
		let th = DbSigna.dbget h in
		newsigtree := Some(ostree_insert !newsigtree (hashval_bitseq h) th)
	      with Not_found ->
		raise (Failure("fatal error trying to build signature tree; unknown signature " ^ (hashval_hexstring h))))
	    added;
	  let newroot = ostree_hashroot !newsigtree in
	  if newroot = sigroot then
	    begin
	      add_sigtree sigroot !newsigtree;
	      !newsigtree
	    end
	  else
	    raise (Failure("fatal error trying to build signature tree; signature tree root mismatch expected " ^ (hashval_hexstring r) ^ " but got " ^ (match newroot with None -> "None" | Some(h) -> hashval_hexstring h)))
	with
        | Not_found ->
           if not !Config.liteserver then
             begin
               let req_stree (s,sin,sout) =
                 seocf (seo_liteclientmsg seoc (LCSTreeRequest(r)) (sout,None));
                 flush sout;
                 let (lsm,_) = sei_liteservmsg seic (sin,None) in
                 shutdown_close s;
                 match lsm with
                 | LSSTree(tr) ->
                    Hashtbl.add sigtree r tr;
                    Some(tr)
                 | _ ->
                    raise (Failure (Printf.sprintf "Problem getting signature tree with root %s from the Proofgold Lite server." (hashval_hexstring r)))
               in
               match !Config.liteserveronion with
               | Some(onion) ->
                  begin
                    let (s,sin,sout) = connectonionpeer !Config.socksport onion !Config.liteserverport in
                    req_stree (s,sin,sout)
                  end
               | None ->
                  match !Config.liteserverip with
                  | Some(ip) ->
                     begin
                       let s = connectpeer ip !Config.liteserverport in
                       let sin = Unix.in_channel_of_descr s in
                       let sout = Unix.out_channel_of_descr s in
                       set_binary_mode_in sin true;
                       set_binary_mode_out sout true;
                       req_stree (s,sin,sout)
                     end
                  | None -> raise (Failure "Either liteserveronion or liteserverip must be set.")
             end
           else           
	     raise (Failure("could not find signature tree with root " ^ (hashval_hexstring r) ^ " in the database"))

let rec get_all_theories t =
  match t with
  | None -> []
  | Some(HBin(tl,tr)) -> get_all_theories tl @ get_all_theories tr
  | Some(HLeaf(x)) ->
      match hashtheory x with
      | Some(h) -> [(h,x)]
      | None -> raise (Failure "empty theory ended up in the theory tree somehow")

let rec get_all_signas t loc =
  match t with
  | None -> []
  | Some(HLeaf(th,x)) -> [(bitseq_hashval (List.rev loc),hashopair2 th (hashsigna x),(th,x))]
  | Some(HBin(tl,tr)) -> get_all_signas tl (false::loc) @ get_all_signas tr (true::loc)

let rec get_added_theories t1 t2 =
  match (t1,t2) with
  | (None,t2) -> get_all_theories t2
  | (Some(HLeaf(_)),Some(HLeaf(_))) -> [] (*** assume equal, which should be an invariant ***)
  | (Some(HBin(t1l,t1r)),Some(HBin(t2l,t2r))) -> get_added_theories t1l t2l @ get_added_theories t1r t2r (*** inefficient, but new theories should be rare ***)
  | (_,_) -> raise (Failure("Impossible pair of old and new theory trees"))

let rec get_added_signas t1 t2 loc =
  match (t1,t2) with
  | (None,t2) -> get_all_signas t2 loc
  | (Some(HLeaf(_)),Some(HLeaf(_))) -> [] (*** assume equal, which should be an invariant ***)
  | (Some(HBin(t1l,t1r)),Some(HBin(t2l,t2r))) -> get_added_signas t1l t2l (false::loc) @ get_added_signas t1r t2r (true::loc) (*** inefficient, but new signatures should be rare ***)
  | (_,_) -> raise (Failure("Impossible pair of old and new signature trees"))

(*** save information indicating how to rebuild the theory and signature trees upon initialization ***)
let update_theories oldthyroot oldthytree newthytree =
  let newthyroot = ottree_hashroot newthytree in
  if not (oldthyroot = newthyroot) then
    begin
      match newthyroot with
      | None -> raise (Failure "cannot go from nonempty thy tree to empty thy tree")
      | Some(newthyrootreal) ->
	  let addedtheories = get_added_theories oldthytree newthytree in
	  List.iter
	    (fun (h,thy) -> DbTheory.dbput h thy)
	    addedtheories;
	  DbTheoryTree.dbput newthyrootreal (oldthyroot,List.map (fun (h,_) -> h) addedtheories);
	  add_thytree newthyroot newthytree
    end

let update_signatures oldsigroot oldsigtree newsigtree =
  let newsigroot = ostree_hashroot newsigtree in
  if not (oldsigroot = newsigroot) then
    begin
      match newsigroot with
      | None -> raise (Failure "cannot go from nonempty sig tree to empty sig tree")
      | Some(newsigrootreal) ->
	  let addedsignas = get_added_signas oldsigtree newsigtree [] in
	  List.iter
	    (fun (loc,k,(th,signa)) ->
	      DbSigna.dbput k (th,signa))
	    addedsignas;
	  DbSignaTree.dbput newsigrootreal (oldsigroot,List.map (fun (_,k,_) -> k) addedsignas);
	  add_sigtree newsigroot newsigtree
    end

let invalid_or_blacklisted_p h =
  if Hashtbl.mem blockinvalidated h then
    true
  else
    begin
      try
	if DbInvalidatedBlocks.dbget h then
	  true
	else
	  raise Not_found
      with Not_found ->
	try
	  DbBlacklist.dbget h
	with Not_found ->
	  false
    end

let rec recursively_invalidate_blocks_2 lbk ltx =
  try
    begin
      let (h,_,_,_,_,_,_) = Db_outlinevals.dbget (hashpair lbk ltx) in
      if not (Hashtbl.mem blockinvalidated h) then
	begin
	  Hashtbl.add blockinvalidated h ();
	  DbInvalidatedBlocks.dbput h true;
	end;
      List.iter
	(fun (nlbk,nltx) -> recursively_invalidate_blocks_2 nlbk nltx)
        (get_outlinesucc (lbk,ltx))
    end
  with Not_found -> ()

let recursively_invalidate_blocks h =
  Hashtbl.add blockinvalidated h ();
  DbInvalidatedBlocks.dbput h true;
  let bbl = get_blockburns h in
  List.iter
    (fun (lbk,ltx) -> recursively_invalidate_blocks_2 lbk ltx)
    bbl

let rec recursively_revalidate_blocks_2 lbk ltx =
  try
    begin
      let (h,_,_,_,p,_,_) = Db_outlinevals.dbget (hashpair lbk ltx) in
      Hashtbl.remove blockinvalidated h;
      if DbInvalidatedBlocks.dbexists h then DbInvalidatedBlocks.dbdelete h;
      if DbBlacklist.dbexists h then DbBlacklist.dbdelete h;
      match p with
      | Some(plbk,pltx) -> recursively_revalidate_blocks_2 plbk pltx
      | None -> ()
    end
  with Not_found -> ()

let recursively_revalidate_blocks h =
  Hashtbl.remove blockinvalidated h;
  if DbInvalidatedBlocks.dbexists h then DbInvalidatedBlocks.dbdelete h;
  if DbBlacklist.dbexists h then DbBlacklist.dbdelete h;
  let bbl = get_blockburns h in
  List.iter
    (fun (lbk,ltx) -> recursively_revalidate_blocks_2 lbk ltx)
    bbl

let ensure_prev_header_valid_p lh =
  try
    let (dbh,_,_,_,par,_,_) = Db_outlinevals.dbget lh in
    if invalid_or_blacklisted_p dbh then
      raise Not_found
    else
      match par with
      | None -> true
      | Some(plbk,pltx) ->
         let plh = hashpair plbk pltx in
         Db_validheadervals.dbexists plh
  with
  | Not_found ->
     if Db_validheadervals.dbexists lh then Db_validheadervals.dbdelete lh;
     if Db_validblockvals.dbexists lh then Db_validblockvals.dbdelete lh;
     false

let ensure_prev_block_valid_p lh dbh (bhd,bhs) =
  try
    if Db_validheadervals.dbexists lh then
      begin
        match bhd.prevblockhash with
        | None -> true
        | Some(pdbh,Poburn(plbk,pltx,_,_,_,_)) ->
           let plh = hashpair plbk pltx in
           if Db_validblockvals.dbexists plh then
             begin
               try
                 let pbh = DbBlockHeader.dbget pdbh in
                 if blockheader_succ pbh (bhd,bhs) then
                   true
                 else
                   begin
                     recursively_invalidate_blocks dbh;
                     raise Exit
                   end
               with
               | Exit -> raise Not_found
               | Not_found -> (* if we don't have the header we can't know it or the block is really valid so something went wrong *)
                 Db_validheadervals.dbdelete plh;
                 Db_validblockvals.dbdelete plh;
                 raise Not_found
             end
           else
             raise Not_found
      end
    else
      raise Not_found
  with
  | Not_found ->
     if Db_validblockvals.dbexists lh then Db_validblockvals.dbdelete lh;
     false

(** try to avoid processing more than one header/delta/block at once in different threads; it should still work if we do, but it's likely to be doing the same work multiple times **)
let processing_wrapper f =
  try
    while true do
      match !processing with
      | Some(tm) ->
         if Int64.add tm 1800L < Int64.of_float (Unix.time()) then
           (processing := None; raise Exit)
         else
           Thread.delay 60.0
      | None -> raise Exit
    done
  with
  | Exit ->
     let tm = Int64.of_float (Unix.time()) in
     processing := Some(tm);
     try
       f();
       processing := None
     with
     | e ->
        processing := None;
        raise e

(*** assumes ancestors have been validated and info for parent is on validheadervals;
 but also does some extra checking in ensure_prev_header_valid_p
 ***)
let process_header_real sout validate forw dbp (lbh,ltxh) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1 =
  if validate then
    begin
      let bh = blockheader_id (bhd,bhs) in
      if invalid_or_blacklisted_p bh then
        begin
          log_string (Printf.sprintf "Refusing to process header (%Ld) %s since marked invalid.\n" currhght (hashval_hexstring bh))
        end
      else
        let lh = hashpair lbh ltxh in
        if ensure_prev_header_valid_p lh then
          if valid_blockheader currhght csm tar (bhd,bhs) lmedtm burned txid1 vout1 then
	    begin
	      Db_validheadervals.dbput (hashpair lbh ltxh) (bhd.tinfo,bhd.timestamp,bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot);
              broadcast_inv [(int_of_msgtype Headers,h)];
	      if not (DbBlockDelta.dbexists h) then (if not (List.exists (fun (_,k) -> k = h) !missingdeltas) then missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,h)] !missingdeltas);
	      if dbp then
	        begin
	          DbBlockHeader.dbput h (bhd,bhs);
                  let bh2 = DbBlockHeader.dbget h in (* double check *)
                  if not (h = blockheader_id bh2) then
                    begin
                      log_string (Printf.sprintf "Header %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring h));
                      DbBlockHeader.dbdelete h;
                      DbBlockHeader.dbpurge ();
                    end
                  else
	            missingheaders := List.filter (fun (_,k) -> not (h = k)) !missingheaders;
	        end;
	      if forw then
	        begin
	          List.iter
		    (fun (lbh,ltxh) ->
		      try
		        let f = Hashtbl.find delayed_headers (lbh,ltxh) in
		        Hashtbl.remove delayed_headers (lbh,ltxh);
		        f bhd.tinfo
		      with Not_found -> ())
                    (get_outlinesucc (lbh,ltxh))
	        end
	    end
          else
	    begin
	      Printf.fprintf sout "Alleged block %s had an invalid header.\n" (hashval_hexstring h);
	      verbose_blockcheck := Some(!Utils.log);
	      ignore (valid_blockheader currhght csm tar (bhd,bhs) lmedtm burned txid1 vout1);
	      verbose_blockcheck := None;
	      DbInvalidatedBlocks.dbput h true
	    end
        else
          begin
            log_string (Printf.sprintf "Refusing to process header (%Ld) %s since we do not yet know previous header is valid.\n" currhght (hashval_hexstring bh));
          end
    end
  else
    begin
      Db_validheadervals.dbput (hashpair lbh ltxh) (bhd.tinfo,bhd.timestamp,bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot);
      if not (DbBlockDelta.dbexists h) then if not (List.exists (fun (_,k) -> k = h) !missingdeltas) then missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,h)] !missingdeltas;
    end

let process_header sout validate forw dbp (lbh,ltxh) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1 =
  processing_wrapper
    (fun () -> process_header_real sout validate forw dbp (lbh,ltxh) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1)
     
(*** this is for saving the new ctree elements in the database ***)
let process_delta_ctree_real h blkhght blk bhd blkdel =
  List.iter
    (fun stau ->
      let txid = hashstx stau in
      DbSTx.dbput txid stau;
      if !Config.swapping then
        begin
          unconfswapredemptions := List.filter (fun (txid2,_,_) -> not (txid = txid2)) !unconfswapredemptions;
          let (tau,_) = stau in
          let (_,tauout) = tau in
          analyze_swapmatchoffer_tx txid (hashtx tau) tauout
        end)
    blkdel.blockdelta_stxl;
  begin
    let prevc1 = ctree_of_block blk in
    let prevc2 = (* remove temporary staked asset in case of pure burn *)
      match bhd.pureburn with
      | None -> prevc1
      | Some(_,_) ->
         match tx_octree_trans false false 1L ([(p2pkhaddr_addr bhd.stakeaddr,bhd.stakeassetid)],[]) (Some(prevc1)) with
         | Some(prevledger2) -> prevledger2
         | None -> raise (Failure("removing the temporary staked asset in pure burn case somehow (impossibly) left ledger empty"))
    in
    let prevc3 = ctree_expand_leaves prevc2 in
    let prevc = (* and now put the asset back into the expanded ctree before transforming *)
      match bhd.pureburn with
      | None -> prevc3
      | Some(_,_) ->
         let aid = bhd.stakeassetid in
         let a = (aid,0L,None,Currency(0L)) in
         match tx_octree_trans_ false false 162 [] [(addr_bitseq (p2pkhaddr_addr bhd.stakeaddr),a)] (Some(prevc3)) with
         | Some(prevc) -> prevc
         | None -> raise (Failure("impossible"))
    in
    let (cstk,txl) = txl_of_block blk in (*** the coinstake tx is performed last, i.e., after the txs in the block. ***)
    try
      match tx_octree_trans false false blkhght cstk (txl_octree_trans false false blkhght txl (Some(prevc))) with (*** "false false" disallows database lookups and remote requests ***)
      | Some(newc) ->
         ignore (save_ctree_atoms newc)
      | None -> raise (Failure("transformed tree was empty, although block seemed to be valid"))
    with MaxAssetsAtAddress -> raise (Failure("transformed tree would hold too many assets at an address"))
  end

let rec process_delta_ctree_very_behind n h blkhght (blkh,blkd) =
  if n > 0 then
    begin
      let (bhd,_) = blkh in
      begin
        try
          let prevc1 = bhd.prevledger in
          let prevc2 = (* remove temporary staked asset in case of pure burn *)
            match bhd.pureburn with
            | None -> prevc1
            | Some(_,_) ->
               match tx_octree_trans false false 1L ([(p2pkhaddr_addr bhd.stakeaddr,bhd.stakeassetid)],[]) (Some(prevc1)) with
               | Some(prevledger2) -> prevledger2
               | None -> raise (Failure("removing the temporary staked asset in pure burn case somehow (impossibly) left ledger empty"))
          in
          let lr = ctree_hashroot prevc2 in
          verifyledger_h lr [];
          false (** not very behind **)
        with _ ->
              match bhd.prevblockhash with
              | None -> false
              | Some(ph,_) ->
                 let pblkhght = Int64.sub blkhght 1L in
                 let pblkh = DbBlockHeader.dbget ph in
                 let pblkd = DbBlockDelta.dbget ph in
                 process_delta_ctree_very_behind (n-1) ph pblkhght (pblkh,pblkd)
      end
    end
  else
    true (** very behind; take extreme measures **)

let rec process_delta_ctree_history_real h blkhght blk =
  let (blkh,blkdel) = blk in
  let (bhd,_) = blkh in
  try
    if !Config.fullnode then (** ensure we have the full ledger before processing the block **)
      begin
        try
          let prevc1 = bhd.prevledger in
          let prevc2 = (* remove temporary staked asset in case of pure burn *)
            match bhd.pureburn with
            | None -> prevc1
            | Some(_,_) ->
               match tx_octree_trans false false 1L ([(p2pkhaddr_addr bhd.stakeaddr,bhd.stakeassetid)],[]) (Some(prevc1)) with
               | Some(prevledger2) -> prevledger2
               | None -> raise (Failure("removing the temporary staked asset in pure burn case somehow (impossibly) left ledger empty"))
          in
          let lr = ctree_hashroot prevc2 in
          verifyledger_h lr [];
        with _ ->
              match bhd.prevblockhash with
              | None -> ()
              | Some(ph,_) ->
                 let pblkhght = Int64.sub blkhght 1L in
                 try
                   let pblkh = DbBlockHeader.dbget ph in
                   try
                     let pblkd = DbBlockDelta.dbget ph in
                     process_delta_ctree_history_real ph pblkhght (pblkh,pblkd)
                   with Not_found ->
                     if not (List.exists (fun (_,k) -> k = ph) !missingdeltas) then missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(pblkhght,ph)] !missingdeltas;
                 with Not_found ->
                   if not (List.exists (fun (_,k) -> k = ph) !missingheaders) then missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(pblkhght,ph)] !missingheaders;
      end;
    process_delta_ctree_real h blkhght blk bhd blkdel
  with _ -> ()

let process_delta_ctree_history h blkhght blk =
  let mc = !Config.maxconns in
  Config.maxconns := 0;
  log_string (Printf.sprintf "Stopping network while catching up.\n");
  disconnect_completely();
  process_delta_ctree_history_real h blkhght blk;
  log_string (Printf.sprintf "Restarting network.\n");
  initnetwork !Utils.log;
  Config.maxconns := mc;
  Thread.exit()

let rec process_delta_ctree h blkhght blk =
  let (blkh,blkdel) = blk in
  let (bhd,_) = blkh in
  try
    if !Config.fullnode then (** ensure we have the full ledger before processing the block **)
      begin
        try
          let prevc1 = bhd.prevledger in
          let prevc2 = (* remove temporary staked asset in case of pure burn *)
            match bhd.pureburn with
            | None -> prevc1
            | Some(_,_) ->
               match tx_octree_trans false false 1L ([(p2pkhaddr_addr bhd.stakeaddr,bhd.stakeassetid)],[]) (Some(prevc1)) with
               | Some(prevledger2) -> prevledger2
               | None -> raise (Failure("removing the temporary staked asset in pure burn case somehow (impossibly) left ledger empty"))
          in
          let lr = ctree_hashroot prevc2 in
          verifyledger_h lr [];
        with _ ->
              match bhd.prevblockhash with
              | None -> ()
              | Some(ph,_) ->
                 let pblkhght = Int64.sub blkhght 1L in
                 try
                   let pblkh = DbBlockHeader.dbget ph in
                   try
                     let pblkd = DbBlockDelta.dbget ph in
                     if process_delta_ctree_very_behind 100 ph pblkhght (pblkh,pblkd) then
                       begin
                         ignore (Thread.create (fun () -> process_delta_ctree_history ph pblkhght (pblkh,pblkd)) ())
                       end
                     else (** not too far behind, so reprocess the recent ones **)
                       process_delta_ctree ph pblkhght (pblkh,pblkd)
                   with Not_found ->
                     if not (List.exists (fun (_,k) -> k = ph) !missingdeltas) then missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(pblkhght,ph)] !missingdeltas;
                 with Not_found ->
                   if not (List.exists (fun (_,k) -> k = ph) !missingheaders) then missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(pblkhght,ph)] !missingheaders;
      end;
    process_delta_ctree_real h blkhght blk bhd blkdel
  with _ -> ()

(*** assumes ancestors have been validated and info for parent is on validheadervals and entry on validblockvals;
 also assumes header has been validated and info for it is on validheadervals;
 but also does some extra checking in ensure_prev_block_valid_p
 ***)
let rec process_delta_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1 =
  if validate then
    begin
      if invalid_or_blacklisted_p h then
        begin
          log_string (Printf.sprintf "Refusing to process delta (%Ld) %s since marked invalid.\n" currhght (hashval_hexstring h))
        end
      else
        let lh = hashpair lbh ltxh in
        if Db_validheadervals.dbexists lh then
          if ensure_prev_block_valid_p lh h (bhd,bhs) then
            begin
              match valid_block tht sgt currhght csm tar ((bhd,bhs),bd) lmedtm burned txid1 vout1 with
              | Some(newtht,newsigt) ->
	         Db_validblockvals.dbput (hashpair lbh ltxh) true;
	         sync_last_height := max !sync_last_height currhght;
	         update_theories thtr tht newtht;
	         update_signatures sgtr sgt newsigt;
	         process_delta_ctree h currhght ((bhd,bhs),bd);
                 broadcast_inv [(int_of_msgtype Blockdelta,h)];
	         if dbp then
	           begin
	             DbBlockDelta.dbput h bd;
	             missingdeltas := List.filter (fun (_,k) -> not (h = k)) !missingdeltas;
	           end;
	         if forw then
	           begin
	             List.iter
		       (fun (lbh,ltxh) ->
		         try
		           let f = Hashtbl.find delayed_deltas (lbh,ltxh) in
		           Hashtbl.remove delayed_deltas (lbh,ltxh);
		           f bhd.newtheoryroot bhd.newsignaroot bhd.tinfo
		         with Not_found -> ())
                       (get_outlinesucc (lbh,ltxh))
	           end
              | None -> (*** invalid block ***)
	         Printf.fprintf sout "Alleged block %s at height %Ld is invalid.\n" (hashval_hexstring h) currhght;
	         verbose_blockcheck := Some(!Utils.log);
	         ignore (valid_block tht sgt currhght csm tar ((bhd,bhs),bd) lmedtm burned txid1 vout1);
	         verbose_blockcheck := None;
	         DbInvalidatedBlocks.dbput h true
            end
          else
            begin
              log_string (Printf.sprintf "Refusing to process delta (%Ld) %s since do not know prev block valid.\n" currhght (hashval_hexstring h))
            end
        else
          begin
            log_string (Printf.sprintf "Processing header and then if successful delta (%Ld) %s since do not know header valid.\n" currhght (hashval_hexstring h));
            process_header_real sout validate forw dbp (lbh,ltxh) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1;
            if Db_validheadervals.dbexists lh then process_delta_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1
          end
    end
  else
    begin
      Db_validheadervals.dbput (hashpair lbh ltxh) (bhd.tinfo,bhd.timestamp,bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot);
      Db_validblockvals.dbput (hashpair lbh ltxh) true;
    end

let process_delta sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1 =
  processing_wrapper
    (fun () -> process_delta_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1)

(*** assumes ancestors have been validated and info for parent is on validheadervals and entry on validblockvals;
 but also does some extra checking in ensure_prev_block_valid_p
 ***)
let process_block_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1 =
  if validate then
    begin
      if invalid_or_blacklisted_p h then
        begin
          log_string (Printf.sprintf "Refusing to process block (%Ld) %s since marked invalid.\n" currhght (hashval_hexstring h))
        end
      else
        let lh = hashpair lbh ltxh in
        if Db_validheadervals.dbexists lh then
          if ensure_prev_block_valid_p lh h (bhd,bhs) then
            begin
              match valid_block tht sgt currhght csm tar ((bhd,bhs),bd) lmedtm burned txid1 vout1 with
              | Some(newtht,newsigt) ->
	         Db_validheadervals.dbput (hashpair lbh ltxh) (bhd.tinfo,bhd.timestamp,bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot);
	         Db_validblockvals.dbput (hashpair lbh ltxh) true;
                 broadcast_inv [(int_of_msgtype Headers,h);(int_of_msgtype Blockdelta,h)];
	         sync_last_height := max !sync_last_height currhght;
	         update_theories thtr tht newtht;
	         update_signatures sgtr sgt newsigt;
	         process_delta_ctree h currhght ((bhd,bhs),bd);
	         if dbp then
	           begin
	             DbBlockHeader.dbput h (bhd,bhs);
                     let bh2 = DbBlockHeader.dbget h in (* double check *)
                     if not (h = blockheader_id bh2) then
                       begin
                         log_string (Printf.sprintf "Header %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring h));
                         DbBlockHeader.dbdelete h;
                         DbBlockHeader.dbpurge ();
                       end
                     else
                       begin
	                 missingheaders := List.filter (fun (_,k) -> not (h = k)) !missingheaders;
	                 DbBlockDelta.dbput h bd;
                         let bd2 = DbBlockDelta.dbget h in (* double check *)
                         if not (bhd.blockdeltaroot = blockdelta_hashroot bd2) then
                           begin
                             log_string (Printf.sprintf "Delta %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring h));
                             DbBlockDelta.dbdelete h;
                             DbBlockDelta.dbpurge ();
                           end
                         else
	                   missingdeltas := List.filter (fun (_,k) -> not (h = k)) !missingdeltas;
                       end
	           end;
	         if forw then
	           begin
	             List.iter
		       (fun (lbh,ltxh) ->
		         begin
		           try
		             let f = Hashtbl.find delayed_headers (lbh,ltxh) in
		             Hashtbl.remove delayed_headers (lbh,ltxh);
		             f bhd.tinfo
		           with Not_found -> ()
		         end;
		         begin
		           try
		             let f = Hashtbl.find delayed_deltas (lbh,ltxh) in
		             Hashtbl.remove delayed_deltas (lbh,ltxh);
		             f bhd.newtheoryroot bhd.newsignaroot bhd.tinfo
		           with Not_found -> ()
		         end)
                       (get_outlinesucc (lbh,ltxh))
	           end
              | None -> (*** invalid block ***)
	         Printf.fprintf sout "Alleged block %s at height %Ld is invalid.\n" (hashval_hexstring h) currhght;
	         verbose_blockcheck := Some(!Utils.log);
	         ignore (valid_block tht sgt currhght csm tar ((bhd,bhs),bd) lmedtm burned txid1 vout1);
	         verbose_blockcheck := None;
	         Hashtbl.add blockinvalidated h ();
	         DbInvalidatedBlocks.dbput h true
            end
          else
            begin
              log_string (Printf.sprintf "Refusing to process block (%Ld) %s since do not know prev block valid.\n" currhght (hashval_hexstring h))
            end
        else
          begin
            process_header_real sout validate forw dbp (lbh,ltxh) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1;
            process_delta_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1;
          end
    end
  else
    begin
      Db_validheadervals.dbput (hashpair lbh ltxh) (bhd.tinfo,bhd.timestamp,bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot);
      Db_validblockvals.dbput (hashpair lbh ltxh) true;
    end

let process_block sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1 =
  processing_wrapper
    (fun () -> process_block_real sout validate forw dbp (lbh,ltxh) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1)

let reprocessblock oc h lbk ltx =
  let lh = hashpair lbk ltx in
  try
    let bh = DbBlockHeader.dbget h in
    if not (h = blockheader_id bh) then
      begin
        log_string (Printf.sprintf "Header %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring h));
        DbBlockHeader.dbdelete h;
        DbBlockHeader.dbpurge ();
        try
	  let (_,_,_,_,_,_,currhght) = Db_outlinevals.dbget lh in
          missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,h)] !missingheaders
        with Not_found -> ()
      end
    else
      let (bhd,bhs) = bh in
      try
        let bd = DbBlockDelta.dbget h in
        if not (bhd.blockdeltaroot = blockdelta_hashroot bd) then
          begin
            log_string (Printf.sprintf "Delta %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring h));
            DbBlockDelta.dbdelete h;
            DbBlockDelta.dbpurge ();
            try
	      let (_,_,_,_,_,_,currhght) = Db_outlinevals.dbget lh in
              missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,h)] !missingdeltas
            with Not_found -> ()
          end
        else
          try
	    let (_,lmedtm,burned,(txid1,vout1),par,_,currhght) = Db_outlinevals.dbget lh in
            let (csm,tar,thtr,sgtr) =
	      match par with
	      | None -> (*** genesis ***)
                 let thtr = Some(Checking.initthytreeroot) in
	         (!genesisstakemod,!genesistarget,thtr,None)
	      | Some(plbk,pltx) ->
                 let plh = hashpair plbk pltx in
	         let (_,_,_,_,_,csm,_) = Db_outlinevals.dbget plh in
	         let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget plh in
	         (csm,tar,thtr,sgtr)
	    in
	    let tht = lookup_thytree thtr in
	    let sgt = lookup_sigtree sgtr in
            process_block oc true false false (lbk,ltx) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1
          with Not_found ->
	    Printf.fprintf oc "Could not find information for parent block %s\n"
	      (match bhd.prevblockhash with Some(h,_) -> (hashval_hexstring h) | None -> "(genesis)");
	    flush oc
      with Not_found ->
        Printf.fprintf oc "Do not have delta for block %s\n" (hashval_hexstring h);
        flush oc
  with Not_found ->
    Printf.fprintf oc "Do not have header for block %s\n" (hashval_hexstring h);
    flush oc
      
let initialize_pfg_from_ltc sout lblkh =
  List.iter
    (fun h ->
      let h = hexstring_hashval h in
      Hashtbl.add blockinvalidated h ();
      DbInvalidatedBlocks.dbput h true)
    !Config.invalidatedblocks;
  List.iter
    (fun h ->
      let h = hexstring_hashval h in
      Hashtbl.add blockinvalidated h ();
      DbInvalidatedBlocks.dbdelete h;
      DbBlacklist.dbdelete h)
    !Config.validatedblocks;
  let missingh : (hashval,unit) Hashtbl.t = Hashtbl.create 1000 in
  let missingd : (hashval,unit) Hashtbl.t = Hashtbl.create 1000 in
  let liveblocks : (hashval,unit) Hashtbl.t = Hashtbl.create 1000 in
  let liveblocks2 : (hashval * hashval,unit) Hashtbl.t = Hashtbl.create 1000 in
  let ltx_lblk : (hashval,hashval) Hashtbl.t = Hashtbl.create 1000 in
  let rec marklivenodes lbh ltx =
    try
      let (dnxt,_,_,_,par,_,_) = Db_outlinevals.dbget (hashpair lbh ltx) in
      if not (Hashtbl.mem liveblocks2 (lbh,ltx)) then
	begin
	  Hashtbl.add liveblocks2 (lbh,ltx) ();
	  Hashtbl.add liveblocks dnxt ();
	  match par with
	  | None -> ()
	  | Some(lbh,ltx) -> marklivenodes lbh ltx
	end
    with Not_found -> ()
  in
  let get_ltx_lblk ltx =
    try
      Hashtbl.find ltx_lblk ltx
    with Not_found ->
          let (_,_,_,olbk,_,_,_) = ltc_getburntransactioninfo (hashval_hexstring ltx) in
          match olbk with
          | Some(lbk) -> hexstring_hashval lbk
          | None -> raise Not_found
  in
  let handleltcburntx lbh lmedtm ltx =
    if not (Db_outlinevals.dbexists (hashpair lbh ltx)) then
      begin
	Hashtbl.add ltx_lblk ltx lbh;
	try
	  let (burned,lprevtx,dnxt,txid1,vout1) = DbLtcBurnTx.dbget ltx in
          insert_blockburn dnxt (lbh,ltx);
	  if lprevtx = (0l,0l,0l,0l,0l,0l,0l,0l) then
	    begin
	      if lmedtm >= !Config.genesistimestamp && lmedtm <= Int64.add !Config.genesistimestamp 604800L then
		begin
		  Db_outlinevals.dbput (hashpair lbh ltx) (dnxt,lmedtm,burned,(txid1,vout1),None,hashpair lbh ltx,1L);
		  if invalid_or_blacklisted_p dnxt then
		    Hashtbl.add blockinvalidated dnxt ()
		  else (*** process header and delta if we have them ***)
		    begin
		      try
			let (bhd,bhs) = DbBlockHeader.dbget dnxt in
			if bhd.prevblockhash = None then
			  begin
			    try
			      let bd = DbBlockDelta.dbget dnxt in
	                      sync_last_height := max !sync_last_height 1L;
                              let thtr = Some(Checking.initthytreeroot) in
                              let tht = Some(Checking.initthytree) in
			      process_block sout (Hashtbl.mem recentheaders dnxt) false false (lbh,ltx) dnxt ((bhd,bhs),bd) thtr tht None None 1L !genesisstakemod !genesistarget lmedtm burned txid1 vout1;
			    with Not_found ->
			      process_header sout (Hashtbl.mem recentheaders dnxt) false false (lbh,ltx) dnxt (bhd,bhs) 1L !genesisstakemod !genesistarget lmedtm burned txid1 vout1;
			  end
			else
			  begin
			    Printf.fprintf sout "Alleged genesis block %s had an invalid header (claims point to a previous block).\n" (hashval_hexstring dnxt);
			    DbInvalidatedBlocks.dbput dnxt true
			  end
		      with Not_found ->
			missingheaders := (1L,dnxt)::!missingheaders
		    end
		end
	    end
	  else
	    begin
	      try
		begin
		  let lprevblkh = get_ltx_lblk lprevtx in
		  try
		    let (prevdbh,prevlmedtm,prevburned,(prevtxid1,prevvout1),_,csm,prevhght) = Db_outlinevals.dbget (hashpair lprevblkh lprevtx) in
		    if invalid_or_blacklisted_p prevdbh then
		      begin
			Hashtbl.add blockinvalidated dnxt ();
			DbInvalidatedBlocks.dbput dnxt true;
			Printf.fprintf sout "Block %s invalid since parent is invalid.\n" (hashval_hexstring dnxt);
		      end
		    else
		      let currhght = Int64.add 1L prevhght in
		      Db_outlinevals.dbput (hashpair lbh ltx) (dnxt,lmedtm,burned,(txid1,vout1),Some(lprevblkh,lprevtx),hashpair lbh ltx,currhght);
                      insert_outlinesucc (lprevblkh,lprevtx) (lbh,ltx);
		      if invalid_or_blacklisted_p dnxt then
			Hashtbl.add blockinvalidated dnxt ()
		      else (*** process header and delta if we have them ***)
			begin
			  try
			    let (bhd,bhs) = DbBlockHeader.dbget dnxt in
			    begin
			      match bhd.prevblockhash with
			      | None ->
				 Printf.fprintf sout "Alleged block %s at height %Ld had an invalid header, points to no previous block but should point to %s.\n" (hashval_hexstring dnxt) currhght (hashval_hexstring prevdbh);
				 DbInvalidatedBlocks.dbput dnxt true
			      | Some(prevdbh2,Poburn(lbh2,ltx2,lmedtm2,burned2,txid2,vout2)) ->
				 if prevdbh = prevdbh2 && lbh2 = lprevblkh && ltx2 = lprevtx && lmedtm2 = prevlmedtm && burned2 = prevburned && txid2 = prevtxid1 && vout2 = prevvout1 then
				   begin
				     try
				       let (tar,tmstmp,lr,thtr,sgtr) = Db_validheadervals.dbget (hashpair lprevblkh lprevtx) in
				       if not (blockheader_succ_b prevdbh lr tmstmp tar (bhd,bhs)) then
					 begin
					   Printf.fprintf sout "Block %s at height %Ld is not a valid successor for %s.\n" (hashval_hexstring dnxt) currhght (hashval_hexstring prevdbh);
					   DbInvalidatedBlocks.dbput dnxt true
					 end
				       else
					 begin
					   if Db_validblockvals.dbexists (hashpair lprevblkh lprevtx) then (*** full blocks up to here have been validated ***)
					     begin
	                                       sync_last_height := max !sync_last_height currhght;
					       try
						 let bd = DbBlockDelta.dbget dnxt in
						 let tht = lookup_thytree thtr in
						 let sgt = lookup_sigtree sgtr in
						 process_block sout (Hashtbl.mem recentheaders dnxt) false false (lbh,ltx) dnxt ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1;
					       with Not_found -> (*** check if header is valid, report delta as missing ***)
						 process_header sout (Hashtbl.mem recentheaders dnxt) false false (lbh,ltx) dnxt (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1
					     end
					   else (*** an ancestor delta was not validated/is missing ***)
					     process_header sout (Hashtbl.mem recentheaders dnxt) false false (lbh,ltx) dnxt (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1
					 end
				     with Not_found -> (*** an ancestor header was not validated/is missing ***)
					   if not (Hashtbl.mem missingh dnxt) && not (DbBlockHeader.dbexists dnxt) then
                                             begin
                                               Hashtbl.add missingh dnxt ();
                                               missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dnxt)] !missingheaders
                                             end
				   end
				 else
				   begin
				     Printf.fprintf sout "Alleged block %s at height %Ld had an invalid header, pointing to an incorrect previous block or proof of burn.\n" (hashval_hexstring dnxt) currhght;
				     DbInvalidatedBlocks.dbput dnxt true
				   end
			    end
			  with Not_found ->
			    missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dnxt)] !missingheaders
			end
		  with Not_found ->
		    Printf.fprintf sout "Missing outline info for %s:%s\n" (hashval_hexstring lprevblkh) (hashval_hexstring lprevtx)
		end
	      with Not_found ->
		Printf.fprintf sout "Could not determine ltc block in which %s was confirmed.\n" (hashval_hexstring lprevtx)
	    end
	with Not_found ->
	  Printf.fprintf sout "Missing ltc burntx %s\n" (hashval_hexstring ltx)
      end
  in
  let recent_reprocessed : (hashval,unit) Hashtbl.t = Hashtbl.create 100 in
  let rec recent_recursive_validblockvals lh =
    try
      let (prevdbh,prevlmedtm,prevburned,(prevtxid1,prevvout1),par,csm,prevhght) = Db_outlinevals.dbget lh in
      if Hashtbl.mem recentheaders prevdbh then
        begin
          match par with
          | None -> true
          | Some(plbh,pltx) ->
             let plh = hashpair plbh pltx in
             if Db_validblockvals.dbexists plh then
               if Db_validheadervals.dbexists plh then
                 if recent_recursive_validblockvals plh then
                   true
                 else
                   begin
                     Db_validheadervals.dbdelete plh;
                     Db_validblockvals.dbdelete plh;
                     false
                   end
               else
                 begin
                   Db_validblockvals.dbdelete plh;
                   false
                 end
             else
               false
        end
      else
        true (** if not recent, assume valid **)
    with Not_found ->
      false
  in
  let rec handleltcblock lbh recent =
    try
      let lds = DbLtcPfgStatus.dbget lbh in
      begin
	match lds with
	| LtcPfgStatusPrev(lbh2) -> handleltcblock lbh2 recent
	| LtcPfgStatusNew(bds) -> (*** not all of these will contain burntxs, but these are the only ltc blocks that might contain burntxs ***)
	   begin
             let lpbh = ref None in
             let callwithprev = ref false in
             if recent then
               begin
                 List.iter
                   (fun (_,bdl) ->
                     List.iter
                       (fun (dbh,lbh,ltxh,_,_) ->
                         Hashtbl.replace recentheaders dbh ())
                       bdl)
                   (List.rev bds);
                 List.iter
                   (fun (blkhght,bdl) ->
                     List.iter
                       (fun (dbh,lbh,ltxh,_,_) ->
                         let lh = hashpair lbh ltxh in
                         if recent_recursive_validblockvals lh then (** check that recent ones have really been recursively verified **)
                           if not (Db_validblockvals.dbexists lh) then
                             begin
                               if not (Hashtbl.mem recent_reprocessed lh) then
                                 begin
                                   Hashtbl.add recent_reprocessed lh ();
                                   reprocessblock !Utils.log dbh lbh ltxh
                                 end
                             end
                           else
                             begin
	                       sync_last_height := max !sync_last_height blkhght;
                             end
                         else
                           begin
                             Db_validheadervals.dbdelete lh;
                             Db_validblockvals.dbdelete lh
                           end)
                       bdl)
                   (List.rev bds)
               end;
	     List.iter
	       (fun (_,bdl) ->
		 List.iter
		   (fun (dbh,lbh,ltx,_,lhght) ->
                     let lh = hashpair lbh ltx in
                     begin
                       match !lpbh with
                       | None -> lpbh := Some(lbh,lhght)
                       | Some(lbh2,lhght2) ->
                          if lhght < lhght2 then lpbh := Some(lbh,lhght)
                     end;
                     try
                       let (_,_,_,(_,_),_,_,hght) = Db_outlinevals.dbget lh in
                       if not (Hashtbl.mem missingh dbh) && not (DbBlockHeader.dbexists dbh) then
                         begin
                           Hashtbl.add missingh dbh ();
                           callwithprev := true;
                           missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(hght,dbh)] !missingheaders
                         end;
                       if not (Hashtbl.mem missingd dbh) && not (DbBlockDelta.dbexists dbh) then
                         begin
                           Hashtbl.add missingd dbh ();
                           callwithprev := true;
                           missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(hght,dbh)] !missingdeltas
                         end;
                     with
                     | Not_found ->
                        if not (Db_validheadervals.dbexists lh && Db_validblockvals.dbexists lh) then callwithprev := true)
		   bdl)
	       bds;
	     try
	       if !callwithprev then
                 begin
                   match !lpbh with
                   | Some(lbh2,_) -> handleltcblock lbh2 false
                   | None -> ()
                 end;
	       let (lprevbh,lmedtm,_,ltxl) = DbLtcBlock.dbget lbh in (*** if lbh is before ltc_oldest_to_consider, then there will be no entry in the database and this will raise Not_found ***)
	       List.iter (handleltcburntx lbh lmedtm) ltxl;
	       if recent then
		 begin
		   List.iter
		     (fun (_,bdl) ->
		       List.iter
			 (fun (_,lbh,ltx,_,_) -> marklivenodes lbh ltx)
			 bdl)
		     bds
		 end;
	     with Not_found -> ()
	   end
      end
    with Not_found -> ()
  in
  handleltcblock lblkh true;
  (*** remove dead blocks (no recent descendant/permanent orphans) ***)
  missingheaders := List.filter (fun (_,h) -> Hashtbl.mem liveblocks h) !missingheaders;
  missingdeltas := List.filter (fun (_,h) -> Hashtbl.mem liveblocks h) !missingdeltas
                               
let collect_inv m cnt tosend txinv =
  if (DbCTreeElt.dbexists !genesisledgerroot) || (DbCTreeAtm.dbexists !genesisledgerroot) then (tosend := (int_of_msgtype CTreeElement,!genesisledgerroot)::!tosend; incr cnt);
  let (lastchangekey,ctips0l) = ltcpfgstatus_dbget !ltc_bestblock in
  let inclh : (hashval,unit) Hashtbl.t = Hashtbl.create 5000 in
  let collect_inv_rec_blocks tosend =
    let (lastchangekey,ctips0l) = ltcpfgstatus_dbget !ltc_bestblock in
    List.iter
      (fun (_,ctips) ->
	List.iter
	  (fun (bh,_,_,_,_) ->
	    if not (Hashtbl.mem inclh bh) then
	      begin
		try
		  let (bhd,_) = DbBlockHeader.dbget bh in
		  Hashtbl.add inclh bh ();
		  tosend := (int_of_msgtype Headers,bh)::!tosend;
		  incr cnt;
		  if (DbCTreeElt.dbexists bhd.newledgerroot) || (DbCTreeAtm.dbexists bhd.newledgerroot) then (tosend := (int_of_msgtype CTreeElement,bhd.newledgerroot)::!tosend; incr cnt);
		  if DbBlockDelta.dbexists bh then (tosend := (int_of_msgtype Blockdelta,bh)::!tosend; incr cnt);
		with Not_found -> ()
	      end)
	  ctips)
      ctips0l
  in
  let rec collect_inv_stxs m cnt tosend ctipsl txinv =
    if !cnt < m then
      begin
	match txinv with
	| (txid::txinvr) ->
	   tosend := (int_of_msgtype STx,txid)::!tosend; incr cnt;
	   collect_inv_stxs m cnt tosend ctipsl txinvr
	| []  -> ()
      end
  in
  collect_inv_rec_blocks tosend;
  collect_inv_stxs m cnt tosend ctips0l txinv
                   
let send_inv m sout cs =
  let cnt = ref 0 in
  let tosend = ref [] in
  let txinv = ref [] in
  Hashtbl.iter (fun k _ -> txinv := k::!txinv) stxpool;
  collect_inv m cnt tosend !txinv;
  send_inv_to_one !tosend cs;;

send_inv_fn := send_inv;;

let rec insertnewdelayed (tm,n) btnl =
  match btnl with
  | [] -> [(tm,n)]
  | (tm2,n2)::btnr when tm < tm2 -> (tm,n)::btnl
  | (tm2,n2)::btnr -> (tm2,n2)::insertnewdelayed (tm,n) btnr
                                                 
let equ_tinfo (x,(y3,y2,y1,y0),z) (u,(v3,v2,v1,v0),w) =
  x = u && y3 = v3 && y2 = v2 && y1 = v1 && Int64.logand y0 (Int64.lognot 1L) = Int64.logand v0 (Int64.lognot 1L) && eq_big_int z w
                                                                                                                                
type consensuswarning =
  | ConsensusWarningMissing of hashval * hashval * hashval
  | ConsensusWarningBlacklist of hashval
  | ConsensusWarningInvalid of hashval
  | ConsensusWarningNoBurn of hashval
  | ConsensusWarningTerminal

let get_burn dbh =
  let bbl = get_blockburns dbh in
  List.find
    (fun (lbk,ltx) ->
      if !Config.ltcoffline then (** this may cause a problem if there are ltc orphans **)
	true
      else
	begin
	  try
	    let (_,_,_,lbk2,_,_,_) = ltc_getburntransactioninfo (hashval_hexstring ltx) in
	    lbk2 = Some(hashval_hexstring lbk)
	  with Not_found -> false
	end)
    bbl
    
let rec get_bestblock () =
  match !artificialbestblock with
  | Some(h,lbk,ltx) -> (Some(h,lbk,ltx),[])
  | None ->
     let (lastchangekey,ctips0l) = ltcpfgstatus_dbget !ltc_bestblock in
     let tm = ltc_medtime() in
     if ctips0l = [] && tm > Int64.add !Config.genesistimestamp 604800L then
       begin
	 Printf.printf "No blocks were created in the past week. Proofgold has reached terminal status.\nSometimes this message means the node is out of sync with ltc.\n"
       end;
     let rec get_bestblock_r2 p ctipsorig ctips ctipsr cwl =
       match ctips with
       | [] ->
          if p = 1 then
            get_bestblock_r2 2 ctipsorig ctipsorig ctipsr cwl
          else
            get_bestblock_r ctipsr cwl
       | (dbh,lbh,ltxh,ltm,lhght)::ctipr ->
	  begin
	    if DbInvalidatedBlocks.dbexists dbh then
	      get_bestblock_r2 p ctipsorig ctipr ctipsr (ConsensusWarningInvalid(dbh)::cwl)
	    else if DbBlacklist.dbexists dbh then
	      get_bestblock_r2 p ctipsorig ctipr ctipsr (ConsensusWarningBlacklist(dbh)::cwl)
	    else
	      begin
		try
		  let (lbk,ltx) = get_burn dbh in
                  if p = 1 then
                    if Hashtbl.mem localpreferred dbh then
		      (Some(dbh,lbk,ltx),cwl)
                    else
		      get_bestblock_r2 p ctipsorig ctipr ctipsr cwl
                  else
		    if Db_validblockvals.dbexists (hashpair lbk ltx) then
		      (Some(dbh,lbk,ltx),cwl)
		    else
		      get_bestblock_r2 p ctipsorig ctipr ctipsr (ConsensusWarningMissing(dbh,lbk,ltx)::cwl)
		with Not_found ->
		  get_bestblock_r2 p ctipsorig ctipr ctipsr (ConsensusWarningNoBurn(dbh)::cwl)
	      end
	  end
     and get_bestblock_r ctipsl cwl =
       match ctipsl with
       | [] ->
	  let tm = ltc_medtime() in
	  if tm > Int64.add !Config.genesistimestamp 604800L then
	    begin
	      raise (Failure "cannot find best validated header; probably out of sync")
	    end
	  else
	    (None,cwl)
       | (_,ctips)::ctipsr ->
	  get_bestblock_r2 1 ctips ctips ctipsr cwl
     in
     let cwl =
       let tm = ltc_medtime() in
       if ctips0l = [] && tm > Int64.add !Config.genesistimestamp 604800L then
	 [ConsensusWarningTerminal]
       else
	 []
     in
     get_bestblock_r ctips0l cwl
                     
let ensure_sync () =
  let (_,ctips0l) = ltcpfgstatus_dbget !ltc_bestblock in
  List.iter
    (fun (_,ctips) ->
      List.iter
        (fun (dbh,lbh,ltxh,_,_) ->
          if not (DbInvalidatedBlocks.dbexists dbh) && not (DbBlacklist.dbexists dbh) then
            if not (DbBlockHeader.dbexists dbh) then
              begin
                log_string (Printf.sprintf "ensure_sync requesting header %s\n" (hashval_hexstring dbh));
                find_and_send_requestdata GetHeader dbh
              end
            else if not (DbBlockDelta.dbexists dbh) && ensure_prev_header_valid_p (hashpair lbh ltxh) then
              begin
                log_string (Printf.sprintf "ensure_sync requesting delta %s\n" (hashval_hexstring dbh));
                find_and_send_requestdata GetBlockdelta dbh
              end)
        ctips)
    ctips0l
    
let publish_stx txh stx1 =
  if not (Hashtbl.mem stxpool txh) then Hashtbl.add stxpool txh stx1;
  DbSTx.dbput txh stx1;
  Hashtbl.add published_stx txh ();
  broadcast_inv [(int_of_msgtype STx,txh)]
                
let publish_block blkh bhh (bh,bd) =
  log_string (Printf.sprintf "publishing block %s\n" (hashval_hexstring bhh));
  broadcast_inv [(int_of_msgtype Headers,bhh);(int_of_msgtype Blockdelta,bhh)];;

Hashtbl.add msgtype_handler GetHeader
  (fun (sin,sout,cs,ms) ->
    let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
    let i = int_of_msgtype GetHeader in
    let tm = Unix.time() in
    if recently_sent (i,h) tm cs.sentinv then (*** don't resend ***)
      begin
	log_string (Printf.sprintf "recently sent header %s to %s; not resending\n" (hashval_hexstring h) cs.addrfrom);
      end
    else
      try
	let (bhd,bhs) as bh = DbBlockHeader.dbget h in
	let s = Buffer.create 1000 in
	log_string (Printf.sprintf "sending header %s to %s upon request at time %f (GetHeader)\n" (hashval_hexstring h) cs.addrfrom (Unix.time()));
	seosbf (seo_blockheader seosb bh (seo_hashval seosb h (seo_int8 seosb 1 (s,None))));
	Hashtbl.replace cs.sentinv (i,h) tm;
	let ss = Buffer.contents s in
	ignore (queue_msg cs Headers ss);
	begin
	  try
	    let cnt = Hashtbl.find localnewheader_sent h in
	    Hashtbl.replace localnewheader_sent h (cnt + 1)
	  with Not_found -> ()
	end
      with Not_found ->
	(*** don't have it to send, ignore ***)
	());;

Hashtbl.add msgtype_handler GetHeaders
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let m = ref 0 in
    let bhl = ref [] in
    let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
    c := cn;
    let i = int_of_msgtype GetHeader in
    let tm = Unix.time() in
    for j = 1 to n do
      let (h,cn) = sei_hashval seis !c in
      c := cn;
      if recently_sent (i,h) tm cs.sentinv then (*** don't resend ***)
	begin
	  log_string (Printf.sprintf "recently sent header %s to %s; not resending\n" (hashval_hexstring h) cs.addrfrom);
	end
      else
	try
	  let (blkhd1,blkhs1) as bh = DbBlockHeader.dbget h in
	  if not (blockheader_id bh = h) then
	    log_string (Printf.sprintf "Serious bug: not sending blockheader %s since it does not have correct id but instead %s\n" (hashval_hexstring h) (hashval_hexstring (blockheader_id bh)))
	  else
	    begin
	      incr m;
	      bhl := (h,bh)::!bhl;
	      log_string (Printf.sprintf "sending header %s to %s upon request at time %f (GetHeaders)\n" (hashval_hexstring h) cs.addrfrom (Unix.time()));
	      Hashtbl.replace cs.sentinv (i,h) tm;
	      begin
		try
		  let cnt = Hashtbl.find localnewheader_sent h in
		  Hashtbl.replace localnewheader_sent h (cnt + 1)
		with Not_found -> ()
	      end
	    end;
	with
	| Not_found ->
	   (*** don't have it to send, ignore ***)
	   ()
	| e -> (** ignore any other exception ***)
	   log_string (Printf.sprintf "unexpected exception when handling GetHeaders: %s\n" (Printexc.to_string e))
    done;
    let s = Buffer.create 10000 in
    log_string (Printf.sprintf "sending %d headers\n" !m);
    let co = ref (seo_int8 seosb !m (s,None)) in
    List.iter (fun (h,bh) -> co := seo_blockheader seosb bh (seo_hashval seosb h !co)) !bhl;
    seosbf !co;
    let ss = Buffer.contents s in
    ignore (queue_msg cs Headers ss)
  );;

let deserialize_exc_protect cs f =
  try
    f()
  with e ->
    log_string (Printf.sprintf "Deserialization exception: %s\nDisconnecting and banning node %s\n" (Printexc.to_string e) cs.realaddr);
    cs.banned <- true;
    raise e;;

let rec rec_add_to_missingheaders (lbk,ltx) =
  try
    let (dbh,_,_,(_,_),par,_,currhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
    if not (DbBlockHeader.dbexists dbh) then
      begin
        if not (List.mem (currhght,dbh) !missingheaders) then
          missingheaders := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dbh)] !missingheaders;
        match par with
        | None -> ()
        | Some(plbk,pltx) ->
           rec_add_to_missingheaders (plbk,pltx)
      end
  with Not_found -> ();;

let rec rec_process_headers (lbk,ltx) cnt =
  let lh = hashpair lbk ltx in
  try
    let (h,lmedtm,burned,(txid1,vout1),par,_,currhght) = Db_outlinevals.dbget lh in
    match par with
    | None -> (*** genesis ***)
       let (csm,tar) = (!genesisstakemod,!genesistarget) in
       let (bhd,bhs) = DbBlockHeader.dbget h in
       process_header !Utils.log true true false (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1;
       cnt()
    | Some(plbk,pltx) ->
       let plh = hashpair plbk pltx in
       let (_,_,_,_,_,csm,_) = Db_outlinevals.dbget plh in
       try
         let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget plh in
         try
           let (bhd,bhs) = DbBlockHeader.dbget h in
           process_header !Utils.log true true false (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1;
           cnt()
         with Not_found -> raise Exit
       with Not_found ->
         rec_process_headers
           (plbk,pltx)
           (fun () ->
             try
               let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget plh in
               let (bhd,bhs) = DbBlockHeader.dbget h in
               process_header !Utils.log true true false (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1;
               cnt()
             with Not_found -> raise Exit)
  with Not_found -> raise Exit;;

let rec rec_add_to_missingdeltas (lbk,ltx) =
  try
    let lh = hashpair lbk ltx in
    let (dbh,_,_,(_,_),par,_,currhght) = Db_outlinevals.dbget lh in
    if Db_validheadervals.dbexists lh && not (DbBlockDelta.dbexists dbh) then
      begin
        if not (List.mem (currhght,dbh) !missingdeltas) then
          missingdeltas := List.merge (fun (i,_) (j,_) -> compare i j) [(currhght,dbh)] !missingdeltas;
        match par with
        | None -> ()
        | Some(plbk,pltx) ->
           rec_add_to_missingdeltas (plbk,pltx)
      end
  with Not_found -> ();;

let rec rec_process_deltas (lbk,ltx) cnt =
  let lh = hashpair lbk ltx in
  try
    let (h,lmedtm,burned,(txid1,vout1),par,_,currhght) = Db_outlinevals.dbget lh in
    let (_,_,_,_,_) = Db_validheadervals.dbget lh in
    match par with
    | None -> (*** genesis ***)
       let (csm,tar) = (!genesisstakemod,!genesistarget) in
       let (bhd,bhs) = DbBlockHeader.dbget h in
       let bd = DbBlockDelta.dbget h in
       let thtr = Some(Checking.initthytreeroot) in
       let tht = lookup_thytree thtr in
       process_delta !Utils.log true true false (lbk,ltx) h ((bhd,bhs),bd) thtr tht None None currhght csm tar lmedtm burned txid1 vout1;
       cnt()
    | Some(plbk,pltx) ->
       let plh = hashpair plbk pltx in
       let (_,_,_,_,_,csm,_) = Db_outlinevals.dbget plh in
       try
         let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget plh in
         let tht = lookup_thytree thtr in
	 let sgt = lookup_sigtree sgtr in
         try
           let (bhd,bhs) = DbBlockHeader.dbget h in
           let bd = DbBlockDelta.dbget h in
           process_delta !Utils.log true true false (lbk,ltx) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1;
           cnt()
         with Not_found -> raise Exit
       with Not_found ->
         rec_process_deltas
           (plbk,pltx)
           (fun () ->
             try
               let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget plh in
               let (bhd,bhs) = DbBlockHeader.dbget h in
               let tht = lookup_thytree thtr in
	       let sgt = lookup_sigtree sgtr in
               let bd = DbBlockDelta.dbget h in
               process_delta !Utils.log true true false (lbk,ltx) h ((bhd,bhs),bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1;
               cnt()
             with Not_found -> raise Exit)
  with Not_found -> raise Exit;;

Hashtbl.add msgtype_handler Headers
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
    log_string (Printf.sprintf "got %d Headers\n" n);
    c := cn;
    let tm = Unix.time() in
    for j = 1 to n do
      let (h,cn) = sei_hashval seis !c in
      let (bh,cn) = deserialize_exc_protect cs (fun () -> sei_blockheader seis cn) in (*** deserialize if only to get to the next one ***)
      c := cn;
      if not (h = blockheader_id bh) then
	begin
	  log_string (Printf.sprintf "Ignoring header since it had the wrong id, %s but expected %s.\n" (hashval_hexstring (blockheader_id bh)) (hashval_hexstring h));
	end
      else
	begin
	  let local_process_header (lbk,ltx) =
	    let (bhd,bhs) = bh in
	    if not (Db_validheadervals.dbexists (hashpair lbk ltx)) then
	      begin
		let (dbh,lmedtm,burned,(txid1,vout1),par,newcsm,currhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
		if not (dbh = h) then
		  begin
		    log_string (Printf.sprintf "Impossible Error: Header burn mismatch %s %s %s != %s\n" (hashval_hexstring lbk) (hashval_hexstring ltx) (hashval_hexstring dbh) (hashval_hexstring h))
		  end
		else
		  begin
		    match par with
		    | None -> (*** genesis ***)
		       if bhd.prevblockhash = None then
			 process_header !Utils.log true true true (lbk,ltx) h (bhd,bhs) currhght !genesisstakemod !genesistarget lmedtm burned txid1 vout1
		       else
			 begin
			   Printf.fprintf !Utils.log "Alleged genesis block %s had an invalid header (claims point to a previous block).\n" (hashval_hexstring h);
			   DbInvalidatedBlocks.dbput h true
			 end
		    | Some(plbk,pltx) ->
		       try
			 let (pdbh,plmedtm,pburned,(ptxid1,pvout1),_,csm,_) = Db_outlinevals.dbget (hashpair plbk pltx) in
			 if bhd.prevblockhash = Some(pdbh,Poburn(plbk,pltx,plmedtm,pburned,ptxid1,pvout1)) then
			   begin
			     try
			       let (tar,_,_,_,_) = Db_validheadervals.dbget (hashpair plbk pltx) in
			       process_header !Utils.log true true true (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1
			     with
                             | Not_found ->
			        Hashtbl.add delayed_headers (lbk,ltx) (fun tar -> process_header !Utils.log true true true (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1);
                                if DbBlockHeader.dbexists pdbh then
                                  begin
                                    try
                                      rec_process_headers
                                        (plbk,pltx)
                                        (fun () -> ())
                                    with Exit -> ()
                                  end
                                else if not (Hashtbl.mem delayed_headers (plbk,pltx)) then
                                  rec_add_to_missingheaders (plbk,pltx)
			   end
			 else
			   begin
			     Printf.fprintf !Utils.log "Alleged block %s at height %Ld had an invalid header, pointing to an incorrect previous block or proof of burn.\n" (hashval_hexstring h) currhght;
			     DbInvalidatedBlocks.dbput h true
			   end
		       with Not_found -> () (*** do not know the burn for the parent; ignore header ***)
		  end
	      end
	  in
	  try
	    let (lbk,ltx) = get_burn h in
	    local_process_header (lbk,ltx)
	  with Not_found -> (*** the burn is not there, so do some checks on the header, save the function to process it in unburned_headers, and request delta ***)
	        if sanity_check_header bh then
	          let msb = Buffer.create 100 in
	          seosbf (seo_hashval seosb h (msb,None));
	          let ms = Buffer.contents msb in
                  let (bhd,_) = bh in
                  (if List.length !tmp_delta_roots > 100 then tmp_delta_roots := []);
                  tmp_delta_roots := (h,bhd.blockdeltaroot)::!tmp_delta_roots;
	          let di = int_of_msgtype GetBlockdelta in
	          Hashtbl.replace cs.invreq (di,h) tm;
	          ignore (queue_msg cs GetBlockdelta ms);
	          log_string (Printf.sprintf "Got header %s but not enough info for it so saving it for later\n" (hashval_hexstring h));
	          Hashtbl.add unburned_headers h local_process_header
	end
    done);;

let req_headers sout cs m nw =
  if m > 0 then
    begin
      let s = Buffer.create 1000 in
      let co = ref (seo_int8 seosb m (s,None)) in
      List.iter (fun h -> co := seo_hashval seosb h !co) nw;
      seosbf !co;
      ignore (queue_msg cs GetHeaders (Buffer.contents s))
    end;;

let rec req_header_batches sout cs m hl nw =
  if m = 255 then
    (req_headers sout cs m nw; req_header_batches sout cs 0 hl [])
  else
    match hl with
    | h::hr ->
       let i = int_of_msgtype GetHeader in
       let tm = Unix.time() in
       Hashtbl.replace cs.invreq (i,h) tm;
       req_header_batches sout cs (m+1) hr (h::nw)
    | [] -> req_headers sout cs m nw;;

Hashtbl.add msgtype_handler GetInvNbhd
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let ((i,h),cn) = sei_prod sei_int8 sei_hashval seis !c in
    c := cn;
    match msgtype_of_int i with
    | Headers ->
       begin
	 let tosend = ref [] in
	 collect_header_inv_nbhd 8 h tosend;
	 if not (!tosend = []) then send_inv_to_one !tosend cs
       end
    | _ -> ());;

Hashtbl.add msgtype_handler Inv
  (fun (sin,sout,cs,ms) ->
    let c = ref (ms,String.length ms,None,0,0) in
    let hkl = ref [] in
    let hl = ref [] in
    let (n,cn) = sei_int32 seis !c in
    if n >= 65536l then (** hard upper limit; bug or misbehaving peer **)
      begin
        cs.sendershouldclose <- true;
        Condition.signal cs.sendqueuenonempty;
      end
    else
      begin
    (*    log_string (Printf.sprintf "Inv msg %ld entries\n" n); *)
        c := cn;
        for j = 1 to Int32.to_int n do
          let ((i,h),cn) = sei_prod sei_int8 sei_hashval seis !c in
          c := cn;
          Hashtbl.replace cs.rinv (i,h) ();
          begin
	    try
	      hkl := (Hashtbl.find cs.invreqhooks (i,h))::!hkl; (*** collect hook functions waiting on this inventory message to execute at the end ***)
	      Hashtbl.remove cs.invreqhooks (i,h)
	    with Not_found ->
	      ()
          end;
          if i = int_of_msgtype Headers && not (DbBlockHeader.dbexists h) && not (DbArchived.dbexists h) && not (invalid_or_blacklisted_p h) then hl := h::!hl; (* request headers early *)
          if i = int_of_msgtype STx && not (DbArchived.dbexists h) then
	    begin
	      if not (DbSTx.dbexists h) && not (Hashtbl.mem stxpool h) then
 	        begin
	          let tm = Unix.time() in
	          Hashtbl.replace cs.invreq (int_of_msgtype GetSTx,h) tm;
                  let s = Buffer.create 1000 in
	          seosbf (seo_hashval seosb h (s,None));
	          log_string (Printf.sprintf "Sending GetSTx %s to %s at %f\n" (hashval_hexstring h) cs.realaddr tm);
	          ignore (queue_msg cs GetSTx (Buffer.contents s))
	        end
	    end
        done;
        List.iter (fun hk -> ignore (Thread.create hk ())) !hkl;
        req_header_batches sout cs 0 !hl []
      end);;

Hashtbl.add msgtype_handler GetBlockdelta
  (fun (sin,sout,cs,ms) ->
    let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
    let i = int_of_msgtype GetBlockdelta in
    let tm = Unix.time() in
    if recently_sent (i,h) tm cs.sentinv then (*** don't resend ***)
      begin
	log_string (Printf.sprintf "recently sent delta %s to %s; not resending\n" (hashval_hexstring h) cs.addrfrom);
      end
    else
      try
	let bdsb = Buffer.create 100 in
        seosbf (seo_hashval seosb h (bdsb,None));
        (** DbBlockDelta.dbbincp h bdsb; (* faster, but there is evidence it may not have worked in some cases *) **)
	let blkdel = DbBlockDelta.dbget h in
	let bdsb = Buffer.create 100 in
	seosbf (seo_blockdelta seosb blkdel (seo_hashval seosb h (bdsb,None)));
	let bdser = Buffer.contents bdsb in
	ignore (queue_msg cs Blockdelta bdser);
	Hashtbl.replace cs.sentinv (i,h) tm;
	begin
	  try
	    let cnt = Hashtbl.find localnewdelta_sent h in
	    Hashtbl.replace localnewdelta_sent h (cnt + 1)
	  with Not_found -> ()
	end
      with Not_found ->
	log_string (Printf.sprintf "Unknown Block Delta %s (Bad Peer or Did I Advertize False Inventory?)\n" (hashval_hexstring h));
	());;

Hashtbl.add msgtype_handler Blockdelta
  (fun (sin,sout,cs,ms) ->
    let (h,r) = sei_hashval seis (ms,String.length ms,None,0,0) in
    begin
      let local_process_delta bd (lbk,ltx) =
	let (dbh,lmedtm,burned,(txid1,vout1),par,newcsm,currhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
	if not (dbh = h) then
	  begin
	    log_string (Printf.sprintf "Impossible Error: Delta burn mismatch %s %s %s != %s\n" (hashval_hexstring lbk) (hashval_hexstring ltx) (hashval_hexstring dbh) (hashval_hexstring h))
	  end
	else
	  begin
	    if not (DbBlockDelta.dbexists h) || not (Db_validblockvals.dbexists (hashpair lbk ltx)) then
	      begin
		let bh = DbBlockHeader.dbget h in
		match par with
		| None -> (*** genesis ***)
                   let thtr = Some(Checking.initthytreeroot) in
                   let tht = Some(Checking.initthytree) in
		   process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht None None currhght !genesisstakemod !genesistarget lmedtm burned txid1 vout1
		| Some(plbk,pltx) ->
		   let (pdbh,_,_,_,_,csm,_) = Db_outlinevals.dbget (hashpair plbk pltx) in
		   try
		     let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget (hashpair plbk pltx) in
                     let _ = Db_validblockvals.dbget (hashpair plbk pltx) in
		     let tht = lookup_thytree thtr in
		     let sgt = lookup_sigtree sgtr in
		     process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1
		   with
                   | Not_found ->
		      Hashtbl.add delayed_deltas (lbk,ltx)
		        (fun thtr sgtr tar ->
			  let tht = lookup_thytree thtr in
			  let sgt = lookup_sigtree sgtr in
			  process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1);
                      if DbBlockDelta.dbexists pdbh then
                        begin
                          try
                            rec_process_deltas
                              (plbk,pltx)
                              (fun () -> ())
                          with Exit -> ()
                        end
                      else if not (Hashtbl.mem delayed_deltas (plbk,pltx)) then
                        rec_add_to_missingdeltas (plbk,pltx)
                   | e -> raise e
	      end
	  end
      in
      if not (DbBlockDelta.dbexists h) then (* ignore the delta if we already have it *)
        begin
          try
            log_string (Printf.sprintf "Got delta %s\n" (hashval_hexstring h));
            let bdr =
              try
                let (bhd,_) = DbBlockHeader.dbget h in
                bhd.blockdeltaroot
              with Not_found ->
                List.assoc h !tmp_delta_roots
            in
	    let (bd,_) = deserialize_exc_protect cs (fun () -> sei_blockdelta seis r) in
            try
              if blockdelta_hashroot bd = bdr then (** ignore the delta if the hashroot does not match with one declared in the header **)
	        let (lbk,ltx) = get_burn h in
	        local_process_delta bd (lbk,ltx)
              else
                log_string (Printf.sprintf "ignoring delta %s due to hashroot mismatch" (hashval_hexstring h))
            with Not_found -> (** save the function to process the delta in unburned_deltas in case we need it later **)
	      log_string (Printf.sprintf "Got delta %s but not enough info for it so saving it for later\n" (hashval_hexstring h));
	      Hashtbl.add unburned_deltas h (local_process_delta bd)
          with Not_found ->
            log_string (Printf.sprintf "ignoring delta %s since do not have delta root from header" (hashval_hexstring h))
        end
    end);;

Hashtbl.add msgtype_handler GetSTx
  (fun (sin,sout,cs,ms) ->
    let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
    let i = int_of_msgtype GetSTx in
    let tm = Unix.time() in
    if not (recently_sent (i,h) tm cs.sentinv) then (*** don't resend ***)
      try
	let stau = Hashtbl.find stxpool h in
	let stausb = Buffer.create 100 in
	seosbf (seo_stx seosb stau (seo_hashval seosb h (stausb,None)));
	let stauser = Buffer.contents stausb in
	log_string (Printf.sprintf "Sending Signed Tx (from pool) %s\n" (hashval_hexstring h));
	ignore (queue_msg cs STx stauser);
	Hashtbl.replace cs.sentinv (i,h) tm
      with Not_found ->
	try
	  let stau = DbSTx.dbget h in
	  let stausb = Buffer.create 100 in
	  seosbf (seo_stx seosb stau (seo_hashval seosb h (stausb,None)));
	  let stauser = Buffer.contents stausb in
	  log_string (Printf.sprintf "Sending Signed Tx (from db) %s\n" (hashval_hexstring h));
	  ignore (queue_msg cs STx stauser);
	  Hashtbl.replace cs.sentinv (i,h) tm
	with Not_found ->
	  log_string (Printf.sprintf "Unknown Tx %s\n" (hashval_hexstring h));
	  ());;

let add_to_txpool txid stau =
  Hashtbl.add stxpool txid stau;
  let ((txin,_),_) = stau in
  List.iter (fun (_,h) -> Hashtbl.add unconfirmed_spent_assets h txid) txin
            
let remove_from_txpool txid =
  try
    let stau = Hashtbl.find stxpool txid in
    Hashtbl.remove stxpool txid;
    Hashtbl.remove stxpooltm txid;
    Hashtbl.remove stxpoolfee txid;
    let ((txin,_),_) = stau in
    List.iter (fun (_,h) -> Hashtbl.remove unconfirmed_spent_assets h) txin
  with Not_found -> ()
                      
let savetxtopool_real txid stau =
  let ch = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o600 (Filename.concat (datadir()) "txpool") in
  seocf (seo_prod seo_hashval seo_stx seoc (txid,stau) (ch,None));
  close_out_noerr ch;
  let ch = open_out_gen [Open_creat;Open_append;Open_wronly;Open_binary] 0o600 (Filename.concat (datadir()) "txpooltm") in
  seocf (seo_prod seo_int64 seo_hashval seoc (Int64.of_float (Unix.time()),txid) (ch,None));
  close_out_noerr ch;;

Hashtbl.add msgtype_handler STx
  (fun (sin,sout,cs,ms) ->
    let (h,r) = sei_hashval seis (ms,String.length ms,None,0,0) in
    let i = int_of_msgtype GetSTx in
    let tm = Unix.time() in
    log_string (Printf.sprintf "Got Signed Tx %s from %s at %f\n" (hashval_hexstring h) cs.realaddr tm);
    if not (DbSTx.dbexists h) && not (Hashtbl.mem stxpool h) then (*** if we already have it, abort ***)
      if recently_requested (i,h) tm cs.invreq then (*** only continue if it was requested ***)
        let (((tauin,tauout) as tau,_) as stau,_) = deserialize_exc_protect cs (fun () -> sei_stx seis r) in
	if hashstx stau = h then
	  begin
	    let txbytes = stxsize stau in
	    if txbytes > 450000 then
	      (log_string (Printf.sprintf "ignoring tx %s since it is %d bytes, above the 450K bytes limit" (hashval_hexstring h) txbytes))
	    else
	      let minfee = Int64.mul (Int64.of_int txbytes) !Config.minrelayfee in
	      try
		begin
		  match get_bestblock() with
		  | (Some(dbh,lbk,ltx),_) -> (*** ignore consensus warnings here ***)
		     begin
		       let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		       let nblkh = Int64.add 1L blkh in
		       let (_,tmstmp,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		       if tx_valid tau then
			 let unsupportederror alpha k = log_string (Printf.sprintf "Could not find asset %s at address %s in ledger %s; throwing out tx %s\n" (hashval_hexstring k) (Cryptocurr.addr_pfgaddrstr alpha) (hashval_hexstring lr) (hashval_hexstring h)) in
			 let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin (CHash(lr)) unsupportederror) in
			 if tx_signatures_valid nblkh tmstmp al stau then (*** accept it if it will be valid in the next block ***)
			   begin
			     let nfee = ctree_supports_tx (ref 0) true true false (lookup_thytree tr) (lookup_sigtree sr) nblkh tau (CHash(lr)) in
			     let fee = Int64.sub 0L nfee in
			     if fee >= minfee then
			       begin
                                 Hashtbl.add stxpoolfee h (Int64.div fee (Int64.of_int txbytes));
				 Hashtbl.add stxpool h stau;
				 log_string (Printf.sprintf "Accepting tx %s into pool\n" (hashval_hexstring h));
				 add_to_txpool h stau;
				 savetxtopool_real h stau;
                                 broadcast_inv [(int_of_msgtype STx,h)];
                                 if !Config.swapping then analyze_swapmatchoffer_tx h (hashtx tau) tauout
			       end
			     else
			       (log_string (Printf.sprintf "ignoring tx %s with low fee of %s bars (%Ld atoms)\n" (hashval_hexstring h) (Cryptocurr.bars_of_atoms fee) fee))
			   end
			 else
			   (log_string (Printf.sprintf "ignoring tx %s since signatures are not valid at the next block height of %Ld\n" (hashval_hexstring h) nblkh))
		       else
			 (log_string (Printf.sprintf "misbehaving peer? [invalid Tx %s]\n" (hashval_hexstring h)))
		     end
		  | _ -> raise Not_found
		end
	      with _ ->
		(log_string (Printf.sprintf "Tx %s is unsupported by the local ledger, dropping it.\n" (hashval_hexstring h)))
	  end
        else (*** otherwise, it seems to be a misbehaving peer --  ignore for now ***)
	  (log_string (Printf.sprintf "misbehaving peer? [malformed Tx]\n"))
      else (*** if something unrequested was sent, then seems to be a misbehaving peer ***)
	(log_string (Printf.sprintf "misbehaving peer? [unrequested Tx %s]\n" (hashval_hexstring h))));;

let dumpblocktreestate sa =
  Printf.fprintf sa "=========\nstxpool:\n";
  Hashtbl.iter
    (fun h ((tauin,tauout) as tau,tausg) ->
      Printf.fprintf sa "- tx %s\n" (hashval_hexstring (hashtx tau));
      Printf.fprintf sa "inputs %d\n" (List.length tauin);
      let c = ref 0 in
      List.iter
	(fun (alpha,aid) ->
	  Printf.fprintf sa "%d. %s %s\n" !c (Cryptocurr.addr_pfgaddrstr alpha) (hashval_hexstring aid);
	  incr c)
	tauin;
      Printf.fprintf sa "outputs %d\n" (List.length tauin);
      c := 0;
      List.iter (fun (alpha,(obl,u)) ->
	  Printf.fprintf sa "%d. %s %s %s\n" !c (Cryptocurr.addr_pfgaddrstr alpha) (obligation_string obl) (preasset_string u);
	  incr c)
	tauout;
      let sb = Buffer.create 100 in
      seosbf (seo_stx seosb (tau,tausg) (sb,None));
      Printf.fprintf sa "%s\n" (string_hexstring (Buffer.contents sb))
    )
    stxpool;
  Printf.fprintf sa "=========\npublished_stx:\n";
  Hashtbl.iter (fun h () ->
      Printf.fprintf sa "- tx %s\n" (hashval_hexstring h))
    published_stx;
  Printf.fprintf sa "=========\nthytree:\n";
  Hashtbl.iter (fun h _ ->
      Printf.fprintf sa "- thytree root %s\n" (hashval_hexstring h))
    thytree;
  Printf.fprintf sa "=========\nsigtree:\n";
  Hashtbl.iter (fun h _ ->
      Printf.fprintf sa "- sigtree root %s\n" (hashval_hexstring h))
    sigtree;;

let print_consensus_warning s cw =
  match cw with
  | ConsensusWarningMissing(h,lbk,ltx) ->
     begin
       try
	 let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	 Printf.fprintf s "Missing Block %Ld %s%s\n"
	   blkh (hashval_hexstring h)
	   (if Db_validblockvals.dbexists (hashpair lbk ltx) then
	      " Block Validated"
	    else if Db_validheadervals.dbexists (hashpair lbk ltx) then " Header Validated"
	    else "")
       with _ ->
	 Printf.fprintf s "Missing Block %s%s\n"
	   (hashval_hexstring h)
	   (if Db_validblockvals.dbexists (hashpair lbk ltx) then
	      " Block Validated"
	    else if Db_validheadervals.dbexists (hashpair lbk ltx) then " Header Validated"
	    else "")
     end
  | ConsensusWarningBlacklist(h) ->
     Printf.fprintf s "Blacklisted Block %s\n" (hashval_hexstring h)
  | ConsensusWarningInvalid(h) ->
     Printf.fprintf s "Invalid Block %s\n" (hashval_hexstring h)
  | ConsensusWarningNoBurn(h) ->
     Printf.fprintf s "Could not find ltc burn for block %s\n" (hashval_hexstring h)
  | ConsensusWarningTerminal ->
     Printf.fprintf s "No blocks were created in the past week. Proofgold has reached terminal status.\nThe only recovery possible for the network is a hard fork.\nSometimes this message means the node is out of sync with ltc.\n";;

let get_bestblock_print_warnings s =
  let (b,cwl) = get_bestblock() in
  List.iter (print_consensus_warning s) cwl;
  b;;

let get_bestblock_cw_exception e =
  let (best,cwl) = get_bestblock() in
  begin
    try
      let cw =
	List.find
	  (fun cw ->
	    match cw with
	    | ConsensusWarningMissing(_,_,_) -> true
	    | _ -> false)
	  cwl
      in
      print_consensus_warning !log cw;
      log_string (Printf.sprintf "possibly not synced; delaying staking\n");
      raise Exit
    with
    | Not_found -> ()
    | Exit -> raise e
  end;
  match best with
  | Some(dbh,lbk,ltx) -> (dbh,lbk,ltx)
  | None -> raise e;;

let print_best_block () =
  let (b,cwl) = get_bestblock () in
  List.iter (print_consensus_warning !Utils.log) cwl;
  match b with
  | Some(bh,lbk,ltx) -> log_string (Printf.sprintf "bestblock %s\nsupported by %s %s\n" (hashval_hexstring bh) (hashval_hexstring lbk) (hashval_hexstring ltx))
  | None -> log_string (Printf.sprintf "no bestblock\n")
                       
