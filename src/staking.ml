(* Copyright (c) 2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2017 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint
open Utils
open Sha256
open Hashaux
open Hash
open Ser
open Ltcrpc
open Net
open Mathdata
open Assets
open Tx
open Secp256k1
open Cryptocurr
open Signat
open Ctre
open Ctregraft
open Block
open Blocktree
open Commands

let sorted_stxpool () =
  let sl1 = ref [] in (* no fee info, assume local so prefer and don't require fee *)
  let sl2 = ref [] in (* fee info, sorted by fee size *)
  Hashtbl.iter
    (fun h stau ->
      try
        let fee = Hashtbl.find stxpoolfee h in
        sl2 := List.merge (fun (_,_,x) (_,_,y) -> compare y x) [(h,stau,fee)] !sl2
      with Not_found ->
        sl1 := (h,stau)::!sl1)
    stxpool;
  !sl1 @ List.map (fun (h,stau,_) -> (h,stau)) !sl2

let blockheaderdata_burn_vin1_match bhd txid vout =
  match bhd.pureburn with
  | None -> true
  | Some(txid1,vout1) -> (txid = txid1) && (vout = vout1)
  
let advertise_new_block newblkid =
  broadcast_inv [(int_of_msgtype Headers,newblkid);(int_of_msgtype Blockdelta,newblkid)];
  Hashtbl.add localnewheader_sent newblkid 0;
  Hashtbl.add localnewdelta_sent newblkid 0

let get_reward_locktime blkh =
  let rl =
    match !Config.reward_lock_relative with
    | None -> reward_locktime
    | Some(rl) -> if rl > reward_locktime then rl else reward_locktime
  in
  let m = Int64.add blkh rl in
  match !Config.reward_lock_absolute with
  | None -> m
  | Some(a) -> if a > m then a else m

let pendingpfgblock : (unit -> unit) option ref = ref None;;
let pendingltctxs : string list ref = ref [];;

let staking_local_process_header h (bhd,bhs) (lbk,ltx) =
  let (dbh,lmedtm,burned,(txid1,vout1),par,newcsm,currhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
  if not (dbh = h) then
    log_string (Printf.sprintf "Impossible Error: Header burn mismatch %s %s %s != %s\n" (hashval_hexstring lbk) (hashval_hexstring ltx) (hashval_hexstring dbh) (hashval_hexstring h))
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
               with Not_found ->
                 Hashtbl.add delayed_headers (lbk,ltx) (fun tar -> process_header !Utils.log true true true (lbk,ltx) h (bhd,bhs) currhght csm tar lmedtm burned txid1 vout1)
             end
           else
             begin
               Printf.fprintf !Utils.log "Alleged block %s at height %Ld had an invalid header, pointing to an incorrect previous block or proof of burn.\n" (hashval_hexstring h) currhght;
               DbInvalidatedBlocks.dbput h true
             end
         with Not_found -> () (*** do not know the burn for the parent; ignore header for now ***)
    end

let staking_local_process_delta h (bh,bd) (lbk,ltx) =
  let (dbh,lmedtm,burned,(txid1,vout1),par,newcsm,currhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
  if not (dbh = h) then
    begin
      log_string (Printf.sprintf "Impossible Error: Delta burn mismatch %s %s %s != %s\n" (hashval_hexstring lbk) (hashval_hexstring ltx) (hashval_hexstring dbh) (hashval_hexstring h))
    end
  else
    begin
      if not (DbBlockDelta.dbexists h) || not (Db_validblockvals.dbexists (hashpair lbk ltx)) then
        begin
          match par with
          | None -> (*** genesis ***)
             let thtr = Some(Checking.initthytreeroot) in
             let tht = Some(Checking.initthytree) in
             process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht None None currhght !genesisstakemod !genesistarget lmedtm burned txid1 vout1
          | Some(plbk,pltx) ->
             let (_,_,_,_,_,csm,_) = Db_outlinevals.dbget (hashpair plbk pltx) in
             try
               let (tar,_,_,thtr,sgtr) = Db_validheadervals.dbget (hashpair plbk pltx) in
               let tht = lookup_thytree thtr in
               let sgt = lookup_sigtree sgtr in
               process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1
             with
             | Not_found ->
                Hashtbl.add delayed_deltas (lbk,ltx)
                  (fun thtr sgtr tar ->
                    let tht = lookup_thytree thtr in
                    let sgt = lookup_sigtree sgtr in
                    process_delta !Utils.log true true true (lbk,ltx) h (bh,bd) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1)
             | e -> raise e
        end
    end

type nextstakeinfo =
  | NextPureBurn of (int64 * ltcutxo * hashval * int * int64 * (hashval * hashval) option ref * hashval option * ttree option * hashval option * stree option)
  | NextStake of (int64 * p2pkhaddr * hashval * int64 * obligation * int64 * int64 option * (hashval * hashval) option ref * hashval option * ttree option * hashval option * stree option)
  | NoStakeUpTo of int64;;

let nextstakechances : (hashval * hashval,nextstakeinfo) Hashtbl.t = Hashtbl.create 100;;
let nextstakechances_hypo : (hashval * hashval,nextstakeinfo) Hashtbl.t = Hashtbl.create 100;;
let nextstakechances_checkedtotm : (hashval * hashval,int64) Hashtbl.t = Hashtbl.create 100;;

let stakingassetsmutex = Mutex.create();;

let compute_recid (r,s) k =
  match smulp k _g with
  | Some(x,y) ->
      if eq_big_int x r then
	if evenp y then 0 else 1
      else
	if evenp y then 2 else 3
  | None -> raise (Failure "bad0");;

let rec hlist_stakingassets blkh alpha hl n =
  let minamt =
    if blkh < 5000L then
      0L
    else if blkh < 16000L then
      10000000000L
    else if blkh < 18000L then
      100000000000L
    else if blkh < 20000L then
      1000000000000L
    else
      10000000000000L
  in
  if n > 0 then
    match hl with
    | HCons((aid,bday,obl,Currency(v)),hr) when v >= minamt ->
       let ca = coinage blkh bday obl v in
(*	log_string (Printf.sprintf "Checking asset %s %Ld %Ld %s %Ld %s\n" (hashval_hexstring aid) blkh bday (obligation_string obl) v (string_of_big_int ca)); *)
       if gt_big_int ca zero_big_int && not (Hashtbl.mem unconfirmed_spent_assets aid) && (blkh < 730L || bday > 0L) then
	  begin
(*	    log_string (Printf.sprintf "Staking asset: %s\n" (hashval_hexstring aid)); *)
	    Mutex.lock stakingassetsmutex;
	    Commands.stakingassets := (alpha,aid,bday,obl,v)::!Commands.stakingassets;
	    Mutex.unlock stakingassetsmutex;
	  end;
	hlist_stakingassets blkh alpha hr (n-1)
    | HCons(_,hr) -> hlist_stakingassets blkh alpha hr (n-1)
    | HConsH(h,hr) ->
	begin
	  try
	    hlist_stakingassets blkh alpha (HCons(DbAsset.dbget h,hr)) n
	  with Not_found -> ()
	end
    | HHash(h,_) ->
	begin
	  try
	    let (h1,h2) = DbHConsElt.dbget h in
	    match h2 with
	    | Some(h2,l2) -> hlist_stakingassets blkh alpha (HConsH(h1,HHash(h2,l2))) n
	    | None -> hlist_stakingassets blkh alpha (HConsH(h1,HNil)) n
	  with Not_found -> ()
	end
    | _ -> ()
  else
    ();;

let extraburn : int64 ref = ref 0L;;

exception StakingPause of float
exception StakingProblemPause
exception StakingPublishBlockPause

let compute_staking_chances (prevblkh,lbk,ltx) fromtm totm =
  try
    let (_,lmedtm,burned,_,_,csm1,prevblkhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
    let blkhght = Int64.add 1L prevblkhght in
    let (tar1,tmstamp,currledgerroot,thyroot,sigroot) = Db_validheadervals.dbget (hashpair lbk ltx) in
    if Db_validblockvals.dbexists (hashpair lbk ltx) then
      begin
        let thytree =
          try
	    lookup_thytree thyroot
          with Not_found ->
	    log_string (Printf.sprintf "Do not know theory tree with root %s\n" (match thyroot with None -> "None" | Some(h) -> hashval_hexstring h));
	    raise StakingProblemPause
        in
        let sigtree =
          try
	    lookup_sigtree sigroot
          with Not_found ->
	    log_string (Printf.sprintf "Do not know signature tree with root %s\n" (match sigroot with None -> "None" | Some(h) -> hashval_hexstring h));
	    raise StakingProblemPause
        in
        let fromtm =
          try
	    Hashtbl.find nextstakechances_checkedtotm (lbk,ltx)
          with Not_found -> fromtm
        in
        let i = ref (max fromtm (Int64.add 1L tmstamp)) in
        if !Config.maxburn < 0L then (*** if must burn but not willing to burn, don't bother computing next staking chances ***)
          ()
        else
          let c = CHash(currledgerroot) in
          (*** collect assets allowed to stake now ***)
          Commands.stakingassets := [];
          let minburntostake = ref None in
          log_string (Printf.sprintf "Collecting staking assets in ledger %s (block height %Ld).\n" (hashval_hexstring currledgerroot) blkhght);
          let stakingkeys : (md160,unit) Hashtbl.t = Hashtbl.create 10 in
          let mbn = max !extraburn !Config.maxburn in
          let mbnb = big_int_of_int64 mbn in
          List.iter
	    (fun (k,b,(x,y),w,h,alpha) ->
	      Hashtbl.add stakingkeys h (); (*** remember this is a staking key to decide whether to stake with related endorsed assets ***)
	      match try ctree_addr true true (p2pkhaddr_addr h) c None with _ -> (None,0) with
	      | (Some(hl),_) ->
                 hlist_stakingassets blkhght h (nehlist_hlist hl) 30
	      | _ ->
	         ())
	    !Commands.walletkeys_staking;
          List.iter
	    (fun (alpha,beta,_,_,_,_) ->
	      let (p,x4,x3,x2,x1,x0) = alpha in
	      let (q,y4,y3,y2,y1,y0) = beta in
	      if not p && not q && Hashtbl.mem stakingkeys (y4,y3,y2,y1,y0) then (*** only p2pkh can stake ***)
	        match try ctree_addr true true (payaddr_addr alpha) c None with _ -> (None,0) with
	        | (Some(hl),_) ->
		   hlist_stakingassets blkhght (x4,x3,x2,x1,x0) (nehlist_hlist hl) 50
	        | _ -> ())
	    !Commands.walletendorsements;
          log_string (Printf.sprintf "%d staking assets\n" (List.length !Commands.stakingassets));
          let lul = ltc_listunspent () in
          if not (!Commands.stakingassets = []) || not (lul = []) then
	    let nextstake i stkaddr h bday obl v toburn =
	      Hashtbl.add nextstakechances (lbk,ltx) (NextStake(i,stkaddr,h,bday,obl,v,toburn,ref None,thyroot,thytree,sigroot,sigtree));
              raise Exit
	    in
	    let nextpureburn i lutxo txidh vout toburn =
              Hashtbl.add nextstakechances (lbk,ltx) (NextPureBurn(i,lutxo,txidh,vout,toburn,ref None,thyroot,thytree,sigroot,sigtree));
              raise Exit
            in
	    try
	      while !i < totm do
	        i := Int64.add 1L !i;
                if prevblkhght < 730L then (*** go through ltc utxos to look for pure burn chances ***)
                  List.iter
                    (fun lutxo ->
                      try
                        match lutxo with
                        | LtcP2shSegwit(txid,vout,ltcaddr,_,_,amt) ->
                           let txidh = hexstring_hashval txid in
                           let h = hashtag txidh (Int32.of_int vout) in
                           let hv = hitval !i h csm1 in
		           let minv = div_big_int hv tar1 in
		           let toburn = succ_big_int (div_big_int minv (big_int_of_int 1000000)) in
                           if lt_big_int toburn (big_int_of_int64 100000000000L) then
                             let toburn64 = int64_of_big_int toburn in
		             if 0L < toburn64 && Int64.add toburn64 !Config.ltctxfee <= amt then
                               begin
                                 (if le_big_int toburn mbnb then nextpureburn !i lutxo txidh vout toburn64);
		                 match !minburntostake with
		                 | None ->
			            Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thyroot,thytree,sigroot,sigtree));
			            minburntostake := Some(toburn,!i,None,Some(txidh,vout))
		                 | Some(mburn,_,_,_) ->
			            if lt_big_int toburn mburn then
			              begin
			                Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thyroot,thytree,sigroot,sigtree));
                                        minburntostake := Some(toburn,!i,None,Some(txidh,vout))
                                      end
                               end
                        | LtcBech32(txid,vout,ltcaddr,_,amt) ->
                           let txidh = hexstring_hashval txid in
                           let h = hashtag txidh (Int32.of_int vout) in
                           let hv = hitval !i h csm1 in
		           let minv = div_big_int hv tar1 in
		           let toburn = succ_big_int (div_big_int minv (big_int_of_int 1000000)) in
		           (* log_string (Printf.sprintf "Checking for pure burn of %s %Ld at time %Ld -- hv %s toburn %s tar1 %s\n" txid amt !i (string_of_big_int hv) (string_of_big_int toburn) (string_of_big_int tar1)); *)
                           if lt_big_int toburn (big_int_of_int64 100000000000L) then
                             let toburn64 = int64_of_big_int toburn in
		             if 0L < toburn64 && Int64.add toburn64 !Config.ltctxfee <= amt then
                               begin
                                 (if le_big_int toburn mbnb then nextpureburn !i lutxo txidh vout toburn64);
		                 match !minburntostake with
		                 | None ->
			            Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thyroot,thytree,sigroot,sigtree));
			            minburntostake := Some(toburn,!i,None,Some(txidh,vout))
		                 | Some(mburn,_,_,_) ->
			            if lt_big_int toburn mburn then
			              begin
			                Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thyroot,thytree,sigroot,sigtree));
                                        minburntostake := Some(toburn,!i,None,Some(txidh,vout))
                                      end
                               end
                      with
                      | Exit -> raise Exit
                      | _ -> ())
                    lul;
	        (*** go through assets and check for staking at time !i ***)
	        List.iter
	          (fun (stkaddr,h,bday,obl,v) ->
		    (** log_string (Printf.sprintf "Checking for staking of %s at time %Ld\n" (hashval_hexstring h) !i); **)
		    let caf = coinagefactor blkhght bday obl in
		    if gt_big_int caf zero_big_int then
		      begin
		        let hv = hitval !i h csm1 in
		        let mtar = mult_big_int tar1 caf in
		        let minv = div_big_int hv mtar in
		        let toburn =
                          if blkhght < 124L then
                            succ_big_int (div_big_int (sub_big_int minv (big_int_of_int64 v)) (big_int_of_int 1000000))
                          else
                            succ_big_int (div_big_int (sub_big_int (mult_big_int minv (big_int_of_int 10000)) (big_int_of_int64 v)) (big_int_of_int 1000000))
                        in
		        if lt_big_int zero_big_int toburn && lt_big_int toburn (big_int_of_string "1000000000") then (*** 10 ltc limit for reporting staking chances ***)
		          begin
			    match !minburntostake with
			    | None ->
			       Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextStake(!i,stkaddr,h,bday,obl,v,Some(int64_of_big_int toburn),ref None,thyroot,thytree,sigroot,sigtree));
			       minburntostake := Some(toburn,!i,Some(stkaddr,h),None)
			    | Some(mburn,_,_,_) ->
			       if lt_big_int toburn mburn then
			         begin
				   Hashtbl.add nextstakechances_hypo (lbk,ltx) (NextStake(!i,stkaddr,h,bday,obl,v,Some(int64_of_big_int toburn),ref None,thyroot,thytree,sigroot,sigtree));
				   minburntostake := Some(toburn,!i,Some(stkaddr,h),None)
			         end
		          end;
			if le_big_int toburn zero_big_int then (*** hit without burn ***)
		          nextstake !i stkaddr h bday obl v (Some(0L)) (*** burn nothing, but announce in the pow chain (ltc) ***)
		        else
		          if le_big_int toburn mbnb then (*** hit with burn ***)
			    nextstake !i stkaddr h bday obl v (Some(int64_of_big_int toburn))
		      end
	          )
	          !Commands.stakingassets
	      done;
	      log_string (Printf.sprintf "No staking chances up to time %Ld\n" totm);
	      Hashtbl.add nextstakechances (lbk,ltx) (NoStakeUpTo(totm));
	    with
	    | Exit ->
               ()
	    | exn ->
	       log_string (Printf.sprintf "Unexpected Exception in Staking Loop: %s\n" (Printexc.to_string exn))
      end
    else
      raise Not_found
  with exn ->
    log_string (Printf.sprintf "Unexpected Exception in Staking: %s\n" (Printexc.to_string exn));
    raise StakingProblemPause
        
let genesisstakechances : nextstakeinfo option ref = ref None
let genesisstakechances_hypo : nextstakeinfo list ref = ref []

(** nothing to stake, so can only be pure burn **)
let compute_genesis_staking_chances fromtm totm =
  let i = ref (max fromtm (Int64.add 1L !Config.genesistimestamp)) in
  if !Config.maxburn <= 0L then (*** if must burn but not willing to burn, don't bother computing next staking chances ***)
    ()
  else
    let lul = ltc_listunspent () in
    if lul = [] then
      ()
    else
      let minburntostake = ref None in
      try
        while !i < totm do
          i := Int64.add 1L !i;
          (*** go through ltc utxos to look for pure burn chances ***)
          List.iter
            (fun lutxo ->
              try
                match lutxo with
                | LtcP2shSegwit(txid,vout,ltcaddr,_,_,amt) ->
                   let txidh = hexstring_hashval txid in
                   let h = hashtag txidh (Int32.of_int vout) in
                   let hv = hitval !i h !genesisstakemod in
		   let minv = div_big_int hv !genesistarget in
		   let toburn = succ_big_int (div_big_int minv (big_int_of_int 1000000)) in
                   let toburn64 = int64_of_big_int toburn in
                   let thtr = Some(Checking.initthytreeroot) in
		   let tht = Some (Checking.initthytree) in
		   if 0L < toburn64 && Int64.add toburn64 !Config.ltctxfee <= amt then
                     begin
                       begin
                         match !genesisstakechances with
                         | None when toburn64 <= !Config.maxburn ->
                            genesisstakechances := Some(NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None))
                         | _ -> ()
                       end;
		       match !minburntostake with
		       | None ->
			  genesisstakechances_hypo := (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None)) :: !genesisstakechances_hypo;
			  minburntostake := Some(toburn,!i,txidh,vout)
		       | Some(mburn,_,_,_) ->
			  if lt_big_int toburn mburn then
			    begin
			      genesisstakechances_hypo := (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None)) :: !genesisstakechances_hypo;
                              minburntostake := Some(toburn,!i,txidh,vout)
                            end
                     end
                | LtcBech32(txid,vout,ltcaddr,_,amt) ->
                   let txidh = hexstring_hashval txid in
                   let h = hashtag txidh (Int32.of_int vout) in
                   let hv = hitval !i h !genesisstakemod in
		   let minv = div_big_int hv !genesistarget in
		   let toburn = succ_big_int (div_big_int minv (big_int_of_int 1000000)) in
                   let toburn64 = int64_of_big_int toburn in
                   let thtr = Some(Checking.initthytreeroot) in
		   let tht = Some (Checking.initthytree) in
		   if 0L < toburn64 && Int64.add toburn64 !Config.ltctxfee <= amt then
                     begin
                       begin
                         match !genesisstakechances with
                         | None when toburn64 <= !Config.maxburn ->
                            genesisstakechances := Some(NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None))
                         | _ -> ()
                       end;
		       match !minburntostake with
		       | None ->
			  genesisstakechances_hypo := (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None)) :: !genesisstakechances_hypo;
			  minburntostake := Some(toburn,!i,txidh,vout)
		       | Some(mburn,_,_,_) ->
			  if lt_big_int toburn mburn then
			    begin
			      genesisstakechances_hypo := (NextPureBurn(!i,lutxo,txidh,vout,toburn64,ref None,thtr,tht,None,None)) :: !genesisstakechances_hypo;
                              minburntostake := Some(toburn,!i,txidh,vout)
                            end
                     end
              with _ -> ())
            lul
        done;
        match !genesisstakechances with
        | None -> genesisstakechances := Some(NoStakeUpTo(totm))
        | _ -> ()
      with
      | Exit -> ()
      | exn ->
	 log_string (Printf.sprintf "Unexpected Exception in Staking Loop: %s\n" (Printexc.to_string exn));;

exception Genesis;;
exception SyncIssue;;

(***
 The staking code underwent a major rewrite in March 2019.
 ***)
let stakingthread () =
  log_string (Printf.sprintf "stakingthread thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let sleepuntil = ref (ltc_medtime()) in
  let pending = ref None in
  while true do
    try
      let nw = ltc_medtime() in
      let sleeplen = Int64.to_float (Int64.sub !sleepuntil nw) in
(*      log_string (Printf.sprintf "Staking sleeplen %f seconds\n" sleeplen); *)
      if sleeplen > 1.0 then Thread.delay sleeplen;
(*      log_string (Printf.sprintf "Staking after sleeplen %f seconds thread %d\n" sleeplen (Thread.id (Thread.self()))); *)
      if not (ltc_synced()) then (log_string (Printf.sprintf "ltc not synced yet; delaying staking\n"); raise (StakingPause(60.0)));
      pendingltctxs := List.filter (fun h -> ltc_tx_confirmed h = None) !pendingltctxs;
      if not (!pendingltctxs = []) then (log_string (Printf.sprintf "there are pending ltc txs; delaying staking\n"); raise (StakingPause(60.0)));
      (match !pendingpfgblock with Some(p) -> p() | None -> ()); (* if a pfg block has been staked, but not yet burned *)
      try
        let (pbhh1,lbk,ltx) = get_bestblock_cw_exception (if nw < Int64.add !Config.genesistimestamp 604800L && !Config.genesis then Genesis else SyncIssue) in
        try
	  let (_,plmedtm,pburned,(ptxid1,pvout1),par,csm0,pblkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	  let (tar0,pbhtm,prevledgerroot,thtr,sgtr) = Db_validheadervals.dbget (hashpair lbk ltx) in
	  if Db_validblockvals.dbexists (hashpair lbk ltx) then (** do not stake until best block is fully validated **)
            begin
              match Hashtbl.find nextstakechances (lbk,ltx) with
              | NextPureBurn(tm,lutxo,txidh,vout,toburn,already,thyroot,thytree,sigroot,sigtree) ->
                 begin
	           match !already with
	           | Some(_,_) -> raise SyncIssue
	           | None ->
		      begin
		        let nw = ltc_medtime() in
	                log_string (Printf.sprintf "NextPureBurn tm = %Ld nw = %Ld\n" tm nw);
		        if tm >= Int64.add nw 60L || tm <= pbhtm then
		          begin (*** wait for a minute and then reevaluate; would be better to sleep until time to publish or until a new best block is found **)
			    let tmtopub = Int64.sub tm nw in
			    log_string ((Int64.to_string tmtopub) ^ " seconds until time to publish staked block\n");
			    if tmtopub >= 60L then
			      sleepuntil := Int64.add nw 60L
			    else
			      begin
			        sleepuntil := Int64.add nw tmtopub;
			      end
		          end
		        else
		          begin (** go ahead and form the block; then publish it at the right time **)
			    let deltm = Int64.to_int32 (Int64.sub tm pbhtm) in
			    let blkh = Int64.add 1L pblkh in
			    let tar = retarget tar0 deltm in
                            let alpha =
                              (let (_,alpha3) = Commands.generate_newkeyandaddress prevledgerroot (if !Config.stakewithrewards then "staking" else "nonstaking") in alpha3) (*** prevent staking address from ending up holding too many assets; max 32 are allowed ***)
                            in
                            let alpha2 = p2pkhaddr_addr alpha in
                            let aid = hashtag txidh (Int32.of_int vout) in
                            let a = (aid,0L,None,Currency(0L)) in
			    let prevc = (* insert temporary asset to simulate staking when doing pure burn *)
                              tx_octree_trans_ true false 162 [] [(addr_bitseq alpha2,a)] (Some(CHash(prevledgerroot)))
                            in
			    let octree_ctree c =
			      match c with
			      | Some(c) -> c
			      | None -> raise (Failure "tree should not be empty")
			    in
                            try
			      let dync = ref (octree_ctree prevc) in
			      let dyntht = ref (lookup_thytree thtr) in (** The theory tree and signature tree change all at once at the end of processing the block **)
			      let dynsigt = ref (lookup_sigtree sgtr) in (** so these two do not really need to be refs. **)
			      let fees = ref 0L in
			      let otherstxs = ref [] in
			      let othersout = ref [] in
                              let counter = ref 0 in
			      let rembytesestimate = ref (maxblockdeltasize blkh - (2048 * 2)) in (*** estimate the remaining room in the block delta if the tx is added ***)
			      let try_to_incl_stx h stau =
			        let ((tauin,tauout) as tau,sg) = stau in
                                (*		    log_string (Printf.sprintf "Trying to include tx %s\n" (hashval_hexstring h)); *)
			        try
			          ignore (List.find (fun (alpha,_) -> alpha = alpha2) tauout) (*** Do not include txs that spend to the staking address, to avoid the possibility of ending up with too many assets at the staking address ***)
			        with Not_found ->
			          if tx_valid (tauin,tauout) then
                                    begin
			              try
				        let unsupportederror alpha h = log_string (Printf.sprintf "Could not find asset %s at address %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha)) in
				        let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin !dync unsupportederror) in
				        if tx_signatures_valid blkh tm al ((tauin,tauout),sg) then
				          begin
                                            let counter1 = !counter in
                                            try
				              let nfee = ctree_supports_tx counter true true false !dyntht !dynsigt blkh (tauin,tauout) !dync in
				              if nfee > 0L then (*** note: nfee is negative of the fee, not the fee itself ***)
				                begin
                                                (*				  log_string (Printf.sprintf "tx %s has negative fees %Ld; removing from pool\n" (hashval_hexstring h) nfee); *)
					          remove_from_txpool h;
				                end
				              else
                                                let realsize = stxsize stau in
				                let bytesestimate = realsize + 1024 * List.length tauin + 1024 * List.length tauout in (*** extra 1K per input and output (since must include relevant parts of ctree) ***)
				                if bytesestimate < !rembytesestimate then
					          begin
					            try
					              let c = octree_ctree (tx_octree_trans true false blkh (tauin,tauout) (Some(!dync))) in
					              otherstxs := (h,((tauin,tauout),sg))::!otherstxs;
					              othersout := !othersout @ tauout;
					              fees := Int64.sub !fees nfee;
					              dync := c;
					              rembytesestimate := !rembytesestimate - bytesestimate
					            with MaxAssetsAtAddress ->
                                                      counter := counter1
					          end
				                else
					          begin
					            log_string (Printf.sprintf "tx %s not being included because estimated block size would be too big (rembytesestimate %d, bytesestimate %d)\n" (hashval_hexstring h) !rembytesestimate bytesestimate);
					          end
                                            with _ -> counter := counter1
				          end
				        else
				          begin
                                            (*			      log_string (Printf.sprintf "tx %s has an invalid signature; removing from pool\n" (hashval_hexstring h)); *)
				            remove_from_txpool h;
				          end
			              with exn ->
				        begin
                                          (*			    log_string (Printf.sprintf "Exception %s raised while trying to validate tx %s; this may mean the tx is not yet supported so leaving it in the pool\n" (Printexc.to_string exn) (hashval_hexstring h)); *)
				        end
                                    end
			          else
			            begin
                                      (*			  log_string (Printf.sprintf "tx %s is invalid; removing from pool\n" (hashval_hexstring h)); *)
				      remove_from_txpool h;
			            end
			      in
			      let localbatchtxsfile = Filename.concat (datadir()) "localbatchtxs" in
			      if Sys.file_exists localbatchtxsfile then (*** if localbatchtxs file exists in the datadir, then first try to include these txs (in order) ***)
			        begin
			          let ch = open_in_bin localbatchtxsfile in
			          try
			            while true do
				      let (stau,_) = sei_stx seic (ch,None) in
				      let (tau,_) = stau in
				      try_to_incl_stx (hashtx tau) stau
			            done
			          with _ -> (try close_in_noerr ch with _ -> ())
			        end;
                              List.iter
                                (fun (h,stau) -> try_to_incl_stx h stau)
			        (sorted_stxpool());
			      let ostxs = !otherstxs in
			      let otherstxs = ref [] in (*** reverse them during this process so they will be evaluated in the intended order ***)
			      List.iter
			        (fun (h,stau) ->
			          remove_from_txpool h;
			          otherstxs := stau::!otherstxs)
			        ostxs;
			      let othertxs = List.map (fun (tau,_) -> tau) !otherstxs in
			      let alpha3 =
			        let default() =
			          let (i,x0,x1,x2,x3,x4) = alpha2 in
			          if i = 0 then
			            (x0,x1,x2,x3,x4)
			          else
			            begin
				      log_string (Printf.sprintf "Apparent attempt to stake from non-p2pkh address %s\n" (addr_pfgaddrstr alpha2));
				      raise StakingProblemPause
			            end
			        in
			        if !Config.offlinestakerewardsdest then
			          begin
			            match !Commands.walletwatchaddrs_offlinekey_fresh with
			            | alpha::wr ->
				       let (i,x0,x1,x2,x3,x4) = alpha in
				       if i = 0 then
				         begin
				           Commands.walletwatchaddrs_offlinekey := alpha::!Commands.walletwatchaddrs_offlinekey;
				           Commands.walletwatchaddrs_offlinekey_fresh := wr;
				           (x0,x1,x2,x3,x4)
				         end
				       else
				         default()
			            | _ ->
				       default()
			          end
			        else
			          begin
			            if !Config.generatenewrewardaddresses then
				      (let (_,alpha3) = Commands.generate_newkeyandaddress prevledgerroot (if !Config.stakewithrewards then "staking" else "nonstaking") in alpha3) (*** prevent staking address from ending up holding too many assets; max 32 are allowed ***)
			            else
				      default()
			          end
			      in
			      let alpha4 =
			        match !Config.offlinestakerewardslock with
			        | None ->
			           if !Config.offlinestakerewardsdest then
			             begin
				       match !Commands.walletwatchaddrs_offlinekey_fresh with
				       | alpha::wr ->
				          let (i,x0,x1,x2,x3,x4) = alpha in
				          if i = 0 || i = 1 then
				            begin
					      Commands.walletwatchaddrs_offlinekey := alpha::!Commands.walletwatchaddrs_offlinekey;
					      Commands.walletwatchaddrs_offlinekey_fresh := wr;
					      (i=1,x0,x1,x2,x3,x4)
				            end
				          else
				            p2pkhaddr_payaddr alpha3
				       | _ ->
				          p2pkhaddr_payaddr alpha3
			             end
			           else
			             p2pkhaddr_payaddr alpha3
			        | Some(x) ->
			           try
			             let (i,x0,x1,x2,x3,x4) = pfgaddrstr_addr x in
			             if i = 0 then
				       (false,x0,x1,x2,x3,x4) (*** p2pkh ***)
			             else if i = 1 then
				       (true,x0,x1,x2,x3,x4) (*** p2sh ***)
			             else
				       p2pkhaddr_payaddr alpha3
			           with _ -> p2pkhaddr_payaddr alpha3
			      in
                              let reward = rewfn blkh in
                              let reward2 = Int64.shift_right reward 1 in (** half reward goes to staker, half goes to bounty (or burned) **)
			      let stkoutl =
                                try
                                  if blkh >= late2020hardforkheight2 then raise Exit; (* no bounty *)
                                  if blkh >= late2020hardforkheight1 then
                                    let pthyaddr = hashval_p2pkh_addr csm0 in
                                    let (bfvcontraddr,_) = Script.bountyfundveto alpha in
                                    [(pthyaddr,(Some(p2shaddr_payaddr bfvcontraddr,0L,false),Currency(reward2)));(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                                  else
                                    let (_,_,p) = Checking.reward_bounty_prop blkh csm0 in
                                    let hfthyid = Checking.hfthyid in
                                    let ppureid = tm_hashroot p in
                                    let pthyid = hashtag (hashopair2 (Some(hfthyid)) ppureid) 33l in
                                    let pthyaddr = hashval_term_addr pthyid in
                                    [(pthyaddr,(None,Bounty(reward2)));(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                                with _ -> (** in case of exception, no bounty **)
                                  [(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                              in
			      let coinstk : tx = ([(alpha2,aid)],stkoutl) in
			      dync := octree_ctree (tx_octree_trans true false blkh coinstk (Some(!dync)));
			      let prevcforblock =
			        match
			          get_txl_supporting_octree (coinstk::othertxs) prevc
			        with
			        | Some(c) -> c
			        | None -> raise (Failure "ctree should not have become empty")
			      in
			      if not (ctree_hashroot (octree_ctree (tx_octree_trans false false blkh ([(alpha2,aid)],[]) (Some(prevcforblock)))) = prevledgerroot) then (* remove temporary asset and then check ledger root *)
			        begin
			          log_string (Printf.sprintf "prevcforblock has the wrong hash root. This should never happen.\n");
			          let s = Buffer.create 10000 in
			          seosbf (seo_option seo_ctree seosb prevc (s,None));
			          log_string (Printf.sprintf "prevc: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			          let s = Buffer.create 10000 in
			          seosbf (seo_ctree seosb prevcforblock (s,None));
			          log_string (Printf.sprintf "prevcforblock: %s\nprevledgerroot: %s\n" (Hashaux.string_hexstring (Buffer.contents s)) (hashval_hexstring prevledgerroot));
			          let s = Buffer.create 10000 in
			          seosbf (seo_list seo_tx seosb (coinstk::othertxs) (s,None));
			          log_string (Printf.sprintf "txs: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			          Hashtbl.remove nextstakechances (lbk,ltx);
			          raise StakingProblemPause;
			        end;
			      let (prevcforheader,cgr) = factor_inputs_ctree_cgraft [(alpha2,aid)] prevcforblock in
                              (* let newcr = save_ctree_atoms !dync in *) (* wait until after block is published to save atoms *)
                              let newcr = ctree_hashroot !dync in
                              (*		log_string (Printf.sprintf "finished saving ctree elements of dync\n"); *)
                              (*		    Hashtbl.add recentledgerroots newcr (blkh,newcr); *)
			      dyntht := txout_update_ottree !othersout !dyntht;
			      dynsigt := txout_update_ostree !othersout !dynsigt;
			      let newthtroot = ottree_hashroot !dyntht in
			      let newsigtroot = ostree_hashroot !dynsigt in
                              (*		log_string (Printf.sprintf "Including %d txs in block\n" (List.length !otherstxs)); *)
			      let bdnew : blockdelta =
			        { stakeoutput = stkoutl;
			          prevledgergraft = cgr;
			          blockdelta_stxl = !otherstxs
			        }
			      in
			      let bdnewroot = blockdelta_hashroot bdnew in
			      let bhdnew : blockheaderdata
			        = { prevblockhash = Some(pbhh1,Poburn(lbk,ltx,plmedtm,pburned,ptxid1,pvout1));
                                    pureburn = Some(txidh,Int32.of_int vout);
			            newtheoryroot = newthtroot;
			            newsignaroot = newsigtroot;
			            newledgerroot = newcr;
			            stakeaddr = alpha;
			            stakeassetid = aid;
			            timestamp = tm;
			            deltatime = deltm;
			            tinfo = tar;
			            prevledger = prevcforheader;
			            blockdeltaroot = bdnewroot;
			          }
			      in
			      let bhdnewh = hash_blockheaderdata bhdnew in
			      let bhsnew =
			        try
			          let (prvk,b,_,_,_,_) = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) !Commands.walletkeys_staking in
                                  let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
			          { blocksignat = sg;
			            blocksignatrecid = compute_recid sg r;
			            blocksignatfcomp = b;
			            blocksignatendorsement = None
			          }
			        with Not_found ->
			          try
			            let (_,beta,(w,z),recid,fcomp,esg) =
				      List.find
				        (fun (alpha2,beta,(w,z),recid,fcomp,esg) ->
				          let (p,x0,x1,x2,x3,x4) = alpha2 in
				          let (q,_,_,_,_,_) = beta in
				          not p && (x0,x1,x2,x3,x4) = alpha && not q)
				        !Commands.walletendorsements
			            in
			            let (_,x0,x1,x2,x3,x4) = beta in
			            let betah = (x0,x1,x2,x3,x4) in
			            let (prvk,b,_,_,_,_) =
				      try
				        List.find
				          (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				          !Commands.walletkeys_staking
				      with Not_found ->
				        List.find
				          (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				          !Commands.walletkeys_nonstaking
			            in
                                    let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
			            { blocksignat = sg;
				      blocksignatrecid = compute_recid sg r;
				      blocksignatfcomp = b;
				      blocksignatendorsement = Some(betah,recid,fcomp,esg)
			            }
			          with Not_found ->
			            raise (Failure("Was staking for " ^ Cryptocurr.addr_pfgaddrstr (p2pkhaddr_addr alpha) ^ " but have neither the private key nor an appropriate endorsement for it."))
			      in
			      let bhnew = (bhdnew,bhsnew) in
			      let newblkid = blockheader_id bhnew in
			      DbBlockHeader.dbput newblkid bhnew; (** save current block in local database **)
                              begin (* double check *)
                                let bhnew2 = DbBlockHeader.dbget newblkid in
                                if not (newblkid = blockheader_id bhnew2) then
                                  begin
                                    log_string (Printf.sprintf "Newly created header %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring newblkid));
                                    DbBlockHeader.dbdelete newblkid;
                                    DbBlockHeader.dbpurge ();
                                    raise StakingProblemPause
                                  end
                              end;
			      DbBlockDelta.dbput newblkid bdnew;
                              begin (* double check *)
                                let bdnew2 = DbBlockDelta.dbget newblkid in
                                if not (bdnewroot = blockdelta_hashroot bdnew2) then
                                  begin
                                    log_string (Printf.sprintf "Newly created delta %s was mangled in database.\nDeleting and purging.\n" (hashval_hexstring newblkid));
                                    DbBlockDelta.dbdelete newblkid;
                                    DbBlockDelta.dbpurge ();
                                    raise StakingProblemPause
                                  end
                              end;
			      List.iter
			        (fun stau -> DbSTx.dbput (hashstx stau) stau)
			        bdnew.blockdelta_stxl;
			      begin
			        let s = Buffer.create 10000 in
			        seosbf (seo_blockdelta seosb bdnew (s,None));
			        let bds = Buffer.length s in
			        if bds > maxblockdeltasize blkh then
			          (log_string (Printf.sprintf "New block is too big (%d bytes)\n" bds); raise Not_found); (** in this case, probably the best option would be to switch back to an empty block **)
			        if valid_blockheader_ifburn blkh csm0 tar0 bhnew tm toburn then
			          () (* (log_string (Printf.sprintf "New block header is valid\n")) *)
			        else
			          begin
			            let b = Buffer.create 1000 in
			            seosbf (seo_blockheader seosb bhnew (b,None));
			            log_string (Printf.sprintf "New block header is not valid\nbhnew = %s\nfull header = %s\n" (hashval_hexstring newblkid) (string_hexstring (Buffer.contents b)));
			            verbose_blockcheck := Some(!Utils.log);
			            ignore (valid_blockheader_ifburn blkh csm0 tar0 bhnew tm toburn);
			            verbose_blockcheck := None;
			            let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
			            dumpstate (Filename.concat datadir "stakedinvalidblockheaderstate");
			            Hashtbl.remove nextstakechances (lbk,ltx);
			            raise StakingProblemPause
			          end;
			        begin
			          match valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm toburn with
			          | Some(tht2,sigt2) ->
			             update_theories thyroot thytree tht2; (* locally update theories *)
			             update_signatures sigroot sigtree sigt2; (* locally update signatures *)
			             (** now that we have double checked validity, advertise the block to peers (before burning ltc) **)
			             advertise_new_block newblkid
			          | None ->
			             log_string (Printf.sprintf "New block is not valid\n");
			             begin
				       try
				         verbose_blockcheck := Some(!Utils.log); (* the next call is intended to log info about why the block is invalid *)
				         verbose_supportedcheck := Some(!Utils.log);
				         ignore (valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm toburn);
				         verbose_blockcheck := None;
				         verbose_supportedcheck := None;
				       with _ ->
				         verbose_blockcheck := None;
				         verbose_supportedcheck := None;
			             end;
			             let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in dumpstate (Filename.concat datadir "stakedinvalidblockstate");
				                                                                                                               Hashtbl.remove nextstakechances (lbk,ltx);
				                                                                                                               raise StakingProblemPause
			        end;
			        if blkh = 1L then (log_string (Printf.sprintf "Previous block indicated but block height is 1\n"); Hashtbl.remove nextstakechances (lbk,ltx); raise StakingProblemPause);
			        let (pbhd,pbhs) = get_blockheader pbhh1 in
			        let tmpsucctest bhd1 bhs1 bhd2 =
			          match bhd2.prevblockhash with
			          | Some(pbh,Poburn(lblkh,ltxh,lmedtm,burned,txid2,vout2)) ->
                                     blockheaderdata_burn_vin1_match bhd1 txid2 vout2
                                     &&
				       bhd2.timestamp = Int64.add bhd1.timestamp (Int64.of_int32 bhd2.deltatime)
			             &&
				       pbh = blockheader_id (bhd1,bhs1) (*** the next block must also commit to the previous signature ***)
			             &&
				       let tar1 = bhd1.tinfo in
				       let tar2 = bhd2.tinfo in
				       eq_big_int tar2 (retarget tar1 bhd2.deltatime)
			          | None -> false
			        in
			        if tmpsucctest pbhd pbhs bhdnew then
			          () (* (log_string (Printf.sprintf "Valid successor block\n")) *)
			        else
			          (log_string (Printf.sprintf "Not a valid successor block\n"); let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in dumpstate (Filename.concat datadir "stakedinvalidsuccblockstate"); Hashtbl.remove nextstakechances (lbk,ltx); raise StakingProblemPause)
			      end;
			      begin
			        try
			          while true do
			            let nw = ltc_medtime() in
			            let tmtopub = Int64.sub tm nw in
			            log_string (Printf.sprintf "tmtopub %Ld\n" tmtopub);
			            if tmtopub > 0L then Thread.delay (Int64.to_float tmtopub) else raise Exit
			          done
			        with Exit -> ()
			      end;
			      let publish_new_block_2 () =
			        log_string (Printf.sprintf "called publish_new_block_2\n");
			        let (pbh2,lbk2,ltx2) = get_bestblock_cw_exception (StakingPause(300.0)) in
			        if not ((pbh2,lbk2,ltx2) = (pbhh1,lbk,ltx)) then (*** if the best block has changed, don't publish it ***)
                                  begin log_string "best block changed, not publishing\n";
			                pendingpfgblock := None
                                  end
			        else
			          let hscnt = (try Hashtbl.find localnewheader_sent newblkid with Not_found -> -1) in
			          let dscnt = (try Hashtbl.find localnewdelta_sent newblkid with Not_found -> -1) in
			          if max hscnt dscnt < !Config.minconnstostake then
			            begin
				      log_string (Printf.sprintf "Delaying publication of block %s until it has been sent to %d peers (minconnstostake), currently header sent to %d peers and delta sent to %d peers.\n" (hashval_hexstring newblkid) !Config.minconnstostake hscnt dscnt);
				      broadcast_inv [(int_of_msgtype Headers,newblkid);(int_of_msgtype Blockdelta,newblkid)];
				      raise StakingPublishBlockPause
			            end
			          else
			            begin
                                      log_string "now publishing for real\n";
				      pendingpfgblock := None;
				      let ftm = Int64.add (ltc_medtime()) 3600L in
				      if tm <= ftm then
				        begin
				          begin
                                            let u = toburn in (*** actually burn u litoshis and wait for a confirmation to know the block hash ***)
				            try
					      if !Config.ltcoffline then
					        begin
					          Printf.printf "to stake, after ltc medtm passes %Ld create ltc burn tx for %s %s burning %Ld litoshis\n" tm (hashval_hexstring ltx) (hashval_hexstring newblkid) u
					        end
					      else
					        let btx = ltc_createburntx_spec lutxo ltx newblkid u in
					        let btxhex = Hashaux.string_hexstring btx in
					        let btxs = ltc_signrawtransaction btxhex in
					        let h = ltc_sendrawtransaction btxs in
					        pendingltctxs := h::!pendingltctxs;
					        log_string (Printf.sprintf "Sending ltc burn %s for header %s\n" h (hashval_hexstring newblkid));
					        publish_block blkh newblkid ((bhdnew,bhsnew),bdnew);
                                                Hashtbl.add unburned_headers newblkid (staking_local_process_header newblkid (bhdnew,bhsnew));
                                                Hashtbl.add unburned_deltas newblkid (staking_local_process_delta newblkid ((bhdnew,bhsnew),bdnew));
					        Hashtbl.add localpreferred newblkid ();
					        extraburn := 0L;
					        already := Some(newblkid,hexstring_hashval h);
					        pending := !already;
					        log_string ("Burning " ^ (Int64.to_string u) ^ " litoshis in tx " ^ h ^ "\n")
				            with
				            | InsufficientLtcFunds ->
					       log_string ("insufficient ltc to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
					       raise (StakingPause(300.0))
				            | Not_found ->
					       log_string ("problem trying to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
					       raise (StakingPause(300.0))
				          end
				        end			      
			            end
			      in
			      let publish_new_block () =
			        log_string (Printf.sprintf "called publish_new_block\n");
			        pendingpfgblock := Some(publish_new_block_2);
			        raise StakingPublishBlockPause
			      in
 			      let (pbh2,lbk2,ltx2) = get_bestblock_cw_exception (StakingPause(300.0)) in
			      if (pbh2,lbk2,ltx2) = (pbhh1,lbk,ltx) then (*** if the best block has changed, don't publish it ***)
			        publish_new_block()
			    with MaxAssetsAtAddress ->
			      log_string (Printf.sprintf "Refusing to stake since the coinstake tx would put too many assets in an address.\n")
		          end
                      end
                 end
	      | NextStake(tm,alpha,aid,bday,obl,v,toburn,already,thyroot,thytree,sigroot,sigtree) ->
	         begin
	           match !already with
	           | Some(_,_) -> raise SyncIssue
	           | None ->
		      begin
		        let nw = ltc_medtime() in
		        log_string (Printf.sprintf "NextStake tm = %Ld nw = %Ld\n" tm nw);
		        if tm >= Int64.add nw 60L || tm <= pbhtm then
		          begin (*** wait for a minute and then reevaluate; would be better to sleep until time to publish or until a new best block is found **)
			    let tmtopub = Int64.sub tm nw in
			    log_string ((Int64.to_string tmtopub) ^ " seconds until time to publish staked block\n");
			    if tmtopub >= 60L then
			      sleepuntil := Int64.add nw 60L
			    else
			      begin
			        sleepuntil := Int64.add nw tmtopub;
			      end
		          end
		        else
		          begin (** go ahead and form the block; then publish it at the right time **)
			    let deltm = Int64.to_int32 (Int64.sub tm pbhtm) in
			    let blkh = Int64.add 1L pblkh in
			    let tar = retarget tar0 deltm in
			    let alpha2 = p2pkhaddr_addr alpha in
			    log_string (Printf.sprintf "Forming new block at height %Ld with prevledgerroot %s, prev block %s and new stake addr %s stake aid %s (bday %Ld).\n" blkh (hashval_hexstring prevledgerroot) (hashval_hexstring pbhh1) (addr_pfgaddrstr alpha2) (hashval_hexstring aid) bday);
			    let obl2 =
			      match obl with
			      | None ->  (* if the staked asset had the default obligation it can be left as the default obligation or locked for some number of blocks to commit to staking; there should be a configurable policy for the node *)
			         None
                              (**
   Some(p2pkhaddr_payaddr alpha,Int64.add blkh (Int64.logand 2048L (rand_int64())),false) (* it is not marked as a reward *)
                               **)
			      | _ -> obl (* unless it's the default obligation, then the obligation cannot change when staking it *)
			    in
			    let prevc = Some(CHash(prevledgerroot)) in
			    let octree_ctree c =
			      match c with
			      | Some(c) -> c
			      | None -> raise (Failure "tree should not be empty")
			    in
			    let dync = ref (octree_ctree prevc) in
			    let dyntht = ref (lookup_thytree thtr) in (** The theory tree and signature tree change all at once at the end of processing the block **)
			    let dynsigt = ref (lookup_sigtree sgtr) in (** so these two do not really need to be refs. **)
			    let fees = ref 0L in
			    let otherstxs = ref [] in
			    let othersout = ref [] in
                            let counter = ref 0 in
			    let rembytesestimate = ref (maxblockdeltasize blkh - (2048 * 2)) in (*** estimate the remaining room in the block delta if the tx is added ***)
			    let try_to_incl_stx h stau =
			      let ((tauin,tauout) as tau,sg) = stau in
                              (*		    log_string (Printf.sprintf "Trying to include tx %s\n" (hashval_hexstring h)); *)
			      try
			        ignore (List.find (fun (_,h) -> h = aid) tauin);
                                (*		      log_string (Printf.sprintf "tx spends the staked asset; removing tx from pool\n"); *)
			        remove_from_txpool h
			      with Not_found ->
			        try
			          ignore (List.find (fun (alpha,_) -> alpha = alpha2) tauin) (*** Do not include txs that spend from the staking address, to avoid the ctree in the header not being minimal ***)
			        with Not_found ->
			          try
				    ignore (List.find (fun (alpha,_) -> alpha = alpha2) tauout) (*** Do not include txs that spend to the staking address, to avoid the possibility of ending up with too many assets at the staking address ***)
			          with Not_found ->
				    if tx_valid (tauin,tauout) then
				      try
				        let unsupportederror alpha h = log_string (Printf.sprintf "Could not find asset %s at address %s\n" (hashval_hexstring h) (addr_pfgaddrstr alpha)) in
				        let al = List.map (fun (aid,a) -> a) (ctree_lookup_input_assets true true false tauin !dync unsupportederror) in
				        if tx_signatures_valid blkh tm al ((tauin,tauout),sg) then
				          begin
                                            let counter1 = !counter in
                                            try
					      let nfee = ctree_supports_tx counter true true false !dyntht !dynsigt blkh (tauin,tauout) !dync in
					      if nfee > 0L then (*** note: nfee is negative of the fee, not the fee itself ***)
					        begin
                                                  (*				  log_string (Printf.sprintf "tx %s has negative fees %Ld; removing from pool\n" (hashval_hexstring h) nfee); *)
					          remove_from_txpool h;
					        end
					      else
                                                let realsize = stxsize stau in
					        let bytesestimate = realsize + 1024 * List.length tauin + 1024 * List.length tauout in (*** extra 1K per input and output (since must include relevant parts of ctree) ***)
					        if bytesestimate < !rembytesestimate then
					          begin
					            try
						      let c = octree_ctree (tx_octree_trans true false blkh (tauin,tauout) (Some(!dync))) in
						      otherstxs := (h,((tauin,tauout),sg))::!otherstxs;
						      othersout := !othersout @ tauout;
						      fees := Int64.sub !fees nfee;
						      dync := c;
						      rembytesestimate := !rembytesestimate - bytesestimate
					            with MaxAssetsAtAddress ->
                                                      counter := counter1
					          end
					        else
					          begin
					            log_string (Printf.sprintf "tx %s not being included because estimated block size would be too big (rembytesestimate %d, bytesestimate %d)\n" (hashval_hexstring h) !rembytesestimate bytesestimate);
					          end
                                            with _ -> counter := counter1
				          end
				        else
				          begin
                                            (*			      log_string (Printf.sprintf "tx %s has an invalid signature; removing from pool\n" (hashval_hexstring h)); *)
					    remove_from_txpool h;
				          end
				      with exn ->
				        begin
                                          (*			    log_string (Printf.sprintf "Exception %s raised while trying to validate tx %s; this may mean the tx is not yet supported so leaving it in the pool\n" (Printexc.to_string exn) (hashval_hexstring h)); *)
				        end
				    else
				      begin
                                        (*			  log_string (Printf.sprintf "tx %s is invalid; removing from pool\n" (hashval_hexstring h)); *)
				        remove_from_txpool h;
				      end
			    in
			    let localbatchtxsfile = Filename.concat (datadir()) "localbatchtxs" in
			    if Sys.file_exists localbatchtxsfile then (*** if localbatchtxs file exists in the datadir, then first try to include these txs (in order) ***)
			      begin
			        let ch = open_in_bin localbatchtxsfile in
			        try
			          while true do
				    let (stau,_) = sei_stx seic (ch,None) in
				    let (tau,_) = stau in
				    try_to_incl_stx (hashtx tau) stau
			          done
			        with _ -> (try close_in_noerr ch with _ -> ())
			      end;
			    Hashtbl.iter
			      (fun h stau -> try_to_incl_stx h stau)
			      stxpool;
			    let ostxs = !otherstxs in
			    let otherstxs = ref [] in (*** reverse them during this process so they will be evaluated in the intended order ***)
			    List.iter
			      (fun (h,stau) ->
			        remove_from_txpool h;
			        otherstxs := stau::!otherstxs)
			      ostxs;
			    let othertxs = List.map (fun (tau,_) -> tau) !otherstxs in
			    let alpha3 =
			      let default() =
			        let (i,x0,x1,x2,x3,x4) = alpha2 in
			        if i = 0 then
			          (x0,x1,x2,x3,x4)
			        else
			          begin
				    log_string (Printf.sprintf "Apparent attempt to stake from non-p2pkh address %s\n" (addr_pfgaddrstr alpha2));
				    raise StakingProblemPause
			          end
			      in
			      if !Config.offlinestakerewardsdest then
			        begin
			          match !Commands.walletwatchaddrs_offlinekey_fresh with
			          | alpha::wr ->
				     let (i,x0,x1,x2,x3,x4) = alpha in
				     if i = 0 then
				       begin
				         Commands.walletwatchaddrs_offlinekey := alpha::!Commands.walletwatchaddrs_offlinekey;
				         Commands.walletwatchaddrs_offlinekey_fresh := wr;
				         (x0,x1,x2,x3,x4)
				       end
				     else
				       default()
			          | _ ->
				     default()
			        end
			      else
			        begin
			          if !Config.generatenewrewardaddresses then
				    (let (_,alpha3) = Commands.generate_newkeyandaddress prevledgerroot (if !Config.stakewithrewards then "staking" else "nonstaking") in alpha3) (*** prevent staking address from ending up holding too many assets; max 32 are allowed ***)
			          else
				    default()
			        end
			    in
			    let alpha4 =
			      match !Config.offlinestakerewardslock with
			      | None ->
			         if !Config.offlinestakerewardsdest then
			           begin
				     match !Commands.walletwatchaddrs_offlinekey_fresh with
				     | alpha::wr ->
				        let (i,x0,x1,x2,x3,x4) = alpha in
				        if i = 0 || i = 1 then
				          begin
					    Commands.walletwatchaddrs_offlinekey := alpha::!Commands.walletwatchaddrs_offlinekey;
					    Commands.walletwatchaddrs_offlinekey_fresh := wr;
					    (i=1,x0,x1,x2,x3,x4)
				          end
				        else
				          p2pkhaddr_payaddr alpha3
				     | _ ->
				        p2pkhaddr_payaddr alpha3
			           end
			         else
			           p2pkhaddr_payaddr alpha3
			      | Some(x) ->
			         try
			           let (i,x0,x1,x2,x3,x4) = pfgaddrstr_addr x in
			           if i = 0 then
				     (false,x0,x1,x2,x3,x4) (*** p2pkh ***)
			           else if i = 1 then
				     (true,x0,x1,x2,x3,x4) (*** p2sh ***)
			           else
				     p2pkhaddr_payaddr alpha3
			         with _ -> p2pkhaddr_payaddr alpha3
			    in
                            let reward = rewfn blkh in
                            let reward2 = Int64.shift_right reward 1 in (** half reward goes to staker and other half goes to bounty (or burned) **)
			    let stkoutl =
                              try
                                if blkh >= late2020hardforkheight2 then raise Exit; (* no bounty *)
                                if blkh >= late2020hardforkheight1 then
                                  let pthyaddr = hashval_p2pkh_addr csm0 in
                                  let (bfvcontraddr,_) = Script.bountyfundveto alpha in
                                  [(alpha2,(obl2,Currency(v)));(pthyaddr,(Some(p2shaddr_payaddr bfvcontraddr,0L,false),Currency(reward2)));(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                                else
                                  let (_,_,p) = Checking.reward_bounty_prop blkh csm0 in
                                  let hfthyid = Checking.hfthyid in
                                  let ppureid = tm_hashroot p in
                                  let pthyid = hashtag (hashopair2 (Some(hfthyid)) ppureid) 33l in
                                  let pthyaddr = hashval_term_addr pthyid in
                                  [(alpha2,(obl2,Currency(v)));(pthyaddr,(None,Bounty(reward2)));(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                              with _ -> (** in case of exception, no bounty **)
                                [(alpha2,(obl2,Currency(v)));(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))]
                            in
			    let coinstk : tx = ([(alpha2,aid)],stkoutl) in
			    try
			      dync := octree_ctree (tx_octree_trans true false blkh coinstk (Some(!dync)));
			      let prevcforblock =
			        match
			          get_txl_supporting_octree (coinstk::othertxs) prevc
			        with
			        | Some(c) -> c
			        | None -> raise (Failure "ctree should not have become empty")
			      in
			      if not (ctree_hashroot prevcforblock = prevledgerroot) then
			        begin
			          log_string (Printf.sprintf "prevcforblock has the wrong hash root. This should never happen.\n");
			          let s = Buffer.create 10000 in
			          seosbf (seo_option seo_ctree seosb prevc (s,None));
			          log_string (Printf.sprintf "prevc: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			          let s = Buffer.create 10000 in
			          seosbf (seo_ctree seosb prevcforblock (s,None));
			          log_string (Printf.sprintf "prevcforblock: %s\nprevledgerroot: %s\n" (Hashaux.string_hexstring (Buffer.contents s)) (hashval_hexstring prevledgerroot));
			          let s = Buffer.create 10000 in
			          seosbf (seo_list seo_tx seosb (coinstk::othertxs) (s,None));
			          log_string (Printf.sprintf "txs: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			          Hashtbl.remove nextstakechances (lbk,ltx);
			          raise StakingProblemPause;
			        end;
			      let (prevcforheader,cgr) = factor_inputs_ctree_cgraft [(alpha2,aid)] prevcforblock in
			      (* let newcr = save_ctree_atoms !dync in *) (* wait until after block is published to save atoms *)
                              let newcr = ctree_hashroot !dync in
                              (*		log_string (Printf.sprintf "finished saving ctree elements of dync\n"); *)
                              (*		    Hashtbl.add recentledgerroots newcr (blkh,newcr); *)
			      dyntht := txout_update_ottree !othersout !dyntht;
			      dynsigt := txout_update_ostree !othersout !dynsigt;
			      let newthtroot = ottree_hashroot !dyntht in
			      let newsigtroot = ostree_hashroot !dynsigt in
                              (*		log_string (Printf.sprintf "Including %d txs in block\n" (List.length !otherstxs)); *)
			      let bdnew : blockdelta =
			        { stakeoutput = stkoutl;
			          prevledgergraft = cgr;
			          blockdelta_stxl = !otherstxs
			        }
			      in
			      let bdnewroot = blockdelta_hashroot bdnew in
			      let bhdnew : blockheaderdata
			        = { prevblockhash = Some(pbhh1,Poburn(lbk,ltx,plmedtm,pburned,ptxid1,pvout1));
                                    pureburn = None;
				    newtheoryroot = newthtroot;
				    newsignaroot = newsigtroot;
				    newledgerroot = newcr;
				    stakeaddr = alpha;
				    stakeassetid = aid;
				    timestamp = tm;
				    deltatime = deltm;
				    tinfo = tar;
				    prevledger = prevcforheader;
				    blockdeltaroot = bdnewroot;
			          }
			      in
			      let bhdnewh = hash_blockheaderdata bhdnew in
			      let bhsnew =
			        try
			          let (prvk,b,_,_,_,_) = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) !Commands.walletkeys_staking in
                                  let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
			          { blocksignat = sg;
				    blocksignatrecid = compute_recid sg r;
				    blocksignatfcomp = b;
				    blocksignatendorsement = None
			          }
			        with Not_found ->
			          try
				    let (_,beta,(w,z),recid,fcomp,esg) =
				      List.find
				        (fun (alpha2,beta,(w,z),recid,fcomp,esg) ->
				          let (p,x0,x1,x2,x3,x4) = alpha2 in
				          let (q,_,_,_,_,_) = beta in
				          not p && (x0,x1,x2,x3,x4) = alpha && not q)
				        !Commands.walletendorsements
				    in
				    let (_,x0,x1,x2,x3,x4) = beta in
				    let betah = (x0,x1,x2,x3,x4) in
				    let (prvk,b,_,_,_,_) =
				      try
				        List.find
				          (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				          !Commands.walletkeys_staking
				      with Not_found ->
				        List.find
				          (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				          !Commands.walletkeys_nonstaking
				    in
                                    let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
				    { blocksignat = sg;
				      blocksignatrecid = compute_recid sg r;
				      blocksignatfcomp = b;
				      blocksignatendorsement = Some(betah,recid,fcomp,esg)
				    }
			          with Not_found ->
				    raise (Failure("Was staking for " ^ Cryptocurr.addr_pfgaddrstr (p2pkhaddr_addr alpha) ^ " but have neither the private key nor an appropriate endorsement for it."))
			      in
			      let bhnew = (bhdnew,bhsnew) in
			      let newblkid = blockheader_id bhnew in
			      DbBlockHeader.dbput newblkid bhnew; (** save current block in local database **)
			      DbBlockDelta.dbput newblkid bdnew;
			      List.iter
			        (fun stau -> DbSTx.dbput (hashstx stau) stau)
			        bdnew.blockdelta_stxl;
			      begin
			        let s = Buffer.create 10000 in
			        seosbf (seo_blockdelta seosb bdnew (s,None));
			        let bds = Buffer.length s in
			        if bds > maxblockdeltasize blkh then
			          (log_string (Printf.sprintf "New block is too big (%d bytes)\n" bds); raise Not_found); (** in this case, probably the best option would be to switch back to an empty block **)
			        if valid_blockheader_ifburn blkh csm0 tar0 bhnew tm (match toburn with Some(burn) -> burn | _ -> 0L) then
			          () (* (log_string (Printf.sprintf "New block header is valid\n")) *)
			        else
			          begin
				    let b = Buffer.create 1000 in
				    seosbf (seo_blockheader seosb bhnew (b,None));
				    log_string (Printf.sprintf "New block header is not valid\nbhnew = %s\nfull header = %s\n" (hashval_hexstring newblkid) (string_hexstring (Buffer.contents b)));
				    verbose_blockcheck := Some(!Utils.log);
				    ignore (valid_blockheader_ifburn blkh csm0 tar0 bhnew tm (match toburn with Some(burn) -> burn | _ -> 0L));
				    verbose_blockcheck := None;
				    let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
				    dumpstate (Filename.concat datadir "stakedinvalidblockheaderstate");
				    Hashtbl.remove nextstakechances (lbk,ltx);
				    raise StakingProblemPause
			          end;
			        begin
			          match valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm (match toburn with Some(burn) -> burn | _ -> 0L) with
			          | Some(tht2,sigt2) ->
				     update_theories thyroot thytree tht2; (* locally update theories *)
				     update_signatures sigroot sigtree sigt2; (* locally update signatures *)
				     (** now that we have double checked validity, advertise the block to peers (before burning ltc) **)
				     advertise_new_block newblkid
			          | None ->
				     log_string (Printf.sprintf "New block is not valid\n");
				     begin
				       try
				         verbose_blockcheck := Some(!Utils.log); (* the next call is intended to log info about why the block is invalid *)
				         verbose_supportedcheck := Some(!Utils.log);
				         ignore (valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm (match toburn with Some(burn) -> burn | _ -> 0L));
				         verbose_blockcheck := None;
				         verbose_supportedcheck := None;
				       with _ ->
				         verbose_blockcheck := None;
				         verbose_supportedcheck := None;
				     end;
				     let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in dumpstate (Filename.concat datadir "stakedinvalidblockstate");
				                                                                                                               Hashtbl.remove nextstakechances (lbk,ltx);
				                                                                                                               raise StakingProblemPause
			        end;
			        if blkh = 1L then (log_string (Printf.sprintf "Previous block indicated but block height is 1\n"); Hashtbl.remove nextstakechances (lbk,ltx); raise StakingProblemPause);
			        let (pbhd,pbhs) = get_blockheader pbhh1 in
			        let tmpsucctest bhd1 bhs1 bhd2 =
			          match bhd2.prevblockhash with
			          | Some(pbh,Poburn(lblkh,ltxh,lmedtm,burned,txid2,vout2)) ->
                                     blockheaderdata_burn_vin1_match bhd1 txid2 vout2
				     &&
                                       bhd2.timestamp = Int64.add bhd1.timestamp (Int64.of_int32 bhd2.deltatime)
				     &&
				       pbh = blockheader_id (bhd1,bhs1) (*** the next block must also commit to the previous signature ***)
				     &&
				       let tar1 = bhd1.tinfo in
				       let tar2 = bhd2.tinfo in
				       eq_big_int tar2 (retarget tar1 bhd2.deltatime)
			          | None -> false
			        in
			        if tmpsucctest pbhd pbhs bhdnew then
			          () (* (log_string (Printf.sprintf "Valid successor block\n")) *)
			        else
			          (log_string (Printf.sprintf "Not a valid successor block\n"); let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in dumpstate (Filename.concat datadir "stakedinvalidsuccblockstate"); Hashtbl.remove nextstakechances (lbk,ltx); raise StakingProblemPause)
			      end;
			      begin
			        try
			          while true do
				    let nw = ltc_medtime() in
				    let tmtopub = Int64.sub tm nw in
				    log_string (Printf.sprintf "tmtopub %Ld\n" tmtopub);
				    if tmtopub > 0L then Thread.delay (Int64.to_float tmtopub) else raise Exit
			          done
			        with Exit -> ()
			      end;
			      let publish_new_block_2 () =
			        log_string (Printf.sprintf "called publish_new_block_2\n");
			        let (pbh2,lbk2,ltx2) = get_bestblock_cw_exception (StakingPause(300.0)) in
			        if not ((pbh2,lbk2,ltx2) = (pbhh1,lbk,ltx)) then (*** if the best block has changed, don't publish it ***)
                                  begin log_string "best block changed, not publishing\n";
			                pendingpfgblock := None
                                  end
			        else
			          let hscnt = (try Hashtbl.find localnewheader_sent newblkid with Not_found -> -1) in
			          let dscnt = (try Hashtbl.find localnewdelta_sent newblkid with Not_found -> -1) in
			          if max hscnt dscnt < !Config.minconnstostake then
				    begin
				      log_string (Printf.sprintf "Delaying publication of block %s until it has been sent to %d peers (minconnstostake), currently header sent to %d peers and delta sent to %d peers.\n" (hashval_hexstring newblkid) !Config.minconnstostake hscnt dscnt);
				      broadcast_inv [(int_of_msgtype Headers,newblkid);(int_of_msgtype Blockdelta,newblkid)];
				      raise StakingPublishBlockPause
				    end
			          else
				    begin
                                      log_string "now publishing for real\n";
				      pendingpfgblock := None;
				      let ftm = Int64.add (ltc_medtime()) 3600L in
				      if tm <= ftm then
				        begin
				          begin
					    match toburn with
					    | Some(u) ->
					       begin (*** actually burn u litoshis and wait for a confirmation to know the block hash ***)
					         try
					           if !Config.ltcoffline then
						     begin
						       Printf.printf "to stake, after ltc medtm passes %Ld create ltc burn tx for %s %s burning %Ld litoshis\n" tm (hashval_hexstring ltx) (hashval_hexstring newblkid) u
						     end
					           else
						     let btx = ltc_createburntx ltx newblkid u in
						     let btxhex = Hashaux.string_hexstring btx in
						     let btxs = ltc_signrawtransaction btxhex in
						     let h = ltc_sendrawtransaction btxs in
						     pendingltctxs := h::!pendingltctxs;
						     log_string (Printf.sprintf "Sending ltc burn %s for header %s\n" h (hashval_hexstring newblkid));
						     publish_block blkh newblkid ((bhdnew,bhsnew),bdnew);
                                                     Hashtbl.add unburned_headers newblkid (staking_local_process_header newblkid (bhdnew,bhsnew));
                                                     Hashtbl.add unburned_deltas newblkid (staking_local_process_delta newblkid ((bhdnew,bhsnew),bdnew));
						     Hashtbl.add localpreferred newblkid ();
						     extraburn := 0L;
						     already := Some(newblkid,hexstring_hashval h);
						     pending := !already;
						     log_string ("Burning " ^ (Int64.to_string u) ^ " litoshis in tx " ^ h ^ "\n")
					         with
					         | InsufficientLtcFunds ->
						    log_string ("insufficient ltc to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
						    raise (StakingPause(300.0))
					         | Not_found ->
						    log_string ("problem trying to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
						    raise (StakingPause(300.0))
					       end
					    | None -> raise (Failure("must burn, should have known"))
				          end
				        end			      
				    end
			      in
			      let publish_new_block () =
			        log_string (Printf.sprintf "called publish_new_block\n");
			        pendingpfgblock := Some(publish_new_block_2);
			        raise StakingPublishBlockPause
			      in
 			      let (pbh2,lbk2,ltx2) = get_bestblock_cw_exception (StakingPause(300.0)) in
			      if (pbh2,lbk2,ltx2) = (pbhh1,lbk,ltx) then (*** if the best block has changed, don't publish it ***)
			        publish_new_block()
			    with MaxAssetsAtAddress ->
			      log_string (Printf.sprintf "Refusing to stake since the coinstake tx would put too many assets in an address.\n")
		          end
		      end
	         end
	      | NoStakeUpTo(tm) ->
	         begin (*** before checking for future chances to stake, make sure we are clearly at one of the best chaintips ***)
	           match ltc_best_chaintips () with
	           | [] ->
		      begin
		        (*** this should not have happened, since the header should not have been completely formed until the burn was complete ***)
		        log_string (Printf.sprintf "Refusing to stake on top of apparently unburned %s\nWaiting a few minutes to recheck for burn." (hashval_hexstring pbhh1));
		        raise (StakingPause(300.0))
		      end
	           | (bestctips::othctipsl) ->
		      begin
		        if List.mem pbhh1 bestctips then
		          (if List.length bestctips > 1 then (log_string (Printf.sprintf "Staking on top of %s, orphaning other equally good tips.\n" (hashval_hexstring pbhh1))))
		        else
		          begin
			    log_string (Printf.sprintf "Refusing to stake on top of %s when there are better chaintips. Invalidate them by hand to force staking.\n" (hashval_hexstring pbhh1));
			    raise (StakingPause(3600.0))
		          end
		      end
	         end;
	         let ltm = ltc_medtime() in
	         let stm = Int64.sub ltm 14400L in
	         let ftm = Int64.add ltm 14400L in
	         if tm < ftm && Int64.of_float (Unix.time()) < ftm then
	           begin
		     try
		   let (dbh,_,_,_,_,_,_) = Db_outlinevals.dbget (hashpair lbk ltx) in
		   compute_staking_chances (dbh,lbk,ltx) (if tm > stm then tm else stm) ftm
		     with Not_found -> Thread.delay 60.0
	           end
	         else
	           Thread.delay 60.0
            end
          else
            raise Not_found
        with
        | Not_found ->
	   log_string (Printf.sprintf "no nextstakechances\n");
	   Thread.delay 10.0;
	   log_string (Printf.sprintf "calling compute_staking_chances nextstakechances\n");
	   let ltm = ltc_medtime() in
	   let ftm = Int64.add ltm 14400L in
	   try
	     let (_,pbhtm,_,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	     compute_staking_chances (pbhh1,lbk,ltx) pbhtm ftm
	   with
           | Not_found -> Thread.delay 120.0
           | StakingProblemPause -> (*** there was some serious staking bug, try to recover by stopping staking for 10 minutes and trying again ***)
	      log_string (Printf.sprintf "Pausing due to a staking bug; will retry staking in about 10 minutes.\n");
	      Thread.delay 600.0;
	      log_string (Printf.sprintf "Continuing staking.\n");
	      let ltm = ltc_medtime() in
	      let stm = Int64.sub ltm 14400L in
	      let ftm = Int64.add ltm 14400L in
	      compute_staking_chances (pbhh1,lbk,ltx) stm ftm
      with
      | Genesis -> (*** genesis phase ***)
         begin
           log_string (Printf.sprintf "Trying to create genesis block.\n");
	   let nw = ltc_medtime() in
	   let upto = Int64.add 14400L nw in
           let alpha =
             (let (_,alpha3) = Commands.generate_newkeyandaddress !genesisledgerroot "staking" in alpha3) (*** prevent staking address from ending up holding too many assets; max 32 are allowed ***)
           in
           let alpha2 = p2pkhaddr_addr alpha in
           log_string (Printf.sprintf "alpha = %s\n" (addr_pfgaddrstr alpha2));
	   let csm0 = !genesisstakemod in
	   let tar0 = !genesistarget in
	   begin
	     try
               compute_genesis_staking_chances !Config.genesistimestamp upto;
               match !genesisstakechances with
               | Some(NextPureBurn(tm,lutxo,txidh,vout,toburn64,already,thyroot,thytree,sigroot,sigtree)) ->
                  begin
	            match !already with
	            | Some(_,_) -> raise SyncIssue
	            | None ->
		       begin
		         let nw = ltc_medtime() in
	                 log_string (Printf.sprintf "NextPureBurn tm = %Ld nw = %Ld\n" tm nw);
                         let pbhtm = !Config.genesistimestamp in
                         let prevledgerroot = !genesisledgerroot in
		         if tm >= Int64.add nw 60L || tm <= pbhtm then
		           begin (*** wait for a minute and then reevaluate; would be better to sleep until time to publish or until a new best block is found **)
			     let tmtopub = Int64.sub tm nw in
			     log_string ((Int64.to_string tmtopub) ^ " seconds until time to publish staked block\n");
			     if tmtopub >= 60L then
			       sleepuntil := Int64.add nw 60L
			     else
			       begin
			         sleepuntil := Int64.add nw tmtopub;
			       end
		           end
		         else
		           begin (** go ahead and form the block; then publish it at the right time **)
			     let deltm = Int64.to_int32 (Int64.sub tm pbhtm) in
			     let blkh = 1L in
			     let tar = retarget tar0 deltm in
                             let aid = hashtag txidh (Int32.of_int vout) in
                             let a = (aid,0L,None,Currency(0L)) in
                             let prevc = tx_octree_trans_ true false 162 [] [(addr_bitseq alpha2,a)] (Some(CHash(prevledgerroot))) in
			     let octree_ctree c =
			       match c with
			       | Some(c) -> c
			       | None -> raise (Failure "tree should not be empty")
			     in
			     let dync = ref (octree_ctree prevc) in
                             let sgtr = None in
			     let dyntht = ref (Some (Checking.initthytree)) in (** The theory tree and signature tree change all at once at the end of processing the block **)
			     let dynsigt = ref (lookup_sigtree sgtr) in (** so these two do not really need to be refs. **)
			     let fees = ref 0L in
			     let otherstxs = ref [] in
			     let othersout = ref [] in
			     let othertxs = [] in
			     let alpha3 = alpha in
			     let alpha4 = p2pkhaddr_payaddr alpha3 in
                             let reward = rewfn blkh in
                             let reward2 = Int64.shift_right reward 1 in (** half reward goes to staker (burner here); no bounty in genesis block, so other half is burned **)
			     let stkoutl = [(p2pkhaddr_addr alpha3,(Some(alpha4,get_reward_locktime blkh,true),Currency(Int64.add !fees reward2)))] in
			     let coinstk : tx = ([(alpha2,aid)],stkoutl) in
                             try
			       dync := octree_ctree (tx_octree_trans true false blkh coinstk (Some(!dync)));
			       let prevcforblock =
			         match
			           get_tx_supporting_octree coinstk prevc
			         with
			         | Some(c) -> c
			         | None -> raise (Failure "ctree should not have become empty")
			       in
			       if not (ctree_hashroot (octree_ctree (tx_octree_trans false false blkh ([(alpha2,aid)],[]) (Some(prevcforblock)))) = prevledgerroot) then (* remove temporary asset and then check ledger root *)
			         begin
			           log_string (Printf.sprintf "prevcforblock has the wrong hash root. This should never happen.\n");
			           let s = Buffer.create 10000 in
			           seosbf (seo_option seo_ctree seosb prevc (s,None));
			           log_string (Printf.sprintf "prevc: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			           let s = Buffer.create 10000 in
			           seosbf (seo_ctree seosb prevcforblock (s,None));
			           log_string (Printf.sprintf "prevcforblock: %s\nprevledgerroot: %s\n" (Hashaux.string_hexstring (Buffer.contents s)) (hashval_hexstring prevledgerroot));
			           let s = Buffer.create 10000 in
			           seosbf (seo_list seo_tx seosb (coinstk::othertxs) (s,None));
			           log_string (Printf.sprintf "txs: %s\n" (Hashaux.string_hexstring (Buffer.contents s)));
			           raise StakingProblemPause;
			         end;
			       let (prevcforheader,cgr) = factor_inputs_ctree_cgraft [(alpha2,aid)] prevcforblock in
			       (* let newcr = save_ctree_atoms !dync in *) (* wait until after block is published to save atoms *)
                               let newcr = ctree_hashroot !dync in
                               (*		log_string (Printf.sprintf "finished saving ctree elements of dync\n"); *)
                               (*		    Hashtbl.add recentledgerroots newcr (blkh,newcr); *)
			       dyntht := txout_update_ottree !othersout !dyntht;
			       dynsigt := txout_update_ostree !othersout !dynsigt;
			       let newthtroot = ottree_hashroot !dyntht in
			       let newsigtroot = ostree_hashroot !dynsigt in
                               (*		log_string (Printf.sprintf "Including %d txs in block\n" (List.length !otherstxs)); *)
			       let bdnew : blockdelta =
			         { stakeoutput = stkoutl;
			           prevledgergraft = cgr;
			           blockdelta_stxl = !otherstxs
			         }
			       in
			       let bdnewroot = blockdelta_hashroot bdnew in
			       let bhdnew : blockheaderdata
			         = { prevblockhash = None;
                                     pureburn = Some(txidh,Int32.of_int vout);
				     newtheoryroot = newthtroot;
				     newsignaroot = newsigtroot;
				     newledgerroot = newcr;
				     stakeaddr = alpha;
				     stakeassetid = aid;
				     timestamp = tm;
				     deltatime = deltm;
				     tinfo = tar;
				     prevledger = prevcforheader;
				     blockdeltaroot = bdnewroot;
			           }
			       in
			       let bhdnewh = hash_blockheaderdata bhdnew in
			       let bhsnew =
			         try
			           let (prvk,b,_,_,_,_) = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) !Commands.walletkeys_staking in
                                   let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
			           { blocksignat = sg;
				     blocksignatrecid = compute_recid sg r;
				     blocksignatfcomp = b;
				     blocksignatendorsement = None
			           }
			         with Not_found ->
			           try
				     let (_,beta,(w,z),recid,fcomp,esg) =
				       List.find
				         (fun (alpha2,beta,(w,z),recid,fcomp,esg) ->
				           let (p,x0,x1,x2,x3,x4) = alpha2 in
				           let (q,_,_,_,_,_) = beta in
				           not p && (x0,x1,x2,x3,x4) = alpha && not q)
				         !Commands.walletendorsements
				     in
				     let (_,x0,x1,x2,x3,x4) = beta in
				     let betah = (x0,x1,x2,x3,x4) in
				     let (prvk,b,_,_,_,_) =
				       try
				         List.find
				           (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				           !Commands.walletkeys_staking
				       with Not_found ->
				         List.find
				           (fun (_,_,_,_,beta2,_) -> beta2 = betah)
				           !Commands.walletkeys_nonstaking
				     in
                                     let (r,sg) = repeat_rand (signat_hashval bhdnewh prvk) rand_256 in
				     { blocksignat = sg;
				       blocksignatrecid = compute_recid sg r;
				       blocksignatfcomp = b;
				       blocksignatendorsement = Some(betah,recid,fcomp,esg)
				     }
			           with Not_found ->
				     raise (Failure("Was staking for " ^ Cryptocurr.addr_pfgaddrstr (p2pkhaddr_addr alpha) ^ " but have neither the private key nor an appropriate endorsement for it."))
			       in
			       let bhnew = (bhdnew,bhsnew) in
			       let newblkid = blockheader_id bhnew in
			       DbBlockHeader.dbput newblkid bhnew; (** save current block in local database **)
			       DbBlockDelta.dbput newblkid bdnew;
			       List.iter
			         (fun stau -> DbSTx.dbput (hashstx stau) stau)
			         bdnew.blockdelta_stxl;
			       begin
			         let s = Buffer.create 10000 in
			         seosbf (seo_blockdelta seosb bdnew (s,None));
			         let bds = Buffer.length s in
			         if bds > maxblockdeltasize blkh then
			           (log_string (Printf.sprintf "New block is too big (%d bytes)\n" bds); raise Not_found); (** in this case, probably the best option would be to switch back to an empty block **)
			         if valid_blockheader_ifburn blkh csm0 tar0 bhnew tm toburn64 then
			           () (* (log_string (Printf.sprintf "New block header is valid\n")) *)
			         else
			           begin
				     let b = Buffer.create 1000 in
				     seosbf (seo_blockheader seosb bhnew (b,None));
				     log_string (Printf.sprintf "New block header is not valid\nbhnew = %s\nfull header = %s\n" (hashval_hexstring newblkid) (string_hexstring (Buffer.contents b)));
				     verbose_blockcheck := Some(!Utils.log);
				     ignore (valid_blockheader_ifburn blkh csm0 tar0 bhnew tm toburn64);
				     verbose_blockcheck := None;
				     let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
				     dumpstate (Filename.concat datadir "stakedinvalidblockheaderstate");
				     raise StakingProblemPause
			           end;
			         begin
			           match valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm toburn64 with
			           | Some(tht2,sigt2) ->
				      update_theories thyroot thytree tht2; (* locally update theories *)
				      update_signatures sigroot sigtree sigt2; (* locally update signatures *)
				      (** now that we have double checked validity, advertise the block to peers (before burning ltc) **)
				      advertise_new_block newblkid
			           | None ->
				      log_string (Printf.sprintf "New block is not valid\n");
				      begin
				        try
				          verbose_blockcheck := Some(!Utils.log); (* the next call is intended to log info about why the block is invalid *)
				          verbose_supportedcheck := Some(!Utils.log);
				          ignore (valid_block_ifburn thytree sigtree blkh csm0 tar0 (bhnew,bdnew) tm toburn64);
				          verbose_blockcheck := None;
				          verbose_supportedcheck := None;
				        with _ ->
				          verbose_blockcheck := None;
				          verbose_supportedcheck := None;
				      end;
				      let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in dumpstate (Filename.concat datadir "stakedinvalidblockstate");
				                                                                                                                raise StakingProblemPause
			         end;
			       end;
			       begin
			         try
			           while true do
				     let nw = ltc_medtime() in
				     let tmtopub = Int64.sub tm nw in
				     log_string (Printf.sprintf "tmtopub %Ld\n" tmtopub);
				     if tmtopub > 0L then Thread.delay (Int64.to_float tmtopub) else raise Exit
			           done
			         with Exit -> ()
			       end;
			       let publish_new_block_2 () =
			         let hscnt = (try Hashtbl.find localnewheader_sent newblkid with Not_found -> -1) in
			         let dscnt = (try Hashtbl.find localnewdelta_sent newblkid with Not_found -> -1) in
			         if max hscnt dscnt < !Config.minconnstostake then
				   begin
				     log_string (Printf.sprintf "Delaying publication of block %s until it has been sent to %d peers (minconnstostake), currently header sent to %d peers and delta sent to %d peers.\n" (hashval_hexstring newblkid) !Config.minconnstostake hscnt dscnt);
				     broadcast_inv [(int_of_msgtype Headers,newblkid);(int_of_msgtype Blockdelta,newblkid)];
				     raise StakingPublishBlockPause
				   end
			         else
				   begin
                                     log_string "now publishing for real\n";
				     pendingpfgblock := None;
				     let ftm = Int64.add (ltc_medtime()) 3600L in
				     if tm <= ftm then
				       begin
				         begin
                                           let u = toburn64 in (*** actually burn u litoshis and wait for a confirmation to know the block hash ***)
					   try
                                             let ltx = (0l,0l,0l,0l,0l,0l,0l,0l) in
					     if !Config.ltcoffline then
					       begin
					         Printf.printf "to stake, after ltc medtm passes %Ld create ltc burn tx for %s %s burning %Ld litoshis\n" tm (hashval_hexstring ltx) (hashval_hexstring newblkid) u
					       end
					     else
					       let btx = ltc_createburntx_spec lutxo ltx newblkid u in
					       let btxhex = Hashaux.string_hexstring btx in
					       let btxs = ltc_signrawtransaction btxhex in
					       let h = ltc_sendrawtransaction btxs in
					       pendingltctxs := h::!pendingltctxs;
					       log_string (Printf.sprintf "Sending ltc burn %s for header %s\n" h (hashval_hexstring newblkid));
					       publish_block blkh newblkid ((bhdnew,bhsnew),bdnew);
                                               Hashtbl.add unburned_headers newblkid (staking_local_process_header newblkid (bhdnew,bhsnew));
                                               Hashtbl.add unburned_deltas newblkid (staking_local_process_delta newblkid ((bhdnew,bhsnew),bdnew));
                                               Hashtbl.add localpreferred newblkid ();
					       extraburn := 0L;
					       already := Some(newblkid,hexstring_hashval h);
					       pending := !already;
					       log_string ("Burning " ^ (Int64.to_string u) ^ " litoshis in tx " ^ h ^ "\n")
					   with
					   | InsufficientLtcFunds ->
					      log_string ("insufficient ltc to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
					      raise (StakingPause(300.0))
					   | Not_found ->
					      log_string ("problem trying to burn " ^ (Int64.to_string u) ^ " litoshis" ^ "\n");
					      raise (StakingPause(300.0))
				         end
				       end			      
				   end
			       in
			       let publish_new_block () =
			         log_string (Printf.sprintf "called publish_new_block\n");
			         pendingpfgblock := Some(publish_new_block_2);
			         raise StakingPublishBlockPause
			       in
			       publish_new_block()
			     with MaxAssetsAtAddress ->
			       log_string (Printf.sprintf "Refusing to stake since the coinstake tx would put too many assets in an address.\n")
		           end
                       end
                  end
               | _ -> raise Exit
	     with
             | Exit -> log_string (Printf.sprintf "genesis staking no hits found\n");
	   end;
	   Thread.delay 120.0;
	   sleepuntil := ltc_medtime()
	 end
      | SyncIssue ->
	 begin
	   try
	     match !pending with
	     | Some(newblkid,ltcburntxid) ->
		begin
                  let bbl = get_blockburns newblkid in
		  let (lblkid,ltxid) =
		    List.find (fun (_,ltxid) -> ltxid = ltcburntxid) bbl
		  in
		  let (bhdnew,bhsnew) = DbBlockHeader.dbget newblkid in
		  let bdnew = DbBlockDelta.dbget newblkid in
		  let (_,lmedtm,burned,(txid1,vout1),_,newcsm,currhght) = Db_outlinevals.dbget (hashpair lblkid ltxid) in
		  match bhdnew.prevblockhash with
		  | Some(pbh,Poburn(plblkh,pltxh,plmedtm,pburned,ptxid1,pvout1)) ->
		     begin
		       let (_,_,_,_,_,csm,_) = Db_outlinevals.dbget (hashpair plblkh pltxh) in
		       let (tar,tmstmp,lr,thtr,sgtr) = Db_validheadervals.dbget (hashpair plblkh pltxh) in
		       if not (blockheader_succ_b pbh lr tmstmp tar (bhdnew,bhsnew)) then
			 begin
			   log_string (Printf.sprintf "Staking problem at height %Ld: %s is not a valid succ of %s\n" currhght (hashval_hexstring newblkid) (hashval_hexstring pbh));
			   raise Exit
			 end;
		       let tht = lookup_thytree thtr in
		       let sgt = lookup_sigtree sgtr in
		       process_block !Utils.log true false false (lblkid,ltxid) newblkid ((bhdnew,bhsnew),bdnew) thtr tht sgtr sgt currhght csm tar lmedtm burned txid1 vout1;
		       missingheaders := List.filter (fun (_,k) -> not (newblkid = k)) !missingheaders;
		       missingdeltas := List.filter (fun (_,k) -> not (newblkid = k)) !missingdeltas;
		       pending := None
		     end
		  | None ->
		     process_block !Utils.log true false false (lblkid,ltxid) newblkid ((bhdnew,bhsnew),bdnew) None None None None 1L !genesisstakemod !genesistarget lmedtm burned txid1 vout1;
		     missingheaders := List.filter (fun (_,k) -> not (newblkid = k)) !missingheaders;
		     missingdeltas := List.filter (fun (_,k) -> not (newblkid = k)) !missingdeltas;
		     pending := None
		end
	     | None -> raise Exit
	   with _ ->
	     Thread.delay 120.0;
	     sleepuntil := ltc_medtime()
	 end
    with
    | StakingPause(del) ->
	log_string (Printf.sprintf "Staking pause of %f seconds\n" del);
	Thread.delay del;
	sleepuntil := ltc_medtime()
    | StakingPublishBlockPause -> (** delay to allow peers to request the new block **)
	log_string (Printf.sprintf "Staking pause while peers request new block.\n");
	Thread.delay 60.0
    | StakingProblemPause -> (** something abnormal happened, pause staking for 10 minutes **)
	log_string (Printf.sprintf "Pausing staking for 10 minutes.");
	Thread.delay 600.0;
	sleepuntil := ltc_medtime()
    | e ->
	log_string (Printf.sprintf "Staking exception: %s\nPausing staking for 10 minutes.\n" (Printexc.to_string e));
	Thread.delay 600.0;
	sleepuntil := ltc_medtime()
  done;;

