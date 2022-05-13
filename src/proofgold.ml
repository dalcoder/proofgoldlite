(* Copyright (c) 2020-2021 The Proofgold Core developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2017 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json;;
open Zarithint;;
open Utils;;
open Ser;;
open Sha256;;
open Ripemd160;;
open Hashaux;;
open Hash;;
open Net;;
open Db;;
open Secp256k1;;
open Signat;;
open Cryptocurr;;
open Mathdata;;
open Assets;;
open Tx;;
open Ctre;;
open Ctregraft;;
open Block;;
open Blocktree;;
open Ltcrpc;;
open Setconfig;;
open Staking;;
open Inputdraft;;

let ltc_listener_paused = ref false;;

let commitment_maturation_minus_one = 11L;;

exception BadCommandForm;;

let get_ledgerroot b =
  match b with
  | None -> raise Not_found
  | Some(dbh,lbk,ltx) ->
      try
	let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	lr
      with Not_found ->
	let (bhd,_) = DbBlockHeader.dbget dbh in
	bhd.newledgerroot

let get_3roots b =
  match b with
  | None -> raise Not_found
  | Some(dbh,lbk,ltx) ->
      try
	let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
	(lr,tr,sr)
      with Not_found ->
	let (bhd,_) = DbBlockHeader.dbget dbh in
	(bhd.newledgerroot,bhd.newtheoryroot,bhd.newsignaroot)

let lock datadir =
  let lf = Filename.concat datadir "lock" in
  let c = open_out lf in
  close_out_noerr c;
  exitfn := (fun n -> (try Commands.save_txpool(); Sys.remove lf with _ -> ()); exit n);;

let sinceltctime f =
  let snc = Int64.sub (ltc_medtime()) f in
  if snc >= 172800L then
    (Int64.to_string (Int64.div snc 86400L)) ^ " days"
  else if snc >= 7200L then
    (Int64.to_string (Int64.div snc 7200L)) ^ " hours"
  else if snc >= 120L then
    (Int64.to_string (Int64.div snc 60L)) ^ " minutes"
  else if snc = 1L then
    "1 second"
  else
    (Int64.to_string snc) ^ " seconds";;

let sincetime f =
  let snc = Int64.sub (Int64.of_float (Unix.time())) f in
  if snc >= 172800L then
    (Int64.to_string (Int64.div snc 86400L)) ^ " days"
  else if snc >= 7200L then
    (Int64.to_string (Int64.div snc 7200L)) ^ " hours"
  else if snc >= 120L then
    (Int64.to_string (Int64.div snc 60L)) ^ " minutes"
  else if snc = 1L then
    "1 second"
  else
    (Int64.to_string snc) ^ " seconds";;

let fstohash a =
  match a with
  | None -> None
  | Some(h,_) -> Some(h);;

let stkth : Thread.t option ref = ref None;;
let swpth : Thread.t option ref = ref None;;

let ltc_listener_th : Thread.t option ref = ref None;;

let ltc_init sout =
  try
    log_string (Printf.sprintf "syncing with ltc\n");
    begin (** if recentltcblocks file was given, then process the ones listed in the file **)
      match !recent_ltc_blocks with
      | None -> ()
      | Some(f) ->
         try
	   let s = open_in f in
	   try
	     while true do
	       let l = input_line s in
	       ltc_process_block l
	     done
	   with _ -> close_in_noerr s
         with _ -> ()
    end;
    begin (** if forwardfromltcblock was given, then try to sync forward from a given block **)
      match !forward_from_ltc_block with
      | None -> ltc_forward_from_oldest()
      | Some(h) ->
         ltc_forward_from_block h
    end;
    let lbh = ltc_getbestblockhash () in
    log_string (Printf.sprintf "ltc bestblock %s\n" lbh);
    ltc_process_block lbh;
    ltc_bestblock := hexstring_hashval lbh;
    log_string (Printf.sprintf "finished initial syncing with ltc, now checking for new blocks\n");
    let lbh = ltc_getbestblockhash () in
    log_string (Printf.sprintf "ltc bestblock %s\n" lbh);
    ltc_process_block lbh;
    ltc_bestblock := hexstring_hashval lbh;
    log_string (Printf.sprintf "finished syncing with ltc\n");
  with exc ->
    log_string (Printf.sprintf "problem syncing with ltc. %s quitting.\n" (Printexc.to_string exc));
    Printf.fprintf sout "problem syncing with ltc. quitting.\n";
    !exitfn 2

let ltc_listener () =
  log_string (Printf.sprintf "ltc_listener thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let lastensuresync = ref (Unix.time()) in
  let maybe_ensure_sync () =
    let nw = Unix.time() in
    if nw -. !lastensuresync > 3600.0 then
      begin
        lastensuresync := nw;
        ensure_sync()
      end
  in
  while true do
    try
      (*      log_string (Printf.sprintf "ltc_listener thread %d loop %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday())); *)
      if !ltc_listener_paused then raise Exit;
      let lbh = ltc_getbestblockhash () in
      ltc_process_block lbh;
      ltc_bestblock := hexstring_hashval lbh;
      begin
        match !alertcandidatetxs with
        | (altx::altxr) ->
           alertcandidatetxs := altxr;
           ltc_process_alert_tx altx
        | [] -> ()
      end;
      if !netconns = [] then
        (netseeker2 (); Thread.delay 60.0)
      else if !missingheaders = [] && !missingdeltas = [] then
        (maybe_ensure_sync(); Thread.delay 60.0)
      else
        begin
          missingheaders :=
            List.filter
              (fun (_,k) -> not (DbBlockHeader.dbexists k || DbInvalidatedBlocks.dbexists k || DbBlacklist.dbexists k))
              !missingheaders;
          missingdeltas :=
            List.filter
              (fun (_,k) -> not (DbBlockDelta.dbexists k || DbInvalidatedBlocks.dbexists k || DbBlacklist.dbexists k))
              !missingdeltas;
          if !missingheaders = [] && !missingdeltas = [] then
            (maybe_ensure_sync(); Thread.delay 60.0)
          else
            begin
              List.iter
                (fun (_,_,(_,_,_,gcs)) ->
                  match !gcs with
                  | Some(cs) ->
                     if cs.handshakestep = 5 then find_and_send_requestmissingblocks cs
                  | None -> ())
                !netconns;
              Thread.delay 10.0
            end
        end
    with
    | Unix.Unix_error(Unix.ENOMEM,_,_) ->
       log_string (Printf.sprintf "Out of memory. Trying to exit gracefully.\n");
       Printf.printf "Out of memory. Trying to exit gracefully.\n";
       !exitfn 9
    | exn ->
      log_string (Printf.sprintf "ltc_listener thread %d exception %s\n" (Thread.id (Thread.self())) (Printexc.to_string exn));
      Thread.delay 120.0
  done;;

let unconfirmedspentutxo : (hashval * hashval,unit) Hashtbl.t = Hashtbl.create 100;;

exception CouldNotConsolidate;;
            
let consolidate_spendable oc blkh lr amt esttxsize gathered gatheredkeys gatheredassets txinlr =
  try
    List.iter
      (fun (alpha,a,v) ->
	match a with
	| (aid,_,obl,Currency(_)) when not (Hashtbl.mem unconfirmedspentutxo (lr,aid)) ->
	   begin
	     match obl with
	     | None ->
		begin
		  let (p,x4,x3,x2,x1,x0) = alpha in
		  if p = 0 then (** only handling assets controlled by p2pkh addresses for now **)
		    begin
		      let s kl = List.find (fun (_,_,_,_,h,_) -> h = (x4,x3,x2,x1,x0)) kl in
		      try
			let (k,c,(x,y),_,h,_) = try s !Commands.walletkeys_staking with Not_found -> s !Commands.walletkeys_nonstaking in
			gatheredkeys := (k,c,(x,y),h)::!gatheredkeys;
			gatheredassets := a::!gatheredassets;
			txinlr := (alpha,aid)::!txinlr;
			gathered := Int64.add !gathered v;
			esttxsize := !esttxsize + 300;
			if !gathered >= Int64.add amt (Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee) then raise Exit
		      with Not_found -> ()
		    end
		end
	     | Some(beta,_,_) ->
		begin
		  let (p,x4,x3,x2,x1,x0) = beta in
		  if not p then (** only handling assets controlled by p2pkh addresses for now **)
		    begin
		      let s kl = List.find (fun (_,_,_,_,h,_) -> h = (x4,x3,x2,x1,x0)) kl in
		      try
			let (k,c,(x,y),_,h,_) = try s !Commands.walletkeys_staking with Not_found -> s !Commands.walletkeys_nonstaking in
			gatheredkeys := (k,c,(x,y),h)::!gatheredkeys;
			gatheredassets := a::!gatheredassets;
			txinlr := (alpha,aid)::!txinlr;
			gathered := Int64.add !gathered v;
			esttxsize := !esttxsize + 300;
			if !gathered >= Int64.add amt (Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee) then raise Exit
		      with Not_found -> ()
		    end
		end
	   end
	| _ -> ())
      (Commands.get_spendable_assets_in_ledger oc lr blkh);
    raise CouldNotConsolidate
  with Exit -> ();;

let swappingthread () =
  log_string (Printf.sprintf "swapping thread %d begin %f\n" (Thread.id (Thread.self())) (Unix.gettimeofday()));
  let change = ref false in
  while true do
    try
      let (bb,_) = get_bestblock () in
      match bb with
      | None -> raise Not_found
      | Some(dbh,lbk,ltx) ->
	 let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	 let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
         let now = Unix.time() in
         change := false;
         swapbuyoffers :=
           List.filter
             (fun (h,pr,sbo) ->
               match sbo with
               | SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis) ->
                  let hh = hashval_hexstring h in
                  if ltc_unspent hh 1 then
                    true
                  else
                    begin
                      change := true;
                      false
                    end)
             !swapbuyoffers;
         let swapcandidatetxs1 = !swapcandidatetxs in
         List.iter
           (fun h -> ltc_getswaptransactioninfo h)
           swapcandidatetxs1;
         swapmatchoffers :=
           List.filter
             (fun (ltm,smo) ->
               match smo with
               | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,fakeltcfee) ->
                  begin
                    let caddr2 = p2shaddr_addr caddr in
                    match ctree_lookup_asset false true false caid (CHash(lr)) (addr_bitseq caddr2) with
                    | Some(_,bday,None,_) ->
                       begin
                         ltm := now; (** seems to be current **)
                         try
	                   let s kl = List.find (fun (_,_,_,_,h,_) -> h = alphap) kl in
	                   let (k,b,(x,y),_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                           if Int64.sub blkh bday > 48L then (** expired, reclaim **)
                             begin
                               let tauin = [(caddr2,caid)] in
                               let tauout = [(p2pkhaddr_addr alphap,(None,Currency(Int64.sub atms (Int64.mul 1000L !Config.defaulttxfee)))) ] in
                               let tau = (tauin,tauout) in
                               let realltcfee = Int64.mul 100L (Int64.of_int fakeltcfee) in
                               let litoshisout = Int64.sub litoshis realltcfee in
                               let ltccontracttx = swapmatchoffer_ltccontracttx ltctxid alphal litoshisout in
                               let ltccontracttxid = hashval_rev (Sha256.sha256dstr ltccontracttx) in
                               let (caddr3,credscr) = Script.createatomicswapcsv ltccontracttxid betap alphap 48l in
                               if caddr3 = caddr then
                                 begin
                                   log_string (Printf.sprintf "Redeeming expired swap\n");
                                   let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [(credscr,caddr)] [] (Some([(k,b,(x,y),alphap)])) in
                                   if (ci && co) then
                                     begin
                                       log_string (Printf.sprintf "Sending refund tx for expired swap contract\n");
                                       Commands.sendtx2 (!Utils.log) blkh 0L tr sr lr (stxsize stau) stau;
                                       change := true;
                                       false (* remove the match offer now *)
                                     end
                                   else
                                     begin
                                       log_string (Printf.sprintf "SWAPWARNING: could not sign to redeem expired contract.\n");
                                       true (* this is a bug, but keep it so we don't lose it *)
                                     end;
                                 end
                               else
                                 begin
                                   log_string (Printf.sprintf "SWAPWARNING: expired contract address mismatch\n");
                                   true (* this is a bug, but keep it so we don't lose it *)
                                 end
                             end
                           else
                             true
                         with
                         | Not_found -> (* I'm not the seller, delete eagerly, unless I'm the buyer *)
                            if Int64.sub blkh bday > 24L then (** old or expired; delete **)
                              begin
                                change := true;
                                false
                              end
                            else
                              if List.exists (fun (h,_,sbo) -> match sbo with SimpleSwapBuyOffer(lbeta,_,_,_) -> List.mem lbeta !Config.ltctradeaddresses) !swapbuyoffers then (** I'm the buyer; don't delete it so can try to spend it below **)
                                true
                              else (** not involved; if ltc utxo is spent then delete it **)
                                let hh = hashval_hexstring ltctxid in
                                if ltc_unspent hh 1 then
                                  true
                                else
                                  begin
                                    change := true;
                                    false
                                  end
                       end
                    | None ->
                       if now -. !ltm > 86400. then (** seems old, so assume the asset was spent already and not waiting to confirm **)
                         begin
                           change := true;
                           false
                         end
                       else
                         true
                    | _ -> (** nothing else should be possible, but just delete it if so **)
                       change := true;
                       false
                  end)
             !swapmatchoffers;
         Commands.swapredemptions :=
           List.filter
             (fun (ltccontracttxid,caddr,caid,betap,alphap) ->
               match ctree_lookup_asset false true false caid (CHash(lr)) (addr_bitseq (p2shaddr_addr caddr)) with
               | Some(_,bday,None,Currency(atoms)) ->
                  let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid betap alphap 48l in
                  if caddr = caddr2 then
                    begin
                      match ltc_tx_confirmed (hashval_hexstring ltccontracttxid) with
                      | Some(n) when n >= 3 ->
                         begin
                           let atomsminusfee = Int64.sub atoms (Int64.mul 400L !Config.defaulttxfee) in
                           let txinl = [(p2shaddr_addr caddr,caid)] in
                           let txoutl = [(p2pkhaddr_addr betap,(None,Currency(atomsminusfee)))] in
                           let tau = (txinl,txoutl) in
                           let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [(credscr2,caddr)] [] None in
                           if (ci && co) then
                             begin
                               let redtxid = hashstx stau in
                               log_string (Printf.sprintf "Publishing redemption tx %s for completing swap with contract address %s. Must confirm within %Ld blocks or might lose funds.\n" (hashval_hexstring redtxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (Int64.sub (Int64.add bday 48L) blkh));
                               Commands.sendtx2 !Utils.log blkh 0L tr sr lr (stxsize stau) stau; (** publish tx and remove from redemption list **)
                               unconfswapredemptions := (redtxid,Int64.add bday 48L,stau)::!unconfswapredemptions;
                               false
                             end
                           else
                             begin
                               log_string (Printf.sprintf "SWAPWARNING: Trouble signing redemption for swap with ltc tx %s and contract address %s. In %Ld blocks might lose funds.\n" (hashval_hexstring ltccontracttxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (Int64.sub (Int64.add bday 48L) blkh));
                               true
                             end
                         end
                      | _ -> true (** waiting for enough confirmations of ltc tx **)
                    end
                  else
                    begin
                      log_string (Printf.sprintf "SWAPWARNING: Contract address mismatch: computed %s but expected %s.\nIf this is not resolved quickly, funds may be lost.\n" (addr_pfgaddrstr (p2shaddr_addr caddr2)) (addr_pfgaddrstr (p2shaddr_addr caddr)));
                      true
                    end
               | None -> false (** asset has been spent so either redemption or refund already happened **)
               | _ -> false) (** other cases should be impossible (noncurrency assets or nondefault obligation), but if slips in then delete it **)
             !Commands.swapredemptions;
         List.iter
           (fun (h,pr,sbo) ->
             match sbo with
             | SimpleSwapBuyOffer(lbeta,(zp,z4,z3,z2,z1,z0),atoms,litoshis) when zp = 0 ->
                if List.mem lbeta !Config.ltctradeaddresses then (** check for match offers to accept; could generalize to check for higher bidding matches leading to something like an auction **)
                  begin
                    if ltc_unspent (hashval_hexstring h) 1 then (** if haven't already done it **)
                      begin
                        try
                          List.iter
                            (fun (_,smo) ->
                              match smo with
                              | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atoms2,litoshis2,lalpha160,alphap,betap,fakeltcfee) when ltctxid = h && atoms2 >= atoms && Int64.mul 100L (Int64.of_int fakeltcfee) >= !Config.minltctxfee ->
                                 begin
                                   match ctree_lookup_asset false true false caid (CHash(lr)) (addr_bitseq (p2shaddr_addr caddr)) with
                                   | Some(_,bday,None,Currency(atoms3)) when atoms2 = atoms3 ->
                                      begin
                                        let n = Int64.sub blkh bday in
                                        if n >= 3L && n <= 24L then (** active range **)
                                          begin
                                            log_string (Printf.sprintf "Accepting swap with contract address %s\n" (addr_pfgaddrstr (p2shaddr_addr caddr)));
                                            let realltcfee = Int64.mul (Int64.of_int fakeltcfee) 100L in
                                            let litoshisout = Int64.sub litoshis realltcfee in
                                            let ltccontracttx = swapmatchoffer_ltccontracttx h lalpha160 litoshisout in
                                            let ltccontracttxid = hashval_rev (Sha256.sha256dstr ltccontracttx) in
                                            let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid (z4,z3,z2,z1,z0) alphap 48l in
                                            if not (caddr = caddr2) then
                                              begin
                                                log_string (Printf.sprintf "SWAPWARNING: Contract address mismatch: computed %s but expected %s.\nNot accepting match, but this must be a bug.\n" (addr_pfgaddrstr (p2shaddr_addr caddr2)) (addr_pfgaddrstr (p2shaddr_addr caddr)));
                                              end
                                            else
                                              begin
                                                let ltccontracttxhex = string_hexstring ltccontracttx in
                                                try
                                                  let ltccontracttxsignedhex = ltc_signrawtransaction ltccontracttxhex in
                                                  try
                                                    let h = ltc_sendrawtransaction ltccontracttxsignedhex in
                                                    if h = hashval_hexstring ltccontracttxid then
                                                      begin
                                                        log_string (Printf.sprintf "Seem to have successfully signed and published ltc swap contract tx %s\n" h);
                                                        Commands.swapredemptions := (ltccontracttxid,caddr,caid,betap,alphap)::!Commands.swapredemptions
                                                      end
                                                    else
                                                      log_string (Printf.sprintf "SWAP WARNING: Signed and published ltc contract tx but txid was %s instead of %s. Debug or funds may be lost!\n" h (hashval_hexstring ltccontracttxid))
                                                  with Not_found ->
                                                    log_string (Printf.sprintf "Failed with accepting swap match since could not send presumably signed ltc tx: %s\n" ltccontracttxsignedhex)
                                                with Not_found ->
                                                  log_string (Printf.sprintf "Failed with accepting swap match since could not sign ltc tx: %s\n" ltccontracttxhex)
                                              end
                                          end
                                      end
                                   | _ -> ()
                                 end
                              | _ -> ())
                            !swapmatchoffers
                        with
                        | Exit -> ()
                      end
                  end
                else if not (List.exists (fun (_,smo) -> match smo with SimpleSwapMatchOffer(_,ltctxid,_,_,_,_,_,_,_,_) -> ltctxid = h) !swapmatchoffers) (** don't make offers if an offer exists; could generalize to outbig existing offers by others **)
                then
                  begin
                    try
                      let (lalpha,prsell,minatoms,maxatoms) as sof =
                        List.find
                          (fun (lalpha,pr2,minatoms,maxatoms) ->
                            pr2 <= pr && minatoms <= atoms && atoms <= maxatoms)
                          !Commands.swapselloffers
                      in
                      (** create a match offer **)
                      let fakeltcfee =
                        if Int64.rem !Config.ltctxfee 100L = 0L then
                          Int64.div !Config.ltctxfee 100L
                        else
                          Int64.add 1L (Int64.div !Config.ltctxfee 100L)
                      in
                      if fakeltcfee <= 4000L then
                        let realltcfee = Int64.mul fakeltcfee 100L in
                        begin
                          try
                            let lalpha160 = ltcbech32_md160 lalpha in
                            let litoshisout = Int64.sub litoshis realltcfee in
                            let ltccontracttx = swapmatchoffer_ltccontracttx h lalpha160 litoshisout in
                            let ltccontracttxid = hashval_rev (Sha256.sha256dstr ltccontracttx) in
                            let (k,alphap) =
                              Commands.generate_newkeyandaddress lr "nonstaking"
                            in
                            let (caddr2,credscr2) = Script.createatomicswapcsv ltccontracttxid (z4,z3,z2,z1,z0) alphap 48l in
	                    let esttxsize = ref 500 in
	                    let gathered = ref 0L in
	                    let gatheredkeys = ref [] in
	                    let gatheredassets = ref [] in
	                    let txinlr = ref [] in
                            consolidate_spendable !Utils.log blkh lr (Int64.add atoms (Int64.mul 450000L !Config.defaulttxfee)) esttxsize gathered gatheredkeys gatheredassets txinlr;
	                    let minfee = Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee in
	                    let change = Int64.sub !gathered (Int64.add atoms minfee) in
                            let lalphap = p2pkhaddr_addr lalpha160 in
                            let txoutl =
                              [(p2shaddr_addr caddr2,(None,Currency(atoms)));
                               (lalphap,(Some(p2pkhaddr_payaddr alphap,fakeltcfee,false),Currency(change)))]
                            in
                            let tau = (!txinlr,txoutl) in
                            let (stau,ci,co) = Commands.signtx2 !Utils.log lr (tau,([],[])) [] [] (Some(!gatheredkeys)) in
                            if (ci && co) then
                              begin
                                if not (List.mem lalphap !Commands.walletwatchaddrs) then Commands.walletwatchaddrs := lalphap::!Commands.walletwatchaddrs;
                                log_string (Printf.sprintf "Creating Swap Match for Buy Offer with ltc txid %s\nRefund address: %s (key %s)\nContract address: %s\nscript\n" (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr alphap)) (pfgwif k true) (addr_pfgaddrstr (p2shaddr_addr caddr2)));
                                List.iter (fun by -> Printf.fprintf !Utils.log "%02x" by) credscr2;
                                Printf.fprintf !Utils.log "\n";
	                        let s = Buffer.create 100 in
	                        seosbf (seo_stx seosb stau (s,None));
	                        let hs = Hashaux.string_hexstring (Buffer.contents s) in
	                        Printf.fprintf !Utils.log "tx: %s\n" hs;
                                flush !Utils.log;
                                Commands.sendtx2 (!Utils.log) blkh 0L tr sr lr (stxsize stau) stau;
                                let ctm = ref (Unix.time()) in
                                swapmatchoffers := (ctm,SimpleSwapMatchOffer(hashstx stau,h,caddr2,hashpair (hashtx tau) (hashint32 0l),atoms,litoshis,lalpha160,alphap,(z4,z3,z2,z1,z0),Int64.to_int fakeltcfee)) :: !swapmatchoffers;
                                let maxatoms2 = Int64.sub maxatoms atoms in
                                if maxatoms2 >= minatoms then
                                  Commands.swapselloffers := List.map (fun sof2 -> if sof = sof2 then (lalpha,prsell,minatoms,maxatoms2) else sof2) !Commands.swapselloffers (* remove some atoms from the sell offer so it does not get used to match twice *)
                                else
                                  Commands.swapselloffers := List.filter (fun sof2 -> not (sof = sof2)) !Commands.swapselloffers; (* remove the sell offer so it does not get used to match twice *)
                                Commands.save_swaps false;
                                List.iter
                                  (fun (alpha,aid) -> Hashtbl.add unconfirmedspentutxo (lr,aid) ())
                                  !txinlr
                              end
                            else
                              log_string (Printf.sprintf "Not able to match buy offer since could not fully sign consolidation tx for %s bars.\n" (bars_of_atoms atoms));
                          with
                          | InvalidBech32 ->
                             log_string (Printf.sprintf "Could not match buy offer since %s is an invalid bech32 address.\n" lalpha);
                          | CouldNotConsolidate ->
                             log_string (Printf.sprintf "Not able to match buy offer since cannot consolidate %s bars.\n" (bars_of_atoms atoms));
                        end
                    with
                    | Not_found -> ()
                  end
             | _ -> ())
           !swapbuyoffers;
         Thread.delay 30.0
    with exn ->
      log_string (Printf.sprintf "swapping thread %d exception %s\n" (Thread.id (Thread.self())) (Printexc.to_string exn));
      Thread.delay 300.0
  done;;

(*** if only one ledger root is in the snapshot, assets, hconselts and ctreeelts will not be revisited, so no need to waste memory by saving them in fin ***)
let snapshot_fin_mem fin h = 
  (List.length !snapshot_ledgerroots > 1) && Hashtbl.mem fin h

let snapshot_fin_add fin h =
  if List.length !snapshot_ledgerroots > 1 then
    Hashtbl.add fin h ()

let dbledgersnapshot_asset assetfile fin h =
  if not (snapshot_fin_mem fin h) then
    begin
      snapshot_fin_add fin h;
      try
        let a = DbAsset.dbget h in
        seocf (seo_asset seoc a (assetfile,None))
      with Not_found ->
        Printf.printf "Could not find %s asset in database\n" (hashval_hexstring h)
    end

let rec dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l =
  if not (snapshot_fin_mem fin h) then
    begin
      snapshot_fin_add fin h;
      try
	let (ah,hr) = DbHConsElt.dbget h in
        seocf (seo_prod seo_hashval (seo_option (seo_prod seo_hashval seo_int8)) seoc (ah,hr) (hconseltfile,None));
	dbledgersnapshot_asset assetfile fin ah;
	match hr with
	| Some(hr,l2) ->
	    if not (l = l2+1) then Printf.printf "Length mismatch in hconselt %s: expected length %d after cons but rest has claimed length %d.\n" (hashval_hexstring h) l l2;
	    dbledgersnapshot_hcons (hconseltfile,assetfile) fin hr l2
	| None ->
	    if not (l = 1) then Printf.printf "Length mismatch in hconselt %s: expected length %d after cons but claimed to have no extra elements.\n" (hashval_hexstring h) l;
	    ()
      with Not_found ->
	Printf.printf "Could not find %s hcons element in database\n" (hashval_hexstring h)
    end

let rec dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h =
  if not (snapshot_fin_mem fin h) && (!snapshot_full || not (supp = [])) then
    begin
      snapshot_fin_add fin h;
      try
	let c = expand_ctree_atom_or_element false h in
	seocf (seo_ctree seoc c (ctreeeltfile,None));
	dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin supp c
      with Not_found ->
	Printf.printf "Could not find %s ctree element in database\n" (hashval_hexstring h)
    end
and dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin supp c =
  match c with
  | CLeaf(bl,NehHash(h,l)) ->
      dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l
  | CLeaf(bl,_) ->
      Printf.printf "non element ctree found in database\n"
  | CHash(h) -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
  | CLeft(c0) -> dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_false0 supp) c0
  | CRight(c1) -> dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_true0 supp) c1
  | CBin(c0,c1) ->
      dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_false0 supp) c0;
      dbledgersnapshot_ctree (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_true0 supp) c1

let rec dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin supp c sl =
  if not (sl = []) then
    match c with
    | CLeaf(bl,NehHash(h,l)) ->
	dbledgersnapshot_hcons (hconseltfile,assetfile) fin h l
    | CLeaf(bl,_) ->
	Printf.printf "non element ctree found in database\n"
    | CHash(h) -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
    | CLeft(c0) -> dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_false0 supp) c0 (strip_bitseq_false0 sl)
    | CRight(c1) -> dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_true0 supp) c1 (strip_bitseq_true0 sl)
    | CBin(c0,c1) ->
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_false0 supp) c0 (strip_bitseq_false0 sl);
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin (strip_bitseq_true0 supp) c1 (strip_bitseq_true0 sl)

let dbledgersnapshot_shards (ctreeeltfile,hconseltfile,assetfile) fin supp h sl =
  if not (snapshot_fin_mem fin h) && (!snapshot_full || not (supp = [])) then
    begin
      snapshot_fin_add fin h;
      try
	let c = expand_ctree_atom_or_element false h in
	seocf (seo_ctree seoc c (ctreeeltfile,None));
	dbledgersnapshot_ctree_shards (ctreeeltfile,hconseltfile,assetfile) fin supp c sl
      with Not_found ->
	Printf.printf "Could not find %s ctree element in database\n" (hashval_hexstring h)
    end

let dbledgersnapshot_ctree_top (ctreeeltfile,hconseltfile,assetfile) fin supp h s =
  match s with
  | None -> dbledgersnapshot (ctreeeltfile,hconseltfile,assetfile) fin supp h
  | Some(sl) ->
      let bitseq j =
	let r = ref [] in
	for i = 0 to 8 do
	  if ((j lsr i) land 1) = 1 then
	    r := true::!r
	  else
	    r := false::!r
	done;
	!r
      in
      dbledgersnapshot_shards (ctreeeltfile,hconseltfile,assetfile) fin supp h (List.map bitseq sl);;

let parse_json_privkeys kl =
  let (klj,_) = parse_jsonval kl in
  match klj with
  | JsonArr(kla) ->
      List.map
	(fun kj ->
	  match kj with
	  | JsonStr(k) ->
	    begin
	      let (k,b) = 
		try
		  privkey_from_wif k
		with _ ->
		  try
		    privkey_from_btcwif k
		  with _ -> raise (Failure "Bad private key")
	      in
	      match Secp256k1.smulp k Secp256k1._g with
	      | Some(x,y) ->
		  let h = hashval_md160 (pubkey_hashval (x,y) b) in
		  (k,b,(x,y),h)
	      | None -> raise (Failure "Bad private key")
	    end
	  | _ -> raise BadCommandForm)
	kla
  | _ -> raise BadCommandForm;;

let parse_json_redeemscripts rl =
  let (rlj,_) = parse_jsonval rl in
  match rlj with
  | JsonArr(rla) ->
      List.map
	(fun rj ->
	  match rj with
	  | JsonStr(r) -> 
	      let il = string_bytelist (hexstring_string r) in
	      (il,Script.hash160_bytelist il)
	  | _ -> raise BadCommandForm)
	rla
  | _ -> raise BadCommandForm;;

let parse_json_secrets sl =
  let (slj,_) = parse_jsonval sl in
  match slj with
  | JsonArr(sla) ->
      List.map
	(fun sj ->
	  match sj with
	  | JsonStr(s) -> 
	      let sh = hexstring_hashval s in
	      let shh = Script.sha256_bytelist (string_bytelist (hexstring_string s)) in
	      (sh,shh)
	  | _ -> raise BadCommandForm)
	sla
  | _ -> raise BadCommandForm;;
	
let commandh : (string,(string * string * (out_channel -> string list -> unit))) Hashtbl.t = Hashtbl.create 100;;
let sortedcommands : string list ref = ref [];;

let local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy =
  try
    Hashtbl.find remgvtpth oidthy
  with Not_found ->
    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
    match hlist_lookup_obj_owner true true true oidthy hl with
    | None -> raise Not_found
    | Some(beta,r) -> (beta,r);;

let local_lookup_prop_thy_owner lr remgvknth pidthy alphathy =
  try
    Hashtbl.find remgvknth pidthy
  with Not_found ->
    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
    match hlist_lookup_prop_owner true true true pidthy hl with
    | None -> raise Not_found
    | Some(beta,r) -> (beta,r);;

let ac c h longhelp f =
  sortedcommands := List.merge compare [c] !sortedcommands;
  Hashtbl.add commandh c (h,longhelp,(fun oc al -> try f oc al with BadCommandForm -> Printf.fprintf oc "%s\n" h));;

let validusername_p u =
  if u = "" || String.length u > 32 then
    false
  else
    begin
      try
        for i = 0 to String.length u - 1 do
          let ci = Char.code u.[i] in
          if not ((ci >= 48 && ci <= 57) || (ci >= 65 && ci <= 90) || (ci >= 97 && ci <= 122) || (ci = 95)) then raise Exit
        done;
        true
      with Exit -> false
    end;;

let identities : (string,bool * Z.t * (Z.t * Z.t) * addr) Hashtbl.t = Hashtbl.create 10;;
let othidentities : (string,bool * (Z.t * Z.t) * addr) Hashtbl.t = Hashtbl.create 10;;

let identities_loaded = ref false;;

let identity_pubkey u =
  try
    let (_,(x,y),_) = Hashtbl.find othidentities u in
    (x,y)
  with
  | Not_found ->
     let (_,_,(x,y),_) = Hashtbl.find identities u in
     (x,y)

let load_identities () =
  if not (!identities_loaded) then
    begin
      identities_loaded := true;
      let idfn = Filename.concat (datadir()) "ids" in
      if Sys.file_exists idfn then
        begin
          let f = open_in idfn in
          try
            while true do
              let u = input_line f in
              let alpha = input_line f in
              let pubkey = input_line f in
              let privkey = input_line f in
              try
                let alpha = Cryptocurr.pfgaddrstr_addr alpha in
                let ((x,y),_) = Cryptocurr.hexstring_pubkey pubkey in
                let (k,b) = Cryptocurr.privkey_from_wif privkey in
                Hashtbl.add identities u (b,k,(x,y),alpha)
              with _ -> ()
            done
          with End_of_file ->
            close_in_noerr f;
        end;
      let idfn = Filename.concat (datadir()) "otherids" in
      if Sys.file_exists idfn then
        begin
          let f = open_in idfn in
          try
            while true do
              let u = input_line f in
              let alpha = input_line f in
              let pubkey = input_line f in
              try
                let alpha = Cryptocurr.pfgaddrstr_addr alpha in
                let ((x,y),b) = Cryptocurr.hexstring_pubkey pubkey in
                Hashtbl.add othidentities u (b,(x,y),alpha)
              with _ -> ()
            done
          with End_of_file ->
            close_in_noerr f
        end
    end;;

let sendprivmessage oc fromuser touser msg =
  let msgl = String.length msg in
  if msgl > 30000 then
    Printf.fprintf oc "Private messages must contain less than 30000 bytes.\n"
  else
    begin
      load_identities();
      try
        let (b1,k1,_,_) = Hashtbl.find identities fromuser in
        try
          let (x2,y2) = identity_pubkey touser in
          try
            match Secp256k1.smulp k1 (Some(x2,y2)) with
            | Some(x3,y3) -> (** shared secret **)
               let padseedz = rand_256() in
               let padseedh = big_int_md256 padseedz in
               let (p0,p1,p2,p3,p4,p5,p6,p7) = padseedh in
               let (x30,x31,x32,x33,x34,x35,x36,x37) = big_int_md256 x3 in
               let q0 = Int32.logxor p0 x30 in (** xor shared secret with pad seed **)
               let q1 = Int32.logxor p1 x31 in
               let q2 = Int32.logxor p2 x32 in
               let q3 = Int32.logxor p3 x33 in
               let q4 = Int32.logxor p4 x34 in
               let q5 = Int32.logxor p5 x35 in
               let q6 = Int32.logxor p6 x36 in
               let q7 = Int32.logxor p7 x37 in
               let qs = hexstring_string (hashval_hexstring (q0,q1,q2,q3,q4,q5,q6,q7)) in
               let emsgsb = Buffer.create (34 + msgl) in
               Buffer.add_char emsgsb (Char.chr (msgl / 256));
               Buffer.add_char emsgsb (Char.chr (msgl land 255));
               Buffer.add_string emsgsb qs;
               let tg = ref 0 in
               let pad = ref (hexstring_string (hashval_hexstring (hashtag padseedh (Int32.of_int !tg)))) in
               let j = ref 0 in
               for i = 0 to msgl - 1 do
                 Buffer.add_char emsgsb (Char.chr ((Char.code !pad.[!j]) lxor (Char.code msg.[i])));
                 incr j;
                 if !j = 32 then
                   begin
                     incr tg;
                     pad := hexstring_string (hashval_hexstring (hashtag padseedh (Int32.of_int !tg)));
                     j := 0
                   end
               done;
               let emsg = Buffer.contents emsgsb in
               let emsghex = string_hexstring emsg in
               let cmsg = Printf.sprintf "pm:f=%s:t=%s:m=%s\n" fromuser touser emsghex in
               let (_,sg) = repeat_rand (sign_proofgold_message (hashval_hexstring (sha256str cmsg)) k1) rand_256 in
               let sg = encode_signature 0 b1 sg in
               let fullcall = Printf.sprintf "%s -X POST -F 'f=%s' -F 't=%s' -F 's=%s' -F 'm=@-' https://proofgold.org/msg/postmsg.php" !Config.curl fromuser touser (string_hexstring sg) in
               let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
               begin
                 try
                   Printf.fprintf outc "%s\n" emsghex;
                   close_out_noerr outc;
                   let l = input_line inc in
                   if l = "OK" then
                     Printf.fprintf oc "Message seems to have been sent.\n"
                   else
                     begin
                       Printf.fprintf oc "Message does not seem to have been sent.\n%s\n" l;
                       try
                         while true do
                           let l = input_line inc in
                           Printf.fprintf oc "%s\n" l
                         done
                       with _ ->
                         ignore (Unix.close_process_full (inc,outc,errc))
                     end
                 with _ ->
                   ignore (Unix.close_process_full (inc,outc,errc))
               end
            | None ->
               Printf.fprintf oc "Due to extremely rare null point, these two users cannot share private messages.\nThis is probably a bug.\n"
          with _ ->
            Printf.fprintf oc "Problem trying to send private message.\n"
        with Not_found ->
          Printf.fprintf oc "Could not find identity for recipient %s\n" touser
      with Not_found ->
        Printf.fprintf oc "Could not find identity for sender %s\n" fromuser
    end;;

let apost oc u p opid =
  if String.length p = 0 then
    Printf.fprintf oc "Empty posts are not allowed.\n"
  else if String.length p >= 1024 then
    Printf.fprintf oc "Posts must have fewer than 1024 characters.\n"
  else if not (validusername_p u) then
    Printf.fprintf oc "%s is not a valid username\n" u
  else
    begin
      load_identities();
      try
        let (b,k,_,_) = Hashtbl.find identities u in
        try
          let msg =
            match opid with
            | None -> Printf.sprintf "apost:u=%s:c=%s" u p
            | Some(pid) -> Printf.sprintf "apost:u=%s:p=%s:c=%s" u pid p
          in
          let (_,sg) = repeat_rand (sign_proofgold_message (hashval_hexstring (sha256str msg)) k) rand_256 in
          let sg = encode_signature 0 b sg in
          let fullcall =
            match opid with
            | None ->
               Printf.sprintf "%s -X POST -F 'u=%s' -F 'c=%s' -F 's=%s' https://proofgold.org/apost/apost.php" !Config.curl u (string_hexstring p) (string_hexstring sg)
            | Some(pid) ->
               Printf.sprintf "%s -X POST -F 'u=%s' -F 'p=%s' -F 'c=%s' -F 's=%s' https://proofgold.org/apost/apost.php" !Config.curl u pid (string_hexstring p) (string_hexstring sg)
          in
          let (inc,outc,errc) = Unix.open_process_full fullcall [| |] in
          try
            let l = input_line inc in
            Printf.fprintf oc "%s\n" l;
            ignore (Unix.close_process_full (inc,outc,errc))
          with exn ->
            Printf.fprintf oc "Problem communicating with server: %s\n" (Printexc.to_string exn);
            ignore (Unix.close_process_full (inc,outc,errc))
        with exn ->
          Printf.fprintf oc "Crypto exception: %s\n" (Printexc.to_string exn);
      with _ ->
        Printf.fprintf oc "Do not have priv key for %s.\nIf it is in the wallet you might need to do importid.\n" u
    end

let find_spendable_utxo oc lr blkh mv =
  let b = ref None in
  List.iter
    (fun (alpha,a,v) ->
      if v >= mv && (match a with (aid,_,_,Currency(_)) when not (Hashtbl.mem unconfirmedspentutxo (lr,aid)) -> true | _ -> false) then
	match !b with
	| None -> b := Some(alpha,a,v)
	| Some(_,_,u) -> if v < u then b := Some(alpha,a,v))
    (Commands.get_spendable_assets_in_ledger oc lr blkh);
  match !b with
  | None -> raise Not_found
  | Some(alpha,a,v) ->
      Hashtbl.add unconfirmedspentutxo (lr,assetid a) ();
      (alpha,a,v);;

let rec find_marker_in_hlist hl =
  match hl with
  | HNil -> raise Not_found
  | HCons((aid,bday,obl,Marker),_) -> (aid,bday,obl)
  | HCons(_,hr) -> find_marker_in_hlist hr
  | HConsH(h,hr) ->
      let a = get_asset h in
      find_marker_in_hlist (HCons(a,hr))
  | HHash(h,_) ->
      find_marker_in_hlist (get_hlist_element h)

let find_marker_at_address tr beta =
  let hl = ctree_lookup_addr_assets true true tr (addr_bitseq beta) in
  find_marker_in_hlist hl

let initialize_commands () =
  ac "version" "version" "Print client description and version number"
    (fun oc _ ->
      Printf.fprintf oc "%s %s\n" Version.clientdescr Version.clientversion);
  ac "retractltcblockandexit" "retractltcblockandexit <ltcblock>" "Purge ltc information back to the given block and exit.\nWhen Proofgold restarts it will resync with ltc back to the retracted block."
    (fun oc al ->
      match al with
      | [h] -> (try ltc_listener_paused := true; retractltcblock h; !exitfn 0 with e -> Printf.fprintf oc "%s\n" (Printexc.to_string e); !exitfn 7)
      | _ -> raise BadCommandForm);
  ac "sendtoaddress" "sendtoaddress <address> <bars> [<lockheight>]" "Consolidate enough spendable utxos to send the given number of bars to the given address.\nIf the address is a term address, then the bars are put as a bounty.\nIf a lockheight is given and the address is a pay address,\n then the new asset is locked until the given height."
    (fun oc al ->
      let (a,v,lh) =
        match al with
        | [a;v] ->
           (a,v,None)
        | [a;v;lh] ->
           (a,v,Some(Int64.of_string lh))
        | _ -> raise BadCommandForm
      in
      let gamma = pfgaddrstr_addr a in
      if pubaddr_p gamma then (Printf.fprintf oc "%s is a publication address, so neither currency nor bounty can be sent there.\n" a; raise BadCommandForm);
      let amt = Cryptocurr.atoms_of_bars v in
      let esttxsize = ref 500 in
      let gathered = ref 0L in
      let gatheredkeys = ref [] in
      let gatheredassets = ref [] in
      let txinlr = ref [] in
      begin
	let (blkh,tm,lr,tr,sr) =
	  match get_bestblock_print_warnings oc with
	  | None -> raise Not_found
	  | Some(dbh,lbk,ltx) ->
	     let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	     let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
	     (blkh,tm,lr,tr,sr)
	in
	try
          consolidate_spendable oc blkh lr amt esttxsize gathered gatheredkeys gatheredassets txinlr;
	  let minfee = Int64.mul (Int64.of_int !esttxsize) !Config.defaulttxfee in
	  let change = Int64.sub !gathered (Int64.add amt minfee) in
          let newpreasset = if termaddr_p gamma then Bounty(amt) else Currency(amt) in
          let obl =
            if termaddr_p gamma then
              None
            else
              match lh with
              | None -> None
              | Some(lh) ->
                 if lh <= blkh then
                   raise (Failure "lockheight must be greater than current height")
                 else
                   let (p,x0,x1,x2,x3,x4) = gamma in
                   Some((p=1,x0,x1,x2,x3,x4),lh,false)
          in
	  let txoutl =
	    if change >= 10000L then
	      let (_,delta) = Commands.generate_newkeyandaddress lr "" in
	      [(gamma,(obl,newpreasset));(p2pkhaddr_addr delta,(None,Currency(change)))]
	    else
	      [(gamma,(obl,newpreasset))]
	  in
	  let stau = ((!txinlr,txoutl),([],[])) in
	  let (stau,ci,co) = Commands.signtx2 oc lr stau [] [] (Some(!gatheredkeys)) in
	  if (ci && co) then
            begin
	      Commands.sendtx2 oc blkh tm tr sr lr (stxsize stau) stau;
              List.iter
                (fun (alpha,aid) -> Hashtbl.add unconfirmedspentutxo (lr,aid) ())
                !txinlr
            end
	  else
	    Printf.fprintf oc "Transaction was created but only partially signed and so was not sent.\n"
	with CouldNotConsolidate ->
	  Printf.fprintf oc "Could not consolidate enough spendable currency to send %s to address %s\n" v a
      end);
  ac "signmessage" "signmessage <address> <msg>" "Sign a message with the private key for the given address, assuming it is p2pkh and in the wallet."
    (fun oc al ->
      match al with
      | [a;m] ->
	 let alpha = pfgaddrstr_addr a in
	 let (p,x4,x3,x2,x1,x0) = alpha in
	 begin
	   if p = 0 then
	     begin
	       try
		 let s kl = List.find (fun (_,_,_,_,h,_) -> h = (x4,x3,x2,x1,x0)) kl in
		 let (k,b,_,_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                 let (_,(r,s)) = repeat_rand (sign_proofgold_message m k) rand_256 in
                 Printf.fprintf oc "%s\n" (encode_signature 0 b (r,s)) (** recid is just set to 0 here since pubkey recovery is not supported in proofgold signed messages **)
               with Not_found ->
                 Printf.fprintf oc "The private key for %s is not in your wallet.\n" a
             end
           else
             Printf.fprintf oc "%s is not a p2pkh address.\n" a
         end         
      | _ -> raise BadCommandForm);
  ac "signmessagewithkey" "signmessagewithkey <privkey> <msg>" "Sign a message with the private key (in WIF format)."
    (fun oc al ->
      match al with
      | [k;m] ->
         let (k,b) = privkey_from_wif k in
         let (_,(r,s)) = repeat_rand (sign_proofgold_message m k) rand_256 in
         Printf.fprintf oc "%s\n" (encode_signature 0 b (r,s))
      | _ -> raise BadCommandForm);
  ac "verifymessage" "verifymessage <pubkey> <signature> <msg>" "Verify the signature of the message by the key for the pubkey is valid."
    (fun oc al ->
      match al with
      | [pk;sg;m] ->
         let (q,b) = hexstring_pubkey pk in
         let (_,fcomp,(r,s)) = decode_signature sg in
         if b = fcomp && verifyproofgoldmessage (Some(q)) (r,s) m then
           Printf.fprintf oc "Valid\n"
         else
           Printf.fprintf oc "Invalid\n"
      | _ -> raise BadCommandForm);
  ac "importid" "(deprecated) importid <username> <address>" "(deprecated) Locally associate a username with an address in the local wallet.\nThis identity is assumed to already have been registered with registerid."
    (fun oc al -> Printf.fprintf oc "importid is deprecated");
  ac "registerid" "(deprecated) registerid <username> <address>" "(deprecated) Associate a pubkey (the one for the given address) with a username on proofgold.org.\nThis can then be used to exchange private messages (end-to-end encrypted)\nwith other registered users via the pm command.\nThe address must be a p2pkh address in the wallet.\nThe command newaddress can be used to obtain a fresh p2pkh address.\nThe commands importprivkey and importbtcprivkey can be used if you have a private key for a p2pkh address in WIF Format."
    (fun oc al -> raise (Failure "registerid is deprecated"));
  ac "getid" "(deprecated) getid <username>" "(deprecated) Try to get the pubkey associated with a username registered on proofgold.org."
    (fun oc al -> raise (Failure "getid is deprecated"));
  ac "getmessages" "(deprecated) getmessages <user> [<timestamp>]" "(deprecated) Get all private messages for the user since the given timestamp.\nIf no timestamp is given, all messages from the past week are downloaded."
    (fun oc al -> raise (Failure "getmessages is deprecated"));
  ac "savemessages" "(deprecated) savemessages <user> <file> [<timestamp>]" "(deprecated) Get all private messages for the user since the given timestamp and save them into the given file.\nIf no timestamp is given, all messages from the past week are downloaded."
    (fun oc al -> raise (Failure "savemessages is deprecated"));
  ac "pm" "(deprecated) pm <fromuser> <touser> <text>" "(deprecated) Send the (short) text as a private message."
    (fun oc al -> raise (Failure "pm is deprecated"));
  ac "pmfile" "(deprecated) pmfile <fromuser> <touser> <filename>" "(deprecated) Send the contents of the given text file as a private message."
    (fun oc al -> raise (Failure "pmfile is deprecated"));
  ac "posttop" "(deprecated) posttop <user> <text>" "(deprecated) Post in the top level of the latest anon topic on the proofgold forum.\nThe given username is assumed to be registered with registerid."
    (fun oc al -> raise (Failure "posttop is deprecated"));
  ac "postreply" "(deprecated) postreply <user> <parentid> <text>" "(deprecated) Post reply on the proofgold forum"
    (fun oc al -> raise (Failure "postreply is deprecated"));
  ac "selloffers" "selloffers"
    "Show the current local sell offers of the node."
    (fun oc al ->
      List.iter
        (fun (lalpha,pr,minatoms,maxatoms) ->
          Printf.fprintf oc "%f %s [%s,%s]\n" pr lalpha (bars_of_atoms minatoms) (bars_of_atoms maxatoms))
        !Commands.swapselloffers);
  ac "buyoffers" "buyoffers"
    "Show all active buy offers, indicating which are by the local node."
    (fun oc al ->
      List.iter
        (fun (h,pr,sbo) ->
          match sbo with
          | SimpleSwapBuyOffer(lbeta,pbeta,atoms,litoshis) ->
             let hh = hashval_hexstring h in
             if List.mem lbeta !Config.ltctradeaddresses then Printf.fprintf oc "[LOCAL] ";
             Printf.fprintf oc "%f %s %s litecoins for %s proofgold bars\n" pr hh (ltc_of_litoshis litoshis) (bars_of_atoms atoms))
        !swapbuyoffers);
  ac "swapredemptions" "swapredemptions"
    "Show all swap redemptions in progress (completing the buying of pfg via a swap with ltc)"
    (fun oc al ->
      List.iter
        (fun (ltctxid,caddr,caid,betap,alphap) ->
          Printf.fprintf oc "* ltctx: %s\ncontract %s: %s\nMy address (buyer): %s\nRefund address (seller): %s\n" (hashval_hexstring ltctxid) (addr_pfgaddrstr (p2shaddr_addr caddr)) (hashval_hexstring caid) (addr_pfgaddrstr (p2pkhaddr_addr betap)) (addr_pfgaddrstr (p2pkhaddr_addr alphap)))
        !Commands.swapredemptions);
  ac "matchoffers" "matchoffers"
    "Show all current match offers, indicating which correspond to the local node."
    (fun oc al ->
      List.iter
        (fun (_,smo) ->
          match smo with
          | SimpleSwapMatchOffer(pfgtxid,ltctxid,caddr,caid,atms,litoshis,alphal,alphap,betap,ltcfee) ->
             begin
               try
	         let s kl = List.find (fun (_,_,_,_,h,_) -> h = alphap) kl in
	         let (_,_,_,_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
                 Printf.fprintf oc "* [LOCAL] Match offer for ltc buy offer %s\nContract address: %s\n" (hashval_hexstring ltctxid) (addr_pfgaddrstr (p2shaddr_addr caddr))
               with Not_found ->
                 Printf.fprintf oc "* Match offer for ltc buy offer %s\n" (hashval_hexstring ltctxid)
             end)
        !swapmatchoffers);
  ac "createswapselloffer" "createswapselloffer <price> <minamt> <maxamt>"
    "Create a local (not advertised) offer to sell some pfg for ltc via an atomic swap.\nThis will be used to match public buy offers."
    (fun oc al ->
      match !Config.ltctradeaddresses with
      | [] -> Printf.fprintf oc "Cannot set up a sell offer until at least one bech32 litecoin address\nis given via ltctradeaddress in proofgold.conf file.\n";
      | (lalpha::_) ->
         match al with
         | [pr;mi;ma] ->
            let pr = float_of_string pr in
            let minatoms = atoms_of_bars mi in
            let maxatoms = atoms_of_bars ma in
            if minatoms > maxatoms then
              raise (Failure "minamount must be <= to maxamount")
            else
              Commands.swapselloffers := List.merge (fun (_,p1,_,_) (_,p2,_,_) -> compare p1 p2) [(lalpha,pr,minatoms,maxatoms)] !Commands.swapselloffers
         | _ -> raise BadCommandForm);
  ac "cancelswapselloffers" "cancelswapselloffers"
    "Cancels all local swap sell offers.\n"
    (fun oc al -> Commands.swapselloffers := []; Commands.save_swaps false);
  ac "createswapbuyoffer" "createswapbuyoffer <pfgaddr> <price> <pfgamount> <ltcamount>"
    "Create a public offer to buy proofgold bars via an atomic swap.\nThe price is given in LTC:PFG, e.g., 0.01 means 0.01 litecoins per proofgold.\nThe amount is then given in both the amount of proofgold to buy and litecoins to spend.\nIf the ratio does not match the price within a 1% tolerance the swap buy offer is not created.\nLines of the form ltctradeaddress=<address> in proofgold.conf\n give segwit addresses to use for swaps.\nIf successful, this command will create a litecoin tx that makes the terms of the swap\nand the utxo for the swap explicit.\n"
    (fun oc al ->
      match al with
      | [pbetastr;pr;pfgamt;ltcamt] ->
         let pbeta = pfgaddrstr_addr pbetastr in
         if not (p2pkhaddr_p pbeta) then raise (Failure "proofgold address for swap must be p2pkh");
         let prg = float_of_string pr in
         let atoms = atoms_of_bars pfgamt in
         let litoshis = litoshis_of_ltc ltcamt in
         let prc = Int64.to_float litoshis *. 1000.0 /. Int64.to_float atoms in
         let prf = prg /. prc in
         if prf < 0.99 || prf > 1.01 then raise (Failure "Given price is more than 1% off from computed price. Not making offer.");
	 begin
	   try
	     let ltctxid = ltc_createswapoffertx pbeta litoshis atoms in
             Printf.fprintf oc "If you decide to cancel this swap offer, use:\ncancelswapbuyoffer %s\n" ltctxid;
           with InsufficientLtcFunds -> raise (Failure "Insufficient LTC funds to create swap buy offer. (There must be a single utxo in an ltctradeaddress to fund the swap buy offer.)")
         end
      | _ -> raise BadCommandForm);
  ac "cancelswapbuyoffer" "cancelswapbuyoffer <txid>"
    "Cancel an atomic swap by spending the ltc utxo for the swap to a local ltcaddress.\nLines of the form ltctradeaddress=<address> in proofgold.conf\n give segwit addresses to use for swaps.\n"
    (fun oc al ->
      match al with
      | [h] -> ltc_cancelswapbuyoffer h
      | _ -> raise BadCommandForm);
  ac "scanforswapbuyoffers" "scanforswapbuyoffers [<num>]"
    "Scans recent ltc blocks for swap buy offers.\nThe number of blocks can optionally be given with default 1000"
    (fun oc al ->
      let n =
        match al with
        | [] -> 1000
        | [n] -> int_of_string n
        | _ -> raise BadCommandForm
      in
      ltc_scanforswapbuyoffers n);
  ac "getaddressinfo" "getaddressinfo <address>" "Print information about address"
    (fun oc al ->
      match al with
      | [a] ->
	  let alpha = pfgaddrstr_addr a in
	  let (p,x4,x3,x2,x1,x0) = alpha in
	  let jol = ref [] in
	  begin
	    if p = 0 then
	      begin
		jol := ("address",JsonStr("p2pkh"))::!jol;
		try
		  let s kl = List.find (fun (_,_,_,_,h,_) -> h = (x4,x3,x2,x1,x0)) kl in
		  let (_,b,(x,y),_,_,_) = s (!Commands.walletkeys_staking @ !Commands.walletkeys_nonstaking @ !Commands.walletkeys_staking_fresh @ !Commands.walletkeys_nonstaking_fresh) in
		  if b then
		    if evenp y then
		      jol := ("pubkey",JsonStr(Printf.sprintf "02%s" (md256_hexstring (big_int_md256 x))))::!jol
		    else
		      jol := ("pubkey",JsonStr(Printf.sprintf "03%s" (md256_hexstring (big_int_md256 x))))::!jol
		  else
		    jol := ("pubkey",JsonStr(Printf.sprintf "04%s%s" (md256_hexstring (big_int_md256 x)) (md256_hexstring (big_int_md256 y))))::!jol
		with Not_found -> ()
	      end
	    else if p = 1 then
	      begin
		jol := ("address",JsonStr("p2sh"))::!jol;
		let (_,_,bl) = List.find (fun (beta,_,_) -> (x4,x3,x2,x1,x0) = beta) !Commands.walletp2shs in
		let bu = Buffer.create 10 in
		List.iter (fun b -> Buffer.add_char bu (Char.chr b)) bl;
		jol := ("script",JsonStr(string_hexstring (Buffer.contents bu)))::!jol
	      end
	    else if p = 2 then
	      begin
		jol := ("address",JsonStr("term"))::!jol;
	      end
	    else if p = 3 then
	      begin
		jol := ("address",JsonStr("pub"))::!jol;
	      end
	    else
	      raise (Failure "apparently not an address");
	  end;
	  if not (!jol = []) then
	    begin
	      print_jsonval oc (JsonObj(List.rev !jol));
	      Printf.fprintf oc "\n";
	    end
      | _ -> raise BadCommandForm);
  ac "addnonce" "addnonce <file>" "Add a nonce to a theory specification file, a signature specification file or a document"
    (fun oc al ->
      match al with
      | [f] ->
	  begin
	    let ch = open_in f in
	    try
	      while true do
		let l = input_token ch in
		if l = "Nonce" then raise Exit
	      done
	    with
	    | Exit -> close_in_noerr ch; Printf.fprintf oc "A nonce was already declared.\nNo change was made.\n"
	    | End_of_file ->
		close_in_noerr ch;
		let ch = open_out_gen [Open_append] 0o600 f in
		let h = big_int_md256 (strong_rand_256()) in
		let nonce = hashval_hexstring h in
		Printf.fprintf ch "\nNonce %s\n" nonce;
		close_out_noerr ch
	    | e -> close_in_noerr ch; raise e
	  end
      | _ -> raise BadCommandForm);
  ac "addpublisher" "addpublisher <file> <payaddr>" "Add a publisher address to a theory specification file, a signature specification file or a document."
    (fun oc al ->
      match al with
      | [f;gammas] ->
	  begin
	    let gamma = Cryptocurr.pfgaddrstr_addr gammas in
	    if not (payaddr_p gamma) then raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." gammas));
	    let ch = open_in f in
	    try
	      while true do
		let l = input_token ch in
		if l = "Publisher" then raise Exit
	      done
	    with
	    | Exit -> close_in_noerr ch; Printf.fprintf oc "A publisher was already declared.\nNo change was made.\n"
	    | End_of_file ->
		close_in_noerr ch;
		let ch = open_out_gen [Open_append] 0o600 f in
		Printf.fprintf ch "\nPublisher %s\n" gammas;
		close_out_noerr ch
	    | e -> close_in_noerr ch; raise e
	  end
      | _ -> raise BadCommandForm);
  ac "readdraft" "readdraft <file>" "Read a theory specification file, signature specification file or document file and give information."
    (fun oc al ->
      match al with
      | [f] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,prophrev,propownsh,proprightsh) = input_theoryspec ch in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_theoryspec seosb thyspec (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Theory is too big: %d bytes. It probably will not fit in a block.\n" p;
              let counter = ref 0 in
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      let b = theoryspec_burncost thyspec in
		      Printf.fprintf oc "Theory is correct and has id %s and address %s.\n%s bars must be burned to publish the theory.\n" (hashval_hexstring thyh) (Cryptocurr.addr_pfgaddrstr (hashval_pub_addr thyh)) (bars_of_atoms b);
		      match nonce with
		      | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		      | Some(h) ->
			  Printf.fprintf oc "Nonce: %s\n" (hashval_hexstring h);
			  match gamma with
			  | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			  | Some(gamma) ->
			      if payaddr_p gamma then
				let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair h thyh)) in
				Printf.fprintf oc "Publisher address: %s\n" (Cryptocurr.addr_pfgaddrstr gamma);
				Printf.fprintf oc "Marker Address: %s\n" (Cryptocurr.addr_pfgaddrstr beta);
				let (_,kl) = thy in
				let pname h =
				  try
				    Hashtbl.find prophrev h
				  with Not_found -> ""
				in
				List.iter
				  (fun pidpure ->
				    let pidthy = hashtag (hashopair2 (Some(thyh)) pidpure) 33l in
				    let alphapure = hashval_term_addr pidpure in
				    let alphathy = hashval_term_addr pidthy in
				    let nm = pname pidpure in
				    begin
				      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
				      match hlist_lookup_prop_owner true true true pidpure hl with
				      | None ->
					  begin
					    let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
					    let rstr =
					      try
						let (delta2,r) = Hashtbl.find proprightsh (false,pidpure) in
						match r with
						| None -> "no rights available (unusable)"
						| Some(0L) -> "free to use"
						| Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
					      with Not_found -> "free to use"
					    in
					    Printf.fprintf oc "Pure proposition '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
					  end;
					  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
					  if not (bl = []) then
					    begin
					      Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the pure prop:\n" (Cryptocurr.addr_pfgaddrstr alphapure);
					      List.iter
						(fun (bid,_,_,b) ->
						  match b with
						  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
						  | _ -> raise (Failure "impossible"))
						bl
					    end
				      | Some(beta,r) ->
					  Printf.fprintf oc "Pure proposition '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
					    (match r with
					    | None -> "No right to use without defining; must leave as theorem in the document"
					    | Some(r) ->
						if r = 0L then
						  "free to use; consider changing to Known without proof"
						else
						  (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
				    end;
				    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
				    begin
				      match hlist_lookup_prop_owner true true true pidthy hl with
				      | None ->
					  begin
					    let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
					    let rstr =
					      try
						let (delta2,r) = Hashtbl.find proprightsh (true,pidpure) in
						match r with
						| None -> "no rights available (unusable)"
						| Some(0L) -> "free to use"
						| Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
					      with Not_found -> "free to use"
					    in
					    Printf.fprintf oc "Proposition '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
					  end;
					  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
					  if not (bl = []) then
					    begin
					      Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the theory prop:\n" (Cryptocurr.addr_pfgaddrstr alphathy);
					      List.iter
						(fun (bid,_,_,b) ->
						  match b with
						  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
						  | _ -> raise (Failure "impossible"))
						bl
					    end
				      | Some(beta,r) ->
					  Printf.fprintf oc "Proposition '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
					    (match r with
					    | None -> "No right to use without defining; must leave as definition in the document"
					    | Some(r) ->
						if r = 0L then
						  "free to use; consider changing Thm to Known"
						else
						  (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
				    end)
				  kl;
			      else
				raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_signaspec seosb signaspec (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Signature is too big: %d bytes. It probably will not fit in a block. Split it into multiple signatures.\n" p;
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  let b = signaspec_burncost signaspec in
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "%s bars must be burned to publish signature.\n" (Cryptocurr.bars_of_atoms b);
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition '%s' %s at %s when checking. Unexpected case.\n"
			  nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n";
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (lr,tr,sr) = get_3roots (get_bestblock_print_warnings oc) in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,_,objhrev,_,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh) = input_doc ch th sgt in
	    begin
	      let p = let s = Buffer.create 100 in seosbf (seo_doc seosb dl (s,None)); String.length (Buffer.contents s) in
	      if p > 450000 then Printf.fprintf oc "Warning: Document is too big: %d bytes. It probably will not fit in a block. Split it into multiple documents.\n" p;
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_doc counter gvtp gvkn th thy sgt dl with
	      | None -> raise (Failure "Document does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashdoc dl) in
		  Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Document imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Document mentions %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),_) -> Printf.fprintf oc " '%s' %s\n" (oname h) (hashval_hexstring h)) tml;
		  Printf.fprintf oc "Document mentions %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = doc_uses_objs dl in
		  let usesprops = doc_uses_props dl in
		  let createsobjs = doc_creates_objs dl in
		  let createsprops = doc_creates_props dl in
		  let createsnegpropsaddrs2 = List.map (fun h -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) (doc_creates_neg_props dl) in
		  Printf.fprintf oc "Document uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | None -> "No right to use; document cannot be published unless this is redefined.\n"
			  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use; document cannot be published unless this is redefined.\n"
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
		      with Not_found ->
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Document uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s) Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | None -> "No right to use; document cannot be published unless this is reproven."
			  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use; document cannot be published unless this is reproven."
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
		      with Not_found ->
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  Printf.fprintf oc "Document creates %d objects:\n" (List.length createsobjs);
		  List.iter
		    (fun (h,k) ->
		      let oidpure = h in
		      let oidthy = hashtag (hashopair2 th (hashpair h k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
		      let nm = oname oidpure in
		      begin
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find objownsh oidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find objrightsh (false,oidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Pure object '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <defname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <defname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <defname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end
			| Some(beta,r) ->
			    Printf.fprintf oc "Pure object '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    (Printf.sprintf "free to use; consider changing Def to Param %s if the definition is not needed" (hashval_hexstring oidpure))
				  else
				    (Printf.sprintf "Using the object without defining it would cost %Ld atoms; consider changing Def to Param %s if the definition is not needed" r (hashval_hexstring oidpure)))
		      end;
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
		      begin
			match hlist_lookup_obj_owner true true true oidthy hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find objownsh oidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find objrightsh (true,oidpure) in
				  match r with
				  | None -> "no rights available (unusable)"
				  | Some(0L) -> "free to use"
				  | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Object '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <defname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <defname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <defname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end
			| Some(beta,r) ->
			    Printf.fprintf oc "Object '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    (Printf.sprintf "free to use; consider changing Def to Param %s if the definition is not needed" (hashval_hexstring oidpure))
				  else
				    (Printf.sprintf "Using the object without defining it would cost %Ld atoms; consider changing Def to Param %s if the definition is not needed" r (hashval_hexstring oidpure)))
		      end)
		    createsobjs;
		  Printf.fprintf oc "Document creates %d props:\n" (List.length createsprops);
		  List.iter
		    (fun h ->
		      let pidpure = h in
		      let pidthy = hashtag (hashopair2 th h) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
		      let nm = pname pidpure in
		      begin
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find proprightsh (false,pidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Pure proposition '%s' has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewPureRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end;
			    let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			    if not (bl = []) then
			      begin
				Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the pure prop:\n" (Cryptocurr.addr_pfgaddrstr alphapure);
				List.iter
				  (fun (bid,_,_,b) ->
				    match b with
				    | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				    | _ -> raise (Failure "impossible"))
				  bl
			      end
			| Some(beta,r) ->
			    Printf.fprintf oc "Pure proposition '%s' is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as theorem in the document"
			      | Some(r) ->
				  if r = 0L then
				    "free to use; consider changing to Known without proof"
				  else
				    (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
		      end;
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
		      begin
			match hlist_lookup_prop_owner true true true pidthy hl with
			| None ->
			    begin
			      let delta1str = try Printf.sprintf "address %s" (Cryptocurr.addr_pfgaddrstr (payaddr_addr (Hashtbl.find propownsh pidpure))) with Not_found -> "publisher address" in
			      let rstr =
				try
				  let (delta2,r) = Hashtbl.find proprightsh (true,pidpure) in
				  match r with
				   | None -> "no rights available (unusable)"
				   | Some(0L) -> "free to use"
				   | Some(x) -> Printf.sprintf "right for each use costs %Ld atoms (%s bars) payable to %s" x (Cryptocurr.bars_of_atoms x) (Cryptocurr.addr_pfgaddrstr (payaddr_addr delta2))
				  with Not_found -> "free to use"
			      in
			      Printf.fprintf oc "Proposition '%s' in theory has no owner.\nYou will be declared as the owner when the document is published with the following details:\nNew ownership: %s.\n (This can be changed prior to publication with NewOwner <propname> <payaddress>.)\nRights policy: %s\nThis can be changed prior to publication with\nNewRights <propname> <payaddress> [Free|None|<bars>]\nor\nNewTheoryRights <propname> <payaddress> [Free|None|<bars>]\n" nm delta1str rstr
			    end;
			    let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			    if not (bl = []) then
			      begin
				Printf.fprintf oc "There are bounties at %s you can claim by becoming the owner of the theory prop:\n" (Cryptocurr.addr_pfgaddrstr alphathy);
				List.iter
				  (fun (bid,_,_,b) ->
				    match b with
				    | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				    | _ -> raise (Failure "impossible"))
				  bl
			      end
			| Some(beta,r) ->
			    Printf.fprintf oc "Proposition '%s' in theory is owned by %s: %s\n" nm (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> "No right to use without defining; must leave as definition in the document"
			      | Some(r) ->
				  if r = 0L then
				    "free to use; consider changing Thm to Known"
				  else
				    (Printf.sprintf "Declaring the proposition as Known without proving it would cost %Ld atoms; consider this" r))
		      end)
		    createsprops;
		  Printf.fprintf oc "Document creates %d negprops:\n" (List.length createsnegpropsaddrs2);
		  List.iter
		    (fun alphathy ->
		      Printf.fprintf oc "%s\n" (addr_pfgaddrstr alphathy);
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
		      if hlist_lookup_neg_prop_owner true true true hl then
			Printf.fprintf oc "The negated proposition already has an owner.\n"
		      else
			begin
			  Printf.fprintf oc "Negated proposition has no owner.\nThe publisher address will be used to declare ownership of the negated proposition when publishing the document.\n";
			  let bl = hlist_filter_assets_gen true true (fun a -> match a with (_,_,_,Bounty(_)) -> true | _ -> false) hl in
			  if not (bl = []) then
			    begin
			      Printf.fprintf oc "There are bounties you can claim by becoming the owner of the negated prop:\n";
			      List.iter
				(fun (bid,_,_,b) ->
				  match b with
				  | Bounty(v) -> Printf.fprintf oc "Bounty %s bars (asset id %s)\n" (bars_of_atoms v) (hashval_hexstring bid)
				  | _ -> raise (Failure "impossible"))
				bl
			    end
			end)
		    createsnegpropsaddrs2;
                  Printf.fprintf oc "Conjecture theory addresses:\n";
                  Hashtbl.iter
                    (fun nm pureh ->
		      let pid = hashtag (hashopair2 th pureh) 33l in
                      Printf.fprintf oc "%s : %s\n" nm (addr_pfgaddrstr (hashval_term_addr pid)))
                    conjh;
		  let countbounties = ref 0 in
		  let totalbounties = ref 0L in
		  Hashtbl.iter
		    (fun _ (amt,_) ->
		      incr countbounties;
		      totalbounties := Int64.add amt !totalbounties)
		    bountyh;
		  if !countbounties > 0 then Printf.fprintf oc "%d new bounties worth a total of %s bars.\n" !countbounties (bars_of_atoms !totalbounties)
	    end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "commitdraft" "commitdraft <draftfile> <newtxfile>" "Form a transaction to publish a commitment for a draft file."
    (fun oc al ->
      match al with
      | [f;g] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  let mkcommittx blkh lr beta =
	    try
	      let (aid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
	      if Int64.add bday commitment_maturation_minus_one <= blkh then (** this means 12 confirmations **)
		Printf.fprintf oc "A commitment marker for this draft has already been published and matured.\nThe draft can be published with the publishdraft command.\n"
	      else
		Printf.fprintf oc "A commitment marker for this draft has already been published and will mature after %Ld more blocks.\nAfter that the draft can be published with the publishdraft command.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh )
	    with Not_found ->
	      try
		let minfee = Int64.mul 1000L !Config.defaulttxfee in (** very rough overestimate of 1K bytes for commitment tx **)
		let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh minfee in
		let txinl = [(alpha,aid)] in
		let txoutl =
		  if v >= Int64.add 10000L minfee then (** only create change if it is at least 10000 atoms ***)
		    [(alpha,(None,Currency(Int64.sub v minfee)));(beta,(None,Marker))]
		  else
		    [(beta,(None,Marker))]
		in
		let stau = ((txinl,txoutl),([],[])) in
		let c2 = open_out_bin g in
		begin
		  try
		    Commands.signtxc oc lr stau c2 [] [] None;
		    close_out_noerr c2;
		    Printf.fprintf oc "The commitment transaction (to publish the marker) was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
		  with e ->
		    close_out_noerr c2;
		    raise e
		end
	      with Not_found ->
		Printf.fprintf oc "Cannot find a spendable utxo to use to publish the marker.\n"
	  in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,_,_,_) = input_theoryspec ch in
            let counter = ref 0 in
	    begin
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      match get_bestblock_print_warnings oc with
		      | None -> Printf.fprintf oc "No blocks yet\n"
		      | Some(h,lbk,ltx) ->
			  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
			  let (_,_,lr,tr,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			  try
			    let tht = lookup_thytree tr in
			    let _ = ottree_lookup tht (Some(thyh)) in
			    Printf.fprintf oc "Theory %s has already been published.\n" (hashval_hexstring thyh)
			  with Not_found ->
			    match nonce with
			    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			    | Some(nonce) ->
				match gamma with
				| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
				| Some(gamma) ->
				    if payaddr_p gamma then
				      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce thyh)) in
				      mkcommittx blkh lr beta
				    else
				      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then
		    Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n"
		  else
		    match nonce with
		    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		    | Some(nonce) ->
			match gamma with
			| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			| Some(gamma) ->
			    if payaddr_p gamma then
			      let signaspech = hashsigna (signaspec_signa signaspec) in
			      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th signaspech))) in
			      mkcommittx blkh lr beta
			    else
			      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,_,_,_,_,_,_,_,_,_,_) = input_doc ch th sgt in
	    let doch = hashdoc dl in
	    let alphadoc = hashval_pub_addr (hashopair2 th doch) in
	    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphadoc) in
	    match hlist_lookup_asset_gen true true true (fun a -> match a with (_,_,_,DocPublication(_,_,_,_)) -> true | _ -> false) hl with
	    | Some(aid,_,_,_) ->
		Printf.fprintf oc "Document has already been published: address %s asset id %s\n" (Cryptocurr.addr_pfgaddrstr alphadoc) (hashval_hexstring aid)
	    | None ->
		begin
		  let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
		  let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
		  let refusecommit = ref false in
		  let gvtp th1 h1 a =
		    if th1 = th then
		      let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		      let alpha = hashval_term_addr oid in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		      match hlist_lookup_obj_owner true true true oid hl with
		      | None -> false
		      | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		    else
		      false
		  in
		  let gvkn th1 k =
		    if th1 = th then
		      let pid = hashtag (hashopair2 th k) 33l in
		      let alpha = hashval_term_addr pid in
		      let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		      match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		      | None -> false
		      | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		    else
		      false
		  in
                  let counter = ref 0 in
		  match Checking.check_doc counter gvtp gvkn th thy sgt dl with
		  | None -> raise (Failure "Document does not check.\n")
		  | Some(_) ->
		      let id = hashopair2 th (hashdoc dl) in
		      Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		      let usesobjs = doc_uses_objs dl in
		      let usesprops = doc_uses_props dl in
		      Printf.fprintf oc "Document uses %d objects:\n" (List.length usesobjs);
		      List.iter
			(fun (oidpure,k) ->
			  let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
			  let alphapure = hashval_term_addr oidpure in
			  let alphathy = hashval_term_addr oidthy in
			  try
			    let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			    Printf.fprintf oc "  Theory Object %s (%s) Owner %s: %s\n" (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> refusecommit := true; "No right to use; document cannot be published unless this is redefined.\n"
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			    match hlist_lookup_obj_owner true true true oidpure hl with
			    | None ->
				Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
				  (hashval_hexstring oidpure)
				  (addr_pfgaddrstr alphapure)
			    | Some(beta,r) ->
				Printf.fprintf oc "  Pure Object %s (%s) Owner %s: %s\n" (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
				  (addr_pfgaddrstr (payaddr_addr beta))
				  (match r with
				  | None -> refusecommit := true; "No right to use; document cannot be published unless this is redefined.\n"
				  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			  with Not_found ->
			    refusecommit := true;
			    Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			      (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
			usesobjs;
		      Printf.fprintf oc "Document uses %d props:\n" (List.length usesprops);
		      List.iter
			(fun pidpure ->
			  let pidthy = hashtag (hashopair2 th pidpure) 33l in
			  let alphapure = hashval_term_addr pidpure in
			  let alphathy = hashval_term_addr pidthy in
			  try
			    let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			    Printf.fprintf oc "  Theory Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | None -> refusecommit := true; "No right to use; document cannot be published unless this is reproven."
			      | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			    match hlist_lookup_prop_owner true true true pidpure hl with
			    | None ->
				Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
				  (hashval_hexstring pidpure)
				  (addr_pfgaddrstr alphapure)
			    | Some(beta,r) ->
				Printf.fprintf oc "  Pure Prop %s (%s) Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
				  (addr_pfgaddrstr (payaddr_addr beta))
				  (match r with
				  | None -> refusecommit := true; "No right to use; document cannot be published unless this is reproven."
				  | Some(r) -> if r = 0L then "free to use" else Printf.sprintf "each use costs %Ld atoms" r);
			  with Not_found ->
			    refusecommit := true;
			    Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			      (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
			usesprops;
		      if !refusecommit then
			Printf.fprintf oc "Refusing to commit to the draft until the issues above are resolved.\n"
		      else
			match nonce with
			| None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			| Some(nonce) ->
			    match gamma with
			    | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			    | Some(gamma) ->
				if payaddr_p gamma then
				  let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th doch))) in
				  mkcommittx blkh lr beta
				else
				  raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
		end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "publishdraft" "publishdraft <draftfile> <newtxfile>" "Form a transaction to publish a committed draft file."
    (fun oc al ->
      match al with
      | [f;g] ->
	  let ch = open_in f in
	  let l = input_token ch in
	  if l = "Theory" then
	    let (thyspec,nonce,gamma,_,_,propownsh,proprightsh) = input_theoryspec ch in
	    begin
              let counter = ref 0 in
	      match Checking.check_theoryspec counter thyspec with
	      | None -> raise (Failure "Theory spec does not check.\n")
	      | Some(thy,sg) ->
		  match hashtheory thy with
		  | None ->
		      Printf.fprintf oc "Theory is empty. It is correct but an empty theory is not allowed to be published.\n"
		  | Some(thyh) ->
		      match get_bestblock_print_warnings oc with
		      | None -> Printf.fprintf oc "No blocks yet\n"
		      | Some(h,lbk,ltx) ->
			  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
			  let (_,_,lr,tr,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			  try
			    let tht = lookup_thytree tr in
			    let _ = ottree_lookup tht (Some(thyh)) in
			    Printf.fprintf oc "Theory %s has already been published.\n" (hashval_hexstring thyh)
			  with Not_found ->
			    match nonce with
			    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
			    | Some(h) ->
				match gamma with
				| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
				| Some(gamma) ->
				    if payaddr_p gamma then
				      let gammap = let (i,x0,x1,x2,x3,x4) = gamma in (i = 1,x0,x1,x2,x3,x4) in
				      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair h thyh)) in
				      begin
					try
					  let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
					  try
					    if Int64.add bday commitment_maturation_minus_one <= blkh then
					      begin
						let b = theoryspec_burncost thyspec in
						try
						  let delta = hashval_pub_addr thyh in
						  let txoutl = [(delta,(None,TheoryPublication(gammap,h,thyspec)))] in
						  let txoutlr = ref txoutl in
						  let (_,kl) = thy in
						  List.iter
						    (fun h ->
                                                      let pidpure = h in
				                      let pidthy = hashtag (hashopair2 (Some(thyh)) pidpure) 33l in
				                      let alphapure = hashval_term_addr pidpure in
				                      let alphathy = hashval_term_addr pidthy in
						      let gamma1p =
							try
							  Hashtbl.find propownsh h
							with Not_found -> gammap
						      in
						      let (gamma2pp,rpp) =
							try
							  Hashtbl.find proprightsh (false,h)
							with Not_found -> (gamma1p,Some(0L))
						      in
						      let (gamma2tp,rtp) =
							try
							  Hashtbl.find proprightsh (true,h)
							with Not_found -> (gamma1p,Some(0L))
						      in
                                                      begin
				                        let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
				                        match hlist_lookup_prop_owner true true true pidpure hl with
                                                        | Some(_,_) -> () (** pure version already owned **)
				                        | None -> (** pure version not owned yet **)
						           txoutlr := (alphapure,(Some(gamma1p,0L,false),OwnsProp(pidpure,gamma2pp,rpp)))::!txoutlr
                                                      end;
                                                      (** the theory version cannot be previously owned unless the exact theory was already published, in which case the theory should not be republished **)
                                                      txoutlr := (alphathy,(Some(gamma1p,0L,false),OwnsProp(pidthy,gamma2tp,rtp)))::!txoutlr)
						    kl;
						  let esttxbytes = 2000 + stxsize (([],!txoutlr),([],[])) in (** rough overestimate for txin and signatures at 2000 bytes **)
						  let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
						  let minamt = Int64.add b minfee in
						  let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh minamt in
						  let change = Int64.sub v minamt in
						  if change >= 10000L then txoutlr := (alpha,(None,Currency(change)))::!txoutlr;
						  let txinl = [(alpha,aid);(beta,markerid)] in
						  let stau = ((txinl,!txoutlr),([],[])) in
						  let c2 = open_out_bin g in
						  begin
						    try
						      Commands.signtxc oc lr stau c2 [] [] None;
						      let p = pos_out c2 in
						      close_out_noerr c2;
						      if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
						      Printf.fprintf oc "The transaction to publish the theory was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
						    with e ->
						      close_out_noerr c2;
						      raise e
						  end
						with Not_found ->
						  Printf.fprintf oc "Cannot find a spendable utxo to use to publish the marker.\n"
					      end
					    else
					      Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
					  with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
					with Not_found ->
					  Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
				      end
				    else
				      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Signature" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (signaspec,nonce,gamma,_,objhrev,_,prophrev) = input_signaspec ch th sgt in
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_signaspec counter gvtp gvkn th thy sgt signaspec with
	      | None -> raise (Failure "Signature does not check.\n")
	      | Some((tml,knl),imported) ->
		  let id = hashopair2 th (hashsigna (signaspec_signa signaspec)) in
		  let delta = hashval_pub_addr id in
		  let hldelta = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq delta) in
		  if not (hldelta = HNil) then raise (Failure "Signature already seems to have been published.");
		  Printf.fprintf oc "Signature is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr (hashval_pub_addr id));
		  Printf.fprintf oc "Signature imports %d signatures:\n" (List.length imported);
		  List.iter (fun h -> Printf.fprintf oc " %s\n" (hashval_hexstring h)) imported;
		  let oname h =
		    try
		      Hashtbl.find objhrev h
		    with Not_found -> ""
		  in
		  let pname h =
		    try
		      Hashtbl.find prophrev h
		    with Not_found -> ""
		  in
		  Printf.fprintf oc "Signature exports %d objects:\n" (List.length tml);
		  List.iter (fun ((h,_),m) -> Printf.fprintf oc " '%s' %s %s\n" (oname h) (hashval_hexstring h) (match m with None -> "(opaque)" | Some(_) -> "(transparent)")) tml;
		  Printf.fprintf oc "Signature exports %d props:\n" (List.length knl);
		  List.iter (fun (h,_) -> Printf.fprintf oc " '%s' %s\n" (pname h) (hashval_hexstring h)) knl;
		  let usesobjs = signaspec_uses_objs signaspec in
		  let usesprops = signaspec_uses_props signaspec in
		  let refusesig = ref false in
		  Printf.fprintf oc "Signature uses %d objects:\n" (List.length usesobjs);
		  List.iter
		    (fun (oidpure,k) ->
		      let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
		      let alphapure = hashval_term_addr oidpure in
		      let alphathy = hashval_term_addr oidthy in
		      let nm = oname oidpure in
		      try
			let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
			Printf.fprintf oc " Theory Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_obj_owner true true true oidpure hl with
			| None ->
			    refusesig := true;
			    Printf.fprintf oc "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring oidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc " Pure Object '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you redefine the object or buy the object and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory object %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring oidthy) (addr_pfgaddrstr alphathy))
		    usesobjs;
		  Printf.fprintf oc "Signature uses %d props:\n" (List.length usesprops);
		  List.iter
		    (fun pidpure ->
		      let pidthy = hashtag (hashopair2 th pidpure) 33l in
		      let alphapure = hashval_term_addr pidpure in
		      let alphathy = hashval_term_addr pidthy in
		      let nm = pname pidpure in
		      try
			let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
			Printf.fprintf oc " Theory Prop '%s' %s (%s)\n  Owner %s: %s\n" nm (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy)
			  (addr_pfgaddrstr (payaddr_addr beta))
			  (match r with
			  | Some(0L) -> "free to use"
			  | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
			let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
			match hlist_lookup_prop_owner true true true pidpure hl with
			| None ->
			    Printf.fprintf oc "** Somehow the theory prop has an owner but the pure prop %s (%s) did not. Invariant failure. **\n"
			      (hashval_hexstring pidpure)
			      (addr_pfgaddrstr alphapure)
			| Some(beta,r) ->
			    Printf.fprintf oc "  Pure Prop %s (%s)\n  Owner %s: %s\n" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)
			      (addr_pfgaddrstr (payaddr_addr beta))
			      (match r with
			      | Some(0L) -> "free to use"
			      | _ -> refusesig := true; "not free to use; signature cannot be published unless you buy the proposition and make it free for everyone.");
		      with Not_found ->
			refusesig := true;
			Printf.fprintf oc "  Did not find owner of theory proposition %s at %s when checking. Unexpected case.\n"
			  (hashval_hexstring pidthy) (addr_pfgaddrstr alphathy))
		    usesprops;
		  if !refusesig then
		    Printf.fprintf oc "Cannot publish signature without resolving the issues above.\n"
		  else
		    match nonce with
		    | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		    | Some(nonce) ->
			match gamma with
			| None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
			| Some(gamma) ->
			    if payaddr_p gamma then
			      let gammap = let (i,x0,x1,x2,x3,x4) = gamma in (i = 1,x0,x1,x2,x3,x4) in
			      let signaspech = hashsigna (signaspec_signa signaspec) in
			      let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th signaspech))) in
			      begin
				try
				  let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
				  try
				    if Int64.add bday commitment_maturation_minus_one <= blkh then
				      begin
					let b = signaspec_burncost signaspec in
					let txinlr = ref [(beta,markerid)] in
					let txoutlr = ref [(delta,(None,SignaPublication(gammap,nonce,th,signaspec)))] in
					let esttxbytes = 2000 + stxsize (([],!txoutlr),([],[])) in (** rough overestimate for txin, possible change and signatures at 2000 bytes **)
					let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
					let tospend = ref (Int64.add b minfee) in
					try
					  let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
					  let tauin = (alpha,aid)::!txinlr in
					  let tauout = if Int64.sub v !tospend >= 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
					  let stau = ((tauin,tauout),([],[])) in
					  let c2 = open_out_bin g in
					  begin
					    try
					      Commands.signtxc oc lr stau c2 [] [] None;
					      let p = pos_out c2 in
					      close_out_noerr c2;
					      if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
					      Printf.fprintf oc "The transaction to publish the signature was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
					    with e ->
					      close_out_noerr c2;
					      raise e
					  end
					with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
				      end
				    else
				      Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
				  with Not_found -> Printf.fprintf oc "Not_found was raised while trying to construct the publication tx.\n"
				with Not_found ->
				  Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
			      end
			    else
			      raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else if l = "Document" then
	    let thyid = input_token ch in
	    let th = if thyid = "Empty" then None else Some(hexstring_hashval thyid) in
            let addrh : (payaddr,int64) Hashtbl.t = Hashtbl.create 10 in
	    let (blkh,lr,tr,sr) =
	      match get_bestblock_print_warnings oc with
	      | None -> raise Not_found
	      | Some(dbh,lbk,ltx) ->
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,_,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  (blkh,lr,tr,sr)
	    in
	    let tht = lookup_thytree tr in
	    let thy = try ottree_lookup tht th with Not_found -> raise (Failure (Printf.sprintf "Theory %s not found" thyid)) in
	    let sgt = lookup_sigtree sr in
	    let (dl,nonce,gamma,paramh,objhrev,proph,prophrev,conjh,objownsh,objrightsh,propownsh,proprightsh,bountyh) = input_doc ch th sgt in
	    let id = hashopair2 th (hashdoc dl) in
	    let delta = hashval_pub_addr id in
	    let hldelta = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq delta) in
	    if not (hldelta = HNil) then raise (Failure "Document already seems to have been published.");
	    begin
	      let remgvtpth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let remgvknth : (hashval,payaddr * int64 option) Hashtbl.t = Hashtbl.create 100 in
	      let gvtp th1 h1 a =
		if th1 = th then
		  let oid = hashtag (hashopair2 th (hashpair h1 (hashtp a))) 32l in
		  let alpha = hashval_term_addr oid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_obj_owner true true true oid hl with
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvtpth oid (beta,r); true
		else
		  false
	      in
	      let gvkn th1 k =
		if th1 = th then
		  let pid = hashtag (hashopair2 th k) 33l in
		  let alpha = hashval_term_addr pid in
		  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha) in
		  match hlist_lookup_prop_owner true true true pid hl with (*** A proposition has been proven in a theory iff it has an owner. ***)
		  | None -> false
		  | Some(beta,r) -> Hashtbl.add remgvknth pid (beta,r); true
		else
		  false
	      in
              let counter = ref 0 in
	      match Checking.check_doc counter gvtp gvkn th thy sgt dl with
	      | None -> raise (Failure "Document does not check.\n")
	      | Some(_) ->
		  Printf.fprintf oc "Document is correct and has id %s and address %s.\n" (hashval_hexstring id) (addr_pfgaddrstr delta);
		  match nonce with
		  | None -> Printf.fprintf oc "No nonce is given. Call addnonce to add one automatically.\n"
		  | Some(nonce) ->
		      match gamma with
		      | None -> Printf.fprintf oc "No publisher address. Call addpublisher to add one.\n"
		      | Some(gamma) ->
			  if payaddr_p gamma then
			    let gammap = let (i,x0,x1,x2,x3,x4) = gamma in (i = 1,x0,x1,x2,x3,x4) in
			    let doch = hashdoc dl in
			    let beta = hashval_pub_addr (hashpair (hashaddr gamma) (hashpair nonce (hashopair2 th doch))) in
			    begin
			      try
				let (markerid,bday,obl) = find_marker_at_address (CHash(lr)) beta in
				try
				  if Int64.add bday commitment_maturation_minus_one <= blkh then
				    begin
				      let tospend = ref 0L in
				      let al = ref [(markerid,bday,obl,Marker)] in
				      let txinlr = ref [(beta,markerid)] in
				      let txoutlr = ref [(delta,(None,DocPublication(gammap,nonce,th,dl)))] in
                                      let revisituses = ref [] in
				      let usesobjs = doc_uses_objs dl in
				      let usesprops = doc_uses_props dl in
				      let createsobjs = doc_creates_objs dl in
				      let createsprops = doc_creates_props dl in
				      let createsnegpropsaddrs2 = List.map (fun h -> hashval_term_addr (hashtag (hashopair2 th h) 33l)) (doc_creates_neg_props dl) in
				      let objrightsassets : (hashval,addr * asset) Hashtbl.t = Hashtbl.create 10 in
				      let proprightsassets : (hashval,addr * asset) Hashtbl.t = Hashtbl.create 10 in
				      List.iter
					(fun (alpha,a,v) ->
					  match a with
					  | (_,_,_,RightsObj(h,_)) -> Hashtbl.add objrightsassets h (alpha,a)
					  | (_,_,_,RightsProp(h,_)) -> Hashtbl.add proprightsassets h (alpha,a)
					  | _ -> ())
					(Commands.get_spendable_assets_in_ledger oc lr blkh);
				      let oname h =
					try
					  Hashtbl.find objhrev h
					with Not_found -> ""
				      in
				      let pname h =
					try
					  Hashtbl.find prophrev h
					with Not_found -> ""
				      in
				      List.iter
					(fun (oidpure,k) ->
					  let oidthy = hashtag (hashopair2 th (hashpair oidpure k)) 32l in
					  let alphapure = hashval_term_addr oidpure in
					  let alphathy = hashval_term_addr oidthy in
					  let (beta,r) = local_lookup_obj_thy_owner lr remgvtpth oidthy alphathy in
					  begin
					    match r with
					    | None -> raise (Failure (Printf.sprintf "No right to use theory object '%s' %s. It must be redefined." (oname oidpure) (hashval_hexstring oidthy)))
					    | Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
					       begin
                                                 revisituses := (false,oidthy,beta,i)::!revisituses;
                                                 if Hashtbl.mem objrightsassets oidthy then
                                                   begin
                                                     try
                                                       let i2 = Hashtbl.find addrh beta in
                                                       if i > i2 then Hashtbl.replace addrh beta i
                                                     with Not_found ->
                                                       Hashtbl.add addrh beta i
                                                   end
                                               end
					    | _ -> ()
					  end;
					  begin
					    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
					    match hlist_lookup_obj_owner true true true oidpure hl with
					    | None -> raise (Failure (Printf.sprintf "** Somehow the theory object has an owner but the pure object %s (%s) did not. Invariant failure. **" (hashval_hexstring oidpure) (addr_pfgaddrstr alphapure)))
					    | Some(beta,r) ->
						match r with
						| None -> raise (Failure (Printf.sprintf "No right to use pure object '%s' %s. It must be redefined." (oname oidpure) (hashval_hexstring oidpure)))
						| Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
					           begin
                                                     revisituses := (false,oidpure,beta,i)::!revisituses;
                                                     if Hashtbl.mem objrightsassets oidpure then
                                                       begin
                                                         try
                                                           let i2 = Hashtbl.find addrh beta in
                                                           if i > i2 then Hashtbl.replace addrh beta i
                                                         with Not_found ->
                                                           Hashtbl.add addrh beta i
                                                       end
                                                   end
						| _ -> ()
					  end)
					usesobjs;
				      List.iter
					(fun pidpure ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphapure = hashval_term_addr pidpure in
					  let alphathy = hashval_term_addr pidthy in
					  let (beta,r) = local_lookup_prop_thy_owner lr remgvknth pidthy alphathy in
					  begin
					    match r with
					    | None -> raise (Failure (Printf.sprintf "No right to use theory proposition '%s' %s. It must be reproven." (pname pidpure) (hashval_hexstring pidthy)))
					    | Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
						begin
                                                  revisituses := (true,pidthy,beta,i)::!revisituses;
                                                  if Hashtbl.mem proprightsassets pidthy then
                                                    begin
						      try
                                                        let i2 = Hashtbl.find addrh beta in
                                                        if i > i2 then Hashtbl.replace addrh beta i
                                                      with Not_found ->
                                                        Hashtbl.add addrh beta i
                                                    end
						end
					    | _ -> ()
					  end;
					  begin
					    let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
					    match hlist_lookup_prop_owner true true true pidpure hl with
					    | None -> raise (Failure (Printf.sprintf "** Somehow the theory proposition has an owner but the pure object %s (%s) did not. Invariant failure. **" (hashval_hexstring pidpure) (addr_pfgaddrstr alphapure)))
					    | Some(beta,r) ->
						match r with
						| None -> raise (Failure (Printf.sprintf "No right to use pure proposition '%s' %s. It must be reproven." (pname pidpure) (hashval_hexstring pidpure)))
						| Some(i) when i > 0L -> (*** look for owned rights; if not increase 'tospend' to buy the rights ***)
						   begin
                                                     revisituses := (true,pidpure,beta,i)::!revisituses;
                                                     if Hashtbl.mem proprightsassets pidpure then
                                                       begin
						         try
                                                           let i2 = Hashtbl.find addrh beta in
                                                           if i > i2 then Hashtbl.replace addrh beta i
                                                         with Not_found ->
                                                           Hashtbl.add addrh beta i
                                                       end
						   end
						| _ -> ()
					  end)
					usesprops;
                                      Hashtbl.iter
                                        (fun beta m ->
                                          tospend := Int64.add !tospend m;
                                          txoutlr := (payaddr_addr beta,(None,Currency(m)))::!txoutlr)
                                        addrh;
                                      List.iter
                                        (fun (b1,h1,beta1,i1) ->
                                          try
                                            let i2 = Hashtbl.find addrh beta1 in
                                            if i2 < i1 then raise Not_found;
                                          with Not_found ->
                                            try
                                              let (alpha,a) = Hashtbl.find (if b1 then proprightsassets else objrightsassets) h1 in
					      match a with
					      | (aid,bday,obl,RightsObj(h,r)) when not b1 ->
						 if r > 0L then
						   begin
						     al := a::!al;
						     txinlr := (alpha,aid)::!txinlr;
                                                     if r > 1L then txoutlr := (alpha,(obl,RightsObj(h,Int64.sub r 1L)))::!txoutlr;
                                                   end
                                                 else
                                                   raise Not_found
					      | (aid,bday,obl,RightsProp(h,r)) when b1 ->
						 if r > 0L then
						   begin
						     al := a::!al;
						     txinlr := (alpha,aid)::!txinlr;
                                                     if r > 1L then txoutlr := (alpha,(obl,RightsProp(h,Int64.sub r 1L)))::!txoutlr;
                                                   end
                                                 else
                                                   raise Not_found
                                              | _ ->
                                                 raise Not_found
                                            with Not_found ->
                                              raise (Failure (Printf.sprintf "Problem obtaining rights for %s" (hashval_hexstring h1))))
                                        !revisituses;
				      List.iter
					(fun (h,k) ->
					  let oidpure = h in
					  let oidthy = hashtag (hashopair2 th (hashpair h k)) 32l in
					  let alphapure = hashval_term_addr oidpure in
					  let alphathy = hashval_term_addr oidthy in
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
					  begin
					    match hlist_lookup_obj_owner true true true oidpure hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find objownsh oidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find objrightsh (false,oidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphapure,(Some(delta1,0L,false),OwnsObj(oidpure,delta2,r)))::!txoutlr
					  end;
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
					  begin
					    match hlist_lookup_obj_owner true true true oidthy hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find objownsh oidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find objrightsh (true,oidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphathy,(Some(delta1,0L,false),OwnsObj(oidthy,delta2,r)))::!txoutlr
					  end)
					createsobjs;
				      List.iter
					(fun pidpure ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphapure = hashval_term_addr pidpure in
					  let alphathy = hashval_term_addr pidthy in
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphapure) in
					  begin
					    match hlist_lookup_prop_owner true true true pidpure hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find propownsh pidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find proprightsh (false,pidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphapure,(Some(delta1,0L,false),OwnsProp(pidpure,delta2,r)))::!txoutlr
					  end;
					  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alphathy) in
					  begin
					    match hlist_lookup_prop_owner true true true pidthy hl with
					    | Some(_) -> ()
					    | None ->
						let delta1 = try Hashtbl.find propownsh pidpure with Not_found -> gammap in
						let (delta2,r) = try Hashtbl.find proprightsh (true,pidpure) with Not_found -> (gammap,Some(0L)) in
						txoutlr := (alphathy,(Some(delta1,0L,false),OwnsProp(pidthy,delta2,r)))::!txoutlr
					  end)
					createsprops;
				      List.iter
					(fun alpha -> txoutlr := (alpha,(Some(gammap,0L,false),OwnsNegProp))::!txoutlr)
					createsnegpropsaddrs2;
				      Hashtbl.iter
					(fun pidpure (amt,olkh) ->
					  let pidthy = hashtag (hashopair2 th pidpure) 33l in
					  let alphathy = hashval_term_addr pidthy in
					  tospend := Int64.add amt !tospend;
					  match olkh with
					  | None -> txoutlr := (alphathy,(None,Bounty(amt)))::!txoutlr
					  | Some(deltap,lkh) -> txoutlr := (alphathy,(Some(deltap,lkh,false),Bounty(amt)))::!txoutlr)
					bountyh;
				      try
					let esttxbytes = 2000 + stxsize ((!txinlr,!txoutlr),([],[])) + 200 * estimate_required_signatures !al (!txinlr,!txoutlr) in (** rough overestimate for funding asset, possible change and signature for the funding asset 2000 bytes; overestimate of 200 bytes per other signature **)
					let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
					tospend := Int64.add !tospend minfee;
					let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
					let tauin = (alpha,aid)::!txinlr in
					let tauout = if Int64.sub v !tospend > 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
					let stau = ((tauin,tauout),([],[])) in
					let c2 = open_out_bin g in
					begin
					  try
					    Commands.signtxc oc lr stau c2 [] [] None;
					    let p = pos_out c2 in
					    close_out_noerr c2;
					    if p > 450000 then Printf.fprintf oc "Warning: The transaction has %d bytes and may be too large to be confirmed in a block.\n" p;
					    Printf.fprintf oc "The transaction to publish the document was created.\nTo inspect it:\n> decodetxfile %s\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" g g g
					  with e ->
					    close_out_noerr c2;
					    raise e
					end
				      with Not_found -> Printf.fprintf oc "Could not find a utxo sufficient to fund publication tx.\n"
				    end
				  else
				    Printf.fprintf oc "The commitment will mature after %Ld more blocks.\nThe draft can only be published after the commitment matures.\n" (Int64.sub (Int64.add bday commitment_maturation_minus_one) blkh)
				with Not_found -> Printf.fprintf oc "Not_found was raised while trying to create the publication tx.\n"
			      with Not_found ->
				Printf.fprintf oc "No commitment marker for this draft found.\nUse commitdraft to create and publish a commitment marker.\n"
			    end
			  else
			    raise (Failure (Printf.sprintf "Publisher address %s is not a pay address." (Cryptocurr.addr_pfgaddrstr gamma)))
	    end
	  else
	    begin
	      close_in_noerr ch;
	      raise (Failure (Printf.sprintf "Draft file has incorrect header: %s" l))
	    end
      | _ -> raise BadCommandForm);
  ac "createbuyrightstx" "createbuyrightstx <payaddr> <num of rights> <id> ... <id>" "Create tx to buy rights for objects and/or propositions to be held at the given pay address."
    (fun oc al ->
      match al with
      | (beta::n::idl0) ->
         begin
           let beta = pfgaddrstr_addr beta in
           if not (payaddr_p beta) then raise BadCommandForm;
           let addrh : (payaddr,int64) Hashtbl.t = Hashtbl.create 10 in
           let n = Int64.of_string n in
           let idaddrl =
             List.map
               (fun h ->
                 let id1 = hexstring_hashval h in
                 let alpha1 = hashval_term_addr id1 in
                 (id1,alpha1))
               idl0
           in
           match get_bestblock_print_warnings oc with
           | None -> Printf.fprintf oc "No blocks yet\n"
           | Some(h,lbk,ltx) ->
	      let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	      let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
              List.iter
                (fun (id1,alpha1) ->
                  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha1) in
                  let al2 =
                    hlist_filter_assets_gen true true
                      (fun a ->
                        match a with
                        | (_,_,_,OwnsObj(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | (_,_,_,OwnsProp(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | _ -> false)
                      hl
                  in
                  List.iter
                    (fun a ->
                      match a with
                      | (_,_,_,OwnsObj(id2,gamma,Some(r))) ->
                         let rn = Int64.mul r n in
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             if rn > m then Hashtbl.replace addrh gamma rn
                           with Not_found ->
                             Hashtbl.add addrh gamma rn
                         end
                      | (_,_,_,OwnsProp(id2,gamma,Some(r))) ->
                         let rn = Int64.mul r n in
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             if rn > m then Hashtbl.replace addrh gamma rn
                           with Not_found ->
                             Hashtbl.add addrh gamma rn
                         end
                      | _ -> ())
                    al2)
                idaddrl;
              let tospend = ref 0L in
              let txoutlr = ref [] in
              Hashtbl.iter
                (fun gamma m ->
                  tospend := Int64.add !tospend m;
                  txoutlr := (payaddr_addr gamma,(None,Currency(m)))::!txoutlr)
                addrh;
              List.iter
                (fun (id1,alpha1) ->
                  let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq alpha1) in
                  let al2 =
                    hlist_filter_assets_gen true true
                      (fun a ->
                        match a with
                        | (_,_,_,OwnsObj(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | (_,_,_,OwnsProp(id2,_,Some(r))) when r > 0L && id2 = id1 -> true
                        | _ -> false)
                      hl
                  in
                  List.iter
                    (fun a ->
                      match a with
                      | (_,_,_,OwnsObj(id2,gamma,Some(r))) ->
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             let n2 = Int64.div m r in
                             txoutlr := (beta,(None,RightsObj(id2,n2)))::!txoutlr
                           with Not_found -> ()
                         end
                      | (_,_,_,OwnsProp(id2,gamma,Some(r))) ->
                         begin
                           try
                             let m = Hashtbl.find addrh gamma in
                             let n2 = Int64.div m r in
                             txoutlr := (beta,(None,RightsProp(id2,n2)))::!txoutlr
                           with Not_found -> ()
                         end
                      | _ -> ())
                    al2)
                idaddrl;
              let esttxbytes = 2000 + 200 * List.length !txoutlr in
              let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
              tospend := Int64.add !tospend minfee;
	      let (alpha,(aid,_,_,_),v) = find_spendable_utxo oc lr blkh !tospend in
	      let tauin = [(alpha,aid)] in
	      let tauout = if Int64.sub v !tospend > 10000L then (alpha,(None,Currency(Int64.sub v !tospend)))::!txoutlr else !txoutlr in
              let stau = ((tauin,tauout),([],[])) in
	      let s = Buffer.create 100 in
	      seosbf (seo_stx seosb stau (s,None));
              let hs = Hashaux.string_hexstring (Buffer.contents s) in
	      Printf.fprintf oc "%s\n" hs
         end
      | _ -> raise BadCommandForm);
  ac "missing" "missing" "Report current list of missing headers/deltas"
    (fun oc al ->
      Printf.fprintf oc "%d missing headers\n" (List.length !missingheaders);
      List.iter
	(fun (i,h) -> Printf.fprintf oc "%Ld %s\n" i (hashval_hexstring h))
	!missingheaders;
      Printf.fprintf oc "%d missing deltas\n" (List.length !missingdeltas);
      List.iter
	(fun (i,h) -> Printf.fprintf oc "%Ld %s\n" i (hashval_hexstring h))
	!missingdeltas;
      );
  ac "reportowned" "reportowned [<outputfile> [<ledgerroot>]]" "Give a report of all owned objects and propositions in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportowned oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportowned oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportowned oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "reportbounties" "reportbounties [<outputfile> [<ledgerroot>]]" "Give a report of all bounties in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportbounties oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportbounties oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportbounties oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "collectbounties" "collectbounties <outputaddress> <txfileout> [<ledgerroot>]" "Create a tx (stored in a file) paying all collectable bounties (if there are any) to the output address."
    (fun oc al ->
      let collb gammas fn lr =
	  let gamma = Cryptocurr.pfgaddrstr_addr gammas in
	  if not (payaddr_p gamma) then raise (Failure (Printf.sprintf "Address %s is not a pay address." gammas));
	  let cbl = Commands.collectable_bounties oc lr in
	  if cbl = [] then
	    Printf.fprintf oc "No bounties can be collected.\n"
	  else
	    let txinl = ref [] in
	    let txoutl = ref [] in
	    let vtot = ref 0L in
            let cnt = ref 0 in
	    List.iter
	      (fun (alpha,a1,a2) ->
		match (a1,a2) with
		| ((aid1,_,_,Bounty(v)),(aid2,_,obl2,pre2)) ->
		    vtot := Int64.add !vtot v;
		    txinl := (alpha,aid1)::!txinl;
		    if (!cnt < 50) && not (List.exists (fun (_,aid2b) -> aid2b = aid2) !txinl) then
		      begin
			txinl := (alpha,aid2)::!txinl;
			txoutl := (alpha,(obl2,pre2))::!txoutl;
                        incr cnt
		      end
		| _ -> ())
	      cbl;
	    let esttxbytes = 2000 + stxsize ((!txinl,!txoutl),([],[])) in
	    let minfee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
	    if !vtot < minfee then
	      Printf.fprintf oc "Total bounties are less than the tx fee, so refusing to make the tx.\n"
	    else
	      begin
		let totminusfee = Int64.sub !vtot minfee in
		txoutl := (gamma,(None,Currency(totminusfee)))::!txoutl;
		let stau = ((!txinl,!txoutl),([],[])) in
		let c2 = open_out_bin fn in
		begin
		  try
		    Commands.signtxc oc lr stau c2 [] [] None;
		    close_out_noerr c2;
		    Printf.fprintf oc "Transaction created to claim %s bars from bounties.\nTo validate it:\n> validatetxfile %s\nTo send it:\n> sendtxfile %s\n" (Cryptocurr.bars_of_atoms totminusfee) fn fn
		  with e ->
		    close_out_noerr c2;
		    raise e
		end
	      end
      in
      match al with
      | [gammas;fn] -> let lr = get_ledgerroot (get_bestblock_print_warnings oc) in collb gammas fn lr
      | [gammas;fn;lr] -> collb gammas fn (hexstring_hashval lr)
      | _ -> raise BadCommandForm);
  ac "reportpubs" "reportpubs [<outputfile> [<ledgerroot>]]" "Give a report of all publications in the ledger tree."
    (fun oc al ->
      match al with
      | [] ->
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  Commands.reportpubs oc oc lr
      | [fn] ->
	  let f = open_out fn in
	  let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
	  begin
	    try
	      Commands.reportpubs oc f lr;
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | [fn;lr] ->
	  let f = open_out fn in
	  begin
	    try
	      Commands.reportpubs oc f (hexstring_hashval lr);
	      close_out_noerr f
	    with exn -> close_out_noerr f; raise exn
	  end
      | _ -> raise BadCommandForm);
  ac "setbestblock" "setbestblock <blockid> [<blockheight> <ltcblockid> <ltcburntx>]" "Manually set the current best block. This is mostly useful if -ltcoffline is being used."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      let bh = DbBlockHeader.dbget h in
	      let (bhd,_) = bh in
	      begin
		try
		  let (lbk,ltx) = get_burn h in
		  artificialbestblock := Some(h,lbk,ltx);
		  artificialledgerroot := Some(bhd.newledgerroot)
		with Not_found ->
		  Printf.fprintf oc "Cannot find burn for block.\n"
	      end
	    with Not_found ->
	      Printf.fprintf oc "Unknown block.\n"
	  end
      | [a;lblk;ltx] ->
	  begin
	    let h = hexstring_hashval a in
	    let lblk = hexstring_md256 lblk in
	    let ltx = hexstring_md256 ltx in
	    artificialbestblock := Some(h,lblk,ltx);
	  end
      | [a;_;lblk;ltx] -> (*** ignore blkh (second argument), but leave this format for backwards compatibility ***)
	  begin
	    let h = hexstring_hashval a in
	    let lblk = hexstring_md256 lblk in
	    let ltx = hexstring_md256 ltx in
	    artificialbestblock := Some(h,lblk,ltx);
	  end
      | _ ->
	  raise BadCommandForm);
  ac "setledgerroot" "setledgerroot <ledgerroot or blockhash>" "Manually set the current ledger root, either by giving the ledger root (Merkle root of a ctree)\nor by giving the hash of a block containing the new ledger root."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      let (bhd,_) = DbBlockHeader.dbget h in
	      artificialledgerroot := Some(bhd.newledgerroot)
	    with Not_found ->
	      artificialledgerroot := Some(h)
	  end
      | _ -> raise BadCommandForm);
  ac "addresslocation" "addresslocation <address>"
    "Print the location of an address in the ledger tree as two numbers i:j with both between 0 and 511"
    (fun oc al ->
      match al with
      | [a] -> Commands.report_subtop_subsubtop oc (addr_bitseq (pfgaddrstr_addr a))
      | _ -> raise BadCommandForm);
  ac "verifyfullledger" "verifyfullledger [<ledgerroot>]" "Ensure the node has the full ledger with the given ledger root. This may take serveral hours."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    Commands.verifyfullledger oc h
	  end
      | [] ->
	  begin
	    try
	      let ledgerroot = get_ledgerroot (get_bestblock_print_warnings oc) in
	      Commands.verifyfullledger oc ledgerroot
	    with e ->
	      Printf.fprintf oc "Exception: %s\n" (Printexc.to_string e)
	  end
      | _ -> raise BadCommandForm);
  ac "requestfullledger" "requestfullledger [<ledgerroot>]" "try to request the full ledger from peers\nThis is an experimental command and can take several hours.\nCurrently it is more likely to be successful if the node already has most of the ledger.\nIf you have very little of the full ledger and you want it, consider downloading the initial full ledger from\nhttps://mega.nz/#!waQE1DiC!yRo9vTYPK9CZsfOxT-6eJ7vtl3WLeIMqK4LAcA2ASKc"
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    Commands.requestfullledger oc h
	  end
      | [] ->
	  begin
	    try
	      let ledgerroot = get_ledgerroot (get_bestblock_print_warnings oc) in
	      Commands.requestfullledger oc ledgerroot
	    with e ->
	      Printf.fprintf oc "Exception: %s\n" (Printexc.to_string e)
	  end
      | _ -> raise BadCommandForm);
  ac "requestblock" "requestblock <blockhash>" "Manually request a missing block from peers, if possible.\nThis is mostly useful if -ltcoffline is set.\nUnder normal operations proofgold will request the block when its hash is seen in the ltc burn tx."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let h = hexstring_hashval a in
	    try
	      if DbInvalidatedBlocks.dbexists h then DbInvalidatedBlocks.dbdelete h;
	      if DbBlacklist.dbexists h then DbBlacklist.dbdelete h;
	      if DbBlockHeader.dbexists h then
		Printf.fprintf oc "Already have header.\n"
	      else
		begin
		  find_and_send_requestdata GetHeader h;
		  Printf.fprintf oc "Block header requested.\n"
		end;
	      try
		if DbBlockDelta.dbexists h then
		  Printf.fprintf oc "Already have delta.\n"
		else
		  begin
		    find_and_send_requestdata GetBlockdelta h;
		    Printf.fprintf oc "Block delta requested.\n"
		  end
	      with Not_found ->
		Printf.fprintf oc "No peer has delta %s.\n" a
	    with Not_found ->
	      Printf.fprintf oc "No peer has header %s.\n" a
	  end
      | _ -> raise BadCommandForm);
  ac "originalrewardbountyprop" "originalrewardbountyprop <ltcblockid> <ltcburntxid> [format]" "Convert an ltc block id and ltc tx id (where the tx should be a burn tx confirmed in the block),\ncreate the corresponding proposition where a reward bounty would be placed.\nIf the format argument is given, then it can have the following values:\nassembly : give the conjecture in the assembly format proofgold can parse\nfof : try to give the conjecture as a first-order problem in the TPTP fof format\nthf : give the conjecture as a higher-order problem in the TPTP thf format\nThis alternativeversion of rewardbountyprop uses the original (buggy) algorithm\nbefore the emergency hard fork of August 30 2020.\n"
    (fun oc al ->
      let (lbk,ltx,formatval) =
        match al with
        | [lbk;ltx] -> (lbk,ltx,0)
        | [lbk;ltx;f] when f = "assembly" -> (lbk,ltx,1)
        | [lbk;ltx;f] when f = "fof" -> (lbk,ltx,2)
        | [lbk;ltx;f] when f = "thf" -> (lbk,ltx,3)
        | [lbk;ltx;f] when f = "mg" -> (lbk,ltx,256)
        | _ -> raise BadCommandForm
      in
      begin
	let lbk = hexstring_hashval lbk in
	let ltx = hexstring_hashval ltx in
        let h = hashpair lbk ltx in
        let (pc,p,q) = Checking.reward_bounty_prop 2214L h in (** q is the normalized version of p, where the bounty really goes, but p is what we show and can put into the document since it will be normalized anyway **) (** 2214 is a fake block height just to indicate we want the reward bounty prop before the August 30 2020 emergency hard fork **)
        let cls = (try (List.nth ["Random1";"Random2";"Random3";"QBF";"HOSetConstr";"HOUnif";"CombUnif";"AbstrHF";"DiophantineMod";"AIM1";"AIM2";"Diophantine"] pc) with _ -> "Unknown") in
	Printf.fprintf oc "%s\n" cls;
        if formatval = 0 then
          Printf.fprintf oc "%s\n" (if pc = 9 || pc = 10 then Checking.aim_trm_str p [] else if pc = 6 then Checking.comb_trm_str p [] else if pc = 7 then Checking.ahf_trm_str p [] else Checking.hf_trm_str p [])
        else if formatval = 1 then
          begin
            let bh : (int,string) Hashtbl.t = Hashtbl.create 1 in
            let trmh : (hashval,string) Hashtbl.t = Hashtbl.create 1 in
            let leth : (Logic.trm,string) Hashtbl.t = Hashtbl.create 10 in
            if not (cls = "QBF") then
              begin
                Hashtbl.add bh 0 "set";
                Printf.fprintf oc "Base set\n"
              end;
            decl_let_hfprims oc bh leth p;
            Printf.fprintf oc "Conj bountyprop : %s\n" (output_trm p bh trmh leth [])
          end
        else if formatval = 2 then
          begin
            if cls = "AbstrHF" then
              Checking.ahf_fof_prob oc p
            else if cls = "AIM1" then
              Checking.aim1_fof_prob oc p
            else if cls = "AIM2" then
              Checking.aim2_fof_prob oc p
            else if cls = "QBF" then
              Checking.qbf_fof_prob oc p
            else if cls = "CombUnif" then
              Checking.comb_fof_prob oc p
            else
              Printf.fprintf oc "Currently no implementation giving a TPTP fof problem for problems of class %s.\n" cls
          end
        else if formatval = 3 then
          Checking.hf_thf_prob oc p
        else if formatval = 256 then
          Checking.hf_mg_prob oc p;
        let pureid = tm_hashroot q in
        let inthyid = hashtag (hashopair2 (Some(Checking.hfthyid)) pureid) 33l in
        Printf.fprintf oc "Pure Id: %s\nId in Theory: %s\nAddress in Theory: %s\n" (hashval_hexstring pureid) (hashval_hexstring inthyid) (addr_pfgaddrstr (hashval_term_addr inthyid))
      end);
  ac "rewardbountyprop" "rewardbountyprop <ltcblockid> <ltcburntxid> [format]" "Convert an ltc block id and ltc tx id (where the tx should be a burn tx confirmed in the block),\ncreate the corresponding proposition where a reward bounty would be placed.\nIf the format argument is given, then it can have the following values:\nassembly : give the conjecture in the assembly format proofgold can parse\nfof : try to give the conjecture as a first-order problem in the TPTP fof format\nthf : give the conjecture as a higher-order problem in the TPTP thf format\n"
    (fun oc al ->
      let (lbk,ltx,formatval) =
        match al with
        | [lbk;ltx] -> (lbk,ltx,0)
        | [lbk;ltx;f] when f = "assembly" -> (lbk,ltx,1)
        | [lbk;ltx;f] when f = "fof" -> (lbk,ltx,2)
        | [lbk;ltx;f] when f = "thf" -> (lbk,ltx,3)
        | [lbk;ltx;f] when f = "mg" -> (lbk,ltx,256)
        | _ -> raise BadCommandForm
      in
      begin
	let lbk = hexstring_hashval lbk in
	let ltx = hexstring_hashval ltx in
        let h = hashpair lbk ltx in
        let (pc,p,q) = Checking.reward_bounty_prop 2216L h in (** q is the normalized version of p, where the bounty really goes, but p is what we show and can put into the document since it will be normalized anyway **) (** 2216 is a fake block height just to indicate we want the reward bounty prop after the August 30 2020 emergency hard fork **)
        let cls = (try (List.nth ["Random1";"Random2";"Random3";"QBF";"HOSetConstr";"HOUnif";"CombUnif";"AbstrHF";"DiophantineMod";"AIM1";"AIM2";"Diophantine"] pc) with _ -> "Unknown") in
	Printf.fprintf oc "%s\n" cls;
        if formatval = 0 then
          Printf.fprintf oc "%s\n" (if pc = 9 || pc = 10 then Checking.aim_trm_str p [] else if pc = 6 then Checking.comb_trm_str p [] else if pc = 7 then Checking.ahf_trm_str p [] else Checking.hf_trm_str p [])
        else if formatval = 1 then
          begin
            let bh : (int,string) Hashtbl.t = Hashtbl.create 1 in
            let trmh : (hashval,string) Hashtbl.t = Hashtbl.create 1 in
            let leth : (Logic.trm,string) Hashtbl.t = Hashtbl.create 10 in
            if not (cls = "QBF") then
              begin
                Hashtbl.add bh 0 "set";
                Printf.fprintf oc "Base set\n"
              end;
            decl_let_hfprims oc bh leth p;
            Printf.fprintf oc "Conj bountyprop : %s\n" (output_trm p bh trmh leth [])
          end
        else if formatval = 2 then
          begin
            if cls = "AbstrHF" then
              Checking.ahf_fof_prob oc p
            else if cls = "AIM1" then
              Checking.aim1_fof_prob oc p
            else if cls = "AIM2" then
              Checking.aim2_fof_prob oc p
            else if cls = "QBF" then
              Checking.qbf_fof_prob oc p
            else if cls = "CombUnif" then
              Checking.comb_fof_prob oc p
            else
              Printf.fprintf oc "Currently no implementation giving a TPTP fof problem for problems of class %s.\n" cls
          end
        else if formatval = 3 then
          Checking.hf_thf_prob oc p
        else if formatval = 256 then
          Checking.hf_mg_prob oc p;
        let pureid = tm_hashroot q in
        let inthyid = hashtag (hashopair2 (Some(Checking.hfthyid)) pureid) 33l in
        Printf.fprintf oc "Pure Id: %s\nId in Theory: %s\nAddress in Theory: %s\n" (hashval_hexstring pureid) (hashval_hexstring inthyid) (addr_pfgaddrstr (hashval_term_addr inthyid))
      end);
  ac "query" "query <hashval or address or int[block height]> [<blockid or ledgerroot>]" "Get information (in json format) about some item.\nThis is intended to support exporers.\nThe query command gives more detailed information if -extraindex is set to true."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let blkh = Int64.of_string h in
	      let j = Commands.query_blockheight blkh in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	    with Failure(_) ->
	      let j = Commands.query h in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	  end
      | [h;kh] ->
	  let k = hexstring_hashval kh in
	  begin
	    try
	      let (lbk,ltx) = get_burn k in
	      let (_,lmedtm,burned,(txid1,vout1),_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	      let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	      let pbh = Some(k,Poburn(lbk,ltx,lmedtm,burned,txid1,vout1)) in
	      let j = Commands.query_at_block h pbh lr blkh in
	      print_jsonval oc j;
	      Printf.fprintf oc "\n"
	    with Not_found ->
              if DbCTreeAtm.dbexists k then
		begin
		  let j = Commands.query_at_block h None k (-1L) in
		  print_jsonval oc j;
		  Printf.fprintf oc "\n"
		end
	      else if DbCTreeElt.dbexists k then
		begin
		  let j = Commands.query_at_block h None k (-1L) in
		  print_jsonval oc j;
		  Printf.fprintf oc "\n"
		end
	      else
		raise (Failure ("could not interpret " ^ kh ^ " as a block or ledger root"))
	  end
      | _ -> raise BadCommandForm);
  ac "filterwallet" "filterwallet [<ledgerroot>]" "Remove private keys/addresses not classified as fresh if they are empty.\nA backup of the old wallet is kept in the walletbkps directory."
    (fun oc al ->
      let lr =
        match al with
        | [] -> get_ledgerroot (get_bestblock_print_warnings oc)
        | [h] -> hexstring_hashval h
        | _ -> raise BadCommandForm
      in
      Commands.filter_wallet lr);
  ac "dumpwallet" "dumpwallet <filename>" "Dump the current wallet keys, addresses, etc., to a given file."
    (fun oc al ->
      match al with
      | [fn] -> Commands.dumpwallet fn
      | _ -> raise BadCommandForm);
  ac "ltcstatusdump" "ltcstatusdump [<filename> [<ltcblockhash> [<how many ltc blocks back>]]]" "Dump the proofgold information about the current ltc status to a given file."
    (fun oc al ->
      let (fn,blkh,howfarback) =
	match al with
	| [] -> ("ltcstatusdumpfile",hexstring_hashval (Ltcrpc.ltc_getbestblockhash ()),1000)
	| [fn] -> (fn,hexstring_hashval (Ltcrpc.ltc_getbestblockhash ()),1000)
	| [fn;hh] -> (fn,hexstring_hashval hh,1000)
	| [fn;hh;b] -> (fn,hexstring_hashval hh,int_of_string b)
	| _ -> raise BadCommandForm
      in
      let cblkh = ref blkh in
      let f = open_out fn in
      begin
	try
	  for i = 1 to howfarback do
	    Printf.fprintf f "%d. ltc block %s PfgStatus\n" i (hashval_hexstring !cblkh);
	    begin
	      try
		match DbLtcPfgStatus.dbget !cblkh with
		| LtcPfgStatusPrev(h) ->
		    Printf.fprintf f "  PfgStatus unchanged since ltc block %s\n" (hashval_hexstring h)
		| LtcPfgStatusNew(l) ->
		    Printf.fprintf f "  New PfgStatus:\n";
		    let cnt = ref 0 in
		    List.iter
		      (fun (dhght,li) ->
			let i = !cnt in
			incr cnt;
			match li with
			| [] -> Printf.fprintf f "   %d. Empty tip? Should not be possible. Dalilcoin height %Ld\n" i dhght;
			| ((bh,lbh,ltx,ltm,lhght)::r) ->
			    Printf.fprintf f " %Ld (%d) - Proofgold Block: %s\n        Litecoin Block: %s\n        Litecoin Burn Tx: %s\n        Litecoin Time: %Ld\n        Litecoin Height: %Ld\n" dhght i (hashval_hexstring bh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght;
			    List.iter (fun (bh,lbh,ltx,ltm,lhght) ->
			      Printf.fprintf f "       - Proofgold Block: %s\n        Litecoin Block: %s\n        Litecoin Burn Tx: %s\n        Litecoin Time: %Ld\n        Litecoin Height: %Ld\n" (hashval_hexstring bh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght)
			      r)
		      l
	      with Not_found ->
		Printf.fprintf f "  PfgStatus not found\n"
	    end;
	    begin
	      try
		let (prevh,tm,hght,burntxhs) = DbLtcBlock.dbget !cblkh in
		Printf.fprintf f "%d. ltc block %s info\n" i (hashval_hexstring !cblkh);
		Printf.fprintf f "   Previous %s\n   Block Time %Ld\n    Height %Ld\n" (hashval_hexstring prevh) tm hght;
		cblkh := prevh;
		match burntxhs with
		| [] -> ()
		| [x] -> Printf.fprintf f "    Burn Tx: %s\n" (hashval_hexstring x)
		| _ ->
		    Printf.fprintf f "    %d Burn Txs:\n" (List.length burntxhs);
		    List.iter (fun x -> Printf.fprintf f "         %s\n" (hashval_hexstring x)) burntxhs
	      with Not_found ->
		Printf.fprintf f "  LtcBlock not found\n"
	    end
	  done
	with e -> Printf.fprintf f "Exception: %s\n" (Printexc.to_string e)
      end;
      close_out_noerr f);
  ac "ltcstatus" "ltcstatus [<ltcblockhash>]" "Print the proofgold blocks burned into the ltc blockchain from the past week.\nThe topmost is the current best block."
    (fun oc al ->
      let h =
	match al with
	| [hh] -> hexstring_hashval hh
	| [] ->
	    Printf.fprintf oc "ltcbest %s\n" (hashval_hexstring !ltc_bestblock);
	    !ltc_bestblock
	| _ -> raise BadCommandForm
      in
      let (lastchangekey,zll) = ltcpfgstatus_dbget h in
      let tm = ltc_medtime() in
      if zll = [] && tm > Int64.add !Config.genesistimestamp 604800L then
	begin
	  Printf.fprintf oc "No blocks were created in the past week. Proofgold has reached terminal status.\nThe only recovery possible for the network is a hard fork.\nSometimes this message means the node is out of sync with ltc.\n"
	end;
      let i = ref 0 in
      List.iter
	(fun (dhght,zl) ->
	  incr i;
	  Printf.fprintf oc "%d [%Ld].\n" !i dhght;
	  List.iter
	    (fun (dbh,lbh,ltx,ltm,lhght) ->
	      if DbBlacklist.dbexists dbh then
		Printf.fprintf oc "- %s (blacklisted, presumably invalid) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	      else if DbInvalidatedBlocks.dbexists dbh then
		Printf.fprintf oc "- %s (marked invalid) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	      else
                let lh = hashpair lbh ltx in
                if Db_validblockvals.dbexists lh then
		  Printf.fprintf oc "+ %s %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	        else if Db_validheadervals.dbexists lh then
		  if DbBlockDelta.dbexists dbh then
		    Printf.fprintf oc "* %s (have delta, but not fully validated) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		  else
		    Printf.fprintf oc "* %s (missing delta) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
	        else
		  if DbBlockHeader.dbexists dbh then
		    if DbBlockDelta.dbexists dbh then
		      Printf.fprintf oc "* %s (have block, but neither header nor delta fully valided) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		    else
		      Printf.fprintf oc "* %s (missing delta, header not fully validated) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght
		  else
		    Printf.fprintf oc "* %s (missing header) %s %s %Ld %Ld\n" (hashval_hexstring dbh) (hashval_hexstring lbh) (hashval_hexstring ltx) ltm lhght)
	    zl)
	zll);
  ac "ltcgettxinfo" "ltcgettxinfo <txid>" "Get proofgold related information about an ltc burn tx."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let (burned,prev,nxt,lblkh,confs,_,_) = Ltcrpc.ltc_getburntransactioninfo h in
	      match lblkh,confs with
	      | Some(lh),Some(confs) ->
		  Printf.fprintf oc "burned %Ld prev %s next %s in ltc block %s, %d confirmations\n" burned (hashval_hexstring prev) (hashval_hexstring nxt) lh confs
	      | _,_ ->
		  Printf.fprintf oc "burned %Ld prev %s next %s\n" burned (hashval_hexstring prev) (hashval_hexstring nxt)
	    with Not_found -> raise (Failure("problem"))
	  end
      | _ -> raise BadCommandForm);
  ac "ltcgetbestblockhash" "ltcgetbestblockhash" "Get the current tip of the ltc blockchain."
    (fun oc al ->
      if al = [] then
	begin
	  try
	    let x = Ltcrpc.ltc_getbestblockhash () in
	    Printf.fprintf oc "best ltc block hash %s\n" x
	  with Not_found ->
	    Printf.fprintf oc "could not find best ltc block hash\n"
	end
      else
	raise BadCommandForm);
  ac "ltcgetblock" "ltcgetblock <blockid>" "Print proofgold related information about the given ltc block."
    (fun oc al ->
      match al with
      | [h] ->
	  begin
	    try
	      let (pbh,tm,hght,txl,_) = Ltcrpc.ltc_getblock h in
	      Printf.fprintf oc "ltc block %s time %Ld height %Ld prev %s; %d proofgold candidate txs:\n" h tm hght pbh (List.length txl);
	      List.iter (fun tx -> Printf.fprintf oc "%s\n" tx) txl
	    with Not_found ->
	      Printf.fprintf oc "could not find ltc block %s\n" h
	  end
      | _ -> raise BadCommandForm);
  ac "ltclistunspent" "ltclistunspent" "List the current relevant utxos in the local ltc wallet.\nThese utxos are used to fund ltc burn txs during the creation of proofgold blocks."
    (fun oc al ->
      if al = [] then
	begin
	  try
	    let utxol = Ltcrpc.ltc_listunspent () in
	    Printf.fprintf oc "%d ltc utxos\n" (List.length utxol);
	    List.iter
	      (fun u ->
		match u with
		| LtcP2shSegwit(txid,vout,ltcaddr,_,_,amt) ->
		    Printf.fprintf oc "%s:%d %Ld (%s [p2sh-segwit])\n" txid vout amt ltcaddr
		| LtcBech32(txid,vout,ltcaddr,_,amt) ->
		    Printf.fprintf oc "%s:%d %Ld (%s [bech32])\n" txid vout amt ltcaddr)
	      utxol
	  with Not_found ->
	    Printf.fprintf oc "could not get unspent ltc list\n"
	end
      else
	raise BadCommandForm);
  ac "ltcsigntx" "ltcsigntx <txinhex>" "Use the local ltc wallet to sign an ltc tx."
    (fun oc al ->
      match al with
      | [tx] -> Printf.fprintf oc "%s\n" (Ltcrpc.ltc_signrawtransaction tx)
      | _ -> raise BadCommandForm);
  ac "ltcsendtx" "ltcsendtx <txinhex>" "Use the local ltc wallet to send an ltc tx."
    (fun oc al ->
      match al with
      | [tx] -> Printf.fprintf oc "%s\n" (Ltcrpc.ltc_sendrawtransaction tx)
      | _ -> raise BadCommandForm);
  ac "ltccreateburn" "ltccreateburn <hash1> <hash2> <litoshis to burn>" "Manually create an ltc burn tx to support a newly staked proofgold block."
    (fun oc al ->
      match al with
      | [h1;h2;toburn] ->
	  begin
	    try
	      let txs = Ltcrpc.ltc_createburntx (hexstring_hashval h1) (hexstring_hashval h2) (Int64.of_string toburn) in
	      Printf.fprintf oc "burntx: %s\n" (Hashaux.string_hexstring txs)
	    with
	    | Ltcrpc.InsufficientLtcFunds ->
		Printf.fprintf oc "no ltc utxo has %s litoshis\n" toburn
	    | Not_found ->
		Printf.fprintf oc "trouble creating burn tx\n"
	  end
      | _ -> raise BadCommandForm);
  ac "exit" "exit" "exit or stop kills the proofgold node"
    (fun oc _ -> (*** Could call Thread.kill on netth and stkth, but Thread.kill is not always implemented. ***)
      Printf.fprintf oc "Shutting down threads. Please be patient.\n"; flush oc;
      closelog();
      !exitfn 0);
  ac "stop" "stop" "exit or stop kills the proofgold node"
    (fun oc _ -> (*** Could call Thread.kill on netth and stkth, but Thread.kill is not always implemented. ***)
      Printf.fprintf oc "Shutting down threads. Please be patient.\n"; flush oc;
      closelog();
      !exitfn 0);
  ac "dumpstate" "dumpstate <textfile>" "Dump the current proofgold state to a file for debugging."
    (fun oc al ->
      match al with
      | [fa] -> Commands.dumpstate fa
      | _ -> raise BadCommandForm);
  ac "broadcastbootstrap" "broadcastbootstrap <url>" "Use an ltc alert tx to broadcast a url from which bootstraps are available."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'B' msg in
             Printf.fprintf oc "Alert bootstrap url broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "broadcastbootstrapwarning" "broadcastbootstrapwarning <url>" "Use an ltc alert tx to broadcast a warning about a url from which bootstraps were alleged to be available."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'b' msg in
             Printf.fprintf oc "Alert bootstrap warning url broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "broadcastlistener" "broadcastlistener [<url>]" "Use an ltc alert tx to broadcast an ip or onion address for a listening node.\nIf no url is given, the value of onion or ip is used."
    (fun oc al ->
      let f msg =
        let l = String.length msg in
        if l < 70 then
          begin
            for i = 0 to l-1 do
              if Char.code msg.[i] > 127 then
                raise (Failure "Alert message must only contain ASCII characters")
            done;
            let ltctx = broadcast_alert_via_ltc 'L' msg in
            Printf.fprintf oc "Alert listener msg broadcast as ltc tx %s\n" ltctx
          end
        else
          raise (Failure "Alert message must have fewer than 70 ASCII characters")
      in
      match al with
      | [] ->
         begin
           match !Config.onion with
           | Some(onionaddr) ->
              let msg = Printf.sprintf "%s:%d" onionaddr !Config.onionremoteport in
              f msg
           | None ->
              match !Config.ip with
              | Some(ipaddr) ->
                 let msg = Printf.sprintf "%s:%d" ipaddr !Config.port in
                 f msg
              | None ->
                 raise (Failure "No listening url available")
         end
      | [url] -> f url
      | _ -> raise BadCommandForm);
  ac "broadcastalert" "broadcastalert <string>" "Use an ltc alert tx to broadcast an alert message for nodes. The message must contain fewer than 70 ASCII characters."
    (fun oc al ->
      match al with
      | [msg] ->
         let l = String.length msg in
         if l < 70 then
           begin
             for i = 0 to l-1 do
               if Char.code msg.[i] > 127 then
                 raise (Failure "Alert message must only contain ASCII characters")
             done;
             let ltctx = broadcast_alert_via_ltc 'A' msg in
             Printf.fprintf oc "Alert broadcast as ltc tx %s\n" ltctx
           end
         else
           raise (Failure "Alert message must have fewer than 70 ASCII characters")
      | _ -> raise BadCommandForm);
  ac "addnode" "addnode <address:port> [add|remove|onetry] [strength (for onetry)]" "Add or remove a peer by giving an address or port number.\nThe address may be an ip or an onion address."
    (fun oc al ->
      let addnode_add n =
	match tryconnectpeer n with
	| None -> raise (Failure "Failed to add node")
	| Some(lth,sth,(fd,sin,sout,gcs)) ->
	   match !gcs with
	   | None -> raise (Failure "Problem adding node")
	   | Some(cs) ->
	      if cs.addrfrom = "" then
                if cs.realaddr = "" then
                  ()
                else
		  addknownpeer (Int64.of_float cs.conntime) cs.realaddr
              else
		addknownpeer (Int64.of_float cs.conntime) cs.addrfrom
      in
      match al with
      | [n] -> addnode_add n
      | [n;"add"] -> addnode_add n
      | [n;"remove"] ->
          removeknownpeer n;
          List.iter
	    (fun (lth,sth,(fd,sin,sout,gcs)) -> if peeraddr !gcs = n then (shutdown_close fd; gcs := None))
	    !netconns
      | [n;"onetry"] ->
	  ignore (tryconnectpeer n)
      | [n;"onetry";str] ->
          reqstrength := Some(int_of_string str);
	  ignore (tryconnectpeer n)
      | _ -> raise BadCommandForm);
  ac "clearbanned" "clearbanned" "Clear the list of banned peers."
    (fun _ _ -> clearbanned());
  ac "listbanned" "listbanned" "List the current banned peers."
    (fun oc _ -> Hashtbl.iter (fun n () -> Printf.fprintf oc "%s\n" n) bannedpeers);
  ac "bannode" "bannode [<address:port>] ... [<address:port>]" "ban the given peers"
    (fun _ al -> List.iter (fun n -> banpeer n) al);
  ac "missingblocks" "missingblocks" "Print info about headers and deltas the node is missing.\nTypically a delta is only listed as missing after the header has been received and validated."
    (fun oc al ->
      Printf.fprintf oc "%d missing headers.\n" (List.length !missingheaders);
      List.iter (fun (h,k) -> Printf.fprintf oc "%Ld. %s\n" h (hashval_hexstring k)) !missingheaders;
      Printf.fprintf oc "%d missing deltas.\n" (List.length !missingdeltas);
      List.iter (fun (h,k) -> Printf.fprintf oc "%Ld. %s\n" h (hashval_hexstring k)) !missingdeltas);
  ac "getledgerroot" "getledgerroot" "Print the current ledger root."
    (fun oc al ->
      let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
      Printf.fprintf oc "Ledger root: %s\n" (hashval_hexstring lr));
  ac "getinfo" "getinfo" "Print a summary of the current proofgold node state including:\nnumber of connections, current best block, current difficulty, current balance."
    (fun oc al ->
      remove_dead_conns();
      let ll = List.length !netconns in
      Printf.fprintf oc "%d connection%s\n" ll (if ll = 1 then "" else "s");
      begin
	try
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "No blocks yet\n"
	    | Some(h,lbk,ltx) ->
		let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		let (tar,tmstmp,ledgerroot,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
		let gtm = Unix.gmtime (Int64.to_float tmstmp) in
		Printf.fprintf oc "Best block %s at height %Ld\n" (hashval_hexstring h) blkh;
		Printf.fprintf oc "Ledger root: %s\n" (hashval_hexstring ledgerroot);
		Printf.fprintf oc "Time: %Ld (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		Printf.fprintf oc "Target: %s\n" (string_of_big_int tar);
		Printf.fprintf oc "Difficulty: %s\n" (string_of_big_int (difficulty tar));
		let (bal1,bal1u,bal2,bal2u,bal3,bal3u,bal4,bal4u) = Commands.get_atoms_balances_in_ledger oc ledgerroot blkh in
		Printf.fprintf oc "Total p2pkh: %s bars (%s unlocked)\n" (bars_of_atoms bal1) (bars_of_atoms bal1u);
		Printf.fprintf oc "Total p2sh: %s bars (%s unlocked)\n" (bars_of_atoms bal2) (bars_of_atoms bal2u);
		Printf.fprintf oc "Total via endorsement: %s bars (%s unlocked)\n" (bars_of_atoms bal3) (bars_of_atoms bal3u);
		Printf.fprintf oc "Total watched: %s bars (%s unlocked)\n" (bars_of_atoms bal4)  (bars_of_atoms bal4u);
		Printf.fprintf oc "Sum of all: %s bars (%s unlocked)\n"
		  (bars_of_atoms (Int64.add bal1 (Int64.add bal2 (Int64.add bal3 bal4))))
		  (bars_of_atoms (Int64.add bal1u (Int64.add bal2u (Int64.add bal3u bal4u))))
	  end;
	with e ->
	  Printf.fprintf oc "Exception: %s\n" (Printexc.to_string e)
      end);
  ac "getpeerinfo" "getpeerinfo" "List the current peers and when the last message was received from each."
    (fun oc al ->
      remove_dead_conns();
      let ll = List.length !netconns in
      Printf.fprintf oc "%d connection%s\n" ll (if ll = 1 then "" else "s");
      List.iter
	(fun (_,_,(_,_,_,gcs)) ->
	  match !gcs with
	  | Some(cs) ->
	      Printf.fprintf oc "%s (%s): %s\n" cs.realaddr cs.addrfrom cs.useragent;
	      let snc1 = sincetime (Int64.of_float cs.conntime) in
	      let snc2 = sincetime (Int64.of_float cs.lastmsgtm) in
	      Printf.fprintf oc "Connected for %s; last message %s ago.\n" snc1 snc2;
              begin
                match cs.strength with
                | Some(str) -> Printf.fprintf oc "Strength %d POW target %ld\n" str cs.powtarget
                | None -> ()
              end;
	      if cs.handshakestep < 5 then Printf.fprintf oc "(Still in handshake phase)\n";
              if not (cs.powchallenge = None) then Printf.fprintf oc "(outstanding POW challenge)\n";
	  | None -> (*** This could happen if a connection died after remove_dead_conns above. ***)
	      Printf.fprintf oc "[Dead Connection]\n";
	)
	!netconns;
      flush oc);
  ac "nettime" "nettime" "Print the current network time (median of peers) and skew from local node."
    (fun oc al ->
      let (tm,skew) = network_time() in
      Printf.fprintf oc "network time %Ld (median skew of %d)\n" tm skew;
      flush oc);
  ac "invalidateblock" "invalidateblock <blockhash>" "Manually invalidate a proofgold block\nThis should be used if someone is attacking the network and nodes decide to ignore their blocks."
    (fun oc al ->
      match al with
      | [h] ->
	  let hh = hexstring_hashval h in
	  recursively_invalidate_blocks hh
      | _ -> raise BadCommandForm);
  ac "revalidateblock" "revalidateblock <blockhash>" "Manually mark a previously manually invalidated block as being valid.\nThis will also mark the previous blocks as valid."
    (fun oc al ->
      match al with
      | [h] ->
	  let hh = hexstring_hashval h in
	  recursively_revalidate_blocks hh
      | _ -> raise BadCommandForm);
  ac "rawblockheader" "rawblockheader <blockhash>" "Print the given block header in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bh = DbBlockHeader.dbget h in
	      let sb = Buffer.create 1000 in
	      seosbf (seo_blockheader seosb bh (sb,None));
	      let s = string_hexstring (Buffer.contents sb) in
	      Printf.fprintf oc "%s\n" s;
	    with Not_found ->
	      Printf.fprintf oc "Could not find header %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "rawblockdelta" "rawblockdelta <blockid>" "Print the given block delta in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bd = DbBlockDelta.dbget h in
	      let sb = Buffer.create 1000 in
	      seosbf (seo_blockdelta seosb bd (sb,None));
	      let s = string_hexstring (Buffer.contents sb) in
	      Printf.fprintf oc "%s\n" s;
	    with Not_found ->
	      Printf.fprintf oc "Could not find delta %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "rawblock" "rawblock <blockid>" "Print the block (header and delta) in hex."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let bh = DbBlockHeader.dbget h in
	      try
		let bd = DbBlockDelta.dbget h in
		let sb = Buffer.create 1000 in
		seosbf (seo_block seosb (bh,bd) (sb,None));
		let s = string_hexstring (Buffer.contents sb) in
		Printf.fprintf oc "%s\n" s;
	      with Not_found ->
		Printf.fprintf oc "Could not find delta %s\n" hh
	    with Not_found ->
	      Printf.fprintf oc "Could not find header %s\n" hh
	  end
      | _ -> raise BadCommandForm);
  ac "getblock" "getblock <blockhash>" "Print information about the block, or request it from a peer if it is missing."
    (fun oc al ->
      match al with
      | [hh] ->
	  begin
	    let h = hexstring_hashval hh in
	    try
	      let (bhd,_) = DbBlockHeader.dbget h in
	      Printf.fprintf oc "Time: %Ld\n" bhd.timestamp;
	      begin
		try
		  let bd = DbBlockDelta.dbget h in
		  Printf.fprintf oc "%d txs\n" (List.length (bd.blockdelta_stxl));
		  List.iter (fun (tx,txs) -> Printf.fprintf oc "%s\n" (hashval_hexstring (hashtx tx))) (bd.blockdelta_stxl);
		with Not_found ->
		  find_and_send_requestdata GetBlockdelta h;
		  Printf.fprintf oc "Missing block delta\n"
	      end
	    with Not_found ->
	      find_and_send_requestdata GetHeader h
	  end
      | _ -> raise BadCommandForm);
  ac "nextstakingchances" "nextstakingchances [<hours> [<max ltc to burn> [<blockid>]]" "Print chances for the node to stake\nincluding chances if the node were to hypothetically burn some ltc (see extraburn).\nBy default nextstakingchances checks for every chance from the time of the previous block to 4 hours in the future."
    (fun oc al ->
      let (scnds,maxburn,n) =
	match al with
	| [] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * 4,100000000L,n)
	| [hrs] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * (int_of_string hrs),100000000L,n)
	| [hrs;maxburn] ->
	    let n = get_bestblock_print_warnings oc in
	    (3600 * (int_of_string hrs),litoshis_of_ltc maxburn,n)
	| [hrs;maxburn;blockid] ->
	    begin
	      try
		let k = hexstring_hashval blockid in
		let (lbk,ltx) = get_burn k in
		(3600 * (int_of_string hrs),litoshis_of_ltc maxburn,Some(k,lbk,ltx))
	      with Not_found ->
		raise (Failure ("unknown block " ^ blockid))
	    end
	| _ -> raise BadCommandForm
      in
      begin
	let nw = ltc_medtime() in (*** for staking purposes, ltc is the clock to follow ***)
	let fromnow_string i nw =
	  if i <= nw then
	    "now"
	  else
	    let del = Int64.to_int (Int64.sub i nw) in
	    if del < 60 then
	      Printf.sprintf "%d seconds from now" del
	    else if del < 3600 then
	      Printf.sprintf "%d minutes %d seconds from now" (del / 60) (del mod 60)
	    else
	      Printf.sprintf "%d hours %d minutes %d seconds from now" (del / 3600) ((del mod 3600) / 60) (del mod 60)
	in
	match n with
	| None ->
           begin
             if nw > Int64.add !Config.genesistimestamp 86400L then
               raise (Failure ("could not find block"))
             else
               begin
                 compute_genesis_staking_chances !Config.genesistimestamp (min (Int64.add !Config.genesistimestamp 86400L) (Int64.add nw (Int64.of_int scnds)));
                 begin
	           try
		     match !genesisstakechances with
                     | Some(NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_)) ->
                        Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		     | Some(NextStake(_,_,_,_,_,_,_,_,_,_,_,_)) -> () (*** should not happen; ignore **)
		     | Some(NoStakeUpTo(_)) -> Printf.fprintf oc "Found no chance to stake with current wallet and ltc burn limits.\n"
                     | None -> raise Not_found
	           with Not_found -> ()
	         end;
	         List.iter
	           (fun z ->
		     let il = ref [] in
		     match z with
                     | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                        Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		     | NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		        if not (List.mem i !il) then
		          begin
			    il := i::!il; (** while the info should not be on the hash table more than once, sometimes it is, so only report it once **)
			    Printf.fprintf oc "With extraburn %Ld litoshis (%s ltc), could stake at time %Ld (%s) with asset %s at address %s.\n" toburn (ltc_of_litoshis toburn) i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr))
		          end
		     | _ -> ())
	           (List.sort
		      (fun y z ->
                        let tmstkch y =
                          match y with
                          | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> i
		          | NextStake(i,_,_,_,_,_,Some(_),_,_,_,_,_) -> i
		          | _ -> 0L
                        in
                        compare (tmstkch y) (tmstkch z))
		      (List.filter
		         (fun z ->
		           match z with
                           | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> true
		           | _ -> false)
		         !genesisstakechances_hypo))
               end
           end
	| Some(dbh,lbk,ltx) ->
	    let (_,tmstmp,_,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    Printf.fprintf oc "Trying to stake on top of %s with time stamp %Ld ltc block %s ltc burn tx %s\n" (hashval_hexstring dbh) tmstmp (hashval_hexstring lbk) (hashval_hexstring ltx);
	    compute_staking_chances (dbh,lbk,ltx) tmstmp (min (Int64.add tmstmp 604800L) (Int64.add nw (Int64.of_int scnds)));
	    begin
	      try
		match Hashtbl.find nextstakechances (lbk,ltx) with
                | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                   Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		    Printf.fprintf oc "Can stake at time %Ld (%s) with asset %s at address %s burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr)) toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,None,_,_,_,_,_) -> () (*** should not happen; ignore ***)
		| NoStakeUpTo(_) -> Printf.fprintf oc "Found no chance to stake with current wallet and ltc burn limits.\n"
	      with Not_found -> ()
	    end;
	    List.iter
	      (fun z ->
		let il = ref [] in
		match z with
                | NextPureBurn(i,lutxo,txidh,vout,toburn,_,_,_,_,_) ->
                   Printf.fprintf oc "Can stake at time %Ld (%s) with utxo %s:%d burning %Ld litoshis (%s ltc).\n" i (fromnow_string i nw) (hashval_hexstring txidh) vout toburn (ltc_of_litoshis toburn);
		| NextStake(i,stkaddr,h,bday,obl,v,Some(toburn),_,_,_,_,_) ->
		    if not (List.mem i !il) then
		      begin
			il := i::!il; (** while the info should not be on the hash table more than once, sometimes it is, so only report it once **)
			Printf.fprintf oc "With extraburn %Ld litoshis (%s ltc), could stake at time %Ld (%s) with asset %s at address %s.\n" toburn (ltc_of_litoshis toburn) i (fromnow_string i nw) (hashval_hexstring h) (addr_pfgaddrstr (p2pkhaddr_addr stkaddr))
		      end
		| _ -> ())
	      (List.sort
		 (fun y z ->
                   let tmstkch y =
                     match y with
                     | NextPureBurn(i,_,_,_,_,_,_,_,_,_) -> i
		     | NextStake(i,_,_,_,_,_,Some(_),_,_,_,_,_) -> i
		     | _ -> 0L
                   in
                   compare (tmstkch y) (tmstkch z))
		 (List.filter
		    (fun z ->
		      match z with
                      | NextPureBurn(_,_,_,_,_,_,_,_,_,_) -> true
		      | NextStake(_,_,_,_,_,_,Some(_),_,_,_,_,_) -> true
		      | _ -> false)
		    (Hashtbl.find_all nextstakechances_hypo (lbk,ltx))))
       end);
  ac "extraburn" "extraburn <ltc> or extraburn <litoshis> litoshis" "Order the node to burn up to the given amount of ltc given a chance to stake\nby doing the burn (see nextstakingchances)."
    (fun oc al ->
      match al with
      | [a] -> (extraburn := litoshis_of_ltc a; Hashtbl.clear nextstakechances)
      | [a;b] when b = "litoshis" -> (extraburn := Int64.of_string a; Hashtbl.clear nextstakechances)
      | _ -> raise BadCommandForm);
  ac "printassets" "printassets [<ledgerroot>] [<height>]" "Print the assets (in given ledger root assuming given block height).\nBy default the ledger root and height of the current best block is used."
    (fun oc al ->
      match al with
      | [] -> Commands.printassets oc
      | [lr;hght] -> Commands.printassets_in_ledger oc (hexstring_hashval lr) (Int64.of_string hght)
      | [lr] ->
	  begin
	    let n = get_bestblock_print_warnings oc in
	    match n with
	    | None -> raise (Failure ("could not find block"))
	    | Some(_,lbk,ltx) ->
		let (_,_,_,_,_,_,hght) = Db_outlinevals.dbget (hashpair lbk ltx) in
		Commands.printassets_in_ledger oc (hexstring_hashval lr) hght
	  end
      | _ -> raise BadCommandForm);
  ac "printtx" "printtx <txid> [<txid>] ... [<txid>]" "Print info about the given txs."
    (fun oc al -> List.iter (fun h -> Commands.printtx oc (hexstring_hashval h)) al);
  ac "importwallet" "importwallet <walletfile>" "Imports the entries from a wallet file into the current wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importwallet oc w
      | _ -> raise BadCommandForm);
  ac "importprivkey" "importprivkey <WIFkey> [staking|nonstaking|staking_fresh|nonstaking_fresh]" "Import a private key for a p2pkh address into the wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importprivkey oc w "staking"
      | [w;cls] -> Commands.importprivkey oc w cls
      | _ -> raise BadCommandForm);
  ac "importbtcprivkey" "importbtcprivkey <btcWIFkey> [staking|nonstaking|staking_fresh|nonstaking_fresh]" "Import a btc private key for a p2pkh address into the wallet."
    (fun oc al ->
      match al with
      | [w] -> Commands.importbtcprivkey oc w "staking"
      | [w;cls] -> Commands.importbtcprivkey oc w cls
      | _ -> raise BadCommandForm);
  ac "importwatchaddr" "importwatchaddr <address> [offlinekey|offlinekey_fresh]" "Import a proofgold address to watch.\nofflinekey or offlinekey_fresh indicates that the user has the private key offline.\nofflinekey_fresh tells proofgold to use the address when it needs a fresh address controlled offline (e.g. for staking rewards)"
    (fun oc al ->
      match al with
      | [a] -> Commands.importwatchaddr oc a ""
      | [a;cls] ->
	  if cls = "offlinekey" || cls = "offlinekey_fresh" then
	    Commands.importwatchaddr oc a cls
	  else
	    raise BadCommandForm
      | _ -> raise BadCommandForm);
  ac "importwatchbtcaddr" "importwatchbtcaddr <address> [offlinekey|offlinekey_fresh]" "Import a proofgold address to watch by giving it as a bitcoin address.\nofflinekey or offlinekey_fresh indicates that the user has the private key offline.\nofflinekey_fresh tells proofgold to use the address when it needs a fresh address controlled offline (e.g. for staking rewards)"
    (fun oc al ->
      match al with
      | [a] -> Commands.importwatchbtcaddr oc a ""
      | [a;cls] ->
	  if cls = "offlinekey" || cls = "offlinekey_fresh" then
	    Commands.importwatchbtcaddr oc a cls
	  else
	    raise BadCommandForm
      | _ -> raise BadCommandForm);
  ac "importendorsement" "importendorsement <address> <address> <signature>" "Import a bitcoin signed endorsement message into the proofgold wallet.\nimportendorsement should be given three arguments: a b s where s is a signature made with the private key for address a endorsing to address b"
    (fun oc al ->
      match al with
      | [a;b;s] -> Commands.importendorsement oc a b s
      | _ -> raise BadCommandForm);
  ac "btctopfgaddr" "btctopfgaddr <btcaddress> [<btcaddress>] .. [<btcaddress>]" "Print the proofgold addresses corresponding to the given btc addresses."
    (fun oc al -> List.iter (Commands.btctopfgaddr oc) al);
  ac "printasset" "printasset <assethash>" "print information about the given asset"
    (fun oc al ->
      match al with
      | [h] -> Commands.printasset oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printhconselt" "printhconselt <hashval>" "Print information about the given hconselt, which is an asset possibly followed by a hash referencing more assets."
    (fun oc al ->
      match al with
      | [h] -> Commands.printhconselt oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeatm" "printctreeatm <hashval>" "Print information about a ctree atom with the given Merkle root."
    (fun oc al ->
      match al with
      | [h] -> Commands.printctreeatm oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeelt" "printctreeelt <hashval>" "Print information about a ctree element with the given Merkle root."
    (fun oc al ->
      match al with
      | [h] -> Commands.printctreeelt oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "printctreeinfo" "printctreeinfo [ledgerroot]" "Print info about a ctree with the given Merkle root."
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  Commands.printctreeinfo oc currledgerroot
      | [h] -> Commands.printctreeinfo oc (hexstring_hashval h)
      | _ -> raise BadCommandForm);
  ac "exportctreeelts" "exportctreeelts <new file to save binary ctree> <ledgerroot> <subtop[0-511]> [<subsubtop[0-511]>]"
    "Export a ctree as elements into a binary file.\nThe root of the tree must be given and either a subtop or a subtop and subsubtop.\nOnly the relevant subtrees are saved, with the others abbreviated by hashes."
    (fun oc al ->
      match al with
      | [f;lr;subtop] ->
	  let c = open_out_bin f in
	  export_ctree_subtop c (hexstring_hashval lr) (int_of_string subtop);
	  close_out_noerr c
      | [f;lr;subtop;subsubtop] ->
	  let c = open_out_bin f in
	  export_ctree_subtop_subsubtop c (hexstring_hashval lr) (int_of_string subtop) (int_of_string subsubtop);
	  close_out_noerr c
      | _ -> raise BadCommandForm);
  ac "importctreeelts" "importctreeelts <binary file with a ctree> <ledgerroot>"
    "Read a elements of a ctree (ledger tree) from a file and save them in the local database."
    (fun oc al ->
      match al with
      | [f;lr] ->
	  let lr = hexstring_hashval lr in
	  let c = open_in_bin f in
	  let (m,n) = import_ctree_subelts c lr in
	  close_in_noerr c;
	  Printf.fprintf oc "Finished importing elements of ctree with root %s: read %d and saved %d as new.\n" (hashval_hexstring lr) m n
      | _ -> raise BadCommandForm);
  ac "newofflineaddress" "newofflineaddress" "Find an address in the watch wallet that was marked as offlinekey and fresh.\nPrint it and mark it as no longer fresh."
    (fun oc al ->
      let alpha = Commands.get_fresh_offline_address oc in
      Printf.fprintf oc "%s\n" (addr_pfgaddrstr alpha));
  ac "newaddress" "newaddress [ledgerroot]" "If there is a key in the wallet classified as nonstaking_fresh, then print it and mark it as no longer fresh.\nOtherwise randomly generate a key, import the key into the wallet (as nonstaking) and print the correponding address.\nThe ledger root is used to ensure that the address is really empty (or was empty, given an old ledgerroot).\nSee also: newstakingaddress"
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  let (k,h) = Commands.generate_newkeyandaddress currledgerroot "nonstaking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | [clr] ->
	  let (k,h) = Commands.generate_newkeyandaddress (hexstring_hashval clr) "nonstaking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | _ -> raise BadCommandForm);
  ac "newstakingaddress" "newstakingaddress [ledgerroot]" "If there is a key in the wallet classified as staking_fresh, then print it and mark it as no longer fresh.\nOtherwise randomly generate a key, import the key into the wallet (as staking) and print the correponding address.\nThe ledger root is used to ensure that the address is really empty (or was empty, given an old ledgerroot).\nSee also: newaddress"
    (fun oc al ->
      match al with
      | [] ->
	  let best = get_bestblock_print_warnings oc in
	  let currledgerroot = get_ledgerroot best in
	  let (k,h) = Commands.generate_newkeyandaddress currledgerroot "staking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | [clr] ->
	  let (k,h) = Commands.generate_newkeyandaddress (hexstring_hashval clr) "staking" in
	  let alpha = p2pkhaddr_addr h in
	  let a = addr_pfgaddrstr alpha in
	  Printf.fprintf oc "%s\n" a
      | _ -> raise BadCommandForm);
  ac "stakewith" "stakewith <address>" "Move an address in the wallet from nonstaking to staking.\nAttempts to spend assets from staking addresses might fail due to the asset being used to stake instead.\nSee also: donotstakewith"
    (fun oc al ->
      match al with
      | [alpha] -> Commands.reclassify_staking oc alpha true
      | _ -> raise BadCommandForm);
  ac "donotstakewith" "donotstakewith <address>" "Move an address in the wallet from staking to nonstaking.\nYou should mark an address as nonstaking if you want to ensure you can spend assets at the address.\nSee also: stakewith"
    (fun oc al ->
      match al with
      | [alpha] -> Commands.reclassify_staking oc alpha false
      | _ -> raise BadCommandForm);
  ac "createp2sh" "createp2sh <redeem script in hex>" "Create a p2sh address by giving the redeem script in hex"
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let bl = ref [] in
	  for i = (String.length s) - 1 downto 0 do
	    bl := Char.code s.[i]::!bl
	  done;
	  let alpha = Script.hash160_bytelist !bl in
	  Printf.fprintf oc "p2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr alpha));
      | _ -> raise BadCommandForm);
  ac "importp2sh" "importp2sh <redeem script in hex>" "Create a p2sh address by giving the redeem script in hex and import it into wallet"
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let bl = ref [] in
	  for i = (String.length s) - 1 downto 0 do
	    bl := Char.code s.[i]::!bl
	  done;
	  Commands.importp2sh oc !bl
      | _ -> raise BadCommandForm);
  ac "createchannel" "createchannel <alphapubkey> <betapubkey> <alphaassetid> <betaassetid> <alphaamt[bars]> <betaamt[bars]> [json]"
    "Create the initial information for a payment channel,\nincluding the unsigned funding tx, the funding address and funding asset id."
    (fun oc al ->
      let (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,jb) =
	match al with
	| [alphapubkey;betapubkey;alphaaid;betaaid;alphaamt;betaamt] ->
	    (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,false)
	| [alphapubkey;betapubkey;alphaaid;betaaid;alphaamt;betaamt;"json"] ->
	    (alphapubkey,betapubkey,alphaaid,betaaid,alphaamt,betaamt,true)
	| _ -> raise BadCommandForm
      in
      let (alphapk,alphab) = hexstring_pubkey alphapubkey in
      let (betapk,betab) = hexstring_pubkey betapubkey in
      let aaid = hexstring_hashval alphaaid in
      let baid = hexstring_hashval betaaid in
      let aamt = atoms_of_bars alphaamt in
      let bamt = atoms_of_bars betaamt in
      let esttxbytes = 2000 in
      let fee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
      let halffee = Int64.div fee 2L in
      let (blkh,lr) =
	match get_bestblock_print_warnings oc with
	| None -> raise (Failure "trouble finding current ledger")
	| Some(_,lbk,ltx) ->
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    (blkh,lr)
      in
      let alpha = pubkey_md160 alphapk alphab in
      let beta = pubkey_md160 betapk betab in
      let alpha2 = p2pkhaddr_addr alpha in
      let beta2 = p2pkhaddr_addr beta in
      let (fundaddress,fundredscr) = Commands.createmultisig2 2 [(alphapubkey,(alphapk,alphab));(betapubkey,(betapk,betab))] in
      let fundaddress2 = p2shaddr_addr fundaddress in
      let (aa,av) =
	match ctree_lookup_asset false true true aaid (CHash(lr)) (addr_bitseq alpha2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
      in
      let ach = Int64.sub av (Int64.add aamt halffee) in
      if ach < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" alphaaid));
      let (ba,bv) =
	match ctree_lookup_asset false true true baid (CHash(lr)) (addr_bitseq beta2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" betaaid (addr_pfgaddrstr beta2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" betaaid (addr_pfgaddrstr beta2)))
      in
      let bch = Int64.sub bv (Int64.add bamt halffee) in
      if bch < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" betaaid));
      let tauin = [(alpha2,aaid);(beta2,baid)] in
      let tauout = ref [] in
      if bch > 0L then tauout := (beta2,(None,Currency(bch)))::!tauout;
      if ach > 0L then tauout := (alpha2,(None,Currency(ach)))::!tauout;
      (* split into two assets so commitment txs replace the two assets with two assets, avoiding full address attack (since addresses can only hold at most 32 assets) *)
      tauout := (fundaddress2,(None,Currency(bamt)))::!tauout;
      tauout := (fundaddress2,(None,Currency(aamt)))::!tauout;
      let tau = (tauin,!tauout) in
      let s = Buffer.create 100 in
      seosbf (seo_stx seosb (tau,([],[])) (s,None));
      let txh = hashtx tau in
      let fundid1 = hashpair txh (hashint32 0l) in
      let fundid2 = hashpair txh (hashint32 1l) in
      let hs = Hashaux.string_hexstring (Buffer.contents s) in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) fundredscr;
	  let jol = [("fundingtx",JsonStr(hs));
		     ("fundaddress",JsonStr(addr_pfgaddrstr (p2shaddr_addr fundaddress)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("fundassetid1",JsonStr(hashval_hexstring fundid1));
		     ("fundassetid2",JsonStr(hashval_hexstring fundid2))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "Funding tx: %s\n" hs;
	  Printf.fprintf oc "Fund 2-of-2 address: %s\n" (addr_pfgaddrstr (p2shaddr_addr fundaddress));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) fundredscr;
	  Printf.fprintf oc "\nFund asset id 1: %s\n" (hashval_hexstring fundid1);
	  Printf.fprintf oc "Fund asset id 2: %s\n" (hashval_hexstring fundid2)
	end);
  ac "createchannelonefunder" "createchannelonefunder <alphapubkey> <betapubkey> <alphaassetid> <alphaamt[bars]> [json]"
    "Create the initial information for a payment channel (with only alpha funding the channel),\nincluding the unsigned funding tx, the funding address and funding asset id."
    (fun oc al ->
      let (alphapubkey,betapubkey,alphaaid,alphaamt,jb) =
	match al with
	| [alphapubkey;betapubkey;alphaaid;alphaamt] ->
	    (alphapubkey,betapubkey,alphaaid,alphaamt,false)
	| [alphapubkey;betapubkey;alphaaid;alphaamt;"json"] ->
	    (alphapubkey,betapubkey,alphaaid,alphaamt,true)
	| _ -> raise BadCommandForm
      in
      let (alphapk,alphab) = hexstring_pubkey alphapubkey in
      let (betapk,betab) = hexstring_pubkey betapubkey in
      let aaid = hexstring_hashval alphaaid in
      let aamt = atoms_of_bars alphaamt in
      let esttxbytes = 2000 in
      let fee = Int64.mul (Int64.of_int esttxbytes) !Config.defaulttxfee in
      let (blkh,lr) =
	match get_bestblock_print_warnings oc with
	| None -> raise (Failure "trouble finding current ledger")
	| Some(_,lbk,ltx) ->
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	    (blkh,lr)
      in
      let alpha = pubkey_md160 alphapk alphab in
      let alpha2 = p2pkhaddr_addr alpha in
      let (fundaddress,fundredscr) = Commands.createmultisig2 2 [(alphapubkey,(alphapk,alphab));(betapubkey,(betapk,betab))] in
      let fundaddress2 = p2shaddr_addr fundaddress in
      let (aa,av) =
	match ctree_lookup_asset false true true aaid (CHash(lr)) (addr_bitseq alpha2) with
	  Some((_,_,_,Currency(_)) as a) ->
	    begin
	      match asset_value blkh a with
	      | Some(v) -> (a,v)
	      | _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
	    end
	| _ -> raise (Failure (Printf.sprintf "could not find currency asset with id %s at address %s" alphaaid (addr_pfgaddrstr alpha2)))
      in
      let ach = Int64.sub av (Int64.add aamt fee) in
      if ach < 0L then raise (Failure (Printf.sprintf "asset %s has insufficient value" alphaaid));
      let tauin = [(alpha2,aaid)] in
      let tauout = ref [] in
      if ach > 0L then tauout := (alpha2,(None,Currency(ach)))::!tauout;
      (* split into two assets so commitment txs replace the two assets with two assets, avoiding full address attack (since addresses can only hold at most 32 assets) *)
      let aamthalf = Int64.div aamt 2L in
      tauout := (fundaddress2,(None,Currency(aamthalf)))::!tauout;
      tauout := (fundaddress2,(None,Currency(Int64.sub aamt aamthalf)))::!tauout;
      let tau = (tauin,!tauout) in
      let s = Buffer.create 100 in
      seosbf (seo_stx seosb (tau,([],[])) (s,None));
      let txh = hashtx tau in
      let fundid1 = hashpair txh (hashint32 0l) in
      let fundid2 = hashpair txh (hashint32 1l) in
      let hs = Hashaux.string_hexstring (Buffer.contents s) in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) fundredscr;
	  let jol = [("fundingtx",JsonStr(hs));
		     ("fundaddress",JsonStr(addr_pfgaddrstr (p2shaddr_addr fundaddress)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("fundassetid1",JsonStr(hashval_hexstring fundid1));
		     ("fundassetid2",JsonStr(hashval_hexstring fundid2))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "Funding tx: %s\n" hs;
	  Printf.fprintf oc "Fund 2-of-2 address: %s\n" (addr_pfgaddrstr (p2shaddr_addr fundaddress));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) fundredscr;
	  Printf.fprintf oc "\nFund asset id 1: %s\n" (hashval_hexstring fundid1);
	  Printf.fprintf oc "Fund asset id 2: %s\n" (hashval_hexstring fundid2)
	end);
  ac "createhtlc" "createhtlc <p2pkhaddr:alpha> <p2pkhaddr:beta> <timelock> [relative] [<secret>] [json]"
    "Create hash timelock constract script and address.\nThe controller of address alpha can spend with the secret.\nThe controller of the address beta can spend after the timelock.\nThe controller of address alpha should call this command and the secret will be held in alpha's wallet.\nA hex 32 byte secret can optionally be given, otherwise one will be randomly generated.\nIf 'relative' is given, then relative lock time (CSV) is used. Otherwise absolute lock time (CLTV) is used.\nThe timelock is either in block time (if less than 500000000) or unix time (otherwise).\nOnly block time can be used with relative block time."
    (fun oc al ->
      let (alphas,alpha,betas,beta,tmlock,rel,secr,jb) =
	match al with
	  [alpha;beta;tmlock] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,big_int_md256 (strong_rand_256()),false)
	| [alpha;beta;tmlock;"relative"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,big_int_md256 (strong_rand_256()),false)
	| [alpha;beta;tmlock;"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,big_int_md256 (strong_rand_256()),false)
	| [alpha;beta;tmlock;secr] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,hexstring_hashval secr,false)
	| [alpha;beta;tmlock;"relative";"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,big_int_md256 (strong_rand_256()),true)
	| [alpha;beta;tmlock;"relative";secr] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,hexstring_hashval secr,false)
	| [alpha;beta;tmlock;secr;"json"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,false,hexstring_hashval secr,true)
	| [alpha;beta;tmlock;"relative";secr;"true"] -> (alpha,pfgaddrstr_addr alpha,beta,pfgaddrstr_addr beta,Int32.of_string tmlock,true,hexstring_hashval secr,true)
	| _ -> raise BadCommandForm
      in
      if not (p2pkhaddr_p alpha) then raise (Failure (Printf.sprintf "%s is not a p2pkh address" alphas));
      if not (p2pkhaddr_p beta) then raise (Failure (Printf.sprintf "%s is not a p2pkh address" betas));
      if tmlock < 1l then raise (Failure ("locktime must be positive"));
      if rel && tmlock >= 500000000l then raise (Failure ("relative lock time must be given in number of blocks"));
      let (_,a1,a2,a3,a4,a5) = alpha in
      let (_,b1,b2,b3,b4,b5) = beta in
      let (gamma,scrl,secrh) = Commands.createhtlc (a1,a2,a3,a4,a5) (b1,b2,b3,b4,b5) tmlock rel secr in
      if jb then
	begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) scrl;
	  let jol = [("address",JsonStr(addr_pfgaddrstr (p2shaddr_addr gamma)));
		     ("redeemscript",JsonStr(Buffer.contents redscr));
		     ("secret",JsonStr(hashval_hexstring secr));
		     ("hashofsecret",JsonStr(hashval_hexstring secrh))]
	  in
	  print_jsonval oc (JsonObj(jol))
	end
      else
	begin
	  Printf.fprintf oc "P2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr gamma));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	  Printf.fprintf oc "\n";
	  Printf.fprintf oc "Secret: %s\n" (hashval_hexstring secr);
	  Printf.fprintf oc "Hash of secret: %s\n" (hashval_hexstring secrh)
	end);
  ac "verifycommitmenttx" "verifycommitmenttx alpha beta fundaddress fundid1 fundid2 alphaamt betaamt secrethash tx [json]"
    "Verify a commitment tx"
    (fun oc al ->
      let (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,jb) =
	match al with
	| [alphas;betas;gammas;fundid1s;fundid2s;alphaamts;betaamts;secrethashs;txs] ->
	    (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,false)
	| [alphas;betas;gammas;fundid1s;fundid2s;alphaamts;betaamts;secrethashs;txs;"json"] ->
	    (alphas,betas,gammas,fundid1s,fundid2s,alphaamts,betaamts,secrethashs,txs,true)
	| _ -> raise BadCommandForm
      in
      let alpha = pfgaddrstr_addr alphas in
      let beta = pfgaddrstr_addr betas in
      let gamma = pfgaddrstr_addr gammas in
      let fundid1 = hexstring_hashval fundid1s in
      let fundid2 = hexstring_hashval fundid2s in
      let alphaamt = atoms_of_bars alphaamts in
      let betaamt = atoms_of_bars betaamts in
      let secrethash = hexstring_hashval secrethashs in
      let txs2 = hexstring_string txs in
      let (((tauin,tauout) as tau,(tausigsin,_)),_) = sei_stx seis (txs2,String.length txs2,None,0,0) in
      let inputsok =
	match tauin with
	| [(a1,aid1);(a2,aid2)] when a1 = gamma && a2 = gamma && aid1 = fundid1 && aid2 = fundid2 -> true
	| _ -> false
      in
      let (outputsok,htlcaddr) =
	match tauout with
	| [(a01,(Some(aaddr2,0L,false),Currency(aamt2)));(a02,(Some(baddr2,0L,false),Currency(bamt2)))] when aamt2 = alphaamt && bamt2 = betaamt && a01 = gamma && a02 = gamma ->
	    if payaddr_addr aaddr2 = alpha then (*** this must be a commitment for beta to close the channel ***)
	      (2,Some(payaddr_addr baddr2))
	    else if payaddr_addr baddr2 = beta then (*** this must be a commitment for alpha to close the channel ***)
	      (1,Some(payaddr_addr aaddr2))
	    else
	      (0,None)
	| _ -> (0,None)
      in
      if inputsok then
	if outputsok = 1 then
	  begin
	    let (_,a1,a2,a3,a4,a5) = alpha in
	    let (_,b1,b2,b3,b4,b5) = beta in
	    let (delta,scrl,secrh) = Commands.createhtlc2 (b1,b2,b3,b4,b5) (a1,a2,a3,a4,a5) 28l true secrethash in
	    if Some(p2shaddr_addr delta) = htlcaddr then
	      begin (** it's good, could also check if beta has already signed it -- for now alpha can check the signature by signing with alphas key and ensuring the result is completely signed **)
		if jb then
		  print_jsonval oc (JsonObj([("result",JsonBool(true));("commitmentfor",JsonStr(alphas))]))
		else
		  Printf.fprintf oc "Valid commitment tx for %s\n" alphas
	      end
	    else
	      begin
		if jb then
		  print_jsonval oc (JsonBool(false))
		else
		  begin
		    Printf.fprintf oc "Appears to be a commitment tx for alpha, but htlc address mismatch:\nFound %s\nExpected %s\n"
		      (addr_pfgaddrstr (p2shaddr_addr delta))
		      (match htlcaddr with Some(delta2) -> addr_pfgaddrstr delta2 | None -> "None")
		  end
	      end
	  end
	else if outputsok = 2 then
	  begin
	    let (_,a1,a2,a3,a4,a5) = alpha in
	    let (_,b1,b2,b3,b4,b5) = beta in
	    let (delta,scrl,secrh) = Commands.createhtlc2 (a1,a2,a3,a4,a5) (b1,b2,b3,b4,b5) 28l true secrethash in
	    if Some(p2shaddr_addr delta) = htlcaddr then
	      begin (** it's good, could also check if alpha has already signed it -- for now alpha can check the signature by signing with alphas key and ensuring the result is completely signed **)
		if jb then
		  print_jsonval oc (JsonObj([("result",JsonBool(true));("commitmentfor",JsonStr(betas))]))
		else
		  Printf.fprintf oc "Valid commitment tx for %s\n" betas
	      end
	    else
	      begin
		if jb then
		  print_jsonval oc (JsonBool(false))
		else
		  begin
		    Printf.fprintf oc "Appears to be a commitment tx for beta, but htlc address mismatch:\nFound %s\nExpected %s\n"
		      (addr_pfgaddrstr (p2shaddr_addr delta))
		      (match htlcaddr with Some(delta2) -> addr_pfgaddrstr delta2 | None -> "None")
		  end
	      end
	  end
	else
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Outputs do not match the form of a commitment tx.\n"
	  end
      else
	if not (outputsok = 0) then
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Inputs do not match the form of a commitment tx.\n"
	  end
	else
	  begin
	    if jb then
	      print_jsonval oc (JsonBool(false))
	    else
	      Printf.fprintf oc "Inputs and outputs do not match the form of a commitment tx.\n"
	  end);
  ac "createmultisig" "createmultisig <m> <jsonarrayofpubkeys>" "Create an m-of-n script and address"
    (fun oc al ->
      match al with
      | [ms;pubkeyss] ->
	  let m = int_of_string ms in
	  begin
	    let (jpks,_) = parse_jsonval pubkeyss in
	    let (alpha,scrl) = Commands.createmultisig m jpks in
	    let alphastr = addr_pfgaddrstr (p2shaddr_addr alpha) in
	    Printf.fprintf oc "P2sh address: %s\n" alphastr;
	    Printf.fprintf oc "Redeem script: ";
	    List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	    Printf.fprintf oc "\n";
	  end
      | _ -> raise BadCommandForm);
  ac "addmultisig" "addmultisig <m> <jsonarrayofpubkeys>" "Create an m-of-n script and address and add it to the wallet"
    (fun oc al ->
      match al with
      | [ms;pubkeyss] ->
	  let m = int_of_string ms in
	  begin
	    let (jpks,_) = parse_jsonval pubkeyss in
	    let (alpha,scrl) = Commands.createmultisig m jpks in
	    let alphastr = addr_pfgaddrstr (p2shaddr_addr alpha) in
	    Commands.importp2sh oc scrl;
	    Printf.fprintf oc "P2sh address: %s\n" alphastr;
	    Printf.fprintf oc "Redeem script: ";
	    List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	    Printf.fprintf oc "\n";
	  end
      | _ -> raise BadCommandForm);
  ac "createatomicswap" "createatomicswap <ltctxid> <pfgaddr> <pfgrefundaddr> <timelock> [json]"
    "Create a script and corresponding p2sh address for an atomic swap with ltc.\nThe address will be spendable by <pfgaddr> after the given litecoin tx has at least one confirmation.\nThe address will be spendable by <pfgrefundaddr> after <timelock>.\nIf the keyword 'json' is given then the response is given in json format.\nThe intended use is that Alice has some X Proofgold bars that Bob will pay Y litecoins for.\nBob has his litecoins in a segwit addresses. Bob creates an unsigned litecoin tx sending Y litecoins to Alice.\nAlice verifies Bob's litecoin tx and notes the txid.\nAlice then uses createatomicswap with this litecoin txid, Bob's Proofgold address,\na refund address for Alice and a timelock in case Bob does not sign and publish the litecoin tx.\nAlice sends X Proofgold bars to the created p2sh address.\nIf Bob signs and publishes the litecoin tx and it confirms before the timelock,\n Bob will be able to spend the Proofgold bars to an address only he controls.\nIf the litecoin tx is not confirmed before the timelock,\nAlice can recover the funds by spending from the p2sh address after the timelock passes."
    (fun oc al ->
      let (ltx,alpha,beta,tmlock,jb) =
        match al with
        | (ltx::alpha::beta::tmlock::r) ->
           let ltx = hexstring_hashval ltx in
           let alpha = Cryptocurr.pfgaddrstr_addr alpha in
           let beta = Cryptocurr.pfgaddrstr_addr beta in
           let tmlock = Int32.of_string tmlock in
           let (a0,a1,a2,a3,a4,a5) = alpha in
           let (b0,b1,b2,b3,b4,b5) = beta in
           if not (a0 = 0 && b0 = 0) then raise (Failure "The two addresses must be p2pkh.");
           (ltx,(a1,a2,a3,a4,a5),(b1,b2,b3,b4,b5),tmlock,r = ["json"])
        | _ -> raise BadCommandForm
      in
      let (gamma,scrl) = Commands.createatomicswap ltx alpha beta tmlock in
      if jb then
        begin
	  let redscr = Buffer.create 10 in
	  List.iter (fun x -> Buffer.add_string redscr (Printf.sprintf "%02x" x)) scrl;
          let jol = [("address",JsonStr(addr_pfgaddrstr (p2shaddr_addr gamma)));
                     ("redeemscript",JsonStr(Buffer.contents redscr))]
          in
          print_jsonval oc (JsonObj(jol))
        end
      else
        begin
	  Printf.fprintf oc "P2sh address: %s\n" (addr_pfgaddrstr (p2shaddr_addr gamma));
	  Printf.fprintf oc "Redeem script: ";
	  List.iter (fun x -> Printf.fprintf oc "%02x" x) scrl;
	  Printf.fprintf oc "\n";
        end);
  ac "createtx" "createtx <inputs as json array> <outputs as json array>" "Create a simple tx spending some assets to create new currency assets.\neach input: {\"<addr>\":\"<assetid>\"}\neach output: {\"addr\":\"<addr>\",\"val\":<bars>,\"lockheight\":<height>,\"lockaddr\":\"<addr>\"}\nwhere lock is optional (default null, unlocked output)\nand lockaddr is optional (default null, meaning the holder address is implicitly the lockaddr)\nSee also: creategeneraltx"
    (fun oc al ->
      match al with
      | [inp;outp] ->
	  begin
	    try
	      let (inpj,_) = parse_jsonval inp in
	      begin
		try
		  let (outpj,_) = parse_jsonval outp in
		  let tau = Commands.createtx inpj outpj in
		  let s = Buffer.create 100 in
		  seosbf (seo_stx seosb (tau,([],[])) (s,None));
		  let hs = Hashaux.string_hexstring (Buffer.contents s) in
		  Printf.fprintf oc "%s\n" hs
		with
		| JsonParseFail(i,msg) ->
		    Printf.fprintf oc "Problem parsing json object for tx inputs at position %d %s\n" i msg
	      end
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for tx outputs at position %d %s\n" i msg
	  end
      | _ -> raise BadCommandForm);
  ac "creategeneraltx" "creategeneraltx <tx as json object>" "Create a general tx given as as a json object.\nEvery possible transaction can be represented this way,\nincluding txs publishing mathematical documents and collecting bounties.\nSee also: createtx and createsplitlocktx"
    (fun oc al ->
      try
	match al with
	| [jtxstr] ->
	    let (jtx,_) = parse_jsonval jtxstr in
	    let tau = tx_from_json jtx in
	    let s = Buffer.create 100 in
	    seosbf (seo_stx seosb (tau,([],[])) (s,None));
	    let hs = Hashaux.string_hexstring (Buffer.contents s) in
	    Printf.fprintf oc "%s\n" hs
	| _ -> raise BadCommandForm
      with
      | JsonParseFail(i,msg) ->
	  Printf.fprintf oc "Problem parsing json object for tx at position %d %s\n" i msg);
  ac "createsplitlocktx" "createsplitlocktx <current address> <assetid> <number of outputs> <lockheight> <fee> [<new holding address> [<new obligation address> [<ledger root> <current block height>]]]" "Create a tx to spend an asset into several assets locked until a given height.\nOptionally the new assets can be held at a new address, and may be controlled by a different obligation address."
    (fun oc al ->
      match al with
      | (alp::aid::n::lkh::fee::r) ->
	  begin
	    let alpha2 = pfgaddrstr_addr alp in
	    if not (payaddr_p alpha2) then raise (Failure (alp ^ " is not a pay address"));
	    let (p,a4,a3,a2,a1,a0) = alpha2 in
	    let alpha = (p=1,a4,a3,a2,a1,a0) in
	    let aid = hexstring_hashval aid in
	    let n = int_of_string n in
	    if n <= 0 then raise (Failure ("Cannot split into " ^ (string_of_int n) ^ " assets"));
	    let lkh = Int64.of_string lkh in
	    let fee = atoms_of_bars fee in
	    if fee < 0L then raise (Failure ("Cannot have a negative fee"));
	    let (blkhght,lr) =
	      match r with
	      | [_;_;lr;blkhght] ->
		  (Int64.of_string blkhght,hexstring_hashval lr)
	      | _ ->
		  try
		    match get_bestblock_print_warnings oc with
		    | None -> raise Not_found
		    | Some(_,lbk,ltx) ->
			let (_,_,_,_,_,_,blkhght) = Db_outlinevals.dbget (hashpair lbk ltx) in
			let (_,_,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
			(blkhght,lr)
		  with Not_found ->
		    raise (Failure("Could not find ledger root"))
	    in
	    match r with
	    | [] ->
		let gamma = alpha2 in
		let beta = alpha in
		Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
	    | (gam::r) ->
		let gamma = pfgaddrstr_addr gam in
		if not (payaddr_p gamma) then raise (Failure (gam ^ " is not a pay address"));
		match r with
		| [] ->
		    let beta = alpha in
		    let lr = get_ledgerroot (get_bestblock_print_warnings oc) in
		    Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
		| (bet::r) ->
		    let beta2 = pfgaddrstr_addr bet in
		    if not (payaddr_p beta2) then raise (Failure (bet ^ " is not a pay address"));
		    let (p,b4,b3,b2,b1,b0) = beta2 in
		    let beta = (p=1,b4,b3,b2,b1,b0) in
		    match r with
		    | [] -> Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee
		    | [_;_] -> Commands.createsplitlocktx oc lr blkhght alpha beta gamma aid n lkh fee (** lr and blockheight given, handled above **)
		    | _ -> raise BadCommandForm
	  end
      | _ -> raise BadCommandForm);
  ac "hashsecret" "hashsecret <hashval in hex>"
    "Compute the sha256 hash of a secret (32 bytes given in hex)\nintended to be used to check secrets used in hash time lock contracts (htlc)\nespecially in payment channels."
    (fun oc al ->
      match al with
      | [secr] when String.length secr = 64 ->
	  let secrh = Script.sha256_bytelist (string_bytelist (hexstring_string secr)) in
	  Printf.fprintf oc "%s\n" (hashval_hexstring secrh)
      | _ -> raise BadCommandForm);
  ac "simplesigntx" "simplesigntx <tx in hex> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets>]]]" "Sign a proofgold tx, under the simple assumption that the obligations are defaults\nand all inputs and outputs are currency assets.\nThis command is useful for signing txs that spend assets that are not yet in the ledger,\nfor example when creating a payment channel."
    (fun oc al ->
      match al with
      | [s] -> Commands.simplesigntx oc s [] [] None
      | [s;kl] ->
	  let kl = parse_json_privkeys kl in
	  Commands.simplesigntx oc s [] [] (Some(kl))
      | [s;kl;rl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  Commands.simplesigntx oc s rl [] (Some(kl))
      | [s;kl;rl;sl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.simplesigntx oc s rl sl (Some(kl))
      | _ -> raise BadCommandForm);
  ac "signtx" "signtx <tx in hex> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets> [<ledgerroot>]]]]" "Sign a proofgold tx."
    (fun oc al ->
      match al with
      | [s] -> Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s [] [] None
      | [s;kl] ->
	  let kl = parse_json_privkeys kl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s [] [] (Some(kl))
      | [s;kl;rl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s rl [] (Some(kl))
      | [s;kl;rl;sl] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.signtx oc (get_ledgerroot (get_bestblock_print_warnings oc)) s rl sl (Some(kl))
      | [s;kl;rl;sl;lr] ->
	  let kl = parse_json_privkeys kl in
	  let rl = parse_json_redeemscripts rl in
	  let sl = parse_json_secrets sl in
	  Commands.signtx oc (hexstring_hashval lr) s rl sl (Some(kl))
      | _ -> raise BadCommandForm);
  ac "signtxfile" "signtxfile <infile> <outfile> [<jsonarrayofprivkeys> [<redeemscripts> [<secrets> [<ledgerroot>]]]]" "Sign a proofgold tx.\n<infile> is an existing binary file with the (possibly partially signed) tx.\n<outfile> is a binary file created with the output tx."
    (fun oc al ->
      let kl =
	match al with
	| (_::_::kl::_) -> Some(parse_json_privkeys kl)
	| _ -> None
      in
      let rl =
	match al with
	| (_::_::_::rl::_) -> parse_json_redeemscripts rl
	| _ -> []
      in
      let sl =
	match al with
	| (_::_::_::_::sl::_) -> parse_json_secrets sl
	| _ -> []
      in
      let lr =
	match al with
	| (_::_::_::_::_::lr::_) -> hexstring_hashval lr
	| _ -> get_ledgerroot (get_bestblock_print_warnings oc)
      in
      match al with
      | (s1::s2::_) ->
	  let c1 = open_in_bin s1 in
	  let (stau,_) = Tx.sei_stx seic (c1,None) in
	  close_in_noerr c1;
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signtxc oc lr stau c2 rl sl kl;
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | _ -> raise BadCommandForm);
  ac "signbatchtxsfiles" "signbatchtxsfiles <infile> <outfile> [<jsonarrayofprivkeys> [<ledgerroot>]]" "Sign a proofgold tx.\n<infile> is an existing binary file with several (possibly partially signed) txs.\n<outfile> is a binary file created with the txs after signing."
    (fun oc al ->
      let read_staul s1 =
	let staur = ref [] in
	let c1 = open_in_bin s1 in
	try
	  while true do
	    let (stau,_) = Tx.sei_stx seic (c1,None) in
	    staur := stau::!staur
	  done;
	  []
	with
	| End_of_file -> close_in_noerr c1; List.rev !staur
	| _ -> close_in_noerr c1; raise BadCommandForm
      in
      match al with
      | [s1;s2] ->
	  let staul = read_staul s1 in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (get_ledgerroot (get_bestblock_print_warnings oc)) staul c2 [] [] None;
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | [s1;s2;kl] ->
	  let staul = read_staul s1 in
	  let kl = parse_json_privkeys kl in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (get_ledgerroot (get_bestblock_print_warnings oc)) staul c2 [] [] (Some(kl));
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | [s1;s2;kl;lr] ->
	  let staul = read_staul s1 in
	  let kl = parse_json_privkeys kl in
	  let c2 = open_out_bin s2 in
	  begin
	    try
	      Commands.signbatchtxsc oc (hexstring_hashval lr) staul c2 [] [] (Some(kl));
	      close_out_noerr c2
	    with e ->
	      close_out_noerr c2;
	      raise e
	  end
      | _ -> raise BadCommandForm);
  ac "txpool" "txpool" "Print info about txpool"
    (fun oc al ->
      Hashtbl.iter
        (fun k stau ->
          let sz = stxsize stau in
          Printf.fprintf oc ". %s size %d\n" (hashval_hexstring k) sz;
          if sz < 400 then
            let sb = Buffer.create 400 in
            seosbf (seo_stx seosb stau (sb,None));
            Printf.fprintf oc "%s\n" (string_hexstring (Buffer.contents sb)))
        stxpool);
  ac "savetxtopool" "savetxtopool <tx in hex>" "Save a proofgold tx to the local pool without sending it to the network."
    (fun oc al ->
      match al with
      | [s] ->
	  let b = get_bestblock_print_warnings oc in
	  begin
	    match b with
	    | None -> Printf.fprintf oc "Cannot find best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    Commands.savetxtopool blkh tm lr s
		  with Not_found ->
		    let (bhd,_) = DbBlockHeader.dbget dbh in
		    let lr = bhd.newledgerroot in
		    let tm = bhd.timestamp in
		    Commands.savetxtopool blkh tm lr s
		with Not_found ->
		  Printf.fprintf oc "Trouble finding current block height\n"
	  end
      | _ -> raise BadCommandForm);
  ac "sendtx" "sendtx <tx in hex>" "Send a proofgold tx to other nodes on the network."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "Cannot find best block.\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  Commands.sendtx oc (Int64.add 1L blkh) tm tr sr lr s
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "sendtxfile" "sendtxfile <file with tx in binary>" "Send a proofgold tx to other nodes on the network."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    match get_bestblock_print_warnings oc with
	    | None -> Printf.fprintf oc "Cannot find best block.\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		  let c = open_in_bin s in
		  let (stau,_) = Tx.sei_stx seic (c,None) in
		  let txbytes = pos_in c in
		  close_in_noerr c;
		  if txbytes > 450000 then
		    Printf.fprintf oc "Refusing to send tx > 450K bytes\n"
		  else
		    Commands.sendtx2 oc (Int64.add 1L blkh) tm tr sr lr txbytes stau
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatetx" "validatetx <tx in hex>" "Print information about the tx and whether or not it is valid.\nIf the tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      Commands.validatetx oc (Int64.add 1L blkh) tm tr sr lr s
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatetxfile" "validatetxfile <file with tx in binary>" "Print information about the tx and whether or not it is valid.\nIf the tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      let c = open_in_bin s in
		      let (stau,_) = Tx.sei_stx seic (c,None) in
		      let txbytes = pos_in c in
		      close_in_noerr c;
		      if txbytes > 450000 then
			Printf.fprintf oc "Tx is > 450K bytes and will be considered too big to include in a block\n"
		      else
			Commands.validatetx2 oc (Int64.add 1L blkh) tm tr sr lr txbytes stau
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "validatebatchtxsfile" "validatebatchtxsfile <file with several tx in binary>" "Print information about the txs and whether or not it they valid.\nThe txs are considered in sequences with the previous txs modifying the ledger before evaluating the next.\nIf a tx is not valid, information about why it is not valid is given."
    (fun oc al ->
      match al with
      | [s] ->
	  begin
	    let best = get_bestblock_print_warnings oc in
	    match best with
	    | None -> Printf.fprintf oc "Cannot determine best block\n"
	    | Some(dbh,lbk,ltx) ->
		try
		  let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
		  try
		    let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
		    try
		      let c = open_in_bin s in
		      let staur = ref [] in
		      begin
			try
			  while true do
			    let (stau,_) = Tx.sei_stx seic (c,None) in
			    staur := stau::!staur
			  done
			with End_of_file ->
			  close_in_noerr c;
			  Commands.validatebatchtxs oc (Int64.add 1L blkh) tm tr sr lr (List.rev !staur)
		      end
		    with exn ->
		      Printf.fprintf oc "Trouble validating tx %s\n" (Printexc.to_string exn)
		  with Not_found ->
		    Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring dbh) blkh
		with Not_found ->
		  Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring dbh)
	  end
      | _ -> raise BadCommandForm);
  ac "theory" "theory <theoryid>" "Print information about a confirmed theory"
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    let thyid = hexstring_hashval a in
	    let (_,tr,_) = get_3roots (get_bestblock_print_warnings oc) in
	    try
	      let tht = lookup_thytree tr in
	      let thy = ottree_lookup tht (Some(thyid)) in
	      let (prms,axs) = thy in
	      let i = ref 0 in
	      Printf.fprintf oc "Theory %s %d Prims %d Axioms:\nIds and Types of Prims:\n" a (List.length prms) (List.length axs);
	      List.iter
		(fun a ->
		  let h = tm_hashroot (Logic.Prim(!i)) in
		  incr i;
		  Printf.fprintf oc "%s %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 (Some(thyid)) (hashpair h (hashtp a))) 32l));
		  print_jsonval oc (json_stp a); Printf.fprintf oc "\n")
		prms;
	      Printf.fprintf oc "Ids of Axioms:\n";
	      List.iter
		(fun h -> Printf.fprintf oc "%s %s\n" (hashval_hexstring h) (hashval_hexstring (hashtag (hashopair2 (Some(thyid)) h) 33l)))
		axs;
	    with Not_found ->
	      Printf.fprintf oc "Theory not found.\n"
	  end
      | _ -> raise BadCommandForm);
  ac "signature" "signature <signatureid>" "Print information about a confirmed signature"
    (fun oc al ->
      let (a,sgid) =
	match al with
	| [a] -> (a,hexstring_hashval a)
	| _ -> raise BadCommandForm
      in
      let (_,_,sr) = get_3roots (get_bestblock_print_warnings oc) in
      try
	let sgt = lookup_sigtree sr in
	let (th,sg) = ostree_lookup sgt (Some(sgid)) in
	let ths = match th with Some(h) -> hashval_hexstring h | None -> "empty" in
	let (imps,(objs,kns)) = sg in
	Printf.fprintf oc "Signature %s in Theory %s\n%d Imported Signatures %d Objects %d Knowns:\n" a ths (List.length imps) (List.length objs) (List.length kns);
	Printf.fprintf oc "Imports:\n";
	List.iter
	  (fun h -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  imps;
	Printf.fprintf oc "Objects:\n";
	List.iter
	  (fun ((h,_),_) -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  objs;
	Printf.fprintf oc "Knowns:\n";
	List.iter
	  (fun (h,_) -> Printf.fprintf oc "%s\n" (hashval_hexstring h))
	  kns;
      with Not_found ->
	Printf.fprintf oc "Signature not found.\n");
  ac "preassetinfo" "preassetinfo <preasset as json>" "Print information about a preasset given in json form.\nTypes of assets are currency, bounties,\n ownership of objects, ownership of propositions, ownership of negations of propositions,\nrights to use an object, rights to use a proposition,\ncommitment markers published before publishing a document, theory or signature,\na theories, signatures and documents."
    (fun oc al ->
      match al with
      | [a] ->
	  begin
	    try
	      let (j,_) = parse_jsonval a in
	      let u = preasset_from_json j in
	      Commands.preassetinfo_report oc u
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for preasset at position %d %s\n" i msg
	  end
      | _ -> raise BadCommandForm);
  ac "terminfo" "terminfo <term as json> [<type as json>, with default 'prop'] [<theoryid, default of empty theory>]" "Print information about a mathematical term given in json format."
    (fun oc al ->
      let (jtm,jtp,thyid) =
	match al with
	| [jtm] -> (jtm,"'\"prop\"'",None)
	| [jtm;jtp] -> (jtm,jtp,None)
	| [jtm;jtp;theoryid] -> (jtm,jtp,Some(hexstring_hashval theoryid))
	| _ -> raise BadCommandForm
      in
      begin
	try
	  let (jtm,_) = parse_jsonval jtm in
	  begin
	    try
	      let (jtp,_) = parse_jsonval jtp in
	      let m =
		match jtm with
		| JsonStr(x) -> Logic.TmH(hexstring_hashval x) (*** treat a string as just the term root abbreviating the term ***)
		| _ -> trm_from_json jtm
	      in
	      let a =
		match jtp with
		| JsonStr(x) when x = "prop" -> Logic.Prop
		| JsonNum(x) -> Logic.Base(int_of_string x)
		| _ -> stp_from_json jtp
	      in (*** not checking if the term has the type; this could depend on the theory ***)
	      let h = tm_hashroot m in
	      let tph = hashtp a in
	      Printf.fprintf oc "term root: %s\n" (hashval_hexstring h);
	      Printf.fprintf oc "pure term address: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_md160 h)));
	      if thyid = None then
		begin
		  let k = hashtag (hashopair2 None (hashpair h tph)) 32l in
		  Printf.fprintf oc "obj id in empty theory: %s\n" (hashval_hexstring k);
		  Printf.fprintf oc "obj address in empty theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_md160 k)))
		end
	      else
		begin
		  let k = hashtag (hashopair2 thyid (hashpair h tph)) 32l in
		  Printf.fprintf oc "obj id in given theory: %s\n" (hashval_hexstring k);
		  Printf.fprintf oc "obj address in given theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_md160 k)))
		end;
	      if a = Logic.Prop then
		begin
		  if thyid = None then
		    begin
		      let k = hashtag (hashopair2 None h) 33l in
		      Printf.fprintf oc "prop id in empty theory: %s\n" (hashval_hexstring k);
		      Printf.fprintf oc "prop address in empty theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_md160 k)))
		    end
		  else
		    begin
		      let k = hashtag (hashopair2 thyid h) 33l in
		      Printf.fprintf oc "prop id in given theory: %s\n" (hashval_hexstring k);
		      Printf.fprintf oc "prop address in given theory: %s\n" (addr_pfgaddrstr (termaddr_addr (hashval_md160 k)))
		    end
		end
	    with
	    | JsonParseFail(i,msg) ->
		Printf.fprintf oc "Problem parsing json object for tp at position %d %s\n" i msg
	  end
	with
	| JsonParseFail(i,msg) ->
	    Printf.fprintf oc "Problem parsing json object for tm at position %d %s\n" i msg
      end);
  ac "decodetx" "decodetx <raw tx in hex>" "Decode a proofgold tx."
    (fun oc al ->
      match al with
      | [a] ->
	  let s = hexstring_string a in
	  let (stx,_) = sei_stx seis (s,String.length s,None,0,0) in
	  print_jsonval oc (json_stx stx);
	  Printf.fprintf oc "\n"
      | _ -> raise BadCommandForm);
  ac "decodetxfile" "decodetxfile <file with binary tx>" "Decode a proofgold tx from a file."
    (fun oc al ->
      match al with
      | [s1] ->
	  let c1 = open_in_bin s1 in
	  let (stau,_) = Tx.sei_stx seic (c1,None) in
	  close_in_noerr c1;
	  print_jsonval oc (json_stx stau);
	  Printf.fprintf oc "\n"
      | _ -> raise BadCommandForm);
  ac "querybestblock" "querybestblock" "Print the current best block in json format.\nIn case of a tie, only one of the current best blocks is returned.\nThis command is intended to support explorers.\nSee also: bestblock"
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let lr = get_ledgerroot best in
	      print_jsonval oc (JsonObj([("height",JsonNum(Int64.to_string blkh));("block",JsonStr(hashval_hexstring h));("ledgerroot",JsonStr(hashval_hexstring lr))]))
	    with Not_found ->
	      print_jsonval oc (JsonObj([("height",JsonNum(Int64.to_string blkh));("block",JsonStr(hashval_hexstring h))]))
	  with Not_found ->
	    Printf.fprintf oc "Cannot determine height of best block %s\n" (hashval_hexstring h));
  ac "bestblock" "bestblock" "Print the current best block in text format.\nIn case of a tie, only one of the current best blocks is returned.\nSee also: querybestblock"
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let lr = get_ledgerroot best in
	      Printf.fprintf oc "Height: %Ld\nBlock hash: %s\nLedger root: %s\n" (Int64.sub blkh 1L) (hashval_hexstring h) (hashval_hexstring lr)
	    with Not_found ->
	      Printf.fprintf oc "Height: %Ld\nBlock hash: %s\n" (Int64.sub blkh 1L) (hashval_hexstring h)
	  with Not_found ->
	    Printf.fprintf oc "Block hash: %s\n" (hashval_hexstring h));
  ac "difficulty" "difficulty" "Print the current difficulty."
    (fun oc al ->
      let best = get_bestblock_print_warnings oc in
      match best with
      | None -> Printf.fprintf oc "Cannot determine best block\n"
      | Some(h,lbk,ltx) ->
	  try
	    let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
	    try
	      let (tar,_,_,_,_) = Db_validheadervals.dbget (hashpair lbk ltx) in
	      Printf.fprintf oc "Current target (for block at height %Ld): %s\n" blkh (string_of_big_int tar)
	    with Not_found ->
	      Printf.fprintf oc "Cannot determine information about best block %s at height %Ld\n" (hashval_hexstring h) blkh
	  with Not_found ->
	    Printf.fprintf oc "Cannot find block height for best block %s\n" (hashval_hexstring h));
  ac "vetobountyfund" "vetobountyfund <blockid> [<addr>]" "If your node staked the given block, then try to spend the bounty fund part of the block reward.\nThe bounty fund part of the reward can be collected to the bounty fund after 48 blocks,\ngiving the staker (at least) 48 blocks to veto the collection.\nIf you veto the collection, you are expected to place an equal amount of bars (25 per block)\nas a bounty on a proposition of your choice.\nThe address (if given) might be a term address, in which case vetobountyfund directly places the bounty on that address.\nOtherwise the address is a pay address (by default the staking address) and you\nare expected to manually place bounties.\nIf you do not place such a bounty or it is determined the bounties are gamed,\nfuture staked blocks may be orphaned by the network."
    (fun oc al ->
      let (h,blkid,alpha,delta) =
        match al with
        | [h] ->
           let blkid = hexstring_hashval h in
           begin
             try
               let (bhd,bhs) = DbBlockHeader.dbget blkid in
               let alpha = bhd.stakeaddr in
               (h,blkid,alpha,p2pkhaddr_addr alpha)
             with Not_found ->
               raise (Failure (Printf.sprintf "Do not have header %s\n" h));
           end
        | [h;a] ->
           let blkid = hexstring_hashval h in
           let delta = pfgaddrstr_addr a in
           if pubaddr_p delta then raise BadCommandForm;
           begin
             try
               let (bhd,bhs) = DbBlockHeader.dbget blkid in
               let alpha = bhd.stakeaddr in
               (h,blkid,alpha,delta)
             with Not_found ->
               raise (Failure (Printf.sprintf "Do not have header %s\n" h));
           end
       | _ -> raise BadCommandForm
      in
      begin
        try
          let s kl = List.find (fun (_,_,_,_,beta,_) -> beta = alpha) kl in
          let (k,b,(x,y),_,_,_) = s !Commands.walletkeys_staking in
          try
            let bd = DbBlockDelta.dbget blkid in
            let (gamma,scr) = Script.bountyfundveto alpha in
            match get_bestblock_print_warnings oc with
            | None -> Printf.fprintf oc "No blocks yet\n"
            | Some(h,lbk,ltx) ->
               let (_,_,_,_,_,_,blkh) = Db_outlinevals.dbget (hashpair lbk ltx) in
               let (_,tm,lr,tr,sr) = Db_validheadervals.dbget (hashpair lbk ltx) in
               if termaddr_p delta then
                 begin
                   let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq delta) in
                   if not (hl = HNil) then
                     raise (Failure (Printf.sprintf "There are already assets at %s.\nPlease choose an unused term address for a bounty.\n" (addr_pfgaddrstr delta)))
                 end;
               let f beta =
                 let hl = ctree_lookup_addr_assets true true (CHash(lr)) (addr_bitseq beta) in
                 match
                   hlist_lookup_asset_gen true true true
                     (fun a -> match a with (_,_,Some(gamma2,n2,r2),Currency(_)) when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> true | _ -> false)
                     hl
                 with
                 | Some(aid,_,_,Currency(v)) ->
                    let txfee = Int64.mul 2000L !Config.defaulttxfee in
                    if v <= txfee then
                      Printf.fprintf oc "Not enough for txfee. Consider reducing defaulttxfee in proofgold.conf.\n"
                    else
                      let tau = ([(beta,aid)],[delta,(None,if termaddr_p delta then Bounty(Int64.sub v txfee) else Currency(Int64.sub v txfee))]) in
                      let (stau,si,so) = Commands.signtx2 oc lr (tau,([],[])) [(scr,gamma)] [] (Some([(k,b,(x,y),alpha)])) in
                      if (si && so) then
                        begin
                          Commands.sendtx2 oc blkh tm tr sr lr (stxsize stau) stau;
                          Printf.fprintf oc "Sent veto transaction.\n";
                          if payaddr_p delta then
                            Printf.fprintf oc "Make sure to place at least 25 bars worth of bounties on meaningful unproven propositions.\n"
                        end
                      else
                        Printf.fprintf oc "Problem signing veto tx.\n"
                 | _ ->
                    Printf.fprintf oc "Could not find bounty fund reward output in current ledger.\nIt is probably too late to veto.\n"
               in
               match bd.stakeoutput with
               | (beta,(Some(gamma2,n2,r2),Currency(_)))::_ when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> f beta
               | _::(beta,(Some(gamma2,n2,r2),Currency(_)))::_ when not r2 && n2 = 0L && gamma2 = p2shaddr_payaddr gamma -> f beta
               | _ ->
                  Printf.fprintf oc "Could not find bounty fund reward output in coinstake.\n"
          with Not_found ->
            Printf.fprintf oc "Do not have delta %s\n" h
        with Not_found ->
          Printf.fprintf oc "Do not have private key for stake address in wallet.\n"
      end);
  ac "blockchain" "blockchain [<n>]" "Print the blockchain up to the most recent <n> blocks, with a default of 1000 blocks."
    (fun oc al ->
      match al with
      | [] -> Commands.pblockchain oc (get_bestblock_print_warnings oc) 1000
      | [n] -> let n = int_of_string n in Commands.pblockchain oc (get_bestblock_print_warnings oc) n
      | _ -> raise BadCommandForm);
  ac "reprocessblockchain" "reprocessblockchain [<n>]" "reprocess the block chain from the block at height n up to the current block, where by default n=1 (the genesis block)"
    (fun oc al ->
      match al with
      | [] -> Commands.reprocess_blockchain oc (get_bestblock_print_warnings oc) 1
      | [n] -> let n = int_of_string n in Commands.reprocess_blockchain oc (get_bestblock_print_warnings oc) n
      | _ -> raise BadCommandForm);
  ac "reprocessblock" "reprocessblock <blockid> <ltcblock> <ltcburntx>" "Manually reprocess a given block.\nThis is useful if either -ltcoffline is set or if part of the current ledger seems to be missing from the local node.\nIf the current node has the full ledger from before the block,\nthen processing the block should ensure the node has the resulting full ledger."
    (fun oc al ->
      match al with
      | [h;lbk;ltx] ->
         let h = hexstring_hashval h in
         let lbk = hexstring_hashval lbk in
         let ltx = hexstring_hashval ltx in
         let lh = hashpair lbk ltx in
         Db_validheadervals.dbdelete lh;
         Db_validblockvals.dbdelete lh;
         DbInvalidatedBlocks.dbdelete h;
         reprocessblock oc h lbk ltx
      | _ -> raise (Failure "reprocessblock <blockid> <ltcblock> <ltcburntx>"));;

let rec parse_command_r l i n =
  if i < n then
    let j = ref i in
    while !j < n && l.[!j] = ' ' do
      incr j
    done;
    let b = Buffer.create 20 in
    while !j < n && not (List.mem l.[!j] [' ';'"';'\'']) do
      Buffer.add_char b l.[!j];
      incr j
    done;
    let a = Buffer.contents b in
    let c d = if a = "" then d else a::d in
    if !j < n && l.[!j] = '"' then
      c (parse_command_r_q l (!j+1) n)
    else if !j < n && l.[!j] = '\'' then
      c (parse_command_r_sq l (!j+1) n)
    else
      c (parse_command_r l (!j+1) n)
  else
    []
and parse_command_r_q l i n =
  let b = Buffer.create 20 in
  let j = ref i in
  while !j < n && not (l.[!j] = '"') do
    Buffer.add_char b l.[!j];
    incr j
  done;
  if !j < n then
    Buffer.contents b::parse_command_r l (!j+1) n
  else
    raise (Failure("missing \""))
and parse_command_r_sq l i n =
  let b = Buffer.create 20 in
  let j = ref i in
  while !j < n && not (l.[!j] = '\'') do
    Buffer.add_char b l.[!j];
    incr j
  done;
  if !j < n then
    Buffer.contents b::parse_command_r l (!j+1) n
  else
    raise (Failure("missing '"))

let parse_command l =
  let ll = parse_command_r l 0 (String.length l) in
  match ll with
  | [] -> raise Exit (*** empty command, silently ignore ***)
  | (c::al) -> (c,al)

let do_command oc l =
  let (c,al) = parse_command l in
  if c = "help" then
    begin
      match al with
      | [a] ->
	  begin
	    try
	      let (h,longhelp,_) = Hashtbl.find commandh a in
	      Printf.fprintf oc "%s\n" h;
	      if not (longhelp = "") then Printf.fprintf oc "%s\n" longhelp
	    with Not_found ->
	      Printf.fprintf oc "Unknown command %s\n" a;
	  end
      | _ ->
	  Printf.fprintf oc "Available Commands:\n";
	  List.iter
	    (fun c -> Printf.fprintf oc "%s\n" c)
	    !sortedcommands;
	  Printf.fprintf oc "\nFor more specific information: help <command>\n";
    end
  else
    try
      let (_,_,f) = Hashtbl.find commandh c in
      try
        f oc al;
        flush oc
      with Not_found -> raise (Failure "Not_found raised by command")
    with Not_found ->
      Printf.fprintf oc "Unknown command %s\n" c;;

let init_ledger () =
  let inith = !genesisledgerroot in
  if not (DbCTreeAtm.dbexists inith) then
    begin
      let hfthy = Checking.hfthy in
      let hfthyid = Checking.hfthyid in
      log_string (Printf.sprintf "Creating initial hf theory with id %s\n" (hashval_hexstring hfthyid));
      DbTheory.dbput hfthyid hfthy;
      let hfalpha = hashval_pub_addr hfthyid in
      let nonce = (0l,0l,0l,0l,0l,0l,0l,0l) in
      let burnpayaddr = (false,0l,0l,0l,0l,0l) in
      let inittauout = ref [(hfalpha,(None,TheoryPublication(burnpayaddr,nonce,Checking.hfthyspec)))] in
      let (_,hfaxhs) = Checking.hfthy in
      List.iter
        (fun axh ->
          inittauout := (hashval_term_addr axh,(Some(burnpayaddr,0L,false),OwnsProp(axh,burnpayaddr,Some(0L))))::!inittauout; (* ownership of pure prop of hf ax; free to use forever *)
          let axhthyid = hashtag (hashopair2 (Some(hfthyid)) axh) 33l in
          inittauout := (hashval_term_addr axhthyid,(Some(burnpayaddr,0L,false),OwnsProp(axhthyid,burnpayaddr,Some(0L))))::!inittauout) (* ownership of theory prop of hf ax; free to use forever *)
        hfaxhs;
      flush stdout;
      let inittau : tx = ([],!inittauout) in
      match tx_octree_trans false false 0L inittau None with
      | None -> Printf.printf "Something is terribly wrong.\n"; flush stdout; !exitfn 1
      | Some(initc) ->
         let inith2 = save_ctree_atoms initc in
         if not (inith = inith2) then
           (Printf.printf "Initial ledger hash root mismatch.\nExpected %s\nFound %s\n" (hashval_hexstring inith) (hashval_hexstring inith2); flush stdout; !exitfn 1);
         match txout_update_ottree !inittauout None with
         | None -> Printf.printf "Something is terribly wrong.\n"; flush stdout; !exitfn 1
         | Some(initthytree) ->
            match ottree_hashroot (Some(initthytree)) with
            | Some(initthytreeroot) when initthytreeroot = Checking.initthytreeroot ->
               DbTheoryTree.dbput initthytreeroot (None,[hfthyid])
            | _ -> Printf.printf "Init thy tree root mismatch."; flush stdout; !exitfn 1
    end;;

let set_signal_handlers () =
(*  let generic_signal_handler str sg =
    Utils.log_string (Printf.sprintf "thread %d got signal %d (%s) - terminating\n" (Thread.id (Thread.self ())) sg str);
    !exitfn 1;
  in *)
(*  Sys.set_signal Sys.sigvtalrm Sys.Signal_ignore; (* these might make sense, but not sure *)
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
  Sys.set_signal Sys.sigprof Sys.Signal_ignore;
  Sys.set_signal Sys.sigchld Sys.Signal_ignore; *)
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle
       (fun sg ->
         Printf.printf "got sigint signal. Terminating.\n";
         !exitfn 1));
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  ();;

let initialize () =
  begin
    let datadir = if !Config.testnet then (Filename.concat !Config.datadir "testnet") else !Config.datadir in
    if !Config.testnet then
      begin
	if !Config.ltcrpcport = 9332 then Config.ltcrpcport := 19332;
        ltctestnet();
        max_target := shift_left_big_int unit_big_int 208;
        genesistarget := shift_left_big_int unit_big_int 207;
      end;
    genesisstakemod := !ltc_oldest_to_consider; (** use the oldest ltc block hash as the initial stake modifier **)
    Config.genesistimestamp := Int64.add 3600L !ltc_oldest_to_consider_time; (** genesis time is 1 hour after the oldest ltc block to consider **)
    Gc.set { (Gc.get ()) with Gc.stack_limit = !Config.gc_stack_limit; Gc.space_overhead = !Config.gc_space_overhead; };
    if Sys.file_exists (Filename.concat datadir "lock") then
      begin
	if not !Config.daemon then
	  begin
	    Printf.printf "Cannot start Proofgold. Do you already have Proofgold running? If not, remove: %s\n" (Filename.concat datadir "lock");
	    flush stdout;
	    exit 1;
	  end;
      end;
    lock datadir;
    if not !Config.daemon then (Printf.printf "Initializing the database...\n"; flush stdout);
    let dbdir = Filename.concat datadir "db" in
    begin
      try
        dbconfig dbdir; (*** configure the database ***)
      with
      | NoBootstrapURL ->
         if not !Config.daemon then
           (Printf.printf "Searching the ltc chain for a bootstrap URL\n"; flush stdout);
         search_ltc_bootstrap_url ();
         if !Config.bootstrapurl = "" then
           begin
             Printf.printf "No bootstrap url found.\n";
             !exitfn 1;
           end
         else
           dbconfig dbdir
    end;
    DbTheory.dbinit();
    DbTheoryTree.dbinit();
    DbSigna.dbinit();
    DbSignaTree.dbinit();
    DbAsset.dbinit();
    DbAssetIdAt.dbinit();
    DbSTx.dbinit();
    DbHConsElt.dbinit();
    DbHConsEltAt.dbinit();
    DbCTreeLeaf.dbinit();
    DbCTreeLeafAt.dbinit();
    DbCTreeAtm.dbinit();
    DbCTreeAtmAt.dbinit();
    DbCTreeElt.dbinit();
    DbCTreeEltAt.dbinit();
    DbBlockHeader.dbinit();
    DbBlockDelta.dbinit();
    DbInvalidatedBlocks.dbinit();
    DbLtcPfgStatus.dbinit();
    DbLtcBurnTx.dbinit();
    DbLtcBlock.dbinit();
    Db_outlinevals.dbinit();
    Db_validheadervals.dbinit();
    Db_validblockvals.dbinit();
    Db_outlinesucc.dbinit();
    Db_blockburns.dbinit();
    openlog(); (*** Don't open the log until the config vars are set, so if we know whether or not it's testnet. ***)
    init_ledger();
    if not !Config.daemon then (Printf.printf "Initialized.\n"; flush stdout);
    let sout = if !Config.daemon then !Utils.log else stdout in
    if !createsnapshot then
      begin
	match !snapshot_dir with
	| None ->
	    Printf.fprintf sout "No snapshot directory given.\n";
	    !exitfn 1
	| Some(dir) -> (*** then creating a snapshot ***)
	    Printf.fprintf sout "Creating snapshot.\n"; flush sout;
	    let fin : (hashval,unit) Hashtbl.t = Hashtbl.create 10000 in
	    begin
	      if Sys.file_exists dir then
		if Sys.is_directory dir then
		  ()
		else
		  raise (Failure (dir ^ " is a file not a directory"))
	      else
		begin
		  Unix.mkdir dir 0b111111000
		end
	    end;
	    let headerfile = open_out_bin (Filename.concat dir "headers") in
	    let blockfile = open_out_bin (Filename.concat dir "blocks") in
	    let ctreeeltfile = open_out_bin (Filename.concat dir "ctreeelts") in
	    let hconseltfile = open_out_bin (Filename.concat dir "hconselts") in
	    let assetfile = open_out_bin (Filename.concat dir "assets") in
	    List.iter
	      (fun h ->
		if not (Hashtbl.mem fin h) then
		  begin
		    Hashtbl.add fin h ();
                    try
		      let bh = DbBlockHeader.dbget h in
		      let bd = DbBlockDelta.dbget h in
		      seocf (seo_block seoc (bh,bd) (blockfile,None))
		    with e ->
		      Printf.fprintf sout "WARNING: Exception called when trying to save block %s: %s\n" (hashval_hexstring h) (Printexc.to_string e)
		  end)
	      !snapshot_blocks;
	    List.iter
	      (fun h ->
		if not (Hashtbl.mem fin h) then
		  begin
		    Hashtbl.add fin h ();
                    try
		      let bh = DbBlockHeader.dbget h in
		      seocf (seo_blockheader seoc bh (headerfile,None));
		    with e ->
		      Printf.fprintf sout "WARNING: Exception called when trying to save header %s: %s\n" (hashval_hexstring h) (Printexc.to_string e)
		  end)
	      !snapshot_headers;
	    let supp = List.map addr_bitseq !snapshot_addresses in
	    List.iter
	      (fun h -> dbledgersnapshot_ctree_top (ctreeeltfile,hconseltfile,assetfile) fin supp h !snapshot_shards)
	      !snapshot_ledgerroots;
	    close_out_noerr headerfile;
	    close_out_noerr blockfile;
	    close_out_noerr ctreeeltfile;
	    close_out_noerr hconseltfile;
	    close_out_noerr assetfile;
	    closelog();
	    !exitfn 0;
      end;
    if !importsnapshot then
      begin
	match !snapshot_dir with
	| None ->
	    Printf.fprintf sout "No snapshot directory given.\n";
	    !exitfn 1
	| Some(dir) -> (*** then creating a snapshot ***)
	    Printf.fprintf sout "Importing snapshot.\n"; flush sout;
	    let headerfile = open_in_bin (Filename.concat dir "headers") in
	    let blockfile = open_in_bin (Filename.concat dir "blocks") in
	    let ctreeeltfile = open_in_bin (Filename.concat dir "ctreeelts") in
	    let hconseltfile = open_in_bin (Filename.concat dir "hconselts") in
	    let assetfile = open_in_bin (Filename.concat dir "assets") in
	    begin
	      try
		while true do
		  let ((bh,bd),_) = sei_block seic (blockfile,None) in
		  let h = blockheader_id bh in
		  DbBlockHeader.dbput h bh;
		  DbBlockDelta.dbput h bd;
		done
	      with _ -> ()
	    end;
	    begin
	      try
		while true do
		  let (bh,_) = sei_blockheader seic (headerfile,None) in
		  let h = blockheader_id bh in
		  DbBlockHeader.dbput h bh;
		done
	      with _ -> ()
	    end;
	    begin
	      try
		while true do
		  let (c,_) = sei_ctree seic (ctreeeltfile,None) in
		  let h = ctree_hashroot c in
		  DbCTreeElt.dbput h c;
		done
	      with _ -> ()
	    end;
	    begin
	      try
		while true do
		  let ((ah,hr),_) = sei_prod sei_hashval (sei_option (sei_prod sei_hashval sei_int8)) seic (hconseltfile,None) in
		  let (h,_) = nehlist_hashroot (NehConsH(ah,match hr with None -> HNil | Some(hr,l) -> HHash(hr,l))) in
		  DbHConsElt.dbput h (ah,hr)
		done
	      with _ -> ()
	    end;
	    begin
	      try
		while true do
		  let (a,_) = sei_asset seic (assetfile,None) in
		  let h = hashasset a in
		  DbAsset.dbput h a
		done
	      with _ -> ()
	    end;
	    close_in_noerr headerfile;
	    close_in_noerr blockfile;
	    close_in_noerr ctreeeltfile;
	    close_in_noerr hconseltfile;
	    close_in_noerr assetfile;
	    closelog();
	    !exitfn 0;
      end;
    begin
      match !check_ledger with
      | None -> ()
      | Some(lr) ->
	  let totatoms = ref 0L in
	  let totbounties = ref 0L in
	  let rec check_asset h =
	    try
	      let a = DbAsset.dbget h in
	      match a with
	      | (_,_,_,Currency(v)) -> totatoms := Int64.add v !totatoms
	      | (_,_,_,Bounty(v)) -> totbounties := Int64.add v !totbounties
	      | _ -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: asset %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec check_hconselt h =
	    try
	      let (ah,hr) = DbHConsElt.dbget h in
	      check_asset ah;
	      match hr with
	      | Some(h,_) -> check_hconselt h
	      | None -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: hconselt %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec check_ledger_rec h =
	    try
	      let c = DbCTreeElt.dbget h in
	      check_ctree_rec c 9
	    with Not_found ->
	      Printf.fprintf sout "WARNING: ctreeelt %s is not in database\n" (hashval_hexstring h)
	  and check_ctree_rec c i =
	    match c with
	    | CHash(h) -> check_ledger_rec h
	    | CLeaf(_,NehHash(h,_)) -> check_hconselt h
	    | CLeft(c0) -> check_ctree_rec c0 (i-1)
	    | CRight(c1) -> check_ctree_rec c1 (i-1)
	    | CBin(c0,c1) ->
		check_ctree_rec c0 (i-1);
		check_ctree_rec c1 (i-1)
	    | _ ->
		Printf.fprintf sout "WARNING: unexpected non-element ctree at level %d:\n" i;
		print_ctree sout c
	  in
	  check_ledger_rec lr;
	  Printf.fprintf sout "Total Currency Assets: %Ld atoms (%s bars)\n" !totatoms (bars_of_atoms !totatoms);
	  Printf.fprintf sout "Total Bounties: %Ld atoms (%s bars)\n" !totbounties (bars_of_atoms !totbounties);
	  !exitfn 0
    end;
    begin
      match !build_extraindex with
      | None -> ()
      | Some(lr) ->
	  let rec extraindex_asset h alpha =
	    try
	      let a = DbAsset.dbget h in
	      DbAssetIdAt.dbput (assetid a) alpha
	    with Not_found ->
	      Printf.fprintf sout "WARNING: asset %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec extraindex_hconselt h alpha =
	    try
	      let (ah,hr) = DbHConsElt.dbget h in
	      DbHConsEltAt.dbput ah alpha;
	      extraindex_asset ah alpha;
	      match hr with
	      | Some(h,_) -> extraindex_hconselt h alpha
	      | None -> ()
	    with Not_found ->
	      Printf.fprintf sout "WARNING: hconselt %s is not in database\n" (hashval_hexstring h)
	  in
	  let rec extraindex_ledger_rec h pl =
	    try
	      let c = DbCTreeElt.dbget h in
	      DbCTreeEltAt.dbput h (List.rev pl);
	      extraindex_ctree_rec c 9 pl
	    with Not_found ->
	      Printf.fprintf sout "WARNING: ctreeelt %s is not in database\n" (hashval_hexstring h)
	  and extraindex_ctree_rec c i pl =
	    match c with
	    | CHash(h) -> extraindex_ledger_rec h pl
	    | CLeaf(bl,NehHash(h,_)) -> extraindex_hconselt h (bitseq_addr (List.rev_append pl bl))
	    | CLeft(c0) -> extraindex_ctree_rec c0 (i-1) (false::pl)
	    | CRight(c1) -> extraindex_ctree_rec c1 (i-1) (true::pl)
	    | CBin(c0,c1) ->
		extraindex_ctree_rec c0 (i-1) (false::pl);
		extraindex_ctree_rec c1 (i-1) (true::pl)
	    | _ ->
		Printf.fprintf sout "WARNING: unexpected non-element ctree at level %d:\n" i;
		print_ctree sout c
	  in
	  extraindex_ledger_rec lr [];
	  !exitfn 0
    end;
    begin
      match !netlogreport with
      | None -> ()
      | Some([]) ->
	  Printf.fprintf sout "Expected -netlogreport <sentlogfile> [<reclogfile>*]\n";
	  !exitfn 1
      | Some(sentf::recfl) ->
	  let extra_log_info mt ms = (*** for certain types of messages, give more information ***)
	    match mt with
	    | Inv ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int32 seis !c in
		  Printf.fprintf sout "Inv msg %ld entries\n" n;
		  c := cn;
		  for j = 1 to Int32.to_int n do
		    let ((i,h),cn) = sei_prod sei_int8 sei_hashval seis !c in
		    c := cn;
		    Printf.fprintf sout "Inv %d %s\n" i (hashval_hexstring h);
		  done
		end
	    | GetHeader ->
		begin
		  let (h,_) = sei_hashval seis (ms,String.length ms,None,0,0) in
		  Printf.fprintf sout "GetHeader %s\n" (hashval_hexstring h)
		end
	    | GetHeaders ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
		  c := cn;
		  Printf.fprintf sout "GetHeaders requesting these %d headers:\n" n;
		  for j = 1 to n do
		    let (h,cn) = sei_hashval seis !c in
		    c := cn;
		    Printf.fprintf sout "%d. %s\n" j (hashval_hexstring h);
		  done
		end
	    | Headers ->
		begin
		  let c = ref (ms,String.length ms,None,0,0) in
		  let (n,cn) = sei_int8 seis !c in (*** peers can request at most 255 headers at a time **)
		  Printf.fprintf sout "Got %d Headers\n" n;
		  c := cn;
		  for j = 1 to n do
		    let (h,cn) = sei_hashval seis !c in
		    let (bh,cn) = sei_blockheader seis cn in
		    c := cn;
		    Printf.fprintf sout "%d. %s\n" j (hashval_hexstring h)
		  done
		end
	    | _ -> ()
	  in
	  Printf.fprintf sout "++++++++++++++++++++++++\nReport of all sent messages:\n";
	  let f = open_in_bin sentf in
	  begin
	    try
	      while true do
		let (tmstmp,_) = sei_int64 seic (f,None) in
		let gtm = Unix.gmtime (Int64.to_float tmstmp) in
		Printf.fprintf sout "Sending At Time: %Ld (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		let (magic,_) = sei_int32 seic (f,None) in
		if magic = 0x44616c54l then Printf.fprintf sout "Testnet message\n" else if magic = 0x44616c4dl then Printf.fprintf sout "Mainnet message\n" else Printf.fprintf sout "Bad Magic Number %08lx\n" magic;
		let rby = input_byte f in
		if rby = 0 then
		  Printf.fprintf sout "Not a reply\n"
		else if rby = 1 then
		  begin
		    let (h,_) = sei_hashval seic (f,None) in
		    Printf.fprintf sout "Reply to %s\n" (hashval_hexstring h)
		  end
		else
		  Printf.fprintf sout "Bad Reply Byte %d\n" rby;
		let mti = input_byte f in
		Printf.fprintf sout "Message type %d: %s\n" mti (try string_of_msgtype (msgtype_of_int mti) with Not_found -> "no such message type");
		let (msl,_) = sei_int32 seic (f,None) in
		Printf.fprintf sout "Message contents length %ld bytes\n" msl;
		let (mh,_) = sei_hashval seic (f,None) in
		Printf.fprintf sout "Message contents hash %s\n" (hashval_hexstring mh);
		let sb = Buffer.create 100 in
		for i = 1 to (Int32.to_int msl) do
		  let x = input_byte f in
		  Buffer.add_char sb (Char.chr x)
		done;
		let s = Buffer.contents sb in
		Printf.fprintf sout "Message contents: %s\n" (string_hexstring s);
		try let mt = msgtype_of_int mti in extra_log_info mt s with Not_found -> ()
	      done
	    with
	    | End_of_file -> ()
	    | e -> Printf.fprintf sout "Exception: %s\n" (Printexc.to_string e)
	  end;
	  close_in_noerr f;
	  List.iter
	    (fun fn ->
	      Printf.fprintf sout "++++++++++++++++++++++++\nReport of all messages received via %s:\n" fn;
	      let f = open_in_bin fn in
	      begin
		try
		  while true do
		    let tmstmp : float = input_value f in
		    let gtm = Unix.gmtime tmstmp in
		    Printf.fprintf sout "Received At Time: %f (UTC %02d %02d %04d %02d:%02d:%02d)\n" tmstmp gtm.Unix.tm_mday (1+gtm.Unix.tm_mon) (1900+gtm.Unix.tm_year) gtm.Unix.tm_hour gtm.Unix.tm_min gtm.Unix.tm_sec;
		    let rmmm : hashval option * hashval * msgtype * string = input_value f in
		    let (replyto,mh,mt,m) = rmmm in
		    begin
		      match replyto with
		      | None -> Printf.fprintf sout "Not a reply\n"
		      | Some(h) -> Printf.fprintf sout "Reply to %s\n" (hashval_hexstring h)
		    end;
		    Printf.fprintf sout "Message type %d: %s\n" (int_of_msgtype mt) (string_of_msgtype mt);
		    Printf.fprintf sout "Message contents hash %s\n" (hashval_hexstring mh);
		    Printf.fprintf sout "Message contents: %s\n" (string_hexstring m);
		    extra_log_info mt m
		  done
		with
		| End_of_file -> ()
		| e -> Printf.fprintf sout "Exception: %s\n" (Printexc.to_string e)
	      end;
	      close_in_noerr f)
	    recfl;
	  !exitfn 0
    end;
    if not !Config.offline && not !Config.ltcoffline then
      begin
	if not !Config.daemon then (Printf.fprintf sout "Syncing with ltc.\n"; flush sout);
	ltc_init sout;
	if not !Config.daemon then (Printf.fprintf sout "Building block tree.\n"; flush sout);
	initialize_pfg_from_ltc sout !ltc_bestblock;
      end;
    Printf.fprintf sout "Loading wallet\n"; flush sout;
    Commands.load_wallet();
    let efn = !exitfn in
    exitfn := (fun n -> (try Commands.save_wallet() with _ -> ()); efn n);
    if !Config.swapping then
      begin
        Commands.load_swaps();
        let efn = !exitfn in
        exitfn := (fun n -> (try Commands.save_swaps true with _ -> ()); efn n);
      end;
    Printf.fprintf sout "Loading txpool\n"; flush sout;
    Commands.load_txpool();
    (*** We next compute a nonce for the node to prevent self conns; it doesn't need to be cryptographically secure ***)
    if not !random_initialized then initialize_random_seed();
    let n = rand_int64() in
    this_nodes_nonce := n;
    log_string (Printf.sprintf "Nonce: %Ld\n" n);
  end;;

exception Skip

let main () =
  initialize_commands();
  datadir_from_command_line(); (*** if -datadir=... is on the command line, then set Config.datadir so we can find the config file ***)
  process_config_file();
  process_config_args(); (*** settings on the command line shadow those in the config file ***)
  let last_failure = ref None in
  let failure_count = ref 0 in
  let failure_delay() =
    let tm = ltc_medtime() in
    match !last_failure with
    | Some(tm0) ->
	let d = Int64.sub tm tm0 in
	if d > 21600L then (** first failure in 6 hours, reset failure count to 1 and only delay 1 second **)
	  begin
	    failure_count := 1;
	    last_failure := Some(tm);
	    Thread.delay 1.0
	  end
	else if !failure_count > 100 then (** after 100 regular failures, just exit **)
	  begin
	    closelog();
	    !exitfn 1
	  end
	else
	  begin
	    incr failure_count;
	    last_failure := Some(tm);
	    Thread.delay (float_of_int !failure_count) (** with each new failure, delay for longer **)
	  end
    | None ->
	incr failure_count;
	last_failure := Some(tm);
	Thread.delay 1.0
  in
  let readevalloop () =
    while true do
      try
	Printf.printf "%s" !Config.prompt; flush stdout;
	let l = read_line() in
	do_command stdout l
      with
      | GettingRemoteData -> Printf.printf "Requested some remote data; try again.\n"
      | Exit -> () (*** silently ignore ***)
      | End_of_file ->
	  closelog();
	  Printf.printf "Shutting down threads. Please be patient.\n"; flush stdout;
	  !exitfn 0
      | Failure(x) ->
	  Printf.fprintf stdout "Ignoring Uncaught Failure: %s\n" x; flush stdout;
	  failure_delay()
      | BannedPeer -> Printf.fprintf stdout "Banned Peer"
      | exn -> (*** unexpected ***)
	  Printf.fprintf stdout "Ignoring Uncaught Exception: %s\n" (Printexc.to_string exn); flush stdout;
	  failure_delay()
    done
  in
  let daemon_readevalloop () =
    let lst = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let ia = Unix.inet_addr_of_string "127.0.0.1" in
    begin
      try
	Unix.bind lst (Unix.ADDR_INET(ia,!Config.rpcport));
      with _ ->
	Printf.fprintf !Utils.log "Cannot bind to rpcport. Quitting.\n";
	!exitfn 1
    end;
    let efn = !exitfn in
    exitfn := (fun n -> shutdown_close lst; efn n);
    set_signal_handlers();
    Unix.listen lst 1;
    while true do
      try
	let (s,a) = Unix.accept lst in
	let sin = Unix.in_channel_of_descr s in
	let sout = Unix.out_channel_of_descr s in
	try
	  let l = input_line sin in
	  if not (l = !Config.rpcuser) then raise (Failure "bad rpcuser");
	  let l = input_line sin in
	  if not (l = !Config.rpcpass) then raise (Failure "bad rpcpass");
	  let l = input_line sin in
	  do_command sout l;
	  flush sout;
	  shutdown_close s
	with
	| exn ->
	    flush sout;
	    Unix.close s;
	    raise exn
      with
      | Exit -> () (*** silently ignore ***)
      | End_of_file ->
	  closelog();
	  !exitfn 0
      | Failure(x) ->
	  log_string (Printf.sprintf "Ignoring Uncaught Failure: %s\n" x);
	  failure_delay()
      | exn -> (*** unexpected ***)
	  log_string (Printf.sprintf "Ignoring Uncaught Exception: %s\n" (Printexc.to_string exn));
	  failure_delay()
    done
  in
  if !Config.daemon then
    begin
      if !Config.rpcpass = "changeme" then
        begin
          Printf.printf "Refusing to run as a daemon until rpcpass is set\n";
          Printf.printf "Add the following lines to your proofgold.conf file:\n";
          Printf.printf "rpcuser='...'\nrpcpass='...'\nwhere the pass is a secure password.\n";
          !Utils.exitfn 1;
        end;
      match Unix.fork() with
      | 0 ->
	  initialize();
	  if not !Config.offline then
	    begin
	      initnetwork !Utils.log;
	      if !Config.staking then stkth := Some(Thread.create stakingthread ());
	      if !Config.swapping then swpth := Some(Thread.create swappingthread ());
	      if not !Config.ltcoffline then ltc_listener_th := Some(Thread.create ltc_listener ());
	    end;
	  daemon_readevalloop ()
      | pid -> Printf.printf "Proofgold daemon process %d started.\n" pid
    end
  else
    begin
      initialize();
      set_signal_handlers();
      if not !Config.offline then
	begin
	  initnetwork stdout;
	  if !Config.staking then stkth := Some(Thread.create stakingthread ());
	  if !Config.swapping then swpth := Some(Thread.create swappingthread ());
	  if not !Config.ltcoffline then ltc_listener_th := Some(Thread.create ltc_listener ());
	end;
      readevalloop()
    end;;

main();;

