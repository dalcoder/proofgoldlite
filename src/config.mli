(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

val datadir : string ref
val offline : bool ref
val ltcoffline : bool ref
val ltcversion : int ref
val ltcsubversion : int ref
val daemon : bool ref
val testnet : bool ref
val staking : bool ref
val swapping : bool ref
val proxyip : string option ref
val ip : string option ref
val ipv6 : bool ref
val port : int ref
val onion : string option ref
val onionlocalport : int ref
val onionremoteport : int ref
val socks : int option ref
val socksport : int ref
val rpcuser : string ref
val rpcpass : string ref
val rpcport : int ref
val ltcrpcip : string ref
val ltcrpconion : string option ref
val ltcrpcport : int ref
val ltcrpcuser : string ref
val ltcrpcpass : string ref
val ltcaddresses : string list ref
val ltctradeaddresses : string list ref
val curl : string ref
val ltcrpcavoidcurl : bool ref
val maxconns : int ref
val lastcheckpoint : string ref
val prompt : string ref
val genesis : bool ref
val genesistimestamp : int64 ref
val maxburn : int64 ref
val ltctxfee : int64 ref
val minltctxfee : int64 ref
val randomseed : string option ref
val minconnstostake : int ref
val minrelayfee : int64 ref
val defaulttxfee : int64 ref
val extraindex : bool ref
val offlinestakerewardsdest : bool ref
val offlinestakerewardslock : string option ref
val generatenewrewardaddresses : bool ref
val stakewithrewards : bool ref
val reward_lock_relative : int64 option ref
val reward_lock_absolute : int64 option ref
val invalidatedblocks : string list ref
val validatedblocks : string list ref
val independentbootstrap : bool ref
val bootstrapurl : string ref
val fullnode : bool ref
val gc_space_overhead : int ref
val gc_stack_limit : int ref
val db_max_in_cache : int ref
val min_conns_pow : int ref
val min_conn_pow_target : int32 ref
val max_conn_pow_tries : int ref
