(* Copyright (c) 2022 The Proofgold Love developers *)
(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Json
open Hash
open Mathdata
open Assets
open Signat
open Ltcrpc
open Tx
open Ctre
open Logic

val walletkeys_staking : (Z.t * bool * (Z.t * Z.t) * string * p2pkhaddr * string) list ref
val walletkeys_nonstaking : (Z.t * bool * (Z.t * Z.t) * string * p2pkhaddr * string) list ref
val walletkeys_staking_fresh : (Z.t * bool * (Z.t * Z.t) * string * p2pkhaddr * string) list ref
val walletkeys_nonstaking_fresh : (Z.t * bool * (Z.t * Z.t) * string * p2pkhaddr * string) list ref
val walletendorsements : (payaddr * payaddr * (Z.t * Z.t) * int * bool * signat) list ref
val walletp2shs : (p2shaddr * string * int list) list ref
val walletwatchaddrs : addr list ref
val walletwatchaddrs_offlinekey : addr list ref
val walletwatchaddrs_offlinekey_fresh : addr list ref
val stakingassets : (p2pkhaddr * hashval * int64 * obligation * int64) list ref

val get_spendable_assets_in_ledger : out_channel -> hashval -> int64 -> (addr * asset * int64) list
val get_atoms_balances_in_ledger : out_channel -> hashval -> int64 -> int64 * int64 * int64 * int64 * int64 * int64 * int64 * int64

val swapselloffers : (string * float * int64 * int64) list ref
val swapredemptions : (hashval * md160 * hashval * md160 * md160) list ref

val load_txpool : unit -> unit
val save_txpool : unit -> unit
val load_wallet : unit -> unit
val save_wallet : unit -> unit
val load_swaps : unit -> unit
val save_swaps : bool -> unit

val printassets : out_channel -> unit
val printassets_in_ledger : out_channel -> hashval -> int64 -> unit
val printctreeinfo : out_channel -> hashval -> unit
val printctreeatm : out_channel -> hashval -> unit
val printctreeelt : out_channel -> hashval -> unit
val printhconselt : out_channel -> hashval -> unit
val printasset : out_channel -> hashval -> unit
val printtx : out_channel -> hashval -> unit

val privkey_from_wallet : p2pkhaddr -> Z.t * bool
val privkey_and_pubkey_from_wallet : p2pkhaddr -> (Z.t * bool) * (Z.t * Z.t)

val ltctopfgaddr : out_channel -> string -> unit
val btctopfgaddr : out_channel -> string -> unit
val pfgtoltcaddr : out_channel -> string -> unit
val pfgtobtcaddr : out_channel -> string -> unit
val pfgtobtcwif : out_channel -> string -> unit
val importwallet : out_channel -> string -> unit
val importprivkey : out_channel -> string -> string -> unit
val importbtcprivkey : out_channel -> string -> string -> unit
val importendorsement : out_channel -> string -> string -> string -> unit
val importp2sh : out_channel -> int list -> unit
val importwatchaddr : out_channel -> string -> string -> unit
val importwatchbtcaddr : out_channel -> string -> string -> unit
val generate_newkeyandaddress : hashval -> string -> Z.t * p2pkhaddr
val get_fresh_offline_address : out_channel -> addr

val reclassify_staking : out_channel -> string -> bool -> unit

val createtx : jsonval -> jsonval -> tx
val createsplitlocktx : out_channel -> hashval -> int64 -> payaddr -> payaddr -> addr -> hashval -> int -> int64 -> int64 -> unit

val signbatchtxsc : out_channel -> hashval -> stx list -> out_channel -> (int list * p2shaddr) list -> (hashval * hashval) list -> (Z.t * bool * (Z.t * Z.t) * p2pkhaddr) list option -> unit
val signtx2 : out_channel -> hashval -> stx -> (int list * p2shaddr) list -> (hashval * hashval) list -> (Z.t * bool * (Z.t * Z.t) * p2pkhaddr) list option -> stx * bool * bool
val signtxc : out_channel -> hashval -> stx -> out_channel -> (int list * p2shaddr) list -> (hashval * hashval) list -> (Z.t * bool * (Z.t * Z.t) * p2pkhaddr) list option -> unit
val savetxtopool : int64 -> int64 -> hashval -> string -> unit
val signtx : out_channel -> hashval -> string -> (int list * p2shaddr) list -> (hashval * hashval) list -> (Z.t * bool * (Z.t * Z.t) * p2pkhaddr) list option -> unit
val simplesigntx : out_channel -> string -> (int list * p2shaddr) list -> (hashval * hashval) list -> (Z.t * bool * (Z.t * Z.t) * p2pkhaddr) list option -> unit
val validatebatchtxs : out_channel -> int64 -> int64 -> hashval option -> hashval option -> hashval -> stx list -> unit
val validatetx2 : out_channel -> int64 -> int64 -> hashval option -> hashval option -> hashval -> int -> stx -> unit
val validatetx : out_channel -> int64 -> int64 -> hashval option -> hashval option -> hashval -> string -> unit
val sendtx2 : out_channel -> int64 -> int64 -> hashval option -> hashval option -> hashval -> int -> stx -> unit
val sendtx : out_channel -> int64 -> int64 -> hashval option -> hashval option -> hashval -> string -> unit

val query_at_block : string -> (hashval * poburn) option -> hashval -> int64 -> jsonval
val query : string -> jsonval
val query_blockheight : int64 -> jsonval

val preassetinfo_report : out_channel -> preasset -> unit

val report_subtop_subsubtop : out_channel -> bool list -> unit

val verifyfullledger : out_channel -> hashval -> unit

val requestfullledger : out_channel -> hashval -> unit

val filter_wallet : hashval -> unit
val dumpwallet : string -> unit
val pblockchain : out_channel -> (hashval * hashval * hashval) option -> int -> unit
val reprocess_blockchain : out_channel -> (hashval * hashval * hashval) option -> int -> unit
val dumpstate : string -> unit

val reportowned : out_channel -> out_channel -> hashval -> unit
val reportbounties : out_channel -> out_channel -> hashval -> unit
val reportpubs : out_channel -> out_channel -> hashval -> unit

val collectable_bounties : out_channel -> hashval -> (addr * asset * asset) list

val createatomicswap : hashval -> md160 -> md160 -> int32 -> p2shaddr * int list
val createhtlc2 : md160 -> md160 -> int32 -> bool -> hashval -> p2shaddr * int list * hashval
val createhtlc : md160 -> md160 -> int32 -> bool -> hashval -> p2shaddr * int list * hashval
val createbtchtlc2 : md160 -> md160 -> int -> bool -> hashval -> p2shaddr * int list * hashval
val createbtchtlc : md160 -> md160 -> int -> bool -> hashval -> p2shaddr * int list * hashval
val createmultisig2 : int -> (string * ((Z.t * Z.t) * bool)) list -> p2shaddr * int list
val createmultisig : int -> jsonval -> p2shaddr * int list
val extract_secret_from_btctx : hashval -> int -> string -> hashval
