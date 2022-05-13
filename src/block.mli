(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2015-2016 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Sha256
open Hash
open Mathdata
open Logic
open Assets
open Signat
open Ltcrpc
open Tx
open Ctre
open Ctregraft

type stakemod = hashval
val genesisstakemod : stakemod ref
val genesisledgerroot : hashval ref
val genesistarget : Z.t ref
val max_target : Z.t ref

type targetinfo = Z.t

val targetinfo_string : targetinfo -> string

val seo_targetinfo : (int -> int -> 'a -> 'a) -> targetinfo -> 'a -> 'a
val sei_targetinfo : (int -> 'a -> int * 'a) -> 'a -> targetinfo * 'a

val rewfn : int64 -> int64
val hitval : int64 -> hashval -> stakemod -> Z.t

val poburn_stakemod : poburn -> stakemod

val verbose_blockcheck : out_channel option ref

type blockheaderdata = {
    prevblockhash : (hashval * poburn) option;
    pureburn : (hashval * int32) option;
    newtheoryroot : hashval option;
    newsignaroot : hashval option;
    newledgerroot : hashval;
    stakeaddr : p2pkhaddr;
    stakeassetid : hashval;
    timestamp : int64;
    deltatime : int32;
    tinfo : targetinfo;
    prevledger : ctree;
    blockdeltaroot : hashval;
  }

type blockheadersig = {
    blocksignat : signat;
    blocksignatrecid : int;
    blocksignatfcomp : bool;
    blocksignatendorsement : (p2pkhaddr * int * bool * signat) option;
  }

type blockheader = blockheaderdata * blockheadersig

val seo_blockheaderdata : (int -> int -> 'a -> 'a) -> blockheaderdata -> 'a -> 'a
val sei_blockheaderdata : (int -> 'a -> int * 'a) -> 'a -> blockheaderdata * 'a
val seo_blockheader : (int -> int -> 'a -> 'a) -> blockheader -> 'a -> 'a
val sei_blockheader : (int -> 'a -> int * 'a) -> 'a -> blockheader * 'a

type blockdelta = {
    stakeoutput : addr_preasset list;
    prevledgergraft : cgraft;
    blockdelta_stxl : stx list
  }

type block = blockheader * blockdelta

val seo_blockdelta : (int -> int -> 'a -> 'a) -> blockdelta -> 'a -> 'a
val sei_blockdelta : (int -> 'a -> int * 'a) -> 'a -> blockdelta * 'a
val seo_block : (int -> int -> 'a -> 'a) -> block -> 'a -> 'a
val sei_block : (int -> 'a -> int * 'a) -> 'a -> block * 'a

module DbBlockHeader :
    sig
      val dbinit : unit -> unit
      val dbget : Hash.hashval -> blockheader
      val dbexists : Hash.hashval -> bool
      val dbput : Hash.hashval -> blockheader -> unit
      val dbdelete : Hash.hashval -> unit
      val dbpurge : unit -> unit
    end

module DbBlockDelta :
    sig
      val dbinit : unit -> unit
      val dbget : Hash.hashval -> blockdelta
      val dbexists : Hash.hashval -> bool
      val dbput : Hash.hashval -> blockdelta -> unit
      val dbdelete : Hash.hashval -> unit
      val dbpurge : unit -> unit
      val dbbincp : Hash.hashval -> Buffer.t -> unit
    end

val get_blockheaderdata : hashval -> blockheaderdata
val get_blockheadersig : hashval -> blockheadersig
val get_blockheader : hashval -> blockheader
val get_blockdelta : hashval -> blockdelta

val coinstake : block -> tx

val check_hit_b : int64 -> int64 -> obligation -> int64
  -> stakemod -> Z.t -> int64 -> hashval -> p2pkhaddr -> int64 -> bool
val check_hit : int64 -> stakemod -> targetinfo -> blockheaderdata -> int64 -> obligation -> int64 -> int64 -> bool

val hash_blockheaderdata : blockheaderdata -> hashval
val hash_blockheadersig : blockheadersig -> hashval
val blockdelta_hashroot : blockdelta -> hashval
val blockheader_id : blockheader -> hashval

val valid_blockheader_allbutsignat : int64 -> stakemod -> targetinfo -> blockheaderdata -> asset -> int64 -> int64 -> bool
val valid_blockheader_signat : blockheader -> asset -> bool

val valid_blockheader : int64 -> stakemod -> targetinfo -> blockheader -> int64 -> int64 -> hashval -> int32 -> bool
val valid_blockheader_ifburn : int64 -> stakemod -> targetinfo -> blockheader -> int64 -> int64 -> bool

val sanity_check_header : blockheader -> bool

val ctree_of_block : block -> ctree

val txl_of_block : block -> tx * tx list

val retarget : Z.t -> int32 -> Z.t
val difficulty : Z.t -> Z.t

val valid_block : ttree option -> stree option -> int64 -> stakemod -> targetinfo -> block -> int64 -> int64 -> hashval -> int32 -> (ttree option * stree option) option
val valid_block_ifburn : ttree option -> stree option -> int64 -> stakemod -> targetinfo -> block -> int64 -> int64 -> (ttree option * stree option) option

val blockheader_succ_a : hashval -> int64 -> targetinfo -> blockheader -> bool
val blockheader_succ_b : hashval -> hashval -> int64 -> targetinfo -> blockheader -> bool
val blockheader_succ : blockheader -> blockheader -> bool

val collect_header_inv_nbhd : int -> hashval -> (int * hashval) list ref -> unit

