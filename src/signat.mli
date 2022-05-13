(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Sha256
open Hash
open Secp256k1

exception ZeroValue

type signat = Z.t * Z.t

val decode_signature : string -> int * bool * signat
val encode_signature : int -> bool -> signat -> string

val signat_big_int : Z.t -> Z.t -> Z.t -> signat
val signat_hashval : hashval -> Z.t -> Z.t -> signat

val verify_signed_big_int : Z.t -> pt -> signat -> bool
val verify_signed_hashval : hashval -> pt -> signat -> bool
val verify_p2pkhaddr_signat : Z.t -> p2pkhaddr -> signat -> int -> bool -> bool

val verifybitcoinmessage : p2pkhaddr -> int -> bool -> signat -> string -> bool
val verifybitcoinmessage_recover : p2pkhaddr -> int -> bool -> signat -> string -> (Z.t * Z.t) option

val md256_of_bitcoin_message : string -> md256

val verifyproofgoldmessage : pt -> signat -> string -> bool

val md256_of_proofgold_message : string -> md256

val sign_proofgold_message : string -> Z.t -> Z.t -> signat

val repeat_rand : (Z.t -> signat) -> (unit -> Z.t) -> Z.t * signat

val seo_signat : (int -> int -> 'a -> 'a) -> signat -> 'a -> 'a
val sei_signat : (int -> 'a -> int * 'a) -> 'a -> signat * 'a

val hashsignat : signat -> hashval
