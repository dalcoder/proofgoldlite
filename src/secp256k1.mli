(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

(* This code for secp256k1 is directly taken from Egal. *)

(* Code for the Elliptic Curve secp256k1 *)
(* https://en.bitcoin.it/wiki/Secp256k1 *)

val evenp : Z.t -> bool

(* _p : the 256 bit int prime in secp256k1 *)
val _p : Z.t

(* operations module _p *)
val add : Z.t -> Z.t -> Z.t
val mul : Z.t -> Z.t -> Z.t
val pow : Z.t -> int -> Z.t
val eea : Z.t -> Z.t -> Z.t * Z.t

(* Intended to be points on the curve y^2 = x^3 + 7 *)
(* None is used for the zero point/point at infinity *)
type pt = (Z.t * Z.t) option

(* addition of two points *)
val addp : pt -> pt -> pt

(* scalar multiplication *)
val smulp : Z.t -> pt -> pt

(* base point _g *)
val _g : pt

(* _n : order of _g *)
val _n : Z.t

val curve_y : bool -> Z.t -> Z.t

val seo_pt : (int -> int -> 'a -> 'a) -> pt -> 'a -> 'a
val sei_pt : (int -> 'a -> int * 'a) -> 'a -> pt * 'a
