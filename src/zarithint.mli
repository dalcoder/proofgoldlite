(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

val zero_big_int : Z.t
val unit_big_int : Z.t
val two_big_int : Z.t
val big_int_of_string : string -> Z.t
val string_of_big_int : Z.t -> string
val int_of_big_int : Z.t -> int
val big_int_of_int : int -> Z.t
val int32_of_big_int : Z.t -> int32
val big_int_of_int32 : int32 -> Z.t
val int64_of_big_int : Z.t -> int64
val big_int_of_int64 : int64 -> Z.t
val eq_big_int : Z.t -> Z.t -> bool
val le_big_int : Z.t -> Z.t -> bool
val ge_big_int : Z.t -> Z.t -> bool
val lt_big_int : Z.t -> Z.t -> bool
val gt_big_int : Z.t -> Z.t -> bool
val sign_big_int : Z.t -> int
val succ_big_int : Z.t -> Z.t
val add_big_int : Z.t -> Z.t -> Z.t
val add_int_big_int : int -> Z.t -> Z.t
val sub_big_int : Z.t -> Z.t -> Z.t
val mult_big_int : Z.t -> Z.t -> Z.t
val mult_int_big_int : int -> Z.t -> Z.t
val div_big_int : Z.t -> Z.t -> Z.t
val mod_big_int : Z.t -> Z.t -> Z.t
val quomod_big_int : Z.t -> Z.t -> Z.t * Z.t
val power_big_int_positive_int : Z.t -> int -> Z.t
val min_big_int : Z.t -> Z.t -> Z.t
val and_big_int : Z.t -> Z.t -> Z.t
val or_big_int : Z.t -> Z.t -> Z.t
val shift_left_big_int : Z.t -> int -> Z.t
val shift_right_towards_zero_big_int : Z.t -> int -> Z.t
