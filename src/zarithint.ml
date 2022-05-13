(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

let zero_big_int = Z.zero
let unit_big_int = Z.one
let two_big_int = Z.of_int 2

let big_int_of_string x =
  let r = Z.of_string x in
  r

let string_of_big_int x =
  let r = Z.to_string x in
  r

let int_of_big_int x = Z.to_int x
let int32_of_big_int x = Z.to_int32 x
let int64_of_big_int x = Z.to_int64 x

let big_int_of_int x =
  let r = Z.of_int x in
  r

let big_int_of_int32 x =
  let r = Z.of_int32 x in
  r

let big_int_of_int64 x =
  let r = Z.of_int64 x in
  r

let eq_big_int x y = Z.equal x y
let le_big_int x y = Z.leq x y
let ge_big_int x y = Z.geq x y
let lt_big_int x y = Z.lt x y
let gt_big_int x y = Z.gt x y
let sign_big_int x = Z.sign x

let succ_big_int x =
  let r = Z.succ x in
  r

let add_big_int x y =
  let r = Z.add x y in
  r

let add_int_big_int x y = add_big_int (Z.of_int x) y
  
let sub_big_int x y =
  let r = Z.sub x y in
  r
  
let mult_big_int x y =
  let r = Z.mul x y in
  r

let mult_int_big_int x y = mult_big_int (Z.of_int x) y

let div_big_int x y =
  let r = Z.div x y in
  r

let mod_big_int x y =
  let r =
    if Z.sign x < 0 then
      Z.add y (Z.rem x y)
    else
      Z.rem x y
  in
  r
  
let quomod_big_int x y =
  let r = Z.div_rem x y in
  r
  
let power_big_int_positive_int x y =
  let r = Z.pow x y in
  r

let min_big_int x y =
  let r = Z.min x y in
  r

let and_big_int x y =
  let r = Z.logand x y in
  r

let or_big_int x y =
  let r = Z.logor x y in
  r

let shift_left_big_int x y =
  let r = Z.shift_left x y in
  r

let shift_right_towards_zero_big_int x y =
  let r = Z.shift_right_trunc x y in
  r
