(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Sha256

(* Most of this code is taken directly from Egal. *)

(* Code for the Elliptic Curve secp256k1 *)
(* https://en.bitcoin.it/wiki/Secp256k1 *)

open Zarithint
   
let big2 = big_int_of_string "2"
let big3 = big_int_of_string "3"

let evenp k = Z.is_even k
let oddp k = Z.is_odd k

(* _p : the 256 bit int prime in secp256k1 *)
let _p = big_int_of_string "115792089237316195423570985008687907853269984665640564039457584007908834671663"

(* Z mod _p operations *)

(* x+y mod _p *)
let add x y = mod_big_int (add_big_int x y) _p

(* x-y mod _p *)
let sub x y = mod_big_int (sub_big_int x y) _p

(* x*y mod _p *)
let mul x y = mod_big_int (mult_big_int x y) _p

(* x^n mod _p *)
let pow x n = mod_big_int (power_big_int_positive_int x n) _p

(* x^n mod _p, where n is a big_int *)
let rec bigpow x n =
  if (sign_big_int n > 0) then
    let r = bigpow (mul x x) (shift_right_towards_zero_big_int n 1) in
    if evenp n then
      r
    else
      mul r x
  else
    unit_big_int

(* square root mod p *)
let sqrt_p x = bigpow x (shift_right_towards_zero_big_int (succ_big_int _p) 2)

(* Extended Euclidean Algorithm *)
let rec eea_rec a b x lastx y lasty =
  if (sign_big_int b > 0) then
    let (q,r) = quomod_big_int a b in
    eea_rec b r (sub_big_int lastx (mult_big_int q x)) x (sub_big_int lasty (mult_big_int q y)) y
  else
    (lastx,lasty)

(* assumes a > b *)
let eea a b =
  eea_rec a b zero_big_int unit_big_int unit_big_int zero_big_int

(* multiplicative inverse mod *)
let inv_mod x q =
  let (_,v) = eea q (mod_big_int x q) in v

(* multiplicative inverse mod _p *)
let inv x = inv_mod x _p

(* Intended to be points on the curve y^2 = x^3 + 7 *)
(* None is used for the zero point/point at infinity *)
type pt = (Z.t * Z.t) option

(* Addition for points on the elliptic curve *)
(* Simplified from the general case using the fact that a is 0 *)
(* p,q : points on the curve *)
(* return point p+q *)
let addp p q =
  begin
    match (p,q) with
    | (None,q) -> q
    | (p,None) -> p
    | (Some(xp,yp),Some(xq,yq)) ->
	if eq_big_int xp xq then
	  if eq_big_int (add yp yq) zero_big_int then
	    None
	  else
	    let s = mul (inv (mul big2 yp)) (mul big3 (mul xp xp)) in
	    let xr = add (mul s s) (mul (sub_big_int _p big2) xp) in
	    let yr = mod_big_int (sub_big_int _p (add yp (mul s (sub xr xp)))) _p in
	    Some(xr,yr)
	else
	  let s = mul (sub yp yq) (inv (sub xp xq)) in
	  let xr = sub (mul s s) (add xp xq) in
	  let yr = mod_big_int (sub_big_int _p (add yp (mul s (sub xr xp)))) _p in
	  Some(xr,yr)
  end

let doublep_hash : (md256 * md256,pt) Hashtbl.t = Hashtbl.create 1000
                                                                 
(** addp p p, with caching since this happens with the same p often **)
let doublep p =
  match p with
  | None -> None
  | Some(xp,yp) ->
     let xp2 = big_int_md256 xp in
     let yp2 = big_int_md256 yp in
     try
       Hashtbl.find doublep_hash (xp2,yp2)
     with _ ->
           let q = addp p p in
           Hashtbl.add doublep_hash (xp2,yp2) q;
           q

(* Scalar multiplication *)
(* k : Z.t *)
(* p : point p on the curve *)
(* return point k*p as a point *)
let rec smulp k p =
  if gt_big_int k zero_big_int then
    let q = doublep p in
    let r = smulp (shift_right_towards_zero_big_int k 1) q in
    let r2 = addp p r in
    if evenp k then
      r
    else
      r2
  else
    None

(* base point _g *)
let _g = Some(big_int_of_string "55066263022277343669578718895168534326250603453777594175500187360389116729240",
	      big_int_of_string "32670510020758816978083085130507043184471273380659243275938904335757337482424")

(* _n : order of _g *)
let _n = big_int_of_string "115792089237316195423570985008687907852837564279074904382605163141518161494337"

let curve_y e x =
  let y = sqrt_p (add (pow x 3) (big_int_of_int 7)) in
  if e = evenp y then
    y
  else
    sub_big_int _p y

let seo_pt o p c = seo_option (seo_prod seo_big_int_256 seo_big_int_256) o p c
let sei_pt i c = sei_option (sei_prod sei_big_int_256 sei_big_int_256) i c
