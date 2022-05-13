(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Zarithint
open Ser
open Sha256
open Hash
open Secp256k1
open Cryptocurr

type signat = Z.t * Z.t

let rec bytelist_to_big_int rst n c =
  if n > 0 then
    match rst with
    | (b::rst2) -> bytelist_to_big_int rst2 (n-1) (or_big_int (shift_left_big_int (big_int_of_int b) ((n-1)*8)) c)
    | [] -> raise (Failure("not enough bytes"))
  else
    (c,rst)

let decode_signature_real sg =
  match Utils.base64decode sg with
  | (by0::rst) ->
      let (r,rst2) = bytelist_to_big_int rst 32 zero_big_int in
      let (s,rst3) = bytelist_to_big_int rst2 32 zero_big_int in
      if rst3 = [] then
	(by0,(r,s))
      else
	raise (Failure("Signature Too Long"))
  | [] -> raise (Failure("Empty Signature"))

let decode_signature sg =
  let (by0,(r,s)) = decode_signature_real sg in
  let by27 = by0-27 in
  let recid = by27 land 3 in
  let fcomp = by27 land 4 > 0 in
  (recid,fcomp,(r,s))

let rec big_int_to_bytelist r l bl =
  if l > 0 then
    big_int_to_bytelist (shift_right_towards_zero_big_int r 8) (l-1) (int_of_big_int (and_big_int r (big_int_of_int 255))::bl)
  else
    bl

let encode_signature recid fcomp (r,s) =
  let by0 = 27 + if fcomp then 4 lor recid else recid in
  Utils.base64encode (by0::big_int_to_bytelist r 32 []@big_int_to_bytelist s 32 [])
  
(** * Digital Signatures for Qeditas ***)
exception ZeroValue

let inv_gen x q =
  let (u,v) = eea q (mod_big_int x q) in
  mod_big_int v q

let signat_big_int e privk randk =
  match smulp randk _g with
  | Some(xr,yr) ->
      let r = mod_big_int xr _n in
      if r = zero_big_int then raise ZeroValue;
      let s = mod_big_int (mult_big_int (inv_gen randk _n) (add_big_int e (mult_big_int r privk))) _n in
      if s = zero_big_int then raise ZeroValue;
      (r,s)
  | None -> raise ZeroValue

let verify_signed_big_int e q (r,s) =
  if lt_big_int r _n && lt_big_int s _n && lt_big_int e _p then
    let sinv = inv_gen s _n in
    let u1 = mod_big_int (mult_big_int e sinv) _n in
    let u2 = mod_big_int (mult_big_int r sinv) _n in
    match addp (smulp u1 _g) (smulp u2 q) with
    | None -> false
    | Some(xr,yr) -> eq_big_int (mod_big_int xr _n) r
  else
    false

let signat_hashval h privk randk = signat_big_int (hashval_big_int h) privk randk

let verify_signed_hashval h q (r,s) = verify_signed_big_int (hashval_big_int h) q (r,s)

(*** The pow function from Egal only works for int exponents, but sqrtp needs it for a big int ***)
let rec bigpow_p x m =
  if gt_big_int m zero_big_int then
    let z = bigpow_p (mul x x) (shift_right_towards_zero_big_int m 1) in
    if evenp m then
      z
    else
      mul z x
  else
    unit_big_int

let sqrtp a =
  bigpow_p a (div_big_int (add_big_int unit_big_int _p) (big_int_of_int 4))

let curve_y x = sqrtp (add (pow x 3) (big_int_of_int 7))

let _minusg = Some(big_int_of_string "55066263022277343669578718895168534326250603453777594175500187360389116729240",
		 big_int_of_string "83121579216557378445487899878180864668798711284981320763518679672151497189239")
		 
let recover_key e (r,s) recid =
  let xr = if recid > 1 then mod_big_int (add_big_int r _n) _p else r in
  let yr1 = curve_y xr in
  let yr = if (recid mod 2 = 0) = (evenp yr1) then yr1 else sub_big_int _p yr1 in
  let rinv = inv_gen r _n in
  smulp rinv (addp (smulp s (Some(xr,yr))) (smulp e _minusg))

let verify_p2pkhaddr_signat e alpha (r,s) recid fcomp =
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_md160 q fcomp = alpha
  | None -> false

let verifymessage alpha recid fcomp (r,s) m =
  let e = md256_big_int (sha256dstr m) in
  match recover_key e (r,s) recid with
  | Some(q) -> pubkey_md160 q fcomp = alpha
  | None -> false

let verifymessage_recover alpha recid fcomp (r,s) m =
  let e = md256_big_int (sha256dstr m) in
  match recover_key e (r,s) recid with
  | Some(q) when pubkey_md160 q fcomp = alpha -> Some(q)
  | _ -> None

let md256_of_bitcoin_message m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  sha256dstr (Buffer.contents ms)

let verifybitcoinmessage alpha recid fcomp (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage alpha recid fcomp (r,s) (Buffer.contents ms)

let verifybitcoinmessage_recover alpha recid fcomp (r,s) m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Bitcoin Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  verifymessage_recover alpha recid fcomp (r,s) (Buffer.contents ms)

let md256_of_proofgold_message m =
  let m = if !Config.testnet then "testnet:" ^ m else m in
  let ml = String.length m in
  let ms = Buffer.create (26 + ml) in
  Buffer.add_string ms "\024Proofgold Signed Message:\n";
  let c = seo_varint seosb (Int64.of_int ml) (ms,None) in (*** output the length as a varint ***)
  seosbf c;
  Buffer.add_string ms m;
  sha256str (Buffer.contents ms)

let verifyproofgoldmessage q (r,s) m =
  let mh = md256_of_proofgold_message m in
  let e = md256_big_int mh in
  verify_signed_big_int e q (r,s)

let sign_proofgold_message m privk randk =
  let h = md256_of_proofgold_message m in
  signat_hashval h privk randk

let rec repeat_rand f r =
  try
    let randk = r() in
    (randk,f randk)
  with ZeroValue -> repeat_rand f r
                        
let seo_signat o rs c = seo_prod seo_big_int_256 seo_big_int_256 o rs c
let sei_signat i c = sei_prod sei_big_int_256 sei_big_int_256 i c

let hashsignat (r,s) = hashpair (big_int_hashval r) (big_int_hashval s)
