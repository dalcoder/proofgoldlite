(* Copyright (c) 2015 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Ser
open Hash

type 'a htree =
  | HLeaf of 'a
  | HBin of 'a htree option * 'a htree option

let rec htree_lookup bl ht =
  match bl,ht with
  | [],HLeaf(x) -> Some(x)
  | false::br,HBin(Some(hl),hr) -> htree_lookup br hl
  | true::br,HBin(hl,Some(hr)) -> htree_lookup br hr
  | _,_ -> None

let rec htree_create bl x =
  match bl with
  | [] -> HLeaf(x)
  | false::br -> HBin(Some(htree_create br x),None)
  | true::br -> HBin(None,Some(htree_create br x))

let rec htree_insert ht bl x =
  match bl with
  | [] -> HLeaf(x)
  | false::br ->
      begin
	match ht with
	| HBin(Some(hl),hr) -> HBin(Some(htree_insert hl br x),hr)
	| HBin(None,hr) -> HBin(Some(htree_create br x),hr)
	| _ ->  raise (Failure "bad htree case")
      end
  | true::br ->
      begin
	match ht with
	| HBin(hl,Some(hr)) -> HBin(hl,Some(htree_insert hr br x))
	| HBin(hl,None) -> HBin(hl,Some(htree_create br x))
	| _ ->  raise (Failure "bad htree case")
      end

let rec ohtree_hashroot f n oht =
  if n > 0 then
    match oht with
    | Some(HBin(hl,hr)) -> hashopair (ohtree_hashroot f (n-1) hl) (ohtree_hashroot f (n-1) hr)
    | _ -> None
  else
    match oht with
    | Some(HLeaf(x)) -> f x
    | _ -> None

let rec seo_htree s o tr c =
  match tr with
  | HLeaf(m) ->
     let c = o 1 0 c in
     let c = s o m c in
     c
  | HBin(l,r) ->
     let c = o 1 1 c in
     let c = seo_option (seo_htree s) o l c in
     let c = seo_option (seo_htree s) o r c in
     c

let rec sei_htree s i c =
  let (b,c) = i 1 c in
  if b = 0 then
    let (m,c) = s i c in
    (HLeaf(m),c)
  else
    let (l,c) = sei_option (sei_htree s) i c in
    let (r,c) = sei_option (sei_htree s) i c in
    (HBin(l,r),c)
