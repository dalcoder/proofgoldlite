(* Copyright (c) 2019 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash
open Logic
open Mathdata

val input_token : in_channel -> string
val input_theoryspec : in_channel -> theoryspec * hashval option * addr option
    * (string,hashval) Hashtbl.t
    * (hashval,string) Hashtbl.t
    * (hashval,payaddr) Hashtbl.t
    * (bool * hashval,payaddr * (int64 option)) Hashtbl.t
val input_signaspec : in_channel -> hashval option -> stree option -> signaspec * hashval option * addr option
    * (string,stp * hashval) Hashtbl.t
    * (hashval,string) Hashtbl.t
    * (string,hashval) Hashtbl.t
    * (hashval,string) Hashtbl.t
val input_doc : in_channel -> hashval option -> stree option -> doc * hashval option * addr option
    * (string,stp * hashval) Hashtbl.t
    * (hashval,string) Hashtbl.t
    * (string,hashval) Hashtbl.t
    * (hashval,string) Hashtbl.t
    * (string,hashval) Hashtbl.t
    * (hashval,payaddr) Hashtbl.t * (bool * hashval,payaddr * (int64 option)) Hashtbl.t
    * (hashval,payaddr) Hashtbl.t * (bool * hashval,payaddr * (int64 option)) Hashtbl.t
    * (hashval,int64 * (payaddr * int64) option) Hashtbl.t

val output_stp : stp -> (int,string) Hashtbl.t -> string
val output_trm : trm -> (int,string) Hashtbl.t -> (hashval,string) Hashtbl.t -> (trm,string) Hashtbl.t -> string list -> string
val output_pf : pf -> (int,string) Hashtbl.t -> (hashval,string) Hashtbl.t -> (trm,string) Hashtbl.t -> (hashval,string) Hashtbl.t -> string list -> string list -> string
val decl_let_hfprims : out_channel -> (int,string) Hashtbl.t -> (trm,string) Hashtbl.t -> trm -> unit
