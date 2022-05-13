(* Copyright (c) 2020 The Proofgold developers *)
(* Copyright (c) 2016 The Qeditas developers *)
(* Copyright (c) 2017-2018 The Dalilcoin developers *)
(* Distributed under the MIT software license, see the accompanying
   file COPYING or http://www.opensource.org/licenses/mit-license.php. *)

open Hash

type stp =
| Base of int
| TpArr of stp * stp
| Prop

type trm =
| DB of int
| TmH of hashval
| Prim of int
| Ap of trm * trm
| Lam of stp * trm
| Imp of trm * trm
| All of stp * trm
| Ex of stp * trm
| Eq of stp * trm * trm

type pf =
| Known of hashval
| Hyp of int
| PrAp of pf * pf
| TmAp of pf * trm
| PrLa of trm * pf
| TmLa of stp * pf
| Ext of stp * stp

type gsign = ((hashval * stp) * trm option) list * (hashval * trm) list

type theoryitem =
| Thyprim of stp
| Thyaxiom of trm
| Thydef of stp * trm

type theoryspec = theoryitem list

type theory = stp list * hashval list

type signaitem =
| Signasigna of hashval
| Signaparam of hashval * stp
| Signadef of stp * trm
| Signaknown of trm

type signaspec = signaitem list

type signa = hashval list * gsign

type docitem =
| Docsigna of hashval
| Docparam of hashval * stp
| Docdef of stp * trm
| Docknown of trm
| Docpfof of trm * pf
| Docconj of trm

type doc = docitem list

