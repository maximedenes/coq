(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open CClosure
open Esubst

(***********************************************************************
  s Call-by-value reduction *)

(** Entry point for cbv normalization of a constr *)
type cbv_infos

val create_cbv_infos : RedFlags.reds -> env -> Evd.evar_map -> cbv_infos
val cbv_norm         : strong:bool -> cbv_infos -> constr -> constr
