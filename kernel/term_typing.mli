(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Declarations
open Entries

val translate_local_def : structure_body -> env -> Id.t -> definition_entry ->
  constant_def * types * constant_universes

val translate_local_assum : env -> types -> types

val mk_pure_proof : constr -> proof_output

val handle_side_effects : env -> constr -> side_effects -> constr
(** Returns the term where side effects have been turned into let-ins or beta
    redexes. *)

val handle_entry_side_effects : env -> definition_entry -> definition_entry
(** Same as {!handle_side_effects} but applied to entries. Only modifies the
    {!Entries.const_entry_body} field. It is meant to get a term out of a not
    yet type checked proof. *)

val uniq_seff : side_effects -> side_effects

val translate_constant : structure_body -> env -> constant -> constant_entry -> constant_body

val translate_mind :
  env -> mutual_inductive -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> constant -> Cooking.recipe -> constant_body

(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : trust:structure_body -> env -> constant option -> 
  constant_entry -> Cooking.result

val build_constant_declaration :
  constant -> env -> Cooking.result -> constant_body

val set_suggest_proof_using :
  (string -> env -> Id.Set.t -> Id.Set.t -> Id.t list -> string) -> unit
