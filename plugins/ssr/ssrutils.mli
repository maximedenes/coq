open Names
open Context
open Environ
open Evd
open Proofview
open Ltac_plugin

val nb_assums : env -> evar_map -> EConstr.t -> int
val nb_deps_assums : env -> evar_map -> EConstr.t -> int

val mk_anon_id : string -> Id.t list -> Id.t

val gentac : Id.t -> Name.t -> unit tactic
