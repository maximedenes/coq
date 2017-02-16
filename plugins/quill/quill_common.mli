open Names
open Context
open Environ
open Evd
open Proofview

val nb_assums : env -> evar_map -> Constr.t -> int
val nb_deps_assums : env -> evar_map -> Constr.t -> int

val mk_anon_id : string -> ('a, 'b) Goal.t -> Id.t

val gentac : Id.t -> Name.t -> unit tactic
