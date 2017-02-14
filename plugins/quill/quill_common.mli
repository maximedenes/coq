open Names
open Context
open Environ
open Evd

val nb_assums : env -> evar_map -> Constr.t -> int
val nb_deps_assums : env -> evar_map -> Constr.t -> int

val mk_anon_id : string -> ('a, 'b) Proofview.Goal.t -> Id.t
