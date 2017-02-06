open Context
open Environ
open Evd
open Reductionops

val whd_beta : local_reduction_function
val whd_betaiota : local_reduction_function
val whd_betaiotazeta : local_reduction_function
val whd_allnolet : reduction_function
val whd_all : reduction_function

val decompose_assum : env -> evar_map -> Constr.t -> Rel.Declaration.t * Constr.t
