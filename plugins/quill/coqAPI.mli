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

val tclNIY : string -> unit Proofview.tactic

module Option : sig
  include module type of Option
  val assert_get : 'a option -> Pp.std_ppcmds -> 'a
end

val intern_constr_expr : 
  Genintern.glob_sign ->
    Constrexpr.constr_expr -> Glob_term.glob_constr      
