open Context
open Environ
open Evd
open Reductionops
open EConstr
open Ltac_plugin

type term

val decompose_assum : env -> evar_map -> EConstr.t -> EConstr.rel_declaration * EConstr.t

val tclNIY : string -> unit Proofview.tactic

module Option : sig
  include module type of Option
  val assert_get : 'a option -> Pp.std_ppcmds -> 'a
end

val intern_constr_expr : 
  Genintern.glob_sign ->
    Constrexpr.constr_expr -> Glob_term.glob_constr      
