
open Genarg
open Ssrast
open Names
open Ltac_plugin

val ssrtacarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtacarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtacarg : 'a -> 'b -> (int * Ppextend.parenRelation -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : 'a -> 'b -> (int * Ppextend.parenRelation -> 'c -> 'd) -> 'c -> 'd

(************************* generic argument helpers *********************)
(* FIXME: hide?*)
open Genarg

open Proof_type
open Evd
open Refiner
val add_genarg : string -> ('a -> Pp.std_ppcmds) -> 'a Genarg.uniform_genarg_type

