open Ssrast
open Ssrcommon
open Ltac_plugin

val viewtab : Glob_term.glob_constr list array
val add_view_hints : Glob_term.glob_constr list -> int -> unit
val glob_view_hints : Constrexpr.constr_expr list -> Glob_term.glob_constr list

val pfa_with_view :
           ist ->
           ?next:ssripats ref ->
           bool * ssrterm list ->
           EConstr.t ->
           EConstr.t ->
           (EConstr.t -> EConstr.t -> tac_ctx tac_a) ->
           ssrhyps ->
   (goal * tac_ctx) sigma -> EConstr.types * EConstr.t * (goal * tac_ctx) list sigma

val pf_with_view_linear :
           ist ->
           goal sigma ->
           bool * ssrterm list ->
           EConstr.t ->
           EConstr.t ->
           EConstr.types * EConstr.t * goal sigma


