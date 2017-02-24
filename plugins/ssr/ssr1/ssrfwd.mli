open Names

open Ssrast
open Ssrcommon

val ssrsettac : ist ->  Id.t -> ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ssrterm option)) * ssrdocc) -> v82tac

val ssrposetac : ist -> (Id.t * (ssrfwdfmt * ssrterm)) -> v82tac

val hinttac :
           Tacinterp.interp_sign ->
           bool -> bool * Tacinterp.Value.t option list -> Ssrast.v82tac

val havetac :
           Ssrast.ist ->
           bool *
           ((((Ssrast.ssrclear * Ssrast.ssripat list) * Ssrast.ssripats) *
             Ssrast.ssripats) *
            (((Ssrast.ssrfwdkind * 'a) *
              ('b * (Glob_term.glob_constr * Constrexpr.constr_expr option))) *
             (bool * Tacinterp.Value.t option list))) ->
           bool ->
           bool -> v82tac
val ssrabstract :
           Tacinterp.interp_sign ->
           (Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list
           list * Ssrast.ssrclear -> v82tac

