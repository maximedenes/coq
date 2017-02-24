open Ssrast
open Ssrcommon

val pfa_with_view :
           ist ->
           ?next:ssripats ref ->
           bool * ssrterm list ->
           Term.constr ->
           Term.constr ->
           (Term.constr -> Term.constr -> tac_ctx tac_a) ->
           ssrhyps ->
   (goal * tac_ctx) sigma -> Term.types * Term.constr * (goal * tac_ctx) list sigma

val pf_with_view_linear :
           ist ->
           goal sigma ->
           bool * ssrterm list ->
           Term.constr ->
           Term.constr ->
           Term.types * Term.constr * goal sigma


