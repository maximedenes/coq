open Names

open Ssrast
open Ssrcommon

type block_names = (int * EConstr.types array) option

(* For case/elim with eq generation: args are elim_tac introeq_tac ipats
 * elim E : "=> ipats" where E give rise to introeq_tac *)
val tclEQINTROS :
           ?ind:block_names ref ->
           ?ist:ist ->
           v82tac ->
           v82tac -> ssripats -> v82tac
(* special case with no eq and tactic taking ist *)
val tclINTROS :
           ist ->
           (ist -> v82tac) ->
           ssripats -> v82tac

(* FIXME horrid API: "=> /tac next" *)
val tclINTROSviewtac :
        ist:ist ->
        next:ssripats ref -> tac_ctx tac_a -> tac_ctx tac_a

(* move=> ipats *)
val introstac : ?ist:ist -> ssripats -> v82tac

(* "move=> x" saving the name stored in the Prod into orig *)
val introid : ?speed:[ `Slow | `Fast ] -> ?orig:name ref -> Id.t -> v82tac

(* "move=> top; tac top; clear top" respecting the speed *)
val with_top : (EConstr.t -> v82tac) -> tac_ctx tac_a


