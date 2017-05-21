val tclSEQAT :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ltac_plugin.Tacinterp.Value.t ->
  Ssrast.ssrdir ->
  int Misctypes.or_var *
    (('a * Ltac_plugin.Tacinterp.Value.t option list) *
       Ltac_plugin.Tacinterp.Value.t option) ->
  Proof_type.tactic

val tclCLAUSES :
  Ltac_plugin.Tacinterp.interp_sign ->
  Proofview.V82.tac ->
  (Ssrast.ssrhyps *
     ((Ssrast.ssrhyp_or_id * string) *
        Ssrmatching_plugin.Ssrmatching.cpattern option)
       option)
    list * Ssrast.ssrclseq ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val hinttac :
           Tacinterp.interp_sign ->
           bool -> bool * Tacinterp.Value.t option list -> Ssrast.v82tac

val ssrdotac :
  Ltac_plugin.Tacinterp.interp_sign ->
  ((int Misctypes.or_var * Ssrast.ssrmmod) *
     (bool * Ltac_plugin.Tacinterp.Value.t option list)) *
    ((Ssrast.ssrhyps *
        ((Ssrast.ssrhyp_or_id * string) *
           Ssrmatching_plugin.Ssrmatching.cpattern option)
          option)
       list * Ssrast.ssrclseq) ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

