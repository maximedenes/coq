val apply_top_tac : Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val inner_ssrapplytac :
  Ssrast.ssrterm list ->
  ((Ssrast.ssrhyps option * Ssrmatching_plugin.Ssrmatching.occ) *
     (Ssrast.ssrtermkind * Tacexpr.glob_constr_and_expr))
    list list ->
  Ssrast.ssrhyps ->
  Ssrast.ist ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
