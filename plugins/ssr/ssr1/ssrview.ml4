open Names
open Term
open Ltac_plugin
open Tacinterp
open Genarg
open Globnames
open Glob_term
open Misctypes
open Tacexpr
open Tacmach
open Tactics
open Tacticals

open Ssrparser
open Ssrcommon
open Ssripats

module PG = Proofview.Goal
module TN = Tacticals.New
let old_tac = Proofview.V82.tactic
let new_tac = Proofview.V82.of_tactic
let apply_type x xs = Proofview.V82.of_tactic (apply_type x xs)

let interp_view ist si env sigma gv v rid =
  match v with
  | GApp (loc, GHole _, rargs) ->
    let rv = GApp (loc, rid, rargs) in
    snd (interp_open_constr ist (re_sig si sigma) (rv, None))
  | rv ->
  let interp rc rargs =
    interp_open_constr ist (re_sig si sigma) (mkRApp rc rargs, None) in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist (re_sig si sigma) rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); rid] in
  let rec view_with = function
  | [] -> simple_view [rid] (interp_nbargs ist (re_sig si sigma) rv)
  | hint :: hints -> try interp hint view_args with _ -> view_with hints in
  snd (view_with (if view_nbimps < 0 then [] else Ssrvernac.viewtab.(0)))


let with_view ist ~next si env (gl0 : (Proof_type.goal * tac_ctx) Evd.sigma) c name cl prune (conclude : EConstr.t -> EConstr.t -> tac_ctx tac_a) clr =
  let c2r ist x = { ist with lfun =
    Id.Map.add top_id (Value.of_constr x) ist.lfun } in
  let terminate (sigma, c') =
    let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
    let c' = Reductionops.nf_evar sigma c' in
    let n, c', _, ucst = without_ctx pf_abs_evars gl0 (sigma, c') in
    let c' = if not prune then c' else without_ctx pf_abs_cterm gl0 n c' in
    let gl0 = pf_merge_uc ucst gl0 in
    let gl0, ap =
      let gl0, ctx = pull_ctx gl0 in
      let gl0, ap = pf_abs_prod name gl0 c' (Termops.prod_applist sigma cl [c]) in
      push_ctx ctx gl0, ap in
    let gl0 = pf_merge_uc_of sigma gl0 in
    ap, c', gl0 in
  let rec loop (sigma, c') = function
  | [] ->
      let ap, c', gl = terminate (sigma, c') in
      ap, c', conclude ap c' gl
  | f :: view ->
      let ist, rid =
        match EConstr.kind sigma c' with
        | Var id -> ist,mkRVar id
        | _ -> c2r ist c',mkRltacVar top_id in
      let v = intern_term ist env f in
      let tactic_view = mkSsrRef "tactic_view" in
      match v with
      | GApp (loc, GRef (_,box,None), [GHole (_,_,_, Some tac)])
       when has_type tac (glbwit Tacarg.wit_tactic) &&
            eq_gr box tactic_view -> begin
        let tac = out_gen (glbwit Tacarg.wit_tactic) tac in
        match tac with
        | TacLetIn (false,binds,TacArg(l0,TacCall(l,k,args))) ->
            let ap, c', gl = terminate (sigma, c') in
            let wid, gl = with_ctx new_wild_id gl in
            let argid = ArgVar(dummy_loc,wid) in
            let tac =
              TacLetIn (false,binds, 
                TacArg(l0,TacCall(l,k,args @ [ Reference argid ]))) in
            let tac = tac_ctx (ssrevaltac ist (Tacinterp.Value.of_closure ist tac)) in
            let tac = tclTHENLIST_a [
                tac_ctx (apply_type ap [c']);
                tac_ctx (introid wid);
                (tclINTROSviewtac ~ist ~next tac);
                (tac_ctx (new_tac (clear (hyps_ids clr)))) ] in
            let tac_check _ max gl =
              if view <> [] then CErrors.error "No view can follow a tactic-view"
              else tac_ctx tclIDTAC gl in
            ap,c',tclTHEN_i_max tac tac_check gl
        | _ -> CErrors.error "Only simple tactic call allowed as tactic-view" end
      | _ -> loop (interp_view ist si env sigma f v rid) view
  in loop

let pfa_with_view ist ?(next=ref []) (prune, view) cl c conclude clr gl =
  let env, sigma, si =
    without_ctx pf_env gl, Refiner.project gl, without_ctx sig_it gl in
  with_view
    ist ~next si env gl c (constr_name sigma c) cl prune conclude clr (sigma, c) view 

let pf_with_view_linear ist gl v cl c =
  let x,y,gl =
    pfa_with_view ist v cl c (fun _ _ -> tac_ctx tclIDTAC) []
      (push_ctx (new_ctx ()) gl) in
  let gl, _ = pull_ctxs gl in
  assert(List.length (sig_it gl) = 1);
  x,y,re_sig (List.hd (sig_it gl)) (Refiner.project gl)


(* vim: set filetype=ocaml foldmethod=marker: *)
