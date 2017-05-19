open Names
open Pp
open Feedback
open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Genarg
open Stdarg
open Tacarg
open Term
open Vars
open Context
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Namegen
open Recordops
open Tacmach
open Coqlib
open Glob_term
open Util
open Evd
open Proofview.Notations
open Sigma.Notations
open Extend
open Goptions
open Tacexpr
open Tacinterp
open Pretyping
open Constr
open Pltac
open Extraargs
open Ppconstr
open Printer

open Globnames
open Misctypes
open Decl_kinds
open Evar_kinds
open Constrexpr
open Constrexpr_ops
open Notation_term
open Notation_ops
open Locus
open Locusops

open Tok

open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrprinters
open Ssrcommon
open Ssrequality
open Ssrview
open Ssrelim

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
(** Extended intro patterns {{{ ***********************************************)


(* There are two ways of "applying" a view to term:            *)
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)

let apply_type x xs = Proofview.V82.of_tactic (apply_type x xs)

module PG = Proofview.Goal
module TN = Tacticals.New
let old_tac = Proofview.V82.tactic
let new_tac = Proofview.V82.of_tactic

(* we reduce head beta redexes *)
let betared env = 
  CClosure.(create_clos_infos 
   (RedFlags.mkflags [RedFlags.fBETA])
    env)
;;

let rec fst_unused_prod red tac = PG.nf_enter { PG.enter = begin fun gl ->
  let concl = PG.concl (PG.assume gl) in
  let sigma = Sigma.to_evar_map @@ PG.sigma gl in
  match EConstr.kind sigma concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) ->
      if EConstr.Vars.noccurn sigma 1 tgt then tac id
      else TN.tclTHEN (old_tac intro_anon) (fst_unused_prod false tac)
  | _ -> if red then TN.tclZEROMSG (str"No product even after head-reduction.")
         else TN.tclTHEN hnf_in_concl (fst_unused_prod true tac)
end };;
let introid_fast orig name = 
  fst_unused_prod false (fun id -> orig := id; old_tac (introid name))
let intro_anon_fast = fst_unused_prod false (fun _ -> old_tac intro_anon)

let intro_anon ?(speed=`Slow) () =
  if speed = `Slow then intro_anon else new_tac intro_anon_fast

let intro_anon_a gl =
  tac_ctx (intro_anon ~speed:(snd (pull_ctx gl)).speed ()) gl

let speed_to_next_NDP gl =
  match (snd (pull_ctx gl)).speed with
  | `Slow -> tac_ctx tclIDTAC gl
  | `Fast ->
       tac_ctx (new_tac (fst_unused_prod false (fun _ -> old_tac tclIDTAC))) gl
let introid ?(speed=`Slow) ?(orig=ref Anonymous) name =
  if speed = `Slow then introid ~orig name
  else tclTHEN (fun gl ->
   let sigma = project gl in
   let g, env = pf_concl gl, pf_env gl in
   match EConstr.kind sigma g with
   | App (hd, _) when EConstr.isLambda sigma hd -> 
     new_tac (convert_concl_no_check (Reductionops.whd_beta sigma g)) gl
   | _ -> tclIDTAC gl)
  (new_tac (introid_fast orig name))
;;

let introid_a ?orig name gl =
  tac_ctx (introid ~speed:(snd (pull_ctx gl)).speed ?orig name) gl

let with_top tac gl =
  let speed = (snd (pull_ctx gl)).speed in
  tac_ctx
    (tclTHENLIST [ introid ~speed top_id; tac (EConstr.mkVar top_id); new_tac (clear [top_id])])
    gl

let tclTHENS_nonstrict tac tacl taclname gl =
  let tacres = tac gl in
  let n_gls = List.length (sig_it tacres) in
  let n_tac = List.length tacl in
  if n_gls = n_tac then tclTHENS_a (fun _ -> tacres) tacl gl else
  if n_gls = 0 then tacres else
  let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
  let pr_nb n1 n2 name =
    pr_only n1 n2 ++ int n1 ++ str (" " ^ String.plural n1 name) in
  errorstrm (pr_nb n_tac n_gls taclname ++ spc ()
             ++ str "for " ++ pr_nb n_gls n_tac "subgoal")

let rec nat_of_n n =
  if n = 0 then EConstr.mkConstruct path_of_O
  else EConstr.mkApp (EConstr.mkConstruct path_of_S, [|nat_of_n (n-1)|])

let ssr_abstract_id = Summary.ref "~name:SSR:abstractid" 0

let mk_abstract_id () = incr ssr_abstract_id; nat_of_n !ssr_abstract_id

let ssrmkabs id gl =
  let env, concl = pf_env gl, Tacmach.pf_concl gl in
  let step = { run = begin fun sigma ->
    let Sigma ((abstract_proof, abstract_ty), sigma, p) =
      let Sigma ((ty, _), sigma, p1) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let Sigma (ablock, sigma, p2) = mkSsrConst "abstract_lock" env sigma in
      let Sigma (lock, sigma, p3) = Evarutil.new_evar env sigma ablock in
      let Sigma (abstract, sigma, p4) = mkSsrConst "abstract" env sigma in
      let abstract_ty = EConstr.mkApp(abstract, [|ty;mk_abstract_id ();lock|]) in
      let Sigma (m, sigma, p5) = Evarutil.new_evar env sigma abstract_ty in
      Sigma ((m, abstract_ty), sigma, p1 +> p2 +> p3 +> p4 +> p5) in
    let sigma, kont =
      let rd = RelDecl.LocalAssum (Name id, abstract_ty) in
      let Sigma (ev, sigma, _) = Evarutil.new_evar (EConstr.push_rel rd env) sigma concl in
      let sigma = Sigma.to_evar_map sigma in
      (sigma, ev)
    in
(*    pp(lazy(pr_econstr concl)); *)
    let term = EConstr.(mkApp (mkLambda(Name id,abstract_ty,kont) ,[|abstract_proof|])) in
    let sigma, _ = Typing.type_of env sigma term in
    Sigma.Unsafe.of_pair (term, sigma)
  end } in
  Proofview.V82.of_tactic
    (Proofview.tclTHEN
      (Tactics.New.refine step)
      (Proofview.tclFOCUS 1 3 Proofview.shelve)) gl

let ssrmkabstac ids =
  List.fold_right (fun id tac -> tclTHENFIRST (ssrmkabs id) tac) ids tclIDTAC

(* introstac: for "move" and "clear", tclEQINTROS: for "case" and "elim" *)
(* This block hides the spaghetti-code needed to implement the only two  *)
(* tactics that should be used to process intro patters.                 *)
(* The difficulty is that we don't want to always rename, but we can     *)
(* compute needeed renamings only at runtime, so we theread a tree like  *)
(* imperativestructure so that outer renamigs are inherited by inner     *)
(* ipts and that the cler performed at the end of ipatstac clears hyps   *)
(* eventually renamed at runtime.                                        *)

let delayed_clear force rest clr gl = 
  let gl, ctx = pull_ctx gl in
  let hyps = pf_hyps gl in
  let () = if not force then List.iter (check_hyp_exists hyps) clr in
  if List.exists (fun x -> force || is_name_in_ipats (hyp_id x) rest) clr then
    let ren_clr, ren = 
      List.split (List.map (fun x ->
        let x = hyp_id x in
        let x' = mk_anon_id (string_of_id x) gl in
        x', (x, x')) clr) in
    let ctx = { ctx with delayed_clears = ren_clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx (Proofview.V82.of_tactic (rename_hyp ren)) gl 
  else
    let ctx = { ctx with delayed_clears = hyps_ids clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx tclIDTAC gl
      
let ipat_rewrite occ dir gl = Hook.get ipat_rewrite_tac occ dir gl

(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr ist gl =
  let top_id =
    match EConstr.kind_of_type (project gl) (pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (string_of_id id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN (introid top_id) (maintac deps top_gen ist) gl

let with_defective_a maintac deps clr ist gl =
  let sigma = sig_sig gl in
  let top_id =
    match EConstr.kind_of_type sigma (without_ctx pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (string_of_id id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN_a (tac_ctx (introid top_id)) (maintac deps top_gen ist) gl

let with_dgens (gensl, clr) maintac ist = match gensl with
  | [deps; []] -> with_defective maintac deps clr ist
  | [deps; gen :: gens] ->
    tclTHEN (genstac (gens, clr) ist) (maintac deps gen ist)
  | [gen :: gens] -> tclTHEN (genstac (gens, clr) ist) (maintac [] gen ist)
  | _ -> with_defective maintac [] clr ist

let () = Hook.set Ssrcommon.with_dgens_hook with_dgens

let viewmovetac_aux ?(next=ref []) clear name_ref (_, vl as v) _ gen ist gl =
  let cl, c, clr, gl, gen_pat =
    let gl, ctx = pull_ctx gl in
    let _, gen_pat, a, b, c, ucst, gl = pf_interp_gen_aux ist gl false gen in
    a, b ,c, push_ctx ctx (pf_merge_uc ucst gl), gen_pat in
  let clr = if clear then clr else [] in
  name_ref := (match id_of_pattern gen_pat with Some id -> id | _ -> top_id);
  let clr = if clear then clr else [] in
  if vl = [] then tac_ctx (genclrtac cl [c] clr) gl
  else
    let _, _, gl =
      pfa_with_view ist ~next v cl c
        (fun cl c -> tac_ctx (genclrtac cl [c] clr)) clr gl in
      gl

let move_top_with_view ~next c r v =
  with_defective_a (viewmovetac_aux ~next c r v) [] []

type block_names = (int * EConstr.types array) option

let (introstac : ?ist:Tacinterp.interp_sign -> ssripats -> Proof_type.tactic),
    (tclEQINTROS : ?ind:block_names ref -> ?ist:Tacinterp.interp_sign ->
                     Proof_type.tactic -> Proof_type.tactic -> ssripats ->
                      Proof_type.tactic),
    (tclINTROSviewtac : ist:Tacinterp.interp_sign -> next:ssripats ref ->
                            tac_ctx tac_a -> (*tac_ctx tac_a ->*) tac_ctx tac_a)
=

  let rec ipattac ?ist ~next p : tac_ctx tac_a = fun gl ->
(*     pp(lazy(str"ipattac: " ++ pr_ipat p)); *)
    match p with
    | IPatAnon Drop ->
        let id, gl = with_ctx new_wild_id gl in
        introid_a id gl
    | IPatAnon All -> tac_ctx intro_all gl
    | IPatAnon Temporary ->
        let (id, orig), gl = with_ctx new_tmp_id gl in
        introid_a ~orig id gl
    | IPatCase(iorpat) ->
        tclIORPAT ?ist (with_top (ssrscasetac false)) iorpat gl
    | IPatInj iorpat ->
        tclIORPAT ?ist (with_top (ssrscasetac true)) iorpat gl
    | IPatRewrite (occ, dir) ->
        with_top (ipat_rewrite occ dir) gl
    | IPatId (id_mod,id) -> (* FIXME id_mod *) introid_a id gl
    | IPatNewHidden idl -> tac_ctx (ssrmkabstac idl) gl
    | IPatSimpl sim ->
        tac_ctx (simpltac sim) gl
    | IPatClear clr ->
        delayed_clear false !next clr gl
    | IPatAnon One -> intro_anon_a gl
    | IPatNoop -> tac_ctx tclIDTAC gl
    | IPatView v ->
        let ist =
          match ist with Some x -> x | _ -> anomaly "ipat: view with no ist" in
        let next_keeps =
          match !next with (IPatCase _ | IPatRewrite _)::_ -> false | _ -> true in
        let top_id = ref top_id in
        tclTHENLIST_a [
          speed_to_next_NDP;
          (move_top_with_view ~next next_keeps top_id (next_keeps,v) ist);
          (fun gl ->
             let hyps = without_ctx pf_hyps gl in
             if not next_keeps && test_hypname_exists hyps !top_id then
               delayed_clear true !next [SsrHyp (dummy_loc,!top_id)] gl
             else tac_ctx tclIDTAC gl)]
        gl

  and tclIORPAT ?ist tac = function
  | [[]] -> tac
  | orp -> tclTHENS_nonstrict tac (List.map (ipatstac ?ist) orp) "intro pattern"

  and ipatstac ?ist ipats gl =
    let rec aux ipats gl =
      match ipats with
      | [] -> tac_ctx tclIDTAC gl
      | p :: ps ->
          let next = ref ps in
          let gl = ipattac ?ist ~next p gl in
          tac_on_all gl (aux !next)
    in
      aux ipats gl
  in

  let rec split_itacs ?ist ~ind tac' = function
    | (IPatSimpl _ as spat) :: ipats' -> (* FIXME block *)
        let tac = ipattac ?ist ~next:(ref ipats') spat in
        split_itacs ?ist ~ind (tclTHEN_a tac' tac) ipats'
    | IPatCase iorpat :: ipats' -> 
        tclIORPAT ?ist tac' iorpat, ipats'
    | ipats' -> tac', ipats' in

  let combine_tacs tac eqtac ipats ?ist ~ind gl =
    let tac1, ipats' = split_itacs ?ist ~ind tac ipats in
    let tac2 = ipatstac ?ist ipats' in
    tclTHENLIST_a [ tac1; eqtac; tac2 ] gl in
 
  (* Exported code *) 
  let introstac ?ist ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      ipatstac ?ist ipats;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids
    ]) gl in
  
  let tclEQINTROS ?(ind=ref None) ?ist tac eqtac ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      combine_tacs (tac_ctx tac) (tac_ctx eqtac) ipats ?ist ~ind;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids;
    ]) gl in

  let tclINTROSviewtac ~ist ~next tac gl =
    let tac1, ipats' = (* TODO: pass ind via lets in concl *)
      split_itacs ~ist ~ind:(ref None) tac !next in
    next := ipats';
    tclTHENLIST_a [ tac1(*; eqtac*) ] gl in (* FIXME *)

  introstac, tclEQINTROS, tclINTROSviewtac
;;

(* Intro patterns processing for elim tactic*)
let elim_intro_tac ipats ?ist what eqid ssrelim is_rec clr gl =
  (* Utils of local interest only *)
  let iD s ?t gl = let t = match t with None -> pf_concl gl | Some x -> x in
                   ppdebug(lazy Pp.(str s ++ pr_econstr t)); Tacticals.tclIDTAC gl in
  let protectC, gl = pf_mkSsrConst "protect_term" gl in
  let eq, gl = pf_fresh_global (Coqlib.build_coq_eq ()) gl in
  let eq = EConstr.of_constr eq in
  let fire_subst gl t = Reductionops.nf_evar (project gl) t in
  let intro_eq = 
    match eqid with 
    | Some (IPatId (mod_id,ipat)) (* FIXME mod_id *) when not is_rec -> 
       let rec intro_eq gl = match EConstr.kind_of_type (project gl) (pf_concl gl) with
         | ProdType (_, src, tgt) -> 
            (match EConstr.kind_of_type (project gl) src with
             | AtomicType (hd, _) when EConstr.eq_constr (project gl) hd protectC -> 
                Tacticals.tclTHENLIST [unprotecttac; introid ipat] gl
             | _ -> Tacticals.tclTHENLIST [ iD "IA"; Ssrcommon.intro_anon; intro_eq] gl)
         |_ -> errorstrm (Pp.str "Too many names in intro pattern") in
       intro_eq
    | Some (IPatId (mod_id,ipat))(* FIXME mod_id *) -> 
       let name gl = mk_anon_id "K" gl in
       let intro_lhs gl = 
         let elim_name = match clr, what with
           | [SsrHyp(_, x)], _ -> x
           | _, `EConstr(_,_,t) when EConstr.isVar (project gl) t -> EConstr.destVar (project gl) t
           | _ -> name gl in
         if is_name_in_ipats elim_name ipats then introid (name gl) gl
         else introid elim_name gl
       in
       let rec gen_eq_tac gl =
         let concl = pf_concl gl in
         let ctx, last = EConstr.decompose_prod_assum (project gl) concl in
         let args = match EConstr.kind_of_type (project gl) last with
           | AtomicType (hd, args) -> assert(EConstr.eq_constr (project gl) hd protectC); args
           | _ -> assert false in
         let case = args.(Array.length args-1) in
         if not(EConstr.Vars.closed0 (project gl) case) then Tacticals.tclTHEN Ssrcommon.intro_anon gen_eq_tac gl
         else
           let gl, case_ty = pfe_type_of gl case in 
           let refl = EConstr.mkApp (eq, [|EConstr.Vars.lift 1 case_ty; EConstr.mkRel 1; EConstr.Vars.lift 1 case|]) in
           let new_concl = fire_subst gl
                                      EConstr.(mkProd (Name (name gl), case_ty, mkArrow refl (Vars.lift 2 concl))) in 
           let erefl, gl = mkRefl case_ty case gl in
           let erefl = fire_subst gl erefl in
           apply_type new_concl [case;erefl] gl in
       Tacticals.tclTHENLIST [gen_eq_tac; intro_lhs; introid ipat]
    | _ -> Tacticals.tclIDTAC in
  let unprot = if eqid <> None && is_rec then unprotecttac else Tacticals.tclIDTAC in
  tclEQINTROS ?ist ssrelim (Tacticals.tclTHENLIST [intro_eq; unprot]) ipats gl

(* General case *)
let tclINTROS ist t ip = tclEQINTROS ~ist (t ist) tclIDTAC ip

(** The "=>" tactical *)

let ssrintros_sep =
  let atom_sep = function
    (* | TacSplit (_, [NoBindings]) -> mt *)
    (* | TacExtend (_, "ssrapply", []) -> mt *)
    | _ -> spc in
  function
    | TacId [] -> mt
    | TacArg (_, Tacexp _) -> mt
    | TacArg (_, Reference _) -> mt
    | TacAtom (_, atom) -> atom_sep atom
    | _ -> spc

(* }}} *)

let viewmovetac ?next v deps gen ist gl = 
 with_fresh_ctx
   (tclTHEN_a
     (viewmovetac_aux ?next true (ref top_id) v deps gen ist)
      clear_wilds_and_tmp_and_delayed_ids)
     gl

let mkCoqEq gl =
  let sigma = project gl in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma (eq, sigma, _) = EConstr.fresh_global (pf_env gl) sigma (build_coq_eq_data()).eq in
  let sigma = Sigma.to_evar_map sigma in
  let gl = { gl with sigma } in
  eq, gl

let mkEq dir cl c t n gl =
  let open EConstr in
  let eqargs = [|t; c; c|] in eqargs.(dir_org dir) <- mkRel n;
  let eq, gl = mkCoqEq gl in
  let refl, gl = mkRefl t c gl in
  mkArrow (mkApp (eq, eqargs)) (EConstr.Vars.lift 1 cl), refl, gl

let pushmoveeqtac cl c gl =
  let open EConstr in
  let x, t, cl1 = destProd (project gl) cl in
  let cl2, eqc, gl = mkEq R2L cl1 c t 1 gl in
  apply_type (mkProd (x, t, cl2)) [c; eqc] gl

let pushcaseeqtac cl gl =
  let open EConstr in
  let cl1, args = destApp (project gl) cl in
  let n = Array.length args in
  let dc, cl2 = decompose_lam_n_assum (project gl) n cl1 in
  assert(List.length dc = n); (* was decompose_lam_n *)
  let _, _, t = Context.Rel.Declaration.to_tuple (List.nth dc (n - 1)) in
  let cl3, eqc, gl = mkEq R2L cl2 args.(0) t n gl in
  let gl, clty = pfe_type_of gl cl in
  let prot, gl = mkProt clty cl3 gl in
  let cl4 = mkApp (it_mkLambda_or_LetIn prot dc, args) in
  let gl, _ = pf_e_type_of gl cl4 in
  tclTHEN (apply_type cl4 [eqc])
    (Proofview.V82.of_tactic (convert_concl cl4)) gl

let pushelimeqtac gl =
  let open EConstr in
  let _, args = destApp (project gl) (Tacmach.pf_concl gl) in
  let x, t, _ = destLambda (project gl) args.(1) in
  let cl1 = mkApp (args.(1), Array.sub args 2 (Array.length args - 2)) in
  let cl2, eqc, gl = mkEq L2R cl1 args.(2) t 1 gl in
  tclTHEN (apply_type (mkProd (x, t, cl2)) [args.(2); eqc])
    (Proofview.V82.of_tactic intro) gl

let eqmovetac _ gen ist gl =
  let cl, c, _, gl = pf_interp_gen ist gl false gen in pushmoveeqtac cl c gl

let movehnftac gl = match EConstr.kind (project gl) (pf_concl gl) with
  | Prod _ | LetIn _ -> tclIDTAC gl
  | _ -> new_tac hnf_in_concl gl

let rec eqmoveipats eqpat = function
  | (IPatSimpl _ as ipat) :: ipats -> ipat :: eqmoveipats eqpat ipats
  | (IPatClear _ as ipat) :: ipats -> ipat :: eqmoveipats eqpat ipats
  | (IPatAnon All :: _ | []) as ipats -> IPatAnon One :: eqpat :: ipats
   | ipat :: ipats -> ipat :: eqpat :: ipats

let ssrmovetac ist = function
  | _::_ as view, (_, (dgens, ipats)) ->
    let next = ref ipats in
    let dgentac = with_dgens dgens (viewmovetac ~next (true, view)) ist in
    tclTHEN dgentac (fun gl -> introstac ~ist !next gl)
  | _, (Some pat, (dgens, ipats)) ->
    let dgentac = with_dgens dgens eqmovetac ist in
    tclTHEN dgentac (introstac ~ist (eqmoveipats pat ipats))
  | _, (_, (([gens], clr), ipats)) ->
    let gentac = genstac (gens, clr) ist in
    tclTHEN gentac (introstac ~ist ipats)
  | _, (_, ((_, clr), ipats)) ->
    tclTHENLIST [movehnftac; cleartac clr; introstac ~ist ipats]

let ssrcasetac ist (view, (eqid, (dgens, ipats))) =
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) ist gl =
    let simple = (eqid = None && deps = [] && occ = None) in
    let cl, c, clr, gl = pf_interp_gen ist gl true gen in
    let _,vc, gl =
      if view = [] then c,c, gl else pf_with_view_linear ist gl (false, view) cl c in
    if simple && is_injection_case vc gl then
      tclTHENLIST [perform_injection vc; cleartac clr; introstac ~ist ipats] gl
    else 
      (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
      let deps, clr, occ = 
        if view <> [] && eqid <> None && deps = [] then [gen], [], None
        else deps, clr, occ in
      ssrelim ~is_case:true ~ist deps (`EConstr (clr,occ, vc)) eqid (elim_intro_tac ipats) gl
  in
  with_dgens dgens (ndefectcasetac view eqid ipats) ist


(* vim: set filetype=ocaml foldmethod=marker: *)
