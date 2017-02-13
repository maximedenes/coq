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

open Compat
open Tok

open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrcommon
open Ssrparser

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
let rec fst_prod red tac = PG.nf_enter { PG.enter = begin fun gl ->
  let concl = PG.concl (PG.assume gl) in
  match kind_of_term concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) -> tac id
  | _ -> if red then TN.tclZEROMSG (str"No product even after head-reduction.")
         else TN.tclTHEN hnf_in_concl (fst_prod true tac)
end }
;;
let introid ?(orig=ref Anonymous) name = tclTHEN (fun gl ->
   let g, env = pf_concl gl, pf_env gl in
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = CClosure.whd_val (betared env) (CClosure.inject g) in
     new_tac (convert_concl_no_check g) gl
   | _ -> tclIDTAC gl)
  (Proofview.V82.of_tactic
    (fst_prod false (fun id -> orig := id; intro_mustbe_force name)))
;;
let anontac decl gl =
  let id =  match RelDecl.get_name decl with
  | Name id ->
    if is_discharged_id id then id else mk_anon_id (string_of_id id) gl
  | _ -> mk_anon_id ssr_anon_hyp gl in
  introid id gl

let intro_all gl =
  let dc, _ = Term.decompose_prod_assum (pf_concl gl) in
  tclTHENLIST (List.map anontac (List.rev dc)) gl

let rec intro_anon gl =
  try anontac (List.hd (fst (Term.decompose_prod_n_assum 1 (pf_concl gl)))) gl
  with err0 -> try tclTHEN (Proofview.V82.of_tactic red_in_concl) intro_anon gl with e when CErrors.noncritical e -> raise err0
  (* with _ -> CErrors.error "No product even after reduction" *)

let rec fst_unused_prod red tac = PG.nf_enter { PG.enter = begin fun gl ->
  let concl = PG.concl (PG.assume gl) in
  match kind_of_term concl with
  | Prod (id,_,tgt) | LetIn(id,_,_,tgt) ->
      if noccurn 1 tgt then tac id
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
   let g, env = pf_concl gl, pf_env gl in
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = CClosure.whd_val (betared env) (CClosure.inject g) in
     new_tac (convert_concl_no_check g) gl
   | _ -> tclIDTAC gl)
  (new_tac (introid_fast orig name))
;;

let introid_a ?orig name gl =
  tac_ctx (introid ~speed:(snd (pull_ctx gl)).speed ?orig name) gl


let simplest_newcase ?ind x gl = Hook.get simplest_newcase_tac ?ind x gl
let ssrscasetac ?ind force_inj c gl = Hook.get simplest_newcase_or_inj_tac ?ind ~force_inj c gl


let with_top tac gl =
  let speed = (snd (pull_ctx gl)).speed in
  tac_ctx
    (tclTHENLIST [ introid ~speed top_id; tac (mkVar top_id); new_tac (clear [top_id])])
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
  if n = 0 then mkConstruct path_of_O
  else mkApp (mkConstruct path_of_S, [|nat_of_n (n-1)|])

let ssr_abstract_id = Summary.ref "~name:SSR:abstractid" 0

let mk_abstract_id () = incr ssr_abstract_id; nat_of_n !ssr_abstract_id

let ssrmkabs id gl =
  let env, concl = pf_env gl, pf_concl gl in
  let step = { run = begin fun sigma ->
    let Sigma ((abstract_proof, abstract_ty), sigma, p) =
      let Sigma ((ty, _), sigma, p1) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let Sigma (ablock, sigma, p2) = mkSsrConst "abstract_lock" env sigma in
      let Sigma (lock, sigma, p3) = Evarutil.new_evar env sigma ablock in
      let Sigma (abstract, sigma, p4) = mkSsrConst "abstract" env sigma in
      let abstract_ty = mkApp(abstract, [|ty;mk_abstract_id ();lock|]) in
      let Sigma (m, sigma, p5) = Evarutil.new_evar env sigma abstract_ty in
      Sigma ((m, abstract_ty), sigma, p1 +> p2 +> p3 +> p4 +> p5) in
    let sigma, kont =
      let rd = RelDecl.LocalAssum (Name id, abstract_ty) in
      let Sigma (ev, sigma, _) = Evarutil.new_evar (Environ.push_rel rd env) sigma concl in
      let sigma = Sigma.to_evar_map sigma in
      (sigma, ev)
    in
(*     pp(lazy(pr_constr concl)); *)
    let term = mkApp (mkLambda(Name id,abstract_ty,kont) ,[|abstract_proof|]) in
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
let move_top_with_view ~next c r v ist gl =
  Hook.get move_top_with_view_tac ~next c r v ist gl
let simpltac x gl = Hook.get simpltac x gl

type block_names = (int * Term.types array) option

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
    | IpatSeed _ -> CErrors.anomaly(str"IpatSeed is to be used for parsing only")
    | IpatWild ->
        let id, gl = with_ctx new_wild_id gl in
        introid_a id gl
    | IpatTmpId ->
        let (id, orig), gl = with_ctx new_tmp_id gl in
        introid_a ~orig id gl
    | IpatCase(`Regular iorpat) ->
        tclIORPAT ?ist (with_top (ssrscasetac false)) iorpat gl
    | IpatCase(`Block (before,(id_side),after)) ->
        let ind = ref None in
        tclTHEN_i_max
          (with_top (ssrscasetac ~ind false))
          (block_intro ?ist ~ind id_side
            (List.map (ipatstac ?ist) before)
            (List.map (ipatstac ?ist)  after)) gl
    | IpatInj iorpat ->
        tclIORPAT ?ist (with_top (ssrscasetac true)) iorpat gl
    | IpatRw (occ, dir) ->
        with_top (ipat_rewrite occ dir) gl
    | IpatId id -> introid_a id gl
    | IpatNewHidden idl -> tac_ctx (ssrmkabstac idl) gl
    | IpatSimpl (clr, sim) ->
        tclTHEN_a (delayed_clear false !next clr) (tac_ctx (simpltac sim)) gl
    | IpatAll -> tac_ctx intro_all gl
    | IpatAnon -> intro_anon_a gl
    | IpatNoop -> tac_ctx tclIDTAC gl
    | IpatFastMode ->
        let gl, ctx = pull_ctx gl in
        let gl = push_ctx { ctx with speed = `Fast } gl in
        tac_ctx tclIDTAC gl
    | IpatView v ->
        let ist =
          match ist with Some x -> x | _ -> anomaly "ipat: view with no ist" in
        let next_keeps =
          match !next with (IpatCase _ | IpatRw _)::_ -> false | _ -> true in
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
             
  and block_intro ?ist ~ind prefix_side before after nth max gl =
    let nparams, ktypes =
      match !ind with
      | Some x -> x
      | None -> CErrors.anomaly (str "block_intro with no ind info") in
    let n_before = List.length before in
    let n_after = List.length after in
    let n_ks = Array.length ktypes in
    if max <> n_before + n_after + n_ks then
      let n_gls = max in
      let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
      let pr_nb n1 n2 name =
        pr_only n1 n2 ++ int n1 ++ str (" "^String.plural n1 name) in
      errorstrm (pr_nb (n_before + n_ks + n_after) n_gls "intro pattern"
        ++ spc () ++ str "for "
        ++ pr_nb n_gls (n_before + n_ks + n_after) "subgoal")
    else
    let ipat_of_name name =
      match prefix_side, name with
      | `Anon, _ -> IpatAnon
      | `Wild, _ -> IpatWild
      | _, Anonymous -> IpatAnon
      | `Id(prefix,side), Name id ->
          let id = Id.to_string id in
          match side with
          | `Pre -> IpatId (Id.of_string (Id.to_string prefix ^ id))
          | `Post -> IpatId (Id.of_string (id ^ Id.to_string prefix)) in
    let rec ipat_of_ty n t =
      match kind_of_type t with
      | CastType(t,_) ->  ipat_of_ty n t
      | ProdType(name,_,tgt) | LetInType(name,_,_,tgt) ->
          (if n<= 0 then [ipat_of_name name] else []) @
          ipat_of_ty (n-1) tgt
      | AtomicType _ | SortType _ -> [] in
    if nth <= n_before then
      List.nth before (nth-1) gl
    else if nth > n_before && nth <= n_before + n_ks then
      let ktype = ktypes.(nth - 1 - n_before) in
      let ipats = ipat_of_ty nparams ktype in
(*
      pp(lazy(str"=> "++pr_ipats ipats++str" on "++
        pr_constr (without_ctx pf_concl gl)));
*)
      let gl = let gl,ctx = pull_ctx gl in push_ctx {ctx with speed=`Slow} gl in
      ipatstac ?ist ipats gl
    else
      List.nth after (nth - 1 - n_before - n_ks) gl

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
    | (IpatSimpl _ as spat) :: ipats' -> (* FIXME block *)
        let tac = ipattac ?ist ~next:(ref ipats') spat in
        split_itacs ?ist ~ind (tclTHEN_a tac' tac) ipats'
    | IpatCase (`Regular iorpat) :: ipats' -> 
        tclIORPAT ?ist tac' iorpat, ipats'
    | IpatCase (`Block(before,id_side,after)) :: ipats' ->
        tclTHEN_i_max tac'
          (block_intro ?ist ~ind id_side
            (List.map (ipatstac ?ist) before)
            (List.map (ipatstac ?ist)  after)),
        ipats'
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

(* vim: set filetype=ocaml foldmethod=marker: *)
