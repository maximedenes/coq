open Util
open Names
open Context
open Constr
open Term
open Vars
open Environ
open Constrexpr
open Tacexpr
open Sigma
open Proofview
open Proofview.Notations
open Evarutil

open CoqAPI

(* Only [One] forces an introduction, possibly reducing the goal. *)
type anon_iter =
  | One
  | Dependent (* fast mode *)
  | UntilMark
  | Temporary (* "+" *)
  | All

type intro_mode = Slow | Fast

type concat_kind = Prefix | Suffix

type direction = LeftToRight | RightToLeft

type selector = int

type state = { to_clear: Id.t list;
               name_seed: Constr.t option }

let state_field : state Proofview_monad.StateStore.field =
  Proofview_monad.StateStore.field ()

let fresh_state = { to_clear = [];
                    name_seed = None }

(* FIXME: should not inject fresh_state, but initialize it at the beginning *)
let upd_state upd s =
  let old_state = Option.default fresh_state (Proofview_monad.StateStore.get s state_field) in
  let new_state = upd old_state in
  Proofview_monad.StateStore.set s state_field new_state

(* should go away?
let set_intro_mode mode state =
  { state with intro_mode = mode }
 *)

type simpl = Simpl of int | Cut of int | SimplCut of int * int

type ipat =
  | IPatNoop
  | IPatName of Id.t
  | IPatAnon of anon_iter (* inaccessible name *)
  | IPatDrop (* => _ *)
  | IPatClearMark
  | IPatConcat of concat_kind * Id.t (* => prefix_[] *)
  | IPatDispatch of ipat list list (* /[..|..] *)
  | IPatCase of ipat list list (* this is not equivalent to /case /[..|..] if there are already multiple goals *)
  | IPatTactic of (raw_tactic_expr * selector option * unit list) (* /tac *)
(*  | IPatRewrite of occurrence option * rewrite_pattern * direction *)
  | IPatView of constr_expr list (* /view *)
  | IPatClear of Id.t list(* {H1 H2} *)
  | IPatSimpl of simpl
  | IPatInj of ipat list
(* | IPatView of term list *)
(* | IPatVarsForAbstract of Id.t list *)

let pr_iorpat _ _ _ ipat = Pp.mt ()
let pr_ipat _ _ _ ipat = Pp.mt ()

let interp_ipat ist gl ipat = Evd.empty, (ist, ipat)

let glob_ipat _ ipat = ()

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env store decl b =
  Refine.refine ~unsafe:true { run = begin fun sigma ->
    let ctx = named_context_val env in
    let nctx = push_named_context_val decl ctx in
    let inst = List.map (Named.Declaration.get_id %> mkVar) (named_context env) in
    let ninst = mkRel 1 :: inst in
    let nb = subst1 (mkVar (Named.Declaration.get_id decl)) b in
    let Sigma (ev, sigma, p) = new_evar_instance nctx sigma nb ~principal:true ~store ninst in
    Sigma (mkNamedLambda_or_LetIn decl ev, sigma, p)
  end }

let set_decl_id id = function
  | Rel.Declaration.LocalAssum(name,ty) -> Named.Declaration.LocalAssum(id,ty)
  | Rel.Declaration.LocalDef(name,ty,t) -> Named.Declaration.LocalDef(id,ty,t)

let intro_id_slow id = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let store = Goal.extra gl in
  let g = Goal.raw_concl gl in
  let decl,t = CoqAPI.decompose_assum env (Sigma.to_evar_map sigma) g in
  unsafe_intro env store (set_decl_id id decl) t
 }

(*
   match kind_of_term g with
   | App (hd, _) when isLambda hd -> 
     let g = CClosure.whd_val (betared env) (CClosure.inject g) in
     new_tac (convert_concl_no_check g) gl
   | _ -> tclIDTAC gl) } )
  (Proofview.V82.of_tactic
    (fst_prod false (fun id -> orig := id; intro_mustbe_force name)))
 *)

let set_state upd =
  let open Proofview_monad in
  Goal.enter { enter = fun gl ->
    Proofview.Unsafe.tclGETGOALS >>= fun l ->
    let l = List.map (fun gs -> let (g,s) = (drop_state gs, get_state gs) in goal_with_state g (upd s)) l in
    Proofview.Unsafe.tclSETGOALS l
  }

let analyze env evd ty =
  let ((kn, i), _ as indu), unfolded_c_ty =
    Tacred.reduce_to_quantified_ind env evd ty
  in
  let mind,indb = Inductive.lookup_mind_specif env (kn,i) in
  (mind.Declarations.mind_nparams,indb.Declarations.mind_nf_lc)

let tac_case t =
  Goal.enter { enter = fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let evd = Sigma.to_evar_map sigma in
    let evd, ty = Typing.type_of ~refresh:false env evd t in
    let (nparams,seeds) = analyze env evd ty in 
    let i = ref (-1) in
    Tactics.simplest_case t <*> set_state (fun s -> incr i; Printf.printf "i=%i\n" !i; upd_state (fun st -> { st with name_seed = Some seeds.(!i) }) s)
  }

let tac_intro_seed interp_ipats prefix =
  Goal.enter { enter = fun gl ->
    let env = Goal.env gl in
    let state = Goal.state gl in
    let state = Option.get (Proofview_monad.StateStore.get state state_field) in
    let ty = Option.get state.name_seed in
    let ctx,_ = decompose_prod_assum ty in
    Printf.printf "tac_intro_seed with l(ctx)=%i,ty=%s\n" (List.length ctx) (Pp.string_of_ppcmds (Printer.pr_constr ty));
    let seeds = CList.rev_map Context.Rel.Declaration.get_name ctx in
    let ipats = List.map (function Anonymous -> IPatAnon One | Name id -> IPatName (Id.of_string (Id.to_string prefix ^ Id.to_string id)) ) seeds in
    interp_ipats ipats
  }

(* FIXME: use unreachable name *)
let tclWITHTOP tac =
  let top = Id.of_string "top_assumption" in
  intro_id_slow top <*> tac (mkVar top) <*> Tactics.clear [top]


(* The problem is: how to enrich multi goals tactic with state?  Tactics like
cycle which are not aware of our state type should thread it correctly, so it
should really be attached to goals *)

let rec ipat_tac1 ipat : unit tactic =
  match ipat with
  | IPatTactic(t,sel,args) ->
     Tacinterp.hide_interp true t None
  | IPatDispatch(ipats) ->
     tclDISPATCH (List.map ipat_tac ipats)
  | IPatName id ->
     intro_id_slow id
  | IPatCase(ipatss) ->
     Tacticals.New.tclTHENS (tclWITHTOP tac_case) (List.map ipat_tac ipatss)
  | IPatConcat(_kind,prefix) ->
     tac_intro_seed ipat_tac prefix
  | IPatNoop -> tclNIY "IPatNoop"
  | IPatAnon iter -> tclNIY "IPatAnon"
  | IPatDrop -> tclNIY "IPatDrop"
  | IPatClearMark -> tclNIY "IPatClearMark"
  | IPatView views -> tclNIY "IPatView"
  | IPatClear ids -> tclNIY "IPatClear"
  | IPatSimpl simp -> tclNIY "IPatSimpl"
  | IPatInj ipats -> tclNIY "IPatInj"

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> tclUNIT ()
  | pat :: pl -> tclTHEN (ipat_tac1 pat) (ipat_tac pl)

(*
let ipat_tac pl =
  
 *)
