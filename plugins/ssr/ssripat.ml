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

open Printf
open CoqAPI
open Ssrutils

module AdaptorDb : sig 

  type kind = Forward | Backward | Equivalence
  val get : kind -> Glob_term.glob_constr list
  val declare : kind -> Glob_term.glob_constr -> unit

end = struct
  type kind = Forward | Backward | Equivalence

  module AdaptorKind = struct
    type t = kind
    let compare = Pervasives.compare
  end
  module AdaptorMap = Map.Make(AdaptorKind)

  let term_view_adaptor_db =
    Summary.ref ~name:"view_adaptor_db" AdaptorMap.empty

  let get k =
    try AdaptorMap.find k !term_view_adaptor_db
    with Not_found -> []

  let cache_adaptor (_, (k, t)) =
    let lk = get k in
    if not (List.exists (Glob_ops.glob_constr_eq t) lk) then
      term_view_adaptor_db := AdaptorMap.add k (t :: lk) !term_view_adaptor_db

  let subst_adaptor ( subst, (k, t as a)) =
    let t' = Detyping.subst_glob_constr subst t in
    if t' == t then a else k, t'
      
  let classify_adaptor x = Libobject.Substitute x

  let in_db =
    Libobject.declare_object {
       (Libobject.default_object "VIEW_ADAPTOR_DB")
    with
       Libobject.open_function = (fun i o -> if i = 1 then cache_adaptor o);
       Libobject.cache_function = cache_adaptor;
       Libobject.subst_function = subst_adaptor;
       Libobject.classify_function = classify_adaptor }

  let declare kind term = Lib.add_anonymous_leaf (in_db (kind,term))
end



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

type delayed_gen = { from_id : Id.t;
                     to_name : Name.t }

type state = {
  to_drop : Id.t list;
  to_clear : Id.t list;
  to_generalize : delayed_gen list;
  name_seed : Constr.t option;
  view_pile : (Id.t * Constr.t) option;  (* to incrementally build /v1/v2/v3.. *)
}

let state_field : state Proofview_monad.StateStore.field =
  Proofview_monad.StateStore.field ()

let fresh_state = {
  to_drop = [];
  to_clear = [];
  to_generalize = [];
  name_seed = None;
  view_pile = None;
}

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

type ipats_mod = Equal | Ampersand
type name_mod = Hat | HatTilde | Sharp

let pr_ipats_mod _ _ _ = function
  | Equal -> Pp.str"="
  | Ampersand -> Pp.str"&"

let pr_name_mod _ _ _ = function
  | Hat -> Pp.str"^"
  | HatTilde -> Pp.str"^~"
  | Sharp -> Pp.str"#"

let suffix_of_name_mod = function
  | None -> ""
  | Some Hat -> "_append"
  | Some HatTilde -> "_prepend"
  | Some Sharp -> "_sharp"


let suffix_of_anon_iter = function
  | One -> ""
  | Dependent -> "_deps"
  | UntilMark -> "_mark"
  | Temporary -> "_temp"
  | All -> "_all"

(* These terms are raw but closed with the intenalization/interpretation context.
 * It is up to the tactic receiving it to decide if such contexts are useful or not,
 * and eventually manipulate the term before turning it into a constr *)
type term = {
  body : Constrexpr.constr_expr;
  glob_env : Genintern.glob_sign option; (* for Tacintern.intern_constr *)
  interp_env :  Geninterp.interp_sign option; (* for Tacinterp.interp_open_constr_with_bindings *)
  annotation : [ `None | `Parens | `DoubleParens | `At ];
} 
let glob_term (ist : Genintern.glob_sign) t =
  { t with glob_env = Some ist }
let subst_term (_s : Mod_subst.substitution) t =
  (* _s makes sense only for glob constr *)
  t
let interp_term (ist : Geninterp.interp_sign) (gl : 'goal Evd.sigma) t = 
  (* gl is only useful if we want to interp *now*, later we have
   * a potentially different gl.sigma *)
  Tacmach.project gl, { t with interp_env = Some ist }

let mk_term a t = {
  annotation = a;
  body = t;
  interp_env = None;
  glob_env = None;
}
let pr_term _ _ _ { body } = Ppconstr.pr_constr_expr body

type ipat =
  | IPatNoop
  | IPatName of name_mod option * Id.t
  | IPatAnon of anon_iter (* inaccessible name *)
  | IPatDrop (* => _ *)
  | IPatClearMark
  | IPatDispatch of ipats_mod option * ipat list list (* /[..|..] *)
  | IPatCase of ipats_mod option * ipat list list (* this is not equivalent to /case /[..|..] if there are already multiple goals *)
  | IPatRewrite of (*occurrence option * rewrite_pattern **) Ssrast.ssrdir
  | IPatView of term list (* /view *)
  | IPatClear of Id.t list(* {H1 H2} *)
  | IPatSimpl of simpl
(* | IPatVarsForAbstract of Id.t list *)

let pr_iorpat _ _ _ ipat = Pp.mt ()
let pr_ipat _ _ _ ipat = Pp.mt ()
let pr_ipats _ _ _ ipats = Pp.mt ()
let subst_ipat _ x = x

let rec map_ipat map_term = function
  | (IPatNoop 
    | IPatName _  (* XXX fix ltac, not a term but potentially affected by ltac *)
    | IPatClear _ (* XXX fix ltac, the same as above *)
    | IPatAnon _
    | IPatDrop 
    | IPatClearMark
    | IPatSimpl _
    | IPatRewrite _ (* FIXME *)
    ) as x -> x
  | IPatDispatch(m,ll) ->
      IPatDispatch(m,List.map (List.map (map_ipat map_term)) ll)
  | IPatCase(m,ll) ->
      IPatCase(m,List.map (List.map (map_ipat map_term)) ll)
  | IPatView tl -> IPatView(List.map map_term tl)

let interp_ipat ist gl x =
  Tacmach.project gl, map_ipat (fun x -> snd (interp_term ist gl x)) x
let glob_ipat ist = map_ipat (glob_term ist)

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

(** [intro id k] introduces the first premise (product or let-in) of the goal
    under the name [id], reducing the head of the goal (using beta, iota, delta
    but not zeta) if necessary. If [id] is None, a name is generated, that will
    not be user accesible. If the goal does not start with a product or a let-in
    even after reduction, it fails. In case of success, the original name and
    final id are passed to the continuation [k] which gets evaluated. *)
let intro ~id k = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let store = Goal.extra gl in
  let g = Goal.raw_concl gl in
  let decl,t = CoqAPI.decompose_assum env (Sigma.to_evar_map sigma) g in
  let original_name = Rel.Declaration.get_name decl in
  let id = match id, original_name with
    | Some id, _ -> id
    | _, Name id ->
       if Ssrcommon.is_discharged_id id then id
       else mk_anon_id (string_of_id id) (Tacmach.New.pf_ids_of_hyps gl)
    | _, _ ->
       let ids = Tacmach.New.pf_ids_of_hyps gl in
       mk_anon_id Ssrcommon.ssr_anon_hyp ids
  in
  unsafe_intro env store (set_decl_id id decl) t
  <*> k original_name id
 }

let return _name _id = tclUNIT ()

let intro_id id = intro ~id:(Some id) return
let intro_anon = intro ~id:None return

let intro_anon_all = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.raw_concl gl in
  let n = Ssrutils.nb_assums env (Sigma.to_evar_map sigma) g in
  Tacticals.New.tclDO n intro_anon
 }

let intro_anon_deps = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.raw_concl gl in
  let n = Ssrutils.nb_deps_assums env (Sigma.to_evar_map sigma) g in
  Tacticals.New.tclDO n intro_anon
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

let on_state f = set_state (fun s -> upd_state f s) (* could return a value? *)

let get_view_pile g =
  (Option.default fresh_state (Proofview_monad.StateStore.get (Goal.state g) state_field)).view_pile
let set_view_pile t = on_state (fun s -> { s with view_pile = Some t }) 

(** [intro_drop] behaves like [intro_anon] but registers the id of the
introduced assumption for a delayed clear. *)
let intro_drop = 
  let k _original_name new_id =
    set_state (upd_state (fun st -> { st with to_drop = new_id :: st.to_drop }))
  in
  intro ~id:None k

(** [intro_temp] behaves like [intro_anon] but registers the id of the
introduced assumption for a regeneralization. *)
let intro_anon_temp = 
  let k original_name new_id =
    let gen = { from_id = new_id; to_name = original_name } in
    set_state (upd_state (fun st -> { st with to_generalize = gen :: st.to_generalize }))
  in
  intro ~id:None k

(** [intro_finalize] performs the actions that have been delayed. *)
let intro_finalize = Goal.enter { enter = fun gl ->
  let state = Goal.state gl in
  match Proofview_monad.StateStore.get state state_field with
  | None -> tclUNIT ()
  | Some state ->
     (* Because of dependencies, delayed clears must be performed from the
     innermost to the outermost assumption. We process delayed drops first,
     because they may refer to hypotheses targetted by a delayed clear.
     Consider for example:
       Goal forall m n : nat, m = n -> True.
       => m n.
       => _ {m n}.
     *)
     Tactics.clear state.to_drop
     <*> Tactics.clear state.to_clear
     (* delayed generalizations *)
     <*> Tacticals.New.tclTHENLIST (List.map (fun gen -> gentac gen.from_id gen.to_name) state.to_generalize)
     <*> Tactics.clear (List.map (fun gen -> gen.from_id) state.to_generalize)
 }

let intro_clear ids =
  Goal.enter { enter = fun gl ->
    let (_, clear_ids, ren) =
      List.fold_left (fun (used_ids, clear_ids, ren) id ->
          let new_id = mk_anon_id (Id.to_string id) used_ids in
          (new_id :: used_ids, new_id :: clear_ids, (id, new_id) :: ren))
                     ((Tacmach.New.pf_ids_of_hyps gl), [], []) ids
    in
    Tactics.rename_hyp ren
    <*> set_state (upd_state (fun st -> { st with to_clear = List.rev_append clear_ids st.to_clear }))
  }

let analyze env evd ty =
  let ((kn, i), _ as indu), unfolded_c_ty =
    Tacred.reduce_to_quantified_ind env evd ty
  in
  let mind,indb = Inductive.lookup_mind_specif env (kn,i) in
  (mind.Declarations.mind_nparams,indb.Declarations.mind_nf_lc)

let tac_case mode t =
  match mode with
  | Some Equal ->
      V82.tactic (Ssreflect.perform_injection t)
  | None ->
  Goal.enter { enter = fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let evd = Sigma.to_evar_map sigma in
    let evd, ty = Typing.type_of ~refresh:false env evd t in
    let (nparams,seeds) = analyze env evd ty in 
    let i = ref (-1) in
    let case_tac = Hook.get Ssrcommon.simplest_newcase_tac in
    V82.tactic (case_tac t)
    <*> set_state (fun s -> incr i; Printf.printf "i=%i\n" !i; upd_state (fun st -> { st with name_seed = Some seeds.(!i) }) s)
  }

let tac_intro_seed interp_ipats where fix =
  Goal.enter { enter = fun gl ->
    let env = Goal.env gl in
    let state = Goal.state gl in
    let state = Option.get (Proofview_monad.StateStore.get state state_field) in
    let ty = Option.get state.name_seed in
    let ctx,_ = decompose_prod_assum ty in
    Printf.printf "tac_intro_seed with l(ctx)=%i,ty=%s\n" (List.length ctx) (Pp.string_of_ppcmds (Printer.pr_constr ty));
    let seeds = CList.rev_map Context.Rel.Declaration.get_name ctx in
    let ipats = List.map (function
       | Anonymous -> IPatAnon One
       | Name id ->
           let s = match where with
           | `Prepend ->  Id.to_string fix ^ Id.to_string id 
           | `Append -> Id.to_string id ^ Id.to_string fix in
           IPatName (None,Id.of_string s)) seeds in
    interp_ipats ipats
  }

let tclWITHTOP tac =
  Goal.enter { enter = fun gl ->
    let top = mk_anon_id "top_assumption" (Tacmach.New.pf_ids_of_hyps gl) in
    intro_id top <*> tac (mkVar top) <*> Tactics.clear [top]
  }


(* The .v file that loads the plugin *)
let bios_dirpath = DirPath.make [Id.of_string "ssreflect"]
let bios_ml = "ssreflect_plugin"

let locate_tac name =
  let mk_qtid name = Libnames.make_qualid bios_dirpath name in
  let mk_tid name = Libnames.qualid_of_ident name in
  let keep f x = ignore(f x);Libnames.Qualid (Loc.ghost,x) in
  try keep Nametab.locate_tactic (mk_tid name)
  with Not_found ->
    try keep Nametab.locate_tactic (mk_qtid name)
    with Not_found ->
      CErrors.error ("SSReflect not loaded, missing " ^ Id.to_string name)

let lookup_tac name args : raw_tactic_expr =
  TacArg(Loc.ghost, TacCall(Loc.ghost, locate_tac (Id.of_string name), args))

let in_ident id =
  TacGeneric (Genarg.in_gen (Genarg.rawwit Stdarg.wit_ident) id)

let in_idents ids =
  TacGeneric (Genarg.in_gen (Genarg.rawwit (Genarg.wit_list Stdarg.wit_ident)) ids)

let interp_raw_tac t = Tacinterp.hide_interp true t None
let interp_glob_tac t = Tacinterp.eval_tactic t

(* Disambiguation of /t
    - t is ltac:(tactic args)   
    - t is a term
   To allow for t being a notation, like "Notation foo x := ltac:(foo x)", we
   need to internalize t.
*)
let is_tac_in_term { body; glob_env; interp_env } = 
  Proofview.Goal.(enter_one { enter = fun goal ->
    let genv = env goal in
    let ist = CoqAPI.Option.assert_get glob_env (Pp.str"not a term") in
    (* We use the env of the goal, not the global one *)
    let ist = { ist with Genintern.genv } in
    (* We unravel notations *)
    match CoqAPI.intern_constr_expr ist body with
    | Glob_term.GHole (_,_,_, Some x)
      when Genarg.has_type x (Genarg.glbwit Tacarg.wit_tactic) 
        -> tclUNIT (`Tac (Genarg.out_gen (Genarg.glbwit Tacarg.wit_tactic) x))
    | x -> tclUNIT (`Term (interp_env,x))
 })

let tclGET_VIEWPILE = Proofview.Goal.(enter_one { enter = fun goal ->
  let name = Id.of_string "tmp" in (* make private *)
  let t = mkVar name in
  match get_view_pile goal with
  | None ->  intro_id name <*> set_view_pile (name,t) <*> tclUNIT t
  | Some (_,x) -> tclUNIT x
})

let tclUPD_VIEWPILE x = Proofview.Goal.(enter_one { enter = fun goal ->
  match get_view_pile goal with
  | None -> CErrors.anomaly Pp.(str"empty view pile")
  | Some (n,_) -> set_view_pile (n,x)
})

let tclRESET_VIEWPILE = Proofview.Goal.(enter_one { enter = fun goal ->
  match get_view_pile goal with
  | None -> tclUNIT ()
  | Some (n,_) -> Tactics.clear [n] <*> on_state(fun s -> { s with view_pile = None })
})

(* given a bound n it finds the largest 0 <= i <= n for which tac i works *)
let rec tclFIRSTi tac n =
  if n < 0 then Tacticals.New.tclZEROMSG Pp.(str "tclFIRSTi")
  else tclORELSE (tclFIRSTi tac (n-1)) (fun _ -> tac n)

(* To inject a constr into a glob_constr we use an Ltac variable *)
let tclINJ_CONSTR_IST ist p = 
  let fresh_id = Names.Id.of_string "xxx" in (* make private *)
  let ist = { 
    ist with Geninterp.lfun =
      Id.Map.add fresh_id (Taccoerce.Value.of_constr p) ist.Geninterp.lfun} in
  tclUNIT (ist,Glob_term.GVar(Loc.ghost,fresh_id))

(* Coq API *)
let isAppInd env sigma c =
  try ignore(Tacred.reduce_to_atomic_ind env sigma c); true
  with CErrors.UserError _ -> false

let mkGHole =
  Glob_term.GHole (Loc.ghost, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)
let rec mkGHoles n = if n > 0 then mkGHole :: mkGHoles (n - 1) else []
let mkGApp f args = if args = [] then f else Glob_term.GApp (Loc.ghost, f, args)

(* From glob_constr to open_constr === (env,sigma,constr) *)
let interp_glob ist glob = Proofview.Goal.(enter_one { enter = fun goal ->
    let env = env goal in
    let sigma = Sigma.to_evar_map (sigma goal) in
    Feedback.msg_info Pp.(str"interp-in: " ++ Printer.pr_glob_constr glob);
    let sigma, term = Tacinterp.interp_open_constr ist env sigma (glob,None) in
    Feedback.msg_info Pp.(str"interp-out: " ++ Printer.pr_constr term);
    tclUNIT (env,sigma,term)
  })

(* Commits the term to the monad *)
(* I think we should make the API safe by storing here the original evar map,
 * so that one cannot commit it wrongly.
 * We could also commit the term automatically, but this makes the code less
 * modular, see the 2 functions below that would need to "uncommit" *)
let tclKeepOpenConstr (_env, sigma, t) = Unsafe.tclEVARS sigma <*> tclUNIT t

(* The ssr heuristic : *)
(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)
let guess_max_implicits ist glob =
  tclORELSE
    (interp_glob ist (mkGApp glob (mkGHoles 6)) >>= fun (env,sigma,term) ->
     let term_ty = Retyping.get_type_of env sigma term in
     let ctx, _ = Reductionops.splay_prod env sigma term_ty in
     tclUNIT (List.length ctx))
  (fun _ -> tclUNIT 5)

let pad_to_inductive ist glob = Proofview.Goal.(enter_one { enter = fun goal ->
  interp_glob ist glob >>= fun (env,sigma,term) ->
    let term_ty = Retyping.get_type_of env sigma term in
    let ctx, i = Reductionops.splay_prod env sigma term_ty in
    if isAppInd env sigma i
    then tclUNIT (mkGApp glob (mkGHoles (List.length ctx)))
    else tclUNIT glob
})

(* CoqAPI, the one in Tacticals.New scares me ... *)
let rec tclFIRST = function
  | [] -> Tacticals.New.tclZEROMSG Pp.(str"tclFIRST")
  | tac :: rest -> tclORELSE tac (fun _ -> tclFIRST rest)

(* Builds v p *)
let interp_view ist v p =
  let adaptors = AdaptorDb.(get Forward) in
  (* We cast the pile of views p into a term p_id *)
  tclINJ_CONSTR_IST ist p >>= fun (ist, p_id) ->
  (* We find out how to build (v p) eventually using an adaptor *)
  tclORELSE
    (pad_to_inductive ist v >>= fun vpad ->
     tclFIRST (List.map (fun a -> interp_glob ist (mkGApp a [vpad; p_id])) adaptors))
    (fun _ -> guess_max_implicits ist v >>=
              tclFIRSTi (fun n -> interp_glob ist (mkGApp v (mkGHoles n @ [p_id]))))
  >>= tclKeepOpenConstr

(* we store in the state (v top), then (v1 (v2 top))... *)
let pile_up_view (ist, v) =
  let ist = CoqAPI.Option.assert_get ist (Pp.str"not a term") in
  tclGET_VIEWPILE >>= fun p -> interp_view ist v p >>= tclUPD_VIEWPILE

let pf_merge_uc uc sigma = Evd.merge_universe_context sigma uc
let pf_merge_uc_of sigma gl =
  let ucst = Evd.evar_universe_context sigma in
  pf_merge_uc ucst gl

let pf k f sigma = f (Tacmach.re_sig k sigma)

let pose_proof s0 p = Proofview.Goal.(enter_one { enter = fun g ->
  let env = Proofview.Goal.env g in
  let sigma = Sigma.to_evar_map (sigma g) in
  let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
  let p = Reductionops.nf_evar sigma p in
  let get_body = function Evd.Evar_defined x -> x | _ -> assert false in
  let rigid_of s =
    List.fold_left (fun l k ->
      if Evd.is_defined sigma k then
          k :: l @ 
        (Evar.Set.elements
          (Evd.evars_of_term
            (Reductionops.nf_evar sigma (get_body (Evd.(evar_body (find sigma k)))))))
      else l
    ) [] s in
  let und0 = (* Undefined in initial goal *)
    let g0 =
      Evd.evars_of_filtered_evar_info
        (Evd.find (Tacmach.project s0) (Tacmach.sig_it s0)) in
    List.filter (fun k -> Evar.Set.mem k g0)
      (List.map fst (Evar.Map.bindings (Evd.undefined_map (Tacmach.project s0)))) in
  let rigid = rigid_of und0 in
  let n, p, to_prune, _ucst = Ssrcommon.pf_abs_evars2 s0 rigid (sigma, p) in
  let p = Ssrcommon.pf_abs_cterm s0 n p in
  Feedback.msg_info Pp.(str"view_result: " ++ Printer.pr_constr p);
  let sigma = List.fold_left Evd.remove sigma to_prune in
  Unsafe.tclEVARS sigma <*> Tactics.generalize [p]
})

let tclSIGMA0 = Proofview.Goal.(enter_one { enter = fun g ->
  let k = Proofview.Goal.goal (Proofview.Goal.assume g) in
  let sigma = Sigma.to_evar_map (sigma g) in
  tclUNIT (Tacmach.re_sig k sigma)
})

let end_view_application s0 = tclGET_VIEWPILE >>= pose_proof s0 <*> tclRESET_VIEWPILE

let is_tac = function `Tac _ -> true | _ -> false

let rec tac_views s0 = function
  | [] -> end_view_application s0
  | v :: vs ->
      tclINDEPENDENTL (is_tac_in_term v) >>= fun tacs ->
      if not((List.for_all is_tac tacs ||
             not(List.exists is_tac tacs))) then
        CErrors.error ("/view is too ambiguous: tactic or term? use ltac: or term:");
      let actions =
        List.map (function
          | `Tac tac -> end_view_application s0 <*> interp_glob_tac tac (*wrong s0 *)
          | `Term v -> pile_up_view v) tacs in
      (* CAVEAT: we are committing to mono-goal tactics, what about
       * ltacM:(tactic), a new ltac quotation, identical to "ltac:" that
       * tells us to be multi goal? *)
      tclDISPATCH actions <*> tac_views s0 vs

let tac_views vs =
      on_state (fun ({ view_pile } as s) -> assert (view_pile = None); s)
  <*> tclSIGMA0 >>= fun sigma0 -> tac_views sigma0 vs
  <*> on_state (fun ({ view_pile } as s) -> assert (view_pile = None); s)

let rec ipat_tac1 ipat : unit tactic =
  match ipat with
  | IPatView l -> tac_views l

  | IPatDispatch(m,ipats) ->
     tclDISPATCH (List.map ipat_tac ipats)
  | IPatName (m,id) ->
     interp_raw_tac (lookup_tac ("intro_id" ^ suffix_of_name_mod m) [in_ident id])
       
  | IPatCase(m,ipatss) ->
     Tacticals.New.tclTHENS (tclWITHTOP (tac_case m)) (List.map ipat_tac ipatss)

  | IPatAnon(iter) ->
      interp_raw_tac (lookup_tac ("intro_anon" ^ suffix_of_anon_iter iter) [])

  | IPatNoop -> tclUNIT ()

  | IPatDrop ->
     interp_raw_tac (lookup_tac ("intro_drop") [])

  | IPatClearMark -> tclNIY "IPatClearMark"

  | IPatClear(ids) ->
     interp_raw_tac (lookup_tac ("intro_clear") [in_idents ids])

  | IPatSimpl (Simpl n) ->
       V82.tactic (Hook.get Ssrcommon.simpltac (Ssrast.Simpl n))
  | IPatSimpl (Cut n) ->
       V82.tactic (Hook.get Ssrcommon.simpltac (Ssrast.Cut n))
  | IPatSimpl (SimplCut (n,m)) ->
       V82.tactic (Hook.get Ssrcommon.simpltac (Ssrast.SimplCut (n,m)))

  | IPatRewrite dir ->
     let allocc = Some(false,[]) in
     tclWITHTOP (fun x -> V82.tactic (Hook.get Ssrcommon.ipat_rewrite_tac allocc dir x))

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> interp_raw_tac (lookup_tac ("intro_finalize") [])
  | pat :: pl -> tclTHEN (ipat_tac1 pat) (ipat_tac pl)
