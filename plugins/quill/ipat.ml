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
open Quill_common

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

type ipat =
  | IPatNoop
  | IPatName of name_mod option * Id.t
  | IPatAnon of anon_iter (* inaccessible name *)
  | IPatDrop (* => _ *)
  | IPatClearMark
  | IPatDispatch of ipats_mod option * ipat list list (* /[..|..] *)
  | IPatCase of ipats_mod option * ipat list list (* this is not equivalent to /case /[..|..] if there are already multiple goals *)
  | IPatTactic of (raw_tactic_expr * selector option * unit list) (* /tac *)
(*  | IPatRewrite of occurrence option * rewrite_pattern * direction *)
  | IPatView of constr_expr list (* /view *)
  | IPatClear of Id.t list(* {H1 H2} *)
  | IPatSimpl of simpl
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

(** [intro id] introduces the first premise (product or let-in) of the goal
    under the name [id], reducing the head of the goal (using beta, iota, delta
    but not zeta) if necessary. If [id] is None, a name is generated, that will
    not be user accesible. If the goal does not start with a product or a let-in
    even after reduction, it fails. *)
let intro ~id = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let store = Goal.extra gl in
  let g = Goal.raw_concl gl in
  let decl,t = CoqAPI.decompose_assum env (Sigma.to_evar_map sigma) g in
  let id = match id, Rel.Declaration.get_name decl with
    | Some id, _ -> id
    | _, Name id ->
       if Ssreflect_plugin.Ssrcommon.is_discharged_id id then id
       else mk_anon_id (string_of_id id) gl
    | _, _ -> mk_anon_id Ssreflect_plugin.Ssrcommon.ssr_anon_hyp gl
  in
  unsafe_intro env store (set_decl_id id decl) t
 }

let intro_id id = intro ~id:(Some id)
let intro_anon = intro ~id:None

let intro_anon_all = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.raw_concl gl in
  let n = Quill_common.nb_assums env (Sigma.to_evar_map sigma) g in
  Tacticals.New.tclDO n intro_anon
 }

let intro_anon_deps = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.raw_concl gl in
  let n = Quill_common.nb_deps_assums env (Sigma.to_evar_map sigma) g in
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

(** [intro_drop] behaves like [intro_anon] but registers the id of the
introduced assumption for a delayed clear. *)
(* TODO: see if we could avoid duplicating code by using [Goal.enter_one]. *)
let intro_drop = Goal.enter { enter = fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let store = Goal.extra gl in
  let g = Goal.raw_concl gl in
  let decl,t = CoqAPI.decompose_assum env (Sigma.to_evar_map sigma) g in
  let id = match Rel.Declaration.get_name decl with
    | Name id ->
       if Ssreflect_plugin.Ssrcommon.is_discharged_id id then id
       else mk_anon_id (string_of_id id) gl
    | _ -> mk_anon_id Ssreflect_plugin.Ssrcommon.ssr_anon_hyp gl
  in
  unsafe_intro env store (set_decl_id id decl) t
  <*>
  set_state (upd_state (fun st -> { st with to_clear = id :: st.to_clear }))
 }

(** [intro_finalize] performs the actions that have been delayed. *)
let intro_finalize = Goal.enter { enter = fun gl ->
  let state = Goal.state gl in
  match Proofview_monad.StateStore.get state state_field with
  | None -> tclUNIT ()
  | Some state -> Tactics.clear state.to_clear
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
      V82.tactic (Ssreflect_plugin.Ssreflect.perform_injection t)
  | None ->
  Goal.enter { enter = fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let evd = Sigma.to_evar_map sigma in
    let evd, ty = Typing.type_of ~refresh:false env evd t in
    let (nparams,seeds) = analyze env evd ty in 
    let i = ref (-1) in
    let case_tac = Hook.get Ssreflect_plugin.Ssrcommon.simplest_newcase_tac in
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

(* FIXME: use unreachable name *)
let tclWITHTOP tac =
  let top = Id.of_string "top_assumption" in
  intro_id top <*> tac (mkVar top) <*> Tactics.clear [top]


(* The .v file that loads the plugin *)
let bios_dirpath = DirPath.make [Id.of_string "quill"]
let bios_ml = "quill_plugin"

let locate_tac name =
  let mk_qtid name = Libnames.make_qualid bios_dirpath name in
  let mk_tid name = Libnames.qualid_of_ident name in
  let keep f x = ignore(f x);Libnames.Qualid (Loc.ghost,x) in
  try keep Nametab.locate_tactic (mk_tid name)
  with Not_found ->
    try keep Nametab.locate_tactic (mk_qtid name)
    with Not_found ->
      CErrors.error ("Quill not loaded, missing " ^ Id.to_string name)


let lookup_tac name args : raw_tactic_expr =
  TacArg(Loc.ghost, TacCall(Loc.ghost, locate_tac (Id.of_string name), args))

let in_ident id =
  TacGeneric (Genarg.in_gen (Genarg.rawwit Stdarg.wit_ident) id)

let rec ipat_tac1 ipat : unit tactic =
  match ipat with
  | IPatTactic(t,sel,args) ->
     Tacinterp.hide_interp true t None
  | IPatDispatch(m,ipats) ->
     tclDISPATCH (List.map ipat_tac ipats)
  | IPatName (m,id) ->
     ipat_tac1 (IPatTactic(
        lookup_tac ("intro_id" ^ suffix_of_name_mod m) [in_ident id],
        None,[]))
       
  | IPatCase(m,ipatss) ->
     Tacticals.New.tclTHENS (tclWITHTOP (tac_case m)) (List.map ipat_tac ipatss)

  | IPatAnon(iter) ->
     ipat_tac1 (IPatTactic(
        lookup_tac ("intro_anon" ^ suffix_of_anon_iter iter) [],
        None,[]))

(*
  | IPatConcat(_kind,prefix) ->
     tac_intro_seed ipat_tac prefix
*)
  | IPatNoop -> tclNIY "IPatNoop"

  | IPatDrop ->
     ipat_tac1 (IPatTactic(lookup_tac ("intro_drop") [],None,[]))

  | IPatClearMark -> tclNIY "IPatClearMark"
  | IPatView views -> tclNIY "IPatView"
  | IPatClear ids -> tclNIY "IPatClear"
  | IPatSimpl simp -> tclNIY "IPatSimpl"

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> ipat_tac1 (IPatTactic(lookup_tac ("intro_finalize") [],None,[]))
  | pat :: pl -> tclTHEN (ipat_tac1 pat) (ipat_tac pl)
