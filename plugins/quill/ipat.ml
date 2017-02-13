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
  intro_id_slow top <*> tac (mkVar top) <*> Tactics.clear [top]


(* The problem is: how to enrich multi goals tactic with state?  Tactics like
cycle which are not aware of our state type should thread it correctly, so it
should really be attached to goals *)

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


(* BEGIN FIXME this is mostly tacextend.mlp *)
let export_to_ltac ~name ~nargs code =
  let args =
    List.init nargs (fun i -> Id.of_string (sprintf "%s_arg_%d" name i)) in
  let mltac _ ist =
    let args =
      List.map (fun arg ->
        try Id.Map.find arg ist.Tacinterp.lfun 
        with Not_found ->
          CErrors.anomaly Pp.(str "calling convention mismatch: " ++
            str name ++ str " arg " ++ Ppconstr.pr_id arg)
      ) args
    in
      code ist args in
  let tname = { mltac_plugin = bios_ml; mltac_tactic = name; } in
  let () = Tacenv.register_ml_tactic tname [|mltac|] in
  let tac =
    Tacexpr.TacFun (List.map (fun x -> Some x) args,
      Tacexpr.TacML (Loc.ghost, {mltac_name = tname; mltac_index = 0}, [])) in
  let obj () = Tacenv.register_ltac true false (Id.of_string name) tac in
  Mltop.declare_cache_obj obj bios_ml
(* /END *)


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
(*
  | IPatConcat(_kind,prefix) ->
     tac_intro_seed ipat_tac prefix
*)
  | IPatNoop -> tclNIY "IPatNoop"
  | IPatAnon iter -> tclNIY "IPatAnon"
  | IPatDrop -> tclNIY "IPatDrop"
  | IPatClearMark -> tclNIY "IPatClearMark"
  | IPatView views -> tclNIY "IPatView"
  | IPatClear ids -> tclNIY "IPatClear"
  | IPatSimpl simp -> tclNIY "IPatSimpl"

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> tclUNIT ()
  | pat :: pl -> tclTHEN (ipat_tac1 pat) (ipat_tac pl)

(* FIXME LL EXPORTS, angain should be done by tacextend.mlp magin in g_quill.ml4*)
let exported_intro_id ist = function
  | [ id ] ->
      let id = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_ident) id in
      intro_id_slow id
  | _ -> assert false (* give API error *)

let () = export_to_ltac "intro_id" 1 exported_intro_id

let exported_intro_id_prepend ist = function
  | [ id ] ->
      let id = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_ident) id in
      tac_intro_seed ipat_tac `Prepend id
  | _ -> assert false (* give API error *)

let () = export_to_ltac "intro_id_prepend" 1 exported_intro_id_prepend

let exported_intro_id_append ist = function
  | [ id ] ->
      let id = Tacinterp.Value.cast (Genarg.topwit Stdarg.wit_ident) id in
      tac_intro_seed ipat_tac `Append id
  | _ -> assert false (* give API error *)

let () = export_to_ltac "intro_id_append" 1 exported_intro_id_append


(*
let ipat_tac pl =
  
 *)
