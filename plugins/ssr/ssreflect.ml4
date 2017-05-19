(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

(* This line is read by the Makefile's dist target: do not remove. *)
DECLARE PLUGIN "ssreflect_plugin"
let ssrversion = "2.0";;
let ssrAstVersion = 1;;
let () = Mltop.add_known_plugin (fun () ->
  if Flags.is_verbose () && not !Flags.batch_mode then begin
    Printf.printf "\nSmall Scale Reflection version %s loaded.\n" ssrversion;
    Printf.printf "Copyright 2005-2017 Microsoft Corporation and INRIA.\n";
    Printf.printf "Distributed under the terms of the CeCILL-B license.\n\n"
  end)
  "ssreflect_plugin"
;;

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

(*i camlp4use: "pa_extend.cmo" i*)
(*i camlp4deps: "grammar/grammar.cma" i*)

open Names
open Pp
open Feedback
open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Ltac_plugin
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
open Ssrbwd
open Ssrequality
open Ssrelim
open Ssrparser

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

module Intset = Evar.Set

(** Ssreflect load check. *)

(* To allow ssrcoq to be fully compatible with the "plain" Coq, we only *)
(* turn on its incompatible features (the new rewrite syntax, and the   *)
(* reserved identifiers) when the theory library (ssreflect.v) has      *)
(* has actually been required, or is being defined. Because this check  *)
(* needs to be done often (for each identifier lookup), we implement    *)
(* some caching, repeating the test only when the environment changes.  *)
(*   We check for protect_term because it is the first constant loaded; *)
(* ssr_have would ultimately be a better choice.                        *)
let ssr_loaded = Summary.ref ~name:"SSR:loaded" false
let is_ssr_loaded () =
  !ssr_loaded ||
  (if CLexer.is_keyword "SsrSyntax_is_Imported" then ssr_loaded:=true;
   !ssr_loaded)

(** Utils {{{ *****************************************************************)
let safeDestApp c =
  match kind_of_term c with App (f, a) -> f, a | _ -> c, [| |]
let get_index = function ArgArg i -> i | _ ->
  anomaly "Uninterpreted index"
(* Toplevel constr must be globalized twice ! *)

let skip_numchars s =
  let rec loop i = match s.[i] with '0'..'9' -> loop (i + 1) | _ -> i in loop
(* More sensible names for constr printers *)
let prl_constr = pr_lconstr
let pr_constr = pr_constr
let prl_glob_constr c = pr_lglob_constr_env (Global.env ()) c
let prl_constr_expr = pr_lconstr_expr
let prl_glob_constr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> prl_glob_constr c

(** Constructors for cast type *)
let dC t = CastConv t

let mkAppRed f c = match kind_of_term f with
| Lambda (_, _, b) -> subst1 c b
| _ -> mkApp (f, [|c|])

(* Application to a sequence of n rels (for building eta-expansions). *)
(* The rel indices decrease down to imin (inclusive), unless n < 0,   *)
(* in which case they're incresing (from imin).                       *)
let mkType () = Universes.new_Type (Lib.cwd ())

(* ssrterm conbinators *)
let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"
let loc_ofCG = function
 | (_, (s, None)) -> Glob_ops.loc_of_glob_constr s
 | (_, (_, Some s)) -> Constrexpr_ops.constr_loc s

let map_fold_constr g f ctx acc cstr =
  let array_f ctx acc x = let x, acc = f ctx acc x in acc, x in
  match kind_of_term cstr with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _) ->
      cstr, acc
  | Proj (x,c) ->
      let c', acc = f ctx acc c in
      (if c == c' then cstr else mkProj (x,c')), acc
  | Cast (c,k, t) ->
      let c', acc = f ctx acc c in
      let t', acc = f ctx acc t in
      (if c==c' && t==t' then cstr else mkCast (c', k, t')), acc
  | Prod (na,t,c) ->
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,None,t) ctx) acc c in
      (if t==t' && c==c' then cstr else mkProd (na, t', c')), acc
  | Lambda (na,t,c) ->
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,None,t) ctx) acc c in
      (if t==t' && c==c' then cstr else  mkLambda (na, t', c')), acc
  | LetIn (na,b,t,c) ->
      let b', acc = f ctx acc b in
      let t', acc = f ctx acc t in
      let c', acc = f (g (na,Some b,t) ctx) acc c in
      (if b==b' && t==t' && c==c' then cstr else mkLetIn (na, b', t', c')), acc
  | App (c,al) ->
      let c', acc = f ctx acc c in
      let acc, al' = CArray.smartfoldmap (array_f ctx) acc al in
      (if c==c' && Array.for_all2 (==) al al' then cstr else mkApp (c', al')),
      acc
  | Evar (e,al) ->
      let acc, al' = CArray.smartfoldmap (array_f ctx) acc al in
      (if Array.for_all2 (==) al al' then cstr else mkEvar (e, al')), acc
  | Case (ci,p,c,bl) ->
      let p', acc = f ctx acc p in
      let c', acc = f ctx acc c in
      let acc, bl' = CArray.smartfoldmap (array_f ctx) acc bl in
      (if p==p' && c==c' && Array.for_all2 (==) bl bl' then cstr else
        mkCase (ci, p', c', bl')),
      acc
  | Fix (ln,(lna,tl,bl)) ->
      let acc, tl' = CArray.smartfoldmap (array_f ctx) acc tl in
      let ctx' = Array.fold_left2 (fun l na t -> g (na,None,t) l) ctx lna tl in
      let acc, bl' = CArray.smartfoldmap (array_f ctx') acc bl in
      (if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkFix (ln,(lna,tl',bl'))), acc
  | CoFix(ln,(lna,tl,bl)) ->
      let acc, tl' = CArray.smartfoldmap (array_f ctx) acc tl in
      let ctx' = Array.fold_left2 (fun l na t -> g (na,None,t) l) ctx lna tl in
      let acc,bl' = CArray.smartfoldmap (array_f ctx') acc bl in
      (if Array.for_all2 (==) tl tl' && Array.for_all2 (==) bl bl'
      then cstr
      else mkCoFix (ln,(lna,tl',bl'))), acc

(* }}} *)


let inVersion = Libobject.declare_object {
  (Libobject.default_object "SSRASTVERSION") with
  Libobject.load_function = (fun _ (_,v) -> 
    if v <> ssrAstVersion then CErrors.error "Please recompile your .vo files");
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "ssreflect version";
      Goptions.optkey   = ["SsrAstVersion"];
      Goptions.optread  = (fun _ -> true);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun _ -> 
        Lib.add_anonymous_leaf (inVersion ssrAstVersion)) }

let tactic_expr = Pltac.tactic_expr
let gallina_ext = Vernac_.gallina_ext 
let sprintf = Printf.sprintf
let tactic_mode = G_ltac.tactic_mode

(** 1. Utilities *)


(** Pretty-printing utilities *)

let tacltop = (5,Ppextend.E)

(** Tactic-level diagnosis *)

let pf_pr_constr gl = pr_constr_env (pf_env gl)

(* debug *)

let pf_msg gl =
   let ppgl = pr_leconstr_env (pf_env gl) (project gl) (pf_concl gl) in
   Feedback.msg_info (str "goal is " ++ ppgl)

let msgtac gl = pf_msg gl; tclIDTAC gl

(** Tactic utilities *)

let last_goal gls = let sigma, gll = Refiner.unpackage gls in
   Refiner.repackage sigma (List.nth gll (List.length gll - 1))

let pf_ids_of_proof_hyps gl =
  let add_hyp decl ids =
    let id = NamedDecl.get_id decl in
    if not_section_id id then id :: ids else ids in
  Context.Named.fold_outside add_hyp (pf_hyps gl) ~init:[]

let pf_new_evar gl ty =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma (extra, sigma, _) = Evarutil.new_evar env sigma ty in
  let sigma = Sigma.to_evar_map sigma in
  re_sig it sigma, extra

(* Basic tactics *)

let reduct_in_concl t = reduct_in_concl (t, DEFAULTcast)
let settac id c = letin_tac None (Name id) c None
let posetac id cl = Proofview.V82.of_tactic (settac id cl nowhere)

let apply_type x xs = Proofview.V82.of_tactic (apply_type x xs)

(* Let's play with the new proof engine API *)
module PG = Proofview.Goal
module TN = Tacticals.New
let old_tac = Proofview.V82.tactic
let new_tac = Proofview.V82.of_tactic


(** Name generation {{{ *******************************************************)

(* Since Coq now does repeated internal checks of its external lexical *)
(* rules, we now need to carve ssreflect reserved identifiers out of   *)
(* out of the user namespace. We use identifiers of the form _id_ for  *)
(* this purpose, e.g., we "anonymize" an identifier id as _id_, adding *)
(* an extra leading _ if this might clash with an internal identifier. *)
(*    We check for ssreflect identifiers in the ident grammar rule;    *)
(* when the ssreflect Module is present this is normally an error,     *)
(* but we provide a compatibility flag to reduce this to a warning.    *)

let ssr_reserved_ids = Summary.ref ~name:"SSR:idents" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect identifiers";
      Goptions.optkey   = ["SsrIdents"];
      Goptions.optdepr  = false;
      Goptions.optread  = (fun _ -> !ssr_reserved_ids);
      Goptions.optwrite = (fun b -> ssr_reserved_ids := b)
    }

let is_ssr_reserved s =
  let n = String.length s in n > 2 && s.[0] = '_' && s.[n - 1] = '_'

let ssr_id_of_string loc s =
  if is_ssr_reserved s && is_ssr_loaded () then begin
    if !ssr_reserved_ids then
      loc_error loc (str ("The identifier " ^ s ^ " is reserved."))
    else if is_internal_name s then
      Feedback.msg_warning (str ("Conflict between " ^ s ^ " and ssreflect internal names."))
    else Feedback.msg_warning (str (
     "The name " ^ s ^ " fits the _xxx_ format used for anonymous variables.\n"
  ^ "Scripts with explicit references to anonymous variables are fragile."))
    end; id_of_string s

let ssr_null_entry = Gram.Entry.of_parser "ssr_null" (fun _ -> ())

let (!@) = Pcoq.to_coqloc

GEXTEND Gram 
  GLOBAL: Prim.ident;
  Prim.ident: [[ s = IDENT; ssr_null_entry -> ssr_id_of_string !@loc s ]];
END

let perm_tag = "_perm_Hyp_"
let _ = add_internal_name (is_tagged perm_tag)
let mk_perm_id =
  let salt = ref 1 in 
  fun () -> salt := !salt mod 10000 + 1; mk_tagged_id perm_tag !salt

  
(* }}} *)

(* We must not anonymize context names discharged by the "in" tactical. *)

(** Tactical extensions. {{{ **************************************************)

(* The TACTIC EXTEND facility can't be used for defining new user   *)
(* tacticals, because:                                              *)
(*  - the concrete syntax must start with a fixed string            *)
(*   We use the following workaround:                               *)
(*  - We use the (unparsable) "YouShouldNotTypeThis"  token for tacticals that      *)
(*    don't start with a token, then redefine the grammar and       *)
(*    printer using GEXTEND and set_pr_ssrtac, respectively.        *)

type ssrargfmt = ArgSsr of string | ArgCoq of argument_type | ArgSep of string

let ssrtac_name name = {
  mltac_plugin = "ssreflect_plugin";
  mltac_tactic = "ssr" ^ name;
}

let ssrtac_entry name n = {
  mltac_name = ssrtac_name name; 
  mltac_index = n;
}

let set_pr_ssrtac name prec afmt =
  let fmt = List.map (function
    | ArgSep s -> Egramml.GramTerminal s
    | ArgSsr s -> Egramml.GramTerminal s
    | ArgCoq at -> Egramml.GramTerminal "COQ_ARG") afmt in
  let tacname = ssrtac_name name in ()
  (* FIXME *)
(*
   Pptactic.declare_ml_tactic_pprule tacname
    { Pptactic.pptac_args = mk_akey afmt;
      Pptactic.pptac_prods = (prec, fmt) }
*)

let ssrtac_atom loc name args = TacML (loc, ssrtac_entry name 0, args)
let ssrtac_expr = ssrtac_atom

(* fun gl -> let lfun = [tacarg_id, val_interp ist gl gtac] in
  interp_tac_gen lfun [] ist.debug tacarg_expr gl *)



(* }}} *)

(** Tacticals (+, -, *, done, by, do, =>, first, and last). {{{ ***************)

(** Bracketing tactical *)

(* The tactic pretty-printer doesn't know that some extended tactics *)
(* are actually tacticals. To prevent it from improperly removing    *)
(* parentheses we override the parsing rule for bracketed tactic     *)
(* expressions so that the pretty-print always reflects the input.   *)
(* (Removing user-specified parentheses is dubious anyway).          *)

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrparentacarg: [[ "("; tac = tactic_expr; ")" -> !@loc, Tacexp tac ]];
  tactic_expr: LEVEL "0" [[ arg = ssrparentacarg -> TacArg arg ]];
END

(** The internal "done" and "ssrautoprop" tactics. *)

(* For additional flexibility, "done" and "ssrautoprop" are  *)
(* defined in Ltac.                                          *)
(* Although we provide a default definition in ssreflect,    *)
(* we look up the definition dynamically at each call point, *)
(* to allow for user extensions. "ssrautoprop" defaults to   *)
(* trivial.                                                  *)

let ssrautoprop gl =
  try 
    let tacname = 
      try Nametab.locate_tactic (qualid_of_ident (id_of_string "ssrautoprop"))
      with Not_found -> Nametab.locate_tactic (ssrqid "ssrautoprop") in
    let tacexpr = dummy_loc, Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
    Proofview.V82.of_tactic (eval_tactic (Tacexpr.TacArg tacexpr)) gl
  with Not_found -> Proofview.V82.of_tactic (Auto.full_trivial []) gl

let () = ssrautoprop_tac := ssrautoprop

let tclBY tac = tclTHEN tac (donetac ~-1)

(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

(* Force use of the tactic_expr parsing entry, to rule out tick marks. *)

(** The "by" tactical. *)


open Ssrfwd

TACTIC EXTEND ssrtclby
| [ "by" ssrhintarg(tac) ] -> [ Proofview.V82.tactic (hinttac ist true tac) ]
END

(* }}} *)
(* We can't parse "by" in ARGUMENT EXTEND because it will only be made *)
(* into a keyword in ssreflect.v; so we anticipate this in GEXTEND.    *)

GEXTEND Gram
  GLOBAL: ssrhint simple_tactic;
  ssrhint: [[ "by"; arg = ssrhintarg -> arg ]];
END

(** The "in" pseudo-tactical {{{ **********************************************)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" suffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

(** Clear switch *)

let cleartac clr = check_hyps_uniq [] clr; Proofview.V82.of_tactic (clear (hyps_ids clr))

(* type ssrwgen = ssrclear * ssrhyp * string *)



let nohide = mkRel 0
let hidden_goal_tag = "the_hidden_goal"


let check_wgen_uniq gens =
  let clears = List.flatten (List.map fst gens) in
  check_hyps_uniq [] clears;
  let ids = CList.map_filter
    (function (_,Some ((id,_),_)) -> Some (hoi_id id) | _ -> None) gens in
  let rec check ids = function
  | id :: _ when List.mem id ids ->
    errorstrm (str"Duplicate generalization " ++ pr_id id)
  | id :: hyps -> check (id :: ids) hyps
  | [] -> () in
  check [] ids

let pf_clauseids gl gens clseq =
  let keep_clears = List.map (fun (x, _) -> x, None) in
  if gens <> [] then (check_wgen_uniq gens; gens) else
  if clseq <> InAll && clseq <> InAllHyps then keep_clears gens else
  CErrors.error "assumptions should be named explicitly"

let hidden_clseq = function InHyps | InHypsSeq | InAllHyps -> true | _ -> false

let hidetacs clseq idhide cl0 =
  if not (hidden_clseq clseq) then  [] else
  [posetac idhide cl0;
   Proofview.V82.of_tactic (convert_concl_no_check (EConstr.mkVar idhide))]

let endclausestac id_map clseq gl_id cl0 gl =
  let not_hyp' id = not (List.mem_assoc id id_map) in
  let orig_id id = try List.assoc id id_map with _ -> id in
  let dc, c = EConstr.decompose_prod_assum (project gl) (pf_concl gl) in
  let hide_goal = hidden_clseq clseq in
  let c_hidden = hide_goal && EConstr.eq_constr (project gl) c (EConstr.mkVar gl_id) in
  let rec fits forced = function
  | (id, _) :: ids, decl :: dc' when RelDecl.get_name decl = Name id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (not hide_goal || dc' = [] && c_hidden) in
  let rec unmark c = match EConstr.kind (project gl) c with
  | Var id when hidden_clseq clseq && id = gl_id -> cl0
  | Prod (Name id, t, c') when List.mem_assoc id id_map ->
    EConstr.mkProd (Name (orig_id id), unmark t, unmark c')
  | LetIn (Name id, v, t, c') when List.mem_assoc id id_map ->
    EConstr.mkLetIn (Name (orig_id id), unmark v, unmark t, unmark c')
  | _ -> EConstr.map (project gl) unmark c in
  let utac hyp =
    Proofview.V82.of_tactic 
     (convert_hyp_no_check (NamedDecl.map_constr unmark hyp)) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' =
    Proofview.V82.of_tactic
      (convert_concl_no_check (unmark (pf_concl gl'))) gl' in
  let ctacs = if hide_goal then [Proofview.V82.of_tactic (clear [gl_id])] else [] in
  let mktac itacs = tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, id) = Proofview.V82.of_tactic (introduction id) in
  if fits false (id_map, List.rev dc) then mktac (List.map itac id_map) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_hyp' all_ids && not c_hidden then mktac [] gl else
  CErrors.error "tampering with discharged assumptions of \"in\" tactical"

let abs_wgen keep_let ist f gen (gl,args,c) =
  let sigma, env = project gl, pf_env gl in
  let evar_closed t p =
    if occur_existential sigma t then
      CErrors.user_err ~loc:(loc_of_cpattern p) ~hdr:"ssreflect"
        (pr_constr_pat (EConstr.Unsafe.to_constr t) ++
        str" contains holes and matches no subterm of the goal") in
  match gen with
  | _, Some ((x, mode), None) when mode = "@" || (mode = " " && keep_let) ->
     let x = hoi_id x in
     let decl = pf_get_hyp gl x in
     gl,
     (if NamedDecl.is_local_def decl then args else EConstr.mkVar x :: args),
     mkProd_or_LetIn (decl |> NamedDecl.to_rel_decl |> RelDecl.set_name (Name (f x)))
                     (EConstr.Vars.subst_var x c)
  | _, Some ((x, _), None) ->
     let x = hoi_id x in
     gl, EConstr.mkVar x :: args, EConstr.mkProd (Name (f x),pf_get_hyp_typ gl x, EConstr.Vars.subst_var x c)
  | _, Some ((x, "@"), Some p) -> 
     let x = hoi_id x in
     let cp = interp_cpattern ist gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma (EConstr.Unsafe.to_constr c) cp None 1
       with NoMatch -> redex_of_pattern env cp, (EConstr.Unsafe.to_constr c) in
     let c = EConstr.of_constr c in
     let t = EConstr.of_constr t in
     evar_closed t p;
     let ut = red_product_skip_id env sigma t in
     let gl, ty = pfe_type_of gl t in
     pf_merge_uc ucst gl, args, EConstr.mkLetIn(Name (f x), ut, ty, c)
  | _, Some ((x, _), Some p) ->
     let x = hoi_id x in
     let cp = interp_cpattern ist gl p None in
     let (t, ucst), c =
       try fill_occ_pattern ~raise_NoMatch:true env sigma (EConstr.Unsafe.to_constr c) cp None 1
       with NoMatch -> redex_of_pattern env cp, (EConstr.Unsafe.to_constr c) in
     let c = EConstr.of_constr c in
     let t = EConstr.of_constr t in
     evar_closed t p;
     let gl, ty = pfe_type_of gl t in
     pf_merge_uc ucst gl, t :: args, EConstr.mkProd(Name (f x), ty, c)
  | _ -> gl, args, c

let clr_of_wgen gen clrs = match gen with
  | clr, Some ((x, _), None) ->
     let x = hoi_id x in
     cleartac clr :: cleartac [SsrHyp(Loc.ghost,x)] :: clrs
  | clr, _ -> cleartac clr :: clrs
    
let tclCLAUSES ist tac (gens, clseq) gl =
  if clseq = InGoal || clseq = InSeqGoal then tac gl else
  let clr_gens = pf_clauseids gl gens clseq in
  let clear = tclTHENLIST (List.rev(List.fold_right clr_of_wgen clr_gens [])) in
  let gl_id = mk_anon_id hidden_goal_tag gl in
  let cl0 = pf_concl gl in
  let dtac gl =
    let c = pf_concl gl in
    let gl, args, c =
      List.fold_right (abs_wgen true ist mk_discharged_id) gens (gl,[], c) in
    apply_type c args gl in
  let endtac =
    let id_map = CList.map_filter (function
      | _, Some ((x,_),_) -> let id = hoi_id x in Some (mk_discharged_id id, id)
      | _, None -> None) gens in
    endclausestac id_map clseq gl_id cl0 in
  tclTHENLIST (hidetacs clseq gl_id cl0 @ [dtac; clear; tac; endtac]) gl
(* }}} *)

open Ssripats
open Ssrview

(** The "do" tactical. ********************************************************)

(*
type ssrdoarg = ((ssrindex * ssrmmod) * ssrhint) * ssrclauses
*)

let ssrdotac ist (((n, m), tac), clauses) =
  let mul = get_index n, m in
  tclCLAUSES ist (tclMULT mul (hinttac ist false tac)) clauses

TACTIC EXTEND ssrtcldo
| [ "YouShouldNotTypeThis" "do" ssrdoarg(arg) ] -> [ Proofview.V82.tactic (ssrdotac ist arg) ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr loc n m tac clauses =
  let arg = ((n, m), tac), clauses in
  ssrtac_expr loc "tcldo" [Tacexpr.TacGeneric (in_gen (rawwit wit_ssrdoarg) arg)]

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrdotac: [
    [ tac = tactic_expr LEVEL "3" -> mk_hint tac
    | tacs = ssrortacarg -> tacs
  ] ];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr !@loc noindex m tac clauses
    | IDENT "do"; tac = ssrortacarg; clauses = ssrclauses ->
      ssrdotac_expr !@loc noindex Once tac clauses
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                  tac = ssrdotac; clauses = ssrclauses ->
      ssrdotac_expr !@loc (mk_index !@loc n) m tac clauses
    ] ];
END
(* }}} *)

(** The "first" and "last" tacticals. {{{ *************************************)


let tclPERM perm tac gls =
  let subgls = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let subgll' = perm subgll in
  Refiner.repackage sigma subgll'
(*
let tclPERM perm tac gls =
  let mkpft n g r =
    {Proof_type.open_subgoals = n; Proof_type.goal = g; Proof_type.ref = r} in
  let mkleaf g = mkpft 0 g None in
  let mkprpft n g pr a = mkpft n g (Some (Proof_type.Prim pr, a)) in
  let mkrpft n g c = mkprpft n g (Proof_type.Refine c) in
  let mkipft n g =
    let mki pft (id, _, _ as d) =
      let g' = {g with evar_concl = mkNamedProd_or_LetIn d g.evar_concl} in
      mkprpft n g' (Proof_type.Intro id) [pft] in
    List.fold_left mki in
  let gl = Refiner.sig_it gls in
  let mkhyp subgl =
    let rec chop_section = function
    | (x, _, _ as d) :: e when not_section_id x -> d :: chop_section e
    | _ -> [] in
    let lhyps = Environ.named_context_of_val subgl.evar_hyps in
    mk_perm_id (), subgl, chop_section lhyps in
  let mkpfvar (hyp, subgl, lhyps) =
    let mkarg args (lhyp, body, _) =
      if body = None then mkVar lhyp :: args else args in
    mkrpft 0 subgl (applist (mkVar hyp, List.fold_left mkarg [] lhyps)) [] in
  let mkpfleaf (_, subgl, lhyps) = mkipft 1 gl (mkleaf subgl) lhyps in
  let mkmeta _ = Evarutil.mk_new_meta () in
  let mkhypdecl (hyp, subgl, lhyps) =
    hyp, None, it_mkNamedProd_or_LetIn subgl.evar_concl lhyps in
  let subgls, v as res0 = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let n = List.length subgll in if n = 0 then res0 else
  let hyps = List.map mkhyp subgll in
  let hyp_decls = List.map mkhypdecl (List.rev (perm hyps)) in
  let c = applist (mkmeta (), List.map mkmeta subgll) in
  let pft0 = mkipft 0 gl (v (List.map mkpfvar hyps)) hyp_decls in
  let pft1 = mkrpft n gl c (pft0 :: List.map mkpfleaf (perm hyps)) in
  let subgll', v' = Refiner.frontier pft1 in
  Refiner.repackage sigma subgll', v'
*)

let tclREV tac gl = tclPERM List.rev tac gl

let rot_hyps dir i hyps =
  let n = List.length hyps in
  if i = 0 then List.rev hyps else
  if i > n then CErrors.error "Not enough subgoals" else
  let rec rot i l_hyps = function
    | hyp :: hyps' when i > 0 -> rot (i - 1) (hyp :: l_hyps) hyps'
    | hyps' -> hyps' @ (List.rev l_hyps) in
  rot (match dir with L2R -> i | R2L -> n - i) [] hyps

let tclSEQAT ist atac1 dir (ivar, ((_, atacs2), atac3)) =
  let i = get_index ivar in
  let evtac = ssrevaltac ist in
  let tac1 = evtac atac1 in
  if atacs2 = [] && atac3 <> None then tclPERM (rot_hyps dir i) tac1  else
  let evotac = function Some atac -> evtac atac | _ -> tclIDTAC in
  let tac3 = evotac atac3 in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (i - 1), List.map evotac atacs2 with
  | L2R, [], [tac2] when atac3 = None -> tclTHENFIRST tac1 tac2
  | L2R, [], [tac2] when atac3 = None -> tclTHENLAST tac1 tac2
  | L2R, pad, tacs2 -> tclTHENSFIRSTn tac1 (Array.of_list (pad @ tacs2)) tac3
  | R2L, pad, tacs2 -> tclTHENSLASTn tac1 tac3 (Array.of_list (tacs2 @ pad))

(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let pr_ssrseqdir _ _ _ = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "

ARGUMENT EXTEND ssrseqdir TYPED AS ssrdir PRINTED BY pr_ssrseqdir
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

TACTIC EXTEND ssrtclseq
| [ "YouShouldNotTypeThis" ssrtclarg(tac) ssrseqdir(dir) ssrseqarg(arg) ] ->
  [ Proofview.V82.tactic (tclSEQAT ist tac dir arg) ]
END
set_pr_ssrtac "tclseq" 5 [ArgSsr "tclarg"; ArgSsr "seqdir"; ArgSsr "seqarg"]

let tclseq_expr loc tac dir arg =
  let arg1 = in_gen (rawwit wit_ssrtclarg) tac in
  let arg2 = in_gen (rawwit wit_ssrseqdir) dir in
  let arg3 = in_gen (rawwit wit_ssrseqarg) (check_seqtacarg dir arg) in
  ssrtac_expr loc "tclseq" (List.map (fun x -> Tacexpr.TacGeneric x) [arg1; arg2; arg3])

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssr_first: [
    [ tac = ssr_first; ipats = ssrintros_ne -> tclintros_expr !@loc tac ipats
    | "["; tacl = LIST0 tactic_expr SEP "|"; "]" -> TacFirst tacl
    ] ];
  ssr_first_else: [
    [ tac1 = ssr_first; tac2 = ssrorelse -> TacOrelse (tac1, tac2)
    | tac = ssr_first -> tac ]];
  tactic_expr: LEVEL "4" [ LEFTA
    [ tac1 = tactic_expr; ";"; IDENT "first"; tac2 = ssr_first_else ->
      TacThen (tac1, tac2)
    | tac = tactic_expr; ";"; IDENT "first"; arg = ssrseqarg ->
      tclseq_expr !@loc tac L2R arg
    | tac = tactic_expr; ";"; IDENT "last"; arg = ssrseqarg ->
      tclseq_expr !@loc tac R2L arg
    ] ];
END
(* }}} *)

(** 5. Bookkeeping tactics (clear, move, case, elim) *)

(* post-interpretation of terms *)
let whd_app f args = Reductionops.whd_betaiota Evd.empty (EConstr.mkApp (f, args))

let pr_cargs a =
  str "[" ++ pr_list pr_spc pr_constr (Array.to_list a) ++ str "]"

(** Rewrite redex switch *)

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

(* type ssrgen = ssrdocc * ssrterm *)

let pr_gen (docc, dt) = pr_docc docc ++ pr_cpattern dt

let pr_ssrgen _ _ _ = pr_gen

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * cpattern PRINTED BY pr_ssrgen
| [ ssrdocc(docc) cpattern(dt) ] -> [ docc, dt ]
| [ cpattern(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> None

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

(* type ssrgens = ssrgen list *)
(* type ssrdgens = ssrgens list * ssrclear *)

let gens_sep = function [], [] -> mt | _ -> spc

let pr_dgens pr_gen (gensl, clr) =
  let prgens s gens = str s ++ pr_list spc pr_gen gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens _ _ _ = pr_dgens pr_gen

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  CErrors.error "multiple dependents switches '/'"

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ cpattern(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END



let first_goal gls =
  let gl = gls.Evd.it and sig_0 = gls.Evd.sigma in
  if List.is_empty gl then CErrors.error "first_goal";
  { Evd.it = List.hd gl; Evd.sigma = sig_0; }

let with_deps deps0 maintac cl0 cs0 clr0 ist gl0 =
  let rec loop gl cl cs clr args clrs = function
  | [] ->
    let n = List.length args in
    maintac (if n > 0 then EConstr.applist (EConstr.to_lambda (project gl) n cl, args) else cl) clrs ist gl0
  | dep :: deps ->
    let gl' = first_goal (genclrtac cl cs clr gl) in
    let cl', c', clr',gl' = pf_interp_gen ist gl' false dep in
    loop gl' cl' [c'] clr' (c' :: args) (clr' :: clrs) deps in
  loop gl0 cl0 cs0 clr0 cs0 [clr0] (List.rev deps0)

(** Equations *)

(* argument *)

type ssreqid = ssripat option

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ssripatrep option PRINTED BY pr_ssreqid
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssreqid strm =
  match Util.stream_nth 0 strm with
  | Tok.IDENT _ -> accept_before_syms [":"] strm
  | Tok.KEYWORD ":" -> ()
  | Tok.KEYWORD pat when List.mem pat ["_"; "?"; "->"; "<-"] ->
                      accept_before_syms [":"] strm
  | _ -> raise Stream.Failure

let test_ssreqid = Gram.Entry.of_parser "test_ssreqid" accept_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid;
  ssreqpat: [
    [ id = Prim.ident -> IPatId (None, id)
    | "_" -> IPatAnon Drop
    | "?" -> IPatAnon One
    | occ = ssrdocc; "->" -> (match occ with
      | None, occ -> IPatRewrite (occ, L2R)
      | _ -> loc_error !@loc (str"Only occurrences are allowed here"))
    | occ = ssrdocc; "<-" -> (match occ with
      | None, occ ->  IPatRewrite (occ, R2L)
      | _ -> loc_error !@loc (str "Only occurrences are allowed here"))
    | "->" -> IPatRewrite (allocc, L2R)
    | "<-" -> IPatRewrite (allocc, R2L)
    ]];
  ssreqid: [
    [ test_ssreqid; pat = ssreqpat -> Some pat
    | test_ssreqid -> None
    ]];
END

(** Bookkeeping (discharge-intro) argument *)

(* Since all bookkeeping ssr commands have the same discharge-intro    *)
(* argument format we use a single grammar entry point to parse them.  *)
(* the entry point parses only non-empty arguments to avoid conflicts  *)
(* with the basic Coq tactics.                                         *)

(* type ssrarg = ssrview * (ssreqid * (ssrdgens * ssripats)) *)

let pr_ssrarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_gen dgens ++ pri ipats

ARGUMENT EXTEND ssrarg TYPED AS ssrview * (ssreqid * (ssrdgens * ssrintros))
   PRINTED BY pr_ssrarg
| [ ssrview(view) ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ view, (eqid, (dgens, ipats)) ]
| [ ssrview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ view, (None, (([], clr), ipats)) ]
| [ ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ [], (eqid, (dgens, ipats)) ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ [], (None, (([], clr), ipats)) ]
| [ ssrintros_ne(ipats) ] ->
  [ [], (None, (([], []), ipats)) ]
END

(** The "clear" tactic *)

(* We just add a numeric version that clears the n top assumptions. *)

let poptac ist n = introstac ~ist (List.init n (fun _ -> IPatAnon Drop))

TACTIC EXTEND ssrclear
  | [ "clear" natural(n) ] -> [ Proofview.V82.tactic (poptac ist n) ]
END

(** The "move" tactic *)

(* TODO: review this, in particular the => _ and => [] cases *)
let rec improper_intros = function
  | IPatSimpl _ :: ipats -> improper_intros ipats
  | (IPatId _ | IPatAnon _ | IPatCase _) :: _ -> false
  | [] -> true

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    CErrors.error "incompatible view and equation in move tactic"
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    CErrors.error "incompatible view and occurrence switch in move tactic"
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    CErrors.error "dependents switch `/' in move tactic"
  | _, (eqid, (_, ipats)) when eqid <> None && improper_intros ipats ->
    CErrors.error "no proper intro pattern for equation in move tactic"
  | arg -> arg

ARGUMENT EXTEND ssrmovearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_movearg arg ]
END



TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ Proofview.V82.tactic (tclTHEN (ssrmovetac ist arg) (introstac ~ist [pat])) ]
| [ "move" ssrmovearg(arg) ssrclauses(clauses) ] ->
  [ Proofview.V82.tactic (tclCLAUSES ist (ssrmovetac ist arg) clauses) ]
| [ "move" ssrrpat(pat) ] -> [ Proofview.V82.tactic (introstac ~ist [pat]) ]
| [ "move" ] -> [ Proofview.V82.tactic (movehnftac) ]
END



let pf_fresh_inductive_instance ind gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, indu = Evd.fresh_inductive_instance env sigma ind in
  indu, re_sig it sigma




let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  CErrors.error "incompatible view and occurrence switch in dependent case tactic"
| arg -> arg

ARGUMENT EXTEND ssrcasearg TYPED AS ssrarg PRINTED BY pr_ssrarg
| [ ssrarg(arg) ] -> [ check_casearg arg ]
END


TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrclauses(clauses) ] ->
  [ old_tac (tclCLAUSES ist (ssrcasetac ist arg) clauses) ]
| [ "case" ] -> [ old_tac (with_fresh_ctx (with_top (ssrscasetac false))) ]
END

(** The "elim" tactic *)

(* Elim views are elimination lemmas, so the eliminated term is not addded *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {+} switch is used, or the equation switch  *)
(* is used and there are no dependents.                                    *)

let ssrelimtac ist (view, (eqid, (dgens, ipats))) =
  let ndefectelimtac view eqid ipats deps gen ist gl =
    let elim = match view with [v] -> Some (snd(force_term ist gl v)) | _ -> None in
    ssrelim ~ist deps (`EGen gen) ?elim eqid (elim_intro_tac ipats) gl
  in
  with_dgens dgens (ndefectelimtac view eqid ipats) ist 

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrclauses(clauses) ] ->
  [ old_tac (tclCLAUSES ist (ssrelimtac ist arg) clauses) ]
| [ "elim" ] -> [ old_tac (with_fresh_ctx (with_top elimtac)) ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let pr_agen (docc, dt) = pr_docc docc ++ pr_term dt
let pr_ssragen _ _ _ = pr_agen
let pr_ssragens _ _ _ = pr_dgens pr_agen

ARGUMENT EXTEND ssragen TYPED AS ssrdocc * ssrterm PRINTED BY pr_ssragen
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ] -> [ mkclr clr, dt ]
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssragen list list * ssrclear 
PRINTED BY pr_ssragens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ [[]], clr]
| [ ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

let mk_applyarg views agens intros = views, (None, (agens, intros))

let pr_ssraarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_eqid eqid ++ pr_dgens pr_agen dgens ++ pri ipats

ARGUMENT EXTEND ssrapplyarg 
TYPED AS ssrview * (ssreqid * (ssragens * ssrintros))
PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) intros ]
| [ ssrclear_ne(clr) ssrintros(intros) ] ->
  [ mk_applyarg [] ([], clr) intros ]
| [ ssrintros_ne(intros) ] ->
  [ mk_applyarg [] ([], []) intros ]
| [ ssrview(view) ":" ssragen(gen) ssragens(dgens) ssrintros(intros) ] ->
  [ mk_applyarg view (cons_gen gen dgens) intros ]
| [ ssrview(view) ssrclear(clr) ssrintros(intros) ] ->
  [ mk_applyarg view ([], clr) intros ]
    END

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [ Proofview.V82.tactic (ssrapplytac ist arg) ]
| [ "apply" ] -> [ Proofview.V82.tactic apply_top_tac ]
END

(** The "exact" tactic *)

let mk_exactarg views dgens = mk_applyarg views dgens []

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyarg PRINTED BY pr_ssraarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_exactarg [] (cons_gen gen dgens) ]
| [ ssrview(view) ssrclear(clr) ] ->
  [ mk_exactarg view ([], clr) ]
| [ ssrclear_ne(clr) ] ->
  [ mk_exactarg [] ([], clr) ]
END

let vmexacttac pf =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  exact_no_check (EConstr.mkCast (pf, VMcast, Tacmach.New.pf_concl gl))
  end }

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [ Proofview.V82.tactic (tclBY (ssrapplytac ist arg)) ]
| [ "exact" ] -> [ Proofview.V82.tactic (tclORELSE (donetac ~-1) (tclBY apply_top_tac)) ]
| [ "exact" "<:" lconstr(pf) ] -> [ vmexacttac pf ]
END

(** The "congr" tactic *)

(* type ssrcongrarg = open_constr * (int * constr) *)

let pr_ssrcongrarg _ _ _ ((n, f), dgens) =
  (if n <= 0 then mt () else str " " ++ int n) ++
  str " " ++ pr_term f ++ pr_dgens pr_gen dgens

ARGUMENT EXTEND ssrcongrarg TYPED AS (int * ssrterm) * ssrdgens
  PRINTED BY pr_ssrcongrarg
| [ natural(n) constr(c) ssrdgens(dgens) ] -> [ (n, mk_term xNoFlag c), dgens ]
| [ natural(n) constr(c) ] -> [ (n, mk_term xNoFlag c),([[]],[]) ]
| [ constr(c) ssrdgens(dgens) ] -> [ (0, mk_term xNoFlag c), dgens ]
| [ constr(c) ] -> [ (0, mk_term xNoFlag c), ([[]],[]) ]
END



TACTIC EXTEND ssrcongr
| [ "congr" ssrcongrarg(arg) ] ->
[ let arg, dgens = arg in
  Proofview.V82.tactic begin
    match dgens with
    | [gens], clr -> tclTHEN (genstac (gens,clr) ist) (newssrcongrtac arg ist)
    | _ -> errorstrm (str"Dependent family abstractions not allowed in congr")
  end]
END

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Coq rewrite compatibility flag *)

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, None -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind = add_genarg "ssrrwkind" pr_rwkind

let pr_rule = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term r
  | RWeq, r -> pr_term r

let pr_ssrrule _ _ _ = pr_rule

let noruleterm loc = mk_term xNoFlag (mkCProp loc)

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrwkind * ssrterm PRINTED BY pr_ssrrule
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

GEXTEND Gram
  GLOBAL: ssrrule_ne;
  ssrrule_ne : [
    [ test_not_ssrslashnum; x =
        [ "/"; t = ssrterm -> RWdef, t
        | t = ssrterm -> RWeq, t 
        | s = ssrsimpl_ne -> RWred s, noruleterm !@loc
        ] -> x
    | s = ssrsimpl_ne -> RWred s, noruleterm !@loc
  ]];
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_ne PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, noruleterm loc ]
END

(** Rewrite arguments *)

let pr_option f = function None -> mt() | Some x -> f x
let pr_pattern_squarep= pr_option (fun r -> str "[" ++ pr_rpattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_rwarg ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_pattern_squarep rx ++ pr_rule r

let pr_ssrrwarg _ _ _ = pr_rwarg

ARGUMENT EXTEND ssrpattern_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
  | [ ] -> [ None ]
END

ARGUMENT EXTEND ssrpattern_ne_squarep
TYPED AS rpattern option PRINTED BY pr_ssrpattern_squarep
  | [ "[" rpattern(rdx) "]" ] -> [ Some rdx ]
END


ARGUMENT EXTEND ssrrwarg
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * rpattern option) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrrule(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, None) r ]
  | [ "{" ssrocc(occ) "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkocc occ, rx) r ]
  | [ "{" "}" ssrpattern_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (nodocc, rx) r ]
  | [ ssrpattern_ne_squarep(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (noclr, rx) r ]
  | [ ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult norwocc r ]
END

TACTIC EXTEND ssrinstofruleL2R
| [ "ssrinstancesofruleL2R" ssrterm(arg) ] -> [ Proofview.V82.tactic (ssrinstancesofrule ist L2R arg) ]
END
TACTIC EXTEND ssrinstofruleR2L
| [ "ssrinstancesofruleR2L" ssrterm(arg) ] -> [ Proofview.V82.tactic (ssrinstancesofrule ist R2L arg) ]
END

(** Rewrite argument sequence *)

(* type ssrrwargs = ssrrwarg list *)

let pr_ssrrwargs _ _ _ rwargs = pr_list spc pr_rwarg rwargs

ARGUMENT EXTEND ssrrwargs TYPED AS ssrrwarg list PRINTED BY pr_ssrrwargs
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let ssr_rw_syntax = Summary.ref ~name:"SSR:rewrite" true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      Goptions.optname  = "ssreflect rewrite";
      Goptions.optkey   = ["SsrRewrite"];
      Goptions.optread  = (fun _ -> !ssr_rw_syntax);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b -> ssr_rw_syntax := b) }

let test_ssr_rw_syntax =
  let test strm  =
    if not !ssr_rw_syntax then raise Stream.Failure else
    if is_ssr_loaded () then () else
    match Util.stream_nth 0 strm with
    | Tok.KEYWORD key when List.mem key.[0] ['{'; '['; '/'] -> ()
    | _ -> raise Stream.Failure in
  Gram.Entry.of_parser "test_ssr_rw_syntax" test

GEXTEND Gram
  GLOBAL: ssrrwargs;
  ssrrwargs: [[ test_ssr_rw_syntax; a = LIST1 ssrrwarg -> a ]];
END

(** The "rewrite" tactic *)

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs(args) ssrclauses(clauses) ] ->
    [ Proofview.V82.tactic (tclCLAUSES ist (ssrrewritetac ist args) clauses) ]
END

(** The "unlock" tactic *)

let pr_unlockarg (occ, t) = pr_occ occ ++ pr_term t
let pr_ssrunlockarg _ _ _ = pr_unlockarg

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrterm(t) ] -> [ occ, t ]
  | [  ssrterm(t) ] -> [ None, t ]
END

let pr_ssrunlockargs _ _ _ args = pr_list spc pr_unlockarg args

ARGUMENT EXTEND ssrunlockargs TYPED AS ssrunlockarg list
  PRINTED BY pr_ssrunlockargs
  | [  ssrunlockarg_list(args) ] -> [ args ]
END

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockargs(args) ssrclauses(clauses) ] ->
[  Proofview.V82.tactic (tclCLAUSES ist (unlocktac ist args) clauses) ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)


TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ Proofview.V82.tactic (ssrposetac ist ffwd) ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ Proofview.V82.tactic (ssrposetac ist ffwd) ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ Proofview.V82.tactic (ssrposetac ist (id, fwd)) ]
END

(** The "set" tactic *)

(* type ssrsetfwd = ssrfwd * ssrdocc *)

TACTIC EXTEND ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrclauses(clauses) ] ->
  [ Proofview.V82.tactic (tclCLAUSES ist (ssrsettac ist id fwd) clauses) ]
END

(** The "have" tactic *)

(* type ssrhavefwd = ssrfwd * ssrhint *)


(* Pltac. *)

(* The standard TACTIC EXTEND does not work for abstract *)
GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "3"
    [ RIGHTA [ IDENT "abstract"; gens = ssrdgens ->
               ssrtac_expr !@loc "abstract"
                [Tacexpr.TacGeneric (Genarg.in_gen (Genarg.rawwit wit_ssrdgens) gens)] ]];
END
TACTIC EXTEND ssrabstract
| [ "abstract" ssrdgens(gens) ] -> [
    if List.length (fst gens) <> 1 then
      errorstrm (str"dependents switches '/' not allowed here");
    Proofview.V82.tactic (ssrabstract ist gens) ]
END

TACTIC EXTEND ssrhave
| [ "have" ssrhavefwdwbinders(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist fwd false false) ]
END

TACTIC EXTEND ssrhavesuff
| [ "have" "suff" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrhavesuffices
| [ "have" "suffices" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true false) ]
END

TACTIC EXTEND ssrsuffhave
| [ "suff" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

TACTIC EXTEND ssrsufficeshave
| [ "suffices" "have" ssrhpats_nobs(pats) ssrhavefwd(fwd) ] ->
  [ Proofview.V82.tactic (havetac ist (false,(pats,fwd)) true true) ]
END

(** The "suffice" tactic *)

let pr_ssrsufffwdwbinders _ _ prt (hpats, (fwd, hint)) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrsufffwd
  TYPED AS ssrhpats * (ssrfwd * ssrhint) PRINTED BY pr_ssrsufffwdwbinders
| [ ssrhpats(pats) ssrbinder_list(bs)  ":" lconstr(t) ssrhint(hint) ] ->
  [ let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let fwd = mkFwdHint ":" t in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs fwd, hint) ]
END

let sufftac ist ((((clr, pats),binders),simpl), ((_, c), hint)) =
  let htac = tclTHEN (introstac ~ist pats) (hinttac ist true hint) in
  let c = match c with
  | (a, (b, Some (CCast (_, _, CastConv cty)))) -> a, (b, Some cty)
  | (a, (GCast (_, _, CastConv cty), None)) -> a, (cty, None)
  | _ -> anomaly "suff: ssr cast hole deleted by typecheck" in
  let ctac gl =
    let _,ty,_,uc = pf_interp_ty ist gl c in let gl = pf_merge_uc uc gl in
    Ssrfwd.basecuttac "ssr_suff" ty gl in
  tclTHENS ctac [htac; tclTHEN (cleartac clr) (introstac ~ist (binders@simpl))]

TACTIC EXTEND ssrsuff
| [ "suff" ssrsufffwd(fwd) ] -> [ Proofview.V82.tactic (sufftac ist fwd) ]
END

TACTIC EXTEND ssrsuffices
| [ "suffices" ssrsufffwd(fwd) ] -> [ Proofview.V82.tactic (sufftac ist fwd) ]
END

(** The "wlog" (Without Loss Of Generality) tactic *)

(* type ssrwlogfwd = ssrwgen list * ssrfwd *)

let pr_ssrwlogfwd _ _ _ (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd t

ARGUMENT EXTEND ssrwlogfwd TYPED AS ssrwgen list * ssrfwd
                         PRINTED BY pr_ssrwlogfwd
| [ ":" ssrwgen_list(gens) "/" lconstr(t) ] -> [ gens, mkFwdHint "/" t]
END

let destProd_or_LetIn sigma c =
  match EConstr.kind sigma c with
  | Prod (n,ty,c) -> RelDecl.LocalAssum (n, ty), c
  | LetIn (n,bo,ty,c) -> RelDecl.LocalDef (n, bo, ty), c
  | _ -> raise DestKO
        
let wlogtac ist (((clr0, pats),_),_) (gens, ((_, ct))) hint suff ghave gl =
  let mkabs gen = abs_wgen false ist (fun x -> x) gen in
  let mkclr gen clrs = clr_of_wgen gen clrs in
  let mkpats = function
  | _, Some ((x, _), _) -> fun pats -> IPatId (None, hoi_id x) :: pats
  | _ -> fun x -> x in
  let ct = match ct with
  | (a, (b, Some (CCast (_, _, CastConv cty)))) -> a, (b, Some cty)
  | (a, (GCast (_, _, CastConv cty), None)) -> a, (cty, None)
  | _ -> anomaly "wlog: ssr cast hole deleted by typecheck" in
  let cut_implies_goal = not (suff || ghave <> `NoGen) in
  let c, args, ct, gl =
    let gens = List.filter (function _, Some _ -> true | _ -> false) gens in
    let concl = pf_concl gl in
    let c = EConstr.mkProp in
    let c = if cut_implies_goal then EConstr.mkArrow c concl else c in
    let gl, args, c = List.fold_right mkabs gens (gl,[],c) in
    let env, _ =
      List.fold_left (fun (env, c) _ ->
        let rd, c = destProd_or_LetIn (project gl) c in
        EConstr.push_rel rd env, c) (pf_env gl, c) gens in
    let sigma = project gl in
    let sigma = Sigma.Unsafe.of_evar_map sigma in
    let Sigma (ev, sigma, _) = Evarutil.new_evar env sigma EConstr.mkProp in
    let sigma = Sigma.to_evar_map sigma in
    let k, _ = EConstr.destEvar sigma ev in
    let fake_gl = {Evd.it = k; Evd.sigma = sigma} in
    let _, ct, _, uc = pf_interp_ty ist fake_gl ct in
    let rec var2rel c g s = match EConstr.kind sigma c, g with
      | Prod(Anonymous,_,c), [] -> EConstr.mkProd(Anonymous, EConstr.Vars.subst_vars s ct, c)
      | Sort _, [] -> EConstr.Vars.subst_vars s ct
      | LetIn(Name id as n,b,ty,c), _::g -> EConstr.mkLetIn (n,b,ty,var2rel c g (id::s))
      | Prod(Name id as n,ty,c), _::g -> EConstr.mkProd (n,ty,var2rel c g (id::s))
      | _ -> CErrors.anomaly(str"SSR: wlog: var2rel: " ++ pr_econstr c) in
    let c = var2rel c gens [] in
    let rec pired c = function
      | [] -> c
      | t::ts as args -> match EConstr.kind sigma c with
         | Prod(_,_,c) -> pired (EConstr.Vars.subst1 t c) ts
         | LetIn(id,b,ty,c) -> EConstr.mkLetIn (id,b,ty,pired c args)
         | _ -> CErrors.anomaly(str"SSR: wlog: pired: " ++ pr_econstr c) in
    c, args, pired c args, pf_merge_uc uc gl in
  let tacipat pats = introstac ~ist pats in
  let tacigens = 
    tclTHEN
      (tclTHENLIST(List.rev(List.fold_right mkclr gens [cleartac clr0])))
      (introstac ~ist (List.fold_right mkpats gens [])) in
  let hinttac = hinttac ist true hint in
  let cut_kind, fst_goal_tac, snd_goal_tac =
    match suff, ghave with
    | true, `NoGen -> "ssr_wlog", tclTHEN hinttac (tacipat pats), tacigens
    | false, `NoGen -> "ssr_wlog", hinttac, tclTHEN tacigens (tacipat pats)
    | true, `Gen _ -> assert false
    | false, `Gen id ->
      if gens = [] then errorstrm(str"gen have requires some generalizations");
      let clear0 = cleartac clr0 in
      let id, name_general_hyp, cleanup, pats = match id, pats with
      | None, (IPatId (mod_id,id) as ip)::pats -> (* FIXME mod_id *) Some id, tacipat [ip], clear0, pats
      | None, _ -> None, tclIDTAC, clear0, pats
      | Some (Some id),_ -> Some id, introid id, clear0, pats
      | Some _,_ ->
          let id = mk_anon_id "tmp" gl in
          Some id, introid id, tclTHEN clear0 (Proofview.V82.of_tactic (clear [id])), pats in
      let tac_specialize = match id with
      | None -> tclIDTAC
      | Some id ->
        if pats = [] then tclIDTAC else
        let args = Array.of_list args in
        ppdebug(lazy(str"specialized="++pr_econstr EConstr.(mkApp (mkVar id,args))));
        ppdebug(lazy(str"specialized_ty="++pr_econstr ct));
        tclTHENS (basecuttac "ssr_have" ct)
          [Proofview.V82.of_tactic (apply EConstr.(mkApp (mkVar id,args))); tclIDTAC] in
      "ssr_have",
      (if hint = nohint then tacigens else hinttac),
      tclTHENLIST [name_general_hyp; tac_specialize; tacipat pats; cleanup]
  in
  tclTHENS (basecuttac cut_kind c) [fst_goal_tac; snd_goal_tac] gl

TACTIC EXTEND ssrwlog
| [ "wlog" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwlogs
| [ "wlog" "suff" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwlogss
| [ "wlog" "suffices" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutloss
| [ "without" "loss" ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint false `NoGen) ]
END

TACTIC EXTEND ssrwithoutlosss
| [ "without" "loss" "suff" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

TACTIC EXTEND ssrwithoutlossss
| [ "without" "loss" "suffices" 
    ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ]->
  [ Proofview.V82.tactic (wlogtac ist pats fwd hint true `NoGen) ]
END

(* Generally have *)
let pr_idcomma _ _ _ = function
  | None -> mt()
  | Some None -> str"_, "
  | Some (Some id) -> pr_id id ++ str", "

ARGUMENT EXTEND ssr_idcomma TYPED AS ident option option PRINTED BY pr_idcomma
  | [ ] -> [ None ]
END

let accept_idcomma strm =
  match stream_nth 0 strm with
  | Tok.IDENT _ | Tok.KEYWORD "_" -> accept_before_syms [","] strm
  | _ -> raise Stream.Failure

let test_idcomma = Gram.Entry.of_parser "test_idcomma" accept_idcomma

GEXTEND Gram
  GLOBAL: ssr_idcomma;
  ssr_idcomma: [ [ test_idcomma; 
    ip = [ id = IDENT -> Some (id_of_string id) | "_" -> None ]; "," ->
    Some ip
  ] ];
END

let augment_preclr clr1 (((clr0, x),y),z) = (((clr1 @ clr0, x),y),z)

TACTIC EXTEND ssrgenhave
| [ "gen" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    Proofview.V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

TACTIC EXTEND ssrgenhave2
| [ "generally" "have" ssrclear(clr)
    ssr_idcomma(id) ssrhpats_nobs(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ let pats = augment_preclr clr pats in
    Proofview.V82.tactic (wlogtac ist pats fwd hint false (`Gen id)) ]
END

(*
(* => *)
TACTIC EXTEND ssrtclintros
| [ "YouShouldNotTypeThis" ssrintrosarg(arg) ] ->
  [ let tac, intros = arg in
    Proofview.V82.tactic (tclINTROS ist (fun ist -> ssrevaltac ist tac) intros) ]
END
 *)

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)
