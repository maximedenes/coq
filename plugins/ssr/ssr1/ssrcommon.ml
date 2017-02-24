(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

open Names
open Proof_type
open Evd
open Tacmach
open Refiner
open Ssrmatching_plugin.Ssrmatching
open Ssrast

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.freeze () ;;


type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

let push_ctx  a gl = re_sig (sig_it gl, a) (project gl)
let push_ctxs a gl =
  re_sig (List.map (fun x -> x,a) (sig_it gl)) (project gl)
let pull_ctx gl = let g, a = sig_it gl in re_sig g (project gl), a
let pull_ctxs gl = let g, a = List.split (sig_it gl) in re_sig g (project gl), a

let with_ctx f gl =
  let gl, ctx = pull_ctx gl in
  let rc, ctx = f ctx in
  rc, push_ctx ctx gl
let without_ctx f gl =
  let gl, _ctx = pull_ctx gl in
  f gl
let tac_ctx t gl =
  let gl, a = pull_ctx gl in
  let gl = t gl in
  push_ctxs a gl

let tclTHEN_ia t1 t2 gl =
  let gal = t1 gl in
  let goals, sigma = sig_it gal, project gal in
  let _, opened, sigma =
    List.fold_left (fun (i,opened,sigma) g ->
      let gl = t2 i (re_sig g sigma) in
      i+1, sig_it gl :: opened, project gl)
      (1,[],sigma) goals in
  re_sig (List.flatten (List.rev opened)) sigma

let tclTHEN_a t1 t2 gl = tclTHEN_ia t1 (fun _ -> t2) gl

let tclTHENS_a t1 tl gl = tclTHEN_ia t1
  (fun i -> List.nth tl (i-1)) gl

let rec tclTHENLIST_a = function
  | [] -> tac_ctx tclIDTAC
  | t1::tacl -> tclTHEN_a t1 (tclTHENLIST_a tacl)

(* like  tclTHEN_i but passes to the tac "i of n" and not just i *)
let tclTHEN_i_max tac taci gl =
  let maxi = ref 0 in
  tclTHEN_ia (tclTHEN_ia tac (fun i -> maxi := max i !maxi; tac_ctx tclIDTAC))
    (fun i gl -> taci i !maxi gl) gl

let tac_on_all gl tac =
  let goals = sig_it gl in
  let opened, sigma =
    List.fold_left (fun (opened,sigma) g ->
      let gl = tac (re_sig g sigma) in
      sig_it gl :: opened, project gl)
      ([],project gl) goals in
  re_sig (List.flatten (List.rev opened)) sigma

(* Used to thread data between intro patterns at run time *)
type tac_ctx = {
  tmp_ids : (Id.t * name ref) list;
  wild_ids : Id.t list;
  delayed_clears : Id.t list;
  speed : [ `Slow | `Fast ]
}

let new_ctx () =
  { tmp_ids = []; wild_ids = []; delayed_clears = []; speed = `Slow }

let with_fresh_ctx t gl =
  let gl = push_ctx (new_ctx()) gl in
  let gl = t gl in
  fst (pull_ctxs gl)



type ist = Tacinterp.interp_sign
type gist = Tacintern.glob_sign

open Ssrparser
open Genarg
open Stdarg
open Nameops
open Pp
open Pcoq.Prim

let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep
let dummy_loc = Loc.ghost
let errorstrm x = CErrors.user_err ~hdr:"ssreflect" x
let loc_error loc msg = CErrors.user_err ~loc ~hdr:"ssreflect" msg
let anomaly s = CErrors.anomaly (str s)

(* Tentative patch from util.ml *)

let array_fold_right_from n f v a =
  let rec fold n =
    if n >= Array.length v then a else f v.(n) (fold (succ n))
  in
  fold n

let array_app_tl v l =
  if Array.length v = 0 then invalid_arg "array_app_tl";
  array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then invalid_arg "array_list_of_tl";
  array_fold_right_from 1 (fun e l -> e::l) v []

(* end patch *)


let (!@) = Compat.to_coqloc

(** Constructors for rawconstr *)
open Glob_term
open Globnames
open Misctypes
open Decl_kinds
let mkRHole = Glob_term.GHole (dummy_loc, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []
let rec isRHoles = function GHole _ :: cl -> isRHoles cl | cl -> cl = []
let mkRApp f args = if args = [] then f else GApp (dummy_loc, f, args)
let mkRVar id = GRef (dummy_loc, VarRef id,None)
let mkRltacVar id = GVar (dummy_loc, id)
let mkRCast rc rt =  GCast (dummy_loc, rc, CastConv rt)
let mkRType =  GSort (dummy_loc, GType [])
let mkRProp =  GSort (dummy_loc, GProp)
let mkRArrow rt1 rt2 = GProd (dummy_loc, Anonymous, Explicit, rt1, rt2)
let mkRConstruct c = GRef (dummy_loc, ConstructRef c,None)
let mkRInd mind = GRef (dummy_loc, IndRef mind,None)
let mkRLambda n s t = GLambda (dummy_loc, n, Explicit, s, t)

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr gl (sigma, c) =
  let env = pf_env gl in let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let isAppInd gl c =
  try ignore (pf_reduce_to_atomic_ind gl c); true with _ -> false

let interp_view_nbimps ist gl rc =
  try
    let sigma, t = interp_open_constr ist gl (rc, None) in
    let si = sig_it gl in
    let gl = re_sig si sigma in
    let pl, c = splay_open_constr gl t in
    if isAppInd gl c then List.length pl else (-(List.length pl))
  with _ -> 0

let nbargs_open_constr gl oc =
  let pl, _ = splay_open_constr gl oc in List.length pl

let interp_nbargs ist gl rc =
  try
    let rc6 = mkRApp rc (mkRHoles 6) in
    let sigma, t = interp_open_constr ist gl (rc6, None) in
    let si = sig_it gl in
    let gl = re_sig si sigma in
    6 + nbargs_open_constr gl t
  with _ -> 5

let pf_nbargs gl c = nbargs_open_constr gl (project gl, c)

let internal_names = ref []
let add_internal_name pt = internal_names := pt :: !internal_names
let is_internal_name s = List.exists (fun p -> p s) !internal_names

let tmp_tag = "_the_"
let tmp_post = "_tmp_"
let mk_tmp_id i =
  id_of_string (Printf.sprintf "%s%s%s" tmp_tag (CString.ordinal i) tmp_post)
let new_tmp_id ctx =
  let id = mk_tmp_id (1 + List.length ctx.tmp_ids) in
  let orig = ref Anonymous in
  (id, orig), { ctx with tmp_ids = (id, orig) :: ctx.tmp_ids }
;;


let mk_internal_id s =
  let s' = Bytes.of_string (Printf.sprintf "_%s_" s) in
  for i = 1 to Bytes.length s do if s'.[i] = ' ' then Bytes.set s' i '_' done;
  let s' = Bytes.to_string s' in
  add_internal_name ((=) s'); id_of_string s'

let same_prefix s t n =
  let rec loop i = i = n || s.[i] = t.[i] && loop (i + 1) in loop 0

let skip_digits s =
  let n = String.length s in 
  let rec loop i = if i < n && Util.is_digit s.[i] then loop (i + 1) else i in loop

let mk_tagged_id t i = id_of_string (Printf.sprintf "%s%d_" t i)
let is_tagged t s =
  let n = String.length s - 1 and m = String.length t in
  m < n && s.[n] = '_' && same_prefix s t m && skip_digits s m = n

let evar_tag = "_evar_"
let _ = add_internal_name (is_tagged evar_tag)
let mk_evar_name n = Name (mk_tagged_id evar_tag n)

let ssr_anon_hyp = "Hyp"

let wildcard_tag = "_the_"
let wildcard_post = "_wildcard_"
let mk_wildcard_id i =
  id_of_string (Printf.sprintf "%s%s%s" wildcard_tag (CString.ordinal i) wildcard_post)
let has_wildcard_tag s = 
  let n = String.length s in let m = String.length wildcard_tag in
  let m' = String.length wildcard_post in
  n < m + m' + 2 && same_prefix s wildcard_tag m &&
  String.sub s (n - m') m' = wildcard_post &&
  skip_digits s m = n - m' - 2
let _ = add_internal_name has_wildcard_tag

let new_wild_id ctx =
  let i = 1 + List.length ctx.wild_ids in
  let id = mk_wildcard_id i in
  id, { ctx with wild_ids = id :: ctx.wild_ids }

let discharged_tag = "_discharged_"
let mk_discharged_id id =
  id_of_string (Printf.sprintf "%s%s_" discharged_tag (string_of_id id))
let has_discharged_tag s =
  let m = String.length discharged_tag and n = String.length s - 1 in
  m < n && s.[n] = '_' && same_prefix s discharged_tag m
let _ = add_internal_name has_discharged_tag
let is_discharged_id id = has_discharged_tag (string_of_id id)

let max_suffix m (t, j0 as tj0) id  =
  let s = string_of_id id in let n = String.length s - 1 in
  let dn = String.length t - 1 - n in let i0 = j0 - dn in
  if not (i0 >= m && s.[n] = '_' && same_prefix s t m) then tj0 else
  let rec loop i =
    if i < i0 && s.[i] = '0' then loop (i + 1) else
    if (if i < i0 then skip_digits s i = n else le_s_t i) then s, i else tj0
  and le_s_t i =
    let ds = s.[i] and dt = t.[i + dn] in
    if ds = dt then i = n || le_s_t (i + 1) else
    dt < ds && skip_digits s i = n in
  loop m

let mk_anon_id t gl =
  let m, si0, id0 =
    let s = ref (Printf.sprintf  "_%s_" t) in
    if is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (Util.is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), id_of_string !s in
  let gl_ids = pf_ids_of_hyps gl in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let s = Bytes.of_string s in
  let n = Bytes.length s - 1 in
  let set = Bytes.set s in
  let rec loop i =
    if s.[i] = '9' then (set i '0'; loop (i - 1)) else
    if i < m then (set n '0'; set m '1'; s ^ "_") else
    (set i (Char.chr (Char.code s.[i] + 1)); s) in
  id_of_string (Bytes.to_string (loop (n - 1)))

let convert_concl_no_check t = Tactics.convert_concl_no_check t Term.DEFAULTcast
let convert_concl t = Tactics.convert_concl t Term.DEFAULTcast

let rename_hd_prod orig_name_ref gl =
  match Term.kind_of_term (pf_concl gl) with
  | Term.Prod(_,src,tgt) ->
      Proofview.V82.of_tactic (convert_concl_no_check (Term.mkProd (!orig_name_ref,src,tgt))) gl
  | _ -> CErrors.anomaly (str "gentac creates no product")

let gentac, gen = Hook.make ()
let gen_tmp_ids
  ?(ist=Geninterp.({ lfun = Id.Map.empty; extra = TacStore.empty })) gl
=
  let gl, ctx = pull_ctx gl in
  push_ctxs ctx
    (tclTHENLIST
      (List.map (fun (id,orig_ref) ->
        tclTHEN 
        (Hook.get gentac ist ((None,Some(false,[])),cpattern_of_id id))
        (rename_hd_prod orig_ref))
      ctx.tmp_ids) gl)
;;


let ssrevaltac ist gtac =
  Proofview.V82.of_tactic (Tacinterp.tactic_of_value ist gtac)
(** Open term to lambda-term coercion  {{{ ************************************)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ := _ + 1 means pose succ := fun n : nat => n + 1, *)
(* and, in context of the the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : detaSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set, which tries       *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to "have" et al. uses product abstraction, e.g.      *)
(*    have Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    have Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

(* Replace new evars with lambda variables, retaining local dependencies *)
(* but stripping global ones. We use the variable names to encode the    *)
(* the number of dependencies, so that the transformation is reversible. *)

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
open Term
let env_size env = List.length (Environ.named_context env)

let pf_abs_evars2 gl rigid (sigma, c0) =
  let sigma0, ucst = project gl, Evd.evar_universe_context sigma in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = CList.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k || List.mem k rigid then evlist else
    let n = max 0 (Array.length a - nenv) in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0,[], ucst else
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
  let rec get i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | (_, (n, t)) :: evl ->
    loop (mkLambda (mk_evar_name n, get (i - 1) t, c)) (i - 1) evl
  | [] -> c in
  List.length evlist, loop (get 1 c0) 1 evlist, List.map fst evlist, ucst

let pf_abs_evars gl t = pf_abs_evars2 gl [] t


(* As before but if (?i : T(?j)) and (?j : P : Prop), then the lambda for i
 * looks like (fun evar_i : (forall pi : P. T(pi))) thanks to "loopP" and all 
 * occurrences of evar_i are replaced by (evar_i evar_j) thanks to "app".
 *
 * If P can be solved by ssrautoprop (that defaults to trivial), then
 * the corresponding lambda looks like (fun evar_i : T(c)) where c is 
 * the solution found by ssrautoprop.
 *)
let ssrautoprop_tac = ref (fun gl -> assert false)

(* Thanks to Arnaud Spiwack for this snippet *)
let call_on_evar tac e s =
  let { it = gs ; sigma = s } =
    tac { it = e ; sigma = s; } in
  gs, s

open Pp
let pp _ = () (* FIXME *)
module Intset = Evar.Set

let pf_abs_evars_pirrel gl (sigma, c0) =
  pp(lazy(str"==PF_ABS_EVARS_PIRREL=="));
  pp(lazy(str"c0= " ++ Printer.pr_constr c0));
  let sigma0 = project gl in
  let c0 = Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma c0) in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = CList.firstn n (evar_filtered_context evi) in
    let abs_dc c = function
    | NamedDecl.LocalDef (x,b,t) -> mkNamedLetIn x b t (mkArrow t c)
    | NamedDecl.LocalAssum (x,t) -> mkNamedProd x t c in
    let t = Context.Named.fold_inside abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma0 (Evarutil.nf_evar sigma t) in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = max 0 (Array.length a - nenv) in
    let k_ty = 
      Retyping.get_sort_family_of 
        (pf_env gl) sigma (Evd.evar_concl (Evd.find sigma k)) in
    let is_prop = k_ty = InProp in
    let t = abs_evar n k in (k, (n, t, is_prop)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let pr_constr t = Printer.pr_constr (Reductionops.nf_beta (project gl) t) in
  pp(lazy(str"evlist=" ++ pr_list (fun () -> str";")
    (fun (k,_) -> str(Evd.string_of_existential k)) evlist));
  let evplist = 
    let depev = List.fold_left (fun evs (_,(_,t,_)) -> 
        Intset.union evs (Evarutil.undefined_evars_of_term sigma t)) Intset.empty evlist in
    List.filter (fun (i,(_,_,b)) -> b && Intset.mem i depev) evlist in
  let evlist, evplist, sigma = 
    if evplist = [] then evlist, [], sigma else
    List.fold_left (fun (ev, evp, sigma) (i, (_,t,_) as p) ->
      try 
        let ng, sigma = call_on_evar !ssrautoprop_tac i sigma in
        if (ng <> []) then errorstrm (str "Should we tell the user?");
        List.filter (fun (j,_) -> j <> i) ev, evp, sigma
      with _ -> ev, p::evp, sigma) (evlist, [], sigma) (List.rev evplist) in
  let c0 = Evarutil.nf_evar sigma c0 in
  let evlist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evlist in
  let evplist = 
    List.map (fun (x,(y,t,z)) -> x,(y,Evarutil.nf_evar sigma t,z)) evplist in
  pp(lazy(str"c0= " ++ pr_constr c0));
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n,_,_)) :: evl -> if k = k' then i,n else lookup k (i + 1) evl in
  let rec get evlist i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get evlist i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get evlist i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) (get evlist) i c in
  let rec app extra_args i c = match decompose_app c with
  | hd, args when isRel hd && destRel hd = i ->
      let j = destRel hd in
      mkApp (mkRel j, Array.of_list (List.map (Vars.lift (i-1)) extra_args @ args))
  | _ -> map_constr_with_binders ((+) 1) (app extra_args) i c in
  let rec loopP evlist c i = function
  | (_, (n, t, _)) :: evl ->
    let t = get evlist (i - 1) t in
    let n = Name (id_of_string (ssr_anon_hyp ^ string_of_int n)) in 
    loopP evlist (mkProd (n, t, c)) (i - 1) evl
  | [] -> c in
  let rec loop c i = function
  | (_, (n, t, _)) :: evl ->
    let evs = Evarutil.undefined_evars_of_term sigma t in
    let t_evplist = List.filter (fun (k,_) -> Intset.mem k evs) evplist in
    let t = loopP t_evplist (get t_evplist 1 t) 1 t_evplist in
    let t = get evlist (i - 1) t in
    let extra_args = 
      List.map (fun (k,_) -> mkRel (fst (lookup k i evlist))) 
        (List.rev t_evplist) in
    let c = if extra_args = [] then c else app extra_args 1 c in
    loop (mkLambda (mk_evar_name n, t, c)) (i - 1) evl
  | [] -> c in
  let res = loop (get evlist 1 c0) 1 evlist in
  pp(lazy(str"res= " ++ pr_constr res));
  List.length evlist, res

(* Strip all non-essential dependencies from an abstracted term, generating *)
(* standard names for the abstracted holes.                                 *)

let nb_evar_deps = function
  | Name id ->
    let s = string_of_id id in
    if not (is_tagged evar_tag s) then 0 else
    let m = String.length evar_tag in
    (try int_of_string (String.sub s m (String.length s - 1 - m)) with _ -> 0)
  | _ -> 0

let pf_type_id gl t = id_of_string (Namegen.hdchar (pf_env gl) t)
let pf_type_of gl t = let sigma, ty = pf_type_of gl t in re_sig (sig_it gl)  sigma, ty


let pf_abs_cterm gl n c0 =
  if n <= 0 then c0 else
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match kind_of_term c with
  | App (f, a) when isRel f ->
    let j = i - destRel f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> map_constr_with_binders ((+) 1) strip i c in
  let rec strip_ndeps j i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if Vars.noccurn 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if Vars.noccurn 1 c2 then dl, Vars.lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match kind_of_term c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (pf_type_id gl t2) else mk_evar_name na' in
      mkLambda (x', t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  strip_evars 0 c0

(* Undo the evar abstractions. Also works for non-evar variables. *)

let pf_unabs_evars gl ise n c0 =
  if n = 0 then c0 else
  let evv = Array.make n mkProp in
  let nev = ref 0 in
  let env0 = pf_env gl in
  let nenv0 = env_size env0 in
  let rec unabs i c = match kind_of_term c with
  | Rel j when i - j < !nev -> evv.(i - j)
  | App (f, a0) when isRel f ->
    let a = Array.map (unabs i) a0 in
    let j = i - destRel f in
    if j >= !nev then mkApp (f, a) else
    let ev, eva = destEvar evv.(j) in
    let nd = Array.length eva - nenv0 in
    if nd = 0 then mkApp (evv.(j), a) else
    let evarg k = if k < nd then a.(nd - 1 - k) else eva.(k) in
    let c' = mkEvar (ev, Array.init (nd + nenv0) evarg) in
    let na = Array.length a - nd in
    if na = 0 then c' else mkApp (c', Array.sub a nd na)
  | _ -> map_constr_with_binders ((+) 1) unabs i c in
  let push_rel = Environ.push_rel in
  let rec mk_evar j env i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    mk_evar j (push_rel (RelDecl.LocalAssum (x, unabs i t)) env) (i + 1) c1
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c2 = destProd c1 in
    mk_evar j (push_rel (RelDecl.LocalDef (x, unabs i b, unabs i t)) env) (i + 1) c2
  | _ -> Evarutil.e_new_evar env ise (unabs i c) in
  let rec unabs_evars c =
    if !nev = n then unabs n c else match kind_of_term c with
  | Lambda (x, t, c1) when !nev < n ->
    let i = !nev in
    evv.(i) <- mk_evar (i + nb_evar_deps x) env0 i t;
    incr nev; unabs_evars c1
  | _ -> unabs !nev c in
  unabs_evars c0

(* }}} *)

let pf_merge_uc uc gl =
  re_sig (sig_it gl) (Evd.merge_universe_context (Refiner.project gl) uc)
let pf_merge_uc_of sigma gl =
  let ucst = Evd.evar_universe_context sigma in
  pf_merge_uc ucst gl


let rec constr_name c = match kind_of_term c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name c'
  | Const (cn,_) -> Name (id_of_label (con_label cn))
  | App (c', _) -> constr_name c'
  | _ -> Anonymous

let pf_mkprod gl c ?(name=constr_name c) cl =
  let gl, t = pf_type_of gl c in
  if name <> Anonymous || Vars.noccurn 1 cl then gl, mkProd (name, t, cl) else
  gl, mkProd (Name (pf_type_id gl t), t, cl)

let pf_abs_prod name gl c cl = pf_mkprod gl c ~name (Termops.subst_term c cl)

(** look up a name in the ssreflect internals module *)
let ssrdirpath = make_dirpath [id_of_string "ssreflect"]
let ssrqid name = Libnames.make_qualid ssrdirpath (id_of_string name) 
let ssrtopqid name = Libnames.make_short_qualid (id_of_string name) 
let locate_reference qid =
  Smartlocate.global_of_extended_global (Nametab.locate_extended qid)
let mkSsrRef name =
  try locate_reference (ssrqid name) with Not_found ->
  try locate_reference (ssrtopqid name) with Not_found ->
  CErrors.error "Small scale reflection library not loaded"
let mkSsrRRef name = GRef (dummy_loc, mkSsrRef name,None), None
let mkSsrConst name env sigma =
  Sigma.fresh_global env sigma (mkSsrRef name)
let pf_mkSsrConst name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma.Sigma (t, sigma, _) = mkSsrConst name env sigma in
  let sigma = Sigma.to_evar_map sigma in
  t, re_sig it sigma
let pf_fresh_global name gl =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma,t  = Evd.fresh_global env sigma name in
  t, re_sig it sigma

let mkEtaApp c n imin =
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)


let discharge_hyp (id', (id, mode)) gl =
  let cl' = Vars.subst_var id (pf_concl gl) in
  match pf_get_hyp gl id, mode with
  | NamedDecl.LocalAssum (_, t), _ | NamedDecl.LocalDef (_, _, t), "(" ->
     Proofview.V82.of_tactic (Tactics.apply_type (mkProd (Name id', t, cl')) [mkVar id]) gl
  | NamedDecl.LocalDef (_, v, t), _ ->
     Proofview.V82.of_tactic (convert_concl (mkLetIn (Name id', v, t, cl'))) gl

(* wildcard names *)
let clear_wilds wilds gl =
  Proofview.V82.of_tactic (Tactics.clear (List.filter (fun id -> List.mem id wilds) (pf_ids_of_hyps gl))) gl

let clear_with_wilds wilds clr0 gl =
  let extend_clr clr nd =
    let id = NamedDecl.get_id nd in
    if List.mem id clr || not (List.mem id wilds) then clr else
    let vars = Termops.global_vars_set_of_decl (pf_env gl) nd in
    let occurs id' = Idset.mem id' vars in
    if List.exists occurs clr then id :: clr else clr in
  Proofview.V82.of_tactic (Tactics.clear (Context.Named.fold_inside extend_clr ~init:clr0 (pf_hyps gl))) gl

let clear_wilds_and_tmp_and_delayed_ids gl =
  let _, ctx = pull_ctx gl in
  tac_ctx
   (tclTHEN
    (clear_with_wilds ctx.wild_ids ctx.delayed_clears)
    (clear_wilds (List.map fst ctx.tmp_ids @ ctx.wild_ids))) gl

let rec is_name_in_ipats name = function
  | IpatSimpl(clr,_) :: tl -> 
      List.exists (function SsrHyp(_,id) -> id = name) clr 
      || is_name_in_ipats name tl
  | IpatId id :: tl -> id = name || is_name_in_ipats name tl
  | IpatCase(`Regular l) :: tl -> is_name_in_ipats name (List.flatten l @ tl)
  | IpatCase(`Block _) :: _ -> true
  | _ :: tl -> is_name_in_ipats name tl
  | [] -> false

let view_error s gv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pr_term gv)


open Locus
(****************************** tactics ***********************************)

let rewritetac dir c =
  (* Due to the new optional arg ?tac, application shouldn't be too partial *)
  Proofview.V82.of_tactic begin
    Equality.general_rewrite (dir = L2R) AllOccurrences true false c
  end

(**********************`:********* hooks ************************************)

type name_hint = (int * Constr.types array) option ref

type simplest_newcase = ?ind:name_hint -> Constr.t -> tactic
let simplest_newcase_tac, simplest_newcase = Hook.make ()


type simplest_newcase_or_inj = ?ind:name_hint -> force_inj:bool -> Constr.t -> v82tac
let simplest_newcase_or_inj_tac, simplest_newcase_or_inj = Hook.make ()



type ipat_rewrite = ssrocc -> ssrdir -> Constr.t -> tactic
let ipat_rewrite_tac, ipat_rewrite =
  Hook.make ~default:(fun _ -> rewritetac) ()

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrterm list -> ist ->
    tac_ctx tac_a
let move_top_with_view_tac, move_top_with_view = Hook.make ()

let simpltac, simpl = Hook.make ()

let pf_abs_ssrterm ?(resolve_typeclasses=false) ist gl t =
  let sigma, ct as t = interp_term ist gl t in
  let sigma, _ as t =
    let env = pf_env gl in
    if not resolve_typeclasses then t
    else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma ct in
  let n, c, abstracted_away, ucst = pf_abs_evars gl t in
  List.fold_left Evd.remove sigma abstracted_away, pf_abs_cterm gl n c, ucst, n

let top_id = mk_internal_id "top assumption"

let ssr_n_tac seed n gl =
  let name = if n = -1 then seed else ("ssr" ^ seed ^ string_of_int n) in
  let fail msg = Feedback.msg_error (str msg); CErrors.error msg in
  let tacname = 
    try Nametab.locate_tactic (Libnames.qualid_of_ident (id_of_string name))
    with Not_found -> try Nametab.locate_tactic (ssrqid name)
    with Not_found ->
      if n = -1 then fail "The ssreflect library was not loaded"
      else fail ("The tactic "^name^" was not found") in
  let tacexpr = dummy_loc, Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
  Proofview.V82.of_tactic (Tacinterp.eval_tactic (Tacexpr.TacArg tacexpr)) gl

let donetac n gl = ssr_n_tac "done" n gl

open Constrexpr
open Util

let dC t = CastConv t
let mkCCast loc t ty = CCast (loc,t, dC ty)
let mkCType loc = CSort (loc, GType [])

let pf_interp_ty ?(resolve_typeclasses=false) ist gl ty =
   let n_binders = ref 0 in
   let ty = match ty with
   | a, (t, None) ->
     let rec force_type = function
     | GProd (l, x, k, s, t) -> incr n_binders; GProd (l, x, k, s, force_type t)
     | GLetIn (l, x, v, t) -> incr n_binders; GLetIn (l, x, v, force_type t)
     | ty -> mkRCast ty mkRType in
     a, (force_type t, None)
   | _, (_, Some ty) ->
     let rec force_type = function
     | CProdN (l, abs, t) ->
       n_binders := !n_binders +  List.length (List.flatten (List.map pi1 abs));
       CProdN (l, abs, force_type t)
     | CLetIn (l, n, v, t) -> incr n_binders; CLetIn (l, n, v, force_type t)
     | ty -> mkCCast dummy_loc ty (mkCType dummy_loc) in
     mk_term xNoFlag (force_type ty) in
   let strip_cast (sigma, t) =
     let rec aux t = match kind_of_type t with
     | CastType (t, ty) when !n_binders = 0 && isSort ty -> t
     | ProdType(n,s,t) -> decr n_binders; mkProd (n, s, aux t)
     | LetInType(n,v,ty,t) -> decr n_binders; mkLetIn (n, v, ty, aux t)
     | _ -> anomaly "pf_interp_ty: ssr Type cast deleted by typecheck" in
     sigma, aux t in
   let sigma, cty as ty = strip_cast (interp_term ist gl ty) in
   let ty =
     let env = pf_env gl in
     if not resolve_typeclasses then ty
     else
       let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
       sigma, Evarutil.nf_evar sigma cty in
   let n, c, _, ucst = pf_abs_evars gl ty in
   let lam_c = pf_abs_cterm gl n c in
   let ctx, c = decompose_lam_n n lam_c in
   n, compose_prod ctx c, lam_c, ucst
;;

(* TASSI: given (c : ty), generates (c ??? : ty[???/...]) with m evars *)
open Sigma
exception NotEnoughProducts
let saturate ?(beta=false) ?(bi_types=false) env sigma c ?(ty=Retyping.get_type_of env sigma c) m 
=
  let rec loop ty args sigma n = 
  if n = 0 then 
    let args = List.rev args in
     (if beta then Reductionops.whd_beta sigma else fun x -> x)
      (mkApp (c, Array.of_list (List.map snd args))), ty, args, sigma 
  else match kind_of_type ty with
  | ProdType (_, src, tgt) ->
      let sigma = create_evar_defs sigma in
      let sigma = Sigma.Unsafe.of_evar_map sigma in
      let Sigma (x, sigma, _) =
        Evarutil.new_evar env sigma
          (if bi_types then Reductionops.nf_betaiota (Sigma.to_evar_map sigma) src else src) in
      let sigma = Sigma.to_evar_map sigma in
      loop (Vars.subst1 x tgt) ((m - n,x) :: args) sigma (n-1)
  | CastType (t, _) -> loop t args sigma n 
  | LetInType (_, v, _, t) -> loop (Vars.subst1 v t) args sigma n
  | SortType _ -> assert false
  | AtomicType _ ->
      let ty =  (* FIXME *)
        (Reductionops.whd_all env sigma) ty in
      match kind_of_type ty with
      | ProdType _ -> loop ty args sigma n
      | _ -> raise NotEnoughProducts
  in
   loop ty [] sigma m

let pf_saturate ?beta ?bi_types gl c ?ty m = 
  let env, sigma, si = pf_env gl, project gl, sig_it gl in
  let t, ty, args, sigma = saturate ?beta ?bi_types env sigma c ?ty m in
  t, ty, args, re_sig si sigma 

let pf_nf_evar gl e = Reductionops.nf_evar (project gl) e


let pf_partial_solution gl t evl =
  let sigma, g = project gl, sig_it gl in
  let sigma = Goal.V82.partial_solution sigma g t in
  re_sig (List.map (fun x -> (fst (destEvar x))) evl) sigma

let dependent_apply_error =
  try CErrors.error "Could not fill dependent hole in \"apply\"" with err -> err

(* TASSI: Sometimes Coq's apply fails. According to my experience it may be
 * related to goals that are products and with beta redexes. In that case it
 * guesses the wrong number of implicit arguments for your lemma. What follows
 * is just like apply, but with a user-provided number n of implicits.
 *
 * Refine.refine function that handles type classes and evars but fails to
 * handle "dependently typed higher order evars". 
 *
 * Refiner.refiner that does not handle metas with a non ground type but works
 * with dependently typed higher order metas. *)
let applyn ~with_evars ?beta ?(with_shelve=false) n t gl =
  if with_evars then
    let refine gl =
      let t, ty, args, gl = pf_saturate ?beta ~bi_types:true gl t n in
(*       pp(lazy(str"sigma@saturate=" ++ pr_evar_map None (project gl))); *)
      let gl = pf_unify_HO gl ty (pf_concl gl) in
      let gs = CList.map_filter (fun (_, e) ->
        if isEvar (pf_nf_evar gl e) then Some e else None)
        args in
      pf_partial_solution gl t gs
    in
    Proofview.(V82.of_tactic
      (tclTHEN (V82.tactic refine)
        (if with_shelve then shelve_unifiable else tclUNIT ()))) gl
  else
    let t, gl = if n = 0 then t, gl else
      let sigma, si = project gl, sig_it gl in
      let rec loop sigma bo args = function (* saturate with metas *)
        | 0 -> mkApp (t, Array.of_list (List.rev args)), re_sig si sigma 
        | n -> match kind_of_term bo with
          | Lambda (_, ty, bo) -> 
              if not (Vars.closed0 ty) then raise dependent_apply_error;
              let m = Evarutil.new_meta () in
              loop (meta_declare m ty sigma) bo ((mkMeta m)::args) (n-1)
          | _ -> assert false
      in loop sigma t [] n in
    pp(lazy(str"Refiner.refiner " ++ Printer.pr_constr t));
    Refiner.refiner (Proof_type.Refine t) gl

let refine_with ?(first_goes_last=false) ?beta ?(with_evars=true) oc gl =
  let rec mkRels = function 1 -> [] | n -> mkRel n :: mkRels (n-1) in
  let uct = Evd.evar_universe_context (fst oc) in
  let n, oc = pf_abs_evars_pirrel gl oc in
  let gl = pf_unsafe_merge_uc uct gl in
  let oc = if not first_goes_last || n <= 1 then oc else
    let l, c = decompose_lam oc in
    if not (List.for_all_i (fun i (_,t) -> Vars.closedn ~-i t) (1-n) l) then oc else
    compose_lam (let xs,y = List.chop (n-1) l in y @ xs) 
      (mkApp (compose_lam l c, Array.of_list (mkRel 1 :: mkRels n)))
  in
  pp(lazy(str"after: " ++ Printer.pr_constr oc));
  try applyn ~with_evars ~with_shelve:true ?beta n oc gl
  with e when CErrors.noncritical e -> raise dependent_apply_error

type with_dgens = (Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list list *
Ssrast.ssrclear ->
((Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list ->
 Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern ->
 Tacinterp.interp_sign -> Proof_type.tactic) ->
Tacinterp.interp_sign -> Proof_type.tactic
let with_dgens, with_dgens_hook = Hook.make ()


(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.unfreeze frozen_lexer ;;

(* vim: set filetype=ocaml foldmethod=marker: *)
