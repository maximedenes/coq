open Names

open Ssrmatching_plugin.Ssrmatching
open Tacmach

open Ssrcommon

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)
(** Defined identifier *)


let settac id c = Tactics.letin_tac None (Name id) c None
let posetac id cl = Proofview.V82.of_tactic (settac id cl Locusops.nowhere)

let ssrposetac ist (id, (_, t)) gl =
  let sigma, t, ucst, _ = pf_abs_ssrterm ist gl t in
  posetac id t (pf_merge_uc ucst gl)

open Pp
open Term

let ssrsettac ist id ((_, (pat, pty)), (_, occ)) gl =
  let pat = interp_cpattern ist gl pat (Option.map snd pty) in
  let cl, sigma, env = pf_concl gl, project gl, pf_env gl in
  let (c, ucst), cl = 
    try fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with NoMatch -> redex_of_pattern ~resolve_typeclasses:true env pat, cl in
  if Termops.occur_existential c then errorstrm(str"The pattern"++spc()++
    pr_constr_pat c++spc()++str"did not match and has holes."++spc()++
    str"Did you mean pose?") else
  let c, (gl, cty) =  match kind_of_term c with
  | Cast(t, DEFAULTcast, ty) -> t, (gl, ty)
  | _ -> c, pf_type_of gl c in
  let cl' = mkLetIn (Name id, c, cty, cl) in
  let gl = pf_merge_uc ucst gl in
  Tacticals.tclTHEN (Proofview.V82.of_tactic (convert_concl cl')) (Ssripats.introid id) gl

open Util

let is_Evar_or_CastedMeta x =
  isEvar_or_Meta x ||
  (isCast x && isEvar_or_Meta (pi1 (destCast x)))

let occur_existential_or_casted_meta c =
  let rec occrec c = match kind_of_term c with
    | Evar _ -> raise Not_found
    | Cast (m,_,_) when isMeta m -> raise Not_found
    | _ -> iter_constr occrec c
  in try occrec c; false with Not_found -> true

open Printer

let examine_abstract id gl =
  let gl, tid = pf_type_of gl id in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  if not (isApp tid) || not (Term.eq_constr (fst(destApp tid)) abstract) then
    errorstrm(strbrk"not an abstract constant: "++pr_constr id);
  let _, args_id = destApp tid in
  if Array.length args_id <> 3 then
    errorstrm(strbrk"not a proper abstract constant: "++pr_constr id);
  if not (is_Evar_or_CastedMeta args_id.(2)) then
    errorstrm(strbrk"abstract constant "++pr_constr id++str" already used");
  tid, args_id

let pf_find_abstract_proof check_lock gl abstract_n = 
  let fire gl t = Reductionops.nf_evar (project gl) t in
  let abstract, gl = pf_mkSsrConst "abstract" gl in
  let l = Evd.fold_undefined (fun e ei l ->
    match kind_of_term ei.Evd.evar_concl with
    | App(hd, [|ty; n; lock|])
      when (not check_lock || 
                 (occur_existential_or_casted_meta (fire gl ty) &&
                  is_Evar_or_CastedMeta (fire gl lock))) &&
      Term.eq_constr hd abstract && Term.eq_constr n abstract_n -> e::l
    | _ -> l) (project gl) [] in
  match l with
  | [e] -> e
  | _ -> errorstrm(strbrk"abstract constant "++pr_constr abstract_n++
           strbrk" not found in the evar map exactly once. "++
           strbrk"Did you tamper with it?")

let reduct_in_concl t = Tactics.reduct_in_concl (t, DEFAULTcast)
let unfold cl =
  let module R = Reductionops in let module F = CClosure.RedFlags in
  reduct_in_concl (R.clos_norm_flags (F.mkflags
    (List.map (fun c -> F.fCONST (fst (destConst c))) cl @
       [F.fBETA; F.fMATCH; F.fFIX; F.fCOFIX])))

let apply_type x xs = Proofview.V82.of_tactic (Tactics.apply_type x xs)
let havegentac ist t gl =
  let sigma, c, ucst, _ = pf_abs_ssrterm ist gl t in
  let gl = pf_merge_uc ucst gl in
  let gl, cty = pf_type_of gl c in
  apply_type (mkArrow cty (pf_concl gl)) [c] gl

open Ssrast
open Ssripats
open Ssrparser

let cleartac clr = check_hyps_uniq [] clr; Proofview.V82.of_tactic (Tactics.clear (hyps_ids clr))

let pf_e_type_of gl t =
  let sigma, env, it = project gl, pf_env gl, sig_it gl in
  let sigma, ty = Typing.type_of env sigma t in
  re_sig it sigma, ty

let eval_tclarg ist tac = ssrevaltac ist tac

let hinttac ist is_by (is_or, atacs) =
  let dtac = if is_by then donetac ~-1 else Tacticals.tclIDTAC in
  let mktac = function
  | Some atac -> Tacticals.tclTHEN (ssrevaltac ist atac) dtac
  | _ -> dtac in
  match List.map mktac atacs with
  | [] -> if is_or then dtac else Tacticals.tclIDTAC
  | [tac] -> tac
  | tacs -> Tacticals.tclFIRST tacs


let ssrhaveNOtcresolution = Summary.ref ~name:"SSR:havenotcresolution" false

let inHaveTCResolution = Libobject.declare_object {
  (Libobject.default_object "SSRHAVETCRESOLUTION") with
  Libobject.cache_function = (fun (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.load_function = (fun _ (_,v) -> ssrhaveNOtcresolution := v);
  Libobject.classify_function = (fun v -> Libobject.Keep v);
}
let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = false;
      Goptions.optname  = "have type classes";
      Goptions.optkey   = ["SsrHave";"NoTCResolution"];
      Goptions.optread  = (fun _ -> !ssrhaveNOtcresolution);
      Goptions.optdepr  = false;
      Goptions.optwrite = (fun b ->
        Lib.add_anonymous_leaf (inHaveTCResolution b)) }


open Constrexpr 
open Glob_term 
open Misctypes
open Decl_kinds

let dC t = CastConv t
let mkCHole loc = CHole (loc, None, IntroAnonymous, None)
let mkCCast loc t ty = CCast (loc,t, dC ty)
let combineCG t1 t2 f g = match t1, t2 with
 | (x, (t1, None)), (_, (t2, None)) -> x, (g t1 t2, None)
 | (x, (_, Some t1)), (_, (_, Some t2)) -> x, (mkRHole, Some (f t1 t2))
 | _, (_, (_, None)) -> anomaly "have: mixed C-G constr"
 | _ -> anomaly "have: mixed G-C constr"
let mkCArrow loc ty t =
   CProdN (loc, [[dummy_loc,Anonymous], Default Explicit, ty], t)

let basecuttac name c gl =
  let hd, gl = pf_mkSsrConst name gl in
  let t = mkApp (hd, [|c|]) in
  let gl, _ = pf_e_type_of gl t in
  Proofview.V82.of_tactic (Tactics.apply t) gl

let havetac ist
  (transp,((((clr, pats), binders), simpl), (((fk, _), t), hint)))
  suff namefst gl 
=
 let concl = pf_concl gl in
 let skols, pats =
   List.partition (function IpatNewHidden _ -> true | _ -> false) pats in
 let itac_mkabs = introstac ~ist skols in
 let itac_c = introstac ~ist (IpatSimpl(clr,Nop) :: pats) in
 let itac, id, clr = introstac ~ist pats, Tacticals.tclIDTAC, cleartac clr in
 let binderstac n =
   let rec aux = function 0 -> [] | n -> IpatAnon :: aux (n-1) in
   Tacticals.tclTHEN (if binders <> [] then introstac ~ist (aux n) else Tacticals.tclIDTAC)
     (introstac ~ist binders) in
 let simpltac = introstac ~ist simpl in
 let fixtc =
   not !ssrhaveNOtcresolution &&
   match fk with FwdHint(_,true) -> false | _ -> true in
 let hint = hinttac ist true hint in
 let cuttac t gl =
   if transp then
     let have_let, gl = pf_mkSsrConst "ssr_have_let" gl in
     let step = mkApp (have_let, [|concl;t|]) in
     let gl, _ = pf_e_type_of gl step in
     applyn ~with_evars:true ~with_shelve:false 2 step gl
   else basecuttac "ssr_have" t gl in
 (* Introduce now abstract constants, so that everything sees them *)
 let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
 let unlock_abs (idty,args_id) gl =
    let gl, _ = pf_e_type_of gl idty in
    pf_unify_HO gl args_id.(2) abstract_key in
 Tacticals.tclTHENFIRST itac_mkabs (fun gl ->
  let mkt t = mk_term xNoFlag t in
  let mkl t = (xNoFlag, (t, None)) in
  let interp gl rtc t = pf_abs_ssrterm ~resolve_typeclasses:rtc ist gl t in
  let interp_ty gl rtc t =
    let a,b,_,u = pf_interp_ty ~resolve_typeclasses:rtc ist gl t in a,b,u in
  let ct, cty, hole, loc = match t with
    | _, (_, Some (CCast (loc, ct, CastConv cty))) ->
      mkt ct, mkt cty, mkt (mkCHole dummy_loc), loc
    | _, (_, Some ct) ->
      mkt ct, mkt (mkCHole dummy_loc), mkt (mkCHole dummy_loc), dummy_loc
    | _, (GCast (loc, ct, CastConv cty), None) ->
      mkl ct, mkl cty, mkl mkRHole, loc
    | _, (t, None) -> mkl t, mkl mkRHole, mkl mkRHole, dummy_loc in
  let gl, cut, sol, itac1, itac2 =
   match fk, namefst, suff with
   | FwdHave, true, true ->
     errorstrm (str"Suff have does not accept a proof term")
   | FwdHave, false, true ->
     let cty = combineCG cty hole (mkCArrow loc) mkRArrow in
     let _,t,uc,_ = interp gl false (combineCG ct cty (mkCCast loc) mkRCast) in
     let gl = pf_merge_uc uc gl in
     let gl, ty = pf_type_of gl t in
     let ctx, _ = decompose_prod_n 1 ty in
     let assert_is_conv gl =
       try Proofview.V82.of_tactic (convert_concl (compose_prod ctx concl)) gl
       with _ -> errorstrm (str "Given proof term is not of type " ++
         pr_constr (mkArrow (mkVar (id_of_string "_")) concl)) in
     gl, ty, Tacticals.tclTHEN assert_is_conv (Proofview.V82.of_tactic (Tactics.apply t)), id, itac_c
   | FwdHave, false, false ->
     let skols = List.flatten (List.map (function
       | IpatNewHidden ids -> ids
       | _ -> assert false) skols) in
     let skols_args =
       List.map (fun id -> examine_abstract (mkVar id) gl) skols in
     let gl = List.fold_right unlock_abs skols_args gl in
     let sigma, t, uc, n_evars =
       interp gl false (combineCG ct cty (mkCCast loc) mkRCast) in
     if skols <> [] && n_evars <> 0 then
       CErrors.error ("Automatic generalization of unresolved implicit "^
                     "arguments together with abstract variables is "^
                     "not supported");
     let gl = re_sig (sig_it gl) (Evd.merge_universe_context sigma uc) in
     let gs =
       List.map (fun (_,a) ->
         pf_find_abstract_proof false gl a.(1)) skols_args in
     let tacopen_skols gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff (gs @ [g]) in
     let gl, ty = pf_e_type_of gl t in
     gl, ty, Proofview.V82.of_tactic (Tactics.apply t), id,
       Tacticals.tclTHEN (Tacticals.tclTHEN itac_c simpltac)
         (Tacticals.tclTHEN tacopen_skols (fun gl ->
            let abstract, gl = pf_mkSsrConst "abstract" gl in
            Proofview.V82.of_tactic (unfold [abstract; abstract_key]) gl))
   | _,true,true  ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, mkArrow ty concl, hint, itac, clr
   | _,false,true ->
     let _, ty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, mkArrow ty concl, hint, id, itac_c
   | _, false, false -> 
     let n, cty, uc = interp_ty gl fixtc cty in let gl = pf_merge_uc uc gl in
     gl, cty, Tacticals.tclTHEN (binderstac n) hint, id, Tacticals.tclTHEN itac_c simpltac
   | _, true, false -> assert false in
  Tacticals.tclTHENS (cuttac cut) [ Tacticals.tclTHEN sol itac1; itac2 ] gl)
 gl
;;

(* to extend the abstract value one needs:
  Utility lemma to partially instantiate an abstract constant type.
  Lemma use_abstract T n l (x : abstract T n l) : T.
  Proof. by case: l x. Qed.
*)
let ssrabstract ist gens (*last*) gl =
  let main _ (_,cid) ist gl =
(*
    let proj1, proj2, prod =
      let pdata = build_prod () in
      pdata.Coqlib.proj1, pdata.Coqlib.proj2, pdata.Coqlib.typ in
*)
    let concl, env = pf_concl gl, pf_env gl in
    let fire gl t = Reductionops.nf_evar (project gl) t in
    let abstract, gl = pf_mkSsrConst "abstract" gl in
    let abstract_key, gl = pf_mkSsrConst "abstract_key" gl in
    let cid_interpreted = interp_cpattern ist gl cid None in
    let id = mkVar (Option.get (id_of_pattern cid_interpreted)) in
    let idty, args_id = examine_abstract id gl in
    let abstract_n = args_id.(1) in
    let abstract_proof = pf_find_abstract_proof true gl abstract_n in 
    let gl, proof =
      let pf_unify_HO gl a b =
        try pf_unify_HO gl a b
        with _ -> errorstrm(strbrk"The abstract variable "++pr_constr id++
          strbrk" cannot abstract this goal.  Did you generalize it?") in
      let rec find_hole p t =
        match kind_of_term t with
        | Evar _ (*when last*) -> pf_unify_HO gl concl t, p
        | Meta _ (*when last*) -> pf_unify_HO gl concl t, p
        | Cast(m,_,_) when isEvar_or_Meta m (*when last*) -> pf_unify_HO gl concl t, p
(*
        | Evar _ ->
            let sigma, it = project gl, sig_it gl in
            let sigma, ty = Evarutil.new_type_evar sigma env in
            let gl = re_sig it sigma in
            let p = mkApp (proj2,[|ty;concl;p|]) in
            let concl = mkApp(prod,[|ty; concl|]) in
            pf_unify_HO gl concl t, p
        | App(hd, [|left; right|]) when Term.eq_constr hd prod ->
            find_hole (mkApp (proj1,[|left;right;p|])) left
*)
        | _ -> errorstrm(strbrk"abstract constant "++pr_constr abstract_n++
               strbrk" has an unexpected shape. Did you tamper with it?")
      in
        find_hole
          ((*if last then*) id
          (*else mkApp(mkSsrConst "use_abstract",Array.append args_id [|id|])*))
          (fire gl args_id.(0)) in
    let gl = (*if last then*) pf_unify_HO gl abstract_key args_id.(2) (*else gl*) in
    let gl, _ = pf_e_type_of gl idty in
    let proof = fire gl proof in
(*     if last then *)
      let tacopen gl =
        let stuff, g = Refiner.unpackage gl in
        Refiner.repackage stuff [ g; abstract_proof ] in
      Tacticals.tclTHENS tacopen [Tacticals.tclSOLVE [Proofview.V82.of_tactic (Tactics.apply proof)]; Proofview.V82.of_tactic (unfold[abstract;abstract_key])] gl
(* else apply proof gl *)
  in
  let introback ist (gens, _) =
    introstac ~ist
      (List.map (fun (_,cp) -> match id_of_pattern (interp_cpattern ist gl cp None) with
        | None -> IpatAnon
        | Some id -> IpatId id)
        (List.tl (List.hd gens))) in
  Tacticals.tclTHEN (Hook.get with_dgens gens main ist) (introback ist gens) gl

