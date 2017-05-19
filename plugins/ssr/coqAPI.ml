open CErrors
open Util
open Evarutil
open Reductionops
open Constr
open Context
open Vars
open Evarsolve
open EConstr
open Ltac_plugin

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

let clos_whd_flags flgs env sigma t =
  try
    let evars ev = safe_evar_value sigma ev in
    CClosure.whd_val
      (CClosure.create_clos_infos ~evars flgs env)
      (CClosure.inject t)
  with e when is_anomaly e -> error "Tried to normalize ill-typed term"

let rec decompose_assum env sigma t =
  let t as goal = whd_allnolet env sigma t in
  match kind sigma t with
  | Prod(name,ty,t) -> Rel.Declaration.LocalAssum(name,ty), t
  | LetIn(name,ty,t1,t2) -> Rel.Declaration.LocalDef(name, ty, t1), t2
  | App(hd,args) when isLetIn sigma hd -> (* hack *)
      let _,v,_,b = destLetIn sigma hd in
      decompose_assum env sigma (mkApp (Vars.subst1 v b, args))
  | _ -> user_err Pp.(str "No assumption in " ++ Printer.pr_econstr_env env sigma goal)

let tclNIY what = anomaly Pp.(str "NIY: " ++ str what)

module Option = struct
  include Option
  let assert_get o msg =
    match o with
    | None -> CErrors.anomaly msg
    | Some x -> x
end

let intern_constr_expr { Genintern.genv; ltacvars = vars } ce =
  let ltacvars = { (* TODO: ask PMP is ltac_boud = [] is OK *)
    Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv ce

