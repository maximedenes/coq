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

