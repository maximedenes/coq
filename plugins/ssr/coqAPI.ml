open CErrors
open Util
open Evarutil
open Reductionops
open Constr
open Context
open Vars
open Evarsolve

let clos_whd_flags flgs env sigma t =
  try
    let evars ev = safe_evar_value sigma ev in
    CClosure.whd_val
      (CClosure.create_clos_infos ~evars flgs env)
      (CClosure.inject t)
  with e when is_anomaly e -> error "Tried to normalize ill-typed term"

(* Is it right to use global env here (maybe unused)? Check on Coq's side. *)
let whd_beta = clos_whd_flags CClosure.beta (Global.env ())
let whd_betaiota = clos_whd_flags CClosure.betaiota (Global.env ())
let whd_betaiotazeta = clos_whd_flags CClosure.betaiotazeta (Global.env ())
let whd_allnolet env sigma = clos_whd_flags CClosure.allnolet env sigma
let whd_all env sigma = clos_whd_flags CClosure.all env sigma

let rec decompose_assum env sigma t =
  let t as goal = whd_allnolet env sigma t in
  match kind_of_term_upto sigma t with
  | Prod(name,ty,t) -> Rel.Declaration.LocalAssum(name,ty), t
  | LetIn(name,ty,t1,t2) -> Rel.Declaration.LocalDef(name, ty, t1), t2
  | App(hd,args) when Term.isLetIn hd -> (* hack *)
      let _,v,_,b = Term.destLetIn hd in
      decompose_assum env sigma (mkApp (Vars.subst1 v b, args))
  | _ -> user_err Pp.(str "No assumption in " ++ Printer.pr_constr goal)

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

