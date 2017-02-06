open CErrors
open Util
open Evarutil
open Reductionops
open Constr
open Context

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

let decompose_assum env sigma t =
  let t = whd_allnolet env sigma t in
  match kind_of_term_upto sigma t with
  | Prod(name,ty,t) -> Rel.Declaration.LocalAssum(name,ty), t
  | LetIn(name,ty,t1,t2) -> Rel.Declaration.LocalDef(name, ty, t1), t2
  | _ -> user_err (Pp.str "No assumption")
