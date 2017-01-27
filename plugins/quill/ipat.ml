open Names
open Constrexpr
open Tacexpr
open Proofview

(* Only [One] forces an introduction, possibly reducing the goal. *)
type anon_iter =
  | One
  | Dependent
  | UntilMark
  | All

type concat_kind = Prefix | Suffix

type direction = LeftToRight | RightToLeft

type selector = int

type state = { to_clear: Id.t list;
               name_seed: Id.t option }

type ipat =
  | IPatNoop
  | IPatName of Id.t
  | IPatAnon of anon_iter
  | IPatDrop
  | IPatClearMark
  | IPatConcat of concat_kind
  | IPatDispatch of ipat list list
  | IPatCase of ipat list list
  | IPatTactic of (raw_tactic_expr * selector option * unit list)
(*  | IPatRewrite of occurrence option * rewrite_pattern * direction *)
  | IPatView of constr_expr list
  | IPatClear of Id.t

let pr_iorpat _ _ _ ipat = Pp.mt ()
let pr_ipat _ _ _ ipat = Pp.mt ()

let interp_ipat ist gl ipat = Evd.empty, (ist, ipat)

let glob_ipat _ ipat = ()

let rec ipat_tac1 ipat : state tactic =
  match ipat with
  | IPatTactic(t,sel,args) -> Tacinterp.interp t
  | IPatDispatch(ipats) ->
     tclDISPATCH (List.map ipat_tac ipats)
  | _ -> assert false

and ipat_tac pl states : unit tactic =
  match pl with
  | [] -> tclUNIT ()
  | pat :: pl -> tclTHEN (ipat_tac1 pat) (ipat_tac pl)
