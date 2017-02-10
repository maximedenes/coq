open Ipat
open Pltac
open Stdarg
open Genarg
open Extraargs
open Pcoq
open Pcoq.Prim
open Pcoq.Constr

DECLARE PLUGIN "quill_plugin"

let () = Mltop.add_known_plugin (fun () ->
  if Flags.is_verbose () && not !Flags.batch_mode then
     Feedback.msg_info (Pp.str "Quill mode loaded.")
  )
  "quill_plugin"

(** Shouldn't this move to Coq?
(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let gen_pr _ _ _ = pr in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

let wit_ipat = add_genarg "ipat" pr_ipat
 *)

ARGUMENT EXTEND ipat
  PRINTED BY pr_ipat
(*  INTERPRETED BY interp_ipat
  GLOBALIZED BY glob_ipat *)
  | [ "/" tactic_expr(t) ] -> [ IPatTactic(t,None,[]) ]
END

ARGUMENT EXTEND iorpat TYPED AS ipat list list PRINTED BY pr_iorpat
  | [ ipat_list(ipats) "|" iorpat(iorpat) ] -> [ ipats :: iorpat ]
  | [ ipat_list(ipats) ] -> [ [ipats] ]
END

ARGUMENT EXTEND ipats_mod PRINTED BY pr_ipats_mod
  | [ "=" ] -> [ Equal ]
  | [ "&" ] -> [ Ampersand ]
END

ARGUMENT EXTEND name_mod PRINTED BY pr_name_mod
  | [ "^" ] -> [ Hat ]
  | [ "^~" ] -> [ HatTilde ]
  | [ "#" ] -> [ Sharp ]
END

GEXTEND Gram
  GLOBAL: ipat;
  ipat: [ [   "("; m = OPT ipats_mod; il = iorpat; ")" -> IPatDispatch(m,il) 
            | "["; m = OPT ipats_mod; il = iorpat; "]" -> IPatCase(m,il)
            |      m = OPT name_mod;  id = ident       -> IPatName(m,id)
        ] ];
END

(* Low level API exported to ltac to let the user hijack it *)

(* FIXME: patch metasyntax.... *)
(*
TACTIC EXTEND intro_id
| [ "intro_id" ident(id) ] -> [ intro_id_slow id ]
END
*)

(* High level grammar *)

TACTIC EXTEND pipeau
  | [ "quill" ipat_list(pl) ] -> [ ipat_tac pl ]
END

(* vim: set ft=ocaml: *)
