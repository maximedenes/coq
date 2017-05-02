open Ltac_plugin

open Ssripat
open Pltac
open Stdarg
open Genarg
open Extraargs
open Tacarg
open Tacexpr
open Pcoq
open Pcoq.Prim
open Pcoq.Constr

(* DECLARE PLUGIN should take a variable or a string. *)
DECLARE PLUGIN "ssreflect_plugin"

(* This function should be an optional argument of DECLARE PLUGIN *)
let () = Mltop.add_known_plugin (fun () ->
  if Flags.is_verbose () && not !Flags.batch_mode then
     Feedback.msg_info (Pp.str "SSR2 mode loaded.")
  )
  "ssreflect_plugin"

(* Lookahead *)
let input_term_annotation strm =
  match Stream.npeek 2 strm with
  | Tok.KEYWORD "(" :: Tok.KEYWORD "(" :: _ -> `DoubleParens
  | Tok.KEYWORD "(" :: _ -> `Parens
  | Tok.KEYWORD "@" :: _ -> `At
  | _ -> `None
let term_annotation =
  Gram.Entry.of_parser "term_annotation" input_term_annotation

ARGUMENT EXTEND term
     PRINTED BY pr_term
     INTERPRETED BY interp_term
     GLOBALIZED BY glob_term
     SUBSTITUTED BY subst_term
     RAW_PRINTED BY pr_term
     GLOB_PRINTED BY pr_term
  | [ term_annotation(a) constr(c) ] -> [ mk_term a c ]
END

let pr_ipat_view a b c = Pp.prlist_with_sep (fun _ -> Pp.str"/") (pr_term a b c)

ARGUMENT EXTEND ipat_view
  TYPED AS term list
  PRINTED BY pr_ipat_view
  | [ ne_term_list_sep(ts,"/") ] -> [ ts ]
END

ARGUMENT EXTEND ipat
  PRINTED BY pr_ipat
  INTERPRETED BY interp_ipat
  GLOBALIZED BY glob_ipat
  SUBSTITUTED BY subst_ipat
  RAW_PRINTED BY pr_ipat
  GLOB_PRINTED BY pr_ipat
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
(*
ARGUMENT EXTEND ipat TYPED AS foo list
END
 *)
(* Here we'd need to define mutually recursive non-terminals (iorpat, ipat) with
   ARGUMENT EXTEND *)
GEXTEND Gram
  GLOBAL: ipat;
  ipat: [ [   "("; m = OPT ipats_mod; il = iorpat; ")" -> IPatDispatch(m,il) 
            | "["; m = OPT ipats_mod; il = iorpat; "]" -> IPatCase(m,il)
            | "/"; v = ipat_view                       -> IPatView(v)
            |      m = OPT name_mod;  id = ident    -> IPatName(m,id)
            | ">" -> IPatAnon(Dependent)
            | "*" -> IPatAnon(All)
            | "?" -> IPatAnon(One)
            | "+" -> IPatAnon(Temporary)
            | "_" -> IPatDrop
            | "-" -> IPatNoop
            | "->" -> IPatRewrite (Ssrast.L2R)
            | "<-" -> IPatRewrite (Ssrast.R2L)
            | "//" -> IPatSimpl (Cut (-1))
            | "/=" -> IPatSimpl (Simpl (-1))
            | "//=" -> IPatSimpl (SimplCut ((-1),(-1)))
            | "{"; il = LIST1 ident ; "}" -> IPatClear(il)
        ] ];
END

(* Low level API exported to ltac to let the user hijack it *)

EXPORT TACTIC [ "intro_id" ident(id) ] -> [ intro_id id ]
EXPORT TACTIC [ "intro_id_prepend" ident(id) ] -> [ tac_intro_seed ipat_tac `Prepend id ]
EXPORT TACTIC [ "intro_id_append" ident(id) ] -> [ tac_intro_seed ipat_tac `Append id ]
EXPORT TACTIC [ "intro_anon" ] -> [ intro_anon ]
EXPORT TACTIC [ "intro_anon_all" ] -> [ intro_anon_all ]
EXPORT TACTIC [ "intro_anon_deps" ] -> [ intro_anon_deps ]
EXPORT TACTIC [ "intro_anon_temp" ] -> [ intro_anon_temp ]
EXPORT TACTIC [ "intro_drop" ] -> [ intro_drop ]
EXPORT TACTIC [ "intro_finalize" ] -> [ intro_finalize ]
EXPORT TACTIC [ "intro_clear" ident_list(ids) ] -> [ intro_clear ids ]

(* High level grammar *)

TACTIC EXTEND pipeau
  | [ "=>" ipat_list(pl) ] -> [ ipat_tac pl ]
END

TACTIC EXTEND ssrtclintros AT LEVEL 1
| [ tactic1(tac) "=>" ipat_list(intros) ] ->
    [ let tac = Tacinterp.tactic_of_value ist tac in
    Proofview.tclTHEN tac (ipat_tac intros) ]
END


let pr_constr_expr _ _ _ = Ppconstr.pr_constr_expr
let pr_glob_constr _ _ _ (x,_) = Printer.pr_glob_constr x
let intern_gconstr x = Constrintern.intern_constr (Global.env ()) x
let pr_gconstr f _ _ = f

open Stdarg

ARGUMENT EXTEND gconstr
  PRINTED BY pr_gconstr
  RAW_TYPED AS constr
  RAW_PRINTED BY pr_constr_expr
  GLOB_TYPED AS constr
  GLOB_PRINTED BY pr_glob_constr
      | [ constr(c) ] -> [ c ]
END

VERNAC COMMAND EXTEND ViewAdaptor CLASSIFIED AS SIDEFF
|  [  "ViewAdaptor" "Backward"    gconstr(t) ] -> [ let t = intern_gconstr t in AdaptorDb.(declare Backward t) ]
|  [  "ViewAdaptor" "Forward"     gconstr(t) ] -> [ let t = intern_gconstr t in AdaptorDb.(declare Forward t) ]
|  [  "ViewAdaptor" "Equivalence" gconstr(t) ] -> [ let t = intern_gconstr t in AdaptorDb.(declare Equivalence t) ]
END

(* vim: set ft=ocaml: *)
