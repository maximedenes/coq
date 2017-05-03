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

DECLARE PLUGIN "ssreflect_plugin"
(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;



let tacltop = (5,Ppextend.E)

let pr_ssrtacarg _ _ prt = prt tacltop
ARGUMENT EXTEND ssrtacarg TYPED AS tactic PRINTED BY pr_ssrtacarg
| [ "YouShouldNotTypeThis" ] -> [ CErrors.anomaly (Pp.str "Grammar placeholder match") ]
END
GEXTEND Gram
  GLOBAL: ssrtacarg;
  ssrtacarg: [[ tac = tactic_expr LEVEL "5" -> tac ]];
END

(* Lexically closed tactic for tacticals. *)
let pr_ssrtclarg _ _ prt tac = prt tacltop tac
ARGUMENT EXTEND ssrtclarg TYPED AS ssrtacarg
    PRINTED BY pr_ssrtclarg
| [ ssrtacarg(tac) ] -> [ tac ]
END

open Genarg
type ist = Tacinterp.interp_sign
type gist = Tacintern.glob_sign

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

let of_ftactic ftac gl =
  let r = ref None in
  let tac = Ftactic.run ftac (fun ans -> r := Some ans; Proofview.tclUNIT ()) in
  let tac = Proofview.V82.of_tactic tac in
  let { sigma = sigma } = tac gl in
  let ans = match !r with
  | None -> assert false (** If the tactic failed we should not reach this point *)
  | Some ans -> ans
  in
  (sigma, ans)

let interp_wit wit ist gl x = 
  let globarg = in_gen (glbwit wit) x in
  let arg = Tacinterp.interp_genarg ist globarg in
  let (sigma, arg) = of_ftactic arg gl in
  sigma, Tacinterp.Value.cast (topwit wit) arg
(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_any_id syms strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT _ -> ()
  | _ -> raise Stream.Failure

let accept_before_syms_or_ids syms ids strm =
  match Util.stream_nth 1 strm with
  | Tok.KEYWORD sym when List.mem sym syms -> ()
  | Tok.IDENT id when List.mem id ids -> ()
  | _ -> raise Stream.Failure

open Ssrast
let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep
let dummy_loc = Loc.ghost
let errorstrm x = CErrors.user_err ~hdr:"ssreflect" x
let loc_error loc msg = CErrors.user_err ~loc ~hdr:"ssreflect" msg
let anomaly s = CErrors.anomaly (str s)


(**************************** ssrhyp **************************************) 

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impractical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

let hyp_id (SsrHyp (_, id)) = id
let pr_hyp (SsrHyp (_, id)) = pr_id id
let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep = add_genarg "ssrhyprep" pr_hyp

let hyp_err loc msg id =
  CErrors.user_err ~loc  ~hdr:"ssrhyp" (str msg ++ pr_id id)

let not_section_id id = not (Termops.is_section_variable id)

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_var) (loc, id)) in
  if not_section_id id then hyp else
  hyp_err loc "Can't clear section hypothesis " id

let interp_hyp ist gl (SsrHyp (loc, id)) =
  let s, id' = interp_wit wit_var ist gl (loc, id) in
  if not_section_id id' then s, SsrHyp (loc, id') else
  hyp_err loc "Can't clear section hypothesis " id'

open Pcoq.Prim

ARGUMENT EXTEND ssrhyp TYPED AS ssrhyprep PRINTED BY pr_ssrhyp
                       INTERPRETED BY interp_hyp
                       GLOBALIZED BY intern_hyp
  | [ ident(id) ] -> [ SsrHyp (loc, id) ]
END


let hoik f = function Hyp x -> f x | Id x -> f x
let hoi_id = hoik hyp_id
let pr_hoi = hoik pr_hyp
let pr_ssrhoi _ _ _ = pr_hoi

let wit_ssrhoirep = add_genarg "ssrhoirep" pr_hoi

let intern_ssrhoi ist = function
  | Hyp h -> Hyp (intern_hyp ist h)
  | Id (SsrHyp (_, id)) as hyp ->
    let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_ident) id) in
    hyp

let interp_ssrhoi ist gl = function
  | Hyp h -> let s, h' = interp_hyp ist gl h in s, Hyp h'
  | Id (SsrHyp (loc, id)) ->
    let s, id' = interp_wit wit_ident ist gl id in
    s, Id (SsrHyp (loc, id'))

ARGUMENT EXTEND ssrhoi_hyp TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Hyp (SsrHyp(loc, id)) ]
END
ARGUMENT EXTEND ssrhoi_id TYPED AS ssrhoirep PRINTED BY pr_ssrhoi
                       INTERPRETED BY interp_ssrhoi
                       GLOBALIZED BY intern_ssrhoi
  | [ ident(id) ] -> [ Id (SsrHyp(loc, id)) ]
END


let pr_hyps = pr_list pr_spc pr_hyp
let pr_ssrhyps _ _ _ = pr_hyps
let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let check_hyp_exists hyps (SsrHyp(_, id)) =
  try ignore(Context.Named.lookup id hyps)
  with Not_found -> errorstrm (str"No assumption is named " ++ pr_id id)

let test_hypname_exists hyps id =
  try ignore(Context.Named.lookup id hyps); true
  with Not_found -> false

let interp_hyps ist gl ghyps =
  let hyps = List.map snd (List.map (interp_hyp ist gl) ghyps) in
  check_hyps_uniq [] hyps; Tacmach.project gl, hyps

ARGUMENT EXTEND ssrhyps TYPED AS ssrhyp list PRINTED BY pr_ssrhyps
                        INTERPRETED BY interp_hyps
  | [ ssrhyp_list(hyps) ] -> [ check_hyps_uniq [] hyps; hyps ]
END

(** Rewriting direction *)


let pr_dir = function L2R -> str "->" | R2L -> str "<-"
let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let wit_ssrdir = add_genarg "ssrdir" pr_dir

let dir_org = function L2R -> 1 | R2L -> 2

let pr_dir_side = function L2R -> str "LHS" | R2L -> str "RHS"
let inv_dir = function L2R -> R2L | R2L -> L2R

(** Simpl switch *)


let pr_simpl = function
  | Simpl -1 -> str "/="
  | Cut -1 -> str "//"
  | Simpl n -> str "/" ++ int n ++ str "="
  | Cut n -> str "/" ++ int n ++ str"/"
  | SimplCut (-1,-1) -> str "//="
  | SimplCut (n,-1) -> str "/" ++ int n ++ str "/="
  | SimplCut (-1,n) -> str "//" ++ int n ++ str "="
  | SimplCut (n,m) -> str "/" ++ int n ++ str "/" ++ int m ++ str "="
  | Nop -> mt ()

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep = add_genarg "ssrsimplrep" pr_simpl

let test_ssrslashnum b1 b2 strm =
  match Util.stream_nth 0 strm with
  | Tok.KEYWORD "/" ->
      (match Util.stream_nth 1 strm with
      | Tok.INT _ when b1 ->
         (match Util.stream_nth 2 strm with
         | Tok.KEYWORD "=" | Tok.KEYWORD "/=" when not b2 -> ()
         | Tok.KEYWORD "/" ->
             if not b2 then () else begin
               match Util.stream_nth 3 strm with
               | Tok.INT _ -> ()
               | _ -> raise Stream.Failure
             end
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "/" when not b1 ->
         (match Util.stream_nth 2 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Util.stream_nth 3 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "=" when not b1 && not b2 -> ()
      | _ -> raise Stream.Failure)
  | Tok.KEYWORD "//" when not b1 ->
         (match Util.stream_nth 1 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.INT _ when b2 ->
           (match Util.stream_nth 2 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
  | _ -> raise Stream.Failure

let test_ssrslashnum10 = test_ssrslashnum true false
let test_ssrslashnum11 = test_ssrslashnum true true
let test_ssrslashnum01 = test_ssrslashnum false true
let test_ssrslashnum00 = test_ssrslashnum false false

let negate_parser f x =
  let rc = try Some (f x) with Stream.Failure -> None in
  match rc with
  | None -> ()
  | Some _ -> raise Stream.Failure 

let test_not_ssrslashnum =
  Pcoq.Gram.Entry.of_parser
    "test_not_ssrslashnum" (negate_parser test_ssrslashnum10)
let test_ssrslashnum00 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum00
let test_ssrslashnum10 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum10" test_ssrslashnum10
let test_ssrslashnum11 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum11" test_ssrslashnum11
let test_ssrslashnum01 =
  Pcoq.Gram.Entry.of_parser "test_ssrslashnum01" test_ssrslashnum01


ARGUMENT EXTEND ssrsimpl_ne TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ "//=" ] -> [ SimplCut (~-1,~-1) ]
| [ "/=" ] -> [ Simpl ~-1 ]
END

Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrsimpl_ne;
  ssrsimpl_ne: [
    [ test_ssrslashnum11; "/"; n = natural; "/"; m = natural; "=" -> SimplCut(n,m)
    | test_ssrslashnum10; "/"; n = natural; "/" -> Cut n 
    | test_ssrslashnum10; "/"; n = natural; "=" -> Simpl n 
    | test_ssrslashnum10; "/"; n = natural; "/=" -> SimplCut (n,~-1) 
    | test_ssrslashnum10; "/"; n = natural; "/"; "=" -> SimplCut (n,~-1) 
    | test_ssrslashnum01; "//"; m = natural; "=" -> SimplCut (~-1,m)
    | test_ssrslashnum00; "//" -> Cut ~-1
    ]];

END
))

ARGUMENT EXTEND ssrsimpl TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ ssrsimpl_ne(sim) ] -> [ sim ]
| [ ] -> [ Nop ]
END

let pr_clear_ne clr = str "{" ++ pr_hyps clr ++ str "}"
let pr_clear sep clr = if clr = [] then mt () else sep () ++ pr_clear_ne clr

let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ssrhyps PRINTED BY pr_ssrclear
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ check_hyps_uniq [] clr; clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END

(** Indexes *)

(* Since SSR indexes are always positive numbers, we use the 0 value *)
(* to encode an omitted index. We reuse the in or_var type, but we   *)
(* supply our own interpretation function, which checks for non      *)
(* positive values, and allows the use of constr numerals, so that   *)
(* e.g., "let n := eval compute in (1 + 3) in (do n!clear)" works.   *)


let pr_index = function
  | Misctypes.ArgVar (_, id) -> pr_id id
  | Misctypes.ArgArg n when n > 0 -> int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = Misctypes.ArgArg 0

let check_index loc i =
  if i > 0 then i else loc_error loc (str"Index not positive")
let mk_index loc = function
  | Misctypes.ArgArg i -> Misctypes.ArgArg (check_index loc i)
  | iv -> iv

let interp_index ist gl idx =
  Tacmach.project gl, 
  match idx with
  | Misctypes.ArgArg _ -> idx
  | Misctypes.ArgVar (loc, id) ->
    let i =
      try
        let v = Id.Map.find id ist.Tacinterp.lfun in
        begin match Tacinterp.Value.to_int v with
        | Some i -> i
        | None ->
        begin match Tacinterp.Value.to_constr v with
        | Some c ->
          let rc = Detyping.detype false [] (pf_env gl) (project gl) c in
          begin match Notation.uninterp_prim_token rc with
          | _, Constrexpr.Numeral bigi -> int_of_string (Bigint.to_string bigi)
          | _ -> raise Not_found
          end
        | None -> raise Not_found
        end end
    with _ -> loc_error loc (str"Index not a number") in
    Misctypes.ArgArg (check_index loc i)

open Pltac

ARGUMENT EXTEND ssrindex TYPED AS ssrindex PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index loc i ]
END


(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5}. An initial                                *)
(* "+" may be used to indicate positive occurrences (the default). The    *)
(* "+" is optional, except if the list of occurrences starts with a       *)
(* variable or is empty (to avoid confusion with a clear switch). The     *)
(* empty positive switch "{+}" selects no occurrences, while the empty    *)
(* negative switch "{-}" selects all occurrences explicitly; this is the  *)
(* default, but "{-}" prevents the implicit clear, and can be used to     *)
(* force dependent elimination -- see ndefectelimtac below.               *)


let pr_occ = function
  | Some (true, occ) -> str "{-" ++ pr_list pr_spc int occ ++ str "}"
  | Some (false, occ) -> str "{+" ++ pr_list pr_spc int occ ++ str "}"
  | None -> str "{}"

let pr_ssrocc _ _ _ = pr_occ

open Pcoq.Prim

ARGUMENT EXTEND ssrocc TYPED AS (bool * int list) option PRINTED BY pr_ssrocc
| [ natural(n) natural_list(occ) ] -> [
     Some (false, List.map (check_index loc) (n::occ)) ]
| [ "-" natural_list(occ) ]     -> [ Some (true, occ) ]
| [ "+" natural_list(occ) ]     -> [ Some (false, occ) ]
END

let allocc = Some(false,[])

(* modality *)


let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod = add_genarg "ssrmmod" pr_mmod
let ssrmmod = Pcoq.create_generic_entry Pcoq.utactic "ssrmmod" (Genarg.rawwit wit_ssrmmod);;

Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrmmod;
  ssrmmod: [[ "!" -> Must | LEFTQMARK -> May | "?" -> May]];
END
))

(** Rewrite multiplier: !n ?n *)


let notimes = 0
let nomult = 1, Once

let pr_mult (n, m) =
  if n > 0 && m <> Once then int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult

ARGUMENT EXTEND ssrmult_ne TYPED AS int * ssrmmod PRINTED BY pr_ssrmult
  | [ natural(n) ssrmmod(m) ] -> [ check_index loc n, m ]
  | [ ssrmmod(m) ]            -> [ notimes, m ]
END

ARGUMENT EXTEND ssrmult TYPED AS ssrmult_ne PRINTED BY pr_ssrmult
  | [ ssrmult_ne(m) ] -> [ m ]
  | [ ] -> [ nomult ]
END

(** Discharge occ switch (combined occurrence / clear switch *)


let mkocc occ = None, occ
let noclr = mkocc None
let mkclr clr  = Some clr, None
let nodocc = mkclr []

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
END

(* kinds of terms *)

(* type ssrtermkind = InParens | WithAt | NoFlag | Cpattern *)
let xInParens = '('
let xWithAt = '@'
let xNoFlag = ' '
let xCpattern = 'x'

let input_ssrtermkind strm = match Util.stream_nth 0 strm with
  | Tok.KEYWORD "(" -> xInParens
  | Tok.KEYWORD "@" -> xWithAt
  | _ -> xNoFlag

let ssrtermkind = Pcoq.Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

(* terms *)

(** Terms parsing. ********************************************************)

let glob_constr ist genv = function
  | _, Some ce ->
    let vars = Id.Map.fold (fun x _ accu -> Id.Set.add x accu) ist.Tacinterp.lfun Id.Set.empty in
    let ltacvars = {
      Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
    Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv ce
  | rc, None -> rc

let interp_constr = interp_wit wit_constr

let interp_open_constr ist gl gc =
  let (sigma, (c, _)) = Tacinterp.interp_open_constr_with_bindings ist (pf_env gl) (project gl) (gc, Misctypes.NoBindings) in
  (project gl, (sigma, c))

let mkRHole = Glob_term.GHole (dummy_loc, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)

let mk_term k c = k, (mkRHole, Some c)
let mk_lterm c = mk_term xNoFlag c



(* Term printing utilities functions for deciding bracketing.  *)
let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")
(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 = xInParens
(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let pr_guarded guard prc c =
  pp_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

let prl_constr_expr = Ppconstr.pr_lconstr_expr
let pr_glob_constr c = Printer.pr_glob_constr_env (Global.env ()) c
let prl_glob_constr c = Printer.pr_lglob_constr_env (Global.env ()) c
let prl_glob_constr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> Printer.pr_lglob_constr c
let pr_glob_constr_and_expr = function
  | _, Some c -> Ppconstr.pr_constr_expr c
  | c, None -> pr_glob_constr c
let pr_term (k, c) = pr_guarded (guard_term k) pr_glob_constr_and_expr c
let prl_term (k, c) = pr_guarded (guard_term k) prl_glob_constr_and_expr c


(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* terms *)
let pr_ssrterm _ _ _ = pr_term
let pf_intern_term ist gl (_, c) = glob_constr ist (pf_env gl) c
let intern_term ist env (_, c) = glob_constr ist env c
let interp_term ist gl (_, c) = snd (interp_open_constr ist gl c)
let force_term ist gl (_, c) = interp_constr ist gl c
let glob_ssrterm gs = function
  | k, (_, Some c) -> k, Tacintern.intern_constr gs c
  | ct -> ct
let subst_ssrterm s (k, c) = k, Tacsubst.subst_glob_constr_and_expr s c
let interp_ssrterm _ gl t = Tacmach.project gl, t

open Pcoq.Constr

ARGUMENT EXTEND ssrterm
     PRINTED BY pr_ssrterm
     INTERPRETED BY interp_ssrterm
     GLOBALIZED BY glob_ssrterm SUBSTITUTED BY subst_ssrterm
     RAW_PRINTED BY pr_ssrterm
     GLOB_PRINTED BY pr_ssrterm
| [ "YouShouldNotTypeThis" constr(c) ] -> [ mk_lterm c ]
END


Pcoq.(Prim.(
GEXTEND Gram
  GLOBAL: ssrterm;
  ssrterm: [[ k = ssrtermkind; c = Pcoq.Constr.constr -> mk_term k c ]];
END
))

(* Views *)

let pr_view = pr_list mt (fun c -> str "/" ++ pr_term c)

let pr_ssrview _ _ _ = pr_view

ARGUMENT EXTEND ssrview TYPED AS ssrterm list
   PRINTED BY pr_ssrview
| [ "YouShouldNotTypeThis" ] -> [ [] ]
END

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrview;
  ssrview: [
    [  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr -> [mk_term xNoFlag c]
    |  test_not_ssrslashnum; "/"; c = Pcoq.Constr.constr; w = ssrview ->
                    (mk_term xNoFlag c) :: w ]];
END
)

(* }}} *)
 
(* ipats *)


let remove_loc = snd

let ipat_of_intro_pattern p = Misctypes.(
  let rec ipat_of_intro_pattern = function
    | IntroNaming (IntroIdentifier id) -> IpatId id
    | IntroAction IntroWildcard -> IpatWild
    | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
      IpatCase 
       (`Regular (List.map (List.map ipat_of_intro_pattern) 
 	 (List.map (List.map remove_loc) iorpat)))
    | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
      IpatCase 
       (`Regular [List.map ipat_of_intro_pattern (List.map remove_loc iandpat)])
    | IntroNaming IntroAnonymous -> IpatAnon
    | IntroAction (IntroRewrite b) -> IpatRw (allocc, if b then L2R else R2L)
    | IntroNaming (IntroFresh id) -> IpatAnon
    | IntroAction (IntroApplyOn _) -> (* to do *) CErrors.error "TO DO"
    | IntroAction (IntroInjection ips) ->
        IpatInj [List.map ipat_of_intro_pattern (List.map remove_loc ips)]
    | IntroForthcoming _ ->
        (* Unable to determine which kind of ipat interp_introid could
         * return [HH] *)
        assert false
  in
  ipat_of_intro_pattern p
)

let rec pr_ipat p = Misctypes.(
  match p with
  | IpatId id -> pr_id id
  | IpatSimpl (clr, sim) -> pr_clear mt clr ++ pr_simpl sim
  | IpatCase (`Regular iorpat) -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IpatCase (`Block(before,seed,after)) ->
       hov 1 (str "[" ++ pr_iorpat before
                      ++ pr_seed before seed
                      ++ pr_iorpat after ++ str "]")
  | IpatSeed s -> pr_seed [] s
  | IpatInj iorpat -> hov 1 (str "[=" ++ pr_iorpat iorpat ++ str "]")
  | IpatRw (occ, dir) -> pr_occ occ ++ pr_dir dir
  | IpatAll -> str "*"
  | IpatWild -> str "_"
  | IpatAnon -> str "?"
  | IpatView v -> pr_view v
  | IpatNoop -> str "-"
  | IpatNewHidden l -> str "[:" ++ pr_list spc pr_id l ++ str "]"
  | IpatFastMode -> str ">"
  | IpatTmpId -> str "+"
)
and pr_space_notFM = function IpatFastMode :: _ -> str"" | _ -> str" "
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat
and pr_ipats ipats = pr_space_notFM ipats ++ pr_list spc pr_ipat ipats
and pr_seed before seed =
  (if before <> [] then str"|" else str"") ++
  match seed with
  | `Id(id,side) -> str"^" ++ str(if side = `Post then "~" else "") ++ pr_id id
  | `Anon -> str "^ ? "
  | `Wild -> str "^ _ "

let wit_ssripatrep = add_genarg "ssripatrep" pr_ipat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist ipat =
  let rec check_pat = function
  | IpatSimpl (clr, _) -> ignore (List.map (intern_hyp ist) clr)
  | IpatCase (`Regular iorpat) -> List.iter (List.iter check_pat) iorpat
  | IpatCase (`Block (before,_,after)) ->
       List.iter (List.iter check_pat) (before @ after)
  | IpatInj iorpat -> List.iter (List.iter check_pat) iorpat
  | _ -> () in
  check_pat ipat; ipat

let intern_ipats ist = List.map (intern_ipat ist)

let interp_intro_pattern = interp_wit wit_intro_pattern

let interp_introid ist gl id = Misctypes.(
 try IntroNaming (IntroIdentifier (hyp_id (snd (interp_hyp ist gl (SsrHyp (dummy_loc, id))))))
 with _ -> snd(snd (interp_intro_pattern ist gl (dummy_loc,IntroNaming (IntroIdentifier id))))
)

let rec add_intro_pattern_hyps (loc, ipat) hyps = Misctypes.(
  match ipat with
  | IntroNaming (IntroIdentifier id) ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err loc "Can't delete section hypothesis " id
  | IntroAction IntroWildcard -> hyps
  | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
     List.fold_right (List.fold_right add_intro_pattern_hyps) iorpat hyps
  | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
    List.fold_right add_intro_pattern_hyps iandpat hyps
  | IntroNaming IntroAnonymous -> []
  | IntroNaming (IntroFresh _) -> []
  | IntroAction (IntroRewrite _) -> hyps
  | IntroAction (IntroInjection ips) -> List.fold_right add_intro_pattern_hyps ips hyps
  | IntroAction (IntroApplyOn (c,pat)) -> add_intro_pattern_hyps pat hyps
  | IntroForthcoming _ -> 
    (* As in ipat_of_intro_pattern, was unable to determine which kind
      of ipat interp_introid could return [HH] *) assert false
)

let rec interp_ipat ist gl = Misctypes.(
  let ltacvar id = Id.Map.mem id ist.Tacinterp.lfun in
  let interp_seed = function
    | (`Anon | `Wild) as x -> x
    | `Id(id,side) ->
        match interp_introid ist gl id with
        | IntroNaming (IntroIdentifier id) -> `Id(id,side)
        | _ -> `Id(Id.of_string "_",`Pre) in
  let rec interp = function
  | IpatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist gl id)
  | IpatSimpl (clr, sim) ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps (loc, (interp_introid ist gl id)) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr'; IpatSimpl (clr', sim)
  | IpatCase(`Regular iorpat) ->
      IpatCase(`Regular(List.map (List.map interp) iorpat))
  | IpatCase(`Block (before,seed,after)) ->
      let before = List.map (List.map interp) before in
      let seed = interp_seed seed in
      let after = List.map (List.map interp) after in
      IpatCase(`Block (before,seed,after))
  | IpatSeed s -> IpatSeed (interp_seed s)
  | IpatInj iorpat -> IpatInj (List.map (List.map interp) iorpat)
  | IpatNewHidden l ->
      IpatNewHidden
        (List.map (function
           | IntroNaming (IntroIdentifier id) -> id
           | _ -> assert false)
        (List.map (interp_introid ist gl) l))
  | ipat -> ipat in
  interp
)

let interp_ipats ist gl l = project gl, List.map (interp_ipat ist gl) l

let pushIpatRw = function
  | pats :: orpat -> (IpatRw (allocc, L2R) :: pats) :: orpat
  | [] -> []

let pushIpatNoop = function
  | pats :: orpat -> (IpatNoop :: pats) :: orpat
  | [] -> []

ARGUMENT EXTEND ssripat TYPED AS ssripatrep list PRINTED BY pr_ssripats
  INTERPRETED BY interp_ipats
  GLOBALIZED BY intern_ipats
  | [ "_" ] -> [ [IpatWild] ]
  | [ "*" ] -> [ [IpatAll] ]
  | [ "^" "*" ] -> [ [IpatFastMode] ]
  | [ "^" "_" ] -> [ [IpatSeed `Wild] ]
  | [ "^_" ] -> [ [IpatSeed `Wild] ]
  | [ "^" "?" ] -> [ [IpatSeed `Anon] ]
  | [ "^?" ] -> [ [IpatSeed `Anon] ]
  | [ "^" ident(id) ] -> [ [IpatSeed (`Id(id,`Pre))] ]
  | [ "^" "~" ident(id) ] -> [ [IpatSeed (`Id(id,`Post))] ]
  | [ "^~" ident(id) ] -> [ [IpatSeed (`Id(id,`Post))] ]
  | [ ident(id) ] -> [ [IpatId id] ]
  | [ "?" ] -> [ [IpatAnon] ]
  | [ "+" ] -> [ [IpatTmpId] ]
  | [ ssrsimpl_ne(sim) ] -> [ [IpatSimpl ([], sim)] ]
  | [ ssrdocc(occ) "->" ] -> [ match occ with
      | None, occ -> [IpatRw (occ, L2R)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw (allocc, L2R)]]
  | [ ssrdocc(occ) "<-" ] -> [ match occ with
      | None, occ ->  [IpatRw (occ, R2L)]
      | Some clr, _ -> [IpatSimpl (clr, Nop); IpatRw (allocc, R2L)]]
  | [ ssrdocc(occ) ] -> [ match occ with
      | Some cl, _ -> check_hyps_uniq [] cl; [IpatSimpl (cl, Nop)]
      | _ -> loc_error loc (str"Only identifiers are allowed here")]
  | [ "->" ] -> [ [IpatRw (allocc, L2R)] ]
  | [ "<-" ] -> [ [IpatRw (allocc, R2L)] ]
  | [ "-" ] -> [ [IpatNoop] ]
  | [ "-/" "=" ] -> [ [IpatNoop;IpatSimpl([],Simpl ~-1)] ]
  | [ "-/=" ] -> [ [IpatNoop;IpatSimpl([],Simpl ~-1)] ]
  | [ "-/" "/" ] -> [ [IpatNoop;IpatSimpl([],Cut ~-1)] ]
  | [ "-//" ] -> [ [IpatNoop;IpatSimpl([],Cut ~-1)] ]
  | [ "-/" integer(n) "/" ] -> [ [IpatNoop;IpatSimpl([],Cut n)] ]
  | [ "-/" "/=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-//" "=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-//=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (~-1,~-1))] ]
  | [ "-/" integer(n) "/=" ] -> [ [IpatNoop;IpatSimpl([],SimplCut (n,~-1))] ]
  | [ "-/" integer(n) "/" integer (m) "=" ] ->
      [ [IpatNoop;IpatSimpl([],SimplCut(n,m))] ]
  | [ ssrview(v) ] -> [ [IpatView v] ]
  | [ "[" ":" ident_list(idl) "]" ] -> [ [IpatNewHidden idl] ]
  | [ "[:" ident_list(idl) "]" ] -> [ [IpatNewHidden idl] ]
END

ARGUMENT EXTEND ssripats TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
  | [ ] -> [ [] ]
END

ARGUMENT EXTEND ssriorpat TYPED AS ssripat list PRINTED BY pr_ssriorpat
| [ ssripats(pats) "|" ssriorpat(orpat) ] -> [ pats :: orpat ]
| [ ssripats(pats) "|-" ">" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "|-" ssriorpat(orpat) ] -> [ pats :: pushIpatNoop orpat ]
| [ ssripats(pats) "|->" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "||" ssriorpat(orpat) ] -> [ pats :: [] :: orpat ]
| [ ssripats(pats) "|||" ssriorpat(orpat) ] -> [ pats :: [] :: [] :: orpat ]
| [ ssripats(pats) "||||" ssriorpat(orpat) ] -> [ [pats; []; []; []] @ orpat ]
| [ ssripats(pats) ] -> [ [pats] ]
END

let reject_ssrhid strm =
  match Util.stream_nth 0 strm with
  | Tok.KEYWORD "[" ->
      (match Util.stream_nth 1 strm with
      | Tok.KEYWORD ":" -> raise Stream.Failure
      | _ -> ())
  | _ -> ()

let test_nohidden = Pcoq.Gram.Entry.of_parser "test_ssrhid" reject_ssrhid

ARGUMENT EXTEND ssrcpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "YouShouldNotTypeThis" ssriorpat(x) ] -> [ IpatCase(`Regular x) ]
END

let understand_case_type ior =
  let rec aux before = function
    | [] -> `Regular (List.rev before)
    | [IpatSeed seed] :: rest -> `Block(List.rev before, seed, rest)
    | ips :: rest -> aux (ips :: before) rest
  in
    aux [] ior

let rec check_no_inner_seed loc seen = function
  | [] -> ()
  | x :: xs ->
     let in_x = List.exists (function IpatSeed _ -> true | _ -> false) x in
     if seen && in_x then
        CErrors.user_err ~loc ~hdr:"ssreflect"
            (strbrk "Only one block ipat per elimination is allowed")
     else if List.length x < 2 ||
        List.for_all (function
          | IpatSeed _ -> false
          | IpatInj l | IpatCase (`Regular l) ->
              check_no_inner_seed loc false l; true
          | IpatCase (`Block(before,_,after)) ->
              check_no_inner_seed loc false before;
              check_no_inner_seed loc false after; true
          | _ -> true) x
     then check_no_inner_seed loc (seen || in_x) xs
     else CErrors.user_err ~loc ~hdr:"ssreflect"
            (strbrk "Mixing block and regular ipat is forbidden")
;;

Pcoq.(
GEXTEND Gram
  GLOBAL: ssrcpat;
  ssrcpat: [
   [ test_nohidden; "["; iorpat = ssriorpat; "]" ->
      check_no_inner_seed !@loc false iorpat;
      IpatCase (understand_case_type iorpat)
   | test_nohidden; "[="; iorpat = ssriorpat; "]" ->
      check_no_inner_seed !@loc false iorpat;
      IpatInj iorpat ]];
END
);;

Pcoq.(
GEXTEND Gram
  GLOBAL: ssripat;
  ssripat: [[ pat = ssrcpat -> [pat] ]];
END
)

ARGUMENT EXTEND ssripats_ne TYPED AS ssripat PRINTED BY pr_ssripats
  | [ ssripat(i) ssripats(tl) ] -> [ i @ tl ]
                                     END

(* subsets of patterns *)

let check_ssrhpats loc w_binders ipats =
  let err_loc s = CErrors.user_err ~loc ~hdr:"ssreflect" s in
  let clr, ipats =
    let rec aux clr = function
      | IpatSimpl (cl, Nop) :: tl -> aux (clr @ cl) tl
      | IpatSimpl (cl, sim) :: tl -> clr @ cl, IpatSimpl ([], sim) :: tl
      | tl -> clr, tl
    in aux [] ipats in
  let simpl, ipats = 
    match List.rev ipats with
    | IpatSimpl ([],_) as s :: tl -> [s], List.rev tl
    | _ -> [],  ipats in
  if simpl <> [] && not w_binders then
    err_loc (str "No s-item allowed here: " ++ pr_ipats simpl);
  let ipat, binders =
    let rec loop ipat = function
      | [] -> ipat, []
      | ( IpatId _| IpatAnon| IpatCase _| IpatRw _ as i) :: tl -> 
        if w_binders then
          if simpl <> [] && tl <> [] then 
            err_loc(str"binders XOR s-item allowed here: "++pr_ipats(tl@simpl))
          else if not (List.for_all (function IpatId _ -> true | _ -> false) tl)
          then err_loc (str "Only binders allowed here: " ++ pr_ipats tl)
          else ipat @ [i], tl
        else
          if tl = [] then  ipat @ [i], []
          else err_loc (str "No binder or s-item allowed here: " ++ pr_ipats tl)
      | hd :: tl -> loop (ipat @ [hd]) tl
    in loop [] ipats in
  ((clr, ipat), binders), simpl

let single loc =
  function [x] -> x | _ -> loc_error loc (str"Only one intro pattern is allowed")

let pr_hpats (((clr, ipat), binders), simpl) =
   pr_clear mt clr ++ pr_ipats ipat ++ pr_ipats binders ++ pr_ipats simpl
let pr_ssrhpats _ _ _ = pr_hpats
let pr_ssrhpats_wtransp _ _ _ (_, x) = pr_hpats x

ARGUMENT EXTEND ssrhpats TYPED AS ((ssrclear * ssripat) * ssripat) * ssripat
PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc true i ]
END

ARGUMENT EXTEND ssrhpats_wtransp
  TYPED AS bool * (((ssrclear * ssripats) * ssripats) * ssripats)
  PRINTED BY pr_ssrhpats_wtransp
  | [ ssripats(i) ] -> [ false,check_ssrhpats loc true i ]
  | [ ssripats(i) "@" ssripats(j) ] -> [ true,check_ssrhpats loc true (i @ j) ]
END

ARGUMENT EXTEND ssrhpats_nobs 
TYPED AS ((ssrclear * ssripats) * ssripats) * ssripats PRINTED BY pr_ssrhpats
  | [ ssripats(i) ] -> [ check_ssrhpats loc false i ]
END

ARGUMENT EXTEND ssrrpat TYPED AS ssripatrep PRINTED BY pr_ssripat
  | [ "->" ] -> [ IpatRw (allocc, L2R) ]
  | [ "<-" ] -> [ IpatRw (allocc, R2L) ]
END

type ssrintros = ssripats

let pr_intros sep intrs =
  if intrs = [] then mt() else sep () ++ str "=>" ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt

ARGUMENT EXTEND ssrintros_ne TYPED AS ssripat
 PRINTED BY pr_ssrintros
  | [ "=>" ssripats_ne(pats) ] -> [ pats ]
  | [ "=>" ">" ssripats_ne(pats) ] -> [ IpatFastMode :: pats ]
  | [ "=>>" ssripats_ne(pats) ] -> [ IpatFastMode :: pats ]
END

ARGUMENT EXTEND ssrintros TYPED AS ssrintros_ne PRINTED BY pr_ssrintros
  | [ ssrintros_ne(intrs) ] -> [ intrs ]
  | [ ] -> [ [] ]
END

let pr_ssrintrosarg _ _ prt (tac, ipats) =
  prt tacltop tac ++ pr_intros spc ipats

ARGUMENT EXTEND ssrintrosarg TYPED AS tactic * ssrintros
   PRINTED BY pr_ssrintrosarg
| [ "YouShouldNotTypeThis" ssrtacarg(arg) ssrintros_ne(ipats) ] -> [ arg, ipats ]
END

(* set_pr_ssrtac "tclintros" 0 [ArgSsr "introsarg"] *)
let ssrtac_name name = {
  mltac_plugin = "ssreflect_plugin";
  mltac_tactic = "ssr" ^ name;
}

let ssrtac_entry name n = {
  mltac_name = ssrtac_name name; 
  mltac_index = n;
}
let ssrtac_atom loc name args = TacML (loc, ssrtac_entry name 0, args)
let ssrtac_expr = ssrtac_atom

let tclintros_expr loc tac ipats =
  let args = [Tacexpr.TacGeneric (in_gen (rawwit wit_ssrintrosarg) (tac, ipats))] in
  ssrtac_expr loc "tclintros" args

GEXTEND Gram
  GLOBAL: tactic_expr;
  tactic_expr: LEVEL "1" [ RIGHTA
    [ tac = tactic_expr; intros = ssrintros_ne -> tclintros_expr !@loc tac intros
    ] ];
END

(** Defined identifier *)
let pr_ssrfwdid id = pr_spc () ++ pr_id id

let pr_ssrfwdidx _ _ _ = pr_ssrfwdid

(* We use a primitive parser for the head identifier of forward *)
(* tactis to avoid syntactic conflicts with basic Coq tactics. *)
ARGUMENT EXTEND ssrfwdid TYPED AS ident PRINTED BY pr_ssrfwdidx
  | [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let accept_ssrfwdid strm =
  match stream_nth 0 strm with
  | Tok.IDENT id -> accept_before_syms_or_any_id [":"; ":="; "("] strm
  | _ -> raise Stream.Failure


let test_ssrfwdid = Gram.Entry.of_parser "test_ssrfwdid" accept_ssrfwdid

GEXTEND Gram
  GLOBAL: ssrfwdid;
  ssrfwdid: [[ test_ssrfwdid; id = Prim.ident -> id ]];
  END

  
(* by *)
(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)


let pr_ortacs prt = 
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic option list PRINTED BY pr_ssrortacs
| [ ssrtacarg(tac) "|" ssrortacs(tacs) ] -> [ Some tac :: tacs ]
| [ ssrtacarg(tac) "|" ] -> [ [Some tac; None] ]
| [ ssrtacarg(tac) ] -> [ [Some tac] ]
| [ "|" ssrortacs(tacs) ] -> [ None :: tacs ]
| [ "|" ] -> [ [None; None] ]
END

let pr_hintarg prt = function
  | true, tacs -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, [Some tac] -> prt tacltop tac
  | _, _ -> mt()

let pr_ssrhintarg _ _ = pr_hintarg

let mk_hint tac = false, [Some tac]
let mk_orhint tacs = true, tacs
let nullhint = true, []
let nohint = false, []

ARGUMENT EXTEND ssrhintarg TYPED AS bool * ssrortacs PRINTED BY pr_ssrhintarg
| [ "[" "]" ] -> [ nullhint ]
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
| [ ssrtacarg(arg) ] -> [ mk_hint arg ]
END

ARGUMENT EXTEND ssrortacarg TYPED AS ssrhintarg PRINTED BY pr_ssrhintarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_orhint tacs ]
END


let pr_hint prt arg =
  if arg = nohint then mt() else str "by " ++ pr_hintarg prt arg
let pr_ssrhint _ _ = pr_hint

ARGUMENT EXTEND ssrhint TYPED AS ssrhintarg PRINTED BY pr_ssrhint
| [ ]                       -> [ nohint ]
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

open Ssrmatching_plugin.Ssrmatching

let pr_wgen = function 
  | (clr, Some((id,k),None)) -> spc() ++ pr_clear mt clr ++ str k ++ pr_hoi id
  | (clr, Some((id,k),Some p)) ->
      spc() ++ pr_clear mt clr ++ str"(" ++ str k ++ pr_hoi id ++ str ":=" ++
        pr_cpattern p ++ str ")"
  | (clr, None) -> spc () ++ pr_clear mt clr
let pr_ssrwgen _ _ _ = pr_wgen

(* no globwith for char *)
ARGUMENT EXTEND ssrwgen
  TYPED AS ssrclear * ((ssrhoi_hyp * string) * cpattern option) option
  PRINTED BY pr_ssrwgen
| [ ssrclear_ne(clr) ] -> [ clr, None ]
| [ ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, " "), None) ]
| [ "@" ssrhoi_hyp(hyp) ] -> [ [], Some((hyp, "@"), None) ]
| [ "(" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id," "),Some p) ]
| [ "(" ssrhoi_id(id) ")" ] -> [ [], Some ((id,"("), None) ]
| [ "(@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
| [ "(" "@" ssrhoi_id(id) ":=" lcpattern(p) ")" ] ->
  [ [], Some ((id,"@"),Some p) ]
END

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq = add_genarg "ssrclseq" pr_clseq
let pr_clausehyps = pr_list pr_spc pr_wgen
let pr_ssrclausehyps _ _ _ = pr_clausehyps

ARGUMENT EXTEND ssrclausehyps 
TYPED AS ssrwgen list PRINTED BY pr_ssrclausehyps
| [ ssrwgen(hyp) "," ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
| [ ssrwgen(hyp) ] -> [ [hyp] ]
END

(* type ssrclauses = ssrahyps * ssrclseq *)

let pr_clauses (hyps, clseq) = 
  if clseq = InGoal then mt ()
  else str "in " ++ pr_clausehyps hyps ++ pr_clseq clseq
let pr_ssrclauses _ _ _ = pr_clauses

ARGUMENT EXTEND ssrclauses TYPED AS ssrwgen list * ssrclseq
    PRINTED BY pr_ssrclauses
  | [ "in" ssrclausehyps(hyps) "|-" "*" ] -> [ hyps, InHypsSeqGoal ]
  | [ "in" ssrclausehyps(hyps) "|-" ]     -> [ hyps, InHypsSeq ]
  | [ "in" ssrclausehyps(hyps) "*" ]      -> [ hyps, InHypsGoal ]
  | [ "in" ssrclausehyps(hyps) ]          -> [ hyps, InHyps ]
  | [ "in" "|-" "*" ]                     -> [ [], InSeqGoal ]
  | [ "in" "*" ]                          -> [ [], InAll ]
  | [ "in" "*" "|-" ]                     -> [ [], InAllHyps ]
  | [ ]                                   -> [ [], InGoal ]
END




(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)

let pr_binder prl = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prl t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prl v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prl t ++
                            str " := " ++ prl v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prl t

let rec mkBstruct i = function
  | Bvar x :: b ->
    if i = 0 then [Bstruct x] else mkBstruct (i - 1) b
  | Bdecl (xs, _) :: b ->
    let i' = i - List.length xs in
    if i' < 0 then [Bstruct (List.nth xs i)] else mkBstruct i' b
  | _ :: b -> mkBstruct i b
  | [] -> []

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, CLocalAssum ([_, x], _,  _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, CLocalAssum (lxs, _, t) :: bl ->
    Bdecl (List.map snd lxs, t) :: format_local_binders h bl
  | BFdef :: h, CLocalDef ((_, x), v, oty) :: bl ->
    Bdef (x, oty, v) :: format_local_binders h bl
  | _ -> []
  
let rec format_constr_expr h0 c0 = match h0, c0 with
  | BFvar :: h, CLambdaN (_, [[_, x], _, _], c) ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, CLambdaN (_, [lxs, _, t], c) ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map snd lxs, t) :: bs, c'
  | BFdef :: h, CLetIn(_, (_, x), v, oty, c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, oty, v) :: bs, c'
  | [BFcast], CCast (_, c, CastConv t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, 
    CFix (_, _, [_, (Some locn, CStructRec), bl, t, c]) ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then [Bstruct (Name (snd locn))] else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c 
  | BFrec (_, has_cast) :: h, CCoFix (_, _, [_, bl, t, c]) ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

let rec format_glob_decl h0 d0 = match h0, d0 with
  | BFvar :: h, (x, _, None, _) :: d ->
    Bvar x :: format_glob_decl h d
  | BFdecl 1 :: h,  (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_glob_decl h d
  | BFdecl n :: h, (x, _, None, t) :: d when n > 1 ->
    begin match format_glob_decl (BFdecl (n - 1) :: h) d with
    | Bdecl (xs, _) :: bs -> Bdecl (x :: xs, t) :: bs
    | bs -> Bdecl ([x], t) :: bs
    end
  | BFdef :: h, (x, _, Some v, _)  :: d ->
    Bdef (x, None, v) :: format_glob_decl h d
  | _, (x, _, None, t) :: d ->
    Bdecl ([x], t) :: format_glob_decl [] d
  | _, (x, _, Some v, _) :: d ->
     Bdef (x, None, v) :: format_glob_decl [] d
  | _, [] -> []

let rec format_glob_constr h0 c0 = match h0, c0 with
  | BFvar :: h, GLambda (_, x, _, _, c) ->
    let bs, c' = format_glob_constr h c in
    Bvar x :: bs, c'
  | BFdecl 1 :: h,  GLambda (_, x, _, t, c) ->
    let bs, c' = format_glob_constr h c in
    Bdecl ([x], t) :: bs, c'
  | BFdecl n :: h,  GLambda (_, x, _, t, c) when n > 1 ->
    begin match format_glob_constr (BFdecl (n - 1) :: h) c with
    | Bdecl (xs, _) :: bs, c' -> Bdecl (x :: xs, t) :: bs, c'
    | _ -> [Bdecl ([x], t)], c
    end
  | BFdef :: h, GLetIn(_, x, v, oty, c) ->
    let bs, c' = format_glob_constr h c in
    Bdef (x, oty, v) :: bs, c'
  | [BFcast], GCast (_, c, CastConv t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, GRec (_, f, _, bl, t, c)
      when Array.length c = 1 ->
    let bs = format_glob_decl h bl.(0) in
    let bstr = match has_str, f with
    | true, GFix ([|Some i, GStructRec|], _) -> mkBstruct i bs
    | _ -> [] in
    bs @ bstr @ (if has_cast then [Bcast t.(0)] else []), c.(0)
  | _, c ->
    [], c

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

let pr_fwdkind = function
  | FwdHint (s,_) -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt = add_genarg "ssrfwdfmt" pr_fwdfmt

(* type ssrfwd = ssrfwdfmt * ssrterm *)

let mkFwdVal fk c = ((fk, []), mk_term xNoFlag c)
let mkssrFwdVal fk c = ((fk, []), (c,None))
let dC t = CastConv t

let mkFwdCast fk loc t c = ((fk, [BFcast]), mk_term xNoFlag (CCast (loc, c, dC t)))
let mkssrFwdCast fk loc t c = ((fk, [BFcast]), (c, Some t))
let mkCHole loc = CHole (loc, None, IntroAnonymous, None)

let mkFwdHint s t =
  let loc =  Constrexpr_ops.constr_loc t in
  mkFwdCast (FwdHint (s,false)) loc t (mkCHole loc)
let mkFwdHintNoTC s t =
  let loc =  Constrexpr_ops.constr_loc t in
  mkFwdCast (FwdHint (s,true)) loc t (mkCHole loc)

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint (s,_), [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint (s,_), _ ->  prc (s ^ "(* typeof *)")
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _, _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_fwd_guarded prval prval' = function
| (fk, h), (_, (_, Some c)) ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)
| (fk, h), (_, (c, None)) ->
  pr_gen_fwd prval' pr_glob_constr prl_glob_constr fk (format_glob_constr h c)

let pr_unguarded prc prlc = prlc

let pr_fwd = pr_fwd_guarded pr_unguarded pr_unguarded
let pr_ssrfwd _ _ _ = pr_fwd
 
ARGUMENT EXTEND ssrfwd TYPED AS (ssrfwdfmt * ssrterm) PRINTED BY pr_ssrfwd
  | [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" lconstr (t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c ]
END

(** Independent parsing for binders *)

(* The pose, pose fix, and pose cofix tactics use these internally to  *)
(* parse argument fragments.                                           *)

let pr_ssrbvar prc _ _ v = prc v
let mkCVar loc id = CRef (Ident (loc, id),None)

ARGUMENT EXTEND ssrbvar TYPED AS constr PRINTED BY pr_ssrbvar
| [ ident(id) ] -> [ mkCVar loc id ]
| [ "_" ] -> [ mkCHole loc ]
END

let bvar_lname = function
  | CRef (Ident (loc, id), _) -> loc, Name id
  | c -> constr_loc c, Anonymous

let pr_ssrbinder prc _ _ (_, c) = prc c

ARGUMENT EXTEND ssrbinder TYPED AS ssrfwdfmt * constr PRINTED BY pr_ssrbinder
 | [ ssrbvar(bv) ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,mkCHole xloc],mkCHole loc) ]
 | [ "(" ssrbvar(bv) ")" ] ->
   [ let xloc, _ as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[x],Default Explicit,mkCHole xloc],mkCHole loc) ]
 | [ "(" ssrbvar(bv) ":" lconstr(t) ")" ] ->
   [ let x = bvar_lname bv in
     (FwdPose, [BFdecl 1]),
     CLambdaN (loc, [[x], Default Explicit, t], mkCHole loc) ]
 | [ "(" ssrbvar(bv) ne_ssrbvar_list(bvs) ":" lconstr(t) ")" ] ->
   [ let xs = List.map bvar_lname (bv :: bvs) in
     let n = List.length xs in
     (FwdPose, [BFdecl n]),
     CLambdaN (loc, [xs, Default Explicit, t], mkCHole loc) ]
 | [ "(" ssrbvar(id) ":" lconstr(t) ":=" lconstr(v) ")" ] ->
   [ let loc' = Loc.join_loc (constr_loc t) (constr_loc v) in
     (FwdPose,[BFdef]), CLetIn (loc,bvar_lname id, v,Some t,mkCHole loc) ]
 | [ "(" ssrbvar(id) ":=" lconstr(v) ")" ] ->
   [ (FwdPose,[BFdef]), CLetIn (loc,bvar_lname id, v,None,mkCHole loc) ]
END

GEXTEND Gram
  GLOBAL: ssrbinder;
  ssrbinder: [
  [  ["of" | "&"]; c = operconstr LEVEL "99" ->
     let loc = !@loc in
     (FwdPose, [BFvar]),
     CLambdaN (loc,[[loc,Anonymous],Default Explicit,c],mkCHole loc) ]
  ];
END

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 bs =
  let loc2 = constr_loc c2 in let mkloc loc1 = Loc.join_loc loc1 loc2 in
  let rec loop ty c = function
  | (_, CLambdaN (loc1, b, _)) :: bs when ty ->
      CProdN (mkloc loc1, b, loop ty c bs)
  | (_, CLambdaN (loc1, b, _)) :: bs ->
      CLambdaN (mkloc loc1, b, loop ty c bs)
  | (_, CLetIn (loc1, x, v, oty, _)) :: bs ->
      CLetIn (mkloc loc1, x, v, oty, loop ty c bs)
  | [] -> c
  | _ -> anomaly "binder not a lambda nor a let in" in
  match c2 with
  | CCast (x, ct, CastConv cty) ->
      (CCast (x, loop false ct bs, CastConv (loop true cty bs)))
  | ct -> loop false ct bs

let rec fix_binders = function
  | (_, CLambdaN (_, [xs, _, t], _)) :: bs ->
      CLocalAssum (xs, Default Explicit, t) :: fix_binders bs
  | (_, CLetIn (_, x, v, oty, _)) :: bs ->
    CLocalDef (x, v, oty) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()

ARGUMENT EXTEND ssrstruct TYPED AS ident option PRINTED BY pr_ssrstruct
| [ "{" "struct" ident(id) "}" ] -> [ Some id ]
| [ ] -> [ None ]
END

(** The "pose" tactic *)

(* The plain pose form. *)

let bind_fwd bs = function
  | (fk, h), (ck, (rc, Some c)) ->
    (fk,binders_fmts bs @ h), (ck,(rc,Some (push_binders c bs)))
  | fwd -> fwd

ARGUMENT EXTEND ssrposefwd TYPED AS ssrfwd PRINTED BY pr_ssrfwd
  | [ ssrbinder_list(bs) ssrfwd(fwd) ] -> [ bind_fwd bs fwd ]
END

(* The pose fix form. *)

let pr_ssrfixfwd _ _ _ (id, fwd) = str " fix " ++ pr_id id ++ pr_fwd fwd

let bvar_locid = function
  | CRef (Ident (loc, id), _) -> loc, id
  | _ -> CErrors.error "Missing identifier after \"(co)fix\""


ARGUMENT EXTEND ssrfixfwd TYPED AS ident * ssrfwd PRINTED BY pr_ssrfixfwd
  | [ "fix" ssrbvar(bv) ssrbinder_list(bs) ssrstruct(sid) ssrfwd(fwd) ] ->
    [ let (_, id) as lid = bvar_locid bv in
      let (fk, h), (ck, (rc, oc)) = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop = function
          (l', Name id') :: _ when Option.equal Id.equal sid (Some id') -> true, (l', id')
          | [l', Name id'] when sid = None -> false, (l', id')
          | _ :: bn -> loop bn
          | [] -> CErrors.error "Bad structural argument" in
        loop (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CFix (loc, lid, [lid, (Some i, CStructRec), lb, t', c']) in
      id, ((fk, h'), (ck, (rc, Some fix))) ]
END


(* The pose cofix form. *)

let pr_ssrcofixfwd _ _ _ (id, fwd) = str " cofix " ++ pr_id id ++ pr_fwd fwd

ARGUMENT EXTEND ssrcofixfwd TYPED AS ssrfixfwd PRINTED BY pr_ssrcofixfwd
  | [ "cofix" ssrbvar(bv) ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let _, id as lid = bvar_locid bv in
      let (fk, h), (ck, (rc, oc)) = fwd in
      let c = Option.get oc in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      let cofix = CCoFix (loc, lid, [lid, fix_binders bs, t', c']) in
      id, ((fk, h'), (ck, (rc, Some cofix)))
    ]
END

let guard_setrhs s i = s.[i] = '{'

let pr_setrhs occ prc prlc c =
  if occ = nodocc then pr_guarded guard_setrhs prlc c else pr_docc occ ++ prc c

let pr_fwd_guarded prval prval' = function
| (fk, h), (_, (_, Some c)) ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)
| (fk, h), (_, (c, None)) ->
  pr_gen_fwd prval' pr_glob_constr prl_glob_constr fk (format_glob_constr h c)


(* This does not print the type, it should be fixed... *)
let pr_ssrsetfwd _ _ _ (((fk,_),(t,_)), docc) =
  pr_gen_fwd (fun _ _ -> pr_cpattern)
    (fun _ -> mt()) (fun _ -> mt()) fk ([Bcast ()],t)

ARGUMENT EXTEND ssrsetfwd
TYPED AS (ssrfwdfmt * (lcpattern * ssrterm option)) * ssrdocc
PRINTED BY pr_ssrsetfwd
| [ ":" lconstr(t) ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, mkocc occ ]
| [ ":" lconstr(t) ":=" lcpattern(c) ] ->
  [ mkssrFwdCast FwdPose loc (mk_lterm t) c, nodocc ]
| [ ":=" "{" ssrocc(occ) "}" cpattern(c) ] ->
  [ mkssrFwdVal FwdPose c, mkocc occ ]
| [ ":=" lcpattern(c) ] -> [ mkssrFwdVal FwdPose c, nodocc ]
END


let pr_ssrhavefwd _ _ prt (fwd, hint) = pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwd TYPED AS ssrfwd * ssrhint PRINTED BY pr_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] -> [ mkFwdHint ":" t, hint ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdHave loc t c, nohint ]
| [ ":" lconstr(t) ":=" ] -> [ mkFwdHintNoTC ":" t, nohint ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

let intro_id_to_binder = List.map (function 
  | IpatId id ->
      let xloc, _ as x = bvar_lname (mkCVar dummy_loc id) in
      (FwdPose, [BFvar]),
        CLambdaN (dummy_loc, [[x], Default Explicit, mkCHole xloc],
          mkCHole dummy_loc)
  | _ -> anomaly "non-id accepted as binder")

let binder_to_intro_id = List.map (function
  | (FwdPose, [BFvar]), CLambdaN (_,[ids,_,_],_)
  | (FwdPose, [BFdecl _]), CLambdaN (_,[ids,_,_],_) ->
      List.map (function (_, Name id) -> IpatId id | _ -> IpatAnon) ids
  | (FwdPose, [BFdef]), CLetIn (_,(_,Name id),_,_,_) -> [IpatId id]
  | (FwdPose, [BFdef]), CLetIn (_,(_,Anonymous),_,_,_) -> [IpatAnon]
  | _ -> anomaly "ssrbinder is not a binder")

let pr_ssrhavefwdwbinders _ _ prt (tr,((hpats, (fwd, hint)))) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint prt hint

ARGUMENT EXTEND ssrhavefwdwbinders
  TYPED AS bool * (ssrhpats * (ssrfwd * ssrhint))
  PRINTED BY pr_ssrhavefwdwbinders
| [ ssrhpats_wtransp(trpats) ssrbinder_list(bs) ssrhavefwd(fwd) ] ->
  [ let tr, pats = trpats in
    let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let hint = bind_fwd allbs (fst fwd), snd fwd in
    tr, ((((clr, pats), allbinders), simpl), hint) ]
END


let pr_ssrdoarg prc _ prt (((n, m), tac), clauses) =
  pr_index n ++ pr_mmod m ++ pr_hintarg prt tac ++ pr_clauses clauses

ARGUMENT EXTEND ssrdoarg
  TYPED AS ((ssrindex * ssrmmod) * ssrhintarg) * ssrclauses
  PRINTED BY pr_ssrdoarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

(* type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option) *)

let pr_seqtacarg prt = function
  | (is_first, []), _ -> str (if is_first then "first" else "last")
  | tac, Some dtac ->
    hv 0 (pr_hintarg prt tac ++ spc() ++ str "|| " ++ prt tacltop dtac)
  | tac, _ -> pr_hintarg prt tac

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg prt tac

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrhintarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ "YouShouldNotTypeThis" ] -> [ anomaly "Grammar placeholder match" ]
END

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)
let accept_ssrseqvar strm =
  match stream_nth 0 strm with
  | Tok.IDENT id when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms_or_ids ["["] ["first";"last"] strm
  | _ -> raise Stream.Failure

let test_ssrseqvar = Gram.Entry.of_parser "test_ssrseqvar" accept_ssrseqvar

let swaptacarg (loc, b) = (b, []), Some (TacId [])

let check_seqtacarg dir arg = match snd arg, dir with
  | ((true, []), Some (TacAtom (loc, _))), L2R ->
    loc_error loc (str "expected \"last\"")
  | ((false, []), Some (TacAtom (loc, _))), R2L ->
    loc_error loc (str "expected \"first\"")
  | _, _ -> arg

let ssrorelse = Gram.entry_create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrorelse ssrseqarg;
  ssrseqidx: [
    [ test_ssrseqvar; id = Prim.ident -> ArgVar (!@loc, id)
    | n = Prim.natural -> ArgArg (check_index !@loc n)
    ] ];
  ssrswap: [[ IDENT "first" -> !@loc, true | IDENT "last" -> !@loc, false ]];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ arg = ssrswap -> noindex, swaptacarg arg
    | i = ssrseqidx; tac = ssrortacarg; def = OPT ssrorelse -> i, (tac, def)
    | i = ssrseqidx; arg = ssrswap -> i, swaptacarg arg
    | tac = tactic_expr LEVEL "3" -> noindex, (mk_hint tac, None)
    ] ];
END
(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;


(* vim: set filetype=ocaml foldmethod=marker: *)
