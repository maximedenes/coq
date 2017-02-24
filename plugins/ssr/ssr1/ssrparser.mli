
open Genarg
open Ssrast
open Names

val ssrtacarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtacarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtacarg : 'a -> 'b -> (int * Ppextend.parenRelation -> 'c) -> 'c

val ssrtclarg : Tacexpr.raw_tactic_expr Pcoq.Gram.entry
val wit_ssrtclarg : (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr, Geninterp.Val.t) Genarg.genarg_type
val pr_ssrtclarg : 'a -> 'b -> (int * Ppextend.parenRelation -> 'c -> 'd) -> 'c -> 'd

(************************* generic argument helpers *********************)
(* FIXME: hide?*)
open Genarg

open Proof_type
open Evd
open Refiner
val add_genarg : string -> ('a -> Pp.std_ppcmds) -> 'a Genarg.uniform_genarg_type
val interp_wit :
  ('a, 'b, 'c) genarg_type -> ist -> goal sigma -> 'b -> evar_map * 'c


(************************** Parsing helpers *********************************)

(* look ahead for specific symbols/ids *)
val accept_before_syms : string list -> Tok.t Stream.t -> unit
val accept_before_syms_or_any_id : string list -> Tok.t Stream.t -> unit
val accept_before_syms_or_ids : string list -> string list -> Tok.t Stream.t -> unit

(* Names of variables to be cleared (automatic check: not a section var) *)
val ssrhyp : ssrhyp Pcoq.Gram.entry
val wit_ssrhyp : ssrhyp uniform_genarg_type
val intern_hyp : gist -> ssrhyp -> ssrhyp
val interp_hyp : ist -> goal sigma -> ssrhyp -> evar_map * ssrhyp

(* Variant of the above *)
val pr_hyp : ssrhyp -> Pp.std_ppcmds
val hyp_err : loc -> string -> Id.t -> 'a
val hyp_id : ssrhyp -> Id.t
val not_section_id : Id.t -> bool
val check_hyp_exists : Context.Named.t -> ssrhyp -> unit
val test_hypname_exists : Context.Named.t -> Id.t -> bool

(* Variant of the above *)
val ssrhoi_id : ssrhyp_or_id Pcoq.Gram.entry
val ssrhoi_hyp : ssrhyp_or_id Pcoq.Gram.entry
val wit_ssrhoi_hyp : ssrhyp_or_id uniform_genarg_type
val wit_ssrhoi_id : ssrhyp_or_id uniform_genarg_type

val pr_hoi : ssrhyp_or_id -> Pp.std_ppcmds
val hoi_id : ssrhyp_or_id -> Id.t

(* Variant of the above *)
val ssrhyps : ssrhyps Pcoq.Gram.entry
val wit_ssrhyps : ssrhyps uniform_genarg_type
val interp_hyps : ist -> goal sigma -> ssrhyps -> evar_map * ssrhyps

val pr_hyps : ssrhyps -> Pp.std_ppcmds
val check_hyps_uniq : Id.t list -> ssrhyps -> unit
val hyps_ids : ssrhyps -> Id.t list

val wit_ssrdir : ssrdir uniform_genarg_type

val pr_dir : ssrdir -> Pp.std_ppcmds
val pr_rwdir : ssrdir -> Pp.std_ppcmds
val dir_org : ssrdir -> int
val pr_dir_side : ssrdir -> Pp.std_ppcmds
val inv_dir : ssrdir -> ssrdir


val ssrsimpl : ssrsimpl Pcoq.Gram.entry
val ssrsimpl_ne : ssrsimpl Pcoq.Gram.entry
val wit_ssrsimpl : ssrsimpl uniform_genarg_type
val wit_ssrsimpl_ne : ssrsimpl uniform_genarg_type

val pr_simpl : ssrsimpl -> Pp.std_ppcmds
val test_not_ssrslashnum : unit Pcoq.Gram.entry (* REMOVE *)

(* index MAYBE REMOVE ONLY INTERNAL stuff between {} *)

val ssrindex : ssrindex Pcoq.Gram.entry
val wit_ssrindex : ssrindex uniform_genarg_type

val pr_index : ssrindex -> Pp.std_ppcmds
val noindex : ssrindex
val mk_index : loc -> ssrindex -> ssrindex
val check_index : loc -> int -> int

(** Occurrence switch {1 2}, all is Some(false,[]) *)
val ssrocc : ssrocc Pcoq.Gram.entry
val wit_ssrocc : ssrocc uniform_genarg_type

val pr_occ : ssrocc -> Pp.std_ppcmds
val allocc : ssrocc

(* modality for rewrite and do: ! ? *)
val ssrmmod : ssrmmod Pcoq.Gram.entry
val wit_ssrmmod : ssrmmod uniform_genarg_type

val pr_mmod : ssrmmod -> Pp.std_ppcmds

(* modality with a bound for rewrite and do: !n ?n *)

val ssrmult : ssrmult Pcoq.Gram.entry
val ssrmult_ne : ssrmult Pcoq.Gram.entry
val wit_ssrmult : ssrmult uniform_genarg_type
val wit_ssrmult_ne : ssrmult uniform_genarg_type

val pr_mult : ssrmult -> Pp.std_ppcmds
val notimes : int
val nomult : ssrmult

(* clear switch {H G} *)

val ssrclear : ssrclear Pcoq.Gram.entry
val ssrclear_ne : ssrclear Pcoq.Gram.entry
val wit_ssrclear : ssrhyps uniform_genarg_type
val wit_ssrclear_ne : ssrhyps uniform_genarg_type

val pr_clear : (unit -> Pp.std_ppcmds) -> ssrclear -> Pp.std_ppcmds
val pr_clear_ne : ssrclear -> Pp.std_ppcmds


(* Discharge occ switch (combined occurrence / clear switch) *)
val ssrdocc : ssrdocc Pcoq.Gram.entry
val wit_ssrdocc : ssrdocc uniform_genarg_type

val pr_docc : ssrdocc -> Pp.std_ppcmds
val mkocc : ssrocc -> ssrdocc
val noclr : ssrdocc
val mkclr : ssrclear -> ssrdocc
val nodocc : ssrdocc

(* terms are pre constr, the kind is parsing/printing flag to distinguish
 * between x, @x and (x). It affects automatic clear and let-in preservation.
 * Cpattern is a temporary flag that becomes InParens ASAP. *)
(* type ssrtermkind = InParens | WithAt | NoFlag | Cpattern *)
 val xInParens : char
 val xWithAt : char
 val xNoFlag : char
 val xCpattern : char

val ssrtermkind : ssrtermkind Pcoq.Gram.entry


val ssrterm : ssrterm Pcoq.Gram.entry
val wit_ssrterm : ssrterm uniform_genarg_type

val pr_paren : ('a -> Pp.std_ppcmds) -> 'a -> Pp.std_ppcmds

val pr_term : ssrterm -> Pp.std_ppcmds
val prl_term : ssrterm -> Pp.std_ppcmds
val prl_glob_constr : Glob_term.glob_constr -> Pp.std_ppcmds
val pr_guarded :
  (string -> int -> bool) -> ('a -> Pp.std_ppcmds) -> 'a -> Pp.std_ppcmds
val guard_term : ssrtermkind -> string -> int -> bool
val glob_constr :
  Tacinterp.interp_sign -> Environ.env ->
    Tacexpr.glob_constr_and_expr -> Glob_term.glob_constr
val interp_open_constr : 
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    Tacexpr.glob_constr_and_expr -> Evd.evar_map * Evd.open_constr
val intern_term : 
  Tacinterp.interp_sign -> Environ.env ->
    ssrterm -> Glob_term.glob_constr
val pf_intern_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Glob_term.glob_constr
val interp_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Evd.open_constr
val force_term :
  Tacinterp.interp_sign -> Proof_type.goal Tacmach.sigma ->
    ssrterm -> Evd.open_constr
val subst_ssrterm : Mod_subst.substitution -> ssrterm -> ssrterm
val glob_ssrterm : Tacintern.glob_sign -> ssrterm -> ssrterm
val mk_term : ssrtermkind -> Constrexpr.constr_expr -> ssrterm
val mk_lterm : Constrexpr.constr_expr -> ssrterm

val mkRHole : Glob_term.glob_constr

(* views *)


val ssrview : ssrview Pcoq.Gram.entry
val wit_ssrview : ssrview uniform_genarg_type

val pr_view : ssrview -> Pp.std_ppcmds

(* Extended intro patterns: foo /bar[ H | -> ] and company *)

val ssrintros : ssripats Pcoq.Gram.entry
val ssrintros_ne : ssripats Pcoq.Gram.entry
val ssrrpat : ssripat Pcoq.Gram.entry
val ssrhpats : ssrhpats Pcoq.Gram.entry
val ssrhpats_wtransp : ssrhpats_wtransp Pcoq.Gram.entry
val ssrhpats_nobs : ssrhpats Pcoq.Gram.entry

val wit_ssripatrep : ssripat uniform_genarg_type (* FIXME *)
val wit_ssrintros : ssripats uniform_genarg_type
val wit_ssrintros_ne : ssripats uniform_genarg_type
val wit_ssrrpat : ssripat uniform_genarg_type
val wit_ssrhpats : ssrhpats uniform_genarg_type
val wit_ssrhpats_wtransp : ssrhpats_wtransp uniform_genarg_type
val wit_ssrhpats_nobs : ssrhpats uniform_genarg_type

val pr_ipat : ssripat -> Pp.std_ppcmds
val pr_ipats : ssripats -> Pp.std_ppcmds
val pr_intros : (unit -> Pp.std_ppcmds) -> ssripats -> Pp.std_ppcmds
val pr_hpats : ssrhpats -> Pp.std_ppcmds

val ssrintrosarg : ssrintrosarg Pcoq.Gram.entry
val wit_ssrintrosarg :
           (Tacexpr.raw_tactic_expr * Ssrast.ssripats,
            Tacexpr.glob_tactic_expr * Ssrast.ssripats,
            Geninterp.Val.t * Ssrast.ssripats)
  Genarg.genarg_type
val pr_ssrintrosarg : 
           'a ->
           'b ->
           (int * Ppextend.parenRelation -> Tacexpr.raw_tactic_expr -> Pp.std_ppcmds) ->
           ssrintrosarg -> Pp.std_ppcmds





val ssrfwdid : ssrfwdid Pcoq.Gram.entry
val wit_ssrfwdid : ssrfwdid uniform_genarg_type
val pr_ssrfwdid : ssrfwdid -> Pp.std_ppcmds

val wit_ssrfwdfmt : ssrfwdfmt uniform_genarg_type

val ssrfwd : (ssrfwdfmt * ssrterm) Pcoq.Gram.entry
val wit_ssrfwd : (ssrfwdfmt * ssrterm) uniform_genarg_type
val pr_fwd : ssrfwdfmt * ssrterm -> Pp.std_ppcmds

val ssrfixfwd : (Id.t * (ssrfwdfmt * ssrterm)) Pcoq.Gram.entry
val wit_ssrfixfwd : (Id.t * (ssrfwdfmt * ssrterm)) uniform_genarg_type
val ssrcofixfwd : (Id.t * (ssrfwdfmt * ssrterm)) Pcoq.Gram.entry
val wit_ssrcofixfwd : (Id.t * (ssrfwdfmt * ssrterm)) uniform_genarg_type
val ssrposefwd : (ssrfwdfmt * ssrterm) Pcoq.Gram.entry
val wit_ssrposefwd : (ssrfwdfmt * ssrterm) uniform_genarg_type
val ssrsetfwd : ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ssrterm option)) * ssrdocc) Pcoq.Gram.entry
val wit_ssrsetfwd : ((ssrfwdfmt * (Ssrmatching_plugin.Ssrmatching.cpattern * ssrterm option)) * ssrdocc) uniform_genarg_type

val ssrhintarg : Tacexpr.raw_tactic_expr ssrhint Pcoq.Gram.entry
val wit_ssrhintarg :
           (Tacexpr.raw_tactic_expr ssrhint,
            Tacexpr.glob_tactic_expr ssrhint,
            Geninterp.Val.t ssrhint)
           Genarg.genarg_type
val pr_hintarg :
           (int * Ppextend.parenRelation -> 'a -> Pp.std_ppcmds) ->
           'a ssrhint -> Pp.std_ppcmds

val ssrhint : Tacexpr.raw_tactic_expr ssrhint Pcoq.Gram.entry
val wit_ssrhint :
           (Tacexpr.raw_tactic_expr ssrhint,
            Tacexpr.glob_tactic_expr ssrhint,
            Geninterp.Val.t ssrhint)
           Genarg.genarg_type
val pr_hint :
           (int * Ppextend.parenRelation -> 'a -> Pp.std_ppcmds) ->
           'a ssrhint -> Pp.std_ppcmds
val mk_hint : 'a -> 'a ssrhint 
val nohint : 'a ssrhint

val ssrclauses : clauses Pcoq.Gram.entry
val wit_ssrclauses : clauses uniform_genarg_type
val pr_clauses : clauses -> Pp.std_ppcmds

val ssrortacarg: Tacexpr.raw_tactic_expr ssrhint Pcoq.Gram.entry
val wit_ssrortacarg:
           (Tacexpr.raw_tactic_expr ssrhint,
            Tacexpr.glob_tactic_expr ssrhint,
            Geninterp.Val.t ssrhint)
        Genarg.genarg_type

val ssrhavefwdwbinders : Tacexpr.raw_tactic_expr fwdbinders Pcoq.Gram.entry
val wit_ssrhavefwdwbinders :
           (Tacexpr.raw_tactic_expr fwdbinders,
            Tacexpr.glob_tactic_expr fwdbinders,
            Geninterp.Val.t fwdbinders)
        Genarg.genarg_type
       
val wit_ssrhavefwd : 
  ((ssrfwdfmt * ssrterm) * Tacexpr.raw_tactic_expr ssrhint,
   (ssrfwdfmt * ssrterm) * Tacexpr.glob_tactic_expr ssrhint,
   (ssrfwdfmt * ssrterm) * Geninterp.Val.t ssrhint)
        Genarg.genarg_type
val ssrhavefwd : ((ssrfwdfmt * ssrterm) * Tacexpr.raw_tactic_expr ssrhint) Pcoq.Gram.entry

val ssrbinder : (ssrfwdfmt * Constrexpr.constr_expr) Pcoq.Gram.entry
val wit_ssrbinder :
   (Ssrast.ssrfwdfmt * Constrexpr.constr_expr,
            Ssrast.ssrfwdfmt * Tactypes.glob_constr_and_expr,
            Ssrast.ssrfwdfmt * Term.constr)
           Genarg.genarg_type
val intro_id_to_binder : ssripats -> (ssrfwdfmt * Constrexpr.constr_expr) list
val binder_to_intro_id : (ssrfwdfmt * Constrexpr.constr_expr) list -> ssripatss
val mkFwdHint :
           string ->
           Constrexpr.constr_expr -> ssrfwdfmt * ssrterm

val bind_fwd :
           (('a * 'b list) * Constrexpr.constr_expr) list ->
           ('c * 'b list) * ('d * ('e * Constrexpr.constr_expr option)) ->
           ('c * 'b list) * ('d * ('e * Constrexpr.constr_expr option))


val ssrwgen : wgen Pcoq.Gram.entry
val wit_ssrwgen : wgen uniform_genarg_type
val pr_wgen : wgen -> Pp.std_ppcmds

val ssrdoarg : Tacexpr.raw_tactic_expr ssrdoarg Pcoq.Gram.entry
val wit_ssrdoarg : (Tacexpr.raw_tactic_expr ssrdoarg, Tacexpr.glob_tactic_expr ssrdoarg, Geninterp.Val.t ssrdoarg) Genarg.genarg_type
val pr_ssrdoarg : 'x -> 'b ->
  (int * Ppextend.parenRelation -> 'a -> Pp.std_ppcmds) ->
 'a ssrdoarg -> Pp.std_ppcmds

val ssrseqarg : Tacexpr.raw_tactic_expr ssrseqarg Pcoq.Gram.entry
val wit_ssrseqarg : (Tacexpr.raw_tactic_expr ssrseqarg, Tacexpr.glob_tactic_expr ssrseqarg, Geninterp.Val.t ssrseqarg) Genarg.genarg_type
val pr_ssrseqarg : 'x -> 'y ->
  (int * Ppextend.parenRelation -> 'a -> Pp.std_ppcmds) ->
   'a ssrseqarg -> Pp.std_ppcmds
val check_seqtacarg : ssrdir -> Tacexpr.raw_tactic_expr ssrseqarg -> Tacexpr.raw_tactic_expr ssrseqarg 

val ssrorelse : Tacexpr.raw_tactic_expr Pcoq.Gram.entry

(* OOP *)
val interp_open_constr :
           Tacinterp.interp_sign ->
           Proof_type.goal Tacmach.sigma ->
           Tacexpr.glob_constr_and_expr ->
           Evd.evar_map * (Evd.evar_map * Term.constr)


val tclintros_expr :
           Loc.t ->
           Tacexpr.raw_tactic_expr ->
           Ssrast.ssripats ->
           Tacexpr.raw_tactic_expr

