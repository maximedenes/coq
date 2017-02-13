(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

open Names
open Ssrast
(******************************** misc ************************************)

val pr_id : Id.t -> Pp.std_ppcmds
val pr_name : Name.t -> Pp.std_ppcmds
val pr_spc : unit -> Pp.std_ppcmds
val pr_bar : unit -> Pp.std_ppcmds
val pr_list : 
  (unit -> Pp.std_ppcmds) -> ('a -> Pp.std_ppcmds) -> 'a list -> Pp.std_ppcmds
val dummy_loc : loc
val errorstrm : Pp.std_ppcmds -> 'a
val loc_error : loc -> Pp.std_ppcmds -> 'a
val anomaly : string -> 'a

val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b

(**************************** lifted tactics ******************************)
open Proof_type
open Evd
open Refiner

(* tactics with extra data attached to each goals, e.g. the list of
 * temporary variables to be cleared *)
type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

(* Thread around names to be cleared or generalized back, and the speed *)
type tac_ctx = {
  tmp_ids : (Id.t * name ref) list;
  wild_ids : Id.t list;
  (* List of variables to be cleared at the end of the sentence *)
  delayed_clears : Id.t list;
  (* Intro mode: name every item v.s. name every non-dependent-product item *)
  speed : [ `Slow | `Fast ]
}

val new_ctx : unit -> tac_ctx (* REMOVE *)
val pull_ctxs : ('a * tac_ctx) list  sigma -> 'a list sigma * tac_ctx list (* REMOVE *)

val with_fresh_ctx : tac_ctx tac_a -> tactic

val pull_ctx : ('a * tac_ctx) sigma -> 'a sigma * tac_ctx
val push_ctx : tac_ctx -> 'a sigma -> ('a * tac_ctx) sigma
val push_ctxs : tac_ctx -> 'a list sigma -> ('a * tac_ctx) list sigma
val tac_ctx : tactic -> tac_ctx tac_a
val with_ctx :
  (tac_ctx -> 'b * tac_ctx) -> ('a * tac_ctx) sigma -> 'b * ('a * tac_ctx) sigma
val without_ctx : ('a sigma -> 'b) -> ('a * tac_ctx) sigma -> 'b

(* Standard tacticals lifted to the tac_a type *)
val tclTHENLIST_a : tac_ctx tac_a list -> tac_ctx tac_a
val tclTHEN_i_max :
  tac_ctx tac_a -> (int -> int -> tac_ctx tac_a) -> tac_ctx tac_a
val tclTHEN_a : tac_ctx tac_a -> tac_ctx tac_a -> tac_ctx tac_a
val tclTHENS_a : tac_ctx tac_a -> tac_ctx tac_a list -> tac_ctx tac_a

val tac_on_all :
  (goal * tac_ctx) list sigma -> tac_ctx tac_a -> (goal * tac_ctx) list sigma
(************************ ssr tactic arguments ******************************)
open Genarg
open Ssrparser


(*********************** Misc helpers *****************************)

val mkRHoles : int -> Glob_term.glob_constr list
val isRHoles : Glob_term.glob_constr list -> bool
val mkRApp : Glob_term.glob_constr -> Glob_term.glob_constr list -> Glob_term.glob_constr
val mkRVar : Id.t -> Glob_term.glob_constr
val mkRltacVar : Id.t -> Glob_term.glob_constr
val mkRCast : Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr
val mkRType : Glob_term.glob_constr
val mkRProp : Glob_term.glob_constr
val mkRArrow : Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr
val mkRConstruct : Names.constructor -> Glob_term.glob_constr
val mkRInd : Names.inductive -> Glob_term.glob_constr
val mkRLambda : Name.t -> Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr

val splay_open_constr : 
           Proof_type.goal Tacmach.sigma ->
           Evd.evar_map * Term.constr ->
           (Names.Name.t * Term.constr) list * Term.constr
val isAppInd : Proof_type.goal Tacmach.sigma -> Term.types -> bool
val interp_view_nbimps :
           Tacinterp.interp_sign ->
           Proof_type.goal Evd.sigma -> Glob_term.glob_constr -> int
val interp_nbargs :
           Tacinterp.interp_sign ->
           Proof_type.goal Evd.sigma -> Glob_term.glob_constr -> int

val is_internal_name : string -> bool
val add_internal_name : (string -> bool) -> unit
val mk_internal_id : string -> Id.t
val mk_tagged_id : string -> int -> Id.t
val mk_evar_name : int -> Name.t
val ssr_anon_hyp : string
val pf_type_id :  Proof_type.goal Evd.sigma -> Term.types -> Id.t

val pf_abs_evars : 
           Proof_type.goal Evd.sigma ->
           Evd.evar_map * Term.constr ->
           int * Term.constr * Constr.existential_key list *
           Evd.evar_universe_context
val pf_abs_cterm :
           Proof_type.goal Evd.sigma -> int -> Term.constr -> Term.constr

val pf_merge_uc :
           Evd.evar_universe_context -> 'a Tacmach.sigma -> 'a Tacmach.sigma
val pf_merge_uc_of :
           Evd.evar_map -> 'a Evd.sigma -> 'a Tacmach.sigma
val constr_name : Term.constr -> Name.t
val pf_type_of :
           Proof_type.goal Tacmach.sigma ->
           Term.constr -> Proof_type.goal Tacmach.sigma * Term.types
val pf_abs_prod :
           Names.name ->
           Proof_type.goal Tacmach.sigma ->
           Term.constr ->
           Term.constr -> Proof_type.goal Tacmach.sigma * Term.types
val pf_mkprod :
           Proof_type.goal Tacmach.sigma ->
           Term.constr ->
           ?name:Names.name ->
           Constr.constr -> Proof_type.goal Tacmach.sigma * Term.types

val mkSsrRRef : string -> Glob_term.glob_constr * 'a option
val mkSsrRef : string -> Globnames.global_reference
val mkSsrConst : 
           string ->
           Environ.env -> 'a Sigma.t -> (Constr.constr, 'a) Sigma.sigma
val pf_mkSsrConst :
           string ->
           Proof_type.goal Evd.sigma ->
           Constr.constr * Proof_type.goal Tacmach.sigma
val new_wild_id : tac_ctx -> Names.identifier * tac_ctx


val pf_fresh_global :
           Globnames.global_reference ->
           Proof_type.goal Evd.sigma ->
           Term.constr * Proof_type.goal Tacmach.sigma

val is_discharged_id : Id.t -> bool
val mk_discharged_id : Id.t -> Id.t
val is_tagged : string -> string -> bool
val has_discharged_tag : string -> bool
val ssrqid : string -> Libnames.qualid 
val new_tmp_id :
  tac_ctx -> (Names.identifier * Names.name ref) * tac_ctx
val mk_anon_id : string -> Proof_type.goal Tacmach.sigma -> Id.t
val pf_abs_evars_pirrel :
           Proof_type.goal Evd.sigma ->
           Evd.evar_map * Term.constr -> int * Term.constr
val pf_nbargs : Proof_type.goal Evd.sigma -> Term.constr -> int
val gen_tmp_ids : 
           ?ist:Geninterp.interp_sign ->
           (Proof_type.goal * tac_ctx) Evd.sigma ->
           (Proof_type.goal * tac_ctx) list Tacmach.sigma

val ssrevaltac : Tacinterp.interp_sign -> Tacinterp.Value.t -> Proofview.V82.tac

val convert_concl_no_check : Constr.t -> unit Proofview.tactic
val convert_concl : Constr.t -> unit Proofview.tactic
val ssrautoprop_tac :
           (Constr.existential_key Evd.sigma -> Constr.existential_key list Evd.sigma) ref
val mkEtaApp : Constr.t -> int -> int -> Constr.t
val discharge_hyp :
           Names.Id.t * (Names.Id.t * string) ->
           Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma

val clear_wilds_and_tmp_and_delayed_ids :
           (Proof_type.goal * tac_ctx) Evd.sigma ->
           (Proof_type.goal * tac_ctx) list Tacmach.sigma

val view_error : string -> ssrterm -> 'a


val top_id : Id.t

val pf_abs_ssrterm :
           ?resolve_typeclasses:bool ->
           ist ->
           Proof_type.goal Tacmach.sigma ->
           ssrterm ->
           Evd.evar_map * Term.constr * Evd.evar_universe_context * int

val pf_interp_ty :
           ?resolve_typeclasses:bool ->
           Tacinterp.interp_sign ->
           Proof_type.goal Tacmach.sigma ->
           Ssrast.ssrtermkind *
           (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
           int * Term.constr * Term.constr * Evd.evar_universe_context

val ssr_n_tac : string -> int -> v82tac
val donetac : int -> v82tac

val applyn :
           with_evars:bool ->
           ?beta:bool ->
           ?with_shelve:bool ->
           int ->
           Term.constr -> v82tac
exception NotEnoughProducts
val pf_saturate :
           ?beta:bool ->
           ?bi_types:bool ->
           Proof_type.goal Evd.sigma ->
           Term.constr ->
           ?ty:Term.types ->
           int ->
           Term.constr * Term.types * (int * Term.constr) list *
           Proof_type.goal Tacmach.sigma
val saturate :
           ?beta:bool ->
           ?bi_types:bool ->
           Environ.env ->
           Evd.evar_map ->
           Term.constr ->
           ?ty:Term.types ->
           int ->
           Term.constr * Term.types * (int * Term.constr) list * Evd.evar_map
val refine_with :
           ?first_goes_last:bool ->
           ?beta:bool ->
           ?with_evars:bool ->
           Evd.evar_map * Term.constr -> v82tac
(*********************** Wrapped Coq  tactics *****************************)

val rewritetac : ssrdir -> Constr.t -> tactic

(***** Hooks to break recursive deps among tactics ************************)

type name_hint = (int * Constr.types array) option ref
type simplest_newcase = ?ind:name_hint -> Constr.t -> tactic
val simplest_newcase : simplest_newcase Hook.t
val simplest_newcase_tac : simplest_newcase Hook.value

type simplest_newcase_or_inj = ?ind:name_hint -> force_inj:bool -> Constr.t -> v82tac
val simplest_newcase_or_inj : simplest_newcase_or_inj Hook.t
val simplest_newcase_or_inj_tac : simplest_newcase_or_inj Hook.value

type ipat_rewrite = ssrocc -> ssrdir -> Constr.t -> tactic
val ipat_rewrite : ipat_rewrite Hook.t
val ipat_rewrite_tac : ipat_rewrite Hook.value

type move_top_with_view =
  next:ssripats ref -> bool -> Id.t ref -> bool * ssrterm list -> ist ->
    tac_ctx tac_a
val move_top_with_view : move_top_with_view Hook.t
val move_top_with_view_tac : move_top_with_view Hook.value

val simpl : (ssrsimpl -> tactic) Hook.t
val simpltac : (ssrsimpl -> tactic) Hook.value

val gen : 
           (Geninterp.interp_sign ->
            (Ssrast.ssrdocc) *
            Ssrmatching_plugin.Ssrmatching.cpattern -> Proof_type.tactic)
 Hook.t
val gentac : 
           (Geninterp.interp_sign ->
            (Ssrast.ssrdocc) *
            Ssrmatching_plugin.Ssrmatching.cpattern -> Proof_type.tactic)

 Hook.value
val is_name_in_ipats :
           Id.t -> ssripats -> bool

type with_dgens = (Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list list *
Ssrast.ssrclear ->
((Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern) list ->
 Ssrast.ssrdocc * Ssrmatching_plugin.Ssrmatching.cpattern ->
 Tacinterp.interp_sign -> Proof_type.tactic) ->
Tacinterp.interp_sign -> Proof_type.tactic
val with_dgens_hook : with_dgens Hook.t
val with_dgens : with_dgens Hook.value

(*
TODO:
move_top_with_view
gentac_ref
tclEQINTROSviewtac_ref
*)


