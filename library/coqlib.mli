(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(** This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(** The idea is to migrate to a rebindable name-based approach, the
    main function this FILE provides is:

    [lib_ref : string -> global_reference]

    such that [lib_ref "core.eq.type"] returns the proper
    [global_reference] for the type of the core equality type.

    Contrary to the old approach of raising an anomaly if the
    primitive cannot be found, [lib_ref] will emit `Not_found`, thus
    we expect tactics to gracefully fail in the absence of a
    particular primitive. This allows the ML code to test for the
    presence of a particular primitive.

    [add_ref : string -> global_reference -> unit]
    will (re)bind a reference.

    A feature based approach would be possible too, however this is
    not very uniform with the several variations constructors may
    take.
*)

val lib_ref    : string -> GlobRef.t
val add_ref    : string -> GlobRef.t -> unit

(** Exceptions to deprecation *)

(** {6 For Equality tactics } *)
type coq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t }

val build_sigma_set : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed
val build_sigma : coq_sigma_data delayed

type coq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t }

val build_coq_eq_data : coq_eq_data delayed
val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data : coq_eq_data delayed

(* XXX: Some tactics special case JMeq, they should instead check for
   the constant, not the module *)
(** For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(* Used by toplevel *)
val prelude_module : DirPath.t

(* Used by obligations *)
val datatypes_module_name : string list

(* Used by ind_schemes *)
val logic_module_name : string list

(* Used by tactics *)
val jmeq_module : DirPath.t
val jmeq_module_name : string list


(*************************************************************************)
(* DEPRECATED                                                            *)
(*************************************************************************)

(** All the functions below are deprecated and should go away in the
    next coq version ... *)

(** [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazyly; it raises an anomaly with the given message
   if not found *)
type message = string

(** These should be removed *)
val find_reference : message -> string list -> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** This just prefixes find_reference with Coq... *)
val coq_reference  : message -> string list -> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Search in several modules (not prefixed by "Coq") *)
val gen_reference_in_modules : string->string list list-> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val arith_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val zarith_base_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val init_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 Global references } *)

(** Modules *)
val logic_module : DirPath.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val logic_type_module : DirPath.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Identity  *)
val id : Constant.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val type_of_id : Constant.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Natural numbers *)

val nat_path : Libnames.full_path
(* [@@ocaml.deprecated "Please use Coqlib.lib_ref"] *)

val glob_nat : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_O : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_S : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
(* XXX: Fix syntax plugins. *)
val glob_O : GlobRef.t
(* [@@ocaml.deprecated "Please use Coqlib.lib_ref"] *)
val glob_S : GlobRef.t
(* [@@ocaml.deprecated "Please use Coqlib.lib_ref"] *)

(** Booleans *)
val glob_bool : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val path_of_true : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_false : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_true : GlobRef.t
(* [@@ocaml.deprecated "Please use Coqlib.lib_ref"] *)
val glob_false : GlobRef.t
(* [@@ocaml.deprecated "Please use Coqlib.lib_ref"] *)

(** Equality *)
val glob_eq : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_identity : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_jmeq : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 ... } *)
(** Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   forced with [delayed_force] to get the actual constr or pattern 
   at runtime. *)

type coq_bool_data = {
  andb : GlobRef.t;
  andb_prop : GlobRef.t;
  andb_true_intro : GlobRef.t
}

val build_bool_type : coq_bool_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Non-dependent pairs in Set from Datatypes *)
val build_prod : coq_sigma_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val build_coq_eq       : GlobRef.t delayed (** = [(build_coq_eq_data()).eq] *)
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_eq_refl  : GlobRef.t delayed (** = [(build_coq_eq_data()).refl] *)
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_eq_sym   : GlobRef.t delayed (** = [(build_coq_eq_data()).sym] *)
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_f_equal2 : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Data needed for discriminate and injection *)

type coq_inversion_data = {
  inv_eq   : GlobRef.t; (** : forall params, args -> Prop *)
  inv_ind  : GlobRef.t; (** : forall params P (H : P params) args, eq params args
			 ->  P args *)
  inv_congr: GlobRef.t  (** : forall params B (f:t->B) args, eq params args ->
			 f params = f args *)
}

val build_coq_inversion_eq_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_identity_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_jmeq_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_eq_true_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Specif *)
val build_coq_sumbool : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 ... } *)
(** Connectives 
   The False proposition *)
val build_coq_False : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** The True proposition and its unique proof *)
val build_coq_True : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_I : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Negation *)
val build_coq_not : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Conjunction *)
val build_coq_and : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_conj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_iff : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val build_coq_iff_left_proj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_iff_right_proj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Disjunction *)
val build_coq_or : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Existential quantifier *)
val build_coq_ex : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val coq_eq_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_identity_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_jmeq_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_eq_true_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_existS_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_existT_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_exist_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_not_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_False_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_sumbool_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_sig_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val coq_or_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_iff_ref : GlobRef.t lazy_t
