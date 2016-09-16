open Names
open Cbytecodes

type reloc_info =
  | Reloc_annot of annot_switch
  | Reloc_const of structured_constant
  | Reloc_getglobal of constant

type patch = reloc_info * int

type emitcodes

val length : emitcodes -> int

val patch_int : emitcodes -> ((*pos*)int * int) list -> emitcodes

type to_patch = emitcodes * (patch list) * fv

type body_code =
  | BCdefined of to_patch
  | BCalias of constant
  | BCconstant

type to_patch_substituted

val from_val : body_code -> to_patch_substituted

val force : to_patch_substituted -> body_code

val subst_to_patch_subst : Mod_subst.substitution -> to_patch_substituted -> to_patch_substituted

val to_memory : bytecodes * bytecodes * fv -> to_patch
               (** init code, fun code, fv *)
