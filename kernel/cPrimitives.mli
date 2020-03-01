(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  | Int63head0
  | Int63tail0
  | Int63add
  | Int63sub
  | Int63mul
  | Int63div
  | Int63mod
  | Int63lsr
  | Int63lsl
  | Int63land
  | Int63lor
  | Int63lxor
  | Int63addc
  | Int63subc
  | Int63addCarryC
  | Int63subCarryC
  | Int63mulc
  | Int63diveucl
  | Int63div21
  | Int63addMulDiv
  | Int63eq
  | Int63lt
  | Int63le
  | Int63compare
  | Float64opp
  | Float64abs
  | Float64eq
  | Float64lt
  | Float64le
  | Float64compare
  | Float64classify
  | Float64add
  | Float64sub
  | Float64mul
  | Float64div
  | Float64sqrt
  | Float64ofInt63
  | Float64normfr_mantissa
  | Float64frshiftexp
  | Float64ldshiftexp
  | Float64next_up
  | Float64next_down
  | Arraymake
  | Arrayget
  | Arraydefault
  | Arrayset
  | Arraycopy
  | Arrayreroot
  | Arraylength
  | Arrayinit
  | Arraymap
  | Arraymaxlength

val equal : t -> t -> bool

type arg_kind =
  | Kparam (* not needed for the elavuation of the primitive*)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf *)

type args_red = arg_kind list

val hash : t -> int

val to_string : t -> string

val arity : t -> int
val nparams : t -> int

val kind : t -> args_red

(** Special Entries for Register **)

type 'a prim_type =
  | PT_int63 : unit prim_type
  | PT_float64 : unit prim_type
  | PT_array : ind_or_type prim_type

and 'a prim_ind =
  | PIT_bool : unit prim_ind
  | PIT_carry : ind_or_type prim_ind
  | PIT_pair : (ind_or_type * ind_or_type) prim_ind
  | PIT_cmp : unit prim_ind
  | PIT_f_cmp : unit prim_ind
  | PIT_f_class : unit prim_ind

and ind_or_type =
  | PITT_ind : 'a prim_ind * 'a -> ind_or_type
  | PITT_type : 'a prim_type * 'a -> ind_or_type
  | PITT_param : int -> ind_or_type (* DeBruijn index referring to prenex type quantifiers *)

type prim_type_ex = PTE : 'a prim_type -> prim_type_ex

type prim_ind_ex = PIE : 'a prim_ind -> prim_ind_ex

type op_or_type =
  | OT_op of t
  | OT_type : 'a prim_type -> op_or_type

val prim_ind_to_string : 'a prim_ind -> string
val op_or_type_to_string : op_or_type -> string

val types : t -> int * ind_or_type list list
