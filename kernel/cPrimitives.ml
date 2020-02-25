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
  | Arraydestrset
  | Arraycopy
  | Arrayreroot
  | Arraylength
  | Arrayinit
  | Arraymap
  | Arraymaxlength

let equal (p1 : t) (p2 : t) =
  p1 == p2

let hash = function
  | Int63head0 -> 1
  | Int63tail0 -> 2
  | Int63add -> 3
  | Int63sub -> 4
  | Int63mul -> 5
  | Int63div -> 6
  | Int63mod -> 7
  | Int63lsr -> 8
  | Int63lsl -> 9
  | Int63land -> 10
  | Int63lor -> 11
  | Int63lxor -> 12
  | Int63addc -> 13
  | Int63subc -> 14
  | Int63addCarryC -> 15
  | Int63subCarryC -> 16
  | Int63mulc -> 17
  | Int63diveucl -> 18
  | Int63div21 -> 19
  | Int63addMulDiv -> 20
  | Int63eq -> 21
  | Int63lt -> 22
  | Int63le -> 23
  | Int63compare -> 24
  | Float64opp -> 25
  | Float64abs -> 26
  | Float64compare -> 27
  | Float64classify -> 28
  | Float64add -> 29
  | Float64sub -> 30
  | Float64mul -> 31
  | Float64div -> 32
  | Float64sqrt -> 33
  | Float64ofInt63 -> 34
  | Float64normfr_mantissa -> 35
  | Float64frshiftexp -> 36
  | Float64ldshiftexp -> 37
  | Float64next_up -> 38
  | Float64next_down -> 39
  | Float64eq -> 40
  | Float64lt -> 41
  | Float64le -> 42
  | Arraymake -> 43
  | Arrayget -> 44
  | Arraydefault -> 45
  | Arrayset -> 46
  | Arraydestrset -> 47
  | Arraycopy -> 48
  | Arrayreroot -> 49
  | Arraylength -> 50
  | Arrayinit -> 51
  | Arraymap -> 52
  | Arraymaxlength -> 53

(* Should match names in nativevalues.ml *)
let to_string = function
  | Int63head0 -> "head0"
  | Int63tail0 -> "tail0"
  | Int63add -> "add"
  | Int63sub -> "sub"
  | Int63mul -> "mul"
  | Int63div -> "div"
  | Int63mod -> "rem"
  | Int63lsr -> "l_sr"
  | Int63lsl -> "l_sl"
  | Int63land -> "l_and"
  | Int63lor -> "l_or"
  | Int63lxor -> "l_xor"
  | Int63addc -> "addc"
  | Int63subc -> "subc"
  | Int63addCarryC -> "addCarryC"
  | Int63subCarryC -> "subCarryC"
  | Int63mulc -> "mulc"
  | Int63diveucl -> "diveucl"
  | Int63div21 -> "div21"
  | Int63addMulDiv -> "addMulDiv"
  | Int63eq -> "eq"
  | Int63lt -> "lt"
  | Int63le -> "le"
  | Int63compare -> "compare"
  | Float64opp -> "fopp"
  | Float64abs -> "fabs"
  | Float64eq -> "feq"
  | Float64lt -> "flt"
  | Float64le -> "fle"
  | Float64compare -> "fcompare"
  | Float64classify -> "fclassify"
  | Float64add -> "fadd"
  | Float64sub -> "fsub"
  | Float64mul -> "fmul"
  | Float64div -> "fdiv"
  | Float64sqrt -> "fsqrt"
  | Float64ofInt63 -> "float_of_int"
  | Float64normfr_mantissa -> "normfr_mantissa"
  | Float64frshiftexp -> "frshiftexp"
  | Float64ldshiftexp -> "ldshiftexp"
  | Float64next_up    -> "next_up"
  | Float64next_down  -> "next_down"
  | Arraymake -> "arraymake"
  | Arrayget -> "arrayget"
  | Arraydefault -> "arraydefault"
  | Arrayset -> "arrayset"
  | Arraydestrset -> "arraydestr_set"
  | Arraycopy -> "arraycopy"
  | Arrayreroot -> "arrayreroot"
  | Arraylength -> "arraylength"
  | Arrayinit -> "arrayinit"
  | Arraymap -> "arraymap"
  | Arraymaxlength -> "arraymaxlength"

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

let types =
  let int_ty = PITT_type (PT_int63, ()) in
  let float_ty = PITT_type (PT_float64, ()) in
  let array_ty a = PITT_type (PT_array, a) in
  function
  | Int63head0 | Int63tail0 -> 0, [[int_ty]; [int_ty]]
  | Int63add | Int63sub | Int63mul
  | Int63div | Int63mod
  | Int63lsr | Int63lsl
  | Int63land | Int63lor | Int63lxor -> 0, [[int_ty]; [int_ty]; [int_ty]]
  | Int63addc | Int63subc | Int63addCarryC | Int63subCarryC ->
     0, [[int_ty]; [int_ty]; [PITT_ind (PIT_carry, int_ty)]]
  | Int63mulc | Int63diveucl ->
     0, [[int_ty]; [int_ty]; [PITT_ind (PIT_pair, (int_ty, int_ty))]]
  | Int63eq | Int63lt | Int63le -> 0, [[int_ty]; [int_ty]; [PITT_ind (PIT_bool, ())]]
  | Int63compare -> 0, [[int_ty]; [int_ty]; [PITT_ind (PIT_cmp, ())]]
  | Int63div21 ->
     0, [[int_ty]; [int_ty]; [int_ty]; [PITT_ind (PIT_pair, (int_ty, int_ty))]]
  | Int63addMulDiv -> 0, [[int_ty]; [int_ty]; [int_ty]; [int_ty]]
  | Float64opp | Float64abs | Float64sqrt
  | Float64next_up | Float64next_down -> 0, [[float_ty]; [float_ty]]
  | Float64ofInt63 -> 0, [[int_ty]; [float_ty]]
  | Float64normfr_mantissa -> 0, [[float_ty]; [int_ty]]
  | Float64frshiftexp -> 0, [[float_ty]; [PITT_ind (PIT_pair, (float_ty, int_ty))]]
  | Float64eq | Float64lt | Float64le -> 0, [[float_ty]; [float_ty]; [PITT_ind (PIT_bool, ())]]
  | Float64compare -> 0, [[float_ty]; [float_ty]; [PITT_ind (PIT_f_cmp, ())]]
  | Float64classify -> 0, [[float_ty]; [PITT_ind (PIT_f_class, ())]]
  | Float64add | Float64sub | Float64mul
  | Float64div -> 0, [[float_ty]; [float_ty]; [float_ty]]
  | Float64ldshiftexp -> 0, [[float_ty]; [int_ty]; [float_ty]]
  | Arraymake -> 1, [[int_ty]; [PITT_param 1]; [array_ty (PITT_param 1)]]
  | Arrayget -> 1, [[array_ty (PITT_param 1)]; [int_ty]; [PITT_param 1]]
  | Arraydefault -> 1, [[array_ty (PITT_param 1)]; [PITT_param 1]]
  | Arrayset -> 1, [[array_ty (PITT_param 1)]; [int_ty]; [PITT_param 1]; [array_ty (PITT_param 1)]]
  | Arraydestrset -> assert false (* FIXME *)
  | Arraycopy -> 1, [[array_ty (PITT_param 1)]; [array_ty (PITT_param 1)]]
  | Arrayreroot -> 1, [[array_ty (PITT_param 1)]; [array_ty (PITT_param 1)]]
  | Arraylength -> 1, [[array_ty (PITT_param 1)]; [int_ty]]
  | Arrayinit -> 1, [[int_ty];[int_ty;PITT_param 1];[PITT_param 1];[array_ty (PITT_param 1)]]
  | Arraymap -> 2, [[PITT_param 1;PITT_param 2];[array_ty (PITT_param 1)];[array_ty (PITT_param 2)]]
  | Arraymaxlength -> 0, [[int_ty]]

type arg_kind =
  | Kparam (* not needed for the evaluation of the primitive when it reduces *)
  | Kwhnf  (* need to be reduced in whnf before reducing the primitive *)
  | Karg   (* no need to be reduced in whnf. example: [v] in [Array.set t i v] *)

type args_red = arg_kind list

(* Invariant only argument of type int63, float or an inductive can
   have kind Kwhnf *)

let arity t = let (nparams, sign) = types t in nparams + List.length sign - 1
let nparams t = fst (types t)

let kind t =
  let rec params n = if n <= 0 then [] else Kparam :: params (n - 1) in
  let args = function [PITT_type _] | [PITT_ind _] -> Kwhnf | _ -> Karg in
  let nparams, sign = types t in
  params nparams @ List.map args (CList.drop_last sign)

(** Special Entries for Register **)

type op_or_type =
  | OT_op of t
  | OT_type : 'a prim_type -> op_or_type

let prim_ind_to_string (type a) (p : a prim_ind) = match p with
  | PIT_bool -> "bool"
  | PIT_carry -> "carry"
  | PIT_pair -> "pair"
  | PIT_cmp -> "cmp"
  | PIT_f_cmp -> "f_cmp"
  | PIT_f_class -> "f_class"

let prim_type_to_string (type a) (ty : a prim_type) = match ty with
  | PT_int63 -> "int63_type"
  | PT_float64 -> "float64_type"
  | PT_array -> "array_type" (* FIXME *)

let op_or_type_to_string = function
  | OT_op op -> to_string op
  | OT_type t -> prim_type_to_string t
