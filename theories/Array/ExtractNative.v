Require Import Extraction.
Require Import Int63.
Require Import PArray.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive comparison => "ExtrNative.comparison" ["ExtrNative.Eq" "ExtrNative.Lt" "ExtrNative.Gt"].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive carry => "ExtrNative.carry" ["ExtrNative.C0" "ExtrNative.C1"].

Extract Constant int => "ExtrNative.uint".
Extract Constant lsl => "ExtrNative.l_sl".
Extract Constant lsr => "ExtrNative.l_sr".
Extract Constant Int63.land => "ExtrNative.l_and".
Extract Constant Int63.lor => "ExtrNative.l_or".
Extract Constant Int63.lxor => "ExtrNative.l_xor".
Extract Constant add => "ExtrNative.add".
Extract Constant sub => "ExtrNative.sub".
Extract Constant mul => "ExtrNative.mul".
Extract Constant mulc => "ExtrNative.mulc".
Extract Constant div => "ExtrNative.div".
Extract Constant Int63.mod => "ExtrNative.rem".
Extract Constant eqb => "ExtrNative.eq".
Extract Constant ltb => "ExtrNative.lt".
Extract Constant leb => "ExtrNative.le".
Extract Constant compare => "ExtrNative.compare".
Extract Constant head0 => "ExtrNative.head0".
Extract Constant tail0 => "ExtrNative.tail0".

Extract Constant addc => "ExtrNative.addc".
Extract Constant addcarryc => "ExtrNative.addcarryc".
Extract Constant subc => "ExtrNative.subc".
Extract Constant subcarryc => "ExtrNative.subcarryc".
Extract Constant diveucl => "ExtrNative.diveucl".

Extract Constant diveucl_21 => "ExtrNative.diveucl_21".
Extract Constant addmuldiv => "ExtrNative.addmuldiv".

(** Extraction of Array *)
Extract Constant array "'a" => "'a ExtrNative.parray".
Extract Constant make => "ExtrNative.parray_make".
Extract Constant get => "ExtrNative.parray_get".
Extract Constant default => "ExtrNative.parray_default".
Extract Constant set => "ExtrNative.parray_set".
Extract Constant length => "ExtrNative.parray_length".
Extract Constant copy => "ExtrNative.parray_copy".
Extract Constant reroot => "ExtrNative.parray_reroot".
