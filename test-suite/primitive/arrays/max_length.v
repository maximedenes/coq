
Require Import Int63 PArray.

Open Scope int63_scope.

Definition max_length := 4194303.

Check (eq_refl max_length : PArray.max_length = max_length).
Check (eq_refl max_length <: PArray.max_length = max_length).
Check (eq_refl max_length <<: PArray.max_length = max_length).
Definition max_length2 := Eval compute in PArray.max_length.
Check (eq_refl : max_length = max_length2).
Definition max_length3 := Eval cbn in PArray.max_length.
Check (eq_refl : max_length = max_length3).
