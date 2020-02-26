Require Import Int63 PArray.

Open Scope int63_scope.

Definition t : array nat := [| 1; 3; 2 | 4 |]%nat.
Check (eq_refl : PArray.length t = 3).
Check (eq_refl 3 <: PArray.length t = 3).
Check (eq_refl 3 <<: PArray.length t = 3).
Definition x1 := Eval compute in PArray.length t.
Check (eq_refl : x1 = 3).
Definition x2 := Eval cbn in PArray.length t.
Check (eq_refl : x2 = 3).
