Require Import Int63 PArray.

Definition t : array nat := [| 1; 3; 2 | 4 |].
Check (eq_refl : default t = 4).
Check (eq_refl 4 <: default t = 4).
Check (eq_refl 4 <<: default t = 4).
Definition x1 := Eval compute in default t.
Check (eq_refl : x1 = 4).
Definition x2 := Eval cbn in default t.
Check (eq_refl : x2 = 4).
