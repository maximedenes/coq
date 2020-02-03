Require Import PArray.

Open Scope array_scope.

Definition t : array nat := [! 1; 3; 2 | 4 !].
Definition t' : array nat := t.[1 <- 5].

Check (eq_refl : t'.[1] = 5).
Check (eq_refl 5 <: t'.[1] = 5).
Check (eq_refl 5 <<: t'.[1] = 5).
Definition x1 := Eval compute in t'.[1].
Check (eq_refl : x1 = 5).
Definition x2 := Eval cbn in t'.[1].
Check (eq_refl : x2 = 5).

Check (eq_refl : t.[1] = 3).
Check (eq_refl 3 <: t.[1] = 3).
Check (eq_refl 3 <<: t.[1] = 3).
Definition x3 := Eval compute in t.[1].
Check (eq_refl : x3 = 3).
Definition x4 := Eval cbn in t.[1].
Check (eq_refl : x4 = 3).
