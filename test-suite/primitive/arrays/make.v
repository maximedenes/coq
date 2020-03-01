Require Import Int63 PArray.

Open Scope array_scope.

(* Immediate values *)
Definition t1 : array nat := [| 3; 3; 3; 3 | 3 |].
Definition t2 := PArray.make 4 3.
Check (eq_refl : t1 = t2).
Check (eq_refl t1 <: t1 = t2).
Check (eq_refl t1 <<: t1 = t2).
Definition x1 := Eval compute in t2.
Check (eq_refl : x1 = t1).
Definition x2 := Eval cbn in t2.
Check (eq_refl : x2 = t1).
