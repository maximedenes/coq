Require Import Int63 PArray.

Open Scope array_scope.

(* Test reduction of primitives on array with kernel conversion, vm_compute,
native_compute, cbv, cbn *)

(* Immediate values *)
Definition t : array nat := [| 1; 3; 2 | 4 |].
Check (eq_refl : t.[0] = 1).
Check (eq_refl 1 <: t.[0] = 1).
Check (eq_refl 1 <<: t.[0] = 1).
Definition x1 := Eval compute in t.[0].
Check (eq_refl : x1 = 1).
Definition x2 := Eval cbn in t.[0].
Check (eq_refl : x2 = 1).

Check (eq_refl : t.[2] = 2).
Check (eq_refl 2 <: t.[2] = 2).
Check (eq_refl 2 <<: t.[2] = 2).
Definition x3 := Eval compute in t.[2].
Check (eq_refl : x3 = 2).
Definition x4 := Eval cbn in t.[2].
Check (eq_refl : x4 = 2).

Check (eq_refl : t.[99] = 4).
Check (eq_refl 4 <: t.[99] = 4).
Check (eq_refl 4 <<: t.[99] = 4).
Definition x5 := Eval compute in t.[4].
Check (eq_refl : x5 = 4).
Definition x6 := Eval cbn in t.[4].
Check (eq_refl : x6 = 4).

(* Computations inside the array *)
Definition t2 : array nat := [| 1 + 3 | 5 |].
Check (eq_refl : t2.[0] = 4).
Check (eq_refl 4 <: t2.[0] = 4).
Check (eq_refl 4 <<: t2.[0] = 4).
Definition x7 := Eval compute in t2.[0].
Check (eq_refl : x7 = 4).
Definition x8 := Eval cbn in t2.[0].
Check (eq_refl : x8 = 4).

(* Functions inside the array *)
Definition t3 : array (nat -> nat) := [| fun x => x | fun x => O |].
Check (eq_refl : t3.[0] 2 = 2).
Check (eq_refl 2 <: t3.[0] 2 = 2).
Check (eq_refl 2 <<: t3.[0] 2 = 2).
Definition x9 := Eval compute in t3.[0] 2.
Check (eq_refl : x9 = 2).
Definition x10 := Eval cbn in t3.[0] 2.
Check (eq_refl : x10 = 2).

(* Stuck primitive *)
Eval lazy in (fun t => t.[0]).
Eval vm_compute in (fun t => t.[0]).
Eval native_compute in (fun t => t.[0]).
Eval compute in (fun t => t.[0]).
Eval cbn in (fun t => t.[0]).

(* Under-application *)
Eval lazy in @PArray.get.
Eval vm_compute in @PArray.get.
Eval native_compute in @PArray.get.
Eval compute in @PArray.get.
Eval cbn in @PArray.get.
