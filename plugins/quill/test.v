Require Import quill.

Goal True -> True -> True.
quill /(intros H).
Abort.

Tactic Notation "myintro" ident(x) := intros x.
Tactic Notation "myapply" constr(t) := apply t.
Goal True -> True -> True.
quill /(myintro H) /(myintro H2) /(myapply H).
Abort.

Goal nat -> True.
quill /(myintro n) /(case n) /[|] /[ /[] /(exact I)|/(intros _)/(exact I)].
Abort.

Goal nat -> True.
quill /(myintro n) /(case n) /(cycle 1) /[ /(intros _)/(exact I) | /[] /(exact I)].
Abort.

Goal nat -> True.
Fail quill /(myintro n) /(case n) /[/(exact I)| | /(intros _)/(exact I)].
(* The error message is a bit baroque *)
Abort.
