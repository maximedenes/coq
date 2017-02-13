Require Import quill.

Ltac intro_id x :=
  idtac "intro_id" x; Coq.quill.quill.intro_id x.

Module TestSquareBrackets.

Lemma test1 : forall x : bool, x = x.
Proof.
quill [ | ].
  match goal with |- true = true => idtac end.
  reflexivity.
match goal with |- false = false => idtac end.
reflexivity.
Qed.

Inductive named :=
 | K1 (n : nat)
 | K2 (n : nat) (k : named).

Lemma test2 : forall x : named, x = x.
Proof.
quill [ ^ _1 | ^~ two_ ].
  match goal with |- K1 n_1 = K1 n_1 => idtac end.
  reflexivity.
match goal with |- K2 two_n two_k = K2 two_n two_k => idtac end.
reflexivity.
Qed.

Lemma test3 n m : S n = S m -> True.
Proof.
quill [ = Enm ]. (* bug, [= with no space is "taken" *)
  match goal with Enm : n = m |- True => idtac end.
  Check (Enm : n = m).
trivial.
Qed.

End TestSquareBrackets.

Module TestRoundParens.

Lemma test1 : forall n m : nat, n = m -> True.
Proof.
quill [|n1] [|m1] ( E1 | E2 | E3 | E4 ).
- Check E1 : 0 = 0.
  exact I.
- Check E2 : 0 = S m1.
  exact I.
- Check E3 : S n1 = 0.
  exact I.
- Check E4 : S n1 = S m1.
  exact I.
Qed.


End TestRoundParens.
