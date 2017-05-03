Require Import ssreflect.

Ltac intro_id x :=
  idtac "intro_id" x; Coq.ssr.ssreflect.intro_id x.

Module TestSquareBrackets.

Lemma test1 : forall x : bool, x = x.
Proof.
=> - [ | ]. (* FIXME: what should => [ | ] do here? *)
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
=> - [ ^ _1 | ^~ two_ ].
  match goal with |- K1 n_1 = K1 n_1 => idtac end.
  reflexivity.
match goal with |- K2 two_n two_k = K2 two_n two_k => idtac end.
reflexivity.
Qed.

Lemma test3 n m : S n = S m -> True.
Proof.
=> - [ = Enm ]. (* bug, [= with no space is "taken" *)
  match goal with Enm : n = m |- True => idtac end.
  Check (Enm : n = m).
trivial.
Qed.

End TestSquareBrackets.

(* ----------------------------------------------------- *)

Module TestRoundParens.

Lemma test1 : forall n m : nat, n = m -> True.
Proof.
=> - [|n1] [|m1] ( E1 | E2 | E3 | E4 ).
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

(* ----------------------------------------------------- *)

Goal (True -> False) -> True -> False.
Proof.
=> v /v H; exact H.
Qed.

(* BUG 
Notation swap := ltac:(
  let n := fresh in
  let m := fresh in
  => n m; revert n; revert m).

Goal True -> (True -> False) -> False.
Proof.
=> /swap v /v H; exact H.
Qed.
*)

Notation swap := ltac:(
  let n := fresh in
  let m := fresh in
  intro n; intro m; revert n; revert m).

Goal True -> (True -> False) -> False.
Proof.
=> /swap v /v H; exact H.
Qed.


Record IFF A B := mkIFF { i : A -> B; o : B -> A }.

ViewAdaptor Forward (i _ _).

Goal IFF True False -> True -> False.
Proof.
=> H /H F; exact F.
Qed.

Axiom P : nat -> nat -> Prop.
Axiom leq_trans : forall a b c : nat, P a b -> P b c -> P a c.

Goal P 1 2 -> P 2 3 -> P 1 3.
Proof.
=> /leq_trans H H2; apply H; apply H2.
Qed.

Module Evars.
Axiom P : nat -> Prop.
Axiom Q : nat -> nat -> Prop.

Goal exists x, (forall x y, P (S x) -> Q x y) -> P x -> Q x x.
eexists. => v /v. Abort.


End Evars.
