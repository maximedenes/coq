Require Export Int63.

Primitive array := #array_type.

Primitive make := #array_make.
Arguments make {_} _ _.

Primitive get := #array_get.
Arguments get {_} _ _.

Primitive default := #array_default.
Arguments default {_} _.

Primitive set := #array_set.
Arguments set {_} _ _ _.

Primitive length := #array_length.
Arguments length {_} _.

Primitive copy := #array_copy.
Arguments copy {_} _.

Primitive reroot := #array_reroot.
Arguments reroot {_} _.

(* Not done with the vm *)
Primitive init := #array_init.
Arguments init {_} _ _.

Primitive map := #array_map.
Arguments map {_ _} _ _.

Declare Scope array_scope.
Delimit Scope array_scope with array.
Notation "t '.[' i ']'" := (get t i) (at level 50) : array_scope.
Notation "t '.[' i '<-' a ']'" := (set t i a) (at level 50) : array_scope.

Local Open Scope int63_scope.
Local Open Scope array_scope.

Definition max_array_length := 4194302.

(** Axioms *)
Axiom get_outofbound : forall A (t:array A) i, (i < length t) = false -> t.[i] = default t.

Axiom get_set_same : forall (A:Set) t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a.
Axiom get_set_other : forall (A:Set) t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
Axiom default_set : forall (A:Set) t i (a:A), default (t.[i<-a]) = default t.


Axiom get_make : forall (A:Set) (a:A) size i, (make size a).[i] = a.
Axiom default_make : forall (A:Set) (a:A) size, (default (make size a)) = a.

Axiom ltb_length : forall A (t:array A), length t <= max_array_length = true.

Axiom length_make : forall (A:Set) size (a:A),
  length (make size a) = if size <= max_array_length then size else max_array_length.
Axiom length_set : forall (A:Set) t i (a:A),
  length (t.[i<-a]) = length t.

Axiom get_copy : forall A (t:array A) i, (copy t).[i] = t.[i].
Axiom length_copy : forall A (t:array A), length (copy t) = length t.

Axiom get_reroot : forall A (t:array A) i, (reroot t).[i] = t.[i].
Axiom length_reroot : forall A (t:array A), length (reroot t) = length t.


Axiom length_init : forall (A:Set) f size (def:A),
  length (init size f def) = if size <= max_array_length then size else max_array_length.

Axiom get_init : forall (A:Set) f size (def:A) i,
  (init size f def).[i] = if i < length (init size f def) then f i else def.

Axiom default_init : forall (A:Set) f size (def:A), default (init size f def) = def.

(* Rename this ? *)
Axiom get_ext : forall A (t1 t2:array A),
  length t1 = length t2 ->
  (forall i, i < length t1 = true -> t1.[i] = t2.[i]) ->
  default t1 = default t2 ->
  t1 = t2.

(* Lemmas *)

Lemma default_copy : forall A (t:array A), default (copy t) = default t.
Proof.
(*
 intros A t; case_eq (length t < length t).
   apply Int63.ltbP. apply BinInt.Z.lt_irrefl.
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (copy t) (length t)), <- (get_outofbound _ t (length t)), get_copy;trivial.
 rewrite length_copy;trivial.
*)
Admitted.

Lemma reroot_default : forall A (t:array A), default (reroot t) = default t.
Proof.
(*
 intros A t;assert (length t < length t = false).
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (reroot t) (length t)), <- (get_outofbound _ t (length t)), get_reroot;trivial.
 rewrite length_reroot;trivial.
*)
Admitted.

Lemma get_set_same_default :
   forall (A : Set) (t : array A) (i : int) ,
       (t .[ i <- default t]) .[ i] = default t.
Proof.
 intros A t i;case_eq (i < (length t));intros.
 rewrite get_set_same;trivial.
 rewrite get_outofbound, default_set;trivial.
 rewrite length_set;trivial.
Qed.

Lemma get_not_default_lt : forall A (t:array A) x,
 t.[x] <> default t -> (x < length t)%int63 = true.
Proof.
 intros A t x Hd.
 case_eq (x < length t);intros Heq;[trivial | ].
 elim Hd;rewrite get_outofbound;trivial.
Qed.
