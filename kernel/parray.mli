val trunc_size : Uint63.t -> int
type 'a t
val length  : 'a t -> Uint63.t
val get     : 'a t -> Uint63.t -> 'a
val set     : 'a t -> Uint63.t -> 'a -> 'a t
val destr_set : 'a t -> Uint63.t -> 'a -> 'a t
val default : 'a t -> 'a
val make    : Uint63.t -> 'a -> 'a t
val init    : Uint63.t -> (int -> 'a) -> 'a -> 'a t
val copy    : 'a t -> 'a t
val reroot  : 'a t -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val to_array : 'a t -> 'a array * 'a (* default *)

val of_array : 'a array -> 'a (* default *) -> 'a t

val unsafe_of_array : 'a array -> 'a -> 'a t
(* [unsafe_of_array] injects a mutable array into a persistent one, but does
   not perform a copy. This means that if the persistent array is mutated, the
   original one will be too. *)
