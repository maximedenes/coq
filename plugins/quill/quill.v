Require ssrmatching.
Require ssreflect.
Declare ML Module "quill_plugin".

(* Documentation and maybe typechecking? *)
Tactic Notation "intro_id" ident(i) := intro_id i.
Tactic Notation "intro_id_prepend" ident(i) := intro_id_prepend i.
Tactic Notation "intro_id_append" ident(i) := intro_id_append i.
