open CErrors
open Util
open Names
open Evarutil
open Reductionops
open Constr
open Context
open Vars
open Evarsolve
open Proofview
open Proofview.Notations
open Ssrmatching_plugin.Ssrmatching
open CoqAPI

(** [nb_deps_assums] returns the number of dependent premises *)
(** TODO: decide what we should do with occurrences in evars / evar contexts *)
let rec nb_deps_assums cur env sigma t =
  let t' = whd_allnolet env sigma t in
  match kind_of_term_upto sigma t' with
  | Prod(name,ty,body) ->
     (* FIXME use EConstr.noccur *)
     if noccurn 1 body then cur
     else
       nb_deps_assums (cur+1) env sigma body
  | LetIn(name,ty,t1,t2) ->
     nb_deps_assums (cur+1) env sigma t2
  | Cast(t,_,_) ->
     nb_deps_assums cur env sigma t
  | _ -> cur

let nb_deps_assums = nb_deps_assums 0

(** [nb_deps_assums] returns the number of dependent premises *)
(** Warning: unlike [nb_deps_assums], it does not perform reduction *)
(** TODO: decide what we should do with occurrences in evars / evar contexts *)
let rec nb_assums cur env sigma t =
  match kind_of_term_upto sigma t with
  | Prod(name,ty,body) ->
     nb_assums (cur+1) env sigma body
  | LetIn(name,ty,t1,t2) ->
    nb_assums (cur+1) env sigma t2
  | Cast(t,_,_) ->
     nb_assums cur env sigma t 
  | _ -> cur

let nb_assums = nb_assums 0

let same_prefix s t n =
  let rec loop i = i = n || s.[i] = t.[i] && loop (i + 1) in loop 0

let skip_digits s =
  let n = String.length s in 
  let rec loop i = if i < n && Util.is_digit s.[i] then loop (i + 1) else i in loop

let max_suffix m (t, j0 as tj0) id  =
  let s = string_of_id id in let n = String.length s - 1 in
  let dn = String.length t - 1 - n in let i0 = j0 - dn in
  if not (i0 >= m && s.[n] = '_' && same_prefix s t m) then tj0 else
  let rec loop i =
    if i < i0 && s.[i] = '0' then loop (i + 1) else
    if (if i < i0 then skip_digits s i = n else le_s_t i) then s, i else tj0
  and le_s_t i =
    let ds = s.[i] and dt = t.[i + dn] in
    if ds = dt then i = n || le_s_t (i + 1) else
    dt < ds && skip_digits s i = n in
  loop m

let mk_anon_id t gl =
  let m, si0, id0 =
    let s = ref (Printf.sprintf  "_%s_" t) in
    if Ssreflect_plugin.Ssrcommon.is_internal_name !s then s := "_" ^ !s;
    let n = String.length !s - 1 in
    let rec loop i j =
      let d = !s.[i] in if not (Util.is_digit d) then i + 1, j else
      loop (i - 1) (if d = '0' then j else i) in
    let m, j = loop (n - 1) n in m, (!s, j), id_of_string !s in
  let gl_ids = Tacmach.New.pf_ids_of_hyps gl in
  if not (List.mem id0 gl_ids) then id0 else
  let s, i = List.fold_left (max_suffix m) si0 gl_ids in
  let s = Bytes.of_string s in
  let n = Bytes.length s - 1 in
  let set = Bytes.set s in
  let rec loop i =
    if s.[i] = '9' then (set i '0'; loop (i - 1)) else
    if i < m then (set n '0'; set m '1'; s ^ "_") else
    (set i (Char.chr (Char.code s.[i] + 1)); s) in
  id_of_string (Bytes.to_string (loop (n - 1)))

let convert_concl_no_check t = Tactics.convert_concl_no_check t Term.DEFAULTcast
let convert_concl t = Tactics.convert_concl t Term.DEFAULTcast

let rename_hd_prod name =
  Goal.enter { enter = fun gl ->
    let concl = Goal.raw_concl gl in
    match Term.kind_of_term concl with
    | Prod(_,src,tgt) ->
        convert_concl_no_check (mkProd (name,src,tgt))
    | _ -> CErrors.anomaly (Pp.str "rename_hd_prod: no head product")
  }

let gentac id new_name =
 let gen = ((None,Some(false,[])),cpattern_of_id id) in
 let ist = Geninterp.({ lfun = Id.Map.empty; extra = TacStore.empty }) in
 Proofview.V82.tactic (Ssreflect_plugin.Ssreflect.gentac ist gen)
 <*> rename_hd_prod new_name
