(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Libnames
open Globnames
open Nametab

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

(************************************************************************)
(* Coq reference API                                                    *)
(************************************************************************)
[@@@ocaml.warning "-37"]
type mode = Coq | HoTT | Ssr
let mode = Coq

let coq = Libnames.coq_string (* "Coq" *)

let init_dir = match mode with
  | Coq  -> [ coq; "Init"]
  | HoTT -> [ "HoTT"; "Basics" ]
  | Ssr  -> [ "mathcomp"; "ssreflect" ]

let _lib_prelude, lib_logic, lib_data, lib_type, lib_specif = match mode with
  | Coq  -> "Prelude", "Logic", "Datatypes", "Logic_Type", "Specif"
  | HoTT -> "Overture", "Overture", "Overture", "Overture", "Overture"
  | Ssr  -> "init", "init", "init", "init", "init"

let l_eq = match mode with
  | Coq  -> "eq"
  | HoTT -> "paths"
  | Ssr  -> "eq"

(* let prelude_module_name    = init_dir@[lib_prelude] *)
(* let prelude_module         = make_dir prelude_module_name *)

let logic_module_name      = init_dir@[lib_logic]
(* let logic_module           = make_dir logic_module_name *)

let logic_type_module_name = init_dir@[lib_type]
(* let logic_type_module      = make_dir logic_type_module_name *)

let datatypes_module_name  = init_dir@[lib_data]
(* let datatypes_module       = make_dir datatypes_module_name *)

let specif_module_name     = init_dir@[lib_specif]

let jmeq_module_name       = [coq;"Logic";"JMeq"]
let jmeq_module            = make_dir jmeq_module_name

let std_table : (string * string list * string) array =
  let logic_lib = logic_module_name      in
  let data_lib  = datatypes_module_name  in
  let type_lib  = logic_type_module_name in
  let spec_lib  = specif_module_name     in
  let jmeq_lib  = jmeq_module_name       in
  let eqdep_dec_lib  = [coq;"Logic";"Eqdep_dec"] in
  [| "core.False.type", logic_lib, "False"

   ; "core.True.type",  logic_lib, "True"
   ; "core.True.I",     logic_lib, "I"

   ; "core.not.type",   logic_lib, "not"

   ; "core.or.type",    logic_lib, "or"
   ; "core.or.ind",     logic_lib, "or_ind"

   ; "core.and.type",   logic_lib, "and"
   ; "core.and.ind",    logic_lib, "and_ind"
   ; "core.and.conj",   logic_lib, "conj"

   ; "core.iff.type",   logic_lib, "iff"
   ; "core.iff.proj1",  logic_lib, "proj1"
   ; "core.iff.proj2",  logic_lib, "proj2"

   ; "core.ex.type",    logic_lib, "ex"
   ; "core.ex.ind",     logic_lib, "ex_ind"
   ; "core.ex.intro",   logic_lib, "ex_intro"

   ; "core.eq.type",    logic_lib, l_eq ^ ""
   ; "core.eq.refl",    logic_lib, l_eq ^ "_refl"
   ; "core.eq.ind",     logic_lib, l_eq ^ "_ind"
   ; "core.eq.rect",    logic_lib, l_eq ^ "_rect"
   ; "core.eq.sym",     logic_lib, l_eq ^ "_sym"
   ; "core.eq.congr",   logic_lib, "f_equal"
   ; "core.eq.congr2",  logic_lib, "f_equal2"
   ; "core.eq.trans",   logic_lib, "eq_trans"
   (* XXX: Is not there? *)
   ; "core.eq.congr_canonical", logic_lib, "f_equal_canonical_form"

   ; "core.identity.type",    data_lib, "identity"
   ; "core.identity.refl",    data_lib, "identity_refl"
   ; "core.identity.ind",     data_lib, "identity_ind"
   ; "core.identity.sym",     type_lib, "identity_sym"
   ; "core.identity.congr",   type_lib, "identity_congr"
   ; "core.identity.trans",   type_lib, "identity_trans"

   (* XXX: Also doesn't seem there *)
   ; "core.identity.congr_canonical",   ["Coq"; "Init"; "Logic_Type"], "identity_congr_canonical_form"

   ; "core.ID.type",   data_lib, "ID"
   ; "core.ID.id",     data_lib, "id"

   ; "core.IDProp.type",   data_lib, "IDProp"
   ; "core.IDProp.idProp", data_lib, "idProp"

   ; "core.prod.type",   data_lib, "prod"
   ; "core.prod.rect",   data_lib, "prod_rect"
   ; "core.prod.intro",  data_lib, "pair"
   ; "core.prod.proj1",  data_lib, "fst"
   ; "core.prod.proj2",  data_lib, "snd"

   ; "core.sig.type",    spec_lib, "sig"
   ; "core.sig.rect",    spec_lib, "sig_rec"
   ; "core.sig.intro",   spec_lib, "exist"
   ; "core.sig.proj1",   spec_lib, "proj1_sig"
   ; "core.sig.proj2",   spec_lib, "proj2_sig"

   ; "core.sigT.type",   spec_lib, "sigT"
   ; "core.sigT.rect",   spec_lib, "sigT_rect"
   ; "core.sigT.intro",  spec_lib, "existT"
   ; "core.sigT.proj1",  spec_lib, "projT1"
   ; "core.sigT.proj2",  spec_lib, "projT2"

   ; "core.sumbool.type", spec_lib, "sumbool"

   ; "core.JMeq.type",   jmeq_lib, "JMeq"
   ; "core.JMeq.refl",   jmeq_lib, "JMeq_refl"
   ; "core.JMeq.ind",    jmeq_lib, "JMeq_ind"
   ; "core.JMeq.sym",    jmeq_lib, "JMeq_sym"
   ; "core.JMeq.congr",  jmeq_lib, "JMeq_congr"
   ; "core.JMeq.trans",  jmeq_lib, "JMeq_trans"
   ; "core.JMeq.hom",    jmeq_lib, "JMeq_hom"
   ; "core.JMeq.congr_canonical", jmeq_lib, "JMeq_congr_canonical_form"

   ; "core.bool.type",            data_lib, "bool"
   ; "core.bool.true",            data_lib, "true"
   ; "core.bool.false",           data_lib, "false"
   ; "core.bool.andb",            data_lib, "andb"
   ; "core.bool.andb_prop",       data_lib, "andb_prop"
   ; "core.bool.andb_true_intro", data_lib, "andb_true_intro"
   ; "core.bool.orb",             data_lib, "orb"
   ; "core.bool.xorb",            data_lib, "xorb"
   ; "core.bool.negb",            data_lib, "negb"

   ; "core.eq_true.type",         data_lib, "eq_true"
   ; "core.eq_true.ind",          data_lib, "eq_true_ind"

   (* Not in the lib *)
   ; "core.eq_true.congr",  logic_lib,     "eq_true_congr"
   ; "core.eq_true.congr_canonical",  logic_lib,     "eq_true_congr"

   ; "core.nat.type",      data_lib, "nat"
   ; "core.nat.O",         data_lib, "O"
   ; "core.nat.S",         data_lib, "S"

   ; "core.list.type",      data_lib, "list"
   ; "core.list.nil",       data_lib, "nil"
   ; "core.list.cons",      data_lib, "cons"

   ; "core.eqdep_dec.inj_pair2", eqdep_dec_lib, "inj_pair2_eq_dec"

   ; "core.eqdep_dec.inj_pair2", eqdep_dec_lib, "inj_pair2_eq_dec"

   ; "core.wf.well_founded", [coq;"Init";"Wf"], "well_founded"

   ; "program.wf.fix_sub",   [coq;"Program";"Wf"], "Fix_sub"
   ; "program.wf.mr",        [coq;"Program";"Wf"], "MR"

   ; "program.tactics.obligation", [coq;"Program";"Tactics"], "obligation"
   ; "program.tactics.fix_proto",  [coq;"Program";"Tactics"], "fix_proto"

  |]

let table = std_table

let find_reference locstr dir s =
  let dp = make_dir dir in
  let sp = Libnames.make_path dp (Id.of_string s) in
  try Nametab.global_of_path sp
  with Not_found ->
    (* Following bug 5066 we are more permissive with the handling
       of not found errors here *)
    user_err ~hdr:locstr
      Pp.(str "cannot find " ++ Libnames.pr_path sp ++
          str "; maybe library " ++ DirPath.print dp ++
          str " has to be required first.")

let coq_reference locstr dir s = find_reference locstr (coq::dir) s

let table : (string, GlobRef.t Lazy.t) Hashtbl.t =
  let ht = Hashtbl.create (2 * Array.length table) in
  Array.iter (fun (b, path, s) -> Hashtbl.add ht b @@ lazy (find_reference "from_table" path s)) table;
  ht

(** Can throw Not_found *)
let lib_ref    s =
  try Lazy.force (Hashtbl.find table s)
  with | Not_found ->
    Feedback.msg_warning Pp.(str "not found in table: " ++ str s);
    raise Not_found

(** Replaces a binding ! *)
let add_ref  s c =
  Hashtbl.add table s (Lazy.from_val c)

(************************************************************************)
(* Generic functions to find Coq objects *)

type message = string

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (path_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let gen_reference_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let qualid = qualid_of_string s in
  let all = Nametab.locate_all qualid in
  let all = List.sort_uniquize RefOrdered_env.compare all in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> x
    | [] ->
	anomaly ~label:locstr (str "cannot find " ++ str s ++
	str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
        prlist_with_sep pr_comma DirPath.print dirs ++ str ".")
    | l ->
      anomaly ~label:locstr
	(str "ambiguous name " ++ str s ++ str " can represent " ++
	   prlist_with_sep pr_comma
	   (fun x -> Libnames.pr_path (Nametab.path_of_global x)) l ++
	   str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
           prlist_with_sep pr_comma DirPath.print dirs ++ str ".")

(* For tactics/commands requiring vernacular libraries *)

let check_required_library d =
  let dir = make_dir d in
  if Library.library_is_loaded dir then ()
  else
    let in_current_dir = match Lib.current_mp () with
      | MPfile dp -> DirPath.equal dir dp
      | _ -> false
    in
    if not in_current_dir then
      user_err ~hdr:"Coqlib.check_required_library"
        (str "Library " ++ DirPath.print dir ++ str " has to be required first.")

(************************************************************************)
(* Specific Coq objects                                                 *)
(************************************************************************)

let arith_dir = [coq;"Arith"]
let arith_modules = [arith_dir]

let numbers_dir = [coq;"Numbers"]
let parith_dir = [coq;"PArith"]
let narith_dir = [coq;"NArith"]
let zarith_dir = [coq;"ZArith"]

let zarith_base_modules = [numbers_dir;parith_dir;narith_dir;zarith_dir]

let init_modules = [
  init_dir@["Datatypes"];
  init_dir@["Logic"];
  init_dir@["Specif"];
  init_dir@["Logic_Type"];
  init_dir@["Nat"];
  init_dir@["Peano"];
  init_dir@["Wf"]
]

let prelude_module_name = init_dir@["Prelude"]
let prelude_module = make_dir prelude_module_name

let logic_module_name = init_dir@["Logic"]
let logic_module = make_dir logic_module_name

let logic_type_module_name = init_dir@["Logic_Type"]
let logic_type_module = make_dir logic_type_module_name

let datatypes_module_name = init_dir@["Datatypes"]
let datatypes_module = make_dir datatypes_module_name

(* TODO: temporary hack. Works only if the module isn't an alias *)
let make_ind dir id = Globnames.encode_mind dir (Id.of_string id)
let make_con dir id = Globnames.encode_con dir (Id.of_string id)

(** Identity *)

let id = make_con datatypes_module "idProp"
let type_of_id = make_con datatypes_module "IDProp"

(** Natural numbers *)
let nat_kn = make_ind datatypes_module "nat"
let nat_path = Libnames.make_path datatypes_module (Id.of_string "nat")

let glob_nat = IndRef (nat_kn,0)

let path_of_O = ((nat_kn,0),1)
let path_of_S = ((nat_kn,0),2)
let glob_O = ConstructRef path_of_O
let glob_S = ConstructRef path_of_S

(** Booleans *)
let bool_kn = make_ind datatypes_module "bool"

let glob_bool = IndRef (bool_kn,0)

let path_of_true = ((bool_kn,0),1)
let path_of_false = ((bool_kn,0),2)
let glob_true  = ConstructRef path_of_true
let glob_false  = ConstructRef path_of_false

(** Equality *)
let eq_kn = make_ind logic_module "eq"
let glob_eq = IndRef (eq_kn,0)

let identity_kn = make_ind datatypes_module "identity"
let glob_identity = IndRef (identity_kn,0)

let jmeq_kn = make_ind jmeq_module "JMeq"
let glob_jmeq = IndRef (jmeq_kn,0)

(* Sigma data *)
type coq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t }

let build_sigma_gen str =
  { typ   = lib_ref ("core." ^ str ^ ".type");
    elim  = lib_ref ("core." ^ str ^ ".rect");
    intro = lib_ref ("core." ^ str ^ ".intro");
    proj1 = lib_ref ("core." ^ str ^ ".proj1");
    proj2 = lib_ref ("core." ^ str ^ ".proj2");
  }

let build_prod       () = build_sigma_gen "prod"
let build_sigma      () = build_sigma_gen "sig"
let build_sigma_type () = build_sigma_gen "sigT"

(* Booleans *)

type coq_bool_data  = {
  andb : GlobRef.t;
  andb_prop : GlobRef.t;
  andb_true_intro : GlobRef.t}

let build_bool_type () =
  { andb = lib_ref "core.bool.andb";
    andb_prop = lib_ref "core.bool.andb_prop";
    andb_true_intro = lib_ref "core.bool.andb_true_intro"; }

(* Equalities *)
type coq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t }

(* Leibniz equality on Type *)

let build_eqdata_gen lib str =
  let _ = check_required_library lib in {
  eq    = lib_ref ("core." ^ str ^ ".type");
  ind   = lib_ref ("core." ^ str ^ ".ind");
  refl  = lib_ref ("core." ^ str ^ ".refl");
  sym   = lib_ref ("core." ^ str ^ ".sym");
  trans = lib_ref ("core." ^ str ^ ".trans");
  congr = lib_ref ("core." ^ str ^ ".congr");
  }

let build_coq_eq_data       () = build_eqdata_gen logic_module_name "eq"
let build_coq_jmeq_data     () = build_eqdata_gen jmeq_module_name  "JMeq"
let build_coq_identity_data () = build_eqdata_gen datatypes_module_name "identity"

(* Inversion data... *)

(* Data needed for discriminate and injection *)
type coq_inversion_data = {
  inv_eq   : GlobRef.t; (* : forall params, t -> Prop *)
  inv_ind  : GlobRef.t; (* : forall params P y, eq params y -> P y *)
  inv_congr: GlobRef.t  (* : forall params B (f:t->B) y, eq params y -> f c=f y *)
}

let build_coq_inversion_gen l str =
  List.iter check_required_library l; {
    inv_eq    = lib_ref ("core." ^ str ^ ".type");
    inv_ind   = lib_ref ("core." ^ str ^ ".ind");
    inv_congr = lib_ref ("core." ^ str ^ ".congr_canonical");
  }

let build_coq_inversion_eq_data () =
  build_coq_inversion_gen [logic_module_name] "eq"

let build_coq_inversion_eq_true_data () =
  build_coq_inversion_gen [logic_module_name] "True"

let build_coq_inversion_identity_data () =
  build_coq_inversion_gen [logic_module_name] "identity"

(* This needs a special case *)
let build_coq_inversion_jmeq_data () = {
  inv_eq    = lib_ref "core.JMeq.hom";
  inv_ind   = lib_ref "core.JMeq.ind";
  inv_congr = lib_ref "core.JMeq.congr_canonical";
}

(* Specif *)
let build_coq_sumbool () = lib_ref "core.sumbool.type"

let build_coq_eq () = lib_ref "core.eq.type"
let build_coq_eq_refl () = lib_ref "core.eq.refl"
let build_coq_eq_sym () = lib_ref "core.eq.sym"
let build_coq_f_equal2 () = lib_ref "core.eq.congr2"

(* Runtime part *)
let build_coq_True ()  = lib_ref "core.True.type"
let build_coq_I ()     = lib_ref "core.True.I"
let build_coq_identity () = lib_ref "core.identity.type"

let build_coq_eq_true () = lib_ref "core.eq_true.type"
let build_coq_jmeq () = lib_ref "core.JMeq.type"

let build_coq_False () = lib_ref "core.False.type"
let build_coq_not ()   = lib_ref "core.not.type"
let build_coq_and ()   = lib_ref "core.and.type"
let build_coq_conj ()  = lib_ref "core.conj.type"
let build_coq_or ()    = lib_ref "core.or.type"
let build_coq_ex ()    = lib_ref "core.ex.type"
let build_coq_sig () = lib_ref "core.sig.type"
let build_coq_existT () = lib_ref "core.sigT.existT"
let build_coq_iff ()   = lib_ref "core.iff.type"

let build_coq_iff_left_proj ()  = lib_ref "core.iff.proj1"
let build_coq_iff_right_proj () = lib_ref "core.iff.proj2"

(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = Lazy.from_fun build_coq_eq
let coq_identity_ref = Lazy.from_fun build_coq_identity
let coq_jmeq_ref     = Lazy.from_fun build_coq_jmeq
let coq_eq_true_ref = Lazy.from_fun build_coq_eq_true
let coq_existS_ref  = Lazy.from_fun build_coq_existT
let coq_existT_ref  = Lazy.from_fun build_coq_existT
let coq_exist_ref  = Lazy.from_fun build_coq_ex
let coq_not_ref     = Lazy.from_fun build_coq_not
let coq_False_ref   = Lazy.from_fun build_coq_False
let coq_sumbool_ref = Lazy.from_fun build_coq_sumbool
let coq_sig_ref = Lazy.from_fun build_coq_sig
let coq_or_ref     = Lazy.from_fun build_coq_or
let coq_iff_ref    = Lazy.from_fun build_coq_iff

(** Deprecated functions that search by library name. *)
let build_sigma_set () = anomaly (Pp.str "Use build_sigma_type.")
