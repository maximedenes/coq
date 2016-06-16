(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Termops
open Inductiveops
open Hipattern
open Tacmach.New
open Tacticals.New
open Tactics
open Proofview.Notations
open Context.Named.Declaration

(* Supposed to be called without as clause *)
let introElimAssumsThen tac ba =
  assert (ba.Tacticals.branchnames == []);
  let introElimAssums = tclDO ba.Tacticals.nassums intro in
  (tclTHEN introElimAssums (elim_on_ba tac ba))

(* Supposed to be called with a non-recursive scheme *)
let introCaseAssumsThen tac ba =
  let n1 = List.length ba.Tacticals.branchsign in
  let n2 = List.length ba.Tacticals.branchnames in
  let (l1,l2),l3 =
    if n1 < n2 then List.chop n1 ba.Tacticals.branchnames, []
    else (ba.Tacticals.branchnames, []), List.make (n1-n2) false in
  let introCaseAssums =
    tclTHEN (intro_patterns l1) (intros_clearing l3) in
  (tclTHEN introCaseAssums (case_on_ba (tac l2) ba))

(* The following tactic Decompose repeatedly applies the
   elimination(s) rule(s) of the types satisfying the predicate
   ``recognizer'' onto a certain hypothesis. For example :

Require Elim.
Require Le.
   Goal (y:nat){x:nat | (le O x)/\(le x y)}->{x:nat | (le O x)}.
   Intros y H.
   Decompose [sig and] H;EAuto.
   Qed.

Another example :

   Goal (A,B,C:Prop)(A/\B/\C \/ B/\C \/ C/\A) -> C.
   Intros A B C H; Decompose [and or] H; Assumption.
   Qed.
*)

let elimHypThen tac id =
  elimination_then tac (mkVar id)

let rec general_decompose_on_hyp recognizer =
  ifOnHyp recognizer (general_decompose_aux recognizer) (fun _ -> Proofview.tclUNIT())

and general_decompose_aux recognizer id =
  elimHypThen
    (introElimAssumsThen
       (fun bas ->
	  tclTHEN (clear [id])
	    (tclMAP (general_decompose_on_hyp recognizer)
               (ids_of_named_context bas.Tacticals.assums))))
    id

(* We should add a COMPLETE to be sure that the created hypothesis
   doesn't stay if no elimination is possible *)

(* Best strategies but loss of compatibility *)
let tmphyp_name = Id.of_string "_TmpHyp"
let up_to_delta = ref false (* true *)

let general_decompose recognizer c =
  Proofview.Goal.enter { enter = begin fun gl ->
  let type_of = pf_unsafe_type_of gl in
  let typc = type_of c in
  tclTHENS (cut typc)
    [ tclTHEN (intro_using tmphyp_name)
         (onLastHypId
	    (ifOnHyp recognizer (general_decompose_aux recognizer)
	      (fun id -> clear [id])));
       exact_no_check c ]
  end }

let head_in indl t gl =
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  try
    let ity,_ =
      if !up_to_delta
      then find_mrectype env sigma t
      else extract_mrectype t
    in List.exists (fun i -> eq_ind (fst i) (fst ity)) indl
  with Not_found -> false

let decompose_these c l =
  Proofview.Goal.enter { enter = begin fun gl ->
  let indl = List.map (fun x -> x, Univ.Instance.empty) l in
  general_decompose (fun (_,t) -> head_in indl t gl) c
  end }

let decompose_and c =
  general_decompose
    (fun (_,t) -> is_record t)
    c

let decompose_or c =
  general_decompose
    (fun (_,t) -> is_disjunction t)
    c

let h_decompose l c = decompose_these c l

let h_decompose_or = decompose_or

let h_decompose_and = decompose_and
