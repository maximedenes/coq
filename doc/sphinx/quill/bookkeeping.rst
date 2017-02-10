===========
Bookkeeping
===========

Introduction
============

.. tacn:: {? @tactic} => {+ @i_item}

The traditional "intros" tactic is written "=>".
So, one can write the tactic "=> ipats",
where "ipats" denotes a space-separated list of intropatterns.

.. todo::
   ?? can we specify which spaces are relevant or irrelevant 
   between intropatterns made of tokens?
   E.g. is "[]//" valid or should it written "[] //"
   maybe it is better to enforce space, so that we have
   more flexibility for adding new tokens later.

The arrow may also follow a tactic, in the form "tactic => ipats".
This form is equivalent to "tactic ;=> ipats".

.. todo::
   ?? do we want to impose the litteral "move" before the arrow?
   or should we let the users decide for themselves whether they
   like the "move" convention or whether they'd rather have nothing?

The grammar of intropatterns is as follows.

.. productionlist:: coq
   i_item : `i_pattern` | `s_item` | `clear_switch` | /`term`
   s_item : `/=` | // | //=
   i_pattern : `ident` | _ | ? | * | [`occ_switch`]-> | [`occ_switch`]<-
             : | [ `i_item` ... `i_item` | ... | `i_item` ... `i_item` ]
             : | /[ `i_item` ... `i_item` | ... | `i_item` ... `i_item` ]

Each `i_pattern` performs an introduction operation:

.. tacn:: => @ident

   Introduces the next item with name x.

.. tacn:: => ?

   Introduces the next item with a generated name.

.. tacn:: => _

   Introduces and clear the next item.

   Importantly, the clear operation is delayed until
   the end of the interpretation of the arguments of
   the current ``=>`` tactic. This is motivated by the
   need to prevent errors when the variable has 
   dependent occurences.

   Remark: 

   .. coqdoc::
      Goal forall x y, y = y.
      => _ x. (*** fails, as a result of the delayed clear ***)

.. tacn::  => >

   Introduces all forall-quantified variables that are 
   visible at the head of the goal and that have dependent
   occurences.

   These variables are introduced, but using names that
   cannot be mentioned in scripts.

   If the goal does not contain any head quantification,
   then the tactic attempts to reveal one by unfolding
   head constants and performing beta/iota/... reductions
   on the head of the goal.

   .. todo::
      ?? We are not really sure about which reductions should
      be performed; it may also be possible to not attempt any.
   
   If these reductions are not able to reveal any forall-quantified 
   variables, then the introduction tactic does nothing.
   
   The typical use case if after an inversion, for allowing
   to name only the hypotheses.

.. tacn::  => *
  
   Introduces all the variables that are visible.
   The variables are introduced, but using names that
   cannot be mentioned in scripts.

   .. todo::
      ?? What kind of reductions should be performed when
      no variable is visible at the head of the goal?

.. tacn:: => *-

   Introduces all the variables that are visible,
   until the next mark, and consuming this mark.
   The pattern fails if there is no mark in the goal.

   Motivation: marks are introduced by tactics such as
   inversion, which produce unpredictable number of 
   variables in the goal, so that the user may introduce
   all these fresh variables, but not the older ones.

   .. todo::
      ?? btw, what is the syntax for pushing a mark onto the goal?
   
.. tacn:: => -

   Expects a mark at the head of the goal, and clears it.
   It fails if there is no mark at the head of the goal.
  
.. tacn:: => --

   Decoration intropattern. 

   .. todo::
      ?? it's likely that this is no longer technically needed;
      now, the user may still like it as documentation?

.. tacn:: =>  prefix^-

   Introduces all variables until the next mark,
   by assigning them names that are obtained by
   concatenating the given prefix with the name
   obtained from the inductive definition (i.e. the 
   name produced by default by the "inversion" tactic).

.. tacn:: => ^suffix-

   Same as above, except adding a suffix rather than a prefix.

.. tacn:: => /[ ipats1 | ipats2 | .. | ipatsN ]

   This intropattern allows branching according to the various
   subgoals generated so far.

   If the number of branches does not match the current number 
   of subgoals, the tactic fails.

   In general, the tactic:
   ``=> ipat /[ ip1 | ip2 ]``.
   is essentially equivalent to:
   ``=> ipat; [ => ip1 | => ip2 ]``.
   The only difference being related to delayed clearing with ``_``.

   .. todo::
      ?? Remark: we convinced ourselves that the existing Ltac syntax 
      ``intros ip; [> intros ip1 | intros ip2 ]``.
      is not any useful.

   If "ipatsN" is a triple-dot ("..."), then all the remaining
   branches are solved using the same tactic as that provided
   for the previous-to-last branch.

.. tacn:: => []

   This is a shorthand for "/case".

   .. todo::
      ?? we could make it a shorthand for "/invert" instead?

.. tacn:: => [ ipats1 | ipatsN | .. ] 
    
   This is a shorthand for "/case /[ .. | .. ]".

.. tacn:: =>  /tac  
.. tacv:: => /(tac arg1 .. argN)      

   The slash is a generic mechanism for calling a tactic from
   where an intropattern is expected. Thus, "/tac" executes
   the tactic "tac", when "tac" consists of a single identifier.
   For calls with arguments, parentheses are needed.
                       
.. tacn:: => /n:tac
.. tacv:: => /n:(tac arg1 .. argN)  
   
   The goal selector "n:" allows to execute "tac" only on the
   n-th subgoal.
   
   Importantly, the numbering of goals is local.
   The examples below illustrate what is meant by "local".

   ``=> [A|B]; (=> [C|D] /2:foo)``
   here tactic foo applies to goal AD and BD

   ``=> [A|B] [C|D] /2:foo``
   here tactic foo applies to goal AD

   ``=> [A|B] /[ x | y ] /2:foo``
   here "intros x" comes after A, 
   and "intros y; foo" comes after B

   ``=> [A|[B|C]] /3:foo``
   produces 3 sugoals on the same level, foo applies to C

   ``=> [A|B] /[ | /2:foo ]``
   here we have an error because "/2:foo" is invoked
   in a context that has a single goal (branch B).

   ``=> [A|B] /[ | [C|D] /2:foo ]``
   here tactic foo applies to BD

.. tacn:: => //

   This intro-pattern is equivalent to ``/tactic_slash``.
   By convention, this tactic has the purpose of executing 
   some form of automation that may kill the goal.

.. tacn:: => /-
                      
   This intro-pattern is equivalent to ``/(solve[tactic_slash])``.
   By convention, this tactic has the purpose of executing 
   some form of automation that must kill the goal.

   For example:
   ``=> [/-|B]``.
   is like 
   ``=> [A|B] /1:(solve[tactic_slash])``.

.. tacn:: =>  /=

   This intro-pattern is equivalent to "/tactic_equal".
   By convention, this tactic has the purpose of executing 
   some form of normalization process.

.. tacn:: => /:term   

   This intro-pattern is equivalent to /(move: term).
   It thus adds  "term" to the head of the goal.

   .. todo::
      ?? do we really need this intropattern?
      ?? thus is "/:-" valid syntax for introducing a mark in the goal?
      does this not look too much like a smiley? :-/

.. tacn:: => ->

   This intro-pattern is equivalent to "/(rewrite ->)" 
   with the head hypothesis. It clears this hypothesis.
   Generalization: [occswitch]->. 

   Side-conditions generated as a result of the rewriting
   are delayed until the end of the introduction pattern.

   .. todo::
      ?? does this really mean that we have no way of discharging
      those side conditions as we go? is this what we want?

.. tacn:: => <-

   This intro-pattern is like the previous one, for rewriting,
   except that it performs rewriting in the opposite direction.
    
.. tacn:: => ``/view``

   This intropattern applies the view "view". 
   It is equivalent to:
   ``intro H; move: (regeneralize_constr:(#view H))``.

   .. todo::
      ?? how do we resolve the ambiguity between /tac and /view ? 
      Proposal 1: accept ambiguity between term and tactics,
      and in case of conflict require explicit resolution by
      a selector, e.g.  /tac:(foo) /term:(foo).
      Proposal 2: we require view lemmas to be lifted into
      the tactics namespace, through use of a manual tactic
      declaration or use of a new top-level mechanism, e.g.
      "View Lemma foo" or "Add Existing View foo".
      Other proposals?

.. todo::
   Question: should we have {H} as intropattern, which introduces nothing
   and clears H (and its dependencies)? The problem is that we would like
   to execute it right now, whereas the general semantics of {H} is to
   delay to the end of the tactic. One possible semantics: rename H on the
   fly, and delete later the renamed hypothesis. Alternatively, we can
   interpret that each intropattern is in fact a tactic, and thus delaying
   "clear H" to the end of the current tactic does not lead to a delay.

.. coqdoc::
   => [] {H} /(apply H)           => should fail
   => [] /(apply {H}) (apply H)   => should fail? to discuss
   ==> arthur thinks it is simpler to interpret each intropattern
        as the execution of one independent tactic.


Some examples: 

.. todo ::
  ?? this list needs to be updated, completed and documented.

    .. coqdoc::
       => H
       => /invert [x y H | > H1 H2 | *- ]
       => /invert /[ toto_^- | .. ]
       => /invert /[ -^1 | .. ]
       => /andb[H1 H2] (* on the goal "a && b -> G" *)
       => [H1|H2]
       => /invert /[H1|H2]    
       => /invert [H1|H2]  
       => /invert[H]
       => /eqP H - H2
       => /pdivP[p p_prime p_dvdv_X]
       case: H => x1 x2 - H
       elim n => [ // | Hind ].
       elim: n => [ [] // | Hind].
       induct M => [ /- | > H1 H2 | x H ].

.. todo::
   ?? It seems that in ssreflect, chained views "/view1/view2"
   have a special semantics. However, we would like to make
   space not relevant if possible, thus "/view1 /view2" should
   be the same as "/view1/view2". So, how to accomodate for a
   different semantics for chained views?
   Proposal 1: using tilde composition symbol for chained views:
   ``/view1~/view2``
   Proposal 2: using a tactic named "view" that takes as argument a
   list of view lemmas:
   ``/(view view1 view2)``
   Other proposals?

.. todo::
   Remark: the following introduction patterns are free.
   We may either treat them as reserved keywords,
   or bind them to user-customizable tactics.
   I suggest we keep them as keywords for future use.

   /+               ... (free)
   /*               ... (free)
   /$               ... (free)
   /&               ... (free)
   /|               ... (free)
   etc..

  Besides, we have not used the { } or ( ) as intropatterns,
  we should also keep them for future use.


----------------

- Motivation: we don't need (a&b&c).
  
- Motivation: we don't need (a,b,c) in the grammar of patterns.

- Motivation: we can interpret "exists x y z, A /\ B /\ C"
   as either  "exists x, exists y, exists z, A /\ (B /\ C)"
   or as      "exists3 x y z, conj3 A B C",
   scripts should work either way. In other words, we have a 
   properly of "independence w.r.t. internal representation of
   n-ary conj/disj/exists".

- For the common operators /\ and \/ and "exists", we register
  them as being "right-associative in intropattern" via e.g.:

    Constructor Right Associative conj.

- One can destruct the term (A /\ B /\ C)
  as [a b c] instead of [a [b c]]. The formal semantics is: 
  if we have a destructing pattern (starting with a bracket) 
  and if the head constructor of the term being destructed
  is registered as right-associative intropattern,
  and if there are more than 2 names provided, then
  interpret "[a1 a2 .. an]" as "[a1 [a2 .. an]]".
  
- Meaning [a [b c]] can be replaced by [a b c] when [b c] is
  an inductive with the same head constructor.

- Example: "A /\ B /\ C" can be decomposed using "[a b c]".

- Example: "exists3 x y z, conj3 A B C" can be decomposed
  using "[x y z [A B C]]". 
  (compatibility with existing ssr scripts).
  (remark: exists3 might not exist)

- Example: "exists x y z, A /\ B /\ C" can be decomposed
  using "[x y z [a b c]]". 

- Example: "A /\ exists x, C x"  CANNOT be decomposed using
  "[a b c]" because the constructor for the second argument 
  is not the same constructor as the one of the current term 
  being destructed

- Constructor Left Associative pair.
  Example: [a b c] as valid intropattern for (x,y,z).

- Question: should we keep the tuple notation? we vote not.

- Question: can we get rid of "conj3" style? It seems so for
  intros, but what about inversion on A /\ B /\ C, should it
  destruct only the head or everything.
  Same question for "exists3 x y z, P", what should inversion
  do?
  Answer: if inversion and destruct always name the branches,
  it is not needed to keep the exists3/conj3 style.

  A /\ B /\ C -> A /\ (B /\ C).



Discharge
=========
