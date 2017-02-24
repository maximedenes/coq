===========================================
 The Ssreflect proof language
===========================================

------------
Introduction
------------
.. cite 4 colors and FT

Ssreflect was originally designed in the context of formalized mathematics
to support the development of large mathematical proofs and libaries, and
to support a formalization technique called small scale reflection.

Ssreflect has since then evolved toward a more general purpose proof language,
and can now be used in a wide range of ...
In particular, some new constructs make it easier to use the language in PL
contexts and existing constructs have been generalized to support a variety
of paradigms.


The language is built around a few fundamental principles:

Documentation
=============
The language is described in rigorous prose, precise enough to serve as a
specification for implementing it and testing it.

.. Pointers to other documentation sources

Uniformity
==========
All language constructs share the same building blocks both syntactically
and semantically. For example, tactics like "set" and "rewrite" that need
to search for a subterm matching a pattern all share the same pattern syntax
and matching algorithm.

Script maintanability
=====================
In the course of a development, proof scripts need to be adjusted to changes
in definitions or statements they depend on. Ssreflect provides basic blocks
that will report these errors as close as possible from the actual source
of breakage.

Extensibility
=============
Many formalization contexts require to embed domain-specific logic frameworks
inside the one Coq (e.g. use custom connectives). Eventhough these logical
frameworks can be very different, the proof steps can be of similar nature
(e.g. introducing an hypothesis, splitting a conjunction). Ssreflect makes
it possible to rebind all basic constructs of the proof language to
domain-specific ones.

------------
Related work
------------

Other tactics
=============
can be called by switching proof modes

and for convenience some of them can be called directly (TODO document)

combined with some language constructs

Ltac
====
"In a proof system, we can generally distinguish between two kinds of languages:
a proof language, which corresponds to basic or more elaborate primitives and
a tactic language, which allows the user to write his/her own proof schemes."
.. A Tactic Language for the System Coq -- David Delahaye

Ssreflect is a language of the first kind, and hence can be used inside
Ltac's proof schemes.

.. Is it compatible with Ltac2?


.. contents::
   :local:

.. toctree::
   :maxdepth: 10

   bookkeeping
   forward-reasoning
   backward-reasoning
   matching
   equality
   second-order
