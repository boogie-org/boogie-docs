=============================================
The Boogie intermediate verification language
=============================================

The Boogie IVL (intermediate verification language) is a simple
language designed for verification which was originally created
by `Microsoft Research <http://research.microsoft.com/>`_.

The language is an "intermediate language" because it is designed to be
the middle part of a program verifier. A front-end translates a program
written in some language to the Boogie IVL and a back-end tries to verify
the translated program. This provides "separation of concerns" as

* The front-end does need to care about what method is used to
  verify the program.

* The back-end does not need to care about the semantics
  of several different programming languages. It only needs to care
  about the Boogie IVL.

This idea is analogous to the "intermediate representation" (IR)
used in modern compilers.

Language Design
===============

.. toctree::
  :maxdepth: 2
  
  LangRef

Front-ends that emit Boogie IVL
===============================

.. toctree::
  :maxdepth: 2

  Frontends

Back-ends that consume Boogie IVL
=================================

.. toctree::
  :maxdepth: 2

  Backends

Tutorials
=========

.. toctree::
  :maxdepth: 2
  :glob:

  Tutorials/*

Indices and tables
==================

* :ref:`genindex`
* :ref:`search`

