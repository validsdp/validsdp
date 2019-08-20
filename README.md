ValidSDP
========

[![Build Status](https://travis-ci.com/validsdp/validsdp.svg?branch=libvalidsdp)](https://travis-ci.com/validsdp/validsdp)

ValidSDP is a library for the Coq formal proof assistant.  It provides
Coq tactics to prove multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.9.x or 8.8.x or 8.7.x
- [Bignums](https://github.com/coq/bignums) (Coq version specific)
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.8.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.2.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.3)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 3.4.1)
- [OSDP](https://cavale.enseeiht.fr/osdp) (tested with version 1.0.0)
- [multinomials](https://github.com/math-comp/multinomials) (tested with version 1.1)
- [paramcoq](https://github.com/coq-community/paramcoq) (tested with version 1.1.1)
- [CoqEAL](https://github.com/CoqEAL/CoqEAL) (tested with version 1.0.0)

See also the [coq-validsdp.opam](./coq-validsdp.opam) file for the
detail of ValidSDP dependencies' version contraints.

Remark
------

For CoqEAL you may get more info
(the SHA-1 of the corresponding commits) by cloning our Git repository
and running `git submodule status`. However these libraries need not
be retrieved and installed manually: they are available in the
"external" folder and their installation can be automated (see below).

Installation
------------

First install libValidSDP (see instructions in libvalidsdp/README.md).

Most of the remaining dependencies (Multinomials, paramcoq and OSDP)
can be easily installed with [OPAM](https://opam.ocaml.org/).
Once OPAM is installed, run:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update
    $ opam install --jobs=2 coq-mathcomp-multinomials coq-paramcoq osdp

To ensure that you have all dependencies properly installed, run:

    $ ./configure

Then, to build and install CoqEAL, run:

    $ make external

Finally, to build and install ValidSDP, run:

    $ make install

Usage
-----

This library provides the tactics `validsdp` and `validsdp_intro` for
proving inequalities on multivariate polynomials involving real-valued
variables and rational constants.

First, one has to import the validsdp Coq theory:

    From ValidSDP Require Import validsdp.

The main tactic `validsdp` accepts the following goals:

    ineq ::= (e1 <= e2)%R
           | (e1 >= e2)%R
           | (e1 < e2)%R
           | (e1 > e2)%R
    
    hyp ::= ineq
          | hyp /\ hyp
    
    goal ::= ineq
           | hyp -> goal

where `e1`, `e2` are terms of type `R` representing multivariate
polynomial expressions with rational constants. Anything else will be
interpreted as a variable.

The `validsdp` tactic also accepts options thanks to the following
syntax: `validsdp with (param1, param2, ...)`. Below is the list of
supported options:

- `s_sdpa` (*use the SDPA solver*)
- `s_csdp` (*use the CSDP solver*)
- `s_mosek` (*use the Mosek solver*)
- `s_verbose (verb : nat)` (*set the verbosity level, default: 0*)

Forward reasoning
-----------------

A tactic `validsdp_intro` is available to bound given polynomial
expressions (under polynomials constraints if desired). It introduces
the resulting inequalities as a new hypothesis in the goal.

The syntax is as follows:

- `validsdp_intro e` [`using (hyp1, ...)` | `using *`] [`with (param1, ...)`] `as` (`?` | `H` | `(Hl, Hu)`)
- `validsdp_intro e lower` [`using (hyp1, ...)` | `using *`] [`with (param1, ...)`] `as` (`?` | `Hl`)
- `validsdp_intro e upper` [`using (hyp1, ...)` | `using *`] [`with (param1, ...)`] `as` (`?` | `Hu`)

where `e` is a term of type `R` representing a multivariate polynomial
expression with rational constants and real-valued variables.

The syntax `using (hyp1, ...)` allows one to select the hypotheses
from the context to be considered by the solver. These hypotheses
should be multivariate polynomial inequalities with rational constants
and real-valued variables. They determine the input domain of the
considered optimization problem. The syntax `using *` will select
hypotheses from the context that are such inequalities. Otherwise
if the clause `using ...` is omitted, the polynomial expression `e` is
bounded over the whole vector space.

The syntax `as Hl` (resp. `as (Hl, Hu)`) allows one to specify the
name of the inequalities added to the context. 

The syntax `with (param1, ...)` supports the same options as the
`validsdp` tactic.

Examples
--------

    Require Import Reals.
    Local Open Scope R_scope.
    
    Goal forall x y : R, 0 <= y -> 2 / 3 * x ^ 2 + y + 1 / 4 > 0.
    intros x y.
    validsdp.
    Qed.
    
    Goal forall x y : R, -1 <= y <= 1 -> x * (x + y) + 1 / 2 >= 0.
    intros x y.
    validsdp.
    Qed.


Examples of usage of the tactic can be found at the end of the file
"theories/validsdp.v" as well as in the file "theories/testsuite.v"

Documentation
-------------

To generate documentation from the Coq code, you should just have to
run:

    $ cd theories
    $ make doc

The documentation can then be browsed from "theories/html/toc.html"
with your favorite browser.
