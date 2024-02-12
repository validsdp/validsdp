ValidSDP
========

[![CI](https://github.com/validsdp/validsdp/workflows/CI/badge.svg?branch=master)](https://github.com/validsdp/validsdp/actions?query=workflow%3ACI)

ValidSDP is a library for the Coq formal proof assistant.  It provides
Coq tactics to prove multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.16 or later
- [Bignums](https://github.com/coq/bignums) (Coq version specific)
- [mathcomp](https://math-comp.github.io/math-comp/) (version 2.0 or later)
- [mathcomp analysis](https://github.com/math-comp/analysis/) (version 1.0 or later)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.4.1)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.2.0)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 4.3.0)
- [OSDP](https://github.com/Embedded-SW-VnV/osdp) (tested with version 1.1.1)
- [multinomials](https://github.com/math-comp/multinomials) (tested with version 2.0)
- [paramcoq](https://github.com/coq-community/paramcoq) (tested with version 1.1.3)
- [CoqEAL](https://github.com/CoqEAL/CoqEAL) (tested with version 2.0.2)

See also the [coq-validsdp.opam](./coq-validsdp.opam) file for the
detail of ValidSDP dependencies' version constraints.

Install the stable version with OPAM
------------------------------------

ValidSDP can be easily installed using [OPAM](https://opam.ocaml.org),
to do this you will just need to run:

    $ opam install --jobs=2 coq-validsdp

ValidSDP and all its dependencies are hosted in the
[opam-coq-archive](https://github.com/coq/opam-coq-archive) project,
so you will have to type the following commands beforehand, if your
OPAM installation does not know yet about this OPAM repository:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update

Note that coq-validsdp does rely on a few system packages such as
conf-gmp or conf-csdp. If OPAM installation fails on those, you can
either install the system packages by hand or use the depext mechanism
of OPAM:

    $ opam install -y opam-depext  # install depext in the switch
    $ opam depext -u -i -y conf-gmp conf-csdp

Install the dev version with Autoconf and OPAM
----------------------------------------------

If you rely on [OPAM](https://opam.ocaml.org) to manage your Coq
installation, you can install the ValidSDP library by doing:

    $ opam pin add -n -y -k path coq-libvalidsdp.dev .
    $ opam pin add -n -y -k path coq-validsdp.dev .
    $ opam install --jobs=2 coq-validsdp

All ValidSDP dependencies are hosted in the
[opam-coq-archive](https://github.com/coq/opam-coq-archive) project,
so you will have to type the following commands beforehand, if your
OPAM installation does not know yet about this OPAM repository:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update

Build the dev version with Autoconf and Make
--------------------------------------------

We assume you have [Autoconf](https://www.gnu.org/software/autoconf/)
and a Coq installation managed by [OPAM](https://opam.ocaml.org).

Then, you can install the ValidSDP dependencies by doing:

    $ opam pin add -n -y -k path coq-libvalidsdp.dev .
    $ opam pin add -n -y -k path coq-validsdp.dev .
    $ opam install --jobs=2 coq-validsdp --deps-only

Finally, you can build and install the ValidSDP library by doing:

    $ ./autogen.sh && ./configure && make && make install

Note that the command above is necessary if you build the dev version
of ValidSDP (e.g. from a git clone) while the release tarballs already
contain a `configure` script, so in this case you'll just need to run:

    $ ./configure && make && make install

Documentation
-------------

To generate documentation from the Coq code, you should just have to
run:

    $ make doc

The documentation can then be browsed from the page `html/toc.html`
with your favorite browser.

Usage
-----

This library provides three tactics `validsdp`, `validsdp_intro` and
`posdef_check`. See the
[test-suite/testsuite.v](./test-suite/testsuite.v) file for examples
of the last tactic, to prove that matrices are symmetric positive
definite. The first two tactics prove inequalities on multivariate
polynomials involving real-valued variables and rational constants.

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

- `validsdp_intro e` [`using hyp1 ...` | `using *`] [`with (param1, ...)`] `as` (`?` | `H` | `(Hl, Hu)`)
- `validsdp_intro e lower` [`using hyp1 ...` | `using *`] [`with (param1, ...)`] `as` (`?` | `Hl`)
- `validsdp_intro e upper` [`using hyp1 ...` | `using *`] [`with (param1, ...)`] `as` (`?` | `Hu`)

where `e` is a term of type `R` representing a multivariate polynomial
expression with rational constants and real-valued variables.

The syntax `using hyp1 ...` allows one to select the hypotheses
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

    From ValidSDP Require Import validsdp.
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
[theories/validsdp.v](./theories/validsdp.v) as well as in the file
[test-suite/testsuite.v](./test-suite/testsuite.v)

Debug mode
----------

The `validsdp_intro` tactic has a debugging mode, enabled by writing:

```coq
Ltac2 Set deb := fun str => Message.print str.
```

License
-------

The ValidSDP and [libValidSDP](./libvalidsdp/) libraries are distributed under
the terms of the [GNU Lesser General Public License v2.1 or later](./LICENSE).
