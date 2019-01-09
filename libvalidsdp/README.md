libValidSDP
===========

libValidSDP is a library for the Coq formal proof assistant. It provides
results mostly about rounding errors in the Cholesky decomposition algorithm
used in the ValidSDP library which itself implements Coq tactics to prove
multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.8.x or 8.7.x
- [Bignums](https://github.com/coq/bignums) (version 8.8 or 8.7 depending on Coq)
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.7.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.0.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.2)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 3.4.0)

Installation
------------

All dependencies can be easily installed with [OPAM](https://opam.ocaml.org/).
Once OPAM is installed, run:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update
    $ opam install --jobs=2 coq coq-interval coq-mathcomp-field camlp4

To ensure that you have these dependencies properly installed, run:

    $ ./configure

Finally, to build and install libValidSDP, run:

    $ make install

Documentation
-------------

To generate documentation from the Coq code, you should just have to
run:

    $ make doc

The documentation can then be browsed from "html/toc.html"
with your favorite browser.
