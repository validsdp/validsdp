libValidSDP
===========

libValidSDP is a library for the Coq formal proof assistant. It provides
results mostly about rounding errors in the Cholesky decomposition algorithm
used in the ValidSDP library which itself implements Coq tactics to prove
multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.10.x or 8.9.x or 8.8.x or 8.7.x
- [Bignums](https://github.com/coq/bignums) (Coq version specific)
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.8.0 and 1.9.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.2.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.3)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 3.4.1)

See also the [coq-libvalidsdp.opam](../coq-libvalidsdp.opam) file for the
detail of libValidSDP dependencies' version contraints.

Installation
------------

All dependencies can be easily installed with [OPAM](https://opam.ocaml.org/).
Once OPAM is installed, run:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update
    $ opam install --jobs=2 coq coq-interval coq-mathcomp-field

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
