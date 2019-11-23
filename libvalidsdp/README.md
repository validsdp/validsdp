libValidSDP
===========

libValidSDP is a library for the Coq formal proof assistant. It provides
results mostly about rounding errors in the Cholesky decomposition algorithm
used in the ValidSDP library which itself implements Coq tactics to prove
multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.11.x
- [Bignums](https://github.com/coq/bignums) (Coq version specific)
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.8.0 and 1.9.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.2.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.3)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (branch primitive-floats)

See also the [coq-libvalidsdp.opam](../coq-libvalidsdp.opam) file for the
detail of libValidSDP dependencies' version contraints.

Install the dev version with Autoconf and OPAM
----------------------------------------------

If you rely on [OPAM](https://opam.ocaml.org) to manage your Coq
installation, you can install the libValidSDP library by doing:

    $ opam pin add -n -y -k path coq-libvalidsdp.dev ..
    $ opam install --jobs=2 coq-libvalidsdp

All libValidSDP dependencies are hosted in the
[opam-coq-archive](https://github.com/coq/opam-coq-archive) project,
so you will have to type the following commands beforehand, if your
OPAM installation does not know yet about this OPAM repository:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update

Build the dev version with Autoconf and Make
--------------------------------------------

We assume you have [Autoconf](https://www.gnu.org/software/autoconf/)
and a Coq installation managed by [OPAM](https://opam.ocaml.org).

Then, you can install the libValidSDP dependencies by doing:

    $ opam pin add -n -y -k path coq-libvalidsdp.dev ..
    $ opam install --jobs=2 coq-libvalidsdp --deps-only

Finally, you can build and install the libValidSDP library by doing:

    $ ./autogen.sh && ./configure && make && make install

Note that the command above is necessary if you build the dev version
of libValidSDP (e.g. from a git clone) while the release tarballs already
contain a `configure` script, so in this case you'll just need to run:

    $ ./configure && make && make install

Documentation
-------------

To generate documentation from the Coq code, you should just have to
run:

    $ make doc

The documentation can then be browsed from the page `html/toc.html`
with your favorite browser.
