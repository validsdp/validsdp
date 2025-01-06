libValidSDP
===========

libValidSDP is a library for the Coq formal proof assistant. It provides
results mostly about rounding errors in the Cholesky decomposition algorithm
used in the ValidSDP library which itself implements Coq tactics to prove
multivariate inequalities using SDP solvers.

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.12.x or later
- [Bignums](https://github.com/coq/bignums) (Coq version specific)
- [mathcomp](https://math-comp.github.io/math-comp/) (version 1.12.0 or later)
- [mathcomp reals stdlib](https://github.com/math-comp/analysis/) (version 1.8.0 or later)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.4.1)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.2.0)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 4.3.0)

See also the [coq-libvalidsdp.opam](../coq-libvalidsdp.opam) file for the
detail of libValidSDP dependencies' version contraints.

Install the stable version with OPAM
------------------------------------

libValidSDP can be easily installed using [OPAM](https://opam.ocaml.org),
to do this you will just need to run:

    $ opam install --jobs=2 coq-libvalidsdp

libValidSDP and all its dependencies are hosted in the
[opam-coq-archive](https://github.com/coq/opam-coq-archive) project,
so you will have to type the following commands beforehand, if your
OPAM installation does not know yet about this OPAM repository:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update

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

Overview of the libValidSDP files
---------------------------------

### Prerequisites

* [misc.v](./misc.v): Miscellaneous lemmas
* [bounded.v](./bounded.v): Real numbers with bounded absolute value
* [real_matrix.v](./real_matrix.v): Basic results about matrices over the reals

### Arithmetic model

* [float_spec.v](./float_spec.v): **Specification of a "standard model" of floating-point arithmetic**
* [float_infnan_spec.v](./float_infnan_spec.v): Extension of this specification with overflow

### Results

* [fsum.v](./fsum.v): **Bounds on the rounding error of sums in any summation order**
* [fsum_l2r.v](./fsum_l2r.v): Instanciation for the left-to-right order
* [fcmsum.v](./fcmsum.v): Error bounds on `c - \sum_{i=0}^n x_i`, `c` float and `x` in R^n
* [cholesky.v](./cholesky.v): **Application: proof of a positive definiteness check**
* [cholesky_infnan.v](./cholesky_infnan.v): **Extension of this proof with overflows** (see also the corresponding tactic in [`posdef_check.v`](https://github.com/validsdp/validsdp/blob/master/theories/posdef_check.v))

### Instances

* [flx64.v](./flx64.v): Proof that the Flocq format "FLX, precision-53" is a `Float_spec` instance
* [binary64.v](./binary64.v): Proof that the IEEE-754 binary64 format without overflow (formalized as FLT in Flocq) is a `Float_spec` instance
* [binary64_infnan.v](./binary64_infnan.v): Same for the `Float_infnan_spec` with overflows
* [zulp.v](./zulp.v): Helper formalization of `ulp`s (unit in the last place) for signed integers
* [`coqinterval_infnan_31.v`](./coqinterval_infnan_31.v): Proof that the precision-53 restriction of CoqInterval's `Interval_specific_ops` is a `Float_spec` instance (before Coq 8.10)
* [`coqinterval_infnan_63.v`](./coqinterval_infnan_63.v): Same for Coq 8.10+
