ValidSDP
========

Dependencies
------------

- [Coq](https://coq.inria.fr) version 8.6.x
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.6.1)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 2.5.2)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.0)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 3.2.0)
- [OSDP](https://cavale.enseeiht.fr/osdp) (tested with version 0.5.3)
- [paramcoq](https://github.com/CohenCyril/paramcoq.git) (dev. version)
- [CoqEAL](https://github.com/CoqEAL/CoqEAL/tree/paramcoq-dev) (dev. version)
- [multinomials](https://github.com/math-comp/multinomials.git) (dev. version)

Remark
------

For the libraries tagged above as "dev. version" you may get more info
(the SHA-1 of the corresponding commits) by cloning our Git repository
and running `git submodule status`. However these libraries need not
be retrieved and installed manually: they are available in the
"external" folder and their installation can be automated (see below).

Installation
------------

Most of the dependencies (Coq, mathcomp, Flocq, Coquelicot,
Coq-interval and OSDP) can be easily installed with
[OPAM](https://opam.ocaml.org/).
Once OPAM is installed, run:

    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam update
    $ opam install coq coq-interval coq-mathcomp-field osdp

To ensure that you have these dependencies properly installed, run:

    $ ./configure

Then, to build and install paramcoq, CoqEAL, and multinomials, run:

    $ make external

Finally, to build and install ValidSDP, run:

    $ make install

Usage
-----

Examples of usage of the tactic can be found at the end of the
"theories/validsdp.v" file.

Documentation
-------------

To generate documentation from the Coq code:

    $ cd theories
    $ make doc

The documentation can then be browsed from "theories/html/toc.html"
with your favorite browser.
