ValidSDP
========

Dependencies
------------

- [Coq](https://github.com/validsdp/coq) (primitive-floats branch)
- [bignums](https://github.com/maximedenes/bignums) (branch primitive-integers)
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.7.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.1.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.2)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (c.f. external/interval-3.4.0_v88alpha)
- [paramcoq](https://github.com/CohenCyril/paramcoq.git) (c.f. external/paramcoq_v88alpha)
- [CoqEAL](https://github.com/CoqEAL/CoqEAL/tree/paramcoq-dev) (c.f. external/CoqEAL_v88alpha)

Compilation
-----------

./autogen.sh
./configure
cd theories
make
