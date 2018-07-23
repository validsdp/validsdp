ValidSDP
========

Dependencies
------------

- [Coq](https://github.com/validsdp/coq) (primitive-floats branch)
- [bignums](https://github.com/coq/bignums) (tested with master (c03c1eb))
- [mathcomp](https://math-comp.github.io/math-comp/) (tested with version 1.7.0)
- [Flocq](http://flocq.gforge.inria.fr/) (tested with version 3.0.0)
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (tested with version 3.0.2)
- [Coq-interval](http://coq-interval.gforge.inria.fr/) (tested with version 3.4.0)
- [paramcoq](https://github.com/CohenCyril/paramcoq.git) (c.f. external/paramcoq_v89alpha)
- [CoqEAL](https://github.com/CoqEAL/CoqEAL/tree/paramcoq-dev) (c.f. external/CoqEAL_v89alpha)

Compilation
-----------

./autogen.sh
./configure
cd theories
make
