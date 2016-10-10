load 'test_MC11.sage'

polynomial_ring = PolynomialRing(QQ, ['x1','x2','x3','x4','x5','x6'])

rhs = polynomial_ring('-1/100000000 + 2 / 25   * ((- 2/1) * x4 * x4 * x4 * x4 * x4 * x1      + 256/1        * (x5 + (- 1/1) * x6) * (x5 + (- 1/1) * x6) * (x5 + (- 1/1) * x6)          * (x2 + (- 1/1) * x3)        + x4 * x4 * x4          * (2/1 * ((- 256/1) + x5 * x5 + (- 2/1) * x5 * x6 + x6 * x6) * x1             + (x5 * x5 * ((- 8/1) + x6)                + (- 16/1) * x5 * (3/1 + x6) + 16/1 * (16/1 + 9/1 * x6))               * x2               + (x5 * (144/1 + (- 16/1) * x6 + x6 * x6)                  + (- 8/1) * ((- 32/1) + 6/1 * x6 + x6 * x6))                 * x3)          + 2/1            * x4 * x4 * x4 * x4              * (32/1 * x1 + 3/1 * (((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))            + 200/1              * (x4 * x4 * x1                 + 8/1 * (x5 + (- 1/1) * x6) * (x2 + (- 1/1) * x3)                   + (- 1/1)                     * x4                       * (16/1 * x1                          + ((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))                * (x4 * x4 * x1                   + 8/1 * (x5 + (- 1/1) * x6) * (x2 + (- 1/1) * x3)                     + (- 1/1)                       * x4                         * (16/1 * x1                            + ((- 8/1) + x5) * x2 + ((- 8/1) + x6) * x3))              + 2/1                * x4 * x4                  * (x5 + (- 1/1) * x6)                    * (x5 * x5 * x2                       + 8/1 * x6 * (4/1 * x1 + 9/1 * x2 + (- 7/1) * x3)                         + 384/1 * (x2 + (- 1/1) * x3)                           + (- 1/1) * x6 * x6 * x3                             + x5                               * ((- 32/1) * x1                                  + (56/1 + (- 9/1) * x6) * x2                                    + 9/1 * ((- 8/1) + x6) * x3))                + (- 16/1)                  * x4                    * (x5 + (- 1/1) * x6)                      * (x5 * x5 * (x2 + (- 3/1) * x3)                         + (- 4/1)                           * x5                             * (8/1 * x1                                + ((- 20/1) + 3/1 * x6) * x2                                  + (- 3/1) * ((- 4/1) + x6) * x3)                           + x6                             * (32/1 * x1                                + 3/1 * (16/1 + x6) * x2                                  + (- 1/1) * (80/1 + x6) * x3)))')

lhs = [polynomial_ring('(x1 - 1) * (117547965573 / 100000000000 - x1)'), polynomial_ring('(x2 - 1) * (117547965573 / 100000000000 - x2)'), polynomial_ring('(x3 - 1) * (117547965573 / 100000000000 - x3)'), polynomial_ring('(x4 - 251952632905 / 100000000000) * (1553 / 100 - x4)'), polynomial_ring('(x5 - 251952632905 / 100000000000) * (16 / 1 - x5)'), polynomial_ring('(x6 - 251952632905 / 100000000000) * (16 / 1 - x6)')]

check = test_MC11(polynomial_ring, lhs, rhs)

if check:
  print 'proved: true'
else:
  print 'proved: false'
