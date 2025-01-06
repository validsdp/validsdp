#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([libValidSDP], [1.0.4-git])
AC_CONFIG_SRCDIR([cholesky_infnan.v])

AC_DEFUN([AX_VERSION_GE], [AS_VERSION_COMPARE([$1],[$2],[$4],[$3],[$3])])

# Check for programs
AC_CHECK_TOOL([OCAMLC], [ocamlc], [no])
AS_IF([test "x$OCAMLC" = xno], [AC_MSG_ERROR([Cannot find ocamlc.])])

AC_CHECK_TOOL([COQC], [coqc], [no])
AS_IF([test "x$COQC" = xno], [AC_MSG_ERROR([Cannot find coqc.])])

AC_MSG_CHECKING(Coq version)
coq_version=`$COQC -v | grep version | sed -e 's/^.*version \([[0-9.+a-z]]*\).*$/\1/'`
AC_MSG_RESULT($coq_version)
AX_VERSION_GE([$coq_version], 8.18, [],
  [ AC_MSG_ERROR([must be at least 8.18.]) ])

AC_CHECK_TOOL([OCAMLFIND], [ocamlfind], [no])
AS_IF([test "x$OCAMLFIND" = xno], [AC_MSG_ERROR([Cannot find ocamlfind.])])

# Check for libraries
AC_MSG_CHECKING([for Mathcomp])
AS_IF(
  [ echo "From mathcomp Require Import rat matrix countalg." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theories rat, matrix, countalg from coq-mathcomp-field])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Mathcomp Analysis])
AS_IF(
  [ echo "Require Import mathcomp.analysis.Rstruct." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theory Rstruct from coq-mathcomp-analysis])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Flocq])
AS_IF(
  [ echo "Require Import Flocq.Version BinNat." \
         "Goal (30100 <= Flocq_version)%N. easy. Qed." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Flocq >= 3.3 (http://flocq.gforge.inria.fr/)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Coq-interval])
AS_IF(
  [ echo "From Interval Require Import Real.Xreal. " \
         "From Interval Require Import Float.Basic. " \
         "From Interval Require Import Float.Sig. " \
         "Declare Module F : FloatOps. " \
         "Check F.add_UP_correct." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Coq-interval master (http://coq-interval.gforge.inria.fr/)])])
rm -f conftest.v conftest.vo conftest.err

if test "$libdir" = '${exec_prefix}/lib'; then
  libdir="`$COQC -where`/user-contrib/Interval"
fi

AC_MSG_CHECKING([for coq-bignums])
AS_IF(
  [ echo "Require Import Bignums.BigQ.BigQ." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Bignums.BigQ.BigQ (opam package coq-bignums)])])
rm -f conftest.v conftest.vo conftest.err

# Create files
AC_CONFIG_FILES([Makefile _CoqProject])
AC_OUTPUT
chmod a-w Makefile _CoqProject

echo ""
echo "  Now run 'make && make install' to build and install $PACKAGE_NAME $PACKAGE_VERSION"
echo ""
