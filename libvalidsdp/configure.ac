#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([libValidSDP], [0.6-git])
AC_CONFIG_SRCDIR([cholesky_infnan.v])

# Check for programs
AC_CHECK_TOOL([OCAMLC], [ocamlc], [no])
AS_IF([test "x$OCAMLC" = xno], [AC_MSG_ERROR([Cannot find ocamlc.])])

AC_CHECK_TOOL([COQC], [coqc], [no])
AS_IF([test "x$COQC" = xno], [AC_MSG_ERROR([Cannot find coqc.])])

AC_MSG_CHECKING(Coq version)
coq_version=`$COQC -v | grep version | sed -e 's/^.*version \([[0-9.+a-z]]*\).*$/\1/'`
majmin=`echo "$coq_version" | cut -d . -f "1 2"`
if test "v$majmin" != "v8.7" -a "v$majmin" != "v8.8"; then
  AC_MSG_ERROR([Coq version must be 8.7.x or 8.8.x (you have version $coq_version).])
fi
AC_MSG_RESULT($coq_version)

minor=`echo "$coq_version" | cut -d . -f 2`
if test "$minor" -le 7; then
  COQ_VERSION="v87"
else
  COQ_VERSION="v88"
fi
AC_SUBST(COQ_VERSION)

AC_CHECK_TOOL([OCAMLFIND], [ocamlfind], [no])
AS_IF([test "x$OCAMLFIND" = xno], [AC_MSG_ERROR([Cannot find ocamlfind.])])

# Camlp4 is used to compile documentation
AC_MSG_CHECKING([for camlp4])
AS_IF(
  [ echo "" > conftest.ml
    $OCAMLC -o conftest -pp camlp4o conftest.ml > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find camlp4o (opam package camlp4)])])
rm -f conftest conftest.cmi conftest.cmo conftest.ml conftest.err

# Check for libraries
AC_MSG_CHECKING([for Mathcomp])
AS_IF(
  [ echo "From mathcomp Require Import rat matrix countalg." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theories rat, matrix, countalg from mathcomp >= 1.6.1 (http://coq.io/opam/coq-mathcomp-field.1.6.1.html)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Flocq])
AS_IF(
  [ echo "Require Import Flocq.Version BinNat." \
         "Goal (30000 <= Flocq_version)%N. easy. Qed." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Flocq >= 3.0 (http://flocq.gforge.inria.fr/)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Coq-interval])
AS_IF(
  [ echo "From Interval Require Import Interval_xreal. " \
         "From Interval Require Import Interval_definitions. " \
         "From Interval Require Import Interval_float_sig. " \
         "Declare Module F : FloatOps. " \
         "Check F.add_correct : forall mode p x y, " \
         "F.toX (F.add mode p x y) = Xround F.radix mode (F.prec p) (Xadd (F.toX x) (F.toX y))." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Coq-interval >= 3.2 (http://coq-interval.gforge.inria.fr/)])])
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
AC_CONFIG_FILES([_CoqProject])
AC_OUTPUT
chmod a-w _CoqProject

echo ""
echo "  Now run 'make install' to build and install $PACKAGE_NAME $PACKAGE_VERSION"
echo ""
