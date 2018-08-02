#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([ValidSDP], [0.4-git])
AC_CONFIG_SRCDIR([theories/validsdp.v])

# Check for programs
AC_CHECK_TOOL([OCAMLC], [ocamlc], [no])
AS_IF([test "x$OCAMLC" = xno], [AC_MSG_ERROR([Cannot find ocamlc.])])

AC_CHECK_TOOL([COQC], [coqc], [no])
AS_IF([test "x$COQC" = xno], [AC_MSG_ERROR([Cannot find coqc.])])

AC_MSG_CHECKING(Coq version)
coq_version=`$COQC -v | grep version | sed -e 's/^.*version \([[0-9.+a-z]]*\).*$/\1/'`
majmin=`echo "$coq_version" | cut -d . -f "1 2"`
if test "v$majmin" != "v8.6" -a "v$majmin" != "v8.7"; then
  AC_MSG_ERROR([Coq version must be 8.6.x or 8.7.x (you have version $coq_version).])
fi
AC_MSG_RESULT($coq_version)

minor=`echo "$coq_version" | cut -d . -f 2`
if test "$minor" -le 6; then
  COQ_VERSION="v86"
  BIGNUMS_FROM=""
else
  COQ_VERSION="v87"
  BIGNUMS_FROM="From Bignums "
fi
AC_SUBST(COQ_VERSION)
AC_SUBST(BIGNUMS_FROM)

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
    cp conftest.v test.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Flocq >= 3.0 (http://flocq.gforge.inria.fr/)])])
#rm -f conftest.v conftest.vo conftest.err

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

AC_MSG_CHECKING([for Multinomials])
AS_IF(
  [ echo "From mathcomp Require Import ssreflect ssrfun." \
    	 "From SsrMultinomials Require Import mpoly freeg." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Multinomials >= 1.0 (https://github.com/math-comp/multinomials/)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for CoqEAL])
AS_IF(
  [ echo "From CoqEAL.refinements Require Import hrel refinements param binord binnat binint rational binrat multipoly." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library CoqEAL (https://github.com/CoqEAL/CoqEAL/tree/paramcoq-dev)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for OSDP])
AS_IF(
  [ req_maj="0"
    req_min="5"
    req_pat="2"
    osdp_version=`ocamlfind query -format %v osdp 2>/dev/null`
    major=`echo $osdp_version | cut -d . -f 1`
    minor=`echo $osdp_version | cut -d . -f 2`
    patch=`echo $osdp_version | cut -d . -f 3 | cut -d - -f 1`
    test "0$major" -gt "0$req_maj" || { test "0$major" -eq "0$req_maj" && \
      test "0$minor" -gt "0$req_min" || { test "0$minor" -eq "0$req_min" && \
        test "0$patch" -ge "0$req_pat"; }; } ],
  [ AC_MSG_RESULT($osdp_version) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library OSDP >= $req_maj.$req_min.$req_pat (https://cavale.enseeiht.fr/osdp/)])])
rm -f conftest.v conftest.vo conftest.err

if test "$COQ_VERSION" != "v86"; then
  AC_MSG_CHECKING([for coq-bignums])
  AS_IF(
    [ echo "Require Import Bignums.BigQ.BigQ." > conftest.v
      $COQC conftest.v > conftest.err ],
    [ AC_MSG_RESULT([yes]) ],
    [ AC_MSG_RESULT([no])
      AC_MSG_ERROR([ *** Unable to find library Bignums.BigQ.BigQ (opam package coq-bignums)])])
  rm -f conftest.v conftest.vo conftest.err
fi

# Create files
AC_CONFIG_FILES([Makefile plugins/soswitness/Makefile theories/Makefile theories/_CoqProject_${COQ_VERSION} theories/CBigZ.v theories/CBigQ.v theories/parse_reals.v])
AC_OUTPUT
chmod a-w Makefile plugins/soswitness/Makefile theories/Makefile theories/_CoqProject_${COQ_VERSION} theories/CBigZ.v theories/CBigQ.v theories/parse_reals.v
ln -frsv theories/_CoqProject_${COQ_VERSION} theories/_CoqProject

echo ""
echo "  Now run 'make external' to build and install extra Coq dependencies"
echo "  then run 'make install' to build and install $PACKAGE_NAME $PACKAGE_VERSION"
echo ""
