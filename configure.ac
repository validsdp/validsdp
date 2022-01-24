#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([ValidSDP], [1.0.0-git])
AC_CONFIG_SRCDIR([theories/validsdp.v])

AC_DEFUN([AX_VERSION_GE], [AS_VERSION_COMPARE([$1],[$2],[$4],[$3],[$3])])

# Check for programs
AC_CHECK_TOOL([OCAMLC], [ocamlc], [no])
AS_IF([test "x$OCAMLC" = xno], [AC_MSG_ERROR([Cannot find ocamlc.])])

AC_CHECK_TOOL([COQC], [coqc], [no])
AS_IF([test "x$COQC" = xno], [AC_MSG_ERROR([Cannot find coqc.])])

AC_MSG_CHECKING(Coq version)
coq_version=`$COQC -v | grep version | sed -e 's/^.*version \([[0-9.+a-z]]*\).*$/\1/'`
AC_MSG_RESULT($coq_version)
AX_VERSION_GE([$coq_version], 8.11, [],
  [ AC_MSG_ERROR([must be at least 8.11.]) ])
AX_VERSION_GE([$coq_version], 8.13, [COQ_VERSION="v813"; LINK_ZARITH=""], [COQ_VERSION="v811"; LINK_ZARITH=" zarith.cmxa"])

AC_CHECK_TOOL([OCAMLFIND], [ocamlfind], [no])
AS_IF([test "x$OCAMLFIND" = xno], [AC_MSG_ERROR([Cannot find ocamlfind.])])

# Check for libraries
AC_MSG_CHECKING([for Ltac2])
# Ltac2 is installed wit Coq 8.11 but in different places
# whether it is compiled with Make or dune
COQTOP_WHERE=`coqtop -where`
LTAC2_MAKE="${COQTOP_WHERE}/user-contrib/Ltac2"
LTAC2_DUNE_814="${COQTOP_WHERE}-core/plugins/ltac2"
LTAC2_DUNE="${COQTOP_WHERE}/plugins/ltac2"
LTAC2_CAML_FILES=""
AS_IF([test -d ${LTAC2_MAKE}],
      [LTAC2_CAML_FILES="${LTAC2_CAML_FILES} -I ${LTAC2_MAKE}"], [])
AS_IF([test -d ${LTAC2_DUNE_814}],
      [LTAC2_CAML_FILES="${LTAC2_CAML_FILES} -I ${LTAC2_DUNE_814}"; COQ_VERSION="v814"],
      AS_IF([test -d ${LTAC2_DUNE}],
            [LTAC2_CAML_FILES="${LTAC2_CAML_FILES} -I ${LTAC2_DUNE}"], []))
AS_IF([test -n "${LTAC2_CAML_FILES}"],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find Ltac2 which should be installed with Coq >= 8.11])])
AC_SUBST(LTAC2_CAML_FILES)
AX_VERSION_GE([$coq_version], 8.15, [COQ_VERSION="v815"], [])
AC_SUBST(COQ_VERSION)
AC_SUBST(LINK_ZARITH)

AC_MSG_CHECKING([for Mathcomp])
AS_IF(
  [ echo "From mathcomp Require Import rat matrix countalg." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theories rat, matrix, countalg from mathcomp >= 1.12.0 (http://coq.io/opam/coq-mathcomp-field.1.12.0.html)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Mathcomp Analysis])
AS_IF(
  [ echo "Require Import mathcomp.analysis.Rstruct." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theory Rstruct from mathcomp anaysis (http://coq.io/opam/coq-mathcomp-analysis.0.3.5.html)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for Flocq])
AS_IF(
  [ echo "Require Import Flocq.Version BinNat." \
         "Goal (30100 <= Flocq_version)%N. easy. Qed." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Flocq >= 3.1 (http://flocq.gforge.inria.fr/)])])
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
osdp_version=`ocamlfind query -format %v osdp 2>/dev/null`
AX_VERSION_GE([$osdp_version], 1.0,
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library OSDP >= 1.0 (https://github.com/Embedded-SW-VnV/osdp).])])

AC_MSG_CHECKING([for coq-bignums])
AS_IF(
  [ echo "Require Import Bignums.BigQ.BigQ." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library Bignums.BigQ.BigQ (opam package coq-bignums)])])
rm -f conftest.v conftest.vo conftest.err

AC_MSG_CHECKING([for libValidSDP])
AS_IF(
  [ echo "From libValidSDP Require Import misc." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find library libValidSDP (cf. directory libvalidsdp)])])
rm -f conftest.v conftest.vo conftest.err

AC_CHECK_TOOL([SDPA], [sdpa], [no])
if test "x$SDPA" != xno; then
  SDPA_AVAILABLE="true"
  AC_MSG_NOTICE([Optional dependency sdpa was found. Assuming osdp was built accordingly.])
else
  SDPA_AVAILABLE=""
  AC_MSG_NOTICE([Optional dependency sdpa was not found.])
fi
AC_SUBST(SDPA_AVAILABLE)

# Create files
AC_CONFIG_FILES([Makefile _CoqProject])
AC_OUTPUT
chmod a-w Makefile _CoqProject

echo ""
echo "  Now run 'make && make install' to build and install $PACKAGE_NAME $PACKAGE_VERSION"
echo "  (or run 'make help' to get for more info on the available rules)"
echo ""
