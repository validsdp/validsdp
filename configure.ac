#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([ValidSDP], [1.0.4-git])
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
AX_VERSION_GE([$coq_version], 8.18, [],
  [ AC_MSG_ERROR([must be at least 8.18.]) ])
AC_CHECK_TOOL([OCAMLFIND], [ocamlfind], [no])
AS_IF([test "x$OCAMLFIND" = xno], [AC_MSG_ERROR([Cannot find ocamlfind.])])

# Check for libraries
AC_MSG_CHECKING([for Ltac2])
COQTOP_WHERE=`coqtop -where`
LTAC2_DIR="${COQTOP_WHERE}-core/plugins/ltac2"
AS_IF([test -d ${LTAC2_DIR}],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find Ltac2 which should be installed with Coq])])
COQ_VERSION="v818"
SOSWIT_PLUGIN_EXT="coq-validsdp.plugin"
SOSWIT_PLUGIN="soswitness:coq-validsdp.plugin"
META_FILE="plugins/soswitness/src/META.coq-validsdp"
CAMLPKGS="-package coq-core.plugins.ltac2 \
  -package zarith \
  -package logs \
  -package ocplib-simplex \
  -package osdp"
AC_SUBST(COQ_VERSION)
AC_SUBST(SOSWIT_PLUGIN)
AC_SUBST(SOSWIT_PLUGIN_EXT)
AC_SUBST(META_FILE)
AC_SUBST(CAMLPKGS)

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
  [ echo "From mathcomp Require Import Rstruct." > conftest.v
    $COQC conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find theory Rstruct from coq-mathcomp-reals-stdlib])])
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

AC_MSG_CHECKING([for Multinomials])
AS_IF(
  [ echo "From mathcomp Require Import ssreflect ssrfun." \
    	 "From mathcomp.multinomials Require Import mpoly freeg." > conftest.v
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
    AC_MSG_ERROR([ *** Unable to find library OSDP >= 1.1.1 (https://github.com/Embedded-SW-VnV/osdp).])])

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
AC_CONFIG_FILES([Makefile Makefile.coq.local _CoqProject plugins/soswitness/theories/soswitness_plugin.v])
AC_OUTPUT
chmod a-w Makefile Makefile.coq.local _CoqProject plugins/soswitness/theories/soswitness_plugin.v

echo ""
echo "  Now run 'make && make install' to build and install $PACKAGE_NAME $PACKAGE_VERSION"
echo "  (or run 'make help' to get for more info on the available rules)"
echo ""
