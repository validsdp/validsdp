#!/bin/sh

DIRS="global flyspeck prog_invs"
PROVERS="Qepcad Sdpa MC11 nlcnocoq Coq Bernstein nlccoq Taylor"
TIMEOUT="900"

DESCRS=""
for d in ${DIRS} ; do
  DESCRS2=$(sed -e "/^#/d;s|^|${d}/|;s| |,|g" < "${d}/descr")
  DESCRS="${DESCRS} ${DESCRS2}"
done

printf "\\\\begin{tabular}{p{2.8cm}cccccccccc}\n"
printf "Problem & \$n\$ & \$d\$ & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {QEPCAD};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {OSDP\\\\\\\\[1pt](not verified)};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {Monniaux and\\\\\\\\[1pt]Corbineau 2011\\\\\\\\[1pt](not verified)};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {NLCertify\\\\\\\\[1pt](not verified)};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {ValidSDP};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {PVS/Bernstein};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {NLCertify};\\\\end{tikzpicture} & \\\\begin{tikzpicture}\\\\node[rotate=90,align=left] {HOL Light/Taylor};\\\\end{tikzpicture} \\\\\\\\\n"

PREVDIR="."
for fnd in ${DESCRS} ; do
  f=$(echo "${fnd}" | cut -f1 -d,)
  n=$(echo "${fnd}" | cut -f2 -d,)
  d=$(echo "${fnd}" | cut -f3 -d,)
  DIR=$(echo "${f}" | cut -f1 -d/)
  FILENAME=$(echo "${f}" | cut -f2 -d/)
  if [ "${DIR}" != "${PREVDIR}" ] ; then
    printf "\\\\hline\n"
  fi
  PRF=$(echo "${FILENAME}" | sed -e 's/\_/\\_/g')
  printf "%s & %s & %s" "${PRF}" "${n}" "${d}"
  for p in ${PROVERS} ; do
    LOG="${DIR}/${FILENAME}_${p}_${TIMEOUT}s.log"
    OK=0
    TIME="---"
    if [ -f "${LOG}" ] ; then
      case $p in
      Sdpa)
        if grep -q "proved: true" "${LOG}" ; then
          OK=1
        fi
        ;;
      Coq)
        if [ -f "${DIR}/${FILENAME}.vo" ] ; then
          OK=1
        fi
        ;;
      Bernstein)
        NBP=$(grep "Grand Totals: " "${LOG}" | sed -e 's/Grand Totals: //;s/ proofs.*//')
        NBS=$(grep "Grand Totals: " "${LOG}" | sed -e 's/.*attempted, //;s/ succeeded.*//')
        if [ "x${NBP}" != "x" -a "x${NBP}" = "x${NBS}" ] ; then
          OK=1
        fi
        ;;
      MC11)
        if grep -q "proved: true" "${LOG}" ; then
          OK=1
        fi
        ;;
      nlc*coq)
        if grep -q "^Inequality ${FILENAME} verified$" "${LOG}" ; then
          OK=1
        fi
        ;;
      Taylor)
        if grep -q -e "^\[runlim\] status:[ 	]*ok" "${LOG}" && ! grep -q -e "Error\|Exception\|Failure" "${LOG}" ; then
          OK=1
        fi
        ;;
      Qepcad)
        if grep -q -e "^FALSE" "${LOG}" ; then
          OK=1
        fi
        ;;
      esac
      if [ ${OK} = "1" ] ; then
        TIME=$(grep "^\[runlim\] real:" "${LOG}" | sed -e 's/^\[runlim\] real:[ \t]*//;s/ seconds//')
      fi
    fi
    printf " & %s" "${TIME}"
  done
  printf " \\\\\\\\\\n"
  PREVDIR=${DIR}
done

printf "\\\\end{tabular}\n"
