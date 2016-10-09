#!/bin/sh

EXSML=$(find global flyspeck prog_invs -name "*.ml" | grep -v "parse.ml" | grep -v "_build/")
PROVERS="Sdpa Coq Bernstein nlcnocoq nlccoq"
TIMEOUT="900"

printf "\\\\begin{tabular}{p{4.2cm}ccccc}\n"
printf "Problem & OSDP & Validsdp & PVS/Bern & nlcnocoq & nlccoq \\\\\\\\\n"

PREVDIR="."
for f in ${EXSML} ; do
  DIR=$(echo ${f} | sed -e 's|/.*||')
  FILENAME=$(echo ${f} | sed -e 's|.*/||;s/\.ml//')
  if [ ${DIR} != ${PREVDIR} ] ; then
    printf "\\\\hline\n"
  fi
  PRF=$(echo ${FILENAME} | sed -e 's/\_/\\_/g')
  printf "${PRF}"
  for p in ${PROVERS} ; do
    LOG="${DIR}/${FILENAME}_${p}_${TIMEOUT}s.log"
    OK=0
    TIME="---"
    if [ -f ${LOG} ] ; then
      case $p in
      Sdpa)
        if $(grep -q "proved: true" ${LOG}) ; then
          OK=1
        fi
        ;;
      Coq)
        if [ -f "${DIR}/${FILENAME}.vo" ] ; then
          OK=1
        fi
        ;;
      Bernstein)
        NBP=$(grep "Grand Totals: " ${LOG} | sed -e 's/Grand Totals: //;s/ proofs.*//')
        NBS=$(grep "Grand Totals: " ${LOG} | sed -e 's/.*attempted, //;s/ succeeded.*//')
        if [ "x${NBP}" != "x" -a "x${NBP}" = "x${NBS}" ] ; then
          OK=1
        fi
        ;;
      nlc*coq)
        if $(grep -q "^Inequality ${FILENAME} verified$" ${LOG}) ; then
          OK=1
        fi
        ;;
      esac
      if [ ${OK} = "1" ] ; then
        TIME=$(grep "^\[runlim\] real:" ${LOG} | sed -e 's/^\[runlim\] real:[ \t]*//;s/ seconds//')
      fi
    fi
    printf " & ${TIME}"
  done
  printf " \\\\\\\\\\n"
  PREVDIR=${DIR}
done
printf "\\\\hline\n"

printf "\\\\end{tabular}\n"
