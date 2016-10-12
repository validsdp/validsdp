#!/bin/sh

DIRS="global flyspeck prog_invs"
PROVERS="Sdpa Coq Bernstein MC11 nlcnocoq nlccoq"
TIMEOUT="900"

DESCRS=""
for d in ${DIRS} ; do
  DESCRS2=$(cat ${d}/descr | sed -e "/^#/d;s|^|${d}/|;s| |,|g")
  DESCRS="${DESCRS} ${DESCRS2}"  
done

printf "\\\\begin{tabular}{p{2.8cm}cccccccc}\n"
printf "Problem & \$n\$ & \$d\$ & OSDP & Validsdp & PVS/Bern & MC11 & nlcnocoq & nlccoq \\\\\\\\\n"

PREVDIR="."
for fnd in ${DESCRS} ; do
  f=$(echo ${fnd} | cut -f1 -d,)
  n=$(echo ${fnd} | cut -f2 -d,)
  d=$(echo ${fnd} | cut -f3 -d,)
  DIR=$(echo ${f} | cut -f1 -d/)
  FILENAME=$(echo ${f} | cut -f2 -d/)
  if [ ${DIR} != ${PREVDIR} ] ; then
    printf "\\\\hline\n"
  fi
  PRF=$(echo ${FILENAME} | sed -e 's/\_/\\_/g')
  printf "${PRF} & ${n} & ${d}"
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
      MC11)
        if $(grep -q "proved: true" ${LOG}) ; then
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

printf "\\\\end{tabular}\n"
