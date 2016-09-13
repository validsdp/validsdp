#!/bin/sh

# example of use: ./benchs log4_d4

../examples/trmx ../examples/${1} > ${1}.v
time coqc ${1}.v
