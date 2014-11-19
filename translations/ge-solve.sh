#!/bin/sh

PTABLES=./ptables
PTABLES2=./ptables2
SIMPLIFY=xcnf-simplify
XCNF2CNF=xcnf2cnf
SOLVER=$1
K2=$2
K3=$3
KV=$4
INSTANCE=$5
OUTPUT=$6
TMP=`tempfile`.cnf

$PTABLES --k2-limit $K2 --k3-limit $K3 --kv-limit $KV < $INSTANCE 2>/dev/null| $PTABLES2 2>/dev/null| $SIMPLIFY | $XCNF2CNF > $TMP
$SOLVER $TMP $OUTPUT
unlink $TMP
