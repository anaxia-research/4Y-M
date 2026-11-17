#!/bin/bash
# Production runs; resumable: each run tops up its data file to NMEAS rows (fresh thermalisation on restart).
set -u
JL=${JULIA:-julia}; D=$(cd "$(dirname "$0")" && pwd); cd "$D"
NMEAS=2000
run(){ beta=$1; L=$2; Lt=$3; skip=$4; therm=$5
  f=data/b${beta}_L${L}_T${Lt}.dat; have=0; [ -f "$f" ] && have=$(grep -vc '^#' "$f")
  need=$((NMEAS-have)); [ $need -le 0 ] && { echo "skip $f ($have)"; return; }
  echo "run $f need $need"; $JL -t 4 su2mc.jl $beta $L $Lt $therm $need $skip $((RANDOM+have)) "$f" 2>>data/log.txt || echo "FAILED $f"
}
run 2.3 8 16 5 300
run 2.3 12 16 5 300
run 2.3 16 16 5 300
run 2.4 12 24 5 400
run 2.4 16 24 5 400
run 2.4 24 24 5 400
echo ALLDONE
