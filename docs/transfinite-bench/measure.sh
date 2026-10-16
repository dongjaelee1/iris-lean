#!/bin/bash
# TF=... UP=... measure.sh OUTDIR: compare the transfinite branch (TF) with upstream Iris-Lean (UP).
# TF and UP are repository checkouts in which `lake build` and `lake build IrisTest` have run.
#  1. every module and test file, single thread, 3 alternating rounds (bench.py: CPU, import time,
#     peak RSS, lean --profile categories);
#  2. clean builds of the Iris package with LEAN_NUM_THREADS=6, alternating, 2 each;
#  3. sizes as in upstream's scripts/bench/size (lines of .lean, bytes of .olean).
set -u
OUT=$(mkdir -p "$1" && cd "$1" && pwd)
TF=${TF:?set TF to a built checkout of transfinite}; UP=${UP:?set UP to a built checkout of upstream}
S=$(cd "$(dirname "$0")" && pwd); BENCH=$S/bench.py
dir() { if [ $1 = TF ]; then echo $TF; else echo $UP; fi; }
git -C $TF rev-parse HEAD > $OUT/TF.rev; git -C $UP rev-parse HEAD > $OUT/UP.rev
for r in 1 2 3; do
  if [ $((r % 2)) = 1 ]; then order="UP TF"; else order="TF UP"; fi
  for t in $order; do
    d=$(dir $t)
    python3 $BENCH $d/Iris --all --prefix Iris. -r 1 -j 1 -o $OUT/lib-$t-$r.json > $OUT/lib-$t-$r.txt 2>&1
    python3 $BENCH $d/Iris --all --prefix IrisTest. -r 1 -j 1 -o $OUT/test-$t-$r.json > $OUT/test-$t-$r.txt 2>&1
    echo "round $r $t done $(date +%T)" >> $OUT/progress
  done
done
python3 $BENCH $TF/Ordinals --all --prefix Ordinals. -r 3 -j 1 -o $OUT/ordinals-TF.json > $OUT/ordinals-TF.txt 2>&1
i=0
for t in UP TF TF UP; do
  i=$((i + 1)); d=$(dir $t)
  rm -rf $d/Iris/.lake/build; [ $t = TF ] && rm -rf $d/Ordinals/.lake/build
  (cd $d/Iris && LEAN_NUM_THREADS=6 python3 $S/timeit.py $OUT/build-$t-$i.json -- lake build > $OUT/build-$t-$i.log 2>&1)
  echo "clean build $i $t done $(date +%T)" >> $OUT/progress
done
for t in UP TF; do
  d=$(dir $t)
  (cd $d/Iris && python3 - > $OUT/size-$t.json <<'PY'
import json
from pathlib import Path
lean = [p for p in Path().rglob("*.lean") if ".lake" not in p.parts and "StepIndexChoices" not in p.parts]
olean = list(Path(".lake/build").rglob("*.olean"))
print(json.dumps({"lean_files": len(lean), "lean_lines": sum(len(p.read_text().splitlines()) for p in lean),
                  "olean_files": len(olean), "olean_bytes": sum(p.stat().st_size for p in olean)}))
PY
  )
done
(cd $TF/Ordinals && python3 - > $OUT/size-ordinals.json <<'PY'
import json
from pathlib import Path
lean = [p for p in Path().rglob("*.lean") if ".lake" not in p.parts and "StepIndexChoices" not in p.parts]
olean = list(Path(".lake/build").rglob("*.olean"))
print(json.dumps({"lean_files": len(lean), "lean_lines": sum(len(p.read_text().splitlines()) for p in lean),
                  "olean_files": len(olean), "olean_bytes": sum(p.stat().st_size for p in olean)}))
PY
)
echo alldone >> $OUT/progress
