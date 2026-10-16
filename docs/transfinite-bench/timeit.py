#!/usr/bin/env python3
"""timeit.py OUT.json -- CMD...: run CMD and write wall time, CPU time (user + sys of CMD and all
its children) and peak RSS (largest single process) to OUT.json."""
import json, os, subprocess, sys, time
out = sys.argv[1]; cmd = sys.argv[sys.argv.index("--") + 1:]
t0 = time.monotonic()
p = subprocess.Popen(cmd)
_, status, ru = os.wait4(p.pid, 0)
wall = time.monotonic() - t0
json.dump({"cmd": cmd, "rc": os.waitstatus_to_exitcode(status), "wall": wall,
           "cpu": ru.ru_utime + ru.ru_stime, "maxrss_kb": ru.ru_maxrss}, open(out, "w"), indent=1)
