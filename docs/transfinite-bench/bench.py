#!/usr/bin/env python3
"""Per-module elaboration benchmark for a built Lean package.

Re-elaborates each module's .lean file with `lean --profile` (dependencies must already be built),
recording CPU time (user+sys, from wait4), wall time, max RSS and the `--profile` categories.

  bench.py PKG_DIR [-m Mod.A Mod.B | --all [--prefix Iris.]] [-r REPS] [-j JOBS] [-o out.json]

PKG_DIR is the directory holding lakefile.toml (for example Iris/).
"""
import argparse, json, os, re, statistics, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

CAT_RE = re.compile(r"^\t(.+?) ([0-9.]+)(ms|s|us|ns)$")
UNIT = {"s": 1.0, "ms": 1e-3, "us": 1e-6, "ns": 1e-9}


def lean_env(pkg: Path) -> dict:
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=pkg, check=True,
                         capture_output=True, text=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=pkg, check=True,
                          capture_output=True, text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=out, LEAN_NUM_THREADS="1")
    return {"env": env, "lean": lean}


def run_one_rusage(pkg: Path, le: dict, mod: str, extra: list[str]) -> dict:
    f = pkg / (mod.replace(".", "/") + ".lean")
    t0 = time.monotonic()
    p = subprocess.Popen([le["lean"], "--profile", *extra, str(f)], cwd=pkg, env=le["env"],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         errors="replace")
    chunks = [p.stdout.read()]
    p.stdout.close()
    _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    wall = time.monotonic() - t0
    out = "".join(chunks)
    cats = {}
    imp = None
    in_cum = False
    for line in out.splitlines():
        if line.startswith("cumulative profiling times:"):
            in_cum = True
            continue
        if in_cum:
            m = CAT_RE.match(line)
            if m:
                cats[m.group(1)] = float(m.group(2)) * UNIT[m.group(3)]
        m2 = re.match(r"^import took ([0-9.]+)(ms|s)$", line)
        if m2:
            imp = float(m2.group(1)) * UNIT[m2.group(2)]
    errors = [l for l in out.splitlines() if ": error:" in l]
    return {"cpu": ru.ru_utime + ru.ru_stime, "user": ru.ru_utime, "wall": wall,
            "maxrss_kb": ru.ru_maxrss, "rc": os.waitstatus_to_exitcode(status),
            "import": imp, "cats": cats, "errors": errors[:5]}


def all_modules(pkg: Path, prefix: str) -> list[str]:
    root = prefix.split(".")[0]
    mods = []
    for p in sorted((pkg / root).rglob("*.lean")):
        mods.append(".".join(p.relative_to(pkg).with_suffix("").parts))
    mods.append(root) if (pkg / f"{root}.lean").exists() else None
    return [m for m in mods if m.startswith(prefix) or m == root]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pkg", type=Path)
    ap.add_argument("-m", "--modules", nargs="*", default=[])
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--prefix", default="Iris.")
    ap.add_argument("-r", "--reps", type=int, default=3)
    ap.add_argument("-j", "--jobs", type=int, default=4)
    ap.add_argument("-D", dest="opts", action="append", default=[])
    ap.add_argument("-o", "--out", type=Path)
    a = ap.parse_args()
    pkg = a.pkg.resolve()
    le = lean_env(pkg)
    mods = list(a.modules)
    if a.all:
        mods += all_modules(pkg, a.prefix)
    extra = [f"-D{o}" for o in a.opts]
    jobs = [(m, i) for i in range(a.reps) for m in mods]
    res: dict[str, list] = {m: [] for m in mods}
    with ThreadPoolExecutor(a.jobs) as ex:
        for (m, i), r in zip(jobs, ex.map(lambda mi: run_one_rusage(pkg, le, mi[0], extra), jobs)):
            res[m].append(r)
    summary = {}
    for m, rs in res.items():
        cpu = [r["cpu"] for r in rs]
        cats = {}
        for k in set().union(*[r["cats"].keys() for r in rs]):
            cats[k] = statistics.median([r["cats"].get(k, 0.0) for r in rs])
        summary[m] = {"cpu_min": min(cpu), "cpu_med": statistics.median(cpu),
                      "cpu_all": cpu, "maxrss_kb": max(r["maxrss_kb"] for r in rs),
                      "import_med": statistics.median([r["import"] or 0 for r in rs]),
                      "cats_med": cats, "rc": max(r["rc"] for r in rs),
                      "errors": rs[0]["errors"]}
    meta = {"pkg": str(pkg), "reps": a.reps, "jobs": a.jobs, "opts": a.opts,
            "git": subprocess.run(["git", "rev-parse", "HEAD"], cwd=pkg, capture_output=True,
                                  text=True).stdout.strip(),
            "time": time.strftime("%Y-%m-%d %H:%M:%S")}
    data = {"meta": meta, "modules": summary}
    if a.out:
        a.out.write_text(json.dumps(data, indent=1))
    tot = sum(s["cpu_med"] for s in summary.values())
    for m, s in summary.items():
        flag = "" if s["rc"] == 0 else f"  rc={s['rc']} {s['errors'][:1]}"
        tc = s["cats_med"].get("typeclass inference", 0)
        print(f"{m:55s} cpu {s['cpu_med']:7.2f}s (min {s['cpu_min']:6.2f})  import "
              f"{s['import_med']:5.2f}s  tc {tc:5.2f}s{flag}")
    print(f"TOTAL cpu_med {tot:.1f}s over {len(summary)} modules")


if __name__ == "__main__":
    main()
