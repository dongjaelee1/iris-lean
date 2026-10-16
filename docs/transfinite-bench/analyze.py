#!/usr/bin/env python3
"""analyze.py RESULTS_DIR: Markdown tables from measure.sh results (UP = upstream, TF = transfinite).

Per module, the CPU time is the minimum over the rounds, and the profiler categories come from
that round. "Own" time is CPU time without the import (loading of the dependencies)."""
import glob, json, statistics, sys
from collections import defaultdict

R = sys.argv[1]
TAG = sys.argv[2] if len(sys.argv) > 2 else "TF"  # TF, or TFoff (multipleSIdx linter off)
LAYERS = ["Std", "Algebra", "BI", "ProofMode", "Instances", "ProgramLogic", "HeapLang",
          "HeapLang/Lib", "Examples", "other"]


def load(kind, t):
    runs = [json.load(open(f))["modules"] for f in sorted(glob.glob(f"{R}/{kind}-{t}-*.json"))]
    mods = {}
    for m in runs[0]:
        rs = [r[m] for r in runs if m in r]
        rs = [x for x in rs if x["rc"] == 0] or rs  # rounds where the file compiled
        best = min(rs, key=lambda x: x["cpu_all"][0])
        mods[m] = {"cpu": best["cpu_all"][0], "imp": min(x["import_med"] for x in rs),
                   "cats": best["cats_med"], "rss": max(x["maxrss_kb"] for x in rs),
                   "rc": max(x["rc"] for x in rs), "rounds": [x["cpu_all"][0] for x in rs]}
        mods[m]["own"] = mods[m]["cpu"] - mods[m]["imp"]
    return mods, runs


def layer(m):
    p = m.split(".")
    if len(p) > 2 and p[1] == "HeapLang" and p[2] == "Lib":
        return "HeapLang/Lib"
    return p[1] if len(p) > 1 and p[1] in LAYERS else "other"


def pct(a, b):
    return f"{(b - a) / a * 100:+.1f}%" if a else "n/a"


def s(x):
    return f"{x:.1f}"


lib = {"UP": load("lib", "UP"), "TF": load("lib", TAG)}
if TAG == "TFoff":
    # Modules before the linter option exists reject -D linter.iris.multipleSIdx=false. The linter
    # does not run in them, so their normal (TF) values are the right ones.
    on = load("lib", "TF")[0]
    fixed = [m for m, v in lib["TF"][0].items() if v["rc"] != 0]
    for m in fixed:
        lib["TF"][0][m] = on[m]
tst = {"UP": load("test", "UP"), "TF": load("test", TAG)}
if TAG == "TFoff":
    on_t = load("test", "TF")[0]
    for m, v in list(tst["TF"][0].items()):
        if v["rc"] != 0 and m in on_t and on_t[m]["rc"] == 0:
            tst["TF"][0][m] = on_t[m]
# Test files that fail when lean runs them without the lakefile options (IrisTest.Linter needs
# them): leave them out in both trees.
BADTEST = sorted({m for t in tst for m, v in tst[t][0].items() if v["rc"] != 0})
for t in tst:
    for m in BADTEST:
        tst[t][0].pop(m, None)
U, T = lib["UP"][0], lib["TF"][0]
out = []
p = out.append

for t, (mods, _) in list(lib.items()) + list(tst.items()):
    bad = [m for m, v in mods.items() if v["rc"] != 0]
    if bad:
        p(f"**Warning: {t} modules with errors:** {', '.join(bad)}\n")

# Whole build
builds = defaultdict(list)
for f in glob.glob(f"{R}/build-*.json"):
    t = f.split("build-")[1].split("-")[0]
    builds[t].append(json.load(open(f)))
size = {t: json.load(open(f"{R}/size-{t}.json")) for t in ("UP", "TF")}
sz_ord = json.load(open(f"{R}/size-ordinals.json"))
p("## Whole build\n")
p("| | Upstream | Transfinite | Change |\n|---|---:|---:|---:|")
if builds and TAG == "TF":
    bu = min(builds["UP"], key=lambda b: b["wall"]); bt = min(builds["TF"], key=lambda b: b["wall"])
    p(f"| Clean build, wall time, 6 threads (s) | {s(bu['wall'])} | {s(bt['wall'])} | {pct(bu['wall'], bt['wall'])} |")
    cu = min(b["cpu"] for b in builds["UP"]); ct = min(b["cpu"] for b in builds["TF"])
    p(f"| Clean build, CPU time (s) | {s(cu)} | {s(ct)} | {pct(cu, ct)} |")
    p(f"| Clean build, peak memory of one process (MB) | {bu['maxrss_kb'] / 1024:.0f} | {bt['maxrss_kb'] / 1024:.0f} | {pct(bu['maxrss_kb'], bt['maxrss_kb'])} |")
lu = sum(v["cpu"] for v in U.values()); lt = sum(v["cpu"] for v in T.values())
ou = sum(v["own"] for v in U.values()); ot = sum(v["own"] for v in T.values())
p(f"| Library modules | {len(U)} | {len(T)} | {len(T) - len(U):+d} |")
p(f"| Library, sum of module CPU, 1 thread (s) | {s(lu)} | {s(lt)} | {pct(lu, lt)} |")
p(f"| Library, same without imports (s) | {s(ou)} | {s(ot)} | {pct(ou, ot)} |")
tu = sum(v["own"] for v in tst["UP"][0].values()); tt = sum(v["own"] for v in tst["TF"][0].values())
p(f"| Test files | {len(tst['UP'][0])} | {len(tst['TF'][0])} | {len(tst['TF'][0]) - len(tst['UP'][0]):+d} |")
p(f"| Tests, sum of file CPU without imports (s) | {s(tu)} | {s(tt)} | {pct(tu, tt)} |")
p(f"| `.lean` lines (Iris package) | {size['UP']['lean_lines']} | {size['TF']['lean_lines']} | {pct(size['UP']['lean_lines'], size['TF']['lean_lines'])} |")
p(f"| `.olean` bytes (MB) | {size['UP']['olean_bytes'] / 1e6:.1f} | {size['TF']['olean_bytes'] / 1e6:.1f} | {pct(size['UP']['olean_bytes'], size['TF']['olean_bytes'])} |")
p(f"\nOrdinals package (only in Transfinite): {sz_ord['lean_files']} files, {sz_ord['lean_lines']} lines, {sz_ord['olean_bytes'] / 1e6:.1f} MB of `.olean`.")
if builds and TAG == "TF":
    p("\nClean builds, all runs (wall s / CPU s): " + "; ".join(
        f"{t} " + ", ".join(f"{b['wall']:.0f}/{b['cpu']:.0f}" for b in builds[t]) for t in ("UP", "TF")))

# Noise
p("\n## Spread between rounds (library, sum of module CPU)\n")
for t, (_, runs) in lib.items():
    tots = [sum(r[m]["cpu_all"][0] for m in r) for r in runs]
    p(f"- {t}: " + ", ".join(f"{x:.1f}" for x in tots) + f" s (spread {(max(tots) - min(tots)) / min(tots) * 100:.1f}%)")

# Per layer
common = sorted(set(U) & set(T))
p("\n## Per layer: modules in both trees, CPU without imports\n")
p("| Layer | Modules | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|---:|")
for L in LAYERS:
    ms = [m for m in common if layer(m) == L]
    if not ms:
        continue
    a = sum(U[m]["own"] for m in ms); b = sum(T[m]["own"] for m in ms)
    p(f"| {L} | {len(ms)} | {s(a)} | {s(b)} | {pct(a, b)} |")
a = sum(U[m]["own"] for m in common); b = sum(T[m]["own"] for m in common)
p(f"| **All** | {len(common)} | {s(a)} | {s(b)} | {pct(a, b)} |")

p("\n## Modules in only one tree (CPU without imports)\n")
for t, only in (("Transfinite", sorted(set(T) - set(U))), ("Upstream", sorted(set(U) - set(T)))):
    mods = T if t == "Transfinite" else U
    tot = sum(mods[m]["own"] for m in only)
    p(f"- {t} only ({len(only)}, {tot:.1f} s): " + ", ".join(f"`{m}` {mods[m]['own']:.1f}" for m in only))
o = json.load(open(f"{R}/ordinals-TF.json"))["modules"]
p(f"- Ordinals package ({len(o)} modules): {sum(v['cpu_min'] - v['import_med'] for v in o.values()):.1f} s")

# Categories
p("\n## Profiler categories (library, sum over modules)\n")
cu = defaultdict(float); ct = defaultdict(float)
for m, v in U.items():
    for k, x in v["cats"].items():
        cu[k] += x
for m, v in T.items():
    for k, x in v["cats"].items():
        ct[k] += x
p("| Category | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
for k in sorted(set(cu) | set(ct), key=lambda k: -max(cu[k], ct[k]))[:14]:
    p(f"| {k} | {s(cu[k])} | {s(ct[k])} | {pct(cu[k], ct[k])} |")

# Categories, modules in both trees only
p("\n## Profiler categories (modules in both trees)\n")
p("| Category | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
cu2 = defaultdict(float); ct2 = defaultdict(float)
for m in common:
    for k, x in U[m]["cats"].items():
        cu2[k] += x
    for k, x in T[m]["cats"].items():
        ct2[k] += x
for k in sorted(set(cu2) | set(ct2), key=lambda k: -max(cu2[k], ct2[k]))[:12]:
    p(f"| {k} | {s(cu2[k])} | {s(ct2[k])} | {ct2[k] - cu2[k]:+.1f} s ({pct(cu2[k], ct2[k])}) |")

# Categories per layer (change in seconds, modules in both trees)
top = sorted(set(cu) | set(ct), key=lambda k: -max(cu[k], ct[k]))[:7]
p("\n## Change per layer and category (s, transfinite minus upstream, modules in both trees)\n")
p("| Layer | " + " | ".join(top) + " |\n|---|" + "---:|" * len(top))
for L in LAYERS:
    ms = [m for m in common if layer(m) == L]
    if not ms:
        continue
    row = [sum(T[m]["cats"].get(k, 0) - U[m]["cats"].get(k, 0) for m in ms) for k in top]
    p(f"| {L} | " + " | ".join(f"{x:+.1f}" for x in row) + " |")

# Top modules
d = sorted(common, key=lambda m: T[m]["own"] - U[m]["own"])
p("\n## Largest increases (modules in both trees, CPU without imports)\n")
p("| Module | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
for m in reversed(d[-15:]):
    p(f"| `{m}` | {U[m]['own']:.2f} | {T[m]['own']:.2f} | {T[m]['own'] - U[m]['own']:+.2f} s ({pct(U[m]['own'], T[m]['own'])}) |")
p("\n## Largest decreases\n")
p("| Module | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
for m in d[:8]:
    p(f"| `{m}` | {U[m]['own']:.2f} | {T[m]['own']:.2f} | {T[m]['own'] - U[m]['own']:+.2f} s ({pct(U[m]['own'], T[m]['own'])}) |")

# Distribution of relative changes
rel = [(T[m]["own"] - U[m]["own"]) / U[m]["own"] * 100 for m in common if U[m]["own"] > 0.5]
q = statistics.quantiles(rel, n=4)
p(f"\nRelative change per module (modules over 0.5 s, {len(rel)}): median {statistics.median(rel):+.1f}%, "
  f"quartiles {q[0]:+.1f}% / {q[2]:+.1f}%, min {min(rel):+.1f}%, max {max(rel):+.1f}%.")

# HeapLang/Lib
hl = [m for m in common if layer(m) == "HeapLang/Lib"]
p("\n## HeapLang library proofs (`Iris.HeapLang.Lib.*`)\n")
p("| Module | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
for m in hl:
    p(f"| `{m.split('.')[-1]}` | {U[m]['own']:.2f} | {T[m]['own']:.2f} | {pct(U[m]['own'], T[m]['own'])} |")
a = sum(U[m]["own"] for m in hl); b = sum(T[m]["own"] for m in hl)
p(f"| **All {len(hl)}** | {s(a)} | {s(b)} | {pct(a, b)} |")

# Tests
TU, TT = tst["UP"][0], tst["TF"][0]
tc = sorted(set(TU) & set(TT))
p("\n## Tests (`IrisTest.*`, CPU without imports)\n")
a = sum(TU[m]["own"] for m in tc); b = sum(TT[m]["own"] for m in tc)
p(f"Left out (they need the lakefile options): {', '.join(BADTEST) or 'none'}.\n")
p(f"Common test files ({len(tc)}): {a:.1f} s upstream, {b:.1f} s transfinite ({pct(a, b)}). "
  f"Only in transfinite: " + ", ".join(f"`{m}` {TT[m]['own']:.1f}" for m in sorted(set(TT) - set(TU))) +
  ". Only upstream: " + (", ".join(f"`{m}`" for m in sorted(set(TU) - set(TT))) or "none") + ".\n")
p("| Test file | Upstream (s) | Transfinite (s) | Change |\n|---|---:|---:|---:|")
for m in sorted(tc, key=lambda m: -TU[m]["own"]):
    p(f"| `{m}` | {TU[m]['own']:.2f} | {TT[m]['own']:.2f} | {pct(TU[m]['own'], TT[m]['own'])} |")

# Import and memory
p("\n## Import time and memory (library modules)\n")
for t, mods in (("Upstream", U), ("Transfinite", T)):
    imps = [v["imp"] for v in mods.values()]
    rss = sorted(mods.items(), key=lambda kv: -kv[1]["rss"])
    p(f"- {t}: import time mean {statistics.mean(imps):.2f} s, max {max(imps):.2f} s, sum {sum(imps):.1f} s; "
      f"peak memory median {statistics.median(v['rss'] for v in mods.values()) / 1024:.0f} MB, "
      f"max {rss[0][1]['rss'] / 1024:.0f} MB (`{rss[0][0]}`)")
hi = [m for m in common if layer(m) == "HeapLang/Lib"]
p(f"- Import time of a HeapLang library proof (mean): {statistics.mean(U[m]['imp'] for m in hi):.2f} s upstream, "
  f"{statistics.mean(T[m]['imp'] for m in hi):.2f} s transfinite")

open(f"{R}/summary-{TAG}.md", "w").write("\n".join(out) + "\n")
print("\n".join(out))
