#!/usr/bin/env python3
"""Parse CELL lines from bench_recursion_lanes and report per-lane log-log allocation slopes.

Primary metric is BYTES (this box is nproc=2; wall time carries >4x GC spread). A slope is only
printed when it rests on >= 5 distinct n values, per the harness's own falsification rule.
"""
import sys, re, math
from collections import defaultdict

cells = defaultdict(dict)          # (lane, wl) -> n -> [bytes per rep >=2]
status = defaultdict(set)
tinfo = {}
pat = re.compile(r"^CELL lane=(\S+) wl=(\S+) n=(\d+) rep=(\d+) ok=(\d) t=(\S+) bytes=(\d+) "
                 r"gcpct=(\S+) rssMB=(\S+) status=(\S+)(.*)$")
for path in sys.argv[1:]:
    for line in open(path, errors="replace"):
        m = pat.match(line.strip())
        if not m:
            continue
        lane, wl, n, rep, ok, t, b, gc, rss, st, note = m.groups()
        status[(lane, wl)].add(st)
        if "tabled=" in note:
            tinfo[(lane, wl, int(n))] = note.strip()
        if st == "OK" and int(rep) >= 2:
            cells[(lane, wl)].setdefault(int(n), []).append((int(b), float(t), float(gc)))

def slope(xs, ys):
    k = len(xs)
    mx, my = sum(xs) / k, sum(ys) / k
    den = sum((x - mx) ** 2 for x in xs)
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den if den else float("nan")

for (lane, wl) in sorted(cells):
    ns = sorted(cells[(lane, wl)])
    print(f"\n== lane={lane} wl={wl}  statuses={sorted(status[(lane,wl)])}")
    for n in ns:
        reps = cells[(lane, wl)][n]
        bs = [r[0] for r in reps]; ts = [r[1] for r in reps]; gcs = [r[2] for r in reps]
        spread = 100 * (max(ts) - min(ts)) / min(ts) if min(ts) > 0 else 0.0
        bspread = 100 * (max(bs) - min(bs)) / min(bs) if min(bs) > 0 else 0.0
        rel = (max(gcs) <= 10 and spread <= 15)
        print(f"   n={n:<5} bytes={bs} bytes_identical={len(set(bs))==1} "
              f"byte_spread={bspread:.2f}% tmin={min(ts):.4f}s tspread={spread:.1f}% "
              f"gcmax={max(gcs):.1f}% t_reliable={rel}"
              + (f"  [{tinfo[(lane,wl,n)]}]" if (lane, wl, n) in tinfo else ""))
    if len(ns) >= 5:
        xs = [math.log(n) for n in ns]
        yb = [math.log(min(r[0] for r in cells[(lane, wl)][n])) for n in ns]
        print(f"   LOG-LOG SLOPE (bytes vs n, all {len(ns)} points, least squares): {slope(xs, yb):.3f}")
        loc = [f"{ns[i]}->{ns[i+1]}:{(yb[i+1]-yb[i])/(xs[i+1]-xs[i]):.3f}" for i in range(len(ns) - 1)]
        print("   LOCAL exponent per consecutive pair: " + "  ".join(loc))
        # exponential-growth check (meaningful when n is a recursion DEPTH, e.g. fib)
        gf = [(min(r[0] for r in cells[(lane, wl)][ns[i+1]]) /
               min(r[0] for r in cells[(lane, wl)][ns[i]])) ** (1.0 / (ns[i+1] - ns[i]))
              for i in range(len(ns) - 1)]
        print("   per-unit-n growth FACTOR (exponential check): " + "  ".join(f"{g:.3f}" for g in gf))
    else:
        print(f"   (only {len(ns)} n values — slope NOT reported, needs >= 5)")

print("\n== cross-lane byte ratios (min-of-reps), where both lanes have the n")
lanes = sorted({l for (l, w) in cells})
wls = sorted({w for (l, w) in cells})
for wl in wls:
    for a in lanes:
        for b in lanes:
            if a >= b or (a, wl) not in cells or (b, wl) not in cells:
                continue
            common = sorted(set(cells[(a, wl)]) & set(cells[(b, wl)]))
            if not common:
                continue
            rs = [(n, min(r[0] for r in cells[(b, wl)][n]) / min(r[0] for r in cells[(a, wl)][n]))
                  for n in common]
            print(f"   {wl}: {b}/{a} bytes = " + ", ".join(f"n={n}:{r:.2f}x" for n, r in rs))
