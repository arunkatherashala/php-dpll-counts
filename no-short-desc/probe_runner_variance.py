#!/usr/bin/env python3
"""
MINKT variance study: fix a small grid known to complete under cap for
all three orderings, and run 16 different seeds per (n,k,t) to see
whether the order-asymmetry dichotomy observed in v3 is robust across x.

Prerequisite (b) for the phenomenology paper (Appendix B reproducibility).

Output: results_variance.csv in the same directory, columns:
  n, k, t, seed, x, order, num_vars, num_clauses, conflicts,
  time_sec, timed_out.

Also prints per-(n,k,t,ordering) summary statistics (min/max/median/
mean/stddev) across the 16 seeds.
"""
from __future__ import annotations

import csv
import math
import random
import statistics
import time
from pathlib import Path

from no_short_desc_encoder_v3 import encode, ordering
from probe_runner import dpll_count


def rand_x(n: int, seed: int) -> str:
    rng = random.Random(seed)
    return "".join(rng.choice("01") for _ in range(n))


def main():
    here = Path(__file__).parent
    out_csv = here / "results_variance.csv"
    time_cap = 60.0
    total_cap = 30 * 60.0
    start = time.monotonic()

    # Grid chosen to complete under 60s/run for all three orderings
    # based on v3 data. (n=3 completed under all orderings in v3;
    # (n=4, k=4) program_first=16 in v3 was fine, but trace/head
    # timed out there — keep (n=4) in the grid to stress-test
    # variance, accepting some timeouts honestly.)
    grid = [
        (3, 4, 12),
        (3, 5, 12),
        (4, 4, 12),
        (4, 5, 12),
    ]
    seeds = list(range(1, 17))  # 16 seeds

    rows = []
    stats_rows = []
    hit_cap = False

    for (n, k, t) in grid:
        if hit_cap:
            break
        for ord_kind in ("program_first", "trace_first", "head_first"):
            cell_conflicts: list[int] = []
            cell_timeouts = 0
            completed = 0
            for seed in seeds:
                if time.monotonic() - start > total_cap:
                    print(f"[total wall cap hit] stopping mid-cell (n={n},k={k},t={t},ord={ord_kind},seed={seed})")
                    hit_cap = True
                    break
                x = rand_x(n, seed)
                try:
                    cnf = encode(n, k, t, x)
                except Exception as e:
                    print(f"encode err n={n} k={k} t={t} seed={seed}: {e}")
                    continue
                ord_list = ordering(cnf, ord_kind)
                t0 = time.monotonic()
                conflicts, timed_out = dpll_count(
                    cnf["num_vars"], cnf["clauses"], ord_list, time_cap
                )
                dt = time.monotonic() - t0
                row = {
                    "n": n, "k": k, "t": t, "seed": seed, "x": x,
                    "order": ord_kind,
                    "num_vars": cnf["num_vars"],
                    "num_clauses": len(cnf["clauses"]),
                    "conflicts": conflicts,
                    "time_sec": round(dt, 3),
                    "timed_out": timed_out,
                }
                rows.append(row)
                if timed_out:
                    cell_timeouts += 1
                else:
                    completed += 1
                    cell_conflicts.append(conflicts)
                print(
                    f"n={n} k={k} t={t:2d} seed={seed:2d} ord={ord_kind:14s} "
                    f"V={cnf['num_vars']:4d} C={len(cnf['clauses']):5d} "
                    f"conflicts={conflicts:10d} time={dt:6.2f}s"
                    + (" [TIMEOUT]" if timed_out else "")
                )
            if cell_conflicts:
                cc = cell_conflicts
                stats_rows.append({
                    "n": n, "k": k, "t": t, "order": ord_kind,
                    "n_completed": completed,
                    "n_timeout": cell_timeouts,
                    "min": min(cc), "max": max(cc),
                    "median": statistics.median(cc),
                    "mean": round(statistics.mean(cc), 3),
                    "stddev": round(statistics.pstdev(cc), 3) if len(cc) > 1 else 0.0,
                })
            else:
                stats_rows.append({
                    "n": n, "k": k, "t": t, "order": ord_kind,
                    "n_completed": 0, "n_timeout": cell_timeouts,
                    "min": None, "max": None, "median": None,
                    "mean": None, "stddev": None,
                })

    if rows:
        with out_csv.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"\nWrote {len(rows)} rows to {out_csv}")

    print("\n=== Per-cell variance stats ===")
    print(f"{'n':>2} {'k':>2} {'t':>2} {'order':>14} {'done/to':>8} "
          f"{'min':>10} {'max':>10} {'median':>10} {'mean':>12} {'stddev':>12}")
    for s in stats_rows:
        done_to = f"{s['n_completed']}/{s['n_timeout']}"
        print(f"{s['n']:>2} {s['k']:>2} {s['t']:>2} {s['order']:>14} {done_to:>8} "
              f"{str(s['min']):>10} {str(s['max']):>10} {str(s['median']):>10} "
              f"{str(s['mean']):>12} {str(s['stddev']):>12}")

    # top-3 stddev/mean ratios (coefficient of variation) across cells
    # that had at least 2 completed runs
    cv_rows = []
    for s in stats_rows:
        if s["mean"] and s["mean"] > 0 and s["n_completed"] >= 2:
            cv_rows.append((s["stddev"] / s["mean"], s))
    cv_rows.sort(reverse=True)
    print("\n=== Top-3 coefficient-of-variation cells ===")
    for cv, s in cv_rows[:3]:
        print(f"cv={cv:.3f}  n={s['n']} k={s['k']} t={s['t']} order={s['order']} "
              f"mean={s['mean']} stddev={s['stddev']} (completed={s['n_completed']})")

    print(f"\nTotal wall time: {time.monotonic()-start:.1f}s")


if __name__ == "__main__":
    main()
