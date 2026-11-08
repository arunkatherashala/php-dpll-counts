#!/usr/bin/env python3
"""
MINKT v3 COMPLETION probe: 600s per-run cap to convert 60s timeouts
to EXACT conflict counts.

Targets small n only (3 and 4) with t=12 (longer trace than base runner
to keep opcode cycling meaningful for n=3,4). Both trace_first and
head_first orderings — the ones that timed out in results_v3.csv.
Program_first is also run as a sanity check and anchor.

Output: results_v3_completion.csv (does NOT overwrite results_v3.csv).
"""
from __future__ import annotations

import csv
import random
import time
from pathlib import Path

from no_short_desc_encoder_v3 import encode, ordering
from probe_runner import dpll_count


def rand_x(n: int, seed: int) -> str:
    rng = random.Random(seed)
    return "".join(rng.choice("01") for _ in range(n))


def main():
    here = Path(__file__).parent
    out_csv = here / "results_v3_completion.csv"
    time_cap = 600.0           # 10 min per run
    total_cap = 60 * 60.0       # 60 min wall clock
    start = time.monotonic()

    tuples = [
        (3, 4, 12),
        (3, 5, 12),
        (3, 6, 12),
        (4, 4, 12),
        (4, 5, 12),
        (4, 6, 12),
    ]

    rows = []
    for (n, k, t) in tuples:
        if time.monotonic() - start > total_cap:
            print(f"[total time cap hit] skipping (n={n},k={k},t={t}) and beyond")
            break
        x = rand_x(n, seed=42 + n * 100 + k)
        try:
            cnf = encode(n, k, t, x)
        except Exception as e:
            print(f"encode err n={n} k={k} t={t}: {e}")
            continue
        nc = len(cnf["clauses"])
        for ord_kind in ("program_first", "trace_first", "head_first"):
            if time.monotonic() - start > total_cap:
                print(f"[total time cap hit mid-ordering]")
                break
            ord_list = ordering(cnf, ord_kind)
            t0 = time.monotonic()
            conflicts, timed_out = dpll_count(
                cnf["num_vars"], cnf["clauses"], ord_list, time_cap
            )
            dt = time.monotonic() - t0
            row = {
                "n": n, "k": k, "t": t,
                "x": x,
                "order": ord_kind,
                "num_vars": cnf["num_vars"],
                "num_clauses": nc,
                "conflicts": conflicts,
                "time_sec": round(dt, 3),
                "timed_out": timed_out,
            }
            rows.append(row)
            print(
                f"n={n:2d} k={k} t={t:2d} order={ord_kind:14s} "
                f"V={cnf['num_vars']:5d} C={nc:6d} "
                f"conflicts={conflicts:12d} time={dt:7.2f}s"
                + (" [TIMEOUT@600s]" if timed_out else "")
            )
            # flush as we go so partial data survives interruption
            if rows:
                with out_csv.open("w", newline="") as f:
                    w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
                    w.writeheader()
                    w.writerows(rows)

    if rows:
        print(f"\nWrote {len(rows)} rows to {out_csv}")


if __name__ == "__main__":
    main()
