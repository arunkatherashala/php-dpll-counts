#!/usr/bin/env python3
"""
MINKT v2 probe: non-linear machine (head+tape, head-indexed FLIP).
Runs the v2 encoder across the same (n,k) grid as v1, three orderings:
program_first / trace_first / head_first.

Output: results_v2.csv
"""
from __future__ import annotations

import csv
import random
import time
from pathlib import Path

from no_short_desc_encoder_v2 import encode, ordering
from probe_runner import dpll_count


def rand_x(n: int, seed: int) -> str:
    rng = random.Random(seed)
    return "".join(rng.choice("01") for _ in range(n))


def main():
    here = Path(__file__).parent
    out_csv = here / "results_v2.csv"
    time_cap = 60.0
    total_cap = 10 * 60.0
    start = time.monotonic()

    # (n, k, t) triples. n>=2 required. Scale t with n.
    tuples = [
        (2, 2, 4),
        (2, 3, 4),
        (2, 4, 4),
        (3, 2, 6),
        (3, 3, 6),
        (3, 4, 6),
        (3, 6, 6),
        (4, 3, 8),
        (4, 4, 8),
        (4, 6, 8),
        (5, 4, 10),
        (5, 6, 10),
    ]

    rows = []
    for (n, k, t) in tuples:
        if time.monotonic() - start > total_cap:
            print(f"[time cap hit] skipping (n={n},k={k},t={t}) and beyond")
            break
        x = rand_x(n, seed=42 + n * 100 + k)
        try:
            cnf = encode(n, k, t, x)
        except Exception as e:
            print(f"encode err n={n} k={k} t={t}: {e}")
            continue
        for ord_kind in ("program_first", "trace_first", "head_first"):
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
                "num_clauses": len(cnf["clauses"]),
                "conflicts": conflicts,
                "time_sec": round(dt, 3),
                "timed_out": timed_out,
            }
            rows.append(row)
            print(
                f"n={n} k={k} t={t} order={ord_kind:14s} "
                f"V={cnf['num_vars']:4d} C={len(cnf['clauses']):5d} "
                f"conflicts={conflicts:10d} time={dt:7.2f}s"
                + (" [TIMEOUT]" if timed_out else "")
            )

    if rows:
        with out_csv.open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"\nWrote {len(rows)} rows to {out_csv}")


if __name__ == "__main__":
    main()
