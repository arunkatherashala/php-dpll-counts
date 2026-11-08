#!/usr/bin/env python3
"""
MINKT v3 probe: full 4-op machine (INC/RIGHT/LEFT/WRITE).

Runs the v3 encoder across larger (n, k, t) grid, three orderings
(program_first / trace_first / head_first). Output: results_v3.csv.
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
    out_csv = here / "results_v3.csv"
    time_cap = 60.0
    total_cap = 15 * 60.0
    start = time.monotonic()

    # (n, k, t). t = 2n keeps opcode cycling meaningful; smaller than 4n
    # to keep CNF size manageable at larger n.
    tuples = [
        (4, 4, 8),
        (4, 5, 8),
        (4, 6, 8),
        (6, 4, 12),
        (6, 5, 12),
        (6, 6, 12),
        (8, 4, 16),
        (8, 5, 16),
        (8, 6, 16),
        (10, 4, 20),
        (10, 5, 20),
        (12, 4, 24),
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
        if nc > 50000:
            print(f"[clause cap] (n={n},k={k},t={t}) has {nc} clauses > 50k; skipping")
            continue
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
