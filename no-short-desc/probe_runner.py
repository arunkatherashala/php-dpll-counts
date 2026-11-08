#!/usr/bin/env python3
"""
MINKT empirical probe: run DPLL+UP on NoShortDesc(n, k, t=4n, x) CNFs
for small (n, k) and record exact conflict counts under two static
variable orderings.

Output: results.csv in the same directory.

Pattern-matched after Paper 9 PHP DPLL conflict-count methodology
(program-first vs trace-first here analogous to pigeon-major vs
hole-major there).
"""
from __future__ import annotations

import csv
import os
import random
import time
from pathlib import Path

from no_short_desc_encoder import encode, ordering


# -------------------- DPLL+UP conflict counter --------------------
#
# Static-order DPLL with unit propagation. Counts leaves of the search
# tree whose branch ended in a conflict (i.e. produced the empty clause).
# No clause learning, no restarts — matches the "pure DPLL+UP conflict
# count" model used in the PHP papers.

def dpll_count(num_vars: int, clauses: list[tuple[int, ...]],
               order: list[int], time_cap_sec: float) -> tuple[int, bool]:
    """
    Returns (conflicts, timed_out).

    On timed_out=True the returned conflicts is a lower bound (count at
    the moment the cap tripped).
    """
    # clauses stored as list of frozenset of ints (signed vars)
    # assignment: dict var -> bool
    start = time.monotonic()
    timed_out = [False]

    def propagate(assign: dict[int, bool], cls: list[set[int]]) -> tuple[bool, list[set[int]]]:
        """Returns (ok, new_cls). ok=False if conflict."""
        changed = True
        cur = cls
        while changed:
            changed = False
            new_cls: list[set[int]] = []
            for c in cur:
                reduced: set[int] = set()
                sat = False
                for lit in c:
                    v = abs(lit)
                    if v in assign:
                        val = assign[v]
                        if (lit > 0) == val:
                            sat = True
                            break
                    else:
                        reduced.add(lit)
                if sat:
                    continue
                if not reduced:
                    return False, []
                new_cls.append(reduced)
            # unit propagation
            units = [next(iter(c)) for c in new_cls if len(c) == 1]
            if units:
                for u in units:
                    v = abs(u)
                    val = u > 0
                    if v in assign and assign[v] != val:
                        return False, []
                    if v not in assign:
                        assign[v] = val
                        changed = True
            cur = new_cls
        return True, cur

    conflicts = 0
    initial = [set(c) for c in clauses]

    def recurse(depth: int, assign: dict[int, bool], cls: list[set[int]]):
        nonlocal conflicts
        if timed_out[0]:
            return
        if time.monotonic() - start > time_cap_sec:
            timed_out[0] = True
            return
        ok, cur = propagate(assign, cls)
        if not ok:
            conflicts += 1
            return
        # find next unassigned var in order
        next_var = None
        for v in order:
            if v not in assign:
                next_var = v
                break
        if next_var is None:
            # SAT leaf — not a conflict
            return
        # branch: try False then True (matches Paper 9 convention)
        for val in (False, True):
            a2 = dict(assign)
            a2[next_var] = val
            recurse(depth + 1, a2, cur)
            if timed_out[0]:
                return

    recurse(0, {}, initial)
    return conflicts, timed_out[0]


# -------------------- probe --------------------

def rand_x(n: int, seed: int) -> str:
    rng = random.Random(seed)
    return "".join(rng.choice("01") for _ in range(n))


def main():
    here = Path(__file__).parent
    out_csv = here / "results.csv"
    time_cap = 60.0
    total_cap = 10 * 60.0
    start = time.monotonic()

    # (n, k) pairs, t = 4n fixed by encoder
    # Design: k < n/XX would suggest UNSAT-leaning. k >= n with linear
    # machine -> often SAT or quickly closed. Explore both regimes.
    tuples = [
        (1, 1),
        (1, 2),
        (2, 2),
        (2, 3),
        (2, 4),
        (3, 2),
        (3, 3),
        (3, 4),
        (3, 6),
        (4, 3),
        (4, 4),
        (4, 6),
    ]

    rows = []
    for (n, k) in tuples:
        if time.monotonic() - start > total_cap:
            print(f"[time cap hit] skipping (n={n},k={k}) and beyond")
            break
        t = 4 * n
        x = rand_x(n, seed=42 + n * 100 + k)
        cnf = encode(n, k, t, x)
        for ord_kind in ("program_first", "trace_first"):
            ord_list = ordering(cnf, ord_kind)
            t0 = time.monotonic()
            conflicts, timed_out = dpll_count(
                cnf["num_vars"], cnf["clauses"], ord_list, time_cap
            )
            dt = time.monotonic() - t0
            row = {
                "n": n,
                "k": k,
                "t": t,
                "x_len": len(x),
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
                f"conflicts={conflicts:8d} time={dt:6.2f}s"
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
