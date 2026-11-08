#!/usr/bin/env python3
"""
NoShortDesc(n, k, t, x) CNF encoder.

Encodes the propositional statement:

    "There EXISTS a k-bit program p such that machine M, running for
    exactly t steps on p, produces the n-bit output x."

Used as a candidate "meta-complexity tautology family" for empirical
DPLL+UP behavior study — see PHP_TO_MINKT_BRIDGE_SKETCH.md for the
research context and conjecture.

If k is strictly less than the Kolmogorov complexity K_t^M(x), the CNF
is UNSAT and DPLL+UP must refute it. The conflict count on refutation is
the empirical quantity of interest.

Machine M (documented, deterministic, honest):
  - State: a 2-bit register r initialized to 0.
  - Program p: k bits, indexed p[0..k-1].
  - For step s in 0..t-1:
      instr = p[s mod k]
      if instr == 1:
          flip bit (s mod 2) of r
      else:
          no-op
  - Output: after each block of exactly 4 steps the low bit r[0] is
    emitted. Total output length = t // 4. We require t == 4*n.

So M is a stepwise-linear register machine: every output bit is a fixed
XOR of certain program bits (determined by n, k, t). The "time-bounded"
aspect is REAL — the clauses say "after step s, r equals [stuff]" — but
because transitions are linear over GF(2) each output bit is an affine
function of p. This is the simplest honest encoding that:
  - exposes program bits p[0..k-1] as decision variables
  - exposes trace bits r[s][b] as DPLL-visible intermediate state
  - has a tunable time bound t
  - supports both program-first and trace-first orderings

Non-linear / halting-aware machines (counter machines, lambda reducers)
are the natural next step — explicitly NOT encoded here to keep the
first-look probe tractable and the semantics transparent.

Variable count:
    V(n,k,t) = k  (program bits)
             + 2*(t+1)  (register state at each step, 2 bits)
             + n  (output bits, fixed to x; actually substituted inline)
    => V(n,k,t) = k + 2*(t+1)   (output bits are forced constants)

Clause count (approx):
    init: 2 (register starts at 00)
    transitions: 4 clauses per step * 2 bits => 8*t total
    output pin: for each j in [0..n): one 1-literal clause forcing r_low
                at step 4*(j+1) equal to x[j]  => n clauses
    => C(n,k,t) ≈ 8*t + n + 2
"""
from __future__ import annotations

import argparse
from typing import Literal


def encode(n: int, k: int, t: int, x: str) -> dict:
    """
    Encode NoShortDesc(n, k, t, x) as CNF.

    Returns dict with keys:
      num_vars: int
      clauses: list[tuple[int, ...]]  (DIMACS-style, nonzero signed ints)
      var_meta: dict mapping var id -> (kind, indices)
      program_var_ids: list[int]  (length k, in order p[0], p[1], ...)
      trace_var_ids: list[int]    (length 2*(t+1), in order r[0][0],
                                   r[0][1], r[1][0], ...)

    Preconditions: t == 4*n, len(x) == n, x consists of '0'/'1'.
    """
    if t != 4 * n:
        raise ValueError(f"require t == 4*n (got t={t}, n={n})")
    if len(x) != n:
        raise ValueError(f"|x| ({len(x)}) must equal n ({n})")
    if any(c not in "01" for c in x):
        raise ValueError("x must be a binary string")

    next_var = 1
    var_meta: dict[int, tuple] = {}

    def new_var(kind: str, *idx) -> int:
        nonlocal next_var
        v = next_var
        var_meta[v] = (kind, idx)
        next_var += 1
        return v

    # Program bits
    p = [new_var("p", i) for i in range(k)]
    # Register state r[s][b] for s in 0..t, b in {0,1}
    r = [[new_var("r", s, b) for b in range(2)] for s in range(t + 1)]

    clauses: list[tuple[int, ...]] = []

    # --- init: r[0][0] = r[0][1] = 0 ---
    clauses.append((-r[0][0],))
    clauses.append((-r[0][1],))

    # --- transitions ---
    # For each step s in 0..t-1:
    #   instr = p[s mod k]
    #   if instr=1: r[s+1][s%2] = NOT r[s][s%2], other bit unchanged
    #   if instr=0: r[s+1][b] = r[s][b] for both b
    # Encode as implications gated by instr.
    def eq_clauses(a: int, b: int) -> list[tuple[int, ...]]:
        # a <-> b : (-a v b) and (a v -b)
        return [(-a, b), (a, -b)]

    def neq_clauses(a: int, b: int) -> list[tuple[int, ...]]:
        # a <-> NOT b : (-a v -b) and (a v b)
        return [(-a, -b), (a, b)]

    for s in range(t):
        pv = p[s % k]
        b_flip = s % 2
        b_keep = 1 - b_flip
        # instr=1 case: gated by (pv) — add -pv to every clause
        for lits in neq_clauses(r[s + 1][b_flip], r[s][b_flip]):
            clauses.append((-pv,) + lits)
        for lits in eq_clauses(r[s + 1][b_keep], r[s][b_keep]):
            clauses.append((-pv,) + lits)
        # instr=0 case: gated by (NOT pv)
        for lits in eq_clauses(r[s + 1][0], r[s][0]):
            clauses.append((pv,) + lits)
        for lits in eq_clauses(r[s + 1][1], r[s][1]):
            clauses.append((pv,) + lits)

    # --- output pins: for j in 0..n-1, r[4*(j+1)][0] = x[j] ---
    for j in range(n):
        s_emit = 4 * (j + 1)
        want = x[j]
        v = r[s_emit][0]
        clauses.append((v,) if want == "1" else (-v,))

    return {
        "num_vars": next_var - 1,
        "clauses": clauses,
        "var_meta": var_meta,
        "program_var_ids": p,
        "trace_var_ids": [r[s][b] for s in range(t + 1) for b in range(2)],
    }


def ordering(cnf: dict, kind: Literal["program_first", "trace_first"]) -> list[int]:
    """Return a static decision order over all variables in the CNF."""
    prog = cnf["program_var_ids"]
    trace = cnf["trace_var_ids"]
    if kind == "program_first":
        return prog + trace
    if kind == "trace_first":
        return trace + prog
    raise ValueError(kind)


def to_dimacs(cnf: dict) -> str:
    out = [f"p cnf {cnf['num_vars']} {len(cnf['clauses'])}"]
    for cl in cnf["clauses"]:
        out.append(" ".join(str(l) for l in cl) + " 0")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--x", type=str, required=True)
    args = ap.parse_args()
    cnf = encode(args.n, args.k, 4 * args.n, args.x)
    print(to_dimacs(cnf), end="")
