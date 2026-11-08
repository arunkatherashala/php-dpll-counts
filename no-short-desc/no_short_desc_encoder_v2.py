#!/usr/bin/env python3
"""
NoShortDesc v2 — non-linear universal machine (head-indexed tape access).

Honest scope note: the full 4-op INC/RIGHT/LEFT/WRITE machine from
minkt_toy.py encodes to O(n*t) variables with 4-way opcode cases and
output-pointer tracking that balloons clause count past the first-look
budget. v2 delivers the MINIMAL non-linear variant that still blocks the
Gaussian-elimination collapse v1 suffered:

Machine v2 (2-op, head+tape+program; tape_size = n):
  State: tape[0..n-1] (n bits), head[0..n-1] (one-hot position).
  Init:  tape all 0; head one-hot at position 0.
  Program p: k bits, cyclically read.
  Per step s (s = 0..t-1), op = p[s mod k]:
    op = 0  (SHIFT): head rotates right by 1 (cyclic); tape unchanged.
    op = 1  (FLIP):  tape[head] ^= 1; head unchanged.
  Output pin: tape[t][c] == x[c] for all c.

Non-linearity source: the FLIP clause is
  tape[s+1][c] XOR tape[s][c] XOR head[s][c] = 0   (when op = 1)
which is a 3-variable XOR over head and tape vars — DPLL+UP cannot
Gaussian-eliminate this the way it could the v1 linear register XOR,
because head[s][c] is itself a free variable with ExactlyOne constraint
across c.

Variable count:
  k  (program)
  + n*(t+1)  (tape)
  + n*(t+1)  (head, one-hot)
  = k + 2*n*(t+1)

Clause count (rough):
  init: 1 (tape) + 1 (head one-hot anchor) = O(n)
  per step: ~8*n (XOR encodings under op-gating) + ExactlyOne head
  = O(n * t)
"""
from __future__ import annotations

import argparse
from typing import Literal


def encode(n: int, k: int, t: int, x: str) -> dict:
    if len(x) != n:
        raise ValueError(f"|x| ({len(x)}) must equal n ({n})")
    if any(c not in "01" for c in x):
        raise ValueError("x must be binary")
    if n < 2:
        raise ValueError("n >= 2 required (head one-hot over >=2 cells)")

    next_var = 1
    var_meta: dict[int, tuple] = {}

    def new_var(kind: str, *idx) -> int:
        nonlocal next_var
        v = next_var
        var_meta[v] = (kind, idx)
        next_var += 1
        return v

    p = [new_var("p", i) for i in range(k)]
    tape = [[new_var("tape", s, c) for c in range(n)] for s in range(t + 1)]
    head = [[new_var("head", s, c) for c in range(n)] for s in range(t + 1)]

    clauses: list[tuple[int, ...]] = []

    # init: tape[0][*] = 0
    for c in range(n):
        clauses.append((-tape[0][c],))
    # init: head[0][0] = 1, head[0][c>0] = 0
    clauses.append((head[0][0],))
    for c in range(1, n):
        clauses.append((-head[0][c],))

    # ExactlyOne head[s] at each step
    def exactly_one(vs: list[int]) -> list[tuple[int, ...]]:
        cls: list[tuple[int, ...]] = []
        cls.append(tuple(vs))  # at least one
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                cls.append((-vs[i], -vs[j]))  # at most one (pairwise)
        return cls

    # We assert ExactlyOne for every step (not strictly needed if init+transitions
    # preserve it, but makes the CNF honest and robust)
    for s in range(1, t + 1):
        clauses.extend(exactly_one(head[s]))

    # XOR_3: a XOR b XOR c = 0, encoded as 4 clauses
    def xor3_zero(a: int, b: int, c: int) -> list[tuple[int, ...]]:
        return [
            (-a, -b, -c),
            (-a, b, c),
            (a, -b, c),
            (a, b, -c),
        ]

    # IFF: a <-> b, 2 clauses
    def iff(a: int, b: int) -> list[tuple[int, ...]]:
        return [(-a, b), (a, -b)]

    # Transitions
    for s in range(t):
        pv = p[s % k]

        # --- op = 0 (SHIFT): gated by -pv ---
        # tape[s+1][c] = tape[s][c] for all c
        for c in range(n):
            for lits in iff(tape[s + 1][c], tape[s][c]):
                clauses.append((pv,) + lits)
        # head[s+1][(c+1) mod n] = head[s][c] for all c
        # equivalently head[s+1][c'] = head[s][(c'-1) mod n]
        for cp in range(n):
            src = head[s][(cp - 1) % n]
            dst = head[s + 1][cp]
            for lits in iff(dst, src):
                clauses.append((pv,) + lits)

        # --- op = 1 (FLIP): gated by +pv wait, we add -pv for op=0 gate; for op=1 add pv ---
        # Standard encoding: to say "if A then B", we add clause (-A OR B).
        # We want: op=0 (i.e. pv=False) → transitions above. Clause (pv OR ...): true when pv=T or ... holds.
        # So when pv=F (op=0), the clause reduces to (...) which must hold. Correct.
        # For op=1 (pv=T): similar, add (-pv OR ...).

        # FLIP: head unchanged
        for c in range(n):
            for lits in iff(head[s + 1][c], head[s][c]):
                clauses.append((-pv,) + lits)
        # FLIP: tape[s+1][c] XOR tape[s][c] XOR head[s][c] = 0
        for c in range(n):
            for lits in xor3_zero(tape[s + 1][c], tape[s][c], head[s][c]):
                clauses.append((-pv,) + lits)

    # Output pin: tape[t][c] = x[c]
    for c in range(n):
        v = tape[t][c]
        clauses.append((v,) if x[c] == "1" else (-v,))

    return {
        "num_vars": next_var - 1,
        "clauses": clauses,
        "var_meta": var_meta,
        "program_var_ids": p,
        "tape_var_ids": [tape[s][c] for s in range(t + 1) for c in range(n)],
        "head_var_ids": [head[s][c] for s in range(t + 1) for c in range(n)],
    }


def ordering(cnf: dict, kind: Literal["program_first", "trace_first", "head_first"]) -> list[int]:
    prog = cnf["program_var_ids"]
    tape = cnf["tape_var_ids"]
    head = cnf["head_var_ids"]
    if kind == "program_first":
        return prog + head + tape
    if kind == "trace_first":
        return tape + head + prog
    if kind == "head_first":
        return head + prog + tape
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
    ap.add_argument("--t", type=int, required=True)
    ap.add_argument("--x", type=str, required=True)
    args = ap.parse_args()
    cnf = encode(args.n, args.k, args.t, args.x)
    print(to_dimacs(cnf), end="")
