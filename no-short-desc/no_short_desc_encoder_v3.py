#!/usr/bin/env python3
"""
NoShortDesc v3 — full 4-op minkt_toy machine (INC/RIGHT/LEFT/WRITE).

Machine spec (matches minkt_toy.py, adapted for CNF with tape_size = n):
  State: tape[0..n-1] bits, head one-hot over n cells.
  Init:  tape all 0; head one-hot at position 0.
  Program p: k bits (free vars).
  Per step s = 0..t-1:
    Decode opcode from program at positions a=(2s) mod k, b=(2s+1) mod k:
      p[a]=0, p[b]=0  -> INC    (tape[head] ^= 1)
      p[a]=0, p[b]=1  -> RIGHT  (head rotates right)
      p[a]=1, p[b]=0  -> LEFT   (head rotates left)
      p[a]=1, p[b]=1  -> WRITE  (tape[head] := p[s mod k])
  Output pin: tape[t][c] == x[c] for all c.

Non-linearity sources:
  - INC couples tape XOR head (same as v2)
  - WRITE couples tape XOR head XOR program (3-way: a conditional
    assignment gated by both opcode bits AND head one-hot).
  - Opcode itself is a 2-bit case-split over program bits, making the
    whole transition system a disjunction over 4 program-bit patterns.

Variable count:
  k  (program)
  + n*(t+1)  (tape)
  + n*(t+1)  (head)
  = k + 2n(t+1)

Clause count estimate (n=12, t=24): ~7k clauses.
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
        raise ValueError("n >= 2 required")
    if k < 2:
        raise ValueError("k >= 2 required (opcode needs 2 bits)")

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

    def exactly_one(vs: list[int]) -> list[tuple[int, ...]]:
        cls: list[tuple[int, ...]] = []
        cls.append(tuple(vs))
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                cls.append((-vs[i], -vs[j]))
        return cls

    # ExactlyOne head[s] at each future step (defensive; also needed for
    # the WRITE encoding to be unambiguous).
    for s in range(1, t + 1):
        clauses.extend(exactly_one(head[s]))

    # Helpers that emit an iff or XOR3 under a guard prefix (list of lits).
    def iff_under(guard: list[int], a: int, b: int) -> list[tuple[int, ...]]:
        return [tuple(guard) + (-a, b), tuple(guard) + (a, -b)]

    def xor3_zero_under(guard: list[int], a: int, b: int, c: int) -> list[tuple[int, ...]]:
        return [
            tuple(guard) + (-a, -b, -c),
            tuple(guard) + (-a, b, c),
            tuple(guard) + (a, -b, c),
            tuple(guard) + (a, b, -c),
        ]

    # Transitions. For each step s, decode opcode from p[a], p[b].
    # Guard for "opcode = X" in clause form: the negation of the
    # pattern. INC pattern p[a]=0,p[b]=0; guarding "if INC then phi" adds
    # the clause phi augmented with (+p[a], +p[b]) prefix — i.e. the
    # clause only constrains when both are 0.
    for s in range(t):
        a = p[(2 * s) % k]
        b = p[(2 * s + 1) % k]
        p_write = p[s % k]  # the bit WRITE copies onto tape[head]

        guard_INC   = [a, b]        # fires when p[a]=0, p[b]=0 (all guard lits false)
        guard_RIGHT = [a, -b]       # fires when p[a]=0, p[b]=1
        guard_LEFT  = [-a, b]       # fires when p[a]=1, p[b]=0
        guard_WRITE = [-a, -b]      # fires when p[a]=1, p[b]=1

        # --- INC: tape[s+1][c] XOR tape[s][c] XOR head[s][c] = 0; head unchanged ---
        for c in range(n):
            clauses.extend(xor3_zero_under(guard_INC, tape[s + 1][c], tape[s][c], head[s][c]))
            clauses.extend(iff_under(guard_INC, head[s + 1][c], head[s][c]))

        # --- RIGHT: tape unchanged; head[s+1][c'] = head[s][(c'-1) mod n] ---
        for c in range(n):
            clauses.extend(iff_under(guard_RIGHT, tape[s + 1][c], tape[s][c]))
        for cp in range(n):
            src = head[s][(cp - 1) % n]
            dst = head[s + 1][cp]
            clauses.extend(iff_under(guard_RIGHT, dst, src))

        # --- LEFT: tape unchanged; head[s+1][c'] = head[s][(c'+1) mod n] ---
        for c in range(n):
            clauses.extend(iff_under(guard_LEFT, tape[s + 1][c], tape[s][c]))
        for cp in range(n):
            src = head[s][(cp + 1) % n]
            dst = head[s + 1][cp]
            clauses.extend(iff_under(guard_LEFT, dst, src))

        # --- WRITE: head unchanged; tape[s+1][c] = p_write if head[s][c] else tape[s][c] ---
        for c in range(n):
            clauses.extend(iff_under(guard_WRITE, head[s + 1][c], head[s][c]))
            h = head[s][c]
            # (if head[s][c] then tape_next ↔ p_write)
            # as iff under guard_WRITE + [-h]:
            g1 = guard_WRITE + [-h]
            clauses.append(tuple(g1) + (-tape[s + 1][c], p_write))
            clauses.append(tuple(g1) + (tape[s + 1][c], -p_write))
            # (if ¬head[s][c] then tape_next ↔ tape_cur)
            g2 = guard_WRITE + [h]
            clauses.append(tuple(g2) + (-tape[s + 1][c], tape[s][c]))
            clauses.append(tuple(g2) + (tape[s + 1][c], -tape[s][c]))

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
