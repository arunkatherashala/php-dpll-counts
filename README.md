# php-dpll-counts

Companion code for the paper

> Sai Arun Kumar Katherashala, *Exact conflict counts of unit-propagating DPLL on the pigeonhole principle:
> closed forms for pigeon-major and hole-major static orders*, October 2026.

## `code/`

| File | Purpose |
|---|---|
| `ms_check.py` | Recomputes, in exact arithmetic, all numbers, closed forms (n <= 60), identities and certificates of the paper, and checks them against `ms_php_dpll.tex`. Prints `ALL OK`. Python 3, standard library only. |
| `ref_dp.rs` | Static-order dynamic program (`ref_dp <pig\|hole\|diag> nmin nmax threads`). |
| `ref_resk.rs` | Res(k)-JW / D_2-JW memoised search (`ref_resk k nmin nmax`). |
| `ref_tables.txt`, `ref_diag_14_17.txt` | Stored outputs of the longer runs. |
| `ms_php_dpll.tex` | Manuscript source (read by `ms_check.py`). |

```
cd code
rustc -O ref_dp.rs
rustc -O ref_resk.rs
python ms_check.py          # about 1 minute; use --noexe to skip the Rust programs
```

## `lean/`

Lean 4 (core only, no Mathlib), tested with Lean 4.34.1: `lean Pigeon.lean`, `lean Hole.lean`, `lean Hole2.lean`.

- `Pigeon.lean`: `Pig.L_eq` — the recurrence of Lemma `lem:pig3` has solution `L f = f * Fub (f-1)` for all `f >= 1`.
- `Hole.lean`, `Hole2.lean`: `HoleW.holeSum_eq` — the word sum `sum_w (2 + mex w)` equals `(n+2)^(n-2) + (n+3)^(n-2)` for all `n >= 2`.

No `sorry`; `#print axioms` reports only `propext`, `Quot.sound`, `Classical.choice`.
The reductions from DPLL with unit propagation to the recurrence and to the word sum are **not** formalized;
they rest on the proofs in the paper.
