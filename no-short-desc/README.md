# no-short-desc — DPLL+UP conflict counts on NoShortDesc_U

Companion artifact for the phenomenology note *"A measurement note: DPLL+UP conflict-count dichotomy on a NoShortDesc_U encoding."*

**Scope.** This directory contains the exact encoder scripts, probe runners, and raw CSV outputs for the measurement reported in that note. It is a dataset, not a theorem.

## Files

| File | Role |
|---|---|
| `no_short_desc_encoder.py` | v1 encoder (stepwise-XOR linear machine; produces the negative-result instance) |
| `no_short_desc_encoder_v2.py` | v2 encoder (2-op head-indexed FLIP non-linear machine; emerging gap) |
| `no_short_desc_encoder_v3.py` | v3 encoder (full 4-op INC/RIGHT/LEFT/WRITE register machine; the one the paper's observation is reported on) |
| `probe_runner.py` | v1 probe driver → `results.csv` |
| `probe_runner_v2.py` | v2 probe driver → `results_v2.csv` |
| `probe_runner_v3.py` | v3 probe driver → `results_v3.csv` |
| `probe_runner_v3_completion.py` | v3 completion run with 600s per-cell cap → `results_v3_completion.csv` |
| `probe_runner_variance.py` | 16-seed variance study at one `(n,k,t)` cell → `results_variance.csv` |
| `results.csv` | v1 raw output |
| `results_v2.csv` | v2 raw output |
| `results_v3.csv` | v3 raw output (headline dichotomy measurement) |
| `results_v3_completion.csv` | v3 at 600s cap (confirms cap was binding at 60s) |
| `results_variance.csv` | 16-seed variance CSV |

## Reproduction

The encoders require Python 3.9+ and no third-party CNF library (plain-text DIMACS output). The probe runners invoke a bundled DPLL+UP driver whose conflict-leaf counter is identical to the one used in the Paper 9 artifact at the repository root.

A typical reproduction:

```
python3 no_short_desc_encoder_v3.py --n 6 --k 4 --t 12 --x 0 > v3_n6_k4_t12.cnf
python3 probe_runner_v3.py --grid --cap 60 > results_v3.csv
```

## Timeout policy

- v1 / v2 / v3 base runs: 60 CPU-seconds per `(n,k,t,order)` cell.
- v3 completion run: 600 CPU-seconds per cell at `n=3` (`n>=4` stayed at 60 s for budget reasons).
- Variance run: 60 CPU-seconds per seed; 16 seeds at a single `(n,k,t)` cell.

A row with `timed_out=True` in any CSV reports a lower bound on the conflict count accumulated up to the cap.

## Honest caveats

- Only one universal machine family per encoder version was measured. A different `U` will yield a different family and may not exhibit the dichotomy; v1 is exactly this case.
- `n` reaches at most 8. No asymptotic claim is made from this data.
- The static orderings `program_first`, `trace_first`, `head_first` are the only three tested. Dynamic DPLL (CDCL, VSIDS, etc.) is out of scope.

## License

See top-level repository `README.md` and/or `LICENSE`.
