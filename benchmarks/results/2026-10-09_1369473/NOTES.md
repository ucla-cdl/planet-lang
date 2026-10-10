# Notes on the 2026-10-09 run

Hand-written; `summary.md` is generated. Machine: Apple M2, 24 GB, Python 3.12.0, z3 4.13.3.
Old = `1183212` (before the integer-count solver change), new = `1369473`.

## Corpus

- 14 of 15 programs complete on both versions. `shaping_compliance.py` fails on both with
  `ValueError: Sample larger than population` from `planet/candl.py` (`random.sample` in the
  random-variable path, reached via `Randomizer` after the solver finishes). This is the
  multifactor-nested encoding; `shaping_compliance2.py` (the shape-only encoding) completes.
- `mousering.py` is the only slow program: 82.6 s old, 48.7 s new (median of 3). The integer
  counts made z3 faster here, not slower.
- Every other program is within noise of the old version; 12 of the 14 completed programs are
  under 1 s, `mousering2.py` is 2.8 s, `seated_wip.py` 0.7 s.
- The original paper table (M4 Pro) is not directly comparable to these M2 numbers.

## Examples sweep (`src/examples`)

- `cluster.py`, `cross_test.py`, `demo.py` import a `lib` package that no longer exists. Stale
  scripts, same on both versions.
- `scaling.py` (686 plans, 7 conditions) exceeds 300 s on both versions.
- `analysis/replicate_btw.py` is the one real regression: a nested-then-crossed design with
  48 plans x 4 trials. Re-measured 3x per version after the sweep:

  | version | wall (s) | solve (s) |
  |---|---|---|
  | old 1183212 | 0.83, 0.83, 1.03 | 0.50, 0.50, 0.70 |
  | new 1369473 | 2.69, 2.69, 2.69 | 2.37, 2.37, 2.37 |

  Candidates are the `cross.py` change in `55f4e55` (counterbalance regions copied through
  `cross`) and the integer counts in `1598db0`; not investigated here.

## Scaling (new version only, 600 s per point)

- Latin square: flat, 0.74 s at n = 10.
- Full counterbalancing: 0.35 s at n = 4 (24 plans), then times out at n = 5 (120 plans).
- Nested Latin squares: 2.9 s at n = 6, 10.4 s at n = 7, 26.8 s at n = 8, times out at n = 10
  (n = 9 was not in the sweep).
- Trials at n = 4: flat from 4 to 20 trials per participant.
