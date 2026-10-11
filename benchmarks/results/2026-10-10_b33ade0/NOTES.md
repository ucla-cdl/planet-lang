# Notes on the 2026-10-10 run

Hand-written; `summary.md`, `execution-times.tex` and `scaling.png/.pdf` are generated
by `benchmarks/summarize.py` from the JSON in this folder. Machine: Apple M2, 24 GB,
macOS 15.8, Python 3.12.0, z3 4.13.3. Code measured: commit `b33ade0` (the perf-eval
branch rebased onto main at `810b45c`, which includes the corpus fixes in `0db90fc`,
the crash fix for `shaping_compliance.py` and the cross fix of PR #17). No old-version
comparison: the before-and-after of the integer-count solver change is in
`results/2026-10-09_1369473/`, whose numbers predate those fixes and are history.

Command: `run_all.py --skip-old` (corpus 3 runs x 300 s; examples 1 run x 300 s;
scaling 3 runs x 600 s per point; timed-out points re-run once at 3600 s). One
benchmark at a time, nothing else running, under `caffeinate`. Wall-clock: corpus
3 min, examples 5 min, scaling sweep 1 h 44 min, re-runs 1 h 46 min; 20:08 to 23:46.

## Corpus

- All 15 programs complete (the 2026-10-09 run had 14; `shaping_compliance.py` then
  crashed in the random-variable path). 11 finish under 1 s; the rest are ARTiST Exp 2
  at 1.1 s, Shaping Compliance Exp 1 at 1.2 s, MouseRing Exp 2 at 2.6 s and MouseRing
  Exp 1 at 48.1 s. Run-to-run spread is small: MouseRing Exp 1 is 47.7 to 48.3 s over
  three runs.
- Two shapes changed with the corpus fixes: ARTiST Exp 2 is now 25 plans x 15 trials
  (was 25 x 5) and Skinergy 10 x 110 (was 10 x 10). Times moved accordingly (ARTiST
  Exp 2 from 0.4 to 1.1 s; Skinergy unchanged at 0.3 s).
- The 0.26 s floor of the fast programs is interpreter start-up plus importing the
  package (z3, pandas, duckdb): about 0.22 s. Their solver time is milliseconds.
- `shaping_compliance.py` encodes the Exp 1 design, which the paper's expressivity
  evaluation marks as inexpressible (it constrains consecutive Latin-square rows per
  participant). The program is the closest expressible approximation; the generated
  table footnotes it.

## Scaling

Each family sweeps one parameter of a Latin-square design (see `README.md`). Findings:

- **Conditions (Latin square).** 0.26 s at n = 2 to 0.88 s at n = 12; solver time
  0.002 to 0.58 s. Not quite monotone (n = 10 is slower than n = 11), which is solver
  heuristics, not a trend.
- **Full counterbalancing.** 0.34 s at n = 4 (24 plans); n = 5 (120 plans) exceeds
  600 s and completes in 1752 s (29 min) under the 3600 s limit. n = 6 was never run.
- **Plans at n = 5.** 5 to 20 plans: 0.29 to 0.37 s. 25 plans: 2.7 s; 30 plans: 0.8 s;
  40 plans: over 3600 s. So a partial limit between the Latin square (p = n) and full
  counterbalancing (p = n!) is the hardest case for the solver: choosing 40 of the 120
  orders so that every condition appears equally often in every position took longer
  than materializing all 120 (29 min). The number of plans alone does not predict cost;
  the counting constraint of `limit_plans` does. Timings in this range are also
  non-monotone (25 slower than 30).
- **Composition.** Nesting two Latin squares (n^2 plans x n^2 trials): 27 s at n = 8,
  284 s at n = 9, over 600 s at n = 10 and 1035 s (17 min) under the longer limit.
  Crossing two Latin squares (n^2 plans x n trials): 13 s at n = 10, 78 s at n = 12,
  no timeout. Cross is cheaper than nest by about the ratio of their widths.
- **Width (12-condition Latin square).** Repetition alone costs: 13 s at 600 trials
  per participant, 102 s at 2400, 374 s at 4800; between linear and quadratic in the
  width. A nested uncounterbalanced within-subjects variable costs more per trial: 38 s
  at 600 trials (m = 50) and 254 s at 1200 (m = 100), against 13 s and 31 s for the
  same widths from repetition. MouseRing Exp 1 (12 methods x 10 pages x 5 repetitions,
  600 trials, 48 s) sits above both lines, since it combines the two.
- **Expected versus measured plans.** For every completed point the plan matrix the
  solver produced has the plan count and width the semantics predicts (n, n!, p, n^2;
  n, n^2, n·k, n·m). The columns are side by side in `summary.md`.

Non-monotone stretches (plans 25 vs 30; nested_variable m = 16 to 20, 30 to 40) are
reproducible across the three runs of each point (spreads are a few percent), so they
are properties of z3's search on these encodings, not noise.

## Examples sweep (`src/examples`)

- `cluster.py`, `cross_test.py`, `demo.py` import a `lib` package that no longer exists.
  `scaling.py` (686 plans of 7 conditions) exceeds 300 s. Same as on 2026-10-09.
- The main checkout had untracked files (`src/planet/vis.py`, `src/planet/vis_renderer.py`,
  `src/examples/vis_example.py`); the measured worktree did not, so `vis_example.py`
  is absent from this sweep. It does not touch the corpus or the scaling programs.

## Leads for the implementation (not acted on; the package was not changed)

- Repetition is encoded cell by cell: `num_trials(k)` multiplies the matrix width and
  the solver time although the repeated cells carry no new constraint. Expanding
  repetitions after solving would remove that cost.
- `limit_plans(p)` with n < p < n! is the hard case; direct enumeration of counterbalanced
  blocks, or symmetry breaking over the row order, would address both it and full
  counterbalancing.
- A nested uncounterbalanced variable adds a within-block distinctness constraint per
  block; symmetry breaking across blocks is the obvious lever.
- The one-off MouseRing ablation of 2026-10-10 (original 46 s solve; pages replaced by
  50 repetitions 12.7 s; repetitions removed 6.6 s, on commit 1369473) is superseded by
  the width panel; its two variants are the k = 50 and m = 10 points there.
