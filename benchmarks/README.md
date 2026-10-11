# PLanet performance evaluation

Times every example program in the repository and a scaling sweep, on the
current version of PLanet and optionally on an older commit for comparison.
This is the measurement behind the paper's execution-time table and scaling
discussion (`evals/performance-eval.tex` in the paper repository).

## Run it

```sh
git clone <this repo> && cd planet-lang
python3 -m venv .venv && .venv/bin/python -m pip install -r requirements.txt
.venv/bin/python benchmarks/run_all.py            # full run, old vs. new, about an hour
```

Useful variants:

```sh
.venv/bin/python benchmarks/run_all.py --quick         # a few minutes; checks the pipeline on a new machine
.venv/bin/python benchmarks/run_all.py --skip-old      # current tree only
.venv/bin/python benchmarks/run_all.py --old <ref>     # compare against any git ref
.venv/bin/python benchmarks/run_all.py --skip-scaling --reps 5
```

Python 3.12 is what the pinned `requirements.txt` was resolved for. Any
interpreter that can import `z3, duckdb, pandas, numpy, matplotlib` works; pass
it with `--python`. Nothing else is required: the old version is checked out
into a temporary `git worktree` and removed afterwards, and both versions run
under the same interpreter with only `PYTHONPATH` changed.

## What it produces

`benchmarks/results/<date>_<commit>/`:

| file | content |
|---|---|
| `summary.md` | machine info, corpus table (old vs. new when both ran), corpus cost drivers, examples regression table, scaling table, a Timeouts section, and the figure |
| `execution-times.tex` | the body of the paper's execution-time table: one row per corpus program with its citation key, plans x trials, median wall time and median solver time, in ascending order of wall time; rows whose wall time is at most `BOLD_WALL_AT` (1 s) are set in bold |
| `scaling.png`, `scaling.pdf` | the paper's scaling figure: wall time against each family's axis, four panels, timeouts and re-runs marked |
| `corpus_<commit>.json` | raw per-run records for `src/eval_examples` |
| `examples_<commit>.json` | raw per-run records for `src/examples` |
| `scaling_<commit>.json`, `scaling_<commit>_programs/` | raw records and the generated programs for the sweep |
| `scaling_long_<commit>.json`, `scaling_long_<commit>_programs/` | the re-run of the timed-out points under the longer limit |

Commit the whole directory; the JSON files are small and make later comparison possible.

## What is measured

Each program runs in its own subprocess, sequentially, stdout discarded.
`_runner.py` wraps four package entry points before the program starts, so
no example file is modified:

| column | meaning |
|---|---|
| `wall` | end-to-end time of one `python program.py` run, measured by the parent. This is the paper's quantity. |
| `solve` | time inside `Designer.eval`: building the z3 problem and getting one model |
| `plans` | `determine_plans`: solve plus instantiating random variables |
| `assign` | `assign(...)`: plans plus the DuckDB participant assignment |
| `analysis` | `Analysis(...)`, where the program calls it |
| `import` | importing `planet` (z3, pandas, duckdb) |

The phases nest, so `assign` includes `plans` includes `solve`. `assign` calls
`determine_plans` twice (once to assign, once to store the plans); the second
solve hits the design's snapshot cache, so the call counts in the JSON are 2
and the times are what the program actually spent.

Corpus programs are run `--reps` times (default 3) and the summary reports
medians over the runs that completed. The other examples run once; they are a
regression sweep, not paper numbers. A run that exceeds `--timeout` (default
300 s) is recorded as `timeout`; an exception is recorded as `error:<Type>`
with the last traceback line.

### Scaling sweep

`scaling.py` generates one program per point, in the style of the corpus
programs, and times it the same way. Every family sweeps one parameter, its
axis, of a design built on a Latin square (`within_subjects` +
`counterbalance` + `limit_plans(n)`: n plans of n trials) and keeps the rest
fixed, so each family isolates one construct:

| family | axis | design | plans x trials per participant |
|---|---|---|---|
| `latin_square` | n | Latin square over n conditions | n x n |
| `full_counterbalance` | n | the same without `limit_plans` | n! x n |
| `plans` | p | Latin square over n = 5 conditions with `limit_plans(p)` | p x n |
| `nested_latin_squares` | n | `nest(inner=latin_square(n), outer=latin_square(n))` | n² x n² |
| `crossed_latin_squares` | n | `cross(latin_square(n), latin_square(n))` | n² x n |
| `trials` | k | Latin square over n = 12 conditions, each condition repeated k times (`num_trials(k)` nested inside) | n x n·k |
| `nested_variable` | m | Latin square over n = 12 conditions with an uncounterbalanced within-subjects variable of m options nested in each condition | n x n·m |

Participants equal plans in every program. The plans axis uses multiples of n
because `limit_plans` rounds its argument down to a multiple of the
counterbalanced group size. The base n = 12 of the two width families matches
the widest corpus design, MouseRing Exp 1 (12 input methods x 10 pages x 5
repetitions = 600 trials per participant), so that design sits on the curves.
Each record stores the plan count and width the semantics predicts next to
what the solver produced.

Defaults: n = 2..12 for Latin squares and crosses, 2..10 for nests, 2..6 for
full counterbalancing; p = 5..120 in multiples of 5; k and m from 2 to 20 in
steps of 2, then doubling (k to 400, m to 100); 3 runs per point; 600 s per
run. `--ns`, `--ps`, `--ks`, `--ms`, `--base-n` and `--plans-n` override them.
A family stops at its first timed-out point (its remaining runs and all larger
points are skipped), since cost is monotone in the axis. Timeouts are results.

`run_all.py` then re-runs every timed-out point once with `--long-timeout`
(default 3600 s) via `scaling.py --rerun-timeouts`, into
`scaling_long_<commit>.json`. The summary's Timeouts section lists, per family,
the last completed point, the first timeout in the sweep, and the outcome of
the re-run; the figure draws sweep timeouts as crosses on the 600 s line and
the re-runs as hollow markers. Points past the first timeout were never run.

These programs call `assign` but do not print the assignment, so output
formatting is excluded.

## Running pieces by hand

```sh
PYTHONPATH=src .venv/bin/python benchmarks/_runner.py src/eval_examples/rambler.py   # one program, JSON on stderr
.venv/bin/python benchmarks/run_benchmark.py --src src --examples src/eval_examples --reps 3 --out corpus.json
.venv/bin/python benchmarks/run_benchmark.py --src src --examples src/examples --only mousering --reps 1 --out one.json
.venv/bin/python benchmarks/scaling.py --src src --families full_counterbalance --ns 2 3 4 5 --reps 3 --out scaling.json
.venv/bin/python benchmarks/scaling.py --src src --families trials --ks 50 100 --base-n 12 --out width.json
.venv/bin/python benchmarks/scaling.py --src src --rerun-timeouts scaling.json --timeout 3600 --reps 1 --out scaling_long.json
.venv/bin/python benchmarks/summarize.py --out-dir report --corpus-new corpus.json --scaling scaling.json --scaling-long scaling_long.json
PYTHONPATH=src .venv/bin/python benchmarks/results/<run>/scaling_<commit>_programs/plans_n05_p060.py   # one point by hand
```

## Caveats

- Absolute times depend on the machine; `summary.md` records CPU, memory,
  platform and interpreter. Compare versions on the same machine.
- z3 enables its own parallel mode (`solver.py` sets `parallel.enable`), so
  programs are run one at a time; do not run two benchmarks concurrently.
- `src/examples/scaling.py` is a developer script with 686 plans and may time
  out; that is a result, not a harness failure.
- The commit recorded in the JSON is the one whose `src/` was measured. A tag
  on the commit that adds the results folder points one commit later; the two
  differ only by `benchmarks/results/`.
