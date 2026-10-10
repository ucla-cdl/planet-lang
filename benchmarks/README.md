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
| `summary.md` | machine info, corpus table old vs. new, examples regression table, scaling table and notes |
| `execution-times.tex` | one row per corpus program, median wall time, in the shape of the paper's table |
| `scaling.png` | wall time vs. number of conditions (log scale), one line per family, timeouts marked |
| `corpus_<commit>.json` | raw per-run records for `src/eval_examples` |
| `examples_<commit>.json` | raw per-run records for `src/examples` |
| `scaling_<commit>.json`, `scaling_<commit>_programs/` | raw records and the generated programs for the sweep |

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
programs, and times it the same way. Families, for n conditions:

- `latin_square`: `within_subjects` + `counterbalance` + `limit_plans(n)`, n participants
- `full_counterbalance`: same without `limit_plans`, so n! plans and n! participants
- `nested_latin_squares`: `nest(inner=latin_square(n), outer=latin_square(n))`, n² participants
- `trials`: `latin_square(4)` with each condition repeated k times via `nest(inner=Design().num_trials(k), outer=...)`

Default n ∈ {2, 3, 4, 5, 6, 7, 8, 10}, k ∈ {1..5}, 600 s per point, and a
family stops at its first timeout. These programs call `assign` but do not
print the assignment, so output formatting is excluded.

## Running pieces by hand

```sh
PYTHONPATH=src .venv/bin/python benchmarks/_runner.py src/eval_examples/rambler.py   # one program, JSON on stderr
.venv/bin/python benchmarks/run_benchmark.py --src src --examples src/eval_examples --reps 3 --out corpus.json
.venv/bin/python benchmarks/run_benchmark.py --src src --examples src/examples --only mousering --reps 1 --out one.json
.venv/bin/python benchmarks/scaling.py --src src --families full_counterbalance --ns 2 3 4 5 --out scaling.json
.venv/bin/python benchmarks/summarize.py --out-dir report --corpus-new corpus.json --scaling scaling.json
```

## Caveats

- Absolute times depend on the machine; `summary.md` records CPU, memory,
  platform and interpreter. Compare versions on the same machine.
- z3 enables its own parallel mode (`solver.py` sets `parallel.enable`), so
  programs are run one at a time; do not run two benchmarks concurrently.
- `src/examples/scaling.py` is a developer script with 686 plans and may time
  out; that is a result, not a harness failure.
