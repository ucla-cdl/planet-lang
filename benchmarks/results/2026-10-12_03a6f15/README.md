# Benchmark run of 2026-10-12: `main` against the seven open fixes

Two trees, one machine, the settings of `run_all.py`:

| label | tree |
|---|---|
| `810b45c` | `main` at 810b45c (the code of the paper's run; `perf-eval-2026-10` only adds `benchmarks/`) |
| `03a6f15` | `perf-eval-2026-10` at 55da752 with PRs #23 (c578a6e), #25 (dd03e4f), #26 (4ea94e9), #27 (6e4ef68), #29 (ede5f9b), #24 (5e0074c) and #28 (6b9e51a) merged in that order; no conflicts, unit suite 82/82 |

Machine: AMD EPYC 9555 (Zen 5), 2 sockets x 64 cores, 1511 GB; Linux 6.8.0; Python 3.12.13; z3 4.13.3; duckdb 1.1.3; pandas 2.2.3; numpy 2.1.2. Load stayed below 4 of 256 threads.

z3 is single-threaded, so the sequential stages of `run_all.py` ran as parallel processes with the same arguments:

- corpus: `run_benchmark.py --reps 3 --timeout 300` on `src/eval_examples`, old and new side by side;
- examples: `run_benchmark.py --reps 1 --timeout 300` on `src/examples`, split so `scaling.py` (which always hits the limit) ran on its own, shards merged afterwards;
- scaling: `scaling.py --reps 3 --timeout 600 --families F`, one process per family, for both trees; the timed-out points re-run once with `--timeout 3600`; the seven shards merged into `scaling_<label>.json` and `scaling_long_<label>.json` (records concatenated, metadata from the shards with the earliest start and the latest finish; `meta.parallel_shards` lists them);
- `summarize.py` over the new scaling sweep and both corpus and examples runs, as in `run_all.py`; the figures and `execution-times.tex` are therefore of the new tree.

Files:

| file | content |
|---|---|
| `summary.md`, `execution-times.tex`, `scaling_overview.*`, `scaling_families.*` | written by `summarize.py` |
| `corpus_<label>.json`, `examples_<label>.json` | per-run records of `src/eval_examples` and `src/examples`, both trees |
| `scaling_<label>.json`, `scaling_<label>_programs/` | the sweep and its generated programs, both trees |
| `scaling_long_<label>.json`, `scaling_long_<label>_programs/` | the 3600 s re-run of the timed-out points, both trees |
| `scaling-old-vs-new.md` | the two sweeps side by side, one row per point |

`git rev-parse` of `03a6f15` does not resolve in this repository: it is a local merge commit, described above by its parts.
