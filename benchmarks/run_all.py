"""Run the whole PLanet performance evaluation with one command.

    python benchmarks/run_all.py                 # full run, old vs new, ~1 h
    python benchmarks/run_all.py --quick         # pipeline check, a few minutes
    python benchmarks/run_all.py --skip-old      # only the current tree
    python benchmarks/run_all.py --old v0.1.0    # compare against another ref

Steps:
  1. check that the interpreter running this script can import PLanet's
     dependencies (z3, duckdb, pandas, numpy, matplotlib); if not, print the
     pip command and stop (or pass --install to run it);
  2. check out the old ref into a temporary git worktree (removed at the end);
  3. time every corpus program (src/eval_examples) on both versions, --reps times;
  4. time every other example (src/examples) once on both versions;
  5. run the scaling sweep on the new version (--scaling-reps runs per point);
  6. re-run the points that timed out, once each, under --long-timeout;
  7. write summary.md, execution-times.tex, scaling.png and scaling.pdf.

Everything lands in benchmarks/results/<date>_<new label>/. The same
interpreter and virtualenv is used for both versions; only PYTHONPATH differs.
"""
import argparse
import shutil
import subprocess
import sys
import tempfile
from datetime import date
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
DEFAULT_OLD = "1183212"  # last commit before the integer-count solver change


def sh(cmd, **kw):
    print("+ " + " ".join(str(c) for c in cmd), file=sys.stderr, flush=True)
    return subprocess.run([str(c) for c in cmd], check=True, **kw)


def check_deps(python, install):
    probe = [python, "-c", "import z3, duckdb, pandas, numpy, matplotlib"]
    if subprocess.run(probe, capture_output=True).returncode == 0:
        return
    if install:
        sh([python, "-m", "pip", "install", "-r", REPO / "requirements.txt"])
        subprocess.run(probe, check=True)
        return
    sys.exit(
        f"{python} cannot import PLanet's dependencies.\n"
        f"Run:  {python} -m pip install -r {REPO / 'requirements.txt'}\n"
        "or re-run with --install."
    )


def commit_of(tree):
    return subprocess.check_output(["git", "-C", str(tree), "rev-parse", "--short", "HEAD"], text=True).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--old", default=DEFAULT_OLD, help=f"git ref of the old version (default {DEFAULT_OLD})")
    ap.add_argument("--new", default=None, help="git ref of the new version (default: this working tree)")
    ap.add_argument("--reps", type=int, default=3, help="runs per corpus program")
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per corpus/example run")
    ap.add_argument("--scaling-timeout", type=float, default=600.0, help="seconds per scaling run")
    ap.add_argument("--scaling-reps", type=int, default=3, help="runs per scaling point")
    ap.add_argument("--long-timeout", type=float, default=3600.0, help="seconds for the re-run of timed-out scaling points")
    ap.add_argument("--ns", nargs="+", type=int, default=None, help="condition counts for the n-axis scaling families")
    ap.add_argument("--skip-old", action="store_true")
    ap.add_argument("--skip-examples", action="store_true")
    ap.add_argument("--skip-scaling", action="store_true")
    ap.add_argument("--skip-long", action="store_true", help="do not re-run timed-out scaling points")
    ap.add_argument("--quick", action="store_true", help="1 rep, 60 s timeouts, n <= 5: checks the pipeline")
    ap.add_argument("--install", action="store_true", help="pip install requirements.txt if imports fail")
    ap.add_argument("--out-dir", default=None, help="default benchmarks/results/<date>_<new label>")
    ap.add_argument("--python", default=sys.executable)
    args = ap.parse_args()

    scaling_extra = []
    if args.quick:
        args.reps, args.timeout, args.scaling_timeout, args.scaling_reps, args.long_timeout = 1, 60.0, 60.0, 1, 60.0
        args.ns = args.ns or [2, 3, 4, 5]
        scaling_extra = ["--ps", "5", "10", "--ks", "1", "2", "--ms", "2", "4", "--base-n", "4"]

    check_deps(args.python, args.install)

    tmp = Path(tempfile.mkdtemp(prefix="planet-perf-"))
    worktrees = []

    def checkout(ref):
        tree = tmp / f"planet-{ref.replace('/', '_')}"
        sh(["git", "-C", REPO, "worktree", "add", "--detach", tree, ref], stdout=subprocess.DEVNULL)
        worktrees.append(tree)
        return tree

    try:
        new_tree = checkout(args.new) if args.new else REPO
        new_label = commit_of(new_tree) + ("" if args.new or not dirty(REPO) else "-dirty")
        out_dir = Path(args.out_dir) if args.out_dir else HERE / "results" / f"{date.today().isoformat()}_{new_label}"
        out_dir.mkdir(parents=True, exist_ok=True)
        versions = [("new", new_tree, new_label)]
        if not args.skip_old:
            old_tree = checkout(args.old)
            versions.append(("old", old_tree, commit_of(old_tree)))

        files = {}
        for which, tree, label in versions:
            corpus = out_dir / f"corpus_{label}.json"
            sh([args.python, HERE / "run_benchmark.py", "--src", tree / "src", "--examples", tree / "src" / "eval_examples",
                "--reps", args.reps, "--timeout", args.timeout, "--label", label, "--out", corpus, "--python", args.python])
            files[f"corpus_{which}"] = corpus
            if not args.skip_examples:
                examples = out_dir / f"examples_{label}.json"
                sh([args.python, HERE / "run_benchmark.py", "--src", tree / "src", "--examples", tree / "src" / "examples",
                    "--reps", 1, "--timeout", args.timeout, "--label", label, "--out", examples, "--python", args.python])
                files[f"examples_{which}"] = examples

        if not args.skip_scaling:
            scaling = out_dir / f"scaling_{new_label}.json"
            cmd = [args.python, HERE / "scaling.py", "--src", new_tree / "src", "--timeout", args.scaling_timeout,
                   "--reps", args.scaling_reps, "--label", new_label, "--out", scaling, "--python", args.python]
            if args.ns:
                cmd += ["--ns", *args.ns]
            cmd += scaling_extra
            sh(cmd)
            files["scaling"] = scaling
            if not args.skip_long and has_timeouts(scaling):
                scaling_long = out_dir / f"scaling_long_{new_label}.json"
                sh([args.python, HERE / "scaling.py", "--src", new_tree / "src", "--timeout", args.long_timeout,
                    "--reps", 1, "--rerun-timeouts", scaling, "--label", new_label, "--out", scaling_long,
                    "--python", args.python])
                files["scaling_long"] = scaling_long

        cmd = [args.python, HERE / "summarize.py", "--out-dir", out_dir, "--corpus-new", files["corpus_new"]]
        for key, flag in (("corpus_old", "--corpus-old"), ("examples_new", "--examples-new"),
                          ("examples_old", "--examples-old"), ("scaling", "--scaling"),
                          ("scaling_long", "--scaling-long")):
            if key in files:
                cmd += [flag, files[key]]
        sh(cmd)
        print(f"\nresults: {out_dir}", file=sys.stderr)
    finally:
        for tree in worktrees:
            subprocess.run(["git", "-C", str(REPO), "worktree", "remove", "--force", str(tree)],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        shutil.rmtree(tmp, ignore_errors=True)


def has_timeouts(scaling_json):
    import json
    with open(scaling_json) as fh:
        return any(r["status"] == "timeout" for r in json.load(fh)["records"])


def dirty(tree):
    out = subprocess.check_output(["git", "-C", str(tree), "status", "--porcelain", "--untracked-files=no", "--", "src/planet"], text=True)
    return bool(out.strip())


if __name__ == "__main__":
    main()
