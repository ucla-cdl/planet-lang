"""Runtime of PLanet as designs grow (the paper's scaling experiment).

Example:

    .venv/bin/python benchmarks/scaling.py --src src --timeout 600 \
        --out benchmarks/results/<run>/scaling_1369473.json

Generates one small PLanet program per data point, in the same style as the
corpus programs, and times each one with the same machinery as
run_benchmark.py (subprocess per run, phases from _runner.py, parent-measured
wall time). The generated programs are kept next to the JSON so a point can be
re-run by hand.

Families (n = number of conditions):
  latin_square           within_subjects + counterbalance + limit_plans(n)   -> n plans
  full_counterbalance    within_subjects + counterbalance, no plan limit      -> n! plans
  nested_latin_squares   nest(inner=latin_square(n), outer=latin_square(n))
  trials                 latin_square(4) with each condition repeated k times
                         via nest(inner=Design().num_trials(k), outer=...)

A family stops at the first n that times out, since cost is monotone in n.
The programs call assign() but do not print the assignment, so the time is the
solver plus assignment, not output formatting.
"""
import argparse
import json
import sys
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_benchmark import git_commit, machine_info, run_once  # noqa: E402

HEADER = "from planet import *\nimport math\n"


def latin_square(n, k=1):
    return HEADER + f"""
n = {n}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
assign(Units(n), design)
"""


def full_counterbalance(n, k=1):
    return HEADER + f"""
n = {n}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
)
assign(Units(math.factorial(n)), design)
"""


def nested_latin_squares(n, k=1):
    return HEADER + f"""
n = {n}
outer_var = ExperimentVariable("outer", options=[f"o{{i}}" for i in range(n)])
inner_var = ExperimentVariable("inner", options=[f"i{{i}}" for i in range(n)])
outer = (
    Design()
        .within_subjects(outer_var)
        .counterbalance(outer_var)
        .limit_plans(n)
)
inner = (
    Design()
        .within_subjects(inner_var)
        .counterbalance(inner_var)
        .limit_plans(n)
)
design = nest(inner=inner, outer=outer)
assign(Units(n * n), design)
"""


def trials(n, k):
    if k == 1:
        return latin_square(n)
    return HEADER + f"""
n, k = {n}, {k}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
latin = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
repeat = Design().num_trials(k)
design = nest(inner=repeat, outer=latin)
assign(Units(n), design)
"""


FAMILIES = {
    "latin_square": latin_square,
    "full_counterbalance": full_counterbalance,
    "nested_latin_squares": nested_latin_squares,
    "trials": trials,
}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", required=True, help="the tree's src/ directory (put on PYTHONPATH)")
    ap.add_argument("--out", required=True, help="output JSON path; programs go in <out stem>_programs/")
    ap.add_argument("--families", nargs="+", default=list(FAMILIES), choices=list(FAMILIES))
    ap.add_argument("--ns", nargs="+", type=int, default=[2, 3, 4, 5, 6, 7, 8, 10], help="condition counts")
    ap.add_argument("--trials-n", type=int, default=4, help="fixed n for the trials family")
    ap.add_argument("--ks", nargs="+", type=int, default=[1, 2, 3, 4, 5], help="repetitions for the trials family")
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=600.0, help="seconds per run")
    ap.add_argument("--label", default=None)
    ap.add_argument("--python", default=sys.executable)
    args = ap.parse_args()

    src = Path(args.src).resolve()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    programs = out.parent / (out.stem + "_programs")
    programs.mkdir(exist_ok=True)
    import tempfile
    cwd = tempfile.mkdtemp(prefix="planet-scaling-")

    label = args.label or git_commit(src.parent) or "unknown"
    meta = {
        "label": label,
        "commit": git_commit(src.parent),
        "src": str(src),
        "python": args.python,
        "reps": args.reps,
        "timeout": args.timeout,
        "ns": args.ns,
        "trials_n": args.trials_n,
        "ks": args.ks,
        "started": datetime.now().isoformat(timespec="seconds"),
        **machine_info(),
    }
    records = []

    def save():
        with open(out, "w") as fh:
            json.dump({"meta": meta, "records": records}, fh, indent=1)

    print(f"[{label}] scaling: {args.families}, timeout {args.timeout:.0f}s", file=sys.stderr)
    for family in args.families:
        build = FAMILIES[family]
        points = [(args.trials_n, k) for k in args.ks] if family == "trials" else [(n, 1) for n in args.ns]
        for n, k in points:
            name = f"{family}_n{n:02d}" + (f"_k{k}" if family == "trials" else "") + ".py"
            script = programs / name
            script.write_text(build(n, k))
            timed_out = False
            for rep in range(args.reps):
                rec = run_once(script, src, args.python, args.timeout, cwd)
                rec.update({"family": family, "n": n, "k": k, "trials_total": n * k, "script": name, "rep": rep})
                records.append(rec)
                solve = rec["phases"].get("solve")
                solve_s = f"solve={solve:8.2f}s" if solve is not None else "solve=     n/a "
                print(
                    f"  {family:22} n={n:2d} k={k} rep{rep} {rec['status']:18} wall={rec['wall']:8.2f}s {solve_s} "
                    f"plans={rec.get('plans')} {rec.get('error', '')[:70]}",
                    file=sys.stderr,
                    flush=True,
                )
                save()
                timed_out = timed_out or rec["status"] == "timeout"
            if timed_out:
                print(f"  {family}: stopping after timeout at n={n}", file=sys.stderr)
                break

    meta["finished"] = datetime.now().isoformat(timespec="seconds")
    save()
    print(f"wrote {out} ({len(records)} records)", file=sys.stderr)


if __name__ == "__main__":
    main()
