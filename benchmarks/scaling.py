"""Runtime of PLanet as designs grow (the paper's scaling experiment).

Examples:

    .venv/bin/python benchmarks/scaling.py --src src --reps 3 --timeout 600 \
        --out benchmarks/results/<run>/scaling_<label>.json
    .venv/bin/python benchmarks/scaling.py --src src --timeout 3600 --reps 1 \
        --rerun-timeouts benchmarks/results/<run>/scaling_<label>.json \
        --out benchmarks/results/<run>/scaling_long_<label>.json

Generates one small PLanet program per data point, in the same style as the
corpus programs, and times each one with the same machinery as
run_benchmark.py (subprocess per run, phases from _runner.py, parent-measured
wall time). The generated programs are kept next to the JSON so a point can be
re-run by hand with `PYTHONPATH=src python <program>.py`.

Every family sweeps one size parameter, its axis, of a design built on a
Latin square (within_subjects + counterbalance + limit_plans(n): n plans of n
trials). The other parameters are fixed by the family's base, so each family
isolates one construct of the language:

  family                 axis  design                                             plans x trials/participant
  latin_square           n     Latin square over n conditions                      n    x n
  full_counterbalance    n     the same without limit_plans                        n!   x n
  plans                  p     Latin square over n (base) conditions with          p    x n
                               limit_plans(p); p must be a multiple of n, since
                               limit_plans rounds down to one
  nested_latin_squares   n     nest(inner=Latin square(n), outer=Latin square(n))  n^2  x n^2
  crossed_latin_squares  n     cross(Latin square(n), Latin square(n))             n^2  x n
  trials                 k     Latin square over n (base) conditions with each     n    x n*k
                               condition repeated k times (num_trials)
  nested_variable        m     Latin square over n (base) conditions with an       n    x n*m
                               uncounterbalanced within-subjects variable of m
                               options nested in each condition

Default bases: plans uses n = 5, so p runs from 5 to 5! = 120; trials and
nested_variable use n = 12, the widest corpus design (MouseRing Exp 1 is 12
conditions x 10 pages x 5 repetitions = 600 trials per participant).

Each record carries the expected plan count and width from the formulas above
next to the measured ones, as a check that the implementation materializes the
plans the semantics predicts.

A family stops at its first timeout, since cost is monotone in its axis; the
remaining reps of that point and all larger points are skipped. Timeouts are
results and are recorded. --rerun-timeouts replays exactly the timed-out
points of an earlier sweep (same generated programs) under a longer --timeout,
into a second JSON.

The programs call assign() but do not print the assignment, so the time is the
solver plus assignment, not output formatting.
"""
import argparse
import json
import math
import sys
import tempfile
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_benchmark import git_commit, machine_info, run_once  # noqa: E402

HEADER = "from planet import *\nimport math\n"


# Each builder returns (program text, expected shape). The shape gives the
# number of conditions of the base Latin square and the plan count and width
# (trials per participant) the semantics predicts for the design.


def latin_square(n, base=None):
    text = HEADER + f"""
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
    return text, {"n": n, "expected_plans": n, "expected_width": n}


def full_counterbalance(n, base=None):
    text = HEADER + f"""
n = {n}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
)
assign(Units(math.factorial(n)), design)
"""
    return text, {"n": n, "expected_plans": math.factorial(n), "expected_width": n}


def plans(p, base):
    n = base["n"]
    text = HEADER + f"""
n, p = {n}, {p}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(p)
)
assign(Units(p), design)
"""
    return text, {"n": n, "expected_plans": p, "expected_width": n}


def nested_latin_squares(n, base=None):
    text = HEADER + f"""
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
    return text, {"n": n, "expected_plans": n * n, "expected_width": n * n}


def crossed_latin_squares(n, base=None):
    text = HEADER + f"""
n = {n}
a = ExperimentVariable("a", options=[f"a{{i}}" for i in range(n)])
b = ExperimentVariable("b", options=[f"b{{i}}" for i in range(n)])
da = (
    Design()
        .within_subjects(a)
        .counterbalance(a)
        .limit_plans(n)
)
db = (
    Design()
        .within_subjects(b)
        .counterbalance(b)
        .limit_plans(n)
)
design = cross(da, db)
assign(Units(n * n), design)
"""
    return text, {"n": n, "expected_plans": n * n, "expected_width": n}


def trials(k, base):
    n = base["n"]
    if k == 1:
        text, _ = latin_square(n)
    else:
        text = HEADER + f"""
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
    return text, {"n": n, "expected_plans": n, "expected_width": n * k}


def nested_variable(m, base):
    n = base["n"]
    text = HEADER + f"""
n, m = {n}, {m}
cond = ExperimentVariable("cond", options=[f"c{{i}}" for i in range(n)])
inner_var = ExperimentVariable("inner", options=[f"i{{i}}" for i in range(m)])
latin = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
inner = Design().within_subjects(inner_var)
design = nest(inner=inner, outer=latin)
assign(Units(n), design)
"""
    return text, {"n": n, "expected_plans": n, "expected_width": n * m}


# axis: the swept parameter; xs: its default values; base: the fixed parameters
# (a base n for families that keep the Latin square fixed).
FAMILIES = {
    "latin_square": {"build": latin_square, "axis": "n", "xs": list(range(2, 13)), "base": {}},
    "full_counterbalance": {"build": full_counterbalance, "axis": "n", "xs": [2, 3, 4, 5, 6], "base": {}},
    "plans": {"build": plans, "axis": "p", "xs": [5, 10, 15, 20, 25, 30, 40, 50, 60, 80, 100, 120], "base": {"n": 5}},
    "nested_latin_squares": {"build": nested_latin_squares, "axis": "n", "xs": list(range(2, 11)), "base": {}},
    "crossed_latin_squares": {"build": crossed_latin_squares, "axis": "n", "xs": list(range(2, 13)), "base": {}},
    "trials": {"build": trials, "axis": "k", "xs": [1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 30, 40, 50, 100, 200, 400], "base": {"n": 12}},
    "nested_variable": {"build": nested_variable, "axis": "m", "xs": [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 30, 40, 50, 100], "base": {"n": 12}},
}

AXIS_LABELS = {"n": "number of conditions", "p": "plan limit", "k": "repetitions per condition", "m": "options of the nested variable"}


def point_name(family, x, base):
    spec = FAMILIES[family]
    tag = f"_n{base['n']:02d}" if "n" in base else ""
    digits = 2 if spec["axis"] == "n" else 3
    return f"{family}{tag}_{spec['axis']}{x:0{digits}d}.py"


def family_base(family, args):
    base = dict(FAMILIES[family]["base"])
    if "n" in base:
        base["n"] = args.plans_n if family == "plans" else args.base_n
    return base


def family_xs(family, args):
    axis = FAMILIES[family]["axis"]
    given = {"n": args.ns, "p": args.ps, "k": args.ks, "m": args.ms}[axis]
    xs = list(given) if given else list(FAMILIES[family]["xs"])
    if family == "plans":
        n = family_base(family, args)["n"]
        bad = [p for p in xs if p % n]
        if bad:
            print(f"  plans: dropping p={bad}; limit_plans rounds down to a multiple of n={n}", file=sys.stderr)
        xs = [p for p in xs if p % n == 0]
    return xs


def run_point(family, x, base, programs, args, src, cwd, records, save):
    """Run one point up to args.reps times; stop at the first timeout. Returns True if it timed out."""
    spec = FAMILIES[family]
    text, shape = spec["build"](x, base)
    name = point_name(family, x, base)
    script = programs / name
    script.write_text(text)
    axis = spec["axis"]
    fields = {
        "family": family,
        "axis": axis,
        "x": x,
        "n": shape["n"],
        "k": x if axis == "k" else 1,
        "p": x if axis == "p" else None,
        "m": x if axis == "m" else None,
        "expected_plans": shape["expected_plans"],
        "expected_width": shape["expected_width"],
        "trials_total": shape["expected_width"],
        "script": name,
        "timeout": args.timeout,
    }
    for rep in range(args.reps):
        rec = run_once(script, src, args.python, args.timeout, cwd)
        rec.update(fields)
        rec["rep"] = rep
        records.append(rec)
        solve = rec["phases"].get("solve")
        solve_s = f"solve={solve:8.2f}s" if solve is not None else "solve=     n/a "
        print(
            f"  {family:22} {axis}={x:3d} rep{rep} {rec['status']:18} wall={rec['wall']:8.2f}s {solve_s} "
            f"plans={rec.get('plans')} trials={rec.get('trials')} {rec.get('error', '')[:70]}",
            file=sys.stderr,
            flush=True,
        )
        save()
        if rec["status"] == "timeout":
            return True
    return False


def timed_out_points(path):
    """The timed-out points of an earlier sweep: [(family, x, base)], one per family."""
    with open(path) as fh:
        data = json.load(fh)
    seen = {}
    for rec in data["records"]:
        if rec["status"] != "timeout" or rec["family"] not in FAMILIES:
            continue
        key = (rec["family"], rec["x"])
        base = {"n": rec["n"]} if "n" in FAMILIES[rec["family"]]["base"] else {}
        seen.setdefault(key, base)
    return [(fam, x, base) for (fam, x), base in sorted(seen.items())]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", required=True, help="the tree's src/ directory (put on PYTHONPATH)")
    ap.add_argument("--out", required=True, help="output JSON path; programs go in <out stem>_programs/")
    ap.add_argument("--families", nargs="+", default=list(FAMILIES), choices=list(FAMILIES))
    ap.add_argument("--ns", nargs="+", type=int, default=None, help="values for families whose axis is n")
    ap.add_argument("--ps", nargs="+", type=int, default=None, help="values for the plans family (multiples of --plans-n)")
    ap.add_argument("--ks", nargs="+", type=int, default=None, help="values for the trials family")
    ap.add_argument("--ms", nargs="+", type=int, default=None, help="values for the nested_variable family")
    ap.add_argument("--base-n", type=int, default=12, help="conditions of the Latin square in trials and nested_variable")
    ap.add_argument("--plans-n", type=int, default=5, help="conditions of the Latin square in plans")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=float, default=600.0, help="seconds per run")
    ap.add_argument("--rerun-timeouts", default=None, metavar="JSON", help="re-run only the timed-out points of this earlier sweep")
    ap.add_argument("--label", default=None)
    ap.add_argument("--python", default=sys.executable)
    args = ap.parse_args()

    src = Path(args.src).resolve()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    programs = out.parent / (out.stem + "_programs")
    programs.mkdir(exist_ok=True)
    cwd = tempfile.mkdtemp(prefix="planet-scaling-")

    label = args.label or git_commit(src.parent) or "unknown"
    meta = {
        "label": label,
        "commit": git_commit(src.parent),
        "src": str(src),
        "python": args.python,
        "reps": args.reps,
        "timeout": args.timeout,
        "started": datetime.now().isoformat(timespec="seconds"),
        **machine_info(),
    }
    records = []

    def save():
        with open(out, "w") as fh:
            json.dump({"meta": meta, "records": records}, fh, indent=1)

    if args.rerun_timeouts:
        points = timed_out_points(args.rerun_timeouts)
        meta["rerun_of"] = str(Path(args.rerun_timeouts).name)
        meta["points"] = [{"family": f, "x": x, **b} for f, x, b in points]
        print(f"[{label}] re-running {len(points)} timed-out point(s) of {args.rerun_timeouts} at {args.timeout:.0f}s", file=sys.stderr)
        for family, x, base in points:
            run_point(family, x, base, programs, args, src, cwd, records, save)
    else:
        meta["families"] = args.families
        meta["axes"] = {f: family_xs(f, args) for f in args.families}
        meta["bases"] = {f: family_base(f, args) for f in args.families if family_base(f, args)}
        print(f"[{label}] scaling: {args.families}, {args.reps} rep(s), timeout {args.timeout:.0f}s", file=sys.stderr)
        for family in args.families:
            base = family_base(family, args)
            for x in family_xs(family, args):
                if run_point(family, x, base, programs, args, src, cwd, records, save):
                    print(f"  {family}: stopping after timeout at {FAMILIES[family]['axis']}={x}", file=sys.stderr)
                    break

    meta["finished"] = datetime.now().isoformat(timespec="seconds")
    save()
    print(f"wrote {out} ({len(records)} records)", file=sys.stderr)


if __name__ == "__main__":
    main()
