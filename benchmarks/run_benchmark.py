"""Time every PLanet example script under one or more directories.

Example:

    .venv/bin/python benchmarks/run_benchmark.py \
        --src src --examples src/eval_examples --reps 3 --timeout 300 \
        --label 1369473 --out benchmarks/results/2026-10-09_corpus_1369473.json

Each script runs in its own subprocess (DuckDB tables and the z3 context are
process-global, and a timeout must not take the batch down), sequentially, with
stdout discarded. `benchmarks/_runner.py` does the in-process timing and reports
one JSON record per run; this script adds the parent-measured wall time, which is
the quantity the paper's execution-time table reports.

Output JSON: {"meta": {...}, "records": [record, ...]} with one record per
(script, rep). `script` is the path relative to the parent of --src, so records
from different checkouts of the repository share keys.
"""
import argparse
import json
import os
import platform
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "_runner.py"
RESULT_MARKER = "@@PLANET_BENCH@@ "


def machine_info():
    """CPU model and memory, on macOS (sysctl) or Linux (/proc, sysconf)."""
    info = {"platform": platform.platform(), "machine": platform.machine(), "cpu": platform.processor()}
    try:
        info["cpu"] = subprocess.check_output(
            ["sysctl", "-n", "machdep.cpu.brand_string"], text=True, stderr=subprocess.DEVNULL
        ).strip()
        mem = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True, stderr=subprocess.DEVNULL))
        info["memory_gb"] = round(mem / 2**30)
        return info
    except Exception:
        pass
    try:
        with open("/proc/cpuinfo") as fh:
            for line in fh:
                if line.lower().startswith("model name"):
                    info["cpu"] = line.split(":", 1)[1].strip()
                    break
        info["memory_gb"] = round(os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") / 2**30)
    except Exception:
        pass
    return info


def git_commit(tree):
    try:
        return subprocess.check_output(
            ["git", "-C", str(tree), "rev-parse", "--short", "HEAD"], text=True
        ).strip()
    except Exception:
        return None


def find_scripts(dirs):
    scripts = []
    for d in dirs:
        for p in sorted(Path(d).rglob("*.py")):
            if "__pycache__" in p.parts or p.name == "__init__.py":
                continue
            scripts.append(p)
    return scripts


def run_once(script, src, python, timeout, cwd):
    env = dict(os.environ)
    env["PYTHONPATH"] = str(src)
    env["MPLBACKEND"] = "Agg"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [python, str(RUNNER), str(Path(script).resolve())],
            cwd=cwd,
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return {
            "status": "timeout",
            "error": f"exceeded {timeout}s",
            "phases": {},
            "calls": {},
            "plans": None,
            "trials": None,
            "participants": None,
            "wall": time.perf_counter() - t0,
        }
    wall = time.perf_counter() - t0

    rec = None
    for line in reversed(proc.stderr.splitlines()):
        if line.startswith(RESULT_MARKER):
            rec = json.loads(line[len(RESULT_MARKER):])
            break
    if rec is None:
        tail = proc.stderr.strip().splitlines()
        rec = {
            "status": f"error:exit{proc.returncode}",
            "error": tail[-1] if tail else "",
            "phases": {},
            "calls": {},
            "plans": None,
            "trials": None,
            "participants": None,
        }
    rec["wall"] = wall
    rec["returncode"] = proc.returncode
    return rec


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", required=True, help="the tree's src/ directory (put on PYTHONPATH)")
    ap.add_argument("--examples", nargs="+", required=True, help="directories of example scripts")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--timeout", type=float, default=300.0, help="seconds per run")
    ap.add_argument("--label", default=None, help="version label; defaults to the git commit of --src")
    ap.add_argument("--out", required=True, help="output JSON path")
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--cwd", default=None, help="working directory for the scripts (default: a temp dir)")
    ap.add_argument("--only", nargs="*", default=None, help="substring filters on script paths")
    args = ap.parse_args()

    src = Path(args.src).resolve()
    tree = src.parent
    scripts = find_scripts(args.examples)
    if args.only:
        scripts = [s for s in scripts if any(f in str(s) for f in args.only)]
    if not scripts:
        sys.exit("no scripts found")

    cwd = args.cwd
    if cwd is None:
        import tempfile
        cwd = tempfile.mkdtemp(prefix="planet-bench-")

    label = args.label or git_commit(tree) or "unknown"
    meta = {
        "label": label,
        "commit": git_commit(tree),
        "src": str(src),
        "examples": [str(Path(d).resolve()) for d in args.examples],
        "python": args.python,
        "reps": args.reps,
        "timeout": args.timeout,
        "started": datetime.now().isoformat(timespec="seconds"),
        **machine_info(),
    }

    records = []
    print(f"[{label}] {len(scripts)} scripts x {args.reps} reps, timeout {args.timeout:.0f}s", file=sys.stderr)
    for script in scripts:
        rel = str(script.resolve().relative_to(tree)) if tree in script.resolve().parents else str(script)
        for rep in range(args.reps):
            rec = run_once(script, src, args.python, args.timeout, cwd)
            rec["script"] = rel
            rec["rep"] = rep
            records.append(rec)
            solve = rec["phases"].get("solve")
            solve_s = f"solve={solve:7.2f}s" if solve is not None else "solve=   n/a "
            print(
                f"  {rel:45} rep{rep} {rec['status']:18} wall={rec['wall']:7.2f}s {solve_s} "
                f"plans={rec.get('plans')} {rec.get('error', '')[:80]}",
                file=sys.stderr,
                flush=True,
            )
            # Write incrementally so a killed batch still leaves data behind.
            Path(args.out).parent.mkdir(parents=True, exist_ok=True)
            with open(args.out, "w") as fh:
                json.dump({"meta": meta, "records": records}, fh, indent=1)

    meta["finished"] = datetime.now().isoformat(timespec="seconds")
    with open(args.out, "w") as fh:
        json.dump({"meta": meta, "records": records}, fh, indent=1)
    print(f"wrote {args.out} ({len(records)} records)", file=sys.stderr)


if __name__ == "__main__":
    main()
