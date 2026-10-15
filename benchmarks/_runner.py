"""In-process runner for one PLanet example script.

Usage (normally invoked by run_benchmark.py, not by hand):

    PYTHONPATH=<tree>/src python benchmarks/_runner.py path/to/example.py

Times the package entry points by wrapping them before the script runs, so no
example needs editing. The script's own stdout is left alone; the result is
written to stderr as a single JSON line prefixed with RESULT_MARKER.

Phases (seconds, cumulative over all calls in the script):
  import    importing the planet package (z3, pandas, duckdb, numpy)
  solve     planet.designer.Designer.eval      z3 encoding + get_one_model
  plans     planet.assignment.determine_plans  solve + random-variable instantiation
  assign    planet.assignment.assign           plans + DuckDB participant assignment
  analysis  planet.analysis.Analysis.__init__  effect analysis, if the script calls it
  total     runner start to script end

The phases nest (assign includes plans includes solve), so they are reported
as measured, not subtracted.
"""
import json
import os
import runpy
import sys
import time
import traceback

RESULT_MARKER = "@@PLANET_BENCH@@ "


def main():
    script = sys.argv[1]
    rec = {
        "script": script,
        "status": "ok",
        "error": "",
        "phases": {},
        "calls": {},
        "plans": None,
        "trials": None,
        "participants": None,
        "python": sys.version.split()[0],
        "z3": None,
    }
    t_start = time.perf_counter()

    def add(name, dt):
        rec["phases"][name] = rec["phases"].get(name, 0.0) + dt
        rec["calls"][name] = rec["calls"].get(name, 0) + 1

    try:
        t0 = time.perf_counter()
        import planet
        import planet.assignment as assignment_mod
        import planet.designer as designer_mod
        import planet.analysis as analysis_mod
        import z3
        add("import", time.perf_counter() - t0)
        rec["z3"] = z3.get_version_string()
    except Exception as exc:  # pragma: no cover - environment problem
        rec["status"] = f"error:{type(exc).__name__}"
        rec["error"] = traceback.format_exc().strip().splitlines()[-1]
        emit(rec, t_start)
        return

    def timed(name, fn, capture=None):
        def wrapper(*args, **kwargs):
            t0 = time.perf_counter()
            try:
                result = fn(*args, **kwargs)
            finally:
                add(name, time.perf_counter() - t0)
            if capture is not None:
                try:
                    capture(result, args, kwargs)
                except Exception:
                    pass
            return result

        wrapper.__wrapped__ = fn
        return wrapper

    def capture_eval(result, args, kwargs):
        # Designer.eval returns an ndarray of shape (plans, trials), or empty.
        shape = getattr(result, "shape", None)
        if shape and len(shape) == 2:
            rec["plans"], rec["trials"] = int(shape[0]), int(shape[1])

    def capture_plans(result, args, kwargs):
        # determine_plans returns a list/array of plans after random variables
        # are instantiated; this is the final plan matrix.
        if len(result):
            rec["plans"] = int(len(result))
            rec["trials"] = int(len(result[0]))

    def capture_assign(result, args, kwargs):
        units = args[0] if args else kwargs.get("units")
        rec["participants"] = int(len(units))

    designer_mod.Designer.eval = timed("solve", designer_mod.Designer.eval, capture_eval)
    assignment_mod.determine_plans = timed(
        "plans", assignment_mod.determine_plans, capture_plans
    )
    wrapped_assign = timed("assign", assignment_mod.assign, capture_assign)
    assignment_mod.assign = wrapped_assign
    planet.assign = wrapped_assign  # `from planet import *` binds this name
    analysis_mod.Analysis.__init__ = timed("analysis", analysis_mod.Analysis.__init__)

    sys.argv = [script]
    sys.path.insert(0, os.path.dirname(os.path.abspath(script)))
    try:
        runpy.run_path(script, run_name="__main__")
    except SystemExit as exc:
        if exc.code not in (None, 0):
            rec["status"] = f"error:SystemExit({exc.code})"
    except BaseException as exc:
        rec["status"] = f"error:{type(exc).__name__}"
        rec["error"] = traceback.format_exc().strip().splitlines()[-1]
    emit(rec, t_start)


def emit(rec, t_start):
    rec["phases"]["total"] = time.perf_counter() - t_start
    sys.stdout.flush()
    sys.stderr.write(RESULT_MARKER + json.dumps(rec) + "\n")
    sys.stderr.flush()


if __name__ == "__main__":
    main()
