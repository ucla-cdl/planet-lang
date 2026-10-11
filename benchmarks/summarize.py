"""Turn benchmark JSON files into a markdown report, a LaTeX table, and two figures.

Example:

    .venv/bin/python benchmarks/summarize.py --out-dir benchmarks/results/<run> \
        --corpus-new corpus_<label>.json [--corpus-old corpus_<old>.json] \
        [--examples-new examples_<label>.json --examples-old examples_<old>.json] \
        --scaling scaling_<label>.json [--scaling-long scaling_long_<label>.json]

Writes into --out-dir:
  summary.md            machine info, corpus table, corpus cost drivers, examples
                        regression table, scaling table, timeouts, figures
  execution-times.tex   the body of the paper's execution-time table, one row per
                        corpus program, with citation keys
  scaling_overview.png, .pdf   every scaling family on one chart (wall time vs plan-matrix cells)
  scaling_families.png, .pdf   small multiples, one panel per family against its own parameter

"wall" is the parent-measured end-to-end time of one `python program.py` run,
which is what the paper's table reports. "solve" is the time inside
Designer.eval (the z3 part). Medians are over the runs that completed.
Nothing here is meant to be edited by hand; change the JSON or this script.
"""
import argparse
import json
import math
import statistics
from pathlib import Path

# File -> experiment name used in the paper's execution-time table. The Shaping
# Compliance paper numbers its studies Exp 1 (grains x electrodes) and Exp 2 (shapes).
PAPER_NAMES = {
    "artist.py": "ARTiST (Exp 1)",
    "artist2.py": "ARTiST (Exp 2)",
    "dont_ask_just_tell.py": "Don't Just Tell Me, Ask Me",
    "mousering.py": "MouseRing (Exp 1)",
    "mousering2.py": "MouseRing (Exp 2)",
    "ok_google.py": "OK Google, Let's Learn",
    "perception.py": "Human Augmentation",
    "rambler.py": "Rambler",
    "recommender.py": "When Recommender Systems Snoop",
    "seated_wip.py": "Seated-WIP",
    "shaping_compliance.py": "Shaping Compliance (Exp 1)",
    "shaping_compliance2.py": "Shaping Compliance (Exp 2)",
    "silver.py": "Silver-Tongued and Sundry",
    "skinergy.py": "Skinergy",
    "sweating_details.py": "Sweating the Details",
}

# BibTeX keys of the paper repository, so execution-times.tex drops into the paper unchanged.
CITE_KEYS = {
    "artist.py": "WuARTiST2024",
    "artist2.py": "WuARTiST2024",
    "dont_ask_just_tell.py": "Danry2023Explainable",
    "mousering.py": "shen2024mousering",
    "mousering2.py": "shen2024mousering",
    "ok_google.py": "DesaiChin2023",
    "perception.py": "Villa2023Augmentation",
    "rambler.py": "Lin2024rambler",
    "recommender.py": "Sun2023Recommender",
    "seated_wip.py": "ChanSeatedWIP2024",
    "shaping_compliance.py": "jingu2024shaping",
    "shaping_compliance2.py": "jingu2024shaping",
    "silver.py": "Fuji2024GPT",
    "skinergy.py": "YuSkinergy2023",
    "sweating_details.py": "PottsSweatingDetails2024",
}

# Programs that approximate a design the expressivity evaluation marks as not
# expressible; they are timed, and the table says what was timed.
APPROXIMATIONS = {
    "shaping_compliance.py": "the closest expressible approximation of a design the expressivity evaluation marks as not expressible",
}

# Figure palette (validated for a light surface; the two weaker hues always get
# their own marker shape and a legend entry, never color alone).
PALETTE = {
    "blue": "#2a78d6",
    "orange": "#eb6834",
    "aqua": "#1baf7a",
    "yellow": "#eda100",
    "gray": "#8a8a86",
    "ink": "#333333",
    "muted": "#9a9a96",
    "grid": "#e6e6e3",
}

FAMILY_ORDER = ["latin_square", "full_counterbalance", "plans", "nested_latin_squares", "crossed_latin_squares", "trials", "nested_variable"]


# ---------------------------------------------------------------- corpus / examples


def load(path):
    if path is None:
        return None, {}
    with open(path) as fh:
        data = json.load(fh)
    meta = dict(data["meta"])
    for rec in data["records"]:
        if rec.get("python") and rec.get("z3"):
            meta["python_version"], meta["z3_version"] = rec["python"], rec["z3"]
            break
    return meta, aggregate(data["records"])


def median(values):
    return statistics.median(values) if values else None


def aggregate(records):
    """Per script: status summary and medians over completed runs."""
    by_script = {}
    for rec in records:
        by_script.setdefault(rec["script"], []).append(rec)
    agg = {}
    for script, recs in by_script.items():
        ok = [r for r in recs if r["status"] == "ok"]
        statuses = sorted({r["status"] for r in recs})
        row = {
            "runs": len(recs),
            "ok": len(ok),
            "status": statuses[0] if len(statuses) == 1 else "mixed:" + "/".join(statuses),
            "error": next((r.get("error", "") for r in recs if r["status"] != "ok"), ""),
            "plans": next((r.get("plans") for r in ok), None),
            "trials": next((r.get("trials") for r in ok), None),
            "participants": next((r.get("participants") for r in ok), None),
        }
        for phase in ("wall", "import", "solve", "plans", "assign", "analysis", "total"):
            vals = [r["wall"] if phase == "wall" else r["phases"].get(phase) for r in ok]
            vals = [v for v in vals if v is not None]
            row[phase + "_med"] = median(vals)
            row[phase + "_min"] = min(vals) if vals else None
            row[phase + "_max"] = max(vals) if vals else None
        agg[script] = row
    return agg


def fmt(x, digits=3):
    return "-" if x is None else f"{x:.{digits}f}"


def md_table(headers, rows):
    out = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    out += ["| " + " | ".join(str(c) for c in row) + " |" for row in rows]
    return "\n".join(out)


def machine_block(meta, title):
    if not meta:
        return ""
    keys = ["label", "commit", "cpu", "memory_gb", "platform", "python_version", "z3_version", "python",
            "reps", "timeout", "families", "bases", "rerun_of", "started", "finished"]
    lines = [f"**{title}**", ""]
    lines += [f"- {k}: `{meta[k]}`" for k in keys if k in meta]
    return "\n".join(lines) + "\n"


def flag(old, new):
    """Mark rows whose status changed or whose wall time moved more than 2x."""
    if old is None:
        return ""
    if old["status"] != new["status"]:
        return "status changed"
    if old["wall_med"] and new["wall_med"]:
        ratio = new["wall_med"] / old["wall_med"]
        if ratio > 2:
            return f"slower {ratio:.1f}x"
        if ratio < 0.5:
            return f"faster {1 / ratio:.1f}x"
    return ""


def comparison_table(old, new, with_names):
    headers = ["program"]
    if with_names:
        headers.append("paper name")
    headers += ["status", "plans x trials", "units", "runs"]
    if old:
        headers += ["wall old"]
    headers += ["wall new", "wall min..max"]
    if old:
        headers += ["solve old"]
    headers += ["solve new", "assign new", "analysis new", "note"]
    rows = []
    for script in sorted(new):
        n = new[script]
        o = old.get(script) if old else None
        name = Path(script).name
        row = [f"`{script}`"]
        if with_names:
            row.append(PAPER_NAMES.get(name, ""))
        status = n["status"] if o is None or o["status"] == n["status"] else f"{o['status']} -> {n['status']}"
        shape = f"{n['plans']} x {n['trials']}" if n["plans"] is not None else "-"
        row += [status, shape, n["participants"] if n["participants"] is not None else "-", f"{n['ok']}/{n['runs']}"]
        if old:
            row.append(fmt(o["wall_med"]) if o else "-")
        row += [fmt(n["wall_med"]), f"{fmt(n['wall_min'])}..{fmt(n['wall_max'])}" if n["wall_min"] is not None else "-"]
        if old:
            row.append(fmt(o["solve_med"]) if o else "-")
        row += [
            fmt(n["solve_med"]),
            fmt(n["assign_med"]),
            fmt(n["analysis_med"]),
            flag(o, n) or (n["error"][:60] if n["status"] != "ok" else ""),
        ]
        rows.append(row)
    return md_table(headers, rows)


def cost_section(new):
    """Corpus programs ordered by solver time, with the size of their plan matrix."""
    ok = [(s, r) for s, r in new.items() if r["status"] == "ok" and r["plans"] is not None]
    ok.sort(key=lambda sr: -(sr[1]["solve_med"] or 0))
    rows = []
    for script, r in ok:
        name = Path(script).name
        cells = r["plans"] * r["trials"]
        rows.append([f"`{name}`", PAPER_NAMES.get(name, ""), r["plans"], r["trials"], cells, fmt(r["solve_med"]), fmt(r["wall_med"])])
    text = [
        "Programs ordered by solver time. `cells` is plans x trials per participant, the size of",
        "the plan matrix the solver fills; it is an upper bound on the work, not a predictor on",
        "its own, since between-subjects programs have large matrices and no ordering",
        "constraints.",
        "",
        md_table(["program", "paper name", "plans", "trials/participant", "cells", "solve", "wall"], rows),
    ]
    return "\n".join(text)


BOLD_WALL_AT = 1.0  # seconds; corpus rows at or under this wall time are set in bold


def latex_table(new, meta):
    lines = [
        "% Generated by benchmarks/summarize.py; do not edit by hand.",
        f"% Median over {meta.get('reps')} runs of the end-to-end wall time of one `python program.py` run",
        f"% and of its z3 part (Designer.eval). Commit {meta.get('commit')}; {meta.get('cpu')}, {meta.get('memory_gb')} GB;",
        f"% Python {meta.get('python_version')}; z3 {meta.get('z3_version')}; {meta.get('started', '')[:10]}.",
        f"% Rows are in ascending order of median wall time; rows in bold have a median wall time of {BOLD_WALL_AT:g} s or less.",
        "% The row of a program that only approximates a design the expressivity evaluation marks as not",
        "% expressible is kept as a comment: the paper's table shows the expressible designs.",
        "\\begin{tabular}{lrrr}",
        "\\toprule",
        "\\textbf{Experiment} & \\textbf{Plans $\\times$ trials} & \\textbf{Wall (s)} & \\textbf{Solve (s)} \\\\",
        "\\midrule",
    ]
    # Ascending wall time; programs that did not complete go last, by name.
    def order(kv):
        script, row = kv
        name = PAPER_NAMES.get(Path(script).name, script).lower()
        if row["status"] != "ok":
            return (1, float("inf"), float("inf"), name)
        return (0, row["wall_med"], row["solve_med"], name)
    rows = sorted(new.items(), key=order)
    for script, row in rows:
        name = Path(script).name
        paper = PAPER_NAMES.get(name, name).replace("&", "\\&")
        mark = ""
        cite = f"~\\cite{{{CITE_KEYS[name]}}}" if name in CITE_KEYS else ""
        shape = f"${row['plans']} \\times {row['trials']}$" if row["plans"] is not None else "--"
        if row["status"] == "ok":
            wall, solve = fmt(row["wall_med"]), fmt(row["solve_med"])
        else:
            wall, solve = row["status"].replace("_", "\\_"), "--"
        if row["status"] == "ok" and row["wall_med"] <= BOLD_WALL_AT:
            # Bold the whole row; the citation keeps its own weight.
            paper, mark = f"\\textbf{{{paper}{mark}}}", ""
            wall, solve = f"\\textbf{{{wall}}}", f"\\textbf{{{solve}}}"
            shape = f"{{\\boldmath{shape}}}"
        line = f"{paper}{mark}{cite} & {shape} & {wall} & {solve} \\\\ % {name}"
        if name in APPROXIMATIONS:
            lines.append(f"% {line}: {APPROXIMATIONS[name]}; not shown")
        else:
            lines.append(line)
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- scaling


def load_scaling(path):
    """Per (family, x): status and medians over completed runs."""
    if path is None:
        return {}, {}
    with open(path) as fh:
        data = json.load(fh)
    meta = dict(data["meta"])
    meta["_file"] = Path(path).name
    by = {}
    for rec in data["records"]:
        if "x" not in rec:  # records written before families declared an axis
            rec["axis"] = "k" if rec["family"] == "trials" else "n"
            rec["x"] = rec["k"] if rec["axis"] == "k" else rec["n"]
            rec.setdefault("expected_plans", None)
            rec.setdefault("expected_width", rec.get("trials_total"))
        rec.setdefault("timeout", meta.get("timeout"))
        by.setdefault((rec["family"], rec["x"]), []).append(rec)
    points = {}
    for key, recs in sorted(by.items()):
        ok = [r for r in recs if r["status"] == "ok"]
        first = recs[0]
        pt = {k: first.get(k) for k in ("family", "axis", "x", "n", "k", "p", "m", "expected_plans", "expected_width", "trials_total", "script", "timeout")}
        pt.update({
            "runs": len(recs),
            "ok": len(ok),
            "status": "ok" if ok else ("timeout" if any(r["status"] == "timeout" for r in recs) else recs[0]["status"]),
            "error": next((r.get("error", "") for r in recs if r["status"] not in ("ok", "timeout")), ""),
            "plans": next((r.get("plans") for r in ok), None),
            "trials": next((r.get("trials") for r in ok), None),
        })
        for phase in ("wall", "import", "solve", "assign"):
            vals = [r["wall"] if phase == "wall" else r["phases"].get(phase) for r in ok]
            vals = [v for v in vals if v is not None]
            pt[phase + "_med"] = median(vals)
            pt[phase + "_min"] = min(vals) if vals else None
            pt[phase + "_max"] = max(vals) if vals else None
        points[key] = pt
    return meta, points


def family_points(points, family):
    return sorted((p for p in points.values() if p["family"] == family), key=lambda p: p["x"])


def families_in(points):
    seen = {p["family"] for p in points.values()}
    return [f for f in FAMILY_ORDER if f in seen] + sorted(f for f in seen if f not in FAMILY_ORDER)


def scaling_table(points):
    rows = []
    for fam in families_in(points):
        for p in family_points(points, fam):
            expected = f"{p['expected_plans']} x {p['expected_width']}" if p["expected_plans"] is not None else "-"
            measured = f"{p['plans']} x {p['trials']}" if p["plans"] is not None else "-"
            wall = fmt(p["wall_med"]) if p["status"] == "ok" else (f"> {p['timeout']:.0f}" if p["status"] == "timeout" else "-")
            spread = f"{fmt(p['wall_min'])}..{fmt(p['wall_max'])}" if p["wall_min"] is not None else "-"
            rows.append([
                fam, p["axis"], p["x"], p["n"], expected, measured, p["status"], f"{p['ok']}/{p['runs']}",
                wall, spread, fmt(p["solve_med"]), fmt(p["assign_med"]),
                p["error"][:60] if p["status"] not in ("ok", "timeout") else "",
            ])
    return md_table(["family", "axis", "x", "base n", "expected plans x width", "measured plans x trials", "status", "ok/runs",
                     "wall", "wall min..max", "solve", "assign", "error"], rows)


def timeouts_section(meta, points, long_meta, long_points):
    T = meta["timeout"]
    lines = ["### Timeouts", ""]
    lines.append(
        f"The sweep limit was {T:.0f} s per run. A family stops at its first timed-out point: the remaining "
        f"runs of that point and all larger values of its axis were not attempted, so a timeout is the last "
        f"row of its family above."
    )
    if long_meta:
        lines.append(
            f"The timed-out points were then re-run {long_meta.get('reps')} time(s) each with a limit of "
            f"{long_meta['timeout']:.0f} s (`{long_meta['_file']}`, started {long_meta.get('started')}). Those "
            f"runs are listed in the last column and drawn with hollow markers in the figure; they are not part "
            f"of the sweep medians."
        )
    else:
        lines.append("No longer re-run of the timed-out points was supplied (--scaling-long).")
    lines.append("")
    rows = []
    for fam in families_in(points):
        pts = family_points(points, fam)
        ok = [p for p in pts if p["status"] == "ok"]
        last = f"{ok[-1]['axis']} = {ok[-1]['x']}: {fmt(ok[-1]['wall_med'])} s" if ok else "-"
        to = [p for p in pts if p["status"] == "timeout"]
        if not to:
            rows.append([fam, last, "none", "-"])
            continue
        p = to[0]
        desc = f"{p['axis']} = {p['x']} ({p['expected_plans']} plans x {p['expected_width']} trials)"
        lp = long_points.get((fam, p["x"]))
        if lp is None:
            outcome = "not re-run"
        elif lp["status"] == "ok":
            outcome = f"completed: wall {fmt(lp['wall_med'])} s, solve {fmt(lp['solve_med'])} s ({lp['ok']} run(s))"
        elif lp["status"] == "timeout":
            outcome = f"still over {lp['timeout']:.0f} s"
        else:
            outcome = lp["status"]
        rows.append([fam, last, desc, outcome])
    long_label = f"re-run at {long_meta['timeout']:.0f} s" if long_meta else "re-run"
    lines.append(md_table(["family", "last completed point", f"first timeout in the sweep ({T:.0f} s)", long_label], rows))
    return "\n".join(lines)


def scaling_section(meta, points, long_meta, long_points, corpus, out_dir):
    reps = meta.get("reps")
    T = meta["timeout"]
    text = [machine_block(meta, "Scaling sweep")]
    if long_meta:
        text.append(machine_block(long_meta, "Re-run of the timed-out points"))
    text += [
        f"Each row is one generated program (in `{Path(meta['_file']).stem}_programs/`), run {reps} time(s) with a "
        f"limit of {T:.0f} s per run. `wall` and `solve` are medians over the completed runs, with the min and max "
        f"of `wall` alongside. Every family sweeps one parameter, its axis, of a design built on a Latin square and "
        f"keeps the rest fixed (`base n`). `expected` is the plan count and width (trials per participant) the "
        f"semantics predicts for the design; `measured` is the shape of the plan matrix the solver produced.",
        "",
        scaling_table(points),
        "",
        timeouts_section(meta, points, long_meta, long_points),
    ]
    if plot_overview(meta, points, out_dir):
        text += ["", "![wall time against plan-matrix cells, every family](scaling_overview.png)", "",
                 "Figure: every family on one chart, wall time against the cells of the plan matrix (plans × trials per "
                 "participant), log-log. Each curve ends with its parameter value; a cross on the 600 s line, joined to "
                 "the curve by a dashed segment, is the first point that did not finish; the dotted lines are the "
                 "interpreter start-up and import floor, Nielsen's 1 s and 10 s response-time limits, and the time limit. "
                 "Also written as `scaling_overview.pdf`."]
    if plot_families(meta, points, out_dir):
        text += ["", "![one panel per family against its own parameter](scaling_families.png)", "",
                 "Figure: the same data as small multiples, one panel per family against its own parameter, with a "
                 "shared log y-axis and the same reference lines. Also written as `scaling_families.pdf`."]
    return "\n".join(text)


# ---------------------------------------------------------------- figures

# One entry per family, in the order of the paper's list. `shape` is the plan
# matrix (plans x trials per participant) in the family's parameter; `xscale`
# is the x-axis scale of the family's panel in the small multiples.
FAMILY_INFO = [
    {"key": "latin_square",          "name": "Conditions with limit",            "shape": "n × n",    "param": "n", "xlabel": "conditions n",   "xscale": "linear", "color": "#2a78d6", "marker": "o"},
    {"key": "full_counterbalance",   "name": "Conditions with no limit",         "shape": "n! × n",   "param": "n", "xlabel": "conditions n",   "xscale": "linear", "color": "#eb6834", "marker": "s"},
    {"key": "plans",                 "name": "Plans with limit",                 "shape": "p × 5",    "param": "p", "xlabel": "plan limit p",   "xscale": "linear", "color": "#1baf7a", "marker": "D"},
    {"key": "nested_latin_squares",  "name": "Nesting two Latin squares",        "shape": "n² × n²",  "param": "n", "xlabel": "conditions n",   "xscale": "linear", "color": "#eda100", "marker": "^"},
    {"key": "crossed_latin_squares", "name": "Crossing two Latin squares",       "shape": "n² × n",   "param": "n", "xlabel": "conditions n",   "xscale": "linear", "color": "#e87ba4", "marker": "v"},
    {"key": "trials",                "name": "Repeated trials",                  "shape": "12 × 12k", "param": "k", "xlabel": "repetitions k",  "xscale": "log",    "color": "#008300", "marker": "P"},
    {"key": "nested_variable",       "name": "Nesting without counterbalancing", "shape": "12 × 12m", "param": "m", "xlabel": "options m",      "xscale": "log",    "color": "#6250d6", "marker": "X"},
]

# End-label placement in the overview, tuned by eye to the 2026-10-10 data:
# ((dx, dy) in points, ha, va), or ("leader", (x, y)) to put the text at data
# coordinates with a thin line back to the curve's end. Re-tune after a re-run
# that moves where a curve ends.
OVERVIEW_LABELS = {
    "latin_square":          ((-10, 13), "right",  "center"),
    "full_counterbalance":   ((0, -10),  "center", "top"),
    "plans":                 ((-9, 0),   "right",  "center"),
    "nested_latin_squares":  ((0, 10),   "center", "bottom"),
    "crossed_latin_squares": ((0, 8),    "center", "bottom"),
    "trials":                ((7, 0),    "left",   "center"),
    "nested_variable":       ("leader",  (1.2e5, 9)),
}
TWO_LINE_LABELS = {"crossed_latin_squares"}

REFERENCE_LINES = [(1.0, "1 s"), (10.0, "10 s")]  # Nielsen's response-time limits


def _mpl():
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
    except Exception:
        return None, None
    plt.rcParams.update({
        "font.family": "serif", "font.size": 7.5, "axes.titlesize": 8, "axes.labelsize": 7.5,
        "legend.fontsize": 7, "xtick.labelsize": 6.5, "ytick.labelsize": 6.5,
        "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": "#6b6b67",
        "xtick.color": "#6b6b67", "ytick.color": "#6b6b67", "axes.labelcolor": PALETTE["ink"],
    })
    return plt, Line2D


def _series(points, key):
    """Completed points of a family as (x, cells, wall) plus its first timeout, if any."""
    fp = family_points(points, key)
    done = [(p["x"], p["expected_plans"] * p["expected_width"], p["wall_med"]) for p in fp if p["status"] == "ok"]
    to = next((p for p in fp if p["status"] == "timeout"), None)
    timeout = (to["x"], to["expected_plans"] * to["expected_width"]) if to else None
    return done, timeout


def _floor(points):
    return median([p["import_med"] for p in points.values() if p.get("import_med")])


def _reference_lines(ax, floor, T, label=True, label_floor=True):
    for y, txt in [(floor, "interpreter + import floor")] + REFERENCE_LINES + [(T, f"{T:.0f} s limit")]:
        ax.axhline(y, color=PALETTE["muted"], linestyle=(0, (1, 2)), linewidth=0.8, zorder=1)
        if label and (label_floor or y != floor):
            va = "top" if y == floor else "bottom"
            ax.text(0.012 if y == floor else 0.005, y * (0.93 if va == "top" else 1.0), txt, transform=ax.get_yaxis_transform(),
                    ha="left", va=va, fontsize=6.5, color=PALETTE["muted"])


def plot_overview(meta, points, out_dir):
    """Every family on one log-log chart of wall time against plan-matrix cells."""
    plt, Line2D = _mpl()
    if plt is None:
        return None
    T, floor, INK = meta["timeout"], _floor(points), PALETTE["ink"]
    fig, ax = plt.subplots(figsize=(7.4, 5.3))
    ax.set_xscale("log"); ax.set_yscale("log")
    for f in FAMILY_INFO:
        done, timeout = _series(points, f["key"])
        if not done:
            continue
        c, mk = f["color"], f["marker"]
        xs, ys = [d[1] for d in done], [d[2] for d in done]
        ax.plot(xs, ys, marker=mk, color=c, markersize=4.5, linewidth=1.6, zorder=3, label=f'{f["name"]} ({f["shape"]})')
        end_x, end_y, end_param = xs[-1], ys[-1], done[-1][0]
        if timeout:
            ax.plot([xs[-1], timeout[1]], [ys[-1], T], color=c, linewidth=1.2, linestyle=(0, (3, 2)), zorder=2)
            ax.plot([timeout[1]], [T], marker="x", color=c, markersize=7, markeredgewidth=1.8, linestyle="none", zorder=4)
            end_x, end_y, end_param = timeout[1], T, timeout[0]
        sep = "\n" if f["key"] in TWO_LINE_LABELS else " "
        text = f'{f["name"]}{sep}({f["param"]} = {end_param})'
        place = OVERVIEW_LABELS.get(f["key"], ((7, 0), "left", "center"))
        if place[0] == "leader":
            ax.annotate(text, (end_x, end_y), xytext=place[1], textcoords="data", ha="center", va="center", fontsize=7.5, color=INK,
                        arrowprops=dict(arrowstyle="-", color=PALETTE["muted"], linewidth=0.8, shrinkA=0, shrinkB=4), zorder=6)
        else:
            (dx, dy), ha, va = place
            ax.annotate(text, (end_x, end_y), textcoords="offset points", xytext=(dx, dy), ha=ha, va=va, fontsize=7.5, color=INK, zorder=6)
    _reference_lines(ax, floor, T)
    ax.set_xlim(2.5, 1.0e6); ax.set_ylim(0.15, 2.0e3)
    ax.set_xlabel("cells of the plan matrix (plans × trials per participant)")
    ax.set_ylabel("wall time (s)")
    ax.tick_params(length=3)
    ax.grid(True, which="major", color=PALETTE["grid"], linewidth=0.6); ax.grid(False, which="minor")
    handles, labels = ax.get_legend_handles_labels()
    handles.append(Line2D([], [], marker="x", color=PALETTE["muted"], markeredgewidth=1.8, linestyle="none", markersize=7))
    labels.append(f"did not finish within {T:.0f} s")
    fig.legend(handles, labels, loc="lower center", ncol=2, frameon=False, columnspacing=2.0, handlelength=2.2, bbox_to_anchor=(0.53, 0.0))
    fig.tight_layout(rect=(0, 0.115, 1, 1), h_pad=0.2)
    fig.savefig(out_dir / "scaling_overview.png", dpi=200)
    fig.savefig(out_dir / "scaling_overview.pdf")
    plt.close(fig)
    return out_dir / "scaling_overview.png"


def plot_families(meta, points, out_dir):
    """Small multiples: one panel per family against its own parameter, shared log y-axis."""
    plt, Line2D = _mpl()
    if plt is None:
        return None
    T, floor = meta["timeout"], _floor(points)
    fams = [f for f in FAMILY_INFO if _series(points, f["key"])[0]]
    ncol = 4
    nrow = math.ceil((len(fams) + 1) / ncol)
    fig, axes = plt.subplots(nrow, ncol, figsize=(7.4, 2.3 * nrow), sharey=True)
    axes = list(axes.flat)
    for ax, f in zip(axes, fams):
        done, timeout = _series(points, f["key"])
        c, mk = f["color"], f["marker"]
        xs, ys = [d[0] for d in done], [d[2] for d in done]
        ax.set_yscale("log"); ax.set_xscale(f["xscale"])
        ax.plot(xs, ys, marker=mk, color=c, markersize=4, linewidth=1.5, zorder=3)
        if timeout:
            ax.plot([xs[-1], timeout[0]], [ys[-1], T], color=c, linewidth=1.1, linestyle=(0, (3, 2)), zorder=2)
            ax.plot([timeout[0]], [T], marker="x", color=c, markersize=6.5, markeredgewidth=1.7, linestyle="none", zorder=4)
        _reference_lines(ax, floor, T, label=(axes.index(ax) % ncol == 0), label_floor=False)
        name = f["name"] if len(f["name"]) <= 28 else f["name"].replace(" without ", " without\n")
        ax.set_title(f'{name}\n', fontsize=7.5, color=PALETTE["ink"], pad=2)
        ax.text(0.5, 1.02, f'{f["shape"]} plans × trials', transform=ax.transAxes, ha="center", va="bottom", fontsize=6.5, color=PALETTE["muted"])
        ax.set_xlabel(f["xlabel"])
        if f["xscale"] == "linear":
            ax.set_xticks(xs + ([timeout[0]] if timeout and timeout[0] not in xs else []))
            if len(ax.get_xticks()) > 7:
                ax.set_xticks([x for x in ax.get_xticks() if x % 2 == 0 or x == ax.get_xticks()[0]])
        ax.tick_params(length=3)
        ax.grid(True, which="major", color=PALETTE["grid"], linewidth=0.6); ax.grid(False, which="minor")
        ax.set_ylim(0.15, 2.0e3)
    for ax in axes[:nrow * ncol:ncol]:
        ax.set_ylabel("wall time (s)")
    # the spare cell explains the conventions
    spare = axes[len(fams)]
    spare.axis("off")
    handles = [Line2D([], [], marker="x", color=PALETTE["muted"], markeredgewidth=1.7, linestyle="none", markersize=6.5),
               Line2D([], [], color=PALETTE["muted"], linewidth=1.1, linestyle=(0, (3, 2))),
               Line2D([], [], color=PALETTE["muted"], linewidth=0.8, linestyle=(0, (1, 2)))]
    labels = [f"did not finish within {T:.0f} s", "jump from the last completed point", "floor, 1 s, 10 s, 600 s"]
    spare.legend(handles, labels, loc="center left", frameon=False, fontsize=7, handlelength=2.4)
    for ax in axes[len(fams) + 1:]:
        ax.axis("off")
    fig.tight_layout(w_pad=0.6, h_pad=1.2)
    fig.savefig(out_dir / "scaling_families.png", dpi=200)
    fig.savefig(out_dir / "scaling_families.pdf")
    plt.close(fig)
    return out_dir / "scaling_families.png"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--corpus-new", required=True)
    ap.add_argument("--corpus-old")
    ap.add_argument("--examples-new")
    ap.add_argument("--examples-old")
    ap.add_argument("--scaling")
    ap.add_argument("--scaling-long", help="re-run of the timed-out points of --scaling under a longer limit")
    args = ap.parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    new_meta, new = load(args.corpus_new)
    old_meta, old = load(args.corpus_old)

    parts = ["# PLanet performance evaluation", ""]
    parts.append(machine_block(new_meta, "Version measured" if not old_meta else "New version"))
    if old_meta:
        parts.append(machine_block(old_meta, "Old version"))
    parts += [
        "Times in seconds. `wall` is the end-to-end time of one `python program.py` run (the",
        "paper's quantity); `solve` is the z3 part (`Designer.eval`); `assign` includes solving,",
        "random-variable instantiation and participant assignment; `analysis` is `Analysis(...)`",
        f"where the program calls it. Medians over the completed runs ({new_meta.get('reps')} per program,",
        f"{new_meta.get('timeout', 0):.0f} s limit each), with the min and max of `wall` alongside.",
        "Note marks rows whose status changed between versions or whose wall time moved more than 2x.",
        "",
        "## Corpus (`src/eval_examples`)",
        "",
        comparison_table(old, new, with_names=True),
        "",
    ]
    ok_new = [r for r in new.values() if r["status"] == "ok"]
    if ok_new:
        under1 = sum(1 for r in ok_new if r["wall_med"] < 1)
        slowest = max(ok_new, key=lambda r: r["wall_med"])
        parts += [
            f"- {len(ok_new)} of {len(new)} programs completed; {under1} of them under 1 s; slowest {fmt(slowest['wall_med'])} s.",
            "",
            "### Cost drivers",
            "",
            cost_section(new),
            "",
        ]

    if args.examples_new:
        ex_new_meta, ex_new = load(args.examples_new)
        _, ex_old = load(args.examples_old)
        parts += ["## All examples (`src/examples`), regression sweep", "", comparison_table(ex_old, ex_new, with_names=False), ""]
        changed = [s for s in ex_new if ex_old and s in ex_old and ex_old[s]["status"] != ex_new[s]["status"]]
        failing = [s for s in ex_new if ex_new[s]["status"] != "ok"]
        parts += [f"- status changed: {', '.join(f'`{s}`' for s in changed) or 'none'}",
                  f"- not completing on the new version: {', '.join(f'`{s}`' for s in failing) or 'none'}", ""]

    if args.scaling:
        meta, points = load_scaling(args.scaling)
        long_meta, long_points = load_scaling(args.scaling_long)
        parts += ["## Scaling", "", scaling_section(meta, points, long_meta, long_points, new, out_dir), ""]

    (out_dir / "summary.md").write_text("\n".join(parts))
    (out_dir / "execution-times.tex").write_text(latex_table(new, new_meta))
    print(f"wrote {out_dir / 'summary.md'} and {out_dir / 'execution-times.tex'}")


if __name__ == "__main__":
    main()
