"""Turn benchmark JSON files into a markdown report, a LaTeX table, and a figure.

Example:

    .venv/bin/python benchmarks/summarize.py --out-dir benchmarks/results/<run> \
        --corpus-new corpus_<label>.json [--corpus-old corpus_<old>.json] \
        [--examples-new examples_<label>.json --examples-old examples_<old>.json] \
        --scaling scaling_<label>.json [--scaling-long scaling_long_<label>.json]

Writes into --out-dir:
  summary.md            machine info, corpus table, corpus cost drivers, examples
                        regression table, scaling table, timeouts, figure
  execution-times.tex   the body of the paper's execution-time table, one row per
                        corpus program, with citation keys
  scaling.png, .pdf     the paper's scaling figure, four panels

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


def latex_table(new, meta):
    lines = [
        "% Generated by benchmarks/summarize.py; do not edit by hand.",
        f"% Median over {meta.get('reps')} runs of the end-to-end wall time of one `python program.py` run",
        f"% and of its z3 part (Designer.eval). Commit {meta.get('commit')}; {meta.get('cpu')}, {meta.get('memory_gb')} GB;",
        f"% Python {meta.get('python_version')}; z3 {meta.get('z3_version')}; {meta.get('started', '')[:10]}.",
        "\\begin{tabular}{lrrr}",
        "\\toprule",
        "\\textbf{Experiment} & \\textbf{Plans $\\times$ trials} & \\textbf{Wall (s)} & \\textbf{Solve (s)} \\\\",
        "\\midrule",
    ]
    notes = []
    rows = sorted(new.items(), key=lambda kv: PAPER_NAMES.get(Path(kv[0]).name, kv[0]).lower())
    for script, row in rows:
        name = Path(script).name
        paper = PAPER_NAMES.get(name, name).replace("&", "\\&")
        mark = ""
        if name in APPROXIMATIONS:
            notes.append(APPROXIMATIONS[name])
            mark = "$^\\dagger$"
        cite = f"~\\cite{{{CITE_KEYS[name]}}}" if name in CITE_KEYS else ""
        shape = f"${row['plans']} \\times {row['trials']}$" if row["plans"] is not None else "--"
        if row["status"] == "ok":
            wall, solve = fmt(row["wall_med"]), fmt(row["solve_med"])
        else:
            wall, solve = row["status"].replace("_", "\\_"), "--"
        lines.append(f"{paper}{mark}{cite} & {shape} & {wall} & {solve} \\\\ % {name}")
    lines.append("\\bottomrule")
    for note in notes:
        lines.append(f"\\multicolumn{{4}}{{l}}{{\\footnotesize $^\\dagger$ {note[0].upper() + note[1:]}.}} \\\\")
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
    plot_path = plot_scaling(meta, points, long_meta, long_points, corpus, out_dir)
    if plot_path:
        text += ["", "![runtime vs design size](scaling.png)", "",
                 "Figure: wall time against each family's axis, log scale. Filled markers are sweep medians with "
                 "a thin bar from min to max; a cross at a dotted limit line is a timeout at that limit; a hollow "
                 "marker is the re-run of a timed-out point at the longer limit, joined to the sweep by a dashed "
                 "segment; the lowest dotted line is the interpreter start-up and import floor. "
                 "Also written as `scaling.pdf` for the paper."]
    return "\n".join(text)


def plot_scaling(meta, points, long_meta, long_points, corpus, out_dir):
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
        from matplotlib.ticker import NullFormatter, ScalarFormatter
    except Exception:
        return None
    plt.rcParams.update({
        "font.family": "serif", "font.size": 7.5, "axes.titlesize": 8, "axes.labelsize": 7.5,
        "legend.fontsize": 6.2, "xtick.labelsize": 6.5, "ytick.labelsize": 6.5,
        "axes.spines.top": False, "axes.spines.right": False, "axes.edgecolor": "#6b6b67",
        "xtick.color": "#6b6b67", "ytick.color": "#6b6b67", "axes.labelcolor": PALETTE["ink"],
    })
    T = meta["timeout"]
    T_long = long_meta.get("timeout") if long_meta else None
    floor = median([p["import_med"] for p in points.values() if p.get("import_med")])
    bases = meta.get("bases", {})
    plans_n = bases.get("plans", {}).get("n")
    base_n = bases.get("trials", {}).get("n") or bases.get("nested_variable", {}).get("n")

    panels = [
        ("(a) Number of conditions", "number of conditions n", "x", [
            ("latin_square", "Latin square: n plans × n trials", "blue", "o"),
            ("full_counterbalance", "full counterbalancing: n! plans × n trials", "orange", "s"),
        ]),
        (f"(b) Number of plans, n = {plans_n}", "plan limit p", "x", [
            ("plans", "limit_plans(p): p plans × n trials", "aqua", "^"),
        ]),
        ("(c) Composition", "number of conditions n", "x", [
            ("nested_latin_squares", "nest: n² plans × n² trials", "blue", "o"),
            ("crossed_latin_squares", "cross: n² plans × n trials", "orange", "s"),
            ("latin_square", "one Latin square, for reference", "gray", "."),
        ]),
        (f"(d) Trials per participant, n = {base_n}", "trials per participant", "trials_total", [
            ("trials", "repetition (k)", "blue", "o"),
            ("nested_variable", "nested variable (m)", "orange", "s"),
        ]),
    ]

    fig, axes = plt.subplots(2, 2, figsize=(6.4, 5.0))
    used_long = False
    for ax, (title, xlabel, xkey, lines) in zip(axes.flat, panels):
        for fam, label, color, marker in lines:
            pts = family_points(points, fam)
            if not pts:
                continue
            c = PALETTE[color]
            ok = [p for p in pts if p["status"] == "ok"]
            ms = 3.0 if marker == "." else 3.6
            ax.plot([p[xkey] for p in ok], [p["wall_med"] for p in ok], marker=marker, color=c, label=label,
                    linewidth=1.1, markersize=ms, zorder=3)
            for p in ok:
                if p["wall_min"] is not None and p["wall_max"] > p["wall_min"]:
                    ax.plot([p[xkey]] * 2, [p["wall_min"], p["wall_max"]], color=c, linewidth=0.7, alpha=0.7, zorder=2)
            for p in pts:
                if p["status"] == "timeout":
                    ax.plot([p[xkey]], [p["timeout"]], marker="x", color=c, markersize=5.5, markeredgewidth=1.2, linestyle="none", zorder=4)
                    lp = long_points.get((fam, p["x"]))
                    if lp is None:
                        continue
                    used_long = True
                    if lp["status"] == "ok":
                        ax.plot([p[xkey]], [lp["wall_med"]], marker=marker, color=c, markersize=4.6, linestyle="none",
                                fillstyle="none", markeredgewidth=1.2, zorder=4)
                        if ok:
                            ax.plot([ok[-1][xkey], p[xkey]], [ok[-1]["wall_med"], lp["wall_med"]], color=c,
                                    linestyle=(0, (2, 2)), linewidth=1.0, zorder=2)
                    elif lp["status"] == "timeout" and T_long:
                        ax.plot([p[xkey]], [T_long], marker="x", color=c, markersize=5.5, markeredgewidth=1.2, linestyle="none", zorder=4)
                elif p["status"] != "ok":
                    ax.plot([p[xkey]], [p["timeout"]], marker="s", color=c, markersize=5, linestyle="none", fillstyle="none", zorder=4)

        if lines[0][0] == "plans" and plans_n:
            # The same design with no limit at all: full_counterbalance at the base n, drawn at
            # p = n! with the figure's usual marks (cross = timeout, hollow = re-run).
            x = math.factorial(plans_n)
            fc = points.get(("full_counterbalance", plans_n))
            lfc = long_points.get(("full_counterbalance", plans_n))
            c = PALETTE["orange"]
            if fc is not None:
                proxy = dict(marker="D", color=c, markersize=4.2, linestyle="none", fillstyle="none", markeredgewidth=1.2)
                if fc["status"] == "ok":
                    ax.plot([x], [fc["wall_med"]], marker="D", color=c, markersize=4.2, linestyle="none", zorder=5, label="no limit: n! plans")
                elif fc["status"] == "timeout":
                    ax.plot([x], [fc["timeout"]], marker="x", color=c, markersize=5.5, markeredgewidth=1.2, linestyle="none", zorder=5)
                    if lfc is not None and lfc["status"] == "ok":
                        ax.plot([x], [lfc["wall_med"]], zorder=5, label="no limit: n! plans", **proxy)
                        used_long = True
                    elif lfc is not None and T_long:
                        ax.plot([x], [T_long], marker="x", color=c, markersize=5.5, markeredgewidth=1.2, linestyle="none", zorder=5, label="no limit: n! plans")
                        used_long = True
                    else:
                        ax.plot([], [], label="no limit: n! plans", **proxy)

        if xkey == "trials_total" and corpus and base_n:
            mr = next((r for s, r in corpus.items() if s.endswith("mousering.py") and r["status"] == "ok"), None)
            if mr and mr["plans"] == base_n:
                ax.plot([mr["trials"]], [mr["wall_med"]], marker="*", color=PALETTE["ink"], markersize=7, linestyle="none",
                        label="MouseRing Exp 1", zorder=6)

        # Reference lines, labeled at the left where the data sits on the floor and
        # the timeouts sit at the right.
        top = T * 4
        if T_long and used_long:
            top = T_long * 4
        lo = floor / 2.5
        ax.set_yscale("log")
        ax.set_ylim(lo, top)
        ax.axhline(floor, color=PALETTE["muted"], linestyle=(0, (1, 2)), linewidth=0.8, zorder=1)
        ax.text(0.01, floor * 0.88, "interpreter + import", transform=ax.get_yaxis_transform(), ha="left", va="top",
                fontsize=5.5, color=PALETTE["muted"])
        ax.axhline(T, color=PALETTE["muted"], linestyle=(0, (1, 2)), linewidth=0.8, zorder=1)
        ax.text(0.01, T * 1.15, f"{T:.0f} s limit", transform=ax.get_yaxis_transform(), ha="left", va="bottom",
                fontsize=5.5, color=PALETTE["muted"])
        if T_long and used_long:
            ax.axhline(T_long, color=PALETTE["muted"], linestyle=(0, (1, 2)), linewidth=0.8, zorder=1)
            ax.text(0.01, T_long * 1.15, f"{T_long:.0f} s limit", transform=ax.get_yaxis_transform(), ha="left", va="bottom",
                    fontsize=5.5, color=PALETTE["muted"])
        if xkey == "trials_total":
            ax.set_xscale("log")
            ax.xaxis.set_major_formatter(ScalarFormatter())
            ax.xaxis.set_minor_formatter(NullFormatter())
            xs = sorted({p[xkey] for p in points.values() if p["family"] in [l[0] for l in lines]})
            if xs:
                decades = [10 ** e for e in range(int(math.floor(math.log10(xs[0]))), int(math.ceil(math.log10(xs[-1]))) + 1)]
                ticks = sorted({xs[0], *[d for d in decades if xs[0] <= d <= xs[-1]], xs[-1]})
                ax.set_xticks(ticks)
                ax.set_xticklabels([str(t) for t in ticks])
        else:
            xs = sorted({p[xkey] for p in points.values() if p["family"] in [l[0] for l in lines]})
            if 0 < len(xs) <= 14:
                ax.set_xticks(xs)
        ax.set_xlabel(xlabel)
        ax.set_ylabel("wall time (s)")
        ax.set_title(title, loc="left", color=PALETTE["ink"])
        ax.grid(True, which="major", axis="y", color=PALETTE["grid"], linewidth=0.6)
        ax.set_axisbelow(True)
        # Legend in the empty region of each panel: the middle-left below the limit line
        # for the n and p axes (data rises to the right), the lower right for the width
        # panel (its lines start above the floor and rise to the upper right).
        if xkey == "trials_total":
            ax.legend(loc="lower right", frameon=False, handlelength=1.8, borderaxespad=0.3)
        else:
            frac = (math.log(T) - math.log(lo)) / (math.log(top) - math.log(lo))
            ax.legend(loc="upper left", bbox_to_anchor=(0.0, frac - 0.03), frameon=False, handlelength=2.2, borderaxespad=0.2)

    handles = [
        Line2D([], [], marker="o", color=PALETTE["ink"], linestyle="none", markersize=3.6, label="median of the sweep runs (bar: min to max)"),
        Line2D([], [], marker="x", color=PALETTE["ink"], linestyle="none", markersize=5.5, markeredgewidth=1.2, label="timed out at the dotted limit"),
    ]
    if T_long and used_long:
        handles.append(Line2D([], [], marker="o", color=PALETTE["ink"], linestyle="none", markersize=4.6, fillstyle="none",
                              markeredgewidth=1.2, label=f"re-run once with a {T_long:.0f} s limit"))
    fig.legend(handles=handles, loc="lower center", ncol=len(handles), frameon=False, fontsize=6.2, bbox_to_anchor=(0.5, 0.0))
    fig.tight_layout(rect=(0, 0.04, 1, 1), h_pad=1.4, w_pad=1.2)
    out_dir = Path(out_dir)
    fig.savefig(out_dir / "scaling.png", dpi=200)
    fig.savefig(out_dir / "scaling.pdf")
    return out_dir / "scaling.png"


# ---------------------------------------------------------------- main


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
