"""Turn benchmark JSON files into a markdown report, a LaTeX table, and a plot.

Example:

    .venv/bin/python benchmarks/summarize.py --out-dir benchmarks/results/<run> \
        --corpus-new corpus_1369473.json --corpus-old corpus_1183212.json \
        --examples-new examples_1369473.json --examples-old examples_1183212.json \
        --scaling scaling_1369473.json

Writes into --out-dir:
  summary.md            machine info, corpus table (old vs new), examples table, scaling table
  execution-times.tex   one row per corpus program, median wall time of the new version,
                        in the shape of the paper's execution-time table
  scaling.png           runtime vs. number of conditions, one line per family

"wall" is the parent-measured end-to-end time of one `python program.py` run,
which is what the paper's table reports. "solve" is the time inside
Designer.eval (the z3 part). Medians are over the runs that completed.
"""
import argparse
import json
import statistics
from pathlib import Path

# File -> experiment name used in the paper's execution-time table. Names with
# "?" could not be mapped unambiguously from the repository alone.
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
    "shaping_compliance.py": "Shaping Compliance (multifact, nested; Exp ?)",
    "shaping_compliance2.py": "Shaping Compliance (shape; Exp ?)",
    "silver.py": "Silver-Tongued and Sundry",
    "skinergy.py": "Skinergy",
    "sweating_details.py": "Sweating the Details",
}


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
    keys = ["label", "commit", "cpu", "memory_gb", "platform", "python_version", "z3_version", "python", "reps", "timeout", "started", "finished"]
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
    headers += ["status", "plans x trials", "units", "wall old", "wall new", "solve old", "solve new", "assign new", "analysis new", "note"]
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
        row += [
            status,
            shape,
            n["participants"] if n["participants"] is not None else "-",
            fmt(o["wall_med"]) if o else "-",
            fmt(n["wall_med"]),
            fmt(o["solve_med"]) if o else "-",
            fmt(n["solve_med"]),
            fmt(n["assign_med"]),
            fmt(n["analysis_med"]),
            flag(o, n) or (n["error"][:60] if n["status"] != "ok" else ""),
        ]
        rows.append(row)
    return md_table(headers, rows)


def latex_table(new, meta):
    lines = [
        "% Generated by benchmarks/summarize.py. Median end-to-end wall time (s) of",
        f"% one `python program.py` run over {meta.get('reps')} runs; commit {meta.get('commit')};",
        f"% {meta.get('cpu')}, {meta.get('memory_gb')} GB; Python {meta.get('python_version')}; z3 {meta.get('z3_version')}; {meta.get('started', '')[:10]}.",
        "\\begin{tabular}{llr}",
        "\\toprule",
        "Experiment & Program & Time (s) \\\\",
        "\\midrule",
    ]
    for script in sorted(new):
        name = Path(script).name
        row = new[script]
        time_s = fmt(row["wall_med"]) if row["status"] == "ok" else row["status"].replace("_", "\\_")
        paper = PAPER_NAMES.get(name, "").replace("&", "\\&")
        tex_name = name.replace("_", "\\_")
        lines.append(f"{paper} & \\texttt{{{tex_name}}} & {time_s} \\\\")
    lines += ["\\bottomrule", "\\end{tabular}"]
    return "\n".join(lines) + "\n"


def scaling_section(path, out_dir):
    with open(path) as fh:
        data = json.load(fh)
    meta, records = data["meta"], data["records"]
    rows = []
    for r in records:
        rows.append([
            r["family"], r["n"], r["k"], r["trials_total"], r["status"],
            r.get("plans") if r.get("plans") is not None else "-",
            fmt(r["wall"]) if r["status"] != "timeout" else f"> {meta['timeout']:.0f}",
            fmt(r["phases"].get("solve")),
            fmt(r["phases"].get("assign")),
            r.get("error", "")[:60] if r["status"] not in ("ok", "timeout") else "",
        ])
    table = md_table(["family", "n", "k", "trials", "status", "plans", "wall", "solve", "assign", "error"], rows)

    timeouts = {}
    for r in records:
        if r["status"] == "timeout":
            timeouts.setdefault(r["family"], r["n"])
    notes = [f"- `{fam}` first times out at n = {n} ({meta['timeout']:.0f} s limit)" for fam, n in timeouts.items()]
    if not notes:
        notes = ["- no family timed out"]

    plot_path = plot_scaling(records, meta, out_dir)
    text = machine_block(meta, "Scaling run") + "\n" + table + "\n\n" + "\n".join(notes)
    if plot_path:
        text += f"\n\n![runtime vs conditions]({plot_path.name})"
    return text


def plot_scaling(records, meta, out_dir):
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except Exception:
        return None
    families = [f for f in dict.fromkeys(r["family"] for r in records) if f != "trials"]
    has_trials = any(r["family"] == "trials" for r in records)
    fig, axes = plt.subplots(1, 2 if has_trials else 1, figsize=(10 if has_trials else 6, 4), squeeze=False)
    ax = axes[0][0]
    for fam in families:
        pts = [r for r in records if r["family"] == fam]
        xs = [r["n"] for r in pts if r["status"] == "ok"]
        ys = [r["wall"] for r in pts if r["status"] == "ok"]
        line, = ax.plot(xs, ys, marker="o", label=fam)
        for r in pts:
            if r["status"] == "timeout":
                ax.plot([r["n"]], [meta["timeout"]], marker="x", color=line.get_color(), markersize=10, linestyle="none")
                ax.annotate("timeout", (r["n"], meta["timeout"]), textcoords="offset points", xytext=(4, -10), fontsize=8)
            elif r["status"] != "ok":
                ax.plot([r["n"]], [r["wall"]], marker="s", color=line.get_color(), markersize=7, linestyle="none", fillstyle="none")
    ax.set_yscale("log")
    ax.set_xticks(sorted({r["n"] for r in records if r["family"] != "trials"}))
    ax.set_xlabel("number of conditions n")
    ax.set_ylabel("wall time (s)")
    ax.set_title("runtime vs. conditions")
    ax.axhline(meta["timeout"], color="grey", linestyle=":", linewidth=1)
    ax.legend(fontsize=8)
    ax.grid(True, which="both", alpha=0.3)
    if has_trials:
        ax2 = axes[0][1]
        pts = [r for r in records if r["family"] == "trials"]
        ax2.plot([r["trials_total"] for r in pts if r["status"] == "ok"], [r["wall"] for r in pts if r["status"] == "ok"], marker="o")
        for r in pts:
            if r["status"] == "timeout":
                ax2.plot([r["trials_total"]], [meta["timeout"]], marker="x", color="C0", markersize=10, linestyle="none")
        ax2.set_ylim(bottom=0)
        ax2.set_xticks([r["trials_total"] for r in pts])
        ax2.set_xlabel(f"trials per participant (n = {meta.get('trials_n')})")
        ax2.set_ylabel("wall time (s)")
        ax2.set_title("runtime vs. trials")
        ax2.grid(True, which="both", alpha=0.3)
    fig.suptitle(f"PLanet {meta.get('label')} on {meta.get('cpu')}", fontsize=9)
    fig.tight_layout()
    path = Path(out_dir) / "scaling.png"
    fig.savefig(path, dpi=150)
    return path


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--corpus-new", required=True)
    ap.add_argument("--corpus-old")
    ap.add_argument("--examples-new")
    ap.add_argument("--examples-old")
    ap.add_argument("--scaling")
    args = ap.parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    new_meta, new = load(args.corpus_new)
    old_meta, old = load(args.corpus_old)

    parts = ["# PLanet performance evaluation", ""]
    parts.append(machine_block(new_meta, "New version"))
    if old_meta:
        parts.append(machine_block(old_meta, "Old version"))
    parts += [
        "Times in seconds. `wall` is the end-to-end time of one `python program.py` run (the",
        "paper's quantity); `solve` is the z3 part (`Designer.eval`); `assign` includes solving,",
        "random-variable instantiation and participant assignment; `analysis` is `Analysis(...)`",
        "where the program calls it. Medians over completed runs. Note marks rows whose status",
        "changed between versions or whose wall time moved more than 2x.",
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
        parts += ["## Scaling", "", scaling_section(args.scaling, out_dir), ""]

    (out_dir / "summary.md").write_text("\n".join(parts))
    (out_dir / "execution-times.tex").write_text(latex_table(new, new_meta))
    print(f"wrote {out_dir / 'summary.md'} and {out_dir / 'execution-times.tex'}")


if __name__ == "__main__":
    main()
