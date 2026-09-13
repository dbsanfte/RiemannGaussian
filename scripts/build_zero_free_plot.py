#!/usr/bin/env python3
"""Draw the checked zero-free formulas; reject stale figures with --check.

Run ExportZeroFreePlot.lean first. This program only evaluates its expression
trees: it neither proves nonvanishing nor certifies numerical crossovers.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import math
from pathlib import Path
import xml.etree.ElementTree as ET

import matplotlib
matplotlib.use("Agg")
from matplotlib import pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, NullLocator
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "docs/zero-free-regions"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def evaluate(tree, log_height):
    """Real expression interpreter, with stable log(exp(x) +/- c) evaluation.

    The exponentially small correction can round away in binary64, which is
    appropriate for drawing pixels, never for deciding a theorem's endpoint.
    """
    op, *args = tree
    if op == "variable":
        return log_height
    if op == "natural":
        return float(args[0])
    if op == "log":
        term = args[0]
        if term[0] in ("add", "sub") and term[1][0] == "exp":
            x = evaluate(term[1][1], log_height)
            c = evaluate(term[2], log_height)
            sign = 1 if term[0] == "add" else -1
            return x + math.log1p(sign * c * math.exp(-x))
        return math.log(evaluate(term, log_height))
    if op == "exp":
        return math.exp(evaluate(args[0], log_height))
    a, b = (evaluate(arg, log_height) for arg in args)
    if op == "add":
        return a + b
    if op == "sub":
        return a - b
    if op == "mul":
        return a * b
    if op == "div":
        return a / b
    if op == "power":
        return a ** b
    if op == "minimum":
        return min(a, b)
    if op == "maximum":
        return max(a, b)
    raise ValueError(f"Unknown Lean formula operation: {op}")


def crossover(comparison):
    """Illustrative bisection inside Lean's exact rational enclosure."""
    left, right = comparison["bracket"]
    gap = comparison["gap"]
    assert evaluate(gap, left) < 0 < evaluate(gap, right)
    for _ in range(80):
        middle = (left + right) / 2
        if middle == left or middle == right:
            break
        if evaluate(gap, middle) < 0:
            left = middle
        else:
            right = middle
    return (left + right) / 2


def latex(tree):
    """Format the exact endpoint expression from the same exported tree."""
    op, *args = tree
    if op == "natural":
        return str(args[0])
    if op == "variable":
        return "L"
    if op == "exp":
        return "e^{" + latex(args[0]) + "}"
    if op == "log":
        return r"\log(" + latex(args[0]) + ")"
    if op in ("add", "sub"):
        return latex(args[0]) + ("+" if op == "add" else "-") + latex(args[1])
    raise ValueError(f"Unsupported endpoint display: {op}")


def load_inputs():
    formulas_path = ROOT / ".lake/zero-free-regions/formulas.json"
    formulas = json.loads(formulas_path.read_bytes())
    metadata = json.loads((DEST / "metadata.json").read_bytes())
    status = json.loads((ROOT / "docs/proof-status.json").read_bytes())
    graph = json.loads((ROOT / ".lake/theorem-explorer/lean-graph.json").read_bytes())
    graph_audit = json.loads((ROOT / "docs/theorem-explorer/audit.json").read_bytes())
    assert graph_audit["rawGraphSha256"] == hashlib.sha256(
        (ROOT / ".lake/theorem-explorer/lean-graph.json").read_bytes()).hexdigest(), "Stale theorem graph audit"
    for path, sha in graph_audit["sourceSha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == sha, f"Stale source audit: {path}"
    assert formulas["schemaVersion"] == metadata["schemaVersion"] == 1
    assert formulas["leanVersion"] == status["leanVersion"] == graph["leanVersion"]
    assert status["projectAxioms"] == status["placeholderDependentDeclarations"] == 0
    assert status["nonstandardTheoremAxioms"] == []
    assert metadata["provedTheorem"] == status["gaussianPhaseBandToolkit"]["actualTheorem"], (
        "Plot endpoint must follow the current proved region in proof-status.json"
    )
    assert set(formulas["curves"]) == {c["id"] for c in metadata["curves"]}
    assert len(metadata["curves"]) == len(formulas["curves"]), "Duplicate curve IDs"
    for proof in formulas["proofs"]:
        assert set(proof["axioms"]) <= STANDARD_AXIOMS, proof["name"]
    assert {metadata["provedTheorem"], metadata["comparisonTheorem"]} <= {
        p["name"] for p in formulas["proofs"]
    }
    index = {n["id"]: n for n in graph["nodes"]}
    references = {}
    for role in ("provedTheorem", "comparisonTheorem"):
        name = metadata[role]
        n = index[name]
        assert n["kind"] == "theorem" and n["project"]
        assert set(n["axioms"]) <= STANDARD_AXIOMS
        location = n["location"]
        assert location["exact"], f"An exact source link is required for {name}"
        path = n["module"].replace(".", "/") + ".lean"
        assert name.split(".")[-1] in (ROOT / path).read_text().splitlines()[location["line"] - 1]
        references[role] = {"name": name, "path": path, "line": location["line"],
                            "axioms": n["axioms"], "statement": n["statement"]}
    for curve in metadata["curves"]:
        if curve["id"] == "gaussian":
            assert curve["status"] == "lean-proved" and curve["edge"] == "closed"
        else:
            assert curve["minimumHeight"] <= formulas["minimumHeight"]
            assert curve["status"].startswith("external-")
            assert curve["url"].startswith("https://")
            assert curve["style"] == ("solid" if curve["status"] == "external-inspected" else "dashed")
            # The human legend must retain the coefficient actually exported.
            tree = formulas["curves"][curve["id"]]
            coefficient = tree[2][1][1] if curve["id"].startswith("vk-") else tree[2][1]
            assert format(evaluate(coefficient, 1), ".12g") in curve["label"], "Stale legend coefficient"
    return formulas_path, formulas, metadata, references


def render(formulas, meta, png=None):
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 11, "text.color": "#172b40",
        "axes.labelcolor": "#324a60", "axes.edgecolor": "#b7c5d3",
        "xtick.color": "#52677a", "ytick.color": "#52677a",
        "svg.hashsalt": "riemann-gaussian-zero-free-v1", "svg.fonttype": "path",
        "path.simplify": False, "savefig.facecolor": "white",
    })
    fig = plt.figure(figsize=(13, 9), facecolor="white")
    fig.text(.055, .950, meta["title"], fontsize=24, weight="bold")
    fig.text(.055, .918, "Our independent proof extends beyond the benchmarks in the checked interval", fontsize=12)
    fig.text(.055, .875, r"Our proved right edge: $\sigma \geq 1-d(t)$   |   $L=\log|t|$ (natural logarithm)", fontsize=12)
    fig.text(.055, .846, r"Larger width means more zero exclusion. Both signs of height and the reflected left edge apply.", fontsize=10.5)
    overview = fig.add_axes((.080, .393, .392, .373))
    zoom = fig.add_axes((.595, .393, .375, .373))
    for ax in (overview, zoom):
        ax.set_facecolor("#f8fafc")
        ax.grid(True, color="#dfe7ee", lw=.65, zorder=0)
        ax.spines[["top", "right"]].set_visible(False)
    lower = math.log(formulas["minimumHeight"])
    upper = meta["overviewMaximumLogHeight"]
    heights = np.geomspace(lower, upper, 800)
    zlow, zhigh = meta["zoomLogHeights"]
    zheights = np.linspace(zlow, zhigh, 600)
    samples = {c["id"]: np.array([evaluate(formulas["curves"][c["id"]], L) for L in heights])
               for c in meta["curves"]}
    assert all(np.isfinite(v).all() and (v > 0).all() for v in samples.values())
    bottom = min(v.min() for v in samples.values()) / 2
    top = max(v.max() for v in samples.values()) * 1.6
    start = crossover(formulas["comparison"])
    end = evaluate(formulas["comparison"]["ceiling"], 0)
    assert lower < zlow < start < end < zhigh < upper
    assert not formulas["comparison"]["lowerClosed"] and formulas["comparison"]["upperClosed"]
    # Gray marks a theorem's interval, never a numerically inferred record range.
    overview.axvspan(start, end, color="#bbc6d2", alpha=.35, zorder=1)
    zoom.axhspan(start, end, color="#c2ccd8", alpha=.42, zorder=1)
    for curve in meta["curves"]:
        ours = curve["status"] == "lean-proved"
        color, values = curve["color"], samples[curve["id"]]
        style = "-" if curve["style"] == "solid" else (0, (5, 3))
        width, order = (3.4, 10) if ours else (1.6, 3)
        overview.plot(heights, values, color=color, ls=style, lw=width, zorder=order)
        if curve["style"] == "solid":
            overview.fill_between(heights, bottom, values, color=color,
                                  alpha=.14 if ours else .035, zorder=2)
        zwidths = np.array([evaluate(formulas["curves"][curve["id"]], L) for L in zheights])
        # Plot distance from 1 internally to avoid subtractive rounding in sigma.
        zoom.plot(-zwidths * 1e6, zheights, color=color, ls=style, lw=width, zorder=order)
        if curve["style"] == "solid":
            zoom.fill_betweenx(zheights, -zwidths * 1e6, 0, color=color,
                               alpha=.18 if ours else .04, zorder=2)
    overview.set(xscale="log", yscale="log", xlim=(lower, upper), ylim=(bottom, top),
                 xlabel=r"Log-height $L=\log|t|$  (logarithmic scale)",
                 ylabel=r"Zero-free width $d(t)$  (logarithmic scale)")
    overview.set_title("A · Overview across heights", loc="left", pad=15, weight="bold", fontsize=12)
    overview.xaxis.set_minor_locator(NullLocator())
    overview.yaxis.set_minor_locator(NullLocator())
    overview.text(.04, .06, "Shading below solid boundaries\nmarks their stated zero-free regions.",
                  transform=overview.transAxes, fontsize=10,
                  bbox={"facecolor": "white", "edgecolor": "none", "alpha": .90, "pad": 5})
    overview.annotate(f"$|t|={formulas['minimumHeight']:,}$", (lower, samples["gaussian"][0]),
                      xytext=(9, -27), textcoords="offset points", fontsize=10,
                      arrowprops={"arrowstyle": "-", "color": "#d64a35"}, color="#b93827")
    zoom.set(xlim=(-meta["zoomMaximumWidth"] * 1e6, 0), ylim=(zlow, zhigh),
             xlabel=r"Real part $\sigma$  (magnified near 1)", ylabel=r"Log-height $L=\log|t|$")
    zoom.set_title("B · Magnified right edge", loc="left", pad=15, weight="bold", fontsize=12)
    zoom.set_xticks([-3, -2, -1, 0])
    zoom.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{1 + x * 1e-6:.6f}" if x else "1"))
    zoom.set_yticks([zlow, formulas["comparison"]["bracket"][0], end, (end + zhigh) / 2, zhigh])
    zoom.yaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{int(x):,}"))
    zoom.axhline(start, color="#667d91", lw=.9, ls=(0, (3, 3)), zorder=9)
    zoom.axhline(end, color="#667d91", lw=.9, ls=(0, (3, 3)), zorder=9)
    zoom.text(.97, .20, "Zero-free\ntoward σ = 1 →", ha="right", transform=zoom.transAxes,
              fontsize=10.5, color="#98301f", bbox={"facecolor": "white", "alpha": .85, "edgecolor": "none"})
    zoom.text(.03, .955, "Interior continues ←", transform=zoom.transAxes, va="top", fontsize=10)
    zoom.text(.97, (start + end - 2 * zlow) / (2 * (zhigh - zlow)), "Lean comparison band",
              transform=zoom.transAxes, ha="right", va="center", fontsize=10, color="#374a60",
              bbox={"facecolor": "white", "alpha": .90, "edgecolor": "none", "pad": 3})
    handles = [Line2D([], [], color=c["color"], lw=3 if c["status"] == "lean-proved" else 1.8,
                      ls="-" if c["style"] == "solid" else (0, (5, 3)), label=c["label"])
               for c in meta["curves"]]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(.057, .318),
               ncols=2, frameon=False, fontsize=10.5, columnspacing=3, handlelength=3.2, labelspacing=.8)
    fig.text(.06, .128, "Solid: proved here or inspected external result. Dashed: reported refinement / unresolved candidate.", fontsize=10)
    fig.text(.06, .098, r"Gray band: $L_* < L \leq " + latex(formulas["comparison"]["ceiling"]) +
             rf"$; $L_*\approx {start:.3f}$ is drawn numerically.", fontsize=10)
    fig.text(.06, .068, "External proofs are not imported. Eventual bounds with unevaluated thresholds are not plotted.", fontsize=10)
    fig.text(.06, .038, "Curves are sampled illustrations; exact domains, sources and Lean proofs are linked with the graph.", fontsize=10)
    output = io.BytesIO()
    description = (meta["scope"] + " Left: zero-free width versus log-height. Right: regions shaded "
                   "toward sigma=1, our independently proved complete region in coral. "
                   "It extends beyond the combined benchmark widths in the gray Lean-checked interval. "
                   "Dashed external curves are reported or unresolved. " + " ".join(meta["omitted"]))
    fig.savefig(output, format="svg", metadata={"Date": None, "Title": meta["title"],
                "Description": description, "Creator": "scripts/build_zero_free_plot.py"})
    if png:
        png.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(png, dpi=150)
    plt.close(fig)
    # Accessible labels remain readable even though font outlines make the
    # scientific figure render consistently in GitHub and standalone viewers.
    # Matplotlib leaves spaces at the ends of multiline path coordinates.
    # Normalize that insignificant whitespace for the repository's commit gate.
    data = "\n".join(line.rstrip() for line in output.getvalue().decode().splitlines()) + "\n"
    end_tag = data.index(">", data.index("<svg"))
    from html import escape
    data = (data[:end_tag] + ' role="img" aria-labelledby="plot-title plot-description"' + data[end_tag:])
    end_tag = data.index(">", data.index("<svg")) + 1
    data = data[:end_tag] + f'\n <title id="plot-title">{escape(meta["title"])}</title>\n <desc id="plot-description">{escape(description)}</desc>' + data[end_tag:]
    ET.fromstring(data)
    return data.encode(), {"crossoverDrawingApproximation": start,
                           "ceilingDrawingApproximation": end,
                           "exactCeiling": formulas["comparison"]["ceiling"]}


def build(png=None):
    path, formulas, meta, references = load_inputs()
    svg, drawing = render(formulas, meta, png)
    inputs = ["scripts/ExportZeroFreePlot.lean", "scripts/build_zero_free_plot.py",
              "scripts/requirements-plots.txt", "docs/zero-free-regions/metadata.json",
              "docs/proof-status.json", meta["literatureTable"]]
    # Hash every imported source in the graph, not only the terminal file.
    graph_audit = json.loads((ROOT / "docs/theorem-explorer/audit.json").read_bytes())
    audit = {"schemaVersion": 1, "generator": "scripts/build_zero_free_plot.py",
             "leanVersion": formulas["leanVersion"], "sourceAuditDate": meta["sourceAuditDate"],
             "formulaProofs": formulas["proofs"], "theorems": references,
             "scope": meta["scope"], "drawingIsProof": False, "drawing": drawing,
             "minimumHeight": formulas["minimumHeight"],
             "matplotlibVersion": matplotlib.__version__, "numpyVersion": np.__version__,
             "inputs": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in inputs},
             "theoremExplorerAuditSha256": hashlib.sha256((ROOT / "docs/theorem-explorer/audit.json").read_bytes()).hexdigest(),
             "theoremExplorerAudit": "docs/theorem-explorer/audit.json",
             "proofGraphNodes": graph_audit["declarations"],
             "formulaExportSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
             "svgSha256": hashlib.sha256(svg).hexdigest()}
    return {DEST / "comparison.svg": svg, DEST / "formulas.json": path.read_bytes(),
            DEST / "audit.json": (json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--png", type=Path, help="Optional local raster preview; not a CI artifact")
    args = parser.parse_args()
    outputs = build(args.png)
    stale = []
    for path, content in outputs.items():
        if args.check:
            if not path.is_file() or path.read_bytes() != content:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    if stale:
        raise SystemExit("Stale zero-free plot artifacts; run the Lean exporter and plot builder:\n" + "\n".join(stale))
    print("Zero-free comparison picture, checked formulas and provenance are consistent.")


if __name__ == "__main__":
    main()
