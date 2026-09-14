#!/usr/bin/env python3
"""Draw Lean-checked coefficient enclosures, with an optional-proof snapshot audit.

The ordinary Lean exporter checks only lightweight coefficient theorems.
This renderer never invokes the exhaustive numerical certificate target.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from html import escape
import io
import json
from pathlib import Path
import xml.etree.ElementTree as ET

import matplotlib
matplotlib.use("Agg")
from matplotlib import pyplot as plt
from matplotlib.ticker import FuncFormatter

from build_theorem_explorer import digest, json_bytes, STANDARD_AXIOMS
from build_numerical_certificate_explorer import checked_audit

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "docs/numerical-certificate"
EXPORT = ROOT / ".lake/numerical-certificate-plot/coefficients.json"


def inputs():
    coefficients = json.loads(EXPORT.read_bytes())
    meta = json.loads((DEST / "metadata.json").read_bytes())
    audit = checked_audit()
    graph_path = ROOT / "docs/numerical-certificate-explorer/audit.json"
    graph = json.loads(graph_path.read_bytes())
    assert coefficients["leanVersion"] == audit["leanVersion"] == graph["leanVersion"]
    assert coefficients["schemaVersion"] == meta["schemaVersion"] == 1
    assert meta["endpoint"] in graph["endpointAxioms"]
    assert meta["gainTheorem"] in graph["endpointAxioms"]
    assert meta["coefficientTheorem"] == coefficients["exactCoefficientTheorem"]
    for proof in coefficients["proofs"]:
        assert set(proof["axioms"]) <= STANDARD_AXIOMS
    assert meta["gainTheorem"] in {p["theorem"] for p in coefficients["proofs"]}
    q = lambda pair: Fraction(*pair)
    values = {"twoThirds": q(coefficients["twoThirds"]),
              "floor": q(coefficients["certifiedFloor"]),
              "baseline": tuple(map(q, coefficients["baseline"])),
              "improved": tuple(map(q, coefficients["improved"]))}
    assert values["floor"] == Fraction(6731, 10000), "Update literal-count audit and presentation together"
    assert values["twoThirds"] < values["baseline"][0] < values["baseline"][1] < values["floor"]
    assert values["floor"] < values["improved"][0] < values["improved"][1] < 1
    assert values["improved"][0] - values["baseline"][1] > Fraction(3, 5000)
    return coefficients, meta, audit, graph_path, values


def render(meta, values, png=None):
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                         "text.color": "#172b40", "axes.labelcolor": "#324a60",
                         "xtick.color": "#52677a", "ytick.color": "#172b40",
                         "svg.hashsalt": "riemann-certificate-v1", "svg.fonttype": "path",
                         "savefig.facecolor": "white"})
    fig = plt.figure(figsize=(12, 7.1), facecolor="white")
    fig.text(.055, .929, meta["title"], fontsize=28, weight="bold")
    fig.text(.055, .883, "Eventually simple and on the critical line · starting height unevaluated", fontsize=12)
    fig.text(.055, .829, "A · Limiting coefficients in full 0–100% context", fontsize=12, weight="bold")
    overview = fig.add_axes((.255, .581, .665, .21))
    zoom = fig.add_axes((.255, .217, .665, .235))
    baseline = float(sum(values["baseline"]) / 2) * 100
    improved = float(sum(values["improved"]) / 2) * 100
    floor = float(values["floor"]) * 100
    points = [float(values["twoThirds"]) * 100, baseline, improved]
    labels = ["Two thirds", meta["baselineLabel"] + "  h", "RiemannGaussian  C*"]
    colours = [meta["colours"][k] for k in ("twoThirds", "baseline", "improved")]
    for ax in (overview, zoom):
        ax.set_facecolor("#f8fafc")
        ax.set_ylim(-.6, 2.6)
        ax.set_yticks([2, 1, 0], labels)
        ax.tick_params(axis="y", length=0, pad=12)
        ax.spines[["top", "left", "right"]].set_visible(False)
        ax.spines["bottom"].set_color("#b7c5d3")
        ax.grid(axis="x", color="#dfe7ee", linewidth=.7, zorder=0)
        ax.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{x:g}%"))
    overview.set_xlim(0, 100)
    overview.set_xticks([0, 25, 50, 75, 100])
    overview.axvspan(*meta["zoomPercent"], color="#cbd5e1", alpha=.6)
    overview.barh([2, 1, 0], points, color=colours, height=.43, zorder=3)
    for y, v, colour in zip([2, 1, 0], points, colours):
        overview.text(v + 1.8, y, f"≈ {v:.5f}%", va="center", color=colour, fontsize=10)
    fig.text(.055, .495, "B · Magnified comparison — same coefficients", fontsize=12, weight="bold")
    zoom.set_xlim(*meta["zoomPercent"])
    zoom.set_xticks([66.6, 66.8, 67, 67.2, 67.4])
    zoom.axvspan(baseline, improved, color=colours[2], alpha=.12)
    zoom.scatter(points, [2, 1, 0], color=colours, s=90, zorder=4)
    # The exact enclosures are narrower than a pixel, but remain in the audit.
    for y, key, colour in [(1, "baseline", colours[1]), (0, "improved", colours[2])]:
        lo, hi = (float(q) * 100 for q in values[key])
        zoom.hlines(y, lo, hi, color=colour, linewidth=4, zorder=5)
    zoom.plot([floor, floor], [-.5, .45], color="#872f20", linestyle="--", linewidth=1.3)
    zoom.annotate(f"Closed eventual bound: {floor:.2f}%", (floor, 0), xytext=(-25, 13),
                  textcoords="offset points", ha="right", color="#872f20", fontsize=10,
                  arrowprops={"arrowstyle": "-", "color": "#872f20"})
    zoom.annotate("", (baseline, 1.85), (improved, 1.85),
                  arrowprops={"arrowstyle": "<->", "color": colours[2]})
    zoom.text((baseline + improved) / 2, 2.19, "C* − h > 0.06 percentage points", ha="center",
              color="#b13e2c", fontsize=10)
    fig.text(.055, .125, "Lean checks strict rational enclosures of h and C*. Each limiting coefficient permits any positive ε.", fontsize=10)
    fig.text(.055, .091, "The proved 67.31% endpoint pays that ε. Both (0, T] and (T, 2T] counts are covered; RH remains open.", fontsize=10)
    fig.text(.055, .05, "Open the certificate explorer for the continuous cover, analytic transfer, source lines and full axiom audit.", fontsize=10)
    output = io.BytesIO()
    fig.savefig(output, format="svg", metadata={"Date": None, "Title": meta["title"],
                "Description": meta["scope"], "Creator": "scripts/build_numerical_certificate_plot.py"})
    if png:
        png.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(png, dpi=150)
    plt.close(fig)
    data = "\n".join(line.rstrip() for line in output.getvalue().decode().splitlines()) + "\n"
    pos = data.index(">", data.index("<svg"))
    data = data[:pos] + ' role="img" aria-labelledby="certificate-title certificate-description"' + data[pos:]
    pos = data.index(">", data.index("<svg")) + 1
    data = (data[:pos] + f'\n<title id="certificate-title">{escape(meta["title"])}</title>\n'
            f'<desc id="certificate-description">{escape(meta["scope"])}</desc>' + data[pos:])
    ET.fromstring(data)
    return data.encode()


def build(png=None):
    coefficients, meta, certificate, graph_path, values = inputs()
    svg = render(meta, values, png)
    paths = ["scripts/ExportNumericalCertificatePlot.lean", "scripts/build_numerical_certificate_plot.py",
             "scripts/requirements-plots.txt", "docs/numerical-certificate/metadata.json",
             "docs/numerical-certificate-explorer/snapshot.json", meta["baselineSource"]]
    audit = {"schemaVersion": 1, "leanVersion": coefficients["leanVersion"],
             "scope": meta["scope"], "drawingIsProof": False,
             "matplotlibVersion": matplotlib.__version__, "formulaProofs": coefficients["proofs"],
             "certificateInputSha256": certificate["inputSha256"],
             "certificateAuditSha256": digest((ROOT / "docs/numerical-certificate-audit.json").read_bytes()),
             "graphAuditSha256": digest(graph_path.read_bytes()),
             "coefficientExportSha256": digest(EXPORT.read_bytes()), "svgSha256": digest(svg),
             "inputs": {p: digest((ROOT / p).read_bytes()) for p in paths}}
    return {"comparison.svg": svg, "coefficients.json": EXPORT.read_bytes(), "audit.json": json_bytes(audit)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--png", type=Path)
    args = parser.parse_args()
    for name, content in build(args.png).items():
        path = DEST / name
        if args.check:
            assert path.is_file() and path.read_bytes() == content, f"Stale certificate chart: {name}"
        else:
            path.write_bytes(content)
    print("Certificate comparison chart, Lean coefficient enclosures and proof snapshot are consistent.")


if __name__ == "__main__":
    main()
