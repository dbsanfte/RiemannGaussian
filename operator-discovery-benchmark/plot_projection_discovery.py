#!/usr/bin/env python3
"""Standalone figures for the projection, coupling law and zero controls."""

from fractions import Fraction as Q
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
import numpy as np


def main():
    output = Path(__file__).resolve().parent/"projection-results"
    search = json.loads((output/"projection_search.json").read_text())
    exact = json.loads((output/"projection_verification.json").read_text())
    analytic = json.loads((output/"projection_analytic_probe.json").read_text())
    audit = json.loads((output/"projection_analytic_verification.json").read_text())
    assert exact["all_passed"] and analytic["all_passed"] and audit["all_passed"]
    fig, grid = plt.subplots(2, 2, figsize=(13.4, 8.8), constrained_layout=True)
    axes = grid.ravel()
    fig.suptitle("Verified carry projection and operator interactions; originality and RH unresolved", fontsize=14)
    limit = 31
    mask = np.asarray([[int(a & b == 0) for a in range(limit+1)] for b in range(limit+1)])
    axes[0].imshow(mask, origin="lower", cmap=ListedColormap(["#e7ebef", "#258365"]),
                   vmin=0, vmax=1, extent=(-0.5, limit+0.5, -0.5, limit+0.5))
    axes[0].set(xlabel="Exponent a of prime p", ylabel="Exponent b of distinct prime q",
                title="M keeps p^a q^b when exponent bits are disjoint",
                xticks=[0, 8, 16, 24, 31], yticks=[0, 8, 16, 24, 31])
    axes[0].text(0.025, 0.975, "Green: kept; grey: removed\nKnown multinomial-parity ingredient",
                 transform=axes[0].transAxes, va="top", fontsize=9,
                 bbox={"facecolor": "white", "alpha": 0.92, "edgecolor": "none", "pad": 4})
    hierarchy = search["prime_projection_hierarchy"]["records"]
    bases = [x["largest_tested_prime_base"] for x in hierarchy]
    counts = [x["extra_non_prime_power_indices"] for x in hierarchy]
    axes[1].bar(range(len(bases)), counts, color="#355d9a")
    axes[1].set(xticks=range(len(bases)), xticklabels=bases, xlabel="Apply all prime-base projections through this prime",
                ylabel="Mixed-prime indices still kept, n ≤ 4096",
                title="Hierarchy tends to classical multiplicative completion")
    for j, count in enumerate(counts):
        axes[1].annotate(str(count), (j, count), xytext=(0, 4), textcoords="offset points",
                         ha="center", fontsize=10)
    axes[1].text(0.97, 0.95, "Bases 2, 3, 5, 7 miss n = 3072\nW(3072) = 11; base 11 removes it\nUniversal limit requires ALL prime bases",
                 transform=axes[1].transAxes, va="top", ha="right", fontsize=9)
    records = search["commutator_search"]["records"]
    predicted = [float(Q(x["features"][0])**2*Q(x["features"][1])) for x in records]
    measured = [float(Q(x["commutator_coefficient"])) for x in records]
    lo, hi = min(predicted), max(predicted)
    pad = (hi-lo)*0.12 or 1
    axes[2].plot([lo-pad, hi+pad], [lo-pad, hi+pad], color="#c6cbd1", lw=1.5)
    axes[2].scatter(predicted[:8], measured[:8], color="#355d9a", marker="o", s=43, label="Training inputs")
    axes[2].scatter(predicted[8:], measured[8:], color="#bf7147", marker="x", s=55, label="Fresh inputs and prime pairs")
    axes[2].set(xlabel="Predicted f(p)^2 f(q)", ylabel="Measured (T S f − S T f)(p^2 q)",
                title="A cubic cross-prime interaction, proved symbolically")
    axes[2].legend(frameon=False, fontsize=9, loc="upper left")
    axes[2].text(0.97, 0.045, "Full commutator's Re(s) > 1/2\nanalytic bridge is unestablished",
                 transform=axes[2].transAxes, ha="right", fontsize=9)
    actual = analytic["actual_critical_line_zero_control"]
    phases = np.unwrap(np.asarray(actual["phase_samples_radians"]))
    turns = (phases-phases[0])/(2*np.pi)
    axes[3].plot(np.linspace(0, 1, len(turns)), turns, color="#258365", lw=2)
    axes[3].set(xlabel="One circuit around the certified actual zeta zero",
                ylabel="Unwrapped phase change of (s−1)ζ(s) / 2π",
                title="Zero criterion detects branching; M creates its own zeros")
    axes[3].text(0.03, 0.97, "Actual zero near 1/2 + 14.134725i\nC nonzero on disk; log jump = 2πi C\nCrossing circle is compatible with RH",
                 transform=axes[3].transAxes, va="top", fontsize=9)
    axes[3].text(0.97, 0.04, "Created F_chi zero near 1.153397 + 14.016612i\nActual ζ is nonzero on that entire disk\nZero preservation by M is rigorously rejected",
                 transform=axes[3].transAxes, ha="right", fontsize=9,
                 bbox={"facecolor": "#fff5ed", "edgecolor": "none", "pad": 5})
    for ax in axes[1:]:
        ax.spines[["top", "right"]].set_visible(False)
    for extension in ("png", "pdf"):
        path = output/f"projection_discovery.{extension}"
        fig.savefig(path, dpi=180)
        print(path)
    plt.close(fig)


if __name__ == "__main__":
    main()
