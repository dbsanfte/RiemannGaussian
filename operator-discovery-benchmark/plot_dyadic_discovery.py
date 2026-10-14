#!/usr/bin/env python3
"""Standalone figures for certified extraction and multiplicity controls."""

from fractions import Fraction as Q
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
import numpy as np


def main():
    output = Path(__file__).resolve().parent/"dyadic-results"
    source = json.loads((output/"dyadic_root_search.json").read_text())
    independent = json.loads((output/"dyadic_root_verification.json").read_text())
    analytic = json.loads((output/"dyadic_analytic_probe.json").read_text())
    assert independent["all_passed"] and analytic["all_passed"]
    fig, grid = plt.subplots(2, 2, figsize=(13.4, 8.6), constrained_layout=True)
    axes = grid.ravel()
    fig.suptitle("Verified dyadic extraction laws; originality and RH remain unresolved", fontsize=14)
    search = source["search"]
    models = search["all_candidates"]
    colours = ["#22875f" if x["held_out_passed"] else "#c4c9cf" for x in models]
    axes[0].bar([x["multiplier"] for x in models],
                [float(Q(x["learned_parameter_scale"])) for x in models], color=colours)
    axes[0].set(xlabel="Exponent multiplier m", ylabel="Fitted parameter scale c",
                title="31 training fits; 5 fresh survivors", xticks=[2, 4, 8, 16, 24, 32])
    axes[0].text(0.96, 0.94, "Green: m = 2, 4, 8, 16, 32\nc = 1/m",
                 transform=axes[0].transAxes, ha="right", va="top", fontsize=10)
    cert = source["uniform_real_parameter_certificate"]
    radius = Q(cert["radius"])
    degrees, totals = [], []
    finite = Q(0)
    for detail in cert["coefficient_bounds"]:
        degree = detail["exponent"]
        finite += Q(detail["coefficient_bound"])*radius**degree
        degrees.append(degree)
        totals.append(float(finite+2*radius**(degree+1)/(1-radius)))
    axes[1].plot(degrees, totals, color="#355d9a", lw=2)
    axes[1].axhline(1, color="#bd593e", ls="--", lw=1.2)
    axes[1].set(xlabel="Exact polynomial degree", ylabel="Certified head + infinite tail bound",
                title="All real beta in [0, 1]", ylim=(0.5, 3.3))
    axes[1].text(0.97, 0.94, f"Final bound: {totals[-1]:.9f} < 1\nEvery |x| ≤ 0.71",
                 transform=axes[1].transAxes, ha="right", va="top", fontsize=10)
    records = analytic["multiplicity_and_branch_control"]["records"]
    multiplicities, orders = [1, 2, 4, 8], [2, 4, 8, 16]
    matrix = np.asarray([[int(next(x for x in records
                                  if x["added_zero_multiplicity"] == m and x["root_order"] == order)
                              ["root_monodromy_obstruction_proved"])
                          for order in orders] for m in multiplicities])
    axes[2].imshow(matrix, cmap=ListedColormap(["#e9edf0", "#d27d54"]), vmin=0, vmax=1,
                   aspect="auto")
    axes[2].set(xticks=range(4), xticklabels=orders, yticks=range(4), yticklabels=multiplicities,
                xlabel="Dyadic root order", ylabel="Controlled added-zero multiplicity",
                title="A finite root order can miss a zero")
    for row in range(4):
        for column in range(4):
            axes[2].text(column, row, "Branches" if matrix[row, column] else "No jump",
                         ha="center", va="center", fontsize=9)
    actual = analytic["actual_critical_line_zero_control"]
    phases = np.unwrap(np.asarray(actual["phase_samples_radians"]))
    turns = (phases-phases[0])/(2*np.pi)
    circle_parameter = np.linspace(0, 1, len(turns))
    axes[3].plot(circle_parameter, turns, color="#253a55", label="Z = (s−1)ζ(s)")
    for order in (2, 4, 8, 16):
        axes[3].plot(circle_parameter, turns/order, label=f"Z root of order {order}")
    axes[3].set(xlabel="One circuit around the certified zero", ylabel="Unwrapped phase change / 2π",
                title="Actual simple zeta zero near 1/2 + 14.134725i")
    axes[3].text(0.04, 0.96, "Arb + Rouche certify one simple zero\nCorrection extends without zeros on disk\nCircle crosses Re(s) = 1/2; compatible with RH",
                 transform=axes[3].transAxes, va="top", fontsize=9)
    axes[3].legend(frameon=False, fontsize=9, loc="upper left", bbox_to_anchor=(0.025, 0.79))
    for ax in (axes[0], axes[1], axes[3]):
        ax.spines[["top", "right"]].set_visible(False)
    for extension in ("png", "pdf"):
        path = output/f"dyadic_root_discovery.{extension}"
        fig.savefig(path, dpi=180)
        print(path)
    plt.close(fig)


if __name__ == "__main__":
    main()
