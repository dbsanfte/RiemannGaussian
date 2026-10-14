#!/usr/bin/env python3
"""Export the learned coupling law and certified zeta controls."""

from fractions import Fraction as Q
from pathlib import Path
import json
from math import factorial

import flint
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
import numpy as np


def midpoint(text):
    return float(flint.arb(text).mid())


def main():
    output = Path(__file__).resolve().parent/"coupling-results"
    search = json.loads((output/"coupling_search.json").read_text())
    exact = json.loads((output/"coupling_verification.json").read_text())
    analytic = json.loads((output/"coupling_analytic_probe.json").read_text())
    audit = json.loads((output/"coupling_analytic_verification.json").read_text())
    assert exact["all_passed"] and analytic["all_passed"] and audit["all_passed"]
    fig, grid = plt.subplots(2, 2, figsize=(13.5, 9.0), constrained_layout=True)
    axes = grid.ravel()
    fig.suptitle("Learned arithmetic interactions and certified zeta controls; RH remains open", fontsize=14)
    ks = np.arange(2, 17)
    for alpha, color in (("1/2", "#355d9a"), ("1", "#258365"), ("3/2", "#bf7147")):
        predicted = [float(abs(Q(factorial(k), 2)*Q(alpha)**(k+2))) for k in ks]
        observed = [float(abs(Q(search["commutator_tensor_profiles"][alpha][2][k]))) for k in ks]
        axes[0].semilogy(ks, predicted, color=color, lw=1.5, alpha=0.65)
        axes[0].scatter(ks, observed, color=color, s=23, label=f"α = {alpha}")
    axes[0].set(xlabel="Number k of other distinct prime factors", ylabel="Absolute coefficient at p²q₁⋯qₖ",
                title="One factorial law, validated at fresh arities", xticks=[2, 5, 8, 11, 14, 16])
    axes[0].legend(frameon=False, fontsize=9, loc="upper left")
    axes[0].text(0.97, 0.035, "k ≥ 2: (−1)ᵏ⁺¹ k! αᵏ⁺² / 2\nAt k = 1: α³; factorial extrapolation is false",
                 ha="right", transform=axes[0].transAxes, fontsize=9)
    kernel = np.asarray([[int(a & (b+1) == 0) for a in range(16)] for b in range(16)])
    axes[1].imshow(kernel, origin="lower", cmap=ListedColormap(["#e7ebef", "#355d9a"]),
                   vmin=0, vmax=1, extent=(-0.5, 15.5, -0.5, 15.5))
    axes[1].set(xlabel="Local exponent a", ylabel="Other component's p-exponent b",
                title="A typed module action: allow a & (b+1) = 0", xticks=[0, 4, 8, 12, 15], yticks=[0, 4, 8, 12, 15])
    axes[1].text(0.025, 0.975, "Blue: allowed; grey: suppressed\nB(x, 1) = 0, while B(1, x) = x\nModule associativity proved\nB is not a commutative product",
                 transform=axes[1].transAxes, va="top", fontsize=9,
                 bbox={"facecolor": "white", "alpha": 0.94, "edgecolor": "none", "pad": 4})
    comparisons = analytic["actual_zeta_ball_checks"]
    errors = [midpoint(x["difference_upper_ball"])/midpoint(x["combined_infinite_tail_bound_ball"]) for x in comparisons]
    bad = [midpoint(x["perturbed_difference_lower_ball"])/midpoint(x["combined_infinite_tail_bound_ball"]) for x in comparisons]
    labels = [f"{x['s'][0]}\n{x['s'][1]}i" for x in comparisons]
    axes[2].scatter(range(6), errors, color="#258365", s=50, label="Correct coefficients: error upper bound")
    axes[2].scatter(range(6), bad, color="#bf7147", marker="x", s=60, label="Coefficient 12 changed: error lower bound")
    axes[2].axhline(1, color="#7b8289", ls="--", lw=1)
    axes[2].set(yscale="log", xticks=range(6), xticklabels=labels,
                xlabel="Actual zeta argument (real part; imaginary part)",
                ylabel="Error divided by proved infinite-tail bound",
                title="Six actual-zeta checks reject the coefficient error")
    axes[2].legend(frameon=False, fontsize=8.5, loc="upper left")
    theta = np.linspace(0, 2*np.pi, 257)
    axes[3].axvspan(0, 1.6, color="#edf6f0", alpha=0.9)
    axes[3].plot([-1, 1, 1, -1, -1], [-1, -1, 1, 1, -1], color="#b5bec8", lw=1)
    axes[3].plot(np.cos(theta), np.sin(theta), color="#355d9a", lw=2, label="Rouché circle, radius 10⁻⁴")
    axes[3].axvline(0, color="#7b8289", ls="--", lw=1)
    axes[3].scatter([0], [0], color="#bf7147", marker="+", s=75, label="Disk centre")
    axes[3].set(xlim=(-1.6, 1.6), ylim=(-1.6, 1.6), aspect="equal",
                xlabel="(Re(s) − 1/2) / 10⁻⁴", ylabel="(Im(s) − 14.1347251417…) / 10⁻⁴",
                title="A certified actual zero; selected sector detects it")
    axes[3].legend(frameon=False, fontsize=8.5, loc="lower left")
    axes[3].text(0.97, 0.97, "Exactly one simple ζ zero inside\n|A| > 0.587775 on whole rectangle\nLogarithmic jump modulus > 3.69310",
                 ha="right", va="top", transform=axes[3].transAxes, fontsize=9,
                 bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 4})
    for ax in (axes[0], axes[2]):
        ax.spines[["top", "right"]].set_visible(False)
    for extension in ("png", "pdf"):
        path = output/f"coupling_discovery.{extension}"
        fig.savefig(path, dpi=180)
        print(path)
    plt.close(fig)


if __name__ == "__main__":
    main()
