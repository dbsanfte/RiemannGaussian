#!/usr/bin/env python3
"""Export figures showing recovered root arithmetic and proof filters."""

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from exact_arithmetic import factorial_valuation


def main():
    output = Path(__file__).resolve().parent / "root-results"
    root = json.loads((output / "root_probe.json").read_text())
    audit = json.loads((output / "carry_zero_audit.json").read_text())
    schur = json.loads((output / "schur_root_audit.json").read_text())
    schur_passed = {(x["root_order"], x["operator"]["prime"], x["operator"]["parameter"])
                    for x in schur["records"] if x["certifies_nonzero_correction_Re_s_gt_half"]}
    fig, axes = plt.subplots(2, 2, figsize=(12, 8), layout="constrained")

    validation = root["coefficients"]["validation"]["anonymous_00"]
    values = np.array([float(real) for real, _ in validation])
    n = np.arange(1, len(values) + 1)
    ax = axes[0, 0]
    ax.stem(n, values, basefmt=" ", markerfmt="o", linefmt="C0-")
    ax.axvspan(16.5, 32.5, color="C0", alpha=.08, label="held-out indices")
    ax.set(title="Square-root coefficients recovered from numerical zeta", xlabel="n", ylabel="coefficient")
    ax.legend(frameon=False)

    record = next(x for x in root["denominator_search"] if x["root_order"] == 7)
    e = np.arange(1, 70)
    exact = np.array(record["values"][1:70])
    floor_fit = e + e // 7
    ax = axes[0, 1]
    ax.plot(e, exact, color="C0", label="exact denominator valuation")
    ax.plot(e, floor_fit, "--", color="C3", label="training fit: e + floor(e/7)")
    ax.axvspan(0, 8.5, color="gray", alpha=.13, label="fitting range")
    ax.axvline(49, color="C3", alpha=.5, linewidth=1)
    ax.set(title="A convincing fit fails at exponent 49", xlabel="prime exponent e", ylabel="v7(denominator)")
    ax.legend(frameon=False, fontsize=8)

    size = 32
    matrix = np.array([[int(factorial_valuation(i+j, 2) ==
                           factorial_valuation(i, 2)+factorial_valuation(j, 2))
                        for j in range(size)] for i in range(size)])
    ax = axes[1, 0]
    ax.imshow(matrix, origin="lower", cmap="Blues", interpolation="nearest", vmin=0, vmax=1)
    ax.set(title="Recovered no-carry kernel: classical infinitary product", xlabel="left prime exponent", ylabel="right prime exponent")

    bounds = np.array([[next(x["total_bound_decimal_diagnostic"] for x in audit["certificates"]
                            if x["root_order"] == order and x["operator"]["prime"] == prime
                            and x["operator"]["parameter"] == parameter)
                        for prime in (2, 3, 5, 7) for parameter in ("0", "1/2", "2", "-1")]
                       for order in (2, 3, 4, 5, 6, 7)])
    ax = axes[1, 1]
    colors = np.zeros(bounds.shape, dtype=int)
    for i, order in enumerate((2, 3, 4, 5, 6, 7)):
        for j, (prime, parameter) in enumerate((p,t) for p in (2,3,5,7) for t in ("0","1/2","2","-1")):
            if bounds[i,j] >= 1:
                colors[i,j] = 1 if (order, prime, parameter) in schur_passed else 2
    from matplotlib.colors import ListedColormap
    ax.imshow(colors, cmap=ListedColormap(["#247a57", "#315899", "#c99545"]), aspect="auto", vmin=0, vmax=2)
    ax.set(yticks=np.arange(6), yticklabels=np.arange(2, 8), ylabel="root order q",
           xticks=np.arange(16), xticklabels=[f"{p}\n{t}" for p in (2, 3, 5, 7) for t in ("0", "½", "2", "−1")],
           xlabel="base prime / carry parameter", title="96/96 zero-free certificates: 80 norm bounds + 16 Schur")
    ax.tick_params(axis="x", labelsize=8)
    for i in range(6):
        for j in range(16):
            ax.text(j, i, ("✓", "S", "?")[colors[i,j]], ha="center", va="center", color="white", fontsize=10)

    fig.savefig(output / "root_discovery.png", dpi=180)
    fig.savefig(output / "root_discovery.pdf")
    print(f"Saved {output / 'root_discovery.png'} and PDF")


if __name__ == "__main__":
    main()
