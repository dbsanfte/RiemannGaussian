#!/usr/bin/env python3
"""Export the nonlinear candidate operators and their verification evidence."""

from fractions import Fraction as Q
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def main():
    base = Path(__file__).resolve().parent
    local = json.loads((base/"transfer-results/root_transfer_probe.json").read_text())
    global_ = json.loads((base/"global-results/global_carry_probe.json").read_text())
    control = json.loads((base/"global-results/global_analytic_probe.json").read_text())["zero_sensitivity_control"]
    fig, axes = plt.subplots(2,2,figsize=(12,8),layout="constrained")
    n = np.arange(2,33)
    ax = axes[0,0]
    ax.bar(n-.2, [float(Q(x)) for x in local["first_arithmetic_coefficients"][1:32]], width=.4, label="primewise transfer T")
    ax.bar(n+.2, [float(Q(x)) for x in global_["first_arithmetic_coefficients"][1:32]], width=.4, label="cross-prime transfer S")
    ax.set(title="Cross-prime bit collisions suppress arithmetic coefficients", xlabel="n", ylabel="exact rational coefficient")
    ax.legend(frameon=False,fontsize=9)
    samples=global_["root_limit_samples"]
    ax=axes[0,1]
    ax.plot([x["root_order"] for x in samples], [float(Q(x["coefficient_6"])) for x in samples], "o-", label="measured exact root lift at n=6")
    ax.axhline(0,color="gray",linestyle="--",label="proved q→∞ limit")
    ax.set(xscale="log",title="Cross-prime root lift: coefficient at 6 equals 1/q",xlabel="root order q",ylabel="coefficient at n=6")
    ax.legend(frameon=False,fontsize=9)
    certificate=local["uniform_certificate"][0]
    head=float(Q(certificate["finite_sum_bound"]))
    tail=float(Q(certificate["uniform_tail_bound"]))
    ax=axes[1,0]
    ax.barh([0], [head], label="exact Bernstein head bound")
    ax.barh([0], [tail],left=[head],color="C3",label="proved uniform infinite tail")
    ax.axvline(1,color="black",linestyle="--",label="zero-free threshold")
    ax.set(xlim=(0,1.1),yticks=[],title="All integer q≥2 and q→∞: correction stays nonzero",xlabel="bound on |R(x)−1| for |x|≤0.71")
    ax.text(head+.015,0,f"{head+tail:.6f}",va="center")
    ax.legend(frameon=False,fontsize=9,loc="lower left")
    phases=control["phase_samples_radians"]
    ax=axes[1,1]
    for name,label in (("actual_Z","actual Z on certified zero-free disk"),("extra_zero_model","control model with one added zero")):
        values=np.unwrap(phases[name])
        values=(values-values[0])/(2*np.pi)
        ax.plot(np.arange(len(values))/(len(values)-1),values,label=label)
    ax.set(title="Logarithmic criterion detects an added off-line zero",xlabel="one turn around the test disk",ylabel="unwrapped phase change / 2π")
    ax.legend(frameon=False,fontsize=8)
    fig.suptitle("Verified candidate operators; historical novelty and RH remain unresolved",fontsize=13)
    destination=base/"transfer-results"
    fig.savefig(destination/"operator_transfer_results.png",dpi=180)
    fig.savefig(destination/"operator_transfer_results.pdf")
    print(f"Saved {destination/'operator_transfer_results.png'} and PDF")


if __name__=="__main__":
    main()
