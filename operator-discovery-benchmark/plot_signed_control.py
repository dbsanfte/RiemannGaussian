#!/usr/bin/env python3
"""Standalone plots of finite signed-energy and correlation evidence."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def plot(source,destination):
    data=json.loads(Path(source).read_text()); records=data["records"][:3]
    fig,axes=plt.subplots(1,2,figsize=(12,4.5),layout="constrained")
    colors=["#34465b","#167b85","#bc5735"]
    for row,color in zip(records,colors):
        p=row["program"]; observations=row["observations"]
        X=[o["X"] for o in observations]; E=[float(Q(o["energy_over_X_squared"])) for o in observations]
        if p["family"]=="baseline": label="Original Möbius sum"
        elif p["family"]=="polynomial_fit": label="Learned base-2 signed filter"
        else: label="Generated base-9 signed filter"
        axes[0].plot(X,E,"o-",color=color,label=label,markersize=4,linewidth=1.3)
    chosen=records[1]; observations=chosen["observations"]
    X=[o["X"] for o in observations]
    D=[float(Q(o["exact_diagonal"])/o["X"]**2) for o in observations]
    C=[float(Q(o["off_diagonal_over_X_squared"])) for o in observations]
    E=[float(Q(o["energy_over_X_squared"])) for o in observations]
    for y,label,color in ((D,"Diagonal: elementary bound available","#ae8425"),
                           (C,"Signed off-diagonal: uniform control unproved","#783e86"),
                           (E,"Their sum: exact signed energy","#167b85")):
        axes[1].plot(X,y,"o-",label=label,color=color,markersize=4,linewidth=1.3)
    for ax in axes:
        ax.set_xscale("log"); ax.set_xlabel("Tested window scale X"); ax.grid(alpha=.18)
        ax.legend(fontsize=8,frameon=False,loc="best")
    axes[0].set_title("Exact finite moments"); axes[0].set_ylabel("A₂(X) / X²")
    axes[1].set_title("Where arithmetic cancellation is needed"); axes[1].set_ylabel("Contribution / X²")
    axes[1].axhline(0,color="#777777",linewidth=.6)
    axes[1].legend(fontsize=8,loc="center right",frameon=True,facecolor="white",framealpha=.9)
    fig.suptitle("Signed zeta control: finite evidence and the missing correlation bound",fontsize=13)
    fig.supxlabel("Lines connect tested windows. No uniform signed estimate or RH proof is certified.",fontsize=9)
    destination=Path(destination)
    fig.savefig(destination.with_suffix(".png"),dpi=180)
    fig.savefig(destination.with_suffix(".pdf"))
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--source",type=Path,required=True)
    parser.add_argument("--output-stem",type=Path,required=True); args=parser.parse_args(); plot(args.source,args.output_stem)
