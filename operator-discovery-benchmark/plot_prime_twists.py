"""Standalone research figure; finite RH leads are labelled as unproved."""
from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from prime_twist_report import load_latest


def number(v):return float(flint.arb(v).mid())


def main():
    result=load_latest();directory=Path(result["run_directory"])
    final=json.loads((directory/"final_evaluation.json").read_text());cal=final["signed_harmonic_calibration"]
    rows=cal["rows"];x=[r["x"] for r in rows]
    plt.rcParams.update({"font.size":10,"axes.spines.top":False,"axes.spines.right":False,"savefig.facecolor":"white"})
    fig,axes=plt.subplots(1,3,figsize=(15.4,4.9),constrained_layout=True)
    ax=axes[0]
    ax.loglog(x,[abs(number(r["centered_harmonic_residual_ball"])) for r in rows],"o-",color="#2563a6",label="Actual primes: finite observations")
    bound=float(Q(result["prime_density_constant"]))+float(flint.arb.const_euler())
    ax.plot([min(x),max(x)],[bound,bound],"--",color="#777777",label="Proved all-scale constant bound")
    ax.set(xlabel="x",ylabel=r"$|\sum_{p^k<x}\log(p)/p^k-\log x+\gamma|$",title="Signed harmonic control")
    ax.legend(fontsize=8,loc="lower left");ax.grid(alpha=.18,which="both")
    ax=axes[1]
    pool=[r for r in result["surviving_uniform_proof_obligations"] if Q(r["candidate"]["theta"])<0]
    if pool:
        row=min(pool,key=lambda r:(r["candidate"]["log_reciprocal_cost"],r["candidate"]["id"]))
        p,c=row["program"],row["candidate"];values=final["actual_values"][p["id"]]
        xx=sorted(int(n) for n in values if int(n)>=2);center=flint.arb(c["offset"]["value_ball"])
        yy=[abs(float((flint.arb(values[str(n)])-center).mid())) for n in xx]
        B=float(Q(c["constant"]));theta=float(Q(c["theta"]));ell=float(Q(c["log_power"]))
        import math
        curve=[B*n**theta*math.log(math.e+n)**ell for n in xx]
        ax.loglog(xx,yy,"o-",color="#2563a6",label="Actual centered twist: finite errors")
        ax.loglog(xx,curve,"--",color="#bb7d16",label="Learned RH premise; uniform proof missing")
        ax.set_title(f"Negative decay: leading twist {p['leading_shift']}")
        ax.set_ylabel("Absolute centered error")
        ax.legend(fontsize=8,loc="lower left")
    else:
        ax.text(.5,.5,"No negative-decay survivor",ha="center",va="center",transform=ax.transAxes)
    ax.set_xlabel("x");ax.grid(alpha=.18,which="both")
    ax=axes[2]
    for ctrl,color in zip(final["density_matched_delayed_controls"],["#aa4338","#bd8122","#7353a4"]):
        points=sorted(map(int,ctrl["complete_moments"]))
        ratio=[number(ctrl["complete_moments"][str(X)]["A2"])/number(ctrl["complete_moments"][str(X)]["D"]) for X in points]
        ax.plot(points,ratio,"o-",color=color,label=r"$\delta="+ctrl["delta"]+r"$, pole at $1-\delta$")
    ax.axhline(1,color="#777777",linestyle="--",label=r"$A_2=D$ reference")
    ax.set_yscale("log");ax.set(xlabel="Complete window start X",ylabel=r"$A_2(X)/D(X)$",title="Controls with identical prime support")
    ax.legend(fontsize=8,loc="upper left");ax.grid(alpha=.18,which="both")
    fig.suptitle("Actual-prime signed bounds, fractional decay leads, and density-matched false controls",fontsize=13)
    fig.supxlabel("All-scale signed calibrations recover exponent 1. Every RH-strength uniform estimate remains unproved.",fontsize=10)
    for ext in ("png","pdf"):fig.savefig(directory/f"prime_twist_evidence.{ext}",dpi=180)
    plt.close(fig)
    print("Saved prime_twist_evidence.pdf and .png",flush=True)


if __name__=="__main__":main()
