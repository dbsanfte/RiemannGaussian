#!/usr/bin/env python3
"""Plot complete-window evidence; finite cancellation is never a proof."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import math
import flint
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from prime_discrepancy_report import summary
from stable_scale_report import read


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run-dir",type=Path,required=True)
    directory=parser.parse_args().run_dir.resolve();result=summary(directory)
    baseline=next(r for r in result["surviving_uniform_proof_obligations"] if r["program"]["atoms"]==[["1","1"]]
        and -1<Q(r["candidate"]["rho"])<0)
    pid=baseline["program"]["id"];candidate=baseline["candidate"]
    data={}
    for name in ("discovery_data.json","validation_data.json"):
        data.update(read(directory/name)["complete_moments"][pid])
    final=read(directory/"final_evaluation.json");data.update(final["actual_moments"][pid])
    rows=sorted((int(X),{k:float(flint.arb(v).mid()) for k,v in r.items()}) for X,r in data.items())
    xs=[X for X,r in rows];A=[r["A2"] for X,r in rows];D=[r["D"] for X,r in rows]
    rho,gamma,B=(float(Q(candidate[k])) for k in ("rho","gamma","constant"))
    density=float(Q(candidate["transfer"]["diagonal_coefficient"]))
    fig,(left,right)=plt.subplots(1,2,figsize=(12,4.7),constrained_layout=True)
    left.loglog(xs,A,"o-",markersize=3,label="Actual signed error energy A2")
    left.loglog(xs,D,"s-",markersize=3,label="Actual Gram diagonal D")
    left.loglog(xs,[density*X*X/math.log(math.e+X) for X in xs],"--",label="Proved all-scale diagonal bound")
    left.loglog(xs,[(1+rho)*r["D"]+B*X**gamma for X,r in rows],":",linewidth=2,label="Learned energy bound: uniform proof missing")
    left.set(xlabel="Window start X (whole interval [X, 2X])",ylabel="Quadratic energy",title="Prime inputs proved; signed cancellation conjectural")
    left.grid(True,which="both",alpha=.2);left.legend(fontsize=8)
    right.semilogx(xs,[r["C_off"]/r["D"] for X,r in rows],"o-",markersize=3,label="Actual prime-power discrepancies")
    right.semilogx(xs,[rho+B*X**gamma/r["D"] for X,r in rows],":",linewidth=2,label="Learned signed bound / D")
    for name,label in (("positive_support","Positive-support control"),("delayed_support","Actual through 128, then positive")):
        control=sorted((int(X),{k:float(flint.arb(v).mid()) for k,v in r.items()}) for X,r in final["support_control_moments"][name][pid].items())
        right.semilogx([X for X,r in control],[r["C_off"]/r["D"] for X,r in control],"x--",label=label)
    right.set_yscale("symlog",linthresh=1)
    right.axhline(0,color="black",linewidth=.6)
    right.set(xlabel="Window start X",ylabel="Signed pair contribution C_off / D",title="Controls do not receive the prime-density theorem")
    right.grid(True,which="both",alpha=.2);right.legend(fontsize=8)
    fig.suptitle("Finite evidence only: every uniform signed pair premise remains unproved",fontsize=12)
    for suffix in ("pdf","png"):
        fig.savefig(directory/f"prime_discrepancy_evidence.{suffix}",dpi=180)
    plt.close(fig)
    print("Saved standalone prime-discrepancy evidence PDF/PNG",flush=True)


if __name__=="__main__":main()
