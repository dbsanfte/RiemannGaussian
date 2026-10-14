"""Finite success of a globally false target and its unproved log-loss repair."""
from fractions import Fraction as Q
from pathlib import Path
import json
import flint
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from check_prime_twists import real,sha,digest
from prime_oscillation_report import load_latest


def avalue(c):
    A=c["offset"];return real(A["value"]) if A["kind"]=="rational" else flint.arb(A["value_ball"])


def main():
    flint.ctx.prec=384;r=load_latest();directory=Path(r["run_directory"])
    rows=r["repaired_uniform_proof_obligations"]
    if not rows:raise ValueError("A finite repair is required for this comparison figure")
    row=sorted(rows,key=lambda row:row["candidate"]["id"])[0];new=row["candidate"]
    rejected_id=row["rejected_source_candidate_id"]
    old=next(item["candidate"] for item in r["known_false_finite_survivors"] if item["candidate"]["id"]==rejected_id)
    final=json.loads((directory/"final_evaluation.json").read_text());values=final["values"][new["program_id"]]
    ns=sorted(map(int,values));ratios=[];failure_counts=[]
    for c in (old,new):
        A=avalue(c);curve=[];fails=unknown=0
        for n in ns:
            v=abs(flint.arb(values[str(n)])-A)
            bound=real(c["constant"])*real(n)**real(c["theta"])*(flint.arb.const_e()+n).log()**real(c["log_power"])
            if v>bound:fails+=1
            elif not v<=bound:unknown+=1
            curve.append(float((v/bound).upper()))
        ratios.append(curve);failure_counts.append({"candidate_id":c["id"],"failures":fails,"unresolved":unknown})
    block=max(1,(len(ns)+239)//240);xx=[];maxima=[[],[]]
    for k in range(0,len(ns),block):
        segment=ns[k:k+block];xx.append((segment[0]+segment[-1])/2)
        for j in range(2):maxima[j].append(max(ratios[j][k:k+block]))
    plt.rcParams.update({"font.size":10,"axes.spines.top":False,"axes.spines.right":False})
    fig,axes=plt.subplots(1,2,figsize=(12.7,4.8),constrained_layout=True)
    for j,ax in enumerate(axes):
        ax.plot(xx,maxima[j],color="#2563a6",linewidth=1.4,label="Maximum observed ratio in each block")
        ax.axhline(1,color="#b44a3e" if j==0 else "#47836a",linestyle="--",label="Proposed bound")
        ax.set(xlabel="Fresh integer x",ylabel="Absolute error / proposed bound",ylim=(0,1.1))
        ax.grid(alpha=.2);ax.legend(fontsize=9,loc="upper left")
    axes[0].set_title(r"Pure $\sqrt{x}$: uniform claim is proved false")
    axes[1].set_title(r"$\sqrt{x}\log(e+x)$: uniform claim is unproved")
    fig.suptitle("A false all-scale estimate can pass exhaustive finite tests",fontsize=13)
    fig.supxlabel(f"All {len(ns):,} fresh points represented by block maxima. Rejection on the left uses the named oscillation theorem.",fontsize=10)
    for ext in ("pdf","png"):fig.savefig(directory/f"prime_oscillation_evidence.{ext}",dpi=180,facecolor="white")
    plt.close(fig)
    observations={"source_final_sha256":sha(directory/"final_evaluation.json"),"interval":r["fresh_integer_interval"],"complete_interval_points":len(ns),
        "comparisons":failure_counts,"every_observation_represented_in_block_maxima":True,"blocks":len(xx),
        "old_target_globally_false_by_named_oscillation_import":True,"new_target_uniform_proof_missing":True,"RH_proved":False}
    (directory/"plot_observations.json").write_text(json.dumps(observations,indent=2)+"\n")
    print("Saved oscillation evidence; full fresh-interval failure counts:",failure_counts,flush=True)


if __name__=="__main__":main()
