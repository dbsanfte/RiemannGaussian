#!/usr/bin/env python3
"""Finite held-out family evidence and the charged cost of small amplitudes."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import flint
from fractional_remainder_report import summary,load_latest
from mertens_limit_report import load_latest as load_limits
from stable_scale_report import BASE,read,sha


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run-dir");args=ap.parse_args()
    directory=Path(args.run_dir).resolve() if args.run_dir else Path(load_latest()["run_directory"])
    r=summary(directory);cases=read(directory/"final_cases.json");final=read(directory/"final_evaluation.json")
    limits=load_limits();rejected=set()
    if limits["status"]!="not_run" and Path(limits["source_run"])==directory:
        rejected={row["candidate"]["id"] for row in limits["known_false_original_finite_survivors"]}
    selected=[]
    for rate in range(4):
        pool=[row for row in r["archive_results"] if row["candidate"]["id"] not in rejected and row["candidate"]["transfer"]["RH_sufficient_if_uniform"] and row["program"]["parameter_vanishing_order"]==rate and row["candidate"].get("log_reciprocal_cost") is not None]
        if pool:selected.append(min(pool,key=lambda row:row["candidate"]["log_reciprocal_cost"]))
    flint.ctx.prec=256;fig,axes=plt.subplots(1,3,figsize=(14.6,4.7));observations=[]
    colors=["#3067a5","#dd8d20","#389267","#a25493"]
    for row in selected:
        p,c=row["program"],row["candidate"];rate=p["parameter_vanishing_order"];color=colors[rate];ratios=[]
        for q in cases["qs"]:
            a=flint.arb(1)/(max(1,p["degree"])*q);values=[]
            for n in cases["integers"]:
                text=final["program_responses"][p["id"]][f"{q}:{n}"]
                C=Q(c["constant"]);th=Q(c["theta"]);ka=Q(c["parameter_power"]);ell=Q(c["log_power"])
                B=(flint.arb(C.numerator)/C.denominator)*a**(flint.arb(ka.numerator)/ka.denominator)*flint.arb(n)**(flint.arb(th.numerator)/th.denominator)*(flint.arb.const_e()+n).log()**(flint.arb(ell.numerator)/ell.denominator)
                values.append(float((abs(flint.arb(text))/B).upper()))
            ratios.append(max(values))
        axes[0].plot(cases["qs"],ratios,"o-",color=color,label=f"r={rate}")
        costs=c["recovery_cost"]["parameter_observers"];qq=[];amp=[];bound=[]
        for item in costs:
            z=item["numerator_ball"];v=flint.acb(flint.arb(z["real"]),flint.arb(z["imag"]))
            qq.append(item["q"]);amp.append(float(v.abs_upper()));bound.append(float(flint.arb(item["conditional_reciprocal_zeta_bound_ball"]).upper()))
        axes[1].plot(qq,amp,"o-",color=color,label=f"r={rate}")
        axes[2].plot(qq,bound,"o-",color=color,label=f"r={rate}")
        observations.append({"program_id":p["id"],"candidate_id":c["id"],"exact_parameter_order":rate,
            "final_q":cases["qs"],"maximum_fresh_integer_ratio_by_q":ratios,"native_cost_q":qq,"native_numerator_upper":amp,"conditional_reciprocal_zeta_bound_upper":bound})
    axes[0].axhline(1,color="#b44940",ls="--",lw=1,label="frozen bound")
    axes[0].set(title="Fresh integer comparisons",ylabel="largest observed / fitted bound",xlabel="order parameter q",xscale="log")
    axes[1].set(title="Entire numerator at 5/8 + 16i",ylabel="certified numerator magnitude",xlabel="order parameter q",xscale="log",yscale="log")
    axes[2].set(title="Full conditional recovery cost",ylabel="bound on |1 / zeta(s)|, if uniform",xlabel="order parameter q",xscale="log",yscale="log")
    for ax in axes:ax.grid(alpha=.2);ax.legend(fontsize=8)
    fig.suptitle("Fractional arithmetic remainders: cancellation order is charged in recovery",fontsize=13,y=.98)
    caption=(f"r is the exact small-order vanishing order; a_q=1/(max(1,D) q). All {len(cases['integers'])} fresh integer scales enter each left-panel maximum.\n"
        f"Finite parameter success does not prove a bound for every n and q. {len(rejected)} source leads rejected by the later named-import limit gate are excluded.\n"
        "The right panel includes the denominator and unit correction; all its bounds are conditional.")
    fig.text(.5,.025,caption,ha="center",fontsize=9);fig.tight_layout(rect=(0,.12,1,.92))
    for ext in ["png","pdf"]:fig.savefig(directory/f"fractional_remainder_evidence.{ext}",dpi=170)
    record={"source_final_sha256":sha(directory/"final_evaluation.json"),"source_archive_sha256":sha(directory/"archive.json"),
        "all_fresh_scales_enter_each_maximum":True,"observations":observations,"finite_parameter_grid_is_not_uniform_evidence":True,
        "native_query":["5/8","16"],"right_panel_is_conditional":True,"RH_proved":False,
        "later_limit_gate_verification_sha256":limits.get("verification_sha256") if rejected else None,
        "later_rejected_source_candidate_ids_excluded":sorted(rejected)}
    (directory/"plot_observations.json").write_text(json.dumps(record,indent=2)+"\n")
    print("Saved standalone PNG/PDF fractional remainder evidence",flush=True)


if __name__=="__main__":main()
