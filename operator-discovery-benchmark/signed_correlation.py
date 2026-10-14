#!/usr/bin/env python3
"""Exact quadratic correlation obligations for signed scale operators.

This diagnostic uses already inspected, independently checked moments.
The diagonal bound is universal. No off-diagonal bound is asserted.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(data): return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(",", ":"),allow_nan=False).encode()).hexdigest()


def square_prefix(mu):
    counts=[0]*len(mu); weighted=[0]*len(mu)
    for n in range(1,len(mu)):
        counts[n]=counts[n-1]+mu[n]**2
        weighted[n]=weighted[n-1]+n*mu[n]**2
    return counts,weighted


def integrated_ramps(mu,counts,weighted,d,t,power):
    """Sum mu(n)^2 times the primitive of phi_n(t/d)^power."""
    n,r=divmod(t,d)
    result=t*counts[n]-d*weighted[n]+Q(d*counts[n],power+1)
    if r: result+=Q(mu[n+1]**2*r**(power+1),(power+1)*d**power)
    return result


def one_ramp(d,t,power):
    if t>=d: return Q(t-d)+Q(d,power+1)
    return Q(t**(power+1),(power+1)*d**power)


def first_coefficient_energy(base,p,X):
    boundaries=sorted({X,2*X}|{base**k for k in range(len(p)) if X<base**k<2*X})
    result=Q(0)
    for left,right in zip(boundaries,boundaries[1:]):
        middle=Q(left+right,2); a=b=Q(0)
        for k,c in enumerate(p):
            d=base**k
            if middle>=d: a+=c
            else: b+=c/d
        result+=a*a*(right-left)+a*b*(right**2-left**2)+b*b*Q(right**3-left**3,3)
    return result


def diagonal_moment(mu,counts,weighted,base,encoded,X):
    if type(base) is not int or base<2 or type(X) is not int or X<1:
        raise ValueError("An integer base>=2 and integer scale>=1 are required")
    p=[Q(c) for c in encoded]
    if not p or p[0]!=1: raise ValueError("The scale polynomial must have constant one")
    total=Q(0); previous=Q(0); virtual_first=Q(0)
    for k,c in enumerate(p):
        d=base**k
        I1=integrated_ramps(mu,counts,weighted,d,2*X,1)-integrated_ramps(mu,counts,weighted,d,X,1)
        I2=integrated_ramps(mu,counts,weighted,d,2*X,2)-integrated_ramps(mu,counts,weighted,d,X,2)
        total+=c*c*I2+2*c*previous*I1
        first1=one_ramp(d,2*X,1)-one_ramp(d,X,1)
        first2=one_ramp(d,2*X,2)-one_ramp(d,X,2)
        virtual_first+=c*c*first2+2*c*previous*first1
        previous+=c
    return total+mu[1]**2*(first_coefficient_energy(base,p,X)-virtual_first)


def diagnostic(directory,output):
    # A prime sieve belongs to the evaluator, and cannot nominate an operator.
    from check_signed_control import independent_inverse
    from mellin_search_report import summary
    directory=Path(directory).resolve(); summary(directory)
    source=read(directory/"final_evaluation.json"); cases=read(directory/"final_cases.json")
    mu,M=independent_inverse(source["coefficient_cutoff"]); counts,weighted=square_prefix(mu)
    assert digest(mu)==source["inverse_coefficient_sha256"]
    archive=read(directory/"archive.json"); records=[]
    for row,result in zip(archive["archive"],source["records"]):
        p=row["program"]; coefficients=[Q(c) for c in p["polynomial"]]
        S=sum(abs(c) for c in coefficients)
        observations=[]
        for X in cases["scales"]:
            E=Q(result["exact_complete_window_moments"][str(X)]["2"])
            D=diagonal_moment(mu,counts,weighted,p["base"],coefficients,X)
            assert 0<=D<=2*S*S*X*X
            observations.append({"X":X,"exact_signed_energy":str(E),"exact_diagonal":str(D),
                                 "exact_signed_off_diagonal":str(E-D),
                                 "energy_over_X_squared":str(E/(X*X)),
                                 "off_diagonal_over_X_squared":str((E-D)/(X*X))})
        records.append({"program":p,"diagonal_all_scale_upper_coefficient":str(2*S*S),
                        "observations":observations,
                        "missing_uniform_signed_premise":"For every dyadic X>=1, the explicit off-diagonal sum is <= K X^2 for some finite K>=0",
                        "conditional_consequence":"A_2(X)<=(2*S^2+K)X^2 at every dyadic scale; RH follows when the ordinary-zeta multiplier is nonzero at every height Re(s)>=1/2",
                        "alternative_uniform_recurrence_premise":"At every dyadic X>=1, A_2(2X)-4*A_2(X)<=B*X^2 for some finite B>=0; this allows an X^2*log X bound and also suffices for RH with the zero bridge",
                        "off_diagonal_bound_proved":False})
    result={"source_run":str(directory),"source_final_sha256":sha(directory/"final_evaluation.json"),
            "source_verification_sha256":sha(directory/"verification.json"),"code_sha256":sha(Path(__file__)),
            "proof_sha256":sha(Path(__file__).with_name("signed_correlation_proof.txt")),
            "recurrence_code_sha256":sha(Path(__file__).with_name("signed_recurrence_transfer.py")),
            "recurrence_proof_sha256":sha(Path(__file__).with_name("signed_recurrence_proof.txt")),
            "purpose":"exact correlation decomposition of previously inspected complete moments; no reselection or fresh validation claim",
            "records":records,"uniform_signed_off_diagonal_controls_verified":[],"RH_proved":False}
    Path(output).write_text(json.dumps(result,indent=2)+"\n")
    return result


def load_latest(directory):
    if directory is None: return {"status":"not_run","uniform_signed_off_diagonal_controls_verified":[],"RH_proved":False}
    directory=Path(directory).resolve(); path=directory/"correlation_obligations.json"
    if not path.exists(): return {"status":"not_run","uniform_signed_off_diagonal_controls_verified":[],"RH_proved":False}
    data=read(path)
    assert data["source_final_sha256"]==sha(directory/"final_evaluation.json")
    assert data["source_verification_sha256"]==sha(directory/"verification.json")
    assert data["code_sha256"]==sha(Path(__file__))
    assert data["proof_sha256"]==sha(Path(__file__).with_name("signed_correlation_proof.txt"))
    assert data["recurrence_code_sha256"]==sha(Path(__file__).with_name("signed_recurrence_transfer.py"))
    assert data["recurrence_proof_sha256"]==sha(Path(__file__).with_name("signed_recurrence_proof.txt"))
    assert not data["RH_proved"] and data["uniform_signed_off_diagonal_controls_verified"]==[]
    return {"status":"exact_correlation_rewrite_and_conditional_recurrence_backend",
            "source_run":str(directory),"operators":len(data["records"]),
            "unconditional_theorem":"D(X)<=2*S^2*X^2 at every integer scale",
            "missing_signed_premise":"C_off(X)<=K X^2 at every dyadic scale, or an RH-sufficient global moment defect recurrence",
            "diagnostic_sha256":sha(path),"proof_sha256":data["proof_sha256"],
            "uniform_signed_off_diagonal_controls_verified":[],"RH_proved":False}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument("--source-run",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True); args=parser.parse_args()
    result=diagnostic(args.source_run,args.output)
    print("Exported exact signed-correlation obligations",len(result["records"]),"operators; off-diagonal controls remain unproved")
