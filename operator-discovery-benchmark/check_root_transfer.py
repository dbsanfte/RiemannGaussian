#!/usr/bin/env python3
"""Independent exact verifier using partitions of exponent bits.

Does not import FLINT, the root-transfer polynomial generator, or its
Bernstein implementation. Recomputes every coefficient and rational witness.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from math import comb
from pathlib import Path


def trim(values):
    while len(values)>1 and not values[-1]:
        values.pop()
    return values


def poly_add(left,right):
    result=[Q(0)]*max(len(left),len(right))
    for i,x in enumerate(left):result[i]+=x
    for i,x in enumerate(right):result[i]+=x
    return trim(result)


def poly_mul(left,right):
    result=[Q(0)]*(len(left)+len(right)-1)
    for i,x in enumerate(left):
        for j,y in enumerate(right):result[i+j]+=x*y
    return trim(result)


def partitions(bits):
    if not bits:
        yield []
        return
    first,*remaining=bits
    for existing in partitions(remaining):
        yield [[first]]+[list(block) for block in existing]
        for k in range(len(existing)):
            result=[list(block) for block in existing]
            result[k].append(first)
            yield result


def local_polynomials(degree):
    d=[[Q(0)],[Q(1)]]
    for e in range(2,degree+1):
        d.append([x/e for x in poly_mul(d[-1],[Q(e-1),Q(1)])])
    result=[[Q(1)]]
    for e in range(1,degree+1):
        bits=[1<<j for j in range(e.bit_length()) if e & (1<<j)]
        polynomial=[Q(0)]
        for partition in partitions(bits):
            term=[Q(1)]
            for j in range(len(partition)):term=poly_mul(term,[Q(1),Q(-j)])
            for block in partition:term=poly_mul(term,d[sum(block)])
            polynomial=poly_add(polynomial,term)
        result.append(polynomial)
    return result


def bernstein(poly,lower,upper):
    degree=len(poly)-1
    c=[sum((poly[k]*comb(k,j)*lower**(k-j)*(upper-lower)**j
            for k in range(j,degree+1)),Q(0)) for j in range(degree+1)]
    return [sum((c[j]*Q(comb(k,j),comb(degree,j)) for j in range(k+1)),Q(0))
            for k in range(degree+1)]


def main():
    output=Path(__file__).resolve().parent/"transfer-results"
    source=json.loads((output/"root_transfer_probe.json").read_text())
    degree=len(source["all_polynomial_coefficients"])-1
    expected=local_polynomials(degree)
    stored=[trim([Q(x) for x in coefficients] or [Q(0)]) for coefficients in source["all_polynomial_coefficients"]]
    polynomial_agreement=expected==stored
    witnesses=[]
    intervals=[]
    for record in source["uniform_certificate"]:
        lower,upper=map(Q,record["alpha_interval"])
        intervals.append((lower,upper))
        radius=Q(record["radius"])
        finite=Q(0)
        bounds_agree=True
        for detail in record["coefficient_bounds"]:
            e=detail["exponent"]
            correction=poly_add(expected[e],[-x for x in expected[e-1]])
            coefficients=bernstein(correction,lower,upper)
            cap=max(map(abs,coefficients))
            bounds_agree &= [str(x) for x in coefficients]==detail["bernstein_coefficients"]
            bounds_agree &= cap==Q(detail["coefficient_bound"])
            finite+=cap*radius**e
        tail=2*radius**(degree+1)/(1-radius)
        total=finite+tail
        witnesses.append({"alpha_interval":record["alpha_interval"],
                          "all_bernstein_coefficients_agree":bool(bounds_agree),
                          "finite_sum_agrees":finite==Q(record["finite_sum_bound"]),
                          "tail_agrees":tail==Q(record["uniform_tail_bound"]),
                          "rational_total_agrees":total==Q(record["total_bound"]),
                          "strict_zero_free_bound_proved":total<1 and radius**2>Q(1,2)})
    intervals.sort()
    covered=(intervals[0][0]==0 and intervals[-1][1]==Q(1,2)
             and all(a[1]==b[0] for a,b in zip(intervals,intervals[1:])))
    passed=polynomial_agreement and covered and all(all(x for k,x in record.items() if k!="alpha_interval") for record in witnesses)
    result={"independent_set_partition_polynomials_agree":polynomial_agreement,
            "alpha_domain_completely_covered":covered,"witnesses":witnesses,"all_passed":passed,
            "historical_novelty_is_not_certified":True}
    (output/"root_transfer_verification.json").write_text(json.dumps(result,indent=2)+"\n")
    print(f"Independent root-transfer polynomials and uniform certificates: passed={passed}")
    assert passed


if __name__=="__main__":main()
