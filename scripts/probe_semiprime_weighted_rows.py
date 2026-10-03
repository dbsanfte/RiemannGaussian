#!/usr/bin/env python3
"""Retained adjacent-row cancellations and a separate private-order diagnostic.

The paid source takes only N and a public base, reuses the original giant
powers, builds all four adjacent center combinations and runs guarded trace
extraction. The 90-bit witness search is explicitly reference-only. Neither
its search nor its selected pair is a source runtime or a coverage proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import groupby
import json
import math
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-guarded-trace-certificate-audit.json"
REPLAY_ID = 202610033205
TRACE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_trace_rows.py"))
FAMILY, DERIVATIVE = TRACE["FAMILY"], TRACE["DERIVATIVE"]
IntegerLedger, ScalarLedger, BATCH = TRACE["IntegerLedger"], TRACE["ScalarLedger"], TRACE["BATCH"]


def weighted_packets(packets, m, integers=None):
    """Same adjacency and SS,SL,LS,LL order as the Lean constructor."""
    mul = (lambda x,y:x*y) if integers is None else integers.mul
    add = (lambda x,y:x+y) if integers is None else integers.add
    for j, group in groupby(packets, key=lambda w:w["j"]):
        prior, iterator = None, iter(group)
        for first in iterator:
            second = next(iterator)
            current = (first,second)
            assert first["a"] == second["a"] and first["t"] == second["t"]
            if prior is not None:
                for left in prior:
                    for right in current:
                        e = add(mul(right["t"],left["exponent"]),-mul(left["t"],right["exponent"]))
                        d = add(mul(right["t"],left["a"]),-mul(left["t"],right["a"]))
                        assert abs(d) == m and e % m == 0
                        yield dict(j=j,left=left,right=right,exponent=e,determinant=d)
            prior = current


def weighted_rows_source(n, alpha=2):
    """Only public inputs enter; every constructor and recovery is timed."""
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics, originals, powers, buckets, m, values = Counter(), [], {}, {}, None, []

    def finish(factor, stage, witness=None):
        if witness is not None and "original_root" in witness:
            witness = dict(witness, weighted_packet_bucket=buckets[witness["original_root"]])
            if "other_original_root" in witness:
                witness["other_weighted_packet_bucket"] = buckets[witness["other_original_root"]]
        return dict(N=n,factor=factor,stage=stage,modulus=m,witness=witness,
            original_packet_count=len(originals),weighted_packet_count=metrics["retained_weighted_packets"],
            distinct_weighted_units=len(buckets),evaluated_trace_derivatives=len(values),
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics,**integers.stats(),**ring.stats(),**batch.stats()),
            retains_original_and_weighted_packet_buckets=True,constructed_pair_matrix=False,
            uses_original_giant_powers_and_short_weights=True,is_complete_factorizer=False,
            is_bit_complexity_certificate=False,is_formal_native_machine_refinement=False)

    root = integers.sqrt(n)
    if integers.mul(root,root) == n and 1 < root < n:
        return finish(root,"public-square")
    common = integers.gcd(alpha,n)
    if 1 < common < n:
        return finish(common,"public-base-gcd")
    if common != 1:
        return finish(None,"inconclusive-base")
    m = FAMILY["first_public_prime"](n,integers,metrics)
    common = integers.gcd(m,n)
    if 1 < common < n:
        return finish(common,"public-modulus-gcd")
    if common != 1:
        return finish(None,"inconclusive-modulus")
    inverse = integers.divmod(integers.inverse(alpha,n),n)[1]
    for packet in FAMILY["public_packets"](n,m,integers,metrics):
        e = packet["exponent"]
        value = ring.power(alpha if e >= 0 else inverse,abs(e))
        integers.charge("public_original_power_lookup_operands",value)
        metrics["original_giant_powers"] += 1
        powers[e] = value
        originals.append(packet)
    units = list(dict.fromkeys(powers.values()))
    inverses = TRACE["RECIPROCAL"]["batch_inverse"](n,units,integers,ring,metrics) if units else []
    inverse_by_unit = dict(zip(units,inverses))
    for packet in weighted_packets(originals,m,integers):
        left,right = packet["left"],packet["right"]
        x,y = powers[left["exponent"]],powers[right["exponent"]]
        integers.charge("public_original_power_lookup_operands",left["exponent"],right["exponent"])
        value = ring.mul(ring.power(x,right["t"]),ring.power(inverse_by_unit[y],left["t"]))
        metrics["short_weighted_group_powers"] += 2
        metrics["weighted_group_products"] += 1
        integers.charge("public_weighted_root_lookup_operands",value)
        buckets.setdefault(value,[]).append(packet)
        metrics["retained_weighted_packets"] += 1
    assert metrics["retained_weighted_packets"] <= 2*len(originals)
    factor,stage,witness,_,_,values = TRACE["extract_trace_rows"](
        n,list(buckets),integers,ring,batch,metrics)
    count = sum(metrics[k] for k in ("raw_sign_endpoint_gcd_queries","global_trace_guard_gcd_queries",
        "derivative_gcd_queries","selected_row_gcd_queries"))
    assert count <= 5*metrics["retained_weighted_packets"] <= 10*len(originals)
    return finish(factor,stage,witness)


def reference_residue_packets(n,m,j):
    """Uncharged single public residue; private residue choice is diagnostic."""
    low,middle,high = math.isqrt(n//2),math.isqrt(n),math.isqrt(2*n)
    inverse,square = pow(j,-1,m),m*m
    r0,r1,x,y,negative = m,n*inverse*inverse%m,0,1,False
    pairs = []
    while r1:
        pairs.append((-r1 if negative else r1,y))
        quotient,remainder = divmod(r0,r1)
        pairs.extend(((r0-k*r1 if negative else -(r0-k*r1)),x+k*y)
            for k in range(1,quotient))
        r0,r1,x,y,negative = r1,remainder,y,x+quotient*y,not negative
    for a,t in pairs:
        D,rem = divmod(n*t-j*j*a,m)
        assert rem == 0
        b = (-inverse*D+m//2)%m-m//2
        c,rem = divmod(D+j*b,m)
        assert rem == 0
        v,exponent = b*m-2*a*j,n*t+a+b*m-2*a*j
        for orientation,A,B in (("smaller-factor",low+middle,middle+high),
                ("larger-factor",middle+high,low+middle)):
            H = a*A+t*B+2*v
            shift = (H+square)//(2*square)
            yield dict(j=j,a=a,b=b-shift*m,c=c-shift*j,t=t,shift=shift,
                center_orientation=orientation,exponent=exponent-shift*square)


def validate_algebra(rnd):
    checks = Counter()
    for _ in range(192):
        n,m = rnd.randrange(100,10000),rnd.choice((7,11,13,17,19))
        if math.gcd(n,m) != 1:
            continue
        reference = list(DERIVATIVE["reference_packets"](n,m))
        local = [w for j in range(1,m) for w in reference_residue_packets(n,m,j)]
        assert local == reference
        integers,metrics = IntegerLedger(),Counter()
        actual = list(FAMILY["public_packets"](n,m,integers,metrics))
        for native,ref in zip(actual,reference,strict=True):
            assert {k:native[k] for k in ref} == ref
        for packet in weighted_packets(reference,m):
            left,right = packet["left"],packet["right"]
            determinant,B = packet["determinant"],right["t"]*left["b"]-left["t"]*right["b"]
            d,rem = divmod(determinant,m)
            assert rem == 0 and abs(d) == 1
            h,rem = divmod(B-left["j"]*d,m)
            assert rem == 0
            assert packet["exponent"] == determinant*(1-2*left["j"])+m*B
            for X in (-17,0,23):
                evaluate = lambda w:w["a"]*X*X+w["b"]*X+w["c"]
                assert right["t"]*evaluate(left)-left["t"]*evaluate(right) == \
                    (m*X+left["j"])*(d*X+h)
                checks["integral_quadratic_factorizations"] += 1
            if math.gcd(2,n) == 1:
                value = pow(2,packet["exponent"],n)
                reuse = pow(pow(2,left["exponent"],n),right["t"],n)*\
                    pow(pow(2,right["exponent"],n),-left["t"],n)%n
                assert value == reuse
                checks["weighted_group_power_identities"] += 1
        checks["complete_public_constructor_comparisons"] += 1
    return dict(checks)


def physical_indices(p,q,m):
    """Private factors enter only here; these are not source search indices."""
    result = []
    for f in (p,q):
        packets = list(reference_residue_packets(p*q,m,f%m))
        quotient = f//m
        indices = {}
        for w in packets:
            value = w["a"]*quotient*quotient+w["b"]*quotient+w["c"]
            index,rem = divmod(value,f)
            assert rem == 0
            indices[id(w)] = index
        best = {}
        for w in weighted_packets(packets,m):
            left,right = w["left"],w["right"]
            index = right["t"]*indices[id(left)]-left["t"]*indices[id(right)]
            key = left["center_orientation"]+"/"+right["center_orientation"]
            best[key] = min(best.get(key,abs(index)),abs(index))
        result.append(dict(reference_factor=f,correct_residue=f%m,
            original_min_abs_index=min(map(abs,indices.values())),weighted_min_abs_indices=best))
    return dict(N=p*q,modulus=m,is_N_only_source=False,
        is_factorization_runtime_measurement=False,correct_residue_diagnostics=result)


def reference_weighted_witness():
    """Private orders select a proof witness from the N-only packet stream."""
    p,q,m = 24862649616491,31697997935819,30403
    n,dP,dQ = p*q,p-1,q-1
    seenP,seenQ,counts = {},{},Counter()

    def compact(w):
        x,y = w["left"],w["right"]
        return (w["exponent"],w["j"],x["a"],x["t"],x["center_orientation"],
            y["a"],y["t"],y["center_orientation"])

    def recover(key):
        return next(w for w in weighted_packets(reference_residue_packets(n,m,key[1]),m)
            if compact(w) == key)

    for w in weighted_packets(DERIVATIVE["reference_packets"](n,m),m):
        e = w["exponent"]
        counts["weighted_packets_examined"] += 1
        for factor,order,other_order,seen in ((p,dP,dQ,seenP),(q,dQ,dP,seenQ)):
            r = e%order
            fold = min(r,(-r)%order)
            old = seen.get(fold)
            if old is None:
                seen[fold] = compact(w)
                continue
            sign = 1 if r == old[0]%order else -1
            if (e-sign*old[0])%other_order == 0:
                continue
            first = recover(old)
            values = [pow(2,z,n) for z in (old[0],e)]
            signal = (values[1]-values[0])%n if sign == 1 else (values[1]*values[0]-1)%n
            divisor = math.gcd(signal,n)
            assert divisor == factor and 1 < divisor < n
            return dict(N=n,modulus=m,reference_p=p,reference_q=q,
                reference_actual_orders=[dP,dQ],is_N_only_source=False,
                is_factorization_runtime_measurement=False,orders_kernel_checked=False,
                channel="ordinary" if sign == 1 else "reciprocal",counts=dict(counts),
                first_packet=first,second_packet=w,public_unit_values=values,
                signal=signal,factor=divisor,complete_native_weighted_source_replayed=False)
    raise AssertionError("expected literal weighted control was not found")


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"RiemannGaussian/SemiprimeWeightedRows.lean",
        "scripts/CheckSemiprimeWeightedRows.lean","scripts/probe_semiprime_weighted_rows.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--checked-declarations",type=int,default=0)
    parser.add_argument("--checked-theorems",type=int,default=0)
    parser.add_argument("--checked-explicit",type=int,default=0)
    args = parser.parse_args()
    sources,rnd = source_inventory(),random.Random(REPLAY_ID)
    algebra = validate_algebra(rnd)
    pairs = [(101,103),(101,101),(3,1000003),(5,2000003)]
    for _ in range(28):
        p = int(nextprime(rnd.randrange(50,4000)))
        q = int(nextprime(rnd.randrange(p+1,2*p)))
        pairs.append((p,q))
    native = []
    for p,q in pairs:
        result = weighted_rows_source(p*q)
        if result["factor"] is not None:
            assert 1 < result["factor"] < p*q and p*q % result["factor"] == 0
        native.append(result)
    control = weighted_rows_source(14799739*24991489)
    assert control["factor"] is not None
    physical = [physical_indices(p,q,m) for p,q,m in (
        (14799739,24991489,269),(39167077933,64308254573,3691),
        (24862649616491,31697997935819,30403))]
    print(json.dumps(dict(progress="weighted-public-source-controls-completed",
        native_cases=len(native),native_factors=sum(r["factor"] is not None for r in native),
        control_factor=control["factor"],control_milliseconds=control["milliseconds"])),flush=True)
    witness = reference_weighted_witness()
    assert [witness["first_packet"]["exponent"],witness["second_packet"]["exponent"]] == \
        [966926180542225069170,5440830797789338080020]
    assert source_inventory() == sources,"source changed during replay"
    checked = args.checked_declarations > 0 and args.checked_theorems > 0
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,
        scope="Adjacent weighted quadratic cancellations with original carriers and exact centers",
        algebra_oracles=algebra,small_N_only_sources=native,paid_control=control,
        physical_index_diagnostics=physical,reference_only_90bit_witness=witness,
        full_native_90bit_weighted_source_replayed=False,
        kernel_checked_public_90bit_positive_control=checked,
        original_90bit_failure_remains_native_only=True,
        lean_validation=dict(separately_completed_scoped_gates=checked,
            strict_leaf_and_root=checked,namespace_linters=14 if checked else 0,
            linter_errors=0 if checked else None,all_module_declarations=args.checked_declarations,
            explicit_declarations=args.checked_explicit,
            generated_declarations=args.checked_declarations-args.checked_explicit,
            theorem_and_helper_declarations=args.checked_theorems,
            permitted_transitive_axioms=["propext","Classical.choice","Quot.sound"]),
        kernel_components=dict(exact_N_term_cancellation=True,integral_public_linear_companion=True,
            original_power_reuse=True,exact_two_center_index_identity=True,
            same_center_window_obstruction=True,public_denominator_bound=True,
            twice_original_packet_count=True,ten_recovery_gcd_queries_per_original_packet=True,
            complete_guarded_public_weighted_positive_control=True),
        is_complete_factorizer=False,is_bit_complexity_certificate=False,
        is_formal_native_machine_refinement=False,one_sixth_guarantee="OPEN",
        limitations="Lean certifies exact weighted cancellation, the surviving public linear direction, retained signed rounding errors, the complete N-only adjacent four-center constructor, sound guarded extraction, linear packet/query bounds and a complete public positive control on the inherited 90-bit failure input. The positive control has no private witness as an algorithm input. The native order-based search only locates that proof witness; it is not a paid N-only factorizer replay. The inherited original-family exhaustion stays native-only. New paid native sources cover only the listed small controls and first earlier failure input; their ordinary integer/ring ledgers, dictionaries and polynomial engine are not formal deterministic bit machines. Correct-residue physical diagnostics explicitly use private factors. Same-center obstruction bounds only the literal index, not every modular alias or any other algorithm. Cross-center signals demonstrate additional information, not universal coverage. Arbitrary factor ratios, all public construction costs, polynomial/table bit bounds and every-run guaranteed sixth-root factorization remain open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),native_cases=len(native),
        native_factors=sum(r["factor"] is not None for r in native),
        reference_weighted_90bit_factor=witness["factor"],full_native_90bit_replayed=False,
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
