#!/usr/bin/env python3
"""Private-order augmented coverage with disk-backed exact class sorting.

Two uint64 local coordinates encode each whole inverse class exactly.
The scratch table bounds Python-object growth; this still runs no public
factorizer and provides neither a Lean order certificate nor bit theorem.
"""
from __future__ import annotations

import argparse
from array import array
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import runpy
import tempfile

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-augmented-row-coverage-audit.json"
REPLAY_ID = 202610033207
AUGMENTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_augmented_row_coverage.py"))
COVERAGE,WEIGHTED = AUGMENTED["COVERAGE"],AUGMENTED["WEIGHTED"]
DTYPE = np.dtype([("fp",np.uint64),("qc",np.uint64),("fq",np.uint64)])


def distinct_changes(data,keys):
    count,previous = 0,None
    for start in range(0,len(data),1000000):
        block = data[start:start+1000000]
        changed = np.ones(len(block),dtype=bool)
        if len(block)>1:
            changed[1:] = False
            for key in keys:
                changed[1:] |= block[key][1:] != block[key][:-1]
        if previous is not None:
            changed[0] = any(int(block[key][0]) != previous[key] for key in keys)
        count += int(np.count_nonzero(changed))
        previous = {key:int(block[key][-1]) for key in keys}
    return count


def sorted_classify(es,dP,dQ,progress=False):
    assert 0<dP<2**64 and 0<dQ<2**64
    with tempfile.TemporaryDirectory(prefix="semiprime-signed-classes-") as scratch:
        path,buffer,rows = Path(scratch)/"classes.bin",array("Q"),0
        with path.open("wb") as sink:
            for e in es:
                ep,eq = e%dP,e%dQ
                opposite = (-ep)%dP
                fp,fq = min(ep,opposite),min(eq,(-eq)%dQ)
                qc = eq if ep<opposite else (-eq)%dQ if ep>opposite else fq
                buffer.extend((fp,qc,fq))
                rows += 1
                if len(buffer)>=300000:
                    sink.write(buffer.tobytes())
                    buffer = array("Q")
            if buffer:
                sink.write(buffer.tobytes())
        if rows==0:
            return COVERAGE["classify_exponents"]([],dP,dQ)
        data = np.memmap(path,dtype=DTYPE,mode="r+",shape=(rows,))
        if progress:
            print(json.dumps(dict(progress="reference-only-sort-P-start",rows=rows,
                scratch_bytes=rows*DTYPE.itemsize)),flush=True)
        data.sort(order=("fp","qc","fq"),kind="quicksort")
        whole = distinct_changes(data,("fp","qc"))
        pclasses = distinct_changes(data,("fp",))
        stats,previous = Counter(),None
        for start in range(0,rows,1000000):
            block = data[start:start+1000000]
            unique = np.ones(len(block),dtype=bool)
            if len(block)>1:
                unique[1:] = (block["fp"][1:]!=block["fp"][:-1]) | (block["qc"][1:]!=block["qc"][:-1])
            if previous is not None:
                unique[0] = (int(block["fp"][0]),int(block["qc"][0])) != previous
            ep,eq = block["fp"],block["qc"]
            plusP,plusQ = ep==0,eq==0
            minusP = (ep==dP//2) & (dP%2==0)
            minusQ = (eq==dQ//2) & (dQ%2==0)
            selfP,selfQ = plusP|minusP,plusQ|minusQ
            for key,mask in (("global_self_inverse_orbits",selfP&selfQ),
                    ("local_self_inverse_p_only",selfP&~selfQ),
                    ("local_self_inverse_q_only",selfQ&~selfP),
                    ("proper_plus_one_signs",plusP^plusQ),
                    ("proper_minus_one_signs",minusP^minusQ)):
                stats[key] += int(np.count_nonzero(unique&mask))
            previous = int(block["fp"][-1]),int(block["qc"][-1])
        if progress:
            print(json.dumps(dict(progress="reference-only-sort-Q-start",rows=rows,
                distinct_global_inverse_orbits=whole)),flush=True)
        data.sort(order=("fq","fp","qc"),kind="quicksort")
        qclasses = distinct_changes(data,("fq",))
        assert distinct_changes(data,("fp","qc"))==whole
        hit = whole>pclasses or whole>qclasses or stats["local_self_inverse_p_only"]>0 or stats["local_self_inverse_q_only"]>0
        endpoint = stats["proper_plus_one_signs"]+stats["proper_minus_one_signs"]>0
        return dict(stats,original_exponents=rows,duplicate_global_inverse_orbits=rows-whole,
            distinct_global_inverse_orbits=whole,folded_p_aliases=whole-pclasses,
            folded_q_aliases=whole-qclasses,
            distinct_signed_whole_values=2*whole-stats["global_self_inverse_orbits"],
            combined_signed_hit=hit,additional_sign_prefix_hit=endpoint,
            combined_and_sign_prefix_exhausted=not hit and not endpoint)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_augmented_sorted_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime,isprime,n_order
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--bits",type=int,default=108)
    parser.add_argument("--maximum-cases",type=int,default=4)
    args = parser.parse_args()
    sources,rnd,cases,rejected = source_inventory(),random.Random(REPLAY_ID),[],0
    checks = 0
    for i in range(544):
        if i<512:
            dP,dQ = rnd.randrange(1,101),rnd.randrange(1,101)
        else:
            dP,dQ = rnd.randrange(2**63,2**64),rnd.randrange(2**63,2**64)
        es = [rnd.randrange(-2**100,2**100) for _ in range(rnd.randrange(60))]
        actual,expected = sorted_classify(es,dP,dQ),COVERAGE["classify_exponents"](es,dP,dQ)
        for key in set(actual)|set(expected):
            assert actual.get(key,0)==expected.get(key,0),(i,key,actual,expected)
        checks += 1
    print(json.dumps(dict(progress="sorted-classifier-oracles-completed",checks=checks)),flush=True)
    for i in range(args.maximum_cases):
        while True:
            p = int(nextprime(rnd.randrange(2**(args.bits//2-1),2**(args.bits//2))))
            if int(n_order(2,p))==p-1:
                break
            rejected += 1
        while True:
            q = int(nextprime(rnd.randrange(11*p//10,19*p//10)))
            if int(n_order(2,q))==q-1:
                break
            rejected += 1
        assert isprime(p) and isprime(q) and p<=q<=2*p
        n,counts,metrics = p*q,Counter(),Counter()
        m = WEIGHTED["FAMILY"]["first_public_prime"](n,WEIGHTED["IntegerLedger"](),metrics)
        result = sorted_classify(AUGMENTED["augmented_exponents"](n,m,counts),p-1,q-1,True)
        assert counts["weighted_packets"]<=2*counts["original_packets"]
        case = dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,
            reference_actual_orders=[p-1,q-1],modulus=m,packet_counts=dict(counts),
            classification="no-augmented-hit" if result["combined_and_sign_prefix_exhausted"]
                else "augmented-or-endpoint-hit",is_N_only_source=False,orders_kernel_checked=False,**result)
        cases.append(case)
        print(json.dumps(dict(progress="reference-only-sorted-augmented-coverage",sample_index=i,**case)),flush=True)
        if case["classification"]=="no-augmented-hit":
            break
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,source_sha256=sources,nominal_bits=args.bits,
        maximum_reference_cases=args.maximum_cases,rejected_reference_prime_candidates=rejected,
        reference_condition="Base two has full component order in the new balanced corpus",
        backend="Disk-backed uint64 local signed CRT coordinates; two exact structured sorts",
        numpy_version=np.__version__,sorted_vs_dictionary_oracle_checks=checks,cases=cases,
        found_long_order_augmented_reference_miss=any(c["classification"]=="no-augmented-hit" for c in cases),
        is_N_only_source=False,is_factorization_runtime_measurement=False,
        kernel_checked_failure_control=False,is_bit_complexity_certificate=False,
        one_sixth_guarantee="OPEN",
        limitations="Two local residues identify a whole inverse orbit by a consistent common sign; this agrees with the prior LCM/dictionary classifier on 544 arbitrary lists and orders, including 32 full-width uint64 cases. The scratch sorts classify every original and adjacent weighted packet, cross-family pairs, both signed local channels and raw endpoints. Larger component primality/orders remain private native reference data. No public group powers, polynomial source or factorizer runtime are run or measured. A reference miss is not a compiled failure theorem or an asymptotic lower bound. Its scope is this fixed base, public modulus, retained family and pair/endpoint observables; adaptive bases, period certificates, other moduli, higher correlations and other algorithms remain available. Full arbitrary-ratio every-run construction-inclusive sixth-root bit factorization remains open.")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),reference_cases=len(cases),
        found_long_order_augmented_reference_miss=report["found_long_order_augmented_reference_miss"],
        one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
