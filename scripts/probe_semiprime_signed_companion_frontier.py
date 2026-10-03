#!/usr/bin/env python3
"""Complete private-field exhaustion tests beyond the earlier small corpus.

This is a reference classifier, not an N-only factorizer, cost measurement,
or kernel certificate. It calls the frozen complete companion constructor.
Both prime fields and all signed roots are checked, without a pair matrix.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-bit-prime-scan-audit.json"
REPLAY_ID = 202610033224
COVERAGE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_companion_coverage.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_signed_companion_frontier.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def complete_field_counts(n,p,q,m):
    roots,packets,originals = set(),0,0
    weighted = COVERAGE["WEIGHTED"]
    for j in range(1,m):
        rows = list(weighted["reference_residue_packets"](n,m,j))
        originals += len(rows)
        for w in weighted["weighted_packets"](rows,m):
            c = 1-(w["determinant"]//m)*(w["exponent"]//m)
            roots.add(c%n)
            packets += 1
    pvalues,qvalues = {c%p for c in roots},{c%q for c in roots}
    pcount,qcount = len(pvalues),len(qvalues)
    ordinary = pcount == qcount == len(roots) and \
        (0 in roots or (0 not in pvalues and 0 not in qvalues))
    del pvalues,qvalues
    signed = {0}|roots|{(-c)%n for c in roots}
    # Both comprehensions run independently, including when the first finds a hit.
    signed_pcount = len({c%p for c in signed})
    signed_qcount = len({c%q for c in signed})
    return dict(N=n,input_bits=n.bit_length(),reference_p=p,reference_q=q,modulus=m,
        complete_original_packets=originals,companion_packets=packets,
        ordinary_roots=len(roots),ordinary_p_classes=pcount,ordinary_q_classes=qcount,
        signed_roots=len(signed),signed_p_classes=signed_pcount,signed_q_classes=signed_qcount,
        ordinary_exhausted=ordinary,signed_exhausted=signed_pcount == signed_qcount == len(signed),
        ordinary_p_collapsed_roots=len(roots)-pcount,ordinary_q_collapsed_roots=len(roots)-qcount,
        signed_p_collapsed_roots=len(signed)-signed_pcount,signed_q_collapsed_roots=len(signed)-signed_qcount,
        is_N_only_source=False,is_factorization_runtime_measurement=False,is_kernel_failure_certificate=False)


def main():
    from sympy import integer_nthroot,isprime,nextprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    parser.add_argument("--cases",type=int,default=4)
    parser.add_argument("--prime-bits",type=int,default=51)
    args = parser.parse_args()
    sources,rnd,results = source_inventory(),random.Random(REPLAY_ID),[]
    for index in range(args.cases):
        p = int(nextprime(rnd.randrange(1 << (args.prime_bits-1),1 << args.prime_bits)))
        q = int(nextprime(rnd.randrange(p+1,2*p)))
        assert p < q <= 2*p and isprime(p) and isprime(q)
        n = p*q
        floor,exact = integer_nthroot(n,6)
        bound = int(floor)+(not exact)
        m = int(nextprime(max(2,bound)-1))
        assert m*m < p and n <= m**6 and m <= 2*bound and isprime(m)
        print(json.dumps(dict(progress="complete-private-signed-field-test-start",sample_index=index,
            N=n,reference_p=p,reference_q=q,public_bound=bound,modulus=m)),flush=True)
        start = time.perf_counter()
        result = complete_field_counts(n,p,q,m)
        result.update(sample_index=index,public_sixth_width=bound,
            reference_classification_milliseconds=1000*(time.perf_counter()-start),
            all_original_residues_intermediate_rows_and_four_centers_enumerated=True,
            whole_signed_root_set_in_both_prime_fields_checked=True)
        results.append(result)
        print(json.dumps(dict(progress="complete-private-signed-field-test-completed",**result)),flush=True)
        if result["signed_exhausted"]:
            break
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        requested_cases=args.cases,prime_bits=args.prime_bits,completed_cases=results,
        first_complete_signed_exhaustion=next((r for r in results if r["signed_exhausted"]),None),
        stopped_at_first_miss=True,private_factor_data_used_only_by_reference=True,
        is_N_only_algorithm=False,is_factorization_runtime_measurement=False,
        is_kernel_failure_certificate=False,is_universal_coverage_proof=False,
        one_sixth_guarantee="OPEN")
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),completed_cases=len(results),
        complete_signed_miss_found=report["first_complete_signed_exhaustion"] is not None,
        kernel_failure_certificate=False,one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
