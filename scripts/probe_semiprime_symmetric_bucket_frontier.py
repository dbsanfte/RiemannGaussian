#!/usr/bin/env python3
"""Continue complete symmetric-family failure search on fixed 126-bit inputs.

The full original public family and all prior and new scalar channels are
retained. Fix every candidate before classification; stop only at the first
complete miss after both private factor images finish. Source parameters
are pre-filtered by the auxiliary quadratic character, with every trial
saved. Successful cases receive no new Lean certificates or coverage credit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import struct
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-row-partner-offsets-audit.json"
NATIVE_PARENT = "docs/semiprime-symmetric-row-axes-audit.json"
PREFLIGHT_AUDIT = "docs/semiprime-symmetric-bucket-preflight-audit.json"
REPLAY_ID = 202610033263
CANDIDATE_SEED = 202610033262
BUCKET = runpy.run_path(str(ROOT/"scripts/probe_semiprime_symmetric_bucket_confirmation.py"))
CURRENT,PRIOR = BUCKET["CURRENT"],BUCKET["PRIOR"]


def source_inventory():
    paths = {PARENT_AUDIT,NATIVE_PARENT,PREFLIGHT_AUDIT,
        "scripts/probe_semiprime_symmetric_bucket_frontier.py"}
    for audit in (PARENT_AUDIT,NATIVE_PARENT,PREFLIGHT_AUDIT):
        for path,digest in json.loads((ROOT/audit).read_text())["source_sha256"].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
            paths.add(path)
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def candidates():
    from sympy import integer_nthroot,nextprime,prevprime,primerange
    rnd = random.Random(CANDIDATE_SEED)
    small_primes = [int(p) for p in primerange(2,500)]
    ranked = []
    for m in primerange(1900000,1940001):
        m = int(m)
        if m%4!=1:continue
        first = next(p for p in small_primes if pow(p,(m-1)//2,m)==m-1)
        ranked.append((first,m))
    ranked.sort(reverse=True)
    screen = dict(prime_interval=[1900000,1940000],primes_mod_four_one_screened=len(ranked),
        selected_moduli=[dict(modulus=m,least_positive_quadratic_nonresidue=first)
            for first,m in ranked[:4]],no_scalar_family_classification_used=True)
    selected,trials = [],[]
    for first,m in ranked[:4]:
        previous = int(prevprime(m))
        lower,upper,center = previous**6,m**6,m**3
        accepted = 0
        while accepted<3:
            p = int(nextprime(center-rnd.randrange(center//32,center//16)))
            qlo,qhi = lower//p+1,upper//p
            assert qlo<qhi
            q = int(nextprime(qlo-1+rnd.randrange(qhi-qlo)))
            assert q<=qhi
            n = p*q
            floor,exact = integer_nthroot(n,6)
            width = int(floor)+(not exact)
            assert int(nextprime(width-1))==m and lower<n<=upper
            small,large = math.isqrt(n//2)+math.isqrt(n),math.isqrt(n)+math.isqrt(2*n)
            assert n.bit_length()==126 and p<=q<=2*p and m*m<p
            assert (width-1)**6<n<=width**6 and p<2**63 and q<2**63
            assert 0<small<2**64 and 0<large<2**64 and m<2**23
            character = pow(n%m,(m-1)//2,m)
            assert character in (1,m-1)
            trial = dict(trial=len(trials),N=n,input_bits=126,reference_p=p,reference_q=q,
                sixth_width=width,modulus=m,previous_prime=previous,
                least_positive_quadratic_nonresidue=first,
                auxiliary_quadratic_character=-1 if character==m-1 else 1,selected=character==m-1)
            trials.append(trial)
            if trial["selected"]:
                selected.append(dict(index=len(selected),**trial,balanced=True,private_prefix_unit_bound=True,
                    public_centers_fit_uint64=True))
                accepted += 1
    return selected,trials,screen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    sources = source_inventory()
    prior_native = json.loads((ROOT/NATIVE_PARENT).read_text())
    assert len(prior_native["complete_symmetric_families"])==len(prior_native["planned_candidates"])
    assert not prior_native["complete_native_symmetric_misses"],"confirm the existing complete miss instead"
    planned,trials,screen = candidates()
    print(json.dumps(dict(progress="126-bit-symmetric-candidates-fixed",candidate_seed=CANDIDATE_SEED,
        selection_trials=len(trials),auxiliary_character_filter=-1,modulus_screen=screen,planned_candidates=planned,
        stop_condition="first complete miss after both factor images")),flush=True)
    complete,slice_checks = [],[]
    with tempfile.TemporaryDirectory(prefix="semiprime-symmetric-126-") as temp:
        temp = Path(temp)
        generator,checked_rows,sorter,path = (temp/k for k in ("rows","rows-ubsan","sort","classes.bin"))
        BUCKET["compile_binary"](generator,CURRENT["CPP"])
        BUCKET["compile_binary"](checked_rows,CURRENT["CPP"],ubsan=True)
        BUCKET["compile_binary"](sorter,BUCKET["SORT_CPP"])
        for candidate in planned:
            n,m,p,q = (candidate[k] for k in ("N","modulus","reference_p","reference_q"))
            rnd = random.Random(REPLAY_ID+candidate["index"])
            residues = sorted({1,2,3,m-3,m-2,m-1,p%m,q%m,*[rnd.randrange(1,m) for _ in range(56)]}-{0})
            packets,scalars = 0,0
            for j in residues:
                rows,values,companions = CURRENT["original_oracle"](n,m,2,first=j,last=j+1)
                counts = PRIOR["native_rows"](checked_rows,path,n,m,p,q,2,first=j,last=j+1)
                raw = list(struct.iter_unpack("QQ",path.read_bytes()))
                assert raw==[PRIOR["JOINED"]["fold_pair"](v%p,v%q,p,q)[:2] for v in values],j
                assert counts["original_packets"]==len(rows) and counts["companion_packets"]==companions
                packets += len(rows); scalars += len(values)
            slice_checks.append(dict(index=candidate["index"],N=n,residues=residues,
                original_packets=packets,scalar_values=scalars,full_Nt_and_whole_N_inverses_checked=True,
                all_original_centers_and_intermediates_checked=True,undefined_behavior_checks=True))
            print(json.dumps(dict(progress="complete-126-bit-symmetric-family-start",**candidate,
                full_Nt_slice_packets=packets,full_Nt_slice_scalars=scalars)),flush=True)
            start = time.perf_counter()
            counts = PRIOR["native_rows"](generator,path,n,m,p,q,2)
            result = BUCKET["classify"](sorter,path,p,q)
            case = dict(**candidate,**counts,**result,
                private_reference_milliseconds=1000*(time.perf_counter()-start),
                all_original_residues_intermediates_and_both_centers_enumerated=True,
                all_preceding_roots_and_both_new_axes_retained=True,both_factor_projections_fully_counted=True,
                is_N_only_factorizer=False,is_kernel_exhaustion_certificate=False,is_factorizer_runtime=False)
            complete.append(case)
            print(json.dumps(dict(progress="complete-126-bit-symmetric-family-completed",**case)),flush=True)
            if case["signed_exhausted"]:break
    assert source_inventory()==sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,candidate_seed=CANDIDATE_SEED,parent_audit=PARENT_AUDIT,
        native_parent_audit=NATIVE_PARENT,bucket_preflight_audit=PREFLIGHT_AUDIT,source_sha256=sources,
        modulus_screen=screen,candidate_selection_trials=trials,planned_candidates=planned,
        canonical_full_Nt_slices=slice_checks,
        complete_symmetric_families=complete,complete_native_symmetric_misses=sum(c["signed_exhausted"] for c in complete),
        candidate_filter_applied_before_any_classification=True,auxiliary_character_filter=-1,
        no_family_channels_removed=True,no_new_success_Lean_certificates=True,
        universal_symmetric_family_coverage_proved=False,guaranteed_one_sixth_factorization="OPEN",
        is_complete_factorizer=False,is_kernel_exhaustion_certificate=False,is_bit_complexity_certificate=False,
        limitations="Complete private-reference enumeration of the unchanged full amended family. Both factor images, signs, zero and whole-N deduplication are counted; no partial scan gives a miss. Canonical sixth-root moduli and 126-bit source slices are checked natively. The quadratic-character filter selects inputs before classification and carries no coverage theorem. A native miss is not a Lean exhaustion certificate. Large prefix/denominator guards use private factor bounds; complete N-only bit cost, memory accounting, arbitrary-ratio and prime-square coverage remain unproved.")
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),complete_cases=len(complete),
        complete_native_misses=report["complete_native_symmetric_misses"],one_sixth_guarantee="OPEN")),flush=True)


if __name__=="__main__":main()
