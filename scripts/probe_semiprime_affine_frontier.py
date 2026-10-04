#!/usr/bin/env python3
"""A private-field witness search on the frozen complete signed-family miss.

The new values use only public original row coefficients and checked leading
coefficient inverses. Private fields select a signed pair witness from this
public stream. This prefix search is not a full N-only factorizer run, full
family classification, coverage theorem, or factorization runtime measure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-companion-center-spectrum-audit.json"
REPLAY_ID = 202610033228
WEIGHTED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_weighted_rows.py"))


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path,digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest,path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT,"scripts/probe_semiprime_affine_frontier.py"))
    return {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}


def leading_root(n,m,w,inverse):
    return ((2*w["a"]*w["j"]-m*w["b"])*inverse)%n


def first_signed_affine_witness(control):
    n,m,p,q = (control[k] for k in ("N","modulus","reference_p","reference_q"))
    start,inverses,seen,packets = time.perf_counter(),{},[{},{}],0

    def tag(w,sign):
        side = w["center_orientation"] == "larger-factor"
        return ((w["j"]*(2*m+1)+w["a"]+m)*(m+1)+w["t"])*4+side*2+(sign<0)

    def decode(code):
        side,negative = bool(code%4//2),bool(code%2)
        code //= 4
        code,denominator = divmod(code,m+1)
        j,a = divmod(code,2*m+1)
        a -= m
        row = next(w for w in WEIGHTED["reference_residue_packets"](n,m,j)
            if w["a"] == a and w["t"] == denominator and
            (w["center_orientation"] == "larger-factor") == side)
        return dict(packet=row,sign=-1 if negative else 1)

    for j in range(1,m):
        for w in WEIGHTED["reference_residue_packets"](n,m,j):
            packets += 1
            a = w["a"]
            if a not in inverses:
                assert math.gcd(a,n) == 1
                inverses[a] = pow(a,-1,n)
            root = leading_root(n,m,w,inverses[a])
            for sign in (1,-1):
                value = sign*root%n
                code = value+n*tag(w,sign)
                for field,dictionary in zip((p,q),seen):
                    residue = value%field
                    old = dictionary.get(residue)
                    if old is not None and old%n != value:
                        other = old%n
                        factor = math.gcd(n,value-other)
                        assert 1 < factor < n and n%factor == 0
                        first,second = decode(old//n),dict(packet=w,sign=sign)
                        for entry,expected in zip((first,second),(other,value)):
                            packet = entry["packet"]
                            assert math.gcd(packet["a"],n) == 1
                            assert entry["sign"]*leading_root(n,m,packet,
                                pow(packet["a"],-1,n))%n == expected
                        return dict(N=n,modulus=m,packets_examined=packets,
                            signed_prefix_field_classes=[len(x) for x in seen],
                            checked_leading_inverse_cache_size=len(inverses),
                            first=first,second=second,public_root_values=[other,value],
                            public_difference_gcd=factor,
                            reference_search_milliseconds=1000*(time.perf_counter()-start),
                            stopped_at_first_proper_signed_pair=True,
                            is_N_only_source=False,is_full_family_classification=False,
                            is_factorizer_runtime_measurement=False,is_Lean_proof=False)
                    if old is None:
                        dictionary[residue] = code
        if j%5000 == 0:
            print(json.dumps(dict(progress="private-affine-prefix",residue=j,
                original_packets_examined=packets,field_classes=[len(x) for x in seen])),flush=True)
    raise AssertionError("the frozen frontier input lacks its expected affine witness")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    control = parent["inherited_complete_signed_miss"]
    witness = first_signed_affine_witness(control)
    assert source_inventory() == sources,"source changed during replay"
    report = dict(replay_id=REPLAY_ID,parent_audit=PARENT_AUDIT,source_sha256=sources,
        inherited_complete_companion_signed_miss=control,affine_signed_witness=witness,
        source_choice="Frozen 103-bit signed-companion miss; leading-coefficient original-row roots with both signs",
        private_fields_used_only_to_select_a_reference_pair=True,
        full_large_N_only_polynomial_and_recovery_source_replayed=False,
        full_affine_family_exhaustion_replayed=False,universal_affine_coverage="OPEN",
        guaranteed_one_sixth_factorization="OPEN",is_complete_factorizer=False)
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources),witness=witness,
        full_factorizer_replayed=False,one_sixth_guarantee="OPEN")),flush=True)


if __name__ == "__main__":
    main()
