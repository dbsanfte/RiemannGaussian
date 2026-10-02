#!/usr/bin/env python3
"""Replay exact extraction/phase checks and deliberately rough controls.

Reference factors are used ONLY for sample construction and verification.
The extraction functions receive N, a public budget and a public colour.
No cross-input table is used. Optional focused Lean check, never normal CI.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import shutil
import subprocess
import gmpy2

ROOT=Path(__file__).resolve().parents[1]
QUADRATIC=runpy.run_path(str(ROOT/'scripts/probe_semiprime_quadratic_extraction.py'))
SINGLE=QUADRATIC['SINGLE']
COLOURS=(-1,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def json_safe(value):
    if isinstance(value,int) and abs(value)>2**53:return str(value)
    if isinstance(value,dict):return {k:json_safe(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)):return [json_safe(v) for v in value]
    return value

def prime_triples(bits,rng):
    """p=12r-1, both r and (p-1)/2 prime: rough p-1 AND p+1."""
    found=[]
    lo=(1<<(bits//2-1))//12+1;hi=((1<<(bits//2))-1)//12-100
    for _ in range(100000):
        r=int(gmpy2.next_prime(rng.randrange(lo,hi)))
        p=12*r-1
        if gmpy2.is_prime(6*r-1) and gmpy2.is_prime(p) and p not in found:
            found.append(p)
            if len(found)==2:return tuple(sorted(found))
    raise RuntimeError('control generation budget exhausted')

def rough_control(p,q):
    n=p*q;scalar=SINGLE['factor_projected'](n,order_divisor=1)
    rows=[]
    for d in COLOURS:
        out=QUADRATIC['factor_quadratic'](n,order_divisor=1,discriminant=d)
        local_orders=[]
        if out['status']=='certified-large-order':
            for prime in (p,q):
                colour=int(gmpy2.legendre(d,prime))
                order=(prime-1)//2 if colour==1 else (prime+1)//12
                assert gmpy2.is_prime(order)
                ring=QUADRATIC['QuadraticRing'](prime,d)
                alpha=tuple(out['projected_base'])
                assert ring.power(alpha,order)==(1,0) and ring.power(alpha,1)!=(1,0)
                assert order>out['certified_through']
                local_orders.append(order)
            assert math.gcd(*local_orders)==1
        else:
            assert out['factor'] in (p,q),(n,d,out)
        rows.append({'discriminant':d,'jacobi':out.get('jacobi'),
                     'status':out['status'],'factor':out['factor'],
                     'reference_private_orders':local_orders})
    if scalar['status']=='certified-large-order':
        alpha=scalar['projected_base']
        orders=[(prime-1)//2 for prime in (p,q)]
        for prime,order in zip((p,q),orders):
            assert gmpy2.is_prime(order)
            assert pow(alpha,order,prime)==1 and alpha%prime!=1
            assert order>scalar['certified_through']
        scalar['reference_private_orders']=orders
    else:assert scalar['factor'] in (p,q)
    return {'N_decimal':str(n),'reference_factors_decimal':[str(p),str(q)],
            'p_minus_one':{'smooth':2,'rough':(p-1)//2},
            'p_plus_one':{'smooth':12,'rough':(p+1)//12},
            'q_minus_one':{'smooth':2,'rough':(q-1)//2},
            'q_plus_one':{'smooth':12,'rough':(q+1)//12},
            'scalar':scalar,'colours':rows}

def report(check_lean=False):
    proof=ROOT/'RiemannGaussian/SemiprimeOrderSeparation.lean'
    lean={'file':str(proof.relative_to(ROOT)),'sha256':digest(proof),
          'scope':'Structural algebra/order lemmas, not full Python or bit-complexity verification.'}
    if check_lean:
        lake=shutil.which('lake') or str(Path.home()/'.elan/bin/lake')
        check=subprocess.run([lake,'env','lean',str(proof.relative_to(ROOT))],
                             cwd=ROOT,capture_output=True,text=True,check=False)
        lean.update({'returncode':check.returncode,'output':check.stdout+check.stderr})
        assert check.returncode==0 and not lean['output'],lean
    safe=[]
    for p,q in ((59,83),(45707,58403),(12907547,13436327),
                (2189570459,3785926883),(615130607723,854694715367)):
        n=p*q;a=SINGLE['factor_projected'](n,order_divisor=1)
        b=QUADRATIC['factor_quadratic'](n,order_divisor=1)
        assert a['status']=='certified-large-order' and b['factor'] in (p,q)
        safe.append({'N_decimal':str(n),'reference_factors_decimal':[str(p),str(q)],
                     'scalar_status':a['status'],'quadratic_factor_decimal':str(b['factor']),
                     'quadratic_stage':b['stage'],'budget':a['bound']})
    rng=random.Random(2026100541)
    controls=[rough_control(6827,7187)]
    controls.extend(rough_control(*prime_triples(bits,rng)) for bits in (64,80))
    return {'seed':2026100541,'single_checks':SINGLE['validate'](),
            'quadratic_checks':QUADRATIC['validate'](),
            'safe_prime_controls':safe,'four_rough_controls':controls,
            'formal_proof':lean,
            'dependencies_sha256':{str(path.relative_to(ROOT)):digest(path) for path in (
                Path(__file__),ROOT/'scripts/probe_semiprime_single_extraction.py',
                ROOT/'scripts/probe_semiprime_quadratic_extraction.py',
                ROOT/'scripts/probe_semiprime_weighted_batch.py')},
            'interpretation':'Finite coverage counterexamples to these bounded passes only. '
                             'No lower bound for arbitrary factoring algorithms; no generic one-sixth theorem.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-lean',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    encoded=json.dumps(json_safe(report(args.check_lean)),indent=2)+'\n'
    if args.output:args.output.write_text(encoded)
    print(encoded,end='')

if __name__=='__main__':main()
