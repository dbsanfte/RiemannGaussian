"""Exact native reconstruction of one previously saved failed dual support."""
import argparse
import json
import subprocess
import sys
import time
from fractions import Fraction as Q
from pathlib import Path
import flint
import run_cancellation_arithmetic as R
import run_cancellation_factor_search as P
import cancellation_gram_synthesis as S
import cancellation_gram_language as G
import check_cancellation_gram as I
import native_exact_support as N

EXTRA = ['run_cancellation_factor_native_dual.py', 'check_cancellation_factor_native_dual.py',
         'native_exact_support.py', 'test_native_exact_support.py']
LIMITS = dict(time_limit=180, max_rows=1400, max_variables=60000, max_cells=2000000,
              max_work=200000000, max_denominator=2**4096, max_coefficient_bits=4096)
FLAGS = dict(global_bound_proved=False, RH_proved=False)


def freeze(parent):
    parent = Path(parent)
    P.validate(parent)
    original = parent/'factor-probe-001'
    if not R.read(original/'independent_verification.json')['all_passed']:
        raise ValueError('verified original factor run required')
    old = R.read(original/'dual.json')['result']
    if old['status']!='missing_resource' or not old['diagnostics'].get('support'):
        raise ValueError('saved failed-support input required')
    out = original/'native-dual-001'
    if out.exists():
        raise FileExistsError('new exact reconstruction retry required')
    for n in EXTRA:
        if not (R.ROOT/n).exists():
            raise FileNotFoundError(n)
    out.mkdir()
    (out/'frozen_source').mkdir()
    hashes = {}
    for n in EXTRA:
        (out/'frozen_source'/n).write_bytes((R.ROOT/n).read_bytes())
        hashes[n] = R.sha(R.ROOT/n)
    protocol = dict(schema=1, limits=LIMITS, saved_support=old['diagnostics']['support'],
        training_scales=[1,2,3,5], program=R.read(original/'protocol.json')['programs'][0],
        inputs_sha256={n:R.sha(original/(n+'.json')) for n in ['dual','training','source_seal','independent_verification']},
        method='same y+/y-/square-slack equations and saved support; exact FLINT rational RREF; no new float proposal',
        conditioning='posthoc computational retry after exact Fraction elimination deadline; original failure retained',
        runtime=dict(python=sys.version, flint=getattr(flint,'__version__',None)),
        native_resource_scope='preflight cells/work/input bits and postflight time/output bits; no interruptible native RREF bound',
        **FLAGS)
    P.write(out/'protocol.json', protocol)
    P.write(out/'source_seal.json', dict(hashes=hashes))
    P.write(out/'seal.json', dict(protocol_sha256=R.sha(out/'protocol.json'), source_seal_sha256=R.sha(out/'source_seal.json')))


def validate(parent):
    parent = Path(parent)
    P.validate(parent)
    original = parent/'factor-probe-001'
    out = original/'native-dual-001'
    protocol = R.read(out/'protocol.json')
    if R.read(out/'seal.json') != dict(protocol_sha256=R.sha(out/'protocol.json'),source_seal_sha256=R.sha(out/'source_seal.json')):
        raise ValueError('native retry seal changed')
    hashes = R.read(out/'source_seal.json')['hashes']
    if set(hashes)!=set(EXTRA):
        raise ValueError('native source coverage')
    for n,h in hashes.items():
        if R.sha(R.ROOT/n)!=h or R.sha(out/'frozen_source'/n)!=h:
            raise ValueError('native source changed')
    if protocol['inputs_sha256']!={n:R.sha(original/(n+'.json')) for n in ['dual','training','source_seal','independent_verification']}:
        raise ValueError('native retry inputs changed')
    if protocol['saved_support']!=R.read(original/'dual.json')['result']['diagnostics']['support']:
        raise ValueError('saved support changed')
    return protocol


def reconstruct(instances, scales, support, limits):
    start = time.monotonic()
    deadline = start+limits['time_limit']
    try:
        prepared,lhs,ms,(ns,nr),offset,blocks = S.prepare(instances, scales, deadline=deadline)
        crosses = [j for j,(a,b) in enumerate(S.UPPER) if a<b]
        columns = prepared[:offset] + [{m:q/2 for m,q in prepared[offset+15*k+j].items()}
                                      for k in range(2) for j in crosses]
        # Same complete domain and equation order as the archived diagonal-dual search.
        monomials = sorted(set(lhs)|{m for p in columns for m in p})
        nonnegative = list(range(ns))+list(range(ns+2*nr,offset))
        relations = list(range(ns,ns+2*nr))+list(range(offset,len(columns)))
        left = dict(limits, time_limit=deadline-time.monotonic())
        if left['time_limit']<=0:
            raise TimeoutError('native input preparation deadline')
        out = N.reconstruct_dual_fixed_support(columns,lhs,monomials,nonnegative,relations,support,**left)
        if not out.get('certified'):
            return out
        y = dict(zip(monomials,map(Q,out['weights'])))
        grams = {}
        for k,region in enumerate(S.REGIONS):
            H = [[Q(0) for _ in range(5)] for _ in range(5)]
            for j,(a,b) in enumerate(S.UPPER):
                value = sum((q*y[m] for m,q in prepared[offset+15*k+j].items()),Q(0))
                H[a][b] = H[b][a] = value if a==b else value/2
            if any(H[a][b] for a in range(5) for b in range(5) if a!=b):
                raise ValueError('restricted Gram cross pairing must vanish')
            matrix = [[str(q) for q in row] for row in H]
            grams[region] = dict(matrix=matrix,PSD_certificate=G.ldlt_psd(matrix))
        out.update(monomials=[dict(instance=m[0],m=list(m[1:])) for m in monomials],
                   extra_cross_dots=out['columns_dot_y'][offset:],
                   columns_dot_y=out['columns_dot_y'][:offset], gram_duals=grams,
                   ordinary_constant_coordinates=[str(y.get((i,),Q(0))) for i in range(len(scales))],
                   all_C_q_extension_requires_zero_constant_coordinates=all(y.get((i,),Q(0))==0 for i in range(len(scales))),
                   restricted_dual_search='offdiagonal moments zero; successful witness separates the full declared PSD cone',
                   **FLAGS)
        I.verify_dual(instances,scales,out)
        if time.monotonic()>deadline:
            raise TimeoutError('native retry verification deadline')
        return out
    except (OverflowError,TimeoutError,MemoryError) as e:
        return dict(status='missing_resource',certified=False,reason=str(e) or type(e).__name__,**FLAGS)
    except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:
        return dict(status='uncertified',certified=False,reason=str(e) or type(e).__name__,**FLAGS)


def run(parent):
    parent = Path(parent)
    spec = validate(parent)
    original = parent/'factor-probe-001'
    out = original/'native-dual-001'
    if (out/'tests.json').exists():
        raise FileExistsError('native retry already started')
    test = subprocess.run([sys.executable,'-B','-m','unittest','test_native_exact_support'],
                          cwd=R.ROOT,capture_output=True,text=True,timeout=60)
    P.write(out/'tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))
    if test.returncode:
        raise ValueError('native support tests failed')
    try:
        instances = [P.build(spec['program'],X)['instance'] for X in spec['training_scales']]+P.constraints(spec['program'])
        case_hashes = list(map(R.digest,instances))
        if case_hashes!=R.read(original/'training.json')['attempts'][0]['case_hashes']:
            raise ValueError('exact original full instances required')
        result = reconstruct(instances,spec['training_scales'],spec['saved_support'],spec['limits'])
    except (OverflowError,TimeoutError,MemoryError) as e:
        case_hashes = []
        result = dict(status='missing_resource',certified=False,reason=str(e) or type(e).__name__,**FLAGS)
    P.write(out/'result.json',dict(dual=result,case_hashes=case_hashes,saved_support_sha256=R.digest(spec['saved_support']),**FLAGS))
    validate(parent)
    P.write(out/'producer_receipt.json',dict(**{n+'_sha256':R.sha(out/(n+'.json')) for n in ['result','tests','protocol','source_seal']},**FLAGS))
    print(json.dumps(dict(status=result['status'],certified=result.get('certified',False))))


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('command',choices=['freeze','run'])
    p.add_argument('parent')
    a=p.parse_args()
    (freeze if a.command=='freeze' else run)(a.parent)
