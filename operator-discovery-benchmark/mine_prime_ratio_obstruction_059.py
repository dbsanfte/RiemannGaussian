"""Discover exact floor cells forcing many irreversible prime-ratio charges.

This post-run proof search inspects policy syntax and rational floor cells.
It never evaluates a scientific Mobius table, a kernel, or a fitted bound.
The mathematical obstruction is motivated by the post059 analytical review;
its witness interval is generated, not supplied to the enumerator.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
import resource
import time

import mobius_transport_search_059 as SEARCH

MAX_V=64
MAX_CELLS=100_000
FILES=['mine_prime_ratio_obstruction_059.py','test_mine_prime_ratio_obstruction_059.py',
       'prime_ratio_obstruction_miner_059_development.json',
       'check_prime_ratio_obstruction_059.py','test_check_prime_ratio_obstruction_059.py',
       'check_prime_ratio_obstruction_059_development.json','PRIME_RATIO_OBSTRUCTION_CHECK_SCOPE_059.txt',
       'prime_ratio_obstruction_protocol_059.txt']


def first_missing_prime(primes,meter=None):
    meter=meter or SEARCH.Meter()
    if type(primes) is not list or len(primes)>8 or any(type(p) is not int or p<2 for p in primes):
        raise ValueError('bounded fixed prime mask')
    for r in range(2,10000):
        prime=True
        for d in range(2,isqrt(r)+1):
            meter.charge(4)
            if r%d==0: prime=False;break
        if prime and r not in primes: return r
    raise OverflowError('first missing prime search capacity')


def weight(v,base,meter=None):
    if meter is not None:meter.charge(12)
    floor=lambda a:a.numerator//a.denominator
    return floor(4*v/base)-3*floor(2*v/base)+2*floor(v/base)


def classify(a,b):
    if a not in (-1,0,1) or b not in (-1,0,1):raise ValueError('floor kernel range')
    if a==b==0:return None
    if b==0:return 'P',a
    if a==0:return 'Q',-b
    if a==b:return 'D',a
    return 'S',a


def floor_cells(parameters,max_v=MAX_V,meter=None):
    meter=meter or SEARCH.Meter()
    if type(max_v) is not int or not 1<=max_v<=4096:raise ValueError('bounded rational-cell extent')
    p,q=parameters['p'],parameters['q']
    if type(p) is not int or type(q) is not int or not 2<=p<q<=1_000_000:
        raise ValueError('ordered source scales')
    alpha=SEARCH._q(parameters['alpha'])
    if not 0<alpha<1:raise ValueError('fractional source order')
    r=first_missing_prime(parameters['primes'],meter)
    # Changes in floor(2v/b) and floor(v/b) are included in the 4v/b grid.
    boundaries={Q(0),Q(max_v)}
    prospective=sum((4*max_v)//b for b in (p,q,r*p,r*q))+2
    if prospective>MAX_CELLS:raise OverflowError('prospective exact-cell enumeration cap')
    meter.reserve(256*prospective);meter.charge(8*prospective)
    for base in (p,q,r*p,r*q):
        boundaries.update(Q(base*j,4) for j in range(1,(4*max_v)//base+1))
    ordered=sorted(boundaries);cells=[]
    for lower,upper in zip(ordered,ordered[1:]):
        v=(lower+upper)/2
        left=classify(weight(v,p,meter),weight(v,q,meter))
        right=classify(weight(v,r*p,meter),weight(v,r*q,meter))
        meter.charge(32)
        if lower<=0 or left is None or left!=right:continue
        profile,sigma=left
        cells.append({'prime':r,'cell':{'lower':str(lower),'upper':str(upper)},
                      'profile':profile,'kernel_sign':sigma,
                      'log_power':str(len(parameters['primes'])-alpha+1+(profile=='D')),
                      'cofactor_density_window':str(1/lower-1/upper)})
    # Proof strength first, then interval width. No observed arithmetic cost.
    cells.sort(key=lambda c:(Q(c['log_power']),-Q(c['cofactor_density_window']),Q(c['cell']['lower'])))
    return {'prime':r,'boundary_count':len(ordered),'searched_cells':len(ordered)-1,
            'admissible_cells':cells,'max_v':max_v}


def eligible(policy):
    SEARCH.validate_policy(policy)
    steps=policy['steps']
    if not steps or steps[0]['kind']!='prime_ratio' or steps[0]['order']!='asc':return False
    if len(steps)==2 and steps[1] not in (SEARCH._scan(),SEARCH._scan('profile')):return False
    return True


def certificate(parameters,policy,cell):
    if not eligible(policy):raise ValueError('first ascending prime pass with licensed residual pass')
    return {'schema':'prime-ratio-cost-obstruction-v1','parameters':parameters,'policy':policy,
            **{k:cell[k] for k in ('prime','cell','profile','kernel_sign','log_power')}}


def main():
    import run_mobius_transport_059 as RUN
    import check_prime_ratio_obstruction_059 as CHECK
    from run_fractional_prime_kernel_051 import check_receipt
    out=RUN.OUT/'prime_ratio_obstruction_001'
    if out.exists():raise FileExistsError('preserve post059 exact obstruction search')
    started=time.monotonic();meter=SEARCH.Meter();checker_meter=CHECK.Meter()
    RUN.validate_parent()
    for name in RUN.FILES:
        if (RUN.ROOT/name).read_bytes()!=(RUN.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve frozen059 source files')
    parameters=json.loads((RUN.OUT/'selected.json').read_text())['source_parameters']
    programs=json.loads((RUN.OUT/'grammar.json').read_text())['programs']
    selected=json.loads((RUN.OUT/'selected.json').read_text())['rows']
    frozen={name:(RUN.ROOT/name).read_bytes() for name in FILES}
    receipts=[json.loads(frozen[name]) for name in FILES if name.endswith('_development.json')]
    development=sum(check_receipt(receipt) for receipt in receipts)
    reserve=sum(receipt.get('preparatory_reserve_operations',0) for receipt in receipts)
    if type(reserve) is not int or reserve<0:raise ValueError('disclosed nonnegative preparatory reserve')
    out.mkdir();(out/'source_snapshot').mkdir()
    for name,data in frozen.items():(out/'source_snapshot'/name).write_bytes(data)
    try:
        cells=floor_cells(parameters,MAX_V,meter)
        rows=[]
        if cells['admissible_cells']:
            witness=cells['admissible_cells'][0]
            for program in programs:
                meter.charge(100)
                if not eligible(program['policy']):continue
                proof=certificate(parameters,program['policy'],witness)
                verified=CHECK.verify(proof,checker_meter)
                if verified.get('verified') is not True:raise ValueError('independent obstruction admission required')
                rows.append({'program_id':program['id'],'certificate':proof,'verification':verified})
        ruled_out={row['program_id'] for row in rows}
        claims=[{'id':row['id'],'program_id':row['program_id'],'fixed_claim':row['claim'],
                 'uniform_fixed_claim_refuted':True,
                 'reason':'B(N)>=c*N/(logN)^A eventually; incompatible with fixed C*N^beta for beta<1',
                 'finite_counterexample_scale_located':False}
                for row in selected if row['program_id'] in ruled_out and Q(row['claim']['beta'])<1]
        result={'schema':'prime-ratio-cost-obstruction-search-v1','parameters':parameters,
            'max_v':MAX_V,'cell_search':cells,'programs_examined':len(programs),
            'uniformly_obstructed_programs':rows,'selected_claims_asymptotically_refuted':claims,
            'lower_bound_scope':'these fixed policy costs only; not the source J or arbitrary matching policies',
            'all_real_subunit_power_times_fixed_polylog_bounds_excluded':True if rows else False,
            'measured_development_operations':development,'preparatory_reserved_operations':reserve,
            'development_charge_or_reserve_operations':development+reserve,'miner_operations':meter.operations,
            'independent_checker_operations':checker_meter.operations,
            'elapsed_seconds':time.monotonic()-started,
            'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'frozen_postrun_files':len(FILES),'hashes_used':False,
            'fresh_mu_tables_or_kernel_integrals':False,'finite_constants_refitted':False,
            'prior_scientific_search_replayed':False,'actual_arithmetic_refuted':False,
            'uniform_full_source_bound_proved':False,'RH_proved':False,'RH_refuted':False}
        for name,data in frozen.items():
            if (RUN.ROOT/name).read_bytes()!=data:raise ValueError('preserve postrun frozen sources')
        (out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'admissible_cells':len(cells['admissible_cells']),
            'witness':cells['admissible_cells'][0] if cells['admissible_cells'] else None,
            'obstructed_programs':len(rows),'selected_claims_refuted':claims,
            'miner_operations':meter.operations,'checker_operations':checker_meter.operations},indent=2))
        return result
    except BaseException as exc:
        (out/'failure.json').write_text(json.dumps({'type':type(exc).__name__,'message':str(exc)},indent=2)+'\n')
        raise


if __name__=='__main__':main()
