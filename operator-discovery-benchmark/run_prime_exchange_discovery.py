"""Frozen factor discovery and complete prime-edge correction audit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import prime_slide_discovery as S
import run_prime_slide_discovery as OLD
import prime_exchange_discovery as P
import check_prime_exchange_discovery as C

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'prime-slide-results/pilot-001'
INPUT='candidate10_integrated_prime_recovery_obligation.json'
TESTS=['test_prime_exchange_discovery','test_check_prime_exchange_discovery']
RECEIPTS=['prime_exchange_producer_development.json','prime_exchange_checker_development.json']
SOURCES=['prime_exchange_discovery.py','check_prime_exchange_discovery.py','run_prime_exchange_discovery.py',
         'prime_exchange_protocol.txt',INPUT,'PRIME_EXCHANGE_KERNEL_REVIEW_001.txt','PRODUCT_FIBER_SIGNED_REVIEW_001.txt',
         'prime_slide_discovery.py','run_prime_slide_discovery.py']+[t+'.py' for t in TESTS]+RECEIPTS
TOTAL=30000000
SECONDS=900


def read(path):return json.loads(Path(path).read_text())
def write(path,data):
    with Path(path).open('x') as f:json.dump(data,f,sort_keys=True,indent=2);f.write('\n')


def development():
    data={name:read(ROOT/name) for name in RECEIPTS}
    for row in data.values():
        if not row['runs'] or row['runs'][-1]['returncode'] or row['operations']!=sum(r['operations'] for r in row['runs']):
            raise ValueError('passed cumulative development receipts')
    return data


def expressions():
    OLD.verify_source(PARENT);report=read(PARENT/'report.json')
    if report['status']!='PRIME_ADJUNCTION_AUXILIARIES_INDEPENDENTLY_VERIFIED':raise ValueError('verified parent algebra')
    rows=[]
    with (PARENT/'candidates.jsonl').open() as stream:
        for line in stream:
            row=json.loads(line)
            if row['family']=='distinct_prime_sparse':
                rows.append({key:row[key] for key in ('id','family','program','multipliers')})
    if len(rows)!=272 or len(rows)!=report['families']['distinct_prime_sparse']:raise ValueError('complete distinct-prime word bank')
    return rows


def specification():
    parent=read(ROOT/INPUT)
    if (parent['schema']!='prime-slide-integrated-recovery-obligation-v1' or parent['status']!='open' or
        parent['source']!='actual_mu_candidate10' or parent['equivalence_class']!='candidate10_complete_prime_bank_covariance' or
        parent['whole_signed_bound_proved'] or parent['RH_proved']):raise ValueError('same complete open target')
    return dict(schema='joint-prime-factor-discovery-v1',parent=parent,
        input_expressions=272,new_source_evaluations=0,linear_forms=P.linear_forms(),
        discovery='extract every searched common factor, then use ordered-cone total degree and exact prime-swap kernel symmetry',
        named_prior_calibration='prime exchange determinant, considered analytically before this archived-expression analysis',
        source_laws_supplied=True,source_projection='p*p; fresh-prime cross placements equal a*a for base cofactors>=2',
        source_word_scores_reused=False,theta='3/4',graph_degrees=['1','2','4'],
        selection='all antisymmetric cross-placement words with positive common ordered-cone degree, ordered by strongest degree then word size then original ordinal',
        bounds_are_for='absolute value of signed edge correction; unsuppressed symmetric/core/full graph recovery remains open',
        development=development(),work_limit=TOTAL,seconds=SECONDS,metadata_reserve=250000,
        memory_bytes=4*1024**3,aggregate_memory_limit=16*1024**3,hashes=False,
        whole_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();data=specification();rows=expressions()
    files={name:(ROOT/name).read_bytes() for name in SOURCES}
    if directory.exists():raise FileExistsError('fresh immutable factor search')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name,raw in files.items():(directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',data)
    write(directory/'input_expressions.json',rows)


def verify_sources(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen '+name)
    if read(directory/'protocol.json')!=specification() or read(directory/'input_expressions.json')!=expressions():
        raise ValueError('changed input or declared scope')


def audit(row,source,meter):
    if row['parent_id']!=source['id'] or row['program']!=source['program'] or row['original']!=source['multipliers']:
        raise ValueError('same archived source polynomial')
    C.verify(row['original'],row['factors'],row['quotients'],meter)
    orders=[min(sum(e) for e,c in p) if p else None for p in row['original']]
    meter.charge(2*sum(len(p) for p in row['original']))
    if orders!=row['envelope']['component_total_orders'] or min(o for o in orders if o is not None)!=row['envelope']['common_total_order']:
        raise ValueError('ordered-cone vanishing degree')
    weight=Q(min(o for o in orders if o is not None),3)
    if str(weight)!=row['envelope']['prime_weight']:raise ValueError('actual prime-weight order')
    multiplier=Q(1)
    for factor in row['factors']:
        a,b,c=factor['coefficients'];vertex_values=[c,b+c,a+b+c]
        multiplier*=max(abs(v) for v in vertex_values)**factor['multiplicity'];meter.charge(8)
    constants=[multiplier*sum(abs(Q(c)) for e,c in p) for p in row['quotients']]
    if list(map(str,constants))!=row['envelope']['component_constants']:raise ValueError('complete tensor envelope')
    correction_C=Q(81,16)*sum(constants)
    if str(correction_C)!=row['constant_for_correction_over_four']:raise ValueError('new quadratic projection and factor1/4')
    coefficients={tuple(t['left']+t['right']):t['coefficient'] for t in source['program']['terms']}
    neg_swap={(b,a,d,c):-value for (a,b,c,d),value in coefficients.items()}
    anti=coefficients==neg_swap
    cross=all(sum(key[:2])==sum(key[2:])==1 for key in coefficients)
    if anti!=row['prime_swap_antisymmetric'] or (anti and cross)!=row['full_kernel_correction_admissible']:
        raise ValueError('full source/kernel pairing admission')
    expected_degrees=['1','2','4'] if anti and cross and weight>0 else []
    if [edge['bound']['degree'] for edge in row['edge_constructions']]!=expected_degrees:raise ValueError('complete declared graph menu')
    for edge,degree in zip(row['edge_constructions'],expected_degrees):
        checked=C.edge_bound('3/4',str(weight),degree,meter)
        if edge['C']!=str(correction_C) or edge['graph']!='next_'+degree+'_actual_prime_neighbours':raise ValueError('prime-edge construction')
        for key,value in edge['bound'].items():
            if checked[key]!=value:raise ValueError('independent edge theorem consequence '+key)
        if edge['original_target_recovered'] or not edge['degree_independent_of_X']:raise ValueError('unpaid full-graph recovery')
    if any(row[key]!='OPEN' for key in ('symmetric_core','same_prime_and_cross_divisibility_sectors','complete_prime_graph_recovery')):
        raise ValueError('complete remaining domains')
    if row['whole_signed_bound_proved'] or row['RH_proved']:raise ValueError('component-to-target promotion')


def next_input(parent,selected):
    return dict(schema='prime-exchange-joint-recovery-obligation-v1',status='open',
        source=parent['source'],scope=parent['scope'],equivalence_class=parent['equivalence_class'],
        required_bound=parent['required_bound'],centering_feedback=parent['centering_feedback'],
        selected_factor_constructions=selected,
        signed_credit_proved=False,full_graph_recovery_proved=False,
        existing_auxiliary='bounded-degree actual-prime edge exchange correction has a cofinal absolute envelope',
        required_recovery=['retain the unsuppressed symmetric coefficient/kernel term',
            'supply complete-graph recovery with growing path/congestion costs and its constant mode paid',
            'retain same-prime labels, cross-divisibility, shared cofactors, units, poles and all moving supports'],
        source_specific_improvement=dict(provenance='PRIME_EXCHANGE_KERNEL_REVIEW_001.txt',
            formula='|edge correction|<=7*beta^2*d*2^(2-4*theta/3)*X^(1-4*theta/3)*(1+log(2X))',
            beta='9/2',theta='3/4',at_selected_theta='14*beta^2*d*(1+log(2X))',
            proof_scope='Delta/z0 wedge, both orientation supports, fixed uniform outgoing degree d; absolute envelope only',
            proof_status='reviewed analytical input; no proof-text execution'),
        product_fiber_feedback=dict(provenance='PRODUCT_FIBER_SIGNED_REVIEW_001.txt',
            invariant='on squarefree m, every nonzero a(h)*a(k) with h*k=m has sign mu(m)',
            implication='nonnegative prime-allocation transport within such a product cannot pair opposite signs',
            not_excluded=['cross-product transitions changing prime-count parity',
                'different valuation allocations at nonsquarefree products',
                'signed kernel and centered/repeated-prime compensation'],
            paid_regions=['h*k<=X*B(X) with fixed/polylog B, retaining the full d4 bound',
                          'fixed/polylog primitive cofactor height with all gcd and valuation overlaps'],
            proposed_new_production='prime adjunction across product fibers with explicit occupancy states, birth terms and both prefix exits',
            squarefree_projection_is_positive_energy=False),
        not_a_new_source_experiment=True,whole_signed_bound_proved=False,RH_proved=False)


def run(directory):
    directory=Path(directory).resolve();verify_sources(directory);start=time.monotonic()
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    write(directory/'started.json',dict(attempt=1,monotonic=start))
    test=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=60)
    work=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',test.stdout,re.M)
    frozen=sum(int(n) for _,n in work)
    write(directory/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=frozen))
    if test.returncode or sorted(n for n,_ in work)!=sorted(TESTS):raise RuntimeError('complete passed frozen suite')
    preparation=250000+frozen+sum(r['operations'] for r in development().values())
    meter=S.Meter(TOTAL-preparation,SECONDS);meter.deadline=start+SECONDS
    sources=read(directory/'input_expressions.json');records=[]
    for source in sources:
        records.append(P.record(source,meter));meter.live(65536+1500*len(records))
    producer_work=meter.operations
    write(directory/'factorizations.json',records)
    for row,source in zip(records,sources):audit(row,source,meter)
    selected=sorted([r for r in records if r['edge_constructions']],
        key=lambda r:(-r['envelope']['common_total_order'],len(r['program']['terms']),r['parent_id']))
    factor_counts=Counter(tuple(f['coefficients']) for r in records for f in r['factors'])
    report=dict(status='JOINT_FACTORS_AND_COMPLETE_EDGE_CORRECTIONS_VERIFIED',
        expressions=len(records),linear_forms=48,selected_parent_ids=[r['parent_id'] for r in selected],
        edge_constructions=sum(len(r['edge_constructions']) for r in selected),
        factor_occurrences=[dict(coefficients=list(f),words=n) for f,n in sorted(factor_counts.items())],
        coordinatewise_scores_reused=False,new_actual_source_evaluations=0,
        preparation_operations=preparation,producer_operations=producer_work,
        audit_operations=meter.operations-producer_work,total_operations=preparation+meter.operations,
        peak_cells=meter.peak_cells,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        elapsed_seconds=time.monotonic()-start,signed_negative_credit_proved=False,
        complete_prime_graph_recovered=False,whole_signed_bound_proved=False,RH_proved=False)
    verify_sources(directory)
    write(directory/'selected.json',selected);write(directory/'report.json',report)
    write(directory/'next_search_input.json',next_input(read(ROOT/INPUT),selected))
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
