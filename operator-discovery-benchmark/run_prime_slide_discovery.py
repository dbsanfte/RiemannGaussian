"""Frozen exact stencil enumeration with independent full polynomial audit."""
import argparse
from concurrent.futures import ProcessPoolExecutor,as_completed
from fractions import Fraction as Q
import json
from math import comb,gcd
from multiprocessing import get_context
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import prime_slide_discovery as P

ROOT=Path(__file__).resolve().parent
TOTAL=150000000
SECONDS=1800
RESERVE=1000000
TESTS=['test_prime_slide_discovery','test_check_prime_slide_discovery']
RECEIPTS=['prime_slide_producer_development.json','prime_slide_checker_development.json']
SOURCES=['prime_slide_discovery.py','check_prime_slide_discovery.py','run_prime_slide_discovery.py',
         'prime_slide_protocol.txt','candidate10_ordered_prime_covariance_obligation.json',
         'ORDERED_PRIME_PAIRING_REVIEW_001.txt','PRIME_TRANSFER_MARTINGALE_REVIEW_001.txt',
         'PRIME_BANK_COVARIANCE_REVIEW_001.txt']+[name+'.py' for name in TESTS]+RECEIPTS


def read(path):return json.loads(Path(path).read_text())
def write(path,data):
    with Path(path).open('x') as stream:json.dump(data,stream,sort_keys=True,indent=2);stream.write('\n')
def append(path,data):
    with Path(path).open('a') as stream:stream.write(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n');stream.flush()


def receipts():
    data={name:read(ROOT/name) for name in RECEIPTS}
    for name,row in data.items():
        if not row['runs'] or row['runs'][-1]['returncode'] or row['operations']!=sum(r['operations'] for r in row['runs']):
            raise ValueError('passed cumulative development '+name)
    return data


def spec():
    target=read(ROOT/'candidate10_ordered_prime_covariance_obligation.json')
    if target['schema']!='prime-bank-overlap-obligation-v1' or target['status']!='open':raise ValueError('open complete input')
    return dict(schema='prime-slide-exact-search-v1',target=target,source_labels=P.SOURCE_LABELS,
                source_basis='B=a_u*a_v,a_u,a_v; supplied exact local rational series',
                grammar=dict(same_sparse='e+f<=4, support1..3, primitive integer coefficients±1,±2, firstpositive',
                             same_rectangles='all e=a..b,f=c..d with b+d<=6, coefficient1',
                             distinct_sparse='two independent labels each assigned to left orright; support1..4; same coefficient rule'),
                expected_word_counts=dict(same_prime_sparse=13385,same_prime_rectangles=210,distinct_prime_sparse=272),
                prime_weight_unit='1/3',theta='3/4',numerical_fitting=False,
                prior_nominated_calibrations=['single/double prime slide','single-leg prime-power prefix'],
                selection='per family and baseline-recovery lane: cofinal auxiliary, strongest proved power, term count, coefficient size, ordinal; also mixed-channel lane',
                source_masks='smooth-bank base h has at least two distinct prime factors; all units excluded; q coprime to both base indices',
                new_actual_source_evaluations=0,development=receipts(),work_limit=TOTAL,
                seconds=SECONDS,memory_bytes=16*1024**3,process_memory_bytes=4*1024**3,
                scalar_cell_cap=12000000,hashes=False,whole_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();data=spec();files={n:(ROOT/n).read_bytes() for n in SOURCES}
    if directory.exists():raise FileExistsError('fresh immutable search directory')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name,raw in files.items():(directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',data)


def verify_source(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen '+name)
    if read(directory/'protocol.json')!=spec():raise ValueError('changed protocol')


def audit_record(row,meter):
    import check_prime_slide_discovery as C
    facts=C.facts(row['program'],meter)
    for key in ('multipliers','component_valuations','component_l1','common_valuations'):
        if facts[key]!=row[key]:raise ArithmeticError('independent polynomial mismatch '+str(row['id'])+' '+key)
    if facts['whole_signed_bound_proved'] or row['whole_signed_bound_proved'] or row['original_target_recovered']:
        raise ValueError('local algebra cannot discharge full target')
    if row['exact_zero_all_components']!=(facts['common_valuations'] is None) or row['algebraic_identity_verified'] is not True:
        raise ValueError('exact algebra classification')
    left=[1,-1,-1] if row['program']['binding']=='same_prime' else [2,-1,-1]
    tensor=[a*b for a in left for b in [2,-1,-1]]
    constant=Q(81,4)*sum(abs(a)*b for a,b in zip(tensor,facts['component_l1']));meter.charge(30)
    if tensor!=row['tensor_coefficients'] or str(constant)!=row['kernel_polynomial_constant']:
        raise ValueError('actual full source tensor coefficient')
    weights=[str(Q(v,3)) for v in facts['common_valuations']] if facts['common_valuations'] is not None else None
    if weights!=row['prime_weights']:raise ValueError('free-prime weights')
    eligible=bool(weights and all(Q(w)>0 for w in weights))
    if eligible!=(row['bound'] is not None):raise ValueError('no unproved zero-weight tail bound')
    if eligible:
        bound=C.support_bound(row['program']['binding'],weights,'3/4',meter)
        for key in ('binding','weights','theta','prime_count','independent_labels','geometry','logs_retained',
                    'index_support','distinct_and_coprime_domain_required'):
            if bound[key]!=row['bound'][key]:raise ValueError('geometry mismatch '+key)
        if bound['energy_upper_power']!=row['bound']['energy_power'] or row['bound']['C']!=str(constant):
            raise ValueError('exact exponent/constant mismatch')
        if (row['bound']['original_target_recovered'] or row['bound']['whole_signed_bound_proved'] or
            row['bound']['logarithmic_factor']!='(1+log(2X))^2' or
            row['bound']['constant_template']!='2^max(2-theta*sum(b),0)*product(1+1/b_j)*C' or
            row['bound']['analytic_provenance']!='ORDERED_PRIME_PAIRING_REVIEW_001.txt'):
            raise ValueError('complete bound scope and constants')
        paid=Q(bound['energy_upper_power'])<=0
        if paid!=row['auxiliary_cofinal_bound_proved'] or paid!=row['bound']['cofinal_auxiliary']:
            raise ValueError('component-only cofinal classification')
    elif row['auxiliary_cofinal_bound_proved']:raise ValueError('unpaid auxiliary promoted')
    terms=row['program']['terms']
    baseline=sum(t['coefficient'] for t in terms if not any(t['left']+t['right']))
    obligations=[dict(term=t,obligation='bound/cancel complete lifted support and inverse-image complements')
                 for t in terms if any(t['left']+t['right'])] if baseline else []
    if baseline!=row['baseline_coefficient'] or obligations!=row['recovery_obligations']:
        raise ValueError('complete target recovery terms')
    if row['term_count']!=len(terms) or row['coefficient_l1']!=sum(abs(t['coefficient']) for t in terms):
        raise ValueError('selection complexity')


def audit_catalogue(rows,chosen,meter):
    """Coverage follows from independent membership, uniqueness and cardinality."""
    import check_prime_slide_discovery as C
    families=('same_prime_sparse','same_prime_rectangles','distinct_prime_sparse')
    words={family:[] for family in families}
    distinct_actions=((1,1,0,0),(1,0,0,1),(0,1,1,0),(0,0,1,1))
    for identity,row in enumerate(rows):
        if row['id']!=identity or row['family'] not in words:raise ValueError('complete ordinal/family catalogue')
        binding,_,terms=C.validate(row['program'])
        actions=[tuple(t['left']+t['right']) for t in terms];coefficients=[t['coefficient'] for t in terms]
        family=row['family'];meter.charge(20+12*len(terms))
        if family=='same_prime_rectangles':
            if binding!='same_prime' or any(c!=1 for c in coefficients):raise ValueError('rectangle coefficients/binding')
            a,b=min(e for e,f in actions),max(e for e,f in actions)
            c,d=min(f for e,f in actions),max(f for e,f in actions)
            expected=sorted(((e,f) for e in range(a,b+1) for f in range(c,d+1)),key=lambda t:(sum(t),t[0]))
            if actions!=expected or b+d>6:raise ValueError('complete rectangle action domain')
        else:
            if coefficients[0]<0 or gcd(*coefficients)!=1:raise ValueError('primitive coefficient normalization')
            if family=='same_prime_sparse':
                if binding!='same_prime' or len(terms)>3 or any(sum(a)>4 for a in actions):raise ValueError('sparse same-prime domain')
                if actions!=sorted(set(actions),key=lambda t:(sum(t),t[0])):raise ValueError('ordered distinct sparse actions')
            else:
                if binding!='distinct_primes' or len(terms)>4 or any(a not in distinct_actions for a in actions):raise ValueError('distinct-prime assignments')
                if actions!=[a for a in distinct_actions if a in actions]:raise ValueError('ordered distinct prime assignments')
        words[family].append(tuple(zip(actions,coefficients)))
    primitive=lambda k:(4**k-2**k)//2
    expected_counts=(sum(comb(15,k)*primitive(k) for k in (1,2,3)),comb(10,4),
                     sum(comb(4,k)*primitive(k) for k in range(1,5)))
    for family,expected in zip(families,expected_counts):
        ordered=sorted(words[family]);meter.charge(16*len(ordered))
        if len(ordered)!=expected or any(a==b for a,b in zip(ordered,ordered[1:])):
            raise ValueError('grammar completeness or duplicate word '+family)
    # Reconstruct the declared ranking without calling the producer selector.
    expected_selection=[]
    for family in families:
        for baseline in (True,False):
            best=None
            for row in rows:
                meter.charge()
                if row['family']!=family or row['exact_zero_all_components'] or bool(row['baseline_coefficient'])!=baseline:continue
                key=(not row['auxiliary_cofinal_bound_proved'],Q(row['bound']['energy_power']) if row['bound'] else Q(100),
                     row['term_count'],row['coefficient_l1'],row['id'])
                if best is None or key<best:best=key
            if best is not None and best[-1] not in expected_selection:expected_selection.append(best[-1])
    for binding in ('same_prime','distinct_primes'):
        best=None
        for row in rows:
            meter.charge();v=row['component_valuations'][5]
            if row['program']['binding']!=binding or v is None:continue
            key=(-sum(v),row['term_count'],row['coefficient_l1'],row['id'])
            if best is None or key<best:best=key
        if best is not None and best[-1] not in expected_selection:expected_selection.append(best[-1])
    if expected_selection!=chosen:raise ValueError('declared selection')


def audit_worker(directory,index,rows,cap,deadline):
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    meter=P.Meter(cap,max(0.001,deadline-time.monotonic()));meter.deadline=deadline
    meter.live(65536+700*len(rows));checked=0;reason=None
    try:
        for row in rows:
            audit_record(row,meter)
            checked+=1
            if checked%250==0:append(Path(directory)/('audit_'+str(index)+'_checkpoints.jsonl'),dict(checked=checked,counts=meter.counts()))
        status='verified'
    except (ArithmeticError,ValueError,OverflowError,TimeoutError,MemoryError) as error:
        status='incomplete';reason=str(error)
    result=dict(index=index,status=status,reason=reason,checked=checked,counts=meter.counts(),
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(Path(directory)/('audit_'+str(index)+'.json'),result);return result


def next_input(rows,chosen):
    return dict(schema='prime-slide-recovery-obligation-v1',status='open',
                scope=spec()['target']['scope'],equivalence_class=spec()['target']['equivalence_class'],
                selected_auxiliaries=[r for r in rows if r['id'] in chosen],
                known='exact local stencil identities and positive-weight complete-kernel bounds',
                required='recover/dominate the original joint signed moment with ALL lifted/inverse-image supports paid',
                other_components=['remaining smooth/main cross terms','unweighted same-prime pole compensation',
                    'large primitive-cofactor height repeated-prime defect','centered smaller-scale Z0 forcing',
                    'distinct-prime and fresh-scale correlations'],
                proof_hooks=['ORDERED_PRIME_PAIRING_REVIEW_001.txt','PRIME_TRANSFER_MARTINGALE_REVIEW_001.txt section9'],
                excluded_inferences=['small transformed kernel implies original kernel small',
                    'two free primes counted as one','prime powers treated as powers of prime coefficients',
                    'independent-valuation variance identified with integer-prefix variance',
                    'uncontrolled outside support dropped','equivalent target assumed in its own recovery'],
                new_actual_source_evaluations=0,whole_signed_bound_proved=False,RH_proved=False)


def run(directory):
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    directory=Path(directory).resolve();verify_source(directory);started=time.monotonic();deadline=started+SECONDS
    write(directory/'started.json',dict(attempt=1,monotonic=started))
    test=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=120)
    work=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',test.stdout,re.M)
    frozen=sum(int(n) for _,n in work)
    write(directory/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=frozen))
    if test.returncode or sorted(n for n,_ in work)!=sorted(TESTS):raise RuntimeError('complete frozen tests required')
    preparation=sum(r['operations'] for r in receipts().values())+frozen+RESERVE
    meter=P.Meter(min(50000000,TOTAL-preparation),SECONDS);meter.deadline=deadline
    engine=P.Engine(meter);rows=[];counts={};failure=None
    try:
        for identity,(family,program) in enumerate(P.programmes()):
            row=P.record(identity,family,program,engine);rows.append(row);counts[family]=counts.get(family,0)+1
            meter.live(65536+700*len(rows));append(directory/'candidates.jsonl',row)
            if identity%1000==0:append(directory/'producer_checkpoints.jsonl',dict(complete_candidates=len(rows),counts=meter.counts()))
        if counts!=spec()['expected_word_counts']:raise ValueError('all declared grammar words')
        chosen=P.selected(rows);audit_catalogue(rows,chosen,meter)
        write(directory/'selected.json',dict(ids=chosen,records=[r for r in rows if r['id'] in chosen]))
    except (ArithmeticError,ValueError,OverflowError,TimeoutError,MemoryError) as error:failure=str(error)
    spent=preparation+meter.operations
    write(directory/'producer.json',dict(status='complete' if failure is None else 'incomplete',reason=failure,
          counts=meter.counts(),families=counts,candidates=len(rows),peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))
    if failure:
        write(directory/'incomplete.json',dict(reason=failure,total_operations=spent,whole_signed_bound_proved=False));return
    # Polynomial reconstruction is independent. Complete disjoint batches are
    # audited in two processes, with the remaining allowance partitioned first.
    audits=[];allowance=(TOTAL-spent)//2
    with ProcessPoolExecutor(max_workers=2,mp_context=get_context('fork')) as pool:
        futures=[pool.submit(audit_worker,str(directory),i,rows[i::2],allowance,deadline) for i in range(2)]
        for future in as_completed(futures):
            result=future.result();audits.append(result);spent+=result['counts']['operations']
            print(json.dumps(dict(stage='independent_audit',**result)),flush=True)
    verify_source(directory)
    checked=sum(a['checked'] for a in audits);verified=all(a['status']=='verified' for a in audits) and checked==len(rows) and spent<=TOTAL
    report=dict(status='PRIME_ADJUNCTION_AUXILIARIES_INDEPENDENTLY_VERIFIED' if verified else 'INCOMPLETE',
                candidates=len(rows),checked_candidates=checked,families=counts,selected_ids=chosen,
                complete_grammar_and_selection_verified=True,
                cofinal_auxiliary_words=sum(r['auxiliary_cofinal_bound_proved'] for r in rows),
                cofinal_with_explicit_recovery=sum(r['auxiliary_cofinal_bound_proved'] and bool(r['baseline_coefficient']) for r in rows),
                total_operations=spent,preparation_operations=preparation,producer_operations=meter.operations,
                audit_operations=sum(a['counts']['operations'] for a in audits),elapsed_seconds=time.monotonic()-started,
                new_actual_source_evaluations=0,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'report.json',report);write(directory/'next_search_input.json',next_input(rows,chosen))
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
