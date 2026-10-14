"""Report a completed structural pilot without refitting or admitting a theorem."""
import argparse
from pathlib import Path
import re
import potential_candidate_discovery as D
from run_potential_candidate_discovery import read, write


def render(tree):
    op=tree[0]
    if op in ('int','v','q'):return str(tree[1])
    if op=='x':return 'mu('+render(tree[1])+')'
    if op=='root':return 'floor(('+render(tree[1])+')^('+str(tree[2])+'/'+str(tree[3])+'))'
    if op=='sum':
        name,lo,hi,body=tree[1:]
        if lo==['int',1] and body==['x',['v',name]]:
            return 'M('+render(hi)+')'
        return 'sum_{'+name+'='+render(lo)+'..'+render(hi)+'}('+render(body)+')'
    if op=='scale':return '('+tree[1]+' * '+render(tree[2])+')'
    if op=='guard':return '1_{'+render(tree[1])+'} * ('+render(tree[2])+')'
    if op in ('prime','squarefree','not'):return op+'('+render(tree[1])+')'
    if op=='embed':return render(tree[1])
    if op in ('gcd','min','max'):return op+'('+render(tree[1])+','+render(tree[2])+')'
    symbols={'iadd':'+','isub':'-','imul':'*','idiv':'//','imod':'mod',
             'eq':'=','le':'<=','lt':'<','divides':'divides','and':'and','or':'or',
             'ratio':'/','add':'+','mul':'*'}
    return '('+render(tree[1])+' '+symbols[op]+' '+render(tree[2])+')'


def summarize(directory):
    d=Path(directory).resolve(); audit=read(d/'independent_verification.json'); receipt=read(d/'receipt.json')
    if (audit.get('status')!='FINITE_EVALUATION_VERIFIED' or audit.get('finite_arithmetic_verified') is not True
            or receipt.get('status')!='CANDIDATE_LEADS' or any(audit.get(k) is not False for k in D.FLAGS)):
        raise ValueError('complete independently checked finite pilot required')
    batches=[read(d/('generation%d_batch.json'%i)) for i in (0,1)]
    evidence={e['id']:e for i in (0,1) for e in read(d/('generation%d_evidence.json'%i))}
    final=read(d/'final_responses.json'); selected=read(d/'final_batch.json')
    by_case={(r['source'],r['id']):r for r in final}
    cards=[]
    for item in selected:
        record=item['record']; r=by_case['mu',record['id']]; e=evidence[record['id']]
        cards.append(dict(id=record['id'],family=record['family'],generation=record['generation'],
            origin=record['origin'],complexity=record['complexity'],program=record['program'],
            state_formulas=[dict(weight=s['weight'],U=render(s['tree'])) for s in record['program']['states']],
            W1=r['initial']['W'],frozen_constants=item['constants'],
            validation_failures=sum(not s['passed'] for s in e['validation_scores']),
            final_passes=sum(s['passed'] for s in r['scores']),final_failures=sum(not s['passed'] for s in r['scores']),
            final_dyadic_failures=sum(not s['passed'] and s['in_dyadic_claim_domain'] for s in r['scores']),
            finite_final_complete=r['status']=='available',
            final_innovations=[dict(X=c['X'],value=c['innovation']) for c in r['cases']],
            status='baseline_control' if record['id']==0 else 'unproved_numerical_lead',**D.FLAGS))
    tests=read(d/'tests.json'); test_count=int(re.search(r'Ran (\d+) tests',tests['stderr']).group(1))
    report=dict(schema='structural-potential-discovery-report-v1',status='FINITE_EVALUATION_VERIFIED',
        run=str(d),target='actual Mobius prefix energy',
        definition='E(X)=X^-2 sum_{t=X}^{2X-1} M(t)^2; V(X)=X^-2 sum_t sum_j w_j U_j(X,t)^2; W=E+V',
        families=list(D.FAMILIES),initial_structures=len(batches[0]['records'])-1,
        structural_mutations=len(batches[1]['records']),baseline_controls=1,
        all_discovery_outcomes_available=all(e['status']=='available' for e in evidence.values()),
        selected_structures=len(cards)-1,selected=cards,
        structures_passing_all_final_cases=sum(c['id']!=0 and c['final_failures']==0 for c in cards),
        structures_failing_fixed_final_bounds=sum(c['id']!=0 and c['final_failures']>0 for c in cards),
        final_scales=list(D.FINAL),levels=list(D.LEVELS),coefficient_horizon=4*max(D.FINAL)-1,
        final_controls={s:dict(passes=sum(t['passed'] for r in final if r['source']==s for t in r['scores']),
                               failures=sum(not t['passed'] for r in final if r['source']==s for t in r['scores']))
                        for s in ('one','partial_prime_2')},
        tests_passed=test_count,synthetic_work=tests['work'],stage_counts=receipt['stage_counts'],
        independent_counts=audit['counts'],complete_work_reservation=450000000,
        measured_proxy_subtotal_before_preparation=sum(c['operations'] for c in receipt['stage_counts'].values())+audit['counts']['operations'],
        producer_cost=receipt['cost'],independent_elapsed_seconds=audit['elapsed_seconds'],
        independent_records_checked=audit['cases_verified'],
        proof_queue='proof_queue.json',source_of_actual_mu='complete proper-divisor inversion; checker uses independent trial factorization',
        interpretation=[
            'Programs were generated and structurally mutated without a coefficient optimizer.',
            'The baseline is excluded from structural selection slots; selected structures need not beat it.',
            'All finite comparisons use frozen training constants; failures do not refute arbitrary future constants.',
            'Four exponent levels at one scale are not four independent arithmetic samples.',
            'Controls already differ at the base energy; their failure alone shows no new arithmetic information from V.',
            'Source arithmetic overlaps previous experiments; final data was excluded from this run selection.',
            'Independent finite arithmetic and fit/selection checks passed; generation replay shares the generator.',
            'Generation live-cache counter is zero because it has no numeric evaluator; root metadata uses the separate fixed resident reserve.',
            'Uniform all-scale signed estimates and universal source/compiler binding remain unproved.'],**D.FLAGS)
    write(d/'report.json',report)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory')
    r=summarize(p.parse_args().directory)
    print(D.canonical({k:r[k] for k in ('status','initial_structures','structural_mutations','selected_structures',
        'structures_passing_all_final_cases','structures_failing_fixed_final_bounds','tests_passed','measured_proxy_subtotal_before_preparation')}))
