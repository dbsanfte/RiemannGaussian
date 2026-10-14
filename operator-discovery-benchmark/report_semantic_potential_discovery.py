"""Summarize the completed, independently checked structural search without refit."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import re

import semantic_potential_discovery as D
from run_semantic_potential_discovery import read, write
from report_potential_candidate_discovery import render


def summarize(directory):
    d=Path(directory).resolve()
    audit=read(d/'independent_verification.json'); receipt=read(d/'receipt.json')
    if (audit.get('status')!='FINITE_EVALUATION_VERIFIED' or audit.get('semantic_annotations_verified') is not True
            or receipt.get('status')!='CANDIDATE_LEADS' or any(audit.get(k) is not False for k in D.FLAGS)):
        raise ValueError('independent finite arithmetic and semantic verification required')
    batches=[read(d/('generation%d_batch.json'%i)) for i in (0,1)]
    records=[r for batch in batches for r in batch['records']]
    evidence={e['id']:e for i in (0,1) for e in read(d/('generation%d_evidence.json'%i))}
    final=read(d/'final_responses.json'); selected=read(d/'final_batch.json')
    by_case={(r['source'],r['id']):r for r in final}
    baseline={c['X']:Q(c['innovation']) for c in by_case['mu',0]['cases']}
    cards=[]
    for item in selected:
        record=item['record']; row=by_case['mu',record['id']]; e=evidence[record['id']]
        diagnostics=e['diagnostics']
        cards.append(dict(id=record['id'],family=record['family'],generation=record['generation'],
            origin=record['origin'],complexity=record['complexity'],program=record['program'],
            semantics=record['semantics'],selection_mechanism=D.selection_mechanism(record),
            exposure=record['exposure'],
            state_formulas=[dict(weight=s['weight'],U=render(s['tree'])) for s in record['program']['states']],
            W1=row.get('initial',{}).get('W'),frozen_constants=item['constants'],
            shared_validation_failures=sum(not s['passed'] for s in e['validation_scores']),
            diagnostic_status=diagnostics['status'],diagnostic_scales=record['exposure']['diagnostic_scales'],
            diagnostic_failures=sum(not s['passed'] for s in diagnostics['scores']),
            final_status=row['status'],final_reason=row.get('reason'),
            final_passes=sum(s['passed'] for s in row['scores']),
            final_failures=sum(not s['passed'] for s in row['scores']),
            final_dyadic_failures=sum(not s['passed'] and s['in_dyadic_claim_domain'] for s in row['scores']),
            final_innovations=[dict(X=c['X'],value=c['innovation'],
                added_potential_increment=str(Q(c['innovation'])-baseline[c['X']]) if c['X'] in baseline else None)
                for c in row['cases']],
            status='baseline_control' if record['id']==0 else 'unproved_numerical_lead',**D.FLAGS))
    tests=read(d/'tests.json'); test_count=int(re.search(r'Ran (\d+) tests',tests['stderr']).group(1))
    report=dict(schema='semantic-structural-potential-discovery-report-v2',status='FINITE_EVALUATION_VERIFIED',
        run=str(d),target='actual Mobius prefix energy',
        definition='E(X)=X^-2 sum_{t=X}^{2X-1} M(t)^2; V(X)=X^-2 sum_t sum_j w_j U_j(X,t)^2; W=E+V',
        initial_structures=len(batches[0]['records'])-1,structural_mutations=len(batches[1]['records']),
        mechanisms=dict(Counter(r['semantics']['mechanism'] for r in records if r['id'])),
        selection_mechanisms=dict(Counter(D.selection_mechanism(r) for r in records if r['id'])),
        discovery_outcomes=dict(Counter(e['status'] for e in evidence.values())),
        diagnostic_outcomes=dict(Counter(e['diagnostics']['status'] for e in evidence.values())),
        diagnostic_failures=sum(not s['passed'] for e in evidence.values() for s in e['diagnostics']['scores']),
        selected_structures=len(cards)-1,selected=cards,
        structures_passing_all_final_cases=sum(c['id']!=0 and c['final_status']=='available' and c['final_failures']==0 for c in cards),
        structures_failing_fixed_final_bounds=sum(c['id']!=0 and c['final_failures']>0 for c in cards),
        structures_with_incomplete_final_evidence=sum(c['id']!=0 and c['final_status']!='available' for c in cards),
        final_scales=list(D.FINAL),levels=list(D.LEVELS),coefficient_horizon=4*max(D.FINAL)-1,
        final_source_outcomes={source:dict(statuses=dict(Counter(r['status'] for r in final if r['source']==source)),
            passes=sum(s['passed'] for r in final if r['source']==source for s in r['scores']),
            failures=sum(not s['passed'] for r in final if r['source']==source for s in r['scores']))
            for source in ('mu','one','partial_prime_2')},
        tests_passed=test_count,synthetic_work=tests['work'],stage_counts=receipt['stage_counts'],
        independent_counts=audit['counts'],independent_records_checked=audit['cases_verified'],
        complete_work_reservation=450000000,
        measured_proxy_subtotal_before_preparation=sum(c['operations'] for c in receipt['stage_counts'].values())+audit['counts']['operations'],
        producer_cost=receipt['cost'],independent_elapsed_seconds=audit['elapsed_seconds'],
        proof_queue='proof_queue.json',interpretation=[
            'Programs change structure and source-factor placement; no coefficient optimizer is used.',
            'Semantic annotations are scoped algebraic descriptions, not all-scale estimate certificates.',
            'Masked coupled cores retain their mixed mechanism class for selection.',
            'Only common validation cases affect finite ranking; prospective selector diagnostics remain separate.',
            'Unsupported, raw-only and unaffordable selector regimes are explicit; no complete arithmetic activation claim follows from a changed domain.',
            'Independent finite arithmetic and semantic reconstruction passed; generation and exposure replay share their producer implementation.',
            'Every fixed-constant failure and incomplete outcome remains visible; passing finite cases does not prove a uniform bound.',
            'The baseline and complete original E are retained; nomination alone does not establish an improvement over baseline.',
            'Final responses were excluded from this run adaptation; arithmetic overlaps earlier research.',
            'All moving-boundary, mixed-correlation and universal source/compiler obligations remain open.'
        ],**D.FLAGS)
    write(d/'report.json',report)
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory')
    report=summarize(parser.parse_args().directory)
    print(D.canonical({k:report[k] for k in ('status','initial_structures','structural_mutations','selected_structures',
        'structures_passing_all_final_cases','structures_failing_fixed_final_bounds',
        'structures_with_incomplete_final_evidence','tests_passed','measured_proxy_subtotal_before_preparation')}))
