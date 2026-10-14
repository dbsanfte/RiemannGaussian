"""Report separately verified finite search and analytical domain adjudication."""
import argparse
import hashlib
import json
from pathlib import Path


def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def report(directory):
    d=Path(directory).resolve();v=read(d/'verification.json')
    if v['all_passed'] is not True:raise ValueError('independent verification required')
    for name,expected in v['input_sha256'].items():
        if sha(d/name)!=expected:raise ValueError('verified input changed: '+name)
    for name,expected in v['code_sha256'].items():
        if sha(d/'frozen_source'/name)!=expected:raise ValueError('frozen source changed: '+name)
    collection=d/'review-collection-001';review=read(collection/'collection.json')
    for name,expected in review['input_sha256'].items():
        if sha(collection/name)!=expected:raise ValueError('collected review changed')
    ad=d/'asymptotic-adjudication-001';a=read(ad/'adjudication.json')
    if not a['all_domain_checks_passed'] or not a['analytical_proof_independently_reviewed']:
        raise ValueError('reviewed analytical domain adjudication required')
    if a['source_verification_sha256']!=sha(d/'verification.json') or a['source_review_collection_sha256']!=sha(collection/'collection.json'):
        raise ValueError('adjudication source binding mismatch')
    if a['source_input_sha256']!=v['input_sha256']:raise ValueError('adjudication input set differs')
    for name,expected in a['analytical_source_sha256'].items():
        if sha(ad/'frozen_source'/name)!=expected:raise ValueError('analytical source changed')
    if sha(ad/'contract_tests.txt')!=a['contract_tests_sha256']:raise ValueError('theorem-domain tests changed')
    spec=read(d/'protocol.json');cases=read(d/'final_cases.json')
    queue={r['program_id']:r for r in read(d/'proof_queue.json')['queue']}
    data=read(d/'final_evaluation.json')['data'];candidates=[]
    for result in a['selected']:
        pid=result['program_id'];entry=queue[pid];program=entry['exact_program']
        candidates.append(dict(result,exact_program=program,selection_origins=entry['selection_origins']))
    prior=set(v['prime_singleton_refutations']);new=set(a['covered_global_refutations'])
    summary=dict(schema=1,verification_sha256=sha(d/'verification.json'),
                 adjudication_sha256=sha(ad/'adjudication.json'),
                 proposals=sum(r['proposal_count'] for r in v['archives']),
                 candidates=v['candidate_count'],aliases=sum(r['alias_count'] for r in v['archives']),
                 failed_or_missing_proposals=sum(r['failed_or_missing_LP'] for r in v['archives']),
                 feature_count=len(spec['features']),selected_count=v['selected_count'],
                 contract_tests=v['contract_tests_passed'],independent_audit_groups=v['checks_passed'],
                 theorem_domain_tests=5,final_cases=cases,final_counts=v['final_counts'],
                 complete_final_coefficient_horizon=data['profile']['value']['complete_horizon'],
                 final_arithmetic_work_proxy=data['profile']['cost'],
                 prime_singleton_archive_refutations=len(prior),even_prime_core_archive_refutations=len(new),
                 combined_archive_refutations=len(prior|new),selected=candidates,
                 selected_refuted_ids=a['selected_refuted_ids'],
                 remaining_selected_global_claims=a['remaining_selected_global_claims'],
                 imported_analytic_theorem='unconditional PNT, https://dlmf.nist.gov/27.2.E3',
                 formal_machine_checked_proof=False,actual_all_scale_signed_bound_proved=False,RH_proved=False)
    lines=['COMPLETE FACTOR REGIONS: VERIFIED SEARCH AND ANALYTICAL REJECTION','',
           f"{summary['proposals']} proposals; {summary['candidates']} distinct exact programs; "
           f"{summary['aliases']} aliases; {summary['failed_or_missing_proposals']} failed/missing proposals.",
           f"{summary['feature_count']} supplied features; {summary['selected_count']} selected programs.",
           f"{summary['contract_tests']} contracts, {summary['independent_audit_groups']} independent audit groups, "
           'and 5 postselection theorem-domain tests passed.',
           f"Final bases {cases['base_scales']}; complete coefficients through {summary['complete_final_coefficient_horizon']}.",
           f"Finite outcomes: {v['final_counts']['passes']} passes, {v['final_counts']['failures']} fitted-constant failures, "
           f"{v['final_counts']['missing']} missing (untrained q=17,29).",'',
           'The original cofinal potential-innovation claims of two selected programs are globally refuted,',
           'although both passed all six available final observations. Seven original claims remain unresolved.',
           'The full actual direct filtered-energy bound and RH remain unproved.','',
           'Selected exact programs (component order recorded in frozen_source/factor_region_proof.txt):']
    for item in candidates:
        p=item['exact_program'];score=item['final_score'];target=p['target']
        lines += [f"  {item['program_id']}: r={target['r']}, l={target['l']}, filter={target['filter']}",
                  f"    {item['original_global_claim_disposition']}; finite {score['finite_passes']}/{score['finite_failures']}/{score['missing_cases']} pass/fail/missing; C12={p['constants'].get('12')}"]
        if not p['terms']:lines.append('    V=0.')
        for term in p['terms']:
            f=term['feature'];s=f['scheme']
            lines.append(f"    + {term['weight']} * square({f['vector']}); theta={s['prime_power']}, phi={s['core_power']}, eta={f['eta']}.")
    lines += ['',
        'Each square means the complete block Gram form divided by X^2 ceil(X^eta),',
        'with cutoffs recomputed at that block and the fixed filter applied to every source component.',
        'All 81 Gram entries, source coverage, exact roots, refits, aliases, selection and final scores',
        'were independently reconstructed. LP supplies proposals only; no optimality certificate is claimed.',
        'Actual source coefficients overlap prior runs. The Python guard is not OS isolation.',
        'All nine candidates received hash-bound parallel reviews; collection itself makes no math admission.','',
        'Postselection arithmetic theorem:',
        'For actual c=mu*lambda, phi=1/2, theta>=1/3, the even small-prime/small-core prefix obeys',
        'F_X(vX)=(-64 sqrt(v)+o(1))*X^(3/4)/(log X)^2, uniformly for v in fixed positive compact intervals.',
        'All other source classes are retained and bounded absolutely. Classical unconditional PNT is imported.',
        'With fixed filter P(s), its complete normalized square is',
        '(6144 P(1/2)^2+o(1))*X^(1/2)/(log X)^4.',
        'A positive singleton potential with eta<1/2 and P(1/2)!=0 therefore contradicts cofinal subpower',
        'innovation by telescoping. The two rejected programs contain exactly such terms.',
        'The theorem has independent analytical review and exact domain checks; it is not a formal machine proof.',
        'Its asymptotic threshold is not numerically explicit. Current fitted constants never enter the contradiction.',
        f"The general rule rejects {len(new)} archived programs; the earlier prime-singleton gate rejects {len(prior)}; union {len(prior|new)}.",
        'These are original potential-claim refutations, not refutations of direct target energy or RH.','',
        'Useful surviving auxiliary result:',
        'The eight-term mu potential679662 simplifies exactly to a rescaled (M-1) energy plus unit and thin',
        'factor-region terms. The thin region lies below sqrt(X), giving E<=W<=29E+76 globally.',
        'This leaves the critical M-energy estimate unresolved; a smaller finite fit does not supply it.','',
        'Next work must preserve cancellation inside complete signed region combinations and control their residual.',
        'Subtracting only the leading asymptotic cannot establish a critical remainder. Any centering or new',
        'normalization changes the candidate and requires a new frozen search plus full recovery accounting.','']
    return summary,'\n'.join(lines)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory',type=Path)
    args=parser.parse_args();summary,prose=report(args.directory)
    for name,value in [('report.json',json.dumps(summary,sort_keys=True,indent=2)+'\n'),('report.txt',prose)]:
        with (args.directory/name).open('x') as f:f.write(value)
    print(prose)
