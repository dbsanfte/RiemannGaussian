"""Independent arithmetic, provenance, selection and claim audit for factor regions.

The numerical producer/search are not imported. A reviewed elementary prime
obstruction can reject specified potential claims; no signed bound is promoted.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import factor_region_checks as independent

BASE = Path(__file__).resolve().parent
CODE = ['run_factor_region.py','test_run_factor_region.py','factor_region_arithmetic.py',
        'test_factor_region_arithmetic.py','factor_region_proof.txt','factor_region_search.py',
        'test_factor_region_search.py','factor_region_checks.py','test_factor_region_checks.py',
        'check_factor_region_run.py','test_check_factor_region_run.py',
        'arithmetic_filter_pole_budget.py','arithmetic_filter_pole_budget_proof.txt',
        'test_arithmetic_filter_pole_budget.py','detector_safe_evaluation.py',
        'inverse_prefix_grammar.py','detector_workflow_guard.py','factor_region_analytical_review.txt']
INPUT_NAMES = ['protocol.json','source_seal.json','seal.json','contract_tests.txt','worker_replay.json',
               'training.json','validation_data.json','candidate_batch.json','validation.json','proof_queue.json',
               'final_cases.json','final_evaluation.json']
SEALED_NAMES = ['protocol.json','contract_tests.txt','source_seal.json','worker_replay.json',
                'training.json','validation_data.json','candidate_batch.json','validation.json','proof_queue.json']


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def no_promotions(value):
    if isinstance(value, dict):
        for name, child in value.items():
            if name in ('RH_proved', 'global_bound_proved', 'actual_all_scale_signed_bound_proved',
                        'estimate_proved', 'global_actual_signed_innovation_bound_proved',
                        'global_signed_upper_bound_proved', 'global_critical_energy_bound_proved'):
                require(child is False, 'unproved global bound promoted: ' + name)
            no_promotions(child)
    elif isinstance(value, list):
        for child in value:
            no_promotions(child)


def pole_bridge(target):
    normalized = independent.normalized_target(target)
    require(normalized == target, 'target must use canonical fixed filter')
    k = target['r'] + target['l']
    require(1 <= len(target['filter']) <= k, 'ordinary-zeta pole bridge unsupported')
    return dict(target_id=digest(target), support=len(target['filter']), pole_order_floor=k,
                retained_pole_order_at_least=k-len(target['filter'])+1,
                conditional_only=True, estimate_proved=False)


def prime_obstruction(program):
    """Witness for the elementary theorem in frozen factor_region_proof section9.

    This recognizes a single prime square among a sum of nonnegative squares.
    Its lower bound refutes the ORIGINAL cofinal potential innovation claim,
    not merely fitted constants, and not the direct energy assertion or RH.
    """
    target = independent.normalized_target(program['target'])
    for term in program['terms']:
        require(F(term['weight']) >= 0, 'negative potential term')
    if len(target['filter']) != 1 or target['filter'][0]['divisor'] != 1:
        return []
    witnesses = []
    for term in program['terms']:
        f = term['feature']; weight = F(term['weight'])
        if not weight or list(f['vector']) != [0,0,0,0,0,1,0,0,0]:
            continue
        if any(F(f['scheme'][k]) != F(1,2) for k in ('prime_power','core_power')):
            continue
        eta = F(f['eta'])
        if not 0 <= eta < 1:
            continue
        alpha = F(target['filter'][0]['weight']); k = target['r']+target['l']
        witnesses.append(dict(feature_id=f['feature_id'], component_index=5,
                              coefficient=str(weight*alpha*alpha*k*k/128),
                              power=str(1-eta), threshold=4096,
                              lower_bound='W(X)>=coefficient*X^power/(log X)^2',
                              domain='every dyadic integer X>=4096',
                              global_potential_innovation_claim_refuted=True,
                              direct_target_energy_claim_refuted=False,
                              RH_refuted=False, formal_machine_proof=False))
    return witnesses


def rank(candidate, score):
    program = candidate['program']
    constants = list(program['constants'].values())
    return (score['missing_cases']+sum(c is None for c in constants),
            score['finite_failures'],
            max([F(c) for c in constants if c is not None] or [F(0)]),
            sum(F(t['weight']) for t in program['terms']),
            len(program['terms']), candidate['program_id'])


def rank_json(value):
    return [str(x) if isinstance(x, F) else x for x in value]


def selected(factories, results):
    scores = {r['program_id']:r['score'] for r in results}
    decisions = []; queue = {}
    for factory in factories:
        tid = factory['target_id']
        for group in ('baseline','all','singleton','lp'):
            eligible = [c for c in factory['candidates'] if group=='all' or
                        any(o['kind']==group for o in c['origins'])]
            chosen = min(eligible, key=lambda c:rank(c,scores[c['program_id']])) if eligible else None
            pid = None if chosen is None else chosen['program_id']
            decisions.append(dict(target_id=tid,group=group,
                                  eligible_ids=sorted(c['program_id'] for c in eligible),
                                  selected_id=pid,
                                  rank=None if chosen is None else rank_json(rank(chosen,scores[pid]))))
            if chosen is not None:
                if pid not in queue:
                    queue[pid] = dict(candidate=chosen, origins=[])
                queue[pid]['origins'].append(group)
    return queue, decisions


def audit_run(directory):
    require(not sys.flags.optimize and os.environ.get('PYTHONOPTIMIZE','') in ('','0'),
            'verified runtime requires assertions enabled')
    d=Path(directory).resolve()
    require(not (d/'failure.json').exists(), 'failed run cannot be certified')
    initial_inputs={name:sha(d/name) for name in INPUT_NAMES}
    spec=read(d/'protocol.json'); source=read(d/'source_seal.json')
    seal=read(d/'seal.json'); checks=[]
    require(set(spec['code_sha256'])==set(CODE),'incomplete frozen code manifest')
    for name, expected in spec['code_sha256'].items():
        require(sha(d/'frozen_source'/name)==expected, 'frozen source changed: '+name)
        require(sha(BASE/name)==expected, 'live checker/runtime changed: '+name)
    require(source['protocol_sha256']==digest(spec), 'source protocol binding')
    require(source['code_sha256']==spec['code_sha256'], 'source code binding')
    require(source['source_frozen_before_data'] is True and source['tests_passed'] is True,
            'source freeze/tests absent')
    require(source['contract_tests_sha256']==sha(d/'contract_tests.txt'), 'test output binding')
    require(source['tests']==[Path(n).stem for n in CODE if n.startswith('test_')], 'incomplete test module set')
    test_text=(d/'contract_tests.txt').read_text()
    test_match=re.search(r'Ran (\d+) tests? in .*\n\s*OK\s*$',test_text)
    require(test_match is not None and int(test_match.group(1))>0,'successful contract log absent')
    checks.append('frozen source and tests')
    require(seal['protocol_sha256']==digest(spec) and seal['selection_closed'] is True
            and seal['final_cases_exist'] is False, 'candidate seal')
    require(set(seal['files'])==set(SEALED_NAMES),'incomplete sealed artifact set')
    for name, expected in seal['files'].items():
        require(sha(d/name)==expected,'sealed input changed: '+name)
    checks.append('candidate seal')
    replay=read(d/'worker_replay.json')
    require(set(replay['files_match'])=={'candidate_batch.json','validation.json','proof_queue.json'}
            and all(v is True for v in replay['files_match'].values()), 'worker replay')
    checks.append('all three worker outputs reproduced')
    features=independent.feature_dictionary(spec['schemes'])
    require(spec['features']==features and spec['dictionary_sha256']==digest(features),
            'frozen feature grammar mismatch')
    bridges=[pole_bridge(t) for t in spec['targets']]
    checks.append('complete dictionary and conditional pole bridges')
    prior=spec['provenance']
    require(set(prior['prior_verifications'])=={'fixed-pole-filter-results/pilot-001/verification.json'},
            'undeclared prior stage')
    for name,expected in prior['prior_verifications'].items():
        require(sha(BASE/name)==expected,'prior verification changed')
    require(prior['complete_actual_prime_source'] is True and prior['historical_coefficient_overlap'] is True
            and prior['unseen_prime_holdout'] is False, 'arithmetic data provenance scope')
    require(spec['runtime']['python']==sys.version,'runtime Python mismatch')
    checks.append('prior verification and arithmetic overlap disclosure')
    training=read(d/'training.json'); validation_data=read(d/'validation_data.json')
    cases=read(d/'final_cases.json'); final=read(d/'final_evaluation.json')
    generation=spec['final_generation']; seal_sha=sha(d/'seal.json')
    odd=generation['odd_min']+2*(int(seal_sha[:16],16)%generation['odd_count'])
    require(cases['base_scales']==sorted(generation['fixed']+[odd]) and
            cases['levels']==spec['final_levels'] and cases['seal_sha256']==seal_sha and
            cases['protocol_sha256']==digest(spec) and cases['generated_after_seal'] is True,
            'postseal final case derivation')
    require(final['protocol_sha256']==digest(spec) and final['cases_sha256']==sha(d/'final_cases.json'),
            'final evaluation binding')
    checks.append('deterministic postseal evaluation')
    audits={}
    for name,data,scales in [('training',training,spec['training_scales']),
                             ('validation',validation_data,spec['validation_scales']),
                             ('final',final['data'],cases['base_scales'])]:
        require(data['protocol_sha256']==digest(spec) and data['base_scales']==scales, 'dataset binding')
        expanded=sorted(set(scales)|{2*x for x in scales})
        require(data['scales']==expanded,'complete parent/child block domain')
        require(0<=data['profile']['cost']<=spec['budgets']['arithmetic_work'] and
                0<=data['table']['cost']<=spec['budgets']['feature_work'],'declared work budget exceeded')
        audits[name]=independent.check_profile(data['profile'],expanded,spec['targets'],spec['schemes'])
        independent.check_feature_table(data['profile'],data['table'],expanded,spec['targets'],spec['schemes'])
        no_promotions(data)
        checks.append('independent complete '+name+' arithmetic and features')
        print('Verified complete '+name+' factor arithmetic', flush=True)
    batch=read(d/'candidate_batch.json'); validation=read(d/'validation.json'); proof=read(d/'proof_queue.json')
    require(batch['protocol_sha256']==digest(spec) and batch['training_sha256']==sha(d/'training.json'), 'candidate binding')
    require(validation['protocol_sha256']==digest(spec) and validation['validation_sha256']==sha(d/'validation_data.json'), 'validation binding')
    require(set(batch['access_denials'])=={'proof','final_cases','final_evaluation','prior_results'}
            and all(v is True for v in batch['access_denials'].values()), 'discovery access guard')
    checks.append('discovery dataflow guard receipts (not OS isolation)')
    factories=batch['factories']; require([f['target'] for f in factories]==spec['targets'],'factory target coverage')
    archives=[]; candidates={}
    for factory in factories:
        archives.append(independent.check_candidate_archive(factory,training['table'],features,
                                                             spec['training_scales'],spec['levels']))
        for candidate in factory['candidates']:
            require(candidate['program_id'] not in candidates,'duplicate cross-target candidate')
            candidates[candidate['program_id']]=candidate
    checks.append('complete proposal archives, quantization, aliases and exact refits')
    require(len(validation['results'])==len(candidates) and
            {r['program_id'] for r in validation['results']}==set(candidates),'validation candidate coverage')
    for row in validation['results']:
        expected=independent.exact_score(candidates[row['program_id']]['program'],validation_data['table'],
                                          spec['validation_scales'],spec['levels'])
        require(row['score']==expected,'independent validation score mismatch')
    chosen,decisions=selected(factories,validation['results'])
    require(proof['selection_decisions']==decisions,'independent exact selection mismatch')
    require(proof['protocol_sha256']==digest(spec) and proof['candidate_ids_frozen_before_final'] is True
            and proof['final_used_for_selection'] is False,'proof queue binding')
    require([c['program_id'] for c in proof['queue']]==sorted(chosen),'proof queue coverage/order')
    validation_scores={r['program_id']:r['score'] for r in validation['results']}
    for item in proof['queue']:
        pid=item['program_id']; require(item['exact_program']==chosen[pid]['candidate']['program'],'queue program changed')
        require(item['exact_program_sha256']==pid==digest(item['exact_program']),'queue exact program digest')
        require(item['selection_origins']==chosen[pid]['origins'],'queue selection origins')
        require(item['global_claim']==spec['global_claim'] and item['precise_claim_sha256']==digest(spec['global_claim']), 'queue global quantifiers')
        require(item['validation_score']==validation_scores[pid],'queue validation score')
        admission=item['conditional_admission'];target=item['exact_program']['target']
        require(admission['status']=='admitted_conditional' and admission['conditional_bridge_admitted'] is True
                and admission['filter']==target['filter'] and admission['support_size']==len(target['filter'])
                and admission['target']['mu_arity']==target['r'] and admission['target']['liouville_arity']==target['l']
                and admission['minimum_surviving_pole_order']==target['r']+target['l']-len(target['filter'])+1,
                'queued conditional admission mismatch')
    checks.append('independent validation and diverse exact selection')
    require(len(final['results'])==len(chosen) and {r['program_id'] for r in final['results']}==set(chosen),'final selected coverage')
    counts=dict(passes=0,failures=0,missing=0,dyadic_stored_constant_failures=0,offdomain_finite_failures=0)
    for row in final['results']:
        score=independent.exact_score(candidates[row['program_id']]['program'],final['data']['table'],
                                       cases['base_scales'],cases['levels'])
        require(row['score']==score,'independent final score mismatch')
        counts['passes']+=score['finite_passes']; counts['failures']+=score['finite_failures'];counts['missing']+=score['missing_cases']
        for obs in score['observations']:
            if obs['finite_pass'] is False:
                counts['dyadic_stored_constant_failures' if obs['X']&(obs['X']-1)==0 else 'offdomain_finite_failures']+=1
    checks.append('independent final scores with unknown constants missing')
    obstructions={pid:prime_obstruction(candidate['program']) for pid,candidate in candidates.items()}
    obstructions={pid:ws for pid,ws in obstructions.items() if ws}
    for value in (batch,validation,proof,final):no_promotions(value)
    checks.append('no uniform-bound promotion; prime-singleton global rejection witnesses')
    require({name:sha(d/name) for name in INPUT_NAMES}==initial_inputs,'run changed during independent audit')
    for name,expected in spec['code_sha256'].items():
        require(sha(BASE/name)==sha(d/'frozen_source'/name)==expected,'source changed during audit')
    checks.append('input and code bindings stable throughout audit')
    return dict(schema=1,all_passed=True,checks_passed=len(checks),checks=checks,
                input_sha256=initial_inputs,code_sha256=spec['code_sha256'],
                contract_tests_passed=int(test_match.group(1)),
                independent_profile_checks=audits,archives=archives,candidate_count=len(candidates),
                selected_count=len(chosen),final_counts=counts,conditional_bridges=bridges,
                prime_singleton_refutations=obstructions,
                selected_refuted_ids=sorted(set(obstructions)&set(chosen)),
                mathematical_audit_imports_production_code=False,
                formal_machine_checked_proof=False,Python_guard_is_OS_sandbox=False,
                actual_all_scale_signed_bound_proved=False,global_bound_proved=False,RH_proved=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory',type=Path)
    args=parser.parse_args()
    if (args.directory/'verification.json').exists():
        raise FileExistsError('verification already exists; use audit_run for read-only reconstruction')
    result=audit_run(args.directory)
    with (args.directory/'verification.json').open('x') as f:
        json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({k:result[k] for k in ('all_passed','checks_passed','candidate_count','selected_count','final_counts','selected_refuted_ids')}))
