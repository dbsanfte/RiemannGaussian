"""Independent arithmetic, provenance, selection and claim audit for signed prime-pair-forcing corrections.

The numerical producer/search are not imported. Supplied prefix bounds charge one part of the complete signed forcing. No full
signed remainder bound is promoted.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import prime_pair_forcing_checks as independent

BASE = Path(__file__).resolve().parent
CODE = ['run_prime_pair_forcing.py','test_run_prime_pair_forcing.py','prime_pair_forcing.py',
        'test_prime_pair_forcing.py','prime_pair_forcing_proof.txt','prime_pair_forcing_search.py',
        'test_prime_pair_forcing_search.py','prime_pair_forcing_checks.py','test_prime_pair_forcing_checks.py',
        'check_prime_pair_forcing_run.py','test_check_prime_pair_forcing_run.py',
        'arithmetic_filter_pole_budget.py','arithmetic_filter_pole_budget_proof.txt',
        'test_arithmetic_filter_pole_budget.py','detector_safe_evaluation.py',
        'inverse_prefix_grammar.py','detector_workflow_guard.py','prime_pair_forcing_review.txt']
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
                        'global_signed_upper_bound_proved', 'global_critical_energy_bound_proved', 'actual_H_energy_bound_proved', 'full_signed_bound_proved', 'remainder_bound_proved'):
                require(child is False, 'unproved global bound promoted: ' + name)
            no_promotions(child)
    elif isinstance(value, list):
        for child in value:
            no_promotions(child)


CUTOFFS=[dict(kind='fixed',value=v) for v in (0,1,2,3,4,8)]+[dict(kind='power',power=v) for v in ('1/12','1/6','1/3','1/2')]+[dict(kind='bit_length_power',power=v) for v in ('1/2','1','3/2','2')]

def root_ceiling(X,q):
    require(type(X) is int and X>=1 and type(q) is int and q>=1,'root domains')
    a,b=0,X
    while b-a>1:
        c=(a+b)//2
        if c**q>=X:b=c
        else:a=c
    return b

def auxiliary_cost(target,cutoff,X):
    cert=independent.prefix_certificate(target,cutoff)
    return F(cert['scalar'])*(2+X.bit_length())**cert['log_4X_power'] if cert['cofinal_critical_component_bound'] else None

def row_lookup(profile):
    require(profile['status']=='available','complete profile needed')
    rows=profile['value']['rows'];lookup={(r['target'],digest(r['cutoff']),r['X']):r for r in rows}
    require(len(lookup)==len(rows),'duplicate row');return lookup

def fit(program,profile,scales,levels):
    lookup=row_lookup(profile);constants={};observations=[]
    for q in levels:
        maximum=F(0)
        for X in scales:
            row=lookup[program['target'],digest(program['cutoff']),X];v=row['normalized_negative_remainder'];rt=root_ceiling(X,q)
            maximum=max(maximum,F(v['upper'])/rt)
            observations.append(dict(X=X,level=q,interval=[v['lower'],v['upper']],root=rt,missing=False,reason=None))
        constants[str(q)]=str(maximum)
    return constants,observations

def exact_score(program,profile,scales,levels):
    lookup=row_lookup(profile);out=[]
    for X in scales:
        row=lookup[program['target'],digest(program['cutoff']),X];v=row['normalized_negative_remainder'];lo,hi=F(v['lower']),F(v['upper']);cost=auxiliary_cost(program['target'],program['cutoff'],X)
        for q in levels:
            C=program['constants'].get(str(q));missing=C is None;bound=None if missing else F(C)*root_ceiling(X,q)
            require(missing or F(C)>=0,'nonnegative constant')
            state='missing' if missing else 'pass' if hi<=bound else 'fail' if lo>bound else 'unresolved_interval'
            out.append(dict(X=X,level=q,uniform_normalized_abs_prefix_upper=None if cost is None else str(cost),normalized_upper_plus_auxiliary=None if cost is None else str(hi+cost),lower=str(lo),upper=str(hi),bound=None if bound is None else str(bound),upper_margin=None if bound is None else str(bound-hi),lower_margin=None if bound is None else str(bound-lo),status=state,missing=missing,reason='unknown_level_constant' if missing else None,finite_pass=True if state=='pass' else False if state=='fail' else None,global_bound_proved=False))
    return dict(observations=out,finite_passes=sum(o['status']=='pass' for o in out),finite_failures=sum(o['status']=='fail' for o in out),unresolved_intervals=sum(o['status']=='unresolved_interval' for o in out),missing_cases=sum(o['missing'] for o in out),finite_cases=len(out),global_bound_proved=False)

def check_archive(factory,profile,cutoffs,scales,levels):
    target=factory['target'];require(target in ('mu','c'),'actual target')
    require(factory['cutoffs']==cutoffs and factory['dictionary_sha256']==digest(cutoffs),'full cutoff dictionary')
    require(factory['training_scales']==scales and factory['levels']==levels,'training domain')
    require(len(factory['candidates'])==len(factory['proposal_archive'])==len(cutoffs),'complete proposal archive')
    lookup=row_lookup(profile);seen=set()
    for c,entry,cutoff in zip(factory['candidates'],factory['proposal_archive'],cutoffs):
        base=dict(target=target,cutoff=cutoff);constants,evidence=fit(base,profile,scales,levels);program=dict(base,constants=constants);pid=digest(program)
        require(pid not in seen,'duplicate program');seen.add(pid)
        require(c['program']==entry['exact_program']==program and c['program_id']==entry['program_id']==pid,'exact program fit/hash')
        require(entry['fit_observations']==evidence and entry['discarded'] is False,'fit evidence and archive')
        cert=independent.prefix_certificate(target,cutoff);admitted=cert['cofinal_critical_component_bound']
        require(c['component_certificate']==cert,'uniform auxiliary certificate')
        admission=c['conditional_auxiliary'];require(admission==entry['conditional_auxiliary'] and admission['status']==('conditional' if admitted else 'exploratory') and admission['auxiliary_bound_admitted']==admitted and admission['remainder_bound_proved'] is False,'conditional scope')
        require(c['training_score']==exact_score(program,profile,scales,levels),'complete training interval score')
        coverage=[];diagnostics=[];costs=[]
        for X in scales:
            row=lookup[target,digest(cutoff),X];energy=row['original_energy'];cost=auxiliary_cost(target,cutoff,X)
            coverage.append(dict(X=X,coverage=row['coverage'],missing=False))
            diagnostics.append(dict(X=X,original_energy=energy,normalized_original_energy=str(F(energy['A_X'],X*X)),normalized_original_innovation=str(F(energy['A_2X']-4*energy['A_X'],4*X*X)),diagnostic_only=True))
            costs.append((X,None if cost is None else str(cost)))
        require(c['coverage']==coverage and c['original_energy_diagnostics']==diagnostics,'coverage/original target diagnostics')
        require([(o['X'],o['uniform_normalized_abs_prefix_upper']) for o in c['auxiliary_costs']]==costs,'uniform auxiliary costs')
        require(all(o['conditional_only'] is True for o in c['auxiliary_costs']),'auxiliary cost scope')
    return dict(verified=True,attempts=len(seen),candidates=len(seen),global_bound_proved=False)

def rank(candidate,score):
    constants=list(candidate['program']['constants'].values())
    observed={o['X']:F(o['normalized_upper_plus_auxiliary']) for o in score['observations'] if o['normalized_upper_plus_auxiliary'] is not None}
    return (score['missing_cases']+sum(v is None for v in constants),score['unresolved_intervals'],score['finite_failures'],sum(observed.values(),F(0)),max([F(v) for v in constants if v is not None] or [F(0)]),candidate['program_id'])

def rank_json(value):
    return [str(x) if isinstance(x, F) else x for x in value]


def selected(factories,results):
    scores={r['program_id']:r['score'] for r in results};decisions=[];queue={}
    for factory in factories:
        target=factory['target']
        for group in ('baseline','fixed','bit_length_power','all_admitted'):
            eligible=[]
            for c in factory['candidates']:
                cutoff=c['program']['cutoff']
                if not independent.prefix_certificate(target,cutoff)['cofinal_critical_component_bound']:continue
                if group=='all_admitted' or (group=='baseline' and cutoff==dict(kind='fixed',value=0)) or (group=='fixed' and cutoff['kind']=='fixed' and cutoff['value']>0) or (group=='bit_length_power' and cutoff['kind']=='bit_length_power'):eligible.append(c)
            chosen=min(eligible,key=lambda c:rank(c,scores[c['program_id']])) if eligible else None
            pid=chosen['program_id'] if chosen else None
            decisions.append(dict(target=target,group=group,eligible_ids=sorted(c['program_id'] for c in eligible),selected_id=pid,rank=None if chosen is None else rank_json(rank(chosen,scores[pid]))))
            if chosen is not None:
                if pid not in queue:queue[pid]=dict(candidate=chosen,origins=[])
                queue[pid]['origins'].append(group)
    return queue,decisions

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
    require(replay['isolated_subprocess'] is True and replay['independent_implementation'] is False and replay['python_guard_is_OS_sandbox'] is False,'worker replay scope')
    checks.append('all three worker outputs reproduced')
    cutoffs=CUTOFFS
    require(spec['cutoffs']==cutoffs and spec['dictionary_sha256']==digest(cutoffs),'frozen cutoff grammar mismatch')
    require(spec['targets']==['mu','c'],'actual target coverage')
    bridges=[dict(target=t,kappa=1 if t=='mu' else 2,conditional_only=True) for t in spec['targets']]
    checks.append('complete dictionary and conditional pole bridges')
    prior=spec['provenance']
    require(set(prior['prior_verifications'])=={'critical-core-results/pilot-001/verification.json'},
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
        expanded=list(scales)
        require(data['scales']==expanded,'complete parent/child block domain')
        require(0<=data['profile']['cost']<=spec['budgets']['arithmetic_work'],'declared work budget exceeded')
        audits[name]=independent.verify_profile(data['profile'],expanded,spec['targets'],cutoffs)
        no_promotions(data)
        checks.append('independent complete '+name+' arithmetic and features')
        print('Verified complete '+name+' prime-pair-forcing arithmetic', flush=True)
    batch=read(d/'candidate_batch.json'); validation=read(d/'validation.json'); proof=read(d/'proof_queue.json')
    require(batch['protocol_sha256']==digest(spec) and batch['training_sha256']==sha(d/'training.json'), 'candidate binding')
    require(validation['protocol_sha256']==digest(spec) and validation['validation_sha256']==sha(d/'validation_data.json'), 'validation binding')
    require(set(batch['access_denials'])=={'proof','final_cases','final_evaluation','prior_results'}
            and all(v is True for v in batch['access_denials'].values()), 'discovery access guard')
    checks.append('discovery dataflow guard receipts (not OS isolation)')
    factories=batch['factories']; require([f['target'] for f in factories]==spec['targets'],'factory target coverage')
    archives=[]; candidates={}
    for factory in factories:
        require(factory['training_scales']==spec['training_scales'] and factory['levels']==spec['levels'],'training domain changed')
        archives.append(check_archive(factory,training['profile'],cutoffs,spec['training_scales'],spec['levels']))
        for candidate in factory['candidates']:
            require(candidate['program_id'] not in candidates,'duplicate cross-target candidate')
            candidates[candidate['program_id']]=candidate
    checks.append('complete proposal archives, quantization, aliases and exact refits')
    require(len(validation['results'])==len(candidates) and
            {r['program_id'] for r in validation['results']}==set(candidates),'validation candidate coverage')
    for row in validation['results']:
        expected=exact_score(candidates[row['program_id']]['program'],validation_data['profile'],
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
        admission=item['conditional_admission'];target=item['exact_program']['target'];k=1 if target=='mu' else 2
        require(admission['status']=='admitted_conditional' and admission['conditional_bridge_admitted'] is True and admission['support_size']==1 and admission['minimum_surviving_pole_order']==k,'ordinary target bridge')
        require(item['kappa']==k and item['prefix_certificate']==independent.prefix_certificate(target,item['exact_program']['cutoff']) and item['prefix_certificate']['cofinal_critical_component_bound'] is True,'uniform signed decomposition recovery')
    checks.append('independent validation and diverse exact selection')
    require(len(final['results'])==len(chosen) and {r['program_id'] for r in final['results']}==set(chosen),'final selected coverage')
    counts=dict(passes=0,failures=0,missing=0,unresolved_intervals=0,dyadic_stored_constant_failures=0,offdomain_finite_failures=0)
    for row in final['results']:
        score=exact_score(candidates[row['program_id']]['program'],final['data']['profile'],cases['base_scales'],cases['levels'])
        require(row['score']==score,'independent final interval score mismatch')
        counts['passes']+=score['finite_passes'];counts['failures']+=score['finite_failures'];counts['missing']+=score['missing_cases'];counts['unresolved_intervals']+=score['unresolved_intervals']
        for obs in score['observations']:
            if obs['finite_pass'] is False:counts['dyadic_stored_constant_failures' if obs['X']&(obs['X']-1)==0 else 'offdomain_finite_failures']+=1
    checks.append('independent rigorous final scores with unknown constants missing')
    for value in (batch,validation,proof,final):no_promotions(value)
    checks.append('correct lower-bound direction, complete recovery and no full-bound promotion')
    require({name:sha(d/name) for name in INPUT_NAMES}==initial_inputs,'run changed during independent audit')
    for name,expected in spec['code_sha256'].items():
        require(sha(BASE/name)==sha(d/'frozen_source'/name)==expected,'source changed during audit')
    for name,expected in prior['prior_verifications'].items():
        require(sha(BASE/name)==expected,'prior verification changed during audit')
    checks.append('input and code bindings stable throughout audit')
    return dict(schema=1,all_passed=True,checks_passed=len(checks),checks=checks,
                input_sha256=initial_inputs,code_sha256=spec['code_sha256'],
                contract_tests_passed=int(test_match.group(1)),
                independent_profile_checks=audits,archives=archives,candidate_count=len(candidates),
                selected_count=len(chosen),final_counts=counts,conditional_bridges=bridges,
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
    print(json.dumps({k:result[k] for k in ('all_passed','checks_passed','candidate_count','selected_count','final_counts')}))
