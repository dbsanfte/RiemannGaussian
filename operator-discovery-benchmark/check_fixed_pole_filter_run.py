"""Independent factor-local/full-covariance audit for fixed-pole filter runs.

Imports only the separately implemented checker math, never producer coefficient
or search implementations. A conditional pole bridge is not a global estimate.
"""
import argparse
from fractions import Fraction
from itertools import combinations,product
import hashlib
import json
import os
from pathlib import Path
import sys
import fixed_pole_filter_checks as independent

BASE=Path(__file__).resolve().parent
D=independent.DIVISORS
TARGETS=independent.TARGETS
TWO=['-4','-3','-2','-1','-1/2','1/2','1','2','3','4']
THREE=['-2','-1','1','2']


def require(value,message):
    if not value:raise ValueError(message)


def require_runtime():
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
        raise RuntimeError('verified fixed-pole-filter runs require assertions enabled')


def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def q(value):return independent.rational(value)


def dictionary():
    return {'targets':TARGETS,'divisors':D,'leading_divisor':1,'leading_weight':'1','two_weights':TWO,'three_weights':THREE,
        'support_limit':'r+l','inference':'one pooled normalized Gram constrained least-squares minimizer per one/two nonleading divisor support; exact interior/edges/corners; singular missing with explicit grid fallback',
        'box':'8','quantization_denominator':64,
        'composition':'for each d>1 with d^2 in dictionary and each two-weight w, square (1+w D_d): weights1,2w,w^2 at1,d,d^2; retain exact pole support admission'}


def ceil_root(X,level):
    independent.integer(X,1);independent.integer(level,1)
    if X==1:return 1
    if level>=X.bit_length():return 2
    lo=1;hi=X
    while lo<hi:
        mid=(lo+hi)//2
        if mid**level<X:lo=mid+1
        else:hi=mid
    return lo


def records(data):
    value=data['value'] if 'status' in data else data
    return {(r['target']['r'],r['target']['l']):r for r in value['targets']}


def observed(program,data,scales):
    record=records(data).get((program['target']['r'],program['target']['l']))
    rows={} if record is None else {r['X']:r for r in record['moments']}
    energies={X:independent.filtered_energy(rows[X]['matrix'],program['filter']) for X in set(scales)|{2*x for x in scales} if X in rows}
    require(all(v>=0 for v in energies.values()),'negative full square energy')
    result={}
    for X in scales:
        reason='target_missing' if record is None else 'complete_scale_missing'
        result[('direct',X)]=(energies[X],None) if X in energies else (None,reason)
        result[('innovation',X)]=(energies[2*X]-energies[X],None) if X in energies and 2*X in energies else (None,reason)
    return result


def exact_refit(program,data,scales,levels):
    scales=sorted(set(scales));values=observed(program,data,scales);constants={};observations=[]
    for mode in ('direct','innovation'):
        constants[mode]={}
        for level in levels:
            maximum=Fraction(0);complete=True
            for X in scales:
                value,reason=values[(mode,X)];root=ceil_root(X,level)
                if value is None:
                    complete=False;observations.append({'mode':mode,'X':X,'level':level,'missing':True,'reason':reason});continue
                maximum=max(maximum,value/root)
                observations.append({'mode':mode,'X':X,'level':level,'observed':str(value),'root':root,'missing':False})
            constants[mode][str(level)]=str(maximum) if complete else None
    return constants,observations


def exact_score(program,data,scales,levels):
    scales=sorted(set(scales));values=observed(program,data,scales);modes={}
    for mode in ('direct','innovation'):
        observations=[]
        for X in scales:
            for level in levels:
                value,reason=values[(mode,X)];constant=program['constants'][mode].get(str(level));missing=value is None or constant is None
                bound=None if missing else q(constant)*ceil_root(X,level)
                observations.append({'X':X,'level':level,'observed':None if value is None else str(value),'bound':None if bound is None else str(bound),
                    'margin':None if bound is None else str(bound-value),'missing':missing,
                    'reason':(reason or ('unknown_level_constant' if constant is None else None)) if missing else None,
                    'finite_pass':None if missing else value<=bound,'global_bound_proved':False})
        modes[mode]={'observations':observations,'finite_passes':sum(r['finite_pass'] is True for r in observations),'finite_failures':sum(r['finite_pass'] is False for r in observations),
                     'missing_cases':sum(r['missing'] for r in observations),'finite_cases':len(observations)}
    return {'modes':modes,'global_bound_proved':False}


def verify_admission(certificate,program):
    target=program['target'];terms=independent.canonical_filter(program['filter']);native=independent.conditional_certificate(**target,terms=terms)
    k=target['r']+target['l'];m=len(terms)
    require(native['conditional_bridge_admitted'],'fixed filter exceeds pole budget')
    require(certificate['target']=={'mu_arity':target['r'],'liouville_arity':target['l'],'total_arity':k,
        'sequence':'actual complete Dirichlet convolution mu^{*r}*lambda^{*l}','dirichlet_series':'zeta(2s)^l/zeta(s)^(r+l)','prefix':'A(x)=sum_(n<=x)a(n)'},'conditional bridge actual target changed')
    require(certificate['schema']==1 and certificate['filter']==terms and certificate['support_size']==m and
            certificate['conditional_bridge_admitted'] is True and certificate['estimate_proved'] is False and certificate['RH_proved'] is False and
            certificate['maximum_filter_zero_multiplicity']==m-1 and certificate['minimum_surviving_pole_order']==k-m+1 and
            certificate['status']=='admitted_conditional' and certificate['reason'] is None,'pole budget admission/estimate overclaim')
    require(certificate['filter_semantics']=='G(x)=sum_j w_j A(floor(x/d_j)); fixed positive integer d_j','filter semantics altered')
    return native


def verify_dataset(data,base_scales,work_budget=1000000000,max_n=1048575):
    base_scales=sorted(set(base_scales));scales=sorted(set(base_scales)|{2*X for X in base_scales});N=4*max(base_scales)-1
    require(data['status']=='available' and data['reason'] is None and data['lookahead']==N and N<=max_n,'complete actual dataset unavailable')
    require(type(data['cost']) is int and 0<=data['cost']<=work_budget,'invalid dataset work proxy')
    value=data['value'];require(value['base_scales']==base_scales and value['scales']==scales and value['dictionary_sha256']==digest(dictionary()) and value['global_bound_proved'] is False,'dataset scale/dictionary mismatch')
    require([r['target'] for r in value['targets']]==TARGETS,'missing/reordered actual targets')
    structure=independent.factor_structure(N);products=0
    for target,record in zip(TARGETS,value['targets']):
        coefficients=independent.actual_coefficients(N,**target,structure=structure);sums=independent.prefix(coefficients)
        require(all(type(v) is int for v in record['coefficients']) and all(type(v) is int for v in record['prefix']),'exact integer actual arrays required')
        require(record['coefficients']==coefficients and record['prefix']==sums and record['divisors']==D,'factor-local actual coefficients/prefix/divisors mismatch')
        require([r['X'] for r in record['moments']]==scales,'full covariance block missing')
        maximum=max(map(abs,sums))
        for row,X in zip(record['moments'],scales):
            independent.integer(row['X'],1)
            require(row['complete_block'] is True and row['matrix']==independent.covariance(sums,X),'full signed covariance mismatch')
            bound=maximum*maximum*X
            require(row['int64_absolute_sum_bound']==str(bound),'int64 safety charge mismatch')
            require(row['backend'] in ('numpy_int64_proved_safe','python_integer'),'unknown covariance implementation scope')
            if row['backend']=='numpy_int64_proved_safe':require(bound<2**63,'unsafe int64 moment arithmetic')
            products+=X*len(D)*(len(D)+1)//2
    return {'coefficient_horizon':N,'targets':len(TARGETS),'expanded_scales':len(scales),'independent_integer_covariance_products':products,'full_covariance_verified':True}


def proposal_schedule():
    """Every prescribed production, including singular inference attempts."""
    for target in TARGETS:
        k=target['r']+target['l']
        yield {'kind':'baseline','target':target},[(1,1)]
        if k>=2:
            for d,w in product(D[1:],TWO):yield {'kind':'grid_two','target':target,'divisor':d,'weight':w},[(1,1),(d,w)]
        if k>=3:
            for ds in combinations(D[1:],2):
                for ws in product(THREE,repeat=2):yield {'kind':'grid_three','target':target,'divisors':list(ds),'weights':list(ws)},[(1,1)]+list(zip(ds,ws))
            for d in D[1:]:
                if d*d in D:
                    for w in TWO:
                        weight=q(w);yield {'kind':'composition_square','target':target,'divisor':d,'source_weight':w,'formula':'(1+w D_d)^2'},[(1,1),(d,2*weight),(d*d,weight*weight)]
        for size in range(1,k):
            for support in combinations(D[1:],size):yield {'kind':'inferred','target':target,'support':list(support)},None


def verify_archive(factory,data,scales,levels):
    require(factory['schema']==1 and factory['dictionary_sha256']==digest(dictionary()) and factory['training_scales']==sorted(set(scales)) and factory['levels']==list(levels) and factory['global_bound_proved'] is False,'candidate factory scope changed')
    records_by_target=records(data);pool={}
    for target in TARGETS:
        record=records_by_target[(target['r'],target['l'])];rows={r['X']:r for r in record['moments']}
        pool[(target['r'],target['l'])]=[[sum(q(rows[X]['matrix'][i][j]) for X in sorted(set(scales))) for j in range(len(D))] for i in range(len(D))]
    archive=factory['proposal_archive'];schedule=list(proposal_schedule());require(len(archive)==len(schedule),'missing/excess grid/composition/inference attempts')
    archived_candidates={c['program_id']:c for c in factory['candidates']}
    require(len(archived_candidates)==len(factory['candidates']),'duplicate candidate IDs')
    candidates={};missing=aliases=0
    for proposal,(origin,terms) in zip(archive,schedule):
        target=origin['target'];expected_origin=dict(origin)
        if origin['kind']=='inferred':
            solver=independent.boxed_least_squares(pool[(target['r'],target['l'])],origin['support']);expected_origin['solver']=solver
            require(proposal['origin']==expected_origin,'exact pooled box minimizer/provenance mismatch')
            if solver['status']!='available':
                require(proposal['status']=='missing' and proposal['reason']==solver['reason'] and proposal['discarded'] is True and 'exact_program' not in proposal,'singular inference not preserved')
                missing+=1;continue
            terms=[(1,1)]+list(zip(origin['support'],solver['quantized_weights']))
        else:require(proposal['origin']==expected_origin,'grid/composition production changed')
        terms=independent.canonical_filter(terms);require(any(t=={'divisor':1,'weight':'1'} for t in terms),'leading1 normalization absent')
        base={'target':target,'filter':terms};constants,fit_observations=exact_refit(base,data,scales,levels);program={**base,'constants':constants};pid=digest(program)
        require(proposal['exact_program']==program and proposal['program_id']==pid and proposal['fit_observations']==fit_observations,'exact program/refit/hash mismatch')
        if pid in candidates:
            require(proposal['alias_of']==pid and proposal['discarded'] is True,'alias discarded without provenance')
            candidates[pid]['origins'].append(expected_origin);aliases+=1
        else:
            require(proposal['alias_of'] is None and proposal['discarded'] is False,'new candidate improperly discarded')
            # Compare native symbolic admission to the archived backend fields.
            archived=archived_candidates.get(pid);require(archived is not None,'candidate missing from factory')
            verify_admission(archived['admission'],program)
            candidates[pid]={'program_id':pid,'program':program,'admission':archived['admission'],'origins':[expected_origin],'training_score':exact_score(program,data,scales,levels)}
    require(factory['candidates']==list(candidates.values()),'candidate score/archive/alias completeness mismatch')
    return {'candidate_count':len(candidates),'proposal_count':len(schedule),'singular_inference_attempts':missing,'alias_count':aliases,'exact_box_minimizers_and_quantization_verified':True,
            'conditional_pole_bridges_verified':len(candidates),'actual_critical_energy_estimate_proved':False}


CLAIM=('For the exact actual target and fixed filter specified by the program, '
       'there exists an integer q0>=1 such that for every integer q>=q0 there '
       'exists finite Kq>=0 independent of X such that for every dyadic integer '
       'X>=1, sum_(n=X)^(2X-1)|G(n)|^2 <= Kq X^2 ceil(X^(1/q)). '
       'Here a=mu^{*r}*lambda^{*l}, A(x)=sum_(n<=x)a(n), and '
       'G(x)=sum_j w_j A(floor(x/d_j)); all coefficients, terms and boundaries '
       'are retained. Stored direct and innovation constants are finite fits, '
       'not assertions of the unknown existential constants.')
CODE_NAMES={'run_fixed_pole_filter.py','test_run_fixed_pole_filter.py','fixed_pole_filter_search.py','test_fixed_pole_filter_search.py',
    'fixed_pole_filter_checks.py','test_fixed_pole_filter_checks.py','check_fixed_pole_filter_run.py','test_check_fixed_pole_filter_run.py',
    'arithmetic_filter_pole_budget.py','arithmetic_filter_pole_budget_proof.txt','test_arithmetic_filter_pole_budget.py','detector_safe_evaluation.py',
    'inverse_prefix_grammar.py','detector_workflow_guard.py','prime_power_pairing.py','prime_power_pairing_proof.txt','test_prime_power_pairing.py'}
SEALED_NAMES={'protocol.json','contract_tests.txt','source_seal.json','worker_replay.json','training.json','validation_data.json','candidate_batch.json','validation.json','proof_queue.json'}
INPUT_NAMES=sorted(SEALED_NAMES|{'seal.json','final_cases.json','final_evaluation.json'})


def checked_path(base,name):
    require(isinstance(name,str) and name and not Path(name).is_absolute(),'relative artifact name required')
    result=(Path(base)/name).resolve();require(result.is_relative_to(Path(base).resolve()),'file binding escapes root')
    return result


def verify_hashes(base,mapping):
    require(isinstance(mapping,dict) and mapping,'nonempty hashes required')
    for name,value in mapping.items():require(sha(checked_path(base,name))==value,'hash mismatch: '+name)


def reject_promotions(value):
    forbidden={'RH_proved','estimate_proved','actual_all_scale_signed_bound_proved','global_bound_proved','ordinary_signed_energy_bound_proved',
               'actual_critical_energy_estimate_proved','global_signed_upper_bound_proved','actual_signed_upper_bound_proved'}
    if isinstance(value,dict):
        for key,item in value.items():
            if key in forbidden:require(item is False,'conditional/finite record promotes '+key)
            reject_promotions(item)
    elif isinstance(value,list):
        for item in value:reject_promotions(item)


def exact_selection(factory,results):
    candidates=factory['candidates'];scores={r['program_id']:r['score'] for r in results};baselines={}
    def key(candidate):return (candidate['program']['target']['r'],candidate['program']['target']['l'])
    for candidate in candidates:
        if len(candidate['program']['filter'])==1:baselines[key(candidate)]=candidate
    require(set(baselines)=={(t['r'],t['l']) for t in TARGETS},'target baseline missing')
    def maximum(candidate,mode):return max([q(x) for x in candidate['program']['constants'][mode].values() if x is not None] or [Fraction(0)])
    def rank(candidate,baseline=None):
        score=scores[candidate['program_id']];constants=candidate['program']['constants']
        missing=sum(r['missing_cases'] for r in score['modes'].values())+sum(x is None for row in constants.values() for x in row.values())
        failures=sum(r['finite_failures'] for r in score['modes'].values());direct=maximum(candidate,'direct');innovation=maximum(candidate,'innovation')
        if baseline is not None:
            direct/=max(Fraction(1),maximum(baseline,'direct'));innovation/=max(Fraction(1),maximum(baseline,'innovation'))
        terms=candidate['program']['filter']
        return (missing,failures,direct,innovation,sum(abs(q(t['weight'])) for t in terms if t['divisor']!=1),len(terms),candidate['program_id'])
    selected={};decisions=[]
    for group,target in [('target',t) for t in TARGETS]+[('c_baseline',None),('composition_square',None),('inferred',None)]:
        if group=='target':eligible=[c for c in candidates if c['program']['target']==target]
        elif group=='c_baseline':eligible=[baselines[(1,1)]]
        else:eligible=[c for c in candidates if any(o['kind']==group for o in c['origins'])]
        def order(candidate):return rank(candidate,baselines[key(candidate)] if group in ('composition_square','inferred') else None)
        chosen=min(eligible,key=order) if eligible else None;label={'kind':group,'target':target}
        decisions.append({'group':label,'eligible_ids':sorted(c['program_id'] for c in eligible),'selected_id':None if chosen is None else chosen['program_id'],
            'rank':None if chosen is None else [str(v) if isinstance(v,Fraction) else v for v in order(chosen)]})
        if chosen is None:continue
        pid=chosen['program_id']
        if pid not in selected:
            selected[pid]={'program_id':pid,'exact_program':chosen['program'],'exact_program_sha256':digest(chosen['program']),
                'global_claim':CLAIM,'precise_claim_sha256':digest(CLAIM),'conditional_admission':chosen['admission'],
                'selection_origins':[],'validation_score':scores[pid],'global_bound_proved':False}
        selected[pid]['selection_origins'].append(label)
    return sorted(selected.values(),key=lambda c:c['program_id']),decisions


def audit_dataset(wrapper,spec,scales):
    require(wrapper['protocol_sha256']==digest(spec),'dataset/protocol binding mismatch')
    return verify_dataset(wrapper['data'],scales,work_budget=spec['budgets']['work'],max_n=spec['budgets']['max_n'])


def audit_run(directory):
    require_runtime();directory=Path(directory).resolve();require(not (directory/'failure.json').exists(),'failed run cannot be promoted')
    inputs={name:sha(directory/name) for name in INPUT_NAMES};spec=read(directory/'protocol.json');source=read(directory/'source_seal.json');seal=read(directory/'seal.json')
    require(spec['schema']==1 and spec['version']=='fixed-pole-filter-v1','unsupported fixed-filter protocol')
    require(set(spec['code_sha256'])==CODE_NAMES,'incomplete/unsupported code freeze')
    verify_hashes(BASE,spec['code_sha256']);verify_hashes(directory/'frozen_source',spec['code_sha256'])
    require(spec['dictionary']==dictionary() and spec['dictionary_sha256']==digest(dictionary()) and spec['global_claim']==CLAIM,'frozen target/filter/claim dictionary changed')
    require(spec['levels']==[2,3,6,12] and spec['final_levels']==[3,12,17,29],'unsupported normalizer levels')
    require(spec['budgets']['bit']==1000000,'unsupported rational normalizer resource budget')
    for value in spec['budgets'].values():independent.integer(value,1)
    require(spec['training_scales']==[2**j for j in range(14)] and spec['validation_scales']==[12288,16384,24576],'scale selection program changed')
    require(spec['selection']=={'groups':'one per target plus c baseline, best composition and best inferred',
        'rank':['missing','validation_failures_both_modes','max_direct_training_constant','max_innovation_training_constant','nonleading_l1','support','program_id'],
        'cross_target_normalization':'constants divided by max(1, own-target baseline constant)'},'selection rule changed')
    require(spec['runtime']['python']==sys.version,'frozen interpreter mismatch')
    provenance=spec['provenance'];require(provenance['coefficient_history_overlap'] is True and provenance['unseen_prime_holdout'] is False and provenance['actual_all_scale_signed_bound_proved'] is False,'novelty/bound provenance overclaim')
    verify_hashes(BASE,provenance['prior_verifications'])
    require(source['protocol_sha256']==digest(spec) and source['code_sha256']==spec['code_sha256'] and source['tests_passed'] is True and source['source_frozen_before_data'] is True,'source freeze binding mismatch')
    tests=source['tests'];expected_tests={Path(name).stem for name in CODE_NAMES if name.startswith('test_')}
    require(len(tests)==len(set(tests)) and set(tests)==expected_tests,'contract test completeness mismatch')
    require(source['contract_tests_sha256']==sha(directory/'contract_tests.txt'),'contract test hash mismatch')
    log=(directory/'contract_tests.txt').read_text();require('\nOK\n' in log and 'FAILED (' not in log and 'Ran ' in log,'stored contract tests failed')
    require(seal['protocol_sha256']==digest(spec) and set(seal['files'])==SEALED_NAMES and seal['selection_closed'] is True,'selection seal binding mismatch')
    verify_hashes(directory,seal['files'])
    replay=read(directory/'worker_replay.json');require(replay=={'files_match':{name:True for name in ('candidate_batch.json','validation.json','proof_queue.json')},'independent_implementation':False,'python_guard_is_OS_sandbox':False},'worker replay scope mismatch')
    training=read(directory/'training.json');validation_data=read(directory/'validation_data.json');batch=read(directory/'candidate_batch.json');validation=read(directory/'validation.json');queue=read(directory/'proof_queue.json')
    for record in (spec,source,seal,training,validation_data,batch,validation,queue):reject_promotions(record)
    require(batch['protocol_sha256']==digest(spec) and batch['training_sha256']==sha(directory/'training.json'),'training factory binding mismatch')
    require(batch['access_denials']=={'proof':True,'final':True,'cases':True,'prior_results':True},'discovery guard failed')
    require(validation['protocol_sha256']==digest(spec) and validation['validation_sha256']==sha(directory/'validation_data.json'),'validation source binding mismatch')
    require(queue['protocol_sha256']==digest(spec) and queue['final_used_for_selection'] is False and queue['candidate_ids_frozen_before_final'] is True,'queue/final sequencing mismatch')
    train_checks=audit_dataset(training,spec,spec['training_scales']);archive_checks=verify_archive(batch['factory'],training['data'],spec['training_scales'],spec['levels'])
    validation_checks=audit_dataset(validation_data,spec,spec['validation_scales'])
    expected_validation=[{'program_id':candidate['program_id'],'score':exact_score(candidate['program'],validation_data['data'],spec['validation_scales'],spec['levels'])} for candidate in batch['factory']['candidates']]
    require(validation['results']==expected_validation,'all-candidate direct/innovation validation mismatch')
    selected,decisions=exact_selection(batch['factory'],expected_validation)
    require(queue['queue']==selected and queue['selection_decisions']==decisions,'exact selection/conditional admission mismatch')
    require(spec['final_generation']=={'fixed':[32768,65536],'odd_min':40001,'odd_count':5000,'formula':'40001+2*(int(seal_sha256[:16],16)%5000)'},'final generation program changed')
    cases=read(directory/'final_cases.json');seal_hash=sha(directory/'seal.json');odd=40001+2*(int(seal_hash[:16],16)%5000)
    expected_cases={'protocol_sha256':digest(spec),'seal_sha256':seal_hash,'base_scales':sorted([32768,65536,odd]),'levels':spec['final_levels'],'generated_after_seal':True}
    require(cases==expected_cases and len(set(cases['base_scales']))==3,'post-seal heldout scales/levels mismatch')
    final=read(directory/'final_evaluation.json');reject_promotions(final)
    require(final['protocol_sha256']==digest(spec) and final['cases_sha256']==sha(directory/'final_cases.json') and final['global_bound_proved'] is False,'final source/bound binding mismatch')
    final_checks=audit_dataset(final['data'],spec,cases['base_scales'])
    expected_final=[{'program_id':candidate['program_id'],'score':exact_score(candidate['exact_program'],final['data']['data'],cases['base_scales'],cases['levels'])} for candidate in selected]
    require(final['results']==expected_final,'final complete direct/innovation scores mismatch')
    counts={mode:{'passes':0,'failures':0,'missing':0,'dyadic_stored_constant_failures':0,'offdomain_finite_failures':0} for mode in ('direct','innovation')}
    for result in expected_final:
        for mode,score in result['score']['modes'].items():
            for observation in score['observations']:
                status=observation['finite_pass'];counts[mode]['missing' if status is None else 'passes' if status else 'failures']+=1
                if status is False:counts[mode]['dyadic_stored_constant_failures' if observation['X']&(observation['X']-1)==0 else 'offdomain_finite_failures']+=1
                if observation['level'] not in spec['levels']:require(status is None and observation['reason']=='unknown_level_constant','unknown level promoted')
    verify_hashes(directory,inputs);verify_hashes(BASE,spec['code_sha256']);verify_hashes(directory/'frozen_source',spec['code_sha256']);verify_hashes(BASE,provenance['prior_verifications'])
    return {'schema':1,'all_passed':True,'checks_passed':17,'input_sha256':inputs,'code_sha256':spec['code_sha256'],
        'independent_profile_checks':{'training':train_checks,'validation':validation_checks,'final':final_checks},'archive':archive_checks,
        'selected_count':len(selected),'final_counts':counts,'mathematical_audit_imports_production_code':False,
        'independent_coefficient_method':'prime factorization and exact (1-z)^(r+l)/(1-z^2)^l Euler-local coefficients',
        'independent_covariance_method':'complete Python arbitrary-precision integer dot products for every matrix entry',
        'all_signed_cross_terms_retained':True,'fixed_filter_pole_admission_is_conditional_only':True,
        'worker_replay_independent_second_implementation':False,'Python_guard_is_OS_sandbox':False,'formal_machine_checked_proof':False,
        'actual_all_scale_signed_bound_proved':False,'estimate_proved':False,'global_bound_proved':False,'RH_proved':False,
        'scope':'Complete finite target coefficients, matrices, filter weights, exact minimizers, refits, both scores, archive/selection, hashes and post-seal dataflow. Conditional pole-multiplicity algebra does not establish any actual critical-energy estimate.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory',type=Path);args=parser.parse_args();require_runtime()
    if (args.directory/'verification.json').exists():raise FileExistsError('successful verification cannot be overwritten')
    result=audit_run(args.directory)
    with (args.directory/'verification.json').open('x') as stream:stream.write(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
