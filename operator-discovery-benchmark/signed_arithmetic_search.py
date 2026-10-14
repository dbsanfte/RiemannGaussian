#!/usr/bin/env python3
"""Frozen, model-free signed arithmetic stencil and response discovery.

All-scale theorem admission is a separate, supplied proof backend. Numerical
signed estimates remain hypotheses, including those with a conditional RH bridge.
"""
import argparse
import builtins
from fractions import Fraction as Q
import hashlib
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

BASE = Path(__file__).resolve().parent
CODE = ['signed_arithmetic_search.py', 'signed_arithmetic_language.py',
        'signed_arithmetic_certificates.py', 'signed_arithmetic_proof.txt',
        'signed_arithmetic_report.py', 'check_signed_arithmetic_search.py',
        'test_signed_arithmetic_language.py', 'test_signed_arithmetic_certificates.py',
        'test_signed_arithmetic_search.py', 'signed_arithmetic_sampler.py',
        'test_signed_arithmetic_sampler.py']
SEALED = ['candidate_batch.json', 'validation.json', 'proof_queue.json']


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def floor_root(n, q):
    require(type(n) is int and n >= 0 and type(q) is int and q >= 1, 'invalid integer root')
    if n < 2 or q == 1:
        return n
    if q >= n.bit_length():
        return 1
    lo, hi = 0, 1 << ((n.bit_length() + q - 1) // q)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** q <= n:
            lo = mid
        else:
            hi = mid
    return lo


def moment_response(scale, degree):
    # Integrate t^degree K_scale(t) from the declared piecewise linear semantics.
    s, p = Q(scale), degree
    return s ** (p + 2) / (p + 1) + 2 * s * ((2*s)**(p+1)-s**(p+1))/(p+1) - ((2*s)**(p+2)-s**(p+2))/(p+2)


def solve_square(matrix, rhs):
    rows = [[Q(v) for v in row] + [Q(y)] for row,y in zip(matrix,rhs)]
    n=len(rows)
    for column in range(n):
        pivot=next((j for j in range(column,n) if rows[j][column]),None)
        if pivot is None:return None
        rows[column],rows[pivot]=rows[pivot],rows[column]
        scale=rows[column][column];rows[column]=[v/scale for v in rows[column]]
        for j in range(n):
            if j!=column:
                scale=rows[j][column];rows[j]=[a-scale*b for a,b in zip(rows[j],rows[column])]
    return [r[-1] for r in rows]


def generate(spec):
    scales = spec['stencil_scales']
    moments = [[moment_response(s, p) for s in scales] for p in spec['moment_degrees']]
    archive, rejected, seen = [], [], set()
    for size in range(2, spec['support_budget'] + 1):
        for support in combinations(range(len(scales)), size):
            for cancel in range(1,min(len(moments),size-1)+1):
                free=support[:-cancel]; solved=support[-cancel:]
                for raw in product(map(Q, spec['coefficient_grid']), repeat=len(free)):
                    rhs=[-sum((c*moments[p][i] for c,i in zip(raw,free)),Q(0)) for p in range(cancel)]
                    tail=solve_square([[moments[p][i] for i in solved] for p in range(cancel)],rhs)
                    if tail is None or any(c==0 for c in tail):
                        rejected.append({'support':list(support),'cancel_moments':cancel,'raw':list(map(str,raw)), 'reason':'degenerate_or_zero_solved_coefficient'})
                        continue
                    weights=[Q(0)]*len(scales)
                    for i,c in zip(support,(*raw,*tail)):weights[i]=c/tail[-1]
                    key=tuple(weights)
                    if key in seen:continue
                    seen.add(key)
                    if sum(map(abs,weights))>Q(spec['coefficient_norm_budget']) or max(c.denominator for c in weights)>spec['coefficient_denominator_budget']:
                        rejected.append({'weights':list(map(str,weights)),'reason':'finite_coefficient_resource_budget'})
                        continue
                    response=[sum((c*v for c,v in zip(weights,row)),Q(0)) for row in moments]
                    order=next((p for p,r in enumerate(response) if r),len(response))
                    bridge=all(c<=0 for c in weights[:support[-1]])
                    program={'scales':scales,'weights':list(map(str,weights))}
                    archive.append({'program_id':digest(program),'program':program,'support_size':size,
                        'annihilated_moment_count':order,'moment_responses':list(map(str,response)),
                        'nonnegative_critical_recurrence_bridge':bridge,
                        'conditional_bridge_scope':'requires complete signed stencil inequality at every dyadic scale and cofinal exponents' if bridge else 'signed recurrence stability unresolved',
                        'global_signed_bound_proved':False})
    return {'anonymous_moment_response_matrix':[[str(v) for v in row] for row in moments],
            'candidates':sorted(archive,key=lambda r:r['program_id']),'rejected':rejected}


def arithmetic_tables(scales, dilation_scales):
    from signed_arithmetic_language import complete_mobius
    N = 2 * max(scales) * max(dilation_scales) - 1
    result = complete_mobius(N)
    require(result.available, 'actual coefficient production unavailable')
    mu = result.value['coefficients']
    M, sf, energy, diagonal = [0], [0], [0], [0]
    for n in range(1, N+1):
        M.append(M[-1]+mu[n]); sf.append(sf[-1]+mu[n]*mu[n])
        energy.append(energy[-1]+M[-1]*M[-1]); diagonal.append(diagonal[-1]+sf[-1])
    rows = []
    projection_pairs=0; projection_gcd_trials=0
    for X in scales:
        B = floor_root(X, 3)
        basis = []
        for s in dilation_scales:
            Y = s*X
            projection = 0
            for r in range(2, B+1):
                if not mu[r]:
                    continue
                for a in range(1,r):
                    if not mu[a] or gcd(a,r) != 1:
                        continue
                    projection_pairs+=1; projection_gcd_trials+=(2*Y-1)//r
                    group = sum(mu[g]*mu[g]*(2*Y-max(Y,r*g)) for g in range(1,(2*Y-1)//r+1) if gcd(g,a*r)==1)
                    projection += 2*mu[a]*mu[r]*group
            basis.append({'scale': s, 'energy': energy[2*Y-1]-energy[Y-1],
                          'diagonal': diagonal[2*Y-1]-diagonal[Y-1], 'primitive_projection': projection})
        rows.append({'X': X, 'shared_primitive_cutoff': B, 'basis': basis})
    return {'rows': rows, 'coefficient_horizon': N, 'coefficient_provenance': result.value['provenance'],
            'producer_cost': result.value['cost'],
            'table_work':{'prefix_updates':N,'primitive_pairs':projection_pairs,'projection_gcd_trials':projection_gcd_trials,
                          'scope':'loop counts only; not complete bit or CPU cost certificate'},
            'prime_oracle_used_by_producer': False,
            'actual_coefficient_overlap_with_prior_development': True}


def response(candidate, row):
    w = list(map(Q,candidate['program']['weights']))
    full, diagonal, projected = (sum((c*Q(v[key]) for c,v in zip(w,row['basis'])),Q(0)) for key in ['energy','diagonal','primitive_projection'])
    return {'X':row['X'], 'full_signed_stencil':str(full), 'diagonal':str(diagonal),
            'primitive_projection':str(projected), 'dense_signed_residual':str(full-diagonal-projected),
            'complete_partition':True, 'shared_primitive_cutoff': row['shared_primitive_cutoff']}


def fit(candidate, rows, levels):
    from detector_safe_evaluation import rational_ceiling
    values = [response(candidate,r) for r in rows]
    constants = {}
    for q in levels:
        ratios = []
        for row in values:
            norm = rational_ceiling(row['X'],Q(1,q))
            require(norm.available,'fitted normalizer unavailable')
            ratios.append(Q(row['full_signed_stencil'])/(row['X']**2*norm.value))
        constants[str(q)] = str(max([Q(0)]+ratios))
    return {**candidate,'constants':constants,'training_signs':{k:sum((Q(r['full_signed_stencil'])>0 if k=='positive' else Q(r['full_signed_stencil'])==0 if k=='zero' else Q(r['full_signed_stencil'])<0) for r in values) for k in ['positive','zero','negative']}}


def score(candidate, rows, levels):
    from detector_safe_evaluation import rational_ceiling
    cases=[]
    for row in rows:
        value=response(candidate,row)
        for q in levels:
            norm=rational_ceiling(row['X'],Q(1,q))
            constant=candidate['constants'].get(str(q))
            available=norm.available and constant is not None
            bound=Q(constant)*row['X']**2*norm.value if available else None
            cases.append({'X':row['X'],'q':q,'value':value['full_signed_stencil'],
                          'bound':str(bound) if available else None,'finite_pass':Q(value['full_signed_stencil'])<=bound if available else None,
                          'status':'available' if available else 'missing',
                          'in_dyadic_claim_domain':row['X']&(row['X']-1)==0})
    return {'cases':cases,'passes':sum(c['finite_pass'] is True for c in cases),
            'failures':sum(c['finite_pass'] is False for c in cases),'missing':sum(c['finite_pass'] is None for c in cases)}


def root_dictionary(spec):
    features=[{'op':'constant'}]
    features += [{'op':'floor_root','q':q,'offset':offset} for q in spec['root_orders'] for offset in spec['root_offsets']]
    features += [{'op':'polynomial','power':p} for p in [2,3]]
    features += [{'op':'floor_div','divisor':d} for d in [2,3,6]]
    features += [{'op':'divisor_count'},{'op':'divisor_sum'}]
    return features


def feature_value(f,x):
    op=f['op']
    if op=='constant': return 1
    if op=='floor_root': return floor_root(max(0,x+f['offset']),f['q'])
    if op=='polynomial': return x**f['power']
    if op=='floor_div': return x//f['divisor']
    if op=='divisor_count': return sum(x%d==0 for d in range(1,x+1))
    if op=='divisor_sum': return sum(d for d in range(1,x+1) if x%d==0)
    raise ValueError('unknown feature')


def calibration_rows(indices):
    from signed_arithmetic_language import liouville_floor_sum
    rows=[]
    for x in indices:
        r=liouville_floor_sum(x)
        require(r.available,'calibration unavailable')
        rows.append({'x':x,'anonymous_target':r.value['signed_sum'],'unsigned_charge':r.value['unsigned_charge']})
    return rows


def infer_calibration(rows,features):
    y=[Q(r['anonymous_target']) for r in rows]
    columns=[[Q(feature_value(f,r['x'])) for r in rows] for f in features]
    retained=[]; attempts=0
    for size in [1,2]:
        for support in combinations(range(len(features)),size):
            attempts+=1
            if size==1:
                a=columns[support[0]]; pivot=next((i for i,v in enumerate(a) if v),None)
                if pivot is None: continue
                weights=[y[pivot]/a[pivot]]
            else:
                a,b=(columns[i] for i in support)
                pair=next(((i,j) for i in range(len(y)) for j in range(i+1,len(y)) if a[i]*b[j]!=a[j]*b[i]),None)
                if pair is None: continue
                i,j=pair; det=a[i]*b[j]-a[j]*b[i]
                weights=[(y[i]*b[j]-y[j]*b[i])/det,(a[i]*y[j]-a[j]*y[i])/det]
            if any(c==0 for c in weights): continue
            if all(sum(c*columns[k][i] for c,k in zip(weights,support))==target for i,target in enumerate(y)):
                terms=[{'weight':str(c),'feature':features[k]} for c,k in zip(weights,support)]
                retained.append({'program_id':digest(terms),'terms':terms,'support_size':size})
    return {'support_attempts':attempts,'retained':retained}


def calibration_score(candidate,rows):
    return [{'x':r['x'],'target':r['anonymous_target'],
             'prediction':str(sum(Q(t['weight'])*feature_value(t['feature'],r['x']) for t in candidate['terms'])),
             'finite_pass':sum(Q(t['weight'])*feature_value(t['feature'],r['x']) for t in candidate['terms'])==r['anonymous_target']} for r in rows]


def worker(directory):
    from detector_workflow_guard import require_verified_runtime
    require_verified_runtime()
    d=Path(directory).resolve(); spec=read(d/'protocol.json')
    require(not any((d/n).exists() for n in SEALED+['seal.json','failure.json']),'sealed or partial worker destination')
    # Python guard enforces declared file dataflow. This is not OS isolation.
    # Import arithmetic and exact-normalizer dependencies before applying it.
    import signed_arithmetic_language
    import signed_arithmetic_sampler as sampler
    import detector_safe_evaluation
    allowed={d/'protocol.json'}|{d/n for n in SEALED}
    original=builtins.open; original_path=Path.open; original_io=__import__('io').open
    def guarded(file,*args,**kwargs):
        if isinstance(file,(str,Path)) and Path(file).resolve() not in allowed:
            raise PermissionError('discovery file outside declared dataflow')
        return original(file,*args,**kwargs)
    def guarded_path(path,*args,**kwargs):
        if path.resolve() not in allowed: raise PermissionError('discovery path outside declared dataflow')
        return original_path(path,*args,**kwargs)
    builtins.open=guarded; __import__('io').open=guarded; Path.open=guarded_path
    try:
        denied={}
        for label,path in [('proof',BASE/'signed_arithmetic_proof.txt'),('final',d/'final_evaluation.json'),('historical_report',BASE/'root-results/report.txt')]:
            try: read(path); denied[label]=False
            except PermissionError: denied[label]=True
        generated=generate(spec)
        training=arithmetic_tables(spec['training_scales'],spec['stencil_scales'])
        candidates=[fit(c,training['rows'],spec['levels']) for c in generated.pop('candidates')]
        cr=calibration_rows(spec['calibration_training_indices']); features=root_dictionary(spec)
        ci=infer_calibration(cr,features)
        generation=sampler.sample_programs(**spec['ast_sampling'])
        require(generation.available,'AST generation unavailable')
        exploration={'generation':generation.value,
                     'training':sampler.evaluate_programs(generation.value['programs'],spec['ast_training_horizon'])}
        batch={'protocol_sha256':digest(spec),'ast_exploration':exploration,'access_denials':denied,**generated,
               'training':training,'candidates':candidates,'calibration':{'rows':cr,'dictionary':features,**ci}}
        write(d/'candidate_batch.json',batch)
        validation=arithmetic_tables(spec['validation_scales'],spec['stencil_scales'])
        scores=[{'program_id':c['program_id'],'score':score(c,validation['rows'],spec['levels'])} for c in candidates]
        cv=calibration_rows(spec['calibration_validation_indices'])
        ast_validation=sampler.evaluate_programs(generation.value['programs'],spec['ast_validation_horizon'])
        validation.update({'ast_exploration':ast_validation,'scores':scores,'calibration_rows':cv,'calibration_results':[{'program_id':c['program_id'],'cases':calibration_score(c,cv)} for c in ci['retained']]})
        write(d/'validation.json',validation)
        scoremap={r['program_id']:r['score'] for r in scores}; groups={}
        for c in candidates:
            group=(c['support_size'],c['annihilated_moment_count'],c['nonnegative_critical_recurrence_bridge'])
            rank=(scoremap[c['program_id']]['failures'],max(map(Q,c['constants'].values())),sum(map(abs,map(Q,c['program']['weights']))),c['program_id'])
            if group not in groups or rank<groups[group][0]: groups[group]=(rank,c)
        queue=[{**v[1],'validation_score':scoremap[v[1]['program_id']],
                'global_claim':'for every q>=q0, exists finite Cq independent of X, every dyadic X>=1: sum c_j A(s_j X) <= Cq X^2 ceil(X^(1/q))',
                'residual_obligation':'complete dense primitive signed residual retained; no all-scale upper estimate established'} for _,v in sorted(groups.items())]
        calibration_selected=[c for c in ci['retained'] if all(r['finite_pass'] for r in calibration_score(c,cv))]
        write(d/'proof_queue.json',{'protocol_sha256':digest(spec),'queue':queue,'calibration_queue':calibration_selected,
              'ast_queue':sampler.select_diverse(ast_validation['observations']),
              'candidate_ids_frozen_before_final':True,'final_used_for_selection':False,
              'selection_groups':['support_size','annihilated_moment_count','nonnegative_critical_recurrence_bridge']})
    finally:
        builtins.open=original; Path.open=original_path; __import__('io').open=original_io
    print(f'Sealed {len(candidates)} signed stencil candidates, {len(queue)} diverse leads, {len(calibration_selected)} arithmetic response laws.',flush=True)


def specification():
    dependencies=['detector_safe_evaluation.py','inverse_prefix_grammar.py','detector_workflow_guard.py']
    sources=['workflow-audit-results/audit-001/integration_verification.json',
             'workflow-audit-results/mobius-language-design-001/math_design.txt',
             'workflow-audit-results/mobius-language-design-001/search_design.txt',
             'workflow-audit-results/mobius-language-design-001/observables_design.txt']
    failures=[]
    for path in sorted((BASE/'signed-arithmetic-results').glob('*/failure.json')):
        failures.append({'path':str(path),'sha256':sha(path)})
    return {'version':'signed-arithmetic-v1','code_sha256':{n:sha(BASE/n) for n in CODE},
        'dependency_sha256':{n:sha(BASE/n) for n in dependencies},'input_sha256':{n:sha(BASE/n) for n in sources},
        'contract_test_modules':['test_signed_arithmetic_language','test_signed_arithmetic_certificates','test_signed_arithmetic_sampler','test_signed_arithmetic_search'],
        'stencil_scales':[1,2,4,8],'support_budget':4,'moment_degrees':[0,1,2],
        'coefficient_grid':['-16','-8','-4','-2','-1','-1/2','1/2','1','2','4','8','16'],
        'coefficient_norm_budget':'64','coefficient_denominator_budget':64,
        'training_scales':[1,2,4,8,16,32,64,128,512],
        'validation_scales':[192,256,384,768],'levels':[2,3,6,12],
        'ast_sampling':{'seed':19661008,'count':64,'max_depth':3},
        'ast_training_horizon':96,'ast_validation_horizon':160,
        'root_orders':[1,2,3,4,6,12],'root_offsets':[-1,0,1],
        'calibration_training_indices':list(range(1,49)),
        'calibration_validation_indices':[53,61,64,79,96,127,128,173,256],
        'final_rule':'seal-derived 3 distinct odd X in [1101,2401], plus2048,4096,8192; roots use seal-derived integers [3001,6000]',
        'known_development_coupled_scales':[16,64,256],'new_prime_coefficient_holdout_claimed':False,
        'every_final_response_previously_unobserved_claimed':False,
        'final_freshness_scope':'post-seal evaluation with file-separated discovery; standard stencil outcomes may overlap historical evidence',
        'supplied_bias':['piecewise linear block-energy kernels','dyadic dilation basis','zero density moments',
          'sparse rational root/count dictionary','nonnegative critical recurrence bridge','squarefree discrepancy certificate'],
        'learner_reads_proof_or_anticipated_coefficients':False,'model_calls_in_worker':False,
        'dataflow_guard_is_not_adversarial_OS_sandbox':True,'failed_runs':failures,
        'RH_proved':False,'actual_all_scale_signed_bound_proved':False}


def final_cases(seal_digest):
    seed=int(seal_digest[:16],16)
    scales=[]
    for j in range(3):
        x=1101+2*((seed>>(j*13))%651)
        while x in scales: x=1101+2*((x-1101)//2+1)%1302
        scales.append(x)
    indices=[]
    for j in range(5):
        x=3001+((seed>>(j*11))%3000)
        while x in indices: x=3001+(x-3000)%3000
        indices.append(x)
    return {'actual_scales':sorted(scales)+[2048,4096,8192],
            'calibration_indices':indices,'ast_horizon':257+seed%128,
            'seen_levels':[3,12],'unseen_levels':[13,17]}


def final(directory):
    from signed_arithmetic_language import coupled_response
    from signed_arithmetic_sampler import evaluate_programs
    from signed_arithmetic_certificates import kernel_from_dilates, certify_kernel, dilate_bridge_certificate, liouville_squarefloor_certificate, energy_bridge_obstruction_certificate, positive_energy_transform_certificate
    d=Path(directory); spec=read(d/'protocol.json'); seal=read(d/'seal.json'); queue=read(d/'proof_queue.json')
    for n,h in seal['files'].items(): require(sha(d/n)==h,'sealed source changed')
    cases={**final_cases(sha(d/'seal.json')),'seal_sha256':sha(d/'seal.json'),'generated_after_seal':True}
    write(d/'final_cases.json',cases)
    actual=arithmetic_tables(cases['actual_scales'],spec['stencil_scales'])
    results=[]
    for c in queue['queue']:
        kernel=kernel_from_dilates(list(zip(c['program']['scales'],map(Q,c['program']['weights']))))
        certificate=certify_kernel(kernel)
        results.append({'program_id':c['program_id'],'partition':[response(c,r) for r in actual['rows']],
            'score':score(c,actual['rows'],cases['seen_levels']+cases['unseen_levels']),
            'kernel_certificate':certificate,
            'bridge_certificate':dilate_bridge_certificate(list(zip(c['program']['scales'],map(Q,c['program']['weights']))),Q(1,12)),
            'positive_energy_transform':positive_energy_transform_certificate(list(zip(c['program']['scales'],map(Q,c['program']['weights']))),Q(1,12)),
            'energy_bridge_obstruction':energy_bridge_obstruction_certificate(list(zip(c['program']['scales'],map(Q,c['program']['weights'])))),
            'full_signed_bound_proved':False})
    coupled=[]
    for X in cases['actual_scales']:
        r=coupled_response(X); require(r.available,'coupled signed response missing')
        coupled.append(r.value)
    cr=calibration_rows(cases['calibration_indices'])
    cf=[]
    for c in queue['calibration_queue']:
        terms=[]
        for t in c['terms']:
            f=t['feature']; terms.append(({'kind':f['op'],**{k:v for k,v in f.items() if k!='op'}},Q(t['weight'])))
        cf.append({'program_id':c['program_id'],'cases':calibration_score(c,cr),
                   'certificate':liouville_squarefloor_certificate(terms)})
    controls=[]
    # Actual mu through L, then positive. Finite agreement is not a complete
    # inverse axiom, and must fail the exact divisor test above the prefix.
    from signed_arithmetic_language import complete_mobius
    L=spec['training_scales'][-1]; mu=complete_mobius(2*L).value['coefficients']; fake=mu[:L+1]+[1]*L
    for n in range(L+1,2*L+1):
        v=sum(fake[d] for d in range(1,n+1) if n%d==0)
        if v: controls.append({'n':n,'divisor_sum':v})
    write(d/'final_evaluation.json',{'actual':actual,'results':results,'coupled_responses':coupled,
        'calibration_rows':cr,'calibration_results':cf,
        'ast_exploration':evaluate_programs(queue['ast_queue'],cases['ast_horizon']),
        'counterfeit_tail':{'prefix':L,'checked_through':2*L,'violations':controls},
        'RH_proved':False,'actual_all_scale_signed_bound_proved':False})


def replay_worker(directory):
    d=Path(directory)
    with tempfile.TemporaryDirectory(prefix='signed-arithmetic-replay-') as temporary:
        t=Path(temporary);shutil.copyfile(d/'protocol.json',t/'protocol.json')
        completed=subprocess.run([sys.executable,str(BASE/'signed_arithmetic_search.py'),'worker',str(t)],cwd=BASE,check=True,capture_output=True,text=True)
        comparisons={n:{'original_sha256':sha(d/n),'replay_sha256':sha(t/n),'identical':sha(d/n)==sha(t/n)} for n in SEALED}
        require(all(row['identical'] for row in comparisons.values()),'discovery worker replay differs')
        record={'all_identical':True,'files':comparisons,'stdout':completed.stdout,
                'scope':'same frozen generator/selector reexecution with final/proof reads denied; independent numeric checker is separate',
                'independent_second_generator_implementation':False}
        write(d/'worker_replay.json',record)
        return record


def run(directory):
    from detector_workflow_guard import require_verified_runtime
    require_verified_runtime()
    d=Path(directory).resolve(); d.mkdir(parents=True,exist_ok=False)
    try:
        spec=specification(); write(d/'protocol.json',spec); (d/'frozen_source').mkdir()
        for n in CODE: shutil.copyfile(BASE/n,d/'frozen_source'/n)
        tested=subprocess.run([sys.executable,'-m','unittest',*spec['contract_test_modules'],'-v'],cwd=BASE,capture_output=True,text=True)
        (d/'contract_tests.txt').write_text(tested.stdout+tested.stderr)
        require(tested.returncode==0,'frozen contract tests failed')
        subprocess.run([sys.executable,str(BASE/'signed_arithmetic_search.py'),'worker',str(d)],cwd=BASE,check=True)
        write(d/'seal.json',{'protocol_sha256':digest(spec),'files':{n:sha(d/n) for n in ['protocol.json','contract_tests.txt']+SEALED},'final_responses_created':False})
        final(d)
        replay_worker(d)
        subprocess.run([sys.executable,str(BASE/'check_signed_arithmetic_search.py'),str(d)],cwd=BASE,check=True)
        from signed_arithmetic_report import summary,text_report
        s=summary(d); write(d/'summary.json',s); (d/'report.txt').write_text(text_report(s))
        write(BASE/'signed-arithmetic-results/latest.json',{'run_directory':str(d)})
        print(text_report(s))
    except BaseException as exc:
        write(d/'failure.json',{'type':type(exc).__name__,'message':str(exc),'successful':False})
        raise


if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('mode',choices=['run','worker']);parser.add_argument('directory')
    args=parser.parse_args(); globals()[args.mode](args.directory)
