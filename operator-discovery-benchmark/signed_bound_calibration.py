#!/usr/bin/env python3
"""Blind numeric signed-bound calibration, separate from actual-prime research.

Discovery consumes only anonymous integer response arrays. The finite product,
residue and moment feature dictionary and the post-freeze proof method are
supplied biases. No target coefficient vector is supplied to discovery.
"""
import argparse
from fractions import Fraction as Q
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import random

BASE = Path(__file__).resolve().parent
A_FEATURES = ('T*S', 'T*b', 'T', 'S', 'b', 'one')
D_FEATURES = ('T*S_r', 'b*T_r', 'T', 'T_r', 'S_r', 'one')
CANDIDATE_BASES = (2,3,4,5,6)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    with Path(path).open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def generator(seed, mode='signed', delay=1024, bases=(2,3,4)):
    rng = random.Random(seed)
    b = rng.choice(tuple(bases))
    options = [list(w) for w in product((-1, 0, 1), repeat=b-1) if sum(w) == -1]
    weights = [1] + rng.choice(options)
    if mode == 'positive':
        weights = list(map(abs, weights))
    return {'base': b, 'weights': weights, 'mode': mode, 'delay': delay if mode == 'delayed' else None}


def validate_spec(spec):
    b,w,mode=spec['base'],spec['weights'],spec['mode']
    if type(b) is not int or b not in CANDIDATE_BASES or len(w)!=b or w[0]!=1 or any(type(v) is not int or abs(v)>1 for v in w):
        raise ValueError('invalid unit-leading bounded integer digit generator')
    if mode in ('signed','delayed') and sum(w)!=0:
        raise ValueError('signed generator must have zero digit mass')
    if mode=='positive' and (any(v<0 for v in w) or sum(w)<2):
        raise ValueError('positive control must be nonnegative and noncancelling')
    if mode not in ('signed','positive','delayed'):
        raise ValueError('unknown generator mode')
    if mode=='delayed' and (type(spec['delay']) is not int or spec['delay']<1):
        raise ValueError('positive integer delay required')


def coefficient(spec, n):
    if type(n) is not int or n < 0:
        raise ValueError('nonnegative integer index required')
    if spec['mode'] == 'delayed' and n >= spec['delay']:
        return 1
    b, w = spec['base'], spec['weights']
    answer = 1
    while n:
        n, d = divmod(n, b)
        answer *= w[d]
    return answer


def response(spec, horizon):
    validate_spec(spec)
    a = [coefficient(spec, n) for n in range(horizon)]
    M, G, H = [0], [0], [0]
    for value in a:
        H.append(H[-1] + M[-1] ** 2)
        M.append(M[-1] + value)
        G.append(G[-1] + value ** 2)
    return {'a': a, 'M': M, 'G': G, 'H': H}


def independent_response(spec, horizon):
    validate_spec(spec)
    # Repeated parent recursion, distinct from digit-product evaluation above.
    b, w = spec['base'], spec['weights']
    a = [1]
    for n in range(1, horizon):
        a.append(1 if spec['mode'] == 'delayed' and n >= spec['delay']
                 else a[n // b] * w[n % b])
    # Before the override, every parent is before it too. Beyond the override
    # its definition is exactly 1, so the recursive replay is complete.
    M, G, H = [0], [0], [0]
    for n in range(horizon):
        H.append(H[-1] + M[n] ** 2)
        M.append(M[n] + a[n])
        G.append(G[n] + a[n] ** 2)
    return {'a': a, 'M': M, 'G': G, 'H': H}


def solve(A, y):
    if not A or len(A) != len(y):
        return None
    width = len(A[0]); rows = [[Q(v) for v in row] + [Q(t)] for row,t in zip(A,y)]
    cursor, pivots = 0, []
    for col in range(width):
        index = next((j for j in range(cursor,len(rows)) if rows[j][col]), None)
        if index is None:
            continue
        rows[cursor], rows[index] = rows[index], rows[cursor]
        scale = rows[cursor][col]; rows[cursor] = [v/scale for v in rows[cursor]]
        for j in range(len(rows)):
            if j != cursor and rows[j][col]:
                scale = rows[j][col]
                rows[j] = [v-scale*w for v,w in zip(rows[j],rows[cursor])]
        pivots.append(col); cursor += 1
    if any(not any(row[:width]) and row[width] for row in rows) or len(pivots) != width:
        return None
    return [rows[j][width] for j in range(width)]


def local_candidates(data, parents=64, fit_moment=True):
    """Numeric-only per-instance learner; no seed, weights or mode is read."""
    a, M, G, H = (data[key] for key in ('a','M','G','H'))
    output = []
    for b in CANDIDATE_BASES:
        item = {'base': b, 'status': 'finite_rejected', 'missing': False}
        if b*parents > len(a):
            item.update(status='missing',missing=True,reason='response_horizon'); output.append(item); continue
        q, alphas, beta = [], [], []
        for d in range(b):
            result = solve([[a[n]] for n in range(parents)], [a[b*n+d] for n in range(parents)])
            prefix = solve([[M[n],a[n]] for n in range(parents)], [M[b*n+d] for n in range(parents)])
            if result is None or prefix is None:
                break
            q.append(result[0]); alphas.append(prefix[0]); beta.append(prefix[1])
        if len(q) != b or len(set(alphas)) != 1:
            item['reason'] = 'no_exact_digit_and_prefix_rule'; output.append(item); continue
        item.update(status='finite_rule_fit', digit_weights=list(map(str,q)),
                    prefix_alpha=str(alphas[0]), prefix_beta=list(map(str,beta)))
        if fit_moment:
            matrix, target = [], []
            for N in range(parents):
                m,r = divmod(N,b)
                matrix.append([G[m]]+[a[m]**2 * int(r==d) for d in range(b)])
                target.append(H[b*N]-b*H[N])
            model = solve(matrix,target)
            if model is None:
                item['moment_rule'] = None; item['moment_status'] = 'finite_rejected'
            else:
                item['moment_rule'] = {'bulk':str(model[0]),'residues':list(map(str,model[1:]))}
                item['moment_status'] = 'finite_rule_fit'
        output.append(item)
    return output


def sparse_rule(rows, targets, names):
    fits = []
    for size in (1,2):
        for slots in combinations(range(len(names)),size):
            values = solve([[row[i] for i in slots] for row in rows],targets)
            if values is not None and all(values):
                fits.append({'terms':[[names[i],str(v)] for i,v in zip(slots,values)],'slots':list(slots)})
        if fits:
            break
    fits.sort(key=lambda item:(item['slots'],json.dumps(item['terms'])))
    return {'selected':fits[0] if fits else None,'retained_minimum_support_fits':fits,
            'feature_dictionary':list(names),'expected_coefficients_supplied':False}


def statistics(candidate):
    b=candidate['base'];q=list(map(Q,candidate['digit_weights']));beta=list(map(Q,candidate['prefix_beta']))
    return b,q,beta,sum(v*v for v in q),sum(v*v for v in beta)


def infer_shared_rules(candidates):
    Arows,Atarget,Drows,Dtarget=[],[],[],[]
    for c in candidates:
        if c['status'] != 'finite_rule_fit' or c.get('moment_rule') is None or Q(c['prefix_alpha']) != 0:
            continue
        b,q,beta,S,T=statistics(c)
        Arows.append([T*S,T*b,T,S,b,1]);Atarget.append(Q(c['moment_rule']['bulk']))
        for r in range(b):
            Sr=sum(v*v for v in q[:r]);Tr=sum(v*v for v in beta[:r])
            Drows.append([T*Sr,b*Tr,T,Tr,Sr,1]);Dtarget.append(Q(c['moment_rule']['residues'][r]))
    return {'bulk':sparse_rule(Arows,Atarget,A_FEATURES),
            'boundary':sparse_rule(Drows,Dtarget,D_FEATURES),
            'coefficient_response_rows':[len(Arows),len(Drows)],'rule_is_numeric_inference':True}


def evaluate_rule(rule, values):
    if rule['selected'] is None:
        raise ValueError('no inferred shared coefficient rule')
    return sum(Q(v)*values[name] for name,v in rule['selected']['terms'])


def instantiate(candidate, rules):
    if candidate['status'] != 'finite_rule_fit':
        return dict(candidate)
    b,q,beta,S,T=statistics(candidate)
    A=evaluate_rule(rules['bulk'],dict(zip(A_FEATURES,[T*S,T*b,T,S,b,1])))
    ds=[]
    for r in range(b):
        Sr=sum(v*v for v in q[:r]);Tr=sum(v*v for v in beta[:r])
        ds.append(evaluate_rule(rules['boundary'],dict(zip(D_FEATURES,[T*Sr,b*Tr,T,Tr,Sr,1]))))
    out=dict(candidate);out['moment_rule']={'bulk':str(A),'residues':list(map(str,ds))}
    out['moment_rule_origin']='frozen_shared_rule_no_new_moment_fit';return out


def global_digit_agreement(spec, b, q):
    original=spec['base'];w=spec['weights']
    def power_index(big,small):
        value,j=1,0
        while value<big:value*=small;j+=1
        return j if value==big else None
    j=power_index(b,original)
    if j is not None:
        return q==[Q(coefficient({**spec,'mode':'signed','delay':None},d)) for d in range(b)]
    j=power_index(original,b)
    if j is not None:
        def value(n):
            v=Q(1)
            while n:n,d=divmod(n,b);v*=q[d]
            return v
        return [value(d) for d in range(original)]==list(map(Q,w))
    return False


def certificate(spec, candidate):
    """Post-freeze all-integer proof admission, not a finite-test promotion."""
    validate_spec(spec)
    result={'admitted':False,'actual_prime_statement':False,'RH_proved':False}
    if candidate['status'] != 'finite_rule_fit':
        return {**result,'disposition':candidate['status'],'reason':candidate.get('reason','no_numeric_rule')}
    b,q,beta,S,T=statistics(candidate)
    if spec['mode']=='delayed':
        d=next((i for i,v in enumerate(q) if v!=1),None)
        n=spec['delay']
        witness=None if d is None else {'parent':n,'digit':d,'child_index':b*n+d,
             'parent_value':coefficient(spec,n),'child_value':coefficient(spec,b*n+d),'predicted_child':str(q[d]*coefficient(spec,n))}
        return {**result,'disposition':'refuted_global_uniform_defect','reason':'delayed_positive_tail_breaks_global_recurrence',
                'recurrence_counterexample':witness,'tail_prefix':'M(N)=N+c for every N>=delay, c=M(delay)-delay',
                'asymptotic_defect':'H(bN)-bH(N)=(b^3-b)N^3/3+O(N^2), hence no finite uniform bound.'}
    if spec['mode']=='positive':
        L=sum(spec['weights']);P=sum(spec['weights'][:-1]);base=spec['base']
        return {**result,'disposition':'refuted_global_uniform_defect','reason':'noncancelling_positive_control',
                'positive_mass_multiplier':L,'last_block_lower_bound':
                f'H({base}^j)>={base}^(j-1)*{P}^2*{L}^(2j-2) for every j>=1',
                'proof':'The last digit block has length b^(j-1); all its prefixes include the preceding positive blocks of total mass P L^(j-1). A uniform H(cN)-cH(N)<=K for any c>=2 would telescope to H(N)=O(N), contradicting this bound since L>=2.'}
    if not global_digit_agreement(spec,b,q):
        return {**result,'disposition':'unresolved','reason':'global_digit_recurrence_not_symbolically_admitted'}
    expected_beta=[sum(q[:r]) for r in range(b)]
    if q[0]!=1 or any(abs(v)>1 for v in q) or sum(q)!=0 or beta!=expected_beta or Q(candidate['prefix_alpha'])!=0:
        return {**result,'disposition':'rejected_certificate','reason':'zero_sum_bounded_digit_or_prefix_premise'}
    if candidate.get('moment_rule') is None:
        return {**result,'disposition':'missing','reason':'no_frozen_moment_rule'}
    A=T*(S-b);ds=[T*sum(v*v for v in q[:r])-b*sum(v*v for v in beta[:r]) for r in range(b)]
    if Q(candidate['moment_rule']['bulk'])!=A or list(map(Q,candidate['moment_rule']['residues']))!=ds:
        return {**result,'disposition':'rejected_certificate','reason':'learned_moment_coefficients_fail_symbolic_identity'}
    K=max([Q(0)]+ds);C=max(v*v for v in beta)
    return {**result,'admitted':True,'disposition':'proved_global_generic_signed_bound','base':b,
            'digit_weights':list(map(str,q)),'S':str(S),'T':str(T),'bulk':str(A),
            'boundary_coefficients':list(map(str,ds)),'uniform_signed_defect_bound':str(K),'prefix_energy_constant':str(C),
            'quantifiers':'For EVERY integer N>=1, H(bN)-bH(N)<=K and H(N)<=C*N. Also every half-open block prefix-square energy is <=C times its length.',
            'global_premises':'a(0)=1; a(bn+r)=q_r a(n) at EVERY n>=0,r=0,...,b-1; q_0=1; |q_r|<=1; sum q_r=0.',
            'exact_identity':'With m=floor(N/b),r=N mod b: defect=T(S-b)G(m)+a(m)^2*(T*S_r-b*T_r).',
            'proof':'Complete blocks give M(bn+r)=a(n) beta_r. Hence H(N)=T G(m)+a(m)^2 T_r, G(N)=S G(m)+a(m)^2 S_r, and H(bN)=T G(N). Subtraction gives the identity. S<=b,G>=0 and a(m)^2<=1 prove defect<=K. The same prefix identity gives |M(n)|^2<=C and H(N)<=C*N. Global recurrence is admitted by grouping the specified generator digits, not by observing finite fits.',
            'unsigned_control':{'L':sum(abs(v) for v in spec['weights']),
               'lower_bound':'For unsigned coefficient prefixes, H_abs(b0^j)>=b0^(j-1)*P^2*L^(2j-2), P=sum_{d<b0-1}|w_d|>=1, L=sum|w_d|>=2.',
               'conclusion':'H_abs(N)/N is unbounded. A fully unsigned expansion cannot certify the learned linear-energy or constant signed-defect bound.'}}


def check_shared_certificate(rules):
    def terms(rule):
        out={}
        if rule['selected'] is None:return {}
        for name,value in rule['selected']['terms']:out[name]=out.get(name,Q(0))+Q(value)
        return {name:value for name,value in out.items() if value}
    return (terms(rules['bulk'])=={'T*S':Q(1),'T*b':Q(-1)} and
            terms(rules['boundary'])=={'T*S_r':Q(1),'b*T_r':Q(-1)})


def verify_numeric(candidate,data,dimensions):
    if candidate['status']!='finite_rule_fit' or candidate.get('moment_rule') is None:
        return {'missing':True,'reason':'no_frozen_rule','rows':[]}
    b=candidate['base'];q=list(map(Q,candidate['digit_weights']));alpha=Q(candidate['prefix_alpha']);beta=list(map(Q,candidate['prefix_beta']))
    A=Q(candidate['moment_rule']['bulk']);ds=list(map(Q,candidate['moment_rule']['residues']));K=max([Q(0)]+ds)
    rows=[]
    for N in dimensions:
        m,r=divmod(N,b);actual=data['H'][b*N]-b*data['H'][N]
        predicted=A*data['G'][m]+data['a'][m]**2*ds[r]
        recurrence=all(data['a'][b*N+d]==q[d]*data['a'][N] and
                       data['M'][b*N+d]==alpha*data['M'][N]+beta[d]*data['a'][N] for d in range(b))
        rows.append({'N':N,'actual_signed_defect':actual,'predicted_signed_defect':str(predicted),
                     'moment_rule_pass':actual==predicted,'global_recurrence_sample_pass':recurrence,
                     'constant_bound':str(K),'finite_bound_pass':actual<=K})
    return {'missing':False,'rows':rows}


def training_specs():
    # Coverage only fixes a diverse generator design. It does not give parameters
    # to the numeric learner; all learner inputs are arrays, not these records.
    needed=sum(len([w for w in product((-1,0,1),repeat=b-1) if sum(w)==-1]) for b in (2,3,4))
    seen=set();out=[]
    for seed in range(10001,12001):
        s=generator(seed);key=(s['base'],tuple(s['weights']))
        if key in seen:continue
        seen.add(key)
        for mode in ('signed','positive','delayed'):
            out.append({'seed':seed,'generator':generator(seed,mode)})
        if len(seen)==needed:break
    if len(seen)!=needed:raise RuntimeError('generator coverage unavailable')
    return out


def _run(directory):
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=False)
    code=('signed_bound_calibration.py','test_signed_bound_calibration.py')
    specs=training_specs();protocol={'schema':1,'code_sha256':{n:sha(BASE/n) for n in code},
        'training_generators':specs,'training_parents':64,'response_horizon':512,
        'candidate_bases':list(CANDIDATE_BASES),'holdout_generator_bases':[5,6],
        'holdout_novelty_design':'Exclude coefficients matching any training function through index 511; this is a novelty gate, not outcome filtering. Retain rejected seed designs.',
        'bulk_feature_dictionary':list(A_FEATURES),'boundary_feature_dictionary':list(D_FEATURES),
        'sparse_rule_support_budget':2,'tie_break':'minimum support then feature-index tuple then exact coefficient text',
        'discovery_input':'anonymous integer response arrays only; no generator seed/base/weight/mode metadata',
        'supplied_bias':'digit/prefix block-recursion basis, residue moment atoms, and post-freeze induction/positivity proof method',
        'expected_digit_prefix_or_moment_coefficients_supplied':False,'actual_prime_data_used':False,
        'holdout_seed_and_dimension_generation':'derive fresh values only AFTER global/model and per-instance seals',
        'RH_proved':False}
    write(directory/'protocol.json',protocol)
    (directory/'frozen_source').mkdir()
    for name in code:(directory/'frozen_source'/name).write_bytes((BASE/name).read_bytes())
    numeric=[];all_models=[]
    training_arrays=[]
    for index,spec in enumerate(specs):
        data=response(spec['generator'],512);models=local_candidates(data)
        training_arrays.append(data['a'])
        numeric.append({'anonymous_id':index,'response_sha256':digest(data),'candidates':models})
        all_models.extend(models)
    rules=infer_shared_rules(all_models)
    write(directory/'training_candidates.json',{'records':numeric,'every_candidate_retained':True})
    model={'shared_rules':rules,'expected_coefficients_supplied':False,'global_signed_proof_from_finite_tests':False}
    write(directory/'model.json',model)
    seal={'protocol_sha256':sha(directory/'protocol.json'),'model_sha256':sha(directory/'model.json'),
          'training_sha256':sha(directory/'training_candidates.json'),'selection_closed':True}
    write(directory/'seal.json',seal)
    if not check_shared_certificate(rules):raise ValueError('inferred shared rule fails symbolic admission')
    analytical=[]
    for index,spec in enumerate(specs):
        for c in numeric[index]['candidates']:
            analytical.append({'anonymous_id':index,'base':c['base'],'certificate':certificate(spec['generator'],c)})
    # Seeds were absent from the global protocol/model. Derive after seal creation.
    seed_root=int(sha(directory/'seal.json')[:16],16)
    used={s['seed'] for s in specs};fresh=[];holdout_specs=[];novelty_retries=[]
    for j in range(4):
        seed=seed_root+101+7919*j
        base=5+j%2
        while True:
            designs=[generator(seed,mode,bases=(base,)) for mode in ('signed','positive','delayed')]
            overlap=[mode for mode,spec in zip(('signed','positive','delayed'),designs)
                     if response(spec,512)['a'] in training_arrays]
            if seed not in used and not overlap:break
            novelty_retries.append({'seed':seed,'base':base,'overlapping_modes':overlap,'rejected_only_for_novelty':True})
            seed+=1
        for mode in ('signed','positive','delayed'):
            holdout_specs.append({'seed':seed,'generator':generator(seed,mode,bases=(base,))})
    for index,spec in enumerate(holdout_specs):
        probe=response(spec['generator'],512)
        candidates=[instantiate(c,rules) for c in local_candidates(probe,fit_moment=False)]
        fresh.append({'anonymous_id':index,'probe_sha256':digest(probe),'candidates':candidates})
    write(directory/'instance_candidates.json',{'instances':fresh,'new_moment_coefficients_fitted':False,
                                               'frozen_shared_rules_used':True})
    instance_seal={'parent_seal_sha256':sha(directory/'seal.json'),
                   'instance_candidates_sha256':sha(directory/'instance_candidates.json')}
    write(directory/'instance_seal.json',instance_seal)
    dimension_seed=int(sha(directory/'instance_seal.json')[:16],16);rng=random.Random(dimension_seed)
    dimensions=sorted({4096+rng.randrange(1,2048) for _ in range(4)})
    cases={'global_seal_sha256':sha(directory/'seal.json'),'instance_seal_sha256':sha(directory/'instance_seal.json'),
           'withheld_generators':holdout_specs,'withheld_dimensions':dimensions,
           'retained_novelty_seed_retries':novelty_retries,
           'generator_seeds_generated_after_global_freeze':True,'dimensions_generated_after_instance_freeze':True}
    write(directory/'holdout_cases.json',cases)
    final=[];horizon=max(CANDIDATE_BASES)*max(dimensions)+max(CANDIDATE_BASES)
    for index,spec in enumerate(holdout_specs):
        data=response(spec['generator'],horizon)
        if data!=independent_response(spec['generator'],horizon):raise AssertionError('independent recurrence replay differs')
        for c in fresh[index]['candidates']:
            native=certificate(spec['generator'],c)
            tested=verify_numeric(c,data,dimensions)
            if native['admitted'] and (tested['missing'] or not all(r['moment_rule_pass'] and r['global_recurrence_sample_pass'] and r['finite_bound_pass'] for r in tested['rows'])):
                raise AssertionError('admitted global certificate disagrees with held-out arithmetic')
            final.append({'anonymous_id':index,'base':c['base'],'numeric':tested,'certificate':native})
    write(directory/'final_evaluation.json',{'records':final,'actual_prime_statement':False,'RH_proved':False})
    write(directory/'analytical_certificates.json',{'training':analytical,'shared_rule_admitted_symbolically':True,
        'universal_proof_method':'complete block cancellation, residue moment identity, nonnegative bulk with S<=b',
        'signed_upper_bound_proved_for_generic_generators_only':True,'actual_zeta_bound_proved':False,'RH_proved':False})
    admitted=[r for r in final if r['certificate']['admitted']]
    delayed=[r for r in final if holdout_specs[r['anonymous_id']]['generator']['mode']=='delayed' and not r['numeric']['missing']]
    positive=[r for r in final if holdout_specs[r['anonymous_id']]['generator']['mode']=='positive']
    if not admitted or not delayed or not all(not r['certificate']['admitted'] for r in delayed+positive):
        raise AssertionError('calibration did not separate signed bounds from controls')
    if not all(any(not t['global_recurrence_sample_pass'] for t in r['numeric']['rows']) for r in delayed):
        raise AssertionError('delayed fake escaped withheld recurrence samples')
    checks={'frozen_shared_rule_has_independent_symbolic_identity':True,
        'new_generator_seeds_disjoint_and_generated_after_freeze':True,
        'new_dimensions_generated_after_instance_freeze':True,'independent_numeric_recurrence_replay':True,
        'all_admitted_signed_bounds_match_holdout':True,'delayed_finite_passing_fakes_globally_rejected':True,
        'positive_non_cancelling_controls_globally_rejected':True,'unsigned_lower_bound_strictly_exceeds_linear_energy':True}
    for name,h in protocol['code_sha256'].items():
        if sha(BASE/name)!=h or sha(directory/'frozen_source'/name)!=h:raise AssertionError('frozen code changed')
    if seal['protocol_sha256']!=sha(directory/'protocol.json') or seal['model_sha256']!=sha(directory/'model.json') or seal['training_sha256']!=sha(directory/'training_candidates.json'):
        raise AssertionError('global freeze changed')
    if instance_seal['instance_candidates_sha256']!=sha(directory/'instance_candidates.json'):
        raise AssertionError('per-instance freeze changed')
    novelty=[]
    for i,spec in enumerate(holdout_specs):
        new=response(spec['generator'],512)['a']
        for j,old in enumerate(training_arrays):
            n=next((n for n,(x,y) in enumerate(zip(new,old)) if x!=y),None)
            if n is None:raise AssertionError('holdout generator repeats a training function')
            novelty.append({'holdout_instance':i,'training_instance':j,'index':n,'new_value':new[n],'old_value':old[n]})
    checks['holdout_generator_functions_proved_distinct_by_coefficient_witnesses']=True
    checks['frozen_sources_and_both_seals_match_at_completion']=True
    output_files=['protocol.json','training_candidates.json','model.json','seal.json','instance_candidates.json',
                  'instance_seal.json','holdout_cases.json','final_evaluation.json','analytical_certificates.json']
    verification={'checks':checks,'all_passed':all(checks.values()),'input_sha256':{n:sha(directory/n) for n in output_files},
        'generic_global_signed_bound_certificates':len(admitted),'signed_instances_with_admitted_bound':len({r['anonymous_id'] for r in admitted}),
        'training_instances':len(specs),'withheld_instances':len(holdout_specs),'withheld_dimensions':dimensions,
        'delayed_control_candidates_with_finite_probe_fit':len(delayed),'positive_control_candidates':len(positive),
        'every_candidate_missing_or_rejected_or_admitted_record_retained':True,'formal_proof_assistant_used':False,
        'independent_external_review_required':True,'RH_proved':False,'actual_global_prime_signed_bound_proved':False}
    known={(s['generator']['base'],tuple(s['generator']['weights']),s['generator']['mode']) for s in specs}
    unseen={(s['generator']['base'],tuple(s['generator']['weights']),s['generator']['mode']) for s in holdout_specs}-known
    verification['unseen_generator_equivalence_classes']=len(unseen)
    verification['fresh_seed_is_not_necessarily_a_new_generator']=True
    verification['training_exhausts_only_base_2_3_4_generators']=True
    verification['unseen_generator_transfer_measured']=True
    verification['holdout_generator_novelty_witnesses']=novelty
    write(directory/'verification.json',verification)
    lines=['Blind generic signed-bound calibration',
      f"Training instances: {len(specs)}; withheld new-seed instances: {len(holdout_specs)}; dimensions: {dimensions}.",
      f"Learned bulk rule: {rules['bulk']['selected']['terms']}; learned boundary rule: {rules['boundary']['selected']['terms']}.",
      f"All-integer generic signed-bound certificates: {len(admitted)} across {verification['signed_instances_with_admitted_bound']} withheld signed instances.",
      'Bound: H(bN)-b H(N)<=K for EVERY integer N>=1; prefix-square energy H(N)<=C*N.',
      'Exact complete block cancellation and the learned moment identity are admitted symbolically after freeze; tests alone do not prove the bound.',
      'Supplied bias: digit-recursive generators, block/residue moment feature grammar, and induction/positivity certificate method.',
      'Unsigned prefix energy has H_abs(N)/N unbounded. Positive and delayed noncancelling controls are globally refuted; delayed controls passed their finite numeric probes.',
      'All rejected, missing and admitted candidate records are retained. Fresh seeds are generated after global freeze; per-instance numeric parameter probes are declared, and dimensions are generated after instance freeze. No new signed-moment fitting occurs on holdout.',
      'Training uses bases 2/3/4; holdout uses genuinely new bases 5/6. Exact coefficient-difference witnesses prove every held-out function differs from every training function. Per-instance numeric digit/prefix probes are allowed, but signed-moment coefficients come only from the frozen shared learned rule.',
      'This measures a tractable generic signed-cancellation workflow. It estimates no probability of solving RH and proves no actual-prime bound.',
      'Exact internal checks passed; separate external mathematical/code review is required. RH proved: false.','']
    (directory/'report.txt').write_text('\n'.join(lines))
    return verification


def run(directory):
    directory=Path(directory).resolve()
    try:
        return _run(directory)
    except Exception as exc:
        # Existing successful runs are never overwritten or decorated as failures.
        if directory.is_dir() and not (directory/'verification.json').exists() and not (directory/'failure.json').exists():
            write(directory/'failure.json',{'error':str(exc),'completed_files_sha256':
                 {str(p.relative_to(directory)):sha(p) for p in directory.rglob('*') if p.is_file()},
                 'exposed_responses_not_fresh_for_a_revised_run':True})
        raise


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=BASE/'workflow-audit-results/audit-001/signed-bound-calibration')
    args=parser.parse_args();print(json.dumps(run(args.output),indent=2))
