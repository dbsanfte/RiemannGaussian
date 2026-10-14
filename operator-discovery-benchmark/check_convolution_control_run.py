"""Independent factorized arithmetic checker for convolution-control runs.

Numerical fits, LP proposals and complete algebraic Gram identities establish
no actual cofinal signed bound. No producer mathematical module is imported.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from math import isqrt
import os
from pathlib import Path
import sys

BASE=Path(__file__).resolve().parent


def require_runtime():
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
        raise RuntimeError('verified convolution-control runs require assertions enabled')


def require(value,message):
    if not value:raise ValueError(message)


def integer(n,minimum=0):
    require(type(n) is int and n>=minimum,'integer outside exact domain')
    return n


def rational(n):
    require(isinstance(n,(int,str,Fraction)) and not isinstance(n,bool),'exact rational required')
    return Fraction(n)


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):return json.loads(Path(path).read_text())


def factor_sequences(N):
    """Least-prime factorization, independent of complete divisor inversion."""
    integer(N,1);least=list(range(N+1))
    for p in range(2,isqrt(N)+1):
        if least[p]!=p:continue
        for n in range(p*p,N+1,p):
            if least[n]==n:least[n]=p
    mu=[0]*(N+1);lam=mu.copy();h=mu.copy();tau=mu.copy();exponent=mu.copy()
    mu[1]=lam[1]=h[1]=tau[1]=1
    for n in range(2,N+1):
        p=least[n];r=n//p;lam[n]=-lam[r]
        if r%p==0:
            exponent[n]=exponent[r]+1;mu[n]=0;h[n]=h[r]
            tau[n]=tau[r]*(exponent[n]+1)//exponent[n]
        else:
            exponent[n]=1;mu[n]=-mu[r];h[n]=2*h[r];tau[n]=2*tau[r]
    c=[lam[n]*h[n] for n in range(N+1)]
    return {'mu':mu,'lambda':lam,'c':c,'h':h,'tau':tau}


def prefix(values):
    require(values and values[0]==0,'zero sentinel required')
    out=[0];total=0
    for v in values[1:]:total+=v;out.append(total)
    return out


def convolution(a,b):
    require(len(a)==len(b) and a[0]==b[0]==0,'matching complete coefficient prefixes required')
    N=len(a)-1;out=[0]*(N+1)
    for d in range(1,N+1):
        if a[d]:
            for j in range(1,N//d+1):out[d*j]+=a[d]*b[j]
    return out


def weighted_square_prefixes(g):
    return prefix([v*v for v in g]),prefix([d*v*v for d,v in enumerate(g)])


def grouped_diagonal_prefix(C,T,H,R):
    """Full diagonal sum through T using exact floor quotient grouping.

    For each k=floor(n/d), count n in [kd,(k+1)d-1] intersect[1,T].
    This uses O(T) grouped terms; it is not the producer's increment method.
    """
    integer(T,0)
    require(min(len(C),len(H),len(R))>T,'complete grouped Gram inputs required')
    total=0
    for k in range(1,T+1):
        a=T//(k+1);b=T//k
        weight=R[a]+(T+1)*(H[b]-H[a])-k*(R[b]-R[a])
        require(weight>=0,'negative grouped positive weight')
        total+=C[k]*C[k]*weight
    return total


class IndependentProfiles:
    def __init__(self,N,max_grouped_terms=20000000):
        integer(N,1);integer(max_grouped_terms,1)
        self.N=N;self.atoms=factor_sequences(N);self.C=prefix(self.atoms['c'])
        self.M=prefix(self.atoms['mu']);self.L=prefix(self.atoms['lambda'])
        self.energy={name:prefix([v*v for v in seq]) for name,seq in [('c',self.C),('mu',self.M),('lambda',self.L)]}
        self.weights={name:weighted_square_prefixes(self.atoms[name]) for name in ('h','tau')}
        self.diag={};self.used_grouped_terms=0;self.max_grouped_terms=max_grouped_terms
        # Whole h-prefix inverse is1, whole tau-prefix filtered response=floor sqrt.
        self.full={'h':list(range(N+1)), 'tau':prefix([isqrt(n)**2 for n in range(N+1)])}

    def diagonal_prefix(self,kind,T):
        require(kind in self.weights,'unknown Gram weight family')
        key=(kind,T)
        if key not in self.diag:
            if self.used_grouped_terms+T>self.max_grouped_terms:
                raise RuntimeError('complete independent grouped Gram work budget exceeded')
            H,R=self.weights[kind];self.diag[key]=grouped_diagonal_prefix(self.C,T,H,R)
            self.used_grouped_terms+=T
        return self.diag[key]

    def block_profile(self,X):
        integer(X,1);require(2*X-1<=self.N,'full block arithmetic required')
        energies={kind:{'parent':values[2*X-1]-values[X-1]} for kind,values in self.energy.items()}
        grams={}
        for kind in self.weights:
            diag=self.diagonal_prefix(kind,2*X-1)-self.diagonal_prefix(kind,X-1)
            full=self.full[kind][2*X-1]-self.full[kind][X-1]
            grams[kind]={'parent':{'full':full,'diagonal':diag,'cross':full-diag,'other_diagonal':diag-energies['c']['parent']}}
        return {'energy':energies,'grams':grams}

    def profile(self,X):
        integer(X,1);require(4*X-1<=self.N,'full child arithmetic required')
        def block(kind,Y):return self.energy[kind][2*Y-1]-self.energy[kind][Y-1]
        result={'X':X,'coefficient_horizon_required':4*X-1,'energy':{},'grams':{}}
        for kind in self.energy:
            a=block(kind,X);b=block(kind,2*X)
            result['energy'][kind]={'parent':a,'child':b,'defect':b-4*a}
        for kind in self.weights:
            def gram(Y):
                diag=self.diagonal_prefix(kind,2*Y-1)-self.diagonal_prefix(kind,Y-1)
                full=self.full[kind][2*Y-1]-self.full[kind][Y-1]
                return {'full':full,'diagonal':diag,'cross':full-diag,'other_diagonal':diag-block('c',Y)}
            a=gram(X);b=gram(2*X)
            result['grams'][kind]={'parent':a,'child':b,'defect':{k:b[k]-4*a[k] for k in a}}
        return result


def ceil_power(n,power):
    integer(n,1);power=rational(power);require(power>=0,'nonnegative power required')
    if n==1 or not power:return 1
    target=n**power.numerator;den=power.denominator;lo=0;hi=1
    while hi**den<target:hi*=2
    while hi-lo>1:
        mid=(hi+lo)//2
        if mid**den<target:lo=mid
        else:hi=mid
    return hi


def floor_root(n,k):
    integer(n,1);integer(k,1)
    if k>=n.bit_length():return 1
    lo=1;hi=n
    while lo<hi:
        mid=(lo+hi+1)//2
        if mid**k<=n:lo=mid
        else:hi=mid-1
    return lo


def feature_dictionary():
    features=[]
    for base in ('R_h','R_diff'):
        for eta in ('0','1/6','1/3'):features.append({'kind':'gram','base':base,'eta':eta})
    for kind,values in (('fixed',(2,3,5,6)),('root',(2,3,6))):
        for d in values:
            for weight in ('-2','-1','-1/2','1/2','1','2'):features.append({'kind':kind,'divisor':d,'weight':weight})
    for a,b in (('-1','-1'),('-1','1'),('1','-1'),('1','1'),('2/5','3/5'),('-2/5','-3/5')):
        features.append({'kind':'three','weights':[a,b],'divisors':[2,3]})
    for feature in features:feature['feature_id']=digest(feature)
    return features


def independent_feature_table(profiles,scales,work_budget=10000000):
    features=feature_dictionary();cost=len(profiles.C);rows=[]
    for X in sorted(set(scales)):
        profile=profiles.block_profile(X);A=profile['energy']['c']['parent'];values={};metadata={}
        for feature in features:
            kind=feature['kind'];fid=feature['feature_id'];value=None;reason=None
            if kind=='gram':
                md={'normalizer_eta':feature['eta'],'complete_divisor_diagonal':True}
                if cost+4>work_budget:reason='work_budget_exceeded'
                else:
                    numerator=(profile['grams']['h']['parent']['diagonal']-A if feature['base']=='R_h' else
                               profile['grams']['tau']['parent']['diagonal']-profile['grams']['h']['parent']['diagonal'])
                    require(numerator>=0,'nonnegative actual Gram premise failed')
                    value=Fraction(numerator,X*X*ceil_power(X,feature['eta']));cost+=4
            else:
                d=max(2,floor_root(X,feature['divisor'])) if kind=='root' else feature.get('divisor')
                md={'divisors':[2,3]} if kind=='three' else {'divisor_at_scale':d}
                if cost+8*X>work_budget:reason='work_budget_exceeded'
                else:
                    total=Fraction(0)
                    for n in range(X,2*X):
                        z=Fraction(profiles.C[n])
                        if kind=='three':z+=rational(feature['weights'][0])*profiles.C[n//2]+rational(feature['weights'][1])*profiles.C[n//3]
                        else:z+=rational(feature['weight'])*profiles.C[n//d]
                        total+=z*z
                    value=total/(X*X);cost+=8*X
            values[fid]=str(value) if value is not None else None
            metadata[fid]={**md,'missing':value is None,'reason':reason}
        rows.append({'X':X,'E':str(Fraction(A,X*X)),'features':values,'feature_metadata':metadata,'missing':False})
    return {'status':'available','value':{'rows':rows,'dictionary_sha256':digest(features),'full_child_cutoff_recomputed':True,'global_bound_proved':False},
            'reason':None,'cost':cost,'cost_scope':'scalar/list work proxy; not bit complexity'}


def innovation(terms,table,X):
    rows={r['X']:r for r in table['value']['rows']}
    if X not in rows or 2*X not in rows:return None,'child_scale_missing'
    a,b=rows[X],rows[2*X];z=rational(b['E'])-rational(a['E'])
    for term in terms:
        weight=rational(term['weight']);require(weight>=0,'negative potential coefficient')
        if not weight:continue
        fid=term['feature_id'];require(fid in a['features'],'undeclared potential feature')
        if a['features'][fid] is None or b['features'][fid] is None:return None,'feature_or_child_missing'
        z+=weight*(rational(b['features'][fid])-rational(a['features'][fid]))
    return z,None


def exact_refit(terms,table,scales,levels):
    constants={};observations=[]
    for q in levels:
        maximum=Fraction(0);complete=True
        for X in scales:
            z,reason=innovation(terms,table,X);root=ceil_power(X,Fraction(1,q))
            if z is None:
                complete=False;observations.append({'X':X,'level':q,'missing':True,'reason':reason});continue
            maximum=max(maximum,z/root)
            observations.append({'X':X,'level':q,'signed_innovation':str(z),'root':root,'missing':False})
        constants[str(q)]=str(maximum) if complete else None
    return constants,observations


def exact_score(program,table,scales,levels):
    observations=[]
    for X in scales:
        for q in levels:
            z,reason=innovation(program['terms'],table,X);constant=program['constants'].get(str(q));root=ceil_power(X,Fraction(1,q))
            missing=z is None or constant is None;bound=None if missing else rational(constant)*root
            observations.append({'X':X,'level':q,'signed_innovation':None if z is None else str(z),'bound':None if bound is None else str(bound),
                'margin':None if bound is None else str(bound-z),'missing':missing,
                'reason':(reason or ('unknown_level_constant' if constant is None else None)) if missing else None,
                'finite_pass':None if missing else z<=bound,'global_bound_proved':False})
    return {'observations':observations,'finite_passes':sum(r['finite_pass'] is True for r in observations),
            'finite_failures':sum(r['finite_pass'] is False for r in observations),'missing_cases':sum(r['missing'] for r in observations),
            'finite_cases':len(observations),'global_bound_proved':False}


def producer_profile_row(profile,X,kind):
    energy=profile['energy']['c'];gram=profile['grams'][kind];a=gram['parent'];b=gram['child'];delta=gram['defect']
    return {'X':X,'gram_energy_X':a['full'],'gram_energy_2X':b['full'],'A_X':energy['parent'],'A_2X':energy['child'],'Delta':energy['defect'],
            'S_X':a['diagonal'],'S_2X':b['diagonal'],'Delta_S':delta['diagonal'],
            'other_diagonal_X':a['other_diagonal'],'other_diagonal_2X':b['other_diagonal'],'cross_X':a['cross'],'cross_2X':b['cross'],'Delta_cross':delta['cross']}


def verify_actual_profile(record,profiles,scales):
    require(record['status']=='available' and record['reason'] is None,'actual complete profile unavailable')
    value=record['value'];N=4*max(scales)-1
    require(record['lookahead']==N and value['source_lookahead']==N,'actual coefficient horizon mismatch')
    expected=[producer_profile_row(profiles.profile(X),X,'h') for X in scales]
    require(value['rows']==expected,'actual full h Gram profile mismatch')
    require(list(map(rational,value['coefficients']))==profiles.atoms['c'][:N+1],'actual c coefficient mismatch')
    require(list(map(rational,value['control']))==profiles.atoms['h'][:N+1] and list(map(rational,value['prefix']))==profiles.C[:N+1],'actual h/C mismatch')
    require(value['sequence']=='convolution' and value['control_kind']=='actual_h' and value['shift']==0 and value['dilate']==1,'actual target changed')
    require(value['inverse_identity_verified'] is True and value['full_divisor_diagonal'] is True and value['global_bound_proved'] is False,'actual inverse scope mismatch')
    require(value['coefficient_bit_complexity_certified'] is False,'finite arithmetic cost overclaim')
    for name,kind in [('actual_h_profile','h'),('tau_profile','tau')]:
        sub=value[name];require(sub['rows']==[producer_profile_row(profiles.profile(X),X,kind) for X in scales],'nested '+kind+' full Gram mismatch')
        require(list(map(rational,sub['control']))==profiles.atoms[kind][:N+1] and list(map(rational,sub['coefficients']))==profiles.atoms['c'][:N+1] and list(map(rational,sub['prefix']))==profiles.C[:N+1],'nested Gram coefficients mismatch')
        require(sub['full_divisor_diagonal'] is True and sub['global_bound_proved'] is False,'nested Gram scope overclaim')
    expected_diff=[{'X':X,'at_X':profiles.profile(X)['grams']['tau']['parent']['diagonal']-profiles.profile(X)['grams']['h']['parent']['diagonal'],
                    'at_2X':profiles.profile(X)['grams']['tau']['child']['diagonal']-profiles.profile(X)['grams']['h']['child']['diagonal']} for X in scales]
    require(value['tau_minus_h_diagonal']==expected_diff,'tau-minus-h positivity profile mismatch')
    return True

def verify_candidate_archive(archive,table,training_scales,levels,use_lp=True):
    features=feature_dictionary();require(archive['schema']==1 and archive['dictionary_sha256']==digest(features),'candidate dictionary binding mismatch')
    require(archive['selection_used_scales']==list(training_scales) and archive['levels']==list(levels) and archive['global_bound_proved'] is False,'candidate scope mismatch')
    expected_origins=[{'kind':'baseline'}]+[{'kind':'singleton','feature_id':f['feature_id'],'weight':w} for f in features for w in ('1/4','1','4')]
    if use_lp:expected_origins +=[{'kind':'lp','group':g,'penalty':p} for g in ('gram','fixed','root','three','all') for p in ('0','1/1024','1/64')]
    proposals=archive['proposal_archive'];require([r['origin'] for r in proposals]==expected_origins,'proposal archive missing/reordered attempts')
    candidates={};failed=0
    for proposal in proposals:
        origin=proposal['origin'];kind=origin['kind']
        if 'exact_program' not in proposal:
            require(kind=='lp' and proposal.get('status') in ('missing','failed') and proposal.get('discarded') is True,'unretained proposal failure')
            require(bool(proposal.get('reason')) or bool(proposal.get('solver',{}).get('message')),'missing proposal failure reason')
            failed+=1;continue
        program=proposal['exact_program'];require(set(program)=={'terms','constants'},'unrecognized exact potential program')
        terms=program['terms'];require([t['feature_id'] for t in terms]==sorted({t['feature_id'] for t in terms}),'noncanonical/duplicate potential support')
        declared={f['feature_id'] for f in features}
        require(all(set(t)=={'feature_id','weight'} and t['feature_id'] in declared and rational(t['weight'])>0 for t in terms),'invalid potential coefficient or feature')
        if kind=='baseline':require(terms==[] and proposal['solver'] is None,'baseline modified')
        elif kind=='singleton':require(terms==[{'feature_id':origin['feature_id'],'weight':origin['weight']}] and proposal['solver'] is None,'singleton omitted/changed')
        else:
            solver=proposal['solver'];require(solver['success'] is True and solver['role']=='numerical proposal only; exact full refit authoritative','LP promoted beyond proposal')
            fs=[f for f in features if origin['group']=='all' or f['kind']==origin['group']]
            floats=solver['float_solution'];require(len(floats)==len(fs)+len(levels),'LP solution dimension mismatch')
            weights=[Fraction(float(x)).limit_denominator(64) for x in floats[:len(fs)]]
            require(solver['rationalized_weights']==list(map(str,weights)) and all(0<=w<=8 for w in weights),'LP exact weight conversion mismatch')
            expected_terms=sorted([{'feature_id':f['feature_id'],'weight':str(w)} for f,w in zip(fs,weights) if w],key=lambda t:t['feature_id'])
            require(terms==expected_terms,'LP program differs from declared rationalization')
        constants,fit_observations=exact_refit(terms,table,training_scales,levels)
        require(program['constants']==constants and proposal['fit_observations']==fit_observations,'proposal exact refit mismatch')
        pid=digest(program);require(proposal['program_id']==pid,'potential exact program hash mismatch')
        if pid in candidates:
            require(proposal['discarded'] is True and proposal['alias_of']==pid,'alias failure retention mismatch')
            candidates[pid]['origins'].append(origin)
        else:
            require(proposal['discarded'] is False and proposal['alias_of'] is None,'new candidate incorrectly discarded')
            candidates[pid]={'program_id':pid,'program':program,'origins':[origin],'training_score':exact_score(program,table,training_scales,levels)}
    require(archive['candidates']==list(candidates.values()),'candidate archive/exact score mismatch')
    return {'candidate_count':len(candidates),'proposal_count':len(proposals),'proposal_failures':failed,
            'LP_optimality_independently_verified':False}

CLAIM='There exists an integer q0>=1 such that for every integer q>=q0 there exists finite Cq>=0 independent of X such that for every dyadic integer X>=1, E(2X)+V(2X)-E(X)-V(X)<=Cq ceil(X^(1/q)), where E(X)=A_C(X)/X^2, C is the complete prefix of actual mu*lambda, and V is the exact nonnegative potential specified by the frozen terms, with every cutoff recomputed at its own scale.'
CODE_NAMES={'convolution_control_arithmetic.py','test_convolution_control_arithmetic.py','convolution_control_search.py','test_convolution_control_search.py','run_convolution_control.py','test_run_convolution_control.py','check_convolution_control_run.py','test_convolution_control_run.py','convolution_control_checks.py','test_convolution_control_checks.py','convolution_control_proof.txt','convolution_control_analytic.py','test_convolution_control_analytic.py','detector_safe_evaluation.py','inverse_prefix_grammar.py','detector_workflow_guard.py'}
SEALED_NAMES={'protocol.json','contract_tests.txt','source_seal.json','worker_replay.json','training.json','validation_data.json','candidate_batch.json','validation.json','proof_queue.json'}
INPUT_NAMES=sorted(SEALED_NAMES|{'seal.json','final_cases.json','final_evaluation.json'})


def checked_path(base,name):
    require(isinstance(name,str) and name and not Path(name).is_absolute(),'relative file binding required')
    result=(Path(base)/name).resolve();require(result.is_relative_to(Path(base).resolve()),'file binding escapes root')
    return result


def verify_hashes(base,mapping):
    require(isinstance(mapping,dict) and mapping,'nonempty file hashes required')
    for name,value in mapping.items():require(sha(checked_path(base,name))==value,'file hash mismatch: '+name)


def reject_promotions(value):
    forbidden={'RH_proved','global_bound_proved','actual_all_scale_signed_bound_proved','ordinary_signed_energy_bound_proved',
               'critical_energy_estimate_proved','actual_signed_upper_bound_proved','global_signed_upper_bound_proved','global_actual_signed_innovation_bound_proved'}
    if isinstance(value,dict):
        for key,item in value.items():
            if key in forbidden:require(item is False,'numerical/algebraic record promotes '+key)
            reject_promotions(item)
    elif isinstance(value,list):
        for item in value:reject_promotions(item)


def exact_selection(factory,results):
    features={f['feature_id']:f for f in feature_dictionary()};scores={r['program_id']:r['score'] for r in results};selected={};decisions=[]
    def rank(candidate):
        program=candidate['program'];values=list(program['constants'].values());score=scores[candidate['program_id']]
        return (score['missing_cases']+sum(v is None for v in values),score['finite_failures'],
                max([rational(v) for v in values if v is not None] or [Fraction(0)]),
                sum(rational(t['weight']) for t in program['terms']),len(program['terms']),candidate['program_id'])
    for group in ('baseline','gram','fixed','root','three','all'):
        eligible=[]
        for candidate in factory['candidates']:
            matches=any((group=='baseline' and o['kind']=='baseline') or
                        (o['kind']=='lp' and o['group']==group) or
                        (o['kind']=='singleton' and group!='baseline' and features[o['feature_id']]['kind']==group)
                        for o in candidate['origins'])
            if matches:eligible.append(candidate)
        if not eligible:
            decisions.append({'group':group,'eligible_ids':[],'selected_id':None,'rank':None});continue
        chosen=min(eligible,key=rank);pid=chosen['program_id'];r=rank(chosen)
        decisions.append({'group':group,'eligible_ids':sorted(c['program_id'] for c in eligible),'selected_id':pid,
                          'rank':[str(v) if isinstance(v,Fraction) else v for v in r]})
        if pid not in selected:
            selected[pid]={'program_id':pid,'exact_program':chosen['program'],'exact_program_sha256':digest(chosen['program']),
                'global_claim':CLAIM,'precise_claim_sha256':digest(CLAIM),'selection_origins':[],
                'validation_score':scores[pid],'global_bound_proved':False}
        selected[pid]['selection_origins'].append(group)
    return sorted(selected.values(),key=lambda row:row['program_id']),decisions


def audit_dataset(record,spec,scales):
    require(record['protocol_sha256']==digest(spec) and record['base_scales']==list(scales),'dataset/protocol binding mismatch')
    N=4*max(scales)-1;require(N<=spec['budgets']['max_n'],'declared lookahead exceeded')
    profiles=IndependentProfiles(N)
    verify_actual_profile(record['profile'],profiles,scales)
    require(type(record['profile']['cost']) is int and 0<=record['profile']['cost']<=spec['budgets']['arithmetic_work'],'arithmetic proxy cost outside declared limit')
    expanded=sorted(set(scales)|{2*X for X in scales})
    table=independent_feature_table(profiles,expanded,work_budget=spec['budgets']['feature_work'])
    require(record['table']==table,'exact feature/child cutoff/cost table mismatch')
    return table,{'coefficient_horizon':N,'independent_grouped_terms':profiles.used_grouped_terms,'base_scale_count':len(scales),
                  'expanded_scale_count':len(expanded),'all_complete_h_and_tau_grams_verified':True}


def audit_run(directory):
    require_runtime();d=Path(directory).resolve()
    require(not (d/'failure.json').exists(),'failed run cannot be admitted')
    input_hashes={name:sha(d/name) for name in INPUT_NAMES};spec=read(d/'protocol.json');seal=read(d/'seal.json');source=read(d/'source_seal.json')
    require(spec['version']=='convolution-control-v1' and set(spec['code_sha256'])==CODE_NAMES,'unsupported/incomplete frozen code set')
    verify_hashes(BASE,spec['code_sha256']);verify_hashes(d/'frozen_source',spec['code_sha256'])
    require(spec['feature_dictionary']==feature_dictionary() and spec['feature_dictionary_sha256']==digest(feature_dictionary()),'feature dictionary changed')
    require(spec['global_claim']==CLAIM,'original global claim changed')
    require(spec['levels']==[2,3,6,12] and spec['final_levels']==[3,12,13,17],'unsupported level programs')
    require(spec['selection_groups']==['baseline','gram','fixed','root','three','all'] and spec['lp_groups']==['gram','fixed','root','three','all'] and
            spec['lp_penalties']==['0','1/1024','1/64'] and spec['singleton_weights']==['1/4','1','4'],'proposal/selection programs changed')
    require(spec['budgets']['bit']==1000000,'unsupported exact normalizer computation budget')
    for value in spec['budgets'].values():integer(value,1)
    require(spec['runtime']['python']==sys.version and spec['runtime']['scipy_role']=='proposal only; exact rationalized refits authoritative','runtime/proposal role mismatch')
    require(spec['provenance']['prime_coefficients_new_holdout'] is False and spec['provenance']['historical_coefficient_overlap'] is True,'coefficient novelty overclaim')
    provenance=spec['target_provenance'];prior=checked_path(BASE,provenance['path'])
    require(sha(prior)==provenance['sha256'],'prior sampled target hash mismatch')
    prior_queue=read(prior);target='43bc2c2518395be27e340edb652a8a3f7574d337d35f994f8f89a951165bcb78'
    require(provenance['ast_program_id']==target and any(row['program_id']==target for row in prior_queue['ast_queue']),'prior sampled target missing')
    require(source['protocol_sha256']==digest(spec) and source['code_sha256']==spec['code_sha256'] and source['source_frozen_before_actual_data'] is True and source['tests_passed'] is True,'source seal binding mismatch')
    require(source['contract_tests_sha256']==sha(d/'contract_tests.txt'),'contract log hash mismatch')
    expected_tests={'test_convolution_control_arithmetic','test_convolution_control_search','test_run_convolution_control','test_convolution_control_checks','test_convolution_control_run'}
    declared_tests=source['development_tests'];require(len(declared_tests)==len(set(declared_tests)) and expected_tests.issubset(declared_tests) and set(declared_tests)<=expected_tests|{'test_convolution_control_analytic'},'contract test scope mismatch')
    log=(d/'contract_tests.txt').read_text();require('\nOK\n' in log and 'FAILED (' not in log and 'Ran ' in log,'stored contract log unsuccessful')
    require(seal['protocol_sha256']==digest(spec) and set(seal['files'])==SEALED_NAMES and seal['selection_closed'] is True and seal['final_cases_exist'] is False,'selection seal mismatch')
    verify_hashes(d,seal['files'])
    replay=read(d/'worker_replay.json');require(replay=={'files_match':{name:True for name in ('candidate_batch.json','validation.json','proof_queue.json')},'isolated_subprocess':True,'python_guard_not_os_sandbox':True},'worker replay/dataflow scope mismatch')
    training=read(d/'training.json');validation_data=read(d/'validation_data.json');batch=read(d/'candidate_batch.json');validation=read(d/'validation.json');queue=read(d/'proof_queue.json')
    for obj in (spec,source,seal,training,validation_data,batch,validation,queue):reject_promotions(obj)
    require(batch['protocol_sha256']==digest(spec) and batch['training_data_sha256']==sha(d/'training.json'),'training archive binding mismatch')
    require(batch['access_denials']=={'proof':True,'final_cases':True,'final_evaluation':True,'historical_report':True},'discovery dataflow denial failed')
    require(validation['protocol_sha256']==digest(spec) and validation['validation_data_sha256']==sha(d/'validation_data.json'),'validation binding mismatch')
    require(queue['protocol_sha256']==digest(spec) and queue['candidate_ids_frozen_before_final'] is True and queue['final_used_for_selection'] is False,'queue used final data')
    training_table,train_checks=audit_dataset(training,spec,spec['training_scales'])
    archive_checks=verify_candidate_archive(batch['factory'],training_table,spec['training_scales'],spec['levels'])
    validation_table,validation_checks=audit_dataset(validation_data,spec,spec['validation_scales'])
    validation_results=[{'program_id':candidate['program_id'],'score':exact_score(candidate['program'],validation_table,spec['validation_scales'],spec['levels'])} for candidate in batch['factory']['candidates']]
    require(validation['results']==validation_results,'all-candidate validation score mismatch')
    selected,decisions=exact_selection(batch['factory'],validation_results)
    require(queue['queue']==selected and queue['selection_decisions']==decisions,'exact group selection mismatch')
    cases=read(d/'final_cases.json');odd=9001+2*(int(sha(d/'seal.json')[:16],16)%1500)
    require(spec['final_generation']=={'odd_min':9001,'odd_count':1500,'formula':'9001+2*(int(seal_sha256[:16],16)%1500)','fixed':[8192,16384]},'final scale-generation program changed')
    expected_cases={'protocol_sha256':digest(spec),'seal_sha256':sha(d/'seal.json'),'base_scales':sorted([odd,8192,16384]),'levels':spec['final_levels'],'generated_after_seal':True}
    require(cases==expected_cases and len(set(cases['base_scales']))==len(cases['base_scales']),'post-seal scale/level generation mismatch')
    final=read(d/'final_evaluation.json');reject_promotions(final)
    require(final['protocol_sha256']==digest(spec) and final['cases_sha256']==sha(d/'final_cases.json') and final['global_bound_proved'] is False,'final evaluation binding/overclaim')
    final_table,final_checks=audit_dataset(final['data'],spec,cases['base_scales'])
    final_results=[{'program_id':candidate['program_id'],'score':exact_score(candidate['exact_program'],final_table,cases['base_scales'],cases['levels'])} for candidate in selected]
    require(final['results']==final_results,'final full-potential exact scores mismatch')
    counts={'passes':0,'failures':0,'missing':0,'dyadic_stored_constant_failures':0,'offdomain_finite_failures':0}
    for row in final_results:
        for observation in row['score']['observations']:
            status=observation['finite_pass'];counts['missing' if status is None else 'passes' if status else 'failures']+=1
            if status is False:counts['dyadic_stored_constant_failures' if observation['X']&(observation['X']-1)==0 else 'offdomain_finite_failures']+=1
            if observation['level'] not in spec['levels']:require(status is None and observation['reason']=='unknown_level_constant','unknown q promoted to finite success')
    # Every file/source binding is rechecked after the independent math evaluation.
    verify_hashes(d,input_hashes);verify_hashes(BASE,spec['code_sha256']);verify_hashes(d/'frozen_source',spec['code_sha256']);require(sha(prior)==provenance['sha256'],'prior target changed during audit')
    return {'schema':1,'all_passed':True,'checks_passed':16,'input_sha256':input_hashes,'code_sha256':spec['code_sha256'],
        'target_provenance_sha256':provenance['sha256'],'independently_checked_profile_data':{'training':train_checks,'validation':validation_checks,'final':final_checks},
        'archive':archive_checks,'selected_count':len(selected),'final_counts':counts,
        'mathematical_audit_imports_production_code':False,'LP_optimality_independently_verified':False,
        'worker_replay_independent_second_implementation':False,'dataflow_guard_is_OS_sandbox':False,'formal_machine_checked_proof':False,
        'all_candidate_nonnegative_potential_semantics_verified':True,'complete_signed_cross_terms_retained':True,
        'actual_all_scale_signed_bound_proved':False,'global_bound_proved':False,'RH_proved':False,
        'scope':'Independent finite exact factorized coefficients, quotient-grouped full h/tau Gram profiles, all rational program fits/scores and bindings. LP is a proposal; unknown cofinal constants and the global signed innovation remain unproved.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('directory',type=Path);args=parser.parse_args()
    require_runtime()
    if (args.directory/'verification.json').exists():raise FileExistsError('successful verification cannot be overwritten')
    result=audit_run(args.directory)
    with (args.directory/'verification.json').open('x') as stream:stream.write(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
