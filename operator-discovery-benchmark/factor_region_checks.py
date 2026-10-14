"""Independent exact factor-region arithmetic and complete signed Gram audit.

No production arithmetic/search imports. Certificates here establish identities
and finite evaluations; they never establish a uniform cancellation estimate.
"""
from fractions import Fraction
from hashlib import sha256
from math import comb,gcd,isqrt
import json

REGIONS=['unit']+['prime_'+p+'/core_'+c+'/'+e for p in ('small','large') for c in ('small','large') for e in ('odd','even')]


def require(value,message):
    if not value:raise ValueError(message)


def integer(value,minimum=0):
    require(type(value) is int and value>=minimum,'exact integer domain required');return value


def rational(value):
    require(type(value) in (int,str) or isinstance(value,Fraction),'exact rational required')
    return Fraction(value)


def digest(value):return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def floor_root(n,k):
    integer(n);integer(k,1)
    if n<2 or k==1:return n
    if k>=n.bit_length():return 1
    lo=1;hi=1<<((n.bit_length()+k-1)//k)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**k<=n:lo=mid
        else:hi=mid
    return hi if hi**k<=n else lo


def floor_power(X,power,max_power_bits=1000000):
    integer(X,1);power=rational(power)
    require(power>=0,'nonnegative rational power required')
    if X==1 or not power:return 1
    if power.numerator*X.bit_length()>max_power_bits:raise RuntimeError('exact rational-power work budget exceeded')
    return floor_root(X**power.numerator,power.denominator)


def ceiling_power(X,power,max_power_bits=1000000):
    value=floor_power(X,power,max_power_bits);power=rational(power)
    if power==0 or X==1:return value
    return value if value**power.denominator==X**power.numerator else value+1


def factor_data(N):
    integer(N,1);least=list(range(N+1))
    for p in range(2,isqrt(N)+1):
        if least[p]!=p:continue
        for n in range(p*p,N+1,p):
            if least[n]==n:least[n]=p
    exponent=[0]*(N+1);core=[0]*(N+1);core[1]=1
    for n in range(2,N+1):
        p=least[n];m=n//p
        if m%p==0:exponent[n]=exponent[m]+1;core[n]=core[m]
        else:exponent[n]=1;core[n]=m
    return least,exponent,core


def local(r,l,j):
    integer(r);integer(l);integer(j);k=r+l;require(k>0,'positive total arity required')
    if l==0:return (-1)**j*comb(k,j) if j<=k else 0
    return sum((-1)**a*comb(k,a)*comb(l+(j-a)//2-1,(j-a)//2) for a in range(min(k,j)+1) if (j-a)%2==0)


def coefficients(N,target,factors=None):
    integer(target['r']);integer(target['l']);require(target['r']+target['l']>0,'positive arity required')
    least,exponent,core=factors or factor_data(N);out=[0]*(N+1);out[1]=1
    locals_=[local(target['r'],target['l'],j) for j in range(N.bit_length())]
    for n in range(2,N+1):out[n]=out[core[n]]*locals_[exponent[n]]
    return out


def filter_weights(target):
    merged={}
    for term in target['filter']:
        require(set(term)=={'divisor','weight'},'fixed rational filter schema required')
        d=integer(term['divisor'],1);merged[d]=merged.get(d,Fraction(0))+rational(term['weight'])
    terms=[(d,w) for d,w in sorted(merged.items()) if w];require(terms,'nonzero filter required')
    denominator=1
    for d,w in terms:denominator=denominator*w.denominator//gcd(denominator,w.denominator)
    return [(d,int(w*denominator)) for d,w in terms],denominator


def region_index(n,factors,prime_cut,core_cut):
    if n==1:return 0
    least,exponent,core=factors
    return 1+4*(least[n]>prime_cut)+2*(core[n]>core_cut)+(exponent[n]%2==0)


def independent_row(X,target,scheme,*,factors=None,actual=None,max_products=1000000000):
    integer(X,1);require(set(scheme)=={'prime_power','core_power'},'exact scheme schema required')
    T=2*X-1;factors=factors or factor_data(T);actual=actual or coefficients(T,target,factors)
    require(len(actual)>T and len(factors[0])>T,'complete source domain required')
    prime_cut=floor_power(X,scheme['prime_power']);core_cut=floor_power(X,scheme['core_power'])
    terms,L=filter_weights(target)
    # Source-region prefix construction is independent of producer event updates.
    prefixes=[[0]*(T+1) for _ in range(9)]
    for n in range(1,T+1):prefixes[region_index(n,factors,prime_cut,core_cut)][n]=actual[n]
    for column in prefixes:
        for n in range(1,T+1):column[n]+=column[n-1]
    vectors=[[sum(w*prefixes[i][n//d] for d,w in terms) for n in range(X,2*X)] for i in range(9)]
    gram=[[0]*9 for _ in range(9)];products=0
    for i in range(9):
        for j in range(i,9):
            if any(vectors[i]) and any(vectors[j]):
                products+=X
                if products>max_products:raise RuntimeError('complete Gram work budget exceeded')
                gram[i][j]=sum(a*b for a,b in zip(vectors[i],vectors[j]))
            gram[j][i]=gram[i][j]
    denominator=X*X*L*L;total=sum(map(sum,gram))
    sums=[0]*(T+1)
    for n in range(1,T+1):sums[n]=sums[n-1]+actual[n]
    recovered=[sum(vectors[i][j] for i in range(9)) for j in range(X)]
    expected=[sum(w*sums[n//d] for d,w in terms) for n in range(X,2*X)]
    require(recovered==expected and total==sum(v*v for v in expected),'complete region recovery identity failed')
    source_max=T//min(d for d,w in terms)
    classes=[region_index(n,factors,prime_cut,core_cut) for n in range(1,source_max+1)]
    bound=max(abs(v) for column in vectors for v in column)
    diag=sum(gram[i][i] for i in range(9));cross=total-diag
    return {'X':X,'target_id':digest(target),'scheme_id':digest(scheme),'gram_numerators':gram,'gram_denominator':denominator,'E':str(Fraction(total,denominator)),
            'cutoffs':{'z':prime_cut,'u':core_cut},'weight_common_denominator':L,'products':products,'complete_recovery_verified':True,
            'diagonal':str(Fraction(diag,denominator)),'cross':str(Fraction(cross,denominator)),
            'component_source_counts':[classes.count(i) for i in range(9)],'source_max':source_max,
            'source_coverage_sha256':digest(classes),'source_coefficients_sha256':digest(actual[:source_max+1]),
            'prefix_abs_bound':bound,'int64_gram_abs_bound':X*bound*bound}


def quadratic_feature(row,vector,eta):
    require(len(vector)==9,'nine complete region coefficients required');b=list(map(rational,vector))
    matrix=row['gram_numerators'];denominator=integer(row['gram_denominator'],1)
    value=sum((b[i]*b[j]*integer_signed(matrix[i][j]) for i in range(9) for j in range(9)),Fraction(0))/denominator
    require(value>=0,'nonnegative square feature failed')
    return value/ceiling_power(integer(row['X'],1),eta)


def integer_signed(value):
    require(type(value) is int,'exact signed Gram integer required');return value


def check_profile(profile,scales,targets,schemes):
    """Compare every requested complete row, never a projection or partial success."""
    require(profile.get('status')=='available','complete profile unavailable')
    require(scales and targets and schemes,'nonempty complete profile dimensions required')
    require(len(set(scales))==len(scales) and len({digest(t) for t in targets})==len(targets) and len({digest(s) for s in schemes})==len(schemes),'duplicate profile dimensions')
    for X in scales:integer(X,1)
    integer(profile['cost'])
    value=profile['value'];rows=value['rows'];expected_keys={(X,digest(t),digest(s)) for X in scales for t in targets for s in schemes}
    require(list(value['components'])==REGIONS and value['complete_horizon']==2*max(scales)-1,'complete domain/components mismatch')
    require(value['global_bound_proved'] is False and value['RH_proved'] is False,'finite profile overclaim')
    require(len(rows)==len(expected_keys),'missing/extra profile rows')
    actual_keys=[(r['X'],r['target_id'],r['scheme_id']) for r in rows]
    require(len(set(actual_keys))==len(actual_keys) and set(actual_keys)==expected_keys,'duplicate/missing profile row keys')
    N=2*max(scales)-1;factors=factor_data(N);sources={digest(t):coefficients(N,t,factors) for t in targets};tm={digest(t):t for t in targets};sm={digest(s):s for s in schemes}
    expected_arities=list(dict.fromkeys((t['r'],t['l']) for t in targets));provenance=value['source_provenance']
    require([(p['r'],p['l']) for p in provenance]==expected_arities,'source provenance arity coverage mismatch')
    for p in provenance:
        integer(p['r']);integer(p['l']);integer(p['source_cost'])
        t=next(t for t in targets if (t['r'],t['l'])==(p['r'],p['l']))
        require(p['source_sha256']==digest(sources[digest(t)]),'complete source provenance hash mismatch')
    products=0
    for row in rows:
        integer(row['X'],1)
        native=independent_row(row['X'],tm[row['target_id']],sm[row['scheme_id']],factors=factors,actual=sources[row['target_id']])
        matrix=row['gram_numerators'];require(len(matrix)==9 and all(len(r)==9 for r in matrix),'complete9x9 Gram required')
        require(all(type(v) is int for r in matrix for v in r),'exact integer Gram required')
        integer(row['gram_denominator'],1)
        for field in ('weight_common_denominator','source_max','prefix_abs_bound','int64_gram_abs_bound'):integer(row[field])
        for n in row['component_source_counts']:integer(n)
        integer(row['cutoffs']['z']);integer(row['cutoffs']['u'])
        for field in ('gram_numerators','gram_denominator','E','cutoffs','weight_common_denominator','diagonal','cross',
                      'component_source_counts','source_max','source_coverage_sha256','source_coefficients_sha256','prefix_abs_bound','int64_gram_abs_bound'):
            require(row[field]==native[field],'independent '+field+' mismatch')
        require(row['source_coverage_complete'] is True and row['global_bound_proved'] is False,'profile coverage/claim mismatch')
        require(row['gram_engine'] in ('python_int','numpy_int64_proved_safe'),'unrecognized Gram engine')
        if row['gram_engine']=='numpy_int64_proved_safe':require(row['int64_gram_abs_bound']<=2**63-1,'unsafe int64 Gram')
        products+=native['products']
    return {'all_passed':True,'rows_verified':len(rows),'full_81_entries_per_row':True,'independent_factorization':True,'full_region_recovery_verified':True,'integer_products':products,
            'actual_all_scale_signed_bound_proved':False,'RH_proved':False}


def feature_dictionary(schemes):
    vectors=[]
    for i in range(9):b=[0]*9;b[i]=1;vectors.append(b)
    for pairs in (((1,2),(3,4),(5,6),(7,8)),((1,5),(2,6),(3,7),(4,8)),((1,3),(2,4),(5,7),(6,8))):
        for i,j in pairs:b=[0]*9;b[i]=1;b[j]=-1;vectors.append(b)
    vectors.extend([[0]+[1]*8,[0,1,-1,1,-1,1,-1,1,-1],[0,1,1,1,1,-1,-1,-1,-1]])
    out=[];seen=set()
    for s in schemes:
        scheme={key:str(rational(s[key])) for key in ('prime_power','core_power')}
        for b in vectors:
            for eta in ('0','1/3'):
                payload={'scheme':scheme,'scheme_id':digest(scheme),'vector':b,'eta':eta};fid=digest(payload)
                if fid not in seen:seen.add(fid);out.append(dict(payload,feature_id=fid))
    return out


def normalized_target(target):
    require(set(target)=={'r','l','filter'},'complete target schema required')
    integer(target['r']);integer(target['l']);require(target['r']+target['l']>0,'positive arity required')
    terms,L=filter_weights(target)
    return {'r':target['r'],'l':target['l'],'filter':[{'divisor':d,'weight':str(Fraction(w,L))} for d,w in terms]}


def check_feature_table(profile,table,scales,targets,schemes):
    require(table['status']=='available','complete feature table unavailable')
    data=table['value'];features=feature_dictionary(schemes)
    require(data['features']==features and data['dictionary_sha256']==digest(features),'full feature dictionary mismatch')
    require(data['targets']==[{'target_id':digest(normalized_target(t)),'target':normalized_target(t)} for t in targets],'feature table target mismatch')
    require(data['full_signed_Gram_retained'] is True and data['global_bound_proved'] is False,'feature table full-Gram/claim mismatch')
    raw=profile['value']['rows'];lookup={(r['target_id'],r['X'],r['scheme_id']):r for r in raw}
    expected=[]
    for target in targets:
        tid=digest(normalized_target(target))
        for X in sorted(set(scales)):
            values={};energies=[]
            for feature in features:
                row=lookup[(tid,X,feature['scheme_id'])];energies.append(row['E'])
                values[feature['feature_id']]=str(quadratic_feature(row,feature['vector'],feature['eta']))
            require(len(set(energies))==1,'partition-dependent base energy')
            expected.append({'target_id':tid,'X':X,'E':energies[0],'features':values,'feature_missing':{}})
    require(data['rows']==expected,'complete feature values/missingness mismatch')
    return {'all_passed':True,'features_verified':len(features),'rows_verified':len(expected),'all_signed_cross_terms_retained':True,'global_bound_proved':False}


def canonical_potential_terms(terms):
    weights={};features={}
    for term in terms:
        require(set(term)=={'feature','weight'},'potential term schema')
        f=term['feature'];require(set(f)=={'scheme','scheme_id','vector','eta','feature_id'},'feature descriptor schema')
        fid=f['feature_id'];require(digest({k:v for k,v in f.items() if k!='feature_id'})==fid,'feature hash mismatch')
        require(digest(f['scheme'])==f['scheme_id'] and len(f['vector'])==9,'scheme/complete vector mismatch')
        for v in f['vector']:integer_signed(v)
        require(rational(f['eta'])>=0,'nonnegative normalization required')
        w=rational(term['weight']);require(w>=0,'nonnegative outside weight required')
        weights[fid]=weights.get(fid,Fraction(0))+w;features[fid]=f
    return [{'feature':features[fid],'weight':str(w)} for fid,w in sorted(weights.items()) if w]


def innovations(program,table,scales):
    data=table['value'] if 'status' in table else table;target=normalized_target(program['target']);tid=digest(target)
    rows={r['X']:r for r in data['rows'] if r['target_id']==tid};features={f['feature_id']:f for f in data['features']}
    terms=canonical_potential_terms(program['terms'])
    require(all(features.get(t['feature']['feature_id'])==t['feature'] for t in terms),'undeclared potential feature')
    result={}
    for X in scales:
        if X not in rows or 2*X not in rows or rows[X]['E'] is None or rows[2*X]['E'] is None:
            result[X]=(None,'base_or_child_energy_missing');continue
        z=rational(rows[2*X]['E'])-rational(rows[X]['E']);reason=None
        for t in terms:
            fid=t['feature']['feature_id'];a=rows[X]['features'].get(fid);b=rows[2*X]['features'].get(fid)
            if a is None or b is None:reason='feature_or_child_missing';break
            z+=rational(t['weight'])*(rational(b)-rational(a))
        result[X]=(None,reason) if reason else (z,None)
    return result


def exact_refit(program,table,scales,levels):
    observed=innovations(program,table,scales);constants={};evidence=[]
    for q in levels:
        integer(q,1);maximum=Fraction(0);complete=True
        for X in scales:
            z,reason=observed[X]
            if z is None:complete=False;evidence.append({'X':X,'level':q,'missing':True,'reason':reason});continue
            root=ceiling_power(X,Fraction(1,q));maximum=max(maximum,z/root)
            evidence.append({'X':X,'level':q,'signed_innovation':str(z),'root':root,'missing':False})
        constants[str(q)]=str(maximum) if complete else None
    return constants,evidence


def exact_score(program,table,scales,levels):
    observed=innovations(program,table,scales);rows=[]
    for X in scales:
        for q in levels:
            integer(q,1);z,reason=observed[X];C=program['constants'].get(str(q));missing=z is None or C is None
            if C is not None:require(rational(C)>=0,'nonnegative fitted constant required')
            bound=None if missing else rational(C)*ceiling_power(X,Fraction(1,q))
            rows.append({'X':X,'level':q,'signed_innovation':None if z is None else str(z),'bound':None if bound is None else str(bound),
                         'margin':None if bound is None else str(bound-z),'missing':missing,'reason':(reason or ('unknown_level_constant' if C is None else None)) if missing else None,
                         'finite_pass':None if missing else z<=bound,'global_bound_proved':False})
    return {'observations':rows,'finite_passes':sum(r['finite_pass'] is True for r in rows),'finite_failures':sum(r['finite_pass'] is False for r in rows),
            'missing_cases':sum(r['missing'] for r in rows),'finite_cases':len(rows),'global_bound_proved':False}


def positive_prime_singleton_obstruction(program):
    """Conditional-program global disproof, NOT an actual Mobius counterexample."""
    target=normalized_target(program['target'])
    if len(target['filter'])!=1 or target['filter'][0]['divisor']!=1:return {'admitted':False,'reason':'actual singleton divisor1 filter required'}
    alpha=rational(target['filter'][0]['weight'])
    coefficients=[]
    for term in canonical_potential_terms(program['terms']):
        f=term['feature'];b=f['vector'];eta=rational(f['eta'])
        if f['scheme']=={'prime_power':'1/2','core_power':'1/2'} and b==[0,0,0,0,0,1,0,0,0] and eta<1:
            coefficients.append({'weight':term['weight'],'eta':str(eta),'prime_amplitude':str(alpha*(target['r']+target['l']))})
    return {'admitted':bool(coefficients),'reason':None if coefficients else 'no covered positive prime singleton',
            'covered_terms':coefficients,'component_identity_threshold':16,'lower_bound_threshold':4096,
            'lower_bound':'V(X)>=weight*j^2*(log2)^2/32 * X^(1-eta)/(log X)^2',
            'contradiction':'W=E+V>=V, while the original cofinal innovation premise telescopes to W(X)=O_q(X^(1/q)); choose arbitrarily large q with 1/q<1-eta.',
            'finite_data_used':False,'actual_all_scale_signed_bound_proved':False,'RH_proved':False}


def feature_table(profile,targets,schemes,scales=None,*,work_budget=1000000000,bit_budget=1000000):
    """Independent complete-table evaluator; insufficient work raises, never projects."""
    integer(work_budget);integer(bit_budget,1)
    require(profile['status']=='available','complete profile unavailable')
    rawrows=profile['value']['rows'];features=feature_dictionary(schemes)
    scales=sorted(set(r['X'] for r in rawrows)) if scales is None else sorted(set(scales))
    records={}
    for row in rawrows:
        key=(row['target_id'],row['X'],row['scheme_id']);require(key not in records,'duplicate profile row');records[key]=row
    rows=[];cost=0
    for target in targets:
        tid=digest(normalized_target(target))
        for X in scales:
            values={};energies=[]
            for f in features:
                row=records[(tid,X,f['scheme_id'])];cost+=sum(bool(v) for v in f['vector'])**2
                if cost>work_budget:raise RuntimeError('independent complete feature work budget exceeded')
                values[f['feature_id']]=str(quadratic_feature(row,f['vector'],f['eta']));energies.append(row['E'])
            require(len(set(energies))==1,'partition-dependent energy')
            rows.append({'target_id':tid,'X':X,'E':energies[0],'features':values,'feature_missing':{}})
    return {'status':'available','value':{'targets':[{'target_id':digest(normalized_target(t)),'target':normalized_target(t)} for t in targets],
        'features':features,'rows':rows,'dictionary_sha256':digest(features),'full_signed_Gram_retained':True,'global_bound_proved':False},
        'reason':None,'cost':cost,'cost_scope':'nonzero quadratic scalar products only; not bit complexity, parsing or physical allocations'}


def check_candidate_archive(factory,table,features,training_scales,levels):
    """Verify complete productions, proposal rationalization and exact finite fits.

    LP status is preserved as a proposal receipt, not independently proved optimal.
    """
    import math
    target=normalized_target(factory['target']);require(factory['target']==target,'noncanonical factory target')
    require(factory['schema']==1 and factory['target_id']==digest(target) and factory['dictionary_sha256']==digest(features),'factory bindings mismatch')
    require(factory['training_scales']==list(training_scales) and factory['levels']==list(levels) and factory['global_bound_proved'] is False,'factory domain/claim mismatch')
    dictionary_by_id={f['feature_id']:f for f in table['value']['features']};require(all(dictionary_by_id.get(f['feature_id'])==f for f in features),'undeclared factory features')
    schedule=[({'kind':'baseline'},[])]
    for feature in features:
        for weight in ('1/4','1','4'):
            schedule.append(({'kind':'singleton','feature_id':feature['feature_id'],'scheme_id':feature['scheme_id'],'weight':weight},[{'feature':feature,'weight':weight}]))
    for group in sorted({f['scheme_id'] for f in features})+['all']:
        for penalty in ('0','1/1024'):schedule.append(({'kind':'lp','group':group,'penalty':penalty},None))
    archive=factory['proposal_archive'];require(len(archive)==len(schedule),'incomplete proposal archive')
    candidates={};order=[];failures=0;aliases=0
    for (origin,terms),entry in zip(schedule,archive):
        require(entry['origin']==origin,'production origin/order mismatch')
        if origin['kind']=='lp':
            if 'program_id' not in entry:
                require(entry.get('status') in ('missing','failed') and entry.get('discarded') is True and 'exact_program' not in entry,'failed proposal omitted or promoted')
                require(entry.get('reason') or entry.get('solver'),'failure reason/solver missing')
                if entry.get('solver'):require(entry['solver'].get('success') is False,'successful solver classified failed')
                failures+=1;continue
            solver=entry['solver'];require(solver['success'] is True and type(solver['status']) is int and solver['status']==0,'LP success receipt mismatch')
            require(solver['role']=='proposal only; no LP optimality certificate; exact refit authoritative','LP mathematical overclaim')
            fs=[f for f in features if origin['group']=='all' or f['scheme_id']==origin['group']];xs=solver['float_solution']
            require(isinstance(xs,list) and len(xs)==len(fs)+len(levels) and all(type(x) in (int,float) and math.isfinite(x) for x in xs),'complete finite solver vector required')
            weights=[Fraction(float(x)).limit_denominator(64) for x in xs[:len(fs)]]
            require(all(0<=w<=8 for w in weights),'quantized LP weight outside box')
            require(solver['rationalized_weights']==list(map(str,weights)),'proposal quantization mismatch')
            require(solver['float_objective'] is not None and math.isfinite(solver['float_objective']),'finite proposal objective required')
            terms=[{'feature':f,'weight':str(w)} for f,w in zip(fs,weights)]
        else:require(entry['solver'] is None,'non-LP production with solver')
        terms=canonical_potential_terms(terms);base={'target':target,'terms':terms};constants,evidence=exact_refit(base,table,training_scales,levels)
        program=dict(base,constants=constants);pid=digest(program);alias=pid in candidates
        require(entry['exact_program']==program and entry['program_id']==pid and entry['fit_observations']==evidence,'exact proposal/fit/hash mismatch')
        require(entry['alias_of']==(pid if alias else None) and entry['discarded'] is alias,'alias disposition mismatch')
        if alias:candidates[pid]['origins'].append(origin);aliases+=1
        else:
            order.append(pid);candidates[pid]={'program_id':pid,'program':program,'origins':[origin],'training_score':exact_score(program,table,training_scales,levels)}
    require(factory['candidates']==[candidates[pid] for pid in order],'all candidate scores/origins/coverage mismatch')
    return {'all_passed':True,'proposal_count':len(archive),'candidate_count':len(candidates),'alias_count':aliases,'failed_or_missing_LP':failures,
            'exact_quantization_refits_scores_verified':True,'LP_optimality_independently_verified':False,'global_bound_proved':False}
