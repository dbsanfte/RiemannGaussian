"""Complete actual-c critical core correctors, exact Gram, additive recovery.

Uniform corrector envelopes are proved in critical_core_proof.txt. No actual
full corrected/base energy bound or RH result is inferred from numerical data.
"""
from array import array
from fractions import Fraction as F
import hashlib
import json
import math
from detector_safe_evaluation import rational_ceiling
import arithmetic_filter_pole_budget as source

ENVELOPE_K=16


def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def integer(value,minimum=0):
    if type(value) is not int or value<minimum:raise ValueError('exact integer domain required')
    return value


def rational(value):
    if isinstance(value,(float,bool)) or not isinstance(value,(int,str,F)):raise ValueError('exact rational required')
    return F(value)


def feature_spec(feature):
    if not isinstance(feature,dict) or set(feature) not in ({'theta','core_depth'},{'theta','core_depth','feature_id'}):raise ValueError('exact theta/core_depth feature required')
    theta=rational(feature['theta']);integer(feature['core_depth'],1)
    if theta<=0:raise ValueError('positive rational theta required')
    result={'theta':str(theta),'core_depth':feature['core_depth']}
    if 'feature_id' in feature and feature['feature_id']!=digest(result):raise ValueError('feature digest mismatch')
    return result


def feature_descriptor(feature):
    spec=feature_spec(feature);return dict(spec,feature_id=digest(spec))


def target_spec(target):
    if not isinstance(target,dict) or set(target)!={'r','l','filter'}:raise ValueError('actual fixed target schema required')
    integer(target['r']);integer(target['l'])
    if target['r']+target['l']<1:raise ValueError('positive total arity required')
    terms=source.canonical_filter(target['filter'])
    if not terms:raise ValueError('nonzero fixed filter required')
    return {'r':target['r'],'l':target['l'],'filter':terms}


class Meter:
    def __init__(self,budget,bits):integer(budget);integer(bits,1);self.cost=0;self.budget=budget;self.bits=bits
    def add(self,n=1):
        if self.cost+n>self.budget:raise OverflowError('complete scalar work budget exceeded')
        self.cost+=n
    def check(self,n):
        if abs(n).bit_length()>self.bits:raise OverflowError('integer coefficient bit budget exceeded')
        return n


def exact_ceiling(X,power,bits):
    result=rational_ceiling(X,power,bit_budget=bits)
    if not result.available:
        if result.status.value=='invalid':raise ValueError('invalid exact ceiling: '+str(result.reason))
        raise OverflowError('exact ceiling unavailable: '+str(result.reason))
    return result.value


def exact_floor(X,power,bits):
    power=rational(power);ceiling=exact_ceiling(X,power,bits)
    if X==1:return 1
    if X.bit_length()*power.numerator>bits or ceiling.bit_length()*power.denominator>bits:raise OverflowError('exact floor comparison bit budget exceeded')
    return ceiling if ceiling**power.denominator==X**power.numerator else ceiling-1


def factor_table(N,meter):
    meter.add(4*(N+1));least=list(range(N+1));exponent=[0]*(N+1);core=[0]*(N+1);omega=[0]*(N+1);core[1]=1
    for p in range(2,math.isqrt(N)+1):
        meter.add()
        if least[p]!=p:continue
        for n in range(p*p,N+1,p):
            meter.add()
            if least[n]==n:least[n]=p
    for n in range(2,N+1):
        meter.add(4);p=least[n];m=n//p;omega[n]=omega[m]+1
        if m%p==0:exponent[n]=exponent[m]+1;core[n]=core[m]
        else:exponent[n]=1;core[n]=m
    return least,exponent,core,omega


def _prefix_buffer(safe64):return array('q',[0]) if safe64 else [0]


def _source_profile(X,feature,c,factors,meter,safe64):
    T=2*X-1;z=exact_floor(X,feature['theta'],meter.bits);u=math.isqrt(X);h=feature['core_depth']
    least,exponent,core,omega=factors;full=_prefix_buffer(safe64);retained=_prefix_buffer(safe64);removed=_prefix_buffer(safe64)
    classes=array('B');counts=[0]*4
    for m in range(1,T+1):
        meter.add(8)
        active=m>=2 and least[m]<=z and exponent[m]%2==0 and core[m]<=u
        if not active:classification=0
        elif core[m]==1:classification=1
        elif omega[core[m]]>h:classification=2
        else:classification=3
        counts[classification]+=1;classes.append(classification)
        a=c[m] if active else 0;r=a if classification in (1,2) else 0;removed_a=a-r
        if a!=r+removed_a:raise ValueError('source coefficient reconstruction failed')
        full.append(meter.check(full[-1]+a));retained.append(meter.check(retained[-1]+r));removed.append(meter.check(removed[-1]+removed_a))
        if full[-1]!=retained[-1]+removed[-1]:raise ValueError('complete source prefix reconstruction failed')
    record={'X':X,'feature_id':feature['feature_id'],'cutoffs':{'z':z,'u':u},'source_horizon':T,
            'full_prefix_sha256':digest(list(full)),'retained_prefix_sha256':digest(list(retained)),
            'removed_prefix_sha256':digest(list(removed)),'coverage_sha256':digest(list(classes)),
            'class_counts':counts,'coefficient_reconstruction_verified':True,'prefix_reconstruction_verified':True}
    return retained,record


def profile(scales,targets,features,*,work_budget=3000000000,max_n=1048575,bit_budget=1000000,use_numpy=True):
    """Every raw Gram coordinate is retained, including base/corrector cross terms."""
    meter=Meter(work_budget,bit_budget)
    try:
        integer(max_n,1);scales=list(scales);targets=[target_spec(t) for t in targets];features=[feature_descriptor(f) for f in features]
        if not scales or not targets or not features:raise ValueError('nonempty complete profile dimensions required')
        for X in scales:integer(X,1)
        if len(set(scales))!=len(scales) or len({digest(t) for t in targets})!=len(targets) or len({f['feature_id'] for f in features})!=len(features):raise ValueError('duplicate profile dimension')
        N=2*max(scales)-1
        if N>max_n:raise OverflowError('complete source horizon exceeds max_n')
        factors=factor_table(N,meter);coefficients={};source_prefixes={};absolute_coefficients={};provenance=[]
        arities=list(dict.fromkeys([(t['r'],t['l']) for t in targets]+[(1,1)]))
        for r,l in arities:
            result=source.actual_coefficients(N,r,l,work_budget=work_budget-meter.cost);meter.add(result['cost'])
            if result['status']!='available':raise OverflowError('complete actual coefficient source unavailable: '+str(result.get('reason')))
            a=result['coefficients'];absolute=0
            for value in a:meter.add();meter.check(value);absolute+=abs(value)
            safe64=absolute<=2**63-1;pref=_prefix_buffer(safe64)
            for value in a[1:]:meter.add();pref.append(meter.check(pref[-1]+value))
            coefficients[(r,l)]=a;source_prefixes[(r,l)]=pref;absolute_coefficients[(r,l)]=absolute
            provenance.append({'r':r,'l':l,'source_cost':result['cost'],'source_sha256':digest(a),'prefix_sha256':digest(list(pref)),
                               'absolute_coefficient_sum':absolute,'compact_prefix_int64_proved_safe':safe64})
        c=coefficients[(1,1)];c_safe64=absolute_coefficients[(1,1)]<=2**63-1;rows=[];source_profiles=[]
        ids=['base_G']+[f['feature_id'] for f in features];dim=len(ids)
        for X in scales:
            residuals=[];records=[];normalizers=[1]
            for feature in features:
                residual,record=_source_profile(X,feature,c,factors,meter,c_safe64);residuals.append(residual);records.append(record);source_profiles.append(record)
                root=exact_ceiling(X,F(1,2*(feature['core_depth']+1)),bit_budget);meter.check(root);normalizers.append(root)
            for target in targets:
                terms=target['filter'];Q=math.lcm(*(F(t['weight']).denominator for t in terms));weights=[(t['divisor'],int(F(t['weight'])*Q)) for t in terms]
                input_columns=[source_prefixes[(target['r'],target['l'])]]+residuals
                vectors=[]
                for i,pref in enumerate(input_columns):
                    key=(target['r'],target['l']) if i==0 else (1,1)
                    bound=sum(abs(w) for d,w in weights)*absolute_coefficients[key]
                    vector=_prefix_buffer(bound<=2**63-1);del vector[:]
                    for n in range(X,2*X):
                        meter.add(len(weights));vector.append(meter.check(sum(w*pref[n//d] for d,w in weights)))
                    vectors.append(vector)
                meter.add(dim*X)
                maximum=max(abs(v) for col in vectors for v in col);int64_bound=meter.check(X*maximum*maximum);meter.add(dim*dim*X)
                gram=None;engine='python_int'
                if use_numpy and int64_bound<=2**63-1:
                    try:
                        import numpy as np
                        matrix=np.array(vectors,dtype=np.int64);gram=(matrix@matrix.T).tolist();engine='numpy_int64_proved_safe'
                    except ImportError:pass
                if gram is None:
                    gram=[[0]*dim for _ in range(dim)]
                    for i in range(dim):
                        for j in range(i,dim):gram[i][j]=gram[j][i]=sum(a*b for a,b in zip(vectors[i],vectors[j]))
                for row in gram:
                    for val in row:meter.check(val)
                base_den=meter.check(X*X*Q*Q)
                rows.append({'X':X,'target_id':digest(target),'feature_ids':ids,'gram_numerators':gram,'gram_base_denominator':base_den,
                             'correction_denominators':normalizers,'weight_common_denominator':Q,'gram_engine':engine,
                             'prefix_abs_bound':maximum,'int64_gram_abs_bound':int64_bound,'complete_block':True,
                             'source_profile_sha256':[digest(r) for r in records],'base_energy':str(F(gram[0][0],base_den)),
                             'all_base_corrector_cross_terms_retained':True,'global_bound_proved':False})
        return {'status':'available','value':{'rows':rows,'features':features,'targets':targets,'source_profiles':source_profiles,
                 'source_provenance':provenance,'complete_horizon':N,'base_coordinate':'mandatory original G',
                 'corrector_source':'actual complete c=mu*lambda, even when base target is mu',
                 'global_corrector_envelope_proved':True,'actual_all_scale_signed_bound_proved':False,'global_bound_proved':False,'RH_proved':False},
                'cost':meter.cost,'reason':None,'cost_scope':'source scalar/list work, factor/source-profile loops, filtered prefix and full Gram products; not physical memory, hashing/serialization or total bit complexity'}
    except (OverflowError,MemoryError) as e:return {'status':'missing','value':None,'cost':meter.cost,'reason':str(e)}
    except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return {'status':'invalid','value':None,'cost':meter.cost,'reason':str(e)}


def feature_certificate(feature,terms):
    feature=feature_descriptor(feature);terms=source.canonical_filter(terms);Lambda=sum((abs(F(t['weight'])) for t in terms),F(0))
    return {'kind':'actual_c_critical_core_envelope','feature':feature,'filter':terms,'uniform_K':ENVELOPE_K,'filter_l1':str(Lambda),
            'domain':'every integer X>=1; every prefix0<=y<=2X; all positive integer core_depth and positive rational theta',
            'raw_residual_envelope':'16*X^(1/2+1/[2(h+1)])*(1+log(2X))^2',
            'normalized_corrector_energy_envelope':str(ENVELOPE_K**2*Lambda**2)+'*(1+log(2X))^4',
            'cofinal_energy_constant':'256*filter_l1^2*(128+192*q^4)',
            'global_corrector_envelope_proved':True,'actual_all_scale_signed_bound_proved':False,'RH_proved':False}


def recovery_certificate(target,corrections):
    target=target_spec(target);total=F(0)
    for term in corrections:
        if not isinstance(term,dict) or set(term)!={'feature','weight'}:raise ValueError('signed corrector term schema')
        feature_descriptor(term['feature']);total+=abs(rational(term['weight']))
    Lambda=sum((abs(F(t['weight'])) for t in target['filter']),F(0));envelope=ENVELOPE_K**2*Lambda**2*total**2
    return {'kind':'complete additive critical energy recovery','target':target,'corrector_weight_l1':str(total),'filter_l1':str(Lambda),
            'critical_corrector_combination_envelope':str(envelope)+'*(1+log(2X))^4',
            'recovery_inequalities':'E_G<=2E_H+2E_corrector; E_H<=2E_G+2E_corrector',
            'global_additive_recovery_proved':True,'cofinal_H_energy_iff_original_G_energy':True,
            'H_is_block_dependent':True,'ordinary_Mellin_pole_argument_applies_directly_to_H':False,
            'conditional_original_G_pole_bridge':source.certify(target['r'],target['l'],target['filter']),
            'actual_H_energy_bound_proved':False,'actual_all_scale_signed_bound_proved':False,'RH_proved':False}
