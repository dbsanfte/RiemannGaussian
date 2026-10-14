"""Independent complete divisor/localizer builder. No producer imports or signs."""
from fractions import Fraction as F
from math import gcd
import check_cancellation_factor_search as B
import check_grouped_arithmetic as G
P=B.P
SPEC=dict(version='signed-divisor-localizers-v1',regions=['parent','child'],powers=[-1,0,1],square_forms=['plain','squarefree_plain','modulated','plus','minus'],relation_forms=['norm_closure','gcd_inverse'],divisor_domain='all 1<=d<=t',pair_domain='all ordered 1<=a,b<=t',source_scale='N=4X-1',squarefree_weights='factor-certified 0/1; no Mobius signs')
digest=B.I.digest

def additions():
    out=dict(square=[],relation=[])
    for r in SPEC['regions']:
        for j in SPEC['powers']:
            c=dict(version=SPEC['version'],region=r,power=j,divisor_domain=SPEC['divisor_domain'],pair_domain=SPEC['pair_domain'])
            for f in SPEC['square_forms']:
                d=dict(c,family='divisor_localizer_square',form=f);out['square'].append(dict(d,id=digest(d)))
            for f in SPEC['relation_forms']:
                d=dict(c,family='divisor_localizer_relation',form=f);out['relation'].append(dict(d,id=digest(d)))
    return out

def descriptors():
    base=B.descriptors();new=additions();return {k:base[k]+new[k]for k in base}

def build_additions(X,*,max_horizon=80,max_operations=200000000,max_terms=30000,max_coefficient_bits=4096):
    for v in [X,max_horizon,max_operations,max_terms,max_coefficient_bits]:
        if type(v)is not int or v<1:raise ValueError('strict positive integer limits')
    H=4*X-1
    if H>max_horizon or 12*H**3>max_operations:raise OverflowError('complete divisor independent preflight')
    used=0;producer_proxy=0
    def charge(n=1):
        nonlocal used
        used+=n
        if used>max_operations:raise OverflowError('independent divisor work')
    def insert(p,m,w):
        charge();v=p.get(m,F(0))+w
        if max(abs(v.numerator).bit_length(),v.denominator.bit_length())>max_coefficient_bits:raise OverflowError('coefficient bits')
        if v:p[m]=v
        else:p.pop(m,None)
        if len(p)>max_terms:raise OverflowError('polynomial terms')
    def dump(p):
        charge(len(p));return P.canonical(p)
    factors={};sf={}
    for d in range(1,H+1):
        fac=G.P.factor(d);factors[d]=[[p,e]for p,e in sorted(fac.items())];sf[d]=int(all(e==1 for e in fac.values()));charge(d.bit_length())
    sqgroups=[];relgroups=[];archive=[]
    for region in SPEC['regions']:
        ts=list(range(X,2*X)if region=='parent'else range(2*X,4*X))
        pairs=[];members=[];gcounts={}
        for t in ts:
            for a in range(1,t+1):
                for b in range(1,t+1):
                    charge();pairs.append([t,a,b]);g=gcd(a,b);gcounts[g]=gcounts.get(g,0)+1
            for d in range(1,t+1):
                for a in range(1,t+1):
                    charge()
                    if a%d==0:members.append([t,d,a])
        for power in SPEC['powers']:
            groups={f:[]for f in SPEC['square_forms']};norms={};inverse={};cells=0
            for t in ts:
                for d in range(1,t+1):
                    cells+=1;source={}
                    for a in range(1,t+1):
                        charge()
                        if a%d==0:source[(a,)]=F(t,a)if power==-1 else F(1)if power==0 else F(a,t)
                    mod={tuple(sorted((d,a))):w for (a,),w in source.items()}
                    for f in SPEC['square_forms']:
                        p=source if f in ('plain','squarefree_plain')else mod if f=='modulated'else P.add(source,mod,F(1)if f=='plus'else F(-1))
                        groups[f].append(dict(weight=str(sf[d]if f=='squarefree_plain'else 1),poly=dump(p)))
                    n=len(source);producer_proxy+=7*n+n*n+n*(n+1)//2
                # Independent pair-first construction: project each ordered pair
                # into its gcd inverse row and EVERY common-divisor norm row.
                for a in range(1,t+1):
                    for b in range(1,t+1):
                        g=gcd(a,b);m=tuple(sorted((a,b)));w=F(t*t,a*b)if power==-1 else F(1)if power==0 else F(a*b,t*t)
                        insert(inverse.setdefault(g,{}),m,w)
                        for d in range(1,g+1):
                            charge()
                            if g%d==0:insert(norms.setdefault(d,{}),m,w)
                producer_proxy+=t*t
            ng=[dict(spec=dict(kind='norm',n=d,factors=factors[d]),multiplier=dump(p))for d,p in sorted(norms.items())]
            ig=[dict(spec=dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g),multiplier=dump(p))for g,p in sorted(inverse.items())]
            producer_proxy+=sum(len(p)for p in norms.values())+sum(len(p)for p in inverse.values())
            orderedgroups=[groups[f]for f in SPEC['square_forms']];sqgroups.extend(orderedgroups);relgroups.extend([ng,ig])
            archive.append(dict(region=region,power=power,scales=ts,ordered_pair_count=len(pairs),ordered_pairs_sha256=digest(pairs),gcd_pair_counts={str(g):c for g,c in sorted(gcounts.items())},divisor_cells=cells,divisor_members_count=len(members),divisor_members_sha256=digest(members),square_groups_sha256=digest(orderedgroups),norm_group_sha256=digest(ng),gcd_inverse_group_sha256=digest(ig),aggregation='sum complete multipliers with equal primitive relation; no source pair dropped'))
    return dict(square_groups=sqgroups,relation_groups=relgroups,archive=archive,spec=SPEC,construction_operations=producer_proxy,arithmetic_sign_values_substituted=False,global_bound_proved=False,RH_proved=False)

def build(program,X,**limits):
    if program.get('target')!='mu':raise ValueError('mu inverse-of-ones target only')
    extra=build_additions(X,**limits);out=B.build(program,X);out['instance']['square_groups'].extend(extra['square_groups']);out['instance']['relation_groups'].extend(extra['relation_groups']);d=descriptors()
    out.update(square_ids=[v['id']for v in d['square']],relation_ids=[v['id']for v in d['relation']],dictionary_sha256=digest(d),divisor_archive=extra['archive'],divisor_spec=SPEC,divisor_construction_operations=extra['construction_operations']);return out

def auxiliary():return B.I.auxiliary_constraint(descriptors())

def check_builder(program,X,output,**limits):
    expected=build(program,X,**limits)
    for key in ['instance','square_ids','relation_ids','dictionary_sha256','factor_archive','divisor_archive','divisor_spec','divisor_construction_operations']:
        if output.get(key)!=expected[key]:raise ValueError('complete divisor builder '+key)
    return dict(verified=True,complete_ordered_pairs=True,complete_divisor_membership=True,all_primitive_multipliers=True,arithmetic_sign_values_substituted=False,global_bound_proved=False,RH_proved=False)
