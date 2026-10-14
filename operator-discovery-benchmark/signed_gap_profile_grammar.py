"""Exact rational exponent schedules, independent constant laws and signed gaps."""
from fractions import Fraction as Q
from math import factorial,comb
from itertools import combinations
from functools import lru_cache
import flint
from estimate_grammar import inverse_one_prefix
from divisor_dual_grammar import ceil_power as _ceiling
from stable_scale_report import digest

VERSION='actual-signed-nullspace-gap-independent-exponent-constant-log-profiles-v1'

@lru_cache(maxsize=8192)
def ceil_power(n,p):return _ceiling(n,Q(p))


def integer_program(p,q,denominator=None,bit_budget=65536):
    k=p['kind']
    if k=='constant':return 1
    if k=='power':return 1+ceil_power(q,Q(p['power']))
    if k=='factorial':
        if q>bit_budget:return None
        v=factorial(q);return v if v.bit_length()<=bit_budget else None
    if k=='exponential':
        r=ceil_power(q,Q(p['power']))
        if r is None or r>bit_budget:return None
        return 2**r
    if k=='denominator_power':return ceil_power(denominator,Q(p['power']))
    if k=='free_per_level':return None
    raise ValueError('Unknown integer constant law')


def denominator(p,q,bit_budget=65536):
    if p['kind']=='fixed':return None
    if p['kind']=='power':return ceil_power(q,Q(p['power']))
    if p['kind']=='factorial':return integer_program(p,q,bit_budget=bit_budget)
    if p['kind']=='exponential':return integer_program(p,q,bit_budget=bit_budget)
    raise ValueError('Unknown exponent schedule')


def epsilon(p,q):
    if type(q)is not int or q<1:raise ValueError('Positive integer parameter required')
    if p['kind']=='fixed':return Q(p['epsilon'])
    d=denominator(p,q)
    return None if d is None else Q(1,d)


def schedule_certificate(p):
    k=p.get('kind');valid=k=='factorial' or k in ['power','exponential'] and Q(p['power'])>0 or k=='fixed' and Q(p['epsilon'])>0
    return {'admitted':valid,'cofinal_positive_epsilon':valid and k!='fixed','semantic_denominator_cap':False}


def family_certificate(p):
    try:
        s=schedule_certificate(p['exponent_schedule']);c=p['constant_law'];k=c['kind'];valid=s['admitted'] and p.get('arithmetic_model')=='inverse_one' and Q(p['log_power'])>=0 and (k in ['constant','factorial','free_per_level'] or k in ['power','denominator_power'] and Q(c['power'])>=0 or k=='exponential' and Q(c['power'])>0)
    except (KeyError,TypeError,ValueError):valid=False;s={'cofinal_positive_epsilon':False}
    return {'admitted':valid,'RH_if_global_half_gap':valid and s['cofinal_positive_epsilon'],'every_dyadic_scale_required':True,'constant_scale_independence_required':True,'global_actual_critical_signed_gap_proved':False,'RH_proved':False}


def evaluate(p,X,q):
    if type(X)is not int or X<1 or not family_certificate(p)['admitted']:raise ValueError('Actual arithmetic, positive integer scale and admitted profiles required')
    eps=epsilon(p['exponent_schedule'],q)
    if eps is None:return {'missing':True,'reason':'exponent_schedule_resource_limit'}
    if p['constant_law']['kind']=='free_per_level':
        C=p['fitted_constants'].get(str(q))
        if C is None:return {'missing':True,'reason':'unobserved_level_constant_is_not_fitted','no_new_level_fit_counted_as_prediction':True}
        C=Q(C)
    else:
        den=denominator(p['exponent_schedule'],q);K=integer_program(p['constant_law'],q,den)
        if K is None:return {'missing':True,'reason':'constant_program_resource_limit'}
        C=Q(p['fitted_coefficient'])*K
    root=ceil_power(X,eps);log=ceil_power(X.bit_length(),Q(p['log_power']))
    if root is None or log is None:return {'missing':True,'reason':'rational_ceiling_resources_exhausted'}
    D=C*X*root*log
    return {'missing':False,'epsilon':str(eps),'C':str(C),'root_ceiling':root,'log_ceiling':log,'D':str(D),'charged_defect_bound':str(4*X*D),
        'ordinary_energy_power':str(2+eps),'log_power':p['log_power'],'scale_independent_constant':True}


def arithmetic(scales):
    N=4*max(scales);mu=inverse_one_prefix(N);M=0;E=0;Qn=0;snap={};needed={t for X in scales for t in [X,2*X,4*X]}
    for n in range(1,N+1):
        E+=M*M;M+=mu[n];Qn+=mu[n]*mu[n]
        if n in needed:snap[n]=(E,Qn,M)
    rows=[]
    for X in scales:
        A=snap[2*X][0]-snap[X][0];child=snap[4*X][0]-snap[2*X][0];rows.append({'X':X,'energy':A,'child_energy':child,'signed_defect':child-4*A,'squarefree_count_through_4X':snap[4*X][1]})
    return {'cutoff':N,'complete_inverse_sha256':digest(mu),'rows':rows,'coefficient_origin':'every divisor row, no prime or factor oracle','producer_prime_or_factor_oracle_used':False,'whole_signed_defect_retained':True}


def fit(template,data,levels):
    if not family_certificate(template)['admitted']:raise ValueError('Actual inverse and admitted exponent/constant family required')
    p=dict(template);law=p['constant_law'];ratios={}
    for q in levels:
        eps=epsilon(p['exponent_schedule'],q);items=[]
        for row in data['rows']:
            X=row['X'];root=ceil_power(X,eps);log=ceil_power(X.bit_length(),Q(p['log_power']));items.append(Q(2*max(row['signed_defect'],0),X*root*log*row['squarefree_count_through_4X']))
        ratios[q]=max(items)
    margin=Q(5,4);tiny=Q(1,2**64)
    if law['kind']=='free_per_level':p['fitted_constants']={str(q):str(margin*ratios[q]+tiny) for q in levels}
    else:
        values=[ratios[q]/integer_program(law,q,denominator(p['exponent_schedule'],q)) for q in levels];p['fitted_coefficient']=str(margin*max(values)+tiny)
    return p


def observations(p,data,levels):
    rows=[]
    for row in data['rows']:
        X=row['X'];Qn=row['squarefree_count_through_4X'];delta=row['signed_defect']
        for q in levels:
            value=evaluate(p,X,q);entry={'X':X,'level':q,'parameters':value,'actual_signed_defect':delta,'Q_4X':Qn}
            if not value['missing']:
                D=Q(value['D']);gap=D*Qn-delta;half=D*Qn/2-delta;entry.update({'exact_signed_nullspace_gap':str(gap),'exact_half_gap_margin':str(half),'finite_half_gap_pass':half>=0,
                    'positive_defect_requirement':str(Q(2*max(delta,0),X*value['root_ceiling']*value['log_ceiling']*Qn)),
                    'charged_bound_over_generic':str(Q(value['charged_defect_bound'])/sum_of_squares(4*X,2*X)),
                    'global_signed_bound_proved':False,'finite_test_is_not_all_scale_certificate':True})
            rows.append(entry)
    return rows


def sum_of_squares(U,L):return (U-1)*U*(2*U-1)//6-(L-1)*L*(2*L-1)//6


def min_response(dimensions):
    rows=[]
    for m in dimensions:
        best={}
        for bits in range(2**m):
            J=bits.bit_count();c=0;loss=0
            for t in range(m):loss+=c*c;c+=(bits>>t)&1
            if J not in best or loss<best[J][0]:best[J]=(loss,bits)
        rows +=[{'dimension':m,'mass':J,'anonymous_response':loss,'minimizer_bits':bits} for J,(loss,bits) in sorted(best.items())]
    return rows


MONOMIALS=[(0,0),(1,0),(2,0),(3,0),(4,0),(0,1),(0,2),(1,1),(2,1),(1,2)]


def infer_polynomial(rows,support_budget=4):
    """Sparse exact fits; neither an expected polynomial nor coefficient given."""
    data=[[Q(row['mass']**i*row['dimension']**j) for i,j in MONOMIALS] for row in rows];y=[Q(row['anonymous_response']) for row in rows];fits=[]
    for size in range(1,support_budget+1):
        for support in combinations(range(len(MONOMIALS)),size):
            A=[[v[k] for k in support] for v in data];G=[[sum(row[i]*row[j] for row in A) for j in range(size)] for i in range(size)];rhs=[sum(row[i]*t for row,t in zip(A,y)) for i in range(size)]
            try:
                z=flint.fmpq_mat([[flint.fmpq(v.numerator,v.denominator) for v in row] for row in G]).solve(flint.fmpq_mat([[flint.fmpq(v.numerator,v.denominator)] for v in rhs]));coeff=[Q(str(z[i,0])) for i in range(size)]
            except (ZeroDivisionError,ValueError):continue
            if any(not c for c in coeff):continue
            error=sum((t-sum(c*row[i] for i,c in enumerate(coeff)))**2 for row,t in zip(A,y));fits.append({'terms':[[*MONOMIALS[k],str(c)] for k,c in zip(support,coeff)],
                'exact_squared_residual':str(error),'support_size':size,'expected_formula_supplied':False})
    fits.sort(key=lambda p:(Q(p['exact_squared_residual']),p['support_size'],len(str(p['terms'])),digest(p['terms'])))
    return {'selected':fits[0] if fits else None,'retained_fits':fits,'feature_dictionary':[list(t) for t in MONOMIALS],'supplied_generic_inference_method':'sparse exact polynomial fitting','global_minimum_bound_proved':False}
