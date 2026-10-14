"""Source-generated finite power-kernel normalization and scale templates.

Analytic values remain explicit finite defects, never ordinary coefficient
moments. Uncovered channels and all inverse/filter debts are retained.
"""
from fractions import Fraction as Q
from itertools import combinations
from copy import deepcopy
import sympy as S
from flint import arb,ctx

import arithmetic_prefix_relations as A

Meter=A.Meter


def _q(text,m):
    return A._rational(text,m)


def factor_candidates(source,meter=None,kernel_v_values=()):
    """Find every candidate power atom, rather than supplying a desired factor."""
    m=Meter() if meter is None else meter;A.validate_source(source,m)
    lattice=source['lattice'];shifts=set()
    for channel in source['channels']:
        for atom in channel['atoms']:
            m.charge()
            if atom['kind']=='power' and 0<atom['shift']<lattice:shifts.add(atom['shift'])
    if type(kernel_v_values) not in (tuple,list) or len(kernel_v_values)>32:raise ValueError('bounded requested kernel shifts')
    requested=[_q(v,m) for v in kernel_v_values]
    result=[]
    for shift in sorted(shifts):
        m.charge(2+sum(len(c['atoms']) for c in source['channels']))
        covered=[];uncovered=[]
        for i,channel in enumerate(source['channels']):
            found=[j for j,a in enumerate(channel['atoms']) if a==dict(kind='power',shift=shift)]
            if not found:uncovered.append(i);continue
            j=found[0]
            covered.append(dict(channel=i,removed_atom=j,
                                residual_atom_indices=[k for k in range(len(channel['atoms'])) if k!=j],
                                added_atoms=[],
                                weight=channel['weight'][:]))
        theta=Q(lattice-shift,lattice)
        result.append(dict(power_shift=shift,power_exponent=str(-Q(shift,lattice)),theta=str(theta),
                           kernel_r=str(Q(shift,lattice)),kernel_v=None,
                           kernel_kind='pure_power',main_multiplier=dict(kind='one'),
                           covered=covered,uncovered=uncovered,unit_retained=True,
                           residual_source_reference='weighted sum of covered channels after removing exactlyone atom'))
        values=set(Q(a['shift'],lattice) for c in source['channels'] for a in c['atoms'] if a['kind']=='mu' and a['shift']>shift)
        values.update(v for v in requested if v>Q(shift,lattice))
        for v in sorted(values):
            refs=deepcopy(covered)
            for ref in refs:
                atoms=source['channels'][ref['channel']]['atoms']
                matching=[j for j in ref['residual_atom_indices'] if atoms[j]['kind']=='mu' and Q(atoms[j]['shift'],lattice)==v]
                if matching:ref['residual_atom_indices'].remove(matching[0])
                else:ref['added_atoms']=[dict(kind='power',rational_shift=str(v))]
                m.charge(8+len(atoms))
            result.append(dict(power_shift=shift,power_exponent=str(-Q(shift,lattice)),theta=str(theta),
                kernel_r=str(Q(shift,lattice)),kernel_v=str(v),
                kernel_kind='shifted_mu_power',covered=refs,uncovered=uncovered[:],unit_retained=True,
                main_multiplier=dict(kind='reciprocal_zeta',argument=str(theta+v),
                                     auxiliary_mu_moment_converges=True,moment_source='mu_v'),
                normalization_transfer='residual analytic value = pure residual analytic value*zeta(theta+v)',
                residual_source_reference='exact quotient by power_r*mu_v using power_v as its Dirichlet inverse'))
    for factor in result:
        channels=[]
        for ref in factor['covered']:
            original=source['channels'][ref['channel']]
            atoms=[dict(kind=original['atoms'][j]['kind'],shift=str(Q(original['atoms'][j]['shift'],lattice))) for j in ref['residual_atom_indices']]
            atoms.extend(dict(kind=a['kind'],shift=a['rational_shift']) for a in ref['added_atoms'])
            channels.append(dict(source_channel=ref['channel'],atoms=atoms,weight=ref['weight'][:]))
        factor['residual_source']=dict(shift_convention='n^(-rational_shift)',channels=channels)
    return result


def _domain(domain,m):
    if domain is None:return None
    if type(domain) not in (tuple,list) or len(domain)!=2:raise ValueError('affine parameter interval')
    lower,upper=(_q(x,m) for x in domain)
    if lower>upper:raise ValueError('ordered affine parameter interval')
    return lower,upper


def _price(source,factor,alpha,domain,m):
    theta=Q(factor['theta']);prices=[];count=len(factor['covered'])
    kernel=kernel_provider(factor,source['lattice'],m)
    rho=Q(kernel['error_power']);kernel_C=Q(kernel['error_constant'])
    for ref in factor['covered']:
        channel=source['channels'][ref['channel']]
        atoms=[channel['atoms'][j] for j in ref['residual_atom_indices']]+ref['added_atoms']
        growth=sum((max(-Q(a['rational_shift']) if 'rational_shift' in a else Q(-a['shift'],source['lattice']),Q(0)) for a in atoms),Q(0))
        degree=len(atoms);m.charge(8+8*degree)
        if domain is None:
            coefficient=None
        else:
            c,b=(_q(x,m) for x in ref['weight'])
            weight=max(abs(c+b*domain[0]),abs(c+b*domain[1]))
            mass_C=max(Q(1),1/(1+growth-rho)) if degree else Q(1)
            block_C=Q(1) if not rho and not kernel['error_log_degree'] else Q(4)
            log_C=max(Q(1),alpha)**(2*max(degree-1,0))
            coefficient=str(Q(count)*weight*weight*kernel_C*kernel_C*mass_C*mass_C*block_C*log_C)
        power=2*rho+2*alpha*(1+growth-rho)-1 if degree else 2*rho-1
        prices.append(dict(channel=ref['channel'],coefficient=coefficient,
            coefficient_formula='covered_count*abs(weight)^2*kernel_C^2*mass_C^2*block_factor*max(1,alpha)^(2max(degree-1,0))',
            X_power=str(power),log_degree=2*max(degree-1,0)+2*kernel['error_log_degree'],
            divisor_degree=degree,coefficient_growth=str(growth),
            paid_subpower=power<=0,
            premise='abs residual coefficients<=n^growth*d_degree(n); delta when degree0'))
    return dict(kernel_envelope=kernel,
                finite_head_energy_terms=prices,
                head_complete=True,head_cutoff='floor(X^alpha)',
                parameter_domain=None if domain is None else list(map(str,domain)),
                analytic_defect_cost='OPEN',complete_centered_tail_cost='OPEN',
                uncovered_channel_cost='OPEN' if factor['uncovered'] else 'none',
                full_bound_proved=False)


def kernel_provider(factor,lattice,meter=None):
    m=Meter() if meter is None else meter;theta=_q(factor['theta'],m)
    if factor['kernel_kind']=='pure_power':
        return dict(error_constant=str(1/theta),error_power='0',error_log_degree=0,
                    lower=str(-1/theta),upper='0',domain='every real y>0')
    r=Q(factor['kernel_r']);v=Q(factor['kernel_v'])
    if not 0<r<1 or not v>r:raise ValueError('shifted kernel domain')
    tail=1+1/(v-r)
    if v<1:
        rho=1-v;constant=(1/(1-v)+tail)/theta;log_degree=0
    elif v==1:
        rho=Q(0);constant=(1+tail)/theta;log_degree=1
    else:
        rho=Q(0);constant=(v/(v-1)+tail)/theta;log_degree=0
    return dict(error_constant=str(constant),error_power=str(rho),error_log_degree=log_degree,
                main_multiplier=factor['main_multiplier'],
                envelope='C*y^rho*(1+log(max(y,1)))^log_degree',domain='every real y>0',
                positive_kernel=True,local_prime_power='p^(-e*r)*(1-p^(r-v)) for e>=1',
                absolute_kernel_moment_argument=str(theta+v))


def scale_templates(factor,divisors=(1,2,3),cutoff_exponents=('0','1/6','1/3'),meter=None):
    """Solve exact rational main-cancellation nullspaces in typed coefficients.

    a_j=lambda_j*d_j^theta; sumlambda=0 cancels the shared analytic value.
    Unequal cutoffs leave oriented finite moments explicitly, with their sign.
    """
    m=Meter() if meter is None else meter
    theta=_q(factor['theta'],m)
    if not 0<theta<1:raise ValueError('theta in(0,1)')
    if type(divisors) not in (tuple,list) or not 2<=len(divisors)<=8:raise ValueError('two..eight scales')
    if list(divisors)!=sorted(set(divisors)):raise ValueError('distinct increasing divisors')
    for d in divisors:A._integer(d,m,True)
    if type(cutoff_exponents) not in (tuple,list) or not 1<=len(cutoff_exponents)<=16:raise ValueError('bounded cutoff menu')
    alphas=[_q(x,m) for x in cutoff_exponents]
    if any(a<0 for a in alphas):raise ValueError('nonnegative cutoff exponents')
    result=[]
    for arity in range(2,min(3,len(divisors))+1):
        for chosen in combinations(divisors,arity):
            m.charge(32*arity**3)
            null=S.Matrix([[1]*arity]).nullspace()
            for vector in null:
                lambdas=[Q(str(x)) for x in vector]
                for alpha in alphas:
                    # Two systematic assignments: common cutoff, or distinct local scales.
                    for mode in ('common','scaled'):
                        terms=[];drifts=[]
                        for d,lam in zip(chosen,lambdas):
                            m.charge(8)
                            if not lam:continue
                            cutoff=dict(op='floor_power',scale_divisor=1 if mode=='common' else d,exponent=str(alpha))
                            terms.append(dict(divisor=d,coefficient=dict(rational=str(lam),positive_base=d,exponent=str(theta)),cutoff=cutoff))
                            drifts.append(dict(coefficient=str(lam),
                                from_cutoff=dict(op='floor_power',scale_divisor=1 if mode=='common' else chosen[0],exponent=str(alpha)),
                                to_cutoff=cutoff,weight_exponent=str(-theta),orientation='M(to)-M(from)'))
                        result.append(dict(terms=terms,main_nullspace=list(map(str,lambdas)),
                            cutoff_base='block X, independent of prefix argument x',
                            common_analytic_value_cancelled=True,
                            complete_moment_drift=drifts,
                            drift_sign='plus main_multiplier*x^theta/theta times sumlambda*(M(to)-M(from)) in centered-tail filter',
                            main_multiplier=factor['main_multiplier'],
                            uncovered_filter=dict(channel_indices=factor['uncovered'][:],
                                                  expression='sum_j coefficient_j*uncovered_prefix(x/divisor_j)'),
                            unit_and_uncovered_terms_retained=True,
                            inverse_recovery='OPEN; pole cancellation alone is not a bounded inverse',
                            status='exact_filtered_identity_only'))
    return result


def compile_bridges(source,cutoff_exponents=('0','1/6','1/3'),scale_divisors=(1,2,3),parameter_domain=None,meter=None,kernel_v_values=()):
    m=Meter() if meter is None else meter
    factors=factor_candidates(source,m,kernel_v_values);domain=_domain(parameter_domain,m)
    if type(cutoff_exponents) not in (tuple,list) or not 1<=len(cutoff_exponents)<=16:raise ValueError('bounded cutoffs')
    alphas=[_q(a,m) for a in cutoff_exponents]
    if len(set(alphas))!=len(alphas) or any(a<0 for a in alphas):raise ValueError('distinct nonnegative cutoffs')
    programs=[]
    for i,factor in enumerate(factors):
        for alpha in alphas:
            m.charge(24)
            programs.append(dict(factor=i,alpha=str(alpha),
                identity='full_prefix=uncovered_prefix+finite_error_head+complete_centered_tail+main_multiplier*analytic_value*x^theta/theta',
                finite_error_head=dict(d_domain='1<=d<=U, including d>x',kernel='P_kernel(x/d)-main_multiplier*(x/d)^theta/theta'),
                finite_moment=dict(d_domain='1<=d<=U',weight='d^(-theta)'),
                analytic_value=dict(kind='meromorphic_source_value',argument=factor['theta'],ordinary_series_convergence_asserted=False),
                defect='analytic_value-finite_moment',
                complete_centered_tail='sum_(U<d<=floor(x)) g(d)P_kernel(x/d)-main_multiplier*defect*x^theta/theta',
                main_multiplier=factor['main_multiplier'],
                source_unit_retained=True,normalization_zero_assumed=False,
                costs=_price(source,factor,alpha,domain,m)))
    templates=[dict(factor=i,templates=scale_templates(f,scale_divisors,cutoff_exponents,m)) for i,f in enumerate(factors)]
    m.live(128+sum(48+16*len(c['atoms']) for c in source['channels'])+256*(len(programs)+sum(len(t['templates']) for t in templates)))
    return dict(schema='finite-normalization-backend-040-v1',source_binding=deepcopy(source),
                factors=factors,programs=programs,scale_templates=templates,
                kernel_v_requests=[str(_q(v,m)) for v in kernel_v_values],
                rejected_requested_pairs=[dict(kernel_r=f['kernel_r'],kernel_v=str(_q(v,m)),reason='v<=r:positive shifted-kernel provider inapplicable')
                    for f in factors if f['kernel_v'] is None for v in kernel_v_values if Q(v)<=Q(f['kernel_r'])],
                actual_scalar_normalization_required=True,whole_bound_proved=False,RH_proved=False,
                observations_used=False,metadata=m.counts())


def _real(q):return arb(q.numerator)/q.denominator


def _power(q,exponent,m):
    m.charge(64)
    return (_real(q).log()*_real(exponent)).exp()


def kernel_error(theta_text,x,meter=None):
    """Tiny numerical kernel helper, no source coefficients or import-time work."""
    m=Meter() if meter is None else meter
    theta=_q(theta_text,m);x=_q(x,m) if type(x) is str else Q(x) if type(x) is int else None
    if x is None or x<=0 or not 0<theta<1:raise ValueError('positive exact rational x,theta in(0,1)')
    count=x.numerator//x.denominator;m.charge(count+1)
    return sum((_power(Q(k),theta-1,m) for k in range(1,count+1)),arb(0))-_power(x,theta,m)/_real(theta)


def finite_bridge(coefficients,x,U,theta_text,analytic_value,meter=None):
    """Synthetic/test helper for the complete finite identity, at arbitrary Gθ.

    All needed coefficients through max(U,floor(x)) are supplied. The Gθ
    argument is a named analytic scalar, not a computed infinite moment.
    """
    m=Meter() if meter is None else meter
    theta=_q(theta_text,m);xq=_q(x,m);A._integer(U,m)
    if U<0 or xq<=0 or not 0<theta<1 or type(coefficients) not in (tuple,list):raise ValueError('bridge domain')
    N=xq.numerator//xq.denominator
    m.charge(len(coefficients))
    if len(coefficients)<=max(U,N) or any(not isinstance(c,arb) or not c.is_finite() for c in coefficients):raise ValueError('complete finite Arb coefficients')
    if not coefficients[0].is_zero() or not isinstance(analytic_value,arb) or not analytic_value.is_finite():raise ValueError('zero index and finite analytic scalar')
    moment=sum((coefficients[d]*_power(Q(d),-theta,m) for d in range(1,U+1)),arb(0))
    head=sum((coefficients[d]*kernel_error(theta_text,str(xq/d),m) for d in range(1,U+1)),arb(0))
    raw=arb(0)
    for d in range(U+1,N+1):
        raw+=coefficients[d]*(kernel_error(theta_text,str(xq/d),m)+_power(xq/d,theta,m)/_real(theta))
        m.charge(4)
    main=_power(xq,theta,m)/_real(theta);defect=analytic_value-moment
    centered=raw-defect*main
    reconstructed=head+centered+analytic_value*main
    return dict(finite_moment=moment,analytic_defect=defect,finite_error_head=head,
                complete_raw_tail=raw,complete_centered_tail=centered,reconstructed=reconstructed,
                analytic_main=analytic_value*main,ordinary_series_convergence_asserted=False)
