"""Actual ordinary-zero preservation, without demanding zero-free kernels."""
from fractions import Fraction as Q
from math import comb
import flint
from mellin_kernel_grammar import real
from lattice_synthesis_grammar import polynomial,relative,complex_relative


def newton_matrix(P):
    n=len(P)-1
    if not n:return []
    P=[c/P[-1] for c in P];s=[Q(n)]
    for k in range(1,2*n-1):
        if k<=n:s.append(-sum((P[n-j]*s[k-j] for j in range(1,k)),Q(0))-k*P[n-k])
        else:s.append(-sum((P[n-j]*s[k-j] for j in range(1,n+1)),Q(0)))
    return [[s[i+j] for j in range(n)] for i in range(n)]


def rational_positive_factorization(H):
    n=len(H);M=[row.copy() for row in H];indices=list(range(n));terms=[]
    while M:
        if any(M[i][i]<0 for i in range(len(M))):return {'positive_semidefinite':False,'terms':[]}
        available=[i for i in range(len(M)) if M[i][i]>0]
        if not available:return {'positive_semidefinite':not any(v for row in M for v in row),'terms':terms}
        first=available[0];order=[first]+[i for i in range(len(M)) if i!=first];M=[[M[i][j] for j in order] for i in order];indices=[indices[i] for i in order]
        pivot=M[0][0];row=[Q(0)]*n;row[indices[0]]=1
        for j in range(1,len(M)):row[indices[j]]=M[0][j]/pivot
        terms.append({'pivot':str(pivot),'covector':list(map(str,row))})
        M=[[M[i][j]-M[i][0]*M[0][j]/pivot for j in range(1,len(M))] for i in range(1,len(M))];indices=indices[1:]
    return {'positive_semidefinite':True,'terms':terms}


def squarefree_polynomial(P):
    f=flint.fmpq_poly([flint.fmpq(c.numerator,c.denominator) for c in P]);g=f.gcd(f.derivative());q,rem=divmod(f,g)
    if rem:raise ArithmeticError('Exact squarefree polynomial division failed')
    return [Q(str(c)) for c in q]


def root_certificate(c,params,precision=512):
    K,ell,r=map(Q,params);P=polynomial(c);H=newton_matrix(P);factor=rational_positive_factorization(H)
    base={'Mellin_polynomial':list(map(str,P)),'ordinary_zero_domain':'1/2<Re(rho)<1, Im(rho)!=0; all heights and multiplicities',
        'native_certificate_precision':precision,
        'ordinary_mapping':'rho=r*(K-ell*v)','counterexample_to_growth_bound':False,
        'kernel_zero_free_halfplane_required':False,'sampled_zeta_zero_grid_used':False,
        'Hermite_matrix':[[str(v) for v in row] for row in H],'Hermite_factorization':factor}
    if factor['positive_semidefinite']:
        return dict(base,kind='exact_all_real_polynomial_roots',all_right_half_ordinary_zeros_preserved=True,
            reason='real operator roots cannot coincide with nonreal ordinary zeta zeros')
    if len(P)==3:
        discriminant=P[1]**2-4*P[0]*P[2];beta=r*(K+ell*P[1]/(2*P[2]))
        if discriminant<0 and (beta<=Q(1,2) or beta>=1):
            return dict(base,kind='exact_conjugate_roots_outside_ordinary_strip',all_right_half_ordinary_zeros_preserved=True,
                exact_mapped_real_part=str(beta),exact_discriminant=str(discriminant))
    flint.ctx.prec=precision;S=squarefree_polynomial(P);poly=flint.acb_poly([flint.acb(real(v)) for v in S])
    try:roots=poly.roots(tol=real(Q(1,2**230)),maxprec=2048)
    except (ValueError,ArithmeticError):return dict(base,kind='missing_native_root_isolation',all_right_half_ordinary_zeros_preserved=False)
    boxes=[]
    for root in roots:
        cr=Q(root.real.mid().str(85,radius=False));ci=Q(root.imag.mid().str(85,radius=False));radius=(1+abs(cr)+abs(ci))/2**150
        center=flint.acb(real(cr),real(ci));R=real(radius);tay=[]
        for j in range(len(S)):tay.append(sum((real(a)*comb(k,j)*center**(k-j) for k,a in enumerate(S) if k>=j),flint.acb(0)))
        lower=tay[1].abs_lower()*R;upper=tay[0].abs_upper()+sum((tay[j].abs_upper()*R**j for j in range(2,len(S))),flint.arb(0))
        if not lower>upper:return dict(base,kind='missing_native_Rouche_disk',all_right_half_ordinary_zeros_preserved=False)
        rectangle=flint.acb(flint.arb(real(cr),R),flint.arb(real(ci),R));rho=real(r)*(real(K)-real(ell)*rectangle)
        outside=rho.real.upper()<=real(Q(1,2)) or rho.real.lower()>=1
        zeta=rho.zeta() if not outside else None;safe=outside or zeta.abs_lower()>0
        boxes.append({'center':[str(cr),str(ci)],'radius':str(radius),'Rouche_lower_ball':relative(lower),
            'Rouche_upper_ball':relative(upper),'mapped_ordinary_root_box':complex_relative(rho),
            'outside_ordinary_strip':bool(outside),'native_zeta_box':complex_relative(zeta) if zeta is not None else None,
            'native_zeta_lower_ball':relative(zeta.abs_lower()) if zeta is not None else None,'ordinary_zero_excluded':bool(safe)})
    disjoint=True
    for i,B in enumerate(boxes):
        for C in boxes[i+1:]:
            delta=flint.acb(real(Q(B['center'][0])-Q(C['center'][0])),real(Q(B['center'][1])-Q(C['center'][1])))
            disjoint &= bool(delta.abs_lower()>real(Q(B['radius'])+Q(C['radius'])))
    complete=len(boxes)==len(S)-1 and disjoint;safe=complete and all(v['ordinary_zero_excluded'] for v in boxes)
    return dict(base,kind='certified_finite_operator_root_exclusion' if safe else 'missing_actual_zeta_exclusion_at_operator_roots',
        all_right_half_ordinary_zeros_preserved=safe,squarefree_polynomial=list(map(str,S)),
        root_disks=boxes,disks_disjoint=disjoint,all_polynomial_roots_covered=complete,
        finite_operator_roots_are_not_a_sample_of_zeta_zeros=True)


def exceptional_real_parts(r,maximum_steps=128):
    r=Q(r)
    if r<=1:raise ValueError('Strictly expanding positive arithmetic dilation required')
    power=r;out=[]
    for j in range(1,maximum_steps+1):
        if power>=2:return {'kind':'complete_rational_exception_set','r':str(r),'real_parts':out,'complete':True,
            'exception_form':'r^j/2, j>=1 and r^j<2','all_heights_covered':True}
        out.append(str(power/2));power*=r
    return {'kind':'missing_exception_set_resource','r':str(r),'real_parts':out,'complete':False,'all_heights_covered':False}


def complementary_certificate(programs):
    if not programs or any(not p['zero_bridge']['all_right_half_ordinary_zeros_preserved'] or not p['zero_exceptions']['complete'] for p in programs):
        return {'kind':'missing_complete_zero_constraints','RH_sufficient_if_every_member_uniform':False,
            'counterexample_to_growth_bound':False}
    sets=[set(map(Q,p['zero_exceptions']['real_parts'])) for p in programs];remaining=set.intersection(*sets)
    return {'kind':'exact_complementary_zero_constraints','remaining_real_parts':list(map(str,sorted(remaining))),
        'RH_sufficient_if_every_member_uniform':not remaining,'member_ids':[p['id'] for p in programs],
        'all_heights_and_multiplicities_covered':True,'sampled_zeta_zero_grid_used':False,
        'uniform_signed_premises_proved':False,'counterexample_to_growth_bound':False}


def reflection_path(beta,height,r,steps=20):
    beta,height,r=map(Q,(beta,height,r))
    if r<=1 or not Q(1,2)<beta<1 or not height:raise ValueError('Hypothetical right-half ordinary zero and r>1 required')
    fixed=r/(r+1);out=[]
    for j in range(steps):
        divided=beta/r;branch='critical_line_mask' if divided==Q(1,2) else ('direct_division' if divided>Q(1,2) else 'reflection')
        out.append({'real_part':str(beta),'height':str(height),'distance_from_fixed_point':str(beta-fixed),'branch':branch})
        if branch=='critical_line_mask':break
        beta=divided if branch=='direct_division' else 1-divided;height/=r
    return out
