#!/usr/bin/env python3
"""Independent complete lattice, contour, sign-barrier and zero-chain audit.

No producer mathematical module is imported. Discovery replay executes in a
different process; exact Sturm counting replaces the producer's Hermite test.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import ceil,comb,factorial,log2,log,exp
from pathlib import Path
import subprocess,sys,tempfile
import flint
from stable_scale_report import BASE,read,sha,digest
from check_mellin_kernels import a,powq,put,mu_by_factors,tight_overlap,pochhammer


def overlap(txt,v):tight_overlap(txt,v)
def cp(saved,v):overlap(saved['real'],v.real);overlap(saved['imag'],v.imag)


def iroot(n,k):
    if not n:return 0
    x=1<<((n.bit_length()+k-1)//k)
    while True:
        y=((k-1)*x+n//x**(k-1))//k
        if y>=x:break
        x=y
    while x**k>n:x-=1
    while (x+1)**k<=n:x+=1
    return x


def independent_table(table,points,counts):
    K,ell,r=map(Q,table['parameters']);R=Q(table['rate']);p,q=r.numerator,r.denominator;N0=table['cutoff'];N=N0+17;L0=table['Taylor_terms'];L=L0+8;mmax=table['maximum_moment']
    flint.ctx.prec=max(table['precision']+160,ceil(float(K+ell*(L+mmax))*log2(N))+320)
    D=iroot(N**q,p);mu=mu_by_factors(D);oldmu=mu_by_factors(iroot(N0**q,p));assert table['inverse_prefix']==oldmu
    weights=[];sums={model:[flint.arb(0) for _ in range(L+mmax)] for model in ['inverse','unit']};adjust={model:[flint.arb(0) for _ in range(L+mmax)] for model in sums};oldpairs=0
    for d in range(D,0,-1):
        M=iroot(N**q//d**p,q)
        for j in range(M,0,-1):
            u=a(j)*((a(r)*a(d).log()).exp());step=powq(u,-ell);base=powq(u,-K);new=j**q*d**p>N0**q
            oldpairs+=not new;weights.append((base,step,mu[d]));v=base
            for h in range(L+mmax):
                for model,b in [('inverse',mu[d]),('unit',1)]:
                    sums[model][h]+=b*v
                    if new:adjust[model][h]+=b*v
                v*=step
    assert oldpairs==table['prefix_pairs'] and table['all_infinite_arithmetic_positions_included'] and not table['prime_oracle_used_by_producer'] and table['no_RH_input']
    assert table['fractional_r_positions_are_generalized_signed_measures']==(r.denominator!=1)
    assert table['model_profiles']=={'inverse':'zeta(s)/zeta(r*s)','unit':'zeta(s)*zeta(r*s)'}
    tails={model:[] for model in sums};density=a(r).zeta()
    for model in sums:
        for h,v in enumerate(sums[model]):
            w=K+ell*h;moment=a(w).zeta()/(a(r*w).zeta()) if model=='inverse' else a(w).zeta()*a(r*w).zeta()
            tail=moment-v;assert abs(tail)<=density*a(w)*powq(a(N),1-w)/a(w-1);tails[model].append(tail)
            if h<len(table['tail_moment_balls'][model]):overlap(table['tail_moment_balls'][model][h],tail+adjust[model][h]);counts['independent_tail_moments']+=1
    values={model:{} for model in sums}
    for X in map(Q,points):
        XK=powq(a(X),K);c=a(R)*powq(a(X),ell)
        for model in sums:
            for m in range(mmax+1):
                prefix=sum((base*(c*step)**m*(-c*step).exp()*(mu0 if model=='inverse' else 1) for base,step,mu0 in weights),flint.arb(0))
                tail=flint.arb(0)
                for h in range(L-1,-1,-1):tail=-c*tail+tails[model][m+h]/factorial(h)
                w=K+ell*(m+L);error=c**(m+L)*density*a(w)*powq(a(N),1-w)/(factorial(L)*a(w-1));v=XK*(prefix+c**m*tail+flint.arb(0,error));key=f'{m}:{X}'
                overlap(table['values'][model][key],v);values[model][key]=v;counts['independent_complete_atoms']+=1
    for row in table['tail_bounds']:
        X,m=Q(row['scale']),row['moment'];w=K+ell*(m+L0);error=powq(a(X),K)*(a(R)*powq(a(X),ell))**(m+L0)*density*a(w)*powq(a(N0),1-w)/(factorial(L0)*a(w-1))
        overlap(row['error_ball'],error);counts['independent_Taylor_bounds']+=1
    return values


def polynomial(c):
    out=[Q(0)]*(c['maximum_moment']+1)
    for m,b in c['terms']:
        for (j,h),v in pochhammer(m).items():out[j]+=Q(b)*v
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def peval(P,v):return sum((a(c)*v**j for j,c in enumerate(P)),flint.acb(0))
def qeval(P,v):return sum((c*v**j for j,c in enumerate(P)),Q(0))
def transform(P,K,ell,R,s):
    v=(a(K)-s)/a(ell);return v.gamma()*peval(P,v)*(-v*a(R).log()).exp()/a(ell)


def residues(p,counts):
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);c=p['shape'];R=Q(c['rate']);P=polynomial(c);saved=p['residues'];alpha=(K-1)/ell;beta=(K-1/r)/ell
    assert list(map(Q,saved['Mellin_polynomial']))==P and Q(saved['integral_polynomial_value'])==qeval(P,alpha) and Q(saved['secondary_polynomial_value'])==qeval(P,beta)
    I=powq(a(R),-alpha)*a(alpha).gamma()*a(qeval(P,alpha))/a(ell);W=powq(a(R),-beta)*a(beta).gamma()*a(qeval(P,beta))/a(ell);A=I/a(r).zeta();U=I*a(r).zeta();B=a(1/r).zeta()*W/a(r)
    for key,v in [('continuous_integral_ball',I),('inverse_main_ball',A),('unit_main_ball',U),('unit_secondary_ball',B)]:overlap(saved[key],v)
    assert saved['both_reference_residues_vanish']==(qeval(P,alpha)==qeval(P,beta)==0) and not saved['inverse_secondary_term_claimed'];counts['independent_exact_residues']+=1
    return I,A,U,B


def observations(p,values,points,saved,res,counts):
    K,ell,r=map(Q,p['parameters']);I,A,U,B=res;out={}
    for X in map(Q,points):
        raws={model:sum((a(c)*values[model][f'{m}:{X}'] for m,c in p['shape']['terms']),flint.arb(0)) for model in ['inverse','unit']}
        row={'inverse_raw_ball':raws['inverse'],'inverse_centered_ball':raws['inverse']-A*a(X),
            'unit_raw_ball':raws['unit'],'unit_two_residue_residual_ball':raws['unit']-U*a(X)-B*powq(a(X),1/r)}
        for k,v in row.items():overlap(saved[str(X)][k],v);counts['independent_full_observations']+=1
        out[str(X)]=row
    return out


def trim(P):
    while len(P)>1 and P[-1]==0:P.pop()
    return P
def derivative(P):return trim([j*P[j] for j in range(1,len(P))] or [Q(0)])
def divide(P,S):
    P=P.copy();out=[Q(0)]*max(1,len(P)-len(S)+1)
    while any(P) and len(P)>=len(S):
        k=len(P)-len(S);v=P[-1]/S[-1];out[k]+=v
        for j,c in enumerate(S):P[k+j]-=v*c
        trim(P)
    return trim(out),trim(P)
def gcd(P,S):
    while any(S):P,S=S,divide(P,S)[1]
    return [x/P[-1] for x in P]
def squarefree(P):return divide(P,gcd(P,derivative(P)))[0]
def real_root_count(P):
    P=squarefree(P)
    if len(P)==1:return 0,0
    sequence=[P,derivative(P)]
    while any(sequence[-1]):
        rem=divide(sequence[-2],sequence[-1])[1]
        if not any(rem):break
        sequence.append([-x for x in rem])
    def variations(side):
        signs=[(1 if v[-1]>0 else -1)*(side**(len(v)-1)) for v in sequence]
        return sum(x!=y for x,y in zip(signs,signs[1:]))
    return variations(-1)-variations(1),len(P)-1


def companion_hermite(P):
    n=len(P)-1
    if not n:return []
    C=[[Q(0)]*n for _ in range(n)]
    for i in range(1,n):C[i][i-1]=1
    for i in range(n):C[i][-1]=-P[i]/P[-1]
    M=[[Q(int(i==j)) for j in range(n)] for i in range(n)];traces=[]
    for k in range(2*n-1):
        traces.append(sum(M[i][i] for i in range(n)));M=[[sum((M[i][h]*C[h][j] for h in range(n)),Q(0)) for j in range(n)] for i in range(n)]
    return [[traces[i+j] for j in range(n)] for i in range(n)]


def root_check(p,counts):
    flint.ctx.prec=768;P=polynomial(p['shape']);cert=p['zero_bridge'];K,ell,r=map(Q,p['parameters']);H=companion_hermite(P);roots,degree=real_root_count(P)
    assert list(map(Q,cert['Mellin_polynomial']))==P and [[Q(v) for v in row] for row in cert['Hermite_matrix']]==H
    factor=cert['Hermite_factorization'];assert factor['positive_semidefinite']==(roots==degree)
    if factor['positive_semidefinite']:
        terms=[(Q(t['pivot']),list(map(Q,t['covector']))) for t in factor['terms']];assert all(b>0 for b,v in terms)
        assert H==[[sum((b*v[i]*v[j] for b,v in terms),Q(0)) for j in range(len(H))] for i in range(len(H))]
        assert cert['kind']=='exact_all_real_polynomial_roots' and cert['all_right_half_ordinary_zeros_preserved'];counts['independent_Sturm_real_root_certificates']+=1
    elif cert['kind']=='exact_conjugate_roots_outside_ordinary_strip':
        assert len(P)==3 and P[1]**2-4*P[0]*P[2]<0;beta=r*(K+ell*P[1]/(2*P[2]));assert beta<=Q(1,2) or beta>=1
        assert Q(cert['exact_mapped_real_part'])==beta and cert['all_right_half_ordinary_zeros_preserved'];counts['independent_exact_complex_strip_certificates']+=1
    elif 'root_disks' in cert:
        S=squarefree(P);assert list(map(Q,cert['squarefree_polynomial']))==S;boxes=cert['root_disks'];all_safe=True
        for box in boxes:
            center=flint.acb(a(box['center'][0]),a(box['center'][1]));h=a(box['radius']);coeff=[]
            for j in range(len(S)):coeff.append(sum((a(c)*comb(k,j)*center**(k-j) for k,c in enumerate(S) if k>=j),flint.acb(0)))
            lo=coeff[1].abs_lower()*h;hi=coeff[0].abs_upper()+sum((z.abs_upper()*h**j for j,z in enumerate(coeff) if j>=2),flint.arb(0));assert lo>hi
            # abs_lower/abs_upper are algorithmic endpoints, not exact
            # mathematical quantities that must overlap at a new precision.
            # Check the recorded endpoints as conservative inequalities and
            # independently prove the complete Rouché dominance again.
            recorded_lo=flint.arb(box['Rouche_lower_ball']);recorded_hi=flint.arb(box['Rouche_upper_ball'])
            norm_lo=abs(coeff[1])*h;norm_hi=abs(coeff[0])+sum((abs(coeff[j])*h**j for j in range(2,len(S))),flint.arb(0))
            assert recorded_lo.lower()<=norm_lo.lower() and recorded_hi.upper()>=norm_hi.upper()
            assert recorded_lo.lower()>recorded_hi.upper()
            rectangle=flint.acb(flint.arb(a(box['center'][0]),h),flint.arb(a(box['center'][1]),h));rho=a(r)*(a(K)-a(ell)*rectangle);cp(box['mapped_ordinary_root_box'],rho)
            outside=rho.real.upper()<=a(Q(1,2)) or rho.real.lower()>=1;assert box['outside_ordinary_strip']==outside
            safe=bool(outside)
            if not outside:
                zeta=rho.zeta();cp(box['native_zeta_box'],zeta);safe=bool(zeta.abs_lower()>0)
                # The recorded lower endpoint belongs to its declared native
                # precision. Check that metadata at that precision as well as
                # proving zero exclusion with the independent, sharper box.
                flint.ctx.prec=cert.get('native_certificate_precision',512)
                h0=a(box['radius']);box0=flint.acb(flint.arb(a(box['center'][0]),h0),flint.arb(a(box['center'][1]),h0))
                rho0=a(r)*(a(K)-a(ell)*box0);zeta0=rho0.zeta();overlap(box['native_zeta_lower_ball'],zeta0.abs_lower())
                assert zeta0.abs_lower()>0;flint.ctx.prec=768;counts['independent_native_operator_root_zeta_exclusions']+=1
            assert box['ordinary_zero_excluded']==safe;all_safe &=safe
        disjoint=all(flint.acb(a(Q(b['center'][0])-Q(c['center'][0])),a(Q(b['center'][1])-Q(c['center'][1]))).abs_lower()>a(Q(b['radius'])+Q(c['radius'])) for b,c in __import__('itertools').combinations(boxes,2))
        complete=len(boxes)==len(S)-1 and disjoint;assert cert['all_polynomial_roots_covered']==complete and cert['disks_disjoint']==disjoint
        assert cert['all_right_half_ordinary_zeros_preserved']==(complete and all_safe)
    else:assert not cert['all_right_half_ordinary_zeros_preserved'] and cert['kind'].startswith('missing_')
    assert not cert['kernel_zero_free_halfplane_required'] and not cert['sampled_zeta_zero_grid_used'] and not cert['counterexample_to_growth_bound'];counts['independent_all_height_operator_bridges']+=1


def exponent_set(r):
    r=Q(r);out=[];v=r
    for j in range(128):
        if v>=2:return out,True
        out.append(v/2);v*=r
    return out,False


def zero_constraints(p,counts):
    r=Q(p['parameters'][2]);parts,complete=exponent_set(r);saved=p['zero_exceptions'];assert list(map(Q,saved['real_parts']))==parts and saved['complete']==complete
    fixed=r/(r+1);assert Q(1,2)<fixed<1 and a(fixed).zeta()<0
    if r<2:assert fixed<r/2 and 1-Q(1,2)/r<r/2
    for beta0 in [Q(5,8),Q(3,4),Q(7,8)]:
        beta=beta0;height=Q(17)
        for j in range(48):
            if beta/r==Q(1,2):assert beta0 in parts;break
            beta=beta/r if beta/r>Q(1,2) else 1-beta/r;height/=r;assert Q(1,2)<beta<1 and height==Q(17)/r**(j+1)
    counts['independent_fractional_zero_constraints']+=1


def global_check(p,res,counts):
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);R=Q(p['shape']['rate']);I,A,U,B=res;terms=p['shape']['terms'];weak=p['weak_actual'];V=flint.arb(0);J=flint.arb(0);local=[]
    def atom(m):
        w=K+ell*m;integral=powq(a(R),(1-K)/ell)*a((K-1)/ell+m).gamma()/a(ell)
        peak=powq(a(R),-K/ell)*powq(a(w/ell),w/ell)*(-a(w/ell)).exp()
        return integral+2*peak+a(R**m)*a(w).zeta()
    for m,b in terms:
        b=abs(Q(b));w=K+ell*m;beta=(K-1/r)/ell+m
        V+=a(b)*powq(a(R),(1/r-K)/ell)*a(beta).gamma()*(a(w)+a(ell*beta))/a(ell)
        J+=a(b)*(a(w)*atom(m)+a(ell)*atom(m+1));local.append((w,a(b*R**m)*a(w).zeta()*a(r*w).zeta()))
    C=a(Q(1,2))+powq(a(2),r-1)/a(r-1);overlap(weak['constant_ball'],C*V);overlap(weak['count_constant_ball'],C);overlap(weak['variation_ball'],V)
    assert Q(weak['growth_exponent'])==1/r and r*Q(weak['growth_exponent'])==1 and not weak['RH_strength'] and weak['all_real_scales'] and weak['integer_r_free_indicator']==(r.denominator==1)
    gc=p['global_constants'];J=a(r).zeta()*J+abs(A);overlap(gc['inverse_unit_increment_constant_ball'],J);assert gc['small_dilated_scale_majorant_included']
    for old,(w,c) in zip(gc['local_absolute_lattice_terms'],local):assert Q(old['power'])==w;overlap(old['coefficient_ball'],c)
    overlap(gc['source_measure_absolute_density_cost_ball'],a(r).zeta());counts['independent_weak_and_unit_global_certificates']+=1
    return C*V,J,local


def barrier_check(p,res,counts):
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);R=Q(p['shape']['rate']);terms=p['shape']['terms'];P=polynomial(p['shape']);I=res[0];saved=p['sign_loss_barrier']
    if saved['status']!='certified_absolute_rewrite_barrier':assert not saved['counterexample_to_actual_bound'];return
    Y=Q(saved['small_scale_cutoff']);w=Q(saved['local_power']);zero=qeval(P,(K-1)/ell)==0
    if zero:
        m0,c0=terms[0];assert w==K+ell*m0;lead=a(abs(Q(c0))*R**m0)*a(w).zeta();remainder=a(abs(Q(c0))*R**(m0+1))*a(w+ell).zeta()*powq(a(Y),ell)
        remainder+=sum((a(abs(Q(c))*R**m)*a(K+ell*m).zeta()*powq(a(Y),K+ell*m-w) for m,c in terms if m>m0),flint.arb(0))
    else:
        assert w==1;lead=abs(I);remainder=sum((a(abs(Q(c))*R**m)*a(K+ell*m).zeta()*powq(a(Y),K+ell*m-1) for m,c in terms),flint.arb(0))
    assert 0<Y<=1 and lead>0 and remainder<=lead/2
    b=lead*powq(a(Y),w-1/r)/(powq(a(2),r*w)*a(r*w-1));density=1/a(2).zeta();M0=saved['squarefree_interval_threshold'];assert density*a(M0)/2>=a(Q(5,2))*((2*a(M0)).sqrt()+a(M0).sqrt())
    support=density*lead*powq(a(Y),w-1/r)/powq(a(2),2*r*w+1)
    for key,v in [('leading_coefficient_ball',lead),('remainder_coefficient_ball',remainder),('lower_constant_ball',b),('actual_support_lower_constant_ball',support),('squarefree_density_ball',density),('actual_support_onset_ball',a(Y)*powq(a(M0),r))]:overlap(saved[key],v)
    assert b>0 and support>0 and Q(saved['barrier_growth_exponent'])==1/r and not saved['counterexample_to_actual_bound'] and saved['actual_signed_cancellation_can_be_stronger'];counts['independent_actual_support_sign_loss_barriers']+=1


def reference_check(p,spec,counts):
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);R=Q(p['shape']['rate']);pi=flint.arb.pi()
    for order,cert in p['reference_decay_certificates'].items():
        a0=Q(order);alpha=(K+a0)/ell;D=[Q(0)]*(p['shape']['maximum_moment']+1)
        for m,c in p['shape']['terms']:
            for (k,h),b in pochhammer(m).items():
                for j in range(k+1):D[j]+=abs(Q(c))*b*comb(k,j)*alpha**(k-j)/ell**j
        values=[]
        for row in cert['ray_certificates']:
            ray,f=Q(row['kernel_ray_pi_fraction']),Q(row['decay_allocation_fraction']);delta_pi=ray*f/((1+r)*max(ell,Q(1)));decay_pi=ray/ell-(1+r)*delta_pi
            assert decay_pi>0 and Q(row['zeta_complement_angle_pi_fraction'])==delta_pi and Q(row['net_decay_pi_fraction'])==decay_pi
            delta=a(delta_pi)*pi;kappa=a(decay_pi)*pi;kernel=a(alpha).gamma()*powq((a(ray)*pi).cos(),-alpha)*powq(a(R),-alpha)/a(ell)
            zetas=[powq(a(2),-s*a0)*powq(pi,-s*a0-1)*a(1+s*a0).gamma()*powq(delta.sin(),-1-s*a0)*a(1+s*a0).zeta() for s in [Q(1),r]]
            integral=sum((a(c)*a(j+1).gamma()/kappa**(j+1) for j,c in enumerate(D)),flint.arb(0));C=kernel*zetas[0]*zetas[1]*integral/pi
            assert list(map(Q,row['height_polynomial_coefficients']))==D
            for key,v in [('kernel_bound_prefactor_ball',kernel),('height_integral_bound_ball',integral),('global_constant_ball',C)]:overlap(row[key],v)
            for txt,v in zip(row['zeta_bound_prefactor_balls'],zetas):overlap(txt,v)
            assert abs(row['log_constant']-float(C.upper().log()))<1e-10;values.append((row,C))
            # These witnesses check coding of the global analytic inequalities;
            # the whole-height scope comes from the rotated-integral proof.
            for t in [Q(0),Q(1,3),Q(17)]:
                gamma=flint.acb(a(alpha),a(t/ell)).gamma().abs_upper();bound=kernel*a(ell)*powq(a(R),alpha)*(-a(ray)*pi*a(t)/a(ell)).exp();assert gamma<=bound
                for slope,pref in zip([Q(1),r],zetas):assert flint.acb(-a(slope*a0),a(slope*t)).zeta().abs_upper()<=pref*(delta*a(slope*t)).exp()
            counts['independent_whole_height_contour_ray_certificates']+=1
        best=min(values,key=lambda v:v[0]['log_constant']);assert cert['best_ray']==best[0];overlap(cert['constant_ball'],best[1]);assert cert['arithmetic_model']=='unit' and cert['all_real_scales'] and not cert['RH_consequence'] and not cert['actual_inverse_estimate_proved']
        assert Q(cert['growth_exponent'])==-a0 and cert['subtract_both_known_residues'];counts['independent_unit_negative_power_global_estimates']+=1


@lru_cache(maxsize=None)
def envelope(limit,margin,nu,d,q,X):return powq(a(Q(X)),Q(limit))*((a(margin)/powq(a(q),Q(nu)))*a(Q(X)).log()).exp()*powq((flint.arb.const_e()+a(Q(X))).log(),Q(d))
def env(f,q,X):return envelope(f['limit'],f['margin'],f['approach_power'],f['log_power'],q,str(X))


def constants_check(rows,f,qs,Cs,spec,counts):
    D=int(spec['constant_rule']['upward_denominator']);margin=a(spec['constant_rule']['training_margin'])
    for q in qs:
        vals=[abs(row['inverse_centered_ball'])/env(f,q,X) for X,row in rows.items()];top=max(vals,key=lambda v:float(v.upper()));expect=margin*top;got=a(Cs[str(q)])
        uncertainty=max((v.rad() for v in vals),key=float);assert abs(got-expect)<=4*margin*uncertainty+a(Q(4,D)) and got>0;counts['independent_training_only_constants']+=1


def comparison_check(rows,f,Cs,qs,old,counts):
    failures=[];unresolved=[];worst=0
    for q in qs:
        for X,row in rows.items():
            V=abs(row['inverse_centered_ball']);B=a(Cs[str(q)])*env(f,q,X)
            if not V<=B:(failures if V>B else unresolved).append(f'{q}:{X}')
            worst=max(worst,float((V/B).upper()));counts['independent_finite_inequality_comparisons']+=1
    assert old['failures']==failures and old['unresolved']==unresolved and old['finite_points_passed']==(not failures and not unresolved)
    assert abs(old['maximum_ratio']-worst)<=1e-10*max(1,worst) and not old['uniform_signed_premise_proved']


def cost_check(p,c,Cs,qs,old,res,global_data,counts):
    if Q(c['frontier']['ordinary_limit'])!=Q(1,2):assert old['best_log_cost'] is None;return
    if not p['zero_bridge']['all_right_half_ordinary_zeros_preserved']:assert old['status']=='missing_actual_ordinary_zero_bridge';return
    flint.ctx.prec=768;K,ell,r=map(Q,p['parameters']);sigma,t=map(Q,old.get('ordinary_zeta_query',['5/8','16']));s=flint.acb(a(sigma/r),a(t/r));W=transform(polynomial(p['shape']),K,ell,Q(p['shape']['rate']),s);denom=W.abs_lower();zeta=s.zeta().abs_lower()
    if not denom>0 or not zeta>0:assert old['status']=='query_kernel_or_numerator_zero_not_excluded';return
    weak,J,local_terms=global_data;local=sum((v/a(w-sigma/r) for w,v in local_terms),flint.arb(0));pole=abs(res[1])/(s-1).abs_lower();unit=J/a(sigma/r);f=c['frontier'];d=ceil(Q(f['log_power']));L0=(flint.arb.const_e()+1).log();costs=[]
    assert len(old['observers'])==len(qs)
    for q,row in zip(qs,old['observers']):
        gap=a(sigma/r)-a(f['limit'])-a(f['margin'])/powq(a(q),Q(f['approach_power']));assert row['q']==q;overlap(row['gap_ball'],gap)
        if not gap>0:assert row['status']=='outside_observer_domain';continue
        logs=sum((a(comb(d,j))*L0**(d-j)*a(j+1).gamma()/gap**(j+1) for j in range(d+1)),flint.arb(0));cost=(local+pole+unit+a(Cs[str(q)])*logs)/denom/zeta
        for key,v in [('local_cost_ball',local),('pole_cost_ball',pole),('unit_cost_ball',unit),('kernel_denominator_lower_ball',denom),('numerator_zeta_lower_ball',zeta),('conditional_reciprocal_bound_ball',cost)]:overlap(row[key],v)
        cp(row['kernel_transform_ball'],W);assert not row['uniform_signed_premise_proved'] and abs(row['log_cost']-float(cost.upper().log()))<1e-10;costs.append(row['log_cost']);counts['independent_fully_charged_observers']+=1
    assert old['best_log_cost']==min(costs,default=None)


def check(directory):
    spec=read(directory/'protocol.json');seal=read(directory/'seal.json');batch=read(directory/'candidate_batch.json');arc=read(directory/'archive.json');final=read(directory/'final_evaluation.json');cases=read(directory/'final_cases.json');pc=read(directory/'parameter_cases.json');cal=read(directory/'parameter_calibration.json');cs=read(directory/'calibration_seal.json');checks={};counts=defaultdict(int)
    def passed(name):checks[name]=True;print('Verified',name,flush=True)
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/n)==spec['code_sha256'][n]
    for n,h in seal['files'].items():assert sha(directory/n)==h
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from kernel_correlation_report import summary as parent
    parent(source);passed('frozen_source_parent_and_mathematical_import_provenance')
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used'] and batch['frozen_before_validation'] and batch['generation_uses_training_only']
    assert pc['seal_sha256']==sha(directory/'seal.json') and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    for key,n in [('archive_seal_sha256','seal.json'),('parameter_cases_sha256','parameter_cases.json'),('parameter_calibration_sha256','parameter_calibration.json')]:assert cs[key]==sha(directory/n)
    assert not cs['final_cases_exist_at_calibration_seal'] and cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert final['protocol_sha256']==digest(spec) and final['cases_sha256']==digest(cases) and final['seal_sha256']==digest(seal) and final['calibration_seal_sha256']==digest(cs)
    assert not set(pc['fresh_q'])&set(spec['training_q']+spec['validation_new_q']+spec['parent_final_q_excluded']) and not set(cases['integers'])&set(spec['parent_final_scales_excluded'])
    for old in spec['retained_failed_runs_are_development']:
        d=Path(old['run_directory']);assert sha(d/'failure.json')==old['failure_sha256']
        for n,h in old['retained_files_sha256'].items():assert sha(d/n)==h
        oldspec=read(d/'protocol.json');assert oldspec['code_sha256']==old['original_code_sha256']
        for n in oldspec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==oldspec['code_sha256'][n]
        assert not set(cases['integers'])&set(old['excluded_final_scales']) and not set(pc['fresh_q'])&set(old['excluded_final_q'])
    passed('discovery_archive_parameter_calibration_and_fresh_scale_seals')
    discovery=read(directory/'discovery_data.json');validation=read(directory/'validation_data.json')
    for denial in [discovery['worker_access_denials'],cal['worker_access_denials']]:assert len(denial)==6 and all(denial.values())
    assert not read(directory/'source_forms.json')['growth_fits_archive_and_final_outcomes_supplied'];passed('generator_and_calibrator_isolation')
    native={}
    for name,data,points in [('training',discovery,spec['training_points']),('validation',validation,spec['validation_points']),('final',final['data'],cases['points'])]:
        native[name]={key:independent_table(table,points,counts) for key,table in data['tables'].items()};assert data['all_infinite_tails_included']
    passed('independent_generalized_positions_inverse_and_unit_complete_tails')
    flint.ctx.prec=768;ps={p['id']:p for p in batch['ablation_programs']+batch['programs']};res={};globals={}
    for i,p in ps.items():
        assert p['id']==digest({'shape':p['shape'],'parameters':p['parameters']}) and not p['actual_RH_uniform_estimate_proved']
        terms=p['shape']['terms'];assert terms and all(type(m)is int and m>=0 and Q(b) for m,b in terms)
        assert sorted(m for m,b in terms)==sorted(set(m for m,b in terms)) and max(abs(Q(b)) for m,b in terms)==1
        assert p['shape']['maximum_moment']==max(m for m,b in terms) and Q(terms[-1][1])>0 and Q(p['shape']['rate'])>0
        res[i]=residues(p,counts);globals[i]=global_check(p,res[i],counts)
    passed('exact_residues_true_actual_weak_bounds_and_all_scale_unit_increments')
    for p in ps.values():root_check(p,counts)
    passed('independent_Sturm_Hermite_and_complete_native_operator_root_exclusion')
    for p in ps.values():zero_constraints(p,counts)
    passed('fractional_dilation_complete_exception_sets_and_multiplicity_zero_chains')
    for i,p in ps.items():barrier_check(p,res[i],counts)
    passed('proved_sign_loss_barrier_including_actual_squarefree_support')
    for p in ps.values():reference_check(p,spec,counts)
    passed('synthesized_global_negative_power_reference_contour_estimates')
    observations_native={}
    for name,points,saved in [('training',spec['training_points'],batch['training_observables']),('validation',spec['validation_points'],validation['program_observables']),('final',cases['points'],final['program_observables'])]:
        observations_native[name]={i:observations(ps[i],native[name][ps[i]['parameter_id']],points,row,res[i],counts) for i,row in saved.items()}
    passed('independent_complete_centered_and_reference_observations')
    flint.ctx.prec=768;validated={c['id']:c for c in validation['candidates']};candidates={c['id']:c for c in batch['candidates']}
    # Constants are rounded up from the sealed response enclosures. Their
    # original Taylor uncertainty belongs in this check even when the new
    # independent arithmetic enclosure is considerably sharper.
    fit_inputs={i:{X:{k:flint.arb(v) for k,v in row.items()} for X,row in rows.items()} for i,rows in batch['training_observables'].items()}
    for c in batch['candidates']:
        p=ps[c['program_id']];r=Q(p['parameters'][2]);f=c['frontier'];assert r*Q(f['limit'])==Q(f['ordinary_limit']) and r*Q(f['margin'])==Q(f['ordinary_margin']) and not f['constant_growth_in_q_restricted'] and not f['finite_parameter_grid_suffices']
        eligible=Q(f['ordinary_limit'])==Q(1,2) and p['zero_bridge']['all_right_half_ordinary_zeros_preserved'] and p['zero_exceptions']['complete']
        assert c['critical_zero_constraint_if_uniform']==eligible and c['RH_sufficient_if_uniform']==(eligible and not p['zero_exceptions']['real_parts'])
        assert c['certificate_attempt']['uniform_premise_proved']==(Q(f['ordinary_limit'])>=1)
        core={k:c[k] for k in ['program_id','frontier','illustrative_constants_by_q']};assert c['id']==digest(core)
        constants_check(fit_inputs[p['id']],f,spec['training_q']+spec['validation_new_q'],c['illustrative_constants_by_q'],spec,counts)
        comparison_check(observations_native['validation'][p['id']],f,c['illustrative_constants_by_q'],spec['training_q']+spec['validation_new_q'],validated[c['id']]['validation'],counts)
        cost_check(p,c,c['illustrative_constants_by_q'],spec['training_q'],c['recovery_cost'],res[p['id']],globals[p['id']],counts)
    passed('normalized_fractional_targets_training_constants_validation_and_charged_observers')
    for banks in [arc['banks'],arc['ablation_banks']]:
        for bank in banks:
            members=[candidates[i] for i in bank['member_candidate_ids']];programs=[ps[c['program_id']] for c in members];sets=[set(map(Q,p['zero_exceptions']['real_parts'])) for p in programs];remaining=set.intersection(*sets)
            assert all(c['critical_zero_constraint_if_uniform'] for c in members) and not remaining and all(Q(p['parameters'][2])<2 for p in programs)
            cert=bank['certificate'];assert cert['RH_sufficient_if_every_member_uniform'] and list(map(Q,cert['remaining_real_parts']))==sorted(remaining) and not cert['uniform_signed_premises_proved']
            costs=[c['recovery_cost']['best_log_cost'] for c in members];expected=max(costs)+log(sum(exp(x-max(costs)) for x in costs)) if all(x is not None for x in costs) else None
            assert bank['joint_log_cost']==expected and bank['every_member_observer_charged'];counts['independent_complementary_fractional_RH_bridges']+=1
    passed('exact_complementary_banks_without_nominated_dilation_pair')
    calibrated={row['candidate_id']:row['constants'] for row in cal['illustrative_free_constants']};fresh=pc['fresh_q'];outcomes={o['candidate_id']:o for o in final['outcomes']}
    for i,Cs in calibrated.items():constants_check(fit_inputs[candidates[i]['program_id']],candidates[i]['frontier'],fresh,Cs,spec,counts)
    for i,o in outcomes.items():
        c=candidates[i];p=ps[c['program_id']];Cs={**c['illustrative_constants_by_q'],**calibrated[i]};assert o['constants']==Cs;qs=spec['training_q']+spec['validation_new_q']+fresh
        comparison_check(observations_native['final'][p['id']],c['frontier'],Cs,qs,o,counts);cost_check(p,c,Cs,qs,o['recovery_cost'],res[p['id']],globals[p['id']],counts)
    for b,o in zip(arc['banks'],final['bank_outcomes']):assert o['bank_id']==b['id'] and o['finite_points_passed']==all(outcomes[i]['finite_points_passed'] for i in b['member_candidate_ids']) and o['every_member_tested'] and not o['uniform_signed_premises_proved']
    passed('fresh_q_training_only_calibration_and_complete_fresh_bank_tests')
    for row in final['reference_bound_outcomes']:
        p=ps[row['program_id']];order=Q(row['order']);C=flint.arb(p['reference_decay_certificates'][str(order)]['constant_ball']);ratios=[]
        for X,obs0 in observations_native['final'][p['id']].items():
            V=abs(obs0['unit_two_residue_residual_ball']);B=C*powq(a(X),-order);assert V<=B;ratios.append(float((V/B).upper()));counts['independent_global_reference_bound_witnesses']+=1
        assert abs(row['maximum_ratio']-max(ratios))<1e-10 and row['global_premise_proved'] and not row['actual_inverse_estimate_proved']
    for i,rows in observations_native['final'].items():
        r=Q(ps[i]['parameters'][2]);weak,J,local=globals[i]
        for X,row in rows.items():assert abs(row['inverse_centered_ball'])<=weak*powq(a(X),1/r);counts['independent_true_actual_weak_bound_witnesses']+=1
        for X in cases['integers']:assert abs(rows[str(Q(X)+Q(spec['final_cases']['real_offset']))]['inverse_centered_ball']-rows[str(X)]['inverse_centered_ball'])<=J*a(spec['final_cases']['real_offset']);counts['independent_unit_increment_witnesses']+=1
    passed('fresh_global_reference_actual_weak_and_unit_increment_witnesses')
    for c in final['negative_controls']:
        assert c['typed_alias_rejected'] and c['reference_bound_itself_is_true'] and not c['actual_growth_counterexample_claimed'] and ps[c['program_id']]['reference_decay_certificates']['1']['arithmetic_model']!='inverse';counts['independent_arithmetic_type_alias_rejections']+=1
    passed('true_reference_bound_cannot_be_transferred_to_actual_inverse_arithmetic')
    # Producer replay is provenance, not part of independent mathematical code.
    with tempfile.TemporaryDirectory(prefix='lattice-synthesis-replay-') as td:
        d=Path(td);put(d/'protocol.json',spec);put(d/'source_forms.json',read(directory/'source_forms.json'))
        subprocess.run([sys.executable,str(BASE/'lattice_synthesis_search.py'),'worker','--run-dir',str(d)],check=True,cwd=BASE)
        replay={n:sha(d/n) for n in seal['files']};assert replay==seal['files']
    passed('deterministic_isolated_learning_promotion_ablation_and_archive_replay')
    assert spec['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[] and not final['RH_proved'] and not spec['new_prime_distribution_estimate_imported']
    passed('actual_signed_critical_uniform_proof_obligations_remain_open')
    result={'protocol_sha256':digest(spec),'checker_sha256':sha(BASE/'check_lattice_synthesis.py'),'final_sha256':sha(directory/'final_evaluation.json'),
        'checks':checks,'all_passed':all(checks.values()),'counts':dict(counts),'replay_sha256':replay,
        'mathematical_audit_imports_production_code':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,'machine_formalized':False}
    put(directory/'verification.json',result);print('Independent verification',len(checks),'/',len(checks),flush=True);return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run-dir',type=Path,required=True);args=parser.parse_args();check(args.run_dir.resolve())
if __name__=='__main__':main()
