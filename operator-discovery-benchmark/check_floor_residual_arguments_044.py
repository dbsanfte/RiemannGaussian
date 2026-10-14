"""Independent admission of signed floor vectors and conditional refinement.

Targets have constant one and no indicator. Constant-zero diagnostic vectors
cannot replace that target. Exact endpoints, not printed balls, price norms.
"""
from fractions import Fraction as F
from math import gcd
from copy import deepcopy
from heapq import heappush,heappop
from flint import arb,ctx

MAX_BITS=4096
MAX_RESULT_BITS=8192
MAX_H=8388608
MAX_SUPPORT=2048
MAX_INDEX=4096
BURNOL_SOURCE='https://arxiv.org/pdf/math/0103058'
LARGE_SIEVE_SOURCE='https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf'

class Meter:
    def __init__(self,cap=1000000000):self.cap=cap;self.operations=0
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('work cap')
        self.operations+=n

def _meter(m):return Meter() if m is None else m

def _q(s,m):
    if type(s) is not str or not 1<=len(s)<=2500:raise ValueError('canonical rational text')
    m.charge(len(s)+1)
    try:v=F(s)
    except (ValueError,ZeroDivisionError):raise ValueError('rational') from None
    if str(v)!=s or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_BITS:
        raise ValueError('canonical rational bit cap')
    return v

def _int(v,lo,hi,name):
    if type(v) is not int or not lo<=v<=hi:raise ValueError(name)
    return v

def _bits(v,m):
    if type(v) is not int or abs(v).bit_length()>MAX_RESULT_BITS:raise ValueError('intermediate bit cap')
    m.charge(abs(v).bit_length()+1)
    return v

def _mul(a,b,m):
    if a and b and abs(a).bit_length()+abs(b).bit_length()>MAX_RESULT_BITS:
        raise ValueError('product preflight bit cap')
    return _bits(a*b,m)

def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _program(p,m,target=False):
    if type(p) is not dict or set(p)!={'id','constant','coefficients','steps'}:raise ValueError('exact signed program schema')
    if type(p['id']) is not str or not 1<=len(p['id'])<=250:raise ValueError('bounded id')
    constant=_q(p['constant'],m)
    if type(p['coefficients']) is not list or type(p['steps']) is not list or len(p['coefficients'])+len(p['steps'])>MAX_SUPPORT:
        raise ValueError('support cap')
    rows=[]
    for key,name in (('n','coefficients'),('q','steps')):
        out=[];prior=1
        for row in p[name]:
            if type(row) is not dict or set(row)!={key,'value'}:raise ValueError('exact row')
            n=row[key]
            if type(n) is not int or not prior<n<=MAX_INDEX:raise ValueError('sorted distinct indices2..4096')
            value=_q(row['value'],m)
            if not value:raise ValueError('omit zero coefficients')
            out.append((n,value));prior=n;m.charge(n.bit_length()+8)
        rows.append(out)
    if target and (constant!=1 or rows[1]):raise ValueError('RH target requires constant1 and no indicators')
    return constant,rows[0],rows[1]

def _encode(id,C,coeff,steps):
    return {'id':id[:250],'constant':str(C),
      'coefficients':[{'n':n,'value':str(v)} for n,v in sorted(coeff.items()) if v],
      'steps':[{'q':q,'value':str(v)} for q,v in sorted(steps.items()) if v]}

def verify_program(program,target=True,meter=None):
    meter=_meter(meter)
    if type(target) is not bool:raise ValueError('typed target role')
    C,coeff,steps=_program(program,meter,target)
    bound=abs(C)+sum((abs(c)*F(n-1,n) for n,c in coeff),F(0))+sum((abs(c) for _,c in steps),F(0))
    return {'verified':True,'program':deepcopy(program),'role':'target' if target else 'signed_diagnostic_or_forcing',
      'pointwise_abs_bound':str(bound),'constant':str(C),
      'mellin':{'domain':'Re(s)>0; initially floor integrals at Re(s)>1',
        'floor_term':'(n^-1-n^-s)*zeta(s)/s','step_term':'q^-s/s',
        'zero_response':'(constant-sum d_q*q^-rho)/rho',
        'target_zero_obstruction_available':C==1 and not steps,
        'lower_norm_squared_at_offhalf_zero':'(2Re(rho)-1)/abs(rho)^2' if C==1 and not steps else None},
      'convergence_proved':False,'RH_proved':False}

def compile_dilation(program,q,meter=None):
    """Lift only the subtracted combination, not the constant indicator."""
    meter=_meter(meter);_,coeff,steps=_program(program,meter)
    _int(q,2,(1<<MAX_BITS)-1,'integer dilation>=2')
    out={}
    for n,c in coeff:
        index=_mul(q,n,meter);out[index]=out.get(index,F(0))+c
        out[q]=out.get(q,F(0))-c/n
    result=_encode('lift'+str(q)+'('+program['id']+')',F(0),out,{_mul(q,s,meter):c for s,c in steps})
    _program(result,meter)
    return result

def compile_residual_dilation(program,q,meter=None):
    meter=_meter(meter);C,_,_=_program(program,meter)
    lifted=compile_dilation(program,q,meter)
    steps={row['q']:F(row['value']) for row in lifted['steps']}
    steps[q]=steps.get(q,F(0))-C
    result=_encode('D'+str(q)+'('+program['id']+')',F(0),
      {row['n']:F(row['value']) for row in lifted['coefficients']},steps)
    _program(result,meter)
    return result

def fixed_stencil_guard(indices,dilations,meter=None):
    meter=_meter(meter)
    if type(indices) is not list or type(dilations) is not list or len(indices)+len(dilations)>4096:
        raise ValueError('finite dictionary')
    for values in (indices,dilations):
        if any(type(n) is not int or n<2 or n.bit_length()>MAX_BITS for n in values) or values!=sorted(set(values)):
            raise ValueError('sorted distinct dictionary integers>=2')
    period=1
    for n in indices:period=_mul(period,n//gcd(period,n),meter)
    minimum=max([2]+dilations);M=_mul(period,(minimum+period-1)//period,meter)
    constant=F(1,_mul(2,_bits(1+(M+1)**2,meter),meter))
    return {'verified':True,'scope':'constant-one forcing in fixed finite head/indicator dictionary',
      'indices':indices,'dilations':dilations,'cells':[1,M,M+1],'weights':['1','1','-1'],
      'identity':'h(cell1)+h(cellM)-h(cellM+1)=1',
      'forcing_norm_squared_lower':str(constant),'fixed_dictionary_vanishing_forcing_impossible':True,
      'growing_dictionary_refuted':False,'RH_refuted':False}

def verify_family_refinement(parent_program,child_program,q,b,meter=None):
    meter=_meter(meter);_,pc,_=_program(parent_program,meter,True);_,cc,_=_program(child_program,meter,True)
    bb=_q(b,meter);lift=compile_dilation(parent_program,q,meter)
    forcing=dict(cc)
    for row in lift['coefficients']:
        n=row['n'];forcing[n]=forcing.get(n,F(0))-bb*F(row['value'])
    h=_encode('forcing:'+parent_program['id']+'->'+child_program['id'],F(1),forcing,{q:bb} if bb else {})
    _,hc,hs=_program(h,meter)
    return {'verified':True,'parent_program':deepcopy(parent_program),'child_program':deepcopy(child_program),
      'q':q,'b':str(bb),'dilation_program':lift,'forcing_program':h,
      'identity':'e_child=h+b*D_q(e_parent)',
      'norm_identity':'norm(e_child)^2=norm(h)^2+(b^2/q)*norm(e_parent)^2+2*b*<h,D_q e_parent>',
      'operator_norm_squared':str(F(1,q)),'parent_energy_coefficient':str(bb*bb/q),
      'signed_cross_preserved':True,'endpoint_restatement':bb==0,
      'fixed_stencil_guard':fixed_stencil_guard([n for n,_ in hc],[q for q,_ in hs],meter),
      'all_scale_forcing_control':'OPEN','growing_family_convergence_proved':False,'RH_proved':False}

def verify_log_forcing_gate(q,b,A,eta,provider_status='OPEN',meter=None):
    meter=_meter(meter);_int(q,2,(1<<MAX_BITS)-1,'dilation integer>=2')
    bb=_q(b,meter);cost=_q(A,meter);exponent=_q(eta,meter)
    if cost<0 or not 0<exponent<=1 or type(provider_status) is not str or provider_status!='OPEN':
        raise ValueError('nonnegative log cost, eta in(0,1], OPEN provider')
    t=bb*bb/q
    if t>=1:raise ValueError('no admitted dilation contraction')
    young=None if not t else (1-t)/(2*t);rho=F(0) if not t else (1+t)/2
    forcing=cost if not t else (1+1/young)*cost
    return {'verified':True,'q':q,'b':str(bb),'A':str(cost),'eta':str(exponent),
      't':str(t),'rho':str(rho),'young_parameter':None if young is None else str(young),
      'forcing_multiplier':str(forcing),
      'leaf':{'status':'OPEN','inequality':'norm(h_N)^2<=A/L(N)^eta',
        'L':'1+floor(log2(N))=N.bit_length()',
        'domain':'EVERY j>=0,N=N0*q^j; integer N0>=1; one fixed recipe and parameters'},
      'scale_lower_bound':'L(N0*q^i)>=1+i',
      'conditional_energy':'rho^j*E0+B*sum_(i=0..j-1)rho^(j-1-i)/(1+i)^eta',
      'conditional_tends_to_zero':True,'endpoint_restatement':bb==0,
      'zero_forcing_excluded_for_linear_support':cost==0,
      'finite_norms_discharge_leaf':False,'convergence_proved':False,'RH_proved':False}

def geometric_rate_guard():
    return {'provider':'Burnol Theorem1.3; imported unconditional lower bound','source':BURNOL_SOURCE,
      'bound':'liminf_(N->infinity) log(N)*norm(e_N)^2>0',
      'domain':'pure floor targets with maxsupport<=N; along N=N0*q^j',
      'uniform_geometric_contraction_excluded':True,
      'growing_support_convergence_refuted':False,'RH_refuted':False}

def periodic_energy(program,meter=None):
    """Exact full-period mean-square, including signed covariance and mean."""
    meter=_meter(meter);C,coeff,steps=_program(program,meter)
    D=1
    for v in [C]+[c/n for n,c in coeff]+[d for _,d in steps]:
        D=_mul(D,v.denominator//gcd(D,v.denominator),meter)
    CD=int(C*D);weights=[(n,int(c*D/n)) for n,c in coeff]
    mean_num=_bits(2*CD-2*sum(int(d*D) for _,d in steps)-sum(w*(n-1) for n,w in weights),meter)
    # Independently factor each occupied index and enumerate its divisors.
    # The producer uses dense sums over multiples; both express the complete
    # signed gcd Gram by gcd(m,n)^2-1=sum_(d|m,n,d>1)J2(d).
    sums={};jordan={}
    for n,w in weights:
        remaining=n;p=2;factors=[]
        while p*p<=remaining:
            count=0
            while remaining%p==0:count+=1;remaining//=p;meter.charge(8)
            if count:factors.append((p,count))
            p+=1;meter.charge(8)
        if remaining>1:factors.append((remaining,1))
        divisors=[(1,1)]
        for p,count in factors:
            old=divisors[:];power=1;j2=1
            for e in range(1,count+1):
                power*=p;j2=(p*p-1)*p**(2*(e-1));meter.charge(16)
                divisors.extend((d*power,j*j2) for d,j in old)
        for d,j2 in divisors:
            if d>1:
                sums[d]=_bits(sums.get(d,0)+w,meter);jordan[d]=j2
    covariance=0
    for d,w in sorted(sums.items()):
        covariance=_bits(covariance+_mul(jordan[d],_mul(w,w,meter),meter),meter)
    den=_mul(12,_mul(D,D,meter),meter)
    mean=F(mean_num,2*D);variance=F(covariance,den)
    value=F(_bits(3*_mul(mean_num,mean_num,meter)+covariance,meter),den)
    if variance<0 or value<0:raise ArithmeticError('invalid exact periodic Gram')
    K=max([1]+[n for n,_ in coeff])
    return {'K':K,'mean':mean,'variance':variance,'V':value,
      'pair_count':len(coeff)**2,'D':D,'R_zero':CD,'weights':weights,
      'events':[(n,int(c*D)) for n,c in coeff],'step_events':[(q,-int(d*D)) for q,d in steps],
      'integer_mean_numerator':mean_num,'integer_variance_numerator':covariance,
      'integer_V_numerator':3*mean_num**2+covariance,'integer_common_denominator':den,
      'jordan_divisor_sums':[{'d':d,'J2':str(jordan[d]),'weighted_sum':str(w)} for d,w in sorted(sums.items())]}

def _dyadic(row,meter):
    if type(row) is not list or len(row)!=2 or type(row[0]) is not str or type(row[1]) is not int:
        raise ValueError('exact dyadic endpoint')
    try:n=int(row[0])
    except ValueError:raise ValueError('dyadic integer') from None
    if str(n)!=row[0] or len(row[0])>2500 or abs(n).bit_length()>MAX_RESULT_BITS or abs(row[1])>65536:
        raise ValueError('dyadic endpoint cap')
    meter.charge(abs(n).bit_length()+abs(row[1])+1)
    return F(n<<row[1]) if row[1]>=0 else F(n,1<<(-row[1]))

def _arb_endpoint(v):
    n,e=v.man_exp();n=int(n);e=int(e)
    return F(n<<e) if e>=0 else F(n,1<<(-e))

def _enclosure(value,meter):
    if type(value) is not dict or set(value)!={'ball','lower_dyadic','upper_dyadic'}:
        raise ValueError('complete numerical enclosure')
    lo=_dyadic(value['lower_dyadic'],meter);hi=_dyadic(value['upper_dyadic'],meter)
    if lo>hi or type(value['ball']) is not str or len(value['ball'])>2500:raise ValueError('interval')
    try:ball=arb(value['ball'])
    except ValueError:raise ValueError('interval display') from None
    if not ball.is_finite() or _arb_endpoint(ball.upper())<lo or _arb_endpoint(ball.lower())>hi:
        raise ValueError('nonfinite or disjoint diagnostic display')
    return lo,hi

def verify_norm(program,certificate,meter=None):
    meter=_meter(meter);C,coeff,steps=_program(program,meter)
    if type(certificate) is not dict:raise ValueError('norm certificate')
    H=_int(certificate.get('H'),0,MAX_H,'bounded head horizon')
    precision=_int(certificate.get('precision'),128,4096,'precision128..4096')
    if any(q>H for q,_ in steps):raise ValueError('tail before all indicators active')
    energy=periodic_energy(program,meter)
    D=energy['D'];CD=energy['R_zero'];weights=energy['weights'];events=energy['events'];step_events=energy['step_events']
    A=_bits(sum(w for _,w in weights),meter)
    for _,v in events+step_events:_bits(v,meter)
    early=abs(C)+sum((abs(c)*F(n-1,n) for n,c in coeff),F(0))+sum((abs(d) for _,d in steps),F(0))
    M=abs(C-sum((d for _,d in steps),F(0)))+sum((abs(c)*F(n-1,n) for n,c in coeff),F(0))
    _bits(int(early*D),meter)
    a=H+1;K=energy['K'];V=energy['V']
    pointwise=M*M/a;factor=F(1,a)+F(K*K,a*(a+1));sieve=V*factor;tail=min(pointwise,sieve)
    for v in (early,M,pointwise,factor,sieve,tail):_bits(v.numerator,meter);_bits(v.denominator,meter)
    visits=sum(H//n for n,_ in events)
    meter.charge(32*H+visits*(12+len(events).bit_length()*8)+128)
    heap=[]
    for n,event in events:heappush(heap,(n,n,event))
    stepmap=dict(step_events);residue=CD
    with ctx.workprec(max(256,precision+64)):
        total=arb(0)
        for k in range(1,H+1):
            residue-=A
            while heap and heap[0][0]==k:
                at,n,event=heappop(heap);residue+=event;heappush(heap,(at+n,n,event))
            residue+=stepmap.get(k,0)
            if abs(residue)>early*D:raise ArithmeticError('exact early residue bound')
            total+=arb(residue)*residue/(k*(k+1))
        head=total/(arb(D)*D)
        if not head.is_finite():raise ArithmeticError('finite independent head')
        lo,hi=_enclosure(certificate.get('head',{}).get('enclosure'),meter)
        own_lo,own_hi=_arb_endpoint(head.lower()),_arb_endpoint(head.upper())
        if lo>own_lo or hi<own_hi:raise ValueError('head enclosure underprices replay')
        wlo,whi=_enclosure(certificate.get('norm_squared'),meter)
        if wlo>own_lo or whi<own_hi+tail:raise ValueError('whole interval omits analytic tail')
    expected={'schema':'floor-signed-vector-norm-v1','program':deepcopy(program),'H':H,'precision':precision,
      'basis':{'floor':'f_n(cell k)=(k mod n)/n','step':'I_q(cell k)=1_(k>=q)',
        'residual':'constant-sum c_n*f_n-sum d_q*I_q'},
      'lattice':{'D':str(D),'A':str(A),'R_zero':str(CD),
        'weights':[{'n':n,'weight':str(w)} for n,w in weights],
        'periodic_events':[{'n':n,'value':str(v)} for n,v in events],
        'step_events':[{'q':q,'value':str(v)} for q,v in step_events],
        'early_abs_bound':str(early),'update':'R(k)-R(k-1)=-A+sum_(n|k)c_n*D-sum_(q=k)d_q*D'},
      'head':{'indices':[1,H],'enclosure':certificate['head']['enclosure']},
      'periodic_energy':{'K':K,'mean':str(energy['mean']),'variance':str(energy['variance']),'V':str(V),
        'formula':'(C-sum d-sum c*(n-1)/(2n))^2+sum_mn c_m*c_n*(gcd(m,n)^2-1)/(12mn)',
        'kernel_formula':'(gcd(m,n)^2-1)/(12mn)','provider':'Jordan2_divisor_squares',
        'jordan_identity':'gcd(m,n)^2-1=sum_(d|m,n,d>1)J2(d)',
        'integer_mean_numerator':str(energy['integer_mean_numerator']),
        'jordan_divisor_sums':energy['jordan_divisor_sums'],'all_signed_pairs_retained':True,
        'pair_count':energy['pair_count'],'integer_variance_numerator':str(energy['integer_variance_numerator']),
        'integer_V_numerator':str(energy['integer_V_numerator']),
        'integer_common_denominator':str(energy['integer_common_denominator'])},
      'tail':{'start':a,'measure':str(F(1,a)),'M':str(M),'lower':'0','pointwise_upper':str(pointwise),
        'large_sieve_upper':str(sieve),'upper':str(tail),
        'chosen_provider':'large_sieve' if sieve<pointwise else 'pointwise',
        'steps_active':True,'observations_used_to_infer_tail':False},
      'imported_large_sieve':{'authors':'H. L. Montgomery and R. C. Vaughan',
        'title':'The large sieve','year':1973,'theorem':'Theorem1(1.4) and matrix duality Lemma1',
        'url':LARGE_SIEVE_SOURCE,'block_bound':'(L+K^2)*V','frequency_spacing_lower':str(F(1,K*K)),
        'weighted_tail_factor':str(factor),'weighted_tail_formula':'V*(1/a+K^2/(a*(a+1))), a=H+1',
        'minus_one_sharpening_used':False,'detector_discovered_theorem':False},
      'norm_squared':certificate['norm_squared'],'domain':'0<x<=1',
      'continuous_global_fixed_vector_bound':True,'float_norm_or_sign_admission_used':False,
      'target_role_requires_constant1_and_no_steps':True,'general_vector_is_automatically_RH_bearing':False,
      'convergence_as_support_increases_proved':False,'source_coefficient_recovery_claimed':False,
      'actual_source_data_read':False,'RH_proved':False,'RH_refuted':False,
      'coefficient_bit_count':sum(abs(v.numerator).bit_length()+v.denominator.bit_length() for v in [C]+[c for _,c in coeff]+[d for _,d in steps]),
      'support':len(coeff)+len(steps)}
    for name in ('kernel_cache_entries','kernel_cache_hits','kernel_cache_bytes_estimate'):
        v=certificate.get(name)
        if type(v) is not int or v<0:raise ValueError('cache metadata type')
        expected[name]=v
    counts=certificate.get('counts')
    if type(counts) is not dict or set(counts)!={'operations','peak_integer_bits','peak_bytes_estimate'} or any(type(v) is not int or v<0 for v in counts.values()):
        raise ValueError('counter metadata')
    expected['counts']=counts
    if not _eq(certificate,expected):raise ValueError('altered vector/covariance/tail/domain certificate')
    return {'verified':True,'program':deepcopy(program),'global_fixed_norm_squared_lower':str(max(F(0),lo)),
      'global_fixed_norm_squared_upper':str(whi),'H':H,'independent_precision':max(256,precision+64),
      'tail_upper':str(tail),'periodic_energy':str(V),'all_domain_included':True,
      'all_signed_covariances_retained':True,'display_ball_is_diagnostic_only':True,
      'target_zero_guard_available':C==1 and not steps,'convergence_proved':False,'RH_proved':False}
