"""Independent integer-floor identities, whole norms and OPEN convergence gates.

Indicator steps are allowed for forcing norms, never the RH-bearing target.
No producer imports or arithmetic-source observations.
"""
from fractions import Fraction as F
from math import gcd
from copy import deepcopy
from heapq import heappush,heappop
from flint import arb,ctx

MAX_BITS=4096
MAX_RESULT_BITS=8192
MAX_H=8388608
BURNOL_SOURCE='https://arxiv.org/pdf/math/0103058'

def _geometric_exclusion():
    return {'provider':'Burnol Theorem1.3; imported unconditional lower bound',
      'source':BURNOL_SOURCE,
      'bound':'liminf_(N->infinity) log(N)*norm(e_N)^2>0',
      'domain':'pure floor targets with maxsupport<=N; along N=N0*q^j',
      'conclusion':'uniform geometric norm decay is impossible in this domain',
      'growing_support_convergence_refuted':False,'RH_refuted':False}

class Meter:
    def __init__(self,cap=500000000):self.cap=cap;self.operations=0
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
    if abs(v).bit_length()>MAX_RESULT_BITS:raise ValueError('intermediate bit cap')
    m.charge(abs(v).bit_length()+1)
    return v

def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _program(p,m,target=False):
    if type(p) is not dict or set(p)!={'id','coefficients','steps'}:raise ValueError('exact program schema')
    if type(p['id']) is not str or not 1<=len(p['id'])<=250:raise ValueError('bounded id')
    if type(p['coefficients']) is not list or type(p['steps']) is not list or len(p['coefficients'])+len(p['steps'])>256:
        raise ValueError('support cap')
    rows=[]
    for key,name in (('n','coefficients'),('q','steps')):
        out=[];prior=1
        for row in p[name]:
            if type(row) is not dict or set(row)!={key,'value'}:raise ValueError('exact row')
            n=row[key]
            if type(n) is not int or n<=prior or n.bit_length()>MAX_BITS:raise ValueError('sorted distinct indices>=2')
            value=_q(row['value'],m)
            if not value:raise ValueError('omit zero coefficients')
            out.append((n,value));prior=n;m.charge(n.bit_length()+8)
        rows.append(out)
    if target and rows[1]:raise ValueError('indicator forcing is not an RH-bearing target')
    return rows

def verify_program(program,target=True,meter=None):
    meter=_meter(meter)
    if type(target) is not bool:raise ValueError('typed target role')
    coeff,steps=_program(program,meter,target)
    ceiling=1+sum(abs(c)*F(n-1,n) for n,c in coeff)+sum(abs(c) for _,c in steps)
    return {'verified':True,'role':'target' if target else 'forcing_or_diagnostic',
      'program':deepcopy(program),'pointwise_residual_bound':str(ceiling),
      'mellin':{'domain':'Re(s)>0; initially floor integrals at Re(s)>1',
        'floor_term':'(n^-1-n^-s)*zeta(s)/s','step_term':'q^-s/s',
        'zero_response':'1/rho' if not steps else '(1-sum d_q*q^-rho)/rho',
        'target_zero_obstruction_available':not steps,
        'lower_norm_squared_at_offhalf_zero':'(2Re(rho)-1)/abs(rho)^2' if not steps else None},
      'norm_sequence_convergence_proved':False,'RH_proved':False}

def _encode(id,coeff,steps):
    return {'id':id[:250],'coefficients':[{'n':n,'value':str(v)} for n,v in sorted(coeff.items()) if v],
      'steps':[{'q':q,'value':str(v)} for q,v in sorted(steps.items()) if v]}

def compile_dilation(program,q,meter=None):
    meter=_meter(meter);coeff,steps=_program(program,meter)
    _int(q,2,(1<<MAX_BITS)-1,'integer dilation>=2')
    if q.bit_length()>MAX_BITS:raise ValueError('dilation bit cap')
    out={}
    for n,c in coeff:
        index=_bits(q*n,meter)
        out[index]=out.get(index,F(0))+c
        out[q]=out.get(q,F(0))-c/n
    return _encode('D'+str(q)+'('+program['id']+')',out,{_bits(q*s,meter):c for s,c in steps})

def fixed_stencil_guard(indices,dilations,meter=None):
    meter=_meter(meter)
    if type(indices) is not list or type(dilations) is not list or len(indices)+len(dilations)>512:
        raise ValueError('finite dictionary')
    for values in (indices,dilations):
        if any(type(n) is not int or n<2 or n.bit_length()>MAX_BITS for n in values) or values!=sorted(set(values)):
            raise ValueError('sorted distinct dictionary integers>=2')
    period=1
    for n in indices:period=_bits(period*(n//gcd(period,n)),meter)
    minimum=max([2]+dilations);M=_bits(period*((minimum+period-1)//period),meter)
    constant=F(1,_bits(2*(1+(M+1)**2),meter))
    return {'verified':True,'scope':'fixed finite head/indicator dictionary; coefficients arbitrary',
      'indices':indices,'dilations':dilations,'cells':[1,M,M+1],'weights':['1','1','-1'],
      'identity':'h(cell1)+h(cellM)-h(cellM+1)=1',
      'forcing_norm_squared_lower':str(constant),
      'fixed_dictionary_vanishing_forcing_impossible':True,
      'growing_dictionary_refuted':False,'RH_refuted':False}

def verify_family_refinement(parent_program,child_program,q,b,meter=None):
    meter=_meter(meter);pc,_=_program(parent_program,meter,True);cc,_=_program(child_program,meter,True)
    bb=_q(b,meter);lift=compile_dilation(parent_program,q,meter)
    forcing=dict(cc)
    for row in lift['coefficients']:
        n=row['n'];forcing[n]=forcing.get(n,F(0))-bb*F(row['value'])
    h=_encode('forcing:'+parent_program['id']+'->'+child_program['id'],forcing,{q:bb} if bb else {})
    _program(h,meter)
    squared=bb*bb/q
    return {'verified':True,'parent_program':deepcopy(parent_program),'child_program':deepcopy(child_program),
      'q':q,'b':str(bb),'dilation_program':lift,'forcing_program':h,
      'identity':'e_child=h+b*D_q(e_parent)',
      'norm_identity':'norm(e_child)^2=norm(h)^2+(b^2/q)*norm(e_parent)^2+2*b*<h,D_q e_parent>',
      'operator_norm_squared':str(F(1,q)),'parent_energy_coefficient':str(squared),
      'signed_cross_preserved':True,'endpoint_restatement':bb==0,
      'fixed_stencil_guard':fixed_stencil_guard([n for n,_ in _program(h,meter)[0]],[q],meter),
      'all_scale_forcing_control':'OPEN','growing_family_convergence_proved':False,'RH_proved':False}

def verify_relative_forcing_gate(q,b,tau,provider_status='OPEN',meter=None):
    meter=_meter(meter);_int(q,2,(1<<MAX_BITS)-1,'dilation integer>=2')
    bb=_q(b,meter);tau=_q(tau,meter)
    if tau<0 or provider_status!='OPEN' or type(provider_status) is not str:
        raise ValueError('nonnegative relative forcing; only OPEN provider admitted')
    t=bb*bb/q;gap=1-t-tau;margin=gap*gap-4*t*tau
    admissible=gap>0 and margin>0
    rho=None;young=None
    if admissible:
        if not t:rho=tau
        elif not tau:rho=t
        else:young=gap/(2*t);rho=t+tau+gap/2+2*t*tau/gap
        if not 0<=rho<1:raise ArithmeticError('Young contraction')
    return {'verified':True,'admissible':admissible,'q':q,'b':str(bb),'tau':str(tau),
      't':str(t),'gap':str(gap),'strict_margin':str(margin),
      'contraction_energy_coefficient':None if rho is None else str(rho),
      'young_parameter':None if young is None else str(young),
      'leaf':{'status':'OPEN','inequality':'norm(h_N)^2<=tau*norm(e_N)^2',
        'domain':'EVERY j>=0,N=N0*q^j; one fixed recipe and fixed parameters'},
      'conditional_result':'norm(e_(N0*q^j))^2<=rho^j*norm(e_N0)^2; tends to0' if admissible else None,
      'uniform_geometric_gate_excluded_for_linear_support':admissible,
      'imported_lower_bound':_geometric_exclusion(),
      'search_role':'negative calibration; not a viable uniform convergence provider',
      'endpoint_restatement':bb==0,'finite_norms_discharge_leaf':False,
      'convergence_proved':False,'RH_proved':False}

def verify_absolute_forcing_gate(q,b,young,constant,ratio,provider_status='OPEN',meter=None):
    meter=_meter(meter);_int(q,2,(1<<MAX_BITS)-1,'dilation integer>=2')
    bb=_q(b,meter);y=_q(young,meter);A=_q(constant,meter);tau=_q(ratio,meter)
    if y<=0 or A<0 or not 0<=tau<1 or type(provider_status) is not str or provider_status!='OPEN':
        raise ValueError('positive Young, nonnegative cost, decaying OPEN forcing')
    rho=(1+y)*bb*bb/q
    if rho>=1:raise ValueError('no admitted contraction')
    return {'verified':True,'rho':str(rho),'forcing_multiplier':str((1+1/y)*A),'ratio':str(tau),
      'leaf':{'status':'OPEN','domain':'EVERY iteration j>=0','inequality':'norm(h_j)^2<=A*tau^j'},
      'conditional_energy':'rho^j*E0+(1+1/young)*A*sum_(i=0..j-1)rho^(j-1-i)*tau^i',
      'equal_ratio_resonance_retained':rho==tau,'conditional_tends_to_zero':True,
      'uniform_geometric_gate_excluded_for_linear_support':True,
      'imported_lower_bound':_geometric_exclusion(),
      'endpoint_restatement':bb==0,'convergence_proved':False,'RH_proved':False}

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
    mantissa,exponent=v.man_exp()
    return F(int(mantissa)<<int(exponent)) if exponent>=0 else F(int(mantissa),1<<(-int(exponent)))

def _enclosure(value,meter):
    if type(value) is not dict or set(value)!={'ball','lower_dyadic','upper_dyadic'}:
        raise ValueError('complete numerical enclosure')
    lower=_dyadic(value['lower_dyadic'],meter);upper=_dyadic(value['upper_dyadic'],meter)
    if lower>upper or type(value['ball']) is not str or len(value['ball'])>2500:raise ValueError('interval')
    try:ball=arb(value['ball'])
    except ValueError:raise ValueError('interval display') from None
    if not ball.is_finite():raise ValueError('finite interval')
    # Decimal Arb display is rounded independently of the authoritative dyadic
    # endpoints. It is diagnostic, never a price used in certificate admission.
    if _arb_endpoint(ball.upper())<lower or _arb_endpoint(ball.lower())>upper:
        raise ValueError('display ball is disjoint from certified interval')
    return lower,upper

def verify_norm(program,certificate,meter=None):
    meter=_meter(meter);coeff,steps=_program(program,meter)
    if type(certificate) is not dict:raise ValueError('norm certificate')
    H=_int(certificate.get('H'),0,MAX_H,'bounded head horizon')
    precision=_int(certificate.get('precision'),128,4096,'precision128..4096')
    if any(q>H for q,_ in steps):raise ValueError('tail before all indicators active')
    D=1
    for value in [c/n for n,c in coeff]+[c for _,c in steps]:
        D=_bits(D*(value.denominator//gcd(D,value.denominator)),meter)
    weights=[(n,int(c*D/n)) for n,c in coeff];events=[(n,int(c*D)) for n,c in coeff]
    step_events=[(q,-int(c*D)) for q,c in steps];A=sum(w for _,w in weights)
    for _,value in weights+events+step_events:_bits(value,meter)
    _bits(A,meter)
    head_bound=1+sum(abs(c)*F(n-1,n) for n,c in coeff)+sum(abs(c) for _,c in steps)
    _bits(int(head_bound*D),meter)
    M=abs(F(1)-sum((c for _,c in steps),F(0)))+sum((abs(c)*F(n-1,n) for n,c in coeff),F(0))
    tail=M*M/(H+1)
    # Independent heap scan instead of the producer's dense event sieve.
    visits=sum(H//n for n,_ in events)
    meter.charge(32*H+visits*(12+len(events).bit_length()*8)+128)
    heap=[]
    for n,event in events:heappush(heap,(n,n,event))
    stepmap=dict(step_events);residue=D
    with ctx.workprec(max(256,precision+64)):
        total=arb(0)
        for k in range(1,H+1):
            residue-=A
            while heap and heap[0][0]==k:
                at,n,event=heappop(heap);residue+=event;heappush(heap,(at+n,n,event))
            residue+=stepmap.get(k,0)
            total+=arb(residue)*residue/(k*(k+1))
        head=total/(arb(D)*D)
        if not head.is_finite():raise ArithmeticError('head replay')
        lo,hi=_enclosure(certificate.get('head',{}).get('enclosure'),meter)
        own_lo,own_hi=_arb_endpoint(head.lower()),_arb_endpoint(head.upper())
        if lo>own_lo or hi<own_hi:raise ValueError('head interval underprices independent replay')
        wlo,whi=_enclosure(certificate.get('norm_squared'),meter)
        if wlo>own_lo or whi<own_hi+tail:raise ValueError('whole interval omits analytic tail range')
    expected={
      'schema':'floor-residual-continuous-norm-v1','program':deepcopy(program),'H':H,'precision':precision,
      'basis':{'definition':'f_n(x)=floor(1/x)/n-floor(1/(n*x)) on0<x<=1; zero x>1',
        'cell':'x in(1/(k+1),1/k]','cell_value':'(k mod n)/n','step_value':'1_(x<=1/q)=1_(k>=q)',
        'residual':'e=1-sum c_n*f_n-sum d_q*1_(x<=1/q) on(0,1]'},
      'lattice':{'D':str(D),'A':str(A),'weights':[{'n':n,'weight':str(w)} for n,w in weights],
        'events':[{'n':n,'value':str(v)} for n,v in events],
        'step_events':[{'q':q,'value':str(v)} for q,v in step_events],
        'residue_formula':'R(k)=D-k*A+sum c_n*D*floor(k/n)-sum_(q<=k)d_q*D',
        'update_formula':'R(k)-R(k-1)=-A+sum_(n|k)c_n*D-sum_(q=k)d_q*D','R_zero':str(D)},
      'head':{'indices':[1,H],'formula':'sum_(1<=k<=H)e(k)^2/(k*(k+1))',
        'enclosure':certificate['head']['enclosure']},
      'tail':{'indices':[H+1,'infinity'],'measure':str(F(1,H+1)),'pointwise_abs_bound':str(M),
        'bound_formula':'M=|1-sum d_q|+sum|c_n|*(n-1)/n; tail<=M^2/(H+1)',
        'every_step_active_on_tail':True,'lower':'0','upper':str(tail),'observations_used_to_infer_tail':False},
      'norm_squared':certificate['norm_squared'],'continuous_integral_domain':'0<x<=1',
      'continuous_global_fixed_program_bound':True,'head_arithmetic':'exact integer residues and Arb interval accumulation',
      'tail_is_analytic_global_bound':True,'float_sign_admission_used':False,
      'coefficient_bit_count':sum(abs(c.numerator).bit_length()+c.denominator.bit_length() for rows in (coeff,steps) for _,c in rows),
      'support':len(coeff)+len(steps),'convergence_as_support_increases_proved':False,
      'actual_source_coefficient_recovery_claimed':False,'RH_proved':False,'RH_refuted':False}
    counts=certificate.get('counts')
    if type(counts) is not dict or set(counts)!={'operations','peak_integer_bits','peak_bytes_estimate'}:
        raise ValueError('counter metadata')
    if any(type(v) is not int or v<0 for v in counts.values()):raise ValueError('counter types')
    expected['counts']=counts
    if not _eq(certificate,expected):raise ValueError('altered norm/tail/domain/scope certificate')
    return {'verified':True,'program':deepcopy(program),'global_fixed_norm_squared_lower':str(max(F(0),lo)),
      'global_fixed_norm_squared_upper':str(whi),'H':H,'independent_precision':max(256,precision+64),
      'tail_upper':str(tail),'all_domain_included':True,'target_zero_guard_available':not steps,
      'display_ball_is_diagnostic_only':True,
      'convergence_proved':False,'RH_proved':False}

def verify_vanishing_forcing_gate(q,b,provider_status='OPEN',meter=None):
    meter=_meter(meter);_int(q,2,(1<<MAX_BITS)-1,'dilation integer>=2')
    bb=_q(b,meter)
    if type(provider_status) is not str or provider_status!='OPEN':
        raise ValueError('only OPEN all-iteration forcing admitted')
    t=bb*bb/q
    admissible=t<1
    young=None if not t or not admissible else (1-t)/(2*t)
    rho=None if not admissible else (F(0) if not t else (1+t)/2)
    return {'verified':True,'admissible':admissible,'q':q,'b':str(bb),
      'contraction_energy_coefficient':None if rho is None else str(rho),
      'young_parameter':None if young is None else str(young),
      'leaf':{'status':'OPEN','condition':'norm(h_(N0*q^j))^2 tends to0 as j tends toinfinity',
        'quantifier':'EVERY eta>0 admits J_eta, EVERY j>=J_eta, one fixed recipe'},
      'conditional_tends_to_zero':admissible,'endpoint_restatement':bb==0,
      'finite_norms_discharge_leaf':False,'convergence_proved':False,'RH_proved':False}

def verify_log_forcing_gate(q,b,A,eta,provider_status='OPEN',meter=None):
    """Conditional convolution price; finite fits cannot license the leaf."""
    meter=_meter(meter);_int(q,2,(1<<MAX_BITS)-1,'dilation integer>=2')
    bb=_q(b,meter);cost=_q(A,meter);exponent=_q(eta,meter)
    if cost<0 or not 0<exponent<=1 or type(provider_status) is not str or provider_status!='OPEN':
        raise ValueError('nonnegative logarithmic cost, eta in(0,1], OPEN provider')
    t=bb*bb/q
    if t>=1:raise ValueError('no admitted dilation contraction')
    young=None if not t else (1-t)/(2*t)
    rho=F(0) if not t else (1+t)/2
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
      'finite_norms_discharge_leaf':False,'convergence_proved':False,'RH_proved':False}
