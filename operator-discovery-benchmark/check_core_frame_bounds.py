"""Independent exact polynomial proof audit for conditional frame bounds.

No discovery generator, arithmetic observations, or numerical source archives
are imported. Sparse exponent-vector arithmetic verifies exact division,
Lagrange sum-of-squares certificates, common-mode recovery and the stated
rational weak-fact countermodels.
"""
from fractions import Fraction as Q
import re


def _require(condition,message):
    if not condition:raise ValueError(message)


def _rational(text,meter):
    _require(type(text) is str and 0<len(text)<=1235 and re.fullmatch(r'-?\d+(?:/\d+)?',text) is not None,
             'canonical bounded rational string')
    meter.charge(len(text)+1)
    try:value=Q(text)
    except (ValueError,ZeroDivisionError) as error:raise ValueError('exact rational') from error
    _require(str(value)==text and max(abs(value.numerator).bit_length(),value.denominator.bit_length())<=4096,
             'canonical bounded exact rational')
    return value


def _integer(value,lower=0,upper=1000000):
    _require(type(value) is int and lower<=value<=upper,'bounded exact integer')
    return value


def _decode(terms,dimension,meter,degree=4):
    _require(type(terms) is list and len(terms)<=10000,'bounded sparse polynomial')
    out={}
    for term in terms:
        _require(type(term) is dict and set(term)=={'monomial','coefficient'},'exact polynomial term schema')
        monomial=term['monomial']
        _require(type(monomial) is list and len(monomial)<=degree and monomial==sorted(monomial) and
                 all(type(i) is int and 0<=i<dimension for i in monomial),'bounded sorted polynomial monomial')
        powers=tuple(monomial.count(i) for i in range(dimension));coefficient=_rational(term['coefficient'],meter)
        _require(coefficient!=0 and powers not in out,'unique nonzero polynomial coefficients')
        out[powers]=coefficient;meter.charge(10+dimension)
    return out


def _add(left,right,scale=Q(1)):
    out=left.copy()
    for p,c in right.items():
        out[p]=out.get(p,Q(0))+scale*c
        if not out[p]:del out[p]
    return out


def _multiply(left,right,meter):
    out={}
    for p,c in left.items():
        for q,d in right.items():
            key=tuple(a+b for a,b in zip(p,q));out[key]=out.get(key,Q(0))+c*d
            meter.charge(20)
    return {p:c for p,c in out.items() if c}


def _linear(coefficients,dimension,meter):
    _require(type(coefficients) is list and len(coefficients)==dimension+1,'complete linear form')
    out={}
    for j,text in enumerate(coefficients):
        coefficient=_rational(text,meter)
        if coefficient:
            p=[0]*dimension
            if j:p[j-1]=1
            out[tuple(p)]=coefficient
    return out


def divide(numerator,denominator,meter):
    """Independent graded-lex single-divisor polynomial long division."""
    _require(bool(denominator),'nonzero polynomial divisor')
    order=lambda p:(sum(p),p)
    leading=max(denominator,key=order);leading_coefficient=denominator[leading]
    work=numerator.copy();quotient={};remainder={}
    while work:
        current=max(work,key=order);coefficient=work[current]
        if all(a>=b for a,b in zip(current,leading)):
            powers=tuple(a-b for a,b in zip(current,leading));factor=coefficient/leading_coefficient
            quotient[powers]=quotient.get(powers,Q(0))+factor
            work=_add(work,_multiply({powers:factor},denominator,meter),Q(-1))
        else:
            remainder[current]=coefficient;del work[current]
        meter.charge(30+len(work))
    return {p:c for p,c in quotient.items() if c},remainder


def _value(poly,point,meter):
    total=Q(0)
    for powers,coefficient in poly.items():
        term=coefficient
        for d,p in zip(point,powers):term*=d**p;meter.charge(5)
        total+=term;meter.charge(5)
    return total


def _basis_forms(basis,dimension,meter):
    _require(type(basis) is list and 0<len(basis)<=10,'bounded saved polynomial basis')
    out=[]
    for position,item in enumerate(basis):
        _require(item['id']==position and type(item['id']) is int,'complete indexed saved basis')
        _require(type(item['vector']) is list and len(item['vector'])==dimension,'basis coordinate vector')
        vector=[_linear(row,dimension,meter) for row in item['vector']]
        summed={}
        for v in vector:summed=_add(summed,v)
        _require(summed==_linear(item['sum'],dimension,meter),'complete saved basis sum')
        relation={}
        for i,v in enumerate(vector):
            p=[0]*dimension;p[i]=1
            relation=_add(relation,_multiply(v,{tuple(p):Q(1)},meter))
        _require(not relation,'generic saved nullspace identity')
        out.append((vector,summed))
    return out


def _frame(candidate,forms,dimension,meter):
    selected=candidate['basis_ids']
    _require(type(selected) is list and bool(selected) and selected==sorted(set(selected)) and
             all(type(i) is int and 0<=i<len(forms) for i in selected),'nonempty saved frame subset')
    W=[{} for _ in range(dimension)];S={}
    for j in selected:
        vector,s=forms[j];S=_add(S,_multiply(s,s,meter))
        for i,v in enumerate(vector):W[i]=_add(W[i],_multiply(s,v,meter))
    _require(type(candidate['weights']) is list and len(candidate['weights'])==dimension and
             [_decode(p,dimension,meter,2) for p in candidate['weights']]==W and
             _decode(candidate['normalizer'],dimension,meter,2)==S and bool(S),
             'complete saved frame and nonzero SOS denominator')
    _require(type(candidate['sos_linear_forms']) is list and len(candidate['sos_linear_forms'])==len(selected) and
             [_linear(row,dimension,meter) for row in candidate['sos_linear_forms']]==[forms[j][1] for j in selected],
             'every saved SOS linear form retained')
    _require(candidate['active_coordinates']==[i for i,w in enumerate(W) if w], 'complete saved active support')
    _require(candidate['normalizer_nonnegative_proved'] is True and candidate['normalizer_positive_proved'] is False,
             'saved SOS does not assert actual positivity')
    return selected,W,S


def _check_certificate(frame,certificate,forms,dimension,meter):
    selected,W,S=_frame(frame,forms,dimension,meter)
    keys={'id','recovery_numerator','division','branch','bound_numerator','slack','sos','common_mode',
          'arithmetic_condition','countermodel','universal_recovery_reduction_proved',
          'uniform_actual_recovery_proved','uniform_actual_residual_proved'}
    _require(type(certificate) is dict and set(certificate)==keys and type(certificate['id']) is int and
             certificate['id']==frame['id'],'exact bound certificate and catalogue binding')
    P={}
    for weight in W:P=_add(P,_multiply(weight,weight,meter))
    _require(_decode(certificate['recovery_numerator'],dimension,meter)==P,'complete quartic recovery numerator')
    quotient,remainder=divide(P,S,meter)
    division=certificate['division']
    _require(type(division) is dict and set(division)=={'quotient','remainder'} and
             _decode(division['quotient'],dimension,meter)==quotient and
             _decode(division['remainder'],dimension,meter)==remainder,'exact independent graded-lex division')
    A={};witnesses=[];squares={}
    if not remainder:
        branch='exact_quotient';B=quotient
    else:
        branch='cauchy_quotient'
        for j in selected:
            for v in forms[j][0]:A=_add(A,_multiply(v,v,meter))
        B=A
        for i in range(dimension):
            for position,j in enumerate(selected):
                vector_j,sj=forms[j]
                for k in selected[position+1:]:
                    vector_k,sk=forms[k]
                    term=_add(_multiply(sj,vector_k[i],meter),_multiply(sk,vector_j[i],meter),Q(-1))
                    if term:
                        witnesses.append((i,j,k,term));squares=_add(squares,_multiply(term,term,meter))
    _require(certificate['branch']==branch and _decode(certificate['bound_numerator'],dimension,meter,2)==B,
             'exact quotient chosen whenever it exists, otherwise full Cauchy numerator')
    slack=_add(_multiply(S,B,meter),P,Q(-1))
    _require(slack==squares and _decode(certificate['slack'],dimension,meter)==slack,
             'complete Lagrange SOS identity or exact quotient identity')
    sos=certificate['sos']
    _require(type(sos) is list and len(sos)==len(witnesses),'every nonzero SOS square exactly once')
    for record,(i,j,k,polynomial) in zip(sos,witnesses):
        _require(type(record) is dict and set(record)=={'coordinate','left','right','polynomial'} and
                 type(record['coordinate']) is int and type(record['left']) is int and type(record['right']) is int and
                 (record['coordinate'],record['left'],record['right'])==(i,j,k) and
                 _decode(record['polynomial'],dimension,meter,2)==polynomial,'exact ordered SOS witness with all crosses')
    common=certificate['common_mode']
    _require(type(common) is dict and set(common)=={'unnormalized_G_coefficient','unnormalized_J_coefficient',
        'unnormalized_paid_coefficients','normalized_G_coefficient','classification','remaining_signed_bound',
        'uniform_signed_control_added'},'exact common-mode expansion schema')
    total={};J={}
    for i,weight in enumerate(W):
        total=_add(total,weight);coordinate=[0]*dimension;coordinate[i]=1
        J=_add(J,_multiply(weight,{tuple(coordinate):Q(-1)},meter))
    _require(total==S and not J and _decode(common['unnormalized_G_coefficient'],dimension,meter,2)==total and
             _decode(common['unnormalized_J_coefficient'],dimension,meter,3)==J,'common-mode coefficient retained and drift cancels')
    _require(type(common['unnormalized_paid_coefficients']) is list and len(common['unnormalized_paid_coefficients'])==dimension and
             [_decode(p,dimension,meter,2) for p in common['unnormalized_paid_coefficients']]==
             [{p:-c for p,c in weight.items()} for weight in W],'all signed paid coefficients retained')
    _require(common['normalized_G_coefficient']=='1' and
             common['classification']=='equivalent_to_full_core_modulo_paid_vector_and_recovery_cost' and
             common['remaining_signed_bound']=='open' and common['uniform_signed_control_added'] is False,
             'exact common-mode equivalence supplies no signed-control proof')
    condition=certificate['arithmetic_condition']
    condition_keys={'positive_denominator','left','right_factor','rho','parameters','quantifier','required','conclusion','status'}
    _require(type(condition) is dict and set(condition)==condition_keys and
             _decode(condition['positive_denominator'],dimension,meter,2)==S and
             _decode(condition['left'],dimension,meter,2)==S and
             _decode(condition['right_factor'],dimension,meter,2)==B,'exact derived quadratic arithmetic condition')
    _require(condition['rho']=='c*(1+log2X)^(-q)' and
             condition['parameters']=='one fixed c>0, one fixed q>=0, one fixed finite dyadic X0' and
             condition['quantifier']=='EVERY dyadic X>=X0, N=4X-1' and condition['required']=='S>0 and S>=rho*B' and
             condition['conclusion']=='K<=c^(-1)*(1+log2X)^q' and condition['status']=='open',
             'cofinal positive-denominator and recovery estimate remain open')
    points=[[Q(i+1) for i in range(dimension)]]+[[Q(int(i==j)) for i in range(dimension)] for j in range(dimension)]
    point=None
    for trial in points:
        trial_S=_value(S,trial,meter);trial_B=_value(B,trial,meter)
        if trial_S>0 and trial_B>0:
            point=trial;Sv=trial_S;Bv=trial_B;break
    _require(point is not None,'nonzero SOS frame has a positive ordered rational countermodel')
    Pv=_value(P,point,meter)
    K=Pv/Sv**2;rho=Sv/(2*Bv);margin=Sv-rho*Bv
    weights=[_value(weight,point,meter)/Sv for weight in W]
    _require(sum(weights,Q(0))==1 and sum((w*d for w,d in zip(weights,point)),Q(0))==0,
             'rational countermodel exact normalized recovery')
    _require(K>0 and K<=1/rho and margin==Sv/2 and margin>0,
             'rational countermodel satisfies sufficient recovery condition')
    countermodel=dict(drifts=[str(d) for d in point],normalizer=str(Sv),numerator=str(Pv),bound_numerator=str(Bv),
        recovery_cost=str(K),rho=str(rho),margin=str(margin),weights=list(map(str,weights)),common_mode_slope='1',
        residual_energy='T^2 for arbitrary real T on a unit abstract Hilbert vector H',source_AST_satisfied=False,
        actual_source_bound_disproved=False,recovery_condition_satisfied=True)
    _require(certificate['countermodel']==countermodel,'exact abstract countermodel with arbitrary unbounded common mode')
    _require(certificate['universal_recovery_reduction_proved'] is True and
             certificate['uniform_actual_recovery_proved'] is False and certificate['uniform_actual_residual_proved'] is False,
             'universal conditional algebra is separate from open source arithmetic')
    meter.charge(100)
    return branch,len(witnesses)


def verify(catalogue,result,meter):
    _require(type(catalogue) is dict and catalogue['schema']=='core-cutoff-frame-v1','saved frame catalogue')
    dimension=_integer(catalogue['dimension'],2,5)
    _require(type(result) is dict and set(result)=={'schema','dimension','certificates','statistics',
        'whole_signed_bound_proved','RH_proved'} and result['schema']=='core-frame-bound-synthesis-v1' and
        type(result['dimension']) is int and result['dimension']==dimension,'bound synthesis schema and dimension')
    _require(result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,'signed arithmetic and RH remain open')
    forms=_basis_forms(catalogue['basis'],dimension,meter)
    frames=catalogue['candidates'];certificates=result['certificates']
    _require(type(frames) is list and len(frames)==2**len(forms)-1 and type(certificates) is list and
             len(certificates)==len(frames),'all saved candidates have exactly one bound certificate')
    exact=0;cauchy=0;squares=0
    for position,(frame,certificate) in enumerate(zip(frames,certificates)):
        _require(type(frame['id']) is int and frame['id']==position and
                 frame['basis_ids']==[j for j in range(len(forms)) if ((position+1)//2**j)%2],
                 'complete unique saved subset and certificate order')
        branch,count=_check_certificate(frame,certificate,forms,dimension,meter)
        exact+=int(branch=='exact_quotient');cauchy+=int(branch=='cauchy_quotient');squares+=count
    statistics=dict(candidates=len(frames),exact_quotients=exact,cauchy_quotients=cauchy,sos_squares=squares)
    _require(result['statistics']==statistics,'exact complete proof-branch accounting')
    meter.live(100*len(forms)+20*len(frames)+4096)
    return dict(verified=True,dimension=dimension,**statistics,common_mode_equivalence_verified=True,
        weak_fact_countermodels_verified=True,uniform_actual_recovery_proved=False,uniform_actual_residual_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)


def _compose(poly,images,variable_count,meter):
    required=[max((powers[i] for powers in poly),default=0) for i in range(len(images))]
    zero=(0,)*variable_count;tables=[]
    for image,degree in zip(images,required):
        powers=[{zero:Q(1)}]
        for _ in range(degree):powers.append(_multiply(powers[-1],image,meter))
        tables.append(powers)
    result={}
    for exponents,coefficient in poly.items():
        term={zero:coefficient}
        for i,degree in enumerate(exponents):
            if degree:term=_multiply(term,tables[i][degree],meter)
        result=_add(result,term)
    return result


def verify_source_conditions(representations,certificates,items,meter):
    """Audit exact substitution into complete shared signed source moments."""
    _require(type(representations) is list and 2<=len(representations)<=5,'complete ordered source geometries')
    dimension=len(representations);geometry_order=[]
    exponents={'a':set(),'b':set()}
    for geometry in representations:
        ident=_integer(geometry['geometry_id']);geometry_order.append(ident)
        for family,key in (('a','alpha'),('b','gamma')):
            r=_rational(geometry[key],meter)
            _require(0<r<1,'strict complete source cutoff exponent')
            exponents[family].add(r)
        _require(geometry['drift']['theta']=='2/3','actual complete drift uses the source kernel power')
    _require(len(set(geometry_order))==dimension,'unique complete source geometry order')
    variables=[];lookup={}
    for family,power in (('a','2/3'),('b','4/3')):
        for r in sorted(exponents[family]):
            exponent=str(r);lookup[family,exponent]=len(variables)
            variables.append(dict(id=len(variables),kind='complete_mobius_moment',family=family,moment_power=power,
                cutoff_exponent=exponent,definition='sum_(1<=n<=floor(N^cutoff_exponent)) mu(n)*n^(-moment_power)',
                unit_and_prime_powers_retained=True))
    ru=len(variables)
    variables.append(dict(id=ru,kind='source_scalar',name='R_u',
        definition='(9/2)*(zeta(4/3)/zeta(2/3)^2-1/zeta(2/3))'))
    variable_count=len(variables);images=[]
    for geometry in representations:
        polynomial=geometry['drift']['polynomial']
        _require(type(polynomial) is list and 0<len(polynomial)<=1000,'complete saved signed source drift')
        image={};seen=set()
        for term in polynomial:
            _require(type(term) is dict and set(term)=={'powers','coefficient'},'complete source drift term')
            powers=term['powers']
            _require(type(powers) is list and len(powers)==4 and
                     all(type(k) is int and 0<=k<=16 for k in powers),'exact nonnegative signed moment powers')
            _require(powers[2]==0,'unimplemented c_U moment may not be dropped')
            coefficient=_rational(term['coefficient'],meter)
            _require(coefficient!=0 and tuple(powers) not in seen,'unique nonzero complete signed drift terms')
            seen.add(tuple(powers));merged=[0]*variable_count
            merged[lookup['a',geometry['alpha']]]+=powers[0]
            merged[lookup['b',geometry['gamma']]]+=powers[1]
            merged[ru]+=powers[3]
            image=_add(image,{tuple(merged):coefficient});meter.charge(30)
        images.append(image)
    _require(type(certificates) is list and type(items) is list and len(certificates)==len(items),
             'every selected certificate receives one complete source condition')
    seen_candidates=set()
    keys={'candidate_id','variables','geometry_order','complete_drift_polynomials','denominator','recovery_bound_numerator',
          'rho','parameters','quantifier','required','common_horizon','all_shared_moments_identified',
          'algebraic_substitution_proved','arithmetic_inequality_proved','status'}
    for certificate,item in zip(certificates,items):
        ident=_integer(certificate['id'])
        _require(ident not in seen_candidates,'unique selected source-bound construction')
        seen_candidates.add(ident)
        _require(type(item) is dict and set(item)==keys and type(item['candidate_id']) is int and item['candidate_id']==ident,
                 'source condition certificate binding')
        condition=certificate['arithmetic_condition']
        _require(condition['status']=='open' and certificate['uniform_actual_recovery_proved'] is False and
                 certificate['uniform_actual_residual_proved'] is False,'source-specific arithmetic remains open')
        S=_decode(condition['left'],dimension,meter,2);B=_decode(certificate['bound_numerator'],dimension,meter,2)
        expected_S=_compose(S,images,variable_count,meter);expected_B=_compose(B,images,variable_count,meter)
        _require(item['variables']==variables and item['geometry_order']==geometry_order and
                 type(item['complete_drift_polynomials']) is list and len(item['complete_drift_polynomials'])==dimension and
                 [_decode(p,variable_count,meter,48) for p in item['complete_drift_polynomials']]==images,
                 'complete shared finite moments, units, source scalar and signed drift images')
        _require(_decode(item['denominator'],variable_count,meter,96)==expected_S and
                 _decode(item['recovery_bound_numerator'],variable_count,meter,96)==expected_B,
                 'exact source-polynomial substitution with all inter-mode cross terms')
        _require(item['rho']==condition['rho'] and item['parameters']==condition['parameters'] and
                 item['quantifier']==condition['quantifier'] and item['required']=='S>0 and S>=rho*B' and
                 item['common_horizon']=='N=4X-1' and item['all_shared_moments_identified'] is True and
                 item['algebraic_substitution_proved'] is True and item['arithmetic_inequality_proved'] is False and
                 item['status']=='open','concrete cofinal arithmetic lemma is open, independently of exact substitution')
    meter.live(100*variable_count+100*len(items)+4096)
    return dict(verified=True,conditions=len(items),moment_variables=variable_count-1,
        geometry_order=geometry_order,shared_moment_aliases_verified=True,complete_signed_substitution_verified=True,
        arithmetic_inequality_proved=False,whole_signed_bound_proved=False,RH_proved=False)
