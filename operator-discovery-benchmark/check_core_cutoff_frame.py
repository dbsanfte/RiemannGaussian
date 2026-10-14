"""Independent polynomial and Abel-moment auditor for cutoff drift frames.

No discovery generator or source archive is imported. Rational rank and
expanded polynomial identities check the whole finite catalogue. Numerical
bounds remain finite observations, with singularities certified only by
exact alias substitution in the frame's sum-of-squares polynomials.
"""
from fractions import Fraction as Q
from math import gcd, lcm
import re
from flint import arb,ctx


def _require(condition,message):
    if not condition:raise ValueError(message)


def _rational(text,meter):
    _require(type(text) is str and 0<len(text)<=1235 and re.fullmatch(r'-?\d+(?:/\d+)?',text) is not None,
             'canonical bounded rational string')
    meter.charge(len(text)+1)
    try:value=Q(text)
    except (ValueError,ZeroDivisionError) as error:raise ValueError('exact rational') from error
    _require(str(value)==text and max(abs(value.numerator).bit_length(),value.denominator.bit_length())<=4096,
             'canonical bounded rational')
    return value


def _integer(value,lower=0,upper=1000000):
    _require(type(value) is int and lower<=value<=upper,'bounded exact integer')
    return value


def _rank(rows,meter):
    """Fraction-free inputs, independent Gauss-Jordan rank calculation."""
    if not rows:return 0
    _require(all(len(row)==len(rows[0]) for row in rows),'rectangular rational matrix')
    matrix=[list(map(Q,row)) for row in rows];pivot=0
    meter.live(len(matrix)*len(matrix[0])*10+4096)
    for col in range(len(matrix[0])):
        found=next((i for i in range(pivot,len(matrix)) if matrix[i][col]),None)
        if found is None:continue
        matrix[pivot],matrix[found]=matrix[found],matrix[pivot]
        scale=matrix[pivot][col]
        matrix[pivot]=[v/scale for v in matrix[pivot]]
        for i,row in enumerate(matrix):
            if i==pivot or not row[col]:continue
            coefficient=row[col]
            matrix[i]=[x-coefficient*y for x,y in zip(row,matrix[pivot])]
            meter.charge(8*len(row))
        pivot+=1;meter.charge(8*len(matrix[0]))
        if pivot==len(matrix):break
    return pivot


def _add(left,right):
    out=left.copy()
    for powers,coefficient in right.items():
        out[powers]=out.get(powers,Q(0))+coefficient
        if not out[powers]:del out[powers]
    return out


def _multiply(left,right,meter):
    out={}
    for p,c in left.items():
        for q,d in right.items():
            powers=tuple(x+y for x,y in zip(p,q));out[powers]=out.get(powers,Q(0))+c*d
            meter.charge(20)
    return {powers:c for powers,c in out.items() if c}


def _linear(coefficients):
    out={}
    dimension=len(coefficients)-1
    for index,coefficient in enumerate(coefficients):
        if coefficient:
            powers=[0]*dimension
            if index:powers[index-1]=1
            out[tuple(powers)]=coefficient
    return out


def _normalized(flat):
    if any(value.denominator!=1 for value in flat):return None
    multiplier=lcm(*(value.denominator for value in flat))
    integers=[value.numerator*(multiplier//value.denominator) for value in flat]
    divisor=0
    for v in integers:divisor=gcd(divisor,abs(v))
    if not divisor:return None
    integers=[v//divisor for v in integers]
    if next(v for v in integers if v)<0:integers=[-v for v in integers]
    return list(map(Q,integers))


def _constraint_rows(dimension,meter):
    # Expand sum_i d_i v_i in generic monomials, rather than nominate edges.
    coefficients={}
    for i in range(dimension):
        for j in range(dimension+1):
            powers=[0]*dimension;powers[i]+=1
            if j:powers[j-1]+=1
            coefficients.setdefault(tuple(powers),[0]*(dimension*(dimension+1)))[i*(dimension+1)+j]+=1
            meter.charge(20)
    return [coefficients[p] for p in sorted(coefficients)]


def _decode_polynomial(terms,dimension,meter):
    _require(type(terms) is list and len(terms)<=1000,'bounded sparse polynomial')
    out={}
    for term in terms:
        _require(type(term) is dict and set(term)=={'monomial','coefficient'},'exact polynomial term schema')
        monomial=term['monomial']
        _require(type(monomial) is list and len(monomial)<=3 and monomial==sorted(monomial) and
                 all(type(i) is int and 0<=i<dimension for i in monomial),'sorted bounded polynomial monomial')
        coefficient=_rational(term['coefficient'],meter)
        powers=tuple(monomial.count(i) for i in range(dimension))
        _require(coefficient!=0 and powers not in out,'unique nonzero polynomial terms')
        out[powers]=coefficient
        meter.charge(10+len(monomial))
    return out


def moments(mu,requests,meter):
    """224-bit full Abel summation of independently verified integer prefixes."""
    _require(ctx.prec==224,'independent checker precision224')
    _require(type(requests) is dict and set(requests)=={'a','b'},'exact requested moment types')
    wanted={}
    for name in ('a','b'):
        cutoffs=requests[name]
        _require(type(cutoffs) is list and cutoffs==sorted(set(cutoffs)) and
                 all(type(n) is int and 1<=n<=1048575 for n in cutoffs),'sorted unique requested cutoffs')
        wanted[name]=set(cutoffs)
    union=wanted['a']|wanted['b']
    _require(bool(union),'nonempty moment requests')
    H=max(union)
    _require(type(mu) is list and len(mu)==H+1 and mu[0]==0 and mu[1]==1 and
             all(type(v) is int and v in (-1,0,1) for v in mu),'complete exact integer source prefix and unit')
    meter.live(12*(H+1)+4096)
    divisors=[0]*(H+1)
    for d in range(1,H+1):
        for n in range(d,H+1,d):divisors[n]+=mu[d];meter.charge(2)
    for n in range(1,H+1):
        _require(divisors[n]==int(n==1),'all integer divisor inverse equations')
        meter.charge(2)
    output=dict(a={},b={},effective_cutoffs={})
    exponents={'a':arb(2)/3,'b':arb(4)/3}
    totals={'a':arb(0),'b':arb(0)};previous_weights={};prefix=0;effective=0
    for n in range(1,H+1):
        # Abel differences use exact M(n-1), including the full unit.
        old_prefix=prefix;prefix+=mu[n]
        if mu[n]:effective=n
        for name in ('a','b'):
            weight=(-exponents[name]*arb(n).log()).exp()
            _require(weight.is_finite(),'finite Abel power')
            if n>1:totals[name]+=old_prefix*(previous_weights[name]-weight)
            previous_weights[name]=weight
            if n in wanted[name]:
                value=totals[name]+prefix*weight
                _require(value.is_finite(),'finite complete moment')
                output[name][str(n)]=value
            meter.charge(500)
        if n in union:output['effective_cutoffs'][str(n)]=effective
        meter.charge(5)
    return output


def _alias_map(aliases,dimension):
    _require(type(aliases) is list and len(aliases)==dimension,'complete cutoff alias list')
    groups={};mapping=[]
    for index,pair in enumerate(aliases):
        _require(type(pair) in (list,tuple) and len(pair)==2 and
                 all(type(v) is int and 1<=v<=1048575 for v in pair),'exact effective cutoff pair')
        mapping.append(groups.setdefault(tuple(pair),index))
    return mapping


def _substitute_aliases(poly,mapping,meter):
    out={};dimension=len(mapping)
    for powers,coefficient in poly.items():
        merged=[0]*dimension
        for i,count in enumerate(powers):merged[mapping[i]]+=count
        key=tuple(merged);out[key]=out.get(key,Q(0))+coefficient
        meter.charge(10+dimension)
    return {p:c for p,c in out.items() if c}


def _evaluate_polynomial(poly,drifts,meter):
    value=arb(0)
    for powers,coefficient in poly.items():
        term=arb(coefficient.numerator)/coefficient.denominator
        for i,count in enumerate(powers):
            if count:term*=drifts[i]**count
            meter.charge(50)
        value+=term;meter.charge(20)
    _require(value.is_finite(),'finite expanded polynomial observable')
    return value


def evaluate(candidate,basis,drifts,aliases,meter):
    """Evaluate the expanded W,S polynomials after exact alias substitution."""
    _require(ctx.prec==224,'independent checker precision224')
    dimension=len(drifts)
    _require(2<=dimension<=5 and all(type(d) is arb and d.is_finite() for d in drifts),'complete finite real drift vector')
    mapping=_alias_map(aliases,dimension)
    for i,j in enumerate(mapping):
        _require(drifts[i].overlaps(drifts[j]),'aliased actual drift intervals overlap')
    weights=[_substitute_aliases(_decode_polynomial(p,dimension,meter),mapping,meter) for p in candidate['weights']]
    _require(len(weights)==dimension,'one complete frame weight per source geometry')
    normalizer=_substitute_aliases(_decode_polynomial(candidate['normalizer'],dimension,meter),mapping,meter)
    zero_forms=True
    for index in candidate['basis_ids']:
        row=basis[index]['sum']
        _require(len(row)==dimension+1,'complete selected SOS linear form')
        linear=_linear([_rational(c,meter) for c in row])
        if _substitute_aliases(linear,mapping,meter):zero_forms=False
    W=[_evaluate_polynomial(poly,drifts,meter) for poly in weights]
    S=_evaluate_polynomial(normalizer,drifts,meter)
    if zero_forms:
        _require(not normalizer and all(not poly for poly in weights),'exact alias-singular frame identities')
        return dict(status='exact_singular',normalizer=arb(0),weights=[arb(0)]*dimension,**{'lambda':None,'K':None})
    if not S>0:
        return dict(status='unresolved_positive',normalizer=S,weights=W,**{'lambda':None,'K':None})
    lambdas=[w/S for w in W];K=sum((v*v for v in lambdas),arb(0))
    _require(K.is_finite() and all(v.is_finite() for v in lambdas),'finite conditioning and weights')
    _require((sum(lambdas,arb(0))-1).contains(0),'numerical affine recovery equation')
    _require(sum((v*d for v,d in zip(lambdas,drifts)),arb(0)).contains(0),'numerical drift cancellation equation')
    meter.charge(500*dimension)
    return dict(status='certified_positive',normalizer=S,weights=W,**{'lambda':lambdas,'K':K})


def check_catalogue(result,meter):
    """Replay the generic coefficient equations and every pooled polynomial."""
    keys={'schema','dimension','constraint_rank','basis','candidates','weak_fact_countermodel','supplied','generated',
          'model_calls','whole_signed_bound_proved','RH_proved'}
    _require(type(result) is dict and set(result)==keys and result.get('schema')=='core-cutoff-frame-v1','exact frame catalogue schema')
    dimension=_integer(result['dimension'],2,5)
    _require(result['weak_fact_countermodel']==dict(drifts=['1']*dimension,normalizer='0',
        scope='upper magnitude bounds alone cannot prove the recovery denominator positive',actual_mobius_counterexample=False),
        'exact weak-fact countermodel and limited scope')
    _require(result['supplied']==['polynomial degree limit','square-and-pool construction','Cauchy recovery rule'] and
             result['generated']==['complete rational nullspace','all pooled expressions','exact signed cancellation'] and
             type(result['model_calls']) is int and result['model_calls']==0, 'supplied language and generated arithmetic scope')
    constraints=_constraint_rows(dimension,meter)
    constraint_rank=_rank(constraints,meter)
    _require(type(result['constraint_rank']) is int and result['constraint_rank']==constraint_rank,'independent nullspace constraint rank')
    nullity=dimension*(dimension+1)-constraint_rank
    basis=result['basis']
    _require(type(basis) is list and len(basis)==nullity,'complete rational nullspace basis')
    decoded=[];flats=[]
    for index,item in enumerate(basis):
        _require(type(item) is dict and set(item)=={'id','vector','sum'} and type(item['id']) is int and item['id']==index,
                 'canonical indexed basis object')
        vector=item['vector']
        _require(type(vector) is list and len(vector)==dimension and
                 all(type(row) is list and len(row)==dimension+1 for row in vector),'degree1 vector polynomial shape')
        rows=[[_rational(c,meter) for c in row] for row in vector]
        flat=[c for row in rows for c in row]
        _require(_normalized(flat)==flat,'primitive integer vector with first nonzero positive')
        _require(all(sum((Q(a)*b for a,b in zip(equation,flat)),Q(0))==0 for equation in constraints),
                 'generic exact nullspace coefficient equations')
        row_sum=[sum((row[j] for row in rows),Q(0)) for j in range(dimension+1)]
        _require(type(item['sum']) is list and [_rational(c,meter) for c in item['sum']]==row_sum,'exact basis coordinate sum')
        decoded.append(([_linear(row) for row in rows],_linear(row_sum)))
        flats.append(flat);meter.charge(30*len(constraints))
    _require(_rank(flats,meter)==nullity,'independent full nullspace basis rank')
    candidates=result['candidates']
    _require(type(candidates) is list and len(candidates)==2**nullity-1,'all nonempty basis subsets')
    for index,candidate in enumerate(candidates):
        keys={'id','basis_ids','active_coordinates','weights','normalizer','sos_linear_forms',
              'normalizer_nonnegative_proved','normalizer_positive_proved'}
        _require(type(candidate) is dict and set(candidate)==keys and type(candidate['id']) is int and candidate['id']==index,
                 'exact indexed frame candidate schema')
        mask=index+1;selected=[j for j in range(nullity) if (mask//2**j)%2]
        _require(candidate['basis_ids']==selected and all(type(i) is int for i in candidate['basis_ids']),
                 'exact exhaustive subset coverage')
        expected_weights=[{} for _ in range(dimension)];expected_S={}
        for j in selected:
            vector,s=decoded[j]
            expected_S=_add(expected_S,_multiply(s,s,meter))
            for i in range(dimension):expected_weights[i]=_add(expected_weights[i],_multiply(s,vector[i],meter))
        _require(type(candidate['weights']) is list and len(candidate['weights'])==dimension,'one weight per source geometry')
        weights=[_decode_polynomial(terms,dimension,meter) for terms in candidate['weights']]
        S=_decode_polynomial(candidate['normalizer'],dimension,meter)
        _require(weights==expected_weights and S==expected_S,'exact expanded square-and-pool polynomials')
        expected_forms=[basis[j]['sum'] for j in selected]
        _require(candidate['sos_linear_forms']==expected_forms and candidate['normalizer_nonnegative_proved'] is True and
                 candidate['normalizer_positive_proved'] is False,'exact SOS witness without an actual positivity assertion')
        active=[i for i,p in enumerate(weights) if p]
        _require(candidate['active_coordinates']==active and all(type(i) is int for i in candidate['active_coordinates']),
                 'complete active source support')
        total={};drift={}
        for i,weight in enumerate(weights):
            total=_add(total,weight)
            coordinate=[0]*dimension;coordinate[i]=1
            drift=_add(drift,_multiply(weight,{tuple(coordinate):Q(1)},meter))
        _require(total==S and not drift,'exact affine recovery and signed drift cancellation')
        # All ones is an exact countermodel to positivity from magnitude bounds.
        _require(sum(S.values(),Q(0))==0 and all(sum(w.values(),Q(0))==0 for w in weights),
                 'weak magnitude-only denominator countermodel')
        meter.charge(200)
    _require(result['whole_signed_bound_proved'] is False and result['RH_proved'] is False,
             'catalogue does not close the signed core or RH')
    return dict(verified=True,dimension=dimension,constraint_rank=constraint_rank,nullity=nullity,
        basis_rank=nullity,candidates=len(candidates),exact_polynomial_identities_verified=True,
        normalizer_nonnegative_proved=True,normalizer_positive_proved=False,
        weak_fact_countermodel_verified=True,whole_signed_bound_proved=False,RH_proved=False)


def drift(polynomial,a,b,Ru,meter):
    """Independently evaluate the retained complete signed moment polynomial."""
    _require(ctx.prec==224 and all(type(v) is arb and v.is_finite() for v in (a,b,Ru)),
             'independent finite source moments and scalar at precision224')
    _require(type(polynomial) is list and 0<len(polynomial)<=1000,'complete nonempty signed drift polynomial')
    decoded={};maximum=[0,0,0]
    for term in polynomial:
        _require(type(term) is dict and set(term)=={'powers','coefficient'},'signed source polynomial term')
        powers=term['powers']
        _require(type(powers) is list and len(powers)==4 and
                 all(type(k) is int and 0<=k<=16 for k in powers),'bounded complete finite moment powers')
        _require(powers[2]==0,'c_U moment is not implemented and must remain explicit')
        key=(powers[0],powers[1],powers[3]);coefficient=_rational(term['coefficient'],meter)
        _require(coefficient!=0 and key not in decoded,'unique nonzero complete source polynomial')
        decoded[key]=coefficient
        maximum=[max(k,m) for k,m in zip(key,maximum)]
    tables=[]
    for variable,degree in zip((a,b,Ru),maximum):
        values=[arb(1)]
        for _ in range(degree):values.append(values[-1]*variable);meter.charge(200)
        tables.append(values)
    total=arb(0)
    for powers,coefficient in sorted(decoded.items()):
        value=arb(coefficient.numerator)/coefficient.denominator
        for index,power in enumerate(powers):value*=tables[index][power]
        total+=value;meter.charge(500)
    _require(total.is_finite(),'finite complete signed source drift')
    return total
