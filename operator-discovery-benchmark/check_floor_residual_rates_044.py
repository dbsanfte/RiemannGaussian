"""Independent AST log-rate and exact finite-cell obstruction admission.

This checks symbolic source formulas, never finite norm tables or source arrays.
"""
from fractions import Fraction as F
from copy import deepcopy
from flint import arb,ctx

CHANNELS=('mu','liouville','mu_convolution_mu','radical_sign','one',
  'mu_plus_half_liouville','mu_minus_half_liouville')
MAX_BITS=4096

class Meter:
    def __init__(self,cap=50000000):self.cap=cap;self.operations=0
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('rate-check work cap')
        self.operations+=n

def _meter(m):return Meter() if m is None else m

def _q(s,m):
    if type(s) is not str or not 1<=len(s)<=2500:raise ValueError('canonical rational string')
    m.charge(len(s)+1)
    try:v=F(s)
    except (ValueError,ZeroDivisionError):raise ValueError('rational') from None
    if str(v)!=s or max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_BITS:
        raise ValueError('canonical rational bit cap')
    return v

def _positive(s,m):
    v=_q(s,m)
    if v<=0:raise ValueError('strict positive exponent')
    return v

def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _factors(n,m):
    if type(n) is not int or not 1<=n<=4096:raise ValueError('small exact index1..4096')
    result=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1;m.charge(8)
        if e:result.append((p,e))
        p+=1;m.charge(8)
    if n>1:result.append((n,1))
    return result

def arithmetic(channel,n,meter=None):
    meter=_meter(meter)
    if channel not in CHANNELS or type(channel) is not str:raise ValueError('arithmetic channel')
    fac=_factors(n,meter);mu=0 if any(e>1 for _,e in fac) else (-1)**len(fac)
    liouville=(-1)**sum(e for _,e in fac)
    if channel=='mu':return F(mu)
    if channel=='liouville':return F(liouville)
    if channel=='radical_sign':return F((-1)**len(fac))
    if channel=='one':return F(1)
    if channel=='mu_plus_half_liouville':return F(mu)+F(liouville,2)
    if channel=='mu_minus_half_liouville':return F(mu)-F(liouville,2)
    out=1
    for _,e in fac:out*=(-2 if e==1 else 1 if e==2 else 0)
    return F(out)

def _flat():return ('flat',None,{},None)
def _leading(rate,poly):
    poly={key:v for key,v in poly.items() if v}
    return ('leading',rate,poly,None) if poly else ('UNRESOLVED',None,{},str(rate))
def _scale(s,c):
    if not c:return _flat()
    return (s[0],s[1],{key:c*v for key,v in s[2].items()},s[3])
def _add(a,b):
    if a[0]=='flat':return b
    if b[0]=='flat':return a
    if a[0]=='UNRESOLVED' or b[0]=='UNRESOLVED':
        barriers=[F(s[3]) for s in (a,b) if s[0]=='UNRESOLVED']
        known=[s for s in (a,b) if s[0]=='leading']
        if known and known[0][1]<=min(barriers):return known[0]
        return ('UNRESOLVED',None,{},str(min(barriers)))
    rate=min(a[1],b[1]);poly={}
    for s in (a,b):
        if s[1]==rate:
            for key,v in s[2].items():poly[key]=poly.get(key,F(0))+v
    return _leading(rate,poly)

def weight_series(weight,meter=None,depth=0):
    """First correction to limit one; cutoff corrections are log-flat."""
    meter=_meter(meter);meter.charge(20)
    if type(weight) is not dict or depth>6:raise ValueError('bounded weight AST')
    kind=weight.get('kind')
    if kind=='unit' and set(weight)=={'kind'}:return _flat()
    if kind=='taper' and set(weight)=={'kind','coordinate','alpha','gamma'}:
        alpha=_positive(weight['alpha'],meter);gamma=_positive(weight['gamma'],meter)
        if weight['coordinate']=='cutoff':return _flat()
        if weight['coordinate']!='log':raise ValueError('coordinate')
        return _leading(alpha,{(alpha,-alpha):-gamma})
    if kind=='vanishing_twist' and set(weight)=={'kind','rate','level_power'}:
        rate=_positive(weight['rate'],meter);k=weight['level_power']
        if type(k) is not int or not 1<=k<=8:raise ValueError('level power1..8')
        return _leading(F(k),{(F(1),F(0)):-rate})
    if kind=='product' and set(weight)=={'kind','left','right'}:
        return _add(weight_series(weight['left'],meter,depth+1),weight_series(weight['right'],meter,depth+1))
    raise ValueError('unsupported typed weight')

def envelope_series(envelope,meter=None):
    meter=_meter(meter)
    if type(envelope) is not dict:raise ValueError('envelope AST')
    kind=envelope.get('kind')
    if kind=='difference' and set(envelope)=={'kind','left','right'}:
        return _add(weight_series(envelope['left'],meter),_scale(weight_series(envelope['right'],meter),F(-1)))
    if kind in ('power_amplitude','log_amplitude') and set(envelope)=={'kind','power','weight'}:
        power=_positive(envelope['power'],meter);weight_series(envelope['weight'],meter)
        return _flat() if kind=='power_amplitude' else _leading(power,{(F(0),F(0)):F(1)})
    if kind=='moving_band' and set(envelope)=={'kind','cutoff_power','weight'}:
        cutoff=_positive(envelope['cutoff_power'],meter);weight_series(envelope['weight'],meter)
        if cutoff>=1:raise ValueError('sublinear moving cutoff')
        return _flat()
    raise ValueError('unsupported envelope')

def coefficient_series(recipe,index,meter=None):
    meter=_meter(meter)
    if type(recipe) is not dict or set(recipe)!={'id','base','auxiliary'} or type(recipe['id']) is not str or not 1<=len(recipe['id'])<=100:
        raise ValueError('recipe schema')
    if type(index) is not int or not 2<=index<=64:raise ValueError('bounded coefficient index2..64')
    base=weight_series(recipe['base'],meter)
    out=_scale(base,-arithmetic('mu',index,meter))
    aux=recipe['auxiliary']
    if aux is not None:
        if type(aux) is not dict or set(aux)!={'channel','coefficient','envelope'}:raise ValueError('auxiliary schema')
        c=_q(aux['coefficient'],meter)
        if not c:raise ValueError('nonzero auxiliary scalar')
        out=_add(out,_scale(envelope_series(aux['envelope'],meter),c*arithmetic(aux['channel'],index,meter)))
    if index==2 and out[0]=='leading':
        poly={}
        for (a,b),c in out[2].items():poly[(F(0),a+b)]=poly.get((F(0),a+b),F(0))+c
        out=_leading(out[1],poly)
    for (a,b),c in out[2].items():
        for v in (a,b,c):
            bits=max(abs(v.numerator).bit_length(),v.denominator.bit_length())
            if bits>8192:raise ValueError('expansion intermediate bit cap')
            meter.charge(bits+1)
    return out

def verify_witness(witness,meter=None):
    """Check every finite column and the slope annihilating all larger n."""
    meter=_meter(meter)
    keys={'schema','index','cells','constant','denominator','higher_support_slope','identity','norm_lower'}
    if type(witness) is not dict or set(witness)!=keys or witness['schema']!='floor-coefficient-cell-witness-v1':
        raise ValueError('witness schema')
    n=witness['index']
    if type(n) is not int or not 2<=n<=64 or type(witness['cells']) is not list:raise ValueError('witness index')
    alpha={};prior=0
    for row in witness['cells']:
        if type(row) is not dict or set(row)!={'k','alpha'}:raise ValueError('cell row')
        k=row['k'];a=_q(row['alpha'],meter)
        if type(k) is not int or not prior<k<=n or not a:raise ValueError('sorted cell support')
        alpha[k]=a;prior=k
    if sum((a*k for k,a in alpha.items()),F(0))!=0:raise ValueError('higher-support slope')
    for j in range(2,n+1):
        if sum((a*F(k%j,j) for k,a in alpha.items()),F(0))!=-int(j==n):raise ValueError('floor-column elimination')
        meter.charge(20*len(alpha))
    constant=sum(alpha.values(),F(0));den=sum((a*a*k*(k+1) for k,a in alpha.items()),F(0))
    if constant!=arithmetic('mu',n,meter) or _q(witness['constant'],meter)!=constant or den<=0 or _q(witness['denominator'],meter)!=den:
        raise ValueError('unit/Mobius/Cauchy binding')
    if witness['higher_support_slope']!='0' or witness['identity']!='c_index+mu(index)-sum d_q*step_response(q)=sum alpha_k*e(cell k)' or witness['norm_lower']!='(c_index+mu(index)-sum d_q*step_response(q))^2/denominator':
        raise ValueError('witness scope')
    return alpha,den

def _poly_rows(poly):
    return [{'rational':str(c),'log_n_power':str(a),'log_2_power':str(b)} for (a,b),c in sorted(poly.items()) if c]

def _evaluate(poly,index,precision,meter):
    with ctx.workprec(precision):
        total=arb(0);ln=arb(index).log();l2=arb(2).log()
        for (a,b),c in poly.items():
            term=arb(c.numerator)/c.denominator
            for base,power in ((ln,a),(l2,b)):
                if power:term*=((arb(power.numerator)/power.denominator)*base.log()).exp()
            total+=term;meter.charge(precision*8)
        if not total.is_finite():raise ArithmeticError('finite logarithmic coefficient')
        return total

def _endpoint(ball):
    n,e=ball.man_exp();n=int(n);e=int(e)
    return F(n<<e) if e>=0 else F(n,1<<(-e))

def _dyadic(pair,meter):
    if type(pair) is not list or len(pair)!=2 or type(pair[0]) is not str or len(pair[0])>2500 or type(pair[1]) is not int or abs(pair[1])>65536:
        raise ValueError('dyadic endpoints')
    try:n=int(pair[0])
    except ValueError:raise ValueError('integer endpoint') from None
    if str(n)!=pair[0] or abs(n).bit_length()>8192:raise ValueError('canonical bounded endpoint')
    meter.charge(abs(n).bit_length()+abs(pair[1])+1)
    return F(n<<pair[1]) if pair[1]>=0 else F(n,1<<(-pair[1]))

def _license(poly,index,proposal,precision,meter):
    keys={'status','method','sign','precision','enclosure'}
    if type(proposal) is not dict or set(proposal)!=keys or type(proposal['sign']) is not int or proposal['sign'] not in (-1,0,1) or proposal['precision']!=precision or type(proposal['precision']) is not int:
        raise ValueError('nonzero license schema')
    signs={1 if c>0 else -1 for c in poly.values() if c}
    structural=next(iter(signs)) if len(signs)==1 else 0
    if proposal['method']!=('structural_sign' if structural else 'Arb'):raise ValueError('nonzero method binding')
    enclosure=proposal['enclosure'];interval_sign=0
    if enclosure is not None:
        if type(enclosure) is not dict or set(enclosure)!={'ball','lower_dyadic','upper_dyadic'}:
            raise ValueError('full constant enclosure')
        lo=_dyadic(enclosure['lower_dyadic'],meter);hi=_dyadic(enclosure['upper_dyadic'],meter)
        if lo>hi or type(enclosure['ball']) is not str or len(enclosure['ball'])>2500:raise ValueError('constant interval')
        with ctx.workprec(max(256,precision+64)):
            own=_evaluate(poly,index,max(256,precision+64),meter)
            if lo>_endpoint(own.lower()) or hi<_endpoint(own.upper()):raise ValueError('constant interval omits independent value')
            try:display=arb(enclosure['ball'])
            except ValueError:raise ValueError('diagnostic ball') from None
            if not display.is_finite() or _endpoint(display.upper())<lo or _endpoint(display.lower())>hi:
                raise ValueError('nonfinite or disjoint display')
        interval_sign=1 if lo>0 else -1 if hi<0 else 0
        if structural and interval_sign and structural!=interval_sign:raise ValueError('constant sign')
    sign=structural or interval_sign
    if proposal['sign']!=sign or proposal['status']!=('certified' if sign else 'UNRESOLVED'):
        raise ValueError('unproved constant nonzero claim')
    return bool(sign)

def _expansion(series,proposal):
    if type(proposal) is not dict or set(proposal)!={'status','rate','coefficient','cancellation_barrier','reason'}:
        raise ValueError('expansion schema')
    status,rate,poly,barrier=series
    expected={'status':status,'rate':None if rate is None else str(rate),'coefficient':_poly_rows(poly),
      'cancellation_barrier':barrier}
    if not _eq({k:proposal[k] for k in expected},expected):raise ValueError('source AST expansion differs')
    if type(proposal['reason']) is not str or not 1<=len(proposal['reason'])<=250:
        raise ValueError('bounded explanatory reason')

def _candidate(recipe,index,row,precision,meter):
    keys={'index','mu','auxiliary_arithmetic','expansion','coefficient_limit_is_compatible','status','nonzero_license',
      'witness','energy_rate','asymptotic_norm_lower'}
    if type(row) is not dict or set(row)!=keys or row['index']!=index or type(row['index']) is not int:
        raise ValueError('candidate coverage/schema')
    series=coefficient_series(recipe,index,meter);_expansion(series,row['expansion'])
    aux=recipe['auxiliary'];value=None if aux is None else str(arithmetic(aux['channel'],index,meter))
    if type(row['mu']) is not int or row['mu']!=arithmetic('mu',index,meter) or row['auxiliary_arithmetic']!=value or row['coefficient_limit_is_compatible'] is not True:
        raise ValueError('arithmetic/limit source binding')
    alpha,den=verify_witness(row['witness'],meter)
    if row['witness']['index']!=index:raise ValueError('witness target index differs')
    certified=False
    if series[0]=='leading':certified=_license(series[2],index,row['nonzero_license'],precision,meter)
    elif row['nonzero_license'] is not None:raise ValueError('no license on flat/cancelled expansion')
    status='certified_rate_obstruction' if certified else 'OPEN' if series[0]=='flat' else 'UNRESOLVED'
    rate=str(2*series[1]) if certified else None
    lower='liminf L^(2*nu)*norm_squared >= leading_coefficient^2/witness.denominator' if certified else None
    if row['status']!=status or row['energy_rate']!=rate or row['asymptotic_norm_lower']!=lower:
        raise ValueError('unproved/wrong-rate norm obstruction')
    return alpha,rate

def _counter(counts):
    if type(counts) is not dict or set(counts)!={'operations'} or type(counts['operations']) is not int or counts['operations']<0:
        raise ValueError('counter metadata')

def _rule(rule,recipe,meter):
    if type(rule) is not dict or rule.get('family')!=recipe['id'] or type(rule.get('q')) is not int or not 2<=rule['q']<=64:
        raise ValueError('exact recipe/rule binding')
    b=_q(rule.get('b'),meter);bound=rule.get('finite_log_bound')
    if type(bound) is not dict or set(bound)!={'A','eta'} or _q(bound['A'],meter)<=0:
        raise ValueError('positive fixed cost')
    eta=_positive(bound['eta'],meter)
    return b,eta

def verify_recipe(recipe,proposal,rules=None,meter=None):
    meter=_meter(meter);rules=[] if rules is None else rules
    keys={'schema','recipe','scan_indices','scale','precision','target_candidates','strongest_target_rate_obstruction',
      'rule_reviews','necessary_rate_obstruction_only','convergence_status','uniform_upper_bound_proved',
      'additional_norms_evaluated','source_arrays_read','frozen_files_modified','RH_proved','RH_refuted','counts'}
    if type(proposal) is not dict or set(proposal)!=keys or proposal['schema']!='floor-log-rate-review-v1' or not _eq(proposal['recipe'],recipe):
        raise ValueError('recipe review/schema binding')
    indices=proposal['scan_indices'];precision=proposal['precision']
    if type(indices) is not list or len(indices)!=2 or indices[0]!=2 or type(indices[0]) is not int or type(indices[1]) is not int or not 2<=indices[1]<=64:
        raise ValueError('complete bounded witness scan')
    if type(precision) is not int or not 128<=precision<=4096:raise ValueError('precision128..4096')
    flags={'scale':'L=N.bit_length()','necessary_rate_obstruction_only':True,'convergence_status':'OPEN',
      'uniform_upper_bound_proved':False,'additional_norms_evaluated':False,'source_arrays_read':False,
      'frozen_files_modified':False,'RH_proved':False,'RH_refuted':False}
    if not _eq({key:proposal[key] for key in flags},flags):raise ValueError('altered theorem scope')
    rows=proposal['target_candidates']
    if type(rows) is not list or len(rows)!=indices[1]-1:raise ValueError('missing coefficient/witness row')
    alphas={}
    for index,row in zip(range(2,indices[1]+1),rows):alphas[index],_=_candidate(recipe,index,row,precision,meter)
    certified=[row for row in rows if row['energy_rate'] is not None]
    best=min(certified,key=lambda row:(F(row['energy_rate']),row['index'])) if certified else None
    if not _eq(proposal['strongest_target_rate_obstruction'],best):raise ValueError('incorrect target obstruction selection')
    if type(rules) is not list or type(proposal['rule_reviews']) is not list or len(proposal['rule_reviews'])!=len(rules):raise ValueError('rule coverage')
    for rule,review in zip(rules,proposal['rule_reviews']):
        b,eta=_rule(rule,recipe,meter);q=rule['q'];forcings=[]
        for row in rows:
            n=row['index'];response=sum((a for k,a in alphas[n].items() if k>=q),F(0))
            # Check step response against the independent global divisor law.
            if response!=(arithmetic('mu',n//q,meter) if n%q==0 else 0):raise ValueError('indicator recovery law')
            if b and (n%q==0 or response!=0):
                forcings.append({'index':n,'status':'UNRESOLVED',
                  'reason':'divisible forcing index/parent coefficient not compiled','step_response':str(response)})
                continue
            rejected=row['energy_rate'] is not None and eta>F(row['energy_rate'])
            forcings.append({'index':n,'status':'analytically_refuted' if rejected else 'UNRESOLVED' if row['status']=='UNRESOLVED' else 'OPEN',
              'energy_rate':row['energy_rate'],'declared_eta':str(eta),'step_response':str(response),'candidate':row,
              'gap_binding':'child coefficient error at qN; parent floor and indicator contributions vanish' if b else 'b0 forcing is child residual',
              'child_scale_equivalence':'L(qN)/L(N)->1','strict_rejection':rejected})
        rejections=[row for row in forcings if row.get('strict_rejection')]
        strongest=min(rejections,key=lambda row:(F(row['energy_rate']),row['index'])) if rejections else None
        expected={'rule':deepcopy(rule),'status':'analytically_refuted' if strongest else 'OPEN',
          'strongest_rejection':strongest,'forcing_candidates':forcings,
          'strict_eta_rejections':[{'index':row['index'],'energy_rate':row['energy_rate']} for row in rejections],
          'equality_or_smaller_eta_proved':False}
        if not _eq(review,expected):raise ValueError('changed signed forcing/rate/boundary claim')
    _counter(proposal['counts'])
    return {'verified':True,'family':recipe['id'],'target_rate':None if best is None else best['energy_rate'],
      'refuted_rule_count':sum(r['status']=='analytically_refuted' for r in proposal['rule_reviews']),
      'necessary_rate_obstruction_only':True,'convergence_proved':False,'RH_proved':False,'RH_refuted':False}

def verify(selected,proposal,meter=None):
    meter=_meter(meter)
    if type(selected) is not dict or set(selected)!={'recipes','rules'} or type(selected['recipes']) is not list or type(selected['rules']) is not list:
        raise ValueError('selected recipe/rule object')
    if len(selected['recipes'])>10000 or len(selected['rules'])>10000:raise ValueError('selected size cap')
    recipes={}
    for recipe in selected['recipes']:
        coefficient_series(recipe,2,meter)
        if recipe['id'] in recipes:raise ValueError('duplicate recipe identity')
        recipes[recipe['id']]=recipe
    grouped={id:[] for id in recipes};identities=set()
    for rule in selected['rules']:
        if type(rule) is not dict or rule.get('family') not in recipes:raise ValueError('missing source recipe')
        _rule(rule,recipes[rule['family']],meter)
        identity=(rule['family'],rule['q'],rule['b'],rule.get('stratum'))
        if type(rule.get('stratum')) not in (str,type(None)):raise ValueError('bounded rule identity stratum')
        if identity in identities:raise ValueError('duplicate rule identity')
        identities.add(identity);grouped[rule['family']].append(rule)
    if any(not rules for rules in grouped.values()):raise ValueError('missing declared rule')
    keys={'schema','reviews','additional_norms_evaluated','source_arrays_read','convergence_status','RH_proved','RH_refuted','counts'}
    if type(proposal) is not dict or set(proposal)!=keys or proposal['schema']!='floor-selected-log-rate-review-v1' or type(proposal['reviews']) is not list or len(proposal['reviews'])!=len(recipes):
        raise ValueError('selected review coverage/schema')
    results=[]
    for (id,recipe),review in zip(recipes.items(),proposal['reviews']):
        results.append(verify_recipe(recipe,review,grouped[id],meter))
    flags={'additional_norms_evaluated':False,'source_arrays_read':False,'convergence_status':'OPEN','RH_proved':False,'RH_refuted':False}
    if not _eq({key:proposal[key] for key in flags},flags):raise ValueError('selected proof scope')
    _counter(proposal['counts'])
    return {'verified':True,'recipes_verified':len(results),'rules_verified':len(identities),
      'rate_refuted_rules':sum(row['refuted_rule_count'] for row in results),
      'convergence_proved':False,'RH_proved':False,'RH_refuted':False}

def verify_candidate(recipe,index,candidate,precision=192,meter=None):
    meter=_meter(meter)
    if type(precision) is not int or not 128<=precision<=4096:raise ValueError('precision128..4096')
    _,rate=_candidate(recipe,index,candidate,precision,meter)
    return {'verified':True,'index':index,'energy_rate':rate,'necessary_obstruction_only':True,
      'convergence_proved':False,'RH_proved':False,'RH_refuted':False}

def verify_frontier(recipes,eta_values,proposal,max_index=16,precision=192,meter=None):
    """Replay each emitted witness; absent witnesses do not prove rate validity.

    This compressed format does not contain the full scan. Its displayed
    strongest witness is admitted as a supplied bound, not as an optimality
    claim over omitted witnesses.
    """
    meter=_meter(meter)
    if type(recipes) is not list or len(recipes)>10000 or type(eta_values) is not list or not eta_values or type(max_index) is not int or not 2<=max_index<=64 or type(precision) is not int or not 128<=precision<=4096:
        raise ValueError('bounded typed frontier inputs')
    ids=set()
    for recipe in recipes:
        coefficient_series(recipe,2,meter)
        if recipe['id'] in ids:raise ValueError('duplicate recipe identity')
        ids.add(recipe['id'])
    exponents=[_positive(eta,meter) for eta in eta_values]
    if len(set(exponents))!=len(exponents):raise ValueError('distinct canonical eta values')
    keys={'schema','rows','eta_values','necessary_rate_obstruction_only','additional_norms_evaluated',
      'source_arrays_read','convergence_status','RH_proved','RH_refuted','counts'}
    if type(proposal) is not dict or set(proposal)!=keys or proposal['schema']!='floor-log-rate-frontier-v1' or not _eq(proposal['eta_values'],eta_values) or type(proposal['rows']) is not list or len(proposal['rows'])!=len(recipes):
        raise ValueError('frontier coverage/eta binding')
    licensed=0;refuted=0
    for recipe,row in zip(recipes,proposal['rows']):
        if type(row) is not dict or set(row)!={'recipe','strongest_target_rate_obstruction','refuted_etas','OPEN_etas','convergence_status'} or not _eq(row['recipe'],recipe):
            raise ValueError('frontier source/row binding')
        candidate=row['strongest_target_rate_obstruction'];rate=None
        if candidate is not None:
            if type(candidate) is not dict or type(candidate.get('index')) is not int or not 2<=candidate['index']<=max_index:
                raise ValueError('bounded supplied witness index')
            _,rate=_candidate(recipe,candidate['index'],candidate,precision,meter)
            if rate is None:raise ValueError('frontier obstruction requires certified nonzero rate')
            rate=F(rate);licensed+=1
        bad=[eta for eta,power in zip(eta_values,exponents) if rate is not None and power>rate]
        remaining=[eta for eta,power in zip(eta_values,exponents) if rate is None or power<=rate]
        if not _eq(row['refuted_etas'],bad) or not _eq(row['OPEN_etas'],remaining) or row['convergence_status']!='OPEN':
            raise ValueError('incorrect strict rate partition/closure claim')
        refuted+=len(bad)
    flags={'necessary_rate_obstruction_only':True,'additional_norms_evaluated':False,'source_arrays_read':False,
      'convergence_status':'OPEN','RH_proved':False,'RH_refuted':False}
    if not _eq({key:proposal[key] for key in flags},flags):raise ValueError('frontier scope')
    _counter(proposal['counts'])
    return {'verified':True,'recipes_verified':len(recipes),'supplied_obstructions_licensed':licensed,
      'strict_rate_pairs_refuted':refuted,'omitted_witness_scan_optimality_verified':False,
      'OPEN_means_no_obstruction_supplied_or_licensed_at_this_rate':True,
      'convergence_proved':False,'RH_proved':False,'RH_refuted':False}
