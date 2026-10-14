"""Exact shared-prime contraction and partial arithmetic conditioning.

Bit masks encode prime parity as an algorithmic monomial key, not artifact
hashes. No fitted coefficient or LP enters this polynomial normal form.
"""
from fractions import Fraction as Q

from prime_transfer_algebra_058 import Meter
from mobius_transport_search_059 import floor_power

CONDITIONING_POWERS=('1/3','1/2','2/3','3/4','1')


def prime_masks(B,meter):
    if type(B) is not int or not 1<=B<=65536:raise ValueError('arithmetic radius capacity')
    masks=[0]*(B+1);masks[0]=None;primes=[];spf=[0]*(B+1)
    for p in range(2,B+1):
        meter.charge()
        if spf[p]:continue
        bit=1<<len(primes);primes.append(p)
        for n in range(p,B+1,p):
            if not spf[n]:spf[n]=p
            if masks[n] is not None:masks[n]|=bit
            meter.charge(4)
        for n in range(p*p,B+1,p*p):masks[n]=None;meter.charge()
    return primes,masks


def compile_lift(lift,meter=None):
    meter=Meter() if meter is None else meter
    H,K=lift['H'],lift['K'];B=max(H,K)
    if not 1<=H<=4096 or not 0<=K or H*K>1_000_000:raise OverflowError('quadratic expansion capacity')
    meter.reserve(16*1024**2+2048*H*max(1,K))
    primes,masks=prime_masks(B,meter);endpoints=[];raw_costs=[]
    for e in range(2):
        f=list(map(Q,lift['linear_terms'][e]));G=[list(map(Q,row)) for row in lift['long_kernels_after_fill'][e]]
        rows=[];raw=Q(0)
        for j in range(1,H+1):
            terms={}
            for at,sign in ((j,1),(j+1,-1)):
                for m in range(1,H//at+1):
                    mm=masks[m];meter.charge(8)
                    if mm is None:continue
                    d=at*m-1;a=sign*f[d]
                    if a:terms[mm]=terms.get(mm,Q(0))+a;raw+=abs(a)
                    for ell,v in enumerate(G[d],1):
                        meter.charge(8)
                        if not v or masks[ell] is None:continue
                        key=mm^masks[ell];a=-sign*v
                        terms[key]=terms.get(key,Q(0))+a;raw+=abs(a);meter.charge(20)
            rows.append({key:c for key,c in terms.items() if c})
        endpoints.append(rows);raw_costs.append(str(raw))
    return {'primes':primes,'masks':masks,'rows':endpoints,'raw_term_l1':raw_costs,
            'unconditioned_l1':[str(sum((abs(c) for row in rows for c in row.values()),Q(0))) for rows in endpoints]}


def conditioning_plans(lift,compiled,meter=None,powers=None):
    meter=Meter() if meter is None else meter
    powers=CONDITIONING_POWERS if powers is None else powers
    if type(powers) not in (tuple,list) or len(powers)>256:raise ValueError('finite rational conditioning plan budget')
    B=max(lift['H'],lift['K']);primes=compiled['primes'];plans=[];positions={}
    requests=[('none',[]),('registered',[p for p in lift['parameters']['primes'] if p<=B])]
    for theta in powers:
        # The shared exact-power parser accepts any canonical rational in[0,1]
        # within its bit/work budget. B=1 must still validate that request.
        cutoff=min(B,floor_power(max(B,2),theta,meter))
        requests.append(('prefix_'+theta,[p for p in primes if p<=cutoff]))
    for label,ps in requests:
        key=tuple(ps);meter.charge(len(ps)+10)
        if key in positions:plans[positions[key]]['labels'].append(label)
        else:
            positions[key]=len(plans)
            plans.append({'labels':[label],'primes':ps,'fully_conditioned':ps==primes})
    return plans


def condition(lift,compiled,conditioned_primes,meter=None):
    meter=Meter() if meter is None else meter
    primes=compiled['primes'];positions={p:i for i,p in enumerate(primes)}
    if conditioned_primes!=sorted(set(conditioned_primes)) or any(p not in positions for p in conditioned_primes):
        raise ValueError('canonical actual conditioned primes in query radius')
    known=sum(1<<positions[p] for p in conditioned_primes);keys={0:1}
    def integer_key(mask):
        if mask in keys:return keys[mask]
        n=1;bits=mask
        while bits:
            bit=bits&-bits;n*=primes[bit.bit_length()-1];bits-=bit;meter.charge(8)
        keys[mask]=n;return n
    endpoints=[]
    p,q=lift['parameters']['p'],lift['parameters']['q']
    for ratio,rows in zip((Q(p,q),Q(1)),compiled['rows']):
        new_rows=[];cost=Q(0)
        for j,row in enumerate(rows,1):
            reduced={}
            for key,c in row.items():
                sign=-1 if (key&known).bit_count()%2 else 1
                left=key&~known;reduced[left]=reduced.get(left,Q(0))+sign*c;meter.charge(24)
            terms=sorted((integer_key(key),c) for key,c in reduced.items() if c)
            cost+=sum((abs(c) for _,c in terms),Q(0))
            new_rows.append({'j':j,'terms':[{'index':n,'coefficient':str(c)} for n,c in terms]})
        endpoints.append({'ratio':str(ratio),'rows':new_rows,'l1':str(cost)})
    return {'schema':'mobius-quadratic-contraction-v1',
        **{k:lift[k] for k in ('N','y','H','K')},'conditioned_primes':conditioned_primes,
        'endpoints':endpoints,'budget':str(max(Q(e['l1']) for e in endpoints))}


def sign_diagnostics(cert,meter=None):
    """Exact free-sign witnesses and Fourier L2 guard for a checked certificate.

    These are diagnostics for the formal relaxation. Only the all-minus
    assignment is the actual arithmetic; no random-Mobius claim is used.
    """
    meter=Meter() if meter is None else meter
    degrees={1:0};endpoints=[]
    def degree(index):
        if index in degrees:return degrees[index]
        n=index;d=2;count=0
        while d*d<=n:
            meter.charge(4)
            if n%d==0:n//=d;count+=1
            d+=1
        if n>1:count+=1
        degrees[index]=count;return count
    for endpoint in cert['endpoints']:
        plus=actual=squares=Q(0);max_degree=0
        for row in endpoint['rows']:
            row_plus=row_actual=Q(0)
            for term in row['terms']:
                c=Q(term['coefficient']);d=degree(term['index'])
                row_plus+=c;row_actual+=(-1 if d%2 else 1)*c
                squares+=c*c;max_degree=max(max_degree,d);meter.charge(32)
            plus+=abs(row_plus);actual+=abs(row_actual)
        endpoints.append({'ratio':endpoint['ratio'],'all_free_plus_one_l1':str(plus),
            'actual_all_free_minus_one_l1':str(actual),'fourier_l2_squared':str(squares),
            'maximum_remaining_prime_degree':max_degree})
    return {'endpoints':endpoints,'shared_assignment_across_all_rows':True,
        'free_sign_lower_guards_only':True,'uniform_growth_conclusion':False}


def discover(lift,meter=None,powers=None):
    meter=Meter() if meter is None else meter
    compiled=compile_lift(lift,meter);plans=conditioning_plans(lift,compiled,meter,powers);rows=[]
    for plan in plans:
        cert=condition(lift,compiled,plan['primes'],meter)
        rows.append({'labels':plan['labels'],'fully_conditioned':plan['fully_conditioned'],
            'finite_arithmetic_calibration_only':plan['fully_conditioned'],'certificate':cert})
    return {'N':lift['N'],'y':lift['y'],'H':lift['H'],'K':lift['K'],
        'primes_through_query_radius':compiled['primes'],'raw_term_l1':compiled['raw_term_l1'],
        'unconditioned_l1':compiled['unconditioned_l1'],'candidates':rows,
        'uniform_growth_proved':False,'full_conditioning_ranked_as_uniform_solution':False}
