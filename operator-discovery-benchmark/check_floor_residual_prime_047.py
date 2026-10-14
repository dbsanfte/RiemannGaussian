"""Independent finite prime pairing with ordinary Mobius and exact profiles.

The finite supplied rational profile layer is a premise, not a source limit or
uniform norm proof. No new producer imports or source/norm archive reads.
"""
from fractions import Fraction as Q
import heapq
import math
import re

class Meter:
    def __init__(self,cap=50000000):self.cap=cap;self.operations=0
    def charge(self,n=1):
        if type(n) is not int or n<0 or n>self.cap-self.operations:raise OverflowError('prime construction work cap')
        self.operations+=n

def _meter(m):return Meter() if m is None else m

def _integer(text,m):
    if not re.fullmatch(r'(?:0|[1-9][0-9]*|-[1-9][0-9]*)',text):raise ValueError('canonical decimal integer')
    negative=text.startswith('-');digits=text[1:] if negative else text
    value=0
    for pos in range(0,len(digits),18):
        chunk=digits[pos:pos+18];value=value*10**len(chunk)+int(chunk);m.charge(len(chunk)+1)
    return -value if negative else value

def _decimal(value):
    if abs(value).bit_length()<12000:return str(value)
    negative=value<0;value=abs(value);chunks=[]
    while value:
        value,chunk=divmod(value,10**18);chunks.append(chunk)
    text=str(chunks[-1])+''.join(str(c).zfill(18) for c in reversed(chunks[:-1]))
    return '-'+text if negative else text

def _text(value):
    value=Q(value);numerator=_decimal(value.numerator)
    return numerator if value.denominator==1 else numerator+'/'+_decimal(value.denominator)

def _rational(s,m,bits=4096):
    if type(s) is not str or not 1<=len(s)<=2*bits:raise ValueError('canonical finite rational text')
    parts=s.split('/')
    if len(parts) not in (1,2):raise ValueError('rational')
    numerator=_integer(parts[0],m);denominator=_integer(parts[1],m) if len(parts)==2 else 1
    if denominator<=0:raise ValueError('positive rational denominator')
    if max(abs(numerator).bit_length(),denominator.bit_length())>bits:raise ValueError('rational input bits')
    value=Q(numerator,denominator)
    if _text(value)!=s:raise ValueError('canonical rational input')
    m.charge(len(s)+1);return value

def _bounded(v,m,bits_cap=32768):
    bits=max(abs(v.numerator).bit_length(),v.denominator.bit_length())
    if bits>bits_cap:raise ValueError('finite intermediate bit cap')
    m.charge(bits+1);return v

def _add(a,b,m):return _bounded(a+b,m)
def _mul(a,b,m):return _bounded(a*b,m)
def _eq(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(_eq(a[k],b[k]) for k in a)
    if type(a) is list:return len(a)==len(b) and all(_eq(x,y) for x,y in zip(a,b))
    return a==b

def _factor(n,m):
    rows=[];p=2;remainder=n
    while p*p<=remainder:
        e=0
        while remainder%p==0:remainder//=p;e+=1;m.charge(8)
        if e:rows.append((p,e))
        p+=1;m.charge(8)
    if remainder>1:rows.append((remainder,1))
    return rows

def _request(request,m):
    if type(request) is not dict or set(request)!={'prime','parent_support','parent_values','child_values'}:raise ValueError('exact prime/profile request')
    p,N=request['prime'],request['parent_support']
    if type(p) is not int or type(N) is not int or p<2 or not 1<=N<=3072 or p*N>4096:raise ValueError('finite integer prime/support domain')
    if _factor(p,m)!=[(p,1)]:raise ValueError('actual ordinary prime required')
    arrays=[]
    for key,length in (('parent_values',N),('child_values',p*N)):
        rows=request[key]
        if type(rows) is not list or len(rows)!=length:raise ValueError('complete finite profiles including unit')
        values=[Q(0)]+[_rational(v,m) for v in rows]
        if values[1]!=1:raise ValueError('source profile unit must equal one')
        arrays.append(values)
    lattice=1
    for v in arrays[0][1:]+arrays[1][1:]:
        lattice=math.lcm(lattice,v.denominator);m.charge(lattice.bit_length())
        if lattice.bit_length()>8192:raise ValueError('input profile common lattice bit cap')
    estimated=(p*N+N+1)*(16384+32*((lattice.bit_length()+4096+7)//8))
    if estimated>4*1024**3:raise OverflowError('prospective prime construction memory cap')
    factors=[[]]+[_factor(n,m) for n in range(1,p*N+1)]
    mu=[0]+[0 if any(e>1 for _,e in fac) else (-1)**len(fac) for fac in factors[1:]]
    return p,N,arrays[0],arrays[1],factors,mu

# Internally a vector is (constant, floor coefficient dict, indicator dict),
# representing C*chi - sum c_n*f_n - sum d_q*I_q.
def _vector(C=0,coeff=None,steps=None):return Q(C),{} if coeff is None else coeff.copy(),{} if steps is None else steps.copy()

def _scale(vector,a,m):
    C,c,d=vector
    return _mul(C,a,m),{n:_mul(v,a,m) for n,v in c.items() if v*a},{q:_mul(v,a,m) for q,v in d.items() if v*a}

def _plus(left,right,m):
    out=[]
    for x,y in zip(left[1:],right[1:]):
        z=x.copy()
        for n,v in y.items():z[n]=_add(z.get(n,Q(0)),v,m)
        out.append({n:v for n,v in z.items() if v})
    return _add(left[0],right[0],m),out[0],out[1]

def _sum(vectors,m):
    value=_vector()
    for v in vectors:value=_plus(value,v,m)
    return value

def _dilate(vector,p,m):
    C,c,d=vector;floors={};steps={p:-C} if C else {}
    for n,v in c.items():
        floors[p*n]=_add(floors.get(p*n,Q(0)),v,m)
        floors[p]=_add(floors.get(p,Q(0)),-v/n,m)
    for q,v in d.items():steps[p*q]=_add(steps.get(p*q,Q(0)),v,m)
    return _vector(0,{n:v for n,v in floors.items() if v},{q:v for q,v in steps.items() if v})

def _target(values,mu):return _vector(1,{n:-mu[n]*values[n] for n in range(2,len(values)) if mu[n]*values[n]})

def _coprime(values,mu,p):return _vector(0,{n:-mu[n]*values[n] for n in range(2,len(values)) if n%p and mu[n]*values[n]})

def _harmonic(values,mu,m,coprime=None):
    value=Q(0)
    for n in range(1,len(values)):
        if coprime is None or n%coprime:value=_add(value,mu[n]*values[n]/n,m)
    return value

def _decode(program,m):
    if type(program) is not dict or set(program)!={'id','constant','coefficients','steps'} or type(program['id']) is not str or not 1<=len(program['id'])<=256:
        raise ValueError('exact signed-vector schema')
    C=_rational(program['constant'],m,32768);vectors=[]
    if type(program['coefficients']) is not list or type(program['steps']) is not list or len(program['coefficients'])+len(program['steps'])>3072:
        raise ValueError('signed support cap')
    for key,index in (('coefficients','n'),('steps','q')):
        prior=1;vector={}
        for row in program[key]:
            if type(row) is not dict or set(row)!={index,'value'}:raise ValueError('signed coefficient row')
            n=row[index];v=_rational(row['value'],m,32768)
            if type(n) is not int or not prior<n<=4096 or not v:raise ValueError('sorted nonzero signed support')
            vector[n]=v;prior=n
        vectors.append(vector)
    return _vector(C,*vectors)

def _bind(program,expected,m):
    if _decode(program,m)!=expected:raise ValueError('wrong full signed vector, unit or auxiliary')

def _cell(vector,k,m):
    C,c,d=vector;value=C
    for n,v in c.items():value=_add(value,-v*Q(k%n,n),m)
    for q,v in d.items():
        if k>=q:value=_add(value,-v,m)
    return value

def _reconstruct(request,m):
    p,N,U,V,factors,mu=_request(request,m)
    parent=_target(U,mu);child=_target(V,mu)
    original=_plus(child,_dilate(parent,p,m),m)
    Vp=[Q(0)]+[V[p*n] for n in range(1,N+1)]
    Up=[Q(0)]+[U[p*n] for n in range(1,N//p+1)]
    diff=[Q(0)]+[_add(U[n],-Vp[n],m) for n in range(1,N+1)]
    S_U=_harmonic(U,mu,m);T_Vp=_harmonic(Vp,mu,m,p);T_Up=_harmonic(Up,mu,m,p)
    fp=_vector(0,{p:Q(1)})
    blocks=[_vector(1,steps={p:Q(-1)}),_coprime(V,mu,p),
      _dilate(_coprime(diff,mu,p),p,m),_scale(_dilate(_coprime(Up,mu,p),p*p,m),Q(-1),m),
      _scale(fp,T_Vp,m),_scale(_dilate(fp,p,m),T_Up,m)]
    if _sum(blocks,m)!=original:raise ArithmeticError('independent prime split reconstruction failed')
    p_adic=[]
    for n in range(1,p*N+1):
        valuation=0;free=n
        while free%p==0:free//=p;valuation+=1;m.charge(5)
        childterm=_mul(Q(mu[n]),V[n],m)
        parentterm=_mul(Q(mu[n//p]),U[n//p],m) if n%p==0 and n//p<=N else Q(0)
        value=_add(childterm,parentterm,m)
        # Check the complete all-valuation prime law, separately from addition.
        if valuation==0:law=mu[free]*V[free]
        elif valuation==1:law=mu[free]*(U[free]-V[p*free])
        elif valuation==2:law=-mu[free]*U[p*free]
        else:law=Q(0)
        if value!=law:raise ArithmeticError('ordinary Mobius prime law replay')
        p_adic.append({'n':n,'valuation':valuation,'prime_free_part':free,
          'child_term':_text(childterm),'parent_term':_text(parentterm),'value':_text(value)})
    lam=V[p];Qvalues=None;Qprogram=None
    if lam:
        Qvalues=[Q(0)]+[_bounded(Vp[n]/lam,m) for n in range(1,N+1)]
        if Qvalues[1]!=1:raise ArithmeticError('normalized parent unit')
        Qprogram=_target(Qvalues,mu)
    direct=_vector(lam,{n:-mu[n]*Vp[n] for n in range(2,N+1) if mu[n]*Vp[n]})
    matched=_plus(child,_dilate(direct,p,m),m)
    if lam and direct!=_scale(Qprogram,lam,m):raise ArithmeticError('direct versus normalized source')
    Vpp=[Q(0)]+[V[p*p*n] for n in range(1,N//p+1)]
    T_Vpp=_harmonic(Vpp,mu,m,p)
    matchedblocks=[_vector(1,steps={p:-lam} if lam else {}),_coprime(V,mu,p),
      _scale(_dilate(_coprime(Vpp,mu,p),p*p,m),Q(-1),m),
      _scale(fp,T_Vp,m),_scale(_dilate(fp,p,m),T_Vpp,m)]
    if _sum(matchedblocks,m)!=matched:raise ArithmeticError('matched square/normalizer reconstruction')
    conversion=_dilate(_vector(1-lam,{n:-mu[n]*(U[n]-Vp[n]) for n in range(2,N+1) if mu[n]*(U[n]-Vp[n])}),p,m)
    if _plus(matched,conversion,m)!=original:raise ArithmeticError('original forcing recovery failed')
    return {'p':p,'N':N,'U':U,'V':V,'mu':mu,'factors':factors,
      'parent':parent,'child':child,'original':original,'split_blocks':blocks,'p_adic':p_adic,
      'S_U':S_U,'T_Vp':T_Vp,'T_Up':T_Up,'lambda':lam,'Qvalues':Qvalues,
      'Qprogram':Qprogram,'direct':direct,'matched':matched,'matched_blocks':matchedblocks,
      'T_Vpp':T_Vpp,'conversion':conversion}


def _fields(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise ValueError('exact certificate fields required')

def _expect(obj,expected):
    if not _eq(obj,expected):raise ValueError('certificate binding, rule or scope mismatch')

def _counts(obj):
    names=('operations','sieve_updates','rational_operations','cell_rows','program_columns',
           'max_rational_bits','input_lattice_bits','estimated_peak_bytes')
    _fields(obj,names)
    if any(type(v) is not int or not 0<=v<2**63 for v in obj.values()):raise ValueError('bounded diagnostic counts')
    if obj['max_rational_bits']>400000 or obj['input_lattice_bits']>8192 or obj['estimated_peak_bytes']>4*1024**3:
        raise ValueError('diagnostic resource limits')

def _mu_rows(context):
    return {'kind':'ordinary-mobius-factorization','rows':[
        {'n':n,'factors':[{'prime':p,'exponent':e} for p,e in context['factors'][n]],'mu':context['mu'][n]}
        for n in range(1,len(context['mu']))]}

def _blocks(rows,labels,vectors,m):
    if type(rows) is not list or len(rows)!=len(labels):raise ValueError('complete signed block partition')
    for row,label,vector in zip(rows,labels,vectors):
        _fields(row,('label','program'));_expect(row['label'],label);_bind(row['program'],vector,m)

def _identity(obj,name,left,right,m):
    _fields(obj,('name','left','right','difference','holds','comparison'))
    _expect(obj['name'],name);_bind(obj['left'],left,m);_bind(obj['right'],right,m)
    difference=_plus(left,_scale(right,Q(-1),m),m)
    if difference!=_vector():raise ArithmeticError('nonzero independent identity')
    _bind(obj['difference'],difference,m);_expect(obj['holds'],True)
    _expect(obj['comparison'],'constant and every signed floor/indicator column')

def verify_prime_construction(request,certificate,meter=None):
    """Admit finite prime algebra only; supplied scalar profiles remain premises."""
    m=_meter(meter);c=_reconstruct(request,m)
    _fields(certificate,('schema','source_request','supplied_values_independently_source_verified',
        'mu_certificate','parent_program','child_program','original_forcing','profile_scalar_sums',
        'prime_split','p_adic_source_coefficients','matched','identities','identity_only',
        'global_bound_status','norm_convergence_status','RH_proved','RH_refuted','counts'))
    for key,value in {'schema':'floor-prime-construction-v1','source_request':request,
        'supplied_values_independently_source_verified':False,'identity_only':True,
        'global_bound_status':'OPEN','norm_convergence_status':'OPEN','RH_proved':False,'RH_refuted':False}.items():
        _expect(certificate[key],value)
    _counts(certificate['counts']);_expect(certificate['mu_certificate'],_mu_rows(c))
    for field,key in (('parent_program','parent'),('child_program','child'),('original_forcing','original')):
        _bind(certificate[field],c[key],m)
    _expect(certificate['profile_scalar_sums'],{
        'parent_harmonic':_text(c['S_U']),'child_shift_coprime':_text(c['T_Vp']),
        'square_parent_shift_coprime':_text(c['T_Up'])})
    split=certificate['prime_split'];_fields(split,('blocks','sum','identity'))
    _blocks(split['blocks'],('unit_and_indicator','coprime_child','dilated_coprime_profile_difference',
        'square_dilated_coprime_parent','scalar_child_shift','scalar_square_parent_shift'),c['split_blocks'],m)
    _bind(split['sum'],c['original'],m)
    _identity(split['identity'],'prime_split_equals_original',c['original'],c['original'],m)
    _expect(certificate['p_adic_source_coefficients'],c['p_adic'])
    matched=certificate['matched'];_fields(matched,('status','lambda','normalized_parent_values',
        'parent_program','direct_parent_program','program','blocks','sum','conversion_auxiliary',
        'cancelled_valuation_one','square_child_shift_coprime_scalar','range_or_contraction_proved','reason'))
    lam=c['lambda'];_expect(matched['lambda'],_text(lam))
    _expect(matched['status'],'available' if lam else 'unmatched_only')
    _expect(matched['range_or_contraction_proved'],False)
    _expect(matched['reason'],'normalized parent available' if lam else
        'normalization undefined at lambda0; division-free matched and conversion vectors retained')
    _expect(matched['normalized_parent_values'],[_text(v) for v in c['Qvalues'][1:]] if lam else None)
    if lam:_bind(matched['parent_program'],c['Qprogram'],m)
    else:_expect(matched['parent_program'],None)
    for field,key in (('direct_parent_program','direct'),('program','matched'),('sum','matched'),
                      ('conversion_auxiliary','conversion')):_bind(matched[field],c[key],m)
    _blocks(matched['blocks'],('matched_unit_and_indicator','coprime_child','square_dilated_shifted_child',
        'scalar_child_shift','scalar_square_child_shift'),c['matched_blocks'],m)
    _expect(matched['square_child_shift_coprime_scalar'],_text(c['T_Vpp']))
    cancelled=[]
    for n in range(1,c['N']+1):
        if n%c['p']:
            val=_mul(Q(c['mu'][n]),c['V'][c['p']*n],m)
            cancelled.append({'prime_free_index':n,'source_index':c['p']*n,
                'child_term':_text(-val),'parent_term':_text(val),'value':'0'})
    _expect(matched['cancelled_valuation_one'],cancelled)
    specs=[('prime_split_equals_original',c['original'],c['original']),
           ('matched_split_equals_forcing',c['matched'],c['matched'])]
    if lam:specs.append(('direct_parent_equals_scaled_normalized_parent',c['direct'],c['direct']))
    specs.append(('matched_plus_conversion_equals_original',c['original'],c['original']))
    identities=certificate['identities']
    if type(identities) is not list or len(identities)!=len(specs):raise ValueError('complete exact identity list')
    for row,spec in zip(identities,specs):_identity(row,*spec,m)
    return {'verified':True,'identity_only':True,'prime':c['p'],'parent_support':c['N'],
        'matched_normalization_available':bool(lam),'division_free_matched_verified':True,
        'all_valuations_and_units_retained':True,'supplied_values_independently_source_verified':False,
        'global_bound_proved':False,'norm_convergence_proved':False,'RH_proved':False,'RH_refuted':False,
        'limits':{'input_bits':4096,'common_lattice_bits':8192,'result_bits':32768,
                  'block_energy_bits':400000,'max_index':4096,'max_parent_support':3072}}


def _divisor_stream(values,mu,end,m):
    """Heap events independently retain the complete finite divisor source."""
    heap=[(n,n,_mul(Q(mu[n]),values[n],m)) for n in range(1,min(end,len(values)-1)+1) if mu[n]*values[n]]
    heapq.heapify(heap);divisors=[Q(0)]*(end+1);prefix=[Q(0)]*(end+1)
    for k in range(1,end+1):
        total=Q(0)
        while heap and heap[0][0]==k:
            _,step,value=heapq.heappop(heap);total=_add(total,value,m);m.charge(1+len(heap).bit_length())
            if k+step<=end:heapq.heappush(heap,(k+step,step,value))
        divisors[k]=total;prefix[k]=_add(prefix[k-1],total,m)
    return divisors,prefix

def verify_cell_energy(request,certificate,meter=None):
    """Check a finite cell block; no unobserved tail or whole-norm inference."""
    m=_meter(meter);c=_reconstruct(request,m)
    _fields(certificate,('schema','source_request','supplied_values_independently_source_verified',
        'mu_certificate','K','end_exclusive','source_harmonic_sums','cells','energy','weighted_norm','domain',
        'unobserved_cells_or_tails_inferred','whole_norm_proved','global_bound_status','RH_proved','RH_refuted','counts'))
    K=certificate['K']
    if type(K) is not int or not 1<=K<=65536 or K&(K-1):raise ValueError('dyadic finite cell block')
    for key,val in {'schema':'floor-prime-cell-energy-v1','source_request':request,
        'supplied_values_independently_source_verified':False,'end_exclusive':2*K,
        'domain':'cells K..2K-1, x in (1/(2K),1/K]','unobserved_cells_or_tails_inferred':False,
        'whole_norm_proved':False,'global_bound_status':'OPEN','RH_proved':False,'RH_refuted':False}.items():
        _expect(certificate[key],val)
    _counts(certificate['counts']);_expect(certificate['mu_certificate'],_mu_rows(c))
    SV=_harmonic(c['V'],c['mu'],m);SU=c['S_U']
    _expect(certificate['source_harmonic_sums'],{'child':_text(SV),'parent':_text(SU)})
    end=2*K-1;parentend=end//c['p']
    # Preflight the source scalar sizes and prospective exact prefix/output
    # tables; the two aggregate energies have a separate 400000-bit ceiling.
    sourcebits=max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in c['U']+c['V'])
    scalarbits=max(sourcebits+end.bit_length()+16,abs(SV.numerator).bit_length()+SV.denominator.bit_length()+end.bit_length()+4,
                   abs(SU.numerator).bit_length()+SU.denominator.bit_length()+end.bit_length()+4)
    scalarbytes=256+8*((scalarbits+7)//8)
    prospective=4*(end+parentend+2)*scalarbytes+K*(1024+20*scalarbytes)+2*((400000+7)//8)
    if prospective>4*1024**3:raise OverflowError('prospective cell replay memory cap')
    dc,pc=_divisor_stream(c['V'],c['mu'],end,m)
    dp,pp=_divisor_stream(c['U'],c['mu'],parentend,m)
    rows=certificate['cells']
    if type(rows) is not list or len(rows)!=K:raise ValueError('every cell in block required')
    energy=Q(0);weighted=Q(0)
    for k,row in zip(range(K,2*K),rows):
        j=k//c['p'];unit=Q(1+int(k>=c['p']))
        childharm=_mul(Q(k),SV,m);parentharm=_mul(Q(j),SU,m)
        value=_bounded(unit+childharm+parentharm-pc[k]-pp[j],m)
        weight=Q(1,k*(k+1));square=_bounded(value*value,m,400000)
        wsquare=_bounded(square*weight,m,400000)
        expected={'k':k,'parent_cell':j,'unit_and_indicator':_text(unit),
            'child_truncated_divisor_sum':_text(dc[k]),'parent_truncated_divisor_sum':_text(dp[j]),
            'child_harmonic_term':_text(childharm),'parent_harmonic_term':_text(parentharm),
            'child_floor_sum':_text(pc[k]),'parent_floor_sum':_text(pp[j]),
            'value':_text(value),'weight':_text(weight),'weighted_square':_text(wsquare)}
        _expect(row,expected)
        energy=_bounded(energy+square,m,400000);weighted=_bounded(weighted+wsquare,m,400000)
    if _rational(certificate['energy'],m,400000)!=energy or _rational(certificate['weighted_norm'],m,400000)!=weighted:
        raise ValueError('complete signed squared block energy')
    return {'verified':True,'K':K,'cells':K,'domain':certificate['domain'],
        'truncated_divisor_sources_retained':True,'signed_cross_terms_retained':True,
        'whole_norm_proved':False,'global_bound_proved':False,'RH_proved':False,'RH_refuted':False}
