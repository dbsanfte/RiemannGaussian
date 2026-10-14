"""Independent signed divisor-annihilator plus positive-square finite price085."""
from fractions import Fraction as Q
from flint import fmpq_mat
import check_mobius_coupled_completion_083 as C
import check_mobius_coupled_remainder_083 as R
import check_mobius_coupled_square_084 as F
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul
MAX_BANK=16

def parse_bank(bank,meter=None):
    m=meter or C.Meter()
    if type(bank)is not list or len(bank)>MAX_BANK:raise AdmissionError('complete bank<=16')
    result=[]
    for row in bank:
        if type(row)is not dict or set(row)!={'scale','u_exponent','complement','unit_balance'}:raise AdmissionError('exact annihilator descriptor keys')
        scale=_rational(row['scale'],'scale',m);exponent=_rational(row['u_exponent'],'u exponent',m)
        if scale<=0 or type(row['complement'])is not bool or type(row['unit_balance'])is not bool:raise AdmissionError('positive scale and strict bank booleans')
        result.append(dict(scale=scale,u_exponent=exponent,complement=row['complement'],unit_balance=row['unit_balance']))
    return result

def build_identities(model,bank,meter=None):
    """Complete raw g_K and exact known-prime congruent columns P^T g_K."""
    m=meter or C.Meter();descriptors=parse_bank(bank,m);G=model['squarefree_count'];E=model['effective_dimension'];N=model['N'];u=model['u']
    C._budget(model,m,extra_bytes=(G+E)*max(1,len(bank))*2048)
    raw=[[Q(0)for _ in descriptors]for _ in range(G)];V=[[Q(0)for _ in descriptors]for _ in range(E)];cuts=[]
    for j,d in enumerate(descriptors):
        K=C.floor_cut(d['scale'],Q(0),d['u_exponent'],1,u,N,m)
        if d['complement']:K=N-K
        cuts.append(K)
        factor=Q(max(K-1,0),N-1)if d['unit_balance']and N>=2 else Q(0)
        for g,n in enumerate(model['coordinates']):
            value=Q(K//n-int(n==1))if K else Q(0)
            if factor:value=_add(value,-_mul(factor,Q(N//n-int(n==1)),m),m)
            raw[g][j]=value;i=model['projection_indices'][g]
            V[i][j]=_add(V[i][j],model['projection_signs'][g]*value,m)
    return dict(raw_vectors=raw,vectors=V,cuts=cuts)

def annihilator_price(matrix,vectors,identity_matrix,numerators,denominator,meter=None):
    """Exact standalone primitive, on coordinates satisfying V^T y=0."""
    m=meter or C.Meter();E=len(matrix);b=len(identity_matrix)
    if E>F.MAX_EFFECTIVE or b>MAX_BANK:raise ResourceLimit('annihilator complete dimension/bank cap')
    if len(vectors)!=E or any(len(row)!=b for row in vectors)or any(len(row)!=b for row in identity_matrix):raise AdmissionError('complete identity dimensions')
    if any(identity_matrix[i][j]!=identity_matrix[j][i]for i in range(b)for j in range(i)):raise AdmissionError('exact symmetric signed identity matrix')
    vals=[v for row in vectors for v in row]+[v for row in identity_matrix for v in row]
    if any(type(v)not in (int,Q)for v in vals):raise AdmissionError('exact rational identity entries')
    common=1;largest=1
    from math import gcd
    from check_mobius_prime_storage_073 import _int_mul
    for value in vals:
        v=Q(value);common=_int_mul(common//gcd(common,v.denominator),v.denominator,m);largest=max(largest,abs(v.numerator).bit_length())
    bits=4*(common.bit_length()+largest)+32
    if bits>100000:raise ResourceLimit('annihilator native rational bit gate')
    m.reserve(16384+E*E*(4096+bits)+E*max(1,b)*(1024+bits));m.charge(max(1,E*E*max(1,b))*1024)
    if b and E:
        V=fmpq_mat([[str(v)for v in row]for row in vectors]);S=fmpq_mat([[str(v)for v in row]for row in identity_matrix]);native=V*S*V.transpose()
        Z=[[Q(str(native[i,j]))for j in range(E)]for i in range(E)]
    else:Z=[[Q(0)for _ in range(E)]for _ in range(E)]
    corrected=[[matrix[i][j]+Z[i][j]for j in range(E)]for i in range(E)]
    result=F.square_price(corrected,numerators,denominator,m)
    result.update(identity_correction=Z,identity_trace=sum(Z[i][i]for i in range(E)),identity_matrix_positive_semidefinite_required=False)
    return result

def verify_certificate(program,u,outer_certificate,bank,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        keys={'squarefree_count','identity_matrix','factor_denominator','factor_numerators','price','row_prices'}
        if type(certificate)is not dict or set(certificate)!=keys:raise AdmissionError('exact annihilator certificate schema')
        descriptors=parse_bank(bank,m);b=len(descriptors);rawS=certificate['identity_matrix']
        if type(rawS)is not list or len(rawS)!=b or any(type(row)is not list or len(row)!=b for row in rawS):raise AdmissionError('complete square signed identity matrix')
        S=[[_rational(v,'identity matrix',m)for v in row]for row in rawS]
        if any(S[i][j]!=S[j][i]for i in range(b)for j in range(i)):raise AdmissionError('identity matrix EXACT symmetric')
        den=F.integer_string(certificate['factor_denominator'],'factor denominator',True)
        if den>(1<<48)or den&(den-1):raise AdmissionError('factor denominator power2<=2^48')
        raw=certificate['factor_numerators']
        if type(raw)is not list or len(raw)>F.MAX_EFFECTIVE:raise ResourceLimit('factor complete dimension<=512')
        rank=len(raw[0])if raw and type(raw[0])is list else 0
        if rank>len(raw)or any(type(row)is not list or len(row)!=rank for row in raw):raise AdmissionError('factor rectangular rank<=dimension')
        rawbytes=16384
        for row in raw:
            for v in row:
                if type(v)is not str or len(v)>42:raise AdmissionError('bounded canonical factor strings')
                rawbytes+=512+8*len(v)
        p=C.parse_program(program,m)
        if not p['prime_anchor']:raise AdmissionError('complete unit/prime anchored residual required')
        data=R.build_remainder(program,u,outer_certificate,m);model=data['model'];E=model['effective_dimension'];G=model['squarefree_count']
        if E>F.MAX_EFFECTIVE:raise ResourceLimit('complete effective dimension exceeds512')
        if len(raw)!=E:raise AdmissionError('complete effective factor rows')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('complete original squarefree count')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=E:raise AdmissionError('complete corrected price rows')
        # Existing remainder matrices and all factor/identity/native scratch counted together.
        C._budget(model,m,extra_values=[v for row in S for v in row],extra_bytes=rawbytes+G*G*1024+E*E*8192+(G+E)*max(1,b)*2048+E*rank*1024)
        identities=build_identities(model,bank,m);nums=[[F.integer_string(v,'factor numerator')for v in row]for row in raw]
        supplied=[_rational(v,'row price',m)for v in certificate['row_prices']];price=_rational(certificate['price'],'price',m)
        result=annihilator_price(data['projected_remainder'],identities['vectors'],S,nums,den,m)
        if supplied!=result['rows']or price!=result['price']:raise AdmissionError('independent complete signed annihilator price mismatch')
        out.update(status='VERIFIED_FINITE_ANNIHILATOR_SQUARE_BOUND',u=u,squarefree_count=G,effective_dimension=E,bank_size=b,cuts=identities['cuts'],factor_rank=rank,price=str(price),row_prices=list(map(str,result['rows'])),identity_trace=str(result['identity_trace']),factor_trace=str(result['factor_trace']),signed_trace=str(result['trace']),absolute_cross_price=str(result['absolute_cross']),zero_identity_rule_verified_for_all_u=True,identity_rule_scope='Complete ordinary Mobius divisor identity only; no uniform finite price growth conclusion',signed_identity_matrix_allowed=True,identity_matrix_PSD_required=False,old_outer_block_unchanged=True,negative_original_Gram_removed=True,complete_raw_and_anchor_geometry=True,known_prime_signs_anchored=True,uniform_remaining_bound_proved=False,uniform_remainder_bound_proved=False,proof='V^T y=0 for actual complete anchored Mobius vector, so y^T VSV^T y=0 for arbitrary symmetric S; LL^T>=0 and complete Boolean price bounds remaining quadratic.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)
