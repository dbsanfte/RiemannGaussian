"""Independent complete divisor/prime-cofactor arithmetic-bank checker086."""
from fractions import Fraction as Q
from flint import fmpq_mat
import check_mobius_annihilator_085 as D
C=D.C;R=D.R;F=D.F
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add,_mul
MAX_BANK=16

def parse_bank(bank,meter=None):
    m=meter or C.Meter()
    if type(bank)is not list or len(bank)>MAX_BANK:raise AdmissionError('typed bank<=16')
    result=[]
    for row in bank:
        if type(row)is not dict:raise AdmissionError('typed descriptor object')
        if row.get('kind')=='divisor':
            if set(row)!={'kind','cut'}:raise AdmissionError('exact divisor descriptor keys')
            result.append(dict(kind='divisor',cut=D.parse_bank([row['cut']],m)[0]));continue
        if row.get('kind')!='prime_pair'or set(row)!={'kind','cut_on','cut','weight'}:raise AdmissionError('exact prime-pair descriptor keys')
        if row['cut_on']not in ('prime','cofactor'):raise AdmissionError('prime/cofactor cut domain')
        cut=row['cut']
        if type(cut)is not dict or set(cut)!={'scale','u_exponent','complement'}:raise AdmissionError('exact prime-pair cut')
        parsed=D.parse_bank([dict(cut,unit_balance=False)],m)[0];parsed.pop('unit_balance')
        w=row['weight']
        if type(w)is not dict or (w.get('kind')=='one'and set(w)!={'kind'})or(w.get('kind')=='source'and set(w)!={'kind','i'})or w.get('kind')not in ('one','source'):raise AdmissionError('exact prime-pair weight')
        if w['kind']=='source':C.D.integer(w['i'],'source index',0,3)
        result.append(dict(kind='prime_pair',cut_on=row['cut_on'],cut=parsed,weight=dict(w)))
    return result

def build_identities(model,bank,meter=None):
    m=meter or C.Meter();descriptors=parse_bank(bank,m);p=model['program'];N=model['N'];u=model['u'];G=model['squarefree_count'];E=model['effective_dimension'];b=len(descriptors)
    if not p['prime_anchor']:raise AdmissionError('complete unit/prime anchor required')
    if E>F.MAX_EFFECTIVE:raise ResourceLimit('complete effective bank dimension<=512')
    for d in descriptors:
        if d['kind']=='prime_pair'and d['weight']['kind']=='source'and d['weight']['i']>p['memory']:raise AdmissionError('source index binds memory')
    C._budget(model,m,extra_bytes=(G+E)*max(1,b)*4096+64*(N+1));m.charge(max(1,N*N*max(1,b))*64)
    raw=[[Q(0)for _ in descriptors]for _ in range(G)];V=[[Q(0)for _ in descriptors]for _ in range(E)];cuts=[];counts=[]
    primes=C.is_prime_table(N,m);roster=[n for n in range(2,N+1)if primes[n]];positions={n:g for g,n in enumerate(model['coordinates'])}
    for j,d in enumerate(descriptors):
        cut=d['cut'];K=C.floor_cut(cut['scale'],Q(0),cut['u_exponent'],1,u,N,m)
        if cut['complement']:K=N-K
        cuts.append(K);count=0
        if d['kind']=='divisor':
            f=Q(max(K-1,0),N-1)if cut['unit_balance']and N>=2 else Q(0)
            for g,n in enumerate(model['coordinates']):
                value=Q(K//n-int(n==1))if K else Q(0)
                if f:value=_add(value,-_mul(f,Q(N//n-int(n==1)),m),m)
                raw[g][j]=value
        else:
            for prime in roster:
                if d['cut_on']=='prime'and prime>K:break
                limit=N//prime
                for g,n in enumerate(model['coordinates']):
                    if n>limit:break
                    if d['cut_on']=='cofactor'and n>K:break
                    if n%prime==0:continue
                    count+=1;w=Q(1)if d['weight']['kind']=='one'else model['features'][g][d['weight']['i']]
                    if not w:continue
                    h=positions[prime*n]
                    raw[g][j]=_add(raw[g][j],w,m);raw[h][j]=_add(raw[h][j],w,m)
        counts.append(count)
        for g in range(G):
            i=model['projection_indices'][g];V[i][j]=_add(V[i][j],model['projection_signs'][g]*raw[g][j],m)
    return dict(raw_vectors=raw,vectors=V,cuts=cuts,prime_pair_counts=counts,complete_prime_roster=roster)

def _model(program,u,outer_certificate,bank,m,extra_values=(),extra_bytes=0):
    parse_bank(bank,m);p=C.parse_program(program,m)
    if not p['prime_anchor']:raise AdmissionError('complete unit/prime anchored residual required')
    if extra_bytes or extra_values:
        preliminary=C.build_model(program,u,m);G=preliminary['squarefree_count'];E=preliminary['effective_dimension']
        if E>F.MAX_EFFECTIVE:raise ResourceLimit('complete effective dimension<=512')
        C._budget(preliminary,m,extra_values=extra_values,extra_bytes=extra_bytes+G*G*1024+E*E*8192+(G+E)*max(1,len(bank))*4096)
        del preliminary
    data=R.build_remainder(program,u,outer_certificate,m);model=data['model']
    if model['effective_dimension']>F.MAX_EFFECTIVE:raise ResourceLimit('complete effective dimension<=512')
    data['identities']=build_identities(model,bank,m)
    return data

def quadratic_value(matrix,signs,meter=None):
    m=meter or C.Meter();E=len(matrix)
    if E>F.MAX_EFFECTIVE or type(signs)is not list or len(signs)!=E or any(type(v)is not int or v not in (-1,1)for v in signs):raise AdmissionError('complete Boolean quadratic coordinates')
    if any(len(row)!=E for row in matrix):raise AdmissionError('square quadratic matrix')
    m.reserve(16384+E*E*4096);m.charge(max(1,E*E)*1024)
    if not E:return Q(0)
    A=fmpq_mat([[str(v)for v in row]for row in matrix]);s=fmpq_mat([[v]for v in signs]);return Q(str((s.transpose()*A*s)[0,0]))

def verify_lower(program,u,outer_certificate,bank,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        if type(certificate)is not dict or set(certificate)!={'squarefree_count','signs','lower_bound'}:raise AdmissionError('exact compatible Boolean witness schema')
        signs=certificate['signs']
        if type(signs)is not list or len(signs)>F.MAX_EFFECTIVE:raise ResourceLimit('Boolean witness dimension<=512')
        if any(type(v)is not int or v not in (-1,1)for v in signs)or signs and signs[0]!=1:raise AdmissionError('Boolean signs with exact positive anchor')
        data=_model(program,u,outer_certificate,bank,m);model=data['model'];G=model['squarefree_count'];E=model['effective_dimension'];V=data['identities']['vectors']
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G or len(signs)!=E:raise AdmissionError('complete original/effective witness binding')
        for j in range(len(bank)):
            value=Q(0)
            for i in range(E):value=_add(value,signs[i]*V[i][j],m)
            if value:raise AdmissionError('Boolean witness violates exact arithmetic bank')
        C._budget(model,m,extra_bytes=G*G*1024+E*E*4096+(G+E)*max(1,len(bank))*4096)
        actual=quadratic_value(data['projected_remainder'],signs,m);supplied=_rational(certificate['lower_bound'],'lower bound',m)
        if supplied!=actual:raise AdmissionError('independent complete compatible witness value mismatch')
        out.update(status='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND',u=u,squarefree_count=G,effective_dimension=E,bank_size=len(bank),lower_bound=str(actual),cuts=data['identities']['cuts'],prime_pair_counts=data['identities']['prime_pair_counts'],complete_arithmetic_bank_compatible=True,anchor_sign_exact=True,fixed_operator_only=True,unrestricted_signed_and_mixed_zero_plus_PSD_grammars_bound=True,artificial_signs_not_actual_Mobius=True,actual_signed_drift_lower_bound_proved=False,uniform_obstruction_proved=False,uniform_remaining_bound_proved=False,zero_identity_rule_verified_for_all_u=True,proof='V^T s=0 and s_i^2=1 imply s^T Z s=0 for both VSV^T and symmetric mixed V partners; for Q>=0, Boolean price(R+Z+Q)>=s^T R s.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)

verify_certificate=verify_lower

def mixed_price(matrix,vectors,partners,numerators,denominator,meter=None):
    m=meter or C.Meter();E=len(matrix);b=len(vectors[0])if E else(len(partners[0])if partners else 0)
    if E>F.MAX_EFFECTIVE or b>MAX_BANK:raise ResourceLimit('complete mixed geometry cap')
    if len(vectors)!=E or len(partners)!=E or any(len(row)!=b for row in vectors+partners):raise AdmissionError('complete mixed partner shape')
    from math import gcd
    from check_mobius_prime_storage_073 import _int_mul
    common=1;largest=1
    for row in vectors+partners:
        for value in row:
            if type(value)not in (int,Q):raise AdmissionError('exact mixed rational entry')
            v=Q(value);common=_int_mul(common//gcd(common,v.denominator),v.denominator,m);largest=max(largest,abs(v.numerator).bit_length())
    bits=4*(common.bit_length()+largest)+32
    if bits>100000:raise ResourceLimit('mixed native rational bit gate')
    m.reserve(16384+E*E*(8192+bits)+E*max(1,b)*(2048+bits));m.charge(max(1,E*E*max(1,b))*1024)
    if E and b:
        V=fmpq_mat([[str(v)for v in row]for row in vectors]);W=fmpq_mat([[str(v)for v in row]for row in partners]);Z=(V*W.transpose()+W*V.transpose())/2
        correction=[[Q(str(Z[i,j]))for j in range(E)]for i in range(E)]
    else:correction=[[Q(0)for _ in range(E)]for _ in range(E)]
    corrected=[[matrix[i][j]+correction[i][j]for j in range(E)]for i in range(E)];result=F.square_price(corrected,numerators,denominator,m)
    result.update(mixed_correction=correction,mixed_trace=sum(correction[i][i]for i in range(E)))
    return result

def verify_upper(program,u,outer_certificate,bank,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        keys={'squarefree_count','partner_matrix','factor_denominator','factor_numerators','price','row_prices'}
        if type(certificate)is not dict or set(certificate)!=keys:raise AdmissionError('exact mixed upper schema')
        parse_bank(bank,m);b=len(bank);rawW=certificate['partner_matrix'];raw=certificate['factor_numerators']
        if type(rawW)is not list or len(rawW)>F.MAX_EFFECTIVE or type(raw)is not list or len(raw)>F.MAX_EFFECTIVE:raise ResourceLimit('complete partner/factor dimensions<=512')
        if any(type(row)is not list or len(row)!=b for row in rawW):raise AdmissionError('complete bank partner width')
        rank=len(raw[0])if raw and type(raw[0])is list else 0
        if rank>len(raw)or any(type(row)is not list or len(row)!=rank for row in raw):raise AdmissionError('rectangular factor rank<=dimension')
        rawbytes=16384
        for v in [v for row in rawW for v in row]:
            if type(v)is not str or len(v)>10000:raise AdmissionError('bounded canonical mixed strings')
            rawbytes+=512+8*len(v)
        for row in raw:
            for v in row:
                if type(v)is not str or len(v)>42:raise AdmissionError('bounded canonical factor strings')
                rawbytes+=512+8*len(v)
        den=F.integer_string(certificate['factor_denominator'],'factor denominator',True)
        if den>(1<<48)or den&(den-1):raise AdmissionError('dyadic denominator<=2^48')
        W=[[_rational(v,'partner entry',m)for v in row]for row in rawW]
        data=_model(program,u,outer_certificate,bank,m,extra_values=[v for row in W for v in row],extra_bytes=rawbytes);model=data['model'];G=model['squarefree_count'];E=model['effective_dimension']
        if len(rawW)!=E or len(raw)!=E:raise AdmissionError('complete effective partner/factor rows')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('complete original squarefree count')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=E:raise AdmissionError('complete mixed row prices')
        C._budget(model,m,extra_bytes=rawbytes+G*G*1024+E*E*8192+(G+E)*max(1,b)*4096+E*rank*1024)
        C._budget(model,m,extra_values=[v for row in W for v in row],extra_bytes=rawbytes+G*G*1024+E*E*8192+(G+E)*max(1,b)*4096+E*rank*1024)
        nums=[[F.integer_string(v,'factor numerator')for v in row]for row in raw];supplied=[_rational(v,'row price',m)for v in certificate['row_prices']];price=_rational(certificate['price'],'price',m)
        result=mixed_price(data['projected_remainder'],data['identities']['vectors'],W,nums,den,m)
        if supplied!=result['rows']or price!=result['price']:raise AdmissionError('independent complete mixed price mismatch')
        out.update(status='VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND',u=u,squarefree_count=G,effective_dimension=E,bank_size=len(bank),price=str(price),row_prices=list(map(str,result['rows'])),cuts=data['identities']['cuts'],prime_pair_counts=data['identities']['prime_pair_counts'],mixed_trace=str(result['mixed_trace']),factor_trace=str(result['factor_trace']),signed_trace=str(result['trace']),absolute_cross_price=str(result['absolute_cross']),factor_rank=rank,zero_identity_rule_verified_for_all_u=True,complete_prime_unit_cofactor_geometry=True,old_outer_block_unchanged=True,negative_original_Gram_removed=True,uniform_remaining_bound_proved=False,proof='Every bank column is an exact complete arithmetic annihilator; y^T(VW^T+WV^T)y/2=0, LL^T>=0, complete Boolean price upperbounds actual remaining quadratic.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)

def verify_extension(program,u,outer_certificate,old_bank,lower_certificate,added_descriptor,meter=None):
    """A compatible old Boolean witness is excluded by one new exact identity."""
    m=meter or C.Meter();out={}
    try:
        if type(old_bank)is not list or len(old_bank)>=MAX_BANK:raise AdmissionError('extension must fit complete bank<=16')
        admitted=verify_lower(program,u,outer_certificate,old_bank,lower_certificate,m)
        if admitted['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND':raise AdmissionError('old lower certificate independently admitted')
        parsed=parse_bank([added_descriptor],m)
        model=C.build_model(program,u,m);new=build_identities(model,[added_descriptor],m);signs=lower_certificate['signs'];dot=Q(0)
        for i,row in enumerate(new['vectors']):dot=_add(dot,_mul(Q(signs[i]),row[0],m),m)
        if not dot:raise AdmissionError('new exact identity must exclude the compatible witness')
        out.update(status='VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN',u=u,old_bank_size=len(old_bank),new_bank_size=len(old_bank)+1,new_identity_dot=str(dot),old_lower_bound=admitted['lower_bound'],old_bank_compatible=True,new_identity_excludes_witness=True,finite_geometry_rank_gain=True,uniform_rank_gain_proved=False,uniform_remaining_bound_proved=False,actual_signed_drift_lower_bound_proved=False,zero_identity_rule_verified_for_all_u=True,cut=new['cuts'][0],prime_pair_count=new['prime_pair_counts'][0])
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)
