"""Independent finite rational positive-square residual price admission084."""
from fractions import Fraction as Q
from flint import fmpz_mat
import check_mobius_coupled_remainder_083 as R
import check_mobius_coupled_completion_083 as C
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_rational,_add
MAX_EFFECTIVE=512

def integer_string(value,name,positive=False):
    if type(value)is not str or not value or len(value)>42:raise AdmissionError(name+' canonical bounded integer string')
    try:n=int(value)
    except ValueError:raise AdmissionError(name+' integer')
    if str(n)!=value or abs(n).bit_length()>128 or positive and n<=0:raise AdmissionError(name+' canonical integer/domain')
    return n

def square_price(matrix,numerators,denominator,meter=None):
    """Exact standalone matrix primitive, useful for synthetic price fixtures."""
    m=meter or C.Meter();E=len(matrix);rank=len(numerators[0])if E else 0
    if E>MAX_EFFECTIVE or rank>E:raise ResourceLimit('effective square dimension/rank')
    if len(numerators)!=E or any(len(row)!=rank for row in numerators):raise AdmissionError('rectangular factor dimensions')
    if type(denominator)is not int or denominator<=0 or denominator>(1<<48)or denominator&(denominator-1):raise AdmissionError('dyadic factor denominator')
    if any(type(v)is not int or abs(v).bit_length()>128 for row in numerators for v in row):raise AdmissionError('bounded exact integer factor')
    if any(len(row)!=E for row in matrix)or any(matrix[i][j]!=matrix[j][i]for i in range(E)for j in range(i)):raise AdmissionError('complete symmetric residual matrix')
    m.reserve(16384+E*E*4096+E*rank*1024);m.charge(max(1,E*E*max(1,rank))*1024)
    if rank:
        L=fmpz_mat(numerators);G=L*L.transpose()
        gram=[[Q(int(G[i,j]),denominator**2)for j in range(E)]for i in range(E)]
    else:gram=[[Q(0)for _ in range(E)]for _ in range(E)]
    A=[[matrix[i][j]+gram[i][j]for j in range(E)]for i in range(E)]
    rows=[row[i]+sum(abs(v)for j,v in enumerate(row)if j!=i)for i,row in enumerate(A)]
    return dict(matrix=A,gram=gram,rows=rows,price=sum(rows,Q(0)),factor_trace=sum(gram[i][i]for i in range(E)),trace=sum(A[i][i]for i in range(E)),absolute_cross=sum(2*abs(A[i][j])for i in range(E)for j in range(i+1,E)))

def verify_certificate(program,u,outer_certificate,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        keys={'squarefree_count','factor_denominator','factor_numerators','price','row_prices'}
        if type(certificate)is not dict or set(certificate)!=keys:raise AdmissionError('exact square certificate schema')
        den=integer_string(certificate['factor_denominator'],'factor denominator',True)
        if den>(1<<48)or den&(den-1):raise AdmissionError('factor denominator power2<=2^48')
        raw=certificate['factor_numerators']
        if type(raw)is not list or len(raw)>MAX_EFFECTIVE:raise ResourceLimit('factor row horizon before allocation')
        rank=len(raw[0])if raw and type(raw[0])is list else 0
        if rank>len(raw):raise AdmissionError('rank<=effective dimension')
        rawbytes=16384
        for row in raw:
            if type(row)is not list or len(row)!=rank:raise AdmissionError('rectangular factor')
            for value in row:
                if type(value)is not str or len(value)>42:raise AdmissionError('bounded integer factor strings')
                rawbytes+=512+8*len(value)
        # Full original geometry admission precedes factor/native allocation.
        data=R.build_remainder(program,u,outer_certificate,m);model=data['model'];E=model['effective_dimension'];G=model['squarefree_count']
        if E>MAX_EFFECTIVE:raise ResourceLimit('effective square dimension exceeds512')
        if len(raw)!=E:raise AdmissionError('factor rows bind complete effective coordinates')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('complete original squarefree count')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=E:raise AdmissionError('complete square row prices')
        # Extra cumulative scratch includes retained raw remainder matrices, factor and native product.
        C._budget(model,m,extra_bytes=rawbytes+G*G*1024+E*E*4096+E*rank*1024)
        nums=[[integer_string(v,'factor numerator')for v in row]for row in raw]
        price=_rational(certificate['price'],'price',m);supplied=[_rational(v,'row price',m)for v in certificate['row_prices']]
        result=square_price(data['projected_remainder'],nums,den,m)
        if supplied!=result['rows']or price!=result['price']:raise AdmissionError('independent complete rational square price mismatch')
        old=data['projected_remainder'];oldprice=sum(row[i]+sum(abs(v)for j,v in enumerate(row)if j!=i)for i,row in enumerate(old))
        out.update(status='VERIFIED_FINITE_COUPLED_SQUARE_BOUND',u=u,squarefree_count=G,effective_dimension=E,factor_rank=rank,price=str(price),row_prices=list(map(str,result['rows'])),old_residual_price=str(oldprice),factor_trace=str(result['factor_trace']),signed_trace=str(result['trace']),absolute_cross_price=str(result['absolute_cross']),exact_positive_square_verified=True,complete_outer_certificate_bound=True,negative_original_Gram_removed=True,prime_signs_anchored=model['program']['prime_anchor'],uniform_remaining_bound_proved=False,uniform_remainder_bound_proved=False,proof='Q=L L^T>=0, hence mu^T R mu<=mu^T(R+Q)mu<=trace(R+Q)+2sum|offdiag| on complete effective Boolean coordinates')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)

def dual_components(data,numerators,denominator,multipliers,meter=None):
    """Exact residual/template functionals against PSD unit-diagonal X."""
    from flint import fmpq_mat,fmpq
    m=meter or C.Meter();model=data['model'];p=model['program'];E=model['effective_dimension'];G=model['squarefree_count'];t=len(p['coupled_terms'])
    product=square_price([[Q(0)for _ in range(E)]for _ in range(E)],numerators,denominator,m)['gram']
    norms=[product[i][i]for i in range(E)]
    if any(v>1 for v in norms):raise AdmissionError('dual factor row norm squared<=1')
    X=fmpq_mat([[str(Q(1)if i==j else product[i][j])for j in range(E)]for i in range(E)])
    actual=Q(0)
    for i in range(E):
        for j in range(E):actual+=data['projected_remainder'][i][j]*Q(str(X[i,j]))
    # Lift complete X through joint known-prime projection; zero only BOTH outer indices.
    C._budget(model,m,extra_values=multipliers,extra_bytes=G*G*1024+E*E*4096)
    W=fmpq_mat([[str(model['projection_signs'][g]*model['projection_signs'][h]*Q(str(X[model['projection_indices'][g],model['projection_indices'][h]])))if not(data['outer_mask'][g]and data['outer_mask'][h])else '0'for h in range(G)]for g in range(G)])
    values=[];key=None;rows=None
    for k,term in enumerate(p['coupled_terms']):
        nextkey=(model['cuts'][k],term['cut']['unit_balance'])
        if nextkey!=key:rows,den=C._integer_columns(model,k,m);key=nextkey
        weights=model['weights'][k];total=fmpq(0)
        # Symmetry makes the half-factor cancel in trace(BX): use one D direction.
        for h,w in enumerate(weights):
            if not w:continue
            column=fmpq(0)
            for g in range(G):
                if rows[g][h]and W[g,h]:column+=rows[g][h]*W[g,h]
            total+=column*fmpq(w.numerator,w.denominator)/den
        values.append(Q(str(total)))
    base=actual-sum((term['theta']*v for term,v in zip(p['coupled_terms'],values)),Q(0))
    system=R.O.equality_constraints(data['input_program'],m)
    if system['status']!='OUTER_EQUALITY_SYSTEM':raise AdmissionError('exact outer equality reconstruction')
    eq=[[Q(v)for v in row]for row in system['rows']];rhs=[Q(v)for v in system['rhs']]
    if len(multipliers)!=len(eq):raise AdmissionError('one multiplier percomplete outer equality')
    b=[target-sum((row[t+i]*w for i,w in enumerate(p['gram_weights'])),Q(0))for row,target in zip(eq,rhs)]
    adjusted=[v+sum((row[k]*lam for row,lam in zip(eq,multipliers)),Q(0))for k,v in enumerate(values)]
    lower=base-sum((lam*target for lam,target in zip(multipliers,b)),Q(0))-16*sum(map(abs,adjusted),Q(0))
    m.charge(max(1,G*G*max(1,t))*1024)
    return dict(lower=lower,base=base,template_functionals=values,adjusted_functionals=adjusted,equality_rhs=b,row_norms=norms)

def verify_dual(program,u,outer_certificate,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        keys={'squarefree_count','factor_denominator','factor_numerators','equality_multipliers','lower_bound'}
        if type(certificate)is not dict or set(certificate)!=keys:raise AdmissionError('exact square dual schema')
        den=integer_string(certificate['factor_denominator'],'dual denominator',True)
        if den>(1<<48)or den&(den-1):raise AdmissionError('dual denominator power2<=2^48')
        raw=certificate['factor_numerators'];lams=certificate['equality_multipliers']
        if type(raw)is not list or len(raw)>MAX_EFFECTIVE:raise ResourceLimit('dual factor rows cap512')
        rank=len(raw[0])if raw and type(raw[0])is list else 0
        if rank>len(raw)or any(type(row)is not list or len(row)!=rank for row in raw):raise AdmissionError('dual rectangular rank<=dimension')
        if type(lams)is not list or len(lams)>130:raise AdmissionError('bounded complete equality multiplier roster')
        rawbytes=16384
        for v in [v for row in raw for v in row]+lams:
            if type(v)is not str or len(v)>10000:raise AdmissionError('bounded canonical dual strings')
            rawbytes+=512+8*len(v)
        data=R.build_remainder(program,u,outer_certificate,m);data['input_program']=program;model=data['model'];E=model['effective_dimension'];G=model['squarefree_count']
        if E>MAX_EFFECTIVE:raise ResourceLimit('effective dual dimension cap512')
        if len(raw)!=E:raise AdmissionError('complete effective dual factor rows')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('complete original dual squarefree count')
        C._budget(model,m,extra_bytes=rawbytes+G*G*1024+E*E*4096+E*rank*1024)
        nums=[[integer_string(v,'dual factor numerator')for v in row]for row in raw]
        multipliers=[_rational(v,'equality multiplier',m)for v in lams];supplied=_rational(certificate['lower_bound'],'lower bound',m)
        result=dual_components(data,nums,den,multipliers,m)
        if supplied!=result['lower']:raise AdmissionError('independent affine square grammar lower mismatch')
        out.update(status='VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND',u=u,squarefree_count=G,effective_dimension=E,factor_rank=rank,lower_bound=str(result['lower']),base_functional=str(result['base']),template_functionals=list(map(str,result['template_functionals'])),adjusted_functionals=list(map(str,result['adjusted_functionals'])),equality_rhs=list(map(str,result['equality_rhs'])),exact_PSD_unit_diagonal_verified=True,fixed_Gram_weights=True,all_theta_boxes_and_outer_equalities_bound=True,actual_signed_drift_lower_bound_proved=False,uniform_grammar_obstruction_proved=False,uniform_remaining_bound_proved=False,uniform_remainder_bound_proved=False,proof='X=UU^T+diag(1-row_norm_squared)>=0,diagX=1; trace(Rtheta X) lowerbounds every PSD-completed Boolean price. Exact outer affine constraints and box minimization give stated lower.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)
