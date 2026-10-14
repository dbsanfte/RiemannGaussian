"""Independent exact complete coupled remainder admission, finite only."""
from fractions import Fraction as Q
import check_mobius_coupled_completion_083 as C
import check_mobius_coupled_outer_control_083 as O
from check_mobius_prime_storage_073 import AdmissionError,_rational,_add,_mul

def build_remainder(program,u,outer_certificate,meter=None):
    m=meter or C.Meter()
    admitted=O.verify_certificate(program,outer_certificate,m)
    if admitted['status']!='VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL':
        raise AdmissionError('complete same-program outer certificate required: '+admitted.get('reason',''))
    model=C.build_model(program,u,m);G=model['squarefree_count'];C._budget(model,m,extra_bytes=G*G*1024)
    A=C.corrected_matrix(model,m);p=model['program'];outer=tuple(u//5<n<=u//4 for n in model['coordinates'])
    R=[];gram=[]
    for g in range(G):
        row=[];grow=[]
        for h in range(G):
            v=Q(0)
            for i,w in enumerate(p['gram_weights']):
                if w and model['features'][g][i]and model['features'][h][i]:
                    v=_add(v,_mul(w,_mul(model['features'][g][i],model['features'][h][i],m),m),m)
            grow.append(v)
            # Negative Gram is mandatory, also where both indices are outer.
            row.append(_add(Q(0)if outer[g]and outer[h]else A[g][h],-v,m))
        R.append(row);gram.append(grow)
    E=model['effective_dimension'];P=[[Q(0)for _ in range(E)]for _ in range(E)]
    for g in range(G):
        for h in range(G):
            i=model['projection_indices'][g];j=model['projection_indices'][h]
            P[i][j]=_add(P[i][j],model['projection_signs'][g]*model['projection_signs'][h]*R[g][h],m)
    return dict(model=model,raw_complete=A,raw_Gram=gram,outer_mask=outer,raw_remainder=R,projected_remainder=P,outer_admission=admitted)

def verify_certificate(program,u,outer_certificate,certificate,meter=None):
    m=meter or C.Meter();out={}
    try:
        data=build_remainder(program,u,outer_certificate,m);model=data['model'];G=model['squarefree_count'];E=model['effective_dimension']
        if type(certificate)is not dict or set(certificate)!={'squarefree_count','price','row_prices'}:raise AdmissionError('exact complete remainder certificate keys')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('original complete squarefree count mismatch')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=E:raise AdmissionError('complete effective rows required')
        supplied=tuple(_rational(v,'row price',m)for v in certificate['row_prices']);price=_rational(certificate['price'],'price',m)
        A=data['projected_remainder'];rows=[];trace=Q(0);anchor_cross=Q(0);composite_cross=Q(0)
        for g,row in enumerate(A):
            value=row[g];trace=_add(trace,value,m)
            for h,a in enumerate(row):
                if h!=g:value=_add(value,abs(a),m)
            rows.append(value)
        for g in range(E):
            for h in range(g+1,E):
                value=2*abs(A[g][h])
                if model['program']['prime_anchor']and g==0:anchor_cross=_add(anchor_cross,value,m)
                else:composite_cross=_add(composite_cross,value,m)
        total=sum(rows,Q(0))
        if supplied!=tuple(rows)or price!=total:raise AdmissionError('independent complete residual Boolean price mismatch')
        out.update(status='VERIFIED_FINITE_COUPLED_REMAINDER_UPPER_BOUND',u=u,horizon=model['N'],squarefree_count=G,effective_dimension=E,price=str(total),row_prices=list(map(str,rows)),signed_trace=str(trace),anchor_constant=str(A[0][0]if E and model['program']['prime_anchor']else Q(0)),composite_signed_trace=str(trace-(A[0][0]if E and model['program']['prime_anchor']else Q(0))),anchor_composite_absolute_price=str(anchor_cross),composite_composite_absolute_price=str(composite_cross),prime_signs_anchored=model['program']['prime_anchor'],complete_outer_certificate_bound=True,negative_Gram_removed=True,complete_cross_kernel_retained=True,uniform_remainder_bound_proved=False,next_uniform_target='mu^T remainder mu <= K*u for every positive integer u',identity='R=A-O-G; DeltaE=mu^T O mu+mu^T R mu by complete divisor zero identities',outer_uniform_bound_coefficient=outer_certificate['uniform_bound_coefficient'],price_subtraction_used=False)
    except (ValueError,TypeError,KeyError,OverflowError)as e:return C._finish(out,m,e)
    return C._finish(out,m)
