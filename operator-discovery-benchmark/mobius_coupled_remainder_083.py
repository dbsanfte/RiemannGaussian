"""Compile the exact unpaid signed remainder after a proved raw outer block."""
from fractions import Fraction as Q
from flint import fmpq,fmpq_mat
import mobius_coupled_completion_083 as BASE


def raw_remainder(model):
    """R=A-A_outer-G. On actual mu, DeltaE=mu^T A_outer mu+mu^T R mu."""
    n=model['squarefree_count'];p=model['program'];dim=p['memory']+1
    BASE._basis_budget(model,extra=n*n*512)
    R=BASE.native_matrix(model,raw=True)
    outer=[i for i,v in enumerate(model['coordinates'])if 5*int(v)>model['u'] and 4*int(v)<=model['u']]
    for i in outer:
        for j in outer:R[i,j]=0
    if n and any(p['gram_weights']):
        F=fmpq_mat(model['features'].tolist());G=fmpq_mat(dim,dim)
        for i,w in enumerate(p['gram_weights']):G[i,i]=fmpq(w.numerator,w.denominator)
        R-=F*G*F.transpose()/fmpq(model['denominator']**2)
    model['meter'].charge(n*n*(dim+4))
    return R


def remainder_certificate(model):
    R=BASE.project_native(model,raw_remainder(model));n=model['price_dimension'];rows=[]
    trace=Q(0);anchor_edges=Q(0);composite_edges=Q(0)
    anchored=model['program']['prime_anchor'];anchor=BASE.OLD.as_q(R[0,0])if n and anchored else Q(0)
    for i in range(n):
        value=BASE.OLD.as_q(R[i,i]);trace+=value
        for j in range(n):
            if i!=j:value+=abs(BASE.OLD.as_q(R[i,j]))
        rows.append(value)
        for j in range(i+1,n):
            cost=2*abs(BASE.OLD.as_q(R[i,j]))
            if anchored and i==0:anchor_edges+=cost
            else:composite_edges+=cost
    price=sum(rows,Q(0));assert price==trace+anchor_edges+composite_edges
    model['meter'].charge(n*n*8)
    return dict(squarefree_count=model['squarefree_count'],price=str(price),row_prices=list(map(str,rows))),dict(
        signed_trace=str(trace),anchor_constant=str(anchor),
        anchor_composite_absolute_price=str(anchor_edges),composite_composite_absolute_price=str(composite_edges),
        prime_anchor=anchored,effective_dimension=n,
        complete_unpaid_kernel='A minus its raw whole-outer block minus all added positive Grams',
        uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
