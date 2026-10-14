"""Search artificial Boolean witnesses against a fixed square-bound operator."""
from fractions import Fraction as Q
import numpy as np
from flint import fmpq_mat
import mobius_coupled_square_084 as S


def propose(program,u,seed=20261011085):
    model=S.B.build_model(program,u);S._gate(model);n=model['price_dimension']
    if not n:raise ValueError('nonempty witness geometry required')
    native=S.B.project_native(model,S.R.raw_remainder(model))
    A=np.array([[float(native[i,j]) for j in range(n)] for i in range(n)])
    model['meter'].charge(20*n**3+24*8*n**3)
    _,vectors=np.linalg.eigh(A);rng=np.random.default_rng(seed+u)
    starts=[np.ones(n)]+[np.where(vectors[:,k]>=0,1.,-1.) for k in range(max(0,n-4),n)]
    starts += [rng.choice([-1.,1.],size=n) for _ in range(16)]
    best=None;attempts=[]
    for signs in starts:
        signs=signs.copy();field=A@signs;flips=0
        for _ in range(8*n):
            gains=-4*signs*(field-np.diag(A)*signs);index=int(np.argmax(gains))
            if gains[index]<=1e-10:break
            old=signs[index];signs[index]=-old;field-=2*old*A[:,index];flips+=1
        signs=(signs*signs[0]).astype(int).tolist()
        v=fmpq_mat([signs]);value=S.B.OLD.as_q((v*native*v.transpose())[0,0])
        attempts.append(dict(flips=flips,exact_value=str(value)))
        if best is None or value>best[0]:best=(value,signs)
    return dict(certificate=dict(squarefree_count=model['squarefree_count'],signs=best[1],lower_bound=str(best[0])),
                attempts=attempts,ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes,
                artificial_signs_not_actual_Mobius=True,unknown_composite_signs_used=False)
