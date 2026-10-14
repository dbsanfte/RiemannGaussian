"""One fixed-precision free-coordinate cone-distance proposal and exact endpoint."""
from fractions import Fraction as F
import hashlib
import json
import math
import time
import mpmath
import primitive_state_triangular_restoration as EXACT
import primitive_state_equation_projection as PROJECT

SCHEMA='primitive-state-free-cone-search-v1';FLAGS=dict(EXACT.FLAGS)
PRECISION=dict(decimal_digits=80,binary_bits=269,actual_map_relative_tolerance='1e-40',serialized_binary_exponent_abs_cap=4096,mixed_precision=True,PSD_eigh='binary64',PSD_negative_parts='binary64',calibration_scope='affine forward and adjoint only')
SEARCH=dict(power_steps=8,gradient_iterations=24,armijo_trials=3,armijo_coefficient='1/8',step_min_binary_exponent=-900,step_max_binary_exponent=900,identity_free_coordinate_scaling=True,native_eigh_work_coefficient=96)
SEED='licensed publication017 restored projected nonpivots; one seed; no additional clipping'
encoded=EXACT.encoded;digest=EXACT.digest


def context():
    value=mpmath.mp.clone();value.dps=80
    if value.prec!=269:raise ValueError('installed fixed80digit context precision')
    return value


def mp_record(value):
    sign,man,exponent,bits=value._mpf_
    if bits<0:raise ValueError('finite multiprecision value required')
    if bits>269 or abs(exponent)>4096 or max(man.bit_length()+max(exponent,0),max(1,-exponent+1))>4096:raise OverflowError('bounded fixed80digit serialized mantissa/exponent')
    return [sign,format(man,'x'),exponent]


def record_fraction(value,*,max_bits=4096):
    sign,text,exponent=value
    if type(sign)is not int or sign not in (0,1) or type(text)is not str or not text or len(text)>68 or any(c not in '0123456789abcdef' for c in text) or type(exponent)is not int:raise ValueError('canonical finite80digit binary mantissa/exponent')
    man=int(text,16)
    if format(man,'x')!=text or man.bit_length()>269 or man and man%2==0 or not man and (sign or exponent):raise ValueError('canonical normalized80digit mantissa')
    if abs(exponent)>max_bits or max(man.bit_length()+max(exponent,0),max(1,-exponent+1))>max_bits:raise OverflowError('exact endpoint dyadic bits')
    q=F((-1 if sign else 1)*man)
    return q*2**exponent if exponent>=0 else q/F(2**(-exponent))


def to_mp(q,ctx,budget):
    budget.charge(3);return ctx.mpf(q.numerator)/ctx.mpf(q.denominator)


def materialize(cache,basis,projection,parent_restoration,*,deadline,max_operations=50000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096):
    budget=EXACT.Budget(deadline,max_operations,max_live_cells,max_fill_cells,max_bits)
    rows,rhs,n=EXACT.decode_source(cache,budget);o=cache['original'];shape=o['shape'];offset=o['offset'];specs=dict(o['specs']);retained,recipes=PROJECT.full15_recipes(shape,offset,specs,n)
    if projection.get('complete')is not True or projection.get('retained_indices')!=retained or basis.get('source_hash')!=projection.get('projected_rows_hash'):raise ValueError('licensed exact projection/basis map')
    positions={j:i for i,j in enumerate(retained)};projected_rows=[{positions[j]:q for j,q in row.items() if j in positions} for row in rows];budget.charge(sum(map(len,rows)))
    normalized,pivots,replay=EXACT.retained_replay(projected_rows,rhs,len(retained),basis,budget,resident_cells=sum(map(len,rows)))
    if parent_restoration.get('complete')is not True or parent_restoration.get('status')!='restored' or parent_restoration.get('normalized_basis_hash')!=replay['normalized_basis_hash'] or parent_restoration.get('retained_indices')!=retained or parent_restoration.get('pivot_columns')!=sorted(pivots):raise ValueError('publication017 independently licensed normalized map')
    restored=[budget.q(q) for q in parent_restoration['restored_projected_vector']]
    if len(restored)!=len(retained):raise ValueError('licensed projected seed length')
    free=[j for j in range(len(retained)) if j not in set(pivots)];initial=[restored[j] for j in free]
    ctx=context();by_pivot=dict(zip(pivots,normalized));converted={p:{j:to_mp(q,ctx,budget) for j,q in row.items()} for p,row in by_pivot.items()}
    budget.cells(sum(map(len,rows))+sum(map(len,projected_rows))+sum(map(len,normalized))+sum(map(len,converted.values()))+4*len(retained)+len(rhs))
    scalar_indices=[positions[j] for j in range(shape[0])]+[positions[j] for j in range(shape[0]+2*shape[1],offset)]
    gram_pairs=[(a,b) for a in range(15) for b in range(a,15)]
    C_indices=[positions[offset+j] for j in range(120)];P_indices=[positions[offset+120+j] for j in range(120)]
    mapping=dict(normalized_basis_hash=replay['normalized_basis_hash'],ctx=ctx,width=len(retained),retained=retained,pivots=sorted(pivots),free=free,normalized=by_pivot,converted=converted,initial=initial,parent_projected=restored,
        rows=rows,rhs=rhs,shape=shape,offset=offset,specs=specs,n_variables=n,scalar_indices=scalar_indices,gram_pairs=gram_pairs,C_indices=C_indices,P_indices=P_indices)
    receipt=dict(schema='primitive-state-free-cone-map-v1',normalized_basis_hash=replay['normalized_basis_hash'],retained_indices=retained,pivot_columns=sorted(pivots),free_indices=free,
        initial_free_vector=list(map(str,initial)),precision=PRECISION,source_cells=sum(map(len,rows))+len(rhs),sparse_map_entries=sum(map(len,normalized)),counts=budget.counts(),**FLAGS)
    return mapping,receipt


def forward(mapping,free,budget,*,linear=False,diagnostics=False):
    ctx=mapping['ctx'];width=mapping['width']
    if len(free)!=len(mapping['free']):raise ValueError('complete free vector')
    x=[ctx.zero]*width
    for j,v in zip(mapping['free'],free):x[j]=v
    zero_cancellation=0;maximum_ratio=ctx.zero
    for p in reversed(mapping['pivots']):
        row=mapping['converted'][p];rhs=ctx.zero if linear else row.get(width,ctx.zero);terms=[]
        for j,q in row.items():
            if j not in (p,width):terms.append(q*x[j]);budget.charge(2)
        value=ctx.fsum([rhs,*[-v for v in terms]]);x[p]=value
        if diagnostics:
            numerator=ctx.fsum([abs(rhs),*[abs(v) for v in terms]]);budget.charge(2*len(terms)+2)
            if value:maximum_ratio=max(maximum_ratio,numerator/abs(value))
            elif numerator:zero_cancellation+=1
    budget.charge(width)
    if not all(ctx.isfinite(v) for v in x):raise OverflowError('nonfinite fixed80digit forward')
    return x,dict(maximum_coordinate=mp_record(max(map(abs,x),default=ctx.zero)),maximum_finite_cancellation_ratio=mp_record(maximum_ratio),exact_zero_result_cancellations=zero_cancellation)


def adjoint(mapping,gradient,budget):
    ctx=mapping['ctx'];width=mapping['width']
    if len(gradient)!=width:raise ValueError('complete coordinate gradient')
    w=list(gradient)
    for p in mapping['pivots']:
        value=w[p]
        for j,q in mapping['converted'][p].items():
            if j not in (p,width):w[j]-=q*value;budget.charge(2)
        w[p]=ctx.zero
    out=[w[j] for j in mapping['free']];budget.charge(width)
    if not all(ctx.isfinite(v) for v in out):raise OverflowError('nonfinite fixed80digit adjoint')
    return out


def dot(ctx,a,b,budget):
    if len(a)!=len(b):raise ValueError('dot dimensions')
    budget.charge(2*len(a));return ctx.fsum(v*w for v,w in zip(a,b))


def matrices(mapping,x,budget):
    ctx=mapping['ctx'];C=[[ctx.zero]*15 for _ in range(15)];H=[[ctx.zero]*15 for _ in range(15)]
    for (a,b),ci,pi in zip(mapping['gram_pairs'],mapping['C_indices'],mapping['P_indices']):C[a][b]=C[b][a]=x[ci];H[a][b]=H[b][a]=x[pi]+4*x[ci];budget.charge(2)
    return C,H


def coordinate_gradient(mapping,x,C_gradient,H_gradient,budget,*,scalar_negative=True):
    ctx=mapping['ctx'];g=[ctx.zero]*mapping['width']
    for j in mapping['scalar_indices']:g[j]=min(x[j],ctx.zero) if scalar_negative else x[j]
    for (a,b),ci,pi in zip(mapping['gram_pairs'],mapping['C_indices'],mapping['P_indices']):
        factor=1 if a==b else 2;g[ci]=factor*(C_gradient[a][b]+4*H_gradient[a][b]);g[pi]=factor*H_gradient[a][b];budget.charge(5)
    budget.charge(len(mapping['scalar_indices']));return g


def power_operator(mapping,d,budget):
    x,_=forward(mapping,d,budget,linear=True);C,H=matrices(mapping,x,budget);return adjoint(mapping,coordinate_gradient(mapping,x,C,H,budget,scalar_negative=False),budget)


def merit_gradient(mapping,x,budget,*,apply_adjoint=True):
    import numpy as np
    ctx=mapping['ctx'];C,H=matrices(mapping,x,budget);neg=[];native=[]
    for matrix in (C,H):
        budget.charge(SEARCH['native_eigh_work_coefficient']*15**3)
        values=[]
        for row in matrix:
            line=[]
            for v in row:
                z=float(v)
                if not math.isfinite(z) or v and z==0:raise OverflowError('binary64 proposal matrix overflow/underflow')
                line.append(z)
            values.append(line)
        array=np.asarray(values,dtype=float);evals,evecs=np.linalg.eigh(array)
        if not np.all(np.isfinite(evals)) or not np.all(np.isfinite(evecs)):raise OverflowError('nonfinite binary64 proposal eigensolve')
        part=(evecs*np.minimum(evals,0.))@evecs.T
        if not np.all(np.isfinite(part)):raise OverflowError('nonfinite binary64 negative part')
        # Symmetrize only binary64 proposal negative parts; no exact cone change.
        part=(part+part.T)/2.;neg.append([[ctx.mpf(float(v)) for v in row] for row in part]);scale=max(1.,float(np.max(np.abs(array))));scaled=array/scale;scaled_negative=part/scale;scaled_positive=scaled-scaled_negative
        denominator=max(1.,float(np.linalg.norm(scaled,'fro')));backward=float(np.linalg.norm(scaled@evecs-evecs*(evals/scale),'fro'))/denominator;orthogonal=float(np.linalg.norm(evecs.T@evecs-np.eye(15),'fro'));reconstruction=float(np.linalg.norm(scaled-(evecs*(evals/scale))@evecs.T,'fro'))/denominator;projection_pairing=float(np.sum(scaled_negative*scaled_positive))/max(1.,denominator**2)
        if not all(math.isfinite(v) for v in [backward,orthogonal,reconstruction,projection_pairing]):raise OverflowError('nonfinite proposal PSD backward diagnostics')
        native.append(dict(minimum_eigenvalue=float(evals[0]),negative_eigenvalues=int(np.sum(evals<0)),scaled_eigen_backward_error=backward,eigenvector_orthogonality_error=orthogonal,scaled_eigen_reconstruction_error=reconstruction,scaled_negative_positive_pairing=projection_pairing))
    scalar=ctx.fsum(min(x[j],ctx.zero)**2 for j in mapping['scalar_indices']);matrixnorm=ctx.fsum(v*v for matrix in neg for row in matrix for v in row);budget.charge(3*(len(mapping['scalar_indices'])+450))
    merit=(scalar+matrixnorm)/2;g=coordinate_gradient(mapping,x,neg[0],neg[1],budget);gradient=adjoint(mapping,g,budget) if apply_adjoint else g
    if not ctx.isfinite(merit) or merit<0:raise OverflowError('finite nonnegative proposal merit')
    return merit,gradient,dict(native_negative_parts=native,scalar_penalty=mp_record(scalar/2),matrix_penalty=mp_record(matrixnorm/2))


def calibrate(mapping,budget):
    ctx=mapping['ctx'];initial=[to_mp(q,ctx,budget) for q in mapping['initial']]
    if any(record_fraction(mp_record(v))!=q for v,q in zip(initial,mapping['initial'])):raise ValueError('initial free conversion must be exactly represented at80digits')
    x,diag=forward(mapping,initial,budget,diagnostics=True);reference=[to_mp(q,ctx,budget) for q in mapping['parent_projected']]
    max_error=max((abs(v-q)/max(ctx.one,abs(q)) for v,q in zip(x,reference)),default=ctx.zero);budget.charge(4*len(x))
    d=[ctx.mpf((-1)**j) for j in range(len(initial))];g=[ctx.mpf((j%7)-3)/7 for j in range(mapping['width'])];Nd,_=forward(mapping,d,budget,linear=True);Ng=adjoint(mapping,g,budget)
    left=dot(ctx,Nd,g,budget);right=dot(ctx,d,Ng,budget);dot_error=abs(left-right)/max(ctx.one,abs(left),abs(right));threshold=ctx.mpf(PRECISION['actual_map_relative_tolerance'])
    actual_exact=[record_fraction(mp_record(v)) for v in x];exact_error=max((abs(v-q)/max(F(1),abs(q)) for v,q in zip(actual_exact,mapping['parent_projected'])),default=F(0));budget.charge(6*len(x))
    result=dict(initial_forward_mp=[mp_record(v) for v in x],initial_exact_reference_relative_error=str(exact_error),initial_relative_error=mp_record(max_error),adjoint_pairing_relative_error=mp_record(dot_error),tolerance=PRECISION['actual_map_relative_tolerance'],passed=exact_error<=F(1,10**40) and dot_error<=threshold,initial_forward=diag)
    if not result['passed']:raise ValueError('fixed80digit actual affine-map consistency failed: '+json.dumps(result,separators=(',',':')))
    return initial,x,result


def propose(mapping,*,deadline,max_operations=100000000,checkpoint=None,max_trace_bytes=8388608):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,4096);ctx=mapping['ctx'];start=time.monotonic()
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,seed_rule=SEED,normalized_basis_hash=mapping['normalized_basis_hash'],power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    best=None
    def save(phase):
        trace_vectors=3+2*len(out['power_trace'])+len(out['iterations'])+sum(len(v.get('trials',[])) for v in out['iterations'])
        budget.cells(20*mapping['width']+6*(mapping['width']+len(mapping['free'])*trace_vectors))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        free,x,calibration=calibrate(mapping,budget);out['calibration']=calibration;out['initial_free_mp']=[mp_record(v) for v in free];save('power_estimate')
        d=[ctx.mpf((-1)**j)/ctx.sqrt(len(free)) for j in range(len(free))];estimate=ctx.zero
        for k in range(8):
            v=power_operator(mapping,d,budget);den=dot(ctx,d,d,budget);estimate=dot(ctx,d,v,budget)/den;norm=ctx.sqrt(dot(ctx,v,v,budget));out['power_trace'].append(dict(index=k,vector=[mp_record(q) for q in d],operator=[mp_record(q) for q in v],estimate=mp_record(estimate),operator_norm=mp_record(norm)))
            if norm==0:break
            d=[q/norm for q in v];budget.charge(len(d))
        lower=ctx.power(2,-900);upper=ctx.power(2,900);alpha=max(lower,min(upper,ctx.one/estimate if estimate>0 else upper));out['initial_step']=mp_record(alpha)
        merit,gradient,info=merit_gradient(mapping,x,budget);best=list(free);out['initial_merit']=mp_record(merit);out['initial_merit_details']=info;stop='iteration_limit'
        for k in range(24):
            save('gradient_iteration');norm2=dot(ctx,gradient,gradient,budget);entry=dict(index=k,merit_before=mp_record(merit),gradient=[mp_record(q) for q in gradient],gradient_squared_norm=mp_record(norm2),trials=[],accepted=False)
            out['iterations'].append(entry)
            if norm2==0:stop='zero_gradient';break
            accepted=False
            for trial in range(3):
                trialalpha=alpha/ctx.power(2,trial)
                if trialalpha<lower:entry['trials'].append(dict(index=trial,step=mp_record(trialalpha),finite=False,reason='step below declared minimum'));continue
                trialfree=[v-trialalpha*g for v,g in zip(free,gradient)];budget.charge(2*len(free));trialx,diag=forward(mapping,trialfree,budget,diagnostics=True);value,newcoordinategradient,details=merit_gradient(mapping,trialx,budget,apply_adjoint=False);required=merit-trialalpha*norm2/8
                record=dict(index=trial,step=mp_record(trialalpha),free=[mp_record(q) for q in trialfree],merit=mp_record(value),armijo_threshold=mp_record(required),armijo_passed=value<=required,forward=diag,merit_details=details,finite=True);entry['trials'].append(record)
                if value<=required:
                    free=trialfree;x=trialx;merit=value;alpha=trialalpha;best=list(free);entry['accepted']=True;accepted=True;gradient=adjoint(mapping,newcoordinategradient,budget);break
            if not accepted:stop='line_search_failed';break
        out.update(status='proposed',complete=True,stop_reason=stop,final_merit=mp_record(merit),final_free_mp=[mp_record(q) for q in best],final_free_vector=[str(record_fraction(mp_record(q))) for q in best]);save('proposal_complete')
    except Exception as e:
        out.update(status='unknown',complete=False,reason=str(e) or type(e).__name__,error_type=type(e).__name__)
        if best is not None:out['last_finite_free_mp']=[mp_record(v) for v in best]
    out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    if len(encoded(out))>max_trace_bytes:raise OverflowError('bounded complete proposal trace')
    return out


def exact_endpoint(mapping,proposal,*,deadline,max_operations=20000000,max_bits=4096):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,max_bits)
    if proposal.get('complete')is not True or proposal.get('status')!='proposed':raise ValueError('one complete bounded finite proposal required')
    free=[budget.q(record_fraction(record,max_bits=max_bits)) for record in proposal['final_free_mp']]
    if list(map(str,free))!=proposal['final_free_vector'] or len(free)!=len(mapping['free']):raise ValueError('exact finite endpoint dyadic export')
    seed=[F(0)]*mapping['width']
    for j,q in zip(mapping['free'],free):seed[j]=q
    normalized=[mapping['normalized'][p] for p in mapping['pivots']];restored=EXACT.back_substitute(normalized,mapping['pivots'],seed,mapping['width'],budget)
    candidate=EXACT.canonical_lift(restored,mapping['retained'],mapping['shape'],mapping['offset'],mapping['specs'],mapping['n_variables'],budget)
    diagnostics=EXACT.candidate_diagnostics(mapping['rows'],mapping['rhs'],candidate,mapping['offset'],mapping['specs'],budget)
    return dict(schema='primitive-state-free-cone-endpoint-v1',complete=True,normalized_basis_hash=mapping['normalized_basis_hash'],free_indices=mapping['free'],final_free_vector=list(map(str,free)),final_projected_vector=list(map(str,restored)),candidate_original_vector=list(map(str,candidate)),candidate_hash=digest(list(map(str,candidate))),diagnostics=diagnostics,counts=budget.counts(),**FLAGS)
