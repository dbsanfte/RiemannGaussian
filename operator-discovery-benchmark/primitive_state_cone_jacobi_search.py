"""Bounded proposal-only exact-column Jacobi scaling of a licensed affine chart.

The reported rational norms are not independent certificates. Strictly positive
scales preserve the original finite cone; admission uses the exact endpoint.
"""
from fractions import Fraction as F
import time
import primitive_state_free_cone_search as OLD
import primitive_state_triangular_restoration as EXACT

SCHEMA='primitive-state-cone-jacobi-search-v1'
FLAGS=dict(OLD.FLAGS,column_norms_independently_verified=False,scaled_trace_bound_certified=False)
PRECISION=dict(OLD.PRECISION,centered_coordinate_updates=True,final_free_exact_sum_not_269bit_rerounded=True)
SEARCH=dict(OLD.SEARCH,gradient_iterations=64,identity_free_coordinate_scaling=False,positive_dyadic_cone_jacobi=True,iteration_budget_policy='reserve three full trials plus one accepted adjoint before iteration')
SCALING=dict(response_bits=4096,norm_bits=8192,exponent_abs_cap=900,temporary_bits=16385,zero_norm_scale='1',nonzero_rule='2^(2*(k-1)) < g <= 2^(2*k); D=2^(-k)',homogeneous_rhs=True,scalar_coordinates='all squares and five slacks',matrix_coordinates='C and P+4C',offdiagonal_frobenius_factor=2,producer_exact_rational=True,independently_verified=False)
SEED='publication018 complete exact endpoint free coordinates; centered f=f0+D*z; z=0; one seed; no clipping'
encoded=OLD.encoded;digest=OLD.digest


def materialize(cache,basis,projection,parent_restoration,seed_endpoint,*,deadline,max_operations=50000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096):
    mapping,receipt=OLD.materialize(cache,basis,projection,parent_restoration,deadline=deadline,max_operations=max_operations,max_live_cells=max_live_cells,max_fill_cells=max_fill_cells,max_bits=max_bits)
    budget=EXACT.Budget(deadline,max_operations,max_live_cells,max_fill_cells,max_bits)
    budget.operations=receipt['counts']['operations'];budget.peak_live_cells=receipt['counts']['peak_live_cells'];budget.fill_cells=receipt['counts']['fill_cells']
    if seed_endpoint.get('complete')is not True or seed_endpoint.get('normalized_basis_hash')!=mapping['normalized_basis_hash'] or seed_endpoint.get('free_indices')!=mapping['free']:raise ValueError('one licensed publication018 endpoint seed')
    seed=[budget.q(v) for v in seed_endpoint['final_projected_vector']]
    if len(seed)!=mapping['width'] or [str(seed[j]) for j in mapping['free']]!=seed_endpoint['final_free_vector']:raise ValueError('complete seed projected/free agreement')
    mapping['parent_projected']=seed;mapping['initial']=[seed[j] for j in mapping['free']];mapping['seed_endpoint_hash']=digest(seed_endpoint);mapping['initial_projected_hash']=digest(list(map(str,seed)))
    mapping['resident_cells']=receipt['counts']['peak_live_cells']
    receipt.update(schema='primitive-state-cone-jacobi-map-v1',initial_free_vector=list(map(str,mapping['initial'])),precision=PRECISION,seed_rule=SEED,seed_endpoint_hash=mapping['seed_endpoint_hash'],initial_projected_hash=mapping['initial_projected_hash'],counts=budget.counts(),**FLAGS)
    return mapping,receipt


def rational_bits(q):return max(abs(q.numerator).bit_length(),q.denominator.bit_length())

def _checked(q,cap):
    if type(q)is not F:q=F(q)
    if rational_bits(q)>cap:raise OverflowError('Jacobi rational bit cap')
    return q


def dyadic_scale(norm,*,exponent_abs_cap=900):
    """Exact integer comparisons; no floating logarithm or clipping."""
    if type(exponent_abs_cap)is not int or not 1<=exponent_abs_cap<=900:raise ValueError('bounded Jacobi exponent cap')
    norm=_checked(norm,8192)
    if norm<0:raise ValueError('nonnegative cone column norm')
    if norm==0:return 0,F(1)
    # Search a fixed bounded integer interval. Comparisons multiply bounded
    # integers by at most 2^1800; no unbounded exponent allocations.
    def at_most(k):
        return norm.numerator<=norm.denominator*(1<<(2*k)) if k>=0 else norm.numerator*(1<<(-2*k))<=norm.denominator
    if not at_most(exponent_abs_cap) or at_most(-exponent_abs_cap-1):raise OverflowError('Jacobi required exponent outside declared range')
    lo=-exponent_abs_cap;hi=exponent_abs_cap
    while lo<hi:
        mid=(lo+hi)//2
        if at_most(mid):hi=mid
        else:lo=mid+1
    k=lo;return k,F(1,1<<k) if k>=0 else F(1<<(-k))


def homogeneous_response(mapping,free_index,budget,*,max_bits=4096):
    """One exact response; augmented RHS deliberately never enters the solve."""
    if free_index not in mapping['free']:raise ValueError('declared nonpivot coordinate')
    if max_bits!=4096:raise ValueError('fixed4096bit response cap')
    width=mapping['width'];x=[F(0)]*width;x[free_index]=F(1);budget.charge(width)
    for p in reversed(mapping['pivots']):
        value=F(0)
        for j,q in mapping['normalized'][p].items():
            if j not in (p,width):
                budget.charge(2)
                # Inputs <=4096bits; bounded temporary product<=8192 and
                # subtraction<=8193bits before the output bit check.
                if rational_bits(q)>max_bits or rational_bits(x[j])>max_bits or rational_bits(value)>max_bits:raise OverflowError('preallocation homogeneous operand bits')
                if not x[j]:continue  # Same charge and validated operands; exact zero product.
                term=_checked(q*x[j],max_bits);value=_checked(value-term,max_bits)
        x[p]=value
    budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+width+len(mapping['free']))
    return x


def cone_norm(mapping,response,budget,*,norm_bits=8192):
    if norm_bits!=8192:raise ValueError('fixed8192bit norm cap')
    if any(type(q)is not F or rational_bits(q)>4096 for q in response):raise OverflowError('preallocation norm response bits')
    budget.charge(len(response));value=F(0);peak=0
    def add_square(v,factor=1):
        nonlocal value,peak
        budget.charge(3)
        if rational_bits(v)>4096 or rational_bits(value)>norm_bits:raise OverflowError('preallocation norm operand bits')
        # Responses<=4096bits; square/factor<=8194. Accumulator and term
        # <=8192bits give <=16385bit addition temporary, then cap immediately.
        term=_checked(factor*v*v,norm_bits);value=_checked(value+term,norm_bits);peak=max(peak,rational_bits(term),rational_bits(value))
    for j in mapping['scalar_indices']:add_square(response[j])
    for (a,b),ci,pi in zip(mapping['gram_pairs'],mapping['C_indices'],mapping['P_indices']):
        budget.charge(2);h=_checked(response[pi]+4*response[ci],4096);factor=1 if a==b else 2
        add_square(response[ci],factor);add_square(h,factor)
    return value,peak


def cone_column_norms(mapping,*,deadline,max_operations=100000000,max_receipt_bytes=2097152,response_bits=4096,norm_bits=8192,exponent_abs_cap=900,checkpoint=None):
    if (response_bits,norm_bits,exponent_abs_cap)!=(4096,8192,900):raise ValueError('one fixed Jacobi bit/exponent policy')
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,norm_bits);start=time.monotonic();records=[];record_bytes=0
    out=dict(schema='primitive-state-cone-jacobi-norms-v1',complete=False,status='unknown',normalized_basis_hash=mapping['normalized_basis_hash'],seed_endpoint_hash=mapping['seed_endpoint_hash'],scaling=SCALING,records=records,**FLAGS)
    try:
        for index,j in enumerate(mapping['free']):
            response=homogeneous_response(mapping,j,budget,max_bits=response_bits);g,peak=cone_norm(mapping,response,budget,norm_bits=norm_bits);budget.charge(32)
            k,D=dyadic_scale(g,exponent_abs_cap=exponent_abs_cap)
            record=dict(index=index,free_index=j,norm=str(g),exponent=k,scale=str(D),response_max_bits=max(map(rational_bits,response)),norm_max_bits=peak)
            raw=encoded(record);budget.charge(len(raw)+len(response));record_bytes+=len(raw)+1
            if record_bytes+4096>max_receipt_bytes:raise OverflowError('incremental Jacobi norm receipt byte cap')
            records.append(record)
            if checkpoint:checkpoint(dict(phase='norm_column_complete',completed_columns=len(records),counts=budget.counts(),**FLAGS))
        out.update(status='scaled',complete=True,records_hash=digest(records))
    except Exception as e:out.update(reason=str(e) or type(e).__name__,error_type=type(e).__name__)
    out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    if len(encoded(out))>max_receipt_bytes:raise OverflowError('bounded Jacobi norm receipt')
    return out


def install_scales(mapping,norm_receipt,*,deadline=None,max_operations=100000000):
    if norm_receipt.get('complete')is not True or norm_receipt.get('status')!='scaled' or norm_receipt.get('normalized_basis_hash')!=mapping['normalized_basis_hash'] or norm_receipt.get('seed_endpoint_hash')!=mapping['seed_endpoint_hash'] or norm_receipt.get('scaling')!=SCALING:raise ValueError('one complete proposal-only Jacobi diagonal')
    budget=EXACT.Budget(time.monotonic()+60 if deadline is None else deadline,max_operations,4000000,20000000,8192)
    prior=norm_receipt.get('counts',{}).get('operations')
    if type(prior)is not int or not 0<=prior<=max_operations:raise ValueError('bounded shared norm/setup work')
    budget.operations=prior;budget.peak_live_cells=norm_receipt['counts']['peak_live_cells'];budget.fill_cells=norm_receipt['counts']['fill_cells']
    budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+8*len(mapping['free']))
    records=norm_receipt['records'];budget.charge(len(encoded(records))+1)
    if norm_receipt.get('records_hash')!=digest(records) or len(records)!=len(mapping['free']):raise ValueError('complete scale records')
    scales=[]
    for index,(j,r) in enumerate(zip(mapping['free'],records)):
        if r.get('index')!=index or r.get('free_index')!=j or type(r.get('norm'))is not str or len(r['norm'])>10000:raise ValueError('bounded coordinate norm binding')
        budget.charge(len(r['norm'])+40);g=_checked(F(r['norm']),8192);k,D=dyadic_scale(g)
        if str(g)!=r['norm'] or r['exponent']!=k or r['scale']!=str(D):raise ValueError('exact exported norm scale rule')
        scales.append(D)
    budget.charge(8*len(scales));mapping['norm_setup_counts']=budget.counts()
    mapping['scales']=scales;mapping['scale_mp']=[mapping['ctx'].mpf(D.numerator)/mapping['ctx'].mpf(D.denominator) for D in scales];mapping['center_mp']=[mapping['ctx'].mpf(q.numerator)/mapping['ctx'].mpf(q.denominator) for q in mapping['initial']];mapping['norm_records_hash']=norm_receipt['records_hash']
    return mapping


def scaled_forward(mapping,z,budget,*,linear=False,diagnostics=False):
    if len(z)!=len(mapping['free']):raise ValueError('complete centered z vector')
    budget.charge((1 if linear else 2)*len(z))
    free=[d*v if linear else c+d*v for c,d,v in zip(mapping['center_mp'],mapping['scale_mp'],z)]
    x,diagnostic=OLD.forward(mapping,free,budget,linear=linear,diagnostics=diagnostics)
    return x,diagnostic,free


def scaled_adjoint(mapping,gradient,budget):
    value=OLD.adjoint(mapping,gradient,budget);budget.charge(len(value));return [d*v for d,v in zip(mapping['scale_mp'],value)]


def power_operator(mapping,d,budget):
    x,_,_=scaled_forward(mapping,d,budget,linear=True);C,H=OLD.matrices(mapping,x,budget)
    return scaled_adjoint(mapping,OLD.coordinate_gradient(mapping,x,C,H,budget,scalar_negative=False),budget)


def calibrate(mapping,budget):
    ctx=mapping['ctx'];z=[ctx.zero]*len(mapping['free']);x,diag,free=scaled_forward(mapping,z,budget,diagnostics=True)
    if any(OLD.record_fraction(OLD.mp_record(v))!=q for v,q in zip(free,mapping['initial'])):raise ValueError('publication018 initial free conversion must be exactly represented at80digits')
    budget.charge(10*len(x));actual=[OLD.record_fraction(OLD.mp_record(v)) for v in x];error=max((abs(v-q)/max(F(1),abs(q)) for v,q in zip(actual,mapping['parent_projected'])),default=F(0))
    d=[ctx.mpf((-1)**j) for j in range(len(z))];g=[ctx.mpf((j%7)-3)/7 for j in range(mapping['width'])];Nd,_,_=scaled_forward(mapping,d,budget,linear=True);Ng=scaled_adjoint(mapping,g,budget)
    left=OLD.dot(ctx,Nd,g,budget);right=OLD.dot(ctx,d,Ng,budget);relative=abs(left-right)/max(ctx.one,abs(left),abs(right))
    result=dict(initial_forward_mp=[OLD.mp_record(v) for v in x],initial_exact_reference_relative_error=str(error),adjoint_pairing_relative_error=OLD.mp_record(relative),tolerance='1e-40',passed=error<=F(1,10**40) and relative<=ctx.mpf('1e-40'),initial_forward=diag)
    if not result['passed']:raise ValueError('fixed80digit scaled affine-map consistency failed')
    return z,x,result


def iteration_work_reserve(mapping):
    """Upper bound on one full 3-trial step, including accepted adjoint.

    Sparse forward diagnostics are four units per nonpivot coefficient, adjoint
    two. Native eigenwork is96*2*15^3 pertrial. Record encoding is separately
    reserved at byte granularity by a conservative perstep bound.
    """
    entries=sum(map(len,mapping['converted'].values()));w=mapping['width'];n=len(mapping['free']);sc=len(mapping['scalar_indices']);pairs=len(mapping['gram_pairs'])
    forward=4*entries+2*len(mapping['pivots'])+w+2*n
    merit=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)
    adjoint=2*entries+w+n
    arithmetic=3*(2*n+forward+merit+32*n+4096)+adjoint+2*n+8*n+4096
    # A normalized mp record has at most ~90bytes; three trial z/free and
    # gradient records plus metadata. Charged before iteration and export.
    return arithmetic+2048*n+65536


def propose(mapping,*,deadline,max_operations=80000000,checkpoint=None,max_trace_bytes=8388608):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,4096);ctx=mapping['ctx'];start=time.monotonic();best=None;trace_bytes=0
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,scaling=SCALING,seed_rule=SEED,normalized_basis_hash=mapping['normalized_basis_hash'],seed_endpoint_hash=mapping['seed_endpoint_hash'],norm_records_hash=mapping['norm_records_hash'],norm_setup_counts=mapping['norm_setup_counts'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    def save(phase):
        budget.cells(sum(map(len,mapping['normalized'].values()))+40*mapping['width']+8*len(mapping['free'])*(3+2*len(out['power_trace'])+5*len(out['iterations'])))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        z,x,calibration=calibrate(mapping,budget);out['calibration']=calibration;out['initial_z_mp']=[OLD.mp_record(v) for v in z];save('scaled_power_estimate')
        d=[ctx.mpf((-1)**j)/ctx.sqrt(len(z)) for j in range(len(z))];estimate=ctx.zero
        for k in range(8):
            v=power_operator(mapping,d,budget);den=OLD.dot(ctx,d,d,budget);estimate=OLD.dot(ctx,d,v,budget)/den;norm=ctx.sqrt(OLD.dot(ctx,v,v,budget));out['power_trace'].append(dict(index=k,vector=[OLD.mp_record(q) for q in d],operator=[OLD.mp_record(q) for q in v],estimate=OLD.mp_record(estimate),operator_norm=OLD.mp_record(norm)))
            if norm==0:break
            d=[q/norm for q in v];budget.charge(len(d))
        lower=ctx.power(2,-900);upper=ctx.power(2,900);alpha=max(lower,min(upper,ctx.one/estimate if estimate>0 else upper));out['initial_step']=OLD.mp_record(alpha)
        merit,g,info=OLD.merit_gradient(mapping,x,budget,apply_adjoint=False);gradient=scaled_adjoint(mapping,g,budget);best=list(z);out['initial_merit']=OLD.mp_record(merit);out['initial_merit_details']=info;stop='iteration_limit';trace_bytes=len(encoded(out));budget.charge(trace_bytes)
        final_trace_reserve=4096+3000*len(z);iteration_trace_reserve=16384+7*96*len(z)
        for k in range(64):
            required_work=iteration_work_reserve(mapping);out['next_iteration_work_reserve']=required_work
            # Leave bounded final trace encoding and exact-free export work.
            tail=max_trace_bytes+20000*len(z)+65536
            operation_shortfall=max_operations-budget.operations<required_work+tail
            byte_shortfall=max_trace_bytes-trace_bytes<iteration_trace_reserve+final_trace_reserve
            if operation_shortfall or byte_shortfall:
                stop='budget_stop';out['budget_stop']=dict(before_iteration=k,operations=budget.operations,max_operations=max_operations,remaining_operations=max_operations-budget.operations,worst_iteration_work_reserve=required_work,finalization_work_reserve=tail,trace_retained_bytes=trace_bytes,max_trace_bytes=max_trace_bytes,worst_iteration_trace_bytes=iteration_trace_reserve,finalization_trace_bytes=final_trace_reserve,resource='operations' if operation_shortfall else 'trace_bytes');break
            save('gradient_iteration');norm2=OLD.dot(ctx,gradient,gradient,budget);entry=dict(index=k,merit_before=OLD.mp_record(merit),gradient=[OLD.mp_record(q) for q in gradient],gradient_squared_norm=OLD.mp_record(norm2),trials=[],accepted=False,reserved_iteration_work=required_work);out['iterations'].append(entry)
            if norm2==0:
                raw=encoded(entry);budget.charge(len(raw));trace_bytes+=len(raw)+1;stop='zero_gradient';break
            accepted=False
            for trial in range(3):
                trialalpha=alpha/ctx.power(2,trial)
                if trialalpha<lower:entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),finite=False,reason='step below declared minimum'));continue
                trialz=[v-trialalpha*g for v,g in zip(z,gradient)];budget.charge(2*len(z));trialx,diag,approximate_free=scaled_forward(mapping,trialz,budget,diagnostics=True);value,newcoordinategradient,details=OLD.merit_gradient(mapping,trialx,budget,apply_adjoint=False);required=merit-trialalpha*norm2/8
                record=dict(index=trial,step=OLD.mp_record(trialalpha),z=[OLD.mp_record(q) for q in trialz],approximate_free_mp=[OLD.mp_record(q) for q in approximate_free],merit=OLD.mp_record(value),armijo_threshold=OLD.mp_record(required),armijo_passed=value<=required,forward=diag,merit_details=details,finite=True);entry['trials'].append(record)
                if value<=required:
                    z=trialz;x=trialx;merit=value;alpha=trialalpha;best=list(z);entry['accepted']=True;accepted=True;gradient=scaled_adjoint(mapping,newcoordinategradient,budget);break
            raw=encoded(entry);budget.charge(len(raw));trace_bytes+=len(raw)+1
            if len(raw)>iteration_trace_reserve or budget.operations>max_operations-tail:raise OverflowError('declared worst iteration reservation exceeded')
            if not accepted:stop='line_search_failed';break
        # Exact endpoint interpretation deliberately retains more than269bits.
        final_z=[OLD.record_fraction(OLD.mp_record(v)) for v in best];budget.charge(10*len(best));free=[_checked(c+D*q,4096) for c,D,q in zip(mapping['initial'],mapping['scales'],final_z)]
        out.update(status='proposed',complete=True,stop_reason=stop,final_merit=OLD.mp_record(merit),final_z_mp=[OLD.mp_record(q) for q in best],final_free_vector=list(map(str,free)));save('proposal_complete')
    except Exception as e:
        out.update(status='unknown',complete=False,reason=str(e) or type(e).__name__,error_type=type(e).__name__)
        if best is not None:out['last_finite_z_mp']=[OLD.mp_record(v) for v in best]
    budget.charge(len(encoded(out)))
    out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    if len(encoded(out))>max_trace_bytes:raise OverflowError('bounded complete Jacobi proposal trace')
    return out


def exact_endpoint(mapping,proposal,*,deadline,max_operations=20000000,max_bits=4096):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,max_bits)
    if proposal.get('complete')is not True or proposal.get('status')!='proposed' or proposal.get('seed_endpoint_hash')!=mapping['seed_endpoint_hash'] or proposal.get('norm_records_hash')!=mapping['norm_records_hash']:raise ValueError('one complete scaled proposal required')
    z=[budget.q(OLD.record_fraction(r,max_bits=max_bits)) for r in proposal['final_z_mp']]
    if len(z)!=len(mapping['free']):raise ValueError('complete final z')
    free=[budget.add(c,budget.mul(D,q)) for c,D,q in zip(mapping['initial'],mapping['scales'],z)]
    if list(map(str,free))!=proposal['final_free_vector']:raise ValueError('exact centered free addition; no269bit reround')
    seed=[F(0)]*mapping['width']
    for j,q in zip(mapping['free'],free):seed[j]=q
    restored=EXACT.back_substitute([mapping['normalized'][p] for p in mapping['pivots']],mapping['pivots'],seed,mapping['width'],budget)
    candidate=EXACT.canonical_lift(restored,mapping['retained'],mapping['shape'],mapping['offset'],mapping['specs'],mapping['n_variables'],budget)
    diagnostics=EXACT.candidate_diagnostics(mapping['rows'],mapping['rhs'],candidate,mapping['offset'],mapping['specs'],budget)
    return dict(schema='primitive-state-cone-jacobi-endpoint-v1',complete=True,normalized_basis_hash=mapping['normalized_basis_hash'],seed_endpoint_hash=mapping['seed_endpoint_hash'],norm_records_hash=mapping['norm_records_hash'],free_indices=mapping['free'],final_free_vector=list(map(str,free)),final_projected_vector=list(map(str,restored)),candidate_original_vector=list(map(str,candidate)),candidate_hash=digest(list(map(str,candidate))),diagnostics=diagnostics,counts=budget.counts(),**FLAGS)
