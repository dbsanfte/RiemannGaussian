"""Bounded three-block balanced cone-distance proposal on a licensed chart.

All eigensolves, gradients and simplex model solutions remain proposal data.
Only the original-coordinate exact endpoint gates decide finite feasibility.
"""
from fractions import Fraction as F
import math
import time
import primitive_state_cone_jacobi_search as J

OLD=J.OLD;EXACT=J.EXACT;encoded=J.encoded;digest=J.digest
SCHEMA='primitive-state-balanced-cone-search-v1'
FLAGS=dict(J.FLAGS,model_optimality_certified=False,block_gradients_certified=False)
PRECISION=dict(J.PRECISION,model_arithmetic='fixed80decimaldigits',warm_increment_exactly_represented=True)
MODEL=dict(block_order=['scalar','C','H'],penalty='half squared cone distance',objective='max(p_i/b_i)',normalizer_floor='1/1099511627776',normalizer_rule='max(exact exported initial numerical penalty, floor); fixed throughout',dual='r dot lambda - alpha/2 * norm(sum lambda_i*g_i)^2',faces=[[0],[1],[2],[0,1],[0,2],[1,2],[0,1,2]],simplex_dyadic_bits=240,simplex_rounding='edge floor t; interior floor first two; exact complement',interior_relative_determinant_tolerance='1/1461501637330902918203684832716283019655932542976',model_gap_relative_tolerance='1e-40',model_gap_scale='max(1,max abs r,max abs model scores,alpha*aggregate_gradient_squared_norm)',model_inconsistency_policy='UNKNOWN; no retry',near_singular_policy='omit interior as numerical proposal; all boundary faces remain; no rank claim',tie_rule='first face in declared order after quantization and rescoring')
SEARCH=dict(power_steps=8,gradient_iterations=96,armijo_trials=3,armijo_coefficient='1/8',step_min_binary_exponent=-900,step_max_binary_exponent=900,power_operator='sum of normalized block quadratic curvature operators',positive_dyadic_cone_jacobi=True,initial_step='clamped reciprocal of eight-step weighted power estimate',native_eigh_work_coefficient=96,iteration_budget_policy='reserve three trials and three accepted block adjoints before iteration',model_recomputed_each_trial=True)
SCALING=dict(J.SCALING,reused_publication020_records=True,new_column_responses=0)
SEED='base publication018 exact free vector plus reused D times publication020 final_z_mp; one warm seed; no clipping or rerounding'


class ModelConsistencyError(ValueError):
    def __init__(self,record):
        self.record=record
        super().__init__('fixed numerical model-gap consistency gate failed')


def materialize(cache,basis,projection,parent_restoration,base_endpoint,warm_endpoint,*,deadline,max_operations=50000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096):
    mapping,receipt=J.materialize(cache,basis,projection,parent_restoration,base_endpoint,deadline=deadline,max_operations=max_operations,max_live_cells=max_live_cells,max_fill_cells=max_fill_cells,max_bits=max_bits)
    budget=EXACT.Budget(deadline,max_operations,max_live_cells,max_fill_cells,max_bits);budget.operations=receipt['counts']['operations'];budget.peak_live_cells=receipt['counts']['peak_live_cells'];budget.fill_cells=receipt['counts']['fill_cells']
    if warm_endpoint.get('complete')is not True or warm_endpoint.get('normalized_basis_hash')!=mapping['normalized_basis_hash'] or warm_endpoint.get('free_indices')!=mapping['free']:raise ValueError('complete same-chart publication020 warm endpoint')
    warm=[budget.q(v) for v in warm_endpoint['final_projected_vector']]
    if len(warm)!=mapping['width'] or [str(warm[j]) for j in mapping['free']]!=warm_endpoint['final_free_vector']:raise ValueError('complete warm projected/free vector')
    mapping.update(base_endpoint_hash=mapping['seed_endpoint_hash'],warm_endpoint_hash=digest(warm_endpoint),warm_projected=warm)
    receipt.update(schema='primitive-state-balanced-cone-map-v1',precision=PRECISION,seed_rule=SEED,base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_projected_hash=digest(list(map(str,warm))),counts=budget.counts(),**FLAGS)
    return mapping,receipt


def warm_setup(mapping,norms,warm_proposal,warm_endpoint,*,deadline,max_operations=5000000,max_bits=4096):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,8192)
    if norms.get('complete')is not True or norms.get('status')!='scaled' or norms.get('normalized_basis_hash')!=mapping['normalized_basis_hash'] or norms.get('seed_endpoint_hash')!=mapping['base_endpoint_hash'] or norms.get('scaling')!=J.SCALING:raise ValueError('reused immutable positive Jacobi diagonal')
    records=norms['records'];budget.charge(len(encoded(records))+1)
    if len(records)!=len(mapping['free']) or norms.get('records_hash')!=digest(records):raise ValueError('complete reused column records')
    scales=[]
    for index,(j,r) in enumerate(zip(mapping['free'],records)):
        text=r.get('norm')
        if type(text)is not str or len(text)>10000 or r.get('index')!=index or r.get('free_index')!=j:raise ValueError('bounded reused scale coordinates')
        budget.charge(len(text)+40);g=budget.q(text);k,D=J.dyadic_scale(g)
        if r.get('exponent')!=k or r.get('scale')!=str(D):raise ValueError('exact positive dyadic rule from unverified norm records')
        scales.append(D)
    if warm_proposal.get('complete')is not True or warm_proposal.get('status')!='proposed' or warm_proposal.get('normalized_basis_hash')!=mapping['normalized_basis_hash'] or warm_proposal.get('seed_endpoint_hash')!=mapping['base_endpoint_hash'] or warm_proposal.get('norm_records_hash')!=norms['records_hash'] or digest(warm_endpoint)!=mapping['warm_endpoint_hash']:raise ValueError('one complete publication020 scaled proposal/endpoint')
    z=[J._checked(OLD.record_fraction(r,max_bits=max_bits),max_bits) for r in warm_proposal['final_z_mp']];budget.charge(10*len(z))
    if len(z)!=len(scales):raise ValueError('complete publication020 warm z')
    free=[J._checked(c+D*q,max_bits) for c,D,q in zip(mapping['initial'],scales,z)];budget.charge(4*len(z))
    if list(map(str,free))!=warm_endpoint['final_free_vector'] or warm_proposal['final_free_vector']!=warm_endpoint['final_free_vector']:raise ValueError('exact base018+D*z020 warm agreement; no535bit reround')
    ctx=mapping['ctx'];base_mp=[OLD.to_mp(q,ctx,budget) for q in mapping['initial']];scale_mp=[OLD.to_mp(q,ctx,budget) for q in scales];warm_mp=[OLD.to_mp(q,ctx,budget) for q in z]
    if any(OLD.record_fraction(OLD.mp_record(v))!=q for v,q in zip(base_mp,mapping['initial'])) or any(OLD.record_fraction(OLD.mp_record(v))!=q for v,q in zip(warm_mp,z)):raise ValueError('base and warm increment exact269bit representations')
    budget.charge(2*(len(encoded(warm_proposal))//64+1))
    mapping.update(scales=scales,scale_mp=scale_mp,center_mp=base_mp,warm_z=warm_mp,norm_records_hash=norms['records_hash'],warm_proposal_hash=digest(warm_proposal));budget.cells(mapping['resident_cells']+12*len(z))
    receipt=dict(schema='primitive-state-balanced-cone-warm-v1',complete=True,normalized_basis_hash=mapping['normalized_basis_hash'],base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_proposal_hash=mapping['warm_proposal_hash'],norm_records_hash=mapping['norm_records_hash'],initial_free_vector=list(map(str,mapping['initial'])),warm_free_vector=list(map(str,free)),initial_z_mp=[OLD.mp_record(v) for v in warm_mp],scale_vector=list(map(str,scales)),precision=PRECISION,scaling=SCALING,seed_rule=SEED,new_column_responses=0,counts=budget.counts(),**FLAGS)
    mapping['warm_setup_counts']=receipt['counts'];return receipt


def calibrate(mapping,budget):
    ctx=mapping['ctx'];z=list(mapping['warm_z']);x,diag,_=J.scaled_forward(mapping,z,budget,diagnostics=True)
    budget.charge(10*len(x));actual=[OLD.record_fraction(OLD.mp_record(v)) for v in x];error=max((abs(v-q)/max(F(1),abs(q)) for v,q in zip(actual,mapping['warm_projected'])),default=F(0))
    d=[ctx.mpf((-1)**j) for j in range(len(z))];g=[ctx.mpf((j%7)-3)/7 for j in range(mapping['width'])];Nd,_,_=J.scaled_forward(mapping,d,budget,linear=True);Ng=J.scaled_adjoint(mapping,g,budget)
    left=OLD.dot(ctx,Nd,g,budget);right=OLD.dot(ctx,d,Ng,budget);relative=abs(left-right)/max(ctx.one,abs(left),abs(right))
    receipt=dict(initial_forward_mp=[OLD.mp_record(v) for v in x],initial_exact_reference_relative_error=str(error),adjoint_pairing_relative_error=OLD.mp_record(relative),tolerance='1e-40',passed=error<=F(1,10**40) and relative<=ctx.mpf('1e-40'),initial_forward=diag,reference='exact publication020 projected endpoint')
    if not receipt['passed']:raise ValueError('fixed80digit warm affine-map consistency failed')
    return z,x,receipt


def block_metrics(mapping,x,budget,normalizers=None,*,apply_adjoint=True):
    import numpy as np
    ctx=mapping['ctx'];C,H=OLD.matrices(mapping,x,budget);negative=[];native=[]
    for matrix in (C,H):
        budget.charge(96*15**3);values=[]
        for row in matrix:
            line=[]
            for v in row:
                z=float(v)
                if not math.isfinite(z) or v and z==0:raise OverflowError('binary64 proposal matrix overflow/underflow')
                line.append(z)
            values.append(line)
        array=np.asarray(values,dtype=float);evals,evecs=np.linalg.eigh(array)
        if not np.all(np.isfinite(evals)) or not np.all(np.isfinite(evecs)):raise OverflowError('nonfinite binary64 proposal eigensolve')
        part=(evecs*np.minimum(evals,0.))@evecs.T;part=(part+part.T)/2.
        if not np.all(np.isfinite(part)):raise OverflowError('nonfinite binary64 proposal negative part')
        negative.append([[ctx.mpf(float(v)) for v in row] for row in part]);scale=max(1.,float(np.max(np.abs(array))));scaled=array/scale;den=max(1.,float(np.linalg.norm(scaled,'fro')))
        backward=float(np.linalg.norm(scaled@evecs-evecs*(evals/scale),'fro'))/den;orthogonal=float(np.linalg.norm(evecs.T@evecs-np.eye(15),'fro'));reconstruction=float(np.linalg.norm(scaled-(evecs*(evals/scale))@evecs.T,'fro'))/den;pairing=float(np.sum((part/scale)*(scaled-part/scale)))/max(1.,den**2)
        if not all(math.isfinite(v) for v in (backward,orthogonal,reconstruction,pairing)):raise OverflowError('nonfinite proposal PSD backward diagnostics')
        native.append(dict(minimum_eigenvalue=float(evals[0]),negative_eigenvalues=int(np.sum(evals<0)),scaled_eigen_backward_error=backward,eigenvector_orthogonality_error=orthogonal,scaled_eigen_reconstruction_error=reconstruction,scaled_negative_positive_pairing=pairing))
    penalties=[ctx.fsum(min(x[j],ctx.zero)**2 for j in mapping['scalar_indices'])/2]+[ctx.fsum(v*v for row in m for v in row)/2 for m in negative];budget.charge(3*(len(mapping['scalar_indices'])+450))
    coords=[[ctx.zero]*mapping['width'] for _ in range(3)]
    for j in mapping['scalar_indices']:coords[0][j]=min(x[j],ctx.zero)
    for (a,b),ci,pi in zip(mapping['gram_pairs'],mapping['C_indices'],mapping['P_indices']):
        factor=1 if a==b else 2;coords[1][ci]=factor*negative[0][a][b];coords[2][ci]=4*factor*negative[1][a][b];coords[2][pi]=factor*negative[1][a][b];budget.charge(5)
    budget.charge(len(mapping['scalar_indices'])+3*mapping['width'])
    if not all(ctx.isfinite(p) and p>=0 for p in penalties):raise OverflowError('finite nonnegative block penalties')
    if normalizers is not None:
        if len(normalizers)!=3 or any(not ctx.isfinite(v) or v<=0 for v in normalizers):raise ValueError('fixed positive block normalizers')
        coords=[[v/b for v in row] for row,b in zip(coords,normalizers)];budget.charge(3*mapping['width'])
    gradients=[J.scaled_adjoint(mapping,g,budget) for g in coords] if apply_adjoint else coords
    return penalties,gradients,dict(native_negative_parts=native,block_penalties=[OLD.mp_record(p) for p in penalties])


def weighted_power_operator(mapping,d,normalizers,budget):
    x,_,_=J.scaled_forward(mapping,d,budget,linear=True);C,H=OLD.matrices(mapping,x,budget);ctx=mapping['ctx'];g=[ctx.zero]*mapping['width']
    for j in mapping['scalar_indices']:g[j]=x[j]/normalizers[0]
    for (a,b),ci,pi in zip(mapping['gram_pairs'],mapping['C_indices'],mapping['P_indices']):
        factor=1 if a==b else 2;g[ci]=factor*(C[a][b]/normalizers[1]+4*H[a][b]/normalizers[2]);g[pi]=factor*H[a][b]/normalizers[2];budget.charge(9)
    budget.charge(len(mapping['scalar_indices']));return J.scaled_adjoint(mapping,g,budget)


def _grid_floor(v):
    q=OLD.record_fraction(OLD.mp_record(v));scaled=q*(1<<240)
    return F(scaled.numerator//scaled.denominator,1<<240)


def simplex_model(ctx,r,gradients,alpha,budget):
    """Seven numerical faces; feasible dyadic weights, not a QP certificate."""
    if len(r)!=3 or len(gradients)!=3 or any(len(g)!=len(gradients[0]) for g in gradients) or not ctx.isfinite(alpha) or alpha<=0:raise ValueError('three finite block model gradients and positive step')
    if not all(ctx.isfinite(v) for v in r) or not all(ctx.isfinite(v) for g in gradients for v in g):raise OverflowError('finite model inputs')
    gram=[[OLD.dot(ctx,a,b,budget) for b in gradients] for a in gradients];candidates=[]
    def candidate(face,weights):
        if any(q<0 for q in weights) or sum(weights,F(0))!=1:raise ValueError('exact dyadic feasible simplex weights')
        lam=[OLD.to_mp(q,ctx,budget) for q in weights]
        qform=ctx.fsum(lam[i]*gram[i][j]*lam[j] for i in range(3) for j in range(3));linear=ctx.fsum(lam[i]*r[i] for i in range(3));dual=linear-alpha*qform/2;budget.charge(60)
        if not ctx.isfinite(dual):raise OverflowError('finite numerical model score')
        candidates.append(dict(face=face,lambda_vector=list(map(str,weights)),dual=OLD.mp_record(dual)));return dual
    for i in range(3):candidate([i],[F(int(i==j)) for j in range(3)])
    edge_data=[]
    for i,j in ((0,1),(0,2),(1,2)):
        denominator=gram[i][i]-2*gram[i][j]+gram[j][j];slope=(r[i]-r[j])/alpha-(gram[j][i]-gram[j][j]);budget.charge(10)
        if denominator<0:raise ValueError('negative numerical edge curvature')
        t=max(ctx.zero,min(ctx.one,slope/denominator)) if denominator else (ctx.one if slope>0 else ctx.zero)
        q=_grid_floor(t);weights=[F(0)]*3;weights[i]=q;weights[j]=1-q;candidate([i,j],weights)
        edge_data.append(dict(face=[i,j],denominator=OLD.mp_record(denominator),slope=OLD.mp_record(slope),unquantized_t=OLD.mp_record(t)))
    a=gram[0][0]-2*gram[0][2]+gram[2][2];b=gram[0][1]-gram[0][2]-gram[1][2]+gram[2][2];c=gram[1][1]-2*gram[1][2]+gram[2][2]
    det=a*c-b*b;threshold=ctx.power(2,-160)*max(abs(a*c),abs(b*b));budget.charge(30)
    if a<0 or c<0 or det < -threshold:raise ValueError('negative numerical interior curvature')
    interior=dict(difference_gram=[OLD.mp_record(a),OLD.mp_record(b),OLD.mp_record(c)],determinant=OLD.mp_record(det),determinant_tolerance=OLD.mp_record(threshold),disposition='near_singular_numerical_boundary_only')
    if det>threshold:
        u=(r[0]-r[2])/alpha-(gram[0][2]-gram[2][2]);v=(r[1]-r[2])/alpha-(gram[1][2]-gram[2][2]);l0=(c*u-b*v)/det;l1=(a*v-b*u)/det;budget.charge(30)
        interior.update(rhs=[OLD.mp_record(u),OLD.mp_record(v)],unquantized_lambda=[OLD.mp_record(l0),OLD.mp_record(l1)],disposition='outside_simplex')
        if l0>=0 and l1>=0 and l0+l1<=1:
            q0=_grid_floor(l0);q1=_grid_floor(l1);candidate([0,1,2],[q0,q1,1-q0-q1]);interior['disposition']='included'
    best=0
    for k in range(1,len(candidates)):
        if OLD.record_fraction(candidates[k]['dual'])>OLD.record_fraction(candidates[best]['dual']):best=k
    weights=list(map(F,candidates[best]['lambda_vector']));lam=[OLD.to_mp(q,ctx,budget) for q in weights];n=len(gradients[0]);aggregate=[ctx.fsum(lam[i]*gradients[i][j] for i in range(3)) for j in range(n)];direction=[-alpha*v for v in aggregate];budget.charge(8*n)
    norm2=OLD.dot(ctx,direction,direction,budget);gnorm2=OLD.dot(ctx,aggregate,aggregate,budget);scores=[r[i]+OLD.dot(ctx,gradients[i],direction,budget) for i in range(3)];average=ctx.fsum(lam[i]*scores[i] for i in range(3));gap=max(scores)-average
    scale=max(ctx.one,*map(abs,r),*map(abs,scores),alpha*gnorm2);tolerance=ctx.mpf('1e-40')*scale;active=max((abs(scores[i]-average) for i in range(3) if weights[i]),default=ctx.zero);inactive=max([ctx.zero,*[scores[i]-average for i in range(3) if not weights[i]]]);budget.charge(40)
    record=dict(gram=[[OLD.mp_record(q) for q in row] for row in gram],candidates=candidates,edge_data=edge_data,interior=interior,selected_candidate=best,lambda_vector=list(map(str,weights)),direction=[OLD.mp_record(q) for q in direction],direction_squared_norm=OLD.mp_record(norm2),aggregate_gradient_squared_norm=OLD.mp_record(gnorm2),model_scores=[OLD.mp_record(q) for q in scores],model_gap=OLD.mp_record(gap),model_gap_scale=OLD.mp_record(scale),model_gap_tolerance=OLD.mp_record(tolerance),model_consistent=abs(gap)<=tolerance,active_KKT_residual=OLD.mp_record(active),inactive_KKT_violation=OLD.mp_record(inactive),dual=candidates[best]['dual'])
    if not record['model_consistent']:raise ModelConsistencyError(record)
    return direction,norm2,record


def iteration_work_reserve(mapping):
    E=sum(map(len,mapping['converted'].values()));w=mapping['width'];n=len(mapping['free']);sc=len(mapping['scalar_indices']);pairs=len(mapping['gram_pairs']);p=len(mapping['pivots'])
    forward=4*E+2*p+w+2*n
    metrics=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)+6*w
    adjoints=3*(2*E+w+n)
    model=200*n+8192
    return 3*(forward+metrics+model+4*n+16384)+adjoints+4096*n+131072


def propose(mapping,*,deadline,max_operations=130000000,checkpoint=None,max_trace_bytes=16777216):
    budget=EXACT.Budget(deadline,max_operations,4000000,20000000,4096);ctx=mapping['ctx'];start=time.monotonic();best=None;trace_bytes=0
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,normalized_basis_hash=mapping['normalized_basis_hash'],base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_proposal_hash=mapping['warm_proposal_hash'],norm_records_hash=mapping['norm_records_hash'],warm_setup_counts=mapping['warm_setup_counts'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    def save(phase):
        budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+60*mapping['width']+12*len(mapping['free'])*(4+2*len(out['power_trace'])+6*len(out['iterations'])))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        z,x,calibration=calibrate(mapping,budget);out['calibration']=calibration;out['initial_z_mp']=[OLD.mp_record(v) for v in z]
        penalties,coordinate,details=block_metrics(mapping,x,budget,apply_adjoint=False);floor=F(MODEL['normalizer_floor']);b=[max(OLD.record_fraction(OLD.mp_record(p)),floor) for p in penalties];normalizers=[OLD.to_mp(q,ctx,budget) for q in b];r=[p/v for p,v in zip(penalties,normalizers)];value=max(r);best=list(z)
        out.update(initial_block_penalties=[OLD.mp_record(p) for p in penalties],normalizers=list(map(str,b)),initial_normalized_blocks=[OLD.mp_record(q) for q in r],initial_objective=OLD.mp_record(value),initial_merit_details=details)
        stop='zero_initial_numerical_defect' if value==0 else 'iteration_limit'
        if value:
            gradients=[J.scaled_adjoint(mapping,[v/bb for v in g],budget) for g,bb in zip(coordinate,normalizers)];budget.charge(3*mapping['width']);d=[ctx.mpf((-1)**j)/ctx.sqrt(len(z)) for j in range(len(z))];estimate=ctx.zero
            for k in range(8):
                v=weighted_power_operator(mapping,d,normalizers,budget);den=OLD.dot(ctx,d,d,budget);estimate=OLD.dot(ctx,d,v,budget)/den;norm=ctx.sqrt(OLD.dot(ctx,v,v,budget));out['power_trace'].append(dict(index=k,vector=[OLD.mp_record(q) for q in d],operator=[OLD.mp_record(q) for q in v],estimate=OLD.mp_record(estimate),operator_norm=OLD.mp_record(norm)))
                if norm==0:break
                d=[q/norm for q in v];budget.charge(len(d))
            lower=ctx.power(2,-900);upper=ctx.power(2,900);alpha=max(lower,min(upper,ctx.one/estimate if estimate>0 else upper));out['initial_step']=OLD.mp_record(alpha);trace_bytes=len(encoded(out));budget.charge(trace_bytes)
            final_trace_reserve=8192+3000*len(z);iteration_trace_reserve=65536+12*96*len(z)
            for k in range(96):
                required_work=iteration_work_reserve(mapping);tail=max_trace_bytes+20000*len(z)+131072
                op_short=max_operations-budget.operations<required_work+tail;byte_short=max_trace_bytes-trace_bytes<iteration_trace_reserve+final_trace_reserve
                if op_short or byte_short:
                    stop='budget_stop';out['budget_stop']=dict(before_iteration=k,operations=budget.operations,max_operations=max_operations,remaining_operations=max_operations-budget.operations,worst_iteration_work_reserve=required_work,finalization_work_reserve=tail,trace_retained_bytes=trace_bytes,max_trace_bytes=max_trace_bytes,worst_iteration_trace_bytes=iteration_trace_reserve,finalization_trace_bytes=final_trace_reserve,resource='operations' if op_short else 'trace_bytes');break
                save('balanced_iteration');entry=dict(index=k,objective_before=OLD.mp_record(value),normalized_blocks=[OLD.mp_record(q) for q in r],block_gradients=[[OLD.mp_record(q) for q in g] for g in gradients],trials=[],accepted=False,reserved_iteration_work=required_work);out['iterations'].append(entry);accepted=False;stationary=False
                for trial in range(3):
                    trialalpha=alpha/ctx.power(2,trial)
                    if trialalpha<lower:entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),finite=False,reason='step below declared minimum'));continue
                    try:direction,norm2,model=simplex_model(ctx,r,gradients,trialalpha,budget)
                    except ModelConsistencyError as error:
                        entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),model=error.record,finite=False,reason=str(error)))
                        raise
                    if norm2==0:
                        entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),model=model,finite=True,stationary=True));stop='numerical_model_stationarity';stationary=True;break
                    trialz=[v+d for v,d in zip(z,direction)];budget.charge(len(z));trialx,diag,approximate=J.scaled_forward(mapping,trialz,budget,diagnostics=True);pnew,gnew,info=block_metrics(mapping,trialx,budget,normalizers,apply_adjoint=False);rnew=[p/bb for p,bb in zip(pnew,normalizers)];newvalue=max(rnew);threshold=value-norm2/(8*trialalpha);budget.charge(12)
                    record=dict(index=trial,step=OLD.mp_record(trialalpha),model=model,z=[OLD.mp_record(q) for q in trialz],approximate_free_mp=[OLD.mp_record(q) for q in approximate],block_penalties=[OLD.mp_record(q) for q in pnew],normalized_blocks=[OLD.mp_record(q) for q in rnew],objective=OLD.mp_record(newvalue),armijo_threshold=OLD.mp_record(threshold),armijo_passed=newvalue<=threshold,forward=diag,merit_details=info,finite=True);entry['trials'].append(record)
                    if newvalue<=threshold:
                        z=trialz;x=trialx;r=rnew;value=newvalue;alpha=trialalpha;best=list(z);entry['accepted']=True;accepted=True;gradients=[J.scaled_adjoint(mapping,g,budget) for g in gnew];break
                raw=encoded(entry);budget.charge(len(raw));trace_bytes+=len(raw)+1
                if len(raw)>iteration_trace_reserve or budget.operations>max_operations-tail:raise OverflowError('declared balanced iteration reservation exceeded')
                if stationary:break
                if not accepted:stop='line_search_failed';break
        final_z=[OLD.record_fraction(OLD.mp_record(v)) for v in best];budget.charge(10*len(best));free=[J._checked(c+D*q,4096) for c,D,q in zip(mapping['initial'],mapping['scales'],final_z)]
        out.update(status='proposed',complete=True,stop_reason=stop,final_objective=OLD.mp_record(value),final_normalized_blocks=[OLD.mp_record(q) for q in r],final_z_mp=[OLD.mp_record(q) for q in best],final_free_vector=list(map(str,free)));save('proposal_complete')
    except Exception as e:
        out.update(status='unknown',complete=False,reason=str(e) or type(e).__name__,error_type=type(e).__name__)
        if best is not None:out['last_finite_z_mp']=[OLD.mp_record(v) for v in best]
    budget.charge(len(encoded(out)));out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    if len(encoded(out))>max_trace_bytes:raise OverflowError('bounded balanced proposal trace')
    return out


def exact_endpoint(mapping,proposal,*,deadline,max_operations=20000000,max_bits=4096):
    if proposal.get('base_endpoint_hash')!=mapping['base_endpoint_hash'] or proposal.get('warm_endpoint_hash')!=mapping['warm_endpoint_hash'] or proposal.get('warm_proposal_hash')!=mapping['warm_proposal_hash']:raise ValueError('one bound centered balanced endpoint')
    value=dict(proposal,seed_endpoint_hash=mapping['base_endpoint_hash']);result=J.exact_endpoint(mapping,value,deadline=deadline,max_operations=max_operations,max_bits=max_bits)
    result.update(schema='primitive-state-balanced-cone-endpoint-v1',base_endpoint_hash=mapping['base_endpoint_hash'],warm_endpoint_hash=mapping['warm_endpoint_hash'],warm_proposal_hash=mapping['warm_proposal_hash'],**FLAGS);return result
