"""Hash-free centered mixed-precision cone proposals on a saved exact chart."""
from fractions import Fraction as F
import math
import time
import primitive_state_feedback_affine as EXACT
import primitive_state_balanced_cone_search as B

OLD=B.OLD;J=B.J;encoded=EXACT.encoded
SCHEMA='primitive-state-feedback-cone-search-v1'
FLAGS=dict(EXACT.FLAGS,model_optimality_certified=False,block_gradients_certified=False,
           column_norms_independently_verified=False,new_map_preconditioner_certified=False)
PRECISION=dict(decimal_digits=80,binary_bits=269,actual_map_relative_tolerance='1e-40',
               serialized_binary_exponent_abs_cap=4096,mixed_precision=True,PSD_eigh='binary64',
               PSD_negative_parts='binary64',calibration_scope='affine center, one homogeneous direction and adjoint only',
               center_mp_is_approximation=True,endpoint_center_is_exact=True)
MODEL=dict(B.MODEL)
SEARCH=dict(B.SEARCH,gradient_iterations=128,positive_dyadic_cone_jacobi=False,
            cached_positive_dyadic_scales=True,
            accepted_step_carry='next start=min(2^900,2*accepted trial alpha); initial power step unchanged')
SCALING=dict(rule='retain old D on unaffected free columns; recompute approximate80digit cone norm on exact appended-row affected support',
             dropped_projected_free_index=148,exponent_abs_cap=900,new_column_responses=81,
             unchanged_column_scales=363,norms_verified=False,new_map_norm_preconditioner=False,
             cone_norm='all366 square and5 slack squares plus full C and H Frobenius squared norms',
             dyadic_rule='smallest integer k with exported approximate norm_squared <= 2^(2*k); D=2^(-k); zero=>1',
             precision='80 decimal digits; no exact or independently certified norm claim',
             partial_scaling_allowed=False)
SEED='exact publication024 projected endpoint; z0=0; exact center never rerounded for endpoint'

class Budget(EXACT.Budget):
    def __init__(self,deadline,max_operations=200000000,max_cells=6000000,max_bits=4096):
        if type(deadline)not in(int,float)or not math.isfinite(deadline):raise ValueError('finite search deadline')
        if any(type(v)is not int or v<1 for v in(max_operations,max_cells,max_bits))or max_operations>200000000 or max_cells>6000000 or max_bits>4096:raise ValueError('bounded search limits')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.max_bits=max_bits
        self.operations=0;self.peak_cells=0;self.maximum_bits=0;self.resident_cells=0

def decode_chart(chart,affine,budget):
    if chart.get('schema')!=EXACT.CHART_SCHEMA or chart.get('width')!=1224 or chart.get('original_width')!=1957 or chart.get('classification')!='independent'or chart.get('new_rank')!=780 or chart.get('old_rank')!=779:raise ValueError('complete fixed augmented chart')
    if affine.get('complete')is not True or affine.get('classification')!='independent'or affine.get('free_dimension')!=444 or affine.get('coefficient_rank')!=780 or affine.get('augmented_rank')!=780 or affine.get('chart_available')is not True:raise ValueError('complete publication024 affine repair')
    retained,recipes=EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
    if chart['retained_indices']!=retained:raise ValueError('unchanged original projection coordinates')
    old=chart['old_pivots'];pivots=chart['pivot_columns'];free=chart['free_indices'];oldfree=chart['old_free_indices']
    if type(old)is not list or len(old)!=779 or old!=sorted(set(old))or len(pivots)!=780 or pivots!=sorted(set(pivots))or len(free)!=444 or free!=sorted(set(free))or sorted(pivots+free)!=list(range(1224))or oldfree!=[j for j in range(1224)if j not in old]or free!=[j for j in oldfree if j!=148]or pivots!=sorted(old+[148]):raise ValueError('780-pivot/444-free partition with appended148')
    raw=chart['normalized_rows'];appended=chart['appended_row']
    if len(raw)!=779 or [r['pivot']for r in raw]!=old or appended.get('pivot')!=148 or appended.get('source_row')!='feedback':raise ValueError('complete old/new row records')
    normalized={}
    for record in [*raw,appended]:
        p=record['pivot'];row=EXACT.sparse(record['terms'],1224,budget)
        if row.get(p)!=1 or any(j<p for j in row):raise ValueError('upper triangular normalized cached row')
        normalized[p]=row
    center=[budget.q(q)for q in affine['candidate_projected_vector']]
    if len(center)!=1224 or EXACT.back_substitute(normalized,center,1224,budget)!=center:raise ValueError('exact center satisfies augmented chart')
    original=[budget.q(q)for q in affine['candidate_original_vector']]
    if original!=EXACT.canonical_lift(center,retained,budget):raise ValueError('exact024 canonical original center')
    budget.cells(sum(map(len,normalized.values()))+len(center)+len(original))
    return normalized,pivots,free,retained,recipes,center

def reused_scales(norms,free,budget):
    if norms.get('complete')is not True or norms.get('status')!='scaled':raise ValueError('complete reused020 scale records')
    records=norms['records'];by_index={}
    if len(records)!=445:raise ValueError('complete old445 scale records')
    for r in records:
        j=r.get('free_index');k=r.get('exponent')
        if type(j)is not int or not 0<=j<1224 or j in by_index or type(k)is not int or abs(k)>900:raise ValueError('bounded unique scale coordinates/exponents')
        D=budget.q(r['scale']);expected=F(1,1<<k)if k>=0 else F(1<<(-k))
        if D!=expected or D<=0:raise ValueError('exact positive dyadic reused scale')
        by_index[j]=(D,r)
    if set(by_index)!=set(free)|{148}:raise ValueError('oldscale set equals survivingfree plus148')
    return [by_index[j][0]for j in free],[by_index[j][1]for j in free]

def centered_forward(mapping,z,budget,*,linear=False,diagnostics=False):
    if len(z)!=len(mapping['free']):raise ValueError('complete centered coordinate vector')
    increments=[d*v for d,v in zip(mapping['scale_mp'],z)];budget.charge(len(z))
    delta,diag=OLD.forward(mapping,increments,budget,linear=True,diagnostics=diagnostics)
    x=delta if linear else [c+v for c,v in zip(mapping['center_projected_mp'],delta)]
    diag.update(scope='homogeneous delta triangular cancellation only; center addition is not covered',centered_maximum_coordinate=OLD.mp_record(max(map(abs,x),default=mapping['ctx'].zero)))
    budget.charge(2*mapping['width'])
    if not all(mapping['ctx'].isfinite(v)for v in x):raise OverflowError('nonfinite centered proposal')
    free=increments if linear else [c+v for c,v in zip(mapping['center_mp'],increments)]
    budget.charge(len(z));return x,diag,free

def selective_setup_work_reserve(mapping,affected):
    E=sum(map(len,mapping['converted'].values()));w=mapping['width'];n=len(mapping['free']);sc=len(mapping['scalar_indices']);pairs=len(mapping['gram_pairs'])
    per_response=2*E+w+3*(sc+450)+2*pairs+4096
    calibration_tail=20*E+240*w+40*n+2*(8388608//64+1)+65536
    return dict(affected_columns=len(affected),sparse_entries=E,per_response_work=per_response,calibration_and_serialization_work=calibration_tail,total_work=len(affected)*per_response+calibration_tail)

def selective_scales(mapping,chart,records,budget):
    free=mapping['free'];support=EXACT.sparse(chart['appended_row']['terms'],1224,budget)
    affected=[j for j in free if j in support];unchanged=[j for j in free if j not in support]
    if len(affected)!=81 or len(unchanged)!=363:raise ValueError('fixed exact appended support81 and unchanged363')
    reserve=selective_setup_work_reserve(mapping,affected)
    if reserve['total_work']>budget.max_operations-budget.operations:raise OverflowError('whole selective setup plus calibration reservation')
    ctx=mapping['ctx'];updates=[];by_index={j:i for i,j in enumerate(free)}
    for j in affected:
        direction=[ctx.zero]*len(free);direction[by_index[j]]=ctx.one
        response,_=OLD.forward(mapping,direction,budget,linear=True)
        C,H=OLD.matrices(mapping,response,budget)
        g=ctx.fsum(response[k]**2 for k in mapping['scalar_indices'])+ctx.fsum(v*v for row in C for v in row)+ctx.fsum(v*v for row in H for v in row)
        budget.charge(3*(len(mapping['scalar_indices'])+450)+4096)
        if not ctx.isfinite(g)or g<0:raise OverflowError('finite nonnegative approximate column norm')
        exported=OLD.mp_record(g);exact_export=budget.q(OLD.record_fraction(exported));k,D=J.dyadic_scale(exact_export,exponent_abs_cap=900)
        mapping['scales'][by_index[j]]=D
        updates.append(dict(free_index=j,approximate_norm_squared_mp=exported,exponent=k,scale=str(D),numerical_zero=g==0))
    mapping['scale_mp']=[OLD.to_mp(q,ctx,budget)for q in mapping['scales']]
    return dict(affected_free_indices=affected,unchanged_free_indices=unchanged,updates=updates,old_scale_records=records,reservation=reserve,scaling=SCALING,column_norms_independently_verified=False)

def setup(chart,affine,norms,*,deadline,max_operations=25000000,max_cells=6000000,max_bits=4096,max_map_bytes=8388608):
    budget=Budget(deadline,max_operations,max_cells,max_bits)
    if type(max_operations)is not int or not 0<max_operations<=25000000 or type(max_map_bytes)is not int or not 4096<=max_map_bytes<=8388608:raise ValueError('bounded fixed map setup')
    normalized,pivots,free,retained,recipes,center=decode_chart(chart,affine,budget);scales,records=reused_scales(norms,free,budget)
    ctx=OLD.context();converted={p:{j:OLD.to_mp(q,ctx,budget)for j,q in row.items()}for p,row in normalized.items()}
    position={j:i for i,j in enumerate(retained)};initial=[center[j]for j in free]
    mapping=dict(ctx=ctx,width=1224,normalized=normalized,converted=converted,pivots=pivots,free=free,retained=retained,recipes=recipes,initial=initial,parent_projected=center,scales=scales,scale_mp=[OLD.to_mp(q,ctx,budget)for q in scales],center_mp=[OLD.to_mp(q,ctx,budget)for q in initial],center_projected_mp=[OLD.to_mp(q,ctx,budget)for q in center],scalar_indices=[position[j]for j in [*range(366),*range(1592,1597)]],C_indices=[position[j]for j in range(1597,1717)],P_indices=[position[j]for j in range(1717,1837)],gram_pairs=[(i,j)for i in range(15)for j in range(i,15)],resident_cells=2*sum(map(len,normalized.values()))+4*1224+4*444)
    budget.cells(mapping['resident_cells'])
    selective=selective_scales(mapping,chart,records,budget)
    z=[ctx.zero]*len(free);forward,diag,_=centered_forward(mapping,z,budget,diagnostics=True)
    def error(actual,reference):
        budget.charge(10*len(reference));return max((abs(OLD.record_fraction(OLD.mp_record(v))-q)/max(F(1),abs(q))for v,q in zip(actual,reference)),default=F(0))
    center_error=error(forward,center)
    d=[F((-1)**i)for i in range(len(free))];seed=[F(0)]*1224
    for j,D,v in zip(free,scales,d):seed[j]=budget.mul(D,v)
    homogeneous={p:{j:q for j,q in row.items()if j!=1224}for p,row in normalized.items()};budget.cells(mapping['resident_cells']+sum(map(len,homogeneous.values()))+6*1224+4*444);exact=EXACT.back_substitute(homogeneous,seed,1224,budget)
    dmp=[OLD.to_mp(v,ctx,budget)for v in d];Nd,linear_diag,_=centered_forward(mapping,dmp,budget,linear=True,diagnostics=True);hom_error=error(Nd,exact)
    g=[ctx.mpf((j%7)-3)/7 for j in range(1224)];Ng=J.scaled_adjoint(mapping,g,budget);left=OLD.dot(ctx,Nd,g,budget);right=OLD.dot(ctx,dmp,Ng,budget);relative=abs(left-right)/max(ctx.one,abs(left),abs(right));budget.charge(20)
    calibration=dict(initial_forward_mp=[OLD.mp_record(v)for v in forward],center_exact_reference_relative_error=str(center_error),homogeneous_direction_mp=[OLD.mp_record(v)for v in dmp],homogeneous_forward_mp=[OLD.mp_record(v)for v in Nd],homogeneous_exact_reference=list(map(str,exact)),homogeneous_relative_error=str(hom_error),adjoint_test_gradient_mp=[OLD.mp_record(v)for v in g],adjoint_test_result_mp=[OLD.mp_record(v)for v in Ng],adjoint_left=OLD.mp_record(left),adjoint_right=OLD.mp_record(right),adjoint_relative_error=OLD.mp_record(relative),tolerance='1e-40',passed=center_error<=F(1,10**40)and hom_error<=F(1,10**40)and relative<=ctx.mpf('1e-40'),initial_forward=diag,homogeneous_forward=linear_diag)
    if not calibration['passed']:raise ValueError('fixed80digit centered homogeneous/adjoint calibration failed')
    receipt=dict(schema='primitive-state-feedback-cone-map-v1',complete=True,width=1224,pivot_columns=pivots,free_indices=free,center_projected_vector=list(map(str,center)),initial_free_vector=list(map(str,initial)),scale_vector=list(map(str,mapping['scales'])),selective_scaling=selective,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,calibration=calibration,limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_bits,max_map_bytes=max_map_bytes),**FLAGS)
    budget.charge(2*(len(encoded(receipt))//64+1));receipt['counts']=budget.counts()
    if len(encoded(receipt))>max_map_bytes:raise OverflowError('bounded setup receipt')
    mapping['calibration']=calibration;return mapping,receipt

def iteration_work_reserve(mapping):return B.iteration_work_reserve(mapping)+6*mapping['width']

def next_start_step(ctx,accepted,budget):
    if not ctx.isfinite(accepted)or accepted<=0:raise ValueError('positive finite accepted step')
    budget.charge(2);return min(ctx.power(2,900),2*accepted)

def exact_endpoint(mapping,proposal,cache,necessary,*,deadline,max_operations=25000000,max_bits=4096,max_endpoint_bytes=2097152):
    budget=Budget(deadline,max_operations,6000000,max_bits)
    if max_operations>25000000 or type(max_endpoint_bytes)is not int or not 4096<=max_endpoint_bytes<=2097152:raise ValueError('bounded exact endpoint')
    out=dict(schema='primitive-state-feedback-cone-endpoint-v1',complete=False,final_free_vector=None,final_projected_vector=None,candidate_original_vector=None,free_indices=mapping['free'],diagnostics=None,**FLAGS)
    try:
        if proposal.get('complete')is not True or proposal.get('schema')!=SCHEMA:raise ValueError('complete single centered proposal')
        z=[budget.q(OLD.record_fraction(v))for v in proposal['final_z_mp']]
        if len(z)!=len(mapping['free']):raise ValueError('full exact final increment')
        free=[budget.add(c,budget.mul(D,v))for c,D,v in zip(mapping['initial'],mapping['scales'],z)]
        if list(map(str,free))!=proposal['final_free_vector']:raise ValueError('exact center plus scale times final dyadic')
        seed=list(mapping['parent_projected'])
        for j,v in zip(mapping['free'],free):seed[j]=v
        y=EXACT.back_substitute(mapping['normalized'],seed,1224,budget);x=EXACT.canonical_lift(y,mapping['retained'],budget)
        columns,rhs,retained,recipes=EXACT.decode_source(cache,budget)
        if retained!=mapping['retained']:raise ValueError('unchanged original source layout')
        full,newrhs,_=EXACT.project_feedback(necessary,retained,recipes,budget);budget.resident_cells=sum(map(len,columns))+2*sum(map(len,mapping['normalized'].values()))+len(rhs);budget.cells(4*1957+4*1224+15*15*6)
        diagnostics=EXACT.diagnostics(columns,rhs,x,full,newrhs,budget)
        if not diagnostics['affine_equalities_satisfied']:raise ValueError('all5641 original and feedback equations exactly zero')
        out.update(complete=True,final_free_vector=list(map(str,free)),final_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,x)),diagnostics=diagnostics)
    except Exception as error:out.update(complete=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__,final_projected_vector=None,candidate_original_vector=None,diagnostics=None)
    budget.charge(len(encoded(out)));out.update(counts=budget.counts(),limits=dict(max_operations=max_operations,max_coefficient_bits=max_bits,max_endpoint_bytes=max_endpoint_bytes))
    if len(encoded(out))>max_endpoint_bytes:raise OverflowError('bounded exact endpoint receipt')
    return out


block_metrics=B.block_metrics
weighted_power_operator=B.weighted_power_operator
simplex_model=B.simplex_model
ModelConsistencyError=B.ModelConsistencyError

def propose(mapping,*,deadline,max_operations=200000000,checkpoint=None,max_trace_bytes=16777216):
    if type(max_operations)is not int or not 0<max_operations<=200000000 or type(max_trace_bytes)is not int or not 4096<=max_trace_bytes<=16777216:raise ValueError('bounded fixed proposal')
    budget=Budget(deadline,max_operations,6000000,4096);ctx=mapping['ctx'];start=time.monotonic();best=None;trace_bytes=0
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,free_indices=mapping['free'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    def save(phase):
        budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+60*mapping['width']+12*len(mapping['free'])*(4+2*len(out['power_trace'])+6*len(out['iterations'])))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        z=[ctx.zero]*len(mapping['free']);x=list(mapping['center_projected_mp']);calibration=mapping['calibration'];budget.charge(len(z)+len(x));out['calibration']=calibration;out['initial_z_mp']=[OLD.mp_record(v) for v in z]
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
            for k in range(128):
                required_work=iteration_work_reserve(mapping);tail=max_trace_bytes+20000*len(z)+131072
                op_short=max_operations-budget.operations<required_work+tail;byte_short=max_trace_bytes-trace_bytes<iteration_trace_reserve+final_trace_reserve
                if op_short or byte_short:
                    stop='budget_stop';out['budget_stop']=dict(before_iteration=k,operations=budget.operations,max_operations=max_operations,remaining_operations=max_operations-budget.operations,worst_iteration_work_reserve=required_work,finalization_work_reserve=tail,trace_retained_bytes=trace_bytes,max_trace_bytes=max_trace_bytes,worst_iteration_trace_bytes=iteration_trace_reserve,finalization_trace_bytes=final_trace_reserve,resource='operations' if op_short else 'trace_bytes');break
                save('feedback_cone_iteration');entry=dict(index=k,objective_before=OLD.mp_record(value),normalized_blocks=[OLD.mp_record(q) for q in r],block_gradients=[[OLD.mp_record(q) for q in g] for g in gradients],trials=[],accepted=False,reserved_iteration_work=required_work);out['iterations'].append(entry);accepted=False;stationary=False
                for trial in range(3):
                    trialalpha=alpha/ctx.power(2,trial)
                    if trialalpha<lower:entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),finite=False,reason='step below declared minimum'));continue
                    try:direction,norm2,model=simplex_model(ctx,r,gradients,trialalpha,budget)
                    except ModelConsistencyError as error:
                        entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),model=error.record,finite=False,reason=str(error)))
                        raise
                    if norm2==0:
                        entry['trials'].append(dict(index=trial,step=OLD.mp_record(trialalpha),model=model,finite=True,stationary=True));stop='numerical_model_stationarity';stationary=True;break
                    trialz=[v+d for v,d in zip(z,direction)];budget.charge(len(z));trialx,diag,approximate=centered_forward(mapping,trialz,budget,diagnostics=True);pnew,gnew,info=block_metrics(mapping,trialx,budget,normalizers,apply_adjoint=False);rnew=[p/bb for p,bb in zip(pnew,normalizers)];newvalue=max(rnew);threshold=value-norm2/(8*trialalpha);budget.charge(12)
                    record=dict(index=trial,step=OLD.mp_record(trialalpha),model=model,z=[OLD.mp_record(q) for q in trialz],approximate_free_mp=[OLD.mp_record(q) for q in approximate],block_penalties=[OLD.mp_record(q) for q in pnew],normalized_blocks=[OLD.mp_record(q) for q in rnew],objective=OLD.mp_record(newvalue),armijo_threshold=OLD.mp_record(threshold),armijo_passed=newvalue<=threshold,forward=diag,merit_details=info,finite=True);entry['trials'].append(record)
                    if newvalue<=threshold:
                        z=trialz;x=trialx;r=rnew;value=newvalue;alpha=next_start_step(ctx,trialalpha,budget);best=list(z);entry['accepted']=True;entry['next_start_step']=OLD.mp_record(alpha);accepted=True;gradients=[J.scaled_adjoint(mapping,g,budget) for g in gnew];break
                raw=encoded(entry);budget.charge(len(raw));trace_bytes+=len(raw)+1
                if len(raw)>iteration_trace_reserve or budget.operations>max_operations-tail:raise OverflowError('declared balanced iteration reservation exceeded')
                if stationary:break
                if not accepted:stop='line_search_failed';break
        final_z=[OLD.record_fraction(OLD.mp_record(v)) for v in best];budget.charge(10*len(best));free=[budget.add(c,budget.mul(D,q)) for c,D,q in zip(mapping['initial'],mapping['scales'],final_z)]
        out.update(status='proposed',complete=True,stop_reason=stop,final_objective=OLD.mp_record(value),final_normalized_blocks=[OLD.mp_record(q) for q in r],final_z_mp=[OLD.mp_record(q) for q in best],final_free_vector=list(map(str,free)));save('proposal_complete')
    except Exception as e:
        out.update(status='unknown',complete=False,reason=str(e) or type(e).__name__,error_type=type(e).__name__)
        if best is not None:out['last_finite_z_mp']=[OLD.mp_record(v) for v in best]
    budget.charge(len(encoded(out)));out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    if len(encoded(out))>max_trace_bytes:raise OverflowError('bounded balanced proposal trace')
    return out
