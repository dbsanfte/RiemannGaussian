"""Hash-free exact chart composition and centered mixed-precision cone proposals."""
from fractions import Fraction as F
import math
import time
import primitive_state_backtracking_cone_search as PREVIOUS
EXACT=PREVIOUS.EXACT; OLD=PREVIOUS.OLD; J=PREVIOUS.J; B=PREVIOUS.B
encoded=EXACT.encoded; FLAGS=dict(PREVIOUS.FLAGS)
SCHEMA='primitive-state-augmented-cone-search-v1'
CHART_SCHEMA='primitive-state-augmented-cone-chart-v1'
CENTER_SCHEMA='primitive-state-augmented-cone-center-v1'
PRECISION=dict(PREVIOUS.PREVIOUS.PRECISION)
MODEL=dict(PREVIOUS.MODEL,normalizer_rule='reuse original publication025 normalizers from publication026 map unchanged')
SEARCH=dict(PREVIOUS.SEARCH,power_steps=8,power_seed='alternating normalized signs',power_zero_policy='stop after first zero operator',initial_step='clamped reciprocal of eight-step weighted power estimate on new map')
SCALING=dict(rule='retain publication026 D on unaffected surviving coordinates; recompute approximate80digit cone norms on union of appended row surviving supports',exponent_abs_cap=900,new_column_responses=98,unchanged_column_scales=344,norms_verified=False,new_map_norm_preconditioner=False,cone_norm='all366 square and5 slack squares plus C and H Frobenius squared norms',dyadic_rule='smallest integer k with exported approximate norm_squared <= 2^(2*k); D=2^(-k); zero=>1',partial_scaling_allowed=False)
SEED='exact canonical repair of publication026 recovered point preserving442 remaining free coordinates; z0=0'
class Budget(PREVIOUS.Budget):
    def __init__(self,deadline,max_operations=195000000,max_cells=6000000,max_bits=4096):
        if type(max_operations)is not int or not 0<max_operations<=195000000:raise ValueError('bounded augmented work')
        super().__init__(deadline,max_operations,max_cells,max_bits)
centered_forward=PREVIOUS.centered_forward
block_metrics=B.block_metrics
simplex_model=B.simplex_model
ModelConsistencyError=B.ModelConsistencyError
next_start_step=PREVIOUS.next_start_step
iteration_work_reserve=PREVIOUS.iteration_work_reserve

def compose_chart(normalized_rows,appended_rows,width,budget):
    """Append normalized independent triangular rows without rewriting the old basis."""
    if type(width)is not int or not 1<=width<=1224 or type(appended_rows)is not list or len(appended_rows)>64:raise ValueError('bounded chart composition')
    result={}; old=[]
    for records,new in ((normalized_rows,False),(appended_rows,True)):
        for record in records:
            p=record.get('pivot');row=EXACT.sparse(record['terms'],width,budget)
            if type(p)is not int or not 0<=p<width or p in result or row.get(p)!=1 or any(j<p for j in row):raise ValueError('unique normalized minimum pivot')
            if new and any(j in result for j in row if j!=width):raise ValueError('appended row must eliminate every preceding pivot')
            result[p]=row
            if not new:old.append(p)
    pivots=sorted(result);free=[j for j in range(width)if j not in result]
    affected=sorted({j for record in appended_rows for j,q in EXACT.sparse(record['terms'],width,budget).items()if j in free and q})
    budget.cells(sum(map(len,result.values()))+len(free)+len(pivots))
    return result,pivots,free,affected

def compose_and_repair(chart,affine,extension,recovered,budget):
    old,oldp,oldfree,retained,recipes,_=PREVIOUS.PREVIOUS.decode_chart(chart,affine,budget)
    if extension.get('complete')is not True or extension.get('contradiction_row')is not None or extension.get('old_rank')!=len(old):raise ValueError('complete independent row extension')
    appended=extension['appended_rows']
    records=[dict(pivot=p,terms=[[j,str(q)]for j,q in sorted(row.items())])for p,row in sorted(old.items())]
    normalized,pivots,free,affected=compose_chart(records,appended,1224,budget)
    if extension.get('coefficient_rank')!=len(pivots)or extension.get('augmented_rank')!=len(pivots)or extension.get('free_count')!=len(free):raise ValueError('exact declared composed rank partition')
    if recovered.get('complete')is not True:raise ValueError('complete recovered exact point')
    original=[budget.q(q)for q in recovered['candidate_original_vector']]
    seed=EXACT.aggregate_seed(original,retained,recipes,budget)
    if recovered.get('final_projected_vector')!=list(map(str,seed)):raise ValueError('actual recovered quotient coordinates')
    center=EXACT.back_substitute(normalized,seed,1224,budget)
    if any(center[j]!=seed[j]for j in free):raise ValueError('preserved remaining free seed')
    x=EXACT.canonical_lift(center,retained,budget)
    chartout=dict(schema=CHART_SCHEMA,complete=True,width=1224,original_width=1957,normalized_rows=[dict(pivot=p,terms=[[j,str(q)]for j,q in sorted(normalized[p].items())])for p in pivots],pivot_columns=pivots,free_indices=free,retained_indices=retained,old_pivots=oldp,appended_rows=appended,affected_free_indices=affected,**FLAGS)
    centerout=dict(schema=CENTER_SCHEMA,complete=True,free_indices=free,initial_free_vector=[str(center[j])for j in free],center_projected_vector=list(map(str,center)),candidate_original_vector=list(map(str,x)),preserved_seed_free_coordinates=True,**FLAGS)
    return normalized,pivots,free,retained,recipes,center,chartout,centerout

def selective_setup_work_reserve(mapping,affected):
    E=sum(map(len,mapping['converted'].values()));w=mapping['width'];n=len(mapping['free']);sc=len(mapping['scalar_indices']);pairs=len(mapping['gram_pairs'])
    per_response=2*E+w+3*(sc+450)+2*pairs+4096
    calibration_tail=20*E+240*w+40*n+2*(8388608//64+1)+65536
    return dict(affected_columns=len(affected),sparse_entries=E,per_response_work=per_response,calibration_and_serialization_work=calibration_tail,total_work=len(affected)*per_response+calibration_tail)

def selective_scales(mapping,chart,records,budget):
    free=mapping['free'];support={j:F(1)for j in chart['affected_free_indices']}
    affected=[j for j in free if j in support];unchanged=[j for j in free if j not in support]
    if set(affected)|set(unchanged)!=set(free):raise ValueError('complete selective partition')
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

def setup(chart,affine,extension,recovered,prior_map,*,deadline,max_operations=30000000,max_cells=6000000,max_bits=4096,max_map_bytes=8388608):
    budget=Budget(deadline,max_operations,max_cells,max_bits)
    if type(max_operations)is not int or not 0<max_operations<=30000000 or type(max_map_bytes)is not int or not 4096<=max_map_bytes<=8388608:raise ValueError('bounded fixed map setup')
    normalized,pivots,free,retained,recipes,center,chartout,centerout=compose_and_repair(chart,affine,extension,recovered,budget)
    if prior_map.get('complete')is not True or prior_map.get('schema')!='primitive-state-backtracking-cone-map-v1' or len(prior_map.get('free_indices',[]))!=444 or len(prior_map.get('scale_vector',[]))!=444 or prior_map['free_indices']!=sorted(set(prior_map['free_indices'])):raise ValueError('complete unique inherited444 scales')
    inherited={j:PREVIOUS.positive_dyadic(q,budget)for j,q in zip(prior_map['free_indices'],prior_map['scale_vector'])}
    if len(inherited)!=len(prior_map['free_indices'])or any(j not in inherited for j in free):raise ValueError('complete coordinate-keyed inherited D')
    scales=[inherited[j]for j in free];records=[dict(free_index=j,scale=str(inherited[j]))for j in free]
    normalizers=[budget.q(q)for q in prior_map['normalizers']]
    if len(normalizers)!=3 or any(q<F(MODEL['normalizer_floor'])for q in normalizers):raise ValueError('frozen original positive normalizers')
    ctx=OLD.context();converted={p:{j:OLD.to_mp(q,ctx,budget)for j,q in row.items()}for p,row in normalized.items()}
    position={j:i for i,j in enumerate(retained)};initial=[center[j]for j in free]
    mapping=dict(ctx=ctx,width=1224,normalized=normalized,converted=converted,pivots=pivots,free=free,retained=retained,recipes=recipes,initial=initial,parent_projected=center,scales=scales,scale_mp=[OLD.to_mp(q,ctx,budget)for q in scales],center_mp=[OLD.to_mp(q,ctx,budget)for q in initial],center_projected_mp=[OLD.to_mp(q,ctx,budget)for q in center],scalar_indices=[position[j]for j in [*range(366),*range(1592,1597)]],C_indices=[position[j]for j in range(1597,1717)],P_indices=[position[j]for j in range(1717,1837)],gram_pairs=[(i,j)for i in range(15)for j in range(i,15)],resident_cells=4*sum(map(len,normalized.values()))+12*1224+8*len(free)+2*1957)
    budget.cells(mapping['resident_cells'])
    selective=selective_scales(mapping,chartout,records,budget)
    z=[ctx.zero]*len(free);forward,diag,_=centered_forward(mapping,z,budget,diagnostics=True)
    def error(actual,reference):
        budget.charge(10*len(reference));return max((abs(OLD.record_fraction(OLD.mp_record(v))-q)/max(F(1),abs(q))for v,q in zip(actual,reference)),default=F(0))
    center_error=error(forward,center)
    d=[F((-1)**i)for i in range(len(free))];seed=[F(0)]*1224
    for j,D,v in zip(free,scales,d):seed[j]=budget.mul(D,v)
    homogeneous={p:{j:q for j,q in row.items()if j!=1224}for p,row in normalized.items()};budget.cells(mapping['resident_cells']+sum(map(len,homogeneous.values()))+6*1224+4*len(free));exact=EXACT.back_substitute(homogeneous,seed,1224,budget)
    dmp=[OLD.to_mp(v,ctx,budget)for v in d];Nd,linear_diag,_=centered_forward(mapping,dmp,budget,linear=True,diagnostics=True);hom_error=error(Nd,exact)
    g=[ctx.mpf((j%7)-3)/7 for j in range(1224)];Ng=J.scaled_adjoint(mapping,g,budget);left=OLD.dot(ctx,Nd,g,budget);right=OLD.dot(ctx,dmp,Ng,budget);relative=abs(left-right)/max(ctx.one,abs(left),abs(right));budget.charge(20)
    calibration=dict(initial_forward_mp=[OLD.mp_record(v)for v in forward],center_exact_reference_relative_error=str(center_error),homogeneous_direction_mp=[OLD.mp_record(v)for v in dmp],homogeneous_forward_mp=[OLD.mp_record(v)for v in Nd],homogeneous_exact_reference=list(map(str,exact)),homogeneous_relative_error=str(hom_error),adjoint_test_gradient_mp=[OLD.mp_record(v)for v in g],adjoint_test_result_mp=[OLD.mp_record(v)for v in Ng],adjoint_left=OLD.mp_record(left),adjoint_right=OLD.mp_record(right),adjoint_relative_error=OLD.mp_record(relative),tolerance='1e-40',passed=center_error<=F(1,10**40)and hom_error<=F(1,10**40)and relative<=ctx.mpf('1e-40'),initial_forward=diag,homogeneous_forward=linear_diag)
    if not calibration['passed']:raise ValueError('fixed80digit centered homogeneous/adjoint calibration failed')
    receipt=dict(schema='primitive-state-augmented-cone-map-v1',complete=True,width=1224,pivot_columns=pivots,free_indices=free,center_projected_vector=list(map(str,center)),initial_free_vector=list(map(str,initial)),normalizers=list(map(str,normalizers)),scale_vector=list(map(str,mapping['scales'])),selective_scaling=selective,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,calibration=calibration,limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_bits,max_map_bytes=max_map_bytes),**FLAGS)
    budget.charge(2*((len(encoded(receipt))+len(encoded(chartout))+len(encoded(centerout)))//64+1));receipt['counts']=budget.counts()
    if len(encoded(chartout))>8388608 or len(encoded(centerout))>2097152:raise OverflowError('bounded chart/center artifacts')
    if len(encoded(receipt))>max_map_bytes:raise OverflowError('bounded setup receipt')
    mapping.update(calibration=calibration,fixed_normalizers=normalizers,warm_z=z,warm_forward_mp=forward,warm_free=initial);return mapping,receipt,chartout,centerout

def propose(mapping,*,deadline,max_operations=195000000,checkpoint=None,max_trace_bytes=33554432):
    if type(max_operations)is not int or not 0<max_operations<=195000000 or type(max_trace_bytes)is not int or not 4096<=max_trace_bytes<=33554432:raise ValueError('bounded fixed proposal')
    budget=Budget(deadline,max_operations,6000000,4096);ctx=mapping['ctx'];start=time.monotonic();best=None;trace_bytes=0
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,free_indices=mapping['free'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),warm_free_vector=list(map(str,mapping['warm_free'])),power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    def save(phase):
        retained_trial_cells=sum(1+2*len(entry['trials'])for entry in out['iterations'])
        budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+60*mapping['width']+12*len(mapping['free'])*(4+retained_trial_cells))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        z=list(mapping['warm_z']);x=list(mapping['warm_forward_mp']);calibration=mapping['calibration'];budget.charge(len(z)+len(x));out['calibration']=calibration;out['initial_z_mp']=[OLD.mp_record(v) for v in z];
        penalties,coordinate,details=block_metrics(mapping,x,budget,apply_adjoint=False);b=list(mapping['fixed_normalizers']);normalizers=[OLD.to_mp(q,ctx,budget) for q in b];r=[p/v for p,v in zip(penalties,normalizers)];value=max(r);best=list(z)
        out.update(initial_block_penalties=[OLD.mp_record(p) for p in penalties],normalizers=list(map(str,b)),initial_normalized_blocks=[OLD.mp_record(q) for q in r],initial_objective=OLD.mp_record(value),initial_merit_details=details)
        stop='zero_initial_numerical_defect' if value==0 else 'iteration_limit'
        if value:
            gradients=[J.scaled_adjoint(mapping,[v/bb for v in g],budget) for g,bb in zip(coordinate,normalizers)];budget.charge(3*mapping['width'])
            lower=ctx.power(2,-900);upper=ctx.power(2,900);direction=[ctx.mpf((-1)**j)/ctx.sqrt(len(z))for j in range(len(z))];estimate=ctx.zero
            for power_index in range(8):
                v=B.weighted_power_operator(mapping,direction,normalizers,budget);den=OLD.dot(ctx,direction,direction,budget);estimate=OLD.dot(ctx,direction,v,budget)/den;norm=ctx.sqrt(OLD.dot(ctx,v,v,budget))
                out['power_trace'].append(dict(index=power_index,vector=[OLD.mp_record(q)for q in direction],operator=[OLD.mp_record(q)for q in v],estimate=OLD.mp_record(estimate),operator_norm=OLD.mp_record(norm)))
                if norm==0:break
                direction=[q/norm for q in v];budget.charge(len(direction))
            alpha=max(lower,min(upper,ctx.one/estimate if estimate>0 else upper));out['initial_step']=OLD.mp_record(alpha);trace_bytes=len(encoded(out));budget.charge(trace_bytes)
            final_trace_reserve=8192+3000*len(z);iteration_trace_reserve=65536+48*96*len(z)
            for k in range(128):
                required_work=iteration_work_reserve(mapping);tail=max_trace_bytes+20000*len(z)+131072
                op_short=max_operations-budget.operations<required_work+tail;byte_short=max_trace_bytes-trace_bytes<iteration_trace_reserve+final_trace_reserve
                if op_short or byte_short:
                    stop='budget_stop';out['budget_stop']=dict(before_iteration=k,operations=budget.operations,max_operations=max_operations,remaining_operations=max_operations-budget.operations,worst_iteration_work_reserve=required_work,finalization_work_reserve=tail,trace_retained_bytes=trace_bytes,max_trace_bytes=max_trace_bytes,worst_iteration_trace_bytes=iteration_trace_reserve,finalization_trace_bytes=final_trace_reserve,resource='operations' if op_short else 'trace_bytes');break
                save('backtracking_iteration');entry=dict(index=k,objective_before=OLD.mp_record(value),normalized_blocks=[OLD.mp_record(q) for q in r],block_gradients=[[OLD.mp_record(q) for q in g] for g in gradients],trials=[],accepted=False,reserved_iteration_work=required_work);out['iterations'].append(entry);accepted=False;stationary=False
                for trial in range(12):
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


def scalar_first_diagnostics(columns,rhs,x,necessary_rows,budget):
    values=[F(0)]*len(rhs)
    for j,col in enumerate(columns):
        for i,q in col.items():values[i]=budget.add(values[i],budget.mul(q,x[j]))
    mismatches=[dict(row=i,residual=str(budget.add(v,-rhs[i])))for i,v in enumerate(values)if v!=rhs[i]]
    residuals=[]
    for necessary in necessary_rows:
        row=EXACT.sparse([[v['index'],v['coefficient']]for v in necessary['entries']],1956,budget);target=budget.q(necessary['rhs']);value=F(0)
        for j,q in row.items():value=budget.add(value,budget.mul(q,x[j]))
        residuals.append(str(budget.add(value,-target)))
    negatives=[dict(coordinate=j,value=str(q))for j,q in enumerate(x[:1597])if q<0]
    blocks=[]
    if not negatives:
        for k,name in enumerate(('full_child','full_parent','storage_K')):
            matrix=[[F(0)]*15 for _ in range(15)];index=1597+120*k
            for i in range(15):
                for j in range(i,15):matrix[i][j]=matrix[j][i]=x[index];index+=1
            blocks.append(dict(name=name,**EXACT.exact_psd(matrix,budget)))
    failures=None if negatives else sum(not v['psd']for v in blocks)
    return dict(full_original_rows_checked=len(rhs),learned_rows_checked=len(necessary_rows),full_equations_checked=len(rhs)+len(necessary_rows),original_equation_mismatches=mismatches,learned_equation_residuals=residuals,affine_equalities_satisfied=not mismatches and all(v=='0'for v in residuals),negative_scalars=negatives,negative_scalar_count=len(negatives),psd_status='NOT_CHECKED_AFTER_SCALAR_REJECTION'if negatives else 'ALL_THREE_EXACT_BLOCKS_CHECKED',PSD_blocks_checked=len(blocks),PSD_failures=failures,psd_blocks=blocks,all_cones_satisfied=not negatives and failures==0)

def exact_endpoint(mapping,proposal,cache,necessary_rows,*,deadline,max_operations=25000000,max_bits=4096,max_endpoint_bytes=2097152):
    budget=Budget(deadline,max_operations,6000000,max_bits)
    if max_operations>25000000 or type(max_endpoint_bytes)is not int or not 4096<=max_endpoint_bytes<=2097152:raise ValueError('bounded exact endpoint')
    out=dict(schema='primitive-state-augmented-cone-endpoint-v1',complete=False,final_free_vector=None,final_projected_vector=None,candidate_original_vector=None,free_indices=mapping['free'],diagnostics=None,**FLAGS)
    try:
        if proposal.get('complete')is not True or proposal.get('schema')!=SCHEMA:raise ValueError('complete single centered proposal')
        z=[budget.q(OLD.record_fraction(v))for v in proposal['final_z_mp']]
        if len(z)!=len(mapping['free']):raise ValueError('complete exact final increment')
        free=[budget.add(c,budget.mul(D,v))for c,D,v in zip(mapping['initial'],mapping['scales'],z)]
        if list(map(str,free))!=proposal['final_free_vector']:raise ValueError('exact repaired center plus D times final z')
        seed=list(mapping['parent_projected'])
        for j,v in zip(mapping['free'],free):seed[j]=v
        y=EXACT.back_substitute(mapping['normalized'],seed,1224,budget);x=EXACT.canonical_lift(y,mapping['retained'],budget)
        columns,rhs,retained,recipes=EXACT.decode_source(cache,budget)
        if retained!=mapping['retained']:raise ValueError('unchanged source coordinate layout')
        for necessary in necessary_rows:EXACT.project_feedback(necessary,retained,recipes,budget)
        budget.resident_cells=sum(map(len,columns))+2*sum(map(len,mapping['normalized'].values()))+len(rhs);budget.cells(4*1957+4*1224+6*225)
        diag=scalar_first_diagnostics(columns,rhs,x,necessary_rows,budget)
        if not diag['affine_equalities_satisfied']:raise ValueError('all original and learned equations must hold exactly')
        out.update(complete=True,final_free_vector=list(map(str,free)),final_projected_vector=list(map(str,y)),candidate_original_vector=list(map(str,x)),diagnostics=diag)
    except Exception as error:out.update(reason=str(error)or type(error).__name__,error_type=type(error).__name__)
    budget.charge(len(encoded(out)));out.update(counts=budget.counts(),limits=dict(max_operations=max_operations,max_coefficient_bits=max_bits,max_endpoint_bytes=max_endpoint_bytes))
    if len(encoded(out))>max_endpoint_bytes:raise OverflowError('bounded exact endpoint bytes')
    return out
