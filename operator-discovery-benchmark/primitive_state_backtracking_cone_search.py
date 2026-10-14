"""Hash-free twelve-trial warm cone proposals with fixed prior normalization."""
from fractions import Fraction as F
import math
import time
import primitive_state_feedback_cone_search as PREVIOUS

EXACT=PREVIOUS.EXACT;OLD=PREVIOUS.OLD;J=PREVIOUS.J;B=PREVIOUS.B
encoded=EXACT.encoded;FLAGS=dict(PREVIOUS.FLAGS)
SCHEMA='primitive-state-backtracking-cone-search-v1'
PRECISION=dict(PREVIOUS.PRECISION,calibration_scope='warm forward versus exact publication025 endpoint only; prior map checks reused')
MODEL=dict(PREVIOUS.MODEL,normalizer_rule='reuse publication025 initial-floor normalizers unchanged; never renormalize warm penalties')
SEARCH=dict(PREVIOUS.SEARCH,power_steps=0,armijo_trials=12,
            initial_step='half the last failed trial of publication025; reject outside fixed positive range; no new power pass',
            iteration_budget_policy='reserve twelve model/Armijo trials and three accepted block adjoints before iteration')
SCALING=dict(rule='reuse saved publication025 positive D unchanged by projected free_index',
             new_column_responses=0,new_norm_calculations=0,exponent_abs_cap=900,
             norms_verified=False,new_map_norm_preconditioner=False)
SEED='exact publication024 center plus saved publication025 final269bit z; no recentering, clipping or rerounding'

class Budget(PREVIOUS.Budget):
    def __init__(self,deadline,max_operations=220000000,max_cells=6000000,max_bits=4096):
        if type(deadline)not in(int,float)or not math.isfinite(deadline):raise ValueError('finite backtracking deadline')
        if any(type(v)is not int or v<1 for v in(max_operations,max_cells,max_bits))or max_operations>220000000 or max_cells>6000000 or max_bits>4096:raise ValueError('bounded backtracking limits')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.max_bits=max_bits
        self.operations=0;self.peak_cells=0;self.maximum_bits=0;self.resident_cells=0

centered_forward=PREVIOUS.centered_forward
block_metrics=B.block_metrics
simplex_model=B.simplex_model
ModelConsistencyError=B.ModelConsistencyError
next_start_step=PREVIOUS.next_start_step

def failed_trial_step(proposal,budget):
    if proposal.get('schema')!=PREVIOUS.SCHEMA or proposal.get('complete')is not True or proposal.get('status')!='proposed'or proposal.get('stop_reason')!='line_search_failed':raise ValueError('one complete failed-three-trial publication025 endpoint')
    iterations=proposal.get('iterations')
    if type(iterations)is not list or not iterations:raise ValueError('retained terminal failed iteration')
    last=iterations[-1];trials=last.get('trials')
    if last.get('accepted')is not False or type(trials)is not list or len(trials)!=3 or [t.get('index')for t in trials]!=[0,1,2]or any(t.get('finite')is not True or t.get('armijo_passed')is not False for t in trials):raise ValueError('three finite rejected last trials')
    steps=[budget.q(OLD.record_fraction(t['step']))for t in trials]
    if any(q<=0 for q in steps)or steps[1]!=budget.div(steps[0],F(2))or steps[2]!=budget.div(steps[1],F(2)):raise ValueError('saved exact three-halving steps')
    alpha=budget.div(steps[-1],F(2))
    if not F(1,1<<900)<=alpha<=F(1<<900):raise ValueError('initial half failed step in fixed range')
    return steps[-1],alpha

def positive_dyadic(text,budget):
    q=budget.q(text)
    if q<=0 or q.numerator&(q.numerator-1)or q.denominator&(q.denominator-1):raise ValueError('positive dyadic scale')
    exponent=q.numerator.bit_length()-q.denominator.bit_length()
    if abs(exponent)>900:raise ValueError('bounded reused scale exponent')
    return q

def setup(chart,center,prior_map,prior_proposal,prior_endpoint,*,deadline,max_operations=5000000,max_cells=6000000,max_bits=4096,max_map_bytes=8388608):
    budget=Budget(deadline,max_operations,max_cells,max_bits)
    if type(max_operations)is not int or not 0<max_operations<=5000000 or type(max_map_bytes)is not int or not 4096<=max_map_bytes<=8388608:raise ValueError('bounded warm setup')
    normalized,pivots,free,retained,recipes,base=PREVIOUS.decode_chart(chart,center,budget)
    if prior_map.get('schema')!='primitive-state-feedback-cone-map-v1'or prior_map.get('complete')is not True or prior_map.get('free_indices')!=free or prior_map.get('pivot_columns')!=pivots or prior_map.get('center_projected_vector')!=list(map(str,base))or prior_map.get('initial_free_vector')!=[str(base[j])for j in free]or prior_map.get('scaling')!=PREVIOUS.SCALING:raise ValueError('actual same-chart publication025 diagonal and exact center')
    scales=[positive_dyadic(q,budget)for q in prior_map['scale_vector']]
    if len(scales)!=len(free)or prior_proposal.get('scale_vector')!=list(map(str,scales))or prior_proposal.get('free_indices')!=free:raise ValueError('same full444 reused scale coordinates')
    last_step,alpha=failed_trial_step(prior_proposal,budget)
    normalizers=[budget.q(q)for q in prior_proposal['normalizers']]
    if len(normalizers)!=3 or any(q<F(PREVIOUS.MODEL['normalizer_floor'])for q in normalizers):raise ValueError('actual frozen positive025 initial normalizers')
    initial=[base[j]for j in free];z=[budget.q(OLD.record_fraction(v))for v in prior_proposal['final_z_mp']]
    if len(z)!=len(free):raise ValueError('complete saved269bit increment')
    warm_free=[budget.add(c,budget.mul(D,v))for c,D,v in zip(initial,scales,z)]
    if prior_endpoint.get('schema')!='primitive-state-feedback-cone-endpoint-v1'or prior_endpoint.get('complete')is not True or prior_endpoint.get('free_indices')!=free or prior_endpoint.get('final_free_vector')!=list(map(str,warm_free))or prior_proposal.get('final_free_vector')!=list(map(str,warm_free)):raise ValueError('exact024 base plus D times saved025 z')
    seed=list(base)
    for j,q in zip(free,warm_free):seed[j]=q
    warm=EXACT.back_substitute(normalized,seed,1224,budget);original=EXACT.canonical_lift(warm,retained,budget)
    if prior_endpoint.get('final_projected_vector')!=list(map(str,warm))or prior_endpoint.get('candidate_original_vector')!=list(map(str,original)):raise ValueError('full exact025 projected and original warm endpoint')
    ctx=OLD.context();position={j:i for i,j in enumerate(retained)}
    mapping=dict(ctx=ctx,width=1224,normalized=normalized,converted={p:{j:OLD.to_mp(q,ctx,budget)for j,q in row.items()}for p,row in normalized.items()},pivots=pivots,free=free,retained=retained,recipes=recipes,initial=initial,parent_projected=base,scales=scales,scale_mp=[OLD.to_mp(q,ctx,budget)for q in scales],center_mp=[OLD.to_mp(q,ctx,budget)for q in initial],center_projected_mp=[OLD.to_mp(q,ctx,budget)for q in base],scalar_indices=[position[j]for j in [*range(366),*range(1592,1597)]],C_indices=[position[j]for j in range(1597,1717)],P_indices=[position[j]for j in range(1717,1837)],gram_pairs=[(i,j)for i in range(15)for j in range(i,15)],resident_cells=2*sum(map(len,normalized.values()))+8*1224+8*444)
    zmp=[OLD.to_mp(q,ctx,budget)for q in z]
    if [OLD.record_fraction(OLD.mp_record(v))for v in zmp]!=z:raise ValueError('saved269bit z represented exactly')
    forward,diag,_=centered_forward(mapping,zmp,budget,diagnostics=True)
    budget.charge(10*len(warm));error=max((abs(OLD.record_fraction(OLD.mp_record(v))-q)/max(F(1),abs(q))for v,q in zip(forward,warm)),default=F(0))
    calibration=dict(initial_forward_mp=[OLD.mp_record(v)for v in forward],warm_exact_reference_relative_error=str(error),tolerance='1e-40',passed=error<=F(1,10**40),initial_forward=diag,reference='exact publication025 projected endpoint')
    if not calibration['passed']:raise ValueError('fixed80digit warm forward consistency failed')
    alphamp=OLD.to_mp(alpha,ctx,budget)
    if OLD.record_fraction(OLD.mp_record(alphamp))!=alpha:raise ValueError('initial step exactly represented')
    mapping.update(warm_z=zmp,warm_forward_mp=forward,warm_projected=warm,warm_free=warm_free,fixed_normalizers=normalizers,initial_step=alphamp,calibration=calibration);budget.cells(mapping['resident_cells']+len(original))
    receipt=dict(schema='primitive-state-backtracking-cone-map-v1',complete=True,width=1224,pivot_columns=pivots,free_indices=free,center_projected_vector=list(map(str,base)),initial_free_vector=list(map(str,initial)),warm_z_mp=[OLD.mp_record(v)for v in zmp],warm_free_vector=list(map(str,warm_free)),warm_projected_vector=list(map(str,warm)),scale_vector=list(map(str,scales)),normalizers=list(map(str,normalizers)),initial_step=OLD.mp_record(alphamp),source_failed_trial_step=str(last_step),precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,calibration=calibration,limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_bits,max_map_bytes=max_map_bytes),**FLAGS)
    budget.charge(2*(len(encoded(receipt))//64+1));receipt['counts']=budget.counts()
    if len(encoded(receipt))>max_map_bytes:raise OverflowError('bounded backtracking warm receipt')
    return mapping,receipt

def iteration_work_reserve(mapping):
    E=sum(map(len,mapping['converted'].values()));w=mapping['width'];n=len(mapping['free']);sc=len(mapping['scalar_indices']);pairs=len(mapping['gram_pairs']);p=len(mapping['pivots'])
    forward=4*E+2*p+3*w+2*n
    metrics=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)+6*w
    adjoints=3*(2*E+w+n);model=200*n+8192
    return 12*(forward+metrics+model+4*n+16384)+adjoints+4096*n+131072

def exact_endpoint(mapping,proposal,cache,necessary,*,deadline,max_operations=25000000,max_bits=4096,max_endpoint_bytes=2097152):
    budget=Budget(deadline,max_operations,6000000,max_bits)
    if max_operations>25000000 or type(max_endpoint_bytes)is not int or not 4096<=max_endpoint_bytes<=2097152:raise ValueError('bounded exact endpoint')
    out=dict(schema='primitive-state-backtracking-cone-endpoint-v1',complete=False,final_free_vector=None,final_projected_vector=None,candidate_original_vector=None,free_indices=mapping['free'],diagnostics=None,**FLAGS)
    try:
        if proposal.get('complete')is not True or proposal.get('schema')!=SCHEMA:raise ValueError('complete single warm backtracking proposal')
        z=[budget.q(OLD.record_fraction(v))for v in proposal['final_z_mp']]
        if len(z)!=len(mapping['free']):raise ValueError('full exact final increment')
        free=[budget.add(c,budget.mul(D,v))for c,D,v in zip(mapping['initial'],mapping['scales'],z)]
        if list(map(str,free))!=proposal['final_free_vector']:raise ValueError('exact024 center plus final dyadic')
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


def propose(mapping,*,deadline,max_operations=220000000,checkpoint=None,max_trace_bytes=33554432):
    if type(max_operations)is not int or not 0<max_operations<=220000000 or type(max_trace_bytes)is not int or not 4096<=max_trace_bytes<=33554432:raise ValueError('bounded fixed proposal')
    budget=Budget(deadline,max_operations,6000000,4096);ctx=mapping['ctx'];start=time.monotonic();best=None;trace_bytes=0
    out=dict(schema=SCHEMA,status='unknown',complete=False,precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,free_indices=mapping['free'],initial_free_vector=list(map(str,mapping['initial'])),scale_vector=list(map(str,mapping['scales'])),warm_free_vector=list(map(str,mapping['warm_free'])),power_trace=[],iterations=[],final_free_vector=None,**FLAGS)
    def save(phase):
        retained_trial_cells=sum(1+2*len(entry['trials'])for entry in out['iterations'])
        budget.cells(mapping.get('resident_cells',sum(map(len,mapping['normalized'].values())))+60*mapping['width']+12*len(mapping['free'])*(4+retained_trial_cells))
        if checkpoint:checkpoint(dict(phase=phase,counts=budget.counts(),accepted_iterations=sum(v.get('accepted',False) for v in out['iterations']),**FLAGS))
    try:
        z=list(mapping['warm_z']);x=list(mapping['warm_forward_mp']);calibration=mapping['calibration'];budget.charge(len(z)+len(x));out['calibration']=calibration;out['initial_z_mp']=[OLD.mp_record(v) for v in z];out['initial_step']=OLD.mp_record(mapping['initial_step'])
        penalties,coordinate,details=block_metrics(mapping,x,budget,apply_adjoint=False);b=list(mapping['fixed_normalizers']);normalizers=[OLD.to_mp(q,ctx,budget) for q in b];r=[p/v for p,v in zip(penalties,normalizers)];value=max(r);best=list(z)
        out.update(initial_block_penalties=[OLD.mp_record(p) for p in penalties],normalizers=list(map(str,b)),initial_normalized_blocks=[OLD.mp_record(q) for q in r],initial_objective=OLD.mp_record(value),initial_merit_details=details)
        stop='zero_initial_numerical_defect' if value==0 else 'iteration_limit'
        if value:
            gradients=[J.scaled_adjoint(mapping,[v/bb for v in g],budget) for g,bb in zip(coordinate,normalizers)];budget.charge(3*mapping['width'])
            lower=ctx.power(2,-900);upper=ctx.power(2,900);alpha=mapping['initial_step'];out['initial_step']=OLD.mp_record(alpha);trace_bytes=len(encoded(out));budget.charge(trace_bytes)
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
