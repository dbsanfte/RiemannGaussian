"""Independent warm backtracking trace consistency and exact endpoints.

The designated published024 chart and completed025 point are prior mathematical
premises. No hashes, source sweeps, old elimination or numerical optimization
proofs are used.
"""
from fractions import Fraction as F
import time
import check_primitive_state_feedback_cone_search as CACHED
AFFINE=CACHED.AFFINE
BALANCED=CACHED.BALANCED
require=CACHED.require
Budget=CACHED.Budget
encoded=CACHED.encoded
false_flags=CACHED.false_flags
mp_fraction=CACHED.mp_fraction
_near=CACHED._near
_vector=CACHED._vector
_dot=CACHED._dot
_block_metrics=CACHED._block_metrics
verify_simplex_model=CACHED.verify_simplex_model
SCHEMA='primitive-state-backtracking-cone-search-v1'
PRECISION=dict(CACHED.PRECISION,calibration_scope='warm forward versus exact publication025 endpoint only; prior map checks reused')
MODEL=dict(CACHED.MODEL,normalizer_rule='reuse publication025 initial-floor normalizers unchanged; never renormalize warm penalties')
SEARCH=dict(CACHED.SEARCH,power_steps=0,armijo_trials=12,initial_step='half the last failed trial of publication025; reject outside fixed positive range; no new power pass',iteration_budget_policy='reserve twelve model/Armijo trials and three accepted block adjoints before iteration')
SCALING=dict(rule='reuse saved publication025 positive D unchanged by projected free_index',new_column_responses=0,new_norm_calculations=0,exponent_abs_cap=900,norms_verified=False,new_map_norm_preconditioner=False)
SEED='exact publication024 center plus saved publication025 final269bit z; no recentering, clipping or rerounding'
FLAGS=CACHED.FLAGS

def iteration_work_reserve(license):
    E=license.summary['sparse_map_entries'];w=len(license.parent_vector);n=len(license.free);p=len(license.pivots)
    shape=license.source['shape'];sc=license.source['offset']-2*shape[1];pairs=120
    forward=4*E+2*p+w+2*n
    metrics=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)+6*w
    adjoints=3*(2*E+w+n);model=200*n+8192
    return 12*(forward+metrics+model+4*n+16384)+adjoints+4096*n+131072+24*w


def _verify_budget_stop(license,proposal,budget,max_trace_bytes):
    stop=proposal.get('budget_stop');require(type(stop)is dict,'explicit complete last-point balanced budget stop')
    keys=('before_iteration','operations','max_operations','remaining_operations','worst_iteration_work_reserve','finalization_work_reserve','trace_retained_bytes','max_trace_bytes','worst_iteration_trace_bytes','finalization_trace_bytes')
    require(set(stop)==set(keys)|{'resource'} and all(type(stop[k])is int and stop[k]>=0 for k in keys),'strict finite budget stop counters')
    n=len(license.free);work=iteration_work_reserve(license);tail=max_trace_bytes+20000*n+131072;perstep=65536+48*96*n;final=8192+3000*n
    require(stop['before_iteration']==len(proposal['iterations'])<128 and stop['max_operations']==220000000 and stop['operations']<=proposal['counts']['operations']<=220000000 and stop['remaining_operations']==220000000-stop['operations'],'budget stop before next full iteration')
    require(stop['worst_iteration_work_reserve']==work and stop['finalization_work_reserve']==tail and stop['max_trace_bytes']==max_trace_bytes and stop['worst_iteration_trace_bytes']==perstep and stop['finalization_trace_bytes']==final,'independently reconstructed fixed step/export reserves')
    keys=('schema','status','complete','precision','search','model','scaling','seed_rule','free_indices','initial_free_vector','scale_vector','warm_free_vector','calibration','initial_z_mp','initial_block_penalties','normalizers','initial_normalized_blocks','initial_objective','initial_merit_details','power_trace','initial_step')
    initial={k:proposal[k]for k in keys};initial.update(status='unknown',complete=False,iterations=[],final_free_vector=None,**FLAGS)
    retained=len(encoded(initial))+sum(len(encoded(item))+1 for item in proposal['iterations']);budget.charge(retained//64+len(proposal['iterations'])+1)
    require(stop['trace_retained_bytes']==retained,'exact retained complete-prefix serialization proxy')
    op_short=stop['remaining_operations']<work+tail;byte_short=max_trace_bytes-retained<perstep+final
    require(stop['resource']=='operations' and op_short or stop['resource']=='trace_bytes' and not op_short and byte_short,'actual bounded-work or byte shortfall stops before new model')


def verify_proposal_trace(license,proposal,budget,*,max_trace_bytes=33554432):
    require(type(proposal)is dict and proposal.get('schema')==SCHEMA,'known balanced finite numerical proposal');payload=encoded(proposal);require(len(payload)<=max_trace_bytes,'bounded entire balanced history');budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    for k in FLAGS:require(proposal.get(k)is False,'no balanced gradient/model/cone/global theorem claim')
    require(proposal.get('precision')==PRECISION and proposal.get('search')==SEARCH and proposal.get('model')==MODEL and proposal.get('scaling')==SCALING and proposal.get('seed_rule')==SEED,'fixed balanced mixed-precision numerical policy')
    require(proposal.get('warm_free_vector')==list(map(str,license.warm_free)),'actual exact025 warm free vector')
    require(proposal.get('free_indices')==license.free and proposal.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free] and proposal.get('scale_vector')==list(map(str,license.scales)),'exact024 center and selective positive scales')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict balanced proposal completion')
    n=len(license.free);current=None;initial_error=None
    if 'initial_z_mp'in proposal:
        current=_vector(proposal['initial_z_mp'],n,budget);require(current==license.initial_z,'exact exported025 warm increment; no reset or center reround')
    calibration=proposal.get('calibration')
    if calibration is not None:
        require(calibration==license.setup['calibration'],'same independently checked centered affine calibration')
        initial_error=F(calibration['warm_exact_reference_relative_error'])
    power=proposal.get('power_trace');iterations=proposal.get('iterations');require(type(power)is list and len(power)==0 and type(iterations)is list and len(iterations)<=128,'bounded weighted power and balanced iterations')
    normalizers=None;r=None;value=None;native_calls=0
    if 'initial_block_penalties'in proposal:
        require(type(proposal.get('normalizers'))is list and len(proposal['normalizers'])==3,'three frozen positive block normalizers')
        normalizers=[budget.rational(q)for q in proposal['normalizers']];require(all(q>0 for q in normalizers),'strict positive normalizers')
        penalties,expected=_block_metrics(proposal['initial_block_penalties'],normalizers,budget)
        require(normalizers==license.normalizers,'unchanged025 original-seed normalizers; never renormalize warm penalties')
        r=_vector(proposal.get('initial_normalized_blocks'),3,budget);require(all(q>=0 and _near(q,e,budget)for q,e in zip(r,expected)),'normalized initial block ratios')
        value=mp_fraction(proposal.get('initial_objective'),budget);require(value==max(r) and value>=0,'max of three normalized initial blocks');native_calls=1
    alpha=mp_fraction(proposal['initial_step'],budget)if 'initial_step'in proposal else None
    if alpha is not None:require(alpha==license.initial_step and F(1,1<<900)<=alpha<=F(1<<900),'half of last rejected025 trial, no power pass')
    accepted=0;model_calls=0;finite_trials=0;stationary=False;terminated=False;max_gap=F(0)
    for index,item in enumerate(iterations):
        require(type(item)is dict and type(item.get('index'))is int and item['index']==index and not terminated and current is not None and normalizers is not None and value is not None and alpha is not None,'ordered initialized balanced iteration')
        require(item.get('reserved_iteration_work')==iteration_work_reserve(license),'full worst balanced iteration reservation')
        before=mp_fraction(item.get('objective_before'),budget);record_r=_vector(item.get('normalized_blocks'),3,budget)
        require(before==value and record_r==r,'continuous max objective and normalized block history')
        rows=item.get('block_gradients');require(type(rows)is list and len(rows)==3,'three complete numerical normalized z gradients');gradients=[_vector(row,n,budget)for row in rows]
        trials=item.get('trials');require(type(trials)is list and len(trials)<=12 and type(item.get('accepted'))is bool,'at most twelve recomputed model Armijo trials')
        passed=False
        for trial_index,trial in enumerate(trials):
            require(type(trial)is dict and type(trial.get('index'))is int and trial['index']==trial_index and not passed and not stationary,'ordered stop-at-first-success balanced trials')
            step=mp_fraction(trial.get('step'),budget);require(_near(step,alpha/F(1<<trial_index),budget) and step>0,'fixed halving step trials')
            if trial.get('finite')is False:
                if trial.get('reason')=='fixed numerical model-gap consistency gate failed':
                    require(step>=F(1,1<<900) and status=='unknown' and index==len(iterations)-1 and trial_index==len(trials)-1,'failed model is terminal UNKNOWN with no retry')
                    _,_,diagnostic=verify_simplex_model(trial.get('model'),r,gradients,step,budget,allow_inconsistent=True);require(diagnostic['consistent']is False,'failed raw model actually fails fixed gap gate');model_calls+=1;terminated=True;continue
                require(step<F(1,1<<900) and trial.get('reason')=='step below declared minimum','only declared below-minimum numerical skip');continue
            require(trial.get('finite')is True,'explicit finite model trial')
            direction,norm2,diagnostic=verify_simplex_model(trial.get('model'),r,gradients,step,budget);model_calls+=1;max_gap=max(max_gap,F(diagnostic['model_gap']))
            if trial.get('stationary')is True:
                require(norm2==0 and not item['accepted'] and trial_index==len(trials)-1,'numerical model stationarity has zero direction and no accepted trial');stationary=True;terminated=True;continue
            require(norm2>0,'nonstationary trial direction is nonzero')
            z=_vector(trial.get('z'),n,budget);approximate=_vector(trial.get('approximate_free_mp'),n,budget)
            require(all(_near(q,v+d,budget)for q,v,d in zip(z,current,direction)) and all(_near(q,license.parent_vector[i]+D*v,budget)for q,i,D,v in zip(approximate,license.free,license.scales,z)),'rounded centered z/f trial coordinate updates')
            pnew,expected=_block_metrics(trial.get('block_penalties'),normalizers,budget);rnew=_vector(trial.get('normalized_blocks'),3,budget);require(all(q>=0 and _near(q,e,budget)for q,e in zip(rnew,expected)),'same frozen normalizers applied to every block')
            newvalue=mp_fraction(trial.get('objective'),budget);threshold=mp_fraction(trial.get('armijo_threshold'),budget)
            require(newvalue==max(rnew) and newvalue>=0 and _near(threshold,value-norm2/(8*step),budget) and trial.get('armijo_passed')is (newvalue<=threshold),'max-objective Armijo uses actual scaled direction norm/step')
            native_calls+=1;finite_trials+=1
            if newvalue<=threshold:passed=True;current=z;r=rnew;value=newvalue;alpha=min(F(1<<900),2*step);accepted+=1
        if passed:require(mp_fraction(item.get('next_start_step'),budget)==alpha,'fixed capped2x accepted-step carry')
        require(item['accepted']is passed,'accepted iteration equals first passed trial')
        if not passed and not stationary:
            if status=='proposed' or index<len(iterations)-1:require(len(trials)==12,'failed line search exhausts all twelve models')
            terminated=True
    if 'last_finite_z_mp'in proposal:require(current is not None and _vector(proposal['last_finite_z_mp'],n,budget)==current,'retained UNKNOWN warm increment is last complete point')
    counts=CACHED._phase_counts(proposal,220000000)
    require(counts['operations']>=native_calls*2*96*15**3,'all recorded repeated native eigensolves charged')
    if status=='proposed':
        require(counts['operations']<=220000000 and counts['peak_live_cells']<=6000000 and current is not None and value is not None and calibration is not None and initial_error is not None,'complete bounded calibrated balanced proposal')
        final=_vector(proposal.get('final_z_mp'),n,budget);require(final==current,'last complete accepted or stationary warm increment')
        free=[budget.add(license.parent_vector[i],budget.mul(D,z))for i,D,z in zip(license.free,license.scales,final)]
        require(proposal.get('final_free_vector')==list(map(str,free)) and mp_fraction(proposal.get('final_objective'),budget)==value and _vector(proposal.get('final_normalized_blocks'),3,budget)==r,'unrounded exact final f024+D*z and continuous final max objective')
        stop=proposal.get('stop_reason');require(stop in ('iteration_limit','budget_stop','line_search_failed','numerical_model_stationarity','zero_initial_numerical_defect'),'declared proposal-only stopping reason')
        if stop=='zero_initial_numerical_defect':require(value==0 and not iterations and not power,'observed zero initial defect stops without a model')
        else:
            if stop=='iteration_limit':require(len(iterations)==128 and iterations[-1]['accepted']is True,'fixed128iteration endpoint')
            elif stop=='budget_stop':_verify_budget_stop(license,proposal,budget,max_trace_bytes)
            elif stop=='numerical_model_stationarity':require(stationary,'actual numerical zero-direction model stop')
            else:require(iterations and not iterations[-1]['accepted'] and len(iterations[-1]['trials'])==12 and not stationary,'actual exhausted twelve-trial balanced line search')
    else:require(type(proposal.get('reason'))is str and bool(proposal['reason']),'explicit incomplete numerical proposal cause')
    last_penalties=proposal.get('initial_block_penalties')
    for item in iterations:
        for trial in item['trials']:
            if trial.get('armijo_passed')is True:last_penalties=trial['block_penalties']
    return dict(final_block_penalties=last_penalties,verified=True,complete=status=='proposed',proposal_history_only=True,gradient_or_merit_certified=False,intermediate_iterates_exact=False,block_normalizers_verified_from_exported_penalties=normalizers is not None,actual_initial_exact_reference_relative_error=str(initial_error)if initial_error is not None else None,power_iterations=len(power),gradient_iterations=len(iterations),accepted_iterations=accepted,finite_armijo_trials=finite_trials,native_eigensolve_calls=2*native_calls,simplex_models_checked=model_calls,stop_reason=proposal.get('stop_reason'),initial_objective=proposal.get('initial_objective'),final_objective=proposal.get('final_objective'),initial_block_penalties=proposal.get('initial_block_penalties'),final_normalized_blocks=proposal.get('final_normalized_blocks'),maximum_recorded_model_gap=str(max_gap),native_PSD_projection_precision='binary64',affine_map_precision_decimal_digits=80,audit_operations=budget.operations,audit_cells=budget.audit_cells,independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)



def verify_endpoint(license,proposal,endpoint,b,*,max_endpoint_bytes=2097152):
    require(type(endpoint)is dict and endpoint.get('schema')=='primitive-state-backtracking-cone-endpoint-v1','known exact cached endpoint');payload=encoded(endpoint);require(len(payload)<=max_endpoint_bytes,'bounded full exact endpoint');b.charge(len(payload)//64+1)
    false_flags(endpoint);require(all(endpoint.get(k)is False for k in FLAGS),'complete endpoint scope flags');CACHED._phase_counts(endpoint,25000000)
    require(endpoint.get('limits')==dict(max_operations=25000000,max_coefficient_bits=4096,max_endpoint_bytes=max_endpoint_bytes),'fixed25m exact endpoint producer')
    require(type(endpoint.get('complete'))is bool,'explicit endpoint completion')
    if not endpoint['complete']:
        require(endpoint.get('candidate_original_vector')is None and endpoint.get('final_projected_vector')is None and endpoint.get('diagnostics')is None and type(endpoint.get('reason'))is str,'incomplete endpoint cannot license a candidate')
        return dict(verified=True,complete=False,endpoint_verified=False,candidate_equations_verified=False,finite_candidate_feasible=None,**FLAGS)
    require(proposal.get('complete')is True and endpoint.get('free_indices')==license.free,'exact endpoint uses complete proposal and updated444 free coordinates')
    z=_vector(proposal.get('final_z_mp'),444,b);free=[b.add(license.parent_vector[i],b.mul(D,v))for i,D,v in zip(license.free,license.scales,z)]
    require(endpoint.get('final_free_vector')==proposal.get('final_free_vector')==list(map(str,free)),'exact center plus exported dyadic increment is never rerounded')
    seed=license.parent_vector[:]
    for i,q in zip(license.free,free):seed[i]=q
    y=AFFINE.backsubstitute(license.rows,seed,b);require(endpoint.get('final_projected_vector')==list(map(str,y)),'all780 cached rows descend in pivot column order')
    x=AFFINE.lift(y,license.retained,b);require(endpoint.get('candidate_original_vector')==list(map(str,x)),'complete1957 original canonical signed/storage lift')
    declaration=dict(complete=True,status='complete',original_columns=1957,projected_columns=1224,rows=len(license.cache['original']['rhs']),retained_indices=license.retained,recipes=[[i,[[j,str(q)]for j,q in sorted(recipe.items())]]for i,recipe in sorted(license.recipes.items())])
    full,_,rhs,_,_=AFFINE.decode_source(license.cache,declaration,b);require(len(full)==5641,'all5641 original equations')
    computed=AFFINE.endpoint_check(full,rhs,license.feedback_full,license.feedback_rhs,x,b)
    diag=endpoint.get('diagnostics');require(type(diag)is dict,'explicit endpoint diagnostics')
    computed=dict(original_equations=computed['all_original_rows_checked'],original_equation_mismatches=computed['equality_mismatches'],new_equation_residual=computed['new_row_residual'],affine_equalities_satisfied=computed['equality_mismatch_count']==0 and computed['new_row_residual']=='0',negative_scalars=[dict(coordinate=r['index'],value=r['value'])for r in computed['negative_scalars']],psd_blocks=[dict(name=name,**r)for name,r in computed['psd_blocks'].items()],all_cones_satisfied=computed['negative_scalar_count']==0 and all(r['psd']for r in computed['psd_blocks'].values()))
    for key in ('original_equations','original_equation_mismatches','new_equation_residual','affine_equalities_satisfied','negative_scalars','all_cones_satisfied'):require(diag.get(key)==computed.get(key),'independent exact endpoint diagnostic '+key)
    require(computed['affine_equalities_satisfied']is True,'all original and learned equations exactly zero')
    require(type(diag.get('psd_blocks'))is list and len(diag['psd_blocks'])==3,'complete three15x15 PSD reports')
    offset=1597
    for report,verdict in zip(diag['psd_blocks'],computed['psd_blocks']):
        require(report.get('name')==verdict['name'],'original block identity');matrix=[[F(0)]*15 for _ in range(15)]
        for a in range(15):
            for c in range(a,15):matrix[a][c]=matrix[c][a]=x[offset];offset+=1
        AFFINE.check_psd_report(matrix,report,verdict,b)
    return dict(verified=True,complete=True,endpoint_verified=True,candidate_equations_verified=True,finite_candidate_feasible=computed['all_cones_satisfied'],full_original_rows_checked=5641,feedback_row_verified=True,negative_scalar_count=len(computed['negative_scalars']),PSD_blocks_checked=3,PSD_failures=sum(not r['psd']for r in computed['psd_blocks']),**FLAGS)



def warm_license(cache,chart,center,necessary,review024,prior_map,prior_proposal,prior_endpoint,review025,b):
    """Use actual designated published024/025 inputs as prior span/point premises."""
    license=CACHED.validate_chart(cache,chart,center,necessary,review024,b)
    require(review025.get('schema')=='primitive-state-feedback-cone-search-independent-review-v1'and review025.get('all_passed')is True and review025.get('status')=='ENDPOINT_CHECKED'and review025.get('endpoint_verified')is True and review025.get('candidate_equations_verified')is True,'completed025 exact endpoint premise')
    check=review025.get('independent_search_check');require(type(check)is dict and check.get('verified')is True and check.get('complete')is True and check.get('endpoint_verified')is True and check.get('candidate_equations_verified')is True and check.get('full_original_rows_checked')==5641 and check.get('feedback_row_verified')is True,'completed025 independent endpoint check')
    require(prior_map.get('schema')=='primitive-state-feedback-cone-map-v1'and prior_map.get('complete')is True and prior_map.get('free_indices')==license.free and prior_map.get('pivot_columns')==license.pivots and prior_map.get('center_projected_vector')==list(map(str,license.parent_vector)),'same cached024 center and780-pivot chart')
    require(prior_proposal.get('schema')==CACHED.SCHEMA and prior_proposal.get('complete')is True and prior_proposal.get('status')=='proposed'and prior_proposal.get('stop_reason')=='line_search_failed','fixed025 bounded unsuccessful backtracking continuation')
    for v in (prior_map,prior_proposal,prior_endpoint):false_flags(v)
    scales=[b.rational(q)for q in prior_map.get('scale_vector',[])];require(len(scales)==444 and prior_proposal.get('scale_vector')==list(map(str,scales))and prior_proposal.get('free_indices')==license.free and prior_proposal.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free],'actual025 positive diagonal keyed by cached free coordinate')
    for D in scales:
        require(D>0 and D.numerator&(D.numerator-1)==0 and D.denominator&(D.denominator-1)==0,'positive dyadic inherited scale')
        exponent=D.denominator.bit_length()-D.numerator.bit_length();require(abs(exponent)<=900,'bounded inherited scale exponent')
    z=_vector(prior_proposal.get('final_z_mp'),444,b);free=[b.add(license.parent_vector[i],b.mul(D,v))for i,D,v in zip(license.free,scales,z)]
    require(prior_proposal.get('final_free_vector')==prior_endpoint.get('final_free_vector')==list(map(str,free))and prior_endpoint.get('schema')=='primitive-state-feedback-cone-endpoint-v1'and prior_endpoint.get('complete')is True and prior_endpoint.get('free_indices')==license.free,'exact025 free point is unrounded024 center plus D*z025')
    seed=license.parent_vector[:]
    for i,q in zip(license.free,free):seed[i]=q
    y=AFFINE.backsubstitute(license.rows,seed,b);require(prior_endpoint.get('final_projected_vector')==list(map(str,y))and prior_endpoint.get('candidate_original_vector')==list(map(str,AFFINE.lift(y,license.retained,b))),'saved025 exact point and original canonical lift match cached chart')
    penalties=_vector(prior_proposal.get('initial_block_penalties'),3,b);normalizers=[b.rational(q)for q in prior_proposal.get('normalizers',[])];require(normalizers==[max(q,F(1,1<<40))for q in penalties]and all(q>=0 for q in penalties),'original025 seed normalizers retained exactly')
    iterations=prior_proposal.get('iterations');require(type(iterations)is list and iterations and iterations[-1].get('accepted')is False,'actual025 exhausted final line search')
    trials=iterations[-1].get('trials');require(type(trials)is list and len(trials)==3 and all(t.get('finite')is True and t.get('armijo_passed')is False and type(t.get('index'))is int and t['index']==i for i,t in enumerate(trials)),'all three actual025 trials were rejected')
    steps=[mp_fraction(t.get('step'),b)for t in trials];require(all(q>0 for q in steps)and steps[1]==steps[0]/2 and steps[2]==steps[1]/2,'fixed025 rejected-trial halving history')
    license.initial_z=z;license.scales=scales;license.normalizers=normalizers;license.initial_step=b.div(steps[-1],F(2));license.warm_vector=y;license.warm_free=free
    require(F(1,1<<900)<=license.initial_step<=F(1<<900),'fixed half last025 rejected step within declared range')
    return license


def verify_setup(license,receipt,b,*,max_map_bytes=8388608):
    require(type(receipt)is dict and receipt.get('schema')=='primitive-state-backtracking-cone-map-v1'and receipt.get('complete')is True and len(encoded(receipt))<=max_map_bytes,'bounded complete warm cached-map receipt');b.charge(len(encoded(receipt))//64+1)
    require(all(receipt.get(k)is False for k in FLAGS),'complete warm map scope flags')
    require(receipt.get('precision')==PRECISION and receipt.get('search')==SEARCH and receipt.get('model')==MODEL and receipt.get('scaling')==SCALING and receipt.get('seed_rule')==SEED,'fixed warm mixed-precision policy')
    require(receipt.get('width')==1224 and receipt.get('pivot_columns')==license.pivots and receipt.get('free_indices')==license.free and receipt.get('center_projected_vector')==list(map(str,license.parent_vector))and receipt.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free],'same exact024 center and cached780 chart')
    require(receipt.get('warm_z_mp')is not None and _vector(receipt['warm_z_mp'],444,b)==license.initial_z and receipt.get('warm_free_vector')==list(map(str,license.warm_free))and receipt.get('warm_projected_vector')==list(map(str,license.warm_vector))and receipt.get('scale_vector')==list(map(str,license.scales)),'actual025 warm increment, exact endpoint and inherited D')
    require(receipt.get('normalizers')==list(map(str,license.normalizers))and mp_fraction(receipt.get('initial_step'),b)==license.initial_step and b.rational(receipt.get('source_failed_trial_step'))==2*license.initial_step,'unchanged025 normalizers and half last rejected trial')
    require(receipt.get('limits')==dict(max_operations=5000000,max_cells=6000000,max_coefficient_bits=4096,max_map_bytes=max_map_bytes),'single5m warm setup allocation')
    CACHED._phase_counts(receipt,5000000)
    calibration=receipt.get('calibration');require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40'and calibration.get('reference')=='exact publication025 projected endpoint','warm affine-only calibration')
    actual=_vector(calibration.get('initial_forward_mp'),1224,b);error=max(abs(q-v)/max(F(1),abs(v))for q,v in zip(actual,license.warm_vector));b.charge(4*1224)
    require(error<=F(1,10**40)and calibration.get('warm_exact_reference_relative_error')==str(error),'reported warm forward agrees with saved exact025 projected endpoint')
    license.setup=receipt
    return dict(verified=True,warm_endpoint_verified=True,positive_dyadic_scales_verified=True,normalizers_unchanged=True,power_passes=0,new_norm_responses=0,chart_used_without_old_tape_replay=True,**FLAGS)


def verify_search(cache,chart,center,necessary,review024,prior_map,prior_proposal,prior_endpoint,review025,mapreceipt,proposal=None,endpoint=None,*,deadline=None,max_operations=150000000,max_cells=6000000,max_coefficient_bits=4096,max_map_bytes=8388608,max_trace_bytes=33554432,max_endpoint_bytes=2097152):
    require(type(max_operations)is int and 0<max_operations<=150000000,'one final150m audit reservation')
    for value,cap in ((max_map_bytes,8388608),(max_trace_bytes,33554432),(max_endpoint_bytes,2097152)):require(type(value)is int and 0<value<=cap,'bounded backtracking artifact')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,20000000,max_coefficient_bits)
    license=warm_license(cache,chart,center,necessary,review024,prior_map,prior_proposal,prior_endpoint,review025,b);setup=verify_setup(license,mapreceipt,b,max_map_bytes=max_map_bytes)
    trace=verify_proposal_trace(license,proposal,b,max_trace_bytes=max_trace_bytes)if proposal is not None else None
    require(endpoint is None or proposal is not None,'exact endpoint requires explicit proposal')
    exact=verify_endpoint(license,proposal,endpoint,b,max_endpoint_bytes=max_endpoint_bytes)if endpoint is not None else None
    return dict(verified=True,complete=bool(exact and exact['complete']),setup_check=setup,trace_check=trace,endpoint_check=exact,endpoint_verified=bool(exact and exact['endpoint_verified']),candidate_equations_verified=bool(exact and exact['candidate_equations_verified']),finite_candidate_feasible=exact['finite_candidate_feasible']if exact else None,full_original_rows_checked=exact.get('full_original_rows_checked',0)if exact else 0,feedback_row_verified=bool(exact and exact.get('feedback_row_verified')),chart_used_without_old_tape_replay=True,trace_exports_checked=trace is not None,accepted_iterations=trace.get('accepted_iterations',0)if trace else 0,stop_reason=trace.get('stop_reason')if trace else None,initial_block_penalties=trace.get('initial_block_penalties')if trace else None,final_block_penalties=trace.get('final_block_penalties')if trace else None,initial_objective=trace.get('initial_objective')if trace else None,final_objective=trace.get('final_objective')if trace else None,audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations,**FLAGS)
