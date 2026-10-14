"""Independent augmented cached-chart, proposal exports and exact endpoints.

The designated published024 span and027 formal-row evaluations are mathematical
premises. New rows are reduced again, without old elimination or source probes.
Numerical norms, gradients, eigenvalues and minimax optimality are not certified.
"""
from fractions import Fraction as F
import time
import check_primitive_state_feedback_cone_search as CACHED
import check_primitive_state_backtracking_cone_search as TRACE
AFFINE=CACHED.AFFINE
BALANCED=CACHED.BALANCED
require=CACHED.require
Budget=CACHED.Budget
encoded=CACHED.encoded
mp_fraction=CACHED.mp_fraction
_near=CACHED._near
_vector=CACHED._vector
_dot=CACHED._dot
_block_metrics=CACHED._block_metrics
verify_simplex_model=CACHED.verify_simplex_model
homogeneous=CACHED.homogeneous
adjoint=CACHED.adjoint
positive_dyadic=CACHED.positive_dyadic


def compose_chart(rows, appended, width, b):
    """Validate and compose an explicit bounded list of normalized exact rows."""
    require(type(width)is int and 0<width<=1224 and type(rows)is list and len(rows)<=width and type(appended)is list and len(appended)<=64 and len(rows)+len(appended)<=width,'bounded augmented chart dimension and row list')
    basis={}
    for index,item in enumerate(rows+appended):
        p=item.get('pivot');require(type(p)is int and 0<=p<width and p not in basis,'unique variable pivot; no contradiction chart')
        row={};last=-1
        for j,text in item.get('terms',[]):
            require(type(j)is int and last<j<=width,'ordered complete chart coefficients');last=j;q=b.rational(text);require(q!=0,'nonzero sparse chart terms');row[j]=q
        require(row.get(p)==1 and min(row)==p,'normalized minimum variable pivot')
        if index>=len(rows):require(not(set(row)&set(basis)),'appended row eliminates every previous pivot')
        basis[p]=row
    b.live(sum(map(len,basis.values()))+2*width)
    return basis, sorted(basis), [i for i in range(width)if i not in basis]


def decode_constraint(necessary,retained,recipes,b):
    require(necessary.get('schema')=='primitive-state-formal-identity-necessary-row-v1'and necessary.get('width')==1957 and necessary.get('X')==9 and necessary.get('layout',{}).get('n_variables')==1957,'actual original fresh formal-row coordinates')
    assignment=necessary.get('assignment');require(type(assignment)is list and len(assignment)==35 and all(type(q)is int and abs(q)<=4096 for q in assignment),'complete explicit fresh formal assignment')
    full=[F(0)]*1957;last=-1
    for item in necessary.get('entries',[]):
        j=item['index'];require(type(j)is int and last<j<1957,'complete ordered learned coefficients');last=j;full[j]=b.rational(item['coefficient']);require(full[j]!=0,'nonzero sparse learned coefficient')
    require(necessary.get('zero_coordinates')==[j for j,q in enumerate(full)if not q]and all(full[j]==0 for j in range(1592,1597)),'exact zero complement and five absent slacks')
    for omitted,recipe in recipes.items():
        value=F(0)
        for j,q in recipe.items():value=b.add(value,b.mul(q,full[j]))
        require(full[omitted]==value,'complete signed and storage learned dependencies')
    return full,[full[j]for j in retained],b.rational(necessary['rhs'])


def reduce_constraint(necessary, rows, retained, recipes, index, b):
    full, projected, rhs=decode_constraint(necessary,retained,recipes,b)
    kind, normalized, rec=AFFINE.reduce_feedback(projected,rhs,rows,b)
    require(kind=='independent'and normalized is not None,'new learned row must independently extend this consistent chart')
    p=rec['chosen_pivot'];rows[p]=normalized
    rank=len(rows)
    record=dict(index=index,classification=kind,**rec,normalized_row=dict(pivot=p,terms=[[j,str(q)]for j,q in sorted(normalized.items())]),coefficient_rank=rank,augmented_rank=rank,free_count=1224-rank)
    return full,rhs,record


def augmented_license(cache, chart024, center024, old_constraint, review024, extension, constraints, review027, report027, seed026, recovery026, map026, b):
    require(review027.get('all_passed')is True and review027.get('schema')=='primitive-state-fresh-identity-probe-independent-review-v1'and review027.get('affine_extension')==extension,'designated completed027 mathematical extension')
    require(report027.get('schema')==27 and report027.get('independent_audit_complete')is True,'completed publication027 row evaluation premise')
    require(type(constraints)is list and len(constraints)==2 and review027.get('necessary_formal_identity_constraints')==constraints,'two actual published027 exact rows')
    base=CACHED.validate_chart(cache,chart024,center024,old_constraint,review024,b)
    oldrows=dict(base.rows);rows=dict(oldrows);reductions=[];fulls=[base.feedback_full];rhss=[base.feedback_rhs];appended=[]
    for index,row in enumerate(constraints):
        full,rhs,rec=reduce_constraint(row,rows,base.retained,base.recipes,index,b);reductions.append(rec);fulls.append(full);rhss.append(rhs);appended.append(dict(source_case=index,**rec['normalized_row']))
    require(extension.get('complete')is True and extension.get('old_rank')==780 and extension.get('coefficient_rank')==782 and extension.get('augmented_rank')==782 and extension.get('free_count')==442 and extension.get('contradiction_row')is None and extension.get('old_tape_replayed')is False and extension.get('formal_family_only')is True,'consistent actual782-pivot formal extension')
    require(extension.get('reductions')==reductions and extension.get('appended_rows')==appended,'independently recomputed exact reductions and normalized rows')
    require([r['chosen_pivot']for r in reductions]==[160,170],'fixed new160/170 pivots')
    require(recovery026.get('all_passed')is True and recovery026.get('endpoint_verified')is True and recovery026.get('candidate_equations_verified')is True and recovery026.get('status')in('RECOVERED_SCALAR_REJECTED','RECOVERED_CONE_CHECKED'),'designated completed026 exact recovery premise')
    require(seed026.get('complete')is True,'complete exact026 seed')
    oldx, y=AFFINE.projected_seed(seed026.get('candidate_original_vector'),base.retained,base.recipes,b)
    require(seed026.get('final_projected_vector')==list(map(str,y))and AFFINE.backsubstitute(oldrows,y,b)==y,'seed actual quotient and all old780 equations')
    free=[i for i in range(1224)if i not in rows];repaired=AFFINE.backsubstitute(rows,y,b);x=AFFINE.lift(repaired,base.retained,b)
    require(all(repaired[i]==y[i]for i in free),'repair preserves all442 remaining exact seed free values')
    base.rows=rows;base.pivots=sorted(rows);base.free=free;base.parent_vector=repaired;base.center_original=x;base.initial_z=[F(0)]*len(free)
    base.learned_full=fulls;base.learned_rhs=rhss;base.extension=extension;base.appended=appended;base.reductions=reductions;base.seed_vector=y;base.map026=map026
    base.affected=sorted(set(j for item in appended for j,_ in item['terms']if j in free));base.unaffected=[j for j in free if j not in base.affected]
    require(len(free)==442 and len(base.affected)==98 and len(base.unaffected)==344,'actual98 affected and344 unchanged free coordinates')
    base.summary=dict(sparse_map_entries=sum(map(len,rows.values())),rank=782,free_count=442,old_tape_replayed=False,prior_span_license_used=True)
    base.normalizers=[b.rational(q)for q in map026.get('normalizers',[])];require(len(base.normalizers)==3 and all(q>=F(1,1<<40) for q in base.normalizers),'unchanged original025 positive normalizers')
    require(map026.get('free_indices')==[i for i in range(1224)if i not in oldrows]and type(map026.get('scale_vector'))is list and len(map026['scale_vector'])==444,'designated complete026 scale coordinate partition')
    base.old_scales={i:b.rational(q)for i,q in zip(map026['free_indices'],map026['scale_vector'])}
    require(set(base.old_scales)==set(i for i in range(1224)if i not in oldrows),'complete coordinate-keyed444 inherited scales')
    require(all(q>0 and (q.numerator&(q.numerator-1))==0 and (q.denominator&(q.denominator-1))==0 and abs(q.numerator.bit_length()-q.denominator.bit_length())<=900 for q in base.old_scales.values()),'inherited strictly positive dyadics')
    return base


def scalar_first_endpoint(full, rhs, learned, targets, x, b):
    require(len(full)==len(rhs)==5641 and len(learned)==len(targets)==3 and len(x)==1957 and all(len(row)==1957 for row in learned),'all5644 equations and original1957 coordinates')
    x=[b.rational(q)for q in x]
    for row,target in zip(full,rhs):
        target=b.rational(target);value=F(0)
        for j,q in row.items():value=b.add(value,b.mul(q,x[j]))
        require(value==target,'every old original equation exactly zero')
    for row,target in zip(learned,targets):
        target=b.rational(target);value=F(0)
        for q,v in zip(row,x):value=b.add(value,b.mul(q,v))
        require(value==target,'every learned exact original equation')
    b.charge(1597);negative=[dict(coordinate=i,value=str(x[i]))for i in range(1597)if x[i]<0]
    psd=[]
    if not negative:
        for block,name in enumerate(('full_child','full_parent','storage_K')):
            matrix=[[F(0)]*15 for _ in range(15)];position=1597+120*block
            for i in range(15):
                for j in range(i,15):matrix[i][j]=matrix[j][i]=x[position];position+=1
            psd.append(dict(name=name,**AFFINE.exact_psd(matrix,b)))
    return dict(full_original_rows_checked=5641,learned_rows_checked=3,full_equations_checked=5644,feedback_row_verified=True,candidate_equations_verified=True,negative_scalar_count=len(negative),scalar_rejection_witness=negative[0]if negative else None,psd_status='NOT_CHECKED_AFTER_SCALAR_REJECTION'if negative else'ALL_THREE_EXACT_BLOCKS_CHECKED',PSD_blocks_checked=0 if negative else 3,PSD_failures=None if negative else sum(not q['psd']for q in psd),finite_candidate_feasible=False if negative else all(q['psd']for q in psd),psd_blocks=None if negative else psd)

FLAGS=CACHED.FLAGS
PRECISION=CACHED.PRECISION
MODEL=dict(TRACE.MODEL,normalizer_rule='reuse original publication025 normalizers from publication026 map unchanged')
SEARCH=dict(TRACE.SEARCH,power_steps=8,initial_step='clamped reciprocal of eight-step weighted power estimate on new map',power_seed='alternating normalized signs',power_zero_policy='stop after first zero operator')
SCALING=dict(rule='retain publication026 D on unaffected surviving coordinates; recompute approximate80digit cone norms on union of appended row surviving supports',exponent_abs_cap=900,new_column_responses=98,unchanged_column_scales=344,norms_verified=False,new_map_norm_preconditioner=False,cone_norm='all366 square and5 slack squares plus C and H Frobenius squared norms',dyadic_rule='smallest integer k with exported approximate norm_squared <= 2^(2*k); D=2^(-k); zero=>1',partial_scaling_allowed=False)
SEED='exact canonical repair of publication026 recovered point preserving442 remaining free coordinates; z0=0'
SCHEMA='primitive-state-augmented-cone-search-v1'
false_flags=CACHED.false_flags
iteration_work_reserve=TRACE.iteration_work_reserve

_phase_counts=CACHED._phase_counts

def _verify_budget_stop(license,proposal,budget,max_trace_bytes):
    stop=proposal.get('budget_stop');require(type(stop)is dict,'explicit complete last-point balanced budget stop')
    keys=('before_iteration','operations','max_operations','remaining_operations','worst_iteration_work_reserve','finalization_work_reserve','trace_retained_bytes','max_trace_bytes','worst_iteration_trace_bytes','finalization_trace_bytes')
    require(set(stop)==set(keys)|{'resource'} and all(type(stop[k])is int and stop[k]>=0 for k in keys),'strict finite budget stop counters')
    n=len(license.free);work=iteration_work_reserve(license);tail=max_trace_bytes+20000*n+131072;perstep=65536+48*96*n;final=8192+3000*n
    require(stop['before_iteration']==len(proposal['iterations'])<128 and stop['max_operations']==195000000 and stop['operations']<=proposal['counts']['operations']<=195000000 and stop['remaining_operations']==195000000-stop['operations'],'budget stop before next full iteration')
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
    require(proposal.get('warm_free_vector')==[str(license.parent_vector[i])for i in license.free],'repaired center free vector')
    require(proposal.get('free_indices')==license.free and proposal.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free] and proposal.get('scale_vector')==list(map(str,license.scales)),'exact repaired center and selective positive scales')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict balanced proposal completion')
    n=len(license.free);current=None;initial_error=None
    if 'initial_z_mp'in proposal:
        current=_vector(proposal['initial_z_mp'],n,budget);require(current==license.initial_z,'same exact269-bit centered augmented repaired center zero increment; no center reround')
    calibration=proposal.get('calibration')
    if calibration is not None:
        require(calibration==license.setup['calibration'],'same independently checked centered affine calibration')
        initial_error=F(calibration['center_exact_reference_relative_error'])
    power=proposal.get('power_trace');iterations=proposal.get('iterations');require(type(power)is list and len(power)<=8 and type(iterations)is list and len(iterations)<=128,'bounded weighted power and balanced iterations')
    normalizers=None;r=None;value=None;native_calls=0
    if 'initial_block_penalties'in proposal:
        require(type(proposal.get('normalizers'))is list and len(proposal['normalizers'])==3,'three frozen positive block normalizers')
        normalizers=[budget.rational(q)for q in proposal['normalizers']];require(all(q>0 for q in normalizers),'strict positive normalizers')
        penalties,expected=_block_metrics(proposal['initial_block_penalties'],normalizers,budget)
        require(normalizers==license.normalizers,'unchanged original025 normalizers')
        r=_vector(proposal.get('initial_normalized_blocks'),3,budget);require(all(q>=0 and _near(q,e,budget)for q,e in zip(r,expected)),'normalized initial block ratios')
        value=mp_fraction(proposal.get('initial_objective'),budget);require(value==max(r) and value>=0,'max of three normalized initial blocks');native_calls=1
    previous=None;previous_norm=None;zero_power=False;estimate=None
    for index,item in enumerate(power):
        require(normalizers is not None and type(item)is dict and type(item.get('index'))is int and item['index']==index and not zero_power,'ordered initialized weighted power pass')
        d=_vector(item.get('vector'),n,budget);op=_vector(item.get('operator'),n,budget);estimate=mp_fraction(item.get('estimate'),budget);norm=mp_fraction(item.get('operator_norm'),budget)
        if previous is not None:require(all(_near(q,v/previous_norm,budget)for q,v in zip(d,previous))if previous_norm else d==previous_direction,'normalized power continuation; unchanged seed after zero operator')
        else:require(all(q*((-1)**i)>0 for i,q in enumerate(d))and all(abs(q)==abs(d[0])for q in d)and _near(_dot(d,d,budget),F(1),budget),'one fixed alternating normalized power seed')
        den=_dot(d,d,budget);require(den>0 and estimate>=0 and norm>=0 and _near(estimate,_dot(d,op,budget)/den,budget) and _near(norm*norm,_dot(op,op,budget),budget),'finite weighted power dot/norm algebra')
        previous_direction=d;previous=op;previous_norm=norm;zero_power=norm==0
    alpha=mp_fraction(proposal['initial_step'],budget)if 'initial_step'in proposal else None
    if alpha is not None:
        require(estimate is not None and F(1,1<<900)<=alpha<=F(1<<900),'bounded step after weighted power pass')
        expected=min(F(1<<900),max(F(1,1<<900),1/estimate if estimate>0 else F(1<<900)))
        require(_near(alpha,expected,budget),'clamped reciprocal weighted power step')
    accepted=0;model_calls=0;finite_trials=0;stationary=False;terminated=False;max_gap=F(0)
    for index,item in enumerate(iterations):
        require(type(item)is dict and type(item.get('index'))is int and item['index']==index and not terminated and current is not None and normalizers is not None and value is not None and alpha is not None,'ordered initialized balanced iteration')
        require(item.get('reserved_iteration_work')==iteration_work_reserve(license),'full worst balanced iteration reservation')
        before=mp_fraction(item.get('objective_before'),budget);record_r=_vector(item.get('normalized_blocks'),3,budget)
        require(before==value and record_r==r,'continuous max objective and normalized block history')
        rows=item.get('block_gradients');require(type(rows)is list and len(rows)==3,'three complete numerical normalized z gradients');gradients=[_vector(row,n,budget)for row in rows]
        trials=item.get('trials');require(type(trials)is list and len(trials)<=12 and type(item.get('accepted'))is bool,'at most three recomputed model Armijo trials')
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
    counts=_phase_counts(proposal,195000000)
    require(counts['operations']>=native_calls*2*96*15**3,'all recorded repeated native eigensolves charged')
    if status=='proposed':
        require(counts['operations']<=195000000 and counts['peak_live_cells']<=6000000 and current is not None and value is not None and calibration is not None and initial_error is not None,'complete bounded calibrated balanced proposal')
        final=_vector(proposal.get('final_z_mp'),n,budget);require(final==current,'last complete accepted or stationary warm increment')
        free=[budget.add(license.parent_vector[i],budget.mul(D,z))for i,D,z in zip(license.free,license.scales,final)]
        require(proposal.get('final_free_vector')==list(map(str,free)) and mp_fraction(proposal.get('final_objective'),budget)==value and _vector(proposal.get('final_normalized_blocks'),3,budget)==r,'unrounded exact final repaired center+D*z and continuous final max objective')
        stop=proposal.get('stop_reason');require(stop in ('iteration_limit','budget_stop','line_search_failed','numerical_model_stationarity','zero_initial_numerical_defect'),'declared proposal-only stopping reason')
        if stop=='zero_initial_numerical_defect':require(value==0 and not iterations and not power,'observed zero initial defect stops without a model')
        else:
            require(len(power)==8 or zero_power,'complete weighted power estimate before descent')
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




def verify_composed_artifacts(license,chart,center,b):
    payload=encoded(chart);require(len(payload)<=8388608,'bounded composed exact chart');b.charge(len(payload)//64+1)
    expected=dict(schema='primitive-state-augmented-cone-chart-v1',complete=True,width=1224,original_width=1957,normalized_rows=[dict(pivot=p,terms=[[j,str(q)]for j,q in sorted(license.rows[p].items())])for p in license.pivots],pivot_columns=license.pivots,free_indices=license.free,retained_indices=license.retained,old_pivots=sorted(set(license.pivots)-{160,170}),appended_rows=license.appended,affected_free_indices=license.affected,**FLAGS)
    require(chart==expected,'complete independent782-row chart and partition')
    expected=dict(schema='primitive-state-augmented-cone-center-v1',complete=True,free_indices=license.free,initial_free_vector=[str(license.parent_vector[i])for i in license.free],center_projected_vector=list(map(str,license.parent_vector)),candidate_original_vector=list(map(str,license.center_original)),preserved_seed_free_coordinates=True,**FLAGS)
    require(center==expected,'exact independently repaired center preserving442 free entries')
    return dict(verified=True,complete=True,rank=782,free_count=442,old_tape_replayed=False,exact_repair_verified=True,**FLAGS)


def verify_setup(license,receipt,b,*,max_map_bytes=8388608):
    payload=encoded(receipt);require(len(payload)<=max_map_bytes and receipt.get('schema')=='primitive-state-augmented-cone-map-v1'and receipt.get('complete')is True,'complete bounded augmented map');b.charge(len(payload)//64+1)
    require(all(receipt.get(k)is False for k in FLAGS),'complete no-admission map flags')
    for name,value in dict(precision=PRECISION,search=SEARCH,model=MODEL,scaling=SCALING,seed_rule=SEED,width=1224,pivot_columns=license.pivots,free_indices=license.free,center_projected_vector=list(map(str,license.parent_vector)),initial_free_vector=[str(license.parent_vector[i])for i in license.free],normalizers=list(map(str,license.normalizers))).items():require(receipt.get(name)==value,'exact fixed map '+name)
    selective=receipt.get('selective_scaling');require(type(selective)is dict and selective.get('affected_free_indices')==license.affected and selective.get('unchanged_free_indices')==license.unaffected and selective.get('scaling')==SCALING and selective.get('column_norms_independently_verified')is False,'exact98/344 selective partition; no true norm claim')
    require(selective.get('old_scale_records')==[dict(free_index=i,scale=str(license.old_scales[i]))for i in license.free],'inherited scale keyed by surviving coordinate')
    E=license.summary['sparse_map_entries'];n=len(license.free);w=1224
    response=2*E+w+3*(371+450)+240+4096;tail=20*E+240*w+40*n+2*(8388608//64+1)+65536
    reserve=dict(affected_columns=98,sparse_entries=E,per_response_work=response,calibration_and_serialization_work=tail,total_work=98*response+tail)
    require(selective.get('reservation')==reserve and reserve['total_work']<=30000000,'full response/calibration reserve before setup')
    updates=selective.get('updates');require(type(updates)is list and len(updates)==98,'no partial norm setup')
    new={}
    for i,record in zip(license.affected,updates):
        require(record.get('free_index')==i,'ordered actual affected coordinate');g=mp_fraction(record.get('approximate_norm_squared_mp'),b);require(g>=0,'finite exported approximate norm');D=positive_dyadic(record,b);k=record['exponent'];upper=F(1<<2*k)if k>=0 else F(1,1<<(-2*k))
        require(record.get('numerical_zero')is(g==0),'zero is a numerical diagnostic only')
        require((k==0 and D==1)if g==0 else upper/4<g<=upper,'exact positive dyadic rule from reported norm')
        new[i]=D
    license.scales=[new[i]if i in new else license.old_scales[i]for i in license.free];license.setup=receipt
    require(receipt.get('scale_vector')==list(map(str,license.scales)),'all442 positive D and344 unchanged exact scales')
    require(receipt.get('limits')==dict(max_operations=30000000,max_cells=6000000,max_coefficient_bits=4096,max_map_bytes=max_map_bytes),'one30m setup cap');_phase_counts(receipt,30000000)
    calibration=receipt.get('calibration');require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40','complete declared center/homogeneous/adjoint calibration')
    forward=_vector(calibration.get('initial_forward_mp'),1224,b);error=max(abs(q-v)/max(F(1),abs(v))for q,v in zip(forward,license.parent_vector));b.charge(4*1224)
    require(error<=F(1,10**40)and calibration.get('center_exact_reference_relative_error')==str(error),'exact repaired center vs rounded forward calibration')
    direction=_vector(calibration.get('homogeneous_direction_mp'),442,b);require(direction==[F((-1)**i)for i in range(442)],'one fixed homogeneous direction')
    exact=homogeneous(license,[b.mul(D,v)for D,v in zip(license.scales,direction)],b);require(calibration.get('homogeneous_exact_reference')==list(map(str,exact)),'homogeneous cached map excludes every RHS')
    actual=_vector(calibration.get('homogeneous_forward_mp'),1224,b);error=max(abs(q-v)/max(F(1),abs(v))for q,v in zip(actual,exact));require(error<=F(1,10**40)and calibration.get('homogeneous_relative_error')==str(error),'independent exact homogeneous reference drift')
    gradient=_vector(calibration.get('adjoint_test_gradient_mp'),1224,b);require(all(_near(q,F((j%7)-3,7),b)for j,q in enumerate(gradient)),'one fixed adjoint gradient')
    transpose=adjoint(license,gradient,b);reported=_vector(calibration.get('adjoint_test_result_mp'),442,b)
    require(max(abs(q-v)/max(F(1),abs(v))for q,v in zip(reported,transpose))<=F(1,10**40),'reported adjoint agrees with exact triangular transpose within calibration scope')
    left=mp_fraction(calibration.get('adjoint_left'),b);right=mp_fraction(calibration.get('adjoint_right'),b);relative=mp_fraction(calibration.get('adjoint_relative_error'),b)
    require(_near(left,_dot(actual,gradient,b),b)and _near(right,_dot(direction,reported,b),b)and _near(relative,abs(left-right)/max(F(1),abs(left),abs(right)),b)and 0<=relative<=F(1,10**40),'finite forward/adjoint pairing algebra')
    return dict(verified=True,cached_chart_used_without_old_tape_replay=True,exact_center_verified=True,positive_dyadic_scales_verified=True,affected_coordinates=98,unchanged_coordinates=344,selective_norms_independently_recomputed=False,**FLAGS)



def original_system(license,b):
    declaration=dict(complete=True,status='complete',original_columns=1957,projected_columns=1224,rows=5641,retained_indices=license.retained,recipes=[[i,[[j,str(q)]for j,q in sorted(recipe.items())]]for i,recipe in sorted(license.recipes.items())])
    full,_,rhs,_,_=AFFINE.decode_source(license.cache,declaration,b)
    b.live(2*sum(map(len,full))+2*sum(map(len,license.rows.values()))+4*1957+4*1224+6*225)
    return full,rhs


def verify_endpoint(license,proposal,endpoint,full,rhs,b,*,max_endpoint_bytes=2097152):
    require(endpoint.get('schema')=='primitive-state-augmented-cone-endpoint-v1'and endpoint.get('complete')is True,'complete augmented exact endpoint')
    data=encoded(endpoint);require(len(data)<=max_endpoint_bytes,'bounded endpoint');b.charge(len(data)//64+1);require(all(endpoint.get(k)is False for k in FLAGS),'no producer proof admission')
    require(endpoint.get('limits')==dict(max_operations=25000000,max_coefficient_bits=4096,max_endpoint_bytes=max_endpoint_bytes),'one25m exact endpoint phase');_phase_counts(endpoint,25000000)
    z=_vector(proposal['final_z_mp'],len(license.free),b);free=[b.add(license.parent_vector[i],b.mul(D,v))for i,D,v in zip(license.free,license.scales,z)]
    require(endpoint.get('free_indices')==license.free and endpoint.get('final_free_vector')==proposal.get('final_free_vector')==list(map(str,free)),'unrounded exact repaired-center+D*z')
    seed=license.parent_vector[:]
    for i,q in zip(license.free,free):seed[i]=q
    y=AFFINE.backsubstitute(license.rows,seed,b);x=AFFINE.lift(y,license.retained,b)
    require(endpoint.get('final_projected_vector')==list(map(str,y))and endpoint.get('candidate_original_vector')==list(map(str,x)),'exact normalized chart backsub and original1957 lift')
    check=scalar_first_endpoint(full,rhs,license.learned_full,license.learned_rhs,x,b);diag=endpoint.get('diagnostics');require(type(diag)is dict,'complete endpoint diagnostics')
    for key in('full_original_rows_checked','learned_rows_checked','full_equations_checked','negative_scalar_count','PSD_blocks_checked','PSD_failures'):require(diag.get(key)==check[key],'independent endpoint '+key)
    require(diag.get('affine_equalities_satisfied')is True and diag.get('original_equation_mismatches')==[] and diag.get('learned_equation_residuals')==['0']*3 and diag.get('all_cones_satisfied')is check['finite_candidate_feasible'],'all5644 equations and point cone verdict')
    require(diag.get('negative_scalars')==[dict(coordinate=i,value=str(x[i]))for i in range(1597)if x[i]<0],'all1597 scalar signs')
    if check['negative_scalar_count']:
        require(diag.get('psd_status')=='NOT_CHECKED_AFTER_SCALAR_REJECTION'and diag.get('psd_blocks')==[],'PSD explicitly skipped after exact scalar rejection')
    else:
        reports=diag.get('psd_blocks');require(diag.get('psd_status')in('CHECKED','ALL_THREE_EXACT_BLOCKS_CHECKED')and type(reports)is list and len(reports)==3,'all three exact PSD reports required')
        for k,(report,computed)in enumerate(zip(reports,check['psd_blocks'])):
            require(report.get('name')==computed['name'],'original block identity');matrix=[[F(0)]*15 for _ in range(15)];position=1597+120*k
            for i in range(15):
                for j in range(i,15):matrix[i][j]=matrix[j][i]=x[position];position+=1
            AFFINE.check_psd_report(matrix,report,computed,b)
    return dict(verified=True,complete=True,endpoint_verified=True,**check,**FLAGS)


def verify_search(cache,chart024,center024,old_constraint,review024,extension,constraints,review027,report027,seed026,recovery026,map026,chart,center,mapreceipt,proposal=None,endpoint=None,*,deadline=None,max_operations=150000000,max_cells=6000000,max_coefficient_bits=4096):
    require(type(max_operations)is int and 0<max_operations<=150000000,'one shared150m final audit')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,20000000,max_coefficient_bits)
    try:
        license=augmented_license(cache,chart024,center024,old_constraint,review024,extension,constraints,review027,report027,seed026,recovery026,map026,b)
        center_check=verify_composed_artifacts(license,chart,center,b);setup=verify_setup(license,mapreceipt,b)
        full,rhs=original_system(license,b);initial=scalar_first_endpoint(full,rhs,license.learned_full,license.learned_rhs,license.center_original,b)
        center_check.update(candidate_equations_verified=True,endpoint_check=initial)
        trace=verify_proposal_trace(license,proposal,b)if proposal is not None else None
        require(endpoint is None or trace is not None and trace['complete'],'complete proposal before exact endpoint')
        exact=verify_endpoint(license,proposal,endpoint,full,rhs,b)if endpoint is not None else None
        result=dict(verified=True,complete=bool(exact),chart_verified=True,center_verified=True,endpoint_verified=bool(exact),candidate_equations_verified=bool(exact),finite_candidate_feasible=exact['finite_candidate_feasible']if exact else None,setup_check=setup,center_check=center_check,trace_check=trace,endpoint_check=exact,chart_used_without_old_tape_replay=True,**FLAGS)
        for key in('accepted_iterations','stop_reason','initial_objective','final_objective','initial_block_penalties','final_block_penalties'):result[key]=trace.get(key)if trace else None
        payload=encoded(result)
        if len(payload)>8388608:raise OverflowError('bounded8MiB independent summary')
        b.charge(2*(len(payload)//64+1))
        result.update(audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        return result
    except (OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
