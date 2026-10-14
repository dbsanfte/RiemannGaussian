"""Independent cached-chart proposal consistency and exact centered endpoints.

The old span proof is reused directly from publication024. No elimination tape,
source polynomial, cryptographic binding or numerical gradient proof is replayed.
"""
from fractions import Fraction as F
import json
import time
import math
import check_primitive_state_feedback_affine as AFFINE
import check_primitive_state_balanced_cone_search as BALANCED

require=AFFINE.require
Budget=AFFINE.Budget
mp_fraction=BALANCED.mp_fraction
_near=BALANCED._near
_vector=BALANCED._vector
_dot=BALANCED._dot
_block_metrics=BALANCED._block_metrics
verify_simplex_model=BALANCED.verify_simplex_model
MODEL=BALANCED.MODEL


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def false_flags(value):
    require(type(value)is dict,'explicit numerical scope')
    for k in FLAGS:
        if k in value:require(value[k]is False,'no numerical/cone/global admission '+k)

class _License:
    pass


def validate_chart(cache,chart,center,necessary,parent_review,b):
    require(parent_review.get('schema')=='primitive-state-feedback-affine-independent-review-v1'and parent_review.get('all_passed')is True and parent_review.get('status')=='AFFINE_UPDATED'and parent_review.get('chart_verified')is True and parent_review.get('candidate_equations_verified')is True,'actual completed publication024 chart/seed license')
    check=parent_review.get('independent_affine_check');require(type(check)is dict and check.get('verified')is True and check.get('complete')is True and check.get('all_original_rows_replayed')is True and check.get('projection_dependencies_verified')is True and check.get('feedback_reduction_verified')is True and check.get('normalized_chart_verified')is True and check.get('new_rank')==780 and check.get('new_free_count')==444,'complete prior span and appended-row proof used without tape replay')
    require(center.get('schema')=='primitive-state-feedback-affine-v1'and center.get('complete')is True and center.get('status')=='complete'and center.get('classification')=='independent'and center.get('chart_available')is True,'actual exact repaired publication024 center')
    require(chart.get('schema')=='primitive-state-feedback-affine-chart-v1'and chart.get('width')==1224 and chart.get('original_width')==1957 and chart.get('old_rank')==779 and chart.get('new_rank')==780 and chart.get('classification')=='independent','saved780-pivot chart')
    original=cache['original'];retained,recipes=AFFINE.projection_layout(original)
    require(chart.get('retained_indices')==retained,'original quotient coordinate mapping')
    old={};source_rows=set();oldrecords=chart.get('normalized_rows');require(type(oldrecords)is list and len(oldrecords)==779,'all779 licensed old normalized rows')
    previous=-1
    for item in oldrecords:
        p=item['pivot'];require(type(p)is int and previous<p<1224 and type(item.get('source_row'))is int and 0<=item['source_row']<5641 and item['source_row']not in source_rows,'ordered licensed source pivot rows');previous=p;source_rows.add(item['source_row']);row={};last=-1
        for j,text in item['terms']:
            require(type(j)is int and last<j<=1224,'ordered complete augmented chart terms');last=j;q=b.rational(text);require(q!=0,'nonzero sparse chart coefficient');row[j]=q
        require(row.get(p)==1 and min(row)==p,'upper triangular normalized old row');old[p]=row
    require(chart.get('old_pivots')==sorted(old),'all old pivot indices')
    oldfree=[i for i in range(1224)if i not in old];require(chart.get('old_free_indices')==oldfree and len(oldfree)==445,'old445-coordinate partition')
    fullfeedback,projected,newrhs=AFFINE.decode_feedback(necessary,retained,recipes,b)
    classification,new,reduction=AFFINE.reduce_feedback(projected,newrhs,old,b);require(classification=='independent'and new is not None,'learned row is independent in saved chart')
    p=reduction['chosen_pivot'];require(p==148 and center.get('reduction')==reduction,'fixed learned pivot148 and actual reduction')
    appended=dict(pivot=p,source_row='feedback',terms=[[j,str(q)]for j,q in sorted(new.items())]);require(chart.get('appended_row')==appended,'missing/changed learned row is rejected')
    allrows=dict(old);allrows[p]=new;pivots=sorted(allrows);free=[i for i in range(1224)if i not in allrows]
    require(chart.get('pivot_columns')==pivots and chart.get('free_indices')==free and len(pivots)==780 and len(free)==444,'complete final cached pivot/free partition')
    y=[b.rational(q)for q in center.get('candidate_projected_vector',[])];require(len(y)==1224 and AFFINE.backsubstitute(allrows,y,b)==y,'exact center satisfies cached780 equations')
    x=[b.rational(q)for q in center.get('candidate_original_vector',[])];require(len(x)==1957 and AFFINE.lift(y,retained,b)==x,'exact center original canonical lift and offsets')
    require(center.get('preserved_free_indices')==free,'saved repair preserved all other444 free coordinates')
    license=_License();license.rows=allrows;license.old_rows=old;license.new_row=new;license.parent_vector=y;license.center_original=x;license.free=free;license.pivots=pivots;license.retained=retained;license.recipes=recipes;license.cache=cache;license.chart=chart;license.center=center;license.necessary=necessary;license.feedback_full=fullfeedback;license.feedback_rhs=newrhs
    license.source=dict(shape=[366,613],offset=1597);license.summary=dict(sparse_map_entries=sum(map(len,allrows.values())),rank=780,free_count=444,learned_pivot=148,old_tape_replayed=False,prior_span_license_used=True);license.initial_z=[F(0)]*444
    license.affected=[i for i in free if new.get(i)];license.unaffected=[i for i in free if i not in license.affected]
    require(len(license.affected)==81 and len(license.unaffected)==363,'fixed81 affected and363 unchanged homogeneous columns')
    b.live(sum(map(len,allrows.values()))+1224+1957)
    return license


def homogeneous(license,free_direction,b):
    require(len(free_direction)==len(license.free),'complete homogeneous free direction');seed=[F(0)]*1224
    for i,q in zip(license.free,free_direction):seed[i]=q
    rows={p:{j:q for j,q in row.items()if j!=1224}for p,row in license.rows.items()}
    return AFFINE.backsubstitute(rows,seed,b)


def adjoint(license,gradient,b):
    require(len(gradient)==1224,'full finite adjoint gradient');work=gradient[:]
    for p in sorted(license.rows):
        row=license.rows[p];value=work[p]
        for j,q in row.items():
            if j not in(p,1224):work[j]=b.add(work[j],-b.mul(value,q))
        work[p]=F(0)
    return [b.mul(D,work[i])for i,D in zip(license.free,license.scales)]

SCHEMA='primitive-state-feedback-cone-search-v1'
FLAGS=dict(AFFINE.FLAGS,model_optimality_certified=False,block_gradients_certified=False,column_norms_independently_verified=False,new_map_preconditioner_certified=False)
PRECISION=dict(decimal_digits=80,binary_bits=269,actual_map_relative_tolerance='1e-40',serialized_binary_exponent_abs_cap=4096,mixed_precision=True,PSD_eigh='binary64',PSD_negative_parts='binary64',calibration_scope='affine center, one homogeneous direction and adjoint only',center_mp_is_approximation=True,endpoint_center_is_exact=True)
SEARCH=dict(BALANCED.SEARCH,gradient_iterations=128,positive_dyadic_cone_jacobi=False,cached_positive_dyadic_scales=True,accepted_step_carry='next start=min(2^900,2*accepted trial alpha); initial power step unchanged')
SCALING=dict(rule='retain old D on unaffected free columns; recompute approximate80digit cone norm on exact appended-row affected support',dropped_projected_free_index=148,exponent_abs_cap=900,new_column_responses=81,unchanged_column_scales=363,norms_verified=False,new_map_norm_preconditioner=False,cone_norm='all366 square and5 slack squares plus full C and H Frobenius squared norms',dyadic_rule='smallest integer k with exported approximate norm_squared <= 2^(2*k); D=2^(-k); zero=>1',precision='80 decimal digits; no exact or independently certified norm claim',partial_scaling_allowed=False)
SEED='exact publication024 projected endpoint; z0=0; exact center never rerounded for endpoint'


def _phase_counts(receipt,cap):
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','maximum_rational_bits'},'complete phase diagnostic counters')
    for k,bound in [('operations',cap),('peak_live_cells',6000000),('maximum_rational_bits',4096)]:require(type(counts[k])is int and 0<=counts[k]<=bound,'bounded phase counter '+k)
    return counts


def positive_dyadic(record,b):
    k=record.get('exponent');require(type(k)is int and abs(k)<=900,'bounded dyadic exponent')
    D=b.rational(record.get('scale'));require(D==(F(1,1<<k)if k>=0 else F(1<<(-k)))and D>0,'strict positive exact dyadic scale')
    return D


def verify_setup(license,norms,receipt,b,*,max_map_bytes=8388608):
    payload=encoded(receipt);require(len(payload)<=max_map_bytes and receipt.get('schema')=='primitive-state-feedback-cone-map-v1'and receipt.get('complete')is True,'complete bounded cached map receipt');b.charge(len(payload)//64+1)
    false_flags(receipt)
    require(all(receipt.get(k)is False for k in FLAGS),'complete map scope flags')
    require(receipt.get('precision')==PRECISION and receipt.get('search')==SEARCH and receipt.get('model')==MODEL and receipt.get('scaling')==SCALING and receipt.get('seed_rule')==SEED,'fixed centered mixed-precision numerical policy')
    require(receipt.get('width')==1224 and receipt.get('pivot_columns')==license.pivots and receipt.get('free_indices')==license.free and receipt.get('center_projected_vector')==list(map(str,license.parent_vector))and receipt.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free],'exact cached center/pivot/free binding')
    require(norms.get('complete')is True and norms.get('status')=='scaled'and type(norms.get('records'))is list and len(norms['records'])==445,'complete actual prior020 scale records')
    old={}
    for index,record in enumerate(norms['records']):
        i=record.get('free_index');require(type(i)is int and 0<=i<1224 and i not in old and type(record.get('index'))is int and record['index']==index,'unique ordered old coordinate norm declarations');positive_dyadic(record,b);old[i]=record
    require(set(old)==set(license.free)|{148},'old scale coordinate coverage and dropped148')
    selective=receipt.get('selective_scaling');require(type(selective)is dict and selective.get('affected_free_indices')==license.affected and selective.get('unchanged_free_indices')==license.unaffected and selective.get('scaling')==SCALING and selective.get('column_norms_independently_verified')is False,'exact81/363 selective support and no norm proof')
    require(selective.get('old_scale_records')==[old[i]for i in license.free],'unchanged actual prior records keyed by projected coordinate')
    E=license.summary['sparse_map_entries'];response=2*E+1224+3*(371+450)+240+4096;tail=20*E+240*1224+40*444+2*(8388608//64+1)+65536
    reserve=dict(affected_columns=81,sparse_entries=E,per_response_work=response,calibration_and_serialization_work=tail,total_work=81*response+tail)
    require(selective.get('reservation')==reserve and reserve['total_work']<=25000000,'whole81-response/calibration work reserved before selective phase')
    updates=selective.get('updates');require(type(updates)is list and len(updates)==81,'no partial selective scaling')
    new={}
    for i,record in zip(license.affected,updates):
        require(record.get('free_index')==i,'affected updates in exact source order');g=mp_fraction(record.get('approximate_norm_squared_mp'),b);require(g>=0,'finite nonnegative exported approximate norm')
        D=positive_dyadic(record,b);k=record['exponent'];upper=F(1<<2*k)if k>=0 else F(1,1<<(-2*k))
        require(record.get('numerical_zero')is(g==0),'zero is only a numerical preconditioner diagnostic')
        if g==0:require(k==0 and D==1,'observed zero response uses positive scale one')
        else:require(upper/4<g<=upper,'least integer exact dyadic rounding from exported approximate norm')
        new[i]=D
    scales=[new[i]if i in new else positive_dyadic(old[i],b)for i in license.free];require(receipt.get('scale_vector')==list(map(str,scales)),'all444 final positive scales and unchanged363 exact D')
    license.scales=scales;license.warm_vector=license.parent_vector;license.setup=receipt
    limits=receipt.get('limits');require(type(limits)is dict and limits==dict(max_operations=25000000,max_cells=6000000,max_coefficient_bits=4096,max_map_bytes=max_map_bytes),'one bounded25m map phase')
    _phase_counts(receipt,25000000)
    calibration=receipt.get('calibration');require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40','complete declared center/homogeneous/adjoint calibration')
    forward=_vector(calibration.get('initial_forward_mp'),1224,b);error=max(abs(q-v)/max(F(1),abs(v))for q,v in zip(forward,license.parent_vector));b.charge(4*1224)
    require(error<=F(1,10**40)and calibration.get('center_exact_reference_relative_error')==str(error),'exact024 center vs rounded forward calibration')
    direction=_vector(calibration.get('homogeneous_direction_mp'),444,b);require(direction==[F((-1)**i)for i in range(444)],'one fixed homogeneous direction')
    exact=homogeneous(license,[b.mul(D,v)for D,v in zip(scales,direction)],b);require(calibration.get('homogeneous_exact_reference')==list(map(str,exact)),'homogeneous cached map excludes every RHS')
    actual=_vector(calibration.get('homogeneous_forward_mp'),1224,b);error=max(abs(q-v)/max(F(1),abs(v))for q,v in zip(actual,exact));require(error<=F(1,10**40)and calibration.get('homogeneous_relative_error')==str(error),'independent exact homogeneous reference drift')
    gradient=_vector(calibration.get('adjoint_test_gradient_mp'),1224,b);require(all(_near(q,F((j%7)-3,7),b)for j,q in enumerate(gradient)),'one fixed adjoint gradient')
    transpose=adjoint(license,gradient,b);reported=_vector(calibration.get('adjoint_test_result_mp'),444,b)
    require(max(abs(q-v)/max(F(1),abs(v))for q,v in zip(reported,transpose))<=F(1,10**40),'reported adjoint agrees with exact triangular transpose within calibration scope')
    left=mp_fraction(calibration.get('adjoint_left'),b);right=mp_fraction(calibration.get('adjoint_right'),b);relative=mp_fraction(calibration.get('adjoint_relative_error'),b)
    require(_near(left,_dot(actual,gradient,b),b)and _near(right,_dot(direction,reported,b),b)and _near(relative,abs(left-right)/max(F(1),abs(left),abs(right)),b)and 0<=relative<=F(1,10**40),'finite forward/adjoint pairing algebra')
    return dict(verified=True,cached_chart_used_without_old_tape_replay=True,exact_center_verified=True,positive_dyadic_scales_verified=True,affected_coordinates=81,unchanged_coordinates=363,selective_norms_independently_recomputed=False,**FLAGS)


def iteration_work_reserve(license):
    E=license.summary['sparse_map_entries'];w=len(license.parent_vector);n=len(license.free);p=len(license.pivots)
    shape=license.source['shape'];sc=license.source['offset']-2*shape[1];pairs=120
    forward=4*E+2*p+w+2*n
    metrics=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)+6*w
    adjoints=3*(2*E+w+n);model=200*n+8192
    return 3*(forward+metrics+model+4*n+16384)+adjoints+4096*n+131072+6*w


def _verify_budget_stop(license,proposal,budget,max_trace_bytes):
    stop=proposal.get('budget_stop');require(type(stop)is dict,'explicit complete last-point balanced budget stop')
    keys=('before_iteration','operations','max_operations','remaining_operations','worst_iteration_work_reserve','finalization_work_reserve','trace_retained_bytes','max_trace_bytes','worst_iteration_trace_bytes','finalization_trace_bytes')
    require(set(stop)==set(keys)|{'resource'} and all(type(stop[k])is int and stop[k]>=0 for k in keys),'strict finite budget stop counters')
    n=len(license.free);work=iteration_work_reserve(license);tail=max_trace_bytes+20000*n+131072;perstep=65536+12*96*n;final=8192+3000*n
    require(stop['before_iteration']==len(proposal['iterations'])<128 and stop['max_operations']==200000000 and stop['operations']<=proposal['counts']['operations']<=200000000 and stop['remaining_operations']==200000000-stop['operations'],'budget stop before next full iteration')
    require(stop['worst_iteration_work_reserve']==work and stop['finalization_work_reserve']==tail and stop['max_trace_bytes']==max_trace_bytes and stop['worst_iteration_trace_bytes']==perstep and stop['finalization_trace_bytes']==final,'independently reconstructed fixed step/export reserves')
    keys=('schema','status','complete','precision','search','model','scaling','seed_rule','free_indices','initial_free_vector','scale_vector','calibration','initial_z_mp','initial_block_penalties','normalizers','initial_normalized_blocks','initial_objective','initial_merit_details','power_trace','initial_step')
    initial={k:proposal[k]for k in keys};initial.update(status='unknown',complete=False,iterations=[],final_free_vector=None,**FLAGS)
    retained=len(encoded(initial))+sum(len(encoded(item))+1 for item in proposal['iterations']);budget.charge(retained//64+len(proposal['iterations'])+1)
    require(stop['trace_retained_bytes']==retained,'exact retained complete-prefix serialization proxy')
    op_short=stop['remaining_operations']<work+tail;byte_short=max_trace_bytes-retained<perstep+final
    require(stop['resource']=='operations' and op_short or stop['resource']=='trace_bytes' and not op_short and byte_short,'actual bounded-work or byte shortfall stops before new model')


def verify_proposal_trace(license,proposal,budget,*,max_trace_bytes=16777216):
    require(type(proposal)is dict and proposal.get('schema')==SCHEMA,'known balanced finite numerical proposal');payload=encoded(proposal);require(len(payload)<=max_trace_bytes,'bounded entire balanced history');budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    for k in FLAGS:require(proposal.get(k)is False,'no balanced gradient/model/cone/global theorem claim')
    require(proposal.get('precision')==PRECISION and proposal.get('search')==SEARCH and proposal.get('model')==MODEL and proposal.get('scaling')==SCALING and proposal.get('seed_rule')==SEED,'fixed balanced mixed-precision numerical policy')
    require(proposal.get('free_indices')==license.free and proposal.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free] and proposal.get('scale_vector')==list(map(str,license.scales)),'exact024 center and selective positive scales')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict balanced proposal completion')
    n=len(license.free);current=None;initial_error=None
    if 'initial_z_mp'in proposal:
        current=_vector(proposal['initial_z_mp'],n,budget);require(current==license.initial_z,'same exact269-bit centered publication024 zero increment; no center reround')
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
        require(normalizers==[max(q,F(1,1<<40))for q in penalties],'normalizers exactly max(initial finite exported penalty,2^-40)')
        r=_vector(proposal.get('initial_normalized_blocks'),3,budget);require(all(q>=0 and _near(q,e,budget)for q,e in zip(r,expected)),'normalized initial block ratios')
        value=mp_fraction(proposal.get('initial_objective'),budget);require(value==max(r) and value>=0,'max of three normalized initial blocks');native_calls=1
    previous=None;previous_norm=None;zero_power=False;estimate=None
    for index,item in enumerate(power):
        require(normalizers is not None and type(item)is dict and type(item.get('index'))is int and item['index']==index and not zero_power,'ordered initialized weighted power pass')
        d=_vector(item.get('vector'),n,budget);op=_vector(item.get('operator'),n,budget);estimate=mp_fraction(item.get('estimate'),budget);norm=mp_fraction(item.get('operator_norm'),budget)
        if previous is not None:require(all(_near(q,v/previous_norm,budget)for q,v in zip(d,previous)),'normalized fixed weighted power continuation')
        else:require(all(q*((-1)**i)>0 for i,q in enumerate(d)) and all(abs(q)==abs(d[0])for q in d),'one fixed alternating power seed')
        den=_dot(d,d,budget);require(den>0 and estimate>=0 and norm>=0 and _near(estimate,_dot(d,op,budget)/den,budget) and _near(norm*norm,_dot(op,op,budget),budget),'finite weighted power dot/norm algebra')
        previous=op;previous_norm=norm;zero_power=norm==0
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
        trials=item.get('trials');require(type(trials)is list and len(trials)<=3 and type(item.get('accepted'))is bool,'at most three recomputed model Armijo trials')
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
            if status=='proposed' or index<len(iterations)-1:require(len(trials)==3,'failed line search exhausts all three models')
            terminated=True
    if 'last_finite_z_mp'in proposal:require(current is not None and _vector(proposal['last_finite_z_mp'],n,budget)==current,'retained UNKNOWN warm increment is last complete point')
    counts=_phase_counts(proposal,200000000)
    require(counts['operations']>=native_calls*2*96*15**3,'all recorded repeated native eigensolves charged')
    if status=='proposed':
        require(counts['operations']<=200000000 and counts['peak_live_cells']<=6000000 and current is not None and value is not None and calibration is not None and initial_error is not None,'complete bounded calibrated balanced proposal')
        final=_vector(proposal.get('final_z_mp'),n,budget);require(final==current,'last complete accepted or stationary warm increment')
        free=[budget.add(license.parent_vector[i],budget.mul(D,z))for i,D,z in zip(license.free,license.scales,final)]
        require(proposal.get('final_free_vector')==list(map(str,free)) and mp_fraction(proposal.get('final_objective'),budget)==value and _vector(proposal.get('final_normalized_blocks'),3,budget)==r,'unrounded exact final f024+D*z and continuous final max objective')
        stop=proposal.get('stop_reason');require(stop in ('iteration_limit','budget_stop','line_search_failed','numerical_model_stationarity','zero_initial_numerical_defect'),'declared proposal-only stopping reason')
        if stop=='zero_initial_numerical_defect':require(value==0 and not iterations and not power,'observed zero initial defect stops without a model')
        else:
            require(len(power)==8 or zero_power,'complete weighted power estimate before descent')
            if stop=='iteration_limit':require(len(iterations)==128 and iterations[-1]['accepted']is True,'fixed128iteration endpoint')
            elif stop=='budget_stop':_verify_budget_stop(license,proposal,budget,max_trace_bytes)
            elif stop=='numerical_model_stationarity':require(stationary,'actual numerical zero-direction model stop')
            else:require(iterations and not iterations[-1]['accepted'] and len(iterations[-1]['trials'])==3 and not stationary,'actual exhausted three-trial balanced line search')
    else:require(type(proposal.get('reason'))is str and bool(proposal['reason']),'explicit incomplete numerical proposal cause')
    last_penalties=proposal.get('initial_block_penalties')
    for item in iterations:
        for trial in item['trials']:
            if trial.get('armijo_passed')is True:last_penalties=trial['block_penalties']
    return dict(final_block_penalties=last_penalties,verified=True,complete=status=='proposed',proposal_history_only=True,gradient_or_merit_certified=False,intermediate_iterates_exact=False,block_normalizers_verified_from_exported_penalties=normalizers is not None,actual_initial_exact_reference_relative_error=str(initial_error)if initial_error is not None else None,power_iterations=len(power),gradient_iterations=len(iterations),accepted_iterations=accepted,finite_armijo_trials=finite_trials,native_eigensolve_calls=2*native_calls,simplex_models_checked=model_calls,stop_reason=proposal.get('stop_reason'),initial_objective=proposal.get('initial_objective'),final_objective=proposal.get('final_objective'),initial_block_penalties=proposal.get('initial_block_penalties'),final_normalized_blocks=proposal.get('final_normalized_blocks'),maximum_recorded_model_gap=str(max_gap),native_PSD_projection_precision='binary64',affine_map_precision_decimal_digits=80,audit_operations=budget.operations,audit_cells=budget.audit_cells,independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)



def verify_endpoint(license,proposal,endpoint,b,*,max_endpoint_bytes=2097152):
    require(type(endpoint)is dict and endpoint.get('schema')=='primitive-state-feedback-cone-endpoint-v1','known exact cached endpoint');payload=encoded(endpoint);require(len(payload)<=max_endpoint_bytes,'bounded full exact endpoint');b.charge(len(payload)//64+1)
    false_flags(endpoint);require(all(endpoint.get(k)is False for k in FLAGS),'complete endpoint scope flags');_phase_counts(endpoint,25000000)
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


def verify_search(cache,chart,center,necessary,norms,parent_review,mapreceipt,proposal=None,endpoint=None,*,deadline=None,max_operations=150000000,max_cells=6000000,max_coefficient_bits=4096,max_map_bytes=8388608,max_trace_bytes=16777216,max_endpoint_bytes=2097152):
    """Check designated published024 cached inputs; their span is a prior premise.

    Arbitrary caller-supplied parent booleans are not a fresh all-row span proof.
    The archive wrapper loads the designated immutable published artifacts.
    """
    require(type(max_operations)is int and 0<max_operations<=150000000,'joint final150m arithmetic reservation')
    for value,cap in ((max_map_bytes,8388608),(max_trace_bytes,16777216),(max_endpoint_bytes,2097152)):require(type(value)is int and 0<value<=cap,'bounded mathematical artifact')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,20000000,max_coefficient_bits)
    license=validate_chart(cache,chart,center,necessary,parent_review,b);setup=verify_setup(license,norms,mapreceipt,b,max_map_bytes=max_map_bytes)
    trace=verify_proposal_trace(license,proposal,b,max_trace_bytes=max_trace_bytes)if proposal is not None else None
    require(endpoint is None or proposal is not None,'endpoint has an explicit proposal')
    exact=verify_endpoint(license,proposal,endpoint,b,max_endpoint_bytes=max_endpoint_bytes)if endpoint is not None else None
    return dict(verified=True,complete=bool(exact and exact['complete']),setup_check=setup,trace_check=trace,endpoint_check=exact,endpoint_verified=bool(exact and exact['endpoint_verified']),candidate_equations_verified=bool(exact and exact['candidate_equations_verified']),finite_candidate_feasible=exact['finite_candidate_feasible']if exact else None,full_original_rows_checked=exact.get('full_original_rows_checked',0)if exact else 0,feedback_row_verified=bool(exact and exact.get('feedback_row_verified')),chart_used_without_old_tape_replay=True,trace_exports_checked=trace is not None,accepted_iterations=trace.get('accepted_iterations',0)if trace else 0,stop_reason=trace.get('stop_reason')if trace else None,initial_block_penalties=trace.get('initial_block_penalties')if trace else None,final_block_penalties=trace.get('final_block_penalties')if trace else None,initial_objective=trace.get('initial_objective')if trace else None,final_objective=trace.get('final_objective')if trace else None,audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations,**FLAGS)
