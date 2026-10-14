"""Independent positive-coordinate scaling, proposal trace and exact endpoint checks.

Column norms and numerical gradients are NOT independently recomputed. A positive
scale changes coordinates only; exact original-coordinate endpoint tests decide
finite feasibility. The licensed chart is never inferred from numerical samples.
"""
from fractions import Fraction as F
from pathlib import Path
import check_primitive_state_free_cone_search as OLD

EXACT=OLD.EXACT
require=OLD.require
encoded=OLD.encoded
digest=OLD.digest
FLAGS=dict(OLD.FLAGS,column_norms_independently_verified=False,scaled_trace_bound_certified=False)
CACHE=OLD.CACHE;BASIS=OLD.BASIS;PROJECTION=OLD.PROJECTION
CHART_PARENT=OLD.PARENT
PARENT='cancellation-arithmetic-results/primitive-state-free-cone-search-001'
MANIFEST='cancellation-arithmetic-results/publication-018/manifest.json'
REPORT='cancellation-arithmetic-results/publication-018/report.json'
_TOKEN=object()

SCHEMA='primitive-state-cone-jacobi-search-v1'
PRECISION=dict(OLD.PRECISION,centered_coordinate_updates=True,final_free_exact_sum_not_269bit_rerounded=True)
SEARCH=dict(OLD.SEARCH,gradient_iterations=64,identity_free_coordinate_scaling=False,positive_dyadic_cone_jacobi=True,iteration_budget_policy='reserve three full trials plus one accepted adjoint before iteration')
SCALING=dict(response_bits=4096,norm_bits=8192,exponent_abs_cap=900,temporary_bits=16385,zero_norm_scale='1',nonzero_rule='2^(2*(k-1)) < g <= 2^(2*k); D=2^(-k)',homogeneous_rhs=True,scalar_coordinates='all squares and five slacks',matrix_coordinates='C and P+4C',offdiagonal_frobenius_factor=2,producer_exact_rational=True,independently_verified=False)
SEED='publication018 complete exact endpoint free coordinates; centered f=f0+D*z; z=0; one seed; no clipping'


class _EndpointLicense:
    def __init__(self,token,old,summary,parent_vector,bindings,parent_endpoint):
        require(token is _TOKEN,'license issued only by immutable evidence validation')
        self.old=old;self.source=old.source;self.summary=summary
        self.parent_vector=parent_vector;self.bindings=bindings
        self.pivots=old.pivots;self.free=old.free
        self.cache=old.cache;self.basis=old.basis;self.projection=old.projection
        self.parent_restoration=old.parent_restoration;self.parent_endpoint=parent_endpoint
        self.endpoint_license=OLD._EndpointLicense(OLD._TOKEN,self.source,summary,parent_vector,self.pivots,self.free,bindings)


def load_verified_license(root,expected_file_bindings,*,deadline=None,max_operations=50000000,max_cells=60000000,max_coefficient_bits=4096):
    root=Path(root).resolve()
    old=OLD.load_verified_license(root,expected_file_bindings,deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    budget=EXACT.EXACT._Budget(deadline,max_operations-old.summary['audit_operations'],max_cells-old.summary['audit_cells'],max_coefficient_bits)
    needed={MANIFEST,REPORT,PARENT+'/independent_verification.json',PARENT+'/receipt.json',PARENT+'/jobs/endpoint.json',PARENT+'/jobs/map.json',PARENT+'/jobs/check.json',PARENT+'/jobs/search-job.json'}
    require(needed<=set(expected_file_bindings),'complete immutable publication018 exact seed bindings')
    manifest=OLD._read(root,MANIFEST,budget);files=manifest.get('files');require(type(files)is dict,'complete seed publication manifest')
    for name in needed-{MANIFEST}:require(files.get(name)==expected_file_bindings[name],'published seed binding '+name)
    require(files.get(OLD.MANIFEST)==expected_file_bindings[OLD.MANIFEST],'same immutable publication017 chart ancestry')
    report=OLD._read(root,REPORT,budget);review=OLD._read(root,PARENT+'/independent_verification.json',budget)
    receipt=OLD._read(root,PARENT+'/receipt.json',budget,65536)
    endpoint=OLD._read(root,PARENT+'/jobs/endpoint.json',budget)
    check=OLD._read(root,PARENT+'/jobs/check.json',budget)
    job=OLD._read(root,PARENT+'/jobs/search-job.json',budget,65536)
    parent_map=OLD._read(root,PARENT+'/jobs/map.json',budget,65536)
    require(parent_map.get('normalized_basis_hash')==old.summary['normalized_basis_hash'] and parent_map.get('free_indices')==old.free and type(parent_map.get('sparse_map_entries'))is int and 0<parent_map['sparse_map_entries']<=4000000,'licensed sparse-map work proxy')
    require(report.get('schema')==18 and report.get('endpoint_available')is True and review.get('all_passed')is True,'completed publication018 endpoint evidence')
    require(report.get('independent_receipt_sha256')==expected_file_bindings[PARENT+'/independent_verification.json'] and report.get('terminal_receipt_sha256')==expected_file_bindings[PARENT+'/receipt.json'],'published independent and terminal seed bindings')
    require(review.get('schema')=='primitive-state-free-cone-search-independent-review-v1' and review.get('search_check')==check and check.get('complete')is True and check.get('endpoint_verified')is True,'independently completed exact seed endpoint')
    require(job.get('endpoint_verified')is True and review.get('job',{}).get('endpoint_verified')is True,'completed seed transport and resource contract')
    require(endpoint.get('complete')is True and endpoint.get('normalized_basis_hash')==old.summary['normalized_basis_hash'] and endpoint.get('free_indices')==old.free,'seed exact chart and free partition')
    require(check.get('endpoint_check',{}).get('candidate_hash')==endpoint.get('candidate_hash')==report.get('candidate_hash') and endpoint.get('candidate_hash')==digest(endpoint.get('candidate_original_vector')),'published explicit seed candidate hash')
    require(check['endpoint_check'].get('exact_candidate_checks',{}).get('equality_complete')is True and check['endpoint_check']['exact_candidate_checks'].get('equality_mismatch_count')==0,'seed exact original affine identity verified')
    for name in ('endpoint','map','check','search-job'):require(receipt.get('files_sha256',{}).get('jobs/'+name+'.json')==expected_file_bindings[PARENT+'/jobs/'+name+'.json'],'seed terminal file inventory '+name)
    stems={'protocol','source_seal','input','seal','tests','execution','receipt'}
    require(set(review.get('input_sha256',{}))==stems,'complete seed review stem bindings')
    for stem,h in review['input_sha256'].items():require(OLD._sha(root,PARENT+'/'+stem+'.json',budget)==h,'seed review input '+stem)
    texts=endpoint.get('final_projected_vector');require(type(texts)is list and len(texts)==old.summary['projected_variables'],'complete exact publication018 projected seed')
    vector=[EXACT.rational(q,budget) for q in texts]
    require(endpoint.get('final_free_vector')==[str(vector[i]) for i in old.free],'seed free and projected coordinates agree')
    summary=dict(old.summary,publication='publication-018',manifest_sha256=expected_file_bindings[MANIFEST],parent_candidate_hash=endpoint['candidate_hash'],parent_projected_hash=digest(texts),parent_free_hash=digest(endpoint['final_free_vector']),sparse_map_entries=parent_map['sparse_map_entries'],seed_endpoint_sha256=expected_file_bindings[PARENT+'/jobs/endpoint.json'],seed_review_sha256=expected_file_bindings[PARENT+'/independent_verification.json'],audit_operations=old.summary['audit_operations']+budget.operations,audit_cells=old.summary['audit_cells']+budget.cells)
    return _EndpointLicense(_TOKEN,old,summary,vector,dict(expected_file_bindings),endpoint)


mp_fraction=OLD.mp_fraction
_near=OLD._near
def verify_proposal_trace(license,normreceipt,proposal,*,deadline=None,max_operations=50000000,max_cells=60000000,
                          max_coefficient_bits=4096,max_trace_bytes=8388608):
    """Check finite exports/order/rounding diagnostics, never gradient correctness."""
    require(type(license)is _EndpointLicense,'hash-issued published chart required')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(proposal)is dict and proposal.get('schema')==SCHEMA,'known finite proposal trace');data=encoded(proposal)
    require(len(data)<=max_trace_bytes,'bounded entire proposal history');budget.charge(len(data)//64+1,cells=len(data)//64+1)
    require(proposal.get('precision')==PRECISION and proposal.get('search')==SEARCH and proposal.get('seed_rule')==SEED,'fixed80digit proposal protocol')
    require(proposal.get('normalized_basis_hash')==license.summary['normalized_basis_hash'],'proposal chart matches published normalized hash')
    require(proposal.get('norm_records_hash')==digest(normreceipt['records']),'scaled proposal binds full norm and scale receipt')
    scales=[EXACT.rational(item['scale'],budget) for item in normreceipt['records']]
    require(proposal.get('seed_endpoint_hash')==digest(license.parent_endpoint) and proposal.get('scaling')==SCALING,'same seed endpoint and coordinate scaling protocol')
    setup=proposal.get('norm_setup_counts');norm_counts=normreceipt['counts']
    require(type(setup)is dict and set(setup)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=norm_counts[k] for k,v in setup.items()) and setup['operations']<=100000000 and setup['peak_live_cells']<=4000000 and setup['fill_cells']<=20000000,'all norm setup work stays within same100m allocation')
    require(proposal.get('scale_vector')==[item['scale'] for item in normreceipt['records']],'declared complete scale vector')
    require(proposal.get('initial_free_vector')==[str(license.parent_vector[i]) for i in license.free],'explicit unchanged exact018 center')
    for k in FLAGS:require(proposal.get(k)is False,'proposal cannot certify a theorem')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict proposal completion')
    free_count=len(license.free)
    def vector(records):
        require(type(records)is list and len(records)==free_count,'complete finite free-coordinate record')
        return [mp_fraction(q,budget) for q in records]
    current=None;initial_exact_drift=None
    if 'initial_z_mp' in proposal:
        current=vector(proposal['initial_z_mp'])
        require(current==[F(0)]*free_count,'one exactly represented published free seed')
    calibration=proposal.get('calibration')
    if calibration is not None:
        require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40','successful preregistered affine calibration')
        for key in ('adjoint_pairing_relative_error',):
            q=mp_fraction(calibration.get(key),budget);require(0<=q<=F(1,10**40),'declared bounded affine calibration')
        if 'initial_forward_mp' in calibration:
            records=calibration['initial_forward_mp'];require(type(records)is list and len(records)==len(license.parent_vector),'explicit initial actual forward coordinates')
            values=[mp_fraction(q,budget) for q in records]
            initial_exact_drift=max((abs(q-r)/max(F(1),abs(r)) for q,r in zip(values,license.parent_vector)),default=F(0))
            require(initial_exact_drift<=F(1,10**40),'actual initial forward matches exact published endpoint')
            require(calibration.get('initial_exact_reference_relative_error')==str(initial_exact_drift),'independently recomputed exact-reference backward drift')
    power=proposal.get('power_trace');iterations=proposal.get('iterations')
    require(type(power)is list and len(power)<=8 and type(iterations)is list and len(iterations)<=64,'bounded fixed power/descent history')
    last_estimate=None;zero_power=False;previous_operator=None;previous_norm=None
    for index,item in enumerate(power):
        require(type(item)is dict and type(item.get('index'))is int and item['index']==index and not zero_power,'ordered finite power iteration')
        d=vector(item.get('vector'));op=vector(item.get('operator'));estimate=mp_fraction(item.get('estimate'),budget);norm=mp_fraction(item.get('operator_norm'),budget)
        if previous_operator is not None:require(all(_near(q,v/previous_norm,budget) for q,v in zip(d,previous_operator)),'normalized fixed power continuation')
        else:require(all(q*((-1)**i)>0 for i,q in enumerate(d)) and all(abs(q)==abs(d[0]) for q in d),'fixed alternating initial power vector')
        denominator=sum((q*q for q in d),F(0));numerator=sum((q*v for q,v in zip(d,op)),F(0));opnorm=sum((q*q for q in op),F(0));budget.charge(6*free_count,cells=2*free_count)
        require(denominator>0 and estimate>=0 and norm>=0 and _near(estimate,numerator/denominator,budget) and _near(norm*norm,opnorm,budget),'independent power dot/export consistency')
        last_estimate=estimate;zero_power=norm==0;previous_operator=op;previous_norm=norm
    native_calls=0;finite_trials=0;accepted=0;merit=None
    if 'initial_merit' in proposal:merit=mp_fraction(proposal['initial_merit'],budget);require(merit>=0,'nonnegative finite initial proposal merit');native_calls=1
    alpha=mp_fraction(proposal['initial_step'],budget) if 'initial_step' in proposal else None
    if alpha is not None:
        require(F(1,2**900)<=alpha<=F(2**900),'declared proposal step bounds')
        if last_estimate is not None:
            expected=min(F(2**900),max(F(1,2**900),1/last_estimate if last_estimate>0 else F(2**900)))
            require(_near(alpha,expected,budget),'power-derived initial step')
    terminated=False
    for index,item in enumerate(iterations):
        require(type(item)is dict and type(item.get('index'))is int and item['index']==index and not terminated and current is not None and merit is not None and alpha is not None,'ordered initialized descent history')
        require(item.get('reserved_iteration_work')==iteration_work_reserve(license),'full worst iteration reserve matches licensed dimensions/map')
        before=mp_fraction(item.get('merit_before'),budget);require(before==merit,'continuous recorded proposal merit')
        gradient=vector(item.get('gradient'));norm2=mp_fraction(item.get('gradient_squared_norm'),budget)
        require(norm2>=0 and _near(norm2,sum((g*g for g in gradient),F(0)),budget),'finite squared gradient export');budget.charge(3*free_count)
        trials=item.get('trials');require(type(trials)is list and len(trials)<=3 and type(item.get('accepted'))is bool,'bounded finite Armijo trials')
        passed=False
        for trial_index,trial in enumerate(trials):
            require(type(trial)is dict and type(trial.get('index'))is int and trial['index']==trial_index and not passed,'ordered stop-at-first-accepted trials')
            step=mp_fraction(trial.get('step'),budget);require(step==alpha/F(2**trial_index) and step>0,'fixed exact halving trial step')
            if trial.get('finite')is False:
                require(step<F(1,2**900) and trial.get('reason')=='step below declared minimum','only declared below-minimum trial skip');continue
            require(trial.get('finite')is True,'explicit finite trial');trialfree=vector(trial.get('z'));approximate_free=vector(trial.get('approximate_free_mp'))
            require(all(_near(q,license.parent_vector[i]+d*z,budget) for q,i,d,z in zip(approximate_free,license.free,scales,trialfree)),'rounded trial free coordinates equal centered f0+D*z')
            value=mp_fraction(trial.get('merit'),budget);threshold=mp_fraction(trial.get('armijo_threshold'),budget)
            require(value>=0 and all(_near(q,v-step*g,budget) for q,v,g in zip(trialfree,current,gradient)),'recorded finite rounded descent coordinates')
            require(_near(threshold,merit-step*norm2/8,budget) and trial.get('armijo_passed')is (value<=threshold),'recorded Armijo proposal decision')
            native_calls+=1;finite_trials+=1
            if value<=threshold:passed=True;current=trialfree;merit=value;alpha=step;accepted+=1
        require(item['accepted']is passed,'accepted iteration matches first trial')
        if norm2==0:require(not trials and not passed,'zero gradient stops before trials');terminated=True
        elif not passed:
            if status=='proposed' or index<len(iterations)-1:require(len(trials)==3,'failed line search exhausted declared trials')
            terminated=True
    counts=proposal.get('counts');require(type(counts)is dict and all(type(v)is int and v>=0 for v in counts.values()),'strict proposal work counters')
    require(counts.get('operations',-1)>=native_calls*2*96*15**3,'all repeated native eigensolve work charged')
    if status=='proposed':
        require(counts.get('operations')<=80000000 and counts.get('peak_live_cells',0)<=4000000 and counts.get('fill_cells',0)<=20000000,'complete bounded numerical proposal work')
        require(current is not None and calibration is not None and initial_exact_drift is not None and (len(power)==8 or zero_power),'complete measured affine calibration and fixed power pass')
        final=vector(proposal.get('final_z_mp'));require(final==current,'exact final fixed-precision binary export')
        exact_free=[budget.rational(license.parent_vector[i]+budget.rational(d*z)) for i,d,z in zip(license.free,scales,final)]
        require(proposal.get('final_free_vector')==list(map(str,exact_free)),'unrounded exact f0+D*z final rational export')
        require(mp_fraction(proposal.get('final_merit'),budget)==merit,'continuous final proposal merit')
        reason=proposal.get('stop_reason');require(reason in ('iteration_limit','zero_gradient','line_search_failed','budget_stop'),'declared finite stopping reason')
        if reason=='iteration_limit':require(len(iterations)==64 and iterations[-1]['accepted']is True,'fixed64iteration endpoint')
        elif reason=='zero_gradient':require(iterations and mp_fraction(iterations[-1]['gradient_squared_norm'],budget)==0,'actual zero gradient stop')
        elif reason=='budget_stop':
            _verify_budget_stop(license,proposal,budget,max_trace_bytes)
        elif reason=='line_search_failed':require(iterations and iterations[-1]['accepted']is False and len(iterations[-1]['trials'])==3,'actual failed three-trial stop')
    else:require(type(proposal.get('reason'))is str and bool(proposal['reason']),'explicit UNKNOWN proposal cause')
    return dict(verified=True,complete=status=='proposed',proposal_history_only=True,gradient_or_merit_certified=False,intermediate_iterates_exact=False,native_PSD_projection_precision='binary64',affine_map_precision_decimal_digits=80,actual_initial_exact_reference_relative_error=str(initial_exact_drift) if initial_exact_drift is not None else None,power_iterations=len(power),gradient_iterations=len(iterations),accepted_iterations=accepted,finite_armijo_trials=finite_trials,native_eigensolve_calls=2*native_calls,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)



def verify_scaling(license,receipt,*,deadline=None,max_operations=5000000,max_cells=60000000,max_norm_bytes=2097152):
    require(type(license)is _EndpointLicense,'hash-issued publication018 license required')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,8192)
    require(type(max_norm_bytes)is int and 0<max_norm_bytes<=2097152,'strict norm receipt byte cap')
    require(type(receipt)is dict and receipt.get('schema')=='primitive-state-cone-jacobi-norms-v1','known cone-Jacobi norm records')
    data=encoded(receipt);require(len(data)<=max_norm_bytes,'bounded entire norm export');budget.charge(len(data)//64+1,cells=len(data)//64+1)
    require(receipt.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and receipt.get('seed_endpoint_hash')==digest(license.parent_endpoint),'all norms bind same chart and ordered free indices')
    for flag in FLAGS:require(receipt.get(flag)is False,'no norm receipt theorem claim')
    for flag in ('column_norms_independently_verified','scaled_trace_bound_certified'):require(receipt.get(flag)is False,'exported column norms explicitly unverified')
    require(receipt.get('scaling')==SCALING,'preregistered exact dyadic rounding and zero policy')
    records=receipt.get('records');require(type(records)is list and len(records)<=len(license.free),'every coordinate retained with a scale')
    trace=F(0);trace_limited=False
    for index,(i,item) in enumerate(zip(license.free,records)):
        require(type(item)is dict and type(item.get('index'))is int and item['index']==index and type(item.get('free_index'))is int and item['free_index']==i,'ordered original projected free index')
        g=EXACT.rational(item.get('norm'),budget);require(g>=0,'nonnegative exact exported norm')
        require(type(item.get('response_max_bits'))is int and 0<=item['response_max_bits']<=4096 and type(item.get('norm_max_bits'))is int and max(g.numerator.bit_length(),g.denominator.bit_length())<=item['norm_max_bits']<=8192,'bounded declared response/norm coefficient bits')
        k=item.get('exponent');require(type(k)is int and abs(k)<=900,'strict bounded dyadic scale exponent')
        d=EXACT.rational(item.get('scale'),budget);expected=F(2**(-k)) if k<=0 else F(1,2**k)
        require(d==expected and d>0,'strict positive unclipped dyadic scale')
        if g==0:require(k==0 and d==1,'zero norm keeps coordinate with scale one')
        else:
            upper=F(2**(2*k)) if k>=0 else F(1,2**(-2*k))
            require(upper/4<g<=upper,'least integer exponent exact strict-lower inclusive-upper rounding')
        if trace is not None:
            term=budget.rational(g*d*d)
            require(max(abs(trace.numerator).bit_length()+term.denominator.bit_length(),abs(term.numerator).bit_length()+trace.denominator.bit_length())+1<=16385 and trace.denominator.bit_length()+term.denominator.bit_length()<=16385,'prechecked bounded diagnostic trace temporary')
            next_trace=trace+term
            if max(abs(next_trace.numerator).bit_length(),next_trace.denominator.bit_length())>8192:trace=None;trace_limited=True
            else:trace=budget.rational(next_trace)
        budget.charge(8,cells=3)
    complete=receipt.get('complete');require(type(complete)is bool and receipt.get('status')==('scaled' if complete else 'unknown'),'strict norm completion status')
    if complete:require(len(records)==len(license.free) and receipt.get('records_hash')==digest(records),'complete exact ordered norm records hash')
    else:require(type(receipt.get('reason'))is str and bool(receipt['reason']),'explicit incomplete norm reason')
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict bounded norm producer counts')
    require(counts['operations']<=100000000 and counts['peak_live_cells']<=4000000 and counts['fill_cells']<=20000000,'bounded streamed norm producer')
    return dict(verified=True,complete=complete,positive_invertible_coordinate_change=complete,rounding_from_exported_norms_verified=True,coordinate_count=len(records),reported_scaled_diagonal_trace=str(trace) if trace is not None else None,reported_trace_diagnostic_limited=trace_limited,reported_trace_diagnostic_limit_reason='aggregate rational coefficient bit cap8192' if trace_limited else None,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)


def verify_endpoint(license,endpoint,**kwargs):
    require(type(license)is _EndpointLicense,'hash-bound published exact chart required')
    for flag in FLAGS:require(endpoint.get(flag)is False,'no endpoint norm or global certification claim')
    return OLD.verify_endpoint(license.endpoint_license,endpoint,**kwargs)


def verify_map_receipt(license,receipt,*,deadline=None,max_operations=5000000,max_cells=60000000):
    require(type(license)is _EndpointLicense,'hash-issued exact chart license')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,4096);data=encoded(receipt);budget.charge(len(data)//64+1,cells=len(data)//64+1)
    require(type(receipt)is dict and receipt.get('schema')=='primitive-state-cone-jacobi-map-v1','known materialized map metadata')
    for k in FLAGS:require(receipt.get(k)is False,'map carries no theorem admission')
    require(receipt.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and receipt.get('retained_indices')==license.summary['retained_indices'] and receipt.get('pivot_columns')==sorted(license.pivots) and receipt.get('free_indices')==license.free,'materialized map binds independently published source/rank/pivots')
    require(receipt.get('seed_endpoint_hash')==digest(license.parent_endpoint) and receipt.get('initial_projected_hash')==digest(list(map(str,license.parent_vector))) and receipt.get('seed_rule')==SEED,'map licensed exact018 center')
    require(receipt.get('precision')==PRECISION and receipt.get('initial_free_vector')==[str(license.parent_vector[i]) for i in license.free],'fixed mixed-precision map and seed')
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict map work counters')
    require(counts['operations']<=50000000 and counts['peak_live_cells']<=4000000 and counts['fill_cells']<=20000000,'complete bounded map producer')
    require(type(receipt.get('source_cells'))is int and receipt['source_cells']==license.source['source_cells'] and type(receipt.get('sparse_map_entries'))is int and 0<=receipt['sparse_map_entries']<=4000000,'bounded sparse map source/entry counts')
    return dict(verified=True,published_chart_license_match=True,full_elimination_replayed=False,high_precision_map_independently_rebuilt=False,normalized_basis_hash=license.summary['normalized_basis_hash'],audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)




def verify_search(license,mapreceipt,normreceipt,proposal=None,endpoint=None,*,deadline=None,max_operations=100000000,max_cells=60000000,max_coefficient_bits=4096,max_map_bytes=131072,max_norm_bytes=2097152,max_trace_bytes=8388608,max_endpoint_bytes=1048576,max_check_bytes=65536):
    require(type(license)is _EndpointLicense,'hash-issued exact018 source license required')
    require(type(max_operations)is int and 0<max_operations<=450000000 and type(max_cells)is int and 0<max_cells<=60000000,'strict cumulative checker work/cell caps')
    for value,cap in ((max_map_bytes,131072),(max_norm_bytes,2097152),(max_trace_bytes,8388608),(max_endpoint_bytes,1048576),(max_check_bytes,65536)):
        require(type(value)is int and 0<value<=cap,'strict finite artifact byte caps')
    require(type(max_coefficient_bits)is int and 0<max_coefficient_bits<=4096,'bounded exact endpoint coefficients')
    remaining=max_operations;cells=max_cells;checks={};payload_bytes=0
    def account(name,value,result):
        nonlocal remaining,cells,payload_bytes
        checks[name]=result;remaining-=result['audit_operations'];cells-=result['audit_cells'];payload_bytes+=len(encoded(value))
        require(remaining>=0 and cells>=0,'combined independent stage accounting')
    require(len(encoded(mapreceipt))<=max_map_bytes,'bounded map artifact')
    result=verify_map_receipt(license,mapreceipt,deadline=deadline,max_operations=remaining,max_cells=cells);account('map_check',mapreceipt,result)
    result=verify_scaling(license,normreceipt,deadline=deadline,max_operations=remaining,max_cells=cells,max_norm_bytes=max_norm_bytes);account('scaling_check',normreceipt,result)
    if proposal is not None:
        require(result['complete'],'proposal requires every positive scale')
        result=verify_proposal_trace(license,normreceipt,proposal,deadline=deadline,max_operations=remaining,max_cells=cells,max_coefficient_bits=max_coefficient_bits,max_trace_bytes=max_trace_bytes);account('proposal_check',proposal,result)
    else:checks['proposal_check']=None
    endpoint_checked=False
    if endpoint is not None:
        require(proposal is not None and type(endpoint)is dict and len(encoded(endpoint))<=max_endpoint_bytes,'bounded endpoint requires proposal')
        for k in FLAGS:require(endpoint.get(k)is False,'endpoint cannot certify unverified norms or uniform claims')
        if endpoint.get('complete')is True:
            require(proposal.get('complete')is True and endpoint.get('schema')=='primitive-state-cone-jacobi-endpoint-v1','endpoint follows complete numerical proposal')
            require(endpoint.get('final_free_vector')==proposal.get('final_free_vector') and endpoint.get('norm_records_hash')==normreceipt.get('records_hash') and endpoint.get('seed_endpoint_hash')==digest(license.parent_endpoint),'exact endpoint binds final f0+D*z,scale records and exact018 seed')
            result=verify_endpoint(license,endpoint,deadline=deadline,max_operations=remaining,max_cells=cells,max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_endpoint_bytes);account('endpoint_check',endpoint,result);endpoint_checked=True
        else:
            require(endpoint.get('complete')is False and type(endpoint.get('reason'))is str,'explicit incomplete exact endpoint');size=len(encoded(endpoint));payload_bytes+=size
            budget=EXACT.EXACT._Budget(deadline,remaining,cells,max_coefficient_bits);budget.charge(size//64+1,cells=size//64+1);remaining-=budget.operations;cells-=budget.cells;checks['endpoint_check']=None
    else:checks['endpoint_check']=None
    operations=max_operations-remaining;used_cells=max_cells-cells
    out=dict(verified=True,complete=endpoint_checked,endpoint_verified=endpoint_checked,finite_candidate_feasible=checks['endpoint_check']['finite_candidate_feasible'] if endpoint_checked else None,proposal_history_only=True,gradient_or_merit_certified=False,full_elimination_replayed=False,parent_license_summary=license.summary,audit_operations=operations,audit_cells=used_cells,independent_audit_work_reserve=operations+payload_bytes+license.source['source_cells']+1,**checks,**FLAGS)
    require(len(encoded(out))<=max_check_bytes,'bounded combined independent result')
    return out


def iteration_work_reserve(license):
    w=len(license.parent_vector);n=len(license.free);p=len(license.pivots);E=license.summary['sparse_map_entries']
    shape=license.source['shape'];sc=shape[0]+license.source['offset']-shape[0]-2*shape[1];pairs=120
    forward=4*E+2*p+w+2*n
    merit=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)
    adjoint=2*E+w+n
    return 3*(2*n+forward+merit+32*n+4096)+adjoint+2*n+8*n+4096+2048*n+65536


def _verify_budget_stop(license,proposal,budget,max_trace_bytes):
    stop=proposal.get('budget_stop');require(type(stop)is dict,'explicit complete last-point budget stop')
    integers=('before_iteration','operations','max_operations','remaining_operations','worst_iteration_work_reserve','finalization_work_reserve','trace_retained_bytes','max_trace_bytes','worst_iteration_trace_bytes','finalization_trace_bytes')
    require(set(stop)==set(integers)|{'resource'} and all(type(stop[k])is int and stop[k]>=0 for k in integers),'bounded integer budget stop fields')
    n=len(license.free);work=iteration_work_reserve(license);tail=max_trace_bytes+20000*n+65536;perstep=16384+7*96*n;final=4096+3000*n
    require(stop['before_iteration']==len(proposal['iterations'])<64 and stop['max_operations']==80000000 and stop['operations']<=proposal['counts']['operations']<=80000000 and stop['remaining_operations']==80000000-stop['operations'],'budget stop occurs before next complete iteration')
    require(stop['worst_iteration_work_reserve']==work and stop['finalization_work_reserve']==tail and stop['max_trace_bytes']==max_trace_bytes and stop['worst_iteration_trace_bytes']==perstep and stop['finalization_trace_bytes']==final,'independently reconstructed fixed operation/serialization reserves')
    keys=('schema','status','complete','precision','search','scaling','seed_rule','normalized_basis_hash','seed_endpoint_hash','norm_records_hash','norm_setup_counts','initial_free_vector','scale_vector','calibration','initial_z_mp','power_trace','initial_step','initial_merit','initial_merit_details')
    initial={k:proposal[k] for k in keys};initial.update(status='unknown',complete=False,iterations=[],final_free_vector=None,**FLAGS)
    retained=len(encoded(initial))+sum(len(encoded(entry))+1 for entry in proposal['iterations']);budget.charge(retained//64+len(proposal['iterations'])+1)
    require(stop['trace_retained_bytes']==retained,'exact complete retained-prefix serialization proxy')
    operation_shortfall=stop['remaining_operations']<work+tail
    byte_shortfall=max_trace_bytes-retained<perstep+final
    require((stop['resource']=='operations' and operation_shortfall)or(stop['resource']=='trace_bytes' and not operation_shortfall and byte_shortfall),'actual charged work or receipt budget prevents next iteration')
