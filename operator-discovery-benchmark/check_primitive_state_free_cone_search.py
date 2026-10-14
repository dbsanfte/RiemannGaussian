"""Independent licensed affine endpoint and bounded proposal-history checks.

A published exact rank/source/pivot license permits endpoint uniqueness checks
without replaying elimination. Numerical search histories are proposals only.
"""
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import check_primitive_state_triangular_restoration as EXACT
import check_primitive_state_cached_primal_variants as CACHE_CHECK

FLAGS=dict(EXACT.FLAGS)
require=EXACT.require
encoded=EXACT.encoded
digest=EXACT.digest
SCHEMA='primitive-state-free-cone-search-v1'
PARENT='cancellation-arithmetic-results/primitive-state-triangular-restoration-001'
CACHE='cancellation-arithmetic-results/primitive-state-cached-primal-variants-001/jobs/prepare/source-cache.json'
BASIS='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002/jobs/basis.json'
PROJECTION='cancellation-arithmetic-results/primitive-state-exact-row-basis-probe-002/jobs/projection.json'
MANIFEST='cancellation-arithmetic-results/publication-017/manifest.json'
REPORT='cancellation-arithmetic-results/publication-017/report.json'
_TOKEN=object()


def _read(root,name,budget,cap=8388608):
    require(type(name)is str and not Path(name).is_absolute() and '..' not in Path(name).parts,'bounded relative license path')
    path=(root/name).resolve();require(path.is_relative_to(root),'license path remains in source root')
    size=path.stat().st_size;require(size<=cap,'bounded license artifact bytes')
    budget.charge(2*(size//64+1),cells=size//64+1)
    return json.loads(path.read_bytes())


def _sha(root,name,budget):
    path=(root/name).resolve();require(path.is_relative_to(root),'hash path remains in source root')
    size=path.stat().st_size;budget.charge(size//64+1)
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()


class _EndpointLicense:
    def __init__(self,token,source,summary,parent_vector,pivots,free,bindings,*,cache=None,basis=None,projection=None,parent_restoration=None):
        require(token is _TOKEN,'license only issued by immutable evidence validation')
        self.source=source;self.summary=summary;self.parent_vector=parent_vector
        self.pivots=pivots;self.free=free;self.bindings=bindings
        self.cache=cache;self.basis=basis;self.projection=projection;self.parent_restoration=parent_restoration


def load_verified_license(root,expected_file_bindings,*,deadline=None,max_operations=50000000,
                          max_cells=60000000,max_coefficient_bits=4096):
    """Hash-bound published chart evidence; no arithmetic/source compilation."""
    root=Path(root).resolve();budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(expected_file_bindings)is dict and bool(expected_file_bindings),'mandatory frozen file bindings, no trust boolean')
    needed={MANIFEST,REPORT,CACHE,BASIS,PROJECTION,PARENT+'/restoration.json'}
    # Restoration artifacts live in jobs; keep the precise archived paths.
    needed.remove(PARENT+'/restoration.json');needed|={PARENT+'/jobs/restoration.json',PARENT+'/jobs/check.json',PARENT+'/jobs/restoration-job.json',PARENT+'/independent_verification.json',PARENT+'/receipt.json'}
    require(needed<=set(expected_file_bindings),'complete immutable chart/source/seed bindings')
    for name,h in expected_file_bindings.items():require(type(h)is str and len(h)==64 and _sha(root,name,budget)==h,'frozen endpoint license file '+name)
    manifest=_read(root,MANIFEST,budget);published=manifest.get('files');require(type(published)is dict,'complete published endpoint evidence inventory')
    catalogs=[published]
    for number in (16,15):
        name=f'cancellation-arithmetic-results/publication-{number:03d}/manifest.json'
        h=next((files[name] for files in catalogs if name in files),None)
        require(h is not None and _sha(root,name,budget)==h,'recursive immutable publication ancestry')
        files=_read(root,name,budget).get('files');require(type(files)is dict,'complete ancestor manifest');catalogs.append(files)
    for name in needed-{MANIFEST}:
        h=next((files[name] for files in catalogs if name in files),None)
        require(h is not None and h==expected_file_bindings[name],'published source/chart endpoint binding '+name)
    report=_read(root,REPORT,budget);review=_read(root,PARENT+'/independent_verification.json',budget)
    receipt=_read(root,PARENT+'/receipt.json',budget,65536)
    require(report.get('independent_receipt_sha256')==expected_file_bindings[PARENT+'/independent_verification.json'] and report.get('terminal_receipt_sha256')==expected_file_bindings[PARENT+'/receipt.json'],'published independent/terminal review identity')
    require(report.get('schema')==17 and review.get('all_passed')is True and review.get('schema')=='primitive-state-triangular-restoration-independent-review-v1','completed publication017 endpoint license')
    for stem,h in review.get('input_sha256',{}).items():
        require(stem in ('protocol','source_seal','input','seal','tests','execution','receipt') and _sha(root,PARENT+'/'+stem+'.json',budget)==h,'parent stem-only independent review binding')
    require(set(review.get('input_sha256',{}))=={'protocol','source_seal','input','seal','tests','execution','receipt'},'complete parent review stem bindings')
    check=_read(root,PARENT+'/jobs/check.json',budget);parent=_read(root,PARENT+'/jobs/restoration.json',budget);job=_read(root,PARENT+'/jobs/restoration-job.json',budget,65536)
    require(check==review.get('restoration_check') and check.get('verified')is True and check.get('complete')is True and check.get('restoration_verified')is True,'completed independent exact chart replay')
    require(review.get('job',{}).get('restoration_verified')is True and job.get('status')=='restoration_verified' and job.get('restoration_verified')is True,'completed chart transport')
    require(parent.get('complete')is True and parent.get('status')=='restored' and parent.get('normalized_basis_hash')==check.get('normalized_basis_hash'),'licensed exact normalized chart hash')
    for name in ('restoration','check'):
        path='jobs/'+name+'.json';require(receipt.get('files_sha256',{}).get(path)==expected_file_bindings[PARENT+'/'+path],'complete chart terminal artifact inventory')
    cache=_read(root,CACHE,budget,134217728);basis=_read(root,BASIS,budget,33554432);projection=_read(root,PROJECTION,budget,33554432)
    for name,value in [('cache',cache),('basis',basis),('projection',projection)]:
        data=encoded(value);budget.charge(2*(len(data)//64+1),cells=len(data)//64+1)
        require(parent.get('input_bindings',{}).get(name)==hashlib.sha256(data).hexdigest(),'licensed chart bound to exact source/tape '+name)
    source=CACHE_CHECK.decode_original(cache,budget);n=len(source['columns']);retained,recipes,starts=EXACT.derive_projection(source['shape'],source['offset'],source['specs'],n)
    require(projection.get('complete')is True and projection.get('retained_indices')==retained and basis.get('complete')is True and basis.get('coefficient_consistency')=='consistent' and basis.get('inconsistent_augmented_pivots')==[],'licensed complete consistent projected chart')
    pivots=basis.get('pivot_columns');require(type(pivots)is list and all(type(i)is int and 0<=i<len(retained) for i in pivots) and len(set(pivots))==len(pivots)==basis.get('augmented_rank'),'complete licensed rank/pivot partition')
    require(parent.get('retained_indices')==retained and parent.get('pivot_columns')==sorted(pivots) and basis.get('source_hash')==projection.get('projected_rows_hash'),'restored chart matches exact source/pivots')
    free=[i for i in range(len(retained)) if i not in set(pivots)]
    vector=parent.get('restored_projected_vector');require(type(vector)is list and len(vector)==len(retained),'licensed full projected exact seed')
    parent_vector=[EXACT.rational(q,budget) for q in vector]
    summary=dict(publication='publication-017',manifest_sha256=expected_file_bindings[MANIFEST],normalized_basis_hash=check['normalized_basis_hash'],original_system_hash=cache['assembly']['original_system_hash'],original_source_hash=cache['original_source_hash'],original_rows=len(source['monomials']),original_variables=n,projected_variables=len(retained),rank=len(pivots),free_count=len(free),retained_indices=retained,pivot_columns=sorted(pivots),free_indices=free,parent_candidate_hash=parent['candidate_hash'],parent_projected_hash=digest(vector),parent_free_hash=digest([vector[i] for i in free]),audit_operations=budget.operations,audit_cells=budget.cells)
    return _EndpointLicense(_TOKEN,source,summary,parent_vector,pivots,free,dict(expected_file_bindings),cache=cache,basis=basis,projection=projection,parent_restoration=parent)


def aggregate_original(vector,retained,recipes,budget):
    position={j:i for i,j in enumerate(retained)};out=[vector[j] for j in retained]
    for omitted,recipe in recipes.items():
        for j,q in recipe.items():
            i=position[j];out[i]=budget.rational(out[i]+budget.rational(q*vector[omitted]));budget.charge(cells=2)
    return out


def verify_endpoint(license,proposal,*,deadline=None,max_operations=100000000,max_cells=60000000,
                    max_coefficient_bits=4096,max_receipt_bytes=8388608):
    require(type(license)is _EndpointLicense,'in-process hash-issued chart license required')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(proposal)is dict,'explicit exact endpoint proposal');payload=encoded(proposal)
    require(len(payload)<=max_receipt_bytes,'bounded proposal receipt');budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    for k in FLAGS:require(proposal.get(k)is False,'no proposal proof claim '+k)
    source=license.source;n=len(source['columns']);retained,recipes,starts=EXACT.derive_projection(source['shape'],source['offset'],source['specs'],n)
    require(proposal.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and proposal.get('free_indices')==license.free,'endpoint binds licensed exact chart and all free indices')
    vector=proposal.get('candidate_original_vector');require(type(vector)is list and len(vector)==n,'every original exact endpoint coordinate explicit')
    x=[EXACT.rational(q,budget) for q in vector]
    projected=aggregate_original(x,retained,recipes,budget)
    free=proposal.get('final_free_vector');require(type(free)is list and len(free)==len(license.free),'all final free coordinates explicit')
    values=[EXACT.rational(q,budget) for q in free]
    require(values==[projected[i] for i in license.free],'exact endpoint matches licensed free-coordinate chart')
    if 'final_projected_vector' in proposal:require(proposal['final_projected_vector']==list(map(str,projected)),'complete exact projected endpoint aggregation')
    checks=EXACT.check_original_candidate(source['columns'],source['lhs'],source['monomials'],x,source['offset'],source['specs'],budget)
    require(checks['equality_mismatch_count']==0,'exact endpoint fails original affine equations')
    require(proposal.get('candidate_hash')==digest(vector),'full endpoint candidate hash')
    diagnostics=proposal.get('diagnostics')
    if diagnostics is not None:
        require(type(diagnostics)is dict and diagnostics.get('all_original_rows_checked')==len(source['monomials']) and diagnostics.get('equality_mismatch_count')==0 and diagnostics.get('equality_mismatches')==[],'complete endpoint equality diagnostics')
        negatives=[dict(coordinate=i,value=str(q)) for i,q in enumerate(x[:source['offset']]) if q<0]
        require(diagnostics.get('negative_scalar_count')==len(negatives) and diagnostics.get('negative_scalars')==negatives and diagnostics.get('candidate_cone_checks_pass')is checks['finite_candidate_feasible'],'complete endpoint signs and cone outcome')
        reports=diagnostics.get('psd');require(type(reports)is list and [r.get('name') for r in reports]==sorted(source['specs']),'full named endpoint PSD diagnostics')
        start=source['offset']
        for report,(name,size) in zip(reports,sorted(source['specs'].items())):
            matrix=[[F(0) for _ in range(size)] for _ in range(size)]
            for a in range(size):
                for b in range(a,size):matrix[a][b]=matrix[b][a]=x[start];start+=1
            EXACT.verify_psd_receipt(matrix,report,checks['psd_blocks'][name],budget)
    return dict(verified=True,endpoint_verified=True,all_original_equations_checked=len(source['monomials']),original_variables=n,rank=len(license.pivots),free_count=len(license.free),licensed_affine_uniqueness=True,full_elimination_replayed=False,candidate_hash=digest(vector),final_free_hash=digest(free),normalized_basis_hash=license.summary['normalized_basis_hash'],exact_candidate_checks=checks,finite_candidate_feasible=checks['finite_candidate_feasible'],audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(payload)+source['source_cells']+1,**FLAGS)


PRECISION=dict(decimal_digits=80,binary_bits=269,actual_map_relative_tolerance='1e-40',serialized_binary_exponent_abs_cap=4096,mixed_precision=True,PSD_eigh='binary64',PSD_negative_parts='binary64',calibration_scope='affine forward and adjoint only')
SEARCH=dict(power_steps=8,gradient_iterations=24,armijo_trials=3,armijo_coefficient='1/8',step_min_binary_exponent=-900,step_max_binary_exponent=900,identity_free_coordinate_scaling=True,native_eigh_work_coefficient=96)
SEED='licensed publication017 restored projected nonpivots; one seed; no additional clipping'


def mp_fraction(record,budget):
    require(type(record)is list and len(record)==3,'explicit finite mp record')
    sign,text,exponent=record
    require(type(sign)is int and sign in (0,1) and type(text)is str and 0<len(text)<=68 and all(c in '0123456789abcdef' for c in text) and type(exponent)is int,'bounded80digit mp fields')
    man=int(text,16)
    require(format(man,'x')==text and man.bit_length()<=269 and (man%2==1 if man else sign==0 and exponent==0),'canonical normalized mp mantissa')
    require(abs(exponent)<=4096 and max(man.bit_length()+max(exponent,0),max(1,-exponent+1))<=budget.bits,'bounded exact mp exponent before shifts')
    value=F((-1 if sign else 1)*man)
    return budget.rational(value*2**exponent if exponent>=0 else value/F(2**(-exponent)))


def _near(value,expected,budget):
    budget.charge(3)
    return abs(value-expected)<=F(1,2**255)*max(F(1),abs(expected))


def verify_proposal_trace(license,proposal,*,deadline=None,max_operations=50000000,max_cells=60000000,
                          max_coefficient_bits=4096,max_trace_bytes=8388608):
    """Check finite exports/order/rounding diagnostics, never gradient correctness."""
    require(type(license)is _EndpointLicense,'hash-issued published chart required')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(proposal)is dict and proposal.get('schema')==SCHEMA,'known finite proposal trace');data=encoded(proposal)
    require(len(data)<=max_trace_bytes,'bounded entire proposal history');budget.charge(len(data)//64+1,cells=len(data)//64+1)
    require(proposal.get('precision')==PRECISION and proposal.get('search')==SEARCH and proposal.get('seed_rule')==SEED,'fixed80digit proposal protocol')
    require(proposal.get('normalized_basis_hash')==license.summary['normalized_basis_hash'],'proposal chart matches published normalized hash')
    for k in FLAGS:require(proposal.get(k)is False,'proposal cannot certify a theorem')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict proposal completion')
    free_count=len(license.free)
    def vector(records):
        require(type(records)is list and len(records)==free_count,'complete finite free-coordinate record')
        return [mp_fraction(q,budget) for q in records]
    current=None;initial_exact_drift=None
    if 'initial_free_mp' in proposal:
        current=vector(proposal['initial_free_mp'])
        require(current==[license.parent_vector[i] for i in license.free],'one exactly represented published free seed')
    calibration=proposal.get('calibration')
    if calibration is not None:
        require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40','successful preregistered affine calibration')
        for key in ('initial_relative_error','adjoint_pairing_relative_error'):
            q=mp_fraction(calibration.get(key),budget);require(0<=q<=F(1,10**40),'declared bounded affine calibration')
        if 'initial_forward_mp' in calibration:
            records=calibration['initial_forward_mp'];require(type(records)is list and len(records)==len(license.parent_vector),'explicit initial actual forward coordinates')
            values=[mp_fraction(q,budget) for q in records]
            initial_exact_drift=max((abs(q-r)/max(F(1),abs(r)) for q,r in zip(values,license.parent_vector)),default=F(0))
            require(initial_exact_drift<=F(1,10**40),'actual initial forward matches exact published endpoint')
            require(calibration.get('initial_exact_reference_relative_error')==str(initial_exact_drift),'independently recomputed exact-reference backward drift')
    power=proposal.get('power_trace');iterations=proposal.get('iterations')
    require(type(power)is list and len(power)<=8 and type(iterations)is list and len(iterations)<=24,'bounded fixed power/descent history')
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
            require(trial.get('finite')is True,'explicit finite trial');trialfree=vector(trial.get('free'));value=mp_fraction(trial.get('merit'),budget);threshold=mp_fraction(trial.get('armijo_threshold'),budget)
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
        require(counts.get('operations')<=100000000 and counts.get('peak_live_cells',0)<=4000000 and counts.get('fill_cells',0)<=20000000,'complete bounded numerical proposal work')
        require(current is not None and calibration is not None and initial_exact_drift is not None and (len(power)==8 or zero_power),'complete measured affine calibration and fixed power pass')
        final=vector(proposal.get('final_free_mp'));require(final==current and proposal.get('final_free_vector')==list(map(str,final)),'exact final fixed-precision binary export')
        require(mp_fraction(proposal.get('final_merit'),budget)==merit,'continuous final proposal merit')
        reason=proposal.get('stop_reason');require(reason in ('iteration_limit','zero_gradient','line_search_failed'),'declared finite stopping reason')
        if reason=='iteration_limit':require(len(iterations)==24 and iterations[-1]['accepted']is True,'fixed24iteration endpoint')
        elif reason=='zero_gradient':require(iterations and mp_fraction(iterations[-1]['gradient_squared_norm'],budget)==0,'actual zero gradient stop')
        else:require(iterations and iterations[-1]['accepted']is False and len(iterations[-1]['trials'])==3,'actual failed three-trial stop')
    else:require(type(proposal.get('reason'))is str and bool(proposal['reason']),'explicit UNKNOWN proposal cause')
    return dict(verified=True,complete=status=='proposed',proposal_history_only=True,gradient_or_merit_certified=False,intermediate_iterates_exact=False,native_PSD_projection_precision='binary64',affine_map_precision_decimal_digits=80,actual_initial_exact_reference_relative_error=str(initial_exact_drift) if initial_exact_drift is not None else None,power_iterations=len(power),gradient_iterations=len(iterations),accepted_iterations=accepted,finite_armijo_trials=finite_trials,native_eigensolve_calls=2*native_calls,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)


def verify_map_receipt(license,receipt,*,deadline=None,max_operations=5000000,max_cells=60000000):
    require(type(license)is _EndpointLicense,'hash-issued exact chart license')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,4096);data=encoded(receipt);budget.charge(len(data)//64+1,cells=len(data)//64+1)
    require(type(receipt)is dict and receipt.get('schema')=='primitive-state-free-cone-map-v1','known materialized map metadata')
    for k in FLAGS:require(receipt.get(k)is False,'map carries no theorem admission')
    require(receipt.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and receipt.get('retained_indices')==license.summary['retained_indices'] and receipt.get('pivot_columns')==sorted(license.pivots) and receipt.get('free_indices')==license.free,'materialized map binds independently published source/rank/pivots')
    require(receipt.get('precision')==PRECISION and receipt.get('initial_free_vector')==[str(license.parent_vector[i]) for i in license.free],'fixed mixed-precision map and seed')
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict map work counters')
    require(counts['operations']<=50000000 and counts['peak_live_cells']<=4000000 and counts['fill_cells']<=20000000,'complete bounded map producer')
    require(type(receipt.get('source_cells'))is int and receipt['source_cells']==license.source['source_cells'] and type(receipt.get('sparse_map_entries'))is int and 0<=receipt['sparse_map_entries']<=4000000,'bounded sparse map source/entry counts')
    return dict(verified=True,published_chart_license_match=True,full_elimination_replayed=False,high_precision_map_independently_rebuilt=False,normalized_basis_hash=license.summary['normalized_basis_hash'],audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)


def verify_search(license,mapreceipt,proposal,endpoint=None,*,deadline=None,max_operations=100000000,
                  max_cells=60000000,max_coefficient_bits=4096,max_trace_bytes=8388608,
                  max_endpoint_bytes=8388608):
    require(type(license)is _EndpointLicense,'hash-issued endpoint source required')
    remaining_ops=max_operations;remaining_cells=max_cells;checks={};bytes_total=0
    require(type(max_operations)is int and max_operations>0 and type(max_cells)is int and max_cells>0,'strict combined checker caps')
    def account(name,value,result):
        nonlocal remaining_ops,remaining_cells,bytes_total
        checks[name]=result;remaining_ops-=result['audit_operations'];remaining_cells-=result['audit_cells'];bytes_total+=len(encoded(value))
        require(remaining_ops>=0 and remaining_cells>=0,'combined independent checker work/cells')
    require(len(encoded(mapreceipt))<=max_trace_bytes,'bounded map receipt')
    result=verify_map_receipt(license,mapreceipt,deadline=deadline,max_operations=remaining_ops,max_cells=remaining_cells);account('map_check',mapreceipt,result)
    result=verify_proposal_trace(license,proposal,deadline=deadline,max_operations=remaining_ops,max_cells=remaining_cells,max_coefficient_bits=max_coefficient_bits,max_trace_bytes=max_trace_bytes);account('proposal_check',proposal,result)
    endpoint_checked=False
    if endpoint is not None:
        require(type(endpoint)is dict and len(encoded(endpoint))<=max_endpoint_bytes,'bounded exact endpoint artifact')
        for k in FLAGS:require(endpoint.get(k)is False,'endpoint cannot claim uniform theorem')
        if endpoint.get('complete')is True:
            require(proposal.get('complete')is True and proposal.get('status')=='proposed','complete endpoint follows complete fixed proposal')
            require(endpoint.get('schema')=='primitive-state-free-cone-endpoint-v1' and endpoint.get('final_free_vector')==proposal.get('final_free_vector'),'endpoint exact free export equals numerical finalmp export')
            result=verify_endpoint(license,endpoint,deadline=deadline,max_operations=remaining_ops,max_cells=remaining_cells,max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_endpoint_bytes);account('endpoint_check',endpoint,result);endpoint_checked=True
        else:
            require(endpoint.get('complete')is False,'strict incomplete endpoint');bytes_total+=len(encoded(endpoint));checks['endpoint_check']=None
    else:checks['endpoint_check']=None
    operations=max_operations-remaining_ops;cells=max_cells-remaining_cells
    return dict(verified=True,complete=endpoint_checked,endpoint_verified=endpoint_checked,
                finite_candidate_feasible=checks['endpoint_check']['finite_candidate_feasible'] if endpoint_checked else None,
                parent_license_summary=license.summary,**checks,
                proposal_history_only=True,gradient_or_merit_certified=False,full_elimination_replayed=False,
                audit_operations=operations,audit_cells=cells,
                independent_audit_work_reserve=operations+bytes_total+license.source['source_cells']+1,**FLAGS)
