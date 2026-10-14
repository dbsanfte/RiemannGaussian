"""Independent balanced proposal records and full exact finite endpoints.

Numerical model, simplex and descent checks establish record consistency only.
Published chart licenses and exact original equations/cones decide an endpoint;
no numerical gradient, column norm, convergence or global bound is certified.
"""
from fractions import Fraction as F
from pathlib import Path
import check_primitive_state_cone_jacobi_search as J

EXACT=J.EXACT
require=J.require
encoded=J.encoded
digest=J.digest
FLAGS=dict(J.FLAGS,model_optimality_certified=False,block_gradients_certified=False)
CACHE=J.CACHE;BASIS=J.BASIS;PROJECTION=J.PROJECTION
CHART_PARENT=J.CHART_PARENT
BASE_PARENT=J.PARENT
PARENT='cancellation-arithmetic-results/primitive-state-cone-jacobi-search-001'
MANIFEST='cancellation-arithmetic-results/publication-020/manifest.json'
REPORT='cancellation-arithmetic-results/publication-020/report.json'
_TOKEN=object()
SEED='base publication018 exact free vector plus reused D times publication020 final_z_mp; one warm seed; no clipping or rerounding'
SCALING=dict(J.SCALING,reused_publication020_records=True,new_column_responses=0)
SEARCH=dict(power_steps=8,gradient_iterations=96,armijo_trials=3,armijo_coefficient='1/8',step_min_binary_exponent=-900,step_max_binary_exponent=900,power_operator='sum of normalized block quadratic curvature operators',positive_dyadic_cone_jacobi=True,initial_step='clamped reciprocal of eight-step weighted power estimate',native_eigh_work_coefficient=96,iteration_budget_policy='reserve three trials and three accepted block adjoints before iteration',model_recomputed_each_trial=True)
MODEL=dict(block_order=['scalar','C','H'],penalty='half squared cone distance',objective='max(p_i/b_i)',normalizer_floor='1/1099511627776',normalizer_rule='max(exact exported initial numerical penalty, floor); fixed throughout',dual='r dot lambda - alpha/2 * norm(sum lambda_i*g_i)^2',faces=[[0],[1],[2],[0,1],[0,2],[1,2],[0,1,2]],simplex_dyadic_bits=240,simplex_rounding='edge floor t; interior floor first two; exact complement',interior_relative_determinant_tolerance='1/1461501637330902918203684832716283019655932542976',model_gap_relative_tolerance='1e-40',model_gap_scale='max(1,max abs r,max abs model scores,alpha*aggregate_gradient_squared_norm)',model_inconsistency_policy='UNKNOWN; no retry',near_singular_policy='omit interior as numerical proposal; all boundary faces remain; no rank claim',tie_rule='first face in declared order after quantization and rescoring')
PRECISION=dict(J.PRECISION,model_arithmetic='fixed80decimaldigits',warm_increment_exactly_represented=True)
SCHEMA='primitive-state-balanced-cone-search-v1'

class _EndpointLicense:
    def __init__(self,token,jacobi,summary,warm_vector,initial_z,scales,norms,warm_endpoint,warm_proposal,bindings):
        require(token is _TOKEN,'license issued only by immutable published evidence validation')
        self.jacobi_license=jacobi;self.source=jacobi.source;self.summary=summary
        self.parent_vector=jacobi.parent_vector;self.parent_endpoint=jacobi.parent_endpoint
        self.warm_vector=warm_vector;self.initial_z=initial_z;self.scales=scales
        self.norm_receipt=norms;self.warm_endpoint=warm_endpoint;self.warm_proposal=warm_proposal
        self.free=jacobi.free;self.pivots=jacobi.pivots;self.bindings=bindings
        self.cache=jacobi.cache;self.basis=jacobi.basis;self.projection=jacobi.projection;self.parent_restoration=jacobi.parent_restoration


def load_verified_license(root,expected_file_bindings,*,deadline=None,max_operations=50000000,max_cells=60000000,max_coefficient_bits=4096):
    root=Path(root).resolve();jacobi=J.load_verified_license(root,expected_file_bindings,deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    budget=EXACT.EXACT._Budget(deadline,max_operations-jacobi.summary['audit_operations'],max_cells-jacobi.summary['audit_cells'],max_coefficient_bits)
    names=['independent_verification.json','receipt.json','jobs/map.json','jobs/norms.json','jobs/proposal.json','jobs/endpoint.json','jobs/check.json','jobs/search-job.json']
    needed={MANIFEST,REPORT,*[PARENT+'/'+n for n in names]}
    require(needed<=set(expected_file_bindings),'complete immutable publication020 warm endpoint/scale bindings')
    manifest=J.OLD._read(root,MANIFEST,budget);files=manifest.get('files');require(type(files)is dict,'complete warm publication inventory')
    for name in needed-{MANIFEST}:require(files.get(name)==expected_file_bindings[name],'published warm binding '+name)
    require(files.get(J.MANIFEST)==expected_file_bindings[J.MANIFEST],'same immutable publication018 base seed')
    report=J.OLD._read(root,REPORT,budget);review=J.OLD._read(root,PARENT+'/independent_verification.json',budget);receipt=J.OLD._read(root,PARENT+'/receipt.json',budget,65536)
    check=J.OLD._read(root,PARENT+'/jobs/check.json',budget,65536);job=J.OLD._read(root,PARENT+'/jobs/search-job.json',budget,65536)
    warm=J.OLD._read(root,PARENT+'/jobs/endpoint.json',budget,1048576);proposal=J.OLD._read(root,PARENT+'/jobs/proposal.json',budget,8388608);norms=J.OLD._read(root,PARENT+'/jobs/norms.json',budget,2097152)
    require(report.get('schema')==20 and report.get('endpoint_available')is True and review.get('all_passed')is True and review.get('schema')=='primitive-state-cone-jacobi-search-independent-review-v1','completed independently verified publication020 warm endpoint')
    require(report.get('independent_receipt_sha256')==expected_file_bindings[PARENT+'/independent_verification.json'] and report.get('terminal_receipt_sha256')==expected_file_bindings[PARENT+'/receipt.json'],'published warm independent/terminal bindings')
    require(check==review.get('search_check') and check.get('complete')is True and check.get('endpoint_verified')is True and job.get('status')=='endpoint_verified' and job.get('endpoint_verified')is True and review.get('job',{}).get('endpoint_verified')is True,'complete exact warm endpoint and transport')
    require(check['endpoint_check'].get('exact_candidate_checks',{}).get('equality_complete')is True and check['endpoint_check']['exact_candidate_checks'].get('equality_mismatch_count')==0,'warm exact original affine identity independently verified')
    require(warm.get('complete')is True and proposal.get('complete')is True and proposal.get('status')=='proposed' and warm.get('normalized_basis_hash')==jacobi.summary['normalized_basis_hash'] and warm.get('free_indices')==jacobi.free,'complete warm proposal/source chart')
    candidate_hash=digest(warm.get('candidate_original_vector'));require(candidate_hash==warm.get('candidate_hash')==report.get('candidate_hash')==check['endpoint_check'].get('candidate_hash'),'full exact warm candidate hash')
    for n in names:
        if n.startswith('jobs/'):require(receipt.get('files_sha256',{}).get(n)==expected_file_bindings[PARENT+'/'+n],'complete warm terminal artifact '+n)
    stems={'protocol','source_seal','input','seal','tests','execution','receipt'};require(set(review.get('input_sha256',{}))==stems,'complete warm stem-only independent review bindings')
    for stem,h in review['input_sha256'].items():require(J.OLD._sha(root,PARENT+'/'+stem+'.json',budget)==h,'warm review input '+stem)
    # Positive scales are independently checked from already-published records;
    # no homogeneous response or numerical map is recomputed.
    scaling=J.verify_scaling(jacobi,norms,deadline=deadline,max_operations=max_operations-jacobi.summary['audit_operations']-budget.operations,max_cells=max_cells-jacobi.summary['audit_cells']-budget.cells)
    budget.charge(scaling['audit_operations'],cells=scaling['audit_cells']);require(scaling['complete'],'all reused positive scales complete')
    require(proposal.get('norm_records_hash')==norms['records_hash']==warm.get('norm_records_hash') and proposal.get('seed_endpoint_hash')==digest(jacobi.parent_endpoint)==warm.get('seed_endpoint_hash'),'same exact base and scale-record bindings')
    z=proposal.get('final_z_mp');require(type(z)is list and len(z)==len(jacobi.free),'complete269-bit warm increment coordinates')
    initial_z=[J.mp_fraction(q,budget)for q in z];scales=[EXACT.rational(r['scale'],budget)for r in norms['records']]
    free=[budget.rational(jacobi.parent_vector[i]+budget.rational(d*v))for i,d,v in zip(jacobi.free,scales,initial_z)]
    require(warm.get('final_free_vector')==proposal.get('final_free_vector')==list(map(str,free)),'exact535-bit warm free seed equals unrounded f018+D*z0')
    texts=warm.get('final_projected_vector');require(type(texts)is list and len(texts)==len(jacobi.parent_vector),'complete exact warm projected endpoint')
    vector=[EXACT.rational(q,budget)for q in texts];require([vector[i]for i in jacobi.free]==free,'warm free and projected endpoint agree')
    hashes={}
    for name,data in [('base_endpoint_hash',jacobi.parent_endpoint),('warm_endpoint_hash',warm),('warm_proposal_hash',proposal)]:
        payload=encoded(data);budget.charge(len(payload)//64+1,cells=len(payload)//64+1);hashes[name]=digest(data)
    summary=dict(jacobi.summary,**hashes,publication='publication-020',manifest_sha256=expected_file_bindings[MANIFEST],base018_candidate_hash=jacobi.summary['parent_candidate_hash'],base018_free_hash=jacobi.summary['parent_free_hash'],warm_candidate_hash=candidate_hash,warm_projected_hash=digest(texts),warm_free_hash=digest(warm['final_free_vector']),warm_z_hash=digest(z),norm_records_hash=norms['records_hash'],warm_endpoint_sha256=expected_file_bindings[PARENT+'/jobs/endpoint.json'],warm_review_sha256=expected_file_bindings[PARENT+'/independent_verification.json'],audit_operations=jacobi.summary['audit_operations']+budget.operations,audit_cells=jacobi.summary['audit_cells']+budget.cells)
    return _EndpointLicense(_TOKEN,jacobi,summary,vector,initial_z,scales,norms,warm,proposal,dict(expected_file_bindings))

mp_fraction=J.mp_fraction
_near=J._near


def _vector(records,n,budget):
    require(type(records)is list and len(records)==n,'complete finite coordinate exports')
    return [mp_fraction(q,budget)for q in records]


def _dot(a,b,budget):
    require(len(a)==len(b),'consistent dot-product dimensions')
    out=F(0)
    for x,y in zip(a,b):out=budget.rational(out+budget.rational(x*y));budget.charge(2,cells=2)
    return out


def _block_metrics(penalties,normalizers,budget):
    require(type(penalties)is list and len(penalties)==3,'exactly three numerical cone blocks')
    values=[mp_fraction(q,budget)for q in penalties];require(all(q>=0 for q in values),'nonnegative finite exported numerical penalties')
    return values,[budget.rational(q/b)for q,b in zip(values,normalizers)]


def _simplex(weights,budget):
    require(type(weights)is list and len(weights)==3,'three explicit simplex weights')
    values=[EXACT.rational(q,budget)for q in weights]
    require(all(v>=0 and v<=1 and (v*(1<<240)).denominator==1 for v in values) and sum(values,F(0))==1,'nonnegative exact240-bit dyadic simplex partition')
    return values


def verify_simplex_model(model,r,gradients,alpha,budget,*,allow_inconsistent=False):
    """Recompute finite-record algebra; this does not certify true gradients/QP."""
    require(type(model)is dict and len(r)==len(gradients)==3 and alpha>0,'three-block positive-step model')
    n=len(gradients[0]);require(all(len(g)==n for g in gradients),'same complete free-coordinate gradient dimensions')
    gram_rows=model.get('gram');require(type(gram_rows)is list and len(gram_rows)==3,'complete finite Gram export')
    gram=[_vector(row,3,budget)for row in gram_rows]
    actual=[[_dot(a,b,budget)for b in gradients]for a in gradients]
    require(all(_near(gram[i][j],actual[i][j],budget)for i in range(3)for j in range(3)),'Gram entries agree with explicit finite block gradients')
    candidates=model.get('candidates');edges=model.get('edge_data');interior=model.get('interior')
    require(type(candidates)is list and 6<=len(candidates)<=7 and type(edges)is list and len(edges)==3 and type(interior)is dict,'all seven declared face decisions retained')
    expected_weights=[]
    for i in range(3):expected_weights.append([F(int(i==j))for j in range(3)])
    for item,(i,j)in zip(edges,((0,1),(0,2),(1,2))):
        require(type(item)is dict and item.get('face')==[i,j],'ordered three edge model records')
        den=mp_fraction(item.get('denominator'),budget);slope=mp_fraction(item.get('slope'),budget);t=mp_fraction(item.get('unquantized_t'),budget)
        require(den>=0 and _near(den,gram[i][i]-2*gram[i][j]+gram[j][j],budget) and _near(slope,(r[i]-r[j])/alpha-(gram[j][i]-gram[j][j]),budget),'finite edge curvature and slope algebra')
        expected=max(F(0),min(F(1),slope/den))if den else F(int(slope>0))
        require(0<=t<=1 and _near(t,expected,budget),'clamped finite edge maximizer')
        scaled=t*(1<<240);q=F(scaled.numerator//scaled.denominator,1<<240);weights=[F(0)]*3;weights[i]=q;weights[j]=1-q;expected_weights.append(weights)
    abc=_vector(interior.get('difference_gram'),3,budget);a,b,c=abc
    require(a>=0 and c>=0 and all(_near(q,v,budget)for q,v in zip(abc,(gram[0][0]-2*gram[0][2]+gram[2][2],gram[0][1]-gram[0][2]-gram[1][2]+gram[2][2],gram[1][1]-2*gram[1][2]+gram[2][2]))),'finite difference Gram algebra')
    det=mp_fraction(interior.get('determinant'),budget);tol=mp_fraction(interior.get('determinant_tolerance'),budget)
    require(tol>=0 and _near(det,a*c-b*b,budget) and _near(tol,F(1,1<<160)*max(abs(a*c),abs(b*b)),budget) and det>=-tol,'fixed scale-aware numerical interior determinant policy')
    disposition=interior.get('disposition')
    if det<=tol:require(disposition=='near_singular_numerical_boundary_only' and len(candidates)==6,'near-singular numerical omission, no exact rank claim')
    else:
        rhs=_vector(interior.get('rhs'),2,budget);u,v=rhs
        require(_near(u,(r[0]-r[2])/alpha-(gram[0][2]-gram[2][2]),budget) and _near(v,(r[1]-r[2])/alpha-(gram[1][2]-gram[2][2]),budget),'finite interior stationarity RHS')
        raw=_vector(interior.get('unquantized_lambda'),2,budget);l0,l1=raw
        require(_near(l0,(c*u-b*v)/det,budget) and _near(l1,(a*v-b*u)/det,budget),'finite interior two-by-two solve consistency')
        inside=l0>=0 and l1>=0 and (l0+l1<=1 or _near(l0+l1,F(1),budget))
        if disposition=='included':
            require(inside and len(candidates)==7,'interior is included only within rounded simplex')
            q=[]
            for x in raw:
                scaled=x*(1<<240);q.append(F(scaled.numerator//scaled.denominator,1<<240))
            expected_weights.append([q[0],q[1],1-q[0]-q[1]])
        else:require(disposition=='outside_simplex' and (l0<0 or l1<0 or l0+l1>1) and len(candidates)==6,'interior outside simplex is explicitly omitted')
    duals=[];weights_list=[]
    for index,(item,expected)in enumerate(zip(candidates,expected_weights)):
        require(type(item)is dict and item.get('face')==MODEL['faces'][index],'fixed ordered face enumeration')
        weights=_simplex(item.get('lambda_vector'),budget);require(weights==expected,'exact face-preserving dyadic quantization')
        dual=mp_fraction(item.get('dual'),budget);linear=sum((w*v for w,v in zip(weights,r)),F(0));qform=sum((weights[i]*gram[i][j]*weights[j]for i in range(3)for j in range(3)),F(0));budget.charge(60,cells=12)
        # Binary269 products may cancel after expansion. Bound their rounding
        # against the absolute expanded terms, never certify the true QP.
        dual_scale=max(F(1),sum((abs(w*v)for w,v in zip(weights,r)),F(0))+abs(alpha)*sum((abs(weights[i]*gram[i][j]*weights[j])for i in range(3)for j in range(3)),F(0))/2)
        budget.charge(45,cells=12);require(abs(dual-(linear-alpha*qform/2))<=F(1,1<<255)*dual_scale,'finite simplex dual rescoring within expanded binary269 rounding bound')
        duals.append(dual);weights_list.append(weights)
    best=max(range(len(duals)),key=lambda i:duals[i]);require(type(model.get('selected_candidate'))is int and model['selected_candidate']==best,'best rescored candidate with first-face tie rule')
    weights=_simplex(model.get('lambda_vector'),budget);require(weights==weights_list[best] and mp_fraction(model.get('dual'),budget)==duals[best],'selected weights/dual bind declared candidate')
    aggregate=[sum((weights[i]*gradients[i][j]for i in range(3)),F(0))for j in range(n)];budget.charge(8*n,cells=4*n)
    direction=_vector(model.get('direction'),n,budget);require(all(_near(d,-alpha*g,budget)for d,g in zip(direction,aggregate)),'direction uses scaled z gradient and selected exact simplex')
    norm2=mp_fraction(model.get('direction_squared_norm'),budget);gnorm2=mp_fraction(model.get('aggregate_gradient_squared_norm'),budget)
    require(norm2>=0 and gnorm2>=0 and _near(norm2,_dot(direction,direction,budget),budget) and _near(gnorm2,_dot(aggregate,aggregate,budget),budget),'explicit direction and aggregate gradient squared norms')
    scores=_vector(model.get('model_scores'),3,budget)
    require(all(_near(q,ri+_dot(g,direction,budget),budget)for q,ri,g in zip(scores,r,gradients)),'finite model scores agree with direction')
    average=sum((w*q for w,q in zip(weights,scores)),F(0));gap=max(scores)-average
    scale=max(F(1),*map(abs,r),*map(abs,scores),alpha*gnorm2);tolerance=scale/F(10**40)
    reported_gap=mp_fraction(model.get('model_gap'),budget);reported_scale=mp_fraction(model.get('model_gap_scale'),budget);reported_tol=mp_fraction(model.get('model_gap_tolerance'),budget)
    require(_near(reported_gap,gap,budget) and _near(reported_scale,scale,budget) and _near(reported_tol,tolerance,budget) and model.get('model_consistent')is (abs(reported_gap)<=reported_tol),'fixed model-gap diagnostics recomputed from finite exports')
    consistent=model['model_consistent']
    require(consistent or allow_inconsistent,'failed numerical model is retained only for UNKNOWN diagnostics')
    if consistent:require(gap<=tolerance+F(1,1<<255)*max(F(1),scale),'bounded decoded model-gap consistency')
    active=max((abs(scores[i]-average)for i in range(3)if weights[i]),default=F(0));inactive=max([F(0),*[scores[i]-average for i in range(3)if not weights[i]]])
    require(_near(mp_fraction(model.get('active_KKT_residual'),budget),active,budget) and _near(mp_fraction(model.get('inactive_KKT_violation'),budget),inactive,budget),'finite active/inactive KKT diagnostics')
    return direction,norm2,dict(consistent=consistent,selected_face=MODEL['faces'][best],model_gap=str(gap),model_gap_relative_tolerance='1e-40',model_optimality_certified=False,block_gradients_certified=False)


def iteration_work_reserve(license):
    E=license.summary['sparse_map_entries'];w=len(license.parent_vector);n=len(license.free);p=len(license.pivots)
    shape=license.source['shape'];sc=license.source['offset']-2*shape[1];pairs=120
    forward=4*E+2*p+w+2*n
    metrics=2*96*15**3+2*pairs+5*pairs+sc+3*(sc+450)+6*w
    adjoints=3*(2*E+w+n);model=200*n+8192
    return 3*(forward+metrics+model+4*n+16384)+adjoints+4096*n+131072


def _verify_budget_stop(license,proposal,budget,max_trace_bytes):
    stop=proposal.get('budget_stop');require(type(stop)is dict,'explicit complete last-point balanced budget stop')
    keys=('before_iteration','operations','max_operations','remaining_operations','worst_iteration_work_reserve','finalization_work_reserve','trace_retained_bytes','max_trace_bytes','worst_iteration_trace_bytes','finalization_trace_bytes')
    require(set(stop)==set(keys)|{'resource'} and all(type(stop[k])is int and stop[k]>=0 for k in keys),'strict finite budget stop counters')
    n=len(license.free);work=iteration_work_reserve(license);tail=max_trace_bytes+20000*n+131072;perstep=65536+12*96*n;final=8192+3000*n
    require(stop['before_iteration']==len(proposal['iterations'])<96 and stop['max_operations']==130000000 and stop['operations']<=proposal['counts']['operations']<=130000000 and stop['remaining_operations']==130000000-stop['operations'],'budget stop before next full iteration')
    require(stop['worst_iteration_work_reserve']==work and stop['finalization_work_reserve']==tail and stop['max_trace_bytes']==max_trace_bytes and stop['worst_iteration_trace_bytes']==perstep and stop['finalization_trace_bytes']==final,'independently reconstructed fixed step/export reserves')
    keys=('schema','status','complete','precision','search','model','scaling','seed_rule','normalized_basis_hash','base_endpoint_hash','warm_endpoint_hash','warm_proposal_hash','norm_records_hash','warm_setup_counts','initial_free_vector','scale_vector','calibration','initial_z_mp','initial_block_penalties','normalizers','initial_normalized_blocks','initial_objective','initial_merit_details','power_trace','initial_step')
    initial={k:proposal[k]for k in keys};initial.update(status='unknown',complete=False,iterations=[],final_free_vector=None,**FLAGS)
    retained=len(encoded(initial))+sum(len(encoded(item))+1 for item in proposal['iterations']);budget.charge(retained//64+len(proposal['iterations'])+1)
    require(stop['trace_retained_bytes']==retained,'exact retained complete-prefix serialization proxy')
    op_short=stop['remaining_operations']<work+tail;byte_short=max_trace_bytes-retained<perstep+final
    require(stop['resource']=='operations' and op_short or stop['resource']=='trace_bytes' and not op_short and byte_short,'actual bounded-work or byte shortfall stops before new model')


def verify_proposal_trace(license,proposal,*,deadline=None,max_operations=100000000,max_cells=60000000,max_coefficient_bits=4096,max_trace_bytes=16777216):
    require(type(license)is _EndpointLicense,'hash-issued publication020 warm endpoint license')
    require(type(max_trace_bytes)is int and 0<max_trace_bytes<=16777216,'bounded balanced trace byte cap')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(proposal)is dict and proposal.get('schema')==SCHEMA,'known balanced finite numerical proposal');payload=encoded(proposal);require(len(payload)<=max_trace_bytes,'bounded entire balanced history');budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    for k in FLAGS:require(proposal.get(k)is False,'no balanced gradient/model/cone/global theorem claim')
    require(proposal.get('precision')==PRECISION and proposal.get('search')==SEARCH and proposal.get('model')==MODEL and proposal.get('scaling')==SCALING and proposal.get('seed_rule')==SEED,'fixed balanced mixed-precision numerical policy')
    require(proposal.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and proposal.get('base_endpoint_hash')==license.summary['base_endpoint_hash'] and proposal.get('warm_endpoint_hash')==license.summary['warm_endpoint_hash'] and proposal.get('warm_proposal_hash')==license.summary['warm_proposal_hash'] and proposal.get('norm_records_hash')==license.norm_receipt['records_hash'],'same exact chart/base/warm endpoint and reused positive diagonal')
    require(proposal.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free] and proposal.get('scale_vector')==list(map(str,license.scales)),'unchanged exact018 base center and all positive scales')
    setup=proposal.get('warm_setup_counts');require(type(setup)is dict and set(setup)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in setup.values()) and setup['operations']<=5000000 and setup['peak_live_cells']<=4000000 and setup['fill_cells']<=20000000,'all reused warm setup fits one5m allocation')
    status=proposal.get('status');require(status in ('proposed','unknown') and proposal.get('complete')is (status=='proposed'),'strict balanced proposal completion')
    n=len(license.free);current=None;initial_error=None
    if 'initial_z_mp'in proposal:
        current=_vector(proposal['initial_z_mp'],n,budget);require(current==license.initial_z,'same exact269-bit publication020 warm increment; no center reround')
    calibration=proposal.get('calibration')
    if calibration is not None:
        require(type(calibration)is dict and calibration.get('passed')is True and calibration.get('tolerance')=='1e-40' and calibration.get('reference')=='exact publication020 projected endpoint','warm affine calibration uses actual020 endpoint')
        pair=mp_fraction(calibration.get('adjoint_pairing_relative_error'),budget);require(0<=pair<=F(1,10**40),'bounded reported affine adjoint pairing')
        actual=_vector(calibration.get('initial_forward_mp'),len(license.warm_vector),budget)
        initial_error=max((abs(q-r)/max(F(1),abs(r))for q,r in zip(actual,license.warm_vector)),default=F(0));budget.charge(4*len(actual))
        require(initial_error<=F(1,10**40) and calibration.get('initial_exact_reference_relative_error')==str(initial_error),'independently recomputed exact warm-reference backward drift')
    power=proposal.get('power_trace');iterations=proposal.get('iterations');require(type(power)is list and len(power)<=8 and type(iterations)is list and len(iterations)<=96,'bounded weighted power and balanced iterations')
    normalizers=None;r=None;value=None;native_calls=0
    if 'initial_block_penalties'in proposal:
        require(type(proposal.get('normalizers'))is list and len(proposal['normalizers'])==3,'three frozen positive block normalizers')
        normalizers=[EXACT.rational(q,budget)for q in proposal['normalizers']];require(all(q>0 for q in normalizers),'strict positive normalizers')
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
            step=mp_fraction(trial.get('step'),budget);require(step==alpha/F(1<<trial_index) and step>0,'fixed halving step trials')
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
            if newvalue<=threshold:passed=True;current=z;r=rnew;value=newvalue;alpha=step;accepted+=1
        require(item['accepted']is passed,'accepted iteration equals first passed trial')
        if not passed and not stationary:
            if status=='proposed' or index<len(iterations)-1:require(len(trials)==3,'failed line search exhausts all three models')
            terminated=True
    if 'last_finite_z_mp'in proposal:require(current is not None and _vector(proposal['last_finite_z_mp'],n,budget)==current,'retained UNKNOWN warm increment is last complete point')
    counts=proposal.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict proposal work/live/fill counters')
    require(counts['operations']>=native_calls*2*96*15**3,'all recorded repeated native eigensolves charged')
    if status=='proposed':
        require(counts['operations']<=130000000 and counts['peak_live_cells']<=4000000 and counts['fill_cells']<=20000000 and current is not None and value is not None and calibration is not None and initial_error is not None,'complete bounded calibrated balanced proposal')
        final=_vector(proposal.get('final_z_mp'),n,budget);require(final==current,'last complete accepted or stationary warm increment')
        free=[budget.rational(license.parent_vector[i]+budget.rational(D*z))for i,D,z in zip(license.free,license.scales,final)]
        require(proposal.get('final_free_vector')==list(map(str,free)) and mp_fraction(proposal.get('final_objective'),budget)==value and _vector(proposal.get('final_normalized_blocks'),3,budget)==r,'unrounded exact final f018+D*z and continuous final max objective')
        stop=proposal.get('stop_reason');require(stop in ('iteration_limit','budget_stop','line_search_failed','numerical_model_stationarity','zero_initial_numerical_defect'),'declared proposal-only stopping reason')
        if stop=='zero_initial_numerical_defect':require(value==0 and not iterations and not power,'observed zero initial defect stops without a model')
        else:
            require(len(power)==8 or zero_power,'complete weighted power estimate before descent')
            if stop=='iteration_limit':require(len(iterations)==96 and iterations[-1]['accepted']is True,'fixed96iteration endpoint')
            elif stop=='budget_stop':_verify_budget_stop(license,proposal,budget,max_trace_bytes)
            elif stop=='numerical_model_stationarity':require(stationary,'actual numerical zero-direction model stop')
            else:require(iterations and not iterations[-1]['accepted'] and len(iterations[-1]['trials'])==3 and not stationary,'actual exhausted three-trial balanced line search')
    else:require(type(proposal.get('reason'))is str and bool(proposal['reason']),'explicit incomplete numerical proposal cause')
    return dict(verified=True,complete=status=='proposed',proposal_history_only=True,gradient_or_merit_certified=False,intermediate_iterates_exact=False,block_normalizers_verified_from_exported_penalties=normalizers is not None,actual_initial_exact_reference_relative_error=str(initial_error)if initial_error is not None else None,power_iterations=len(power),gradient_iterations=len(iterations),accepted_iterations=accepted,finite_armijo_trials=finite_trials,native_eigensolve_calls=2*native_calls,simplex_models_checked=model_calls,maximum_recorded_model_gap=str(max_gap),native_PSD_projection_precision='binary64',affine_map_precision_decimal_digits=80,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)


def _counts(receipt,budget,cap):
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict bounded phase resource counters')
    require(counts['operations']<=cap and counts['peak_live_cells']<=4000000 and counts['fill_cells']<=20000000,'complete bounded phase producer')
    return counts


def verify_map_receipt(license,receipt,*,deadline=None,max_operations=5000000,max_cells=60000000,max_map_bytes=131072):
    require(type(license)is _EndpointLicense and type(receipt)is dict,'hash-issued source and explicit map metadata')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,4096);data=encoded(receipt);require(len(data)<=max_map_bytes<=131072,'bounded map metadata');budget.charge(len(data)//64+1,cells=len(data)//64+1)
    for k in FLAGS:require(receipt.get(k)is False,'map metadata cannot certify norms, gradients or a theorem')
    require(receipt.get('schema')=='primitive-state-balanced-cone-map-v1' and receipt.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and receipt.get('retained_indices')==license.summary['retained_indices'] and receipt.get('pivot_columns')==sorted(license.pivots) and receipt.get('free_indices')==license.free,'exact licensed source/rank/pivot chart binding')
    require(receipt.get('precision')==PRECISION and receipt.get('seed_rule')==SEED and receipt.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free],'map retains exact018 center, not535-bit warm free reround')
    require(receipt.get('base_endpoint_hash')==license.summary['base_endpoint_hash']==receipt.get('seed_endpoint_hash') and receipt.get('warm_endpoint_hash')==license.summary['warm_endpoint_hash'] and receipt.get('warm_projected_hash')==license.summary['warm_projected_hash'],'map binds exact018 base and exact020 warm reference')
    require(type(receipt.get('source_cells'))is int and receipt['source_cells']==license.source['source_cells'] and receipt.get('sparse_map_entries')==license.summary['sparse_map_entries'],'licensed source and sparse-map resource dimensions')
    _counts(receipt,budget,50000000)
    return dict(verified=True,published_chart_license_match=True,full_elimination_replayed=False,high_precision_map_independently_rebuilt=False,normalized_basis_hash=license.summary['normalized_basis_hash'],audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)


def verify_warm_receipt(license,receipt,*,deadline=None,max_operations=5000000,max_cells=60000000,max_warm_bytes=262144):
    require(type(license)is _EndpointLicense and type(receipt)is dict,'hash-issued warm source and explicit setup metadata')
    budget=EXACT.EXACT._Budget(deadline,max_operations,max_cells,4096);data=encoded(receipt);require(len(data)<=max_warm_bytes<=262144,'bounded reused scale/warm metadata');budget.charge(len(data)//64+1,cells=len(data)//64+1)
    for k in FLAGS:require(receipt.get(k)is False,'warm metadata carries no numerical theorem')
    require(receipt.get('schema')=='primitive-state-balanced-cone-warm-v1' and receipt.get('complete')is True and receipt.get('normalized_basis_hash')==license.summary['normalized_basis_hash'] and receipt.get('precision')==PRECISION and receipt.get('scaling')==SCALING and receipt.get('seed_rule')==SEED,'one complete fixed warm setup')
    for name in ('base_endpoint_hash','warm_endpoint_hash','warm_proposal_hash','norm_records_hash'):require(receipt.get(name)==license.summary[name],'published warm/source binding '+name)
    require(type(receipt.get('new_column_responses'))is int and receipt['new_column_responses']==0,'reuse all scales with no norm-column rerun')
    require(receipt.get('initial_free_vector')==[str(license.parent_vector[i])for i in license.free] and receipt.get('scale_vector')==list(map(str,license.scales)) and receipt.get('warm_free_vector')==[str(license.warm_vector[i])for i in license.free],'full exact base/scales/warm free coordinates')
    z=_vector(receipt.get('initial_z_mp'),len(license.free),budget);require(z==license.initial_z,'complete exact269-bit warm increment')
    free=[budget.rational(license.parent_vector[i]+budget.rational(D*v))for i,D,v in zip(license.free,license.scales,z)]
    require(receipt['warm_free_vector']==list(map(str,free)),'warm535-bit free seed equals exact unrounded base+D*z')
    _counts(receipt,budget,5000000)
    return dict(verified=True,exact_warm_seed_binding=True,new_column_responses=0,full_elimination_replayed=False,audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(data)+1,**FLAGS)


def verify_endpoint(license,endpoint,**kwargs):
    require(type(license)is _EndpointLicense and type(endpoint)is dict,'hash-bound exact endpoint source')
    for k in FLAGS:require(endpoint.get(k)is False,'no endpoint model, gradient or global certification claim')
    for name in ('base_endpoint_hash','warm_endpoint_hash','warm_proposal_hash'):require(endpoint.get(name)==license.summary[name],'endpoint base/warm source binding '+name)
    require(endpoint.get('norm_records_hash')==license.norm_receipt['records_hash'],'endpoint uses same positive diagonal')
    return J.verify_endpoint(license.jacobi_license,endpoint,**kwargs)


def verify_search(license,mapreceipt,warmreceipt,proposal=None,endpoint=None,*,deadline=None,max_operations=100000000,max_cells=60000000,max_coefficient_bits=4096,max_map_bytes=131072,max_warm_bytes=262144,max_trace_bytes=16777216,max_endpoint_bytes=1048576,max_check_bytes=65536):
    require(type(license)is _EndpointLicense,'hash-issued source/chart/base/warm license required')
    require(type(max_operations)is int and 0<max_operations<=450000000 and type(max_cells)is int and 0<max_cells<=60000000 and type(max_coefficient_bits)is int and 0<max_coefficient_bits<=4096,'strict cumulative worker checker caps')
    for value,cap in ((max_map_bytes,131072),(max_warm_bytes,262144),(max_trace_bytes,16777216),(max_endpoint_bytes,1048576),(max_check_bytes,65536)):require(type(value)is int and 0<value<=cap,'strict individual artifact byte caps')
    remaining=max_operations;cells=max_cells;checks={};total_bytes=0
    def account(name,value,result):
        nonlocal remaining,cells,total_bytes
        checks[name]=result;remaining-=result['audit_operations'];cells-=result['audit_cells'];total_bytes+=len(encoded(value));require(remaining>=0 and cells>=0,'combined independent work/cell accounting')
    result=verify_map_receipt(license,mapreceipt,deadline=deadline,max_operations=remaining,max_cells=cells,max_map_bytes=max_map_bytes);account('map_check',mapreceipt,result)
    result=verify_warm_receipt(license,warmreceipt,deadline=deadline,max_operations=remaining,max_cells=cells,max_warm_bytes=max_warm_bytes);account('warm_check',warmreceipt,result)
    if proposal is not None:
        require(proposal.get('warm_setup_counts')==warmreceipt['counts'],'numerical trace binds complete5m warm setup resource counters')
        result=verify_proposal_trace(license,proposal,deadline=deadline,max_operations=remaining,max_cells=cells,max_coefficient_bits=max_coefficient_bits,max_trace_bytes=max_trace_bytes);account('proposal_check',proposal,result)
    else:checks['proposal_check']=None
    endpoint_checked=False
    if endpoint is not None:
        require(proposal is not None and type(endpoint)is dict and len(encoded(endpoint))<=max_endpoint_bytes,'bounded endpoint requires retained proposal')
        for k in FLAGS:require(endpoint.get(k)is False,'endpoint cannot claim a numerical theorem')
        if endpoint.get('complete')is True:
            require(proposal.get('complete')is True and endpoint.get('schema')=='primitive-state-balanced-cone-endpoint-v1' and endpoint.get('final_free_vector')==proposal.get('final_free_vector'),'exact endpoint follows complete final centered proposal')
            result=verify_endpoint(license,endpoint,deadline=deadline,max_operations=remaining,max_cells=cells,max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_endpoint_bytes);account('endpoint_check',endpoint,result);endpoint_checked=True
        else:
            require(endpoint.get('complete')is False and type(endpoint.get('reason'))is str,'explicit incomplete exact endpoint');size=len(encoded(endpoint));total_bytes+=size
            meter=EXACT.EXACT._Budget(deadline,remaining,cells,max_coefficient_bits);meter.charge(size//64+1,cells=size//64+1);remaining-=meter.operations;cells-=meter.cells;checks['endpoint_check']=None
    else:checks['endpoint_check']=None
    ops=max_operations-remaining;used_cells=max_cells-cells
    out=dict(verified=True,complete=endpoint_checked,endpoint_verified=endpoint_checked,finite_candidate_feasible=checks['endpoint_check']['finite_candidate_feasible']if endpoint_checked else None,proposal_history_only=True,gradient_or_merit_certified=False,full_elimination_replayed=False,parent_license_summary=license.summary,audit_operations=ops,audit_cells=used_cells,independent_audit_work_reserve=ops+total_bytes+license.source['source_cells']+1,**checks,**FLAGS)
    require(len(encoded(out))<=max_check_bytes,'bounded combined independent balanced result')
    return out
