"""Exact affine-response, conditional face and compression verification.

The completed publication028 chart is the prior finite-span premise. Saved029
rays are rational rank-one cone generators; their numerical origin is not a
proof premise. Geometry and a final separator are separate conclusions. No
source rebuild, elimination tape, eigensolver, LP replay or digests are used.
"""
from fractions import Fraction as F
import time
import math
import check_primitive_state_chart_dual_search as DIRECT

require=DIRECT.require
encoded=DIRECT.encoded
FLAGS=DIRECT.FLAGS
WIDTH=1224
SCHEMA='primitive-state-chart-dual-geometry-independent-check-v1'
GEOMETRY_SCHEMA='primitive-state-chart-dual-geometry-v1'


class Budget(DIRECT.EXACT.Budget):
    def __init__(self,deadline,max_operations=70000000,max_cells=6000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=70000000,'one shared70m geometry and certificate audit')
        super().__init__(deadline,max_operations,max_cells,20000000,max_bits)


def sparse(terms,allowed,b):
    require(type(terms)is list and len(terms)<=len(allowed),'bounded sparse exact coefficient list');row={};last=-1
    for term in terms:
        require(type(term)is list and len(term)==2,'explicit sparse term');j,text=term;require(type(j)is int and j in allowed and j>last,'unique ordered allowed coefficient index');last=j;q=b.rational(text);require(q!=0,'nonzero sparse coefficient');row[j]=q
    return row


def add_scaled(total,row,factor,b):
    if not factor:return
    b.charge(len(row))
    for j,q in row.items():
        product=q if factor==1 else -q if factor==-1 else b.mul(factor,q)
        value=b.add(total.get(j,F(0)),product)
        if value:total[j]=value
        else:total.pop(j,None)


def verify_forms(rows,pivots,free,records,b,*,resident=0):
    require(type(records)is list and len(records)==WIDTH,'complete1224 affine coordinate forms')
    forms=[];cells=0;allowed=set(free)|{WIDTH}
    for j,record in enumerate(records):
        require(type(record)is dict and set(record)=={'coordinate','constant','terms'}and type(record['coordinate'])is int and record['coordinate']==j,'each affine coordinate explicitly numbered')
        b.live(resident+cells+2*len(record['terms'])+3*WIDTH)
        terms=sparse(record['terms'],set(free),b);constant=b.rational(record['constant'])
        if constant:terms[WIDTH]=constant
        if j in free:require(terms=={j:F(1)},'every free coordinate is exactly its unit form')
        forms.append(terms);cells+=len(terms);b.live(resident+cells+2*WIDTH)
    for p,row in zip(pivots,rows):
        residual={};rhs=row.get(WIDTH,F(0))
        for j,q in row.items():
            if j!=WIDTH:add_scaled(residual,forms[j],q,b)
        if rhs:
            value=b.add(residual.get(WIDTH,F(0)),-rhs)
            if value:residual[WIDTH]=value
            else:residual.pop(WIDTH,None)
        require(not residual,'every normalized row identity in every free coefficient and constant')
        b.live(resident+cells+len(residual)+2*WIDTH)
    return forms,cells


def response_columns(forms,generators,b,*,resident=0):
    responses=[];cells=0
    for generator in generators:
        b.live(resident+cells+3*WIDTH)
        response={}
        for j,q in generator.items():add_scaled(response,forms[j],q,b)
        responses.append(response);cells+=len(response);b.live(resident+cells+3*WIDTH)
    return responses,cells


def line_key(row,b):
    require(bool(row),'nonzero response canonical line');b.charge(len(row)*max(1,len(row).bit_length()))
    ordered=sorted(row);first=row[ordered[0]]
    return tuple((j,b.div(row[j],first))for j in ordered),first


def response_geometry(responses,b):
    """All zero rays and all exact nonzero response lines, including constant."""
    classes=[];lookup={};zero=[];keys=[];firsts=[]
    for i,row in enumerate(responses):
        if not row:zero.append(i);keys.append(None);firsts.append(None);continue
        key,first=line_key(row,b);keys.append(key);firsts.append(first)
        if key not in lookup:lookup[key]=len(classes);classes.append(dict(representative=i,members=[],positive_indices=[],negative_indices=[]))
        group=classes[lookup[key]];factor=b.div(first,firsts[group['representative']]);group['members'].append(dict(ray_index=i,factor=str(factor)));group['positive_indices'if factor>0 else'negative_indices'].append(i)
    exposures=[]
    for i in zero:exposures.append(dict(ray_index=i,kind='zero_response',combination=[dict(ray_index=i,weight='1')]))
    for group in classes:
        positive=group['positive_indices'];negative=group['negative_indices']
        if not positive or not negative:continue
        factors={m['ray_index']:b.rational(m['factor'])for m in group['members']}
        for member in group['members']:
            i=member['ray_index'];factor=factors[i];other=negative[0]if factor>0 else positive[0]
            a=F(1);c=-b.div(factor,factors[other]);total={};add_scaled(total,responses[i],a,b);add_scaled(total,responses[other],c,b);require(not total and a>0 and c>0,'positive exact opposite-line exposure')
            exposures.append(dict(ray_index=i,kind='opposite_line',combination=[dict(ray_index=i,weight=str(a)),dict(ray_index=other,weight=str(c))]))
    exposures.sort(key=lambda record:record['ray_index'])
    shortcut=next((i for i,row in enumerate(responses)if set(row)=={WIDTH}and row[WIDTH]<0),None)
    return zero,classes,exposures,keys,firsts,shortcut


def compressed_system(responses,free,keys,firsts,b):
    """Only positive column multiples; augmented row factors may have either sign."""
    representatives=[];mapping=[];seen={}
    for i,row in enumerate(responses):
        if not row:mapping.append(None);continue
        key=(keys[i],1 if firsts[i]>0 else -1)
        if key not in seen:seen[key]=i;representatives.append(i)
        rep=seen[key];factor=b.div(firsts[i],firsts[rep]);require(factor>0,'positive-only response column compression');mapping.append(dict(representative=rep,positive_factor=str(factor)))
    coordinates=free+[WIDTH];rowmap=[];rowreps=[];rowkeys={};firstvalues={};coefficient_rows={}
    for j in coordinates:
        row={k:responses[i][j]for k,i in enumerate(representatives)if j in responses[i]};b.charge(len(representatives))
        rhs=F(-1)if j==WIDTH else F(0)
        augmented=dict(row)
        if rhs:augmented[len(representatives)]=rhs
        coefficient_rows[j]=row
        if not augmented:rowmap.append(None);continue
        key,first=line_key(augmented,b)
        if key not in rowkeys:rowkeys[key]=j;rowreps.append(j);firstvalues[j]=first
        rep=rowkeys[key];factor=b.div(first,firstvalues[rep]);rowmap.append(dict(representative=rep,signed_factor=str(factor)))
    columns=[[[j,str(responses[i][j])]for j in rowreps if j in responses[i]]for i in representatives]
    rhs=[[j,'-1']for j in rowreps if j==WIDTH]
    return dict(column_representatives=representatives,column_map=mapping,row_representatives=rowreps,row_map=rowmap,compressed_columns=columns,compressed_rhs=rhs,row_keys=coordinates,column_lift='weight at representative, zero at all other original rays',row_target_included=True)


def kernel_basis(vectors,b):
    """Canonical RREF span of all exposed rational vector directions."""
    basis={}
    for vector in vectors:
        require(type(vector)is list and len(vector)==15,'complete exposed vector');row={}
        for j,text in enumerate(vector):
            q=b.rational(text)
            if q:row[j]=q
        for p in sorted(basis):
            if p in row:add_scaled(row,basis[p],-row[p],b)
        if not row:continue
        p=min(row);factor=row[p];basis[p]={j:b.div(q,factor)for j,q in sorted(row.items())}
    for p in sorted(basis,reverse=True):
        for earlier in sorted(q for q in basis if q<p):
            if p in basis[earlier]:add_scaled(basis[earlier],basis[p],-basis[earlier][p],b)
    return [[str(row.get(j,F(0)))for j in range(15)]for _,row in sorted(basis.items())]


def face_summary(records,exposures,b):
    exposed=[record['ray_index']for record in exposures];scalars=[];kernels=[]
    for i in exposed:
        ray=records[i]
        if ray['kind']=='scalar':scalars.append(ray['coordinate'])
    for block in('C','H'):
        indices=[i for i in exposed if records[i]['kind']=='rank_one'and records[i]['block']==block];basis=kernel_basis([records[i]['vector']for i in indices],b)
        kernels.append(dict(block=block,exposed_ray_indices=indices,rank=len(basis),basis_vectors=basis))
    return sorted(scalars),kernels

POLICY=dict(forms='complete1224 exact coordinate affine normal forms',column_compression='drop zero; merge only positive proportional columns; first ray representative',row_compression='drop zero augmented rows; merge signed proportional augmented rows including target',exposures='zero response or exact nonnegative two-ray opposite-line cancellation',exposure_scope='vanishing on every feasible point; no feasibility assertion',cost='unit L1 representative weights; positive common scaled-cost normalization',direct_route='first ray with no free response and negative constant',support='all strictly positive successful native variables; max=min(443,compressed rows)',max_native_iterations=10000,native_attempts=1,restoration_attempts=1)


def verify_geometry(chart,parent_review,rays,geometry,b,*,max_geometry_bytes=16777216):
    require(type(max_geometry_bytes)is int and 0<max_geometry_bytes<=16777216,'bounded geometry artifact')
    data=encoded(geometry)
    if len(data)>max_geometry_bytes:raise OverflowError('independent geometry byte cap')
    b.charge(2*(len(data)//64+1),cells=len(data)//64+1);DIRECT.scope_flags(geometry)
    require(geometry.get('schema')==GEOMETRY_SCHEMA and geometry.get('complete')is True and geometry.get('width')==WIDTH and geometry.get('policy')==POLICY,'known complete exact geometry policy')
    rows,pivots,free,source_cells=DIRECT.parse_chart(chart,parent_review,b);generators,generator_cells=DIRECT.parse_rays(rays,b)
    require(geometry.get('pivot_columns')==pivots and geometry.get('free_indices')==free,'same licensed782/442 chart partition')
    forms,form_cells=verify_forms(rows,pivots,free,geometry.get('forms'),b,resident=source_cells+generator_cells)
    responses,response_cells=response_columns(forms,generators,b,resident=source_cells+generator_cells+form_cells)
    records=geometry.get('responses');require(type(records)is list and len(records)==851,'all851 complete generator responses')
    for i,(row,record)in enumerate(zip(responses,records)):
        require(type(record)is dict and set(record)=={'ray_index','terms'}and type(record['ray_index'])is int and record['ray_index']==i,'explicit851 response numbering')
        require(sparse(record['terms'],set(free)|{WIDTH},b)==row,'every independently composed affine cone response')
    # Conservatively reserve forms, normalized line keys, row-key copies,
    # coefficient rows, compression output and transient sparse accumulators.
    b.live(2*source_cells+2*generator_cells+2*form_cells+12*response_cells+6*WIDTH+12*851)
    zero,classes,exposures,keys,firsts,negative=response_geometry(responses,b)
    require(geometry.get('zero_ray_indices')==zero and geometry.get('line_classes')==classes and geometry.get('exposures')==exposures,'complete zero and opposite-line classes with exact positive exposures')
    compression=compressed_system(responses,free,keys,firsts,b);require(geometry.get('compression')==compression,'complete exact positive columns and signed augmented-row compression')
    contradiction=[i for i in compression['row_representatives']if i==WIDTH and not any(any(j==i for j,_ in col)for col in compression['compressed_columns'])]
    require(geometry.get('negative_constant_ray')==negative and geometry.get('contradictory_compressed_rows')==contradiction,'first exact negative constant and retained contradictory search rows')
    forced,kernels=face_summary(rays['records'],exposures,b)
    require(geometry.get('forced_scalar_indices')==forced and geometry.get('kernel_spans')==kernels,'all exposed scalar zeros and canonical exact C/H kernel spans')
    b.live(source_cells+generator_cells+2*form_cells+4*response_cells+4*851+4*WIDTH+2*sum(len(col)for col in compression['compressed_columns']))
    summary=dict(verified=True,complete=True,rank=782,free_coordinates=442,geometry_verified=True,all_affine_forms_verified=True,all_generator_responses_verified=True,complete_exposure_classes_verified=True,exact_compression_verified=True,conditional_faces_only=True,primal_feasibility_certified=False,zero_ray_count=len(zero),exposed_ray_count=len(exposures),forced_scalar_indices=forced,kernel_spans=kernels,remaining_matrix_dimensions={record['block']:15-record['rank']for record in kernels},compressed_columns=len(compression['column_representatives']),compressed_rows=len(compression['row_representatives']),negative_constant_ray=negative,contradictory_compressed_rows=contradiction,old_elimination_replayed=False,new_eigensolves=0,**FLAGS)
    return summary,rows,pivots,free,generators,responses,compression


def verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,*,max_certificate_bytes=8388608):
    data=encoded(certificate)
    if len(data)>max_certificate_bytes:raise OverflowError('exact separator byte cap')
    b.charge(2*(len(data)//64+1));DIRECT.scope_flags(certificate)
    require(certificate.get('schema')==DIRECT.CERTIFICATE_SCHEMA and certificate.get('complete')is True and certificate.get('width')==WIDTH and certificate.get('exact_identity_verified')is True,'complete direct exact separator proposal')
    require(certificate.get('rays')==rays and certificate.get('pivot_columns')==pivots and certificate.get('free_indices')==free,'same saved851 rays and licensed chart')
    alpha=certificate.get('alpha');lambdas=certificate.get('lambda_vector');require(type(alpha)is list and len(alpha)==851 and type(lambdas)is list and len(lambdas)==782,'full exact ray and row weights')
    functional,pairing,active,multipliers=DIRECT.check_identity(rows,generators,alpha,lambdas,WIDTH,b)
    require(certificate.get('pairing')==str(pairing)and certificate.get('combined_functional')==list(map(str,functional)),'all1224 separator coordinates and pairing-1')
    return dict(schema=DIRECT.SCHEMA,verified=True,complete=True,status='FINITE_CONE_INFEASIBLE',finite_augmented_cone_infeasibility_certified=True,original_unlearned_cone_infeasibility_certified=False,pairing='-1',rank=782,free_coordinates=442,active_generators=active,nonzero_row_multipliers=multipliers,native_LP_replayed=False,native_eigenvectors_independently_verified=False,**FLAGS)


def verify_outcome(chart,parent_review,rays,geometry,outcome,*,deadline=None,max_operations=70000000,max_cells=6000000,max_bits=4096,max_geometry_bytes=16777216,max_certificate_bytes=8388608):
    require(type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded geometry search proposal')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        require(type(outcome)is dict and outcome.get('schema')=='primitive-state-chart-dual-geometry-search-v1'and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN'),'explicit geometry search disposition');DIRECT.scope_flags(outcome)
        for key in ('finite_augmented_cone_infeasibility_certified','primal_feasibility_certified'):
            if key in outcome:require(outcome[key]is False,'producer cannot certify '+key)
        data=encoded(outcome)
        if len(data)>max_certificate_bytes:raise OverflowError('bounded geometry outcome')
        b.charge(2*(len(data)//64+1));summary,rows,pivots,free,generators,responses,compression=verify_geometry(chart,parent_review,rays,geometry,b,max_geometry_bytes=max_geometry_bytes)
        certificate=outcome.get('certificate');check=None
        if outcome['status']=='CERTIFICATE_PROPOSED':
            require(outcome.get('geometry_complete')is True,'certificate follows complete geometry')
            check=verify_saved_certificate(certificate,rays,rows,pivots,free,generators,b,max_certificate_bytes=max_certificate_bytes)
            alpha=[b.rational(q)for q in certificate['alpha']]
            if summary['negative_constant_ray']is not None:
                index=summary['negative_constant_ray'];weight=b.div(F(-1),responses[index][WIDTH])
                require(outcome.get('route')=='negative_constant_ray'and outcome.get('native')is None and alpha==[weight if j==index else F(0)for j in range(851)],'first exact negative constant takes deterministic singleton route')
            else:
                require(outcome.get('route')=='compressed_lp','one declared compressed LP route')
                representatives=compression['column_representatives'];rep_set=set(representatives);require(all(q==0 for j,q in enumerate(alpha)if j not in rep_set),'declared representative-only851-ray lift')
                native=outcome.get('native');require(type(native)is dict and native.get('success')is True and native.get('attempted')is True,'successful single native support proposal')
                vector=native.get('scaled_vector');require(type(vector)is list and len(vector)==len(representatives)and all(type(q)in(int,float)and math.isfinite(q)for q in vector),'complete finite native support vector')
                positive=[j for j,q in enumerate(vector)if q>0];support=[representatives[j]for j in positive];stats=outcome.get('restoration_stats')
                require(len(support)<=min(443,len(compression['row_representatives']))and type(stats)is dict and stats.get('support')==support and stats.get('support_size')==len(support)and stats.get('complete')is True and stats.get('free_rule')=='zero','every strictly positive native coordinate is the declared one support')
                support_set=set(support);b.charge(3*len(representatives)+3*len(alpha)+len(support))
                free_support=stats.get('free_support_coordinates');require(type(free_support)is list and free_support==sorted(set(free_support))and all(type(j)is int and 0<=j<len(support)for j in free_support),'declared exact free support positions')
                require(stats.get('rank')==len(support)-len(free_support)and all(alpha[j]==0 for j in range(851)if j not in support_set)and all(alpha[support[j]]==0 for j in free_support),'support-only exact lift and zero free values')
        else:require(certificate is None,'unsuccessful LP or restoration cannot admit a certificate')
        summary.update(schema=SCHEMA,status='FINITE_CONE_INFEASIBLE'if check else outcome['status'],search_status=outcome['status'],certificate_verified=check is not None,finite_augmented_cone_infeasibility_certified=check is not None,certificate_check=check,native_LP_replayed=False)
        payload=encoded(summary);b.charge(2*(len(payload)//64+1));summary.update(audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations)
        return summary
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
