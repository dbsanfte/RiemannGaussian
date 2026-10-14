"""Exact affine geometry discovery and one compressed Farkas proposal.

Saved maps, exposures, and LP equivalences have separate independent checks.
Native LP output and exact producer self-checks are never admission decisions.
"""
from fractions import Fraction as F
import math
import time
import primitive_state_chart_dual_search as P

encoded=P.encoded;FLAGS=dict(P.FLAGS)
SCHEMA='primitive-state-chart-dual-geometry-search-v1'
GEOMETRY_SCHEMA='primitive-state-chart-dual-geometry-v1'
LIMITS=dict(geometry_operations=70000000,native_operations=150000000,
            restoration_operations=80000000,max_cells=6000000,max_bits=4096,
            max_temporary_bits=8193,max_simplex_iterations=10000,
            max_geometry_bytes=16777216,max_outcome_bytes=8388608)
POLICY=dict(forms='complete1224 exact coordinate affine normal forms',
            column_compression='drop zero; merge only positive proportional columns; first ray representative',
            row_compression='drop zero augmented rows; merge signed proportional augmented rows including target',
            exposures='zero response or exact nonnegative two-ray opposite-line cancellation',
            exposure_scope='vanishing on every feasible point; no feasibility assertion',
            cost='unit L1 representative weights; positive common scaled-cost normalization',
            direct_route='first ray with no free response and negative constant',
            support='all strictly positive successful native variables; max=min(443,compressed rows)',
            max_native_iterations=10000,native_attempts=1,restoration_attempts=1)

class Budget(P.Budget):
    pass


def _line_key(column,budget):
    if not column:return None,F(0)
    first=min(column);factor=budget.q(column[first]);key=tuple((i,budget.div(q,factor))for i,q in sorted(column.items()))
    return key,factor


def discover_lines(columns,budget):
    """All rational line classes, signed factors and exact exposure pairs."""
    lookup={};classes=[];zeros=[];exposures=[];key_cells=0
    for index,column in enumerate(columns):
        key,factor=_line_key(column,budget)
        if key is None:
            zeros.append(index);exposures.append(dict(ray_index=index,kind='zero_response',combination=[dict(ray_index=index,weight='1')]));continue
        if key not in lookup:
            lookup[key]=len(classes);key_cells+=2*len(key);classes.append(dict(representative=index,members=[],positive_indices=[],negative_indices=[],_factor=factor))
        group=classes[lookup[key]];relative=budget.div(factor,group['_factor']);group['members'].append(dict(ray_index=index,factor=str(relative)))
        group['positive_indices'if relative>0 else'negative_indices'].append(index);budget.cells(key_cells+4*(index+1)+4*len(exposures))
    for group in classes:
        if group['positive_indices']and group['negative_indices']:
            factors={m['ray_index']:budget.q(m['factor'])for m in group['members']}
            for member in group['members']:
                i=member['ray_index'];factor=factors[i];opposite=(group['negative_indices']if factor>0 else group['positive_indices'])[0]
                ratio=budget.div(factor,factors[opposite]);weight=-ratio
                if weight<=0:raise ValueError('strict positive opposite-line weight')
                exposures.append(dict(ray_index=i,kind='opposite_line',combination=[dict(ray_index=i,weight='1'),dict(ray_index=opposite,weight=str(weight))]))
        group.pop('_factor')
    exposures.sort(key=lambda record:record['ray_index'])
    return classes,zeros,exposures


def compress_model(columns,target,row_keys,budget):
    """Exact positive column equivalence and signed AUGMENTED row equivalence."""
    groups={};representatives=[];column_map=[];column_key_cells=0;row_cells=0;row_key_cells=0
    for index,column in enumerate(columns):
        key,factor=_line_key(column,budget)
        if key is None:column_map.append(None);continue
        orientation=1 if factor>0 else-1;groupkey=(key,orientation)
        if groupkey not in groups:groups[groupkey]=(index,factor);representatives.append(index);column_key_cells+=2*len(key)
        representative,reference=groups[groupkey];relative=budget.div(factor,reference)
        if relative<=0:raise ValueError('positive-only column factor')
        column_map.append(dict(representative=representative,positive_factor=str(relative)));budget.cells(column_key_cells+3*len(column_map))
    n=len(representatives);row_groups={};row_representatives=[];row_map=[]
    for i in row_keys:
        row={k:columns[j][i]for k,j in enumerate(representatives)if i in columns[j]}
        if target.get(i,F(0)):row[n]=target[i]
        row_cells+=len(row);key,factor=_line_key(row,budget)
        if key is None:row_map.append(None);continue
        if key not in row_groups:row_groups[key]=(i,factor);row_representatives.append(i);row_key_cells+=2*len(key)
        representative,reference=row_groups[key];row_map.append(dict(representative=representative,signed_factor=str(budget.div(factor,reference))));budget.cells(column_key_cells+row_cells+row_key_cells+3*(len(column_map)+len(row_map)))
    compressed_columns=[{i:columns[j][i]for i in row_representatives if i in columns[j]}for j in representatives]
    rhs={i:target[i]for i in row_representatives if target.get(i,F(0))};budget.cells(column_key_cells+row_cells+row_key_cells+3*sum(map(len,compressed_columns))+3*(len(column_map)+len(row_map)))
    receipt=dict(column_representatives=representatives,column_map=column_map,row_keys=row_keys,row_representatives=row_representatives,row_map=row_map,compressed_columns=[[[i,str(q)]for i,q in sorted(col.items())]for col in compressed_columns],compressed_rhs=[[i,str(q)]for i,q in sorted(rhs.items())],column_lift='weight at representative, zero at all other original rays',row_target_included=True)
    return compressed_columns,rhs,receipt


def canonical_span(vectors,budget,width=15):
    if type(width)is not int or not 1<=width<=15:raise ValueError('bounded kernel span width')
    basis={}
    for vector in vectors:
        values=[budget.q(q)for q in vector]
        if len(values)!=width:raise ValueError('complete kernel vector')
        row={j:q for j,q in enumerate(values)if q}
        for p in sorted(basis):
            factor=row.get(p,F(0));budget.charge()
            if not factor:continue
            for j,q in basis[p].items():
                value=budget.add(row.get(j,F(0)),-budget.mul(factor,q))
                if value:row[j]=value
                else:row.pop(j,None)
        if row:
            p=min(row);factor=row[p];basis[p]={j:budget.div(q,factor)for j,q in row.items()}
        budget.cells(width*width+len(row))
    for p in sorted(basis,reverse=True):
        for earlier in sorted(j for j in basis if j<p):
            factor=basis[earlier].get(p,F(0))
            if not factor:continue
            for j,q in basis[p].items():
                value=budget.add(basis[earlier].get(j,F(0)),-budget.mul(factor,q))
                if value:basis[earlier][j]=value
                else:basis[earlier].pop(j,None)
    return [[str(basis[p].get(j,F(0)))for j in range(width)]for p in sorted(basis)]


def exposed_faces(rays,exposures,budget):
    indices=[record['ray_index']for record in exposures];records=rays['records']
    scalars=sorted({records[j]['coordinate']for j in indices if records[j]['kind']=='scalar'})
    spans=[]
    for block in('C','H'):
        exposed=[j for j in indices if records[j]['kind']=='rank_one'and records[j]['block']==block]
        basis=canonical_span([records[j]['vector']for j in exposed],budget)
        spans.append(dict(block=block,exposed_ray_indices=exposed,rank=len(basis),basis_vectors=basis))
    return scalars,spans


def geometry(rows,width,free,retained,rays,budget,*,max_geometry_bytes=16777216):
    if type(max_geometry_bytes)is not int or not 4096<=max_geometry_bytes<=16777216:raise ValueError('bounded complete geometry artifact')
    if rays.get('schema')!=P.RAY_SCHEMA or rays.get('complete')is not True or rays.get('width')!=width or rays.get('retained_indices')!=retained or len(rays.get('records',[]))!=851 or [r.get('index')for r in rays['records']]!=list(range(851)):raise ValueError('same complete851 declared exact rays')
    scalar,C,H=P.geometry(retained)
    if rays.get('scalar_projected_indices')!=scalar or rays.get('C_projected_indices')!=C or rays.get('P_projected_indices')!=H:raise ValueError('same generator geometry')
    base=2*sum(map(len,rows.values()))+16*851+width;budget.resident_cells=base
    forms,_=P.coordinate_responses(rows,width,list(range(width)),budget)
    mathematical_cells=sum(len(r)+1 for r,t in forms.values());budget.resident_cells=base+mathematical_cells
    form_records=[];response_records=[];columns=[];retained_bytes=65536;export_cells=0;column_cells=0
    def record(value,destination,cells):
        nonlocal retained_bytes,export_cells
        data=encoded(value);budget.charge(len(data)//64+1)
        if len(data)+retained_bytes>max_geometry_bytes:raise OverflowError('complete geometry retained-byte cap')
        retained_bytes+=len(data)+1;export_cells+=cells;budget.cells(export_cells+column_cells);destination.append(value)
    for j in range(width):
        r,t=forms[j];record(dict(coordinate=j,constant=str(t),terms=[[i,str(q)]for i,q in sorted(r.items())]),form_records,2*len(r)+1)
    for ray in rays['records']:
        w=P.ray_functional(ray,scalar,C,H,budget);r={};t=F(0)
        for j,q in w.items():
            other,constant=forms[j]
            if constant:t=budget.add(t,budget.mul(q,constant))
            for i,c in other.items():
                value=budget.add(r.get(i,F(0)),budget.mul(q,c))
                if value:r[i]=value
                else:r.pop(i,None)
        if t:r[width]=t
        columns.append(r);column_cells+=len(r);record(dict(ray_index=ray['index'],terms=[[i,str(q)]for i,q in sorted(r.items())]),response_records,2*len(r))
    budget.resident_cells+=export_cells+column_cells
    classes,zeros,exposures=discover_lines(columns,budget);forced,kernels=exposed_faces(rays,exposures,budget)
    row_keys=[*free,width];target={width:F(-1)};compressed,rhs,compression=compress_model(columns,target,row_keys,budget)
    contradictions=[i for i in compression['row_representatives']if rhs.get(i,F(0))and not any(i in col for col in compressed)]
    negative=next((j for j,col in enumerate(columns)if col.get(width,F(0))<0 and all(i==width for i in col)),None)
    out=dict(schema=GEOMETRY_SCHEMA,complete=True,width=width,free_indices=free,pivot_columns=sorted(rows),forms=form_records,responses=response_records,line_classes=classes,zero_ray_indices=zeros,exposures=exposures,compression=compression,negative_constant_ray=negative,contradictory_compressed_rows=contradictions,forced_scalar_indices=forced,kernel_spans=kernels,policy=POLICY,**FLAGS)
    budget.cells(3*sum(map(len,compressed))+4*851+4*len(exposures))
    payload=encoded(out);budget.charge(len(payload)//64+1)
    if len(payload)>max_geometry_bytes:raise OverflowError('complete geometry artifact cap')
    live_model_cells=base+export_cells+column_cells+3*sum(map(len,compressed))+8*851+4*len(exposures)+900
    model=dict(width=width,free=free,rows=rows,retained=retained,rays=rays,columns=columns,target=target,resident_cells=live_model_cells)
    return out,model,compressed,rhs


def native_reservation(m,n,remaining):
    if any(type(v)is not int or v<1 for v in(m,n))or type(remaining)is not int or remaining<0:raise ValueError('bounded compressed LP shape')
    preparation=16*m*n+64*(m+n)+1048576;setup=preparation+m**3+2*m*n+1048576;step=2*m*n+m*m;k=min(10000,max(0,(remaining-setup)//step))
    return dict(preparation_work_reserve=preparation,initial_factorization=m**3,per_iteration=step,max_iterations=k,input_and_transport=2*m*n+1048576,total=setup+k*step)


def native_proposal(compressed,rhs,row_keys,*,deadline,max_operations=150000000,resident_cells=0):
    budget=Budget(deadline,max_operations);budget.resident_cells=resident_cells;state=dict(attempted=False,options=dict(presolve=False,maxiter=None,threads=1,time_limit=None));start=time.monotonic()
    try:
        if not compressed or not row_keys:raise ValueError('empty compressed shape has no native attempt')
        m=len(row_keys);n=len(compressed);reserve=native_reservation(m,n,budget.max_operations)
        state.update(reservation=reserve,rows=m,columns=n)
        state['options']['maxiter']=reserve['max_iterations']
        if reserve['max_iterations']<1:raise OverflowError('no complete compressed native iteration fits reservation')
        # Scaling helper's row domain is its free list plus a last bookkeeping key.
        model=dict(width=row_keys[-1],free=row_keys[:-1],columns=compressed,target=rhs)
        keys,scaled,b,R,D=P.scaled_model(model,budget);cost_scale=max(D)
        exact_cost=[budget.div(q,cost_scale)for q in D]
        budget.cells(sum(map(len,scaled))+2*sum(map(len,scaled))+4*m+4*n)
        if budget.operations>reserve['preparation_work_reserve']:raise OverflowError('dimension-only native preparation reserve exhausted')
        budget.charge(reserve['total']-reserve['preparation_work_reserve'])
        import numpy as np
        import scipy
        from scipy.sparse import csc_matrix
        from scipy.optimize import linprog
        import warnings
        position={j:i for i,j in enumerate(keys)};data=[];indices=[];indptr=[0]
        for col in scaled:
            for i,q in sorted(col.items(),key=lambda item:position[item[0]]):data.append(P.finite_float(q));indices.append(position[i])
            indptr.append(len(data))
        cost=[P.finite_float(q)for q in exact_cost]
        # Common objective division is exact and bounded; no alternate objective.
        matrix=csc_matrix((data,indices,indptr),shape=(m,n));rhs_float=[P.finite_float(q)for q in b]
        options=dict(presolve=False,maxiter=reserve['max_iterations'],threads=1,time_limit=max(.001,deadline-time.monotonic()));state['options']=options
        with warnings.catch_warnings(record=True)as captured:
            warnings.simplefilter('always');state['attempted']=True;result=linprog(cost,A_eq=matrix,b_eq=rhs_float,bounds=(0,None),method='highs-ds',options=options)
        vector=None if result.x is None else [float(v)for v in result.x]
        if vector is not None and(len(vector)!=n or not all(math.isfinite(v)for v in vector)):vector=None
        integer=isinstance(result.nit,(int,np.integer))and not isinstance(result.nit,(bool,np.bool_));valid=integer and 0<=int(result.nit)<=reserve['max_iterations']
        out=dict(success=bool(result.success),status=int(result.status),message=str(result.message),iterations=int(result.nit)if integer else None,scaled_vector=vector,attempted=True,options=options,reservation=reserve,rows=m,columns=n,cost_common_scale=str(cost_scale),scipy_version=scipy.__version__,warnings=[str(w.message)for w in captured],elapsed_seconds=time.monotonic()-start)
        if not valid:out.update(success=False,resource_failure='native iteration count outside declared bound')
        try:budget.charge(0)
        except (OverflowError,TimeoutError)as error:out.update(success=False,resource_failure=str(error))
        out['counts']=budget.counts();return out
    except Exception as error:return dict(success=False,status=None,message=str(error),error_type=type(error).__name__,resource_failure=str(error)or type(error).__name__,iterations=None,scaled_vector=None,counts=budget.counts(),elapsed_seconds=time.monotonic()-start,**state)


def search(chart,rays,*,deadline,checkpoint=None,save_geometry=None):
    out=dict(schema=SCHEMA,status='UNKNOWN',geometry_complete=False,route=None,certificate=None,native=None,policy=POLICY,limits=LIMITS,stage_counts={},**FLAGS)
    def progress(phase):
        if checkpoint:checkpoint(dict(phase=phase,status=out['status'],geometry_complete=out['geometry_complete'],stage_counts=out['stage_counts'],**FLAGS))
    gb=Budget(deadline,70000000)
    try:
        progress('geometry_started');rows,free,retained=P.decode_chart(chart,gb);artifact,model,compressed,rhs=geometry(rows,1224,free,retained,rays,gb)
        out['stage_counts']['geometry']=gb.counts()
        if save_geometry is not None:save_geometry(artifact)
        out.update(geometry_complete=True,geometry_stats=dict(forms=1224,responses=851,zero_rays=len(artifact['zero_ray_indices']),exposed_rays=len(artifact['exposures']),compressed_rows=len(artifact['compression']['row_representatives']),compressed_columns=len(compressed)),negative_constant_ray=artifact['negative_constant_ray']);progress('geometry_complete')
        restoration=Budget(deadline,80000000);restoration.resident_cells=model['resident_cells']+4*851
        if artifact['negative_constant_ray']is not None:
            out['route']='negative_constant_ray';index=artifact['negative_constant_ray'];alpha=[F(0)]*851;alpha[index]=restoration.div(F(-1),model['columns'][index][1224]);out['restoration_stats']=dict(support=[index],support_size=1,route='exact negative constant')
        else:
            out['route']='compressed_lp';row_keys=artifact['compression']['row_representatives']
            if not compressed or not row_keys or artifact['contradictory_compressed_rows']:out.update(status='NONCERTIFIED',reason='empty or contradictory compressed LP equations; no cone conclusion');return out
            native=native_proposal(compressed,rhs,row_keys,deadline=deadline,resident_cells=model['resident_cells']);out['native']=native;out['stage_counts']['native']=native['counts'];progress('native_returned')
            if not native['success']or native['scaled_vector']is None:out.update(status='UNKNOWN'if native.get('resource_failure')or native.get('status')==1 else'NONCERTIFIED',reason=native.get('resource_failure')or'native LP not successful');return out
            support=[j for j,v in enumerate(native['scaled_vector'])if v>0];bound=min(443,len(row_keys))
            if len(support)>bound:out.update(status='NONCERTIFIED',reason='all-positive native support exceeds compressed row bound');return out
            originals=[artifact['compression']['column_representatives'][j]for j in support]
            alpha,stats=P.exact_support_solve(model['columns'],model['target'],1224,originals,restoration);out['restoration_stats']=stats
        progress('restoration_started');certificate=P.certify(rows,1224,free,retained,rays,alpha,restoration);restoration.charge(len(encoded(certificate)));out.update(status='CERTIFICATE_PROPOSED',certificate=certificate);out['stage_counts']['restoration']=restoration.counts();progress('certificate_proposed')
    except Exception as error:
        out.update(status='NONCERTIFIED'if isinstance(error,ValueError)and out['geometry_complete']else'UNKNOWN',reason=str(error)or type(error).__name__,error_type=type(error).__name__)
        if 'restoration'in locals():out['stage_counts']['restoration']=restoration.counts()
    finally:out['stage_counts'].setdefault('geometry',gb.counts())
    if len(encoded(out))>8388608:raise OverflowError('bounded geometry search outcome')
    return out
