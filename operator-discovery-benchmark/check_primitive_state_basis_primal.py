"""Independent exact layout/canonical assembly and approximate native-vector audit.

Imports no producer, numerical solver, or numerical array library. Floating
residuals and PSD necessary diagnostics are binary64 approximations, not proofs.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time
import check_primitive_state_numerical_proposals as EXACT

FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,global_bound_proved=False,RH_proved=False)


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()


def require(condition,message):
    if not condition:raise ValueError(message)


def scope(value):
    require(type(value)is dict,'explicit diagnostic record')
    for key in FLAGS:
        if key in value:require(value[key]is False,'numerical diagnostics cannot admit '+key)


def finite(value):
    require(type(value)in (int,float) and math.isfinite(value),'complete finite explicit native coordinate')
    return float(value)



def number(q):
    x=float(q);require(math.isfinite(x) and (not q or x!=0),'nonoverflowing nonunderflowing exact coefficient conversion')
    return x

def reconstruct(columns,lhs,monomials,shape,offset,specs,selected_indices,*,deadline=None,max_operations=450000000,max_cells=60000000,max_coefficient_bits=4096):
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(columns)is list and type(lhs)is dict and type(monomials)is list and len(set(monomials))==len(monomials),'complete unique source domain')
    require(set(monomials)==set(lhs)|{m for column in columns for m in column},'complete exact source and target domain')
    require(type(shape)is list and len(shape)==2 and all(type(v)is int and v>=0 for v in shape),'source scalar shape')
    require(type(offset)is int and shape[0]+2*shape[1]<=offset<=len(columns),'full nonnegative scalar layout')
    require(type(specs)is dict and all(type(name)is str and type(n)is int and n>0 for name,n in specs.items()),'complete named PSD layouts')
    require(list(specs)==sorted(specs),'source PSD coordinate order must be sorted names')
    require(offset+sum(n*(n+1)//2 for n in specs.values())==len(columns),'full PSD variable dimensions')
    require(type(selected_indices)is list and len(set(selected_indices))==len(selected_indices) and all(type(i)is int and 0<=i<len(monomials) for i in selected_indices),'authorized unique original row indices')
    lookup={m:i for i,m in enumerate(monomials)};rows=[{} for _ in monomials];rhs=[]
    budget.charge(len(monomials)+len(columns),cells=len(monomials)+len(columns))
    for j,column in enumerate(columns):
        require(type(column)is dict,'complete sparse exact source column')
        for m,value in column.items():
            require(m in lookup,'source column outside complete monomial domain')
            q=budget.rational(value);budget.charge(cells=1)
            if q:rows[lookup[m]][j]=q
    require(all(m in lookup for m in lhs),'target outside complete monomial domain')
    for m in monomials:rhs.append(budget.rational(lhs.get(m,F(0))))
    objective=[0.0]*len(columns)
    for j in range(shape[0]+2*shape[1]):objective[j]=1.0
    blocks=[];start=offset
    for name,n in sorted(specs.items()):
        indices=[]
        for a in range(n):
            for b in range(a,n):
                indices.append([a,b,start]);objective[start]=float(a==b);start+=1;budget.charge(cells=1)
        blocks.append(dict(name=name,size=n,offset=indices[0][2],indices=indices))
    layout=dict(shape=shape,offset=offset,specs=[[name,n] for name,n in sorted(specs.items())],psd_blocks=blocks,scalar_nonnegative_indices=list(range(offset)),objective=objective)
    budget.charge(sum(len(row)*max(1,len(row).bit_length()) for row in rows))
    system=dict(rows=[[[j,str(q)] for j,q in sorted(row.items())] for row in rows],rhs=list(map(str,rhs)),variables=len(columns))
    scales=[];canonical=[];targets=[]
    for i in selected_indices:
        budget.charge(len(rows[i])*max(1,len(rows[i]).bit_length()))
        scale=max([abs(rhs[i])]+[abs(q) for q in rows[i].values()]);require(scale>0,'selected nonzero augmented equation');scales.append(str(scale))
        canonical.append([[j,number(budget.rational(q/scale)).hex()] for j,q in sorted(rows[i].items())]);targets.append(number(budget.rational(rhs[i]/scale)).hex())
        budget.charge(cells=len(rows[i])+1)
    for j in range(offset):canonical.append([[j,(-1.0).hex()]]);targets.append((0.0).hex());budget.charge(cells=2)
    for block in blocks:
        coordinates={(a,b):j for a,b,j in block['indices']}
        for b in range(block['size']):
            for a in range(b+1):canonical.append([[coordinates[a,b],(-1.0 if a==b else -math.sqrt(2.0)).hex()]]);targets.append((0.0).hex());budget.charge(cells=2)
    cones=[['Zero',len(selected_indices)],['Nonnegative',offset]]+[['PSDTriangle',n] for _,n in sorted(specs.items())]
    canonical_system=dict(variables=len(columns),rows=canonical,rhs=targets,objective=[value.hex() for value in objective],cones=cones)
    hashes=[]
    for value in (system,layout,canonical_system):
        raw=json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode();budget.charge(2*(len(raw)//64+1),cells=len(raw)//64+1);hashes.append(hashlib.sha256(raw).hexdigest())
    domain_bytes=json.dumps(monomials,sort_keys=True,separators=(',',':'),allow_nan=False).encode();budget.charge(2*(len(domain_bytes)//64+1),cells=len(domain_bytes)//64+1)
    receipt=dict(schema='primitive-state-basis-primal-assembly-v1',original_system_hash=hashes[0],monomial_domain_hash=hashlib.sha256(domain_bytes).hexdigest(),selected_original_indices=selected_indices,
        selected_row_scales=scales,layout=layout,layout_hash=hashes[1],canonical_system_hash=hashes[2])
    source_cells=sum(map(len,columns))+len(monomials);canonical_cells=sum(map(len,canonical))
    assembly_operations=1+source_cells+sum(map(len,columns))+len(rhs)
    for q in rhs:assembly_operations+=len(json.dumps(str(q),separators=(',',':')).encode())//64+1
    for row in rows:
        assembly_operations+=len(row)*max(1,len(row).bit_length())
        for j,q in sorted(row.items()):assembly_operations+=len(json.dumps([j,str(q)],separators=(',',':')).encode())//64+1
    assembly_operations+=sum(len(rows[i])+1 for i in selected_indices)+canonical_cells+len(canonical)
    for row in canonical:
        assembly_operations+=len(row)*max(1,len(row).bit_length())
        for pair in row:assembly_operations+=len(json.dumps(pair,separators=(',',':')).encode())//64+1
    assembly_operations+=len(canonical)+len(columns)+len(cones)+canonical_cells+len(columns)
    # This second deterministic count replay traverses/sorts/encodes the same
    # data as producer assembly. Charge its FULL rederived producer proxy,
    # separately from the first independent reconstruction and hashing pass.
    budget.charge(assembly_operations,cells=source_cells+canonical_cells)
    receipt.update(variables=len(columns),original_rows=len(rows),variable_mapping='identity',objective_mapping='identity',cone_mapping='identity',
        storage_definition='R=e_prefix e_prefix^T+K, enforced K PSD',storage_anchor_index=1,cones=cones,canonical_rows=len(canonical),canonical_cells=canonical_cells,
        counts=dict(operations=assembly_operations,cells=source_cells+canonical_cells+len(canonical),source_cells=source_cells,canonical_cells=canonical_cells))
    return dict(receipt=receipt,rows=rows,rhs=rhs,canonical_system=canonical_system,objective=objective,blocks=blocks,audit_operations=budget.operations,audit_cells=budget.cells)



def approximate_residual(terms,target):
    try:
        value=math.fsum(terms)-target
        return value if math.isfinite(value) else None
    except (OverflowError,ValueError):return None


def approximate_max_abs(values):
    return max(map(abs,values),default=0.0) if all(v is not None for v in values) else None

def diagnostics(vector,reconstructed,selected_indices,budget):
    if vector is None:return None
    require(type(vector)is list and len(vector)==len(reconstructed['objective']),'full explicit native vector length')
    x=[finite(v) for v in vector];budget.charge(len(x),cells=len(x))
    residuals=[]
    for row,b in zip(reconstructed['rows'],reconstructed['rhs']):
        terms=[number(q)*x[j] for j,q in row.items()];budget.charge(3*len(terms)+2,cells=len(terms)+1)
        residuals.append(approximate_residual(terms,number(b)))
    scales=list(map(F,reconstructed['receipt']['selected_row_scales']))
    scaled=[]
    for row,b in zip(reconstructed['canonical_system']['rows'][:len(selected_indices)],reconstructed['canonical_system']['rhs']):
        scaled.append(approximate_residual([float.fromhex(q)*x[j] for j,q in row],float.fromhex(b)));budget.charge(3*len(row)+2,cells=len(row)+1)
    psd=[]
    for block in reconstructed['blocks']:
        n=block['size'];matrix=[[0.0]*n for _ in range(n)]
        for a,b,j in block['indices']:matrix[a][b]=matrix[b][a]=x[j]
        lower=[];diagonal=[];minors=[]
        for a in range(n):
            diagonal.append(matrix[a][a]);value=approximate_residual([abs(matrix[a][b]) for b in range(n) if b!=a],matrix[a][a]);lower.append(-value if value is not None else None)
            for b in range(a+1,n):product=matrix[a][a]*matrix[b][b];cross=matrix[a][b]*matrix[a][b];value=product-cross;minors.append(value if math.isfinite(value) else None)
        budget.charge(6*n*n,cells=2*n*n)
        psd.append(dict(name=block['name'],gershgorin_lower=min(lower) if all(v is not None for v in lower) else None,minimum_diagonal=min(diagonal),minimum_2x2_principal_minor=min(minors,default=None) if all(v is not None for v in minors) else None))
    offset=reconstructed['receipt']['layout']['offset'];budget.charge(3*len(residuals)+len(selected_indices)+3*len(x),cells=len(residuals)+len(selected_indices)+len(x))
    return dict(equality_max_abs=approximate_max_abs(residuals),unknown_original_residual_count=sum(v is None for v in residuals),selected_equality_max_abs=approximate_max_abs([residuals[i] for i in selected_indices]),
        selected_scaled_equality_max_abs=approximate_max_abs(scaled),nonnegative_min=min(x[:offset],default=None),
        negative_scalar_count=sum(v<0 for v in x[:offset]),objective=approximate_residual([c*v for c,v in zip(reconstructed['objective'],x)],0.0),psd_gershgorin=psd)


def verify_trace(trace,columns,lhs,monomials,shape,offset,specs,selected_indices,*,expected_source_hashes=None,expected_options=None,expected_versions=None,deadline=None,
    max_operations=450000000,max_cells=60000000,max_coefficient_bits=4096,max_trace_bytes=8388608,max_log_bytes=1048576):
    scope(trace)
    if 'diagnostics' in trace:scope(trace['diagnostics'])
    require(trace.get('schema')=='primitive-state-basis-primal-v1','native basis primal schema')
    encoded=json.dumps(trace,sort_keys=True,separators=(',',':'),allow_nan=False).encode();require(len(encoded)<=max_trace_bytes,'bounded trace bytes')
    reconstructed=reconstruct(columns,lhs,monomials,shape,offset,specs,selected_indices,deadline=deadline,max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_coefficient_bits)
    assembly=trace.get('assembly');require(type(assembly)is dict,'complete original/canonical assembly receipt');scope(assembly)
    limits=assembly.get('limits');require(type(limits)is dict and set(limits)=={'max_operations','max_cells','max_coefficient_bits'} and all(type(v)is int and v>0 for v in limits.values()),'strict source assembly limits')
    require(assembly.get('counts',{}).get('operations',limits['max_operations']+1)<=limits['max_operations'] and assembly.get('counts',{}).get('cells',limits['max_cells']+1)<=limits['max_cells'],'bounded assembly accounting')
    for key,value in reconstructed['receipt'].items():require(assembly.get(key)==value,'independently rebuilt canonical assembly '+key)
    if expected_source_hashes is not None:require(trace.get('source_hashes')==expected_source_hashes,'source hash closure binding')
    solver=trace.get('solver');require(type(solver)is dict and solver.get('name')=='clarabel-native','direct native solver identity')
    options=solver.get('options');versions=solver.get('versions')
    require(type(options)is dict and type(options.get('max_threads'))is int and options['max_threads']==1 and type(options.get('time_limit'))in (int,float) and math.isfinite(options['time_limit']) and 0<=options['time_limit']<=900,'bounded single-thread solver options')
    require(type(versions)is dict and versions and solver.get('versions_hash')==digest(versions) and solver.get('options_hash')==digest(options),'solver versions/options hashes')
    if expected_options is not None:require(options==expected_options,'frozen solver options')
    if expected_versions is not None:require(versions==expected_versions,'frozen solver versions')
    require('termination_status' in trace,'explicit native termination status')
    native=trace.get('raw_solution');vector=trace.get('original_vector')
    require(type(native)is dict or native is None,'explicit native solution or unavailable')
    if type(native)is dict:
        for key in ('s','z'):
            if key in native:
                require(type(native[key])is list and len(native[key])==reconstructed['receipt']['canonical_rows'] and all(v is None or type(v)in (int,float) and math.isfinite(v) for v in native[key]),'complete explicit native canonical '+key+' coordinates')
    if vector is not None:
        require(type(native)is dict and type(native.get('x'))is list and len(native['x'])==len(vector) and all(finite(a).hex()==finite(b).hex() for a,b in zip(native['x'],vector)),'unchanged complete original native x coordinates')
        require(trace.get('vector_role')in ('raw_native_solution','raw_failed_last_iterate'),'diagnostic raw native role')
        require(native.get('status')==trace['termination_status'],'native solution termination binding')
        require(trace['vector_role']==('raw_native_solution' if trace['termination_status']in ('Solved','AlmostSolved') else 'raw_failed_last_iterate'),'diagnostic native status role')
    else:
        require(trace.get('vector_role')=='unavailable','unavailable full vector role')
        if type(native)is dict and type(native.get('x'))is list and len(native['x'])==len(columns) and all(type(v)in (int,float) and math.isfinite(v) for v in native['x']):
            raise ValueError('complete finite native x must be retained in original coordinates')
    log=trace.get('retained_log');require(type(log)is dict and type(log.get('text'))is str and log.get('encoding')=='utf-8','explicit retained log bytes')
    logbytes=log['text'].encode();require(len(logbytes)<=max_log_bytes and type(log.get('retained_bytes'))is int and log['retained_bytes']==len(logbytes),'retained log cap/count')
    require(type(log.get('total_bytes'))is int and log['total_bytes']>=len(logbytes) and type(log.get('truncated'))is bool and log['truncated']==(log['total_bytes']>len(logbytes)),'bounded log truncation semantics')
    require(log.get('sha256')==hashlib.sha256(logbytes).hexdigest(),'retained log hash')
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits);budget.charge(reconstructed['audit_operations'],cells=reconstructed['audit_cells'])
    native_auxiliary_cells=sum(len(native.get(k,[])) for k in ('s','z')) if native is not None else 0
    budget.charge(2*(len(encoded)//64+1)+2*(len(logbytes)//64+1)+2*len(columns)+3*native_auxiliary_cells,cells=len(encoded)//64+len(logbytes)//64+2)
    for value in (options,versions,reconstructed['receipt']):
        payload=json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode();budget.charge(2*(len(payload)//64+1),cells=len(payload)//64+1)
    metrics=diagnostics(vector,reconstructed,selected_indices,budget)
    return dict(verified=True,canonical_system_independently_rebuilt=True,native_coordinate_mapping='identity; complete original x without projection',original_rows=len(monomials),original_variables=len(columns),selected_rows=len(selected_indices),
        assembly_hash=digest(reconstructed['receipt']),diagnostics=metrics,rounding='Python binary64 coefficient conversion and math.fsum; PSD Gershgorin and 2x2 metrics are necessary diagnostics, not certified error bounds',
        audit_operations=budget.operations,audit_cells=budget.cells,independent_audit_work_reserve=budget.operations+len(encoded)+sum(map(len,columns))+len(lhs)+1,
        trace_bytes=len(encoded),mathematical_feasibility='UNKNOWN',**FLAGS)
