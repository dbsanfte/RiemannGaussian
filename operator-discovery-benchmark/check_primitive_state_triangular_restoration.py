"""Independent exact affine restoration and full-coordinate cone diagnostics.

No producer or numerical solver imports. Resource counters count repeated sparse
rational work; coefficient overflow is UNKNOWN, never a negative PSD verdict.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import check_primitive_state_numerical_proposals as EXACT

FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,
           global_bound_proved=False,RH_proved=False)
SCHEMA='primitive-state-triangular-restoration-v1'


def require(test,message):
    if not test:raise ValueError(message)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(encoded(value)).hexdigest()


def rational(text,budget):
    require(type(text)is str,'explicit canonical rational text')
    q=budget.rational(text,output=True)
    require(str(q)==text,'canonical rational text')
    return q


def exact_psd(matrix,budget):
    """Exact symmetric Schur elimination, retaining a quadratic witness.

    Zero pivots require a zero remaining row; no division by zero or numerical
    tolerance is permitted. A negative result includes a full rational vector.
    """
    n=len(matrix)
    require(n>0 and all(type(row)is list and len(row)==n for row in matrix),'complete square PSD matrix')
    a=[[budget.rational(q) for q in row] for row in matrix]
    require(all(a[i][j]==a[j][i] for i in range(n) for j in range(n)),'symmetric exact PSD matrix')
    t=[[F(i==j) for j in range(n)] for i in range(n)]
    budget.charge(n*n,cells=2*n*n)
    positive=0;zero=0
    def negative(vector,kind,pivot):
        value=F(0)
        for i in range(n):
            for j in range(n):
                value=budget.rational(value+budget.rational(vector[i]*matrix[i][j]*vector[j]))
                budget.charge(cells=2)
        require(value<0,'exact negative quadratic witness')
        return dict(psd=False,kind=kind,pivot=pivot,witness=[str(q) for q in vector],quadratic_value=str(value))
    for i in range(n):
        d=a[i][i]
        if d<0:return negative(t[i],'negative Schur pivot',i)
        if d==0:
            j=next((j for j in range(i+1,n) if a[i][j]),None)
            if j is not None:
                scale=budget.rational(-a[i][j]/(abs(a[j][j])+1))
                vector=[budget.rational(x+scale*y) for x,y in zip(t[i],t[j])]
                return negative(vector,'zero pivot with nonzero remaining row',i)
            zero+=1;continue
        positive+=1
        multipliers={j:budget.rational(a[i][j]/d) for j in range(i+1,n)}
        for j in range(i+1,n):
            for k in range(j,n):
                value=budget.rational(a[j][k]-budget.rational(a[i][j]*multipliers[k]))
                a[j][k]=value;a[k][j]=value;budget.charge(cells=2)
            t[j]=[budget.rational(x-budget.rational(multipliers[j]*y)) for x,y in zip(t[j],t[i])]
            budget.charge(n,cells=n)
    return dict(psd=True,positive_pivots=positive,zero_pivots=zero)


def replay_normalized_rows(rows,rhs,width,tape,budget):
    """Reconstruct every saved normalized row with a fresh exact replay."""
    require(tape.get('status')=='complete' and tape.get('complete')is True,'complete exact basis required')
    require(tape.get('variables')==width and tape.get('original_rows')==len(rows)==len(rhs),'basis source dimensions')
    records=tape.get('transcript');order=tape.get('row_order')
    require(type(records)is list and type(order)is list and len(records)==len(rows)==len(order),'complete basis transcript')
    sizes=[sum(bool(q) for q in row.values())+bool(b) for row,b in zip(rows,rhs)]
    require(order==sorted(range(len(rows)),key=lambda i:(sizes[i],i)),'deterministic basis row order')
    basis=[];pivots={};retained=[]
    for source,record in zip(order,records):
        require(type(record)is dict and record.get('source_row')==source,'ordered source row')
        row={j:budget.rational(q) for j,q in rows[source].items() if q}
        if rhs[source]:row[width]=budget.rational(rhs[source])
        budget.charge(len(row),cells=len(row))
        require(type(record.get('steps'))is list,'explicit basis cancellation steps')
        for step in record['steps']:
            require(row and type(step)is list and len(step)==2 and type(step[0])is int,'bounded ordered cancellation')
            p=min(row);budget.charge(len(row))
            require(p in pivots and step[0]==pivots[p],'cancel current least pivot')
            multiplier=rational(step[1],budget);require(multiplier==row[p],'exact cancellation multiplier')
            for j,q in basis[step[0]].items():
                value=budget.rational(row.get(j,F(0))-budget.rational(multiplier*q));budget.charge(cells=2)
                if value:row[j]=value
                else:row.pop(j,None)
        if row:
            p=min(row);require(p not in pivots and p<width,'consistent new coefficient pivot')
            norm=rational(record.get('normalization'),budget)
            require(norm==row[p] and record.get('pivot_column')==p and record.get('basis_index')==len(basis),'exact normalization and basis index')
            normalized={j:budget.rational(q/norm) for j,q in row.items()};budget.charge(len(row),cells=len(row))
            pivots[p]=len(basis);basis.append(normalized);retained.append(source)
        else:require(all(record.get(k)is None for k in ('pivot_column','normalization','basis_index')),'zero row carries no pivot')
    require(tape.get('retained_indices')==retained and tape.get('pivot_columns')==list(pivots),'complete retained pivot bindings')
    require(tape.get('augmented_rank')==len(basis) and tape.get('coefficient_consistency')=='consistent' and tape.get('inconsistent_augmented_pivots')==[],'consistent augmented basis')
    return basis


def backsubstitute(basis,seed,width,budget):
    require(type(seed)is list and len(seed)==width,'complete projected seed')
    x=[budget.rational(q) for q in seed];by_pivot={}
    for row in basis:
        p=min(row);require(p<width and row[p]==1 and p not in by_pivot,'unique normalized coefficient pivots')
        by_pivot[p]=row
    for p in sorted(by_pivot,reverse=True):
        row=by_pivot[p];value=row.get(width,F(0))
        for j,q in row.items():
            if j in (p,width):continue
            require(j>p and j<width,'upper triangular pivot-column order')
            value=budget.rational(value-budget.rational(q*x[j]));budget.charge(cells=2)
        x[p]=budget.rational(value)
    return x


def derive_projection(shape,offset,specs,width):
    require(type(shape)in (list,tuple) and len(shape)==2 and all(type(n)is int and n>=0 for n in shape),'exact scalar shape')
    ns,nr=shape
    require(specs=={'full_child':15,'full_parent':15,'storage_K':15} and type(offset)is int and offset>=ns+2*nr and width==offset+360,'full original cone layout')
    starts={name:offset+120*k for k,name in enumerate(sorted(specs))}
    recipes={ns+2*j+1:{ns+2*j:F(-1)} for j in range(nr)}
    for j in range(120):recipes[starts['storage_K']+j]={starts['full_child']+j:F(1),starts['full_parent']+j:F(-4)}
    retained=[j for j in range(width) if j not in recipes]
    return retained,recipes,starts


def projected_seed(native,retained,recipes,shape,pivots,budget):
    require(type(native)is list and all(type(v)in (int,float) and math.isfinite(v) for v in native),'full finite binary64 native seed')
    x=[budget.rational(F(float(v))) for v in native]
    position={j:k for k,j in enumerate(retained)};seed=[x[j] for j in retained]
    for omitted,recipe in recipes.items():
        for j,q in recipe.items():seed[position[j]]=budget.rational(seed[position[j]]+budget.rational(q*x[omitted]));budget.charge(cells=2)
    clipped=[]
    for j in range(shape[0]):
        k=position[j]
        if k not in pivots and seed[k]<0:seed[k]=F(0);clipped.append(k)
    return seed,clipped


def lift_original(projected,retained,shape,offset,specs,width,budget):
    expected,recipes,starts=derive_projection(shape,offset,specs,width)
    require(retained==expected and len(projected)==len(retained),'complete projected lift coordinates')
    x=[F(0) for _ in range(width)]
    for j,q in zip(retained,projected):x[j]=budget.rational(q)
    ns,nr=shape
    for j in range(nr):
        value=x[ns+2*j];x[ns+2*j]=max(value,F(0));x[ns+2*j+1]=max(-value,F(0));budget.charge(2,cells=2)
    for j in range(120):
        c=x[starts['full_child']+j];p=x[starts['full_parent']+j]
        x[starts['full_child']+j]=F(0);x[starts['storage_K']+j]=c
        x[starts['full_parent']+j]=budget.rational(p+budget.rational(4*c));budget.charge(cells=3)
    return x


def check_original_candidate(columns,lhs,monomials,vector,offset,specs,budget):
    require(type(vector)is list and len(vector)==len(columns),'all original candidate coordinates explicit')
    x=[budget.rational(q) for q in vector]
    residual=[-budget.rational(lhs.get(m,F(0))) for m in monomials]
    positions={m:i for i,m in enumerate(monomials)}
    require(len(positions)==len(monomials),'unique original moment domain')
    first=None;mismatches=0
    for j,column in enumerate(columns):
        for m,q in column.items():
            require(m in positions,'original equation domain complete')
            i=positions[m];residual[i]=budget.rational(residual[i]+budget.rational(q*x[j]));budget.charge(cells=2)
    for i,q in enumerate(residual):
        if q:
            mismatches+=1
            if first is None:first=dict(original_row=i,residual=str(q))
    negative=[dict(index=i,value=str(q)) for i,q in enumerate(x[:offset]) if q<0];budget.charge(offset)
    blocks={};start=offset
    for name,n in sorted(specs.items()):
        matrix=[[F(0) for _ in range(n)] for _ in range(n)]
        for a in range(n):
            for b in range(a,n):matrix[a][b]=matrix[b][a]=x[start];start+=1;budget.charge(cells=1)
        blocks[name]=exact_psd(matrix,budget)
    require(start==len(x),'complete original PSD variable domain')
    return dict(equality_complete=True,equality_mismatch_count=mismatches,first_equality_mismatch=first,
                scalar_signs_complete=True,negative_scalar_count=len(negative),first_negative_scalar=negative[0] if negative else None,
                psd_blocks=blocks,finite_candidate_feasible=(not mismatches and not negative and all(v['psd'] for v in blocks.values())))


def verify_restoration(cache,trace,basis,projection,receipt,*,deadline=None,max_operations=300000000,
                       max_cells=60000000,max_coefficient_bits=4096,max_receipt_bytes=8388608,
                       expected_bindings=None):
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(receipt)is dict and receipt.get('schema')==SCHEMA,'known exact restoration receipt')
    payload=encoded(receipt);require(len(payload)<=max_receipt_bytes,'bounded exact restoration receipt')
    budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    require(all(receipt.get(k)is False for k in FLAGS),'restoration is no uniform theorem or admission')
    require(receipt.get('seed_rule')=='exact-binary64; negative FREE squares zero; all other free aggregates unchanged','fixed seed rule')
    require(receipt.get('lift')=='child=0; storage_K=C; parent=P+4C; signed relations positive/negative parts','fixed quotient lift')
    require(receipt.get('backsub_order')=='descending pivot column','fixed pivot-column ordering')
    inputs=dict(cache=cache,trace=trace,basis=basis,projection=projection);bindings={}
    for name,value in inputs.items():
        data=encoded(value);bindings[name]=hashlib.sha256(data).hexdigest();budget.charge(2*(len(data)//64+1),cells=len(data)//64+1)
    if expected_bindings is not None:require(bindings==expected_bindings,'trusted restoration input bindings')
    if 'input_bindings' in receipt:require(receipt['input_bindings']==bindings,'complete restoration input bindings')
    limits=receipt.get('limits')
    require(type(limits)is dict and set(limits)=={'max_operations','max_live_cells','max_fill_cells','max_bits','max_receipt_bytes'} and all(type(v)is int and v>0 for v in limits.values()),'complete strict producer resource caps')
    require(limits['max_operations']<=125000000 and limits['max_live_cells']<=4000000 and limits['max_fill_cells']<=20000000 and limits['max_bits']<=max_coefficient_bits and limits['max_receipt_bytes']<=max_receipt_bytes,'authorized producer restoration caps')
    counts=receipt.get('counts')
    require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','fill_cells'} and all(type(v)is int and v>=0 for v in counts.values()),'strict producer restoration counters')
    if receipt.get('status')=='restored':
        require(counts['operations']<=limits['max_operations'] and counts['peak_live_cells']<=limits['max_live_cells'] and counts['fill_cells']<=limits['max_fill_cells'],'complete restoration respects producer caps')
    elapsed=receipt.get('elapsed_seconds')
    if elapsed is not None:require(type(elapsed)in (int,float) and math.isfinite(elapsed) and elapsed>=0,'finite diagnostic elapsed time')
    status=receipt.get('status');require(status in ('restored','unknown','rejected'),'strict restoration termination')
    if status!='restored':
        require(receipt.get('complete')is False,'partial restoration never complete')
        require(type(receipt.get('reason'))is str and bool(receipt['reason']),'explicit partial restoration reason')
        return dict(verified=True,complete=False,restoration_verified=False,finite_candidate_feasible=None,
                    retained_candidate_unverified=receipt.get('candidate_original_vector')is not None,
                    reason=receipt['reason'],audit_operations=budget.operations,audit_cells=budget.cells,
                    independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)
    require(receipt.get('complete')is True and receipt.get('input_bindings')==bindings,'complete bound restoration')
    import check_primitive_state_cached_primal_variants as CACHE
    source=CACHE.decode_original(cache,budget);columns=source['columns'];lhs=source['lhs'];domain=source['monomials']
    n=len(columns);shape=source['shape'];offset=source['offset'];specs=source['specs']
    retained,recipes,starts=derive_projection(shape,offset,specs,n)
    require(projection.get('complete')is True and projection.get('status')=='complete' and projection.get('retained_indices')==retained,'complete exact projection')
    expected_recipes=[[j,[[k,str(q)] for k,q in sorted(recipe.items())]] for j,recipe in sorted(recipes.items())]
    require(projection.get('recipes')==expected_recipes,'exact full original projection recipes')
    for omitted,recipe in recipes.items():
        expected={}
        for j,q in recipe.items():
            for m,c in columns[j].items():
                value=budget.rational(expected.get(m,F(0))+budget.rational(q*c));budget.charge(cells=2)
                if value:expected[m]=value
                else:expected.pop(m,None)
        require(expected==columns[omitted],'original coefficient identity for every omitted column')
    position={j:k for k,j in enumerate(retained)};rows=[{} for _ in domain];positions={m:i for i,m in enumerate(domain)}
    for j in retained:
        for m,q in columns[j].items():rows[positions[m]][position[j]]=q;budget.charge(cells=1)
    rhs=[lhs.get(m,F(0)) for m in domain]
    # Independently fingerprint the exact projected augmented system.
    h=hashlib.sha256();h.update(b'{"rhs":[')
    for i,b in enumerate(rhs):
        if i:h.update(b',')
        h.update(encoded(str(b)));budget.charge()
    h.update(b'],"rows":[')
    for i,row in enumerate(rows):
        if i:h.update(b',')
        h.update(b'[')
        for k,(j,q) in enumerate(sorted(row.items())):
            if k:h.update(b',')
            term=encoded([j,str(q)]);h.update(term);budget.charge(len(term)//64+1)
        h.update(b']');budget.charge(len(row)*max(1,len(row).bit_length()))
    h.update(b'],"variables":'+str(len(retained)).encode()+b'}')
    require(basis.get('source_hash')==projection.get('projected_rows_hash')==h.hexdigest(),'exact projected source hash')
    normalized=replay_normalized_rows(rows,rhs,len(retained),basis,budget)
    pivots=[min(row) for row in normalized];require(receipt.get('pivot_columns')==sorted(pivots) and receipt.get('retained_indices')==retained,'all restored pivot and retained coordinates')
    normal_hash=hashlib.sha256()
    for p,row in zip(pivots,normalized):
        data=encoded([p,[[j,str(q)] for j,q in sorted(row.items())]])
        normal_hash.update(len(data).to_bytes(8,'big'));normal_hash.update(data);budget.charge(len(data)//64+1+len(row)*max(1,len(row).bit_length()),cells=len(row))
    require(receipt.get('normalized_basis_hash')==normal_hash.hexdigest(),'independent normalized basis fingerprint')
    require(type(trace.get('original_vector'))is list and len(trace['original_vector'])==n,'full unchanged native seed coordinates')
    seed,clipped=projected_seed(trace['original_vector'],retained,recipes,shape,set(pivots),budget)
    require(receipt.get('clipped_free_square_indices')==clipped and receipt.get('seed_projected_vector')==list(map(str,seed)),'exact binary64 seed and free-only clipping')
    restored=backsubstitute(normalized,seed,len(retained),budget)
    require(receipt.get('restored_projected_vector')==list(map(str,restored)),'independent exact triangular back substitution')
    candidate=lift_original(restored,retained,shape,offset,specs,n,budget)
    require(receipt.get('candidate_original_vector')==list(map(str,candidate)) and receipt.get('candidate_hash')==digest(list(map(str,candidate))),'complete exact full original lift')
    results=check_original_candidate(columns,lhs,domain,candidate,offset,specs,budget)
    diag=receipt.get('diagnostics');require(type(diag)is dict,'complete producer exact diagnostics')
    require(diag.get('all_original_rows_checked')==len(domain) and diag.get('equality_mismatch_count')==results['equality_mismatch_count'] and diag.get('negative_scalar_count')==results['negative_scalar_count'],'independent all-original equation and scalar conclusions')
    require(type(diag.get('psd'))is list and [(p.get('name'),p.get('psd')) for p in diag['psd']]==[(name,v['psd']) for name,v in results['psd_blocks'].items()],'independent exact PSD conclusions')
    require(diag.get('candidate_cone_checks_pass')is results['finite_candidate_feasible'],'independent finite candidate outcome')
    expected_negatives=[dict(coordinate=i,value=str(q)) for i,q in enumerate(candidate[:offset]) if q<0]
    require(diag.get('negative_scalars')==expected_negatives,'all explicit negative scalar diagnostics')
    mismatches=[]
    for i,row in enumerate(rows):
        value=F(0)
        for j,q in row.items():value=budget.rational(value+budget.rational(q*restored[j]));budget.charge(cells=2)
        if value!=rhs[i]:mismatches.append(dict(row=i,residual=str(budget.rational(value-rhs[i]))))
    require(diag.get('equality_mismatches')==mismatches,'complete explicit equality mismatch diagnostics')
    start=offset
    for report,(name,size) in zip(diag['psd'],sorted(specs.items())):
        matrix=[[F(0) for _ in range(size)] for _ in range(size)]
        for a in range(size):
            for b in range(a,size):matrix[a][b]=matrix[b][a]=candidate[start];start+=1;budget.charge(cells=1)
        verify_psd_receipt(matrix,report,results['psd_blocks'][name],budget)
    return dict(verified=True,complete=True,restoration_verified=True,all_original_equations_checked=len(domain),
                original_variables=n,normalized_basis_hash=normal_hash.hexdigest(),candidate_hash=receipt['candidate_hash'],
                exact_candidate_checks=results,finite_candidate_feasible=results['finite_candidate_feasible'],
                objective_preserved=False,uniform_or_RH_admission=False,
                audit_operations=budget.operations,audit_cells=budget.cells,
                independent_audit_work_reserve=budget.operations+len(payload)+source['source_cells']+1,**FLAGS)


def verify_psd_receipt(matrix,report,independent,budget):
    """Bind producer LDL data or its first failing Schur entry to exact data."""
    n=len(matrix);require(type(report)is dict and report.get('psd')is independent['psd'],'exact PSD receipt verdict')
    if report['psd']:
        weights=report.get('weights');vectors=report.get('vectors');rank=report.get('rank')
        require(type(rank)is int and type(weights)is list and type(vectors)is list and len(weights)==len(vectors)==rank,'complete positive LDL factors')
        ds=[rational(q,budget) for q in weights]
        vs=[[rational(q,budget) for q in row] for row in vectors if type(row)is list]
        require(len(vs)==rank and all(len(row)==n for row in vs) and all(d>0 for d in ds),'complete positive exact factors')
        for i in range(n):
            for j in range(n):
                value=F(0)
                for d,v in zip(ds,vs):value=budget.rational(value+budget.rational(d*v[i]*v[j]));budget.charge(cells=2)
                require(value==matrix[i][j],'producer LDL reconstructs original matrix')
    else:
        witness=report.get('witness');require(type(witness)is dict,'explicit failed PSD Schur witness')
        p=independent['pivot'];require(witness.get('pivot')==p,'first failed Schur pivot')
        # Recompute the reported Schur entry, independent of reported factors.
        a=[row[:] for row in matrix];budget.charge(n*n,cells=n*n)
        for k in range(p):
            d=a[k][k]
            if not d:continue
            for i in range(k+1,n):
                for j in range(i,n):
                    q=budget.rational(a[i][j]-budget.rational(a[i][k]*a[j][k]/d));a[i][j]=a[j][i]=q;budget.charge(cells=2)
        if independent['kind']=='negative Schur pivot':
            require(witness.get('kind')=='negative-schur-pivot' and rational(witness.get('value'),budget)==a[p][p]<0,'exact failed negative Schur witness')
        else:
            j=next(i for i in range(p+1,n) if a[p][i])
            require(witness.get('kind')=='zero-pivot-nonzero-cross' and witness.get('cross')==j and rational(witness.get('value'),budget)==a[p][j],'exact zero-pivot nonzero-cross witness')


def verify_candidate_rejection(receipt,offset,specs,*,deadline=None,max_operations=5000000,
                               max_cells=1000000,max_coefficient_bits=4096):
    """Limited fallback: reject this explicit vector, not the source cone.

    This does not authenticate seed provenance, restoration, or equalities.
    """
    budget=EXACT._Budget(deadline,max_operations,max_cells,max_coefficient_bits)
    require(type(offset)is int and offset>=0 and type(specs)is dict,'explicit original cone layout')
    n=offset+sum(size*(size+1)//2 for size in specs.values())
    vector=receipt.get('candidate_original_vector')
    require(type(vector)is list and len(vector)==n,'complete explicit candidate required for rejection')
    x=[rational(q,budget) for q in vector]
    reason=None
    for i,q in enumerate(x[:offset]):
        if q<0:reason=dict(kind='negative original nonnegative scalar',coordinate=i,value=str(q));break
    if reason is None:
        start=offset
        for name,size in sorted(specs.items()):
            require(type(size)is int and 0<size<=64,'bounded exact PSD block size')
            matrix=[[F(0) for _ in range(size)] for _ in range(size)]
            for a in range(size):
                for b in range(a,size):matrix[a][b]=matrix[b][a]=x[start];start+=1
            result=exact_psd(matrix,budget)
            if not result['psd']:reason=dict(kind='negative original PSD quadratic witness',block=name,psd_check=result);break
    require(reason is not None,'no exact rejection witness established')
    return dict(verified=True,explicit_candidate_rejected=True,candidate_hash=digest(vector),witness=reason,
                restoration_verified=False,all_original_equations_checked=False,
                rejection_only=True,audit_operations=budget.operations,audit_cells=budget.cells,
                independent_audit_work_reserve=budget.operations+len(encoded(receipt))+1,**FLAGS)
