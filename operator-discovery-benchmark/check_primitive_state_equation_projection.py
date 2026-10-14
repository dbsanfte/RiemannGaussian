"""Independent exact column identities for augmented-row basis preprocessing.

Projection affects rank computation only. The complete optimization variables,
objective and cone keep their original meanings. No producer/solver imports.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import check_primitive_state_exact_row_basis as BASIS

SCHEMA='primitive-state-exact-equation-projection-v1'
USE='exact augmented-row-span preprocessing only'
LIMITS={k:v for k,v in BASIS.LIMITS.items() if k!='max_fill_cells'}
FLAGS=dict(BASIS.FLAGS)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def full15_recipes(shape,offset,specs,n_columns):
    """Independent declaration; identities still require coefficientwise replay."""
    if type(shape)not in (tuple,list) or len(shape)!=2 or any(type(n)is not int or n<0 for n in shape):raise ValueError('complete scalar layout')
    squares,relations=shape
    if type(offset)is not int or offset<squares+2*relations or type(n_columns)is not int or n_columns!=offset+360:
        raise ValueError('complete full15 original columns')
    if specs!={'full_child':15,'full_parent':15,'storage_K':15} or any(type(n)is not int for n in specs.values()):raise ValueError('three full15 Gram blocks')
    dependencies={}
    for pair in range(relations):dependencies[squares+2*pair+1]={squares+2*pair:F(-1)}
    child=offset;parent=offset+120;storage=offset+240
    for entry in range(120):dependencies[storage+entry]={child+entry:F(1),parent+entry:F(-4)}
    kept=[j for j in range(n_columns) if j not in dependencies]
    return kept,dependencies


def _limits(record,authorized,receipt_cap):
    if type(record)is not dict or set(record)!=set(LIMITS) or any(type(v)is not int or v<1 for v in record.values()):raise ValueError('strict complete projection limits')
    if record['max_receipt_bytes']<256 or record['max_receipt_bytes']>receipt_cap or any(record[k]>authorized[k] for k in record):raise ValueError('authorized projection caps')
    return record


def verify_projection(columns,lhs,monomials,retained_indices,recipes,projected_rows,projected_rhs,receipt,*,
                      deadline=None,max_audit_operations=900000000,max_audit_cells=60000000,
                      max_coefficient_bits=4096,max_receipt_bytes=8388608,authorized_limits=None):
    limits=dict(LIMITS if authorized_limits is None else authorized_limits)
    if set(limits)!=set(LIMITS) or any(type(v)is not int or v<1 for v in limits.values()):raise ValueError('complete strict authorized projection limits')
    budget=BASIS.Budget(deadline,max_audit_operations,max_audit_cells,max_coefficient_bits)
    if type(receipt)is not dict:raise ValueError('explicit bounded projection receipt')
    payload=encoded(receipt);budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    if len(payload)>max_receipt_bytes:raise OverflowError('independent projection receipt byte cap')
    if receipt.get('schema')!=SCHEMA:raise ValueError('known exact equation projection schema')
    for key in FLAGS:
        if key in receipt and receipt[key]is not False:raise ValueError('projection cannot claim cone feasibility')
    if receipt.get('status')=='unknown':
        if receipt.get('complete')is not False or projected_rows is not None or projected_rhs is not None:
            raise ValueError('UNKNOWN projection never authorizes rank preprocessing')
        if type(receipt.get('reason'))is not str or not receipt['reason']:raise ValueError('explicit UNKNOWN projection reason')
        if 'limits' in receipt:_limits(receipt['limits'],limits,max_receipt_bytes)
        if 'counts' in receipt:
            if type(receipt['counts'])is not dict or any(type(v)is not int or v<0 for v in receipt['counts'].values()) or receipt['counts'].get('receipt_bytes')!=len(payload):raise ValueError('strict partial projection counters')
        return dict(verified=True,complete=False,projection_authorized=False,row_basis_transfer_authorized=False,
            partial_identities_not_replayed=True,reason=receipt['reason'],audit_operations=budget.operations,audit_cells=budget.cells,
            independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)
    if receipt.get('status')!='complete' or receipt.get('complete')is not True:raise ValueError('strict complete-or-UNKNOWN projection')
    declared=_limits(receipt.get('limits'),limits,max_receipt_bytes);budget.bits=min(budget.bits,declared['max_coefficient_bits'])
    if type(columns)is not list or not columns or type(lhs)is not dict or type(monomials)is not list or any(type(p)is not dict for p in columns):raise ValueError('complete original source/target')
    n=len(columns);m=len(monomials)
    source_cells=sum(map(len,columns))+len(lhs)
    if source_cells>declared['max_source_cells']:raise ValueError('complete producer source cell cap')
    if m>source_cells:raise ValueError('complete monomial domain exceeds source keys')
    budget.charge(n+m,cells=n+m)
    if type(retained_indices)is not list or not retained_indices or any(type(j)is not int or not 0<=j<n for j in retained_indices) or len(set(retained_indices))!=len(retained_indices) or type(recipes)is not dict:
        raise ValueError('unique retained ORIGINAL columns')
    if any(type(j)is not int or not 0<=j<n for j in recipes) or set(retained_indices)&set(recipes) or set(retained_indices)|set(recipes)!=set(range(n)):
        raise ValueError('complete disjoint original-column partition')
    retained_set=set(retained_indices)
    if any(type(recipe)is not dict or any(type(j)is not int or j not in retained_set for j in recipe) for recipe in recipes.values()):raise ValueError('dependencies on retained original columns only')
    try:domain=set(monomials)
    except TypeError as error:raise ValueError('hashable exact monomial labels') from error
    if len(domain)!=m or domain!=set(lhs)|{label for p in columns for label in p}:raise ValueError('complete unique original monomial domain')
    source_cells=sum(map(len,columns))+len(lhs)
    if source_cells>declared['max_source_cells']:raise ValueError('complete producer source cell cap')
    producer_ops=n+m+len(retained_indices)+len(recipes)+sum(map(len,recipes.values()))+len(lhs)+sum(len(p)+1 for p in columns)+m
    budget.charge(producer_ops,cells=source_cells+2*m,live=2*m)
    peak=2*m
    def live(value):
        nonlocal peak
        peak=max(peak,value);budget.charge(0,live=value)
        if value>declared['max_live_cells']:raise ValueError('complete producer private live cap')
    def fingerprint(value):
        nonlocal producer_ops
        b=encoded(value);producer_ops+=len(b)//64+1;budget.charge(len(b)//64+1)
        return hashlib.sha256(b).hexdigest()
    lookup={label:i for i,label in enumerate(monomials)};live(m)
    domain_hash=fingerprint(monomials)
    rhs=[budget.rational(lhs.get(label,F(0))) for label in monomials];producer_ops+=m
    target_hash=fingerprint(list(map(str,rhs)))
    h=hashlib.sha256();h.update(b'[')
    for i,column in enumerate(columns):
        live(2*m+len(column));sorting=len(column)*max(1,len(column).bit_length())
        producer_ops+=sorting;budget.charge(sorting)
        if i:h.update(b',')
        h.update(b'[');row_bytes=2
        for k,label in enumerate(sorted(column,key=lookup.__getitem__)):
            q=budget.rational(column[label]);producer_ops+=1
            term=encoded([lookup[label],str(q)]);row_bytes+=len(term)+int(k>0)
            if k:h.update(b',')
            h.update(term)
        h.update(b']');producer_ops+=row_bytes//64+1;budget.charge(row_bytes//64+1)
    h.update(b']');columns_hash=h.hexdigest()
    source_hash=fingerprint(dict(full_columns_hash=columns_hash,monomial_domain_hash=domain_hash,target_hash=target_hash))
    recipe_payload=[];recipe_payload_bytes=2;identities=0;recipe_cells=0
    for omitted,recipe in sorted(recipes.items()):
        clean={};entry_bytes=5+len(str(omitted))
        for j,value in sorted(recipe.items()):
            q=budget.rational(value);producer_ops+=1
            if q:
                entry_bytes+=len(encoded([j,str(q)]))+int(bool(clean))
                if recipe_payload_bytes+entry_bytes+1024>declared['max_receipt_bytes']:raise ValueError('completed recipe receipt budget')
                clean[j]=q
        recipe_cells+=len(recipe)
        entry=[omitted,[[j,str(q)] for j,q in clean.items()]]
        recipe_payload_bytes+=len(encoded(entry))+int(bool(recipe_payload));recipe_payload.append(entry)
        reconstructed={}
        for j,multiplier in clean.items():
            for label,q in columns[j].items():
                product=budget.rational(multiplier*q);value=budget.rational(reconstructed.get(label,F(0))+product)
                producer_ops+=4;budget.charge(2,cells=2)
                if value:
                    if label not in reconstructed:live(2*m+len(reconstructed)+1)
                    reconstructed[label]=value
                else:reconstructed.pop(label,None)
        original={label:F(q) for label,q in columns[omitted].items() if q}
        live(2*m+len(reconstructed)+len(original));producer_ops+=len(original)+len(reconstructed)
        budget.charge(len(original)+len(reconstructed),cells=len(original)+len(reconstructed))
        if reconstructed!=original:raise ValueError('complete coefficientwise omitted column identity '+str(omitted))
        identities+=1
    projection_hash=fingerprint(dict(full_source_hash=source_hash,retained_indices=retained_indices,recipes=recipe_payload))
    for key,value in dict(monomial_domain_hash=domain_hash,target_hash=target_hash,full_columns_hash=columns_hash,
            full_source_hash=source_hash,projection_hash=projection_hash).items():
        if receipt.get(key)!=value:raise ValueError('independent exact projection fingerprint '+key)
    if receipt.get('retained_indices')!=retained_indices or any(type(j)is not int for j in receipt['retained_indices']):raise ValueError('retained original column order')
    if receipt.get('recipes')!=recipe_payload or encoded(receipt.get('recipes'))!=encoded(recipe_payload):raise ValueError('complete exact dependency recipe receipt')
    for key,value in [('original_columns',n),('projected_columns',len(retained_indices)),('rows',m)]:
        if type(receipt.get(key))is not int or receipt[key]!=value:raise ValueError('complete projection dimensions '+key)
    if receipt.get('projection_use')!=USE or any(receipt.get(key)!='identity' for key in ('solver_variable_mapping','solver_cone_mapping','solver_objective_mapping','target_mapping')):
        raise ValueError('row-span preprocessing preserves FULL solver variables/cone/objective and target')
    if type(projected_rows)is not list or len(projected_rows)!=m or type(projected_rhs)is not list or len(projected_rhs)!=m:raise ValueError('complete projected sparse equations')
    for target,expected in zip(projected_rhs,rhs):
        if budget.rational(target)!=expected:raise ValueError('unchanged exact augmented target')
    for row in projected_rows:
        if type(row)is not dict or any(type(j)is not int or not 0<=j<len(retained_indices) for j in row):raise ValueError('bounded projected equation coordinates')
        for value in row.values():
            if not budget.rational(value):raise ValueError('projected sparse rows omit exact zero entries')
    # Audit the supplied projected rows by reconstructing from retained columns.
    # Iterate each selected original column; missing coefficients are never guessed.
    nonzero=0
    for new,original in enumerate(retained_indices):
        for label,value in columns[original].items():
            producer_ops+=1;budget.charge(cells=1)
            q=F(value)
            if q:
                nonzero+=1;live(3*m+nonzero)
                if projected_rows[lookup[label]].get(new)!=q:raise ValueError('retained-column coefficient projection')
    live(3*m)
    if sum(map(len,projected_rows))!=nonzero:raise ValueError('no extra projected coefficients')
    # Canonical exact-row source hash, streamed over the complete supplied rows.
    h=hashlib.sha256();h.update(b'{"rhs":');b=encoded(list(map(str,rhs)));h.update(b)
    producer_ops+=len(b)//64+1;budget.charge(len(b)//64+1)
    h.update(b',"rows":[')
    for i,row in enumerate(projected_rows):
        if i:h.update(b',')
        h.update(b'[');row_bytes=2
        for k,j in enumerate(sorted(row)):
            term=encoded([j,str(F(row[j]))]);row_bytes+=len(term)+int(k>0)
            if k:h.update(b',')
            h.update(term)
        h.update(b']');amount=len(row)*max(1,len(row).bit_length())+row_bytes//64+1
        producer_ops+=amount;budget.charge(amount,cells=len(row))
    h.update(b'],"variables":');h.update(str(len(retained_indices)).encode());h.update(b'}')
    if receipt.get('projected_rows_hash')!=h.hexdigest():raise ValueError('complete projected augmented-row hash')
    producer_ops+=1
    counts=dict(operations=producer_ops,source_cells=source_cells,peak_live_cells=peak,identities_verified=identities,
        recipe_cells=recipe_cells,projected_cells=nonzero,receipt_bytes=len(payload))
    if receipt.get('counts')!=counts or any(type(v)is not int for v in receipt['counts'].values()):raise ValueError('independently replayed complete projection resource counts')
    if producer_ops>declared['max_operations']:raise ValueError('complete producer projection operation cap')
    elapsed=receipt.get('elapsed_seconds')
    if type(elapsed)not in (int,float) or not math.isfinite(elapsed) or elapsed<0:raise ValueError('finite projection diagnostic time')
    return dict(verified=True,complete=True,projection_authorized=True,row_basis_transfer_authorized=True,
        all_omitted_column_identities_verified=True,augmented_projection_injective=True,unchanged_rhs=True,
        optimization_variables=n,rank_computation_coordinates=len(retained_indices),solver_variable_mapping='identity',
        solver_cone_mapping='identity',solver_objective_mapping='identity',full_source_hash=source_hash,
        projected_rows_hash=h.hexdigest(),counts=counts,audit_operations=budget.operations,audit_cells=budget.cells,
        audit_peak_private_cells=budget.peak_live_cells,
        independent_audit_work_reserve=budget.operations+len(payload)+source_cells+nonzero+1,**FLAGS)


def verify_projection_basis(columns,lhs,monomials,retained_indices,recipes,projected_rows,projected_rhs,projection_receipt,
                            selected_projected_rows,selected_projected_rhs,basis_receipt,*,selected_full_rows=None,
                            selected_full_rhs=None,deadline=None,max_audit_operations=900000000,max_audit_cells=60000000):
    """Transfer a complete projected augmented basis to selected FULL source equations."""
    projection=verify_projection(columns,lhs,monomials,retained_indices,recipes,projected_rows,projected_rhs,projection_receipt,
        deadline=deadline,max_audit_operations=max_audit_operations,max_audit_cells=max_audit_cells)
    if not projection['projection_authorized']:
        if selected_full_rows is not None or selected_full_rhs is not None:raise ValueError('UNKNOWN projection cannot select full equations')
        return dict(verified=True,complete=False,reduction_authorized=False,projection=projection,
            audit_operations=projection['audit_operations'],audit_cells=projection['audit_cells'],
            independent_audit_work_reserve=projection['independent_audit_work_reserve'],**FLAGS)
    remaining=max_audit_operations-projection['audit_operations'];cells=max_audit_cells-projection['audit_cells']
    if remaining<1 or cells<1:raise OverflowError('combined independent projection/basis reserve')
    basis=BASIS.verify_rows(projected_rows,projected_rhs,len(retained_indices),selected_projected_rows,selected_projected_rhs,basis_receipt,
        deadline=deadline,max_audit_operations=remaining,max_audit_cells=cells)
    if not basis['reduction_authorized']:
        if selected_full_rows is not None or selected_full_rhs is not None:raise ValueError('UNKNOWN basis cannot select full equations')
        return dict(verified=True,complete=False,reduction_authorized=False,projection=projection,basis=basis,
            audit_operations=projection['audit_operations']+basis['audit_operations'],audit_cells=projection['audit_cells']+basis['audit_cells'],
            independent_audit_work_reserve=projection['independent_audit_work_reserve']+basis['independent_audit_work_reserve'],**FLAGS)
    indices=basis_receipt['retained_indices']
    if (selected_full_rows is None)!=(selected_full_rhs is None):raise ValueError('paired complete original row/target outputs')
    extra_cells=extra_operations=0
    if selected_full_rows is not None:
        if type(selected_full_rows)is not list or type(selected_full_rhs)is not list or len(selected_full_rows)!=len(indices) or selected_full_rhs!=[projected_rhs[i] for i in indices]:raise ValueError('selected FULL original equality targets')
        positions={monomials[i]:k for k,i in enumerate(indices)};expected=[{} for _ in indices]
        for j,column in enumerate(columns):
            for label,q in column.items():
                extra_operations+=1
                if label in positions and q:expected[positions[label]][j]=F(q);extra_cells+=1
        if selected_full_rows!=expected:raise ValueError('selection must use FULL original equations, never projected columns')
        for row in selected_full_rows:
            if type(row)is not dict or any(type(j)is not int or not 0<=j<len(columns) for j in row) or any(type(q)not in (int,F) for q in row.values()):raise ValueError('exact selected FULL original row coordinates')
        if any(type(q)not in (int,F) for q in selected_full_rhs):raise ValueError('exact unchanged FULL equality targets')
    operations=projection['audit_operations']+basis['audit_operations']+extra_operations
    cells=projection['audit_cells']+basis['audit_cells']+extra_cells
    if operations>max_audit_operations or cells>max_audit_cells:raise OverflowError('combined independent projection/basis replay cap')
    return dict(verified=True,complete=True,reduction_authorized=True,original_equation_indices=indices,
        full_original_equations_selected=True,optimization_variables=len(columns),solver_variable_mapping='identity',
        solver_cone_mapping='identity',solver_objective_mapping='identity',projection=projection,basis=basis,
        audit_operations=operations,audit_cells=cells,
        independent_audit_work_reserve=projection['independent_audit_work_reserve']+basis['independent_audit_work_reserve']+extra_operations+extra_cells+1,**FLAGS)
