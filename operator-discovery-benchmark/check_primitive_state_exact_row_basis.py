"""Independent capped replay of exact augmented-row basis selection.

No producer or numerical solver imports. Complete tapes establish equivalence
of the selected ORIGINAL equalities only. UNKNOWN tapes authorize no reduction.
Counters below are declared sparse-entry/rational-work proxies, not RSS or time.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

SCHEMA='primitive-state-exact-augmented-row-basis-v1'
ORDER='initial augmented nonzero count, then original row index'
LIMITS=dict(max_operations=450000000,max_source_cells=4000000,max_live_cells=4000000,
    max_fill_cells=20000000,max_coefficient_bits=4096,max_receipt_bytes=8388608)
FLAGS=dict(certified=False,exact_admission=False,infeasibility_proved=False,
    global_bound_proved=False,RH_proved=False)


def encoded(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


class Budget:
    def __init__(self,deadline,operations,cells,bits):
        if any(type(v)is not int or v<1 for v in (operations,cells,bits)):
            raise ValueError('positive strict independent audit caps')
        if deadline is not None and (type(deadline)not in (int,float) or not math.isfinite(deadline)):
            raise ValueError('finite absolute independent deadline')
        self.deadline=deadline;self.max_operations=operations;self.max_cells=cells;self.bits=bits
        self.operations=0;self.cells=0;self.peak_live_cells=0
    def charge(self,operations=1,cells=0,live=None):
        self.operations+=operations;self.cells+=cells
        if live is not None:self.peak_live_cells=max(self.peak_live_cells,live)
        if self.operations>self.max_operations or self.cells>self.max_cells or self.peak_live_cells>self.max_cells:
            raise OverflowError('independent exact row-basis audit cap')
        if self.deadline is not None and time.monotonic()>self.deadline:
            raise TimeoutError('independent exact row-basis audit deadline')
    def rational(self,value,text=False):
        self.charge()
        if text:
            if type(value)is not str or len(value)>4*self.bits+4 or any(c not in '0123456789+-/' for c in value):
                raise ValueError('bounded explicit rational transcript coefficient')
        elif type(value)not in (int,F):raise ValueError('exact source rational required')
        q=F(value)
        if text and str(q)!=value:raise ValueError('canonical rational transcript coefficient')
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.bits:
            raise OverflowError('independent exact coefficient bit cap')
        return q


def _source(rows,rhs,width,budget,source_cap):
    if type(width)is not int or width<1 or type(rows)is not list or type(rhs)is not list or len(rows)!=len(rhs):
        raise ValueError('complete positive source dimensions')
    if len(rows)>source_cap:raise ValueError('completed producer source cell cap')
    # Independent canonical JSON fingerprint without duplicate dense matrices.
    h=hashlib.sha256();h.update(b'{"rhs":[');targets=[]
    for i,value in enumerate(rhs):
        q=budget.rational(value);targets.append(q)
        if i:h.update(b',')
        payload=encoded(str(q));h.update(payload);budget.charge(len(payload)//64+1)
    h.update(b'],"rows":[');sizes=[];source_cells=0;producer_ops=1+len(rhs);producer_peak=0
    for i,(row,b) in enumerate(zip(rows,targets)):
        if type(row)is not dict or any(type(j)is not int or not 0<=j<width for j in row):
            raise ValueError('unique bounded exact source row coordinates')
        source_cells+=len(row)+1;producer_peak=max(producer_peak,len(row)+1)
        budget.charge(len(row)*max(1,len(row).bit_length()),cells=len(row)+1,live=len(row)+1)
        if source_cells>source_cap:raise ValueError('completed producer source cell cap')
        nnz=0;row_bytes=2
        if i:h.update(b',')
        h.update(b'[')
        for k,(j,value) in enumerate(sorted(row.items())):
            q=budget.rational(value);nnz+=bool(q)
            if k:h.update(b',');row_bytes+=1
            term=b'['+str(j).encode()+b','+encoded(str(q))+b']'
            h.update(term);row_bytes+=len(term)
        h.update(b']');sizes.append(nnz+bool(b))
        producer_ops+=len(row)*max(1,len(row).bit_length())+len(row)+1+row_bytes//64+1
        budget.charge(row_bytes//64+1)
    h.update(b'],"variables":');h.update(str(width).encode());h.update(b'}')
    return h.hexdigest(),sizes,source_cells,producer_ops,producer_peak


def verify_rows(rows,rhs,n_variables,selected_rows,selected_rhs,receipt,*,deadline=None,
                max_audit_operations=900000000,max_audit_cells=60000000,
                max_coefficient_bits=4096,max_receipt_bytes=8388608,
                authorized_limits=None):
    """Replay all augmented equalities; source, column, cone and objective order stay fixed."""
    caps=dict(LIMITS if authorized_limits is None else authorized_limits)
    if set(caps)!=set(LIMITS) or any(type(v)is not int or v<1 for v in caps.values()):
        raise ValueError('complete strict authorized producer caps')
    if type(max_receipt_bytes)is not int or max_receipt_bytes<1:
        raise ValueError('strict independent receipt byte cap')
    budget=Budget(deadline,max_audit_operations,max_audit_cells,max_coefficient_bits)
    if type(receipt)is not dict:raise ValueError('bounded exact row-basis receipt')
    payload=encoded(receipt);budget.charge(len(payload)//64+1,cells=len(payload)//64+1)
    if len(payload)>max_receipt_bytes:raise OverflowError('independent receipt byte cap')
    if receipt.get('schema')!=SCHEMA:raise ValueError('known exact row-basis schema')
    for key in FLAGS:
        if key in receipt and receipt[key]is not False:raise ValueError('row reduction cannot claim cone proof')
    if receipt.get('status')=='unknown':
        if receipt.get('complete')is not False or selected_rows is not None or selected_rhs is not None:
            raise ValueError('UNKNOWN never authorizes selected equations')
        if type(receipt.get('reason'))is not str or not receipt['reason']:
            raise ValueError('explicit UNKNOWN reason')
        if type(n_variables)is not int or n_variables<1 or type(rows)is not list or type(rhs)is not list or len(rows)!=len(rhs):
            raise ValueError('complete source dimensions')
        for key,value in [('variables',n_variables),('original_rows',len(rows))]:
            if key in receipt and (type(receipt[key])is not int or receipt[key]!=value):raise ValueError('UNKNOWN source dimensions '+key)
        if 'limits' in receipt:_limits(receipt['limits'],caps,max_receipt_bytes)
        counts=receipt.get('counts')
        if counts is not None:
            if type(counts)is not dict or any(type(v)is not int or v<0 for v in counts.values()):raise ValueError('strict partial counts')
            if counts.get('receipt_bytes')!=len(payload):raise ValueError('UNKNOWN encoded receipt byte count')
        return dict(verified=True,complete=False,reduction_authorized=False,reason=receipt['reason'],
            partial_transcript_not_replayed=True,audit_operations=budget.operations,audit_cells=budget.cells,
            independent_audit_work_reserve=budget.operations+len(payload)+1,**FLAGS)
    if receipt.get('status')!='complete' or receipt.get('complete')is not True:
        raise ValueError('strict complete-or-UNKNOWN status')
    limits=_limits(receipt.get('limits'),caps,max_receipt_bytes)
    budget.bits=min(budget.bits,limits['max_coefficient_bits'])
    for key,value in [('variables',n_variables),('original_rows',len(rows) if type(rows)is list else None),('augmented_rhs_column',n_variables)]:
        if type(receipt.get(key))is not int or receipt[key]!=value:raise ValueError('complete original dimensions '+key)
    if receipt.get('ordering')!=ORDER or any(receipt.get(k)!='identity' for k in ('variable_mapping','objective_mapping','cone_mapping')):
        raise ValueError('deterministic source order and identity variable/cone/objective maps')
    source_hash,sizes,source_cells,producer_ops,producer_peak=_source(rows,rhs,n_variables,budget,limits['max_source_cells'])
    if receipt.get('source_hash')!=source_hash:raise ValueError('complete exact source fingerprint')
    if source_cells>limits['max_source_cells']:raise ValueError('completed producer source cell cap')
    order=sorted(range(len(rows)),key=lambda i:(sizes[i],i));budget.charge(len(order)*max(1,len(order).bit_length()))
    if receipt.get('row_order')!=order or any(type(i)is not int for i in receipt['row_order']):raise ValueError('complete deterministic original row order')
    producer_ops+=len(order)*max(1,len(order).bit_length())
    tape=receipt.get('transcript')
    if type(tape)is not list or len(tape)!=len(order):raise ValueError('every original augmented row needs a transcript')
    basis=[];by_pivot={};basis_cells=0;retained=[];pivots=[];inconsistent=[]
    fill_cells=0;steps_count=0;producer_live=producer_peak;peak=producer_peak
    def live(value):
        nonlocal producer_live,peak
        producer_live=value;peak=max(peak,value)
        if value>limits['max_live_cells']:raise ValueError('completed producer private live cell cap')
        budget.charge(0,live=value)
    def tape_budget(value):
        nonlocal producer_ops
        b=encoded(value);producer_ops+=len(b)//64+1
        budget.charge(len(b)//64+1,cells=len(b)//64+1)
    for original,record in zip(order,tape):
        budget.charge(len(rows[original])+1);producer_ops+=len(rows[original])+1
        if type(record)is not dict or set(record)!={'source_row','steps','pivot_column','normalization','basis_index'} or type(record['source_row'])is not int or record['source_row']!=original:
            raise ValueError('complete ordered transcript record')
        live(basis_cells+sizes[original])
        residual={j:F(q) for j,q in rows[original].items() if q}
        if rhs[original]:residual[n_variables]=F(rhs[original])
        live(basis_cells+len(residual))
        steps=record['steps']
        if type(steps)is not list:raise ValueError('explicit ordered elimination steps')
        for step in steps:
            if not residual:raise ValueError('no elimination after zero residual')
            budget.charge(len(residual));producer_ops+=len(residual)
            pivot=min(residual)
            if pivot not in by_pivot:raise ValueError('step must cancel the first available exact pivot')
            k=by_pivot[pivot]
            if type(step)is not list or len(step)!=2 or type(step[0])is not int or step[0]!=k:
                raise ValueError('prior normalized basis pivot index')
            multiplier=budget.rational(step[1],text=True)
            if multiplier!=residual[pivot]:raise ValueError('exact augmented cancellation multiplier')
            tape_budget(step);steps_count+=1
            for j,q in basis[k].items():
                product=budget.rational(multiplier*q);value=budget.rational(residual.get(j,F(0))-product)
                producer_ops+=4;budget.charge(2,cells=2)
                if value:
                    if j not in residual:fill_cells+=1
                    residual[j]=value
                else:residual.pop(j,None)
                live(basis_cells+len(residual))
            if pivot in residual:raise ValueError('exact cancellation failed')
        if residual:
            budget.charge(len(residual));producer_ops+=len(residual)
            pivot=min(residual)
            if pivot in by_pivot:raise ValueError('transcript omitted a necessary previous pivot cancellation')
            normalization=budget.rational(record['normalization'],text=True)
            index=len(basis)
            if type(record['pivot_column'])is not int or record['pivot_column']!=pivot or type(record['basis_index'])is not int or record['basis_index']!=index or normalization!=residual[pivot]:
                raise ValueError('retained first pivot and exact normalization')
            normalized={}
            for j,q in sorted(residual.items()):
                live(basis_cells+len(residual)+len(normalized)+1)
                normalized[j]=budget.rational(q/normalization);producer_ops+=1
            live(basis_cells+len(residual)+len(normalized));fill_cells+=len(normalized)
            tape_budget({'retained':original,'pivot':pivot})
            basis.append(normalized);by_pivot[pivot]=index;basis_cells+=len(normalized)
            retained.append(original);pivots.append(pivot)
            if pivot==n_variables:inconsistent.append(index)
            live(basis_cells)
        elif any(record[key]is not None for key in ('pivot_column','normalization','basis_index')):
            raise ValueError('zero residual has no retained pivot or normalization')
        tape_budget(dict(record,steps=[]))
        if fill_cells>limits['max_fill_cells']:raise ValueError('completed cumulative fill cap')
    for key,value in [('retained_indices',retained),('pivot_columns',pivots),('inconsistent_augmented_pivots',inconsistent)]:
        if receipt.get(key)!=value or any(type(i)is not int for i in receipt[key]):raise ValueError('complete '+key)
    if type(receipt.get('augmented_rank'))is not int or receipt['augmented_rank']!=len(basis):raise ValueError('exact augmented rank')
    if receipt.get('coefficient_consistency')!=('inconsistent' if inconsistent else 'consistent'):raise ValueError('explicit augmented RHS inconsistency diagnostic')
    if type(selected_rows)is not list or type(selected_rhs)is not list or selected_rows!=[rows[i] for i in retained] or selected_rhs!=[rhs[i] for i in retained]:
        raise ValueError('selected equations must be complete ORIGINAL equations')
    for row,target in zip(selected_rows,selected_rhs):
        if type(row)is not dict or any(type(j)is not int or not 0<=j<n_variables for j in row):
            raise ValueError('exact ORIGINAL selected row coordinates')
        for q in row.values():budget.rational(q)
        budget.rational(target)
    budget.charge(sum(len(rows[i])+1 for i in retained),cells=sum(len(rows[i])+1 for i in retained))
    producer_ops+=1
    counts=dict(operations=producer_ops,source_cells=source_cells,live_cells=producer_live,peak_live_cells=peak,
        fill_cells=fill_cells,transcript_steps=steps_count,receipt_bytes=len(payload))
    if receipt.get('counts')!=counts or any(type(v)is not int for v in receipt['counts'].values()):raise ValueError('independently replayed producer resource counts')
    if producer_ops>limits['max_operations']:raise ValueError('completed producer operation cap')
    elapsed=receipt.get('elapsed_seconds')
    if type(elapsed)not in (int,float) or not math.isfinite(elapsed) or elapsed<0:raise ValueError('finite diagnostic elapsed time')
    basis_hash=hashlib.sha256()
    for row in basis:
        # Two streamed passes keep huge sparse basis rows out of JSON buffers.
        ordered=sorted(row.items())
        row_bytes=2+max(0,len(row)-1)+sum(len(str(j))+len(encoded(str(q)))+3 for j,q in ordered)
        basis_hash.update(row_bytes.to_bytes(8,'big'));basis_hash.update(b'[')
        for k,(j,q) in enumerate(ordered):
            if k:basis_hash.update(b',')
            basis_hash.update(b'['+str(j).encode()+b','+encoded(str(q))+b']')
        basis_hash.update(b']')
        budget.charge(2*(row_bytes//64+1)+2*len(row),cells=len(row))
    return dict(verified=True,complete=True,reduction_authorized=True,original_rows=len(rows),retained_rows=len(retained),
        variables=n_variables,augmented_rank=len(basis),source_hash=source_hash,normalized_basis_sha256=basis_hash.hexdigest(),
        all_original_augmented_rows_replayed=True,identity_variables_cone_and_objective=True,
        inconsistent_augmented_pivots=inconsistent,counts=counts,audit_operations=budget.operations,audit_cells=budget.cells,
        audit_peak_private_cells=budget.peak_live_cells,
        independent_audit_work_reserve=budget.operations+len(payload)+source_cells+1,**FLAGS)


def _limits(record,authorized,receipt_cap):
    if type(record)is not dict or set(record)!=set(LIMITS) or any(type(v)is not int or v<1 for v in record.values()):
        raise ValueError('complete strict producer limits')
    if record['max_receipt_bytes']<256 or any(record[k]>authorized[k] for k in record) or record['max_receipt_bytes']>receipt_cap:
        raise ValueError('producer limits exceed authorized audit contract')
    return record
