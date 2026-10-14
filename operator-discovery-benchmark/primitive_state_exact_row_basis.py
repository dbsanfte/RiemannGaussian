"""Bounded exact augmented-row basis selection; variables and cones unchanged.

The selected equations are ORIGINAL equations, not the elimination residuals.
An incomplete run never supplies a reduced system. No floating rank decisions.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

SCHEMA='primitive-state-exact-augmented-row-basis-v1'
ORDER='initial augmented nonzero count, then original row index'

class _Limit(Exception):
    pass


def _json(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def reduce_rows(rows,rhs,n_variables,*,deadline,max_operations=450000000,
                max_source_cells=4000000,max_live_cells=4000000,
                max_fill_cells=20000000,max_coefficient_bits=4096,
                max_receipt_bytes=8388608):
    """Return ``(selected_rows, selected_rhs, receipt)`` or ``(None,None,unknown)``.

    Column n_variables is the augmented RHS. A pivot there is an exact linear
    inconsistency, is retained, and is never mistaken for a removable zero row.
    ``steps`` subtract multipliers times normalized previous pivot residuals.
    Each retained residual is divided by its explicit normalization coefficient.
    A replay checker can establish every omitted source row lies in their span.

    Limits charge sparse rational work, cumulative new fill, live private cells,
    and exact encoded receipt bytes. Native execution and solver calls absent.
    """
    if type(n_variables)is not int or n_variables<1:raise ValueError('positive variable count')
    if type(rows)is not list or type(rhs)is not list or len(rows)!=len(rhs):raise ValueError('row/target schema')
    if type(deadline)not in (int,float) or not math.isfinite(deadline):raise ValueError('finite absolute deadline')
    caps=dict(max_operations=max_operations,max_source_cells=max_source_cells,
        max_live_cells=max_live_cells,max_fill_cells=max_fill_cells,
        max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_receipt_bytes)
    if any(type(v)is not int or v<1 for v in caps.values()):raise ValueError('positive strict resource caps')
    if max_receipt_bytes<256:raise ValueError('receipt cap must allow a 256-byte UNKNOWN envelope')
    started=time.monotonic();counts=dict(operations=0,source_cells=0,live_cells=0,peak_live_cells=0,fill_cells=0,transcript_steps=0,receipt_bytes=0)
    receipt=dict(schema=SCHEMA,status='unknown',complete=False,ordering=ORDER,
        variables=n_variables,original_rows=len(rows),augmented_rhs_column=n_variables,
        source_hash=None,retained_indices=[],pivot_columns=[],row_order=[],transcript=[],
        inconsistent_augmented_pivots=[],variable_mapping='identity',
        objective_mapping='identity',cone_mapping='identity',limits=caps,counts=counts)
    # Bounded serialized transcript budget reserves metadata and final summary.
    base_bytes=len(_json(receipt))+1024;transcript_bytes=0
    def charge(amount=1):
        counts['operations']+=amount
        if counts['operations']>max_operations:raise _Limit('operation cap')
        if time.monotonic()>deadline:raise _Limit('deadline')
    def rational(value):
        if type(value)not in (int,F):raise ValueError('exact rational coefficients required')
        charge();q=F(value)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise _Limit('coefficient bit cap')
        return q
    def live(value):
        if value>max_live_cells:
            receipt['blocked_live_cells']=value;raise _Limit('live cell cap')
        counts['live_cells']=value;counts['peak_live_cells']=max(counts['peak_live_cells'],value)
    def fill(amount):
        counts['fill_cells']+=amount
        if counts['fill_cells']>max_fill_cells:raise _Limit('cumulative fill cap')
    def budget(value):
        nonlocal transcript_bytes
        encoded=len(_json(value));charge(encoded//64+1);transcript_bytes+=encoded+1
        if base_bytes+transcript_bytes>max_receipt_bytes:raise _Limit('receipt byte cap')
    try:
        charge()
        source_hash=hashlib.sha256();source_hash.update(b'{"rhs":[')
        for i,b in enumerate(rhs):
            b=rational(b)
            if i:source_hash.update(b',')
            source_hash.update(_json(str(b)))
        source_hash.update(b'],"rows":[')
        sizes=[]
        # Streaming source fingerprint avoids a duplicate giant JSON matrix.
        for i,(row,b) in enumerate(zip(rows,rhs)):
            if type(row)is not dict or any(type(j)is not int or not 0<=j<n_variables for j in row):raise ValueError('sparse row schema')
            counts['source_cells']+=len(row)+1
            if counts['source_cells']>max_source_cells:raise _Limit('source cell cap')
            live(len(row)+1)
            charge(len(row)*max(1,len(row).bit_length()))
            nnz=0;payload_bytes=2
            if i:source_hash.update(b',')
            source_hash.update(b'[')
            for k,j in enumerate(sorted(row)):
                q=rational(row[j]);nnz+=bool(q);payload=_json([j,str(q)])
                payload_bytes+=len(payload)+int(k>0)
                if k:source_hash.update(b',')
                source_hash.update(payload)
            source_hash.update(b']')
            b=rational(b);sizes.append(nnz+bool(b));charge(payload_bytes//64+1)
        source_hash.update(b'],"variables":');source_hash.update(str(n_variables).encode());source_hash.update(b'}')
        receipt['source_hash']=source_hash.hexdigest()
        order=sorted(range(len(rows)),key=lambda i:(sizes[i],i));receipt['row_order']=order
        base_bytes+=len(_json(order));charge(len(order)*max(1,len(order).bit_length()))
        if base_bytes>max_receipt_bytes:raise _Limit('receipt byte cap')
        basis={};basis_cells=0
        for i in order:
            charge(len(rows[i])+1)
            live(basis_cells+sizes[i])
            residual={j:F(q) for j,q in rows[i].items() if q}
            if rhs[i]:residual[n_variables]=F(rhs[i])
            live(basis_cells+len(residual));steps=[]
            while residual:
                charge(len(residual));pivot=min(residual)
                if pivot not in basis:break
                basis_index,normalized=basis[pivot];multiplier=residual[pivot]
                step=[basis_index,str(multiplier)];budget(step);steps.append(step);counts['transcript_steps']+=1
                for j,q in normalized.items():
                    charge(2)
                    product=rational(multiplier*q);value=rational(residual.get(j,F(0))-product)
                    if value:
                        if j not in residual:fill(1)
                        residual[j]=value
                    else:residual.pop(j,None)
                    live(basis_cells+len(residual))
                if pivot in residual:raise RuntimeError('exact pivot cancellation failed')
            record=dict(source_row=i,steps=steps,pivot_column=None,normalization=None,basis_index=None)
            if residual:
                pivot=min(residual);normalization=residual[pivot];normalized={}
                for j,q in sorted(residual.items()):
                    live(basis_cells+len(residual)+len(normalized)+1)
                    normalized[j]=rational(q/normalization)
                live(basis_cells+len(residual)+len(normalized));fill(len(normalized))
                budget({'retained':i,'pivot':pivot})
                index=len(receipt['retained_indices']);basis[pivot]=(index,normalized);basis_cells+=len(normalized)
                record.update(pivot_column=pivot,normalization=str(normalization),basis_index=index)
                receipt['retained_indices'].append(i);receipt['pivot_columns'].append(pivot)
                if pivot==n_variables:receipt['inconsistent_augmented_pivots'].append(index)
                live(basis_cells)
            # Step payload was already charged; charge only the per-row envelope.
            envelope=dict(record,steps=[]);budget(envelope);receipt['transcript'].append(record)
        receipt.update(status='complete',complete=True,augmented_rank=len(basis),
            coefficient_consistency='inconsistent' if receipt['inconsistent_augmented_pivots'] else 'consistent',
            elapsed_seconds=time.monotonic()-started)
        counts['receipt_bytes']=len(_json(receipt))+16
        if counts['receipt_bytes']>max_receipt_bytes:raise _Limit('receipt byte cap')
        # Stabilize the receipt size field (small decimal-length fixed point).
        for _ in range(3):counts['receipt_bytes']=len(_json(receipt))
        charge()
        for _ in range(3):counts['receipt_bytes']=len(_json(receipt))
        return [rows[i] for i in receipt['retained_indices']],[rhs[i] for i in receipt['retained_indices']],receipt
    except _Limit as error:
        receipt.update(status='unknown',complete=False,reason=str(error),elapsed_seconds=time.monotonic()-started)
        counts['receipt_bytes']=len(_json(receipt))
        if counts['receipt_bytes']>max_receipt_bytes:
            # Keep diagnostics under cap; a partial tape carries no admission.
            receipt['transcript']=[];receipt['row_order']=[];receipt['partial_transcript_omitted']=True
            counts['receipt_bytes']=len(_json(receipt))
        if counts['receipt_bytes']>max_receipt_bytes:
            receipt={k:receipt[k] for k in ('schema','status','complete','reason','variables','original_rows','source_hash','limits','counts')}
            counts['receipt_bytes']=len(_json(receipt))
        if len(_json(receipt))>max_receipt_bytes:
            receipt={k:receipt[k] for k in ('schema','status','complete','reason')}
        if 'counts' in receipt:
            for _ in range(3):counts['receipt_bytes']=len(_json(receipt))
        return None,None,receipt
