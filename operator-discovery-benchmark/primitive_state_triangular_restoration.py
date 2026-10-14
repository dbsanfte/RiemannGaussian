"""Bounded exact retained-tape affine restoration with one canonical cone lift."""
from fractions import Fraction as F
import hashlib
import json
import math
import time
import primitive_state_equation_projection as PROJECT
import primitive_state_basis_primal as SOURCE

SCHEMA='primitive-state-triangular-restoration-v1'
FLAGS=dict(SOURCE.FLAGS)
SEED_RULE='exact-binary64; negative FREE squares zero; all other free aggregates unchanged'
LIFT='child=0; storage_K=C; parent=P+4C; signed relations positive/negative parts'

def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(encoded(value)).hexdigest()

class Budget:
    def __init__(self,deadline,max_operations=125000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096):
        if type(deadline)not in (int,float) or not math.isfinite(deadline):raise ValueError('finite deadline')
        if any(type(v)is not int or v<1 for v in (max_operations,max_live_cells,max_fill_cells,max_bits)):raise ValueError('positive restoration caps')
        self.deadline=deadline;self.max_operations=max_operations;self.max_live_cells=max_live_cells;self.max_fill_cells=max_fill_cells;self.max_bits=max_bits
        self.operations=0;self.peak_live_cells=0;self.fill_cells=0
    def charge(self,n=1):
        self.operations+=n
        if self.operations>self.max_operations:raise OverflowError('restoration operation cap')
        if time.monotonic()>self.deadline:raise TimeoutError('restoration deadline')
    def q(self,value):
        self.charge()
        if type(value)is str:
            if len(value)>4*self.max_bits+4 or any(c not in '0123456789+-/' for c in value):raise ValueError('bounded rational text')
            q=F(value)
            if str(q)!=value:raise ValueError('canonical rational text')
        elif type(value)in (int,F):q=F(value)
        else:raise ValueError('exact rational required')
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.max_bits:raise OverflowError('restoration coefficient bits')
        return q
    def mul(self,a,b):return self.q(a*b)
    def add(self,a,b):return self.q(a+b)
    def div(self,a,b):return self.q(a/b)
    def cells(self,n):
        self.peak_live_cells=max(self.peak_live_cells,n)
        if n>self.max_live_cells:raise OverflowError('restoration live cells')
        self.charge()
    def fill(self,n=1):
        self.fill_cells+=n
        if self.fill_cells>self.max_fill_cells:raise OverflowError('restoration cumulative fill')
        self.charge(n)
    def counts(self):return dict(operations=self.operations,peak_live_cells=self.peak_live_cells,fill_cells=self.fill_cells)


def retained_replay(rows,rhs,n_variables,basis,budget,*,resident_cells=0):
    """Reconstruct exact normalized rows in insertion order; no new elimination."""
    if len(rows)!=len(rhs) or type(n_variables)is not int or n_variables<1:raise ValueError('exact projected row geometry')
    if basis.get('complete')is not True or basis.get('coefficient_consistency')!='consistent' or basis.get('inconsistent_augmented_pivots')!=[]:raise ValueError('complete consistent licensed tape')
    normalized=[];pivots=[];records=[];live=resident_cells+sum(map(len,rows))+len(rhs);steps=0;normalized_cells=0
    for record in basis['transcript']:
        budget.charge()
        if record.get('pivot_column')is None:continue
        source=record['source_row'];pivot=record['pivot_column'];index=record['basis_index']
        if type(source)is not int or not 0<=source<len(rows) or type(pivot)is not int or not 0<=pivot<n_variables or index!=len(normalized) or pivot in pivots:raise ValueError('retained tape indices')
        residual={j:budget.q(q) for j,q in rows[source].items() if q}
        if rhs[source]:residual[n_variables]=budget.q(rhs[source])
        budget.fill(len(residual));budget.cells(live+normalized_cells+len(residual))
        for k,text in record['steps']:
            if type(k)is not int or not 0<=k<len(normalized):raise ValueError('earlier normalized tape reference')
            multiplier=budget.q(text);steps+=1
            for j,q in normalized[k].items():
                new=budget.add(residual.get(j,F(0)),-budget.mul(multiplier,q))
                if new:
                    if j not in residual:budget.fill()
                    residual[j]=new
                else:residual.pop(j,None)
            budget.cells(live+normalized_cells+len(residual))
        if not residual or min(residual)!=pivot or residual[pivot]!=budget.q(record['normalization']):raise ValueError('exact retained pivot/normalization')
        norm=residual[pivot];row={j:budget.div(q,norm) for j,q in residual.items()};normalized.append(row);normalized_cells+=len(row);pivots.append(pivot);records.append(source)
    if records!=basis['retained_indices'] or pivots!=basis['pivot_columns'] or len(normalized)!=basis['augmented_rank']:raise ValueError('complete retained tape partition')
    # Hash private normalized augmented rows by insertion; bounded per-row encoding.
    h=hashlib.sha256()
    for pivot,row in zip(pivots,normalized):
        payload=encoded([pivot,[[j,str(q)] for j,q in sorted(row.items())]]);h.update(len(payload).to_bytes(8,'big'));h.update(payload);budget.charge(len(payload)//64+1)
    return normalized,pivots,dict(retained_rows=len(normalized),retained_steps=steps,normalized_basis_hash=h.hexdigest())


def back_substitute(normalized,pivots,seed,n_variables,budget):
    if len(seed)!=n_variables or len(set(pivots))!=len(pivots):raise ValueError('complete seed/pivot map')
    result=[budget.q(q) for q in seed];by_pivot=dict(zip(pivots,normalized))
    # Sparse source ordering is NOT pivot ordering. Descending COLUMN is required.
    for pivot in sorted(pivots,reverse=True):
        row=by_pivot[pivot]
        if row.get(pivot)!=1 or any(j<pivot for j in row):raise ValueError('normalized upper triangular row')
        value=row.get(n_variables,F(0))
        for j,q in row.items():
            if j not in (pivot,n_variables):value=budget.add(value,-budget.mul(q,result[j]))
        result[pivot]=budget.q(value)
    return result


def decode_source(cache,budget):
    original=cache['original'];labels=original['monomials'];rows=[{} for _ in labels];n=len(original['columns']);rhs=[budget.q(q) for q in original['rhs']]
    if len(rhs)!=len(rows):raise ValueError('full source rows/rhs')
    cells=0
    for j,column in enumerate(original['columns']):
        previous=-1
        for i,text in column:
            if type(i)is not int or not previous<i<len(rows):raise ValueError('ordered complete sparse columns')
            previous=i;q=budget.q(text)
            if not q:raise ValueError('nonzero sparse source')
            rows[i][j]=q;cells+=1;budget.cells(cells+len(rhs))
    return rows,rhs,n


def canonical_lift(projected,retained,shape,offset,specs,n_variables,budget):
    ns,nr=shape
    if specs!={'full_child':15,'full_parent':15,'storage_K':15} or n_variables!=offset+360:raise ValueError('canonical full15 quotient lift')
    values={j:budget.q(q) for j,q in zip(retained,projected)};x=[F(0)]*n_variables
    for j in range(ns):x[j]=values[j]
    for j in range(nr):
        beta=values[ns+2*j];x[ns+2*j]=max(beta,F(0));x[ns+2*j+1]=max(-beta,F(0))
    for j in range(ns+2*nr,offset):x[j]=values[j]
    for j in range(120):
        C=values[offset+j];P=values[offset+120+j];x[offset+240+j]=C;x[offset+120+j]=budget.add(P,budget.mul(F(4),C))
    return x


def exact_psd(matrix,budget):
    n=len(matrix)
    if not n or any(len(row)!=n for row in matrix) or any(matrix[i][j]!=matrix[j][i] for i in range(n) for j in range(n)):raise ValueError('exact symmetric PSD matrix')
    R=[row[:] for row in matrix];weights=[];vectors=[]
    for k in range(n):
        d=budget.q(R[k][k])
        if d<0:return dict(psd=False,witness=dict(kind='negative-schur-pivot',pivot=k,value=str(d)),rank=len(weights))
        if d==0:
            cross=next((i for i in range(k+1,n) if R[i][k]),None)
            if cross is not None:return dict(psd=False,witness=dict(kind='zero-pivot-nonzero-cross',pivot=k,cross=cross,value=str(R[cross][k])),rank=len(weights))
            continue
        v=[F(0)]*n;v[k]=F(1)
        for i in range(k+1,n):v[i]=budget.div(R[i][k],d)
        weights.append(d);vectors.append(v)
        for i in range(k+1,n):
            for j in range(i,n):R[i][j]=budget.add(R[i][j],-budget.mul(budget.mul(d,v[i]),v[j]));R[j][i]=R[i][j]
        for i in range(k,n):R[k][i]=R[i][k]=F(0)
    # Full LDL reconstruction including all zero pivots.
    for i in range(n):
        for j in range(n):
            value=F(0)
            for d,v in zip(weights,vectors):value=budget.add(value,budget.mul(budget.mul(d,v[i]),v[j]))
            if value!=matrix[i][j]:raise ValueError('exact LDL reconstruction')
    return dict(psd=True,rank=len(weights),weights=list(map(str,weights)),vectors=[[str(q) for q in v] for v in vectors])


def candidate_diagnostics(rows,rhs,x,offset,specs,budget):
    mismatches=[]
    for i,row in enumerate(rows):
        value=F(0)
        for j,q in row.items():value=budget.add(value,budget.mul(q,x[j]))
        if value!=rhs[i]:mismatches.append(dict(row=i,residual=str(budget.add(value,-rhs[i]))))
    negatives=[dict(coordinate=i,value=str(x[i])) for i in range(offset) if x[i]<0];psd=[];start=offset
    for name,n in sorted(specs.items()):
        matrix=[[F(0)]*n for _ in range(n)]
        for a in range(n):
            for b in range(a,n):matrix[a][b]=matrix[b][a]=x[start];start+=1
        psd.append(dict(name=name,**exact_psd(matrix,budget)))
    return dict(all_original_rows_checked=len(rows),equality_mismatch_count=len(mismatches),equality_mismatches=mismatches,negative_scalar_count=len(negatives),negative_scalars=negatives,psd=psd,
        candidate_cone_checks_pass=not mismatches and not negatives and all(q['psd'] for q in psd))


def restore(cache,trace,basis,projection,*,deadline,max_operations=125000000,max_live_cells=4000000,max_fill_cells=20000000,max_bits=4096,max_receipt_bytes=8388608,checkpoint=None):
    if type(max_receipt_bytes)is not int or max_receipt_bytes<1024:raise ValueError('positive bounded restoration receipt')
    budget=Budget(deadline,max_operations,max_live_cells,max_fill_cells,max_bits);start=time.monotonic()
    out=dict(schema=SCHEMA,status='unknown',complete=False,candidate_original_vector=None,seed_rule=SEED_RULE,lift=LIFT,backsub_order='descending pivot column',limits=dict(max_operations=max_operations,max_live_cells=max_live_cells,max_fill_cells=max_fill_cells,max_bits=max_bits,max_receipt_bytes=max_receipt_bytes),**FLAGS)
    def save(phase):
        if checkpoint:checkpoint(dict(phase=phase,status=out['status'],counts=budget.counts(),candidate_available=out['candidate_original_vector']is not None,**FLAGS))
    try:
        out['input_bindings']={name:digest(v) for name,v in [('cache',cache),('trace',trace),('basis',basis),('projection',projection)]};budget.charge(sum(len(encoded(v))//64+1 for v in [cache,trace,basis,projection]));save('source_decode')
        rows,rhs,n=decode_source(cache,budget);o=cache['original'];specs=dict(o['specs']);shape=o['shape'];offset=o['offset'];retained,recipes=PROJECT.full15_recipes(shape,offset,specs,n)
        if projection.get('complete')is not True or projection.get('retained_indices')!=retained or projection.get('recipes')!=[[j,[[k,str(q)] for k,q in sorted(v.items())]] for j,v in sorted(recipes.items())]:raise ValueError('licensed complete declared projection recipes')
        if basis.get('source_hash')!=projection.get('projected_rows_hash'):raise ValueError('licensed basis projection source')
        positions={j:i for i,j in enumerate(retained)};projected_rows=[{positions[j]:q for j,q in row.items() if j in positions} for row in rows];budget.cells(sum(map(len,rows))+sum(map(len,projected_rows))+len(rhs));save('retained_replay')
        normalized,pivots,info=retained_replay(projected_rows,rhs,len(retained),basis,budget,resident_cells=sum(map(len,rows)));out.update(info,retained_indices=retained,pivot_columns=sorted(pivots));save('seed')
        raw=trace.get('original_vector')
        if type(raw)is not list or len(raw)!=n or any(type(v)not in (int,float) or not math.isfinite(v) for v in raw):raise ValueError('complete finite unchanged native original vector')
        raw_exact=[budget.q(F(float(v))) for v in raw];seed=[raw_exact[j] for j in retained]
        for j,recipe in recipes.items():
            for k,q in recipe.items():i=positions[k];seed[i]=budget.add(seed[i],budget.mul(q,raw_exact[j]))
        clipped=[];pivotset=set(pivots)
        for i,j in enumerate(retained):
            if j<shape[0] and i not in pivotset and seed[i]<0:seed[i]=F(0);clipped.append(j)
        out.update(clipped_free_square_indices=clipped,seed_projected_vector=list(map(str,seed)));save('back_substitution')
        restored=back_substitute(normalized,pivots,seed,len(retained),budget);out['restored_projected_vector']=list(map(str,restored));save('canonical_lift')
        candidate=canonical_lift(restored,retained,shape,offset,specs,n,budget);out['candidate_original_vector']=list(map(str,candidate));out['candidate_hash']=digest(out['candidate_original_vector']);save('exact_original_checks')
        out['diagnostics']=candidate_diagnostics(rows,rhs,candidate,offset,specs,budget);out.update(status='restored',complete=True);save('restored')
    except Exception as e:
        out.update(status='unknown' if isinstance(e,(OverflowError,TimeoutError,MemoryError)) else 'rejected',complete=False,reason=str(e) or type(e).__name__,error_type=type(e).__name__)
    out.update(counts=budget.counts(),elapsed_seconds=time.monotonic()-start)
    payload=encoded(out)
    if len(payload)>max_receipt_bytes:
        out={k:out[k] for k in ['schema','seed_rule','lift','backsub_order','limits','counts',*FLAGS]};out.update(status='unknown',complete=False,candidate_original_vector=None,reason='restoration receipt byte cap')
    return out
