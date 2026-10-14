"""Hash-free bounded exact affine feedback reduction and one canonical repair.

The feedback equation is necessary for one formal identity.  Consistency of
these equations is neither cone feasibility nor a universal identity proof.
"""
from fractions import Fraction as F
import json
import math
import time

SCHEMA='primitive-state-feedback-affine-v1'
CHART_SCHEMA='primitive-state-feedback-affine-chart-v1'
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,
           candidate_admitted=False,exact_admission=False,infeasibility_proved=False,
           cone_feasibility_proved=False,all_scale_identity_proved=False,
           source_equations_independently_verified=False)
POLICY=dict(reduction='all old pivot columns in ascending order, even beyond leading free column',
            pivot='smallest nonzero old free column',
            repair='preserve every other old free coordinate of the single exact publication021 seed',
            substitution='descending pivot column',
            lift='child=0; storage_K=C; parent=P+4*C; beta positive/negative parts',
            optimization='none; no objective preservation or cone feasibility claim')

def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()

class Budget:
    def __init__(self,deadline,max_operations=150000000,max_cells=6000000,max_bits=4096):
        if type(deadline)not in(int,float)or not math.isfinite(deadline):raise ValueError('finite deadline')
        if any(type(v)is not int or v<1 for v in(max_operations,max_cells,max_bits))or max_operations>150000000 or max_cells>6000000 or max_bits>4096:raise ValueError('positive bounded exact limits')
        self.deadline=deadline;self.max_operations=max_operations;self.max_cells=max_cells;self.max_bits=max_bits
        self.operations=0;self.peak_cells=0;self.maximum_bits=0;self.resident_cells=0
    def charge(self,n=1):
        if type(n)is not int or n<0:raise ValueError('nonnegative work')
        if n>self.max_operations-self.operations:raise OverflowError('exact operation cap')
        self.operations+=n
        if time.monotonic()>self.deadline:raise TimeoutError('exact deadline')
    def cells(self,n):
        self.charge();n+=self.resident_cells;self.peak_cells=max(self.peak_cells,n)
        if n>self.max_cells:raise OverflowError('live rational cell cap')
    def q(self,value):
        self.charge()
        if type(value)is str:
            parts=value.split('/')
            if len(parts)>2 or not value or any(not p or not p.lstrip('-').isdigit() for p in parts):raise ValueError('canonical rational text')
            # Validate text size before creating potentially large integers.
            if any(len(p.lstrip('-'))>int(self.max_bits*.30103)+2 for p in parts):raise OverflowError('rational text bit cap')
            nums=[int(p)for p in parts]
            if any(abs(n).bit_length()>self.max_bits for n in nums):raise OverflowError('rational integer bit cap')
            if len(nums)==2 and nums[1]<=0:raise ValueError('positive denominator')
            q=F(*nums)
            if str(q)!=value:raise ValueError('canonical reduced rational')
        elif type(value)in(int,F):q=F(value)
        else:raise ValueError('exact rational required')
        bits=max(abs(q.numerator).bit_length(),q.denominator.bit_length());self.maximum_bits=max(self.maximum_bits,bits)
        if bits>self.max_bits:raise OverflowError('rational result bit cap')
        return q
    def add(self,a,b):
        a=self.q(a);b=self.q(b);self.charge();return self.q(a+b)
    def mul(self,a,b):
        a=self.q(a);b=self.q(b);self.charge();return self.q(a*b)
    def div(self,a,b):
        a=self.q(a);b=self.q(b);self.charge()
        if not b:raise ValueError('nonzero divisor')
        return self.q(a/b)
    def counts(self):return dict(operations=self.operations,peak_live_cells=self.peak_cells,maximum_rational_bits=self.maximum_bits)

def full15_recipes(shape,offset,specs,n):
    if list(shape)!=[366,613]or offset!=1597 or specs!={'full_child':15,'full_parent':15,'storage_K':15}or n!=1957:raise ValueError('complete original full15 layout')
    recipes={366+2*j+1:{366+2*j:F(-1)}for j in range(613)}
    recipes.update({offset+240+j:{offset+j:F(1),offset+120+j:F(-4)}for j in range(120)})
    return [j for j in range(n)if j not in recipes],recipes

def decode_source(cache,budget):
    source=cache['original'];n=len(source['columns']);m=len(source['monomials'])
    if n!=1957 or m!=5641 or len(source['rhs'])!=m:raise ValueError('complete original source dimensions')
    if source['specs']!=[['full_child',15],['full_parent',15],['storage_K',15]]:raise ValueError('ordered full15 original specs')
    retained,recipes=full15_recipes(source['shape'],source['offset'],dict(source['specs']),n)
    columns=[];cells=0
    for raw in source['columns']:
        col={};previous=-1
        for i,text in raw:
            if type(i)is not int or not previous<i<m:raise ValueError('ordered source column domain')
            q=budget.q(text)
            if not q:raise ValueError('nonzero source column')
            col[i]=q;previous=i;cells+=1
        budget.cells(cells+m);columns.append(col)
    rhs=[budget.q(q)for q in source['rhs']]
    if len({tuple(v)for v in source['monomials']})!=m:raise ValueError('unique original monomial labels')
    return columns,rhs,retained,recipes

def verify_dependencies(columns,retained,recipes,budget):
    if sorted(retained+list(recipes))!=list(range(len(columns)))or len(set(retained))!=len(retained):raise ValueError('complete column partition')
    keep=set(retained)
    for omitted,recipe in sorted(recipes.items()):
        if not recipe or any(j not in keep for j in recipe):raise ValueError('retained-only recipes')
        expected={}
        for j,c in recipe.items():
            for i,q in columns[j].items():
                new=budget.add(expected.get(i,F(0)),budget.mul(c,q))
                if new:expected[i]=new
                else:expected.pop(i,None)
        if expected!=columns[omitted]:raise ValueError('exact omitted-column identity')
        budget.charge(len(expected)+len(columns[omitted]))
        budget.cells(len(expected))

def project_rows(columns,rhs,retained,budget):
    rows=[{}for _ in rhs];cells=0
    for j,original in enumerate(retained):
        for i,q in columns[original].items():rows[i][j]=q;cells+=1
    budget.charge(cells);budget.cells(cells+len(rhs))
    return rows

def sparse(raw,width,budget):
    result={};last=-1
    for j,text in raw:
        if type(j)is not int or not last<j<=width:raise ValueError('ordered sparse augmented row')
        q=budget.q(text)
        if not q:raise ValueError('nonzero sparse row')
        result[j]=q;last=j
    return result

def replay_retained(rows,rhs,width,tape,budget):
    if tape.get('complete')is not True or tape.get('coefficient_consistency')!='consistent' or tape.get('inconsistent_augmented_pivots')!=[]or tape.get('variables')!=width or tape.get('original_rows')!=len(rows):raise ValueError('complete consistent old tape')
    normalized=[];pivots=[];sources=[];cells=sum(map(len,rows))+len(rhs)
    for record in tape['transcript']:
        budget.charge()
        if record['pivot_column']is None:continue
        source=record['source_row'];pivot=record['pivot_column']
        if type(source)is not int or not 0<=source<len(rows)or type(pivot)is not int or not 0<=pivot<width or pivot in pivots or record['basis_index']!=len(normalized):raise ValueError('retained tape indices')
        residual=rows[source].copy()
        if rhs[source]:residual[width]=rhs[source]
        for k,text in record['steps']:
            if type(k)is not int or not 0<=k<len(normalized):raise ValueError('earlier tape reference')
            factor=budget.q(text)
            if not factor or residual.get(pivots[k],F(0))!=factor:raise ValueError('exact elimination multiplier')
            for j,q in normalized[k].items():
                value=budget.add(residual.get(j,F(0)),-budget.mul(factor,q))
                if value:residual[j]=value
                else:residual.pop(j,None)
        if not residual or min(residual)!=pivot or residual[pivot]!=budget.q(record['normalization']):raise ValueError('retained normalized pivot')
        row={j:budget.div(q,residual[pivot])for j,q in residual.items()};normalized.append(row);pivots.append(pivot);sources.append(source);cells+=len(row);budget.cells(cells+len(residual))
    if pivots!=tape['pivot_columns']or sources!=tape['retained_indices']or len(pivots)!=tape['augmented_rank']:raise ValueError('complete retained basis')
    return {p:row for p,row in zip(pivots,normalized)},dict(zip(pivots,sources))

def reduce_feedback(row,rhs,chart,width,budget):
    """Eliminate EVERY old pivot, regardless of leading remaining free entry."""
    if type(width)is not int or width<1 or any(type(j)is not int or not 0<=j<width for j in row)or any(type(p)is not int or not 0<=p<width for p in chart):raise ValueError('complete reduction coordinate domain')
    residual={j:budget.q(q)for j,q in row.items()if q}
    if rhs:residual[width]=budget.q(rhs)
    multipliers=[]
    for pivot in sorted(chart):
        normalized=chart[pivot]
        if normalized.get(pivot)!=1 or any(type(j)is not int or not pivot<=j<=width for j in normalized):raise ValueError('upper normalized old chart')
        factor=residual.get(pivot,F(0))
        if not factor:continue
        multipliers.append([pivot,str(factor)])
        for j,q in normalized.items():
            value=budget.add(residual.get(j,F(0)),-budget.mul(factor,q))
            if value:residual[j]=value
            else:residual.pop(j,None)
    if any(p in residual for p in chart):raise ValueError('all old pivots eliminated')
    coefficients=[j for j in residual if j<width]
    if coefficients:
        pivot=min(coefficients);norm=residual[pivot];new={j:budget.div(q,norm)for j,q in residual.items()};classification='independent'
    else:pivot=None;norm=None;new=None;classification='inconsistent'if residual.get(width,F(0))else'redundant'
    return classification,new,dict(multipliers=multipliers,residual_terms=[[j,str(q)]for j,q in sorted(residual.items())],chosen_pivot=pivot,normalization=None if norm is None else str(norm))

def aggregate_seed(original,retained,recipes,budget):
    x=[budget.q(q)for q in original];values={j:x[j]for j in retained}
    if len(x)!=len(retained)+len(recipes):raise ValueError('full original seed')
    for omitted,recipe in recipes.items():
        for j,c in recipe.items():values[j]=budget.add(values[j],budget.mul(c,x[omitted]))
    return [values[j]for j in retained]

def back_substitute(chart,seed,width,budget):
    if len(seed)!=width or any(type(p)is not int or not 0<=p<width for p in chart):raise ValueError('chart and seed width')
    x=[budget.q(q)for q in seed]
    for pivot in sorted(chart,reverse=True):
        row=chart[pivot]
        if row.get(pivot)!=1 or any(j<pivot or j>width for j in row):raise ValueError('normalized triangular chart')
        value=row.get(width,F(0))
        for j,q in row.items():
            if j not in(pivot,width):value=budget.add(value,-budget.mul(q,x[j]))
        x[pivot]=budget.q(value)
    return x

def canonical_lift(projected,retained,budget):
    if len(projected)!=1224 or len(retained)!=1224:raise ValueError('complete quotient coordinates')
    values=dict(zip(retained,projected));x=[F(0)]*1957
    for j in range(366):x[j]=values[j]
    for j in range(613):
        beta=values[366+2*j];x[366+2*j]=max(beta,F(0));x[367+2*j]=max(-beta,F(0))
    for j in range(1592,1597):x[j]=values[j]
    for j in range(120):x[1837+j]=values[1597+j];x[1717+j]=budget.add(values[1717+j],budget.mul(F(4),values[1597+j]))
    return x

def exact_psd(matrix,budget):
    n=len(matrix)
    if any(len(r)!=n for r in matrix)or any(matrix[i][j]!=matrix[j][i]for i in range(n)for j in range(n)):raise ValueError('symmetric exact matrix')
    R=[r[:]for r in matrix];L=[[F(int(i==j))for j in range(n)]for i in range(n)];D=[]
    def witness(k,cross=None):
        # Congruence coordinate y becomes original x through L^T x=y.
        y=[F(0)]*n;y[k]=F(1)
        if cross is not None:
            a=R[cross][k];d=R[cross][cross];y[cross]=budget.div(-a,budget.add(abs(d),F(1)));y[k]=F(1)
        x=[F(0)]*n
        for j in range(n-1,-1,-1):
            v=y[j]
            for i in range(j+1,n):v=budget.add(v,-budget.mul(L[i][j],x[i]))
            x[j]=budget.q(v)
        value=F(0)
        for i in range(n):
            for j in range(n):value=budget.add(value,budget.mul(budget.mul(x[i],matrix[i][j]),x[j]))
        if value>=0:raise ValueError('negative exact PSD witness')
        return dict(psd=False,rank=sum(d!=0 for d in D),witness=dict(kind='negative-schur-pivot'if cross is None else'zero-pivot-nonzero-cross',pivot=k,cross=cross,vector=list(map(str,x)),quadratic_value=str(value)))
    for k in range(n):
        d=budget.q(R[k][k])
        if d<0:return witness(k)
        if d==0:
            cross=next((i for i in range(k+1,n)if R[i][k]),None)
            if cross is not None:return witness(k,cross)
            D.append(F(0));continue
        D.append(d)
        for i in range(k+1,n):L[i][k]=budget.div(R[i][k],d)
        for i in range(k+1,n):
            for j in range(i,n):R[i][j]=budget.add(R[i][j],-budget.mul(budget.mul(d,L[i][k]),L[j][k]));R[j][i]=R[i][j]
        for i in range(k+1,n):R[i][k]=R[k][i]=F(0)
    return dict(psd=True,rank=sum(d!=0 for d in D),diagonal=list(map(str,D)),lower=[[str(q)for q in r]for r in L])

def diagnostics(columns,rhs,x,feedback,feedback_rhs,budget):
    values=[F(0)]*len(rhs)
    for j,col in enumerate(columns):
        for i,q in col.items():values[i]=budget.add(values[i],budget.mul(q,x[j]))
    mismatches=[dict(row=i,residual=str(budget.add(v,-rhs[i])))for i,v in enumerate(values)if v!=rhs[i]]
    value=F(0)
    for j,q in feedback.items():value=budget.add(value,budget.mul(q,x[j]))
    new_residual=budget.add(value,-feedback_rhs);negatives=[dict(coordinate=j,value=str(q))for j,q in enumerate(x[:1597])if q<0];blocks=[]
    for k,name in enumerate(('full_child','full_parent','storage_K')):
        matrix=[[F(0)]*15 for _ in range(15)];index=1597+120*k
        for i in range(15):
            for j in range(i,15):matrix[i][j]=matrix[j][i]=x[index];index+=1
        blocks.append(dict(name=name,**exact_psd(matrix,budget)))
    return dict(original_equations=len(rhs),original_equation_mismatches=mismatches,new_equation_residual=str(new_residual),affine_equalities_satisfied=not mismatches and not new_residual,negative_scalars=negatives,psd_blocks=blocks,all_cones_satisfied=not negatives and all(b['psd']for b in blocks))

def project_feedback(necessary,retained,recipes,budget):
    if necessary.get('schema')!='primitive-state-formal-identity-necessary-row-v1'or necessary.get('width')!=1957:raise ValueError('verified necessary-row format')
    full=sparse([[r['index'],r['coefficient']]for r in necessary['entries']],1956,budget);rhs=budget.q(necessary['rhs'])
    for omitted,recipe in recipes.items():
        expected=F(0)
        for j,c in recipe.items():expected=budget.add(expected,budget.mul(c,full.get(j,F(0))))
        if expected!=full.get(omitted,F(0)):raise ValueError('feedback row column dependency')
    if any(full.get(j,F(0))for j in range(1592,1597)):raise ValueError('constant slacks cancel in necessary row')
    return full,rhs,{j:full[original]for j,original in enumerate(retained)if original in full}

def build(cache,projection,basis,seed_endpoint,necessary,*,deadline,max_operations=150000000,max_cells=6000000,max_bits=4096,max_chart_bytes=33554432,max_receipt_bytes=8388608,checkpoint=None):
    """Return (compact chart, diagnostic receipt); UNKNOWN has no usable chart."""
    budget=Budget(deadline,max_operations,max_cells,max_bits)
    limits=dict(max_operations=max_operations,max_cells=max_cells,max_coefficient_bits=max_bits,max_chart_bytes=max_chart_bytes,max_receipt_bytes=max_receipt_bytes)
    out=dict(schema=SCHEMA,status='UNKNOWN',complete=False,classification=None,policy=POLICY,limits=limits,chart_available=False,reduction=None,initial_projected_vector=None,preserved_free_indices=None,candidate_projected_vector=None,candidate_original_vector=None,diagnostics=None,**FLAGS)
    def phase(name):
        budget.charge()
        if checkpoint:checkpoint(name,budget.counts())
    try:
        if type(max_chart_bytes)is not int or not 1024<=max_chart_bytes<=33554432 or type(max_receipt_bytes)is not int or not 1024<=max_receipt_bytes<=8388608:raise ValueError('bounded artifact caps')
        phase('decoding_source');columns,rhs,retained,recipes=decode_source(cache,budget)
        budget.resident_cells=sum(map(len,columns))+len(rhs)
        expected=[[j,[[k,str(q)]for k,q in sorted(r.items())]]for j,r in sorted(recipes.items())]
        if projection.get('complete')is not True or projection.get('retained_indices')!=retained or projection.get('recipes')!=expected:raise ValueError('actual complete projection declaration')
        phase('verifying_dependencies');verify_dependencies(columns,retained,recipes,budget);rows=project_rows(columns,rhs,retained,budget);width=len(retained)
        phase('replaying_retained_rows');chart,sources=replay_retained(rows,rhs,width,basis,budget)
        budget.resident_cells+=sum(map(len,rows))+sum(map(len,chart.values()))
        budget.cells(4*1957+4*1224+len(rhs)+3*15*15)
        if len(chart)!=779:raise ValueError('fixed old rank779')
        old_pivots=sorted(chart);free=[j for j in range(width)if j not in chart]
        if len(free)!=445:raise ValueError('fixed free445')
        fullrow,newrhs,projectedrow=project_feedback(necessary,retained,recipes,budget)
        phase('reducing_feedback');classification,new,reduction=reduce_feedback(projectedrow,newrhs,chart,width,budget)
        seed=aggregate_seed(seed_endpoint['candidate_original_vector'],retained,recipes,budget)
        if seed_endpoint.get('complete')is not True:raise ValueError('complete fixed exact seed')
        for pivot,row in chart.items():
            value=F(0)
            for j,q in row.items():
                if j!=width:value=budget.add(value,budget.mul(q,seed[j]))
            if value!=row.get(width,F(0)):raise ValueError('fixed seed satisfies old chart')
        record=None if classification=='inconsistent'else dict(schema=CHART_SCHEMA,width=width,original_width=1957,retained_indices=retained,old_pivots=old_pivots,old_free_indices=free,pivot_columns=sorted(old_pivots+([]if new is None else[reduction['chosen_pivot']])),free_indices=[j for j in free if j!=reduction['chosen_pivot']],old_rank=len(chart),new_rank=len(chart)+int(classification=='independent'),classification=classification,normalized_rows=[dict(pivot=p,source_row=sources[p],terms=[[j,str(q)]for j,q in sorted(chart[p].items())])for p in old_pivots],appended_row=None if new is None else dict(pivot=reduction['chosen_pivot'],source_row='feedback',terms=[[j,str(q)]for j,q in sorted(new.items())]),policy=POLICY,**FLAGS)
        if len(encoded(record))>max_chart_bytes:raise OverflowError('compact chart byte cap')
        out.update(classification=classification,reduction=reduction,initial_projected_vector=list(map(str,seed)),preserved_free_indices=[j for j in free if j!=reduction['chosen_pivot']],coefficient_rank=779+int(classification=='independent'),augmented_rank=779+int(classification!='redundant'),free_dimension=None if classification=='inconsistent'else 445-int(classification=='independent'))
        if classification!='inconsistent':
            phase('repairing_seed');augmented=dict(chart)
            if new is not None:augmented[reduction['chosen_pivot']]=new
            repaired=back_substitute(augmented,seed,width,budget);x=canonical_lift(repaired,retained,budget)
            if any(repaired[j]!=seed[j]for j in out['preserved_free_indices']):raise ValueError('preserved other free coordinates')
            phase('checking_endpoint');out.update(candidate_projected_vector=list(map(str,repaired)),candidate_original_vector=list(map(str,x)),diagnostics=diagnostics(columns,rhs,x,fullrow,newrhs,budget))
            if not out['diagnostics']['affine_equalities_satisfied']:raise ValueError('all original and feedback equations exactly satisfied')
        budget.charge((len(encoded(record))+len(encoded(out)))//64+1)
        out.update(status='complete',complete=True,chart_available=record is not None,counts=budget.counts())
        if len(encoded(out))>max_receipt_bytes:raise OverflowError('affine receipt byte cap')
        phase('complete');out['counts']=budget.counts()
        if len(encoded(out))>max_receipt_bytes:raise OverflowError('final affine receipt byte cap')
        return record,out
    except (ArithmeticError,ValueError,KeyError,TypeError,OverflowError,TimeoutError)as error:
        out.update(status='UNKNOWN',complete=False,chart_available=False,reason=str(error)or type(error).__name__,error_type=type(error).__name__,candidate_projected_vector=None,candidate_original_vector=None,diagnostics=None,counts=budget.counts())
        if len(encoded(out))>max_receipt_bytes:
            out.update(reduction=None,initial_projected_vector=None,preserved_free_indices=None)
        return None,out
