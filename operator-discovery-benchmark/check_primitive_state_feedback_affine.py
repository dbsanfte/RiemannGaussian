"""Independent exact affine feedback replay; no producer imports or hashes."""
from fractions import Fraction as F
import json
import math
import time

SCHEMA='primitive-state-feedback-affine-v1'

def require(x,message):
    if not x:raise ValueError(message)

class Budget:
    def __init__(self,deadline,max_operations=250000000,max_live_cells=6000000,max_fill_cells=20000000,max_bits=4096):
        require(type(deadline)in(int,float)and math.isfinite(deadline),'finite feedback deadline')
        for v,cap in [(max_operations,250000000),(max_live_cells,6000000),(max_fill_cells,20000000),(max_bits,4096)]:require(type(v)is int and 0<v<=cap,'strict feedback cap')
        self.deadline=deadline;self.cap=max_operations;self.live_cap=max_live_cells;self.fill_cap=max_fill_cells;self.bits=max_bits;self.operations=0;self.fill_cells=0;self.peak_live_cells=0;self.audit_cells=0
    def charge(self,n=1,cells=0):
        require(type(n)is int and n>=0 and type(cells)is int and cells>=0,'nonnegative independent proxies')
        if n>self.cap-self.operations:raise OverflowError('feedback independent work cap')
        self.operations+=n;self.audit_cells+=cells
        if time.monotonic()>self.deadline:raise TimeoutError('feedback independent deadline')
    def rational(self,value,output=False):
        self.charge()
        if type(value)is str:
            require(value and len(value)<=2*self.bits+3 and all(c in '-0123456789/'for c in value),'bounded rational text')
            parts=value.split('/');require(len(parts)<=2 and all(p and p!='-'for p in parts),'rational components')
            digits=1+self.bits*30103//100000
            if any(len(p.lstrip('-'))>digits for p in parts):raise OverflowError('rational text before integer allocation')
            nums=[int(p)for p in parts];require(len(nums)==1 or nums[1]>0,'positive rational denominator')
            if any(abs(n).bit_length()>self.bits for n in nums):raise OverflowError('rational integers before Fraction')
            q=F(*nums);require(str(q)==value,'canonical rational')
        else:require(type(value)in(int,F),'exact rational');q=F(value)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>self.bits:raise OverflowError('feedback coefficient bits')
        return q
    def add(self,a,b):self.rational(a);self.rational(b);return self.rational(a+b)
    def mul(self,a,b):self.rational(a);self.rational(b);return self.rational(a*b)
    def div(self,a,b):self.rational(a);self.rational(b);require(b!=0,'nonzero divisor');return self.rational(a/b)
    def live(self,n):
        if n>self.live_cap:raise OverflowError('feedback live rational cells')
        self.peak_live_cells=max(self.peak_live_cells,n);self.charge()
    def fill(self,n):
        self.fill_cells+=n
        if self.fill_cells>self.fill_cap:raise OverflowError('feedback cumulative fill')
        self.charge(n)


def exact_psd(matrix,b):
    n=len(matrix);require(n>0 and all(len(row)==n for row in matrix),'complete PSD matrix')
    a=[[b.rational(q)for q in row]for row in matrix];t=[[F(i==j)for j in range(n)]for i in range(n)]
    require(all(a[i][j]==a[j][i]for i in range(n)for j in range(n)),'symmetric PSD matrix');b.charge(n*n,cells=2*n*n)
    positive=0;zero=0
    def negative(vector,kind,pivot):
        value=F(0)
        for i in range(n):
            for j in range(n):value=b.add(value,b.mul(b.mul(vector[i],matrix[i][j]),vector[j]))
        require(value<0,'exact negative original quadratic witness')
        return dict(psd=False,kind=kind,pivot=pivot,witness=list(map(str,vector)),quadratic_value=str(value))
    for i in range(n):
        d=a[i][i]
        if d<0:return negative(t[i],'negative Schur pivot',i)
        if d==0:
            j=next((j for j in range(i+1,n)if a[i][j]),None)
            if j is not None:
                scale=b.div(-a[i][j],b.add(abs(a[j][j]),F(1)))
                vector=[b.add(x,b.mul(scale,y))for x,y in zip(t[i],t[j])]
                return negative(vector,'zero pivot with nonzero remaining row',i)
            zero+=1;continue
        positive+=1;multipliers={j:b.div(a[i][j],d)for j in range(i+1,n)}
        for j in range(i+1,n):
            for k in range(j,n):value=b.add(a[j][k],-b.mul(a[i][j],multipliers[k]));a[j][k]=a[k][j]=value
            t[j]=[b.add(x,-b.mul(multipliers[j],y))for x,y in zip(t[j],t[i])]
    return dict(psd=True,positive_pivots=positive,zero_pivots=zero)


def projection_layout(original):
    require(original.get('shape')==[366,613]and original.get('offset')==1597 and original.get('specs')==[['full_child',15],['full_parent',15],['storage_K',15]],'full unchanged original1957 coordinate geometry')
    recipes={367+2*i:{366+2*i:F(-1)}for i in range(613)}
    recipes.update({1837+i:{1597+i:F(1),1717+i:F(-4)}for i in range(120)})
    retained=[i for i in range(1957)if i not in recipes]
    return retained,recipes


def decode_source(cache,projection,b):
    original=cache['original'];retained,recipes=projection_layout(original);columns=original['columns'];rhs=original['rhs'];labels=original['monomials']
    b.charge(len(labels)+len(columns));require(len(columns)==1957 and len(labels)==len(rhs)and len(labels)>0 and len({tuple(m)for m in labels})==len(labels),'complete source dimensions/domain')
    require(projection.get('complete')is True and projection.get('status')=='complete'and projection.get('original_columns')==1957 and projection.get('projected_columns')==1224 and projection.get('rows')==len(labels),'complete exact projection tape')
    require(projection.get('retained_indices')==retained,'unchanged retained original indices')
    expected=[[i,[[j,str(q)]for j,q in sorted(recipe.items())]]for i,recipe in sorted(recipes.items())]
    require(projection.get('recipes')==expected,'all signed-pair/storage recipes')
    full=[{}for _ in rhs];coeff=[];source_cells=0
    for j,column in enumerate(columns):
        require(type(column)is list,'explicit source column');p={};previous=-1
        for i,text in column:
            require(type(i)is int and previous<i<len(rhs),'ordered unique coefficient row');previous=i;q=b.rational(text);require(q!=0,'nonzero sparse coefficient');p[i]=q;full[i][j]=q;source_cells+=1
            if source_cells>4000000:raise OverflowError('complete source cell cap')
        coeff.append(p)
    target=[b.rational(q)for q in rhs]
    require(all(row or q for row,q in zip(full,target)),'complete monomial domain contains source/target support')
    for omitted,recipe in recipes.items():
        expected_column={}
        for j,q in recipe.items():
            for i,v in coeff[j].items():
                value=b.add(expected_column.get(i,F(0)),b.mul(q,v))
                if value:expected_column[i]=value
                else:expected_column.pop(i,None)
        require(coeff[omitted]==expected_column,'actual complete omitted column dependency')
    lookup={j:i for i,j in enumerate(retained)};rows=[{lookup[j]:q for j,q in row.items()if j in lookup}for row in full]
    b.charge(source_cells+sum(map(len,rows)));b.live(2*source_cells+sum(map(len,rows))+len(target)+1957)
    return full,rows,target,retained,recipes


def subtract(row,other,multiplier,b):
    for j,q in other.items():
        value=b.add(row.get(j,F(0)),-b.mul(multiplier,q))
        if value:
            if j not in row:b.fill(1)
            row[j]=value
        else:row.pop(j,None)


def replay_basis(rows,rhs,width,tape,b,*,resident_cells=0):
    require(tape.get('complete')is True and tape.get('status')=='complete'and tape.get('coefficient_consistency')=='consistent'and tape.get('inconsistent_augmented_pivots')==[],'complete consistent old basis')
    require(tape.get('variables')==width and tape.get('original_rows')==len(rows)and tape.get('augmented_rhs_column')==width,'old complete augmented dimensions')
    b.charge(len(rows)*max(1,len(rows).bit_length()));order=sorted(range(len(rows)),key=lambda i:(len(rows[i])+bool(rhs[i]),i));require(tape.get('row_order')==order and len(tape.get('transcript',[]))==len(rows),'all original source rows ordered and covered')
    normalized=[];pivots=[];indices=[];records=[];basis_cells=0;resident=resident_cells+sum(map(len,rows))+len(rhs)
    for i,record in zip(order,tape['transcript']):
        require(record.get('source_row')==i,'source tape row order');residual=dict(rows[i])
        if rhs[i]:residual[width]=rhs[i]
        b.charge(len(residual));b.fill(len(residual));b.live(resident+basis_cells+len(residual))
        for k,text in record['steps']:
            require(type(k)is int and 0<=k<len(normalized),'earlier proof reference');m=b.rational(text)
            b.charge(len(residual));require(residual and min(residual)==pivots[k]and residual[pivots[k]]==m,'exact old reduction step/multiplicity/pivot')
            subtract(residual,normalized[k],m,b);b.live(resident+basis_cells+len(residual))
        pivot=record.get('pivot_column')
        if pivot is None:require(not residual and record.get('normalization')is None and record.get('basis_index')is None,'every omitted old augmented row reduced to zero')
        else:
            require(type(pivot)is int and 0<=pivot<width and pivot not in pivots and residual and min(residual)==pivot and record.get('basis_index')==len(normalized),'new normalized old pivot')
            norm=b.rational(record['normalization']);require(norm==residual[pivot]and norm!=0,'exact old normalization')
            b.charge(len(residual)*max(1,len(residual).bit_length()));row={j:b.div(q,norm)for j,q in sorted(residual.items())};normalized.append(row);pivots.append(pivot);indices.append(i);records.append(dict(pivot=pivot,source_row=i,terms=[[j,str(q)]for j,q in sorted(row.items())]));basis_cells+=len(row);b.fill(len(row));b.live(resident+basis_cells+len(row))
    require(indices==tape['retained_indices']and pivots==tape['pivot_columns']and len(pivots)==tape['augmented_rank'],'complete old basis partition/rank')
    require(tape.get('variable_mapping')=='identity'and tape.get('objective_mapping')=='identity'and tape.get('cone_mapping')=='identity','old basis changes only equations')
    return dict(zip(pivots,normalized)),sorted(records,key=lambda r:r['pivot'])


def decode_feedback(feedback,retained,recipes,b):
    require(feedback.get('schema')=='primitive-state-formal-identity-necessary-row-v1'and feedback.get('assignment')==[2*n+1 for n in range(1,28)]and feedback.get('width')==1957 and feedback.get('X')==7 and feedback.get('layout',{}).get('n_variables')==1957,'fixed exact original feedback row')
    full=[F(0)]*1957;last=-1
    for item in feedback['entries']:
        i=item['index'];require(type(i)is int and last<i<1957,'ordered sparse feedback row');last=i;full[i]=b.rational(item['coefficient']);require(full[i]!=0,'nonzero feedback coefficient')
    require(feedback['zero_coordinates']==[i for i,q in enumerate(full)if not q]and all(full[i]==0 for i in range(1592,1597)),'complete exact feedback zero coordinates/slacks')
    for omitted,recipe in recipes.items():
        value=F(0)
        for j,q in recipe.items():value=b.add(value,b.mul(q,full[j]))
        require(full[omitted]==value,'feedback obeys same signed/storage dependencies')
    return full,[full[i]for i in retained],b.rational(feedback['rhs'])


def reduce_feedback(projected,rhs,basis,b):
    width=len(projected);residual={i:q for i,q in enumerate(projected)if q}
    if rhs:residual[width]=rhs
    multipliers=[]
    # Do not stop at the first free column: every old pivot must be removed.
    for pivot in sorted(basis):
        if pivot in residual:
            m=residual[pivot];multipliers.append([pivot,str(m)]);subtract(residual,basis[pivot],m,b)
    require(not(set(residual)&set(basis)),'feedback restricted to old free coordinates')
    free=[j for j in residual if j<width]
    classification='independent'if free else'inconsistent'if residual.get(width)else'redundant'
    pivot=min(free)if free else None;norm=residual[pivot]if pivot is not None else None
    normalized={j:b.div(q,norm)for j,q in sorted(residual.items())}if pivot is not None else None
    receipt=dict(multipliers=multipliers,residual_terms=[[j,str(q)]for j,q in sorted(residual.items())],chosen_pivot=pivot,normalization=str(norm)if norm is not None else None)
    return classification,normalized,receipt


def projected_seed(vector,retained,recipes,b):
    require(type(vector)is list and len(vector)==1957,'all old seed coordinates');x=[b.rational(q)for q in vector];lookup={j:k for k,j in enumerate(retained)};y=[x[j]for j in retained]
    for omitted,recipe in recipes.items():
        for j,q in recipe.items():y[lookup[j]]=b.add(y[lookup[j]],b.mul(q,x[omitted]))
    return x,y


def backsubstitute(basis,seed,b):
    width=len(seed);x=seed[:]
    for p in sorted(basis,reverse=True):
        row=basis[p];require(row.get(p)==1 and all(j>=p for j in row),'normalized upper triangular chart')
        value=row.get(width,F(0))
        for j,q in row.items():
            if j not in(p,width):value=b.add(value,-b.mul(q,x[j]))
        x[p]=value
    return x


def lift(y,retained,b):
    values=dict(zip(retained,y));x=[F(0)]*1957
    for i in range(366):x[i]=values[i]
    for i in range(613):q=values[366+2*i];x[366+2*i]=max(q,F(0));x[367+2*i]=max(-q,F(0))
    for i in range(1592,1597):x[i]=values[i]
    for i in range(120):x[1837+i]=values[1597+i];x[1717+i]=b.add(values[1717+i],b.mul(F(4),values[1597+i]))
    return x


def endpoint_check(full,rhs,newrow,newrhs,x,b):
    mismatches=[]
    for i,(row,target)in enumerate(zip(full,rhs)):
        value=F(0)
        for j,q in row.items():value=b.add(value,b.mul(q,x[j]))
        if value!=target:mismatches.append(dict(row=i,residual=str(b.add(value,-target))))
    value=F(0)
    for q,v in zip(newrow,x):value=b.add(value,b.mul(q,v))
    newres=b.add(value,-newrhs);negative=[dict(index=i,value=str(x[i]))for i in range(1597)if x[i]<0];psd={}
    for k,name in enumerate(('full_child','full_parent','storage_K')):
        matrix=[[F(0)]*15 for _ in range(15)];position=1597+120*k
        for i in range(15):
            for j in range(i,15):matrix[i][j]=matrix[j][i]=x[position];position+=1
        psd[name]=exact_psd(matrix,b)
    return dict(all_original_rows_checked=len(full),equality_mismatch_count=len(mismatches),equality_mismatches=mismatches,new_row_residual=str(newres),negative_scalar_count=len(negative),negative_scalars=negative,psd_blocks=psd,finite_original_candidate_feasible=not mismatches and newres==0 and not negative and all(v['psd']for v in psd.values()))

POLICY=dict(reduction='all old pivot columns in ascending order, even beyond leading free column',pivot='smallest nonzero old free column',repair='preserve every other old free coordinate of the single exact publication021 seed',substitution='descending pivot column',lift='child=0; storage_K=C; parent=P+4*C; beta positive/negative parts',optimization='none; no objective preservation or cone feasibility claim')
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,candidate_admitted=False,exact_admission=False,infeasibility_proved=False,cone_feasibility_proved=False,all_scale_identity_proved=False,source_equations_independently_verified=False)


def check_psd_report(matrix,report,computed,b):
    require(type(report)is dict and report.get('psd')is computed['psd'],'independent PSD verdict')
    if report['psd']:
        n=len(matrix);require(len(report.get('diagonal',[]))==n and len(report.get('lower',[]))==n,'complete PSD decomposition')
        d=[b.rational(q)for q in report['diagonal']];lower=[[b.rational(q)for q in row]for row in report['lower']]
        require(all(len(row)==n for row in lower)and all(dv>=0 for dv in d)and report.get('rank')==sum(q!=0 for q in d),'nonnegative exact LDL weights')
        require(all(lower[i][i]==1 and all(lower[i][j]==0 for j in range(i+1,n))for i in range(n)),'unit lower triangular factor')
        for i in range(n):
            for j in range(n):
                value=F(0)
                for k in range(n):value=b.add(value,b.mul(b.mul(lower[i][k],d[k]),lower[j][k]))
                require(value==matrix[i][j],'exact original PSD decomposition')
    else:
        w=report.get('witness');require(type(w)is dict and len(w.get('vector',[]))==len(matrix),'complete original negative witness')
        v=[b.rational(q)for q in w['vector']];value=F(0)
        for i in range(len(v)):
            for j in range(len(v)):value=b.add(value,b.mul(b.mul(v[i],matrix[i][j]),v[j]))
        require(value<0 and b.rational(w['quadratic_value'])==value,'checked exact original negative quadratic witness')


def verify_feedback(cache,projection,tape,seed_endpoint,necessary,chart,receipt,*,deadline=None,max_operations=250000000,max_live_cells=6000000,max_fill_cells=20000000,max_coefficient_bits=4096,max_chart_bytes=33554432,max_receipt_bytes=8388608):
    require(type(max_chart_bytes)is int and 0<max_chart_bytes<=33554432 and type(max_receipt_bytes)is int and 0<max_receipt_bytes<=8388608,'bounded affine artifacts')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_live_cells,max_fill_cells,max_coefficient_bits)
    payload=json.dumps(receipt,sort_keys=True,separators=(',',':'),allow_nan=False).encode();require(len(payload)<=max_receipt_bytes,'bounded explicit affine receipt');b.charge(len(payload)//64+1)
    require(receipt.get('schema')==SCHEMA and receipt.get('status')=='complete'and receipt.get('complete')is True and receipt.get('policy')==POLICY,'complete known fixed affine receipt')
    for k in FLAGS:require(receipt.get(k)is False,'producer cannot self-certify '+k)
    limits=receipt.get('limits');require(type(limits)is dict and set(limits)=={'max_operations','max_cells','max_coefficient_bits','max_chart_bytes','max_receipt_bytes'},'explicit producer limits')
    for k,cap in dict(max_operations=150000000,max_cells=6000000,max_coefficient_bits=4096,max_chart_bytes=33554432,max_receipt_bytes=8388608).items():require(type(limits[k])is int and 0<limits[k]<=cap,'bounded producer limit '+k)
    counts=receipt.get('counts');require(type(counts)is dict and set(counts)=={'operations','peak_live_cells','maximum_rational_bits'},'complete producer count diagnostics')
    for k,cap in [('operations',limits['max_operations']),('peak_live_cells',limits['max_cells']),('maximum_rational_bits',limits['max_coefficient_bits'])]:require(type(counts[k])is int and 0<=counts[k]<=cap,'bounded producer count '+k)
    full,rows,rhs,retained,recipes=decode_source(cache,projection,b);width=len(retained)
    old,records=replay_basis(rows,rhs,width,tape,b,resident_cells=sum(map(len,full)))
    require(len(old)==779 and width==1224,'fixed complete rank779 projectedwidth1224')
    free=[j for j in range(width)if j not in old];require(len(free)==445,'complete old445 free partition')
    full_feedback,projected,newrhs=decode_feedback(necessary,retained,recipes,b);classification,new,reduction=reduce_feedback(projected,newrhs,old,b)
    require(receipt.get('classification')==classification and receipt.get('reduction')==reduction,'every feedback multiplier/residual and disposition')
    require(seed_endpoint.get('complete')is True,'complete fixed exact endpoint seed');original_seed,seed=projected_seed(seed_endpoint['candidate_original_vector'],retained,recipes,b)
    require(backsubstitute(old,seed,b)==seed,'all seed old chart equations')
    require(receipt.get('initial_projected_vector')==list(map(str,seed)),'actual exact old free seed')
    preserved=[j for j in free if j!=reduction['chosen_pivot']];require(receipt.get('preserved_free_indices')==preserved,'all other old free coordinates preserved')
    coefficient_rank=779+int(classification=='independent');augmented_rank=779+int(classification!='redundant');newfree=None if classification=='inconsistent'else 445-int(classification=='independent')
    require(receipt.get('coefficient_rank')==coefficient_rank and receipt.get('augmented_rank')==augmented_rank and receipt.get('free_dimension')==newfree,'coefficient vs augmented rank distinguished')
    diag=None
    if classification=='inconsistent':
        require(chart is None and receipt.get('chart_available')is False and receipt.get('candidate_projected_vector')is None and receipt.get('candidate_original_vector')is None and receipt.get('diagnostics')is None,'inconsistent augmented system has no usable coefficient chart/endpoint')
    else:
        expected=dict(schema='primitive-state-feedback-affine-chart-v1',width=width,original_width=1957,retained_indices=retained,old_pivots=sorted(old),old_free_indices=free,pivot_columns=sorted(list(old)+([]if new is None else[reduction['chosen_pivot']])),free_indices=preserved,old_rank=779,new_rank=coefficient_rank,classification=classification,normalized_rows=records,appended_row=None if new is None else dict(pivot=reduction['chosen_pivot'],source_row='feedback',terms=[[j,str(q)]for j,q in sorted(new.items())]),policy=POLICY,**FLAGS)
        require(chart==expected and receipt.get('chart_available')is True,'complete saved exact normalized old/new chart')
        chart_bytes=len(json.dumps(chart,sort_keys=True,separators=(',',':'),allow_nan=False).encode());require(chart_bytes<=max_chart_bytes,'bounded saved normalized chart');b.charge(chart_bytes//64+1)
        augmented=dict(old)
        if new is not None:augmented[reduction['chosen_pivot']]=new
        repaired=backsubstitute(augmented,seed,b);require(all(repaired[j]==seed[j]for j in preserved),'exact preserved unselected free coordinates');x=lift(repaired,retained,b)
        require(receipt.get('candidate_projected_vector')==list(map(str,repaired))and receipt.get('candidate_original_vector')==list(map(str,x)),'entire exact repaired projected/original endpoint')
        diag=endpoint_check(full,rhs,full_feedback,newrhs,x,b);reported=receipt.get('diagnostics');require(type(reported)is dict,'complete endpoint diagnostic')
        require(reported.get('original_equations')==len(full) and reported.get('original_equation_mismatches')==diag['equality_mismatches']and reported.get('new_equation_residual')==diag['new_row_residual']and reported.get('affine_equalities_satisfied')is True and diag['equality_mismatch_count']==0 and diag['new_row_residual']=='0','all old ORIGINAL equations and new equation exact')
        require(reported.get('negative_scalars')==[dict(coordinate=r['index'],value=r['value'])for r in diag['negative_scalars']],'all1597 scalar signs')
        blocks=reported.get('psd_blocks');require(type(blocks)is list and [r.get('name')for r in blocks]==['full_child','full_parent','storage_K'],'all original3 PSD blocks')
        for k,report in enumerate(blocks):
            matrix=[[F(0)]*15 for _ in range(15)];index=1597+120*k
            for i in range(15):
                for j in range(i,15):matrix[i][j]=matrix[j][i]=x[index];index+=1
            check_psd_report(matrix,report,diag['psd_blocks'][report['name']],b)
        require(reported.get('all_cones_satisfied')is diag['finite_original_candidate_feasible'],'exact finite cone diagnostic; no global admission')
    return dict(schema='primitive-state-feedback-affine-independent-check-v1',verified=True,complete=True,classification=classification,all_original_rows_replayed=True,original_rows=len(full),original_variables=1957,projection_dependencies_verified=True,feedback_reduction_verified=True,normalized_chart_verified=classification!='inconsistent',old_rank=779,new_rank=coefficient_rank,augmented_rank=augmented_rank,old_free_count=445,new_free_count=newfree,candidate_equations_verified=False if diag is None else diag['equality_mismatch_count']==0 and diag['new_row_residual']=='0',finite_candidate_feasible=None if diag is None else diag['finite_original_candidate_feasible'],negative_scalar_count=None if diag is None else diag['negative_scalar_count'],psd_blocks=None if diag is None else diag['psd_blocks'],chosen_pivot=reduction['chosen_pivot'],audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,fill_cells=b.fill_cells,**FLAGS)
