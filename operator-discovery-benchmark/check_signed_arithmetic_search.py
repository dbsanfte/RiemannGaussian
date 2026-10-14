"""Independent arithmetic/provenance audit for signed-language experiments.

No production grammar or mathematical backend is imported. The eventual run
schema is bound before freezing; identities/component bounds and full actual
all-scale signed estimates have separate scopes.
"""
import argparse
from fractions import Fraction
from math import gcd
from itertools import combinations, product
import hashlib
import json
import os
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parent


def require_runtime():
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
        raise RuntimeError('independent signed-language audit requires assertions enabled')


def rational(value):
    if isinstance(value,(bool,float)) or not isinstance(value,(str,int,Fraction)):
        raise ValueError('exact integer/rational required')
    return Fraction(value)


def integer(value,minimum=0):
    if type(value) is not int or value<minimum:
        raise ValueError('integer outside declared domain')
    return value


def exact_json(value):
    if isinstance(value,Fraction):
        return int(value) if value.denominator==1 else str(value)
    if isinstance(value,dict):
        return {k:exact_json(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [exact_json(v) for v in value]
    return value


def digest(value):
    return hashlib.sha256(json.dumps(exact_json(value),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def checked_path(root,name):
    if not isinstance(name,str) or not name or Path(name).is_absolute():
        raise ValueError('relative artifact name required')
    result=(Path(root)/name).resolve()
    if not result.is_relative_to(Path(root).resolve()):
        raise ValueError('artifact path escapes run')
    return result


def check_hashes(root,mapping):
    if not isinstance(mapping,dict) or not mapping:
        raise ValueError('nonempty frozen hash mapping required')
    for name,expected in mapping.items():
        if sha(checked_path(root,name))!=expected:
            raise ValueError('artifact hash mismatch: '+name)


def factor_prefix(N):
    """Independent least-prime factorization, not inverse/divisor recurrence."""
    integer(N,1)
    least=list(range(N+1))
    for p in range(2,N+1):
        if least[p]!=p:continue
        for n in range(p*p,N+1,p):
            if least[n]==n:least[n]=p
    mu=[0]*(N+1);liouville=[0]*(N+1);mu[1]=liouville[1]=1
    for n in range(2,N+1):
        rest=n;omega=0;distinct=0;squarefree=True
        while rest>1:
            p=least[rest];exponent=0
            while rest%p==0:rest//=p;exponent+=1
            omega+=exponent;distinct+=1
            if exponent>1:squarefree=False
        liouville[n]=(-1)**omega
        mu[n]=(-1)**distinct if squarefree else 0
    return {'mu':mu,'liouville':liouville}


def prefix(values):
    if not isinstance(values,list) or not values or values[0]!=0:
        raise ValueError('zero-sentinel coefficient array required')
    result=[Fraction(0)];total=Fraction(0)
    for value in values[1:]:
        total+=rational(value);result.append(total)
    return result


def block_energy(sums,X):
    integer(X,1)
    if len(sums)<4*X:raise ValueError('complete actual prefix through 4X-1 required')
    parent=sum((rational(sums[n])**2 for n in range(X,2*X)),Fraction(0))
    child=sum((rational(sums[n])**2 for n in range(2*X,4*X)),Fraction(0))
    return {'A_X':parent,'A_2X':child,'Delta':child-4*parent,
            'E_X':parent/(X*X),'E_2X':child/(4*X*X)}


def ceil_power(n,exponent):
    """Full mathematical rational ceiling; checker calls use finite budgets."""
    integer(n,1);power=rational(exponent)
    if power<0:raise ValueError('nonnegative power required')
    if n==1 or power==0:return 1
    whole,remainder=divmod(power.numerator,power.denominator)
    base=n**whole
    if not remainder:return base
    if remainder==1 and power.denominator>=base*(n-1):return base+1
    target=n**power.numerator;lo,hi=0,1
    while hi**power.denominator<target:hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**power.denominator<target:lo=mid
        else:hi=mid
    return hi


def liouville_floor_sum(values,N):
    """Exact full sum, retained as calibration rather than a Mobius bound."""
    integer(N,0)
    if len(values)<=N:raise ValueError('complete Liouville prefix required')
    return sum(values[d]*(N//d) for d in range(1,N+1))


def verify_source_bindings(run_dir,protocol,seal,sealed_names):
    require_runtime();directory=Path(run_dir).resolve()
    if seal.get('protocol_sha256')!=digest(protocol):
        raise ValueError('seal protocol binding mismatch')
    mapping=seal.get('files')
    if not isinstance(mapping,dict) or set(mapping)!=set(sealed_names):
        raise ValueError('seal has incomplete or unexpected files')
    check_hashes(directory,mapping)
    declared=protocol.get('code_sha256')
    required={'signed_arithmetic_search.py','signed_arithmetic_language.py','signed_arithmetic_certificates.py','signed_arithmetic_proof.txt','signed_arithmetic_report.py','check_signed_arithmetic_search.py','test_signed_arithmetic_language.py','test_signed_arithmetic_certificates.py','test_signed_arithmetic_search.py','signed_arithmetic_sampler.py','test_signed_arithmetic_sampler.py'}
    if set(declared or {})!=required:raise ValueError('frozen source set incomplete or unexpected')
    check_hashes(BASE,declared);check_hashes(directory/'frozen_source',declared)
    if Path(__file__).name not in declared:
        raise ValueError('independent checker is not frozen')
    return True


def floor_root(n,order):
    integer(n,0);integer(order,1)
    if n<2:return n
    if order>=n.bit_length():return 1
    lo,hi=0,n+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**order<=n:lo=mid
        else:hi=mid
    return lo


def basis_profile(mu,X,scales,B):
    """Independent diagonal/projection/full energy with ONE shared cutoff."""
    integer(X,1);integer(B,0)
    if not scales or any(type(scale) is not int or scale<1 for scale in scales):
        raise ValueError('positive integer dilate scales required')
    if len(mu)<2*max(scales)*X:
        raise ValueError('complete arithmetic through final nonzero kernel index required')
    sums=[0]
    for coefficient in mu[1:]:sums.append(sums[-1]+coefficient)
    result=[]
    for scale in scales:
        Y=scale*X;limit=2*Y-1
        A=sum((sums[n]**2 for n in range(Y,2*Y)),Fraction(0))
        diagonal=sum(mu[n]**2*(2*Y-max(Y,n)) for n in range(1,limit+1))
        projection=0
        for r in range(2,min(B,limit)+1):
            if not mu[r]:continue
            for a in range(1,r):
                if not mu[a] or gcd(a,r)!=1:continue
                inner=0
                for g in range(1,limit//r+1):
                    if mu[g] and gcd(g,a*r)==1:
                        inner+=2*Y-max(Y,r*g)
                projection+=2*mu[a]*mu[r]*inner
        result.append({'scale':scale,'A':A,'diagonal':diagonal,'projection':projection})
    return result


def kernel_from_terms(terms):
    """Direct rational polygon from complete normalized signed stencil."""
    pairs=[(rational(scale),rational(weight)) for scale,weight in terms]
    if not pairs or any(scale<=0 for scale,weight in pairs):
        raise ValueError('positive nonempty dilate list required')
    points=sorted({Fraction(0)}|{s for s,c in pairs}|{2*s for s,c in pairs})
    knots=[]
    for t in points:
        ordinate=sum((c*max(Fraction(0),2*s-max(s,t)) for s,c in pairs),Fraction(0))
        knots.append([str(t),str(ordinate)])
    return {'kind':'continuous_piecewise_linear','knots':knots,'zero_beyond_support':True}


def integral_moment(kernel,power=0):
    """Exact polynomial integration, independent of moment response fitting."""
    integer(power,0)
    knots=[(rational(x),rational(y)) for x,y in kernel['knots']]
    if (kernel.get('kind')!='continuous_piecewise_linear' or
        kernel.get('zero_beyond_support') is not True or len(knots)<2 or
        knots[0][0]!=0 or knots[-1][1]!=0 or
        any(b<=a for (a,y),(b,z) in zip(knots,knots[1:]))):
        raise ValueError('invalid complete continuous compact kernel')
    total=Fraction(0)
    for (a,y),(b,z) in zip(knots,knots[1:]):
        slope=(z-y)/(b-a);intercept=y-slope*a
        total+=intercept*(b**(power+1)-a**(power+1))/(power+1)
        total+=slope*(b**(power+2)-a**(power+2))/(power+2)
    return total


def verify_kernel_certificate(record,terms=None):
    """Validate a conservative radical variation bound by exact inequalities."""
    try:
        kernel=record['kernel'];knots=[(rational(x),rational(y)) for x,y in kernel['knots']]
        moment=integral_moment(kernel)
        if terms is not None and kernel!=kernel_from_terms(terms):return False
        if (record['kernel_sha256']!=digest(kernel) or rational(record['exact_integral'])!=moment or
            rational(record['left_endpoint'])!=knots[0][1] or rational(record['right_endpoint'])!=0 or
            record['left_endpoint_zero']!=(knots[0][1]==0) or record['right_endpoint_zero'] is not True or
            record['left_discrepancy_zero'] is not True or
            record['admitted_zero_moment_component']!=(moment==0) or
            record['full_signed_bound_proved'] is not False):return False
        segments=record['segments']
        if len(segments)!=len(knots)-1:return False
        total=Fraction(0)
        for segment,((a,y),(b,z)) in zip(segments,zip(knots,knots[1:])):
            slope=(z-y)/(b-a)
            if rational(segment['a'])!=a or rational(segment['b'])!=b or rational(segment['slope'])!=slope:return False
            alo,ahi=map(rational,segment['sqrt_a']);blo,bhi=map(rational,segment['sqrt_b'])
            if not (0<=alo<=ahi and alo*alo<=a<=ahi*ahi and
                    0<=blo<=bhi and blo*blo<=b<=bhi*bhi):return False
            bound=abs(slope)*Fraction(2,3)*(b*bhi-a*alo)
            charged=rational(segment['weighted_variation_upper'])
            if charged<bound:return False
            total+=charged
        return rational(record['weighted_sqrt_variation_upper'])>=total
    except (KeyError,TypeError,ValueError,ZeroDivisionError):return False


def verify_positive_energy_transform(record,terms,epsilon=Fraction(1,12)):
    try:
        merged={}
        for scale,coefficient in terms:
            scale=rational(scale);merged[scale]=merged.get(scale,Fraction(0))+rational(coefficient)
        merged={k:v for k,v in merged.items() if v}
        canonical=[[str(k),str(v)] for k,v in sorted(merged.items())]
        if record['terms']!=canonical or rational(record['epsilon'])!=epsilon or record['signed_inequality_proved'] is not False or record['RH_proved'] is not False:return False
        if any(k.denominator!=1 or k<1 or int(k)&(int(k)-1) for k in merged):return False
        m=max(int(k).bit_length()-1 for k in merged);coefficients=[merged.get(Fraction(1<<j),Fraction(0)) for j in range(m+1)]
        remainder=sum(v*4**j for j,v in enumerate(coefficients));b=[]
        # Ascending coefficient comparison, independent of backend descending division.
        for j in range(m):b.append(((remainder-coefficients[0]) if j==0 else (b[-1]-coefficients[j]))/4)
        if m and b[-1]!=coefficients[-1]:return False
        positive=bool(b) and all(v>=0 for v in b) and any(v>0 for v in b);admitted=remainder==0 and positive
        recovery=next((j for j,v in enumerate(b) if v>0),None) if admitted else None
        expected={'status':'available','shift_polynomial_coefficients':list(map(str,coefficients)),
            'factor_coefficients':list(map(str,b)),'factor_terms':[[1<<j,str(v)] for j,v in enumerate(b)],
            'exact_constant_remainder':str(remainder),'quadratic_moment':str(remainder),'factorization_admitted':remainder==0,
            'factor_coefficients_nonnegative_nonzero':positive,'conditional_bridge_admitted':admitted,
            'unsigned_factor_coefficient_l1':str(sum(map(abs,b),Fraction(0))),'symbolic_cells_charged':len(coefficients)+len(b),
            'symbolic_order':m,'max_order':256,'recovery_index':recovery,'recovery_scale':None if recovery is None else 1<<recovery,
            'recovery_coefficient':None if recovery is None else str(b[recovery])}
        return all(record[k]==v for k,v in expected.items())
    except (KeyError,ValueError,TypeError,ZeroDivisionError):return False


def generated_candidates(spec):
    scales=spec['stencil_scales'];degrees=spec['moment_degrees']
    moments=[[integral_moment(kernel_from_terms([[scale,1]]),degree) for scale in scales] for degree in degrees]
    archive=[];rejected=[];seen=set()
    for size in range(2,spec['support_budget']+1):
        for support in combinations(range(len(scales)),size):
            for cancel in range(1,min(len(moments),size-1)+1):
              free=support[:-cancel];solved=support[-cancel:]
              for raw in product([rational(x) for x in spec['coefficient_grid']],repeat=len(free)):
                rhs=[-sum((c*moments[p][i] for c,i in zip(raw,free)),Fraction(0)) for p in range(cancel)]
                tail=solve_unique([[moments[p][i] for i in solved] for p in range(cancel)],rhs)
                if tail is None or any(not x for x in tail):
                    rejected.append({'support':list(support),'cancel_moments':cancel,'raw':[str(x) for x in raw],'reason':'degenerate_or_zero_solved_coefficient'});continue
                weights=[Fraction(0)]*len(scales)
                for index,value in zip(support,list(raw)+tail):weights[index]=value/tail[-1]
                key=tuple(weights)
                if key in seen:continue
                seen.add(key)
                if sum(abs(x) for x in weights)>rational(spec['coefficient_norm_budget']) or max(x.denominator for x in weights)>spec['coefficient_denominator_budget']:
                    rejected.append({'weights':[str(x) for x in weights],'reason':'finite_coefficient_resource_budget'});continue
                response=[sum((c*v for c,v in zip(weights,row)),Fraction(0)) for row in moments]
                order=next((j for j,value in enumerate(response) if value),len(response))
                bridge=all(value<=0 for value in weights[:support[-1]])
                program={'scales':scales,'weights':[str(x) for x in weights]}
                archive.append({'program_id':digest(program),'program':program,'support_size':size,
                    'annihilated_moment_count':order,'moment_responses':[str(x) for x in response],
                    'nonnegative_critical_recurrence_bridge':bridge,
                    'conditional_bridge_scope':'requires complete signed stencil inequality at every dyadic scale and cofinal exponents' if bridge else 'signed recurrence stability unresolved',
                    'global_signed_bound_proved':False})
    return {'anonymous_moment_response_matrix':[[str(x) for x in row] for row in moments],
            'candidates':sorted(archive,key=lambda row:row['program_id']),'rejected':rejected}


def independent_tables(scales,dilation_scales):
    N=2*max(scales)*max(dilation_scales)-1;mu=factor_prefix(N)['mu']
    rows=[]
    for X in scales:
        B=floor_root(X,3);basis=basis_profile(mu,X,dilation_scales,B)
        rows.append({'X':X,'shared_primitive_cutoff':B,'basis':[
            {'scale':row['scale'],'energy':int(row['A']),'diagonal':row['diagonal'],
             'primitive_projection':row['projection']} for row in basis]})
    return {'rows':rows,'coefficient_horizon':N}


def stencil_response(candidate,row):
    weights=[rational(x) for x in candidate['program']['weights']]
    values=[sum((c*rational(v[key]) for c,v in zip(weights,row['basis'])),Fraction(0))
            for key in ('energy','diagonal','primitive_projection')]
    full,diagonal,projection=values
    return {'X':row['X'],'full_signed_stencil':str(full),'diagonal':str(diagonal),
            'primitive_projection':str(projection),'dense_signed_residual':str(full-diagonal-projection),
            'complete_partition':True,'shared_primitive_cutoff':row['shared_primitive_cutoff']}


def fitted_candidate(candidate,rows,levels):
    responses=[stencil_response(candidate,row) for row in rows];constants={}
    for q in levels:
        constants[str(q)]=str(max([Fraction(0)]+[rational(row['full_signed_stencil'])/
            (row['X']**2*ceil_power(row['X'],Fraction(1,q))) for row in responses]))
    signs={key:sum((rational(row['full_signed_stencil'])>0 if key=='positive' else
        rational(row['full_signed_stencil'])==0 if key=='zero' else rational(row['full_signed_stencil'])<0)
        for row in responses) for key in ('positive','zero','negative')}
    return {**candidate,'constants':constants,'training_signs':signs}


def stencil_score(candidate,rows,levels):
    cases=[]
    for row in rows:
        response=stencil_response(candidate,row);X=row['X']
        for q in levels:
            coefficient=candidate['constants'].get(str(q))
            bound=None if coefficient is None else rational(coefficient)*X*X*ceil_power(X,Fraction(1,q))
            cases.append({'X':X,'q':q,'value':response['full_signed_stencil'],
                'bound':str(bound) if bound is not None else None,
                'finite_pass':rational(response['full_signed_stencil'])<=bound if bound is not None else None,
                'status':'available' if bound is not None else 'missing','in_dyadic_claim_domain':X&(X-1)==0})
    return {'cases':cases,'passes':sum(row['finite_pass'] is True for row in cases),
            'failures':sum(row['finite_pass'] is False for row in cases),
            'missing':sum(row['finite_pass'] is None for row in cases)}


def calibration_dictionary(spec):
    return ([{'op':'constant'}]+[{'op':'floor_root','q':q,'offset':offset} for q in spec['root_orders'] for offset in spec['root_offsets']]+
            [{'op':'polynomial','power':p} for p in (2,3)]+[{'op':'floor_div','divisor':d} for d in (2,3,6)]+
            [{'op':'divisor_count'},{'op':'divisor_sum'}])


def feature_value(feature,x):
    op=feature['op']
    if op=='constant':return 1
    if op=='floor_root':return floor_root(max(0,x+feature['offset']),feature['q'])
    if op=='polynomial':return x**feature['power']
    if op=='floor_div':return x//feature['divisor']
    if op in ('divisor_count','divisor_sum'):
        return sum(1 if op=='divisor_count' else d for d in range(1,x+1) if x%d==0)
    raise ValueError('unsupported calibration feature')


def calibration_rows(indices):
    if len(indices)!=len(set(indices)):raise ValueError('duplicate calibration response indices')
    values=factor_prefix(max(indices))['liouville']
    return [{'x':x,'anonymous_target':liouville_floor_sum(values,x),
             'unsigned_charge':sum(abs(values[d])*(x//d) for d in range(1,x+1))} for x in indices]


def solve_unique(matrix,target):
    """Independent full rational row reduction, including all response rows."""
    if not matrix or len(matrix)!=len(target):return None
    width=len(matrix[0]);rows=[[rational(x) for x in row]+[rational(y)] for row,y in zip(matrix,target)]
    cursor=0;pivots=[]
    for column in range(width):
        pivot=next((i for i in range(cursor,len(rows)) if rows[i][column]),None)
        if pivot is None:continue
        rows[cursor],rows[pivot]=rows[pivot],rows[cursor]
        norm=rows[cursor][column];rows[cursor]=[x/norm for x in rows[cursor]]
        for i in range(len(rows)):
            if i!=cursor and rows[i][column]:
                weight=rows[i][column];rows[i]=[a-weight*b for a,b in zip(rows[i],rows[cursor])]
        pivots.append(column);cursor+=1
    if len(pivots)!=width or any(not any(row[:width]) and row[-1] for row in rows):return None
    return [rows[i][-1] for i in range(width)]


def inferred_calibration(rows,features):
    retained=[];attempts=0
    for size in (1,2):
        for support in combinations(range(len(features)),size):
            attempts+=1
            matrix=[[feature_value(features[k],row['x']) for k in support] for row in rows]
            weights=solve_unique(matrix,[row['anonymous_target'] for row in rows])
            if weights is None or any(not x for x in weights):continue
            terms=[{'weight':str(c),'feature':features[k]} for c,k in zip(weights,support)]
            retained.append({'program_id':digest(terms),'terms':terms,'support_size':size})
    return {'support_attempts':attempts,'retained':retained}


def calibration_score(candidate,rows):
    result=[]
    for row in rows:
        predicted=sum((rational(term['weight'])*feature_value(term['feature'],row['x']) for term in candidate['terms']),Fraction(0))
        result.append({'x':row['x'],'target':row['anonymous_target'],'prediction':str(predicted),'finite_pass':predicted==row['anonymous_target']})
    return result


def ensure(value,message):
    if not value:raise ValueError(message)


def final_design(seal_hash):
    seed=int(seal_hash[:16],16);xs=[];indices=[]
    for j in range(3):
        x=1101+2*((seed>>(13*j))%651)
        while x in xs:x=1101+2*(((x-1101)//2+1)%651)
        xs.append(x)
    for j in range(5):
        x=3001+((seed>>(11*j))%3000)
        while x in indices:x=3001+(x-3000)%3000
        indices.append(x)
    return {'actual_scales':sorted(xs)+[2048,4096,8192],'calibration_indices':indices,
            'ast_horizon':257+seed%128,'seen_levels':[3,12],'unseen_levels':[13,17],
            'seal_sha256':seal_hash,'generated_after_seal':True}


def coupled_numeric(X):
    N=4*X-1;u=floor_root(N,2);mu=factor_prefix(N)['mu'];small=mu[:u+1]+[0]*(N-u)
    squared=[0]*(N+1)
    for a in range(1,u+1):
        for b in range(1,u+1):
            if a*b<=N:squared[a*b]+=mu[a]*mu[b]
    convolution=[0]*(N+1)
    for d in range(1,N+1):
        if squared[d]:
            for n in range(d,N+1,d):convolution[n]+=squared[d]
    M=prefix(mu);F1=prefix(small);F2=prefix(convolution)
    def moments(a,b):
        p=sum(a[n]*b[n] for n in range(X,2*X));c=sum(a[n]*b[n] for n in range(2*X,4*X))
        return {'parent':int(p),'child':int(c),'defect':int(c-4*p)}
    mom={'actual':moments(M,M),'F1':moments(F1,F1),'F2':moments(F2,F2),'cross':moments(F1,F2)}
    credit=4*mom['F1']['defect'];residual=mom['F2']['defect']-4*mom['cross']['defect']
    return {'X':X,'cutoff':u,'moments':mom,'energy':mom['actual']['parent'],'child_energy':mom['actual']['child'],
            'signed_defect':mom['actual']['defect'],'negative_low_prefix_credit':credit,'coupled_residual':residual,
            'reconstructed_defect':credit+residual,'identity_residual':credit+residual-mom['actual']['defect'],
            'all_prefix_coefficients_recovered':all(M[n]==2*F1[n]-F2[n] for n in range(N+1)),
            'actual_prefix_sha256':digest([int(v) for v in M]),'component_inverse_prefix_through':u,'actual_target_inverse_through':N}


def ast_values(node,N):
    ensure(isinstance(node,dict) and set(node)=={'op','args','params'},'invalid AST node schema')
    op=node['op'];args=node['args'];p=node['params']
    schemas={'one':(0,set()),'unit':(0,set()),'mu':(0,set()),'liouville':(0,set()),'scale':(1,{'weight'}),'add':(2,set()),'convolution':(2,set()),'product':(2,set()),'prefix':(1,set()),'shift':(1,{'offset'}),'dilate':(1,{'factor'}),'floor_index':(1,{'divisor'}),'root_index':(1,{'order'}),'truncate':(1,{'cutoff'}),'coprime_mask':(1,{'modulus'}),'residue_mask':(1,{'modulus','residue'}),'normalize':(1,{'power'})}
    ensure(op in schemas and isinstance(args,list) and isinstance(p,dict),'invalid AST operation schema')
    arity,keys=schemas[op]
    ensure((len(args)>=1 if op=='add' else len(args)==arity) and set(p)==keys,'invalid AST arity or parameters')
    for name in keys-{'weight','power','offset'}:integer(p[name],0 if name in ('cutoff','residue') else 1)
    if 'offset' in p:ensure(type(p['offset']) is int,'integer AST shift required')
    if 'weight' in p:rational(p['weight'])
    if 'power' in p:ensure(rational(p['power'])>=0,'negative AST normalization power')
    if 'residue' in p:ensure(p['residue']<p['modulus'],'noncanonical residue')
    if op in ('one','unit','mu','liouville'):
        if op=='one':return [Fraction(0)]+[Fraction(1)]*N
        if op=='unit':return [Fraction(0)]+([Fraction(1)]+[Fraction(0)]*(N-1) if N else [])
        return list(map(Fraction,factor_prefix(max(1,N))[op][:N+1]))
    if op=='shift':limit=max(0,N+p['offset'])
    elif op=='dilate':limit=N*p['factor']
    elif op=='floor_index':limit=N//p['divisor']
    elif op=='root_index':limit=floor_root(N,p['order'])
    elif op=='truncate':limit=min(N,p['cutoff'])
    else:limit=N
    children=[ast_values(a,limit) for a in args];a=children[0];out=[Fraction(0)]*(N+1)
    for n in range(1,N+1):
        if op=='scale':out[n]=rational(p['weight'])*a[n]
        elif op=='add':out[n]=sum(v[n] for v in children)
        elif op=='product':out[n]=a[n]*children[1][n]
        elif op=='convolution':out[n]=sum(a[d]*children[1][n//d] for d in range(1,n+1) if n%d==0)
        elif op=='prefix':out[n]=out[n-1]+a[n]
        elif op=='shift':out[n]=a[max(0,n+p['offset'])]
        elif op=='dilate':out[n]=a[n*p['factor']]
        elif op=='floor_index':out[n]=a[n//p['divisor']]
        elif op=='root_index':out[n]=a[floor_root(n,p['order'])]
        elif op=='truncate':out[n]=a[n] if n<=p['cutoff'] else 0
        elif op=='coprime_mask':out[n]=a[n] if gcd(n,p['modulus'])==1 else 0
        elif op=='residue_mask':out[n]=a[n] if n%p['modulus']==p['residue'] else 0
        elif op=='normalize':
            if rational(p['power'])>100:raise ValueError('available expression exceeds independent finite power budget')
            out[n]=rational(a[n])/ceil_power(n,p['power'])
        else:raise ValueError('unknown AST operation')
    return out


def audit_ast(block,programs,N):
    ensure(block['N']==N,'AST horizon mismatch');obs=block['observations']
    ensure([r['program_id'] for r in obs]==[p['program_id'] for p in programs],'AST archive incomplete/order mismatch')
    counts={s:0 for s in ('available','missing','invalid')}
    for r,p in zip(obs,programs):
        ensure(digest(p['expression'])==p['program_id'] and r['expression']==p['expression'],'AST expression hash mismatch')
        ensure(r['global_actual_signed_bound_proved'] is False and r['exploratory_not_full_RH_target'] is True,'AST overclaim')
        counts[r['status']]+=1
        if r['status']!='available':
            ensure(r['reason'] and r['arithmetic'] is None and r['metrics'] is None,'missing outcome erased');continue
        values=ast_values(p['expression'],N)
        ensure(list(map(rational,r['arithmetic']['coefficients']))==values,'AST numeric reconstruction mismatch')
        signed=sum(values);unsigned=sum(map(abs,values));square=sum(v*v for v in values);gain=unsigned-abs(signed)
        metrics={'signed_mass':str(signed),'unsigned_mass':str(unsigned),'square_mass':str(square),'cancellation_gain':str(gain),
                 'cancellation_gain_ratio':str(gain/unsigned if unsigned else Fraction(0)),'nontrivial_unsigned_mass':unsigned>0}
        ensure(r['metrics']==metrics,'AST metrics mismatch')
        cost=r['arithmetic']['cost']
        ensure(all(type(cost[k]) is int and cost[k]>=0 for k in ('operations','allocated_cells','evaluated_nodes','peak_coefficient_bits')),'invalid AST cost')
        ensure(cost['limits']=={'operations':5000000,'cells':2000000,'bits':1000000,'nodes':1024},'AST limits changed')
        for key,limit in [('operations',5000000),('allocated_cells',2000000),('peak_coefficient_bits',1000000),('evaluated_nodes',1024)]:ensure(cost[key]<=limit,'AST declared resource limit exceeded')
        ensure(r['metric_operations']==5*N+3 and r['total_charged_operations']==r['arithmetic']['cost']['operations']+5*N+3,'AST cost omission')
    for s,c in counts.items():ensure(block[s+'_cases']==c,'AST status count mismatch')
    ensure(block['global_actual_signed_bound_proved'] is False,'AST aggregate overclaim')
    return counts


def audit_run(run_dir):
    require_runtime();d=Path(run_dir).resolve();spec=read(d/'protocol.json');seal=read(d/'seal.json')
    verify_source_bindings(d,spec,seal,['protocol.json','candidate_batch.json','validation.json','proof_queue.json','contract_tests.txt'])
    for name in ('dependency_sha256','input_sha256'):check_hashes(BASE,spec[name])
    expected_modules=['test_signed_arithmetic_language','test_signed_arithmetic_certificates','test_signed_arithmetic_sampler','test_signed_arithmetic_search']
    ensure(spec['contract_test_modules']==expected_modules,'contract test module set changed')
    log=(d/'contract_tests.txt').read_text()
    ensure('\nOK\n' in log and 'FAILED (' not in log and 'Ran ' in log,'stored contract test log is not successful')
    final_input_hashes={n:sha(d/n) for n in ('final_cases.json','final_evaluation.json','worker_replay.json')}
    batch=read(d/'candidate_batch.json');validation=read(d/'validation.json');queue=read(d/'proof_queue.json');final=read(d/'final_evaluation.json')
    ensure(batch['protocol_sha256']==digest(spec) and queue['protocol_sha256']==digest(spec),'queue/protocol binding mismatch')
    ensure(seal['final_responses_created'] is False and queue['final_used_for_selection'] is False and queue['candidate_ids_frozen_before_final'] is True,'seal sequencing overclaim')
    for obj in (spec,final):
        ensure(obj['RH_proved'] is False and obj['actual_all_scale_signed_bound_proved'] is False,'global actual bound overclaim')
    ensure(all(batch['access_denials'].values()),'discovery guard failed')
    generated=generated_candidates(spec)
    for key in ('anonymous_moment_response_matrix','rejected'):ensure(batch[key]==generated[key],'inference archive mismatch: '+key)
    tables={}
    for label,indices,stored in [('training',spec['training_scales'],batch['training']),('validation',spec['validation_scales'],validation)]:
        t=independent_tables(indices,spec['stencil_scales']);tables[label]=t['rows']
        for key,value in t.items():ensure(stored[key]==value,label+' exact arithmetic mismatch')
        ensure(stored['prime_oracle_used_by_producer'] is False,'producer prime provenance changed')
    candidates=[fitted_candidate(c,tables['training'],spec['levels']) for c in generated['candidates']]
    ensure(batch['candidates']==candidates,'fit/archive mismatch')
    scores=[{'program_id':c['program_id'],'score':stencil_score(c,tables['validation'],spec['levels'])} for c in candidates]
    ensure(validation['scores']==scores,'validation mismatch');scoremap={r['program_id']:r['score'] for r in scores};groups={}
    for c in candidates:
        group=(c['support_size'],c['annihilated_moment_count'],c['nonnegative_critical_recurrence_bridge'])
        rank=(scoremap[c['program_id']]['failures'],max(map(rational,c['constants'].values())),sum(map(abs,map(rational,c['program']['weights']))),c['program_id'])
        if group not in groups or rank<groups[group][0]:groups[group]=(rank,c)
    chosen=[{**v[1],'validation_score':scoremap[v[1]['program_id']],
        'global_claim':'for every q>=q0, exists finite Cq independent of X, every dyadic X>=1: sum c_j A(s_j X) <= Cq X^2 ceil(X^(1/q))',
        'residual_obligation':'complete dense primitive signed residual retained; no all-scale upper estimate established'} for _,v in sorted(groups.items())]
    ensure(queue['queue']==chosen,'selection mismatch')
    features=calibration_dictionary(spec);cr=calibration_rows(spec['calibration_training_indices']);ci=inferred_calibration(cr,features)
    ensure(batch['calibration']=={'rows':cr,'dictionary':features,**ci},'calibration inference mismatch')
    cv=calibration_rows(spec['calibration_validation_indices']);ensure(validation['calibration_rows']==cv,'calibration validation rows mismatch')
    ensure(validation['calibration_results']==[{'program_id':c['program_id'],'cases':calibration_score(c,cv)} for c in ci['retained']],'calibration validation mismatch')
    selected=[c for c in ci['retained'] if all(r['finite_pass'] for r in calibration_score(c,cv))]
    ensure(queue['calibration_queue']==selected,'calibration selection mismatch')
    replay=read(d/'worker_replay.json')
    ensure(replay['all_identical'] is True and replay['independent_second_generator_implementation'] is False and set(replay['files'])=={'candidate_batch.json','validation.json','proof_queue.json'},'worker replay scope mismatch')
    for name,r in replay['files'].items():ensure(r['original_sha256']==sha(d/name) and r['replay_sha256']==sha(d/name) and r['identical'] is True,'worker replay hash mismatch')
    cases=final_design(sha(d/'seal.json'));ensure(read(d/'final_cases.json')==cases,'fresh indices mismatch')
    actual=independent_tables(cases['actual_scales'],spec['stencil_scales'])
    for key,value in actual.items():ensure(final['actual'][key]==value,'final complete arithmetic mismatch')
    ensure(final['actual']['prime_oracle_used_by_producer'] is False,'final producer provenance mismatch')
    ensure([r['program_id'] for r in final['results']]==[c['program_id'] for c in chosen],'final candidate coverage mismatch')
    dyadic_failures=offdomain_failures=component_count=0
    for c,r in zip(chosen,final['results']):
        ensure(r['partition']==[stencil_response(c,row) for row in actual['rows']],'dense partition mismatch')
        expected=stencil_score(c,actual['rows'],cases['seen_levels']+cases['unseen_levels']);ensure(r['score']==expected,'final score mismatch')
        for case in expected['cases']:
            if case['finite_pass'] is False:
                if case['in_dyadic_claim_domain']:dyadic_failures+=1
                else:offdomain_failures+=1
        terms=list(zip(c['program']['scales'],c['program']['weights']))
        ensure(verify_kernel_certificate(r['kernel_certificate'],terms),'kernel component certificate invalid');component_count+=1
        b=r['bridge_certificate'];ensure(b['conditional_bridge_admitted']==c['nonnegative_critical_recurrence_bridge'] and b['signed_inequality_proved'] is False and b['RH_proved'] is False,'bridge overclaim')
        ensure(r['full_signed_bound_proved'] is False,'full bound overclaim')
        ensure(verify_positive_energy_transform(r['positive_energy_transform'],terms),'positive energy transform invalid')
        obstruction=r['energy_bridge_obstruction'];merged={}
        for scale,weight in terms:
            scale=rational(scale);merged[scale]=merged.get(scale,Fraction(0))+rational(weight)
        merged={s:c for s,c in merged.items() if c}
        canonical=[[str(s),str(c)] for s,c in sorted(merged.items())]
        ensure(b['terms']==canonical and rational(b['quadratic_moment'])==sum(c*s*s for s,c in merged.items()),'bridge polynomial mismatch')
        highest=max(merged);powers=all(s.denominator==1 and s>=1 and int(s)&(int(s)-1)==0 for s in merged)
        nonpositive=all(c<=0 for s,c in merged.items() if s<highest);leading=merged[highest]==1
        moment=sum(c*s*s for s,c in merged.items());admitted=powers and leading and nonpositive and moment==0 and highest>1
        ensure(b['conditional_bridge_admitted']==admitted and b['dyadic_positive_integer_scales']==powers and b['leading_coefficient_one']==leading and b['lower_coefficients_nonpositive']==nonpositive,'bridge admission mismatch')
        expected_weights=[[str(s),str(-c*s*s/(highest*highest))] for s,c in sorted(merged.items()) if s<highest]
        ensure(b['normalized_recursion_weights']==expected_weights and rational(b['highest_scale'])==highest and rational(b['epsilon'])==Fraction(1,12),'bridge normalization mismatch')
        ensure(obstruction['actual_Mobius_claim_disproved'] is False and obstruction['sampled_actual_coefficients_used'] is False and obstruction['terms']==canonical,'abstract countermodel promoted')
        ensure([t['exponent'] for t in obstruction['tests']]==[3,4],'obstruction coverage mismatch')
        for t in obstruction['tests']:
            poly=sum(c*s**t['exponent'] for s,c in merged.items())
            ensure(rational(t['exact_dilate_polynomial'])==poly and t['obstruction']==(poly<=0),'abstract obstruction arithmetic mismatch')
        ensure(obstruction['energy_only_critical_bridge_obstructed']==any(t['obstruction'] for t in obstruction['tests']),'abstract obstruction summary mismatch')
    ensure(len(final['coupled_responses'])==len(cases['actual_scales']),'coupled coverage mismatch')
    for X,record in zip(cases['actual_scales'],final['coupled_responses']):
        for key,value in coupled_numeric(X).items():ensure(record[key]==value,'coupled mismatch: '+key)
        ensure(record['shared_cutoff'] is True and record['strict_support_condition'] is True and record['complete_domain']==[X,4*X] and record['moving_cutoff_between_calls'] is True,'coupled domain mismatch')
        ensure(record['all_terms_and_cross_terms_retained'] is True and record['representation_weight_l1']==3 and record['global_actual_signed_bound_proved'] is False,'coupled scope failure')
    cf=calibration_rows(cases['calibration_indices']);ensure(final['calibration_rows']==cf,'fresh calibration mismatch')
    ensure([r['program_id'] for r in final['calibration_results']]==[c['program_id'] for c in selected],'fresh calibration coverage mismatch')
    for c,r in zip(selected,final['calibration_results']):
        ensure(r['cases']==calibration_score(c,cf),'fresh calibration prediction mismatch')
        merged={}
        for t in c['terms']:
            f=t['feature'];key=(f.get('q'),rational(f.get('offset',0))) if f['op']=='floor_root' else ('unsupported',f['op'])
            merged[key]=merged.get(key,Fraction(0))+rational(t['weight'])
        admitted={k:v for k,v in merged.items() if v}=={(2,Fraction(0)):Fraction(1)}
        cert=r['certificate'];ensure(cert['exact_all_scale_law_proved']==admitted and cert['recognized_after_discovery']==admitted and cert['RH_proved'] is False and cert['ordinary_unsmoothed_Mobius_or_Liouville_bound_proved'] is False,'filtered calibration scope mismatch')
    L=spec['training_scales'][-1];mu=factor_prefix(2*L)['mu'];fake=mu[:L+1]+[1]*L
    violations=[{'n':n,'divisor_sum':sum(fake[t] for t in range(1,n+1) if n%t==0)} for n in range(L+1,2*L+1)]
    violations=[v for v in violations if v['divisor_sum']]
    ensure(final['counterfeit_tail']=={'prefix':L,'checked_through':2*L,'violations':violations} and violations,'counterfeit rejection mismatch')
    generation=batch['ast_exploration']['generation'];programs=generation['programs']
    ensure(len(programs)==len({p['program_id'] for p in programs})==spec['ast_sampling']['count'],'AST generation incomplete')
    ensure(generation['response_values_used_for_generation'] is False,'AST response dependent generation')
    ast_counts=[audit_ast(batch['ast_exploration']['training'],programs,spec['ast_training_horizon']),audit_ast(validation['ast_exploration'],programs,spec['ast_validation_horizon'])]
    groups={}
    for r in validation['ast_exploration']['observations']:
        if r['status']=='available':groups.setdefault(r['top_operation'],[]).append(r)
    def rank(r):return (-int(r['metrics']['nontrivial_unsigned_mass']),-rational(r['metrics']['cancellation_gain_ratio']),r['total_charged_operations'],len(json.dumps(r['expression'],sort_keys=True)),r['program_id'])
    ast_selected=[min(groups[op],key=rank) for op in sorted(groups)]
    ensure(queue['ast_queue']==ast_selected,'AST diversity selection mismatch');ast_counts.append(audit_ast(final['ast_exploration'],ast_selected,cases['ast_horizon']))
    for name in ('dependency_sha256','input_sha256'):check_hashes(BASE,spec[name])
    check_hashes(d,final_input_hashes)
    # Re-read every frozen binding after mathematical work.
    verify_source_bindings(d,spec,read(d/'seal.json'),['protocol.json','candidate_batch.json','validation.json','proof_queue.json','contract_tests.txt'])
    return {'schema':1,'all_passed':True,'mathematical_audit_imports_production_code':False,
        'protocol_sha256':digest(spec),'seal_sha256':sha(d/'seal.json'),
        'checks_passed':16,'artifact_sha256':{n:sha(d/n) for n in ['protocol.json','seal.json','candidate_batch.json','validation.json','proof_queue.json','final_cases.json','final_evaluation.json','worker_replay.json','contract_tests.txt']},
        'candidate_count':len(candidates),'selected_count':len(chosen),'component_certificate_count':component_count,
        'stored_constant_dyadic_failures':dyadic_failures,'offdomain_finite_failures':offdomain_failures,
        'calibration_count':len(selected),'ast_counts':ast_counts,
        'independently_verified_AST_generation_algorithm':False,'independently_verified_AST_missing_resource_reason':False,
        'AST_audit_scope':'complete archive coverage; every available coefficient and metric independently reconstructed; retained missing reasons; generator frozen but not independently replayed',
        'full_dense_residual_retained':True,'RH_proved':False,'actual_all_scale_signed_bound_proved':False,
        'scope':'finite exact arithmetic and conditional/component certificates; fitted constants do not establish unknown-q existential global estimates'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',nargs='?',type=Path);parser.add_argument('--run-dir',type=Path);args=parser.parse_args()
    directory=args.run_dir or args.directory
    if directory is None:parser.error('run directory required')
    args.run_dir=directory
    result=audit_run(directory)
    with (args.run_dir/'verification.json').open('x') as stream:
        stream.write(json.dumps(exact_json(result),indent=2)+'\n')


if __name__=='__main__':main()
