"""Independent exact audit of generic shared Gram finite certificates.

No synthesis, atom-generator, or producer PSD code is imported. Constants are
ordinary polynomial coordinates, including in atoms and cross products.
"""
import hashlib
import json
from fractions import Fraction as F
import check_grouped_arithmetic as G
P = G.P

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()

def rational(value, max_bits=4096):
    if type(value) not in (int, str, F):
        raise ValueError('exact rational required')
    if type(value) is str and (len(value)>4*max_bits+4 or any(c not in '0123456789+-/' for c in value)):
        raise ValueError('bounded rational text')
    q=F(value)
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_bits:
        raise OverflowError('coefficient bits')
    return q

def verify_psd(matrix, *, max_dimension=64, max_operations=1000000, max_coefficient_bits=4096):
    """Exact Schur elimination, independently checking zero-pivot rows."""
    if any(type(v)is not int or v<1 for v in (max_dimension,max_operations,max_coefficient_bits)):
        raise ValueError('positive strict limits')
    if type(matrix)is not list or not matrix or len(matrix)>max_dimension:
        raise ValueError('bounded matrix')
    n=len(matrix)
    if any(type(r)is not list or len(r)!=n for r in matrix):raise ValueError('square matrix')
    a=[[rational(v,max_coefficient_bits) for v in r] for r in matrix]
    if any(a[i][j]!=a[j][i] for i in range(n) for j in range(n)):raise ValueError('symmetric matrix')
    used=0;pivots=[]
    for k in range(n):
        pivot=a[k][k];pivots.append(str(pivot))
        if pivot<0:raise ValueError('negative Schur pivot')
        if pivot==0:
            if any(a[k][j] for j in range(k+1,n)):raise ValueError('zero diagonal nonzero offdiagonal')
            continue
        for i in range(k+1,n):
            for j in range(i,n):
                used+=1
                if used>max_operations:raise OverflowError('PSD operation limit')
                a[i][j]=rational(a[i][j]-a[i][k]*a[k][j]/pivot,max_coefficient_bits)
                a[j][i]=a[i][j]
    return dict(PSD_verified=True,dimension=n,Schur_pivots=pivots,operations=used)

def gram_polynomial(matrix, blocks, horizon):
    n=len(matrix);out={}
    for atoms in blocks:
        if type(atoms)is not list or len(atoms)!=n:raise ValueError('Gram atom dimensions')
        ps=[P.parse(a,horizon) for a in atoms]
        for i in range(n):
            for j in range(n):
                q=rational(matrix[i][j])
                if q:out=P.add(out,P.multiply(ps[i],ps[j]),q)
    return out

def scalar_columns(inst, sw, rw):
    """Validate all premises and polynomial schemas; expand active groups only."""
    import check_grouped_arithmetic_sparse as S
    if type(inst)is not dict or set(inst)!={'target','horizon','lhs','square_groups','relation_groups'}:raise ValueError('instance schema')
    H,t=inst['horizon'],inst['target'];P.integer(H);P.guard(H,'horizon')
    if t not in ('mu','c'):raise ValueError('target')
    if len(inst['square_groups'])!=len(sw) or len(inst['relation_groups'])!=len(rw):raise ValueError('shared dimensions')
    sq=[];rel=[]
    for w,group in zip(sw,inst['square_groups']):
        if type(group)is not list:raise ValueError('square group list')
        out={}
        for term in group:
            if type(term)is not dict or set(term)!={'weight','poly'}:raise ValueError('square atom schema')
            q=S.rational(term['weight']);p=S.parse(term['poly'],H)
            if q<0:raise ValueError('nonnegative within group')
            if w and q:out=P.add(out,P.multiply(p,p),q)
        sq.append(out)
    cache={}
    for w,group in zip(rw,inst['relation_groups']):
        if type(group)is not list:raise ValueError('relation group list')
        out={}
        for term in group:
            if type(term)is not dict or set(term)!={'spec','multiplier'}:raise ValueError('relation atom schema')
            key=digest(term['spec'])
            if key not in cache:cache[key]=G.relation(term['spec'],t,H)
            p=S.parse(term['multiplier'],H)
            if w:out=P.add(out,P.multiply(p,cache[key]))
        rel.append(out)
    return S.parse(inst['lhs'],H),sq,rel

def verify_primal(instances, gram_blocks, gram_specs, result):
    if type(instances)is not list or not instances:raise ValueError('nonempty instances')
    if type(gram_specs)is not dict or not gram_specs or any(type(k)is not str or type(n)is not int or n<1 for k,n in gram_specs.items()):raise ValueError('Gram specifications')
    if type(gram_blocks)is not list or len(gram_blocks)!=len(instances):raise ValueError('Gram instance coverage')
    if result.get('status')!='finite_PSD_certificate':raise ValueError('finite PSD result required')
    if result.get('global_bound_proved') is not False or result.get('RH_proved') is not False:raise ValueError('finite only claim')
    if result.get('gram_specs')!=gram_specs:raise ValueError('Gram spec binding')
    if result.get('source_hashes')!=[digest(i) for i in instances]:raise ValueError('source hash binding')
    if result.get('gram_block_hashes')!=[digest(b) for b in gram_blocks]:raise ValueError('source Gram block binding')
    grams=result['grams']
    if type(grams)is not dict or set(grams)!=set(gram_specs):raise ValueError('exact Gram groups')
    proofs={}
    for key,n in gram_specs.items():
        if len(grams[key])!=n:raise ValueError('declared Gram dimension')
        proofs[key]=verify_psd(grams[key])
    gram_specs=dict(sorted(gram_specs.items()))
    weights=result['weights'];sw=list(map(rational,weights['square_weights']));rw=list(map(rational,weights['relation_weights']))
    if any(w<0 for w in sw):raise ValueError('nonnegative scalar square weights')
    if len(result['certificates'])!=len(instances):raise ValueError('certificate coverage')
    slacks=[]
    for inst,blocks,record in zip(instances,gram_blocks,result['certificates']):
        if type(blocks)is not dict or set(blocks)!=set(gram_specs) or any(type(b)is not list for b in blocks.values()):raise ValueError('exact source block groups')
        lhs,sq,rel=scalar_columns(inst,sw,rw);rhs={};expected_squares=[];expected_relations=[]
        if len(sq)!=len(sw) or len(rel)!=len(rw):raise ValueError('shared scalar dimensions')
        for w,p,group in zip(sw,sq,inst['square_groups']):
            rhs=P.add(rhs,p,w)
            for s in group:
                v=w*rational(s['weight'])
                if v:expected_squares.append(dict(weight=str(v),poly=s['poly']))
        for w,p,group in zip(rw,rel,inst['relation_groups']):
            rhs=P.add(rhs,p,w)
            if w:
                for r in group:expected_relations.append(dict(spec=r['spec'],multiplier=P.canonical({m:w*c for m,c in P.parse(r['multiplier'],inst['horizon']).items()})))
        gps=record['Gram_proofs']
        if set(gps)!=set(gram_specs):raise ValueError('Gram proof coverage')
        for key in gram_specs:
            gp=gps[key];p=gram_polynomial(grams[key],blocks[key],inst['horizon']);rhs=P.add(rhs,p)
            if P.parse(gp['polynomial'],inst['horizon'])!=p:raise ValueError('complete Gram polynomial coefficients')
            if gp['decomposition']['matrix']!=grams[key]:raise ValueError('Gram proof matrix binding')
            expanded={}
            for term in gp['squares']:
                if set(term)!={'weight','poly'}:raise ValueError('Gram square schema')
                w=rational(term['weight'])
                if w<0:raise ValueError('negative Gram SOS weight')
                a=P.parse(term['poly'],inst['horizon']);expanded=P.add(expanded,P.multiply(a,a),w)
            if expanded!=p:raise ValueError('complete Gram SOS crosses')
            expected_squares.extend(gp['squares'])
        residue=P.add(lhs,rhs,F(-1));slack=residue.get((),F(0))
        if any(m for m in residue) or slack<0:raise ValueError('full original target residual / scalar budget')
        slacks.append(str(slack))
        if 'constant_slack' in record and rational(record['constant_slack'])!=slack:raise ValueError('recorded instance constant slack')
        if slack:expected_squares.append(dict(weight=str(slack),poly=[dict(m=[],c='1')]))
        expected=dict(target=inst['target'],horizon=inst['horizon'],lhs=inst['lhs'],squares=expected_squares,relations=expected_relations)
        if record['certificate']!=expected:raise ValueError('flattened shared certificate binding')
        G.verify_certificate(record['certificate'])
    if result['constant_slacks']!=slacks:raise ValueError('exact scalar slack')
    if 'exact_column_weights' in result:
        vals=list(map(rational,result['exact_column_weights']));ns,nr=len(sw),len(rw);offset=ns+2*nr+len(instances)
        upper=[rational(grams[k][i][j]) for k,n in gram_specs.items() for i in range(n) for j in range(i,n)]
        if len(vals)!=offset+len(upper) or vals[:ns]!=sw or any(v<0 for v in vals[:offset]) or [vals[ns+2*j]-vals[ns+2*j+1] for j in range(nr)]!=rw or vals[ns+2*nr:offset]!=list(map(F,slacks)) or vals[offset:]!=upper:raise ValueError('exact column weights shared binding')
    return dict(verified=True,PSD_proofs=proofs,constant_slacks=slacks,shared_weights_verified=True,source_binding_verified=True,finite_only=True,global_bound_proved=False,RH_proved=False)

def verify_dual(instances, gram_blocks, gram_specs, result):
    """Audit an exact separator against the entire supplied shared Gram cone."""
    if result.get('status')!='exact_separator' or result.get('certified') is not True:raise ValueError('exact separator required')
    if result.get('global_bound_proved') is not False or result.get('RH_proved') is not False:raise ValueError('finite only claim')
    if result.get('gram_specs')!=gram_specs or result.get('source_hashes')!=[digest(i) for i in instances] or result.get('gram_block_hashes')!=[digest(b) for b in gram_blocks]:raise ValueError('dual source binding')
    if not instances or len(gram_blocks)!=len(instances):raise ValueError('dual instance coverage')
    specs=dict(sorted(gram_specs.items()));allcols=[G.columns(i) for i in instances];ns,nr=len(allcols[0][1]),len(allcols[0][2]);domain=set();cross={}
    for k,(inst,blocks,(lhs,sq,rel)) in enumerate(zip(instances,gram_blocks,allcols)):
        if len(sq)!=ns or len(rel)!=nr or set(blocks)!=set(specs):raise ValueError('complete dual groups')
        domain.add((k,()))
        for p in [lhs]+sq+rel:domain.update((k,m) for m in p)
        for group,n in specs.items():
            for atoms in blocks[group]:
                if type(atoms)is not list or len(atoms)!=n:raise ValueError('dual atom dimensions')
                ps=[P.parse(a,inst['horizon']) for a in atoms]
                for i in range(n):
                    for j in range(i,n):
                        p=P.multiply(ps[i],ps[j])
                        key=(group,i,j,k);cross[key]=P.add(cross.get(key,{}),p)
    for (group,i,j,k),p in cross.items():domain.update((k,m) for m in p)
    domain=sorted(domain);given=[(r['instance'],tuple(r['m'])) for r in result['monomials']]
    if given!=domain or len(result['weights'])!=len(domain):raise ValueError('complete dual coefficient domain')
    y=dict(zip(domain,map(rational,result['weights'])))
    def dot(k,p):return sum((q*y[k,m] for m,q in p.items()),F(0))
    lhs=sum((dot(k,l) for k,(l,s,r) in enumerate(allcols)),F(0));sd=[sum((dot(k,s[j]) for k,(l,s,r) in enumerate(allcols)),F(0)) for j in range(ns)];rd=[sum((dot(k,r[j]) for k,(l,s,r) in enumerate(allcols)),F(0)) for j in range(nr)];cd=[y[k,()] for k in range(len(instances))]
    if lhs>=0 or any(q<0 for q in sd+cd) or any(rd):raise ValueError('exact scalar separator signs')
    if list(map(rational,result['columns_dot_y']))!=sd+[v for q in rd for v in (q,-q)]+cd or rational(result['lhs_dot_y'])!=lhs:raise ValueError('recorded scalar dual dots')
    if 'constant_coordinates' in result and list(map(rational,result['constant_coordinates']))!=cd:raise ValueError('recorded constant coordinates')
    if 'all_C_q_extension_requires_zero_constant_coordinates' in result and result['all_C_q_extension_requires_zero_constant_coordinates'] is not all(v==0 for v in cd):raise ValueError('constant extension claim')
    if set(result['gram_duals'])!=set(specs):raise ValueError('dual Gram coverage')
    matrices={}
    for group,n in specs.items():
        matrix=[[F(0)]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                matrix[i][j]=matrix[j][i]=sum((dot(k,cross.get((group,i,j,k),{})) for k in range(len(instances))),F(0))
        verify_psd(matrix)
        expected=[[str(q) for q in row] for row in matrix]
        if result['gram_duals'][group]['matrix']!=expected:raise ValueError('complete Gram dual matrix')
        matrices[group]=expected
    if 'gram_columns_dot_y' in result:
        expected_dots=[rational(matrices[k][i][j])*(1 if i==j else 2) for k,n in specs.items() for i in range(n) for j in range(i,n)]
        if list(map(rational,result['gram_columns_dot_y']))!=expected_dots:raise ValueError('recorded Gram column dots')
    return dict(verified=True,full_Gram_dual_matrices=matrices,declared_finite_cone_only=True,all_constant_coordinates_verified=True,global_bound_proved=False,RH_proved=False)

def scalar_cell_charge(grams, contexts, X):
    """Exact formal scalar charge for fixed complete [P,D] cell groups.

Every weight family a^power has w_1=1. Thus P_0=0 and D_0=-1/2;
there are X parent and 2X child blocks. PSD makes this charge nonnegative.
This is a necessary scalar accounting fact, not a uniform bound theorem.
"""
    if type(X)is not int or X<1:raise ValueError('positive scale')
    charge=F(0)
    for key,context in contexts.items():
        if context['region'] not in ('parent','child'):raise ValueError('cell region')
        matrix=grams[key]
        if len(matrix)!=2:raise ValueError('[P,D] dimension')
        verify_psd(matrix)
        charge+=rational(matrix[1][1])*X*(1 if context['region']=='parent' else 2)/4
    return dict(formal_scalar_charge=str(charge),linear_coefficient=str(charge/X),nonnegative=True,global_bound_proved=False,RH_proved=False)
