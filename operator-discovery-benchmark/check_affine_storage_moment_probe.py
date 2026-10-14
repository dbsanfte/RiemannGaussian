"""Full-product independent replay of affine anchored moment diagnostics."""
from fractions import Fraction as F
import check_cancellation_shared_gram as I
P=I.P
GROUPS=('full_child','full_parent','storage_K')
FLAGS=dict(global_bound_proved=False,RH_proved=False,larger_cone_feasibility_proved=False)


def terms(polynomial):
    return [dict(instance=k,m=list(m),c=str(q)) for (k,m),q in sorted(polynomial.items()) if q]


def verify(blocks,horizons,dual,result):
    if type(blocks)is not list or len(blocks)!=len(horizons) or any(result.get(k)is not False for k in FLAGS):
        raise ValueError('finite full affine diagnostic')
    if result.get('no_new_floating_search')is not True or result.get('input_dual_sha256')!=I.digest(dual):
        raise ValueError('supplied exact witness only')
    hashes=list(map(I.digest,blocks))
    if result.get('gram_block_hashes')!=hashes or dual.get('gram_block_hashes')!=hashes:raise ValueError('complete source binding')
    domain=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if domain!=sorted(set(domain)) or len(domain)!=len(dual['weights']):raise ValueError('complete ordered domain')
    y=dict(zip(domain,map(I.rational,dual['weights'])))
    if set(result['groups'])!=set(GROUPS):raise ValueError('all affine regional and storage groups')
    statuses={};verified={}
    for group in GROUPS:
        products={(i,j):{} for i in range(15) for j in range(i,15)};rows=[]
        for k,(block,H) in enumerate(zip(blocks,horizons)):
            if set(block)!={'full_child','full_parent'}:raise ValueError('both full regional source sets')
            regions=[('full_child',F(1)),('full_parent',F(-4))] if group=='storage_K' else [(group,F(1))]
            for region,weight in regions:
                for atoms in block[region]:
                    if len(atoms)!=14:raise ValueError('all ordered base atoms')
                    state=[{():F(1)}]+[P.parse(a,H) for a in atoms];rows.append((k,weight,state))
                    for i in range(15):
                        for j in range(i,15):
                            dest=products[i,j]
                            for m,q in P.multiply(state[i],state[j]).items():
                                key=(k,m);dest[key]=dest.get(key,F(0))+weight*q
        products={ij:{m:q for m,q in p.items() if q} for ij,p in products.items()}
        missing=sorted({m for p in products.values() for m in p if m not in y})
        expected_missing=[dict(instance=k,m=list(m)) for k,m in missing]
        row=result['groups'][group];first=[terms(products[0,j]) for j in range(15)]
        if row['unit_row_polynomials']!=first or row['unit_row_polynomials_sha256']!=I.digest(first):raise ValueError('complete affine source polynomials')
        if row['missing']!=expected_missing:raise ValueError('no unsupported moment zero-fill')
        if missing:
            if row['status']!='unknown_missing_coordinates' or 'matrix' in row:raise ValueError('unknown unsupported affine moment')
            statuses[group]=row['status'];verified[group]=dict(verified=True,missing=len(missing));continue
        matrix=[[F(0)]*15 for _ in range(15)]
        for (i,j),p in products.items():matrix[i][j]=matrix[j][i]=sum((q*y[m] for m,q in p.items()),F(0))
        if row['matrix']!=[[str(q) for q in a] for a in matrix]:raise ValueError('all225 affine moment entries')
        lower=[[str(matrix[i][j]) for j in range(1,15)] for i in range(1,15)]
        if lower!=dual['gram_duals'][group]['matrix']:raise ValueError('original full14 moment submatrix')
        I.verify_psd(lower)
        if row['status']=='PSD_extension':
            proof=I.verify_psd(matrix)
            if row['PSD_proof']!=proof:raise ValueError('exact affine PSD proof')
        elif row['status']=='witness_invalid_for_affine_cone':
            v=list(map(I.rational,row['direction']))
            if len(v)!=15:raise ValueError('full15 negative direction')
            value=sum((v[i]*matrix[i][j]*v[j] for i in range(15) for j in range(15)),F(0))
            if value>=0 or row['quadratic_value']!=str(value):raise ValueError('exact affine negative pairing')
            combined={};squares=[]
            for k,weight,state in rows:
                p={}
                for coefficient,atom in zip(v,state):p=P.add(p,atom,coefficient)
                squares.append(dict(instance=k,weight=str(weight),poly=P.canonical(p)))
                for m,q in P.multiply(p,p).items():
                    key=(k,m);combined[key]=combined.get(key,F(0))+weight*q
            combined={m:q for m,q in combined.items() if q}
            if any(m not in y for m in combined):raise ValueError('negative polynomial complete support')
            dot=sum((q*y[m] for m,q in combined.items()),F(0))
            if dot!=value or row['full_polynomial_dot']!=str(dot) or row['signed_square_terms']!=squares or row['expanded_polynomial_sha256']!=I.digest(terms(combined)) or row['full_polynomial_matching_verified']is not True:raise ValueError('complete signed witness polynomial')
        else:raise ValueError('known diagnostic outcome')
        statuses[group]=row['status'];verified[group]=dict(verified=True,missing=0,full_matrix_rebuilt=True)
    expected=('witness_invalid_for_affine_cone' if 'witness_invalid_for_affine_cone' in statuses.values() else
              'witness_extends_to_affine_cone' if all(s=='PSD_extension' for s in statuses.values()) else
              'unknown_missing_coordinates')
    if result['status']!=expected:raise ValueError('honest complete diagnostic status')
    return dict(verified=True,status=expected,group_statuses=statuses,group_checks=verified,
                full_product_replay=True,**FLAGS)
