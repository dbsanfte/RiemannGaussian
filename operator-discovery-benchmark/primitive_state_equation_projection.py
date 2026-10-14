"""Exact column identities for row-basis preprocessing only.

The projected coefficients are not a reduced optimization variable domain.
Selected equation indices must be applied to the complete original equations.
"""
from fractions import Fraction as F
import hashlib
import json
import math
import time

SCHEMA='primitive-state-exact-equation-projection-v1'

class _Limit(Exception):pass

def _encoded(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()

def _digest(value):return hashlib.sha256(_encoded(value)).hexdigest()


def full15_recipes(shape,offset,specs,n_columns):
    """Declare identities; project_equations must VERIFY them before use.

    Groups use the original sorted Gram group order, matching source assembly.
    This declaration alone proves no coefficient identity.
    """
    if type(shape)not in (tuple,list) or len(shape)!=2 or any(type(n)is not int or n<0 for n in shape):raise ValueError('scalar shape')
    ns,nr=shape
    if type(offset)is not int or offset<ns+2*nr:raise ValueError('scalar offset')
    if type(n_columns)is not int or n_columns<offset:raise ValueError('column count')
    expected={'full_child':15,'full_parent':15,'storage_K':15}
    if specs!=expected or any(type(n)is not int for n in specs.values()):raise ValueError('complete full15 specs')
    if n_columns!=offset+360:raise ValueError('complete full15 layout')
    recipes={ns+2*j+1:{ns+2*j:F(-1)} for j in range(nr)}
    starts={name:offset+120*k for k,name in enumerate(sorted(specs))}
    for j in range(120):recipes[starts['storage_K']+j]={starts['full_child']+j:F(1),starts['full_parent']+j:F(-4)}
    retained=[i for i in range(n_columns) if i not in recipes]
    return retained,recipes


def project_equations(columns,lhs,monomials,retained_indices,recipes,*,deadline,
                      max_operations=450000000,max_source_cells=4000000,
                      max_live_cells=4000000,max_coefficient_bits=4096,
                      max_receipt_bytes=8388608):
    """Return ``(projected_rows, unchanged_rhs, receipt)`` or UNKNOWN with None.

    Full columns are sparse exact polynomials over the declared monomial domain.
    Each omitted index has a recipe in retained ORIGINAL column indices.
    Verification establishes full coefficient rows are determined by projected
    rows. Including the unchanged RHS makes this an injective augmented-row
    projection. It authorizes row-basis preprocessing, never variable removal.

    Hashes encode coefficients using integer monomial-domain positions, avoiding
    assumptions about the labels' natural order. Labels must be JSON encodable.
    """
    if type(columns)is not list or not columns or type(lhs)is not dict or type(monomials)is not list:raise ValueError('source domain schema')
    if type(retained_indices)is not list or not retained_indices or type(recipes)is not dict:raise ValueError('projection schema')
    if type(deadline)not in (int,float) or not math.isfinite(deadline):raise ValueError('finite deadline')
    caps=dict(max_operations=max_operations,max_source_cells=max_source_cells,max_live_cells=max_live_cells,max_coefficient_bits=max_coefficient_bits,max_receipt_bytes=max_receipt_bytes)
    if any(type(v)is not int or v<1 for v in caps.values()) or max_receipt_bytes<256:raise ValueError('positive caps; receipt cap at least256')
    n=len(columns)
    if any(type(i)is not int or not 0<=i<n for i in retained_indices) or len(set(retained_indices))!=len(retained_indices):raise ValueError('retained indices')
    if any(type(i)is not int or not 0<=i<n for i in recipes) or set(retained_indices)&set(recipes) or set(retained_indices)|set(recipes)!=set(range(n)):raise ValueError('complete disjoint column partition')
    retained_set=set(retained_indices)
    for i,recipe in recipes.items():
        if type(recipe)is not dict or any(type(j)is not int or j not in retained_set for j in recipe):raise ValueError('recipes reference retained original columns only')
    try:domain=set(monomials)
    except TypeError as e:raise ValueError('hashable monomial labels') from e
    if len(domain)!=len(monomials):raise ValueError('unique monomial domain')
    if any(type(p)is not dict for p in columns):raise ValueError('sparse column schema')
    counts=dict(operations=0,source_cells=0,peak_live_cells=0,identities_verified=0,recipe_cells=0,projected_cells=0,receipt_bytes=0)
    receipt=dict(schema=SCHEMA,status='unknown',complete=False,projection_use='exact augmented-row-span preprocessing only',
        solver_variable_mapping='identity',solver_cone_mapping='identity',solver_objective_mapping='identity',
        target_mapping='identity',original_columns=n,projected_columns=len(retained_indices),rows=len(monomials),
        retained_indices=retained_indices[:],recipes=[],limits=caps,counts=counts)
    start=time.monotonic()
    def charge(amount=1):
        counts['operations']+=amount
        if counts['operations']>max_operations:raise _Limit('operation cap')
        if time.monotonic()>deadline:raise _Limit('deadline')
    def rational(value):
        if type(value)not in (int,F):raise ValueError('exact rational coefficient required')
        charge();q=F(value)
        if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>max_coefficient_bits:raise _Limit('coefficient bit cap')
        return q
    def live(amount):
        if amount>max_live_cells:raise _Limit('live cell cap')
        counts['peak_live_cells']=max(counts['peak_live_cells'],amount)
    def fingerprint(value):
        payload=_encoded(value);charge(len(payload)//64+1);return hashlib.sha256(payload).hexdigest()
    try:
        charge(n+len(monomials)+len(retained_indices)+len(recipes)+sum(map(len,recipes.values())))
        source_size=sum(map(len,columns))+len(lhs)
        if source_size>max_source_cells:raise _Limit('source cell cap')
        actual_domain=set(lhs);charge(len(lhs))
        for p in columns:
            charge(len(p)+1);actual_domain.update(p)
        if domain!=actual_domain:raise ValueError('complete source/target domain')
        live(len(domain)+len(actual_domain));del actual_domain
        lookup={m:i for i,m in enumerate(monomials)};charge(len(monomials));live(len(lookup))
        receipt['monomial_domain_hash']=fingerprint(monomials)
        rhs=[rational(lhs.get(m,F(0))) for m in monomials];receipt['target_hash']=fingerprint(list(map(str,rhs)))
        h=hashlib.sha256();h.update(b'[')
        for i,p in enumerate(columns):
            counts['source_cells']+=len(p)
            if counts['source_cells']+len(lhs)>max_source_cells:raise _Limit('source cell cap')
            live(len(lookup)+len(rhs)+len(p));charge(len(p)*max(1,len(p).bit_length()))
            if i:h.update(b',')
            h.update(b'[');payload_bytes=2
            for k,m in enumerate(sorted(p,key=lambda m:lookup[m])):
                payload=_encoded([lookup[m],str(rational(p[m]))]);payload_bytes+=len(payload)+int(k>0)
                if k:h.update(b',')
                h.update(payload)
            h.update(b']');charge(payload_bytes//64+1)
        h.update(b']');counts['source_cells']+=len(lhs);receipt['full_columns_hash']=h.hexdigest()
        receipt['full_source_hash']=fingerprint({k:receipt[k] for k in ('full_columns_hash','monomial_domain_hash','target_hash')})
        recipe_payload=[];recipe_payload_bytes=2
        for omitted,recipe in sorted(recipes.items()):
            clean={};entry_bytes=5+len(str(omitted))
            for j,q in sorted(recipe.items()):
                q=rational(q)
                if q:
                    entry_bytes+=len(_encoded([j,str(q)]))+int(bool(clean))
                    if recipe_payload_bytes+entry_bytes+1024>max_receipt_bytes:raise _Limit('receipt byte cap')
                    clean[j]=q
            counts['recipe_cells']+=len(recipe)
            encoded=[omitted,[[j,str(q)] for j,q in clean.items()]]
            recipe_payload_bytes+=len(_encoded(encoded))+int(bool(recipe_payload));recipe_payload.append(encoded)
            reconstructed={}
            for j,multiplier in clean.items():
                for m,q in columns[j].items():
                    charge(2);product=rational(multiplier*q);value=rational(reconstructed.get(m,F(0))+product)
                    if value:
                        if m not in reconstructed:live(len(lookup)+len(rhs)+len(reconstructed)+1)
                        reconstructed[m]=value
                    else:reconstructed.pop(m,None)
            target={m:F(q) for m,q in columns[omitted].items() if q};live(len(lookup)+len(rhs)+len(reconstructed)+len(target));charge(len(target)+len(reconstructed))
            if reconstructed!=target:raise ValueError('unverified omitted column identity '+str(omitted))
            counts['identities_verified']+=1
        receipt['recipes']=recipe_payload
        receipt['projection_hash']=fingerprint(dict(full_source_hash=receipt['full_source_hash'],retained_indices=retained_indices,recipes=recipe_payload))
        if len(_encoded(receipt))+1024>max_receipt_bytes:raise _Limit('receipt byte cap')
        projected=[{} for _ in monomials];projected_cells=0;live(len(lookup)+len(rhs)+len(projected))
        for new,j in enumerate(retained_indices):
            for m,q in columns[j].items():
                charge();q=F(q)
                if q:
                    projected_cells+=1;live(len(lookup)+len(rhs)+len(projected)+projected_cells)
                    projected[lookup[m]][new]=q
        counts['projected_cells']=projected_cells
        # Match the exact-row reducer's canonical source hash, streamed.
        h=hashlib.sha256();h.update(b'{"rhs":');payload=_encoded(list(map(str,rhs)));charge(len(payload)//64+1);h.update(payload);h.update(b',"rows":[')
        for i,row in enumerate(projected):
            if i:h.update(b',')
            h.update(b'[');payload_bytes=2
            for k,j in enumerate(sorted(row)):
                payload=_encoded([j,str(row[j])]);payload_bytes+=len(payload)+int(k>0)
                if k:h.update(b',')
                h.update(payload)
            h.update(b']');charge(len(row)*max(1,len(row).bit_length())+payload_bytes//64+1)
        h.update(b'],"variables":');h.update(str(len(retained_indices)).encode());h.update(b'}');receipt['projected_rows_hash']=h.hexdigest()
        receipt.update(status='complete',complete=True,elapsed_seconds=time.monotonic()-start)
        for _ in range(3):counts['receipt_bytes']=len(_encoded(receipt))
        if counts['receipt_bytes']>max_receipt_bytes:raise _Limit('receipt byte cap')
        charge()
        for _ in range(3):counts['receipt_bytes']=len(_encoded(receipt))
        return projected,rhs,receipt
    except _Limit as error:
        receipt.update(status='unknown',complete=False,reason=str(error),elapsed_seconds=time.monotonic()-start)
        for _ in range(3):counts['receipt_bytes']=len(_encoded(receipt))
        if counts['receipt_bytes']>max_receipt_bytes:
            receipt['recipes']=[];receipt['retained_indices']=[];receipt['partial_mapping_omitted']=True
            for _ in range(3):counts['receipt_bytes']=len(_encoded(receipt))
        if len(_encoded(receipt))>max_receipt_bytes:receipt={k:receipt[k] for k in ('schema','status','complete','reason')}
        return None,None,receipt
