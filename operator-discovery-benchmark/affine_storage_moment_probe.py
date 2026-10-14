"""Complete affine unit extension of an already admitted anchored separator.

Only new unit-row moments are needed. Existing full14 moment blocks are bound
to the admitted input, and a negative direction is checked by full polynomial
expansion. Missing coordinates remain unknown after exact cancellation.
"""
from fractions import Fraction as F
import check_cancellation_shared_gram as I
import check_cancellation_anchored_storage as B
from check_complete_gram_moment_probe_v2 import negative_direction

P=I.P
FLAGS=dict(global_bound_proved=False,RH_proved=False,larger_cone_feasibility_proved=False)
SPEC=dict(version='affine-anchored-unit-probe-v1',base=B.SPEC,dimension=15,
          atoms=['unit']+B.SPEC['atoms'],prefix_anchor_index=1,
          constant_vector=['1']+['0']*5+['-1/2']*9,
          selection='prepend the constant unit to every complete regional and storage state; retain every pair',
          storage_increment='child minus four parent; signed transport',
          auxiliary_blocks='empty',missing_policy='unknown after exact coefficient cancellation',
          new_floating_search=False)


def geometry(blocks,group):
    if group=='full_child':return [(F(1),row) for row in blocks['full_child']]
    if group=='full_parent':return [(F(1),row) for row in blocks['full_parent']]
    if group=='storage_K':return [(F(1),row) for row in blocks['full_child']]+[(F(-4),row) for row in blocks['full_parent']]
    raise ValueError('complete anchored group')


def add_stacked(out,k,p,weight):
    for m,q in p.items():
        key=(k,m);v=out.get(key,F(0))+weight*q
        if v:out[key]=v
        else:out.pop(key,None)


def encode_stacked(p):
    return [dict(instance=k,m=list(m),c=str(q)) for (k,m),q in sorted(p.items())]


def moments(blocks,horizons,dual):
    if type(blocks)is not list or len(blocks)!=len(horizons) or dual.get('gram_specs')!=B.gram_specs():
        raise ValueError('complete full14 source coverage')
    if list(map(I.digest,blocks))!=dual.get('gram_block_hashes'):
        raise ValueError('original admitted block binding')
    domain=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if domain!=sorted(set(domain)) or len(domain)!=len(dual['weights']):raise ValueError('unique ordered moment domain')
    y=dict(zip(domain,map(I.rational,dual['weights'])));reports={}
    for group in B.gram_specs():
        old=dual['gram_duals'][group]['matrix']
        if len(old)!=14:raise ValueError('admitted full14 moment dimension')
        I.verify_psd(old)
        first=[{} for _ in range(15)];parsed=[]
        for k,(row,H) in enumerate(zip(blocks,horizons)):
            if set(row)!=set(B.B.gram_specs()):raise ValueError('complete original regional blocks')
            current=[]
            for weight,atoms in geometry(row,group):
                if len(atoms)!=14:raise ValueError('complete ordered atom vector')
                ps=[{():F(1)}]+[P.parse(atom,H) for atom in atoms]
                current.append((weight,ps))
                for i,p in enumerate(ps):add_stacked(first[i],k,p,weight)
            parsed.append(current)
        encoded=[encode_stacked(p) for p in first]
        missing=sorted({m for p in first for m in p if m not in y})
        report=dict(unit_row_polynomials=encoded,unit_row_polynomials_sha256=I.digest(encoded),
                    missing=[dict(instance=k,m=list(m)) for k,m in missing])
        if missing:
            report['status']='unknown_missing_coordinates';reports[group]=report;continue
        matrix=[[F(0)]*15 for _ in range(15)]
        for i,p in enumerate(first):matrix[0][i]=matrix[i][0]=sum((q*y[m] for m,q in p.items()),F(0))
        for i in range(14):
            for j in range(14):matrix[i+1][j+1]=I.rational(old[i][j])
        direction=negative_direction(matrix)
        report.update(matrix=[[str(q) for q in row] for row in matrix])
        if direction is None:
            report.update(status='PSD_extension',PSD_proof=I.verify_psd(matrix))
        else:
            combined={};terms=[]
            for k,rows in enumerate(parsed):
                for weight,ps in rows:
                    linear={}
                    for q,p in zip(direction,ps):linear=P.add(linear,p,q)
                    polynomial=P.multiply(linear,linear);add_stacked(combined,k,polynomial,weight)
                    terms.append(dict(instance=k,weight=str(weight),poly=P.canonical(linear)))
            if any(m not in y for m in combined):raise ValueError('complete negative-direction polynomial support')
            value=sum((direction[i]*matrix[i][j]*direction[j] for i in range(15) for j in range(15)),F(0))
            dot=sum((q*y[m] for m,q in combined.items()),F(0))
            if value>=0 or dot!=value:raise ValueError('expanded complete affine direction matches moment')
            report.update(status='witness_invalid_for_affine_cone',direction=list(map(str,direction)),
                          quadratic_value=str(value),full_polynomial_dot=str(dot),
                          signed_square_terms=terms,expanded_polynomial_sha256=I.digest(encode_stacked(combined)),
                          full_polynomial_matching_verified=True)
        reports[group]=report
    if any(v['status']=='witness_invalid_for_affine_cone' for v in reports.values()):status='witness_invalid_for_affine_cone'
    elif all(v['status']=='PSD_extension' for v in reports.values()):status='witness_extends_to_affine_cone'
    else:status='unknown_missing_coordinates'
    return dict(status=status,groups=reports,gram_block_hashes=list(map(I.digest,blocks)),
                input_dual_sha256=I.digest(dual),no_new_floating_search=True,**FLAGS)
