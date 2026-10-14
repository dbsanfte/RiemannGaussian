"""Independent exact full-cross extension diagnostic of an admitted separator."""
from fractions import Fraction as F
import check_cancellation_complete_gram_program as B
import check_cancellation_shared_gram as I
from cancellation_cell_joint_gram_probe import negative_direction
P=I.P
FLAGS=dict(global_bound_proved=False,RH_proved=False)

def moment_probe(instances,blocks,dual):
    domain=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if len(domain)!=len(set(domain)) or len(domain)!=len(dual['weights']):raise ValueError('unique exact moment domain')
    y=dict(zip(domain,map(I.rational,dual['weights'])));reports={}
    for key,n in B.gram_specs().items():
        entries=[[{} for j in range(n)] for i in range(n)]
        parsed=[]
        for k,(inst,row) in enumerate(zip(instances,blocks)):
            if set(row)!=set(B.gram_specs()):raise ValueError('complete block source groups')
            current=[]
            for atoms in row[key]:
                if len(atoms)!=n:raise ValueError('ordered complete atom count')
                ps=[P.parse(a,inst['horizon']) for a in atoms];current.append(ps)
                for i in range(n):
                    for j in range(i,n):
                        p=P.multiply(ps[i],ps[j]);dest=entries[i][j]
                        for m,q in p.items():dest[(k,m)]=dest.get((k,m),F(0))+q
            parsed.append(current)
        missing=sorted({m for row in entries for p in row for m,q in p.items() if q and m not in y})
        crosshash=I.digest([dict(i=i,j=j,terms=[dict(instance=k,m=list(m),c=str(q)) for (k,m),q in sorted(entries[i][j].items()) if q]) for i in range(n) for j in range(i,n)])
        if missing:
            reports[key]=dict(status='unknown_missing_coordinates',complete_cross_polynomials_sha256=crosshash,missing=[dict(instance=k,m=list(m)) for k,m in missing]);continue
        matrix=[[F(0)]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):matrix[i][j]=matrix[j][i]=sum((q*y[m] for m,q in entries[i][j].items() if q),F(0))
        v=negative_direction(matrix);report=dict(matrix=[[str(q) for q in row] for row in matrix],complete_cross_polynomials_sha256=crosshash,missing=[])
        if v is None:report.update(status='PSD_extension',PSD_proof=I.verify_psd(matrix))
        else:
            expanded={};squares=[]
            for k,rows in enumerate(parsed):
                for ps in rows:
                    a={}
                    for q,p in zip(v,ps):a=P.add(a,p,q)
                    p=P.multiply(a,a);squares.append(dict(instance=k,poly=P.canonical(a)))
                    for m,q in p.items():expanded[(k,m)]=expanded.get((k,m),F(0))+q
            expanded={m:q for m,q in expanded.items() if q}
            if any(m not in y for m in expanded):raise ValueError('direction complete moment domain')
            q=sum((v[i]*matrix[i][j]*v[j] for i in range(n) for j in range(n)),F(0));dot=sum((q*y[m] for m,q in expanded.items()),F(0))
            if q>=0 or dot!=q:raise ValueError('full negative direction polynomial matching')
            report.update(status='witness_invalid_for_complete_cone',negative_direction=list(map(str,v)),quadratic_value=str(q),square_polynomials=squares,full_square_polynomial_dot=str(dot),full_polynomial_matching_verified=True)
        reports[key]=report
    return dict(regions=reports,larger_cone_feasibility_proved=False,source_hashes=list(map(I.digest,instances)),gram_block_hashes=list(map(I.digest,blocks)),**FLAGS)

def audit_existing_separator(program,scales,dual):
    prior=[B.B.build(program,X) for X in scales];aux=B.B.auxiliary();instances=[b['instance'] for b in prior]+[aux['instance']];oldblocks=[b['gram_blocks'] for b in prior]+[aux['gram_blocks']]
    admitted=I.verify_dual(instances,oldblocks,B.B.gram_specs(),dual)
    blocks=[B.assemble_blocks(X,b['gram_blocks'])['blocks'] for X,b in zip(scales,prior)]+[{k:[] for k in B.gram_specs()}]
    result=moment_probe(instances,blocks,dual);result.update(original_four_Gram_separator_admission=admitted,program=program,scales=scales,gram_specs=B.gram_specs(),supplied_separator_sha256=I.digest(dual));return result
