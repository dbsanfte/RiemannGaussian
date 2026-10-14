"""Preregistered full-region cell interaction diagnostic, finite witness only."""
import ast
import hashlib
import json
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_cell_gram_program as B
import check_cancellation_shared_gram as I
ROOT=Path(__file__).resolve().parent
FLAGS=dict(global_bound_proved=False,RH_proved=False)
SPEC=dict(version='cell-joint-grams-v1',regions=['parent','child'],atoms=['prefix']+[dict(theta=t,power=j) for t in ['1/3','1/2','2/3'] for j in [-1,0,1]],dimensions={'parent':10,'child':10},selection='all nine divisor channels; all complete t blocks; no fitted choices',scope='diagnostic of supplied witness in larger finite cone; no feasibility or uniform theorem')
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blocks(X):
    original=B.build_blocks(X)['blocks'];out={}
    for region in SPEC['regions']:
        names=[name for name,d in B.group_descriptors().items() if d['kind']=='divisor_cell' and d['region']==region]
        rows=[]
        for k in range(X*(1 if region=='parent' else 2)):
            rows.append([original[names[0]][k][0]]+[original[name][k][1] for name in names])
        out[region]=rows
    return out

def negative_direction(matrix):
    """Exact congruence elimination returns a rational vector, or PSD."""
    n=len(matrix);a=[[F(v) for v in row] for row in matrix];v=[[F(i==j) for i in range(n)] for j in range(n)]
    for k in range(n):
        if a[k][k]<0:return v[k]
        if not a[k][k]:
            j=next((j for j in range(k+1,n) if a[k][j]),None)
            if j is not None:
                t=-a[k][j]/(abs(a[j][j])+1)
                return [x+t*y for x,y in zip(v[k],v[j])]
            continue
        pivot=a[k][k];factors={j:a[k][j]/pivot for j in range(k+1,n)}
        for i in range(k+1,n):
            for j in range(i,n):a[j][i]=a[i][j]=a[i][j]-a[i][k]*a[k][j]/pivot
        for j in range(k+1,n):v[j]=[x-factors[j]*y for x,y in zip(v[j],v[k])]
    I.verify_psd(matrix);return None

def audit(scales,instances,dual):
    given=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if len(given)!=len(set(given)) or len(given)!=len(dual['weights']):raise ValueError('unique exact moments')
    y=dict(zip(given,map(F,dual['weights'])));reports={}
    for region in SPEC['regions']:
        entries=[[{} for j in range(10)] for i in range(10)]
        for k,X in enumerate(scales):
            for atoms in blocks(X)[region]:
                ps=[I.P.parse(a,instances[k]['horizon']) for a in atoms]
                for i in range(10):
                    for j in range(i,10):
                        p=I.P.multiply(ps[i],ps[j])
                        dest=entries[i][j]
                        for m,q in p.items():dest[(k,m)]=dest.get((k,m),F(0))+q
        missing=sorted({key for row in entries for p in row for key,q in p.items() if q and key not in y})
        if missing:
            reports[region]=dict(status='unknown_missing_coordinates',missing=[dict(instance=k,m=list(m)) for k,m in missing]);continue
        matrix=[[F(0)]*10 for _ in range(10)]
        for i in range(10):
            for j in range(i,10):matrix[i][j]=matrix[j][i]=sum((q*y[key] for key,q in entries[i][j].items() if q),F(0))
        direction=negative_direction(matrix);report=dict(matrix=[[str(q) for q in row] for row in matrix])
        if direction is None:report.update(status='PSD',PSD_proof=I.verify_psd(matrix))
        else:
            value=sum((direction[i]*matrix[i][j]*direction[j] for i in range(10) for j in range(10)),F(0))
            if value>=0:raise ValueError('negative direction independently re-evaluated')
            report.update(status='witness_invalid_for_joint_cone',negative_direction=list(map(str,direction)),quadratic_value=str(value))
        reports[region]=report
    return dict(regions=reports,larger_cone_feasibility_proved=False,**FLAGS)

def source_names():
    pending=['cancellation_cell_joint_gram_probe','test_cancellation_cell_joint_gram_probe'];seen=set()
    while pending:
        n=pending.pop();p=ROOT/(n+'.py')
        if n in seen or not p.is_file():continue
        seen.add(n)
        for node in ast.walk(ast.parse(p.read_text())):
            if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0] for a in node.names)
            elif isinstance(node,ast.ImportFrom) and node.module:pending.append(node.module.split('.')[0])
    return sorted(n+'.py' for n in seen)
def freeze(directory):
    d=Path(directory);d.mkdir(parents=True,exist_ok=False);(d/'frozen_source').mkdir();hashes={}
    for n in source_names():(d/'frozen_source'/n).write_bytes((ROOT/n).read_bytes());hashes[n]=sha(ROOT/n)
    parent=ROOT/'cancellation-arithmetic-results/cell-shared-gram-probe-001'
    protocol=dict(spec=SPEC,conditioning='sealed before pending exact native retry dual weights inspected',parent_protocol_sha256=sha(parent/'protocol.json'),required_witness='independently verified exact 20-group separator',missing_policy='unknown; no implicit zero moments',full_source='all nine complete divisor channels per region, original scalar cone and legacy Grams retained',**FLAGS)
    for n,value in [('protocol',protocol),('source_seal',hashes)]: (d/(n+'.json')).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
    seal=dict(protocol_sha256=sha(d/'protocol.json'),source_seal_sha256=sha(d/'source_seal.json'))
    (d/'seal.json').write_text(json.dumps(seal,sort_keys=True,indent=2)+'\n');return seal
