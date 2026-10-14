"""Independent exact proportional-augmented-row compression audit."""
from fractions import Fraction as F
import hashlib
import json

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def augmented_rows(columns,lhs,support):
    """Rows of selected-variable system, keeping the RHS in proportionality."""
    if type(columns)is not list or type(lhs)is not dict or type(support)is not list or any(type(i)is not int or not 0<=i<len(columns) for i in support) or len(set(support))!=len(support):raise ValueError('same support schema')
    keys=set(lhs)
    for i in support:keys.update(columns[i])
    return sorted(keys),[[F(columns[i].get(k,0)) for i in support]+[F(lhs.get(k,0))] for k in sorted(keys)]

def canonical_compression(columns,lhs,support):
    labels,rows=augmented_rows(columns,lhs,support);seen={};representatives=[];mapping=[];normalized=[]
    for label,row in zip(labels,rows):
        pivot=next((v for v in row if v),None)
        if pivot is None:
            mapping.append(dict(row=label,representative=None,ratio='0'));continue
        signature=tuple(v/pivot for v in row)
        if signature not in seen:
            seen[signature]=(label,pivot);representatives.append(label);normalized.append(list(map(str,signature)))
        rep,rep_pivot=seen[signature]
        mapping.append(dict(row=label,representative=rep,ratio=str(pivot/rep_pivot)))
    return dict(row_labels=labels,representatives=representatives,row_mapping=mapping,normalized_augmented_rows=normalized,original_rows=len(rows),compressed_rows=len(representatives),support=list(support),augmented_rows_sha256=digest([[str(q) for q in r] for r in rows]))

def verify_mapping(columns,lhs,support,compression):
    expected=canonical_compression(columns,lhs,support)
    for key,value in expected.items():
        if compression.get(key)!=value:raise ValueError('exact compression mismatch '+key)
    return dict(verified=True,exact_augmented_row_equivalence_verified=True,original_rows=expected['original_rows'],compressed_rows=expected['compressed_rows'],same_support_verified=True,global_bound_proved=False,RH_proved=False)

def verify_original_solution(columns,lhs,support,weights):
    if len(weights)!=len(support):raise ValueError('same support solution coverage')
    _,rows=augmented_rows(columns,lhs,support);w=list(map(F,weights))
    if any(sum((q*v for q,v in zip(row[:-1],w)),F(0))!=row[-1] for row in rows):raise ValueError('all original augmented equations')
    return dict(verified=True,all_original_equations_verified=True,global_bound_proved=False,RH_proved=False)

def verify_producer_compression(columns,lhs,support,report,*,max_work=450000000):
    """Rebuild all augmented rows independently; no native/backend imports."""
    labels,rows=augmented_rows(columns,lhs,support);canonical=canonical_compression(columns,lhs,support)
    index={label:i for i,label in enumerate(labels)}
    retained=[index[k] for k in canonical['representatives']]
    mapping=[dict(row=i,representative=None if r['representative'] is None else index[r['representative']],ratio=r['ratio']) for i,r in enumerate(canonical['row_mapping'])]
    sparse=[[[j,str(q)] for j,q in enumerate(row) if q] for row in rows]
    expected=dict(original_row_labels=labels,retained_rows=retained,mapping=mapping,original_system_hash=digest(sparse),original_row_order_hash=digest(labels))
    for key,value in expected.items():
        if report.get(key)!=value:raise ValueError('producer compression equivalence '+key)
    n=len(support);original_work=len(rows)*max(1,n)**2;native_work=len(retained)*max(1,n)**2
    if report.get('original_work_proxy')!=original_work or report.get('native_work_proxy')!=native_work:raise ValueError('unchanged native work proxy')
    E=sum(len(columns[i]) for i in support);S=sum(sum(bool(q) for q in columns[i].values()) for i in support);T=len(lhs);U=sum(bool(q) for q in lhs.values())
    R=len(rows);A=sum(sum(bool(q) for q in row) for row in rows);V=sum(any(row) for row in rows);B=sum(sum(bool(q) for q in rows[i]) for i in retained)
    pre=E+2*S+T+U+R+4*A+V+B;cells=2*S+U+A+B;reserve=4*S+T+R+1
    expected_counts=dict(original_rows=R,reduced_rows=len(retained),support_size=n,preprocessing_work=pre,preprocessing_cells=cells,verification_work_reserve=reserve)
    for key,value in expected_counts.items():
        if report.get(key)!=value:raise ValueError('compression resource accounting '+key)
    total=pre+native_work+reserve+report.get('dual_build_work_proxy',0)+report.get('dual_verification_work_reserve',0)
    if report.get('total_work_proxy')!=total or total>max_work:raise ValueError('compression work gate')
    if 'preprocessing_actual_work' in report and report['preprocessing_actual_work']!=pre+4*S+1:raise ValueError('post verification work count')
    return dict(verified=True,all_augmented_rows_rebuilt=True,row_equivalence_verified=True,same_support_verified=True,original_work_proxy=original_work,native_work_proxy=native_work,total_work_proxy=report['total_work_proxy'],global_bound_proved=False,RH_proved=False)

def dual_equations(columns,lhs,monomials,nonnegative_indices,relation_indices):
    """Independent transpose for fixed-support nonnegative dual reconstruction."""
    selected=relation_indices+nonnegative_indices;nr=len(selected)+1;M=len(monomials)
    if len(set(selected))!=len(columns) or set(selected)!=set(range(len(columns))):raise ValueError('complete dual column classifications')
    if set(monomials)!=set(lhs)|{m for p in columns for m in p}:raise ValueError('complete original domain')
    equations=[]
    for m in monomials:
        p={r:F(columns[i].get(m,0)) for r,i in enumerate(selected) if columns[i].get(m,0)}
        if lhs.get(m,0):p[nr-1]=F(lhs[m])
        equations.append(p)
    equations.extend({r:-q for r,q in p.items()} for p in equations[:M])
    equations.extend({len(relation_indices)+j:F(-1)} for j in range(len(nonnegative_indices)))
    return equations,{nr-1:F(-1)}

def independent_columns(instances,blocks,specs):
    import check_grouped_arithmetic as G
    P=G.P;source=[G.columns(i) for i in instances];ns,nr=len(source[0][1]),len(source[0][2]);columns=[];lhs={}
    for k,(p,s,r) in enumerate(source):
        for m,q in p.items():lhs[(k,)+m]=q
    def stack(ps):return {(k,)+m:q for k,p in enumerate(ps) for m,q in p.items() if q}
    columns.extend(stack([s[j] for p,s,r in source]) for j in range(ns))
    for j in range(nr):
        col=stack([r[j] for p,s,r in source]);columns.extend([col,{m:-q for m,q in col.items()}])
    columns.extend({(k,):F(1)} for k in range(len(instances)));offset=len(columns)
    nonnegative=list(range(ns))+list(range(ns+2*nr,offset));relations=list(range(ns,ns+2*nr))
    for group,n in sorted(specs.items()):
        for i in range(n):
            for j in range(i,n):
                (nonnegative if i==j else relations).append(len(columns));ps=[]
                for inst,row in zip(instances,blocks):
                    out={}
                    for atoms in row[group]:
                        a=P.parse(atoms[i],inst['horizon']);b=P.parse(atoms[j],inst['horizon']);out=P.add(out,P.multiply(a,b),1 if i==j else 2)
                    ps.append(out)
                columns.append(stack(ps))
    domain=sorted(set(lhs)|{m for p in columns for m in p})
    return columns,lhs,domain,nonnegative,relations

def verify_arithmetic_archive(directory):
    """Standalone source/support/compression/full-cone admission of a replay."""
    from pathlib import Path
    import check_cancellation_joint_gram_program as B
    import check_cancellation_shared_gram as G
    d=Path(directory).resolve();root=Path(__file__).resolve().parent
    def read(p):return json.loads(Path(p).read_text())
    def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
    seal=read(d/'seal.json')
    for key in ['protocol','source_seal','input','support']:
        if seal[key+'_sha256']!=sha(d/(key+'.json')):raise ValueError('archive seal '+key)
    for name,h in read(d/'source_seal.json').items():
        if sha(root/name)!=h or sha(d/'frozen_source'/name)!=h:raise ValueError('frozen source '+name)
    for name,h in read(d/'input.json')['input_sha256'].items():
        if sha(root/name)!=h:raise ValueError('original input '+name)
    for name,h in read(d/'receipt.json')['files_sha256'].items():
        if sha(d/name)!=h:raise ValueError('terminal receipt '+name)
    protocol=read(d/'protocol.json');support=read(d/'support.json');result=read(d/'result.json');dual=result['synthesis']
    if protocol['limits']['max_work']!=450000000:raise ValueError('unchanged 450m work gate')
    original_path=root/'cancellation-arithmetic-results/joint-shared-gram-probe-001/jobs/dual-000.json';original=read(original_path)
    if support['original_dual_sha256']!=sha(original_path) or support['indices']!=original['synthesis']['proposal_diagnostics']['support'] or dual.get('saved_support')!=support['indices']:raise ValueError('same failed support binding')
    if len(support['indices'])!=protocol['support_count'] or protocol['support_count']!=632:raise ValueError('same 632 support')
    if dual.get('saved_support_sha256')!=digest(support['indices']):raise ValueError('saved support hash')
    if result['program']!=protocol['program'] or result['scales']!=protocol['scales']:raise ValueError('same program/scales')
    built=[B.build(protocol['program'],X) for X in protocol['scales']];aux=B.auxiliary();instances=[b['instance'] for b in built]+[aux['instance']];blocks=[b['gram_blocks'] for b in built]+[aux['gram_blocks']]
    columns,lhs,domain,nn,rr=independent_columns(instances,blocks,B.gram_specs());eq,target=dual_equations(columns,lhs,domain,nn,rr)
    report=dual['diagnostics']['row_compression']
    expected_build=(len(columns)+1)*(2*len(domain)+len(nn))
    if report.get('dual_build_work_proxy')!=expected_build:raise ValueError('exact dual build work proxy')
    variables=2*len(domain)+len(nn)
    expected_dual_reserve=3*sum(map(len,columns))+2*len(lhs)+variables+2*len(domain)+len(support['indices'])+1
    if report.get('dual_verification_work_reserve')!=expected_dual_reserve:raise ValueError('exact dual verification reserve')
    limits=protocol['limits']
    if limits.get('max_preprocessing_operations')!=200000000 or limits.get('max_preprocessing_cells')!=4000000:raise ValueError('unchanged preprocessing caps')
    if report['preprocessing_work']>limits['max_preprocessing_operations'] or report.get('preprocessing_actual_work',report['preprocessing_work'])>limits['max_preprocessing_operations'] or report['preprocessing_cells']>limits['max_preprocessing_cells']:raise ValueError('preprocessing caps replay')
    compression=verify_producer_compression(eq,target,support['indices'],report)
    if dual.get('status')!='exact_separator':raise ValueError('exact separator admission required')
    solution=verify_original_solution(eq,target,support['indices'],dual['exact_support_weights'])
    if any(F(q)<0 for q in dual['exact_support_weights']):raise ValueError('nonnegative support variables')
    full_variables=[F(0)]*variables
    for i,q in zip(support['indices'],dual['exact_support_weights']):full_variables[i]=F(q)
    reconstructed_y=[full_variables[j]-full_variables[j+len(domain)] for j in range(len(domain))]
    if reconstructed_y!=list(map(F,dual['weights'])):raise ValueError('saved support moments binding')
    full=G.verify_dual(instances,blocks,B.gram_specs(),dual)
    return dict(all_passed=True,compression=compression,original_solution=solution,full_Gram_dual_check=full,input_sha256={name:sha(d/name) for name in ['protocol.json','source_seal.json','input.json','support.json','seal.json','receipt.json','result.json']},same_support_verified=True,unchanged_450m_gate_verified=True,global_bound_proved=False,RH_proved=False)

def audit(directory):
    """Write an exclusive standalone independent admission artifact."""
    from pathlib import Path
    d=Path(directory).resolve();target=d/'independent_verification.json'
    if target.exists():raise FileExistsError('exclusive independent verification artifact')
    result=verify_arithmetic_archive(d)
    with target.open('x') as stream:json.dump(result,stream,sort_keys=True,indent=2);stream.write('\n')
    return result

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('directory');args=parser.parse_args()
    result=audit(args.directory)
    print(json.dumps(dict(all_passed=result['all_passed'],same_support_verified=result['same_support_verified'],unchanged_450m_gate_verified=result['unchanged_450m_gate_verified']),sort_keys=True))
