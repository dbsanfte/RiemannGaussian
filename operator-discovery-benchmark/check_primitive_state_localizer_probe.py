"""Independent complete polynomial replay of signed arithmetic localizers."""
from fractions import Fraction as F
import check_grouped_arithmetic as G
import check_cancellation_shared_gram as I

FLAGS=dict(global_bound_proved=False,RH_proved=False,larger_cone_feasibility_proved=False)


def verify(instances,descriptors,dual,result):
    if any(result.get(k)is not False for k in FLAGS) or result.get('no_new_floating_search')is not True:
        raise ValueError('finite supplied-witness diagnostic only')
    if result['source_hashes']!=list(map(I.digest,instances)) or result['descriptor_sha256']!=I.digest(descriptors) or result['input_dual_sha256']!=I.digest(dual):
        raise ValueError('complete sources, descriptors and parent witness binding')
    domain=[(r['instance'],tuple(r['m'])) for r in dual['monomials']]
    if domain!=sorted(set(domain)) or len(domain)!=len(dual['weights']):raise ValueError('complete unique supplied domain')
    y=dict(zip(domain,map(I.rational,dual['weights'])))
    columns=[{} for _ in descriptors]
    for k,inst in enumerate(instances):
        if inst['target']!='mu' or inst['lhs'] or inst['square_groups'] or len(inst['relation_groups'])!=len(descriptors):
            raise ValueError('complete relation-only arithmetic diagnostic')
        lhs,squares,relations=G.columns(inst)
        if lhs or squares:raise ValueError('no extra target or square')
        for dest,p in zip(columns,relations):dest.update({(k,m):q for m,q in p.items() if q})
    missing=sorted({m for p in columns for m in p if m not in y})
    if result['missing_coordinates']!=[dict(instance=k,m=list(m)) for k,m in missing]:
        raise ValueError('complete unsupported coordinates after cancellation')
    lookup={m:i for i,m in enumerate(missing)}
    if len(result['rows'])!=len(descriptors):raise ValueError('every declared diagnostic column retained')
    counts=dict(violated_relation=0,annihilated_relation=0,unknown_missing_coordinates=0)
    for j,(column,desc,row) in enumerate(zip(columns,descriptors,result['rows'])):
        encoded=[dict(instance=k,m=list(m),c=str(q)) for (k,m),q in sorted(column.items())]
        absent=sorted(lookup[m] for m in column if m not in y)
        expected=dict(index=j,descriptor_id=desc['id'],complete_column_sha256=I.digest(encoded),terms=len(column),missing_indices=absent)
        if absent:expected['status']='unknown_missing_coordinates'
        else:
            value=sum((c*y[m] for m,c in column.items()),F(0))
            expected.update(status='violated_relation' if value else 'annihilated_relation',pairing=str(value))
        if row!=expected:raise ValueError('independent complete signed column pairing '+str(j))
        counts[expected['status']]+=1
    status=('witness_invalid_for_localizer_cone' if counts['violated_relation'] else
            'unknown_missing_coordinates' if counts['unknown_missing_coordinates'] else 'witness_extends_to_localizer_cone')
    if result['counts']!=counts or result['status']!=status:raise ValueError('honest complete diagnostic decision')
    return dict(verified=True,status=status,counts=counts,columns_rebuilt=len(columns),
                missing_coordinates=len(missing),producer_operation_count_independently_verified=False,**FLAGS)
