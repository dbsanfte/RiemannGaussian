"""Guarded source-layout counter adapter; no factoring-rate/execution certificate."""
from source_layout import construct_layout,frozen_counter,ResourceLimit
from source_parameters import scope_statistics,scheduled_guard,check_stats

def count(n,factors,*,parameters=None,max_dimension=None):
    factors=tuple(factors);scopes=tuple(tuple(f.scope) for f in factors)
    st=scope_statistics(n,scopes)
    if parameters is None:p,guard=scheduled_guard(n,st['M'],st['B'],st['w'])
    else:p=parameters;guard=check_stats(n,st['M'],st['B'],st['w'],p)
    if not st['covered']:guard=dict(accepted=False,reasons=['uncovered original variable'])
    if not guard['accepted']:
        result=frozen_counter().direct_count(n,factors)
        return dict(method='explicit_invalid_guard_exhaustive_fallback',guard=guard,result=result.as_dict())
    try:layout=construct_layout(n,scopes,p,max_dimension=max_dimension)
    except ResourceLimit as exc:
        return dict(method='explicit_resource_limit_no_count',reason=str(exc),guard=guard)
    result=frozen_counter().count(n,factors,layout,require_quantitative=True)
    return dict(method='pinned_source_layout_counter',guard=guard,setup=layout.work.output(),result=result.as_dict())
