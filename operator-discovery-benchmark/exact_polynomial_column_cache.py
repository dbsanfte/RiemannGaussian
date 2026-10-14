"""Reusable exact structural-column preparation, independent of target scalar.
Migration helper only: frozen callers are unchanged. All group inputs and resource
limits are hash-bound; lhs is validated on EVERY call. Cache hits change actual
work, not mathematical columns. Returned dictionaries cannot mutate the cache.
"""
import json,hashlib,time
from collections import OrderedDict
import grouped_arithmetic_synthesis as G
DEFAULTS=dict(max_columns=1024,max_monomials=30000,max_operations=200000000,max_coefficient_bits=4096,max_horizon=4096,max_degree=12)
class ColumnCache:
 def __init__(self,*,max_entries=4,max_cached_coefficients=1000000):
  if any(type(v)is not int or v<1 for v in (max_entries,max_cached_coefficients)):raise ValueError('cache limits')
  self.max_entries=max_entries;self.max_cached_coefficients=max_cached_coefficients;self._cache=OrderedDict();self.hits=0;self.misses=0
 def clear(self):self._cache.clear()
 def prepare(self,instances,*,deadline=None,**limits):
  start=time.monotonic();deadline=start+90 if deadline is None else deadline
  caps=dict(DEFAULTS);caps.update(limits)
  if set(caps)!=set(DEFAULTS):raise ValueError('known resource caps only')
  if type(instances)is not list or not instances:raise ValueError('nonempty instances')
  structure=[];targets=[]
  for instance in instances:
   if type(instance)is not dict or set(instance)!={'target','horizon','lhs','square_groups','relation_groups'}:raise ValueError('instance schema')
   structure.append(dict(instance,lhs=[]))
   if type(instance['square_groups'])is not list or type(instance['relation_groups'])is not list:raise ValueError('group lists')
   targets.append(dict(instance,square_groups=[[]for _ in instance['square_groups']],relation_groups=[[]for _ in instance['relation_groups']]))
  # Exact canonical bytes rather than object identity; caller edits cannot reuse stale columns.
  key=hashlib.sha256(json.dumps(dict(instances=structure,caps=caps),sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
  _,lhs,_,shape=G._limits(targets,**caps,deadline=deadline)
  hit=key in self._cache
  if hit:
   self.hits+=1;columns,cached_shape=self._cache.pop(key);self._cache[key]=(columns,cached_shape)
  else:
   self.misses+=1;columns,_,_,cached_shape=G._limits(structure,**caps,deadline=deadline)
   count=sum(len(c)for c in columns)
   if count<=self.max_cached_coefficients:
    self._cache[key]=([dict(c)for c in columns],cached_shape)
    while len(self._cache)>self.max_entries or sum(sum(len(c)for c in entry[0])for entry in self._cache.values())>self.max_cached_coefficients:self._cache.popitem(last=False)
  if shape!=cached_shape:raise ValueError('column/target shape mismatch')
  monomials=sorted(set(lhs)|{m for p in columns for m in p})
  if len(monomials)>caps['max_monomials']:raise OverflowError('complete stacked monomial cap')
  output=[dict(c)for c in columns]
  if time.monotonic()>deadline:raise TimeoutError('column-cache preparation deadline')
  return dict(columns=output,lhs=lhs,monomials=monomials,shape=shape,metadata=dict(cache_hit=hit,structural_key=key,entries=len(self._cache),elapsed_seconds=time.monotonic()-start,exact_columns=True,all_lhs_revalidated=True,global_bound_proved=False))
