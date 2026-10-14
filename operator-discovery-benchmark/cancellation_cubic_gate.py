"""Explicit coefficient-constraint row for the proved mu cubic necessary gate.
This auxiliary row encodes gamma=0; it is not an arithmetic observation or a
same-domain interpretation of the ordinary descriptor groups.
"""
from fractions import Fraction as F
import hashlib,json

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def _dictionary(dictionary):
 if type(dictionary)is not dict or set(dictionary)!={'square','relation'} or any(type(dictionary[k])is not list for k in dictionary):raise ValueError('dictionary schema')
 for ds in dictionary.values():
  ids=set()
  for d in ds:
   if type(d)is not dict or type(d.get('id'))is not str:raise ValueError('descriptor ID required')
   if d['id']!=digest({k:v for k,v in d.items() if k!='id'}) or d['id'] in ids:raise ValueError('canonical unique descriptor IDs')
   ids.add(d['id'])
 return dictionary

def coefficients(dictionary):
 ds=_dictionary(dictionary)['relation'];out=[];found=[]
 for d in ds:
  if d.get('family')=='norm' and d.get('weight')=='child_rowmass' and d.get('multiplier')=='one':
   r=d.get('region')
   if r not in ('all','head','tail'):raise ValueError('unknown rowmass region')
   found.append(r);out.append(dict(all=F(-56,3),head=F(-12),tail=F(-20,3))[r])
  else:out.append(F(0))
 if sorted(found)!=['all','head','tail']:raise ValueError('exact three cubic descriptor positions required')
 return out

def gamma(weights,dictionary):
 c=coefficients(dictionary)
 if type(weights)is dict:
  if set(weights)!={'square_weights','relation_weights'}:raise ValueError('weights schema')
  if type(weights['square_weights'])is not list or len(weights['square_weights'])!=len(dictionary['square']):raise ValueError('square dimensions')
  weights=weights['relation_weights']
 if type(weights)is not list or len(weights)!=len(c):raise ValueError('relation dimensions')
 qs=[]
 for w in weights:
  if type(w)not in (str,int,F):raise ValueError('exact weights only')
  qs.append(F(w))
 return sum((a*b for a,b in zip(c,qs)),F(0))

def build_constraint(dictionary):
 c=coefficients(dictionary)
 groups=[([dict(spec=dict(kind='unit'),multiplier=[dict(m=[],c=str(q))])] if q else []) for q in c]
 instance=dict(target='mu',horizon=1,lhs=[],square_groups=[[] for _ in dictionary['square']],relation_groups=groups)
 return dict(instance=instance,square_ids=[d['id'] for d in dictionary['square']],relation_ids=[d['id'] for d in dictionary['relation']],dictionary_sha256=digest(dictionary),gamma_coefficients=list(map(str,c)),encoding='explicit auxiliary shared-weight constraint gamma=0; not arithmetic data or same-group semantic observation',scope='necessary gate only for fixed mu templates at q>1 under proved scalar-asymptotic assumptions',requires_target='mu',requires_q_greater_than=1,global_bound_proved=False,RH_proved=False)
