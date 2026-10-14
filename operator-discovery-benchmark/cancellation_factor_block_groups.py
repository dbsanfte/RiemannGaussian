"""Explicit factor-block adapters for shared finite cones; no response selection."""
import hashlib,json
import arithmetic_cycle_language as L
from check_cancellation_factor_blocks import check_block
PARTS=('full','inside','complement')
COMPONENTS=('bilinear','coprime_projection','noncoprime_residual')

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def descriptors(square_choices,relation_parts):
 if type(square_choices)is not list or type(relation_parts)is not list:raise ValueError('explicit descriptor lists')
 sq=[];rel=[]
 for choice in square_choices:
  if type(choice)is not dict or set(choice)!={'part','component'} or choice['part']not in PARTS or choice['component']not in COMPONENTS:raise ValueError('square choice schema')
  d=dict(family='factor_block_square',**choice);sq.append(dict(d,id=digest(d)))
 for part in relation_parts:
  if type(part)is not str or part not in PARTS:raise ValueError('relation part')
  d=dict(family='factor_block_rewrite',part=part);rel.append(dict(d,id=digest(d)))
 if len({d['id'] for d in sq})!=len(sq) or len({d['id'] for d in rel})!=len(rel):raise ValueError('duplicate descriptors')
 return dict(square=sq,relation=rel)

def groups(block,descriptor_set):
 check_block(block)
 if type(descriptor_set)is not dict or set(descriptor_set)!={'square','relation'}:raise ValueError('descriptor set')
 expected=descriptors([dict(part=d['part'],component=d['component']) for d in descriptor_set['square']],[d['part'] for d in descriptor_set['relation']])
 if descriptor_set!=expected:raise ValueError('canonical descriptor binding')
 sq=[];rel=[]
 for d in descriptor_set['square']:
  p=block['parts'][d['part']][d['component']]
  if () in L.load_poly(p):raise ValueError('factor atom has formalconstant')
  sq.append([dict(weight='1',poly=p)] if p else [])
 for d in descriptor_set['relation']:
  group=block['parts'][d['part']]['relations']
  for term in group:
   rho=L.relation(term['spec'],block['target'],block['horizon']);m=L.load_poly(term['multiplier'])
   if rho.get((),0)*m.get((),0):raise ValueError('added relation scalar nonzero')
  rel.append(group)
 return dict(square_groups=sq,relation_groups=rel,square_ids=[d['id']for d in descriptor_set['square']],relation_ids=[d['id']for d in descriptor_set['relation']],all_added_formal_scalars_zero=True,block_spec_sha256=block['spec_sha256'],descriptor_sha256=digest(descriptor_set),global_bound_proved=False,RH_proved=False)

def append_groups(instance,block,descriptor_set,*,auxiliary=False):
 if type(auxiliary)is not bool or type(instance)is not dict or set(instance)!={'target','horizon','lhs','square_groups','relation_groups'}:raise ValueError('instance/auxiliary schema')
 if auxiliary:
  if block is not None or instance['target']!='mu' or instance['horizon']!=1 or instance['lhs']!=[] or any(instance['square_groups']):raise ValueError('explicit gamma auxiliary required')
  # Canonical choices are validated without requiring any arithmetic observation.
  expected=descriptors([dict(part=d['part'],component=d['component'])for d in descriptor_set['square']],[d['part']for d in descriptor_set['relation']])
  if expected!=descriptor_set:raise ValueError('auxiliary descriptor binding')
  sq=[[]for d in descriptor_set['square']];rel=[[]for d in descriptor_set['relation']]
 else:
  if block['target']!=instance['target'] or block['horizon']!=instance['horizon']:raise ValueError('block target/source binding')
  built=groups(block,descriptor_set);sq=built['square_groups'];rel=built['relation_groups']
 return dict(instance=dict(target=instance['target'],horizon=instance['horizon'],lhs=instance['lhs'],square_groups=instance['square_groups']+sq,relation_groups=instance['relation_groups']+rel),square_ids=[d['id']for d in descriptor_set['square']],relation_ids=[d['id']for d in descriptor_set['relation']],added_gamma_coefficients=['0']*len(rel),all_added_formal_scalars_zero=True,descriptor_sha256=digest(descriptor_set),auxiliary=auxiliary,global_bound_proved=False,RH_proved=False)

def append_to_instances(instances,blocks,descriptor_set):
 """blocks is parallel: None marks explicit auxiliary rows. All ordinary block
 programs must be identical; own-scale cutoffs are evaluated by that program.
 """
 if type(instances)is not list or type(blocks)is not list or len(instances)!=len(blocks) or not instances:raise ValueError('parallel complete instances')
 specs={b['spec_sha256']for b in blocks if b is not None}
 if len(specs)!=1:raise ValueError('one fixed factor-block program across scales')
 multipliers={digest(b['multiplier'])for b in blocks if b is not None}
 if len(multipliers)!=1:raise ValueError('one fixed canonical multiplier across scales')
 program=dict(spec_sha256=next(iter(specs)),multiplier_sha256=next(iter(multipliers)))
 semantic=digest(dict(program=program,descriptors=descriptor_set))
 out=[append_groups(i,b,descriptor_set,auxiliary=b is None)['instance']for i,b in zip(instances,blocks)]
 return dict(instances=out,descriptor_sha256=digest(descriptor_set),fixed_block_spec_sha256=next(iter(specs)),fixed_multiplier_sha256=next(iter(multipliers)),semantic_binding_sha256=semantic,namespaced_square_ids=[digest(dict(semantic_binding=semantic,descriptor_id=d['id']))for d in descriptor_set['square']],namespaced_relation_ids=[digest(dict(semantic_binding=semantic,descriptor_id=d['id']))for d in descriptor_set['relation']],added_gamma_coefficients=['0']*len(descriptor_set['relation']),shared_descriptor_order_verified=True,all_added_formal_scalars_zero=True,global_bound_proved=False,RH_proved=False)
