"""Tiny algebra only: never builds or evaluates a research candidate."""
import copy
from fractions import Fraction as F
import time
import unittest
import primitive_state_uniform_identity_probe as P
import check_primitive_state_uniform_identity_probe as C

PROGRAM=dict(target='mu',q=6,C='32',claim='critical')
def poly(items):
    return [dict(m=list(m),c=str(c)) for m,c in sorted(items.items()) if c]
def fixture():
    vector=['0']*1957
    plan=P.preflight(vector,PROGRAM,X=1)
    # 32-(u1+u2)^2-(u1+u2+u3)^2+4u1^2.
    lhs=poly({():32,(1,1):2,(2,2):-2,(3,3):-1,(1,2):-4,(1,3):-2,(2,3):-2})
    state=[poly({():1}),poly({(1,):1})]+[[] for _ in range(13)]
    blocks=dict(full_child=[copy.deepcopy(state) for _ in range(2)],full_parent=[copy.deepcopy(state)])
    native=dict(instance=dict(target='mu',horizon=3,square_groups=[[]for _ in range(366)],relation_groups=[[]for _ in range(613)],lhs=lhs),gram_blocks=blocks,storage_blocks=dict(kind='signed_storage_increment',child=blocks['full_child'],parent=blocks['full_parent'],child_multiplier='1',parent_multiplier='-4'),gram_specs=dict(full_child=15,full_parent=15,storage_K=15),gram_program={},primitive_state_spec={})
    return native,vector,plan
class Soundness(unittest.TestCase):
    def test_target_and_original_signed_gram(self):
        n,v,p=fixture();r=C.exact_row(n,p,list(map(F,v)),C.Budget())
        self.assertEqual(r['rhs'],F(-253))
        self.assertEqual(r['row'][1597],0) # constant diagonal cancels
        self.assertEqual(r['row'][1598],12) # two child rows *2*u1
        self.assertEqual(r['row'][1718],6)
        self.assertEqual(r['row'][1838],-12) # child-4parent
        self.assertEqual(r['row'][1592:1597],[F(0)]*5)
    def test_complete_signed_relation_pair(self):
        n,v,p=fixture();n['instance']['relation_groups'][0]=[dict(spec=dict(kind='unit'),multiplier=poly({():1}))]
        r=C.exact_row(n,p,list(map(F,v)),C.Budget())
        self.assertEqual(r['row'][366:368],[F(3),F(-3)])
    def test_scalar_cancellation(self):
        n,v,p=fixture();n['instance']['square_groups'][0]=[dict(weight='7',poly=poly({():5}))]
        r=C.exact_row(n,p,list(map(F,v)),C.Budget());self.assertEqual(r['row'][0],0)
    def test_modular_zero_is_not_polynomial_zero(self):
        e=P.ExactEvaluator(65537,3,P.Budget(deadline=time.monotonic()+5))
        a,b=e.pair(poly({(1,):65537}),[3,5,7]);self.assertNotEqual(a-b,0);self.assertEqual(e.coefficient(str(a-b)),0)
    def test_denominator_not_invertible(self):
        e=P.ExactEvaluator(65537,3,P.Budget(deadline=time.monotonic()+5))
        with self.assertRaises(ValueError):e.pair(poly({(1,):F(1,65537)}),[3,5,7])
    def test_complete_groups_required(self):
        n,v,p=fixture();n['instance']['relation_groups'].pop()
        with self.assertRaises(ValueError):C.exact_row(n,p,list(map(F,v)),C.Budget())
    def test_row_tracks_actual_source_coefficients(self):
        n,v,p=fixture()
        n['instance']['square_groups'][0]=[dict(weight='1',poly=poly({(1,):1}))]
        first=C.exact_row(n,p,list(map(F,v)),C.Budget())
        n['instance']['square_groups'][0]=[dict(weight='1',poly=poly({(1,):2}))]
        second=C.exact_row(n,p,list(map(F,v)),C.Budget())
        self.assertEqual(first['row'][0],F(9))
        self.assertEqual(second['row'][0],F(36))
    def test_actual_mu_unit_would_hide_formal_defect(self):
        e=P.ExactEvaluator(65537,3,P.Budget(deadline=time.monotonic()+5));s=poly({():-1,(1,):1})
        self.assertEqual(e.pair(s,[1,-1,-1])[0],0);a,b=e.pair(s,[3,5,7]);self.assertEqual(a-b,3)
    def test_work_cap_stops_before_evaluation(self):
        n,v,p=fixture()
        with self.assertRaises(OverflowError):C.exact_row(n,p,list(map(F,v)),C.Budget(max_operations=1))
if __name__=='__main__':unittest.main()
