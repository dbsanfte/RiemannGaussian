import copy
from fractions import Fraction as Q
import unittest

import mobius_rough_transport_077 as P
import check_mobius_rough_transport_077 as C
import check_mobius_residual_fold_077 as F


def factors(n):
    values=[];p=2
    while p*p<=n:
        while n%p==0:values.append(p);n//=p
        p+=1
    if n>1:values.append(n)
    return values


def value(intervals,n,tokens):
    return sum((sum((Q(a)*tokens[t] for t,a in row['weight'].items()),Q(0)) for row in intervals if row['left']<n<=row['right']),Q(0))


def rough_sum(intervals,y,excluded,tokens):
    answer=Q(0)
    for n in range(1,max((r['right'] for r in intervals),default=0)+1):
        fs=factors(n)
        if len(set(fs))!=len(fs) or any(p<=y or p in excluded for p in fs):continue
        answer+=(-1)**len(fs)*value(intervals,n,tokens)
    return answer


class Rough(unittest.TestCase):
    def setUp(self):
        self.intervals=[dict(left=0,right=19,weight={'x':'2/3'}),dict(left=22,right=80,weight={'x':'-1/7','y':'2'})]
        self.tokens={'x':Q(3,5),'y':Q(-1,4)}

    def test_threshold_transport_preserves_complete_signed_rough_sum(self):
        result=P.transport(self.intervals,1,7,[3,11])
        self.assertEqual(C.verify_transport(self.intervals,result)['status'],'VERIFIED_IDENTITY')
        lhs=rough_sum(self.intervals,1,[3,11],self.tokens)-rough_sum(self.intervals,7,[3,11],self.tokens)
        rhs=-sum((rough_sum(row['intervals'],row['prime'],[3,11],self.tokens) for row in result['children']),Q(0))
        self.assertEqual(lhs,rhs)
        self.assertEqual([x['prime'] for x in result['children']],[2,5,7])
        bad=copy.deepcopy(result);bad['children'].pop()
        self.assertEqual(C.verify_transport(self.intervals,bad)['status'],'INVALID')

    def test_terminal_keeps_signed_prime_semiprime_interaction(self):
        result=P.factor_terminal(self.intervals,5,2,[11])
        checked=C.verify_terminal(self.intervals,result)
        self.assertEqual(checked['status'],'VERIFIED_IDENTITY',checked)
        signed=sum((Q(a)*self.tokens[t] for t,a in result['signed_polynomial'].items()),Q(0))
        self.assertEqual(signed,rough_sum(self.intervals,5,[11],self.tokens))
        self.assertEqual(result['layer_counts'][0],1)
        # The only potential distinct rough semiprime<=80 is7*11, excluded.
        self.assertEqual(result['layer_counts'][2],0)
        normal=P.factor_terminal(self.intervals,5,2)
        self.assertEqual(normal['layer_counts'][2],1)
        bad=copy.deepcopy(normal);bad['layer_counts'][2]+=1
        self.assertEqual(C.verify_terminal(self.intervals,bad)['status'],'INVALID')

    def test_transport_and_terminal_recombine_with_negative_child_weights(self):
        transport=P.transport(self.intervals,1,5,[])
        terminal=P.factor_terminal(self.intervals,5,2,[])
        tail=sum((Q(a)*self.tokens[t] for t,a in terminal['signed_polynomial'].items()),Q(0))
        coupled=tail-sum((rough_sum(c['intervals'],c['prime'],[],self.tokens) for c in transport['children']),Q(0))
        self.assertEqual(coupled,rough_sum(self.intervals,1,[],self.tokens))
        self.assertEqual(C.verify_transport(self.intervals,transport)['status'],'VERIFIED_IDENTITY')
        self.assertEqual(C.verify_terminal(self.intervals,terminal)['status'],'VERIFIED_IDENTITY')

    def test_general_degree_and_strict_prime_order(self):
        intervals=[dict(left=0,right=16,weight={'1':'1'})]
        result=P.factor_terminal(intervals,2,3)
        self.assertEqual(C.verify_terminal(intervals,result)['status'],'VERIFIED_IDENTITY')
        self.assertEqual(result['layer_counts'],[1,5,1,0])
        self.assertEqual(result['signed_polynomial'],{'1':'-3'})
        self.assertIsNone(P.terminal_degree(100,1))
        with self.assertRaises(ValueError):P.factor_terminal(intervals,2,2)

    def test_arbitrary_rational_cutoffs_and_work_gate(self):
        for gamma in ['1/2','1/3','17/53','2/7','1001/1000']:
            y=P.rational_cutoff(257,gamma);g=Q(gamma);target=257**g.numerator
            self.assertLess((y-1)**g.denominator,target)
            self.assertGreaterEqual(y**g.denominator,target)
        with self.assertRaises(ValueError):P.rational_cutoff(257,'1/100001')

    def test_parent_tokens_do_not_change_under_dilation(self):
        intervals=[dict(left=0,right=90,weight={'count:13^(-17/31)':'2/3'})]
        result=P.transport(intervals,1,5)
        self.assertTrue(all(set(r['weight'])=={'count:13^(-17/31)'} for child in result['children'] for r in child['intervals']))
        self.assertEqual(C.verify_transport(intervals,result)['status'],'VERIFIED_IDENTITY')

    def test_method_obstruction_routes_to_signed_search_without_claiming_proof(self):
        cert=P.P.uniform_obstruction(P.P.KERNEL,2,[2,3,5,7],'1')
        checked=F.verify_bulk_obstruction(P.P.KERNEL,2,[2,3,5,7],cert)
        route=P.route_obstruction(checked)
        self.assertEqual(route['fixed_finite_prime_l1_branch'],'REJECTED_AS_UNIFORM_BOUND_METHOD')
        self.assertIn('RETAINED',route['signed_candidate'])
        self.assertFalse(route['uniform_residual_bound_proved'])
        bad=dict(checked,arithmetic_residual_refuted=True)
        with self.assertRaises(ValueError):P.route_obstruction(bad)

    def test_unit_empty_domain_and_product_resource_gate(self):
        empty=P.factor_terminal([],1,0)
        self.assertEqual(empty['layer_counts'],[0]);self.assertEqual(empty['signed_polynomial'],{})
        self.assertEqual(C.verify_terminal([],empty)['status'],'VERIFIED_IDENTITY')
        unit=P.factor_terminal([dict(left=0,right=1,weight={'x':'-2'})],1,0)
        self.assertEqual(unit['signed_polynomial'],{'x':'-2'})
        self.assertEqual(C.verify_terminal([dict(left=0,right=1,weight={'x':'-2'})],unit)['status'],'VERIFIED_IDENTITY')
        with self.assertRaises(ValueError):P.factor_terminal(self.intervals,5,2,max_products=2)


if __name__=='__main__':unittest.main()
