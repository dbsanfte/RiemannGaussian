import unittest,copy
from fractions import Fraction as Q
from unittest.mock import patch
import check_mobius_coupled_remainder_083 as R
import check_mobius_coupled_completion_083 as C
from test_check_mobius_coupled_outer_control_083 import fixture
from test_check_mobius_coupled_completion_083 import mu

def example(gram=False,anchor=True):
    p,o=fixture();p['prime_anchor']=anchor
    if gram:
        p['gram_weights']=['1/4','1/3']
        for term in p['coupled_terms']:term['theta']='5/2'
        o.update(Astar='5/4',prime_gain='5/2',composite_gain='5/2',uniform_bound_coefficient='5/4');o['matched_groups'][0]['theta_total']='5/2'
    return p,o

def cert(data):
    A=data['projected_remainder'];rows=[row[i]+sum(abs(v)for j,v in enumerate(row)if j!=i)for i,row in enumerate(A)]
    return dict(squarefree_count=data['model']['squarefree_count'],price=str(sum(rows,Q(0))),row_prices=list(map(str,rows)))

class Tests(unittest.TestCase):
    def test_literal_raw_identity_negative_gram_and_actual_mu(self):
        for anchor in (False,True):
            for u in (1,4,24,53):
                p,o=example(True,anchor);d=R.build_remainder(p,u,o);model=d['model'];G=model['squarefree_count'];A=C.literal_corrected_matrix(model);ns=model['coordinates'];x=list(map(mu,ns));mask=d['outer_mask']
                gram=[[sum(model['program']['gram_weights'][i]*model['features'][g][i]*model['features'][h][i]for i in range(2))for h in range(G)]for g in range(G)]
                expected=[[A[g][h]*(not(mask[g]and mask[h]))-gram[g][h]for h in range(G)]for g in range(G)]
                self.assertEqual(d['raw_remainder'],expected)
                quad=lambda M:sum(x[g]*M[g][h]*x[h]for g in range(G)for h in range(G))
                delta=quad([[C._entry(model,g,h,C.Meter(),False,False)for h in range(G)]for g in range(G)])
                outer=[[A[g][h]if mask[g]and mask[h]else Q(0)for h in range(G)]for g in range(G)]
                self.assertEqual(delta,quad(outer)+quad(expected))
                out=R.verify_certificate(p,u,o,cert(d));self.assertEqual(out['status'],'VERIFIED_FINITE_COUPLED_REMAINDER_UPPER_BOUND');self.assertLessEqual(quad(expected),Q(out['price']))
    def test_complete_projection_partition_and_no_promotion(self):
        p,o=example(True);d=R.build_remainder(p,53,o);out=R.verify_certificate(p,53,o,cert(d));A=d['projected_remainder']
        self.assertEqual(Q(out['price']),Q(out['signed_trace'])+Q(out['anchor_composite_absolute_price'])+Q(out['composite_composite_absolute_price']))
        self.assertEqual(Q(out['signed_trace']),Q(out['anchor_constant'])+Q(out['composite_signed_trace']))
        self.assertTrue(out['negative_Gram_removed']);self.assertFalse(out['price_subtraction_used']);self.assertFalse(out['uniform_remainder_bound_proved']);self.assertFalse(out['uniform_source_bound_proved']);self.assertFalse(out['RH_proved'])
        self.assertEqual(Q(out['anchor_constant']),A[0][0]);self.assertGreater(Q(out['anchor_composite_absolute_price']),0)
    def test_bound_outer_binding_mutations_and_boundary(self):
        p,o=example(True);d=R.build_remainder(p,24,o);c=cert(d)
        for kind in ('theta','gram','outer'):
            bad=copy.deepcopy(p);bo=copy.deepcopy(o)
            if kind=='theta':bad['coupled_terms'][0]['theta']='2'
            elif kind=='gram':bad['gram_weights'][0]='0'
            else:bo['uniform_bound_coefficient']='1'
            self.assertEqual(R.verify_certificate(bad,24,bo,c)['status'],'INVALID')
        bad=copy.deepcopy(c);bad['row_prices'][0]=str(Q(bad['row_prices'][0])+1);self.assertEqual(R.verify_certificate(p,24,o,bad)['status'],'INVALID')
        # Both strict lower endpoint and inclusive floor upper retained.
        p,o=example();d=R.build_remainder(p,20,o);self.assertEqual(d['outer_mask'],tuple(4<n<=5 for n in d['model']['coordinates']))
    def test_wrong_full_price_and_dropped_negative_gram_rejected(self):
        p,o=example(True);d=R.build_remainder(p,53,o);model=d['model']
        bad=copy.deepcopy(d);bad['projected_remainder']=C.price_matrix(model)
        self.assertEqual(R.verify_certificate(p,53,o,cert(bad))['status'],'INVALID')
        bad=copy.deepcopy(d);bad['projected_remainder']=[row[:]for row in d['projected_remainder']];bad['projected_remainder'][0][0]+=1
        self.assertEqual(R.verify_certificate(p,53,o,cert(bad))['status'],'INVALID')
    def test_huge_horizon_resource_preallocation_and_shapes(self):
        p,o=example();c=dict(squarefree_count=0,price='0',row_prices=[])
        with patch.object(C.D,'squarefree_prefix',side_effect=AssertionError('must gate before sieve')):
            out=R.verify_certificate(p,10**40,o,c);self.assertEqual(out['status'],'INVALID');self.assertTrue(out['resource_limit'])
        d=R.build_remainder(p,24,o);c=cert(d);c['squarefree_count']=True;self.assertEqual(R.verify_certificate(p,24,o,c)['status'],'INVALID')
        c=cert(d);c['row_prices'].pop();self.assertEqual(R.verify_certificate(p,24,o,c)['status'],'INVALID')
        p,o=example();m=C.Meter();m.ops=m.limit
        self.assertEqual(R.verify_certificate(p,24,o,cert(d),m)['status'],'INVALID')
