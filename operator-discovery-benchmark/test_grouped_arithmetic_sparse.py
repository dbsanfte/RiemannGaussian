import time
import unittest
import grouped_arithmetic_sparse as S
import grouped_arithmetic_synthesis as OLD
import check_grouped_arithmetic as I

def fixture(target='mu',slack=True):
    h=1 if target=='mu' else 4
    from fractions import Fraction as F
    value=str(F(h)+ (F(1,3)if slack else 0))
    i=dict(target=target,horizon=2,lhs=[dict(m=[],c=value)],square_groups=[[dict(weight='2/3',poly=[dict(m=[2],c='1')])],[]],relation_groups=[[dict(spec=dict(kind='norm',n=2,factors=[[2,1]]),multiplier=[dict(m=[],c='2')])],[]])
    w=dict(square_weights=['3/2','0'],relation_weights=['-1/2','0'])
    return i,w

class SparseProducerTests(unittest.TestCase):
    def test_full_equivalence_mu_c_rationals_slacks(self):
        for target in ['mu','c']:
            for slack in [True,False]:
                i,w=fixture(target,slack)
                new=S.instantiate_details(i,w,allow_constant_slack=slack)
                old=OLD.instantiate_certificate(i,w,allow_constant_slack=slack)
                self.assertEqual(new['certificate'],old)
                self.assertTrue(I.verify_certificate(new['certificate'])['verified'])
                self.assertEqual(new['constant_slack'],'1/3'if slack else'0')
                self.assertEqual(new['diagnostics']['expanded_products'],2)
    def test_inactive_invalid_inputs_rejected(self):
        for mutation in ['poly','premise','own_weight','group','noncanonical']:
            i,w=fixture()
            i['square_groups'][1]=[dict(weight='1',poly=[dict(m=[1],c='1')])]
            i['relation_groups'][1]=[dict(spec=dict(kind='unit'),multiplier=[])]
            if mutation=='poly':i['square_groups'][1][0]['poly']=[dict(m=[3],c='1')]
            if mutation=='premise':i['relation_groups'][1][0]['spec']=dict(kind='norm',n=2,factors=[[3,1]])
            if mutation=='own_weight':i['square_groups'][1][0]['weight']='-1'
            if mutation=='group':i['relation_groups'][1]={}
            if mutation=='noncanonical':i['square_groups'][1][0]['poly']=[dict(m=[1],c='01')]
            with self.subTest(mutation=mutation),self.assertRaises((ValueError,OverflowError)):S.instantiate_certificate(i,w,allow_constant_slack=True)
    def test_bounds(self):
        for limits in [dict(max_degree=1),dict(max_horizon=1),dict(max_columns=1),dict(max_operations=1),dict(max_coefficient_bits=1),dict(deadline=time.monotonic()-1),dict(time_limit=float('nan')),dict(time_limit=True),dict(max_monomials=0)]:
            i,w=fixture()
            with self.subTest(limits=limits),self.assertRaises((ValueError,OverflowError)):S.instantiate_certificate(i,w,allow_constant_slack=True,**limits)
    def test_false_identity_and_negative_weights(self):
        for mutation in ['lhs','negative','negative_slack','bool','exponent']:
            i,w=fixture()
            if mutation=='lhs':i['lhs']=[dict(m=[1],c='1')]
            if mutation=='negative':w['square_weights'][0]='-1'
            if mutation=='negative_slack':i['lhs']=[dict(m=[],c='1/2')]
            if mutation=='bool':w['relation_weights'][0]=True
            if mutation=='exponent':w['relation_weights'][0]='1e10000000'
            with self.subTest(mutation=mutation),self.assertRaises((ValueError,OverflowError)):S.instantiate_certificate(i,w,allow_constant_slack=True)
    def test_empty_source_constant_slack(self):
        i=dict(target='c',horizon=1,lhs=[dict(m=[],c='2/7')],square_groups=[],relation_groups=[]);w=dict(square_weights=[],relation_weights=[])
        self.assertEqual(S.instantiate_certificate(i,w,allow_constant_slack=True),OLD.instantiate_certificate(i,w,allow_constant_slack=True))

if __name__=='__main__':unittest.main()
