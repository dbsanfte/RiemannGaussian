"""Soundness boundaries for the reusable pole-order rejection rule."""
import copy
import unittest
from flint import arb
import core_pole_growth_obstruction as P


class PoleGrowthTests(unittest.TestCase):
    def setUp(self):
        self.terms = [dict(coefficient='a', zeta_factors=[['0','-2'],['1/3','1']]),
                      dict(coefficient='b', zeta_factors=[['0','-1'],['2/3','-1']])]
        self.p = dict(target_filter=dict(kind='delay',sign=0,theta='0'), auxiliary=None)
        self.w = dict(schema='certified-core-pole-growth-obstruction-v1',
                      source_pole=dict(order=2,minimum_dyadic_energy_log_degree=2),
                      surviving_filters=[self.p['target_filter'],dict(kind='log_abel',cutoff=64)])

    def test_unique_dominant_pole_and_unknown_cancellation(self):
        r=P.unique_pole(self.terms,1,['1/3','2/3'],{'a':'9/2','b':'-4'})
        self.assertEqual(r['order'],2)
        self.assertEqual(r['minimum_dyadic_energy_log_degree'],2)
        self.assertEqual(P.unique_pole(self.terms,2,['1/3','2/3'],{'a':'9/2','b':'-4'})['order'],4)
        tied=self.terms+[dict(coefficient='b',zeta_factors=[['0','-2']])]
        self.assertIsNone(P.unique_pole(tied,1,['1/3','2/3'],{'a':'9/2','b':'-4'}))
        self.assertIsNone(P.unique_pole(self.terms,1,['1/3','2/3'],{'a':str(arb('0 +/- 1')),'b':'-4'}))

    def test_unpaid_shift_and_fractional_branch_are_not_assumed(self):
        with self.assertRaises(ValueError):
            P.unique_pole(self.terms,1,['2/3'],{'a':'9/2','b':'-4'})
        fractional=copy.deepcopy(self.terms);fractional[0]['zeta_factors'][0][1]='-3/2'
        with self.assertRaises(ValueError):
            P.unique_pole(fractional,1,['1/3','2/3'],{'a':'9/2','b':'-4'})

    def test_log_squared_boundary_and_positive_powers_stay_open(self):
        for rho,k,reject in [('1/2',0,True),('1',0,True),('1/2',1,True),('1',1,False),('1/2',2,False)]:
            r=P.gate(self.p,rho,'0',k,self.w)
            self.assertEqual(r['uniform_shape_disproved'],reject)
            self.assertFalse(r['proved_uniform_critical_bound'])
        self.assertFalse(P.gate(self.p,'1/2','1/6',0,self.w)['uniform_shape_disproved'])

    def test_direct_transformed_degree_and_uncertified_filters(self):
        p=dict(self.p,target_filter=dict(kind='log_abel',cutoff=64))
        self.assertTrue(P.gate(p,'1/2','0',1,self.w)['uniform_shape_disproved'])
        p=dict(self.p,target_filter=dict(kind='frequency_annihilator',frequency='14'))
        self.assertFalse(P.gate(p,'1/2','0',0,self.w)['uniform_shape_disproved'])

    def test_positive_storage_and_finite_evidence_preserved(self):
        aux=dict(coefficients=['1','-1','0','0'],alpha='1/6',theta=None,weight='1/3')
        p=dict(self.p,auxiliary=aux)
        r=dict(rho='1/2',gamma='0',log_power=0,constant='1000000',
               status='finite_survivor_open_uniform_premise',cofinal_candidate=True,
               training={'passed':True})
        out=P.annotate(r,p,self.w)
        self.assertEqual(out['status'],'analytic_countercertificate')
        self.assertEqual(out['prior_status'],r['status']);self.assertEqual(out['training'],r['training'])
        self.assertFalse(out['cofinal_candidate']);self.assertEqual(out['constant'],'1000000')
        with self.assertRaises(ValueError):
            P.gate(dict(p,auxiliary=dict(aux,weight='-1')),'1/2','0',0,self.w)


if __name__=='__main__':unittest.main()
