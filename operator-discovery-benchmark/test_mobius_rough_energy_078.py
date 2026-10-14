import copy
from fractions import Fraction as Q
import unittest

import mobius_rough_energy_078 as P
import check_mobius_rough_energy_078 as C


def factors(n):
    result=[]
    p=2
    while p*p<=n:
        while n%p==0:
            result.append(p)
            n//=p
        p+=1
    if n>1:result.append(n)
    return result


def synthetic(u,R,A):
    return dict(u=u,features=[{'1':str(A)} if A else {},{'1':str(R-A)} if R!=A else {}]+[{} for _ in range(8)],token_intervals={'1':['1','1']})


class RoughEnergy(unittest.TestCase):
    def test_complete_factor_partition_and_shared_signed_tokens(self):
        intervals=[dict(left=0,right=30,weight={'x':'2/3'}),dict(left=34,right=300,weight={'x':'-1/7','1':'2'})]
        source=P.Arithmetic(350)
        for gamma in ['1/7','2/9','17/53','2/3','53/17']:
            features=source.features(intervals,[2,7],gamma)
            admitted=C.verify_features(intervals,[2,7],gamma,features)
            self.assertEqual(admitted['status'],'VERIFIED_FEATURES',admitted)
            expected={}
            for n in range(1,301):
                fs=factors(n)
                if len(set(fs))!=len(fs) or any(p in [2,7] for p in fs):continue
                for interval in intervals:
                    if interval['left']<n<=interval['right']:
                        for t,a in interval['weight'].items():expected[t]=expected.get(t,Q(0))+(-1)**len(fs)*Q(a)
            self.assertEqual(P.sum_features(features),{t:str(a) for t,a in expected.items() if a})

    def test_unit_and_empty_at_arbitrary_exponents(self):
        source=P.Arithmetic(80)
        intervals=[dict(left=0,right=1,weight={'token':'-3/2'})]
        features=source.features(intervals,[],'1001/1000')
        self.assertEqual(features,[{'token':'-3/2'}]+[{} for _ in range(9)])
        self.assertEqual(source.features([],[],'2'),[{} for _ in range(10)])
        intervals=[dict(left=0,right=80,weight={'1':'1'})]
        self.assertEqual(source.features(intervals,[],'2')[0],{'1':'1'})
        with self.assertRaises(ValueError):source.features(intervals,[],'0')

    def test_cutoff_and_eta_grammars_are_budgeted_not_root_whitelists(self):
        self.assertIn('2/9',P.rational_grid('1/7','2/3',9))
        self.assertIn('5/13',P.rational_grid('1/7','2/3',13))
        lo,hi=P.positive_power_bounds(17,'19/7')
        self.assertLessEqual(lo**7,17**19)
        self.assertGreaterEqual(hi**7,17**19)
        self.assertTrue(all(len(set(a))>1 for a in P.ray_dictionary()))

    def test_detector_recovers_an_auxiliary_that_closes_a_known_drift(self):
        # E=(R²+(1/2)A²)/u is identically2 on this synthetic family.
        # It is discovered by the LP, rather than handed to the verifier.
        rows={u:synthetic(u,R,A) for u,R,A in [(4,0,4),(8,4,0),(16,0,8),(32,8,0)]}
        atom=dict(a=['1']+['0']*9,eta='0')
        result=P.search_energy(rows,[8,16,32],[4],'1','1/2',[atom])
        self.assertEqual(result['status'],'FLOATING_PROPOSAL_ONLY')
        program,score=P.calibrate(result['program'],rows,[8,16,32],[4])
        self.assertTrue(program['rays'])
        self.assertLess(Q(score['discovery_score']),Q(str(result['baseline_score'])))
        self.assertEqual(Q(program['rays'][0]['lambda']),Q(1,2))
        heldout=synthetic(64,0,16)
        accepted=C.verify_drift(program,heldout,rows[32],precision=24)
        self.assertEqual(accepted['status'],'CERTIFIED_FINITE',accepted)
        self.assertFalse(accepted['uniform_drift_proved'])
        bad=synthetic(64,100,0)
        self.assertEqual(C.verify_drift(program,bad,rows[32])['status'],'REFUTED_FINITE')

    def test_exact_energy_keeps_cancelling_shared_tokens(self):
        row=dict(u=64,features=[{'x':'2'},{'x':'-2'}]+[{} for _ in range(8)],token_intervals={'x':['1','2']})
        program=dict(schema='rough-energy-program-v1',q='1',tau='1',rays=[],innovation_C='0')
        self.assertEqual(P.energy_bounds(program,row),(Q(0),Q(0)))
        admission=C.verify_energy(program,row,precision=24)
        self.assertEqual(admission['normalized_upper'],'0')

    def test_missing_half_and_resource_limits_are_not_counterexamples(self):
        rows={8:synthetic(8,4,0)}
        with self.assertRaises(ValueError):P.search_energy(rows,[8],[8],'1','1/2')
        with self.assertRaises(ValueError):P.search_energy(rows,[8,8],[8],'1','1/2')
        with self.assertRaises(ValueError):P.Arithmetic(4000001)


if __name__=='__main__':unittest.main()
