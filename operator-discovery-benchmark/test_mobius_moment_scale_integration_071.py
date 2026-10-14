"""New producer/checker integration on a non-pilot source."""
from fractions import Fraction as Q
import unittest
import mobius_moment_scale_071 as S
import check_mobius_moment_scale_071 as C

PM=S.Meter(cap=300_000_000_000)
CM=C.Meter()


class MomentIntegrationTests(unittest.TestCase):
    def test_generated_proofs_bind_to_complete_joined_source(self):
        programs=[S.construct_program(s,r,t,PM) for s,r,t in
                  [('1/2','3/4',None),('5/9','256/257','1/257'),('3/7','2/5',None),('2/7','7/8','3/7')]]
        for program in programs:self.assertTrue(C.verify_program(program,CM)['verified'])
        params=dict(primes=[2,3,5],p=3,q=5,alpha='1/5',gamma='5/28',tau='1/2')
        certificate=S.construct_source(37,23,35,params,programs,PM)
        result=C.verify_source(certificate,CM)
        self.assertTrue(result['verified']); self.assertFalse(result['uniform_head_bound_proved'])
        for ep in result['endpoints']:
            for row in ep['rows']:
                for e in row['evaluations']:
                    self.assertEqual(Q(e['actual_coefficient']),Q(e['direct'])+Q(e['separable'])+Q(e['J']))
                    self.assertEqual(Q(e['J']),Q(e['L_u'])+Q(e['L_v'])-Q(e['E']))
                    self.assertEqual(e['actual_coefficient'],row['actual_coefficient'])


if __name__=='__main__':unittest.main()
