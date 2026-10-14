"""New finite checker integration and adversarial certificate mutations."""
import copy
import unittest
import mobius_density_coverage_081 as Producer
import check_mobius_density_coverage_081 as Checker
from test_mobius_density_packet_081 import program

class IndependentCoverageTests(unittest.TestCase):
    def test_independent_small_geometry(self):
        for u in (1,31,127,181):
            p=program(eta='1/3');cert=Producer.coverage(p,u)
            got=Checker.verify_coverage(p,cert)
            self.assertEqual(got['status'],'VERIFIED_FINITE_DENSITY_COVERAGE',got)
            self.assertFalse(got['uniform_unlinked_bound_proved'])
    def test_prime_block_and_mutations(self):
        p=program(kernel=[dict(divisor=4,weight='-1'),dict(divisor=5,weight='1'),dict(divisor=8,weight='1'),dict(divisor=10,weight='-1')])
        cert=Producer.coverage(p,1103)
        self.assertEqual(Checker.verify_coverage(p,cert)['status'],'VERIFIED_FINITE_DENSITY_COVERAGE')
        changes=[('weighted_label_count','999'),('removed_absolute_coefficient_mass','999'),('retained_nonzero_physical_pairs',True),('uniform_unlinked_bound_proved',True)]
        for key,value in changes:
            changed=copy.deepcopy(cert);changed[key]=value
            self.assertEqual(Checker.verify_coverage(p,changed)['status'],'INVALID')
        for key in ('squarefree','primes'):
            changed=copy.deepcopy(cert);changed['bands'][0][key]+=1
            self.assertEqual(Checker.verify_coverage(p,changed)['status'],'INVALID')
        changed=copy.deepcopy(cert);changed['untouched_prime_block']['prime_count']+=1
        self.assertEqual(Checker.verify_coverage(p,changed)['status'],'INVALID')
    def test_resource_gate_precedes_source(self):
        p=program(eta='1');cert={'u':1000000}
        got=Checker.verify_coverage(p,cert)
        self.assertEqual(got['status'],'INVALID');self.assertTrue(got['resource_limit'])

if __name__=='__main__':unittest.main()
