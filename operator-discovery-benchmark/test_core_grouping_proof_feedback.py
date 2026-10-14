import json
from pathlib import Path
import unittest
from flint import arb,ctx
import core_grouping_proof_feedback as P
import check_core_arithmetic_grouping as LABEL
from prime_bank_candidates import Meter

TOTAL=0
def tearDownModule():print('SYNTHETIC_WORK module=test_core_grouping_proof_feedback operations='+str(TOTAL))


class GroupingProofFeedbackTests(unittest.TestCase):
    def setUp(self):
        ctx.prec=192
        self.source=json.loads(Path('core-signed-work-results/pilot-001/source_program.json').read_text())
        z=(arb(2)/3).zeta();self.Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z)
    def test_complete_semiprime_limits_and_scope(self):
        global TOTAL
        m=Meter(1000000,60)
        for op in ('remove_largest_once','remove_smallest_once','remove_largest_all'):
            p=dict(base=dict(op='strip_small_prime_powers',cutoff=dict(kind='power',value='1/2'),valuation_step=1),post=dict(op=op,value='0'))
            cert=P.semiprime_gate(p,self.source,self.Ru,m)
            self.assertEqual(arb(cert['distinct_prime_coefficient_limit']),9)
            self.assertEqual(arb(cert['repeated_prime_coefficient_limit']),arb(9)/2)
            self.assertTrue(cert['uniform_group_bound_disproved']);self.assertFalse(cert['original_signed_target_disproved'])
            p['base']['valuation_step']=2
            self.assertIsNone(P.semiprime_gate(p,self.source,self.Ru,m))
        TOTAL+=m.operations
    def test_mask_is_actual_zero_class_and_empty_cases_stay_unclaimed(self):
        global TOTAL
        m=Meter(20000000,60)
        for cut,step,mod in [(dict(kind='fixed',value='2'),1,'3'),(dict(kind='power',value='1/6'),2,'6'),(dict(kind='none',value='0'),1,'2')]:
            p=dict(base=dict(op='strip_small_prime_powers',cutoff=cut,valuation_step=step),post=dict(op='residue',value=mod))
            mask=P.residue_mask(p);labels=LABEL.evaluate_labels(p,1024,m)
            for n in range(1,4096):
                belongs=True
                for c in mask['conditions']:
                    q=c['prime'];r=n;e=0
                    while r%q==0:r//=q;e+=1
                    belongs=belongs and (e%2==1 if c['valuations']=='odd' else e>0)
                self.assertEqual(labels[n]==0,belongs);m.charge(30)
        p['base']['cutoff']=dict(kind='power',value='1/6')
        self.assertIsNone(P.residue_mask(p))
        TOTAL+=m.operations
    def test_generated_divisibility_pole_matches_independent_exact_formula(self):
        global TOTAL
        m=Meter(1000000,60)
        p=dict(base=dict(op='strip_small_prime_powers',cutoff=dict(kind='fixed',value='2'),valuation_step=1),post=dict(op='residue',value='3'))
        cert=P.mask_pole_gate(p,self.source,self.Ru,m)
        z=(arb(2)/3).zeta();w=(arb(4)/3).zeta();t=1/arb(3).root(3)
        expected=-arb(9)/2*t*t*(1-t**3)*(2/(z*z)-1/(z*w))/((1-t*t)**2*(1+t*t))
        self.assertTrue(arb(cert['residue']).overlaps(expected));self.assertTrue(expected<0)
        self.assertFalse(cert['original_signed_target_disproved']);self.assertEqual(cert['pole'],'2/3')
        TOTAL+=m.operations+10000

    def test_square_lift_head_support_and_unpaid_crosses(self):
        global TOTAL
        from fractions import Fraction
        m=Meter(1000000,60)
        p=dict(base=dict(op='strip_small_prime_powers',cutoff=dict(kind='power',value='1/3'),valuation_step=2),post=dict(op='root',value='6'))
        c=P.square_lift_head(p,self.Ru,'1/6',m)
        self.assertEqual(c['rational_polylog_degree'],'7')
        self.assertGreater(Fraction(c['rational_polylog_constant']),0)
        self.assertTrue(c['low_low_sector_uniformly_paid'])
        self.assertFalse(c['remainder_independently_bounded']);self.assertFalse(c['whole_signed_bound_proved'])
        # Independent worst-sign coefficient envelope on complete small inputs.
        X=16;J=1;label=LABEL.evaluate_labels(p,X,m)
        for x in (X,2*X,4*X-1):
            def divisors(n):return sum(n%d==0 for d in range(1,n+1))
            actual=sum(divisors(n) for n in range(1,x+1) if label[n]<=J)
            A=2*(J+1)**3*(1+6*arb(J+1).log())
            bound=A*arb(x).sqrt()*(1+arb(x).log())**2
            self.assertTrue(bound>actual);m.charge(x*x)
        p['base']['valuation_step']=1
        self.assertIsNone(P.square_lift_head(p,self.Ru,'1/6',m))
        TOTAL+=m.operations


if __name__=='__main__':unittest.main()
