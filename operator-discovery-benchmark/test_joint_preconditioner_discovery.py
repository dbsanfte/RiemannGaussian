import unittest
from fractions import Fraction as Q
from math import comb
import joint_preconditioner_discovery as P


class Meter:
    operations=0
    def charge(self,n=1):type(self).operations+=n
    def live(self,n):self.charge()


def coefficients(factors,x,length):
    out=[Q(1)]+[Q(0)]*(length-1)
    for shift,exponent in factors:
        local=[Q(1)]
        for e in range(1,length):
            local.append(local[-1]*(Q(exponent)+e-1)/e*x**int(6*Q(shift)))
        out=[sum((out[j]*local[e-j] for j in range(e+1)),Q(0)) for e in range(length)]
        Meter.operations+=length*length*3
    return out


class PreconditionerTests(unittest.TestCase):
    def test_recovery_gate_retains_fractional_and_endpoint_cases(self):
        self.assertFalse(P.recovery('1/3','1')['cofinal'])
        self.assertEqual(P.recovery('1/3','1')['energy_power_loss'],'1/3')
        self.assertEqual(P.recovery('1/2','1/2')['kind'],'polylog')
        self.assertTrue(P.recovery('2/3','-1/2')['covers_forward_and_inverse'])
        self.assertEqual(P.recovery('2/3','0')['kind'],'identity')

    def test_generic_factor_compilation_and_constant_term_preservation(self):
        rows=P.generate(Meter())
        self.assertEqual(len(rows),37)
        for row in rows:
            for term,original in zip(row['terms'],P.SOURCE_TERMS):
                for x in (Q(1,3),Q(3,4)):
                    got=coefficients(term['zeta_factors'],x,7)
                    before=coefficients(list(original[2].items()),x,7)
                    kernel=coefficients([(row['shift'],str(-Q(row['power'])))],x,7)
                    expected=[sum((before[j]*kernel[n-j] for j in range(n+1)),Q(0)) for n in range(7)]
                    self.assertEqual(got,expected)
                    self.assertEqual(got[0],1)

    def test_selected_simple_tail_is_a_universal_recurrence(self):
        rows=P.generate(Meter());selected=P.choose(rows)
        compiled=P.compile_tails(selected,Meter())
        self.assertTrue(selected['recovery']['cofinal'])
        self.assertEqual(compiled['status'],'COMPLETE_REPEATED_VALUATION_TAILS_CERTIFIED')
        for term,tail in zip(selected['terms'],compiled['terms']):
            for x in (Q(1,5),Q(2,3),Q(4,5)):
                direct=coefficients(term['zeta_factors'],x,12)
                for e in range(2,12):
                    if tail['zero_above_first_valuation']:expected=Q(0)
                    else:
                        expected=sum((Q(c)*x**p for p,c in tail['tail']),Q(0))*x**(tail['common_ratio_power']*(e-2))
                    self.assertEqual(direct[e],expected)
                if not tail['zero_above_first_valuation']:
                    self.assertLessEqual(sum(map(abs,direct[2:])),Q(tail['valuation_mass_constant'])*x**int(6*Q(tail['valuation_mass_power'])))

    def test_tensor_scope_keeps_common_unsuppressed_mode(self):
        chosen=P.choose(P.generate(Meter()));tails=P.compile_tails(chosen,Meter())
        sectors=P.tensor_sectors(tails,Meter())
        self.assertEqual(len(sectors),16)
        nonzero=[s for s in sectors if s['status']!='ZERO_ON_SHARED_SQUARE']
        self.assertTrue(any(s['prime_weight']=='0' for s in nonzero))
        self.assertTrue(any(Q(s['cofinal_rho_threshold'])<Q(1,3) for s in nonzero))
        self.assertTrue(all(not s['full_target_recovered'] for s in nonzero))

    def test_general_fractional_programs_are_not_forced_into_finite_tail_schema(self):
        row=next(r for r in P.generate(Meter()) if r['shift']=='2/3' and r['power']=='1/2')
        result=P.compile_tails(row,Meter())
        self.assertEqual(result['status'],'NONINTEGRAL_LOCAL_LANGUAGE_RETAINS_GENERAL_CONVOLUTION')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_joint_preconditioner_discovery operations='+str(Meter.operations))


if __name__=='__main__':unittest.main()
