import copy
from fractions import Fraction as Q
import unittest

import mobius_prime_mass_gate_078 as P


def energy(eta='0',q='1'):
    return dict(schema='rough-energy-program-v1',q=q,tau='3/4',innovation_C='1',
        rays=[dict(a=['0','1']+['0']*8,eta=eta,**{'lambda':'1'})])


class PrimeMass(unittest.TestCase):
    def test_generic_mass_fold_price_and_critical_normalization(self):
        kernel=[dict(divisor=3,weight='2'),dict(divisor=5,weight='-1')]
        result=P.propose_gate(kernel,[2,7],'17/31',energy('1/4'),0)
        cert=result['certificate']
        self.assertEqual(Q(cert['mass']),Q(7,15))
        self.assertEqual(Q(cert['delta']),Q(3,7))
        self.assertEqual(Q(cert['leading_prime']),Q(-1,5))
        self.assertEqual(Q(cert['sigma']),Q(1,2))
        self.assertEqual(Q(cert['eventual_lower_coefficient']),Q(1,100))
        self.assertFalse(result['arithmetic_residual_refuted'])
        self.assertEqual(P.propose_gate(kernel,[],'1/3',energy('1/2'),0)['status'],'NO_POWER_OBSTRUCTION_FROM_THIS_RULE')

    def test_zero_mass_is_unpaid_and_coupled_squares_are_not_rejected(self):
        kernel=[dict(divisor=2,weight='1'),dict(divisor=4,weight='-2')]
        self.assertEqual(P.propose_gate(kernel,[],'1/3',energy(),0)['status'],'UNPAID_ZERO_MASS_LOGARITHMIC_TERMS')
        kernel=[dict(divisor=2,weight='1')]
        e=energy();e['rays'][0]['a'][9]='1'
        self.assertEqual(P.propose_gate(kernel,[],'1/3',e,0)['status'],'COUPLED_RAY_REQUIRES_SIGNED_ANALYSIS')
        self.assertEqual(P.propose_gate(kernel,[],'1',energy(),0)['status'],'OUTSIDE_ASYMPTOTIC_RULE')

    def test_constant_direct_kernel_binding_and_variable_prime_refusal(self):
        source=dict(spec=P.F.S.SOURCE_SPEC,atoms=[dict(column=7,gamma='17/31')],operator=['-2/3'])
        result=P.fixed_kernel(P.F.KERNEL,source)
        self.assertEqual(result['status'],'FIXED_KERNEL_PROPOSAL')
        mass=sum(Q(x['weight'])/x['divisor'] for x in result['kernel'])
        self.assertEqual(mass,-Q(1,40)*(1+Q(2,9)))
        variable=copy.deepcopy(source);variable['atoms'][0]['column']=0
        self.assertEqual(P.fixed_kernel(P.F.KERNEL,variable)['status'],'UNSUPPORTED_VARIABLE_PRIME_OPERATOR')

    def test_feedback_preserves_signed_operator_and_actual_failed_formula(self):
        candidate=dict(id='example',source_id='saved',gamma='1/3',program=energy())
        validation=dict(validation_refuted=1,refutation_witnesses=[dict(u=100,C='1',lower='2')])
        gate=dict(status='VERIFIED_PRIME_MASS_OBSTRUCTION',arithmetic_residual_refuted=False)
        feedback=P.next_search_feedback(candidate,validation,[gate])
        self.assertEqual(feedback['energy_program'],candidate['program'])
        self.assertEqual(feedback['uniform_energy_obstructions'],[gate])
        self.assertEqual(feedback['finite_witnesses'],validation['refutation_witnesses'])
        self.assertFalse(feedback['arithmetic_residual_refuted'])
        self.assertTrue(feedback['normalization_gate_is_not_a_drift_certificate'])


if __name__=='__main__':unittest.main()
