import unittest
from fractions import Fraction as Q
import mobius_full_mode_gate_080 as P


KERNEL = [dict(divisor=4, weight='-1'), dict(divisor=5, weight='1'),
          dict(divisor=8, weight='1'), dict(divisor=10, weight='-1')]


def pair(extra=True):
    a = P.S.save_ray(P.S.zero_ray()); a[1] = ['0', '1']; a[9] = ['1', '0']
    if extra:
        a[7] = ['1/2', '0']; a[8] = ['1', '0']
    target = [int(i in (1, 7, 8, 9)) for i in range(10)]
    return a, P.S.complement(a, target)


class FullModes(unittest.TestCase):
    def test_exact_rho_envelope_and_selected_complements(self):
        import check_mobius_full_mode_gate_080 as C
        rho = P.rho_envelope()
        self.assertLess(Q(rho['rho_three_upper']), Q(3, 50))
        check = C.verify_rho_envelope(rho)
        self.assertEqual(check['status'], 'VERIFIED_DICKMAN_ENVELOPE', check)
        for gamma in ('5/9', '4/7', '3/5', '5/8', '2/3'):
            spec = P.S.log_spec(str((3-2*Q(gamma))/(2*Q(gamma))))
            for a in pair():
                gate = P.propose_full_mode(KERNEL, [2, 3, 5, 7], gamma, a, spec, rho)
                self.assertEqual(gate['status'], 'FULL_MODE_OBSTRUCTION_PROPOSAL')
                check = C.verify_full_mode(KERNEL, [2, 3, 5, 7], gamma, a, spec, rho, gate['certificate'])
                self.assertEqual(check['status'], 'VERIFIED_FULL_MODE_OBSTRUCTION', check)
                self.assertFalse(check['arithmetic_residual_refuted'])

    def test_pure_annihilator_needs_and_has_second_mode(self):
        import check_mobius_full_mode_gate_080 as C
        spec = P.S.log_spec('7/5'); a = pair(False)[0]
        self.assertEqual(P.propose_full_mode(KERNEL, [2, 3, 5, 7], '5/8', a, spec)['status'], 'UNPAID_ZERO_CONTAINING_MODE')
        gate = P.propose_second_mode(KERNEL, [2, 3, 5, 7], '5/8', a, spec)
        self.assertEqual(gate['status'], 'SECOND_MODE_OBSTRUCTION_PROPOSAL')
        self.assertGreater(Q(gate['certificate']['moment_lower']), 0)
        check = C.verify_second_mode(KERNEL, [2, 3, 5, 7], '5/8', a, spec, gate['certificate'])
        self.assertEqual(check['status'], 'VERIFIED_SECOND_MODE_OBSTRUCTION', check)
        self.assertEqual(P.propose_second_mode(KERNEL, [], '5/8', pair()[0], spec)['status'], 'UNSUPPORTED_SECOND_MODE_DOMAIN')

    def test_positive_rho_only_zero_mass_and_unsupported_domains(self):
        import check_mobius_full_mode_gate_080 as C
        spec = P.S.log_spec('7/5'); a = pair(False)[0]; a[7] = ['1', '0']
        gate = P.propose_full_mode(KERNEL, [2, 3], '5/8', a, spec)
        self.assertTrue(gate['strict_rho_positivity_used'])
        self.assertEqual(gate['status'], 'FULL_MODE_OBSTRUCTION_PROPOSAL')
        check = C.verify_full_mode(KERNEL, [2, 3], '5/8', a, spec, P.rho_envelope(), gate['certificate'])
        self.assertEqual(check['status'], 'VERIFIED_FULL_MODE_OBSTRUCTION', check)
        self.assertEqual(P.propose_full_mode([], [], '5/8', a, spec)['status'], 'UNPAID_ZERO_CONTAINING_MODE')
        self.assertEqual(P.propose_full_mode(KERNEL, [], '1/3', a, spec)['status'], 'UNSUPPORTED_FULL_MODE_DOMAIN')
        with self.assertRaises(ValueError): P.propose_full_mode(KERNEL, [], '5/8', a, P.S.log_spec('2'))


if __name__ == '__main__': unittest.main()
