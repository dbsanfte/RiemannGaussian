"""Synthetic source laws and adversarial proof admission, without core discovery."""
import copy
from fractions import Fraction as F
import time
import unittest

from flint import arb, ctx

import check_prime_cofactor_discovery as C
import prime_cofactor_discovery as P  # Fixtures only; never a verification oracle.
from prime_bank_candidates import Meter


METER = Meter(cap=50000000, seconds=180)
STARTED = time.monotonic()


def source(channels):
    return dict(lattice=6, channels=[dict(atoms=[dict(kind=k, shift=s) for k, s in atoms],
                                         weight=list(weight)) for atoms, weight in channels])


def generated(src):
    result = P.discover(src)
    METER.charge(result['operations'])
    if result['status'] != 'universal_law_proposed':
        raise AssertionError('synthetic fixture did not close')
    return result['certificate']


def hand_power(shift=2):
    src = source([([('power', shift)], ['1', '0'])])
    r = F(shift, 6)
    cases = {2: ('1/3', '16', 0, 'two_sided_power_bound', '1/3', True),
             6: ('-1', '9', 2, 'upper_bound_only', None, False),
             12: ('-1', '9', 0, 'upper_bound_only', None, False)}
    exponent, constant, logarithm, status, lower, refutes = cases[shift]
    frontier = dict(state=0, prime_polynomial=[[shift, '1', '0']], unit_ceiling='1',
        scope='raw_rough_prefix_shared_cutoff_ceil_sqrt_2X', all_integer_blocks=True,
        whole_signed_bound_proved=False, status=status, lead_degree=shift, sign=1,
        coefficient_floor='1', remainder_ceiling='0', q_threshold='1/2',
        coefficient_ceiling='1', r=str(r), energy_upper_exponent=exponent,
        energy_lower_exponent=lower, upper_constant=constant, upper_log_power=logarithm,
        refutes_separate_subpower_payment=refutes)
    cert = dict(source=src, states=[dict(row=['1'], program=dict(op='source'))], basis=[['1']],
        transfer=[[dict(numerator=[[0, 0, '1']], denominator=[[0, 0, '1'], [shift, 1, '-1']])]],
        unit=[dict(constant='1', R='0')], target_row=['1'],
        domain=dict(prime=True, cofactor_coprime=True, all_valuations=True), frontier_bounds=[frontier])
    return src, cert


def joined(bound):
    certificate = P.search_joined_forms(bound)
    METER.charge(certificate.get('operations', 1))
    return certificate


class PrimeCofactorTests(unittest.TestCase):
    def test_hand_certificate_complete_tail_and_rough_bound(self):
        src, cert = hand_power()
        answer = C.verify(src, cert, METER)
        self.assertTrue(answer['all_prime_coefficient_closure_proved'])
        self.assertEqual(answer['frontier_bounds'][0]['upper_constant'], '16')
        self.assertEqual(answer['frontier_bounds'][0]['energy_lower_exponent'], '1/3')
        theorem = answer['theorem_scope'][0]['lower']
        self.assertEqual(theorem['c'], 'log(2)/8')
        self.assertIn('y>=64', theorem['head_requirements'])
        self.assertIn('J<=c*A*X^(1-r)/(8*2^r*log(X))', theorem['head_requirements'])
        self.assertEqual(theorem['log_power'], -2)
        self.assertFalse(answer['whole_prefix_bound_proved'])
        self.assertFalse(answer['RH_proved'])

    def test_independent_fixed_constant_enclosure_and_precision_restore(self):
        src, cert = hand_power()
        old = ctx.prec
        try:
            ctx.prec = 96
            answer = C.verify(src, cert, METER)
            self.assertEqual(ctx.prec, 96)
            residue = arb(answer['R_enclosure'])
            self.assertTrue(residue > 1 and residue < 5)
        finally:
            ctx.prec = old

    def test_generic_jet_programs_and_exact_recovery(self):
        src = source([([('power', 2), ('mu', 0)], ['1', '0']),
                      ([('power', 2), ('mu', 4)], ['0', '-1'])])
        cert = generated(src)
        answer = C.verify(src, cert, METER)
        self.assertEqual(answer['state_count'], 2)
        self.assertEqual(answer['unit'][0], dict(constant='1', R='-1'))
        self.assertNotEqual(cert['states'][1]['row'], ['1', '1'])
        for field, replacement in [('row', ['1', '1']),
                                   ('program', dict(op='jet', parent=1, valuation=1, degree=0, scale='-1'))]:
            bad = copy.deepcopy(cert)
            bad['states'][1][field] = replacement
            with self.subTest(field=field), self.assertRaises(ValueError):
                C.verify(src, bad, METER)

    def test_proper_invariant_module_is_not_forced_to_full_channel_rank(self):
        src = source([([('power', 2)], ['2', '0']), ([('power', 2)], ['3', '0'])])
        cert = generated(src)
        self.assertEqual(len(cert['states']), 1)
        answer = C.verify(src, cert, METER)
        self.assertEqual(answer['source_channel_count'], 2)
        self.assertEqual(answer['unit'][0]['constant'], '5')
        self.assertEqual(answer['frontier_bounds'][0]['upper_constant'], '400')

    def test_observed_finite_valuation_alias_cannot_replace_infinite_transfer(self):
        src, cert = hand_power()
        bad = copy.deepcopy(cert)
        bad['transfer'][0][0] = dict(numerator=[[2 * e, e, '1'] for e in range(9)],
                                    denominator=[[0, 0, '1']])
        with self.assertRaisesRegex(ValueError, 'infinite valuation tail'):
            C.verify(src, bad, METER)

    def test_unit_and_target_recovery_cannot_be_dropped(self):
        src, cert = hand_power()
        for key, replacement in [('unit', [dict(constant='0', R='0')]),
                                 ('unit', []), ('target_row', ['0']), ('basis', [['2']])]:
            bad = copy.deepcopy(cert)
            bad[key] = replacement
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify(src, bad, METER)

    def test_source_binding_guards_signed_weights_and_atom_semantics(self):
        src, cert = hand_power()
        for mutate in [lambda s: s['channels'][0]['weight'].__setitem__(0, '-1'),
                       lambda s: s['channels'][0]['atoms'][0].__setitem__('kind', 'mu'),
                       lambda s: s['channels'][0]['atoms'][0].__setitem__('shift', 4),
                       lambda s: s.__setitem__('lattice', 3)]:
            bad = copy.deepcopy(cert)
            mutate(bad['source'])
            with self.subTest(source=bad['source']), self.assertRaisesRegex(ValueError, 'source binding'):
                C.verify(src, bad, METER)

    def test_prime_coprime_and_all_valuation_domains_are_mandatory(self):
        src, cert = hand_power()
        for key in ['prime', 'cofactor_coprime', 'all_valuations']:
            bad = copy.deepcopy(cert)
            bad['domain'][key] = False
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify(src, bad, METER)
        bad = copy.deepcopy(cert)
        bad['domain']['prime'] = 1
        with self.assertRaises(ValueError):
            C.verify(src, bad, METER)

    def test_denominator_and_polynomial_canonical_guards(self):
        src, cert = hand_power()
        mutations = [dict(numerator=[[0, 0, '1']], denominator=[]),
                     dict(numerator=[[0, 0, '1']], denominator=[[1, 0, '1']]),
                     dict(numerator=[[0, 0, '1'], [0, 0, '1']], denominator=[[0, 0, '1']]),
                     dict(numerator=[[0, 0, '0']], denominator=[[0, 0, '1']]),
                     dict(numerator=[[0, 0, '1/1']], denominator=[[0, 0, '1']]),
                     dict(numerator=[[0, 0, '1e999999999']], denominator=[[0, 0, '1']])]
        for function in mutations:
            bad = copy.deepcopy(cert)
            bad['transfer'][0][0] = function
            with self.subTest(function=function), self.assertRaises(ValueError):
                C.verify(src, bad, METER)

    def test_frontier_sign_lead_tail_and_head_constants_are_checked(self):
        src = source([([('power', 2), ('mu', 4)], ['-1', '0'])])
        cert = generated(src)
        C.verify(src, cert, METER)
        for key, replacement in [('sign', 1), ('lead_degree', 4), ('coefficient_floor', '2'),
                                 ('remainder_ceiling', '0'), ('q_threshold', '1'),
                                 ('coefficient_ceiling', '1'), ('upper_constant', '0'),
                                 ('unit_ceiling', '0'), ('upper_log_power', 2),
                                 ('energy_lower_exponent', '0'), ('r', '1/2')]:
            bad = copy.deepcopy(cert)
            bad['frontier_bounds'][0][key] = replacement
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify(src, bad, METER)

    def test_unknown_leading_sign_keeps_its_degree_and_only_upper_bound(self):
        src = source([([('power', 2)], ['-2', '1'])])
        cert = generated(src)
        answer = C.verify(src, cert, METER)
        bound = answer['frontier_bounds'][0]
        self.assertEqual(bound['status'], 'unresolved_leading_coefficient')
        self.assertEqual(bound['lead_degree'], 2)
        self.assertEqual(bound['upper_constant'], '144')
        self.assertIsNone(bound['energy_lower_exponent'])
        for key, replacement in [('sign', 1), ('coefficient_floor', '1'),
                                 ('energy_lower_exponent', '1/3'), ('refutes_separate_subpower_payment', True)]:
            bad = copy.deepcopy(cert)
            bad['frontier_bounds'][0][key] = replacement
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify(src, bad, METER)

    def test_zero_prime_polynomial_retains_constant_unit_energy(self):
        src = source([([('mu', 0), ('power', 0)], ['3', '-1'])])
        cert = generated(src)
        answer = C.verify(src, cert, METER)
        bound = answer['frontier_bounds'][0]
        self.assertEqual(bound['status'], 'zero_prime_polynomial')
        self.assertEqual(bound['unit_ceiling'], '2')
        self.assertEqual(bound['upper_constant'], '4')
        self.assertEqual(bound['energy_upper_exponent'], '-1')
        self.assertIsNone(bound['energy_lower_exponent'])
        bad = copy.deepcopy(cert)
        bad['frontier_bounds'][0]['upper_constant'] = '0'
        with self.assertRaises(ValueError):
            C.verify(src, bad, METER)

    def test_critical_harmonic_and_summable_upper_costs(self):
        for shift in [6, 12]:
            src, cert = hand_power(shift)
            answer = C.verify(src, cert, METER)
            bound = answer['frontier_bounds'][0]
            self.assertEqual(bound['upper_log_power'], 2 if shift == 6 else 0)
            self.assertEqual(bound['upper_constant'], '9')
            self.assertIsNone(bound['energy_lower_exponent'])
        src, cert = hand_power(6)
        cert['frontier_bounds'][0]['upper_log_power'] = 0
        with self.assertRaises(ValueError):
            C.verify(src, cert, METER)

    def test_frontier_coverage_boolean_types_and_scope_fail_closed(self):
        src, cert = hand_power()
        for key, replacement in [('scope', 'complete_source_prefix'), ('state', False),
                                 ('sign', True), ('all_integer_blocks', 1),
                                 ('whole_signed_bound_proved', True)]:
            bad = copy.deepcopy(cert)
            bad['frontier_bounds'][0][key] = replacement
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify(src, bad, METER)
        bad = copy.deepcopy(cert)
        bad['frontier_bounds'] = []
        with self.assertRaises(ValueError):
            C.verify(src, bad, METER)
        cert['whole_signed_bound_proved'] = True
        with self.assertRaises(ValueError):
            C.verify(src, cert, METER)

    def test_frontier_replay_api_requires_all_state_bounds(self):
        src, cert = hand_power()
        answer = C.verify_frontier(src, cert['states'], cert['frontier_bounds'], METER)
        self.assertTrue(answer['verified'])
        self.assertFalse(answer['whole_signed_bound_proved'])
        with self.assertRaises(ValueError):
            C.verify_frontier(src, cert['states'], [], METER)

    def test_joined_storage_all_candidates_and_singular_survivors(self):
        src, cert = hand_power()
        bound = cert['frontier_bounds'][0]
        proof = joined(bound)
        answer = C.verify_joined_forms(bound, proof, METER, source=src, states=cert['states'])
        self.assertTrue(answer['verified'])
        self.assertEqual(sum(answer['counts'].values()), 275)
        self.assertEqual(answer['counts']['endpoint_restatement'], 4)
        self.assertGreater(answer['counts']['refuted_by_rough_lower_bound'], 0)
        self.assertFalse(answer['broader_multiscale_grammar_refuted'])

    def test_joined_storage_coverage_and_classification_mutations(self):
        src, cert = hand_power()
        bound = cert['frontier_bounds'][0]
        proof = joined(bound)
        variants = []
        bad = copy.deepcopy(proof)
        bad['rows'].pop()
        variants.append(bad)
        bad = copy.deepcopy(proof)
        bad['rows'][-1] = copy.deepcopy(bad['rows'][0])
        variants.append(bad)
        bad = copy.deepcopy(proof)
        singular = next(row for row in bad['rows'] if row['classification'] == 'endpoint_restatement')
        singular['classification'] = 'refuted_by_rough_lower_bound'
        variants.append(bad)
        bad = copy.deepcopy(proof)
        paid = next(row for row in bad['rows'] if row['classification'] == 'refuted_by_rough_lower_bound')
        paid['schur_complement'] = '0'
        variants.append(bad)
        for bad in variants:
            with self.assertRaises(ValueError):
                C.verify_joined_forms(bound, bad, METER, source=src, states=cert['states'])

    def test_joined_form_lower_premise_is_independently_source_bound(self):
        src, cert = hand_power()
        bound = cert['frontier_bounds'][0]
        proof = joined(bound)
        with self.assertRaisesRegex(ValueError, 'source and state'):
            C.verify_joined_forms(bound, proof, METER)
        other = source([([('mu', 0), ('power', 0)], ['1', '0'])])
        with self.assertRaisesRegex(ValueError, 'source-bound frontier'):
            C.verify_joined_forms(bound, proof, METER, source=other, states=cert['states'])
        bad = copy.deepcopy(bound)
        bad['coefficient_floor'] = '10'
        with self.assertRaises(ValueError):
            C.verify_joined_forms(bad, proof, METER, source=src, states=cert['states'])

    def test_joined_forms_do_not_refute_multiscale_grammar_or_pay_target(self):
        src, cert = hand_power()
        bound = cert['frontier_bounds'][0]
        proof = joined(bound)
        for key in ['whole_signed_bound_proved', 'RH_proved', 'broader_multiscale_grammar_refuted']:
            bad = copy.deepcopy(proof)
            bad[key] = True
            with self.subTest(key=key), self.assertRaises(ValueError):
                C.verify_joined_forms(bound, bad, METER, source=src, states=cert['states'])
        src, cert = hand_power(6)
        with self.assertRaisesRegex(ValueError, 'positive rough lower'):
            C.verify_joined_forms(cert['frontier_bounds'][0], proof, METER, source=src, states=cert['states'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_prime_cofactor_discovery '
          f'operations={METER.operations} elapsed_seconds={time.monotonic()-STARTED:.6f}')


if __name__ == '__main__':
    unittest.main()
