"""Synthetic rational twists, full signed recovery and adversarial admission."""
import copy
from fractions import Fraction as F
import time
import unittest

import check_fractional_cofactor_bounds as C
import fractional_cofactor_bounds as P  # Proposal fixtures only.
from prime_bank_candidates import Meter


METER = Meter(cap=50000000, seconds=180)
STARTED = time.monotonic()


def power(shift=2, weight=('1', '0')):
    """One-channel hand-proved Euler factor, including its complete tail."""
    source = dict(lattice=6, channels=[dict(atoms=[dict(kind='power', shift=shift)], weight=list(weight))])
    a, b = map(F, weight)
    low, high = sorted([a+b, a+5*b])
    J = max(abs(low), abs(high))
    sign = 1 if low > 0 else -1 if high < 0 else 0
    A = min(abs(low), abs(high)) if sign else F(0)
    r = F(shift, 6)
    lower = 1-2*r if sign and r < 1 else None
    if r < 1:
        upper, constant, logarithm = 1-2*r, (J+2*J/(1-r))**2, 0
    elif r == 1:
        upper, constant, logarithm = F(-1), (J+2*J)**2, 2
    else:
        upper, constant, logarithm = F(-1), (J+J*(1+1/(r-1)))**2, 0
    frontier = dict(state=0, prime_polynomial=[[shift, str(a), str(b)]], unit_ceiling=str(J),
        scope='raw_rough_prefix_shared_cutoff_ceil_sqrt_2X', all_integer_blocks=True,
        whole_signed_bound_proved=False, status='two_sided_power_bound' if lower is not None else
            'unresolved_leading_coefficient' if not sign else 'upper_bound_only',
        lead_degree=shift, sign=sign, coefficient_floor=str(A), remainder_ceiling='0',
        q_threshold='1/2', coefficient_ceiling=str(J), r=str(r), energy_upper_exponent=str(upper),
        energy_lower_exponent=None if lower is None else str(lower), upper_constant=str(constant),
        upper_log_power=logarithm, refutes_separate_subpower_payment=bool(lower is not None and lower > 0))
    certificate = dict(source=source, states=[dict(row=['1'], program=dict(op='source'))],
        basis=[['1']], transfer=[[dict(numerator=[[0, 0, '1']],
            denominator=[[0, 0, '1'], [shift, 1, '-1']])]],
        unit=[dict(constant=str(a), R=str(b))], target_row=['1'],
        domain=dict(prime=True, cofactor_coprime=True, all_valuations=True), frontier_bounds=[frontier])
    return source, certificate


def delta():
    source = dict(lattice=6, channels=[dict(atoms=[dict(kind='mu', shift=0),
        dict(kind='power', shift=0)], weight=['1', '0'])])
    frontier = dict(state=0, prime_polynomial=[], unit_ceiling='1',
        scope='raw_rough_prefix_shared_cutoff_ceil_sqrt_2X', all_integer_blocks=True,
        whole_signed_bound_proved=False, status='zero_prime_polynomial', lead_degree=None, sign=0,
        coefficient_floor='0', remainder_ceiling='0', q_threshold='1/2', coefficient_ceiling='0',
        r=None, energy_upper_exponent='-1', energy_lower_exponent=None, upper_constant='1',
        upper_log_power=0, refutes_separate_subpower_payment=False)
    certificate = dict(source=source, states=[dict(row=['1'], program=dict(op='source'))],
        basis=[['1']], transfer=[[dict(numerator=[[0, 0, '1']], denominator=[[0, 0, '1']])]],
        unit=[dict(constant='1', R='0')], target_row=['1'],
        domain=dict(prime=True, cofactor_coprime=True, all_valuations=True), frontier_bounds=[frontier])
    return source, certificate


def two_states():
    source, certificate = power()
    source['channels'].append(dict(atoms=[dict(kind='power', shift=6)], weight=['100', '0']))
    root = copy.deepcopy(certificate['frontier_bounds'][0])
    root.update(prime_polynomial=[[2, '1', '0'], [6, '100', '0']], unit_ceiling='101',
                remainder_ceiling='100', q_threshold='1/200', coefficient_ceiling='101',
                upper_constant='163216')
    second = copy.deepcopy(certificate['frontier_bounds'][0]); second['state'] = 1
    certificate.update(source=source, states=[dict(row=['1', '1'], program=dict(op='source')),
        dict(row=['1', '0'], program=dict(op='jet', parent=0, valuation=1, degree=2, scale='1'))],
        basis=[['1', '1'], ['1', '0']],
        transfer=[[dict(numerator=[[0, 0, '1']], denominator=[[0, 0, '1'], [6, 1, '-1']]),
            dict(numerator=[[2, 1, '1'], [6, 1, '-1']], denominator=[[0, 0, '1'],
                [2, 1, '-1'], [6, 1, '-1'], [8, 2, '1']])],
            [dict(numerator=[], denominator=[[0, 0, '1']]),
             dict(numerator=[[0, 0, '1']], denominator=[[0, 0, '1'], [2, 1, '-1']])]],
        unit=[dict(constant='101', R='0'), dict(constant='1', R='0')], target_row=['1', '0'],
        frontier_bounds=[root, second])
    return source, certificate


def proposal(certificate, exponents):
    result = P.search(certificate, exponents)
    METER.charge(result['operations'])
    return result


class FractionalBoundsTests(unittest.TestCase):
    def audit(self, source, certificate, result):
        return C.verify(source, certificate, result, METER)

    def test_arbitrary_denominator_257_exact_cancellation_after_Abel(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        answer = self.audit(source, certificate, result)
        row = result['candidates'][0]
        self.assertTrue(answer['verified'])
        self.assertEqual(row['prime_powers'], [['260/771', '1', '0']])
        self.assertEqual(row['prefix_upper']['constant'], '1282/511')
        self.assertEqual(row['energy_upper']['power'], '251/771')
        self.assertEqual(row['recovery']['prefix_upper']['power'], '2/3')
        self.assertEqual(row['recovery']['energy_upper']['power'], '1/3')
        self.assertEqual(F(row['recovery']['energy_upper']['constant']), 16*F(1282, 511)**2)
        self.assertEqual(answer['recovered_strict_power_improvements'], 0)
        self.assertFalse(answer['paid_joined_core'])

    def test_zero_twist_exact_identity_has_no_extra_recovery_factor(self):
        source, certificate = power()
        result = proposal(certificate, ['0'])
        self.audit(source, certificate, result)
        row = result['candidates'][0]
        self.assertEqual(row['prefix_upper']['constant'], '5/2')
        self.assertEqual(row['recovery']['prefix_upper']['constant'], '5/2')
        self.assertEqual(row['energy_upper']['constant'], '25')

    def test_every_independently_proven_state_and_tail_threshold(self):
        source, certificate = two_states()
        result = proposal(certificate, ['0', '1/257'])
        answer = self.audit(source, certificate, result)
        self.assertEqual(answer['candidates_verified'], 4)
        self.assertEqual([(c['gamma'], c['state']) for c in result['candidates']],
                         [('0', 0), ('0', 1), ('1/257', 0), ('1/257', 1)])
        self.assertEqual(result['candidates'][2]['energy_lower']['q_threshold'], '1/200')
        self.assertEqual(result['candidates'][2]['unit_ceiling'], '101')
        self.assertIn('y>='+str(200**6), answer['theorem_scope'][2]['lower_head']['requirements'])
        bad = copy.deepcopy(result); bad['candidates'].pop()
        with self.assertRaises(ValueError):
            self.audit(source, certificate, bad)
        bad = copy.deepcopy(result); bad['candidates'][2]['energy_lower']['q_threshold'] = '1/2'
        with self.assertRaises(ValueError):
            self.audit(source, certificate, bad)

    def test_critical_prime_exponent_has_log_loss(self):
        source, certificate = power()
        result = proposal(certificate, ['2/3'])
        self.audit(source, certificate, result)
        row = result['candidates'][0]
        self.assertEqual(row['effective_prime_exponent'], '1')
        self.assertEqual(row['prefix_upper'], dict(constant='2', power='0', log_power=1,
            scope='every real partial prefix 1<=t<=2X at the same y=ceil(sqrt(2X))'))
        self.assertEqual(row['energy_upper'], dict(constant='16', power='-1', log_power=2))
        self.assertEqual(row['recovery']['energy_upper'], dict(constant='256', power='1/3', log_power=2))
        self.assertIsNone(row['energy_lower'])
        bad = copy.deepcopy(result)
        bad['candidates'][0]['energy_upper']['log_power'] = 0
        with self.assertRaises(ValueError):
            self.audit(source, certificate, bad)

    def test_supercritical_twist_upper_and_inverse_worsening(self):
        source, certificate = power()
        result = proposal(certificate, ['1', '5/4'])
        self.audit(source, certificate, result)
        row = result['candidates'][0]
        self.assertEqual(row['prefix_upper']['constant'], '5')
        self.assertEqual(row['energy_upper'], dict(constant='25', power='-1', log_power=0))
        self.assertEqual(row['recovery']['energy_upper'], dict(constant='400', power='1', log_power=0))
        self.assertLess(F(row['recovery']['recovered_power_gain']), 0)

    def test_unit_only_operator_and_conservative_generic_inverse(self):
        source, certificate = delta()
        result = proposal(certificate, ['0', '1/257', '1'])
        answer = self.audit(source, certificate, result)
        for row in result['candidates']:
            self.assertEqual(row['prime_powers'], [])
            self.assertEqual(row['energy_upper'], dict(constant='1', power='-1', log_power=0))
            self.assertIsNone(row['energy_lower'])
        self.assertEqual(result['candidates'][1]['recovery']['energy_upper']['power'], '-255/257')
        self.assertFalse(answer['theorem_scope'][1]['optimal_recovered_bound_claimed'])

    def test_ambiguous_signed_affine_leading_coefficient_keeps_upper_no_lower(self):
        source, certificate = power(weight=('-2', '1'))
        result = proposal(certificate, ['1/257'])
        self.audit(source, certificate, result)
        self.assertEqual(result['candidates'][0]['unit_ceiling'], '3')
        self.assertIsNone(result['candidates'][0]['energy_lower'])
        bad = copy.deepcopy(result)
        bad['candidates'][0]['energy_lower'] = dict(power='1/3')
        with self.assertRaises(ValueError):
            self.audit(source, certificate, bad)

    def test_lower_scope_updates_exponent_and_retains_count_and_unit_head(self):
        source, certificate = power(weight=('-1', '0'))
        result = proposal(certificate, ['1/6'])
        answer = self.audit(source, certificate, result)
        lower = result['candidates'][0]['energy_lower']
        self.assertEqual(lower['sign'], -1)
        self.assertEqual(lower['prime_exponent'], '1/2')
        self.assertEqual(lower['power'], '0')
        scope = answer['theorem_scope'][0]['lower_head']
        self.assertEqual(scope['r'], '1/2')
        self.assertIn('y>=64', scope['requirements'])
        self.assertIn('J<=c*A*X^(1-r)/(8*2^r*log(X))', scope['requirements'])

    def test_all_signed_recovery_fields_are_audited(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        mutations = [(['identity'], 'A_0=n^gamma*A_gamma'), (['requires_all_partial_prefixes'], False),
            (['fixed_cutoff'], False), (['unit_retained'], False),
            (['prefix_upper', 'constant'], '1'), (['prefix_upper', 'power'], '511/771'),
            (['energy_upper', 'power'], '251/771'), (['energy_upper', 'constant'], '1'),
            (['strict_power_improvement'], True), (['recovered_power_gain'], '2/257')]
        for path, value in mutations:
            bad = copy.deepcopy(result)
            cursor = bad['candidates'][0]['recovery']
            for key in path[:-1]:
                cursor = cursor[key]
            cursor[path[-1]] = value
            with self.subTest(path=path), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)

    def test_every_real_partial_prefix_cannot_be_replaced_by_endpoint(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        result['candidates'][0]['prefix_upper']['scope'] = 'only n=2X'
        with self.assertRaises(ValueError):
            self.audit(source, certificate, result)

    def test_full_prime_twist_and_all_valuation_law_required(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        mutations = [('prime_powers', [['1/3', '1', '0']]),
                     ('effective_prime_exponent', '1/3'), ('unit_ceiling', '0'),
                     ('program', dict(op='root_relabel', state=0, exponent='1/257'))]
        for key, value in mutations:
            bad = copy.deepcopy(result)
            bad['candidates'][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)
        for key in ('includes_all_valuations', 'cofactor_coprime', 'unit_preserved'):
            bad = copy.deepcopy(result)
            bad['candidates'][0]['valuation_law'][key] = False
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)

    def test_complete_enumeration_no_duplicates_missing_or_reordering(self):
        source, certificate = power()
        result = proposal(certificate, ['0', '1/257', '1'])
        mutations = []
        bad = copy.deepcopy(result); bad['candidates'].pop(); mutations.append(bad)
        bad = copy.deepcopy(result); bad['candidates'][1] = copy.deepcopy(bad['candidates'][0]); mutations.append(bad)
        bad = copy.deepcopy(result); bad['candidates'].reverse(); mutations.append(bad)
        bad = copy.deepcopy(result); bad['exponents'][1] = '0'; mutations.append(bad)
        for i, bad in enumerate(mutations):
            with self.subTest(i=i), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)

    def test_canonical_rational_guards_and_negative_twist(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        for value in ('2/514', '-1/257', '0.25', '1e999999999', True, 0.1):
            bad = copy.deepcopy(result)
            bad['exponents'] = [value]
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)

    def test_immutable_base_states_source_and_higher_valuation_tail(self):
        source, certificate = power()
        result = proposal(certificate, ['1/257'])
        for key, value in [('base_states', []), ('base_source', dict(lattice=6, channels=[]))]:
            bad = copy.deepcopy(result); bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)
        bad_certificate = copy.deepcopy(certificate)
        bad_certificate['transfer'][0][0] = dict(numerator=[[0, 0, '1'], [2, 1, '1']],
                                                denominator=[[0, 0, '1']])
        with self.assertRaises(ValueError):
            self.audit(source, bad_certificate, result)
        bad_certificate = copy.deepcopy(certificate)
        bad_certificate['unit'] = []
        with self.assertRaises(ValueError):
            self.audit(source, bad_certificate, result)

    def test_no_root_payment_global_closure_or_bool_alias(self):
        source, certificate = power()
        result = proposal(certificate, ['0'])
        for key in ('whole_signed_bound_proved', 'RH_proved'):
            bad = copy.deepcopy(result); bad[key] = True
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)
        for key in ('paid_joined_core', 'whole_signed_bound_proved', 'RH_proved'):
            bad = copy.deepcopy(result); bad['candidates'][0][key] = True
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)
        bad = copy.deepcopy(result); bad['candidates'][0]['state'] = False
        with self.assertRaises(ValueError):
            self.audit(source, certificate, bad)

    def test_accounting_and_statistics_cannot_claim_discovery_gain(self):
        source, certificate = power()
        result = proposal(certificate, ['0', '1/257'])
        for key, value in [('operations', 0), ('recovered_strict_power_improvements', 1),
                           ('exponent_semantics', 'sixth-root lattice only')]:
            bad = copy.deepcopy(result); bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.audit(source, certificate, bad)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_fractional_cofactor_bounds operations='+str(METER.operations)+
          ' elapsed_seconds='+str(time.monotonic()-STARTED), flush=True)


if __name__ == '__main__':
    unittest.main()
