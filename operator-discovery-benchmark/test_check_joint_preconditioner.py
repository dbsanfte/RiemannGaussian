"""Independent tiny factor/tail/kernel fixtures, no producer arithmetic imports."""
import copy
from fractions import Fraction as Q
from math import ceil
import unittest
from flint import arb, ctx
import check_joint_reciprocal_correlation as S
import check_joint_preconditioner as C

METERS = []


class Meter:
    def __init__(self, cap=2000000, cells=6000000):
        self.operations = 0; self.cap = cap; self.cells = cells; self.peak_cells = 0; METERS.append(self)

    def charge(self, n=1):
        if type(n) is not int or n < 0: raise ValueError('strict operation counter')
        if n > self.cap - self.operations: raise OverflowError('synthetic cap')
        self.operations += n

    def live(self, cells):
        self.charge(); self.peak_cells = max(self.peak_cells, cells)
        if cells > self.cells: raise MemoryError('resident cap')


def tearDownModule():
    print('SYNTHETIC_WORK module=test_check_joint_preconditioner operations=' + str(sum(m.operations for m in METERS)))


def programs(meter):
    shifts = ('1/6', '1/3', '1/2', '2/3', '5/6', '1'); powers = ('-2', '-1', '-1/2', '1/2', '1', '2')
    inputs = [('1', '0')] + [(s, p) for s in shifts for p in powers]; result = []
    for ident, (s, p) in enumerate(inputs):
        shift, power = Q(s), Q(p); terms = []
        bases = [('B', 'beta', [('0', '-2'), ('1/3', '1'), ('2/3', '1')]),
                 ('U', '-beta', [('0', '-1'), ('1/3', '1')]), ('V', '-beta', [('0', '-1'), ('2/3', '1')]),
                 ('power', '-R_u', [('1/3', '1')])]
        positive = numerator = Q(0); max_count = 0; integral = True
        for name, scalar, factors in bases:
            compiled = dict((Q(t), Q(e)) for t, e in factors)
            compiled[shift] = compiled.get(shift, Q(0)) - power
            compiled = {t: e for t, e in compiled.items() if e}; meter.charge(12 + 3 * len(compiled))
            positive += sum((e for e in compiled.values() if e > 0), Q(0)); numerator -= sum((e for e in compiled.values() if e < 0), Q(0))
            max_count = max(max_count, sum(e > 0 for e in compiled.values())); integral &= all(e.denominator == 1 for e in compiled.values())
            terms.append(dict(name=name, coefficient=scalar, zeta_factors=[[str(t), str(e)] for t, e in sorted(compiled.items())]))
        k = ceil(abs(power)); loss = max(Q(1, 2) - shift, Q(0))
        recovery = dict(cofinal=True, kind='identity', divisor_order=0, energy_power_loss='0', norm_bound='1') if not power else dict(
            cofinal=loss == 0, kind='bounded' if shift > Q(1, 2) else 'polylog' if shift == Q(1, 2) else 'unpaid_power',
            divisor_order=k, energy_power_loss=str(2 * loss), norm_bound='zeta(' + str(shift + Q(1, 2)) + ')^' + str(k) if shift > Q(1, 2) else 'H^(' + str(loss) + ')*(1+log H)^' + str(k),
            covers_forward_and_inverse=True, coefficient_majorant='d_' + str(k) + '(n)*n^(-' + str(shift) + ')')
        result.append(dict(id=ident, shift=s, power=p, operator='Dirichlet convolution by coefficients of zeta(s+shift)^(-power)',
                           recovery=recovery, terms=terms, positive_factor_order=str(positive), numerator_factor_order=str(numerator),
                           max_positive_factors_in_one_term=max_count, integral_local_rational_functions=integral,
                           correction='(beta*delta-d)*preconditioner, retained with its proved global norm cost', whole_signed_bound_proved=False, RH_proved=False))
    return result


def selected_tails():
    records = []
    for name, tail, monomial, constant, multiplicity, bernstein in (
        ('B', [[0, '1'], [2, '-2'], [4, '1']], 0, '1', 2, ['-2', '-2', '-1']),
        ('U', [[2, '-1'], [4, '2'], [6, '-1']], 2, '-1', 2, ['-1', '-1', '-5/6', '-1/2', '-1']),
        ('power', [[4, '1'], [6, '-1']], 4, '1', 1, ['0', '0', '1/6', '1/2', '0'])):
        records.append(dict(name=name, zero_above_first_valuation=False, tail_start=2, tail=tail, common_ratio_power=2,
                            factorization=dict(monomial_power=monomial, coefficient=constant, one_minus_power=2, multiplicity=multiplicity),
                            valuation_mass_power=str(Q(monomial, 6)), valuation_mass_constant='1',
                            recurrence='coefficient(p^e)=tail(x)*x^(common_ratio_power*(e-2)), x=p^(-1/6), e>=2',
                            first_valuation_bernstein=bernstein, cofactor_divisor_order=2))
    records.insert(2, dict(name='V', zero_above_first_valuation=True, tail_start=2, tail=[], valuation_mass_power=None, cofactor_divisor_order=2))
    return dict(status='COMPLETE_REPEATED_VALUATION_TAILS_CERTIFIED', terms=records, all_prime_powers_retained=True, whole_signed_bound_proved=False, RH_proved=False)


def direct_convolution(left, right, meter):
    values = [arb(0)] * len(left)
    for n in range(1, len(left)):
        for d in range(1, n + 1):
            meter.charge()
            if n % d == 0: meter.charge(2); values[n] += left[d] * right[n // d]
    return values


class PreconditionerCheckerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old_precision = ctx.prec; ctx.prec = 192
        cls.meter = Meter(); cls.source = S.source(31, cls.meter)

    @classmethod
    def tearDownClass(cls): ctx.prec = cls.old_precision

    def assertBall(self, actual, expected):
        self.assertTrue(actual.is_finite()); self.assertTrue(actual.overlaps(expected), (actual, expected))

    def test_complete_algebraic_grammar_selection_and_mutations(self):
        m = Meter(); rows = programs(m); selected = C.verify_selection(rows, 23, m)
        self.assertEqual(selected['selected']['shift'], '2/3'); self.assertEqual(selected['selected']['power'], '1')
        self.assertFalse(selected['selection_uses_numerical_responses']); self.assertEqual(selected['full_target'], 'OPEN')
        for row in rows: self.assertTrue(C.verify_program(row, m)['verified'])
        for mutation in ('factor', 'coefficient', 'scope', 'id'):
            changed = copy.deepcopy(rows[23])
            if mutation == 'factor': changed['terms'][0]['zeta_factors'][0][1] = '-1'
            elif mutation == 'coefficient': changed['terms'][0]['coefficient'] = '-beta'
            elif mutation == 'scope': changed['RH_proved'] = True
            else: changed['id'] = True
            with self.assertRaises(ValueError): C.verify_program(changed, m)
        with self.assertRaises(ValueError): C.verify_selection(rows, 0, m)
        with self.assertRaises(ValueError): C.verify_selection(rows[:-1], 23, m)
        bad = rows[:]; bad[0] = rows[1]
        with self.assertRaises(ValueError): C.verify_selection(bad, 23, m)

    def test_selected_valuation_tails_and_unsuppressed_mode(self):
        m = Meter(); row = programs(m)[23]; tails = selected_tails()
        record = C.verify_tails(row, tails, m)
        self.assertTrue(record['all_prime_powers_retained']); self.assertEqual(record['unsuppressed_source_mode'], 'OPEN')
        self.assertEqual(tails['terms'][0]['valuation_mass_power'], '0')
        for x in (Q(1, 2), Q(2, 3)):
            for term in (tails['terms'][0], tails['terms'][1], tails['terms'][3]):
                m.charge(30)
                value = sum(Q(c) * x ** e for e, c in term['tail'])
                f = term['factorization']; expected = Q(f['coefficient']) * x ** f['monomial_power'] * (1 - x ** 2) ** f['multiplicity']
                self.assertEqual(value, expected)
                self.assertLessEqual(abs(value) / (1 - x ** 2), x ** f['monomial_power'])

    def test_tampered_tail_metadata_and_missing_complements_rejected(self):
        m = Meter(); row = programs(m)[23]
        for mutation in ('tail', 'monomial', 'mass', 'bernstein', 'zero', 'missing', 'flag', 'extra'):
            tails = selected_tails()
            if mutation == 'tail': tails['terms'][0]['tail'][1][1] = '-1'
            elif mutation == 'monomial': tails['terms'][1]['factorization']['monomial_power'] = 0
            elif mutation == 'mass': tails['terms'][0]['valuation_mass_power'] = '1/3'
            elif mutation == 'bernstein': tails['terms'][0]['first_valuation_bernstein'][0] = '-1'
            elif mutation == 'zero': tails['terms'][0]['zero_above_first_valuation'] = True
            elif mutation == 'missing': tails['terms'].pop()
            elif mutation == 'flag': tails['whole_signed_bound_proved'] = True
            else: tails['terms'][0]['extra'] = 1
            with self.assertRaises(ValueError): C.verify_tails(row, tails, m)
        with self.assertRaises(ValueError): C.verify_tails(programs(m)[22], selected_tails(), m)

    def test_general_fractional_kernels_inverse_and_complete_convolution(self):
        m = Meter()
        for shift, power in (('1/6', '-2'), ('1/3', '-1'), ('1/2', '-1/2'), ('2/3', '1/2'), ('5/6', '1'), ('1', '2'), ('1', '0')):
            result = C.precondition(self.source, shift, power, m)
            w = direct_convolution(result['kernel'], self.source['tilde_b'], m)
            identity = direct_convolution(result['kernel'], result['inverse'], m)
            for n in range(32):
                self.assertBall(result['w'][n], w[n]); self.assertBall(identity[n], arb(1 if n == 1 else 0))
                self.assertTrue(result['reconstruction_residual'][n].contains(0))
            r, v = Q(power), Q(shift)
            for p in (2, 3, 5):
                m.charge(2 * 64 + 20)
                weight = arb(p) ** (-arb(v.numerator) / v.denominator)
                self.assertBall(result['kernel'][p], -arb(r.numerator) / r.denominator * weight)
                coefficient = r * (r - 1) / 2
                self.assertBall(result['kernel'][p * p], arb(coefficient.numerator) / coefficient.denominator * weight ** 2)
            self.assertFalse(result['RH_proved']); self.assertEqual(result['full_target'], 'OPEN')

    def test_selected_core_direct_modes_and_paid_correction(self):
        m = Meter(); result = C.precondition(self.source, '2/3', '1', m)
        mu = list(map(arb, self.source['mu'])); ku = [arb(0)] * 32; mu_v = [arb(0)] * 32
        for n in range(1, 32):
            m.charge(2 * 64 + 5); ku[n] = arb(n) ** (-arb(1) / 3); mu_v[n] = mu[n] * arb(n) ** (-arb(2) / 3)
        reference = dict(nu0=direct_convolution(mu, self.source['au'], m), nu1=direct_convolution(mu_v, self.source['au'], m),
                         nu2=direct_convolution(mu_v, ku, m))
        overlap = direct_convolution(self.source['d'], mu_v, m)
        for n in range(32):
            for name, values in reference.items(): self.assertBall(result[name][n], values[n])
            m.charge(4); self.assertBall(result['correction'][n], arb(9) / 2 * mu_v[n] - overlap[n])
            self.assertBall(result['kernel'][n], mu_v[n]); self.assertTrue(result['core_residual'][n].contains(0))
            m.charge(10)
            self.assertBall(result['core'][n], arb(9) / 2 * reference['nu0'][n] - arb(9) / 2 * reference['nu1'][n] - arb(9) / 2 * mu[n] - self.source['R_u'] * reference['nu2'][n])
            self.assertBall(result['complete_source'][n], result['core'][n] + result['correction'][n])
        self.assertBall(result['w'][1], -self.source['R_u'])
        self.assertBall(result['correction'][1], arb(9) / 2)

    def test_all_prefixes_units_and_identity_power(self):
        m = Meter(); selected = C.precondition(self.source, '2/3', '1', m)
        prefix = arb(0)
        for n in range(1, 32):
            prefix += selected['w'][n]; m.charge(); self.assertBall(selected['prefix'][n], prefix)
        for name, prefixes in selected['mode_prefixes'].items():
            running = arb(0)
            for n in range(1, 32): running += selected[name][n]; m.charge(); self.assertBall(prefixes[n], running)
        core_prefix = correction_prefix = arb(0)
        for n in range(1, 32):
            core_prefix += selected['core'][n]; correction_prefix += selected['correction'][n]; m.charge(2)
            self.assertBall(selected['core_prefix'][n], core_prefix)
            self.assertBall(selected['correction_prefix'][n], correction_prefix)
        identity = C.precondition(self.source, '1', '0', m)
        for n in range(32): self.assertBall(identity['w'][n], self.source['tilde_b'][n])
        self.assertTrue(identity['kernel'][0].is_zero()); self.assertTrue(identity['kernel'][1] == 1)

    def test_strict_program_domains_precision_and_resource_cap(self):
        m = Meter()
        for shift, power in (('0', '1'), ('2/6', '1'), ('1/7', '1'), ('2/3', '3'), ('2/3', True)):
            with self.assertRaises(ValueError): C.precondition(self.source, shift, power, m)
        with self.assertRaises(ValueError): C.precondition(dict(self.source), '2/3', '1', m)
        ctx.prec = 160
        try:
            with self.assertRaises(ValueError): C.precondition(self.source, '2/3', '1', m)
        finally: ctx.prec = 192
        with self.assertRaises(OverflowError): C.precondition(self.source, '2/3', '1', Meter(cap=1))
        with self.assertRaises(MemoryError): C.precondition(self.source, '2/3', '1', Meter(cells=1))

    def test_shared_meter_and_no_open_mode_erasure(self):
        m = Meter(); row = programs(m)[23]
        C.verify_program(row, m); before = m.operations; record = C.verify_tails(row, selected_tails(), m)
        self.assertGreater(m.operations, before); self.assertFalse(record['whole_signed_bound_proved'])
        result = C.precondition(self.source, '2/3', '1', m)
        self.assertEqual(result['unsuppressed_source_mode'], 'OPEN'); self.assertLess(m.peak_cells, 6000000)


if __name__ == '__main__': unittest.main()
