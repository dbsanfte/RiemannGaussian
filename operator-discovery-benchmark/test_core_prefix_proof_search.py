"""Generic arithmetic semantics and bound calibration, separate from search."""
from fractions import Fraction as Q
import unittest
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_prefix_proof_search as P


M = Meter(50000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_prefix_proof_search operations='+str(M.operations))


def convolution(a, b):
    H = len(a)-1
    result = [Q(0)]*(H+1)
    for n in range(1, H+1):
        result[n] = sum((a[d]*b[n//d] for d in range(1, n+1) if n%d == 0), Q(0))
        M.charge(20*n)
    return result


def prefixes(a):
    total = Q(0)
    out = []
    for value in a[1:]:
        total += value
        out.append(total)
    return out


def evaluate(factors, arrays, H):
    out = [Q(0), Q(1)]+[Q(0)]*(H-1)
    for factor in factors:
        out = convolution(out, arrays[factor])
    return out


class PrefixProofSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192

    def test_signed_nonmultiplicative_prefix_convolution(self):
        for phase in range(4):
            left = [Q(0)]+[Q((n*7+phase)%9-4, n%3+1) for n in range(1, 22)]
            right = [Q(0)]+[Q((n*n+phase)%7-3, n%4+1) for n in range(1, 22)]
            product = convolution(left, right)
            bound = max(map(abs, prefixes(left)))*sum(map(abs, right))
            self.assertLessEqual(max(map(abs, prefixes(product))), bound)
            M.charge(300)

    def test_search_chooses_a_signed_factor_and_fractional_cost(self):
        # Calibration of inference rules; these are not source selections.
        for alpha in ('1/7', '1/6', '1/3', '1/2'):
            search = P.ProofSearch(alpha, '5/6', M)
            proof = search.nodes[search.solve(['A', 'E'], 'prefix')]
            self.assertEqual(Q(proof['power']), 2*Q(alpha))
            self.assertEqual(proof['rule'], 'prefix_convolution')
            self.assertEqual(proof['log_degree'], 0)
            absolute = search.nodes[search.solve(['A', 'E'], 'mass')]
            self.assertGreater(Q(absolute['power']), Q(proof['power']))
            self.assertEqual(search.solve(['E', 'A'], 'prefix'), proof['id'])
        search = P.ProofSearch('1/6', '5/6', M)
        tail = search.nodes[search.solve(['S'], 'critical')]
        self.assertEqual(tail['atom_rule'], 'S_critical_tail')
        self.assertEqual(tail['power'], '-5/36')

    def test_all_centering_depths_keep_every_signed_drift(self):
        H, c = 17, Q(-3, 7)
        arrays = {name: [Q(0)]+[Q((n*(i+2)+i)%9-4, n%3+1) for n in range(1, H+1)]
                  for i, name in enumerate(('A', 'B', 'R', 'S', 'K'))}
        arrays['O'] = [Q(0)]+[Q(1)]*H
        arrays['C'] = [Q(0), c]+[Q(0)]*(H-1)
        arrays['E'] = [Q(0)]+[v+c for v in arrays['R'][1:]]
        mode = dict(p=1, q=1, positive_shift='1/3', coefficient='-beta')
        term = dict(a=3, b=1, coefficient='2')
        original = [2*v for v in evaluate(['A', 'B', 'K', 'R', 'R', 'R', 'S'], arrays, H)]
        engine = P.ProofSearch('1/6', '5/6', M)
        for depth in range(4):
            output = P.expansion(mode, term, depth, engine)
            restored = [Q(0)]*(H+1)
            for piece in output['pieces']:
                values = evaluate(piece['expression'], arrays, H)
                restored = [x+Q(piece['coefficient'])*y for x, y in zip(restored, values)]
            self.assertEqual(restored, original)
            if depth:
                self.assertTrue(any('C' in p['expression'] and 'O' in p['expression'] for p in output['pieces']))
                self.assertTrue(any(Q(p['coefficient']) < 0 for p in output['pieces']))

    def test_abel_cost_bounds_complete_weighted_prefixes(self):
        values = [0, -11]+[(n%4)-1 for n in range(2, 35)]
        bound = max(map(abs, prefixes(list(map(Q, values)))))
        channels = [dict(eta='1/6', polynomial=['-2', '3', '-1']),
                    dict(eta='2/3', polynomial=['1', '-2', '1', '-1'])]
        cost = P.channel_cost(dict(channels=channels))
        for n in range(1, len(values)):
            L = arb(2*n).log()
            total = arb(0)
            for channel in channels:
                p = list(map(Q, channel['polynomial']))
                eta = Q(channel['eta'])
                value = arb(0)
                for k in range(1, n+1):
                    t = arb(k).log()/L
                    weight = sum((arb(q.numerator)/q.denominator*t**j for j, q in enumerate(p)), arb(0))
                    value += values[k]*weight
                    M.charge(200)
                value /= L**(arb(eta.numerator)/eta.denominator)
                total += value*value
            ceiling = cost*bound*bound
            self.assertTrue(total <= arb(ceiling.numerator)/ceiling.denominator)

    def test_uniform_payment_keeps_log_and_power_costs(self):
        self.assertIsNone(P.uniform_payment('0', 2))
        self.assertIsNone(P.uniform_payment('1/6', 0))
        self.assertEqual(P.uniform_payment('0', 0), 1)
        for exponent in ('-1/6', '-1/3', '-1'):
            for degree in (0, 1, 2, 4):
                q = Q(exponent)
                bound = P.uniform_payment(exponent, degree)
                for N in (1, 2, 3, 11, 64, 1000000):
                    value = arb(N)**(arb(q.numerator)/q.denominator)*(1+arb(N).log())**degree
                    ceiling = arb(bound.numerator)/bound.denominator
                    self.assertTrue(value <= ceiling or (value-ceiling).is_zero())
                    M.charge(200)

    def test_new_payment_excludes_previously_paid_head(self):
        mode = dict(name='V', p=1, q=0, positive_shift=None, coefficient='-beta')
        row = dict(id=3, alpha='1/6', gamma='5/6', cases=[dict(mode=mode, program=dict(
            terms=[dict(a=0,b=0,coefficient='1'), dict(a=1,b=0,coefficient='1')]))])
        result = P.search(row, M)
        parent = dict(parent_obligation_id='synthetic', paid_component_reduction=dict(
            paid_components=[dict(mode='V',a=0,b=0)], new_sufficient_goal=dict(p='3')))
        construction = dict(channels=[dict(eta='1/3',polynomial=['1','-1'])])
        output = P.reduction(parent, construction, result)
        self.assertEqual(len(output['old_paid_excluded']), 1)
        self.assertEqual(len(output['newly_paid']), 1)
        self.assertEqual(len(output['remaining_signed_pieces']), 1)
        self.assertTrue(output['all_remaining_crosses_retained'])
        self.assertTrue(output['transport_error_retained'])
        self.assertFalse(output['whole_signed_bound_proved'])
        self.assertEqual(output['goal']['status'], 'open')
        self.assertEqual(output['goal']['p'], '3')
        self.assertFalse(output['original_fixed_recurrence_discharged'])
        parent['paid_component_reduction']['new_sufficient_goal']['p'] = '-1/6'
        with self.assertRaises(ValueError):
            P.reduction(parent, construction, result)


if __name__ == '__main__':
    unittest.main()
