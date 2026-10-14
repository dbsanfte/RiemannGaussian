from fractions import Fraction as Q
import unittest
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_truncated_inverse as P
import check_core_truncated_inverse as C
import core_bound_program_search as B

M = Meter(3000000, 120)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_core_truncated_inverse operations='+str(M.operations))


def toy_mu(H):
    a = [0, 1]+[0]*(H-1)
    for n in range(2, H+1):
        a[n] = -sum(a[d] for d in range(1, n) if n%d == 0)
    return a


class InverseSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 192

    def test_solved_polynomials_and_strict_support_boundary(self):
        for alpha, gamma in [('1/6', '5/6'), ('1/3', '1/2'), ('1/2', '1/2')]:
            for p, q in [(2, 0), (1, 1), (1, 0), (0, 1)]:
                program = P.synthesize(alpha, gamma, p, q, M)
                self.assertTrue(C.verify_certificate(program, M)['verified'])
                self.assertTrue(all(Q(alpha)*t['a']+Q(gamma)*t['b'] < 1 for t in program['terms']))
        p = P.synthesize('1/2', '1/2', 2, 0, M)
        self.assertEqual(p['terms'], [{'a':0, 'b':0, 'coefficient':'1'}, {'a':1, 'b':0, 'coefficient':'2'}])
        self.assertEqual(P.cutoff(64, '1/6'), 2)
        self.assertEqual(P.cutoff(63, '1/6'), 1)

    def test_full_inverse_coefficients_against_independent_checker(self):
        mu = toy_mu(63)
        for p, q in [(2, 0), (1, 1), (1, 0), (0, 1)]:
            program = P.synthesize('1/3', '2/3', p, q, M)
            a = P.evaluate(mu, program, 63, M)
            b = C.evaluate(mu, program, 63, M)
            for key in ('A', 'B', 'R', 'S', 'reconstructed'):
                self.assertTrue(all(x.overlaps(y) for x, y in zip(a[key], b[key])))
            self.assertTrue(all(x.overlaps(y) for x, y in zip(a['reconstructed'], b['reference'])))
            self.assertTrue(a['reconstructed'][1].overlaps(arb(1)))
        bad = list(mu)
        bad[1] = 0
        with self.assertRaises(ValueError):
            P.evaluate(bad, program, 63, M)

    def test_complete_source_binding_and_component_bounds(self):
        source = dict(terms=[
            dict(name='a', coefficient='beta', zeta_factors=[['0','-2'],['1/3','1']]),
            dict(name='b', coefficient='-beta', zeta_factors=[['0','-1'],['1/3','1'],['2/3','-1']]),
            dict(name='c', coefficient='-beta', zeta_factors=[['0','-1']]),
            dict(name='d', coefficient='-R_u', zeta_factors=[['1/3','1'],['2/3','-1']])])
        rows = P.catalogue(source, M)
        self.assertEqual(len(rows), 25)
        parent = dict(construction=B.compile_program([(Q(0),Q(1)),(Q(1),Q(-1))],Q(1),M),
                      reduction=dict(required_coarse_forcing_log_power='0',rho='1/2'))
        for row in rows:
            bounds = P.component_bounds(row, M)
            self.assertFalse(bounds['componentwise_route_closes_target'])
            self.assertTrue(all(Q(t['critical_mass_N_power']) > 0 for t in bounds['components']))
            paid = [t for t in bounds['components'] if t['cofinally_paid_by_this_rule']]
            self.assertEqual(len(paid), int(Q(row['alpha']) <= Q(1,2)))
            if paid:
                self.assertEqual((paid[0]['mode'],paid[0]['a'],paid[0]['b']), ('c',0,0))
            reduction = P.paid_component_reduction(parent,row,bounds)
            self.assertEqual(len(reduction['paid_components']),len(paid))
            self.assertEqual(reduction['new_sufficient_goal']['status'],'open')
            self.assertFalse(reduction['older_fixed_recurrence_discharged'])
            self.assertEqual(next(r for r in bounds['rules']['S'] if r['rule']=='actual_shifted_tail_identity')['power'], str(-Q(row['gamma'])/6))
        mu = toy_mu(31)
        value = P.source_components(mu, rows[0], {'beta':arb(9)/2, '-beta':-arb(9)/2, '-R_u':arb(-4)}, 31, M)
        self.assertTrue(value['restored_source'][1].overlaps(arb(-17)/2))
        self.assertTrue(P.select(rows))
        source['terms'].pop()
        with self.assertRaises(ValueError):
            P.decode_source(source)

    def test_component_means_keep_prehistory_and_cross_terms(self):
        program = B.compile_program([(Q(0), Q(2), Q(-1)), (Q(1), Q(-2), Q(1))], Q(1, 3), M)
        a = [arb(0), arb(-9)]+[arb(n%3-1) for n in range(2, 32)]
        b = [arb(0)]+[arb(n%2) for n in range(1, 32)]
        error = [arb(0)]+[arb(-1) if n%5 == 0 else arb(0) for n in range(1, 32)]
        g = [x+y+z for x,y,z in zip(a,b,error)]
        left = P.joined_projection([dict(values=a),dict(values=b)], error, g, program, 16, '1/2', M, 'prefix')
        right = P.joined_projection([dict(values=a),dict(values=b)], error, g, program, 16, '1/2', M, 'abel')
        literal = B.literal_channels(g, program)
        for i, cell in enumerate(left['cells']):
            for j, mean in enumerate(cell['joined']):
                self.assertTrue(mean.overlaps(right['cells'][i]['joined'][j]))
                self.assertTrue(mean.overlaps(sum(literal[j][cell['start']:cell['stop']], arb(0))/(cell['stop']-cell['start'])))
        self.assertTrue(left['full_coarse'].overlaps(right['full_coarse']))
        self.assertTrue((left['full_coarse']-left['component_diagonal']-left['complete_signed_cross']).contains(0))
        self.assertFalse(left['uniform_bound_proved'])

    def test_centering_retains_large_divisors_and_drift(self):
        mu = toy_mu(63)
        program = P.synthesize('2/3', '1/3', 1, 0, M)
        value = P.evaluate(mu, program, 63, M)
        center = P.centered_residual(mu, value['U'], value['R'], M)
        c = Q(center['exact_slope'])
        ball = arb(c.numerator)/c.denominator
        for n in range(1, 64):
            self.assertTrue((center['values'][n]-ball).overlaps(value['R'][n]))
        self.assertEqual(center['prefix_bound'], 1+sum(abs(mu[d]) for d in range(1, value['U']+1)))
        self.assertFalse(center['original_residual_bound_proved'])
        self.assertTrue(P.primitive_controls(dict(alpha='1/2',gamma='1/3'))['centered_unshifted_residual']['cofinally_paid'])
        self.assertFalse(P.primitive_controls(dict(alpha='2/3',gamma='1/3'))['centered_unshifted_residual']['cofinally_paid'])


if __name__ == '__main__':
    unittest.main()
