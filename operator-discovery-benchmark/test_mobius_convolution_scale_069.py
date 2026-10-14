"""New support, signed polynomial and conditional-bound calibration tests."""
from fractions import Fraction as Q
from math import prod
import unittest
import mobius_convolution_scale_069 as S

METER = S.Meter(cap=300_000_000_000)
PARAMS = {'primes': [2, 3, 5], 'p': 3, 'q': 5, 'alpha': '1/5', 'gamma': '5/28', 'tau': '1/2'}


def convolution(a, b):
    R = len(a)-1; result = [0]*(R+1)
    for x in range(1, R+1):
        for y in range(1, R//x+1): result[x*y] += a[x]*b[y]
    return result


def inverse(a):
    out = [0]*len(a); out[1] = 1
    for n in range(2, len(a)):
        out[n] = -sum(a[d]*out[n//d] for d in range(2, n+1) if n%d == 0)
    return out


def prefixes(a):
    answer = [0]*len(a)
    for n in range(1, len(a)): answer[n] = answer[n-1]+a[n]
    return answer


def evaluate(poly, M):
    return sum(value*prod(M[i] for i in key) for key, value in poly.items())


class ConvolutionScaleTests(unittest.TestCase):
    def test_generic_elimination_and_learned_faces(self):
        values, rank = S.affine_solve([({0: 2, 1: 1}, 7), ({0: 1, 1: -1}, -1)], 2, METER)
        self.assertEqual(values, [Q(2), Q(3)]); self.assertEqual(rank, 2)
        for degree in range(2, 9):
            law = S.learn_annihilator(degree, METER)
            self.assertEqual(law['coefficients'][0], 1)
            for i in range(degree):
                for mask in range(1 << degree):
                    if not mask & (1 << i):
                        self.assertEqual(law['coefficients'][mask]+law['coefficients'][mask | (1 << i)], 0)
        with self.assertRaises(ValueError): S.affine_solve([({0: 1}, 1), ({0: 1}, 2)], 1, METER)

    def test_discovered_law_on_unrelated_convolution_inverses(self):
        R = 29; unit = [0]*(R+1); unit[1] = 1
        for one in ([0]+[1]*R, [0, 1]+[((n*7)%5)-2 for n in range(2, R+1)]):
            mu = inverse(one)
            for cuts in ([5, 5], [2, 3, 3], [1, 2, 2, 2]):
                self.assertGreater(prod(u+1 for u in cuts), R)
                law = S.learn_annihilator(len(cuts), METER); reconstructed = [0]*(R+1)
                for mask in range(1, 1 << len(cuts)):
                    term = unit[:]; count = mask.bit_count()
                    for i, u in enumerate(cuts):
                        if mask & (1 << i): term = convolution(term, mu[:u+1]+[0]*(R-u))
                    for _ in range(count-1): term = convolution(term, one)
                    for n in range(1, R+1): reconstructed[n] -= law['coefficients'][mask]*term[n]
                self.assertEqual(reconstructed, mu)

    def test_exact_fractional_cutoffs_and_upward_price_weights(self):
        for R in (1, 2, 17, 64, 257):
            for text in ('0', '1/257', '3/11', '2/3', '1'):
                q = Q(text); u = S.power(R, text, METER)
                self.assertLessEqual(u**q.denominator, R**q.numerator)
                self.assertGreater((u+1)**q.denominator, R**q.numerator)
                w = S.power(R, text, METER, upper_grid=True)
                target = R**q.numerator*S.GRID**q.denominator
                self.assertGreaterEqual(w**q.denominator, target)
                self.assertLess((w-1)**q.denominator, target)
        with self.assertRaises(OverflowError): S.power(17, '1/1000000', METER)

    def test_complete_signed_prefix_polynomial_matches_direct_actual_arithmetic(self):
        for R in (1, 7, 19, 37):
            mu = inverse([0]+[1]*R); M = prefixes(mu)
            k = [0]+[((3*n)%7)-3 for n in range(1, R+1)]
            for request in (['1/2']*2, ['1/3']*3, ['1/5']*5, ['1/3', '2/3'], ['1/2', '2/3']):
                cuts = [S.power(R, e, METER) for e in request]
                law = S.learn_annihilator(len(cuts), METER)
                poly = S.prefix_polynomial(k, -2, cuts, law, S.kernel_levels(k, len(cuts), METER), METER)
                actual = -2+sum(a*b for a, b in zip(mu, k))
                self.assertEqual(evaluate(poly, M), actual)

    def test_support_gate_is_strict_and_complete_rectangles_are_retained(self):
        k = [0, 1, 2, 3, 4]; law = S.learn_annihilator(2, METER)
        levels = S.kernel_levels(k, 2, METER)
        with self.assertRaises(ValueError): S.prefix_polynomial(k, 0, [1, 1], law, levels, METER)
        mu = inverse([0]+[1]*4); M = prefixes(mu)
        poly = S.prefix_polynomial(k, 0, [3, 3], law, levels, METER)
        self.assertEqual(evaluate(poly, M), sum(a*b for a, b in zip(mu, k)))
        # Equal product-to-R and zero extension beyond the tensor rectangle matter.
        self.assertTrue(any(len(key)==2 for key in poly))

    def test_unit_extraction_and_conditional_majorant(self):
        poly = {(): -7, (2,): 3, (2, 3): -4, (3, 3): 2}
        prices = S.conditional_prices(poly, 3, 5, ['0', '1/2', '3/11', '1'], {}, METER)
        self.assertEqual(prices[0]['coefficients'], ['7/5', '3/5', '6/5', '0'])
        for part in prices:
            sigma = Q(part['sigma']); C = 2
            bound = sum(Q(a)*C**i for i, a in enumerate(part['coefficients']))
            for a in (-2, 0, 2):
                for b in (-2, 0, 2):
                    self.assertLessEqual(abs(Q(evaluate(poly, [0, 1, a, b]), 5)), bound)

    def test_complete_polynomial_scalar_box_adversary_is_not_actual_mu(self):
        for scale in (1, 2, 5, 20):
            N, y, R = 15*scale, 16*scale, 20*scale
            g, floors, _ = S.source(N, y, 3, 5, Q(1), METER)
            kernel = [0]+[g[n]-(g[2*n] if 2*n<=R else 0) for n in range(1, R+1)]
            u = S.power(R, '1/2', METER)
            poly = S.prefix_polynomial(kernel, floors.get(1,0), [u,u], S.learn_annihilator(2,METER), S.kernel_levels(kernel,2,METER), METER)
            self.assertEqual(poly.get((),0), (scale+1)//2)
            fake = [0,1]+[0]*(u-1)
            self.assertEqual(evaluate(poly,fake), (scale+1)//2)
            true = prefixes(inverse([0]+[1]*R))
            self.assertNotEqual(fake[3],true[3])

    def test_request_reuse_scope_and_input_gates(self):
        cert = S.construct(11, 7, 2, PARAMS, [['1/2','1/2'], ['3/7','4/7'], ['1/3']*3], meter=METER)
        self.assertTrue(cert['universal_convolution_identity_proved'])
        self.assertFalse(cert['conditional_prefix_bounds_paid'])
        self.assertFalse(cert['uniform_head_bound_proved'])
        self.assertFalse(cert['RH_proved'])
        empty = S.construct(7, 5, 0, PARAMS, [['1/257','256/257']], meter=METER)
        self.assertTrue(all(not e['rows'] for e in empty['endpoints']))
        for req in ([], [['1/3','1/3']], [['1','0']], [['2/4','1/2']], [['1/2','1/2']]*2):
            with self.assertRaises(ValueError): S.construct(11,7,2,PARAMS,req,meter=METER)
        with self.assertRaises(OverflowError): S.construct(11,7,2,PARAMS,meter=S.Meter(cap=0))

    def test_independent_pipeline_source_binding_and_all_degree_costs(self):
        from copy import deepcopy
        import run_mobius_convolution_scale_069 as R
        old = R.PRIOR.SEARCH.construct(37,25,4,PARAMS,['0','1/2'],meter=METER)
        cm0 = R.PRIOR.CHECK.Meter(); ov = R.PRIOR.CHECK.verify_control(old,cm0); METER.charge(cm0.operations)
        saved = dict(N=37,y=25,max_j=4,certificate=old,verification=ov,
            original_source_binding_proved=True,uniform_head_bound_proved=False,RH_proved=False,
            source_cases=[dict(N=37,y=25,H=9,theta='5/8',endpoints=[dict(ratio=e['ratio'],
                actual_head_variation=e['actual_head_variation'],selected_head_upper=e['selected_head_upper']) for e in ov['endpoints']])])
        self.assertIs(R.bind_floor(saved),old)
        cert = S.construct(37,25,4,PARAMS,meter=METER)
        cm = R.CHECK.Meter(); verdict=R.CHECK.verify_control(cert,cm); METER.charge(cm.operations)
        cases=R.summarize(saved,cert,verdict,METER)
        self.assertEqual(len(cases),1)
        for e in cases[0]['endpoints']:
            self.assertEqual(len(e['all_plans']),len(S.DEFAULT_REQUESTS))
            self.assertTrue(e['pareto_plan_indices'])
            for okay,upper in zip(e['finite_C1_premises'],e['selected_conditional_C1_head_prices']):
                if okay:self.assertLessEqual(Q(e['actual_head_variation']),Q(upper))
        for field in ('N','y','max_j'):
            bad=deepcopy(saved);bad['verification'][field]+=1
            with self.assertRaises(ValueError):R.bind_floor(bad)
        bad=deepcopy(saved);bad['verification']['endpoints'][0]['rows'][0]['actual_coefficient']='123'
        with self.assertRaises(ValueError):R.summarize(bad,cert,verdict,METER)
        bad=deepcopy(saved);bad['source_cases'][0]['H']+=1
        with self.assertRaises(ValueError):R.summarize(bad,cert,verdict,METER)
        self.assertFalse(verdict['conditional_prefix_bounds_paid'])
        self.assertFalse(verdict['original_source_binding_proved'])


if __name__ == '__main__': unittest.main()
