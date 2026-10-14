import unittest
from fractions import Fraction
from flint import arb, ctx
import prime_bank_candidates as P

METERS = []


def meter(cap=1000000):
    result = P.Meter(cap, 60)
    METERS.append(result)
    return result


def mobius(n, work):
    sign, q, left = 1, 2, n
    while q*q <= left:
        work.charge(3)
        if left % q == 0:
            left //= q
            sign = -sign
            if left % q == 0:
                return 0
        q += 1
    return -sign if left > 1 else sign


def reference(H, work):
    work.charge(4*(H+1))
    au, av, p = [[arb(0)]*(H+1) for _ in range(3)]
    mu = [0]+[mobius(n, work) for n in range(1, H+1)]
    roots = [arb(0)]*(H+1)
    for n in range(1, H+1):
        work.charge(65)
        roots[n] = 1/arb(n).root(3)
    for n in range(1, H+1):
        for d in range(1, n+1):
            work.charge()
            if n % d == 0:
                work.charge(5)
                au[n] += mu[d]*roots[n//d]
                av[n] += mu[d]*roots[n//d]*roots[n//d]
        for d in range(2, n):
            work.charge()
            if n % d == 0 and n//d >= 2:
                work.charge(4)
                p[n] += (arb(9)/2)*au[d]*av[n//d]
    return au, av, p


class PrimeBankChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128

    def test_complete_source_against_divisor_coefficients(self):
        work = meter()
        state = P.source_state(63, work)
        au, av, coeff = reference(63, work)
        beta = arb(9)/2
        total = arb(0)
        for n in range(1, 64):
            work.charge(10)
            self.assertTrue(state['a_u'][n].overlaps(au[n]))
            self.assertTrue(state['a_v'][n].overlaps(av[n]))
            self.assertTrue(state['p'][n].overlaps(coeff[n]), n)
            prime_power = n > 1 and all(n % q != 0 for q in state['primes'] if q != state['lpf'][n])
            expected_d = coeff[n] if prime_power else arb(0)
            self.assertTrue(state['d'][n].overlaps(expected_d))
            if prime_power:
                self.assertEqual(state['a'][n], 0)
            else:
                self.assertTrue(state['a'][n].overlaps(coeff[n]))
            if n > 1:
                self.assertTrue(state['zu'][n].overlaps(coeff[n]+beta*av[n]))
                self.assertTrue(state['zv'][n].overlaps(coeff[n]+beta*au[n]))
                self.assertTrue(state['z0'][n].overlaps(2*coeff[n]+beta*(au[n]+av[n])))
            total += state['a'][n]
            self.assertTrue(state['R'][n].overlaps(total-state['main'][n]))
        for name in P._ARRAYS:
            self.assertEqual(state[name][0], 0)
        self.assertEqual(state['a_u'][1], 1)
        self.assertEqual(state['a_v'][1], 1)
        for name in ('p','d','a','z0','zu','zv'):
            self.assertEqual(state[name][1], 0)
        self.assertFalse(state['a'][12].contains(0))
        self.assertEqual(state['d'][12], 0)
        self.assertFalse(state['d'][8].contains(0))

    def test_pointwise_bank_and_smooth_paths_against_direct_sums(self):
        work = meter()
        state = P.source_state(63, work)
        for text in ('1/2', '2/3', '5/6', '11/12'):
            value = Fraction(text)
            result = P.evaluate(text, state, work)
            self.assertIs(result['R'], state['R'])
            self.assertIs(result['main'], state['main'])
            for n in range(1, 64):
                K, L0, Lu, Lv = [arb(0) for _ in range(4)]
                target = n**value.numerator
                for k in range(2, n+1):
                    work.charge(3)
                    if state['lpf'][k]**value.denominator <= target:
                        K += state['a'][k]
                for q in state['primes']:
                    work.charge(3)
                    if q**value.denominator <= target:
                        continue
                    for m in range(2, n//q+1):
                        work.charge(6)
                        L0 += state['z0'][m]
                        Lu += state['zu'][m]*state['prime_u'][q]
                        Lv += state['zv'][m]*state['prime_v'][q]
                for name, expected in (('K',K),('L0',L0),('Lu',Lu),('Lv',Lv)):
                    self.assertTrue(result[name][n].overlaps(expected), (text,n,name))
                self.assertTrue(result['reduced'][n].overlaps(K-L0+Lu-state['main'][n]))
                self.assertTrue((result['reduced'][n]+result['Lv'][n]).overlaps(state['R'][n]))

    def test_square_cutoff_birth_expiry_and_unit(self):
        work = meter()
        state = P.source_state(31, work)
        result = P.evaluate('1/2', state, work)
        self.assertEqual(result['K'][6], 0)
        self.assertTrue(result['L0'][6].overlaps(state['z0'][2]))
        self.assertTrue(result['Lu'][6].overlaps(state['zu'][2]*state['prime_u'][3]))
        self.assertTrue((result['K'][9]-result['K'][8]).overlaps(state['a'][6]))
        # q=3 is excluded at the exact n=9 square-root boundary.
        expected = arb(0)
        for q in (5,7):
            for m in range(2, 9//q+1):
                work.charge()
                expected += state['z0'][m]
        self.assertTrue(result['L0'][9].overlaps(expected))
        for n in (1,2,3,4,5):
            for key in ('K','L0','Lu','Lv'):
                self.assertEqual(result[key][n], 0)
        self.assertTrue(result['R'][1].overlaps(-state['m_u']))

    def test_exact_integer_expiry_boundaries(self):
        work = meter()
        for text in ('1/2','2/3','3/4','5/6','11/12'):
            value = Fraction(text)
            for q in (2,3,5,7,11):
                end = P._expiry(q, value, 63, work)
                work.charge(4)
                self.assertLess((end-1)**value.numerator, q**value.denominator)
                if end <= 63:
                    self.assertGreaterEqual(end**value.numerator, q**value.denominator)
        self.assertEqual(P._expiry(3, Fraction(1,2), 63, work), 9)
        self.assertEqual(P._expiry(2, Fraction(2,3), 63, work), 3)

    def test_singleton_precision_and_validation(self):
        work = meter()
        ctx.prec = 256
        state = P.source_state(1, work)
        result = P.evaluate('1/2', state, work)
        self.assertEqual(result['K'][1], 0)
        self.assertEqual(result['L0'][1], 0)
        self.assertEqual(result['Lu'][1], 0)
        self.assertEqual(result['Lv'][1], 0)
        self.assertTrue(result['reduced'][1].overlaps(-state['m_u']))
        ctx.prec = 128
        with self.assertRaises(ValueError):
            P.evaluate('1/2', state, work)
        ctx.prec = 64
        with self.assertRaises(ValueError):
            P.source_state(1, work)
        ctx.prec = 128
        for text in ('1/3','1','2/4','01/2','1/13','12/13',True):
            with self.assertRaises((ValueError, TypeError)):
                P.theta(text)
        P._horizon(1048575)  # Domain validation only; never builds an actual large table.
        for H in (True,0,-1,1048576):
            with self.assertRaises(ValueError):
                P.source_state(H, work)

    def test_bad_state_and_resource_failures_keep_counts(self):
        work = meter()
        state = P.source_state(7, work)
        malformed = dict(state)
        malformed['a_u'] = list(state['a_u'])
        malformed['a_u'][1] = arb(0)
        with self.assertRaises(ValueError):
            P.evaluate('1/2', malformed, work)
        exhausted = meter(10)
        with self.assertRaises(OverflowError):
            P.source_state(7, exhausted)
        self.assertGreater(exhausted.operations, 0)
        self.assertLessEqual(exhausted.operations, exhausted.cap)
        expired = meter()
        expired.deadline = 0
        with self.assertRaises(TimeoutError):
            expired.charge(3)
        self.assertEqual(expired.operations, 3)
        live = meter()
        with self.assertRaises(MemoryError):
            live.live(P.MAX_CELLS+1)
        self.assertEqual(live.counts()['peak_cells'], P.MAX_CELLS+1)
        self.assertEqual(live.operations, 1)
        for value in (True,-1):
            with self.assertRaises(ValueError):
                live.charge(value)
        self.assertLess(state['_resident_cells'], P.MAX_CELLS)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_prime_bank_candidates operations=' + str(sum(m.operations for m in METERS)))


if __name__ == '__main__':
    unittest.main()
