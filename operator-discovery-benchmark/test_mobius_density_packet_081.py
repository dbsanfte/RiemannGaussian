"""Direct small-integer identities and boundary cases for new081 producer."""
from fractions import Fraction as Q
from math import gcd
import unittest

import mobius_density_packet_081 as S


def program(**changes):
    p = dict(schema='growing-density-packet-v1', kernel=[dict(divisor=2, weight='-1'),
        dict(divisor=3, weight='1')], memory=2,
        rays=[dict(a=['1', '-1'], weight='1/4')], drift_multiplier='3/2',
        epsilon='1/4', eta='1/4', q='1')
    p.update(changes)
    return p


def mu(n):
    value, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -value if n > 1 else value


class PacketTests(unittest.TestCase):
    def test_event_kernel_direct_product_including_shared_endpoints(self):
        parsed = S.parse(program())
        _, T = S.matrices(parsed)
        for a, b in ((1, 2), (2, 3), (3, 5)):
            jumps = S.pair_kernel(parsed, a, b)
            for u in (1, 17, 40, 121):
                for g in range(1, u//b+1):
                    f = lambda side, i: sum(v for d, v in parsed['kernel'].items() if side*g*2**i*d <= u)
                    direct = 2*sum(T[i][j]*f(a, i)*f(b, j) for i in range(3) for j in range(3))
                    self.assertEqual(direct, sum((v for d, v in jumps if g*d <= u), Q(0)))

    def test_density_and_exact_signed_pair_values(self):
        p = program(eta='1/3', epsilon='1/2')
        source = S.Arithmetic(100)
        bank = S.PairBank(p, 6, source)
        u, D = 181, 5
        got = bank.packet_values(u, [D])[D]
        P, N, *_ = bank.stats[D]
        self.assertGreater(P, 0)
        self.assertGreater(N, 0)
        total = Q(0)
        for b in range(2, D+1):
            for row in bank.rows[b]:
                v = row['density']
                w = min(Q(1), N/P) if v > 0 else min(Q(1), P/N) if v < 0 else Q(1)
                for g in range(1, u//b+1):
                    coeff = sum((c for d, c in row['kernel'] if d*g <= u), Q(0))
                    total += w*mu(row['a']*g)*mu(b*g)*coeff
        self.assertEqual(total, got['packet'])
        self.assertEqual(got['weighted_density'], 0)

    def test_complete_drift_and_odd_delay_identity(self):
        p = program()
        bank = S.PairBank(p, 4, S.Arithmetic(100))
        for u in (1, 2, 3, 31, 63, 127):
            cert = bank.finite_certificate(p, u)
            direct = [sum(Q(row['weight'])*sum(mu(n) for n in range(1, (u//2**j)//row['divisor']+1))
                          for row in p['kernel']) for j in range(3)]
            self.assertEqual(list(map(Q, cert['state'])), direct)
            self.assertEqual(Q(cert['half_energy']), bank.state(u//2)[1])
            self.assertEqual(Q(cert['drift']), Q(cert['packet'])+Q(cert['unlinked']))
            self.assertGreaterEqual(Q(cert['energy']), direct[0]**2)

    def test_empty_and_single_sign_packets_not_fake_controls(self):
        p = program(memory=1, rays=[], kernel=[dict(divisor=1, weight='1')])
        bank = S.PairBank(p, 2, S.Arithmetic(32))
        values = bank.packet_values(32, [1, 2])
        self.assertEqual(values[1]['packet'], 0)
        self.assertEqual(values[2]['packet'], 0)
        self.assertEqual(values[2]['weighted_pairs'], 0)

    def test_generic_fractional_proof_gate_and_omega_price(self):
        p = program(epsilon='2/7', eta='7/29', q='1')
        cert = S.bound_certificate(p)
        self.assertEqual(Q(cert['exponent']), 1)
        omega = S.omega_price(Q(1, 2))
        self.assertEqual(omega['primes'], [2, 3])
        self.assertGreaterEqual(omega['price']**2, Q(8, 3))
        self.assertEqual(S.omega_price(Q(1))['primes'], [])
        with self.assertRaises(MemoryError):
            S.omega_price(Q(1, 32))

    def test_cache_growth_and_schedules_share_exact_values(self):
        p = program()
        source = S.Arithmetic(100)
        bank = S.PairBank(p, 6, source)
        first = bank.packet_values(181, [2, 3])
        enlarged = bank.packet_values(181, [2, 3, 6])
        self.assertEqual(first, {d: enlarged[d] for d in first})
        self.assertEqual(source.counts((2, 3), [0, 20, 80]),
            [sum(mu(g)**2 for g in range(1, x+1) if gcd(g, 6) == 1) for x in (0, 20, 80)])
        self.assertEqual(source.counts((2, 3), [5]), [2])

    def test_frozen_boundary_draw_is_exact_and_excludes_known(self):
        draw = S.validation_draw(['1/4', '2/7'], [16384], per_band=1)
        self.assertNotIn(16384, draw['parents'])
        for row in draw['draws']:
            if row['kind'] == 'ratio_entry':
                e, v, b = Q(row['eta']), row['boundary'], row['label']
                self.assertLess((v-1)**e.numerator, b**e.denominator)
                self.assertGreaterEqual(v**e.numerator, b**e.denominator)

    def test_language_and_prospective_gates(self):
        self.assertGreater(len(S.proof_schedules()), 20)
        self.assertTrue(any(x['eta'] == '7/29' for x in S.proof_schedules()))
        with self.assertRaises(ValueError):
            S.parse(program(memory=True))
        with self.assertRaises(ValueError):
            S.parse(program(rays=[dict(a=['1', '-1'], weight='-1')]))
        with self.assertRaises(MemoryError):
            S.PairBank(program(), 1000, S.Arithmetic(1000))


if __name__ == '__main__':
    unittest.main()
