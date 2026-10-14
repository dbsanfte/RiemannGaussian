import unittest
from flint import ctx
import check_shifted_quotient_candidates as C
import complete_shifted_quotient_audit as A
from shifted_quotient_candidates import Meter

METERS = []


class CompletionChecks(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192
        self.m = Meter(); METERS.append(self.m)

    def test_euler_subset_all_three_sources(self):
        for source in C.SOURCES:
            values = C.source(source, 63, self.m)
            expected = C.moments(C.evaluate(A.PROGRAM, values, self.m), [16, 32], self.m)
            actual = A.reconstruct(source, 63, [16, 32], self.m)
            for old, new in zip(expected, actual):
                for key in ('energy', 'absolute_energy'):
                    self.assertTrue(old[key].overlaps(new[key]), (source,key))

    def test_exact_three_baselines(self):
        actual = A.baselines(63, [16, 32], self.m)
        for degree in (1, 2, 3):
            expected = C.moments(C.baseline(degree, 63, self.m), [16, 32], self.m)
            for old, new in zip(expected, actual[str(degree)]):
                for key in ('energy', 'absolute_energy'):
                    self.assertTrue(old[key].overlaps(new[key]))

    def test_no_partial_blocks_or_unknown_source(self):
        with self.assertRaises(ValueError): A.reconstruct('mu', 31, [17], self.m)
        with self.assertRaises(ValueError): A.reconstruct('unknown', 31, [8], self.m)
        with self.assertRaises(ValueError): A.reconstruct('mu', True, [1], self.m)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_complete_shifted_quotient_audit operations='+str(sum(m.operations for m in METERS)))


if __name__ == '__main__': unittest.main()
