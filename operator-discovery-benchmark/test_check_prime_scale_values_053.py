import unittest
import numpy as np
import prime_scale_source_053 as P
import prime_scale_search_053 as S
import check_prime_scale_values_053 as C

PM, SM, CM = P.Meter(), S.Meter(), C.Meter(cap=200_000_000)
ALPHA = '13/29'


def fields(source):
    return {k: getattr(source, k) for k in ('alpha', 'max_n', 'bits', 'mu', 'prefix_w', 'prefix_up', 'prefix_down')}


class ValueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = P.make_source(ALPHA, 96, meter=PM)
        cls.verified = C.verify_source(fields(cls.source), CM)

    def request(self):
        return {'alpha': ALPHA, 'q': 2, 'coefficients': [2, -3, 1],
                'bound': {'C': '8', 'log_power': '0', 'minimum': 2, 'normalization': 'divide_by_alpha'}}

    def test_independent_mobius_recurrence_known_values(self):
        self.assertEqual(C._mobius(12, CM).tolist(), [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0])

    def test_joint_signed_filter_contained_in_separate_A_enclosure(self):
        req = self.request()
        word = {k: req[k] for k in ('alpha', 'q', 'coefficients')}
        pair = S.source_value(self.source, word, 19, {}, SM, PM)
        result = C.joint_filter(self.verified, req, 19, S.interval(pair), CM)
        self.assertTrue(result['verified']); self.assertFalse(result['uniform_arithmetic_bound_proved'])

    def test_all_source_prefixes_and_mobius_mutations(self):
        for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
            data = fields(self.source); data[name] = data[name].copy(); data[name][23] += 1
            with self.assertRaises(ValueError): C.verify_source(data, CM)

    def test_source_request_and_domain_swaps(self):
        req = self.request(); req['alpha'] = '12/29'
        with self.assertRaises(ValueError): C.joint_filter(self.verified, req, 19, meter=CM)
        with self.assertRaises(ValueError): C.joint_filter(self.verified, self.request(), 25, meter=CM)
        with self.assertRaises(ValueError): C.joint_filter(self.verified, self.request(), True, meter=CM)

    def test_wrong_producer_interval_and_non_annihilating_word(self):
        with self.assertRaises(ValueError): C.joint_filter(self.verified, self.request(), 19, {'lower': '100', 'upper': '101'}, CM)
        req = self.request(); req['coefficients'] = [2, -2, 1]
        with self.assertRaises(ValueError): C.joint_filter(self.verified, req, 19, meter=CM)

    def test_own_immutable_source_and_resource_caps(self):
        self.assertFalse(self.verified.mu.flags.writeable)
        self.assertFalse(self.verified.weights.flags.writeable)
        self.assertFalse(np.shares_memory(self.source.mu, self.verified.mu))
        data = fields(self.source); data['max_n'] = C.MAX_N+1
        with self.assertRaises(ValueError): C.verify_source(data, CM)
        with self.assertRaises(OverflowError): C.verify_source(fields(self.source), C.Meter(cap=0))

    def test_extension_reuses_independently_verified_atoms_and_IPC_flags(self):
        import pickle
        extended = P.extend_source(self.source, 108, PM)
        verified = C.verify_source(fields(extended), CM, self.verified)
        self.assertTrue(np.array_equal(verified.weights[:97], self.verified.weights))
        self.assertEqual(verified.metadata['reused_verified_prefix_through'], 96)
        self.assertEqual(sum(verified.metadata['atom_refinement_counts'].values()),
                         int(np.count_nonzero(verified.mu[97:])))
        restored = pickle.loads(pickle.dumps(verified))
        self.assertFalse(restored.mu.flags.writeable)
        self.assertFalse(restored.weights.flags.writeable)

    def test_independent_target_scope_and_exact_comparison(self):
        req = self.request()
        value = C.joint_filter(self.verified, req, 19, meter=CM)
        weight = S.bound_weight(19, req['bound']['log_power'], SM)
        target = S.interval(tuple(8*x for x in weight))
        checked = C.check_bound(req, 19, value, target, CM)
        self.assertTrue(checked['verified']); self.assertTrue(checked['finite_only'])
        self.assertFalse(checked['uniform_arithmetic_bound_proved'])
        bad = dict(value, request=dict(req, alpha='12/29'))
        with self.assertRaises(ValueError): C.check_bound(req, 19, bad, meter=CM)
        with self.assertRaises(ValueError): C.check_bound(req, 19, value, {'lower': '0', 'upper': '1'}, CM)


def tearDownModule():
    print('SYNTHETIC_WORK operations=%d' % (PM.operations+SM.operations+CM.operations))


if __name__ == '__main__': unittest.main()
