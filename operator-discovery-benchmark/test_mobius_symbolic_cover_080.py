import unittest
from unittest.mock import patch
import tempfile
from pathlib import Path
import json
import time
from fractions import Fraction as Q
import mobius_symbolic_cover_080 as P
import check_mobius_symbolic_cover_080 as C


def row(u, values):
    d = values+[0]*(10-len(values))
    return dict(u=u, flux_features=[{'1': str(x)} if x else {} for x in d],
        gram_upper=[dict(i=i, j=j, terms=[dict(left_token='1', right_token='1', coefficient='1')] if i == j else [])
                    for i in range(10) for j in range(i, 10)], token_intervals={'1': ['1', '1']})


class SymbolicCover(unittest.TestCase):
    def test_exact_log_promotion_complement_and_scope(self):
        spec = P.log_spec('7/5')
        self.assertEqual(C.verify_log(spec)['status'], 'VERIFIED_LOG_ENCLOSURE')
        frames = P.generate_frames([1, 7, 8, 9], 'promoted', {'coordinates': [1, 9]})
        self.assertTrue(frames)
        self.assertTrue(any(sum(any(map(Q, x)) for x in f['rays'][0]) == 4 for f in frames))
        for f in frames:
            a, b = f['rays']
            self.assertEqual([P.poly_add(tuple(map(Q, x)), tuple(map(Q, y))) for x, y in zip(a, b)],
                             [(Q(t), Q(0)) for t in f['target']])
            check = C.verify_mode_annihilator('5/8', a, spec)
            self.assertEqual(check['status'], 'VERIFIED_LEADING_MODE_ANNIHILATION')
            self.assertEqual(check['whole_ray_mode_annihilated'], not any(any(map(Q, a[i])) for i in (7, 8)))

    def test_search_discovers_synthetic_signed_pair_and_exposes_failure(self):
        rows = {u: row(u, [t, -t, 1]) for u, t in [(16, 10), (32, 20), (64, 40)]}
        frames = P.generate_frames([0, 1, 2]); spec = P.log_spec('1')
        ranking = P.rank_frames(rows, frames, '1', '1', spec)
        best = frames[ranking[0]['frame_index']]
        self.assertTrue(any(a[0] == a[1] and Q(a[0][0]) != 0 for a in best['rays']))
        ks = [P.calibrate(rows, a, '1', spec)['kappa'] for a in best['rays']]
        price = P.cover_price(best['rays'], ks, '1', spec)
        self.assertEqual(C.verify_cover(best['target'], best['rays'], ks, '1', spec, {'price': str(price)})['status'], 'VERIFIED_CONDITIONAL_COVER')
        for a, k in zip(best['rays'], ks):
            for r in rows.values():
                self.assertEqual(C.verify_leaf(r, a, k, '1', spec)['status'], 'CERTIFIED_FINITE')
        i = next(i for i, a in enumerate(best['rays']) if Q(a[0][0]) != 0)
        self.assertEqual(C.verify_leaf(row(128, [80, -79, 1]), best['rays'][i], ks[i], '1', spec)['status'], 'REFUTED_FINITE')

    def test_symbolic_structural_obstruction_does_not_ignore_other_channels(self):
        a = P.save_ray(P.zero_ray()); a[1] = ['1', '-1']
        kernel = [dict(divisor=4, weight='-1')]; spec = P.log_spec('7/5')
        gate = P.mode_obstruction(kernel, [], '5/8', a, spec)
        self.assertEqual(C.verify_mode_obstruction(kernel, [], '5/8', a, spec, gate['certificate'])['status'], 'VERIFIED_SYMBOLIC_MODE_OBSTRUCTION')
        a[7] = ['1', '0']
        self.assertEqual(P.mode_obstruction(kernel, [], '5/8', a, spec)['status'], 'UNPAID_OTHER_SIGNED_CHANNELS')

    def test_folded_intervals_bind_both_arithmetic_endpoints_and_actual_cells(self):
        kernel = [dict(divisor=4, weight='-1'), dict(divisor=5, weight='1')]
        norm = P.OLD.fixed_norm(kernel, [2, 3], 100)
        arithmetic = P.OLD.P.Arithmetic(120)
        for u in (401, 480):
            parent, child = [P.kernel_intervals(norm['folded_kernel'], v) for v in (u, u//2)]
            cells = P.OLD.construct_cells(arithmetic, u, parent, child, [2, 3], '3/5')
            self.assertEqual(C.F.verify_cells(parent, child, [2, 3], '3/5', cells)['status'], 'VERIFIED_CELLS')
            bound = C.verify_source_pair(kernel, [2, 3], u, parent, child, cells)
            self.assertEqual(bound['status'], 'VERIFIED_SOURCE_PAIR', bound)
            a = P.save_ray(P.zero_ray()); a[1] = ['1', '0']
            witness = P.noncircular_witness(cells, a, P.log_spec('1'))
            self.assertIsNotNone(witness)
            self.assertEqual(C.verify_noncircularity(cells, a, P.log_spec('1'), witness['first_cell'], witness['second_cell'])['status'], 'VERIFIED_NONCIRCULARITY')

    def test_validation_prime_entry_boundaries_and_known_exclusions(self):
        draw = P.validation_draw(['2/3'], known_parents=[16384])
        self.assertEqual(len(draw['parents']), len(set(draw['parents'])))
        for item in draw['draws']:
            if item['kind'] == 'prime_entry':
                H, p = item['horizon_threshold'], item['prime']
                self.assertLess(P.OLD.P.T.rational_cutoff(H-1, '2/9'), p)
                self.assertGreaterEqual(P.OLD.P.T.rational_cutoff(H, '2/9'), p)
        chosen = draw['parents'][0]
        excluded = P.validation_draw(['2/3'], known_parents=[chosen])
        self.assertNotIn(chosen, excluded['parents'])
        self.assertTrue(any(x['u'] == chosen and x['status'] == 'KNOWN_PARENT_EXCLUDED' for x in excluded['draws']))

    def test_quadratic_vertex_fractional_calibration_and_prospective_resources(self):
        spec = P.log_spec('7/5'); mid = (Q(spec['lower'])+Q(spec['upper']))/2
        self.assertEqual(P.polynomial_range((mid*mid, -2*mid, Q(1)), spec)[0], 0)
        a = P.save_ray(P.zero_ray()); a[0] = ['0', '1']; a[1] = ['-1', '0']
        rows = {17: row(17, [1, 1, 0])}
        k = P.calibrate(rows, a, '53/47', spec)['kappa']
        self.assertEqual(C.verify_leaf(rows[17], a, k, '53/47', spec)['status'], 'CERTIFIED_FINITE')
        m = P.OLD.P.F.S.Meter(); m.reserve = lambda _: (_ for _ in ()).throw(MemoryError('synthetic cap'))
        with self.assertRaises(MemoryError): P.generate_frames([1, 7, 9], meter=m)
        with self.assertRaises(MemoryError): P.rank_frames(rows, [], '1', '1', spec, meter=m)
        with self.assertRaises(ValueError): P.validation_draw(['2'], maximum=10000000)

    def test_runner_independent_source_and_search_roundtrip(self):
        import run_mobius_symbolic_cover_080 as R
        kernel = [dict(divisor=4, weight='-1'), dict(divisor=5, weight='1')]
        norm = P.OLD.fixed_norm(kernel, [2, 3], 100)
        indices = P.OLD.inactive_coordinates(norm['folded_kernel'], '3/5', 100)
        meta = {'fixture': dict(fixed_kernel=kernel, primes=[2, 3], norm=norm,
            inactive_admissions={'3/5': {'indices': indices}})}
        with tempfile.TemporaryDirectory() as temp, patch.object(R, 'OUT', Path(temp)), patch.dict(R.SPEC,
                source_ids=['fixture'], base=100, q=['1'], exact_shortlist=1):
            (R.OUT/'source_metadata.json').write_text(json.dumps(meta))
            R.initialize_source(160)
            records = {}
            for u in (401, 480, 640):
                R.source_task((u, ['3/5']))
                item = json.loads((R.OUT/('source_'+str(u)+'.json')).read_text())['records']['fixture']['3/5']
                self.assertEqual(item['cell_admission']['status'], 'VERIFIED_CELLS')
                self.assertEqual(item['source_pair_admission']['status'], 'VERIFIED_SOURCE_PAIR')
                records[u] = item
            with patch.object(R, '_DISCOVERY', {('fixture', '3/5'): records}), patch.object(R, '_RULES',
                    {'fixture': {'coordinates': [1, 9]}}):
                result = R.search_task(('fixture', '3/5', 'promoted'))
                self.assertTrue(result['proposals'])
                for p in result['proposals']:
                    self.assertEqual(p['cover_admission']['status'], 'VERIFIED_CONDITIONAL_COVER')
                    self.assertFalse(p['cover_admission']['uniform_bound_proved'])

    def test_runner_watchdog_covers_serial_leaf_checks(self):
        import run_mobius_symbolic_cover_080 as R
        with patch.dict(R.SPEC, module_seconds=1):
            with self.assertRaises(TimeoutError): R.check_stage(time.monotonic()-2)
        def stop():
            raise TimeoutError('synthetic serial phase deadline')
        a = P.save_ray(P.zero_ray()); a[0] = ['1', '0']
        with self.assertRaises(TimeoutError):
            R.checked_leaves({17: row(17, [1])}, [a], ['1'], '1', P.log_spec('1'), watchdog=stop)


if __name__ == '__main__': unittest.main()
