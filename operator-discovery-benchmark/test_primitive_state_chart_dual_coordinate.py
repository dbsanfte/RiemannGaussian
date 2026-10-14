"""Tiny trajectories and exact restoration plumbing; no actual source model."""
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_coordinate as C

_BUDGETS = []
_ORIGINAL_BUDGET = C.Budget


class TrackedBudget(_ORIGINAL_BUDGET):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        _BUDGETS.append(self)


def setUpModule():
    global _PATCH
    _PATCH = patch.object(C, 'Budget', TrackedBudget)
    _PATCH.start()


def tearDownModule():
    _PATCH.stop()
    print('SYNTHETIC_WORK module=test_primitive_state_chart_dual_coordinate operations=' +
          str(sum(b.operations for b in _BUDGETS)))


def budget():
    return C.Budget(time.monotonic() + 30, 1000000)


def model(columns, rhs):
    return dict(columns=columns, rhs=rhs, rows=len(rhs), columns_count=len(columns),
                nonzeros=sum(map(len, columns)), active_columns=list(range(len(columns))),
                row_ids=list(range(len(rhs))), scaling={})


def reduction(rows, active):
    return dict(schema=C.REUSE.REDUCTION_SCHEMA, complete=True, status='REDUCED',
                input_columns=max(active) + 1, input_rows=len(rows), active_columns=active,
                final_rows=[dict(row_id=i, terms=[[j, str(q)] for j, q in sorted(row.items())],
                                rhs=str(rhs)) for i, (row, rhs) in enumerate(rows)],
                steps=[], forced_zero_columns=[], discarded_zero_target_columns=[])


def proposal(value, operations=120000):
    return C.coordinate_proposal(value, deadline=time.monotonic() + 30, max_operations=operations)


class CoordinateTests(unittest.TestCase):
    def assert_blocks(self, out):
        reserve = out['reservation']
        self.assertEqual(out['counts']['operations'], int(out['setup_charged']) * reserve['setup']
                         + out['sweeps_charged'] * reserve['sweep']
                         + out['refreshes_charged'] * reserve['refresh'])
        self.assertLessEqual(out['counts']['operations'], out['max_operations'])

    def test_exact_positive_scaling_and_original_column_ids(self):
        artifact = reduction([({1: F(2), 4: F(-1)}, F(4)),
                              ({1: F(6), 4: F(3)}, F(3))], [1, 4])
        out = C.build_model(artifact, budget())
        self.assertEqual(out['columns'], [{0: .5, 1: 1.0}, {0: -.5, 1: 1.0}])
        self.assertEqual(out['rhs'], [1.0, .5])
        self.assertEqual(out['active_columns'], [1, 4])
        self.assertEqual(out['nonzeros'], 4)
        self.assertTrue(out['scaling']['positive_exact'])
        self.assertEqual(out['scaling']['column_scale_max'], '2')

    def test_model_rejects_nonzero_underflow_without_solver(self):
        artifact = reduction([({0: F(1), 1: F(1, 2 ** 1100)}, F(1)),
                              ({1: F(1)}, F(0))], [0, 1])
        with patch('scipy.optimize.linprog', side_effect=AssertionError('no LP')):
            with self.assertRaises(OverflowError):
                C.build_model(artifact, budget())

    def test_dimension_only_reservation_is_maximal_and_refuses_short_budget(self):
        reserve = C.numerical_reservation(2, 3, 4, 120000)
        s = reserve['sweeps_per_phase']
        self.assertGreater(s, 0)
        self.assertLessEqual(reserve['total'], 120000)
        if s < 10000:
            next_total = reserve['setup'] + 17 * ((s + 1) * reserve['sweep']
                + (((s + 1 + 15) // 16) + 1) * reserve['refresh'])
            self.assertGreater(next_total, 120000)
        out = proposal(model([{0: 1.0}], [1.0]), 1)
        self.assertFalse(out['attempted'])
        self.assertFalse(out['complete'])
        self.assertEqual(out['coordinate_visits'], 0)
        self.assert_blocks(out)

    def test_seventeen_warm_start_phases_and_exact_scalar_update(self):
        out = proposal(model([{0: 1.0}], [1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(len(out['checkpoints']), 17)
        self.assertEqual(out['penalty_reference'], 1.0)
        self.assertEqual([p['penalty'] for p in out['checkpoints']],
                         [2.0 ** -e for e in range(1, 32, 2)] + [0.0])
        self.assertEqual(out['selected']['scaled_vector'], [1.0])
        self.assertEqual(out['selected']['phase'], 16)
        self.assertEqual(out['selected']['relative_residual'], 0.0)
        self.assertEqual(out['coordinate_visits'], out['sweeps_charged'])
        self.assertEqual(out['refreshes_charged'], 17)
        self.assertEqual(out['checkpoints'][0]['residual_norm'], .5)
        self.assert_blocks(out)

    def test_phase_end_and_periodic_fresh_residuals(self):
        out = proposal(model([{0: 1.0, 1: 1.0}, {0: 1.0, 1: .99}], [1.0, 0.0]), 240000)
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertTrue(any(p['completed_sweeps'] >= 16 for p in out['checkpoints']))
        self.assertEqual(out['refreshes_charged'], sum(p['completed_sweeps'] // 16 + 1
                                                     for p in out['checkpoints']))
        self.assertEqual(out['sweeps_charged'], sum(p['completed_sweeps'] for p in out['checkpoints']))
        self.assertEqual(out['coordinate_visits'], 2 * out['sweeps_charged'])
        self.assertLessEqual(out['nonzero_updates'], 4 * out['sweeps_charged'])
        self.assert_blocks(out)

    def test_zero_reference_no_change_and_no_eligible_checkpoint(self):
        out = proposal(model([{0: 1.0}], [-1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['penalty_reference'], 0.0)
        self.assertEqual(out['selected'], None)
        self.assertEqual(out['sweeps_charged'], 17)
        self.assertTrue(all(p['completed_sweeps'] == 1 and p['support_size'] == 0 for p in out['checkpoints']))
        self.assert_blocks(out)

    def test_strict_positive_support_keeps_tiny_coordinates(self):
        out = proposal(model([{0: 1.0}, {1: 1.0}], [1.0, 2.0 ** -50]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['selected']['support'], [0, 1])
        self.assertEqual(out['selected']['scaled_vector'], [1.0, 2.0 ** -50])
        self.assert_blocks(out)

    def test_nonfinite_or_zero_norm_rejects_before_trajectory(self):
        for value in (model([{0: 1.0}], [0.0]), model([{}], [1.0]),
                      model([{0: 1e-300}], [1.0]), model([{0: float('inf')}], [1.0])):
            out = proposal(value)
            self.assertFalse(out['complete'])
            self.assertEqual(out['checkpoints'], [])
            self.assertEqual(out['coordinate_visits'], 0)
            self.assert_blocks(out)

    def test_deadline_after_checkpoint_keeps_charged_partial_work(self):
        shape = model([{0: 1.0}], [1.0]); reserve = C.numerical_reservation(1, 1, 1, 120000)
        threshold = reserve['setup'] + 2 * reserve['sweep'] + reserve['refresh']
        class InterruptedBudget(TrackedBudget):
            def charge(self, n=1):
                super().charge(n)
                if n == 0 and self.operations > threshold:
                    raise TimeoutError('synthetic deadline after first phase')
        with patch.object(C, 'Budget', InterruptedBudget):
            out = proposal(shape)
        self.assertFalse(out['complete'])
        self.assertEqual(len(out['checkpoints']), 1)
        self.assertIsNone(out['selected'])
        self.assertEqual(out['sweeps_charged'], 3)
        self.assertEqual(out['refreshes_charged'], 1)
        self.assert_blocks(out)

    def test_search_lifts_all_selected_positions_and_exactly_restores_once(self):
        tiny = model([{0: -1.0}, {0: -1.0}], [-1.0])
        numeric = proposal(tiny)
        synthetic_model = dict(tiny, rows=302, columns_count=687,
            active_columns=[2, 5], row_ids=list(range(302)), scaling={})
        geometry = dict(free_indices=[], compression=dict(column_representatives=list(range(851))),
            responses=[dict(ray_index=j, terms=[[1224, '-2']] if j == 2 else []) for j in range(851)])
        artifact = reduction([({2: F(-2), 5: F(-2)}, F(-1))], [2, 5])
        with patch.object(C, 'build_model', return_value=synthetic_model), \
             patch.object(C, 'coordinate_proposal', return_value=numeric) as numerical, \
             patch.object(C.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(C.OLD, 'certify', return_value=dict(complete=True, pairing='-1')) as certify, \
             patch.object(C.OLD, 'exact_support_solve', wraps=C.OLD.exact_support_solve) as solve, \
             patch('hashlib.sha256', side_effect=AssertionError('no hashes')):
            out = C.search({}, {}, geometry, artifact, deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'CERTIFICATE_PROPOSED', out.get('reason'))
        self.assertEqual(numerical.call_count, 1)
        self.assertEqual(solve.call_count, 1)
        self.assertEqual(solve.call_args.args[3], [2])
        self.assertEqual(certify.call_args.args[5][2], F(1, 2))
        self.assertEqual(len(certify.call_args.args[5]), 851)
        self.assertEqual(set(out['stage_counts']), {'model', 'numerical', 'restoration'})

    def test_incomplete_numerics_cannot_restore_an_earlier_checkpoint(self):
        tiny = model([{0: 1.0}], [1.0]); numeric = proposal(tiny)
        numeric['complete'] = False; numeric['reason'] = 'synthetic interrupted trajectory'
        synthetic_model = dict(tiny, rows=302, columns_count=687)
        artifact = reduction([({0: F(1)}, F(1))], [0])
        with patch.object(C, 'build_model', return_value=synthetic_model), \
             patch.object(C, 'coordinate_proposal', return_value=numeric), \
             patch.object(C.OLD, 'exact_support_solve', side_effect=AssertionError('partial result forbidden')):
            out = C.search({}, {}, {}, artifact, deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertNotIn('restoration', out['stage_counts'])

    def test_model_failure_starts_no_numerical_stage(self):
        out = C.search({}, {}, {}, {}, deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertEqual(set(out['stage_counts']), {'model'})


if __name__ == '__main__':
    unittest.main()
