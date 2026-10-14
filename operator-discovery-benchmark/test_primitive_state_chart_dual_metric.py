"""Tiny accelerated trajectories and one mocked exact-restoration pipeline."""
from fractions import Fraction as F
import math
import time
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_metric as A

_BUDGETS = []
_ORIGINAL_BUDGET = A.Budget


class TrackedBudget(_ORIGINAL_BUDGET):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        _BUDGETS.append(self)


def setUpModule():
    global _PATCH
    _PATCH = patch.object(A, 'Budget', TrackedBudget)
    _PATCH.start()


def tearDownModule():
    _PATCH.stop()
    print('SYNTHETIC_WORK module=test_primitive_state_chart_dual_metric operations=' +
          str(sum(b.operations for b in _BUDGETS)))


def model(columns, rhs):
    return dict(columns=columns, rhs=rhs, rows=len(rhs), columns_count=len(columns),
                nonzeros=sum(map(len, columns)), active_columns=list(range(len(columns))),
                row_ids=list(range(len(rhs))), scaling={})


def proposal(value, operations=150000, resident_cells=0):
    return A.accelerated_proposal(value, deadline=time.monotonic() + 30,
                                  max_operations=operations, resident_cells=resident_cells)


def reduction():
    return dict(schema=A.REUSE.REDUCTION_SCHEMA, complete=True, status='REDUCED',
                input_columns=3, input_rows=1, active_columns=[2],
                final_rows=[dict(row_id=0, terms=[[2, '-2']], rhs='-1')],
                steps=[], forced_zero_columns=[], discarded_zero_target_columns=[0, 1])


class AcceleratedTests(unittest.TestCase):
    def assert_blocks(self, out):
        work = out['work_model']
        total = (int(out['setup_charged']) * work['setup']
                 + out['gradient_blocks'] * work['gradient']
                 + out['trial_blocks'] * work['trial']
                 + out['commit_blocks'] * work['commit']
                 + int(out['final_charged']) * work['final'])
        self.assertEqual(out['counts']['operations'], total)
        self.assertLessEqual(total, out['max_operations'])

    def test_work_model_and_unattempted_too_small_reservation(self):
        work = A.numerical_work_model(2, 3, 4)
        self.assertEqual(work['gradient'], 8 * 4 + 32 * 5 + 512)
        self.assertEqual(work['iteration_reserve'], work['gradient'] + 32 * work['trial'] + work['commit'])
        self.assertEqual(work['minimum_attempt'], work['setup'] + work['iteration_reserve'] + work['final'])
        out = proposal(model([{0: 1.0}], [1.0]), 1)
        self.assertFalse(out['attempted'])
        self.assertFalse(out['complete'])
        self.assertFalse(out['setup_charged'])
        self.assertEqual(out['checkpoints'], [])
        self.assertIsNone(out['initial_lipschitz'])
        self.assert_blocks(out)

    def test_reuses_exact032_scaling_and_stable_original_ids(self):
        self.assertIs(A.build_model, A.MODEL.build_model)
        b = A.Budget(time.monotonic() + 30, 1000000)
        value = A.build_model(reduction(), b)
        self.assertEqual(value['columns'], [{0: -1.0}])
        self.assertEqual(value['rhs'], [-.5])
        self.assertEqual(value['active_columns'], [2])
        self.assertTrue(value['scaling']['positive_exact'])

    def test_cold_start_exact_scalar_step_and_final_zero_diagnostic(self):
        value = model([{0: 1.0}], [1.0]); value['initial_vector'] = [77.0]
        before = dict(value); out = proposal(value)
        self.assertEqual(value, before)
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['stop_reason'], 'zero_reported_residual')
        self.assertEqual(len(out['checkpoints']), 1)
        self.assertEqual(out['selected']['scaled_vector'], [1.0])
        self.assertEqual(out['initial_lipschitz'], 1.0)
        self.assertEqual(out['final_diagnostic']['projected_gradient_norm'], 0.0)
        self.assertEqual(out['final_diagnostic']['iteration'], 1)
        self.assertTrue(out['final_charged'])
        self.assert_blocks(out)

    def test_correlated_columns_backtrack_and_keep_every_positive_weight(self):
        out = proposal(model([{0: 1.0}, {0: 1.0}], [1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['trial_blocks'], 2)
        self.assertEqual(out['checkpoints'][0]['backtracking_trials'], 2)
        self.assertEqual(out['checkpoints'][0]['lipschitz'], 2.0)
        self.assertEqual(out['selected']['scaled_vector'], [.5, .5])
        self.assertEqual(out['selected']['support'], [0, 1])
        self.assertEqual(out['gradient_blocks'], 1)
        self.assert_blocks(out)

    def test_diagonal_metric_balances_unequal_orthogonal_columns(self):
        out = proposal(model([{0: 1.0}, {1: 4.0}], [1.0, 1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['metric_diagonal'], [1.0, 16.0])
        self.assertEqual(out['initial_lipschitz'], 1.0)
        self.assertEqual(out['trial_blocks'], 1)
        self.assertEqual(out['stop_reason'], 'zero_reported_residual')
        self.assertEqual(out['selected']['scaled_vector'], [1.0, .25])
        self.assert_blocks(out)

    def test_final_mapping_uses_the_weighted_norm(self):
        value = model([{0: 1.0}, {0: 1.0, 1: 2.0}], [1.0, 3.0])
        work = A.numerical_work_model(2, 2, 3)
        out = proposal(value, work['minimum_attempt'])
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['stop_reason'], 'work_boundary')
        self.assertEqual(len(out['checkpoints']), 1)
        self.assertEqual(out['checkpoints'][0]['backtracking_trials'], 2)
        self.assertAlmostEqual(out['final_diagnostic']['projected_gradient_norm'],
                               2 * math.sqrt(.46), places=12)
        self.assertEqual(out['final_diagnostic']['mapping_metric'], 'diagonal column curvature')
        self.assert_blocks(out)

    def test_tiny_strict_positive_coordinate_is_not_thresholded(self):
        out = proposal(model([{0: 1.0}, {1: 1.0}], [1.0, 2.0 ** -50]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['selected']['support'], [0, 1])
        self.assertEqual(out['selected']['scaled_vector'], [1.0, 2.0 ** -50])
        self.assert_blocks(out)

    def test_periodic_restart_boundary_and_stationarity_are_only_diagnostics(self):
        out = proposal(model([{0: 1.0}], [1.0, 1.0]), 300000)
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['stop_reason'], 'work_boundary')
        self.assertGreaterEqual(len(out['checkpoints']), 64)
        self.assertEqual([p['iteration'] for p in out['checkpoints'] if p['momentum_restarted']], [64])
        self.assertEqual(out['selected']['iteration'], 1)
        self.assertGreater(out['final_diagnostic']['residual_norm'], 0)
        self.assertEqual(out['final_diagnostic']['projected_gradient_norm'], 0.0)
        self.assertGreater(out['counts']['operations'] + out['work_model']['iteration_reserve'], 300000)
        self.assertTrue(all(out[key] is False for key in A.FLAGS))
        operations = out['work_model']['setup']
        for checkpoint in out['checkpoints']:
            self.assertGreaterEqual(300000 - operations,
                out['work_model']['iteration_reserve'] + out['work_model']['final'])
            operations += (out['work_model']['gradient']
                + checkpoint['backtracking_trials'] * out['work_model']['trial']
                + out['work_model']['commit'])
            self.assertEqual(checkpoint['cumulative_operations'], operations)
        self.assert_blocks(out)

    def test_complete_zero_support_remains_ineligible(self):
        out = proposal(model([{0: 1.0}], [-1.0]), 120000)
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['stop_reason'], 'work_boundary')
        self.assertIsNone(out['selected'])
        self.assertTrue(all(p['support_size'] == 0 for p in out['checkpoints']))
        self.assert_blocks(out)

    def test_nonfinite_ratio_is_rejected_before_projection_can_hide_it(self):
        out = proposal(model([{0: -1e-160}], [1e160]))
        self.assertFalse(out['complete'])
        self.assertEqual(out['checkpoints'], [])
        self.assertEqual(out['trial_blocks'], 1)
        self.assertEqual(out['commit_blocks'], 0)
        self.assertIn('ratio', out['reason'])
        self.assertIsNone(out['selected'])
        self.assert_blocks(out)

    def test_invalid_target_norm_and_live_cells_keep_setup_accounting(self):
        for value, cells in ((model([{0: 1.0}], [0.0]), 0),
                             (model([{0: 1.0}], [1.0]), 6000000)):
            out = proposal(value, resident_cells=cells)
            self.assertFalse(out['complete'])
            self.assertTrue(out['setup_charged'])
            self.assertEqual(out['gradient_blocks'], 0)
            self.assert_blocks(out)

    def test_partial_commit_cannot_append_a_checkpoint(self):
        work = A.numerical_work_model(1, 1, 1)
        class InterruptedCommit(TrackedBudget):
            def charge(self, n=1):
                super().charge(n)
                if n == work['commit']:
                    raise TimeoutError('synthetic partial commit')
        with patch.object(A, 'Budget', InterruptedCommit):
            out = proposal(model([{0: 1.0}], [1.0]))
        self.assertFalse(out['complete'])
        self.assertEqual(out['checkpoints'], [])
        self.assertEqual(out['commit_blocks'], 1)
        self.assertIsNone(out['selected'])
        self.assert_blocks(out)

    def test_final_failure_clears_selected_after_a_complete_checkpoint(self):
        work = A.numerical_work_model(1, 1, 1)
        class InterruptedFinal(TrackedBudget):
            def charge(self, n=1):
                super().charge(n)
                if n == work['final']:
                    raise TimeoutError('synthetic final diagnostic interruption')
        with patch.object(A, 'Budget', InterruptedFinal):
            out = proposal(model([{0: 1.0}], [1.0]))
        self.assertFalse(out['complete'])
        self.assertEqual(len(out['checkpoints']), 1)
        self.assertTrue(out['final_charged'])
        self.assertIsNone(out['final_diagnostic'])
        self.assertIsNone(out['selected'])
        self.assert_blocks(out)

    def test_search_one_exact_restore_on_all_original_saved_responses(self):
        tiny = model([{0: -1.0}], [-.5]); numeric = proposal(tiny)
        synthetic_model = dict(tiny, rows=302, columns_count=687, active_columns=[2])
        geometry = dict(free_indices=[], compression=dict(column_representatives=list(range(851))),
            responses=[dict(ray_index=j, terms=[[1224, '-2']] if j == 2 else []) for j in range(851)])
        with patch.object(A, 'build_model', return_value=synthetic_model), \
             patch.object(A, 'accelerated_proposal', return_value=numeric) as numerical, \
             patch.object(A.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(A.OLD, 'exact_support_solve', wraps=A.OLD.exact_support_solve) as solve, \
             patch.object(A.OLD, 'certify', return_value=dict(complete=True, pairing='-1')) as certify, \
             patch('hashlib.sha256', side_effect=AssertionError('no hashes')):
            out = A.search({}, {}, geometry, reduction(), deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'CERTIFICATE_PROPOSED', out.get('reason'))
        self.assertEqual(out['route'], 'metric_acceleration')
        self.assertEqual(numerical.call_count, 1)
        self.assertEqual(solve.call_count, 1)
        self.assertEqual(solve.call_args.args[3], [2])
        self.assertEqual(certify.call_args.args[5][2], F(1, 2))
        self.assertEqual(len(certify.call_args.args[5]), 851)
        self.assertEqual(set(out['stage_counts']), {'model', 'numerical', 'restoration'})

    def test_incomplete_trajectory_never_restores_and_model_failure_is_unknown(self):
        tiny = model([{0: 1.0}], [1.0]); numeric = proposal(tiny)
        numeric['complete'] = False; numeric['selected'] = None
        synthetic_model = dict(tiny, rows=302, columns_count=687)
        with patch.object(A, 'build_model', return_value=synthetic_model), \
             patch.object(A, 'accelerated_proposal', return_value=numeric), \
             patch.object(A.OLD, 'exact_support_solve', side_effect=AssertionError('partial result forbidden')):
            out = A.search({}, {}, {}, reduction(), deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertNotIn('restoration', out['stage_counts'])
        failed = A.search({}, {}, {}, {}, deadline=time.monotonic() + 30)
        self.assertEqual(failed['status'], 'UNKNOWN')
        self.assertEqual(set(failed['stage_counts']), {'model'})


if __name__ == '__main__':
    unittest.main()
