"""Tiny coupled face solves and mock archive/identity plumbing only."""
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_active as A

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
    print('SYNTHETIC_WORK module=test_primitive_state_chart_dual_active operations=' +
          str(sum(b.operations for b in _BUDGETS)))


def model(columns, rhs):
    return dict(columns=columns, rhs=rhs, rows=len(rhs), columns_count=len(columns),
                nonzeros=sum(map(len, columns)), active_columns=list(range(len(columns))),
                row_ids=list(range(len(rhs))), scaling={})


def proposal(value, initial=None, operations=150000, resident_cells=0):
    return A.active_set_proposal(value, initial, deadline=time.monotonic() + 30,
                                 max_operations=operations, resident_cells=resident_cells)


def reduction():
    return dict(schema=A.REUSE.REDUCTION_SCHEMA, complete=True, status='REDUCED',
                input_columns=3, input_rows=1, active_columns=[2],
                final_rows=[dict(row_id=0, terms=[[2, '-2']], rhs='-1')],
                steps=[], forced_zero_columns=[], discarded_zero_target_columns=[0, 1])


def seed(vector):
    return dict(schema=A.MODEL.SCHEMA, numerical=dict(schema=A.MODEL.NUMERICAL_SCHEMA,
        complete=True, selected=dict(scaled_vector=vector, relative_residual=999.0)))


class ActiveFaceTests(unittest.TestCase):
    def assert_blocks(self, out):
        work = out['work_model']
        total = (int(out['setup_charged']) * work['setup']
                 + out['gradient_blocks'] * work['gradient']
                 + int(out['final_charged']) * work['final'])
        for face in out['faces']:
            face_work = A.face_work_model(out['rows'], len(face['active']), face['nonzeros'])
            total += (int(face['setup_charged']) * face_work['setup']
                      + face['cg_blocks'] * face_work['cg_step']
                      + int(face['commit_charged']) * work['commit'])
        self.assertEqual(out['counts']['operations'], total)
        self.assertLessEqual(total, out['max_operations'])

    def test_full_and_face_work_and_unattempted_short_reservation(self):
        work = A.numerical_work_model(3, 4, 7)
        face_work = A.face_work_model(3, 2, 4)
        self.assertEqual(work['iteration_reserve'], work['gradient'] + work['face_setup_full']
                         + work['cg_limit_full'] * work['cg_step_full'] + work['commit'])
        self.assertEqual(face_work, dict(setup=8 * 4 + 48 * 5 + 1024,
                                       cg_step=12 * 4 + 64 * 5 + 1024, cg_limit=4))
        out = proposal(model([{0: 1.0}], [1.0]), operations=1)
        self.assertFalse(out['attempted'])
        self.assertFalse(out['setup_charged'])
        self.assertFalse(out['complete'])
        self.assertEqual(out['checkpoints'], [])
        self.assertIsNone(out['initial_vector'])
        self.assert_blocks(out)

    def test_reuses_exact032_scaling_and_original_retained_ids(self):
        self.assertIs(A.build_model, A.MODEL.build_model)
        b = A.Budget(time.monotonic() + 30, 1000000)
        value = A.build_model(reduction(), b)
        self.assertEqual(value['columns'], [{0: -1.0}])
        self.assertEqual(value['rhs'], [-.5])
        self.assertEqual(value['active_columns'], [2])

    def test_initial_exact_seed_wins_checkpoint_zero_without_a_face(self):
        out = proposal(model([{0: 1.0}], [1.0]), [1.0])
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['selected']['iteration'], 0)
        self.assertEqual(out['stop_reason'], 'zero_reported_residual')
        self.assertEqual(out['gradient_blocks'], 0)
        self.assertEqual(out['faces'], [])
        self.assertEqual(out['metric_diagonal'], [1.0])
        self.assertEqual(out['checkpoints'][0]['cumulative_operations'], out['work_model']['setup'])
        self.assertEqual(out['final_diagnostic']['projected_gradient_norm'], 0)
        self.assert_blocks(out)

    def test_coupled_negative_face_damps_then_refines_the_survivor(self):
        value = model([{0: 1.0}, {0: 1.0, 1: 1.0}], [0.0, 1.0])
        initial = [1.0, 1.0]; out = proposal(value, initial)
        self.assertEqual(initial, [1.0, 1.0])
        self.assertTrue(out['complete'], out.get('reason'))
        first, refined = out['faces'][:2]
        self.assertEqual(first['mode'], 'initial_face')
        self.assertEqual(first['active'], [0, 1])
        self.assertTrue(first['damped'])
        self.assertAlmostEqual(first['step_fraction'], .5)
        self.assertEqual(first['boundary_hits'], [0])
        self.assertEqual(first['surviving_support'], [1])
        self.assertEqual(refined['mode'], 'refine_face')
        self.assertEqual(refined['active'], [1])
        self.assertIsNone(refined['entered'])
        self.assertEqual(out['selected']['support'], [1])
        self.assertAlmostEqual(out['selected']['scaled_vector'][1], .5)
        self.assertEqual(out['stop_reason'], 'no_positive_inactive_correlation')
        self.assertEqual(out['gradient_blocks'], len(out['faces']) + 1)
        self.assert_blocks(out)

    def test_alpha_one_zero_boundary_still_schedules_refinement(self):
        out = proposal(model([{0: 1.0}, {1: 1.0}], [0.0, 1.0, 1.0]), [1.0, 1.0])
        self.assertTrue(out['complete'], out.get('reason'))
        first, refined = out['faces'][:2]
        self.assertTrue(first['damped'])
        self.assertEqual(first['step_fraction'], 1.0)
        self.assertEqual(first['boundary_hits'], [0])
        self.assertEqual(first['surviving_support'], [1])
        self.assertEqual(refined['mode'], 'refine_face')
        self.assertEqual(refined['cg_stop'], 'zero_normal_residual')
        self.assertEqual(refined['cg_blocks'], 0)
        self.assertEqual(refined['cg_steps_completed'], 0)
        self.assert_blocks(out)

    def test_entry_ties_use_smaller_index_and_actual_small_face_cost(self):
        out = proposal(model([{0: 1.0}, {0: 1.0}], [1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        face = out['faces'][0]
        self.assertEqual(face['mode'], 'enter_column')
        self.assertEqual(face['entered'], 0)
        self.assertEqual(face['entry_score'], 1.0)
        self.assertEqual(face['active'], [0])
        self.assertEqual(face['nonzeros'], 1)
        self.assertEqual(face['cg_limit'], 2)
        self.assertEqual(out['selected']['scaled_vector'], [1.0, 0.0])
        self.assertLess(A.face_work_model(1, 1, 1)['setup'], out['work_model']['face_setup_full'])
        self.assert_blocks(out)

    def test_all_positive_tiny_weight_is_preserved(self):
        out = proposal(model([{0: 1.0}, {1: 1.0}], [1.0, 2.0 ** -50]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['selected']['support'], [0, 1])
        self.assertEqual(out['selected']['scaled_vector'], [1.0, 2.0 ** -50])
        self.assertEqual([f['entered'] for f in out['faces']], [0, 1])
        self.assert_blocks(out)

    def test_initial_stationary_face_has_zero_cg_steps_and_only_diagnostic_stop(self):
        out = proposal(model([{0: 1.0}], [1.0, 1.0]), [1.0])
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['selected']['iteration'], 0)
        self.assertEqual(out['faces'][0]['cg_stop'], 'zero_normal_residual')
        self.assertEqual(out['faces'][0]['cg_blocks'], 0)
        self.assertEqual(out['stop_reason'], 'no_positive_inactive_correlation')
        self.assertGreater(out['final_diagnostic']['residual_norm'], 0)
        self.assertEqual(out['final_diagnostic']['projected_gradient_norm'], 0)
        self.assertTrue(all(out[key] is False for key in A.FLAGS))
        self.assert_blocks(out)

    def test_underflowed_curvature_commits_then_stops_with_charged_attempt(self):
        out = proposal(model([{0: 1.0}, {0: 1.0, 1: 1e-100}], [0.0, 1.0]), [1.0, 1.0])
        self.assertTrue(out['complete'], out.get('reason'))
        face = out['faces'][0]
        self.assertEqual(face['cg_stop'], 'zero_curvature')
        self.assertEqual(face['cg_blocks'], face['cg_steps_completed'] + 1)
        self.assertTrue(face['complete'])
        self.assertEqual(out['stop_reason'], 'krylov_breakdown')
        self.assertTrue(out['final_charged'])
        self.assert_blocks(out)

    def test_work_boundary_preserves_final_reservation_and_guard_ledger(self):
        value = model([{0: 1.0}], [1.0, 1.0])
        work = A.numerical_work_model(2, 1, 1)
        out = proposal(value, operations=work['minimum_attempt'])
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['stop_reason'], 'work_boundary')
        self.assertEqual(len(out['faces']), 1)
        self.assertGreater(out['counts']['operations'] + work['iteration_reserve'], out['max_operations'])
        self.assertEqual(out['faces'][0]['cumulative_operations'], out['checkpoints'][1]['cumulative_operations'])
        self.assert_blocks(out)

    def test_no_positive_entry_is_a_charged_terminal_gradient_without_face(self):
        out = proposal(model([{0: 1.0}], [-1.0]))
        self.assertTrue(out['complete'], out.get('reason'))
        self.assertEqual(out['gradient_blocks'], 1)
        self.assertEqual(out['faces'], [])
        self.assertEqual(out['stop_reason'], 'no_positive_inactive_correlation')
        self.assertIsNone(out['selected'])
        self.assert_blocks(out)

    def test_nonfinite_preconditioner_and_live_failure_keep_setup_charges(self):
        for value, initial, cells in ((model([{0: -1e-160}], [1e160]), None, 0),
                                      (model([{0: 1.0}], [1.0]), [-1.0], 0),
                                      (model([{0: 1.0}], [1.0]), None, 6000000)):
            out = proposal(value, initial, resident_cells=cells)
            self.assertFalse(out['complete'])
            self.assertTrue(out['setup_charged'])
            self.assertIsNone(out['selected'])
            self.assert_blocks(out)

    def test_partial_cg_and_partial_commit_never_append_a_face_checkpoint(self):
        face_work = A.face_work_model(1, 1, 1)
        work = A.numerical_work_model(1, 1, 1)
        for interrupted_kind in ('cg', 'commit'):
            class InterruptedBudget(TrackedBudget):
                equal_setup_commit = 0
                def charge(self, amount=1):
                    super().charge(amount)
                    if amount == work['commit']:
                        self.equal_setup_commit += 1
                    if (interrupted_kind == 'cg' and amount == face_work['cg_step']) or (
                            interrupted_kind == 'commit' and amount == work['commit']
                            and self.equal_setup_commit == 2):
                        raise TimeoutError('synthetic interrupted face block')
            with patch.object(A, 'Budget', InterruptedBudget):
                out = proposal(model([{0: 1.0}], [1.0]))
            self.assertFalse(out['complete'])
            self.assertEqual(len(out['checkpoints']), 1)
            self.assertEqual(len(out['faces']), 1)
            self.assertFalse(out['faces'][0]['complete'])
            self.assertIsNone(out['selected'])
            self.assert_blocks(out)

    def test_partial_final_clears_a_selected_initial_checkpoint(self):
        work = A.numerical_work_model(1, 1, 1)
        class InterruptedFinal(TrackedBudget):
            def charge(self, amount=1):
                super().charge(amount)
                if amount == work['final']:
                    raise TimeoutError('synthetic final diagnostic interruption')
        with patch.object(A, 'Budget', InterruptedFinal):
            out = proposal(model([{0: 1.0}], [1.0]), [1.0])
        self.assertFalse(out['complete'])
        self.assertEqual(len(out['checkpoints']), 1)
        self.assertTrue(out['final_charged'])
        self.assertIsNone(out['final_diagnostic'])
        self.assertIsNone(out['selected'])
        self.assert_blocks(out)

    def test_search_validates_seed_and_restores_full_original_support_once(self):
        tiny = model([{0: -1.0}], [-.5]); numeric = proposal(tiny, [.1])
        synthetic_model = dict(tiny, rows=302, columns_count=687, active_columns=[2])
        archive = seed([.1] + [0.0] * 686)
        geometry = dict(free_indices=[], compression=dict(column_representatives=list(range(851))),
            responses=[dict(ray_index=j, terms=[[1224, '-2']] if j == 2 else []) for j in range(851)])
        with patch.object(A, 'build_model', return_value=synthetic_model), \
             patch.object(A, 'active_set_proposal', return_value=numeric) as numerical, \
             patch.object(A.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(A.OLD, 'exact_support_solve', wraps=A.OLD.exact_support_solve) as solve, \
             patch.object(A.OLD, 'certify', return_value=dict(complete=True, pairing='-1')) as certify, \
             patch('hashlib.sha256', side_effect=AssertionError('no hashes')):
            out = A.search({}, {}, geometry, reduction(), archive, deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'CERTIFICATE_PROPOSED', out.get('reason'))
        self.assertEqual(out['route'], 'active_set')
        self.assertEqual(numerical.call_args.args[1], archive['numerical']['selected']['scaled_vector'])
        self.assertEqual(solve.call_count, 1)
        self.assertEqual(solve.call_args.args[3], [2])
        self.assertEqual(certify.call_args.args[5][2], F(1, 2))
        self.assertEqual(len(certify.call_args.args[5]), 851)
        self.assertEqual(set(out['stage_counts']), {'model', 'numerical', 'restoration'})

    def test_bad_seed_or_incomplete_numerics_cannot_restore(self):
        tiny = model([{0: 1.0}], [1.0]); numeric = proposal(tiny)
        synthetic_model = dict(tiny, rows=302, columns_count=687)
        numeric['complete'] = False; numeric['selected'] = None
        with patch.object(A, 'build_model', return_value=synthetic_model), \
             patch.object(A, 'active_set_proposal', return_value=numeric), \
             patch.object(A.OLD, 'exact_support_solve', side_effect=AssertionError('partial or bad seed forbidden')):
            bad = A.search({}, {}, {}, reduction(), seed([0.0]), deadline=time.monotonic() + 30)
            incomplete = A.search({}, {}, {}, reduction(), seed([0.0] * 687), deadline=time.monotonic() + 30)
        self.assertEqual(bad['status'], 'UNKNOWN')
        self.assertEqual(set(bad['stage_counts']), {'model'})
        self.assertEqual(incomplete['status'], 'UNKNOWN')
        self.assertNotIn('restoration', incomplete['stage_counts'])


if __name__ == '__main__':
    unittest.main()
