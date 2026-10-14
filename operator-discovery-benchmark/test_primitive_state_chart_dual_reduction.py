"""Small exact proof-rule tests and mocked native/restoration plumbing.

No real030 geometry is loaded and no native solver is invoked. All producer
budgets and explicitly returned mock native work are metered per invocation.
"""
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_reduction as R

_BUDGETS = []
_MOCK_NATIVE_WORK = 0
_ORIGINAL_BUDGET = R.Budget


class TrackedBudget(_ORIGINAL_BUDGET):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        _BUDGETS.append(self)


def setUpModule():
    global _PATCH
    _PATCH = patch.object(R, 'Budget', TrackedBudget)
    _PATCH.start()


def tearDownModule():
    _PATCH.stop()
    total = sum(b.operations for b in _BUDGETS) + _MOCK_NATIVE_WORK
    print('SYNTHETIC_WORK module=test_primitive_state_chart_dual_reduction operations=' + str(total))


def budget(max_operations=1000000):
    return R.Budget(time.monotonic() + 30, max_operations)


def plumbing_geometry():
    """Deliberately sparse317x695 premise for call binding, never admission."""
    return dict(schema=R.NATIVE.GEOMETRY_SCHEMA, complete=True, free_indices=[],
                responses=[dict(ray_index=j, terms=[[1224, '-2']] if j == 0 else [])
                           for j in range(851)],
                compression=dict(column_representatives=list(range(695)),
                    row_representatives=[*range(316), 1224],
                    compressed_columns=[[[1224, '-2']], [[1224, '-3']]] + [[] for _ in range(693)],
                    compressed_rhs=[[1224, '-1']]))


def native_result(vector, *, success=True, status=0, resource_failure=None):
    global _MOCK_NATIVE_WORK
    _MOCK_NATIVE_WORK += 17
    result = dict(success=success, status=status, attempted=True, scaled_vector=vector,
                  counts=dict(operations=17, peak_live_cells=4, maximum_rational_bits=2))
    if resource_failure is not None:
        result['resource_failure'] = resource_failure
    return result


class ReductionTests(unittest.TestCase):
    def test_saved_compression_positional_ids_and_rhs(self):
        geometry = dict(schema=R.NATIVE.GEOMETRY_SCHEMA, complete=True,
                        compression=dict(column_representatives=[4, 7], row_representatives=[8, 1224],
                        compressed_columns=[[[8, '2'], [1224, '-3']], [[8, '-1']]],
                        compressed_rhs=[[1224, '-1']]))
        rows, n = R.input_model(geometry, budget())
        self.assertEqual(n, 2)
        self.assertEqual(rows, {0: {0: F(2), 1: F(-1)}, 1: {0: F(-3), 2: F(-1)}})
        geometry['compression']['compressed_columns'][0].append([8, '1'])
        with self.assertRaises(ValueError):
            R.input_model(geometry, budget())

    def test_positive_and_negative_sign_closure_and_restricted_contradiction(self):
        rows = {0: {0: F(1), 1: F(2)}, 1: {1: F(1), 2: F(-1)},
                2: {2: F(1), 3: F(1)}}
        before = {i: dict(row) for i, row in rows.items()}
        result = R.reduce_system(rows, 3, budget())
        self.assertEqual(rows, before)
        self.assertEqual(result['forced_zero_columns'], [0, 1, 2])
        self.assertEqual(result['discarded_zero_target_columns'], [])
        self.assertEqual(result['status'], 'RESTRICTED_SYSTEM_INCONSISTENT')
        self.assertEqual(result['contradiction_row'], 2)
        self.assertEqual(result['final_rows'], [dict(row_id=2, terms=[], rhs='1')])
        self.assertEqual([s['columns'] for s in result['steps'] if s['kind'] == 'force_zero'], [[0, 1], [2]])
        self.assertTrue(result['complete'])
        self.assertTrue(all(result[k] is False for k in R.FLAGS))

    def test_homogeneous_closed_component_is_chosen_zero_not_forced(self):
        result = R.reduce_system({0: {0: F(1), 1: F(-1)},
                                  1: {2: F(1), 3: F(-1), 5: F(1)}, 2: {}}, 5, budget())
        self.assertEqual(result['forced_zero_columns'], [])
        self.assertEqual(result['discarded_zero_target_columns'], [0, 1, 4])
        self.assertEqual(result['active_columns'], [2, 3])
        discarded = [s for s in result['steps'] if s['kind'] == 'discard_homogeneous_components']
        self.assertEqual(discarded, [dict(kind='discard_homogeneous_components', columns=[0, 1, 4], rows=[0])])
        self.assertTrue(any(s == dict(kind='drop_zero_rows', rows=[2]) for s in result['steps']))
        self.assertTrue(result['fixed_point'])
        self.assertLessEqual(result['rounds'], 8)

    def test_markowitz_augmented_forward_transform_is_exact(self):
        result = R.reduce_system({0: {0: F(2), 1: F(3), 2: F(1)},
                                  1: {0: F(4), 1: F(5), 2: F(1)}}, 2, budget())
        self.assertEqual(result['steps'][0], dict(kind='pivot', row_id=0, column=0, eliminate=[1]))
        self.assertEqual(result['steps'][1], dict(kind='pivot', row_id=1, column=1, eliminate=[]))
        self.assertEqual(result['final_rows'], [dict(row_id=0, terms=[[0, '1'], [1, '3/2']], rhs='1/2'),
                                              dict(row_id=1, terms=[[1, '1']], rhs='1')])
        self.assertEqual(result['forced_zero_columns'], [])
        self.assertEqual(result['active_columns'], [0, 1])
        self.assertEqual(result['status'], 'REDUCED')

    def test_elimination_can_expose_a_new_force_zero_row(self):
        result = R.reduce_system({0: {0: F(1), 1: F(-1), 2: F(1)},
                                  1: {0: F(1), 1: F(-1), 2: F(-1)},
                                  2: {1: F(1), 3: F(-1), 4: F(1)}}, 4, budget())
        kinds = [s['kind'] for s in result['steps']]
        self.assertIn(2, result['forced_zero_columns'])
        self.assertLess(kinds.index('pivot'), kinds.index('force_zero'))
        self.assertEqual(result['active_columns'], [0, 1, 3])
        self.assertGreaterEqual(result['rounds'], 2)

    def test_empty_system_is_a_complete_zero_extension(self):
        result = R.reduce_system({}, 3, budget())
        self.assertEqual(result['final_rows'], [])
        self.assertEqual(result['discarded_zero_target_columns'], [0, 1, 2])
        self.assertEqual(result['forced_zero_columns'], [])
        self.assertEqual(result['active_columns'], [])
        self.assertTrue(result['fixed_point'])

    def test_incomplete_resource_failure_is_never_an_artifact(self):
        with self.assertRaises(OverflowError):
            R.reduce_system({0: {0: F(1)}}, 1, budget(1))
        out = R.search({}, {}, {}, deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertFalse(out['reduction_complete'])
        self.assertEqual(set(out['stage_counts']), {'reduction'})

    def test_one_native_support_lifts_and_restores_on_saved_responses(self):
        saved = []; events = []; geometry = plumbing_geometry()
        def propose(*args, **kwargs):
            self.assertEqual(events[-1], 'reduction_complete')
            self.assertEqual(len(saved), 1)
            self.assertEqual(kwargs['max_operations'], 160000000)
            self.assertGreater(kwargs['resident_cells'], 0)
            self.assertEqual(args[0], [{316: F(1)}, {316: F(3, 2)}])
            self.assertEqual(args[1], {316: F(1, 2)})
            self.assertEqual(args[2], [316])
            return native_result([0.5, 0.0])
        def certificate(rows, width, free, retained, rays, alpha, b):
            self.assertEqual(width, 1224)
            self.assertEqual(len(alpha), 851)
            self.assertEqual(alpha[0], F(1, 2))
            self.assertEqual(alpha[1:], [F(0)] * 850)
            return dict(schema=R.OLD.CERTIFICATE_SCHEMA, complete=True, pairing='-1', alpha=list(map(str, alpha)))
        with patch.object(R.NATIVE, 'native_proposal', side_effect=propose) as native, \
             patch.object(R.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(R.OLD, 'certify', side_effect=certificate) as certify, \
             patch.object(R.OLD, 'coordinate_responses', side_effect=AssertionError('reuse saved responses')), \
             patch('hashlib.sha256', side_effect=AssertionError('no hashes')):
            out = R.search({}, {}, geometry, deadline=time.monotonic() + 30,
                           checkpoint=lambda p: events.append(p['phase']), save_reduction=saved.append)
        self.assertEqual(out['status'], 'CERTIFICATE_PROPOSED', out.get('reason'))
        self.assertEqual(out['route'], 'reduced_lp')
        self.assertEqual(native.call_count, 1)
        self.assertEqual(certify.call_count, 1)
        self.assertEqual(out['restoration_stats']['support'], [0])
        self.assertEqual(set(out['stage_counts']), {'reduction', 'native', 'restoration'})
        self.assertEqual(saved[0]['active_columns'], [0, 1])

    def test_failed_native_still_saves_complete_reduction(self):
        saved = []
        with patch.object(R.NATIVE, 'native_proposal', return_value=native_result(None, success=False, status=1,
                                                                                resource_failure='bounded native stop')) as solve, \
             patch.object(R.OLD, 'exact_support_solve', side_effect=AssertionError('no restoration')):
            out = R.search({}, {}, plumbing_geometry(), deadline=time.monotonic() + 30, save_reduction=saved.append)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertTrue(out['reduction_complete'])
        self.assertEqual(len(saved), 1)
        self.assertEqual(solve.call_count, 1)
        self.assertEqual(set(out['stage_counts']), {'reduction', 'native'})

    def test_all_positive_native_support_exceeding_reduced_rows_is_retained(self):
        with patch.object(R.NATIVE, 'native_proposal', return_value=native_result([0.25, 0.25])), \
             patch.object(R.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(R.OLD, 'certify', return_value=dict(complete=True, pairing='-1')):
            out = R.search({}, {}, plumbing_geometry(), deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'CERTIFICATE_PROPOSED', out.get('reason'))
        self.assertEqual(out['native_support'], [0, 1])
        self.assertEqual(out['restoration_stats']['support'], [0, 1])
        self.assertEqual(out['restoration_stats']['free_support_coordinates'], [1])

    def test_native_support_over443_is_rejected_without_trimming(self):
        artifact = dict(schema=R.REDUCTION_SCHEMA, complete=True, input_rows=317, input_columns=695,
                        active_columns=list(range(444)), forced_zero_columns=[],
                        discarded_zero_target_columns=list(range(444, 695)), steps=[], rounds=1,
                        fixed_point=True, status='REDUCED', contradiction_row=None,
                        final_rows=[dict(row_id=316, terms=[[i, '1'] for i in range(444)], rhs='-1')],
                        policy=R.POLICY, **R.FLAGS)
        with patch.object(R, 'reduce_system', return_value=artifact), \
             patch.object(R.NATIVE, 'native_proposal', return_value=native_result([1.0] * 444)), \
             patch.object(R.OLD, 'exact_support_solve', side_effect=AssertionError('support must not be trimmed')):
            out = R.search({}, {}, plumbing_geometry(), deadline=time.monotonic() + 30)
        self.assertEqual(out['status'], 'NONCERTIFIED')
        self.assertEqual(len(out['native_support']), 444)
        self.assertNotIn('restoration', out['stage_counts'])
        self.assertIn('443', out['reason'])

    def test_restoration_failure_preserves_complete_reduction_and_counts(self):
        saved = []
        with patch.object(R.NATIVE, 'native_proposal', return_value=native_result([0.5, 0.0])), \
             patch.object(R.OLD, 'decode_chart', return_value=({}, [], [])), \
             patch.object(R.OLD, 'exact_support_solve', side_effect=ValueError('synthetic exact rejection')):
            out = R.search({}, {}, plumbing_geometry(), deadline=time.monotonic() + 30, save_reduction=saved.append)
        self.assertEqual(out['status'], 'NONCERTIFIED')
        self.assertTrue(out['reduction_complete'])
        self.assertEqual(out['restoration_stats']['support'], [0])
        self.assertGreater(out['stage_counts']['restoration']['operations'], 0)
        self.assertEqual(len(saved), 1)


if __name__ == '__main__':
    unittest.main()
