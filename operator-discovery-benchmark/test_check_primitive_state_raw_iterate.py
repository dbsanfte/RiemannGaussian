import copy
import unittest
import check_primitive_state_raw_iterate as C


def fixture():
    return dict(schema='primitive-state-solver-trace-v1', kind='primal',
        original_coordinate_map=dict(scalar_offset=0, scalar_count=2, source_column_order='identity',
            upper_triangle_order='row-major-a-then-b-a-through-n-minus-1',
            psd_blocks=[dict(name='G', size=2, indices=[2, 3, 4])]),
        original_system_metadata=dict(variables=5, objective=[1, 1, 1, 0, 1]),
        original_variable_ids=dict(scalar=3, matrices=dict(G=7)),
        canonical_variable_map={'7': 0, '3': 3},
        raw_solution=dict(x=[-1.0, 4.0, 2.0, -3.0, 5.0]),
        original_vector=[0.0, 5.0, -1.0, 4.0, 2.0])


class ReplayTests(unittest.TestCase):
    def test_negative_scalar_and_psd_coordinates_preserved(self):
        r = C.replay(fixture())
        self.assertEqual(r['original_vector'], [-3, 5, -1, 4, 2])
        self.assertEqual(r['changed_coordinate_indices'], [0])
        self.assertEqual(r['raw_objective'], 3)
        self.assertEqual(r['archived_objective'], 6)
        self.assertFalse(r['exact_admission'])

    def test_missing_nonfinite_and_bool_coordinates_rejected(self):
        for value in ([-1, 4], [-1, 4, 2, None, 5], [-1, 4, 2, float('nan'), 5], [-1, 4, 2, True, 5]):
            t = fixture(); t['raw_solution']['x'] = value
            with self.assertRaises(ValueError): C.replay(t)

    def test_canonical_slice_overlap_and_extra_variable_rejected(self):
        for starts in ({'7': 0, '3': 2}, {'7': 0, '3': 3, '9': 0}):
            t = fixture(); t['canonical_variable_map'] = starts
            with self.assertRaises(ValueError): C.replay(t)

    def test_unknown_export_changes_rejected(self):
        for index in range(5):
            t = fixture(); t['original_vector'][index] += .125
            with self.assertRaises(ValueError): C.replay(t)

    def test_omitted_or_reordered_psd_coordinate_rejected(self):
        for indices in ([2, 3], [2, 4, 3]):
            t = fixture(); t['original_coordinate_map']['psd_blocks'][0]['indices'] = indices
            with self.assertRaises(ValueError): C.replay(t)

    def test_source_is_unchanged(self):
        t = fixture(); before = copy.deepcopy(t); C.replay(t)
        self.assertEqual(t, before)

    def test_installed_cvxpy_projection_and_symmetric_order(self):
        import cvxpy as cp
        import numpy as np
        from cvxpy.reductions.cvx_attr2constr import recover_value_for_variable
        scalar = cp.Variable(2, nonneg=True)
        symmetric = cp.Variable((2, 2), symmetric=True)
        self.assertEqual(recover_value_for_variable(scalar, np.array([-3., 5.])).tolist(), [0., 5.])
        self.assertEqual(recover_value_for_variable(symmetric, np.array([-1., 4., 2.])).tolist(), [[-1., 4.], [4., 2.]])


if __name__ == '__main__':
    unittest.main()
