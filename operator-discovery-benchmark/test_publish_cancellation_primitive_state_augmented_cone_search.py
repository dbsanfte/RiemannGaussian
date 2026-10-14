import unittest
import publish_cancellation_primitive_state_augmented_cone_search as P


def fixture():
    free = list(range(782, 1224))
    chart = dict(schema='primitive-state-augmented-cone-chart-v1', complete=True,
                 width=1224, original_width=1957, normalized_rows=[{}]*782,
                 pivot_columns=list(range(782)), free_indices=free)
    center = dict(schema='primitive-state-augmented-cone-center-v1', complete=True,
                  preserved_seed_free_coordinates=True, free_indices=free,
                  initial_free_vector=['0']*442, center_projected_vector=['0']*1224,
                  candidate_original_vector=['0']*1957)
    proposal = dict(complete=True, **P.FLAGS)
    endpoint = dict(complete=True, free_indices=free, final_free_vector=['0']*442,
                    final_projected_vector=['0']*1224,
                    candidate_original_vector=['-1']+['0']*1956, **P.FLAGS)
    exact = dict(full_original_rows_checked=5641, learned_rows_checked=3,
                 full_equations_checked=5644, endpoint_verified=True,
                 candidate_equations_verified=True, finite_candidate_feasible=False,
                 negative_scalar_count=1, psd_status='NOT_CHECKED_AFTER_SCALAR_REJECTION',
                 PSD_blocks_checked=0, PSD_failures=None)
    trace = dict(verified=True, complete=True, accepted_iterations=7)
    check = dict(verified=True, complete=True, endpoint_check=exact,
                 trace_check=trace, **P.FLAGS)
    review = dict(schema='primitive-state-augmented-cone-search-independent-review-v1',
                  all_passed=True, status='SCALAR_REJECTED', resource_failure=None,
                  chart_verified=True, center_verified=True, endpoint_verified=True,
                  candidate_equations_verified=True, finite_candidate_feasible=False,
                  independent_search_check=check,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000), **P.FLAGS)
    return review, chart, center, proposal, endpoint


class AugmentedPublication(unittest.TestCase):
    def test_complete_finite_rejection_is_not_global_admission(self):
        values = fixture()
        result = P.checked_outcome(*values)
        self.assertEqual(result['endpoint_check']['full_equations_checked'], 5644)
        self.assertFalse(values[0]['finite_candidate_feasible'])
        self.assertFalse(values[0]['RH_proved'])

    def test_every_learned_equation_is_required(self):
        for key, bad in (('full_original_rows_checked', 5640), ('learned_rows_checked', 1),
                         ('full_equations_checked', 5642)):
            values = fixture()
            values[0]['independent_search_check']['endpoint_check'][key] = bad
            with self.subTest(key=key), self.assertRaises(ValueError):
                P.checked_outcome(*values)

    def test_old_dimension_or_unverified_center_cannot_be_reused(self):
        for mutation in ('free', 'rows', 'center', 'trace'):
            values = fixture()
            if mutation == 'free':
                values[4]['final_free_vector'] += ['0', '0']
            elif mutation == 'rows':
                values[1]['normalized_rows'].pop()
            elif mutation == 'center':
                values[0]['center_verified'] = False
            else:
                values[0]['independent_search_check']['trace_check']['complete'] = False
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                P.checked_outcome(*values)

    def test_scalar_rejection_does_not_supply_psd_results(self):
        for key, bad in (('PSD_failures', 0), ('PSD_blocks_checked', 3),
                         ('negative_scalar_count', 0)):
            values = fixture()
            values[0]['independent_search_check']['endpoint_check'][key] = bad
            with self.subTest(key=key), self.assertRaises(ValueError):
                P.checked_outcome(*values)

    def test_scalar_success_requires_three_exact_blocks(self):
        values = fixture()
        values[0].update(status='CONE_CHECKED', finite_candidate_feasible=True)
        exact = values[0]['independent_search_check']['endpoint_check']
        exact.update(negative_scalar_count=0, psd_status='ALL_THREE_EXACT_BLOCKS_CHECKED',
                     PSD_blocks_checked=2, PSD_failures=0, finite_candidate_feasible=True)
        with self.assertRaises(ValueError):
            P.checked_outcome(*values)
        exact['PSD_blocks_checked'] = 3
        self.assertIsNotNone(P.checked_outcome(*values))
        values[0]['RH_proved'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(*values)

    def test_unknown_cannot_promote_retained_point_or_reset_budget(self):
        values = fixture()
        values[0].update(status='UNKNOWN', all_passed=False, endpoint_verified=False,
                         candidate_equations_verified=False, finite_candidate_feasible=None)
        self.assertIsNone(P.checked_outcome(*values))
        values[0]['endpoint_verified'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(*values)
        values = fixture()
        values[0]['joint_work']['total_work_reserve'] += 1
        with self.assertRaises(ValueError):
            P.checked_outcome(*values)


if __name__ == '__main__':
    unittest.main()
