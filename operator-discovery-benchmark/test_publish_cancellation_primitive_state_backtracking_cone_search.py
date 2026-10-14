import copy
import unittest
import publish_cancellation_primitive_state_backtracking_cone_search as P


def fixture(feasible=False):
    check = dict(verified=True, complete=True, endpoint_verified=True,
                 candidate_equations_verified=True, feedback_row_verified=True,
                 chart_used_without_old_tape_replay=True, trace_exports_checked=True,
                 full_original_rows_checked=5641, finite_candidate_feasible=feasible,
                 accepted_iterations=2, stop_reason='iteration_limit', **P.FLAGS)
    review = dict(schema='primitive-state-backtracking-cone-search-independent-review-v1',
                  status='ENDPOINT_CHECKED', all_passed=True, independent_search_check=check,
                  endpoint_verified=True, candidate_equations_verified=True,
                  finite_candidate_feasible=feasible,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000), **P.FLAGS)
    return review, dict(complete=True), dict(complete=True, candidate_original_vector=['0']*1957)


class Publication(unittest.TestCase):
    def test_finite_equations_and_cones_are_distinct(self):
        for feasible in (False, True):
            values = fixture(feasible)
            self.assertIs(P.checked_outcome(*values)['finite_candidate_feasible'], feasible)
        review, proposal, endpoint = fixture()
        review['finite_candidate_feasible'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, proposal, endpoint)

    def test_missing_original_or_learned_equations_rejected(self):
        review, proposal, endpoint = fixture()
        for field, value in [('full_original_rows_checked', 5640),
                             ('feedback_row_verified', False), ('trace_exports_checked', False)]:
            changed = copy.deepcopy(review)
            changed['independent_search_check'][field] = value
            with self.assertRaises(ValueError):
                P.checked_outcome(changed, proposal, endpoint)
        review['RH_proved'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, proposal, endpoint)

    def test_unknown_cannot_promote_retained_endpoint(self):
        review, proposal, endpoint = fixture()
        review.update(status='UNKNOWN', endpoint_verified=False,
                      candidate_equations_verified=False, finite_candidate_feasible=None)
        self.assertIsNone(P.checked_outcome(review, proposal, endpoint))
        review.update(all_passed=False, resource_failure=dict(error_type='TimeoutError'))
        self.assertIsNone(P.checked_outcome(review, None, None))
        review['endpoint_verified'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, proposal, endpoint)


if __name__ == '__main__':
    unittest.main()
