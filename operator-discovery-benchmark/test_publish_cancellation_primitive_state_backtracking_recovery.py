import unittest
import publish_cancellation_primitive_state_backtracking_recovery as P


def fixture():
    review = dict(schema='primitive-state-backtracking-recovery-independent-review-v1',
                  status='RECOVERED_SCALAR_REJECTED', all_passed=True,
                  endpoint_verified=True, candidate_equations_verified=True,
                  finite_candidate_feasible=False,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000),
                  recovery_check=dict(full_original_rows_checked=5641, feedback_row_verified=True,
                                      negative_scalar_count=1, psd_status='NOT_CHECKED_AFTER_SCALAR_REJECTION',
                                      PSD_blocks_checked=0, PSD_failures=None), **P.FLAGS)
    endpoint = dict(complete=True, candidate_original_vector=['-1'] + ['0'] * 1956,
                    final_projected_vector=['0'] * 1224, final_free_vector=['0'] * 444)
    return review, endpoint


class RecoveryPublication(unittest.TestCase):
    def test_scalar_rejection_cannot_claim_matrix_checks_or_feasibility(self):
        review, endpoint = fixture()
        self.assertEqual(P.checked_outcome(review, endpoint)['negative_scalar_count'], 1)
        review['recovery_check']['PSD_failures'] = 0
        with self.assertRaises(ValueError):
            P.checked_outcome(review, endpoint)
        review['recovery_check']['PSD_failures'] = None
        review['finite_candidate_feasible'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, endpoint)

    def test_incomplete_recovery_cannot_promote_a_retained_vector(self):
        review, endpoint = fixture()
        review.update(status='UNKNOWN', all_passed=False, endpoint_verified=False,
                      candidate_equations_verified=False, finite_candidate_feasible=None)
        self.assertIsNone(P.checked_outcome(review, endpoint))
        review['endpoint_verified'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, endpoint)

    def test_positive_scalar_branch_requires_all_matrix_checks(self):
        review, endpoint = fixture()
        review.update(status='RECOVERED_CONE_CHECKED', finite_candidate_feasible=True)
        review['recovery_check'].update(negative_scalar_count=0, PSD_blocks_checked=2,
                                        PSD_failures=0, psd_status='ALL_THREE_EXACT_BLOCKS_CHECKED')
        with self.assertRaises(ValueError):
            P.checked_outcome(review, endpoint)
        review['recovery_check']['PSD_blocks_checked'] = 3
        self.assertIsNotNone(P.checked_outcome(review, endpoint))


if __name__ == '__main__':
    unittest.main()
