import copy
import unittest
import publish_cancellation_primitive_state_feedback_affine as P


def fixture(classification='independent', feasible=False):
    inconsistent = classification == 'inconsistent'
    rank = 779 + int(classification == 'independent')
    augmented = 779 + int(classification != 'redundant')
    free = None if inconsistent else 1224 - rank
    check = dict(verified=True, complete=True, classification=classification,
                 all_original_rows_replayed=True, projection_dependencies_verified=True,
                 feedback_reduction_verified=True, normalized_chart_verified=not inconsistent,
                 old_rank=779, new_rank=rank, augmented_rank=augmented,
                 old_free_count=445, new_free_count=free,
                 candidate_equations_verified=not inconsistent,
                 finite_candidate_feasible=None if inconsistent else feasible, **P.FLAGS)
    review = dict(schema='primitive-state-feedback-affine-independent-review-v1',
                  status=P.STATUSES[classification], all_passed=True,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000),
                  independent_affine_check=check, chart_verified=not inconsistent,
                  candidate_equations_verified=not inconsistent,
                  finite_candidate_feasible=None if inconsistent else feasible, **P.FLAGS)
    affine = dict(status='complete', complete=True, classification=classification,
                  coefficient_rank=rank, augmented_rank=augmented, free_dimension=free,
                  chart_available=not inconsistent,
                  candidate_original_vector=None if inconsistent else ['0'],
                  diagnostics=None if inconsistent else
                  dict(affine_equalities_satisfied=True, all_cones_satisfied=feasible))
    return review, affine


class Publication(unittest.TestCase):
    def test_equations_do_not_imply_cones_or_universal_proof(self):
        review, affine = fixture()
        self.assertFalse(P.checked_outcome(review, affine)['finite_candidate_feasible'])
        review['finite_candidate_feasible'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, affine)
        review, affine = fixture(feasible=True)
        self.assertTrue(P.checked_outcome(review, affine)['finite_candidate_feasible'])
        review['RH_proved'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, affine)

    def test_all_classifications_and_contradiction_rank(self):
        for classification in P.STATUSES:
            review, affine = fixture(classification)
            self.assertEqual(P.checked_outcome(review, affine)['classification'], classification)
        review, affine = fixture('inconsistent')
        affine['coefficient_rank'] = 780
        with self.assertRaises(ValueError):
            P.checked_outcome(review, affine)
        review, affine = fixture('inconsistent')
        review['chart_verified'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, affine)

    def test_partial_replay_cannot_license_map(self):
        review, affine = fixture()
        for field in ('all_original_rows_replayed', 'projection_dependencies_verified',
                      'feedback_reduction_verified', 'normalized_chart_verified'):
            changed = copy.deepcopy(review)
            changed['independent_affine_check'][field] = False
            with self.assertRaises(ValueError):
                P.checked_outcome(changed, affine)
        review.update(status='UNKNOWN', chart_verified=False,
                      candidate_equations_verified=False, finite_candidate_feasible=None)
        self.assertIsNone(P.checked_outcome(review, affine))
        review.update(all_passed=False, resource_failure={'error_type': 'TimeoutError'})
        self.assertIsNone(P.checked_outcome(review, None))


if __name__ == '__main__':
    unittest.main()
