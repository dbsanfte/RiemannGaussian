"""A finite probe can reject a formal identity but cannot prove RH."""
import copy
import unittest
import publish_cancellation_primitive_state_uniform_identity_probe as P


def fixture(residue=17):
    status = 'REFUTED' if residue else 'NOT_REFUTED_BY_THIS_PROBE'
    row = dict(width=1957, X=7, entries=[dict(index=0, coefficient='3')], rhs='-5')
    check = dict(verified=True, complete=True, source_semantics_independently_verified=True,
                 source_rebuilds=1, nonconstant_difference=residue, modular_prime=65537,
                 status=status, nonconstant_formal_identity_refuted=bool(residue),
                 necessary_formal_identity_constraint=row, **P.FLAGS)
    review = dict(schema='primitive-state-uniform-identity-probe-independent-review-v1',
                  all_passed=True, joint_work=dict(max_work=450000000, total_work_reserve=420000000),
                  status=status, nonconstant_formal_identity_refuted=bool(residue),
                  independent_probe_check=check, necessary_formal_identity_constraint=row, **P.FLAGS)
    return review, dict(feedback_row=copy.deepcopy(row), nonconstant_difference=residue)


class PublicationScope(unittest.TestCase):
    def test_only_checked_nonzero_rejects(self):
        for residue in (0, 17):
            review, probe = fixture(residue)
            row, observed = P.checked_outcome(review, probe)
            self.assertEqual(observed, residue)
            self.assertEqual(row, probe['feedback_row'])
        review, probe = fixture(0)
        review['status'] = 'REFUTED'
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probe)

    def test_no_universal_promotion_or_unchecked_row(self):
        for mutation in ('RH', 'row', 'source', 'budget'):
            review, probe = fixture()
            if mutation == 'RH':
                review['RH_proved'] = True
            elif mutation == 'row':
                probe['feedback_row']['rhs'] = '0'
            elif mutation == 'source':
                review['independent_probe_check']['source_semantics_independently_verified'] = False
            else:
                review['joint_work']['total_work_reserve'] = 450000001
            with self.assertRaises(ValueError):
                P.checked_outcome(review, probe)

    def test_incomplete_run_exports_no_constraint(self):
        review, probe = fixture()
        review.update(status='UNKNOWN', nonconstant_formal_identity_refuted=False)
        self.assertEqual(P.checked_outcome(review, probe), (None, None))
        review.update(all_passed=False, independent_resource_failure=dict(error_type='MemoryError'),
                      necessary_formal_identity_constraint=None)
        self.assertEqual(P.checked_outcome(review, probe), (None, None))
        review['nonconstant_formal_identity_refuted'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probe)


if __name__ == '__main__':
    unittest.main()
