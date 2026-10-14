import copy
import unittest
import publish_cancellation_primitive_state_direct_identity_probe as P


def fixture(residue=17):
    status = 'REFUTED' if residue else 'NOT_REFUTED_BY_THIS_PROBE'
    row = dict(width=1957, X=7, entries=[dict(index=0, coefficient='3')], rhs='-5')
    check = dict(verified=True, complete=True, complete_grammar_independently_evaluated=True,
                 complete_coefficient_row_verified=True, symbolic_source_constructed=False,
                 nonconstant_difference=residue, modular_prime=65537, status=status,
                 nonconstant_formal_identity_refuted=bool(residue),
                 necessary_formal_identity_constraint=row, **P.FLAGS)
    review = dict(schema='primitive-state-direct-identity-probe-independent-review-v1', all_passed=True,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000), status=status,
                  nonconstant_formal_identity_refuted=bool(residue), independent_probe_check=check,
                  necessary_formal_identity_constraint=row, **P.FLAGS)
    return review, dict(feedback_row=copy.deepcopy(row), nonconstant_difference=residue)


class DirectPublication(unittest.TestCase):
    def test_only_verified_nonzero_rejects(self):
        for residue in (0, 17):
            review, probe = fixture(residue)
            self.assertEqual(P.checked_outcome(review, probe), (probe['feedback_row'], residue))
        review, probe = fixture(0)
        review['status'] = 'REFUTED'
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probe)

    def test_no_universal_promotion_or_partial_grammar(self):
        for mutation in ('RH', 'row', 'grammar', 'budget'):
            review, probe = fixture()
            if mutation == 'RH':
                review['RH_proved'] = True
            elif mutation == 'row':
                probe['feedback_row']['rhs'] = '0'
            elif mutation == 'grammar':
                review['independent_probe_check']['complete_grammar_independently_evaluated'] = False
            else:
                review['joint_work']['total_work_reserve'] += 1
            with self.assertRaises(ValueError):
                P.checked_outcome(review, probe)

    def test_incomplete_evaluation_exports_no_row(self):
        review, probe = fixture()
        review.update(status='UNKNOWN', nonconstant_formal_identity_refuted=False)
        self.assertEqual(P.checked_outcome(review, probe), (None, None))
        review.update(all_passed=False, resource_failure=dict(error_type='TimeoutError'),
                      necessary_formal_identity_constraint=None)
        self.assertEqual(P.checked_outcome(review, probe), (None, None))
        review['nonconstant_formal_identity_refuted'] = True
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probe)


if __name__ == '__main__':
    unittest.main()
