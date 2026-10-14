import copy
import unittest
import publish_cancellation_primitive_state_fresh_identity_probe as P


def fixture(residues=(17, 0), classes=('independent', 'independent')):
    rows, checks, probes = [], [], []
    for i, residue in enumerate(residues):
        row = dict(schema='primitive-state-formal-identity-necessary-row-v1',
                   width=1957, X=9, assignment=P.ASSIGNMENTS[i][:],
                   entries=[dict(index=1, coefficient='3')], rhs='-5')
        check = dict(verified=True, complete=True, complete_grammar_independently_evaluated=True,
                     complete_coefficient_row_verified=True, symbolic_source_constructed=False,
                     nonconstant_difference=residue, modular_prime=65537,
                     status='REFUTED' if residue else 'NOT_REFUTED_BY_THIS_PROBE',
                     nonconstant_formal_identity_refuted=bool(residue),
                     necessary_formal_identity_constraint=row, **P.FLAGS)
        rows.append(row)
        checks.append(dict(index=i, independent_probe_check=check))
        probes.append(dict(complete=True, feedback_row=copy.deepcopy(row),
                           nonconstant_difference=residue))
    rank = 780 + classes.count('independent')
    inconsistent = 'inconsistent' in classes
    extension = dict(complete=True, old_rank=780, coefficient_rank=rank,
                     augmented_rank=rank+int(inconsistent),
                     free_count=None if inconsistent else 1224-rank,
                     reductions=[dict(index=i, classification=c) for i, c in enumerate(classes)],
                     appended_rows=[{} for c in classes if c == 'independent'],
                     formal_family_only=True, **P.FLAGS)
    review = dict(schema='primitive-state-fresh-identity-probe-independent-review-v1',
                  all_passed=True, resource_failure=None,
                  status='REFUTED' if any(residues) else 'NOT_REFUTED_BY_THIS_PROBE',
                  nonconstant_formal_identity_refuted=bool(any(residues)),
                  case_checks=checks, necessary_formal_identity_constraints=rows,
                  affine_extension=extension,
                  joint_work=dict(max_work=450000000, total_work_reserve=450000000), **P.FLAGS)
    return review, probes


class FreshPublication(unittest.TestCase):
    def test_one_nonzero_is_enough_but_two_zeros_are_not_a_theorem(self):
        for residues in ((0, 0), (0, 17), (17, 0), (17, 23)):
            review, probes = fixture(residues)
            rows, actual, extension = P.checked_outcome(review, probes)
            self.assertEqual(actual, list(residues))
            self.assertEqual(len(rows), 2)
            self.assertEqual(extension['coefficient_rank'], 782)
            self.assertFalse(review['universal_identity_proved'])

    def test_both_fixed_assignments_must_be_independently_checked(self):
        for mutation in ('missing', 'duplicate', 'assignment', 'grammar', 'row', 'incomplete'):
            review, probes = fixture()
            if mutation == 'missing':
                review['case_checks'].pop()
            elif mutation == 'duplicate':
                review['case_checks'][1]['index'] = 0
            elif mutation == 'assignment':
                review['case_checks'][1]['independent_probe_check']['necessary_formal_identity_constraint']['assignment'] = P.ASSIGNMENTS[0][:]
            elif mutation == 'grammar':
                review['case_checks'][1]['independent_probe_check']['complete_grammar_independently_evaluated'] = False
            elif mutation == 'row':
                probes[1]['feedback_row']['rhs'] = '0'
            else:
                probes[1]['complete'] = False
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                P.checked_outcome(review, probes)

    def test_contradiction_changes_augmented_rank_only(self):
        for classes in (('independent', 'inconsistent'), ('inconsistent', 'redundant')):
            review, probes = fixture(classes=classes)
            extension = P.checked_outcome(review, probes)[2]
            self.assertEqual(extension['augmented_rank'], extension['coefficient_rank']+1)
            self.assertIsNone(extension['free_count'])
            self.assertFalse(review['infeasibility_proved'])
            review['affine_extension']['coefficient_rank'] += 1
            with self.assertRaises(ValueError):
                P.checked_outcome(review, probes)

    def test_incomplete_audit_publishes_no_partial_rows_or_rank(self):
        review, probes = fixture()
        review.update(status='UNKNOWN', all_passed=False,
                      nonconstant_formal_identity_refuted=False,
                      necessary_formal_identity_constraints=[], affine_extension=None,
                      resource_failure=dict(error_type='TimeoutError'))
        self.assertEqual(P.checked_outcome(review, probes), ([], [], None))
        review['necessary_formal_identity_constraints'] = [probes[0]['feedback_row']]
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probes)

    def test_no_admission_from_finite_probes_or_extra_budget(self):
        for mutation in ('RH_proved', 'candidate_admitted', 'infeasibility_proved', 'budget', 'scope'):
            review, probes = fixture()
            if mutation == 'budget':
                review['joint_work']['total_work_reserve'] += 1
            elif mutation == 'scope':
                review['case_checks'][0]['independent_probe_check']['arithmetic_sign_values_substituted'] = True
            else:
                review[mutation] = True
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                P.checked_outcome(review, probes)

    def test_zero_residue_cannot_be_published_as_refutation(self):
        review, probes = fixture((0, 0))
        review.update(status='REFUTED', nonconstant_formal_identity_refuted=True)
        with self.assertRaises(ValueError):
            P.checked_outcome(review, probes)


if __name__ == '__main__':
    unittest.main()
