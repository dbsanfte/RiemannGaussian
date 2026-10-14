import copy
import unittest

import publish_cancellation_primitive_state_cone_jacobi_search as P


def fixture(feasible=False):
    checks = dict(equality_complete=True, equality_mismatch_count=0, scalar_signs_complete=True,
                  negative_scalar_count=0 if feasible else 1,
                  psd_blocks={name: dict(psd=True) for name in ('full_child', 'full_parent', 'storage_K')},
                  finite_candidate_feasible=feasible)
    exact = dict(all_original_equations_checked=5641, original_variables=1957,
                 candidate_hash='candidate', licensed_affine_uniqueness=True, full_elimination_replayed=False,
                 exact_candidate_checks=checks, finite_candidate_feasible=feasible)
    check = dict(verified=True, complete=True, endpoint_verified=True, endpoint_check=exact,
                 finite_candidate_feasible=feasible, **P.FLAGS)
    job = dict(transport_status='available', worker_status='endpoint_verified', endpoint_verified=True,
               finite_candidate_feasible=feasible, lifecycle=dict(ledger=dict(all_stages_committed=True)), **P.FLAGS)
    review = dict(schema='primitive-state-cone-jacobi-search-independent-review-v1', all_passed=True,
                  original_finite_equations=5641, original_variables=1957, rank=779, free_coordinates=445,
                  parent_source_rebuilds=0, full_elimination_replayed=False, uniform_or_RH_admission=False,
                  objective_preserved=False, gradient_or_merit_certified=False,
                  joint_work=dict(max_work=450000000, whole_archive_audit_allocation=25000000,
                                  worker_reserved_work=420000000, whole_archive_audit_operations=10000000,
                                  joint_reserved_plus_actual_work=430000000),
                  job=job, search_check=check, **P.FLAGS)
    record = dict(status='endpoint_verified', endpoint_verified=True, deadline_exceeded=False,
                  finite_candidate_feasible=feasible, **P.FLAGS)
    return dict(review=review, execution=dict(results=[dict(status='available')]), record=record,
                proposal=dict(status='proposed', complete=True, **P.FLAGS),
                endpoint=dict(complete=True, candidate_hash='candidate', **P.FLAGS), check=check)


class PublicationTests(unittest.TestCase):
    def test_finite_rejection_retained_as_evidence(self):
        self.assertTrue(P.validate_outcome(**fixture()))

    def test_finite_success_cannot_promote_to_uniform_result(self):
        data = fixture(True)
        self.assertTrue(P.validate_outcome(**data))
        for name in ('review', 'record', 'proposal', 'endpoint', 'check'):
            changed = copy.deepcopy(data)
            changed[name]['RH_proved'] = True
            with self.assertRaises(ValueError):
                P.validate_outcome(**changed)

    def test_uncertified_scaling_cannot_be_promoted(self):
        for key in ('column_norms_independently_verified', 'scaled_trace_bound_certified',
                    'gradient_or_merit_certified', 'uniform_or_RH_admission'):
            data = fixture()
            data['review'][key] = True
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_candidate_hash_and_receipt_binding(self):
        data = fixture()
        data['endpoint']['candidate_hash'] = 'other'
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)
        data = fixture()
        data['review']['search_check'] = copy.deepcopy(data['check'])
        data['review']['search_check']['other'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_original_equations_signs_and_psd_are_required(self):
        for key, value in [('equality_mismatch_count', 1), ('scalar_signs_complete', False),
                           ('equality_complete', False), ('psd_blocks', {})]:
            data = fixture()
            data['check']['endpoint_check']['exact_candidate_checks'][key] = value
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_finite_verdict_must_match_exact_checks(self):
        data = fixture()
        data['record']['finite_candidate_feasible'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_resource_failure_cannot_supply_verdict(self):
        data = fixture()
        data.update(record=None, proposal=None, endpoint=None, check=None)
        data['execution']['results'][0]['status'] = 'missing_resource'
        data['review']['job'].update(transport_status='missing_resource', worker_status=None,
                                    endpoint_verified=False, finite_candidate_feasible=None)
        self.assertFalse(P.validate_outcome(**data))
        data['review']['job']['finite_candidate_feasible'] = False
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_deadline_and_unfinished_ledger_cannot_supply_endpoint(self):
        data = fixture()
        data['record']['deadline_exceeded'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)
        data = fixture()
        data['review']['job']['lifecycle']['ledger']['all_stages_committed'] = False
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_final_audit_cannot_be_omitted_from_work_accounting(self):
        for key, value in [('joint_reserved_plus_actual_work', 420000000),
                           ('worker_reserved_work', 450000000),
                           ('whole_archive_audit_operations', 25000001)]:
            data = fixture()
            data['review']['joint_work'][key] = value
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_matrix_regression_visible_despite_total_improvement(self):
        # Scalar penalty falls 100->10 while the matrix penalty rises 1->2.
        proposal = dict(complete=True, initial_merit=[0, '65', 0], final_merit=[0, '3', 2],
                        initial_merit_details=dict(scalar_penalty=[0, '19', 2], matrix_penalty=[0, '1', 0]),
                        iterations=[dict(trials=[dict(armijo_passed=True,
                            merit_details=dict(scalar_penalty=[0, '5', 1], matrix_penalty=[0, '1', 1]))])])
        result = P.merit_summary(proposal)
        self.assertLess(result['final'], result['initial'])
        self.assertGreater(result['final_matrix_penalty'], result['initial_matrix_penalty'])
        self.assertFalse(result['gradient_or_merit_certified'])


if __name__ == '__main__':
    unittest.main()
