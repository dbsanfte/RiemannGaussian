import copy
import unittest

import publish_cancellation_primitive_state_free_cone_search as P


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
    review = dict(schema='primitive-state-free-cone-search-independent-review-v1', all_passed=True,
                  original_finite_equations=5641, original_variables=1957, rank=779, free_coordinates=445,
                  parent_source_rebuilds=0, full_elimination_replayed=False, uniform_or_RH_admission=False,
                  objective_preserved=False, gradient_or_merit_certified=False, job=job, search_check=check, **P.FLAGS)
    record = dict(status='endpoint_verified', endpoint_verified=True, deadline_exceeded=False,
                  finite_candidate_feasible=feasible, **P.FLAGS)
    return dict(review=review, execution=dict(results=[dict(status='available')]), record=record,
                proposal=dict(status='proposed', complete=True, **P.FLAGS),
                endpoint=dict(complete=True, candidate_hash='candidate', **P.FLAGS), check=check)


class PublicationTests(unittest.TestCase):
    def test_exact_rejection_is_publishable_evidence(self):
        self.assertTrue(P.validate_outcome(**fixture(False)))

    def test_exact_finite_success_still_has_no_uniform_claim(self):
        data = fixture(True)
        self.assertTrue(P.validate_outcome(**data))
        self.assertFalse(data['review']['uniform_or_RH_admission'])

    def test_scope_cannot_change(self):
        for key, value in [('original_finite_equations', 4), ('rank', 778), ('free_coordinates', 444),
                           ('full_elimination_replayed', True), ('gradient_or_merit_certified', True)]:
            data = fixture()
            data['review'][key] = value
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_inconsistent_finite_verdict_rejected(self):
        data = fixture()
        data['record']['finite_candidate_feasible'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_missing_equality_or_psd_checks_rejected(self):
        for key, value in [('equality_complete', False), ('equality_mismatch_count', 1), ('psd_blocks', {})]:
            data = fixture()
            data['check']['endpoint_check']['exact_candidate_checks'][key] = value
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_candidate_hash_and_receipt_bound(self):
        data = fixture()
        data['endpoint']['candidate_hash'] = 'wrong'
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)
        data = fixture()
        data['review']['search_check'] = copy.deepcopy(data['check'])
        data['review']['search_check']['different'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_deadline_or_uncommitted_ledger_cannot_promote(self):
        data = fixture()
        data['record']['deadline_exceeded'] = True
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)
        data = fixture()
        data['review']['job']['lifecycle']['ledger']['all_stages_committed'] = False
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_unknown_outcome_preserved(self):
        data = fixture()
        data.update(record=None, proposal=None, endpoint=None, check=None)
        data['execution']['results'][0]['status'] = 'missing_resource'
        data['review']['job'].update(transport_status='missing_resource', worker_status=None,
                                    endpoint_verified=False, finite_candidate_feasible=None)
        self.assertFalse(P.validate_outcome(**data))
        data['review']['job']['finite_candidate_feasible'] = False
        with self.assertRaises(ValueError):
            P.validate_outcome(**data)

    def test_theorem_claim_rejected(self):
        for name in ('review', 'record', 'proposal', 'endpoint', 'check'):
            data = fixture()
            data[name]['RH_proved'] = True
            with self.assertRaises(ValueError):
                P.validate_outcome(**data)

    def test_actual_archive_uses_stem_bindings(self):
        if not (P.RUN / 'independent_verification.json').exists():
            self.skipTest('actual archive audit not completed yet')
        stage = P.completed_archive()
        self.assertEqual(set(stage['review']['input_sha256']),
                         {'protocol', 'source_seal', 'input', 'seal', 'tests', 'execution', 'receipt'})


if __name__ == '__main__':
    unittest.main()
