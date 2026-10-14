"""Tiny independent end-to-end argument compilation, not a pilot replay."""
import unittest
import prime_transfer_search_058 as S
import run_prime_transfer_058 as R
import check_prime_transfer_058 as C
import test_prime_transfer_search_058 as T

OPERATIONS = 0


class RunnerTests(unittest.TestCase):
    def test_full_candidate_admission_keeps_unpaid_states(self):
        global OPERATIONS
        universe, atoms, relations = T.fixture()
        row = next(r for r in S.promote(atoms, relations, T.SM)['rows'] if r['origin']['kind'] == 'pair_current_elimination')
        result = R.compile_candidate(universe, atoms, row)
        OPERATIONS += sum(result['operations'].values())
        self.assertTrue(result['identity_verification']['verified'])
        self.assertTrue(result['source_order_verification']['verified'])
        self.assertEqual(result['interpretation']['family'], 'weighted_prime_exchange')
        self.assertEqual(result['proof_attempt']['status'], 'OPEN_SOURCE_FORCING')
        self.assertFalse(result['RH_proved'])

    def test_target_obstruction_has_limited_scope(self):
        cm = C.Meter()
        checked = R.target_obstruction([2, 7], [2], T.SM, cm)
        global OPERATIONS
        OPERATIONS += cm.operations
        self.assertEqual(checked['obstruction'], 'NONZERO_CURRENT_SECTOR_WHILE_EVERY_STRICTLY_LOWER_ATOM_VANISHES')
        self.assertFalse(checked['rules_out_all_arithmetic_proofs'])
        self.assertFalse(checked['uniform_bound_proved'])


if __name__ == '__main__': unittest.main()
