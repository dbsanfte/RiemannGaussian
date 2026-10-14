"""Reject optimizer bypass, sealed writes and wrong candidate exclusions."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
from detector_workflow_guard import require_verified_runtime, require_unsealed_destination, witness_derived_refutations

BASE = Path(__file__).resolve().parent
ROUND = BASE / 'candidate-review-results/sol-6.1-round-001'


class GuardContracts(unittest.TestCase):
    def test_optimized_python_cannot_enter_guard(self):
        env = dict(os.environ); env.pop('PYTHONOPTIMIZE', None)
        result = subprocess.run([sys.executable, '-O', '-c',
            'from detector_workflow_guard import require_verified_runtime; require_verified_runtime()'],
            cwd=BASE, env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('assertions enabled', result.stderr)

    def test_inherited_optimizer_is_rejected(self):
        with patch.dict(os.environ, {'PYTHONOPTIMIZE': '1'}):
            with self.assertRaises(RuntimeError):
                require_verified_runtime()

    def test_successful_worker_destination_is_read_only(self):
        with self.assertRaises(FileExistsError):
            require_unsealed_destination(BASE / 'inverse-prefix-results/pilot-002')

    def test_verified_ids_recomputed_from_witnesses(self):
        result = witness_derived_refutations(ROUND)
        self.assertEqual(result['independently_rechecked_witnesses'], 5)
        self.assertEqual(len(result['all_refuted_candidate_ids']), 8)
        self.assertEqual(result['remaining_uniform_half_gap_claims'], 40)

    def test_count_preserving_id_swap_is_rejected(self):
        value = json.loads((ROUND / 'verification.json').read_text())
        wrong = copy.deepcopy(value)
        source = Path(value['source_run'])
        queue = json.loads((source / 'proof_queue.json').read_text())['queue']
        unresolved = next(r['program_id'] for r in queue if r['program_id'] not in value['all_refuted_candidate_ids'])
        old = wrong['new_refuted_candidate_ids'][0]
        wrong['new_refuted_candidate_ids'][0] = unresolved
        wrong['all_refuted_candidate_ids'][wrong['all_refuted_candidate_ids'].index(old)] = unresolved
        with self.assertRaises(ValueError):
            witness_derived_refutations(ROUND, wrong)

    def test_inflated_queue_and_remaining_counts_are_rejected(self):
        value = json.loads((ROUND / 'verification.json').read_text())
        value['original_queue_candidate_count'] += 1
        value['remaining_uniform_half_gap_claims'] += 1
        with self.assertRaises(ValueError):
            witness_derived_refutations(ROUND, value)


if __name__ == '__main__':
    unittest.main()
