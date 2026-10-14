"""Sampler replay, broad productions, and complete finite-outcome tests."""

import json
import unittest

from signed_arithmetic_language import WorkBudget
from signed_arithmetic_sampler import sample_programs, evaluate_programs, select_diverse


class SamplerTests(unittest.TestCase):
    def test_same_seed_replay_and_unrelated_seed_changes_programs(self):
        left = sample_programs(19281, 64, 3)
        right = sample_programs(19281, 64, 3)
        self.assertEqual(left, right)
        self.assertEqual(left.value['generated_count'], 64)
        self.assertFalse(left.value['response_values_used_for_generation'])
        different = sample_programs(19282, 64, 3)
        self.assertNotEqual(left.value['programs'], different.value['programs'])
        json.dumps(left.value)

    def test_sampler_uses_broad_signed_productions(self):
        result = sample_programs(19281, 64, 3).value
        ops, weights = set(), set()
        def visit(node):
            ops.add(node['op'])
            if node['op'] == 'scale':
                weights.add(node['params']['weight'])
            for child in node['args']:
                visit(child)
        for program in result['programs']:
            visit(program['expression'])
        self.assertTrue({'convolution', 'product', 'shift', 'dilate', 'floor_index',
                         'coprime_mask', 'residue_mask', 'truncate'} <= ops)
        self.assertTrue(any(weight.startswith('-') for weight in weights))

    def test_every_evaluation_is_archived_and_missing_never_passes(self):
        programs = sample_programs(19281, 64, 3).value['programs']
        result = evaluate_programs(programs, 24)
        self.assertEqual(len(result['observations']), 64)
        self.assertEqual(result['available_cases'] + result['missing_cases'] + result['invalid_cases'], 64)
        for row in result['observations']:
            if row['status'] != 'available':
                self.assertIsNone(row['metrics'])
                self.assertIsNone(row['arithmetic'])
        self.assertEqual(select_diverse(result['observations']), select_diverse(result['observations']))
        winners = select_diverse(result['observations'])
        self.assertEqual(len({w['top_operation'] for w in winners}), len(winners))
        json.dumps(result)

    def test_unattainable_count_and_construction_budget_are_explicit(self):
        report = sample_programs(5, 8, 0, max_attempts=100).value
        self.assertLessEqual(report['generated_count'], 4)
        self.assertFalse(report['requested_count_completed'])
        self.assertGreater(report['duplicate_attempts'], 0)
        report = sample_programs(19281, 16, 8, max_attempts=20, max_nodes_per_program=1).value
        self.assertGreater(report['missing_attempts'], 0)

    def test_tiny_numeric_budget_records_all_missing_cases(self):
        programs = sample_programs(19281, 8, 2).value['programs']
        report = evaluate_programs(programs, 32, budget=WorkBudget(max_cells=1))
        self.assertEqual(report['missing_cases'], 8)
        self.assertEqual(report['available_cases'], 0)
        self.assertEqual(select_diverse(report['observations']), [])


if __name__ == '__main__':
    unittest.main()
