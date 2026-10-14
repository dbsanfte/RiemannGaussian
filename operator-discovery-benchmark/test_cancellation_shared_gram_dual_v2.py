import copy
import unittest

import cancellation_shared_gram_dual_v2 as D
from unittest.mock import patch
import check_cancellation_shared_gram as I


def poly(*terms):
    return [dict(m=list(m), c=str(q)) for m, q in terms]


def fixture():
    # Constant atom, zero atom and diagonal-only monomial are all intentional.
    instance = dict(target='mu', horizon=1, lhs=poly(((1, 1), -1)),
                    square_groups=[], relation_groups=[])
    blocks = [{'z2': [[poly(((), 1)), []]],
               'a5': [[poly(((1,), 1)), [], [], [], []]]}]
    return [instance], blocks, {'z2': 2, 'a5': 5}


class SharedGramDualV2(unittest.TestCase):
    def test_complete_mixed_dimension_separator(self):
        instances, blocks, specs = fixture()
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertTrue(out['independent_full_Gram_check_passed'])
        self.assertEqual(list(out['gram_duals']), ['a5', 'z2'])
        self.assertEqual(len(out['gram_columns_dot_y']), 18)
        self.assertIn(dict(instance=0, m=[1, 1]), out['monomials'])
        self.assertIn(dict(instance=0, m=[]), out['monomials'])
        self.assertEqual(out['gram_duals']['a5']['matrix'][0][0], '1')
        self.assertTrue(I.verify_dual(instances, blocks, specs, out)['verified'])

    def test_constant_moment_not_assumed_zero(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((), -1))
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertEqual(out['constant_coordinates'], ['1'])
        self.assertFalse(out['all_C_q_extension_requires_zero_constant_coordinates'])

    def test_full_gram_diagonal_prevents_false_separator(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((1, 1), 1))
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertFalse(out['certified'])
        self.assertIn('no exact infeasibility', out['reason'])

    def test_all_cross_moments_restricted_to_zero(self):
        instances, blocks, specs = fixture()
        instances[0]['lhs'] = poly(((1,), -1))
        blocks[0]['z2'] = [[poly(((), 1)), poly(((1,), 1))]]
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertFalse(out['certified'])
        self.assertIn('no exact infeasibility', out['reason'])

    def test_auxiliary_constant_coverage(self):
        instances, blocks, specs = fixture()
        instances.append(dict(target='mu', horizon=1, lhs=[], square_groups=[], relation_groups=[]))
        blocks.append({'z2': [], 'a5': []})
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        self.assertEqual(len(out['constant_coordinates']), 2)
        self.assertIn(dict(instance=1, m=[]), out['monomials'])

    def test_classifications_and_bad_coverage(self):
        nonnegative, relations, layout = D.classify([{}]*8, (1, 1), 5, {'g': 2})
        self.assertEqual(nonnegative, [0, 3, 4, 5, 7])
        self.assertEqual(relations, [1, 2, 6])
        self.assertEqual(layout, [('g', 2, [(5, 0, 0), (6, 0, 1), (7, 1, 1)])])
        with self.assertRaises(ValueError):
            D.classify([{}]*7, (1, 1), 5, {'g': 2})

    def test_malformed_inputs_and_resource_limit(self):
        args = fixture()
        for limit in (float('nan'), True, 0):
            self.assertEqual(D.propose(*args[:2], gram_specs=args[2], time_limit=limit)['status'], 'uncertified')
        self.assertEqual(D.propose(*args[:2], gram_specs=args[2], max_rows=1)['status'], 'missing_resource')
        args[1][0]['z2'][0].append([])
        self.assertFalse(D.propose(*args[:2], gram_specs=args[2])['certified'])

    def test_independent_rejects_mutation(self):
        instances, blocks, specs = fixture()
        out = D.propose(instances, blocks, gram_specs=specs, time_limit=20)
        self.assertTrue(out['certified'], out)
        bad = copy.deepcopy(out)
        bad['gram_duals']['a5']['matrix'][0][1] = '1'
        bad['gram_duals']['a5']['matrix'][1][0] = '1'
        with self.assertRaises(ValueError):
            I.verify_dual(instances, blocks, specs, bad)
        bad = copy.deepcopy(out)
        bad['monomials'] = [m for m in bad['monomials'] if m['m'] != [1, 1]]
        with self.assertRaises(ValueError):
            I.verify_dual(instances, blocks, specs, bad)


class DualV2CheckpointTests(unittest.TestCase):
    def test_checkpoint_precedes_native_and_forced_failure_retained(self):
        i,b,s=fixture();saved=[]
        def native(*args,**kwargs):
            self.assertEqual(saved[-1]['phase'],'LP_proposal')
            self.assertIsNotNone(saved[-1]['support'])
            self.assertEqual(kwargs['max_work'],450000000)
            self.assertEqual(kwargs['max_preprocessing_cells'],4000000)
            return dict(status='missing_resource',certified=False,reason='forced native resource cap',diagnostics={})
        with patch.object(D.N,'reconstruct_dual_fixed_support',side_effect=native):
            out=D.propose(i,b,gram_specs=s,on_checkpoint=saved.append,time_limit=20)
        self.assertEqual(out['status'],'missing_resource')
        cp=out['proposal_checkpoint'];self.assertEqual(cp['native_reason'],'forced native resource cap')
        self.assertEqual(cp['source_hashes'],[D.S.digest(i[0])])
        self.assertEqual(cp['row_order_hash'],D.S.digest(cp['monomials']))
    def test_actual_compressed_admission_and_checkpoint(self):
        i,b,s=fixture();saved=[]
        out=D.propose(i,b,gram_specs=s,on_checkpoint=saved.append,time_limit=20)
        self.assertTrue(out['certified'],out)
        self.assertEqual(saved[-1]['phase'],'independent_admission')
        self.assertLessEqual(out['diagnostics']['row_compression']['total_work_proxy'],450000000)
        self.assertEqual(saved[0]['support'],None)
    def test_callback_failure_stops_native(self):
        i,b,s=fixture()
        def callback(cp):raise OSError('storage unavailable')
        with patch.object(D.N,'reconstruct_dual_fixed_support',side_effect=AssertionError('must not run')):
            out=D.propose(i,b,gram_specs=s,on_checkpoint=callback,time_limit=20)
        self.assertEqual(out['status'],'uncertified')
        self.assertIn('checkpoint callback failed',out['reason'])
    def test_byte_cap_precedes_solver(self):
        i,b,s=fixture()
        with patch.object(D,'support_proposal',side_effect=AssertionError('must not solve')):
            out=D.propose(i,b,gram_specs=s,max_checkpoint_bytes=1,time_limit=20)
        self.assertEqual(out['status'],'missing_resource')
        self.assertIsNone(out['proposal_checkpoint'])
    def test_failed_LP_status_checkpointed(self):
        i,b,s=fixture();saved=[]
        with patch.object(D,'support_proposal',return_value=(None,dict(solver_status=2,solver_message='no proposal'))):
            out=D.propose(i,b,gram_specs=s,on_checkpoint=saved.append,time_limit=20)
        self.assertFalse(out['certified'])
        self.assertEqual(saved[-1]['phase'],'LP_proposal')
        self.assertEqual(saved[-1]['numerical_diagnostics']['solver_status'],2)


if __name__ == '__main__':
    unittest.main()
