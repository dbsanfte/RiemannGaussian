from fractions import Fraction as Q
import itertools
import json
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np
from flint import fmpq_mat

import mobius_bank_witness_086 as W
import check_mobius_arithmetic_bank_086 as C
from test_mobius_coupled_square_084 import program


def bank():
    return [dict(kind='prime_pair',cut_on='prime',
                 cut=dict(scale='1',u_exponent='1',complement=False),weight=dict(kind='one'))]


def exhaustive(model, descriptors):
    system = W.integer_system(model,descriptors)
    remainder = W.MIXED.original_remainder(model)
    found = []
    n = model['price_dimension']
    for tail in itertools.product((-1,1),repeat=max(0,n-1)):
        signs = [1]+list(tail) if n else []
        ok,_ = W.compatible(model,system,signs)
        if ok:found.append((W.quadratic_value(model,remainder,signs),signs))
    return found


class BankWitnessTests(unittest.TestCase):
    def model(self,u=53):
        return W.MIXED.build_model(program(),u)

    def test_tiny_exhaustive_feasibility_and_complete_quadratic_admission(self):
        p = program()
        outer = W.MIXED.SQUARE.O.synthesize(p)['certificate']
        for descriptors in ([],bank()):
            model = self.model()
            all_feasible = exhaustive(model,descriptors)
            result = W.solve_model(model,descriptors,time_limit=1,attempts=4,seed=17)
            self.assertEqual(result['status'],'EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL')
            maximum = max(value for value,_ in all_feasible)
            self.assertEqual(Q(result['certificate']['lower_bound']),maximum)
            for candidate in result['candidates']:
                cert = candidate['certificate']
                self.assertIn((Q(cert['lower_bound']),cert['signs']),all_feasible)
                admitted = C.verify_lower(p,53,outer,descriptors,cert)
                self.assertEqual(admitted['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND',admitted)
            self.assertFalse(result['global_quadratic_maximum_proved'])
            self.assertFalse(result['unknown_composite_signs_used'])
            self.assertFalse(result['RH_proved'])
            json.dumps(result,allow_nan=False)

    def test_negative_feasible_incumbent_is_kept_through_solver_failures(self):
        model = self.model()
        with patch.object(W,'milp',side_effect=RuntimeError('deliberate tiny solver failure')) as propose:
            result = W.solve_model(model,bank(),time_limit=1,attempts=4)
        self.assertEqual(propose.call_count,4)
        self.assertEqual(result['certificate']['signs'],[1,1,1])
        self.assertEqual(result['certificate']['lower_bound'],'-1/24')
        failures = [a for a in result['attempts'] if a['name'].startswith('MILP_')]
        self.assertEqual(len(failures),4)
        self.assertTrue(all(a['status'] == 'PROPOSAL_FAILURE' for a in failures))
        self.assertTrue(all('deliberate tiny' in a['reason'] for a in failures))

    def test_numerical_infeasibility_never_becomes_an_exact_proof(self):
        model = self.model(131)
        n = model['price_dimension']
        starts = [('TEST_ONLY_INCOMPATIBLE_START_'+str(i),[1]*n) for i in range(4)]
        fake = SimpleNamespace(status=2,message='synthetic numerical infeasible status',x=None)
        with patch.object(W,'_starts',return_value=(np.zeros((n,n)),starts,1.)),patch.object(W,'milp',return_value=fake) as propose:
            result = W.solve_model(model,bank(),time_limit=1,attempts=4)
        self.assertEqual(propose.call_count,4)
        self.assertEqual(result['status'],'NO_EXACT_COMPATIBLE_WITNESS_FOUND')
        self.assertIsNone(result['certificate'])
        self.assertNotIn('exact_infeasibility_proofs',result)
        numerical = [a for a in result['attempts'] if a['name'].startswith('MILP_')]
        self.assertTrue(all(a['status'] == 'FLOAT_MILP_INFEASIBLE_UNPROVED' for a in numerical))
        self.assertTrue(all(not a['infeasibility_proved'] for a in numerical))

    def test_exact_integer_parity_gcd_and_range_obstructions(self):
        cases = [([0,1,0],'ODD_BINARY_RIGHT_NUMERATOR'),
                 ([2,2,2],'GCD_DOES_NOT_DIVIDE_RIGHT'),
                 ([2,0,0],'ZERO_ROW_NONZERO_RIGHT'),
                 ([4,1,1],'BINARY_INTERVAL_EXCLUDES_RIGHT')]
        for column,kind in cases:
            rec = dict(column=column,denominator=1,cut=1,prime_pair_count=0)
            with patch.object(W.BANK,'integer_column',return_value=rec),patch.object(W,'milp') as propose:
                system = W.integer_system(self.model(),bank())
                self.assertEqual(system['obstructions'][0]['kind'],kind)
                self.assertFalse(any(sum(c*s for c,s in zip(column,[1]+list(tail))) == 0
                                     for tail in itertools.product((-1,1),repeat=2)))
                result = W.solve_model(self.model(),bank(),time_limit=1,attempts=4)
                self.assertEqual(result['status'],'EXACT_BOOLEAN_BANK_INFEASIBLE')
                self.assertEqual(result['exact_infeasibility_proofs'][0]['kind'],kind)
                propose.assert_not_called()
        # These are test-only synthetic integer rows, not assertions that an
        # actual independently justified arithmetic bank can be inconsistent.

    def test_binary_equations_match_original_rational_bank_exactly(self):
        model = self.model()
        descriptors = bank()+[dict(kind='divisor',cut=dict(scale='1/3',u_exponent='1',complement=False,unit_balance=True)),
                              dict(kind='prime_pair',cut_on='cofactor',cut=dict(scale='1/3',u_exponent='1',complement=False),weight=dict(kind='source',i=0))]
        system = W.integer_system(model,descriptors)
        A,b = W.numeric_system(model,system)
        independent = C.build_identities(C.C.build_model(program(),53),descriptors)['vectors']
        for tail in itertools.product((-1,1),repeat=2):
            signs = [1]+list(tail)
            x = [(s+1)//2 for s in tail]
            original = all(sum(independent[i][j]*signs[i] for i in range(3)) == 0 for j in range(len(descriptors)))
            exact_binary = all(sum(coefficient*value for coefficient,value in zip(row,x)) == right
                               for row,right in zip(system['rows'],system['rhs']))
            self.assertEqual(original,exact_binary)
            self.assertEqual(exact_binary,bool(np.all(A@np.asarray(x,dtype=float) == b)))

    def test_exact_local_pair_flip_and_zero_column_flip_keep_anchor(self):
        model = self.model()
        system = dict(columns=[[0,1,1]],bank_size=1)
        remainder = fmpq_mat([[0,-1,1],[-1,0,0],[1,0,0]])
        initial = [1,1,-1]
        cert,diagnostics = W.improve_compatible(model,system,remainder,initial,steps=4)
        self.assertEqual(cert['signs'],[1,-1,1])
        self.assertEqual(cert['lower_bound'],'4')
        self.assertEqual(diagnostics['flips'],[dict(indices=[1,2],exact_gain='8')])
        self.assertTrue(diagnostics['anchor_never_flipped'])
        zero = dict(columns=[],bank_size=0)
        remainder = fmpq_mat([[0,1,0],[1,0,0],[0,0,0]])
        cert,diagnostics = W.improve_compatible(model,zero,remainder,[1,-1,1],steps=4)
        self.assertEqual(cert['signs'],[1,1,1])
        self.assertEqual(cert['lower_bound'],'2')
        self.assertEqual(diagnostics['flips'][0]['exact_gain'],'4')

    def test_literal_quadratic_and_mutation_rejection(self):
        model = self.model()
        remainder = W.MIXED.original_remainder(model)
        signs = [1,1,1]
        cert = W.certificate(model,bank(),signs)
        literal = sum((Q(str(remainder[i,j]))*signs[i]*signs[j]
                       for i in range(3) for j in range(3)),Q(0))
        self.assertEqual(Q(cert['lower_bound']),literal)
        p = program()
        outer = W.MIXED.SQUARE.O.synthesize(p)['certificate']
        for key,value in [('signs',[1,-1,1]),('signs',[-1,1,1]),('lower_bound',str(literal+1)),('squarefree_count',8)]:
            bad = dict(cert)
            bad[key] = value
            self.assertEqual(C.verify_lower(p,53,outer,bank(),bad)['status'],'INVALID')
        for signs in ([1,-1,1],[-1,1,1],[1,True,1],[1,1]):
            with self.assertRaises(ValueError):W.certificate(self.model(),bank(),signs)

    def test_exact_rounding_requires_full_bank_compatibility(self):
        fake = SimpleNamespace(status=0,message='synthetic rounded candidate',x=np.array([0.,0.]))
        with patch.object(W,'milp',return_value=fake):
            result = W.solve_model(self.model(),bank(),time_limit=1,attempts=1)
        attempt = [a for a in result['attempts'] if a['name'] == 'MILP_0'][0]
        self.assertEqual(attempt['status'],'EXACT_BANK_INCOMPATIBLE')
        self.assertEqual(result['certificate']['signs'],[1,1,1])
        fake.x = np.array([0.6,0.6])
        with patch.object(W,'milp',return_value=fake):
            result = W.solve_model(self.model(),bank(),time_limit=1,attempts=1)
        attempt = [a for a in result['attempts'] if a['name'] == 'MILP_0'][0]
        self.assertEqual(attempt['status'],'EXACT_COMPATIBLE_CERTIFICATE')
        self.assertEqual(attempt['max_integer_rounding_deviation'],0.4)

    def test_fixed_thread_option_warning_schedule_and_determinism(self):
        original = W.milp
        options = []
        def observed(*args,**kwargs):
            # SciPy consumes recognized keys from its options dictionary.
            # Snapshot before delegation to inspect exactly what was passed.
            options.append(dict(kwargs['options']))
            return original(*args,**kwargs)
        with patch.object(W,'milp',side_effect=observed) as propose:
            first = W.solve_model(self.model(),[],time_limit=1,attempts=4,seed=91)
        self.assertEqual(propose.call_count,4)
        for passed in options:
            self.assertEqual(passed['threads'],1)
            self.assertEqual(passed['time_limit'],1.)
            self.assertEqual(passed['node_limit'],first['milp_node_limit'])
        for attempt in first['attempts']:
            if attempt['name'].startswith('MILP_'):
                self.assertTrue(any('passed to HiGHS verbatim' in w for w in attempt['warnings']))
        second = W.solve_model(self.model(),[],time_limit=1,attempts=4,seed=91)
        self.assertEqual(first['certificate'],second['certificate'])
        self.assertEqual(first['predeclared_objectives'],second['predeclared_objectives'])

    def test_preallocation_precision_work_native_and_schema_gates(self):
        huge = dict(column=[1,2**50,2**50+1],denominator=1,cut=1,prime_pair_count=0)
        with patch.object(W.BANK,'integer_column',return_value=huge),patch.object(W,'milp') as propose:
            result = W.solve_model(self.model(),bank(),time_limit=1,attempts=4)
        propose.assert_not_called()
        self.assertEqual(result['status'],'NO_EXACT_COMPATIBLE_WITNESS_FOUND')
        self.assertNotIn('exact_infeasibility_proofs',result)
        self.assertTrue(any('float conversion50bit' in a.get('reason','') for a in result['attempts']))
        huge_den = dict(column=[0,0,0],denominator=2**4096,cut=1,prime_pair_count=0)
        with patch.object(W.BANK,'integer_column',return_value=huge_den),patch.object(W,'milp') as propose:
            result = W.solve_model(self.model(),bank(),time_limit=1)
        propose.assert_not_called()
        self.assertEqual(result['attempts'][0]['status'],'RESOURCE_LIMIT')
        model = self.model()
        model['price_dimension'] = 513
        with patch.object(W.BANK,'integer_column') as build,patch.object(W,'milp') as propose:
            result = W.solve_model(model,bank(),time_limit=1)
        build.assert_not_called();propose.assert_not_called()
        self.assertEqual(result['attempts'][0]['status'],'RESOURCE_LIMIT')
        model = self.model()
        model['meter'].limit = model['meter'].ops
        with patch.object(W,'milp') as propose:result = W.solve_model(model,bank(),time_limit=1)
        propose.assert_not_called()
        self.assertIsNone(result['certificate'])
        with patch.dict(W.os.environ,{'OPENBLAS_NUM_THREADS':'2','OMP_NUM_THREADS':'1'}),patch.object(W,'milp') as propose:
            result = W.solve_model(self.model(),[],time_limit=1)
        propose.assert_not_called()
        self.assertIsNotNone(result['certificate'])
        self.assertTrue(any('before process launch' in a.get('reason','') for a in result['attempts']))
        for option,value in [('attempts',True),('attempts',17),('time_limit',False),('time_limit',float('inf')),('seed',-1),('node_limit',0),('local_steps',17)]:
            with self.assertRaises(ValueError):W.solve_model(self.model(),[],**{option:value})

    def test_empty_geometry_and_single_anchor_require_no_milp(self):
        p = program()
        outer = W.MIXED.SQUARE.O.synthesize(p)['certificate']
        for u in (1,4):
            with patch.object(W,'milp') as propose:
                result = W.solve_model(self.model(u),bank(),time_limit=1)
            propose.assert_not_called()
            self.assertEqual(result['status'],'EXACT_COMPATIBLE_BANK_WITNESS_PROPOSAL')
            cert = result['certificate']
            self.assertEqual(C.verify_lower(p,u,outer,bank(),cert)['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND')


if __name__ == '__main__':
    unittest.main()
