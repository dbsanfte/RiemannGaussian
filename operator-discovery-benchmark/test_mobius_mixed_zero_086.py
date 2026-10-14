from fractions import Fraction as Q
import unittest
from unittest.mock import patch

import numpy as np
from flint import fmpq_mat

import mobius_mixed_zero_086 as M
from test_mobius_coupled_square_084 import program


def compatible_bank(n):
    # Three columns, one exact dependence, with a known artificial Boolean
    # all-one annihilated vector. These signs are not asserted to be Mobius.
    rows = [['0','0','0'] for _ in range(n)]
    if n >= 3:
        rows[0] = ['1','2','0']
        rows[1] = ['-1','-2','1']
        rows[2] = ['0','0','-1']
    return rows


class MixedZeroTests(unittest.TestCase):
    def model(self):
        return M.build_model(program(),53)

    def test_half_sum_is_exactly_zero_and_all_pairs_are_priced(self):
        model = self.model()
        n = model['price_dimension']
        V = compatible_bank(n)
        W = [[str(Q(i+j-2,3+j)) for j in range(3)] for i in range(n)]
        Z = M.correction(model,V,W)
        one = fmpq_mat([[1] for _ in range(n)])
        self.assertEqual((one.transpose()*Z*one)[0,0],0)
        self.assertEqual(Z,Z.transpose())
        factor = [[i-2,1-i] for i in range(n)]
        cert,diag = M.certificate(model,V,W,8,factor)
        R = M.original_remainder(model)
        exact_rows = []
        for i in range(n):
            row = Q(0)
            for j in range(n):
                mixed = sum((Q(V[i][k])*Q(W[j][k])+Q(W[i][k])*Q(V[j][k])
                             for k in range(3)),Q(0))/2
                square = Q(sum(factor[i][k]*factor[j][k] for k in range(2)),64)
                value = Q(str(R[i,j]))+mixed+square
                row += value if i == j else abs(value)
            exact_rows.append(row)
        self.assertEqual(cert['row_prices'],list(map(str,exact_rows)))
        self.assertEqual(Q(cert['price']),sum(exact_rows,Q(0)))
        self.assertEqual(diag['effective_dimension'],n)
        self.assertEqual(cert['partner_matrix'],W)
        # This quadratic upper bound holds on every compatible artificial
        # Boolean vector; the square is genuinely positive despite signed Z.
        actual = Q(str((one.transpose()*R*one)[0,0]))
        self.assertLessEqual(actual,Q(cert['price']))

    def test_exact_projection_identity_with_rank_change_and_full_embedding(self):
        model = self.model()
        n = model['price_dimension']
        V = M.parse_vectors(model,compatible_bank(n))
        W,diagnostics = M.projection_partner(model,V)
        self.assertEqual(diagnostics['active_identity_columns'],[0,2])
        self.assertEqual(diagnostics['identity_rank'],2)
        self.assertTrue(all(W[i,1] == 0 for i in range(n)))
        U = fmpq_mat([[V[i,j] for j in [0,2]] for i in range(n)])
        Pi = fmpq_mat([[int(i == j) for j in range(n)] for i in range(n)])-U*(U.transpose()*U).inv()*U.transpose()
        R = M.original_remainder(model)
        corrected = R+M.correction(model,V,W)
        self.assertEqual(corrected,Pi*R*Pi)
        self.assertEqual(corrected*U,fmpq_mat(n,2))
        zero = fmpq_mat(n,3)
        partner,zero_diag = M.projection_partner(model,zero)
        self.assertEqual(partner,zero)
        self.assertEqual(zero_diag['identity_rank'],0)

    def test_scs_partner_unscaling_is_exact_and_keeps_dependent_columns(self):
        model = self.model()
        V = M.parse_vectors(model,compatible_bank(model['price_dimension']))
        floating = np.array([[0.25,-0.5],[0.125,0.75],[-0.25,0.5]])
        W = M._rounded_partner(model,V,[0,2],[Q(3),Q(5,2)],floating,53,8)
        self.assertEqual(Q(str(W[0,0])),Q(53,12))
        self.assertEqual(Q(str(W[0,2])),Q(-53,5))
        self.assertTrue(all(W[i,1] == 0 for i in range(3)))

    def test_solver_retains_global_baseline_and_every_attempt(self):
        model = self.model()
        V = compatible_bank(model['price_dimension'])
        report = M.solve_model(model,V,time_limit=2)
        self.assertEqual(report['status'],'EXACT_MIXED_ZERO_SQUARE_PROPOSAL')
        self.assertEqual(report['identity_rank'],2)
        self.assertTrue(report['original_boolean_coordinates_retained'])
        self.assertTrue(report['same_bank_ideal_sdp_infimum_as_085'])
        self.assertFalse(report['uniform_remaining_bound_proved'])
        self.assertFalse(report['RH_proved'])
        exact = [a for a in report['attempts'] if a['status'] == 'EXACT_CERTIFICATE']
        self.assertGreaterEqual(len(exact),3)
        self.assertEqual(Q(report['certificate']['price']),min(Q(a['certificate']['price']) for a in exact))
        for attempt in exact:
            cert = attempt['certificate']
            rows = [[int(q) for q in row] for row in cert['factor_numerators']]
            independently,diag = M.certificate(self.model(),V,cert['partner_matrix'],int(cert['factor_denominator']),rows)
            self.assertEqual(cert,independently)

    def test_solver_failure_and_resource_failure_preserve_exact_incumbent(self):
        model = self.model()
        V = compatible_bank(model['price_dimension'])
        with patch.object(M.cp.Problem,'solve',side_effect=M.cp.error.SolverError('deliberate tiny test')):
            report = M.solve_model(model,V,time_limit=2,projection=False)
        self.assertEqual(report['selected_attempt'],'ZERO_CONTROL_ZERO_FACTOR')
        self.assertEqual(report['attempts'][-1]['status'],'PROPOSAL_FAILURE')
        self.assertIn('deliberate tiny test',report['attempts'][-1]['reason'])
        with patch.object(M,'_projection_partner',side_effect=M.B.ResourceLimit('prospective test gate')):
            report = M.solve_model(self.model(),V,time_limit=2)
        self.assertEqual(report['attempts'][1]['status'],'RESOURCE_LIMIT')
        self.assertLessEqual(Q(report['certificate']['price']),Q(report['attempts'][0]['certificate']['price']))

    def test_schema_and_prospective_resource_gates(self):
        model = self.model()
        n = model['price_dimension']
        for bad in ([['1/2','2/4'] for _ in range(n)], [['0'] for _ in range(n-1)], [['0']*17 for _ in range(n)]):
            with self.assertRaises(ValueError):M.parse_vectors(model,bad)
        with self.assertRaises(ValueError):M.correction(model,compatible_bank(n),[['0'] for _ in range(n)])
        with self.assertRaises(ValueError):M.certificate(model,compatible_bank(n),[['0']*3 for _ in range(n)],3,[[] for _ in range(n)])
        with self.assertRaises(ValueError):M.solve_model(model,compatible_bank(n),partner_bits=True)
        model['price_dimension'] = 513
        with self.assertRaises(M.B.ResourceLimit):M.parse_vectors(model,[])
        model = self.model()
        model['resident_bytes'] = M.B.OLD.MAX_BYTES
        with self.assertRaises(M.B.ResourceLimit):M.projection_partner(model,compatible_bank(n))
        model = self.model()
        model['meter'].limit = model['meter'].ops
        with self.assertRaises(M.B.ResourceLimit):M.parse_vectors(model,compatible_bank(n))
        model = self.model()
        with self.assertRaises(M.B.ResourceLimit):
            M._gate(model,bits=M.B.OLD.MAX_BITS+1)
        with self.assertRaises(M.B.ResourceLimit):
            M._rounded_partner(model,M.parse_vectors(model,compatible_bank(n)),[0,2],[Q(1),Q(1)],np.full((n,2),1e100),53,24)

    def test_empty_geometry_and_empty_bank(self):
        model = M.build_model(program(),1)
        V = fmpq_mat(0,3)
        report = M.solve_model(model,V,time_limit=2)
        self.assertEqual(report['certificate']['price'],'0')
        self.assertEqual(report['bank_size'],3)
        self.assertEqual(report['certificate']['partner_matrix'],[])
        model = self.model()
        n = model['price_dimension']
        report = M.solve_model(model,[[] for _ in range(n)],time_limit=2)
        self.assertEqual(report['identity_rank'],0)
        self.assertEqual(report['certificate']['partner_matrix'],[[] for _ in range(n)])

    def test_typed_arithmetic_bank_all_attempts_independently_admitted(self):
        import check_mobius_arithmetic_bank_086 as C
        p = program()
        u = 53
        outer = M.SQUARE.O.synthesize(p)['certificate']
        bank = [dict(kind='divisor',cut=dict(scale='1/3',u_exponent='1',complement=False,unit_balance=True)),
                dict(kind='prime_pair',cut_on='prime',cut=dict(scale='1',u_exponent='1',complement=False),weight=dict(kind='one')),
                dict(kind='prime_pair',cut_on='cofactor',cut=dict(scale='1/3',u_exponent='1',complement=False),weight=dict(kind='source',i=0))]
        independent_model = C.C.build_model(p,u)
        supplied = C.build_identities(independent_model,bank)['vectors']
        V = [[str(q) for q in row] for row in supplied]
        report = M.solve(p,V,u,time_limit=2)
        for attempt in report['attempts']:
            if attempt['status'] == 'EXACT_CERTIFICATE':
                admission = C.verify_upper(p,u,outer,bank,attempt['certificate'])
                self.assertEqual(admission['status'],'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND',admission)
        self.assertEqual(C.verify_upper(p,u,outer,bank,report['certificate'])['status'],
                         'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND')


if __name__ == '__main__':
    unittest.main()
