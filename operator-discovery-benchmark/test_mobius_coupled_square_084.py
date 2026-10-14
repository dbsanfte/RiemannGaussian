import copy
import unittest
from fractions import Fraction as Q
import numpy as np
import mobius_coupled_square_084 as P
import check_mobius_coupled_square_084 as C
import test_mobius_coupled_completion_083 as FIX


def program(extended=False):
    p=FIX.program(extended);p['prime_anchor']=True
    for term in p['coupled_terms'][:2]:term['theta']='5/2'
    return p


class SquareTests(unittest.TestCase):
    def test_residual_linear_basis_matches_complete_exact_operator(self):
        p=program(True);p['coupled_terms'][2]['theta']='1/7';p['gram_weights'][1]='1/9'
        model=P.B.build_model(p,137);A=P.native_base(model)
        for k,term in enumerate(p['coupled_terms']):A+=P.native_template(model,k)*P.fmpq(term['theta'])
        actual=P.B.project_native(model,P.R.raw_remainder(model))
        self.assertEqual(A,actual)

    def test_exact_factor_empty_and_nonzero_admitted(self):
        p=program();outer=P.O.synthesize(p)['certificate'];model=P.B.build_model(p,131);n=model['price_dimension']
        for rows,den in [([[]for _ in range(n)],1),([[i-2,1-i]for i in range(n)],8)]:
            cert,diag=P.certificate(model,den,rows)
            admission=C.verify_certificate(p,131,outer,cert)
            self.assertEqual(admission['status'],'VERIFIED_FINITE_COUPLED_SQUARE_BOUND',admission)
            self.assertEqual(admission['factor_trace'],diag['factor_trace'])
            self.assertEqual(admission['old_residual_price'],diag['old_residual_price'])
            if den==1:self.assertEqual(cert['price'],diag['old_residual_price'])

    def test_factor_projection_and_exact_unit_norm_dual(self):
        p=program(True);p['gram_weights'][1]='2/3';model=P.B.build_model(p,131);n=model['price_dimension']
        M=np.arange(n*n,dtype=float).reshape((n,n));M=M+M.T
        den,rows=P.factor_from_psd(M,unit_rows=True)
        self.assertTrue(all(sum(v*v for v in row)<=den*den for row in rows))
        eq=P.theta_equalities(p);dual=P.dual_certificate(model,den,rows,[Q(i-1,7)for i in range(len(eq['rows']))])
        admission=C.verify_dual(p,131,P.O.synthesize(p)['certificate'],dual)
        self.assertEqual(admission['status'],'VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND',admission)

    def test_joint_operator_and_square_invention_exact_admissions(self):
        result=P.solve(program(),131,time_limit=10)
        self.assertEqual(result['status'],'EXACT_SQUARE_PROPOSAL',result)
        p=result['program'];outer=result['outer_certificate']
        self.assertEqual(C.verify_certificate(p,131,outer,result['certificate'])['status'],'VERIFIED_FINITE_COUPLED_SQUARE_BOUND')
        self.assertEqual(C.verify_dual(p,131,outer,result['dual'])['status'],'VERIFIED_FINITE_COUPLED_SQUARE_GRAMMAR_LOWER_BOUND')
        self.assertGreaterEqual(Q(result['exact_gap']),0)
        self.assertLessEqual(Q(result['certificate']['price']),Q(result['diagnostics']['old_residual_price']))

    def test_fixed_operator_auxiliary_reconstruction(self):
        p=program();result=P.solve(p,137,optimize_operator=False,time_limit=10)
        self.assertEqual(result['status'],'EXACT_SQUARE_PROPOSAL',result)
        self.assertEqual(result['program'],p)
        self.assertEqual(C.verify_certificate(p,137,result['outer_certificate'],result['certificate'])['status'],'VERIFIED_FINITE_COUPLED_SQUARE_BOUND')

    def test_prospective_dimension_factor_and_resident_gates(self):
        model=P.B.build_model(program(),131);model['price_dimension']=513
        with self.assertRaises(P.B.ResourceLimit):P.certificate(model,1,[])
        model=P.B.build_model(program(),131);model['resident_bytes']=P.B.OLD.MAX_BYTES
        with self.assertRaises(P.B.ResourceLimit):P.native_template(model,0)
        with self.assertRaises(ValueError):P.factor_from_psd(np.eye(2),bits=49)
        with self.assertRaises(ValueError):P.factor_from_psd(np.eye(2),bits=True)
        with self.assertRaises(P.B.ResourceLimit):P.factor_from_psd(np.empty((513,513)))
        with self.assertRaises(P.B.ResourceLimit):P.factor_from_psd(np.eye(4),meter=P.B.Meter(limit=1))


if __name__=='__main__':unittest.main()
