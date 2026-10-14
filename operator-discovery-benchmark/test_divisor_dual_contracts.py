"""Public full-defect, rational power, forcing, charging and inference contracts."""
import unittest
from fractions import Fraction as Q
import flint
import divisor_dual_grammar as g
from divisor_dual_search import mask_inference,kernel_inference
from check_divisor_dual import matrix,direct_inverse,ceiling
from check_signed_control import independent_inverse


def program(**kw):
    p={'arithmetic_model':'inverse_one','mask':{'kind':'above','threshold':1},'diagonal_coefficient':'1','level_power':'1/6','Gram_power':'5','Gram_coefficient':'4'};p.update(kw);return p


class Contracts(unittest.TestCase):
    def test_inverse_actual_prime_arithmetic(self):
        v,response=direct_inverse(['0']+['1']*256);self.assertEqual(v,list(map(Q,independent_inverse(256)[0])));self.assertEqual(response,[1]+[0]*255)

    def test_complete_divisor_gram_annihilates_actual_inverse(self):
        N=32;mu=independent_inverse(N)[0][1:];G=g.gram({'kind':'above','threshold':1},N);self.assertEqual([sum(a*b for a,b in zip(row,mu)) for row in G],[0]*N)

    def test_floor_lcm_all_rows_kernel(self):
        from math import lcm
        N=24;G=g.gram({'kind':'constant','value':1},N)
        for n in range(1,N+1):
            for m in range(1,N+1):self.assertEqual(G[n-1][m-1],N//lcm(n,m))

    def test_full_signed_matrix_equals_two_window_energy(self):
        X=8;v=independent_inverse(4*X)[0];M=[0]
        for a in v[1:]:M.append(M[-1]+a)
        H=g.Hmatrix(X);self.assertEqual(sum(v[n+1]*H[n][m]*v[m+1] for n in range(4*X) for m in range(4*X)),sum(M[n]**2 for n in range(2*X,4*X))-4*sum(M[n]**2 for n in range(X,2*X)))

    def test_independent_complete_matrix_and_rational_cost(self):
        p=program();params,S=g.matrix(p,4,3);other,A,den=matrix(p,4,3);self.assertEqual(params,other);self.assertEqual(S,[[Q(a,den) for a in row] for row in A])

    def test_unit_forcing_is_fully_charged(self):
        for mask in [{'kind':'constant','value':1},{'kind':'above','threshold':1}]:
            p=program(mask=mask,Gram_power='2');a=g.parameters(p,8,3);self.assertEqual(Q(a['charged_defect_bound']),32*Q(a['D'])+Q(a['Y'])*g.mask_value(mask,1,32))

    def test_unit_high_power_rejected_for_RH_cost(self):
        self.assertFalse(g.family_certificate(program(mask={'kind':'constant','value':1}))['admitted']);self.assertTrue(g.family_certificate(program())['admitted'])

    def test_fixed_and_growing_parameter_constants_distinguished(self):
        self.assertTrue(g.family_certificate(program(level_power='0'))['bounded_level_constants_would_imply_stronger_fixed_critical_bound']);self.assertFalse(g.family_certificate(program())['bounded_level_constants_would_imply_stronger_fixed_critical_bound'])

    def test_fractional_roots_and_split_ceiling(self):
        for n,r,expected in [(729,'1/2',27),(1001,'1/3',11),(4096,'1/6',4),(2,'9/2',32)]:self.assertEqual(g.ceil_power(n,r),expected);self.assertEqual(ceiling(n,r),expected)

    def test_huge_denominator_has_semantics(self):
        for q in [2**64+1,10**100]:self.assertEqual(g.ceil_power(8192,Q(1,q)),2);self.assertEqual(ceiling(8192,Q(1,q)),2)

    def test_bad_mask_and_generic_model_rejected(self):
        self.assertFalse(g.mask_certificate({'kind':'residue','modulus':2,'residue':3})['admitted']);self.assertFalse(g.family_certificate(program(arithmetic_model='generic_sequence'))['admitted'])

    def test_generic_inverse_norm_does_not_transfer(self):
        v,response=direct_inverse(['0','1','-1000','1','1']);self.assertGreater(max(abs(z) for z in v),1);self.assertEqual(response,[1,0,0,0])

    def test_finite_native_positive_independent_exact_minors(self):
        p=program();c=g.certify(p,4,2);self.assertTrue(c['finite_matrix_PSD']);self.assertFalse(c['global_PSD_proved']);params,A,den=matrix(p,4,2)
        for k in range(1,len(A)+1):self.assertGreater(flint.fmpz_mat([row[:k] for row in A[:k]]).det(),0)

    def test_exact_negative_direction_rejects_only_matrix(self):
        p=program(mask={'kind':'constant','value':0},diagonal_coefficient='1/4');c=g.certify(p,4,6);self.assertFalse(c['finite_matrix_PSD']);self.assertLess(Q(c['counterexample']['exact_quadratic_value']),0);self.assertTrue(c['counterexample']['rejects_candidate_matrix_not_actual_RH_inequality'])

    def test_global_generic_calibration_is_only_q1_power_three(self):
        p=program(diagonal_coefficient='4');c=g.certify(p,4,1);self.assertTrue(c['global_PSD_proved']);self.assertEqual(c['parameters']['ordinary_energy_power'],'3');self.assertFalse(c['global_critical_PSD_proved'])

    def test_anonymous_inference_accepts_unanticipated_mask(self):
        result=mask_inference([[1],[0],[1],[0]],[({'kind':'synthetic'},[0,1,0,1]),({'kind':'wrong'},[1,0,1,0])]);self.assertEqual(result[0]['mask']['kind'],'synthetic');self.assertEqual(result[0]['exact_squared_residual'],0)

    def test_anonymous_kernel_fit_accepts_other_feature(self):
        fit=kernel_inference(list(map(Q,[3,6,9])),{'unexpected':[Q(1),Q(2),Q(3)],'wrong':[Q(1)]*3});self.assertEqual(fit[0]['feature'],'unexpected');self.assertEqual(fit[0]['coefficient'],'3');self.assertEqual(fit[0]['relative_squared_residual'],'0')


if __name__=='__main__':unittest.main()
