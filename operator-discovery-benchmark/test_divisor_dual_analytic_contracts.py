"""Analytical barriers against arbitrary Gram weights and unchanged formulas."""
import unittest
from copy import deepcopy
from fractions import Fraction as Q
from divisor_dual_analytic_review import obstruction,count_unselected,witness
from check_divisor_dual_analytic import count,audit_witness


def program(mask,**kw):
    p={'arithmetic_model':'inverse_one','mask':mask,'diagonal_coefficient':'1/4','level_power':'1/6','Gram_power':'6','Gram_coefficient':'4'};p.update(kw);return p


class Contracts(unittest.TestCase):
    def test_any_Gram_weight_cannot_fix_uncovered_residue(self):
        p=program({'kind':'residue','modulus':4,'residue':1},Gram_power='20',Gram_coefficient=str(10**100));self.assertEqual(obstruction(p),'uncovered_tail_rows');w=witness(p,7,obstruction(p));audit_witness(p,w);self.assertTrue(w['Gram_quadratic_exactly_zero'])

    def test_divisor_union_and_square_and_prefix_barriers(self):
        for mask in [{'kind':'divisible_union','bases':[2,3]},{'kind':'square'},{'kind':'prefix','power':'1/3'}]:
            p=program(mask);w=witness(p,2,obstruction(p));audit_witness(p,w)

    def test_nonunit_full_Gram_not_rejected_by_coverage(self):
        self.assertIsNone(obstruction(program({'kind':'above','threshold':1})))

    def test_quadratic_Gram_coefficient_obstruction(self):
        for cy in ['1/4','1','4/3']:
            p=program({'kind':'above','threshold':1},Gram_power='2',Gram_coefficient=cy);method=obstruction(p)
            self.assertEqual(method,None if Q(cy)==Q(4,3) else 'underpowered_quadratic_Gram')
            if method:audit_witness(p,witness(p,3,method))

    def test_exact_counts_independent_and_direct(self):
        masks=[{'kind':'residue','modulus':3,'residue':2},{'kind':'divisible_union','bases':[2,3]},{'kind':'square'},{'kind':'prefix','power':'1/3'}]
        from check_divisor_dual import weight
        for mask in masks:
            a=count_unselected(mask,32,48,64);self.assertEqual(a,count(mask,32,48,64));self.assertEqual(a,sum(not weight(mask,n,64) for n in range(33,49)))

    def test_analytical_attempt_does_not_mutate_program(self):
        p=program({'kind':'residue','modulus':2,'residue':0});original=deepcopy(p);w=witness(p,2,obstruction(p));self.assertEqual(p,original);self.assertTrue(w['negative_matrix_witness_is_not_RH_counterexample'])


if __name__=='__main__':unittest.main()
