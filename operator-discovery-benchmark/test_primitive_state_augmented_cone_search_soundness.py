"""Proof-focused tiny charts only; no published map, point or probe reads."""
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_augmented_cone_search as C
import check_primitive_state_feedback_affine as A
import primitive_state_augmented_cone_search as P

def b():return A.Budget(time.monotonic()+30)
def rows():return {0:{0:F(1),160:F(-2)},160:{160:F(1),170:F(-2),780:F(3),1224:F(5)},170:{170:F(1),781:F(4),1224:F(7)}}
class Soundness(unittest.TestCase):
    def test_coupled_appended_pivots_and_exact_free_preservation(self):
        seed=[F(0)]*1224;seed[780]=F(1)+F(1,1<<535);seed[781]=F(1,4)
        x=A.backsubstitute(rows(),seed,b())
        self.assertEqual(x[170],6);self.assertEqual(x[160],17-3*seed[780])
        self.assertEqual(x[0],2*x[160]);self.assertEqual(x[780:],seed[780:])
        self.assertGreater(x[780].denominator.bit_length(),269)
    def test_rhs_omitted_for_homogeneous_map_and_support_propagates(self):
        homogeneous={p:{j:q for j,q in r.items()if j<1224}for p,r in rows().items()}
        seed=[F(0)]*1224;seed[781]=1
        x=A.backsubstitute(homogeneous,seed,b())
        self.assertEqual((x[170],x[160],x[0]),(-4,-8,-16))
        wrong=A.backsubstitute(rows(),seed,b())
        self.assertNotEqual(x,wrong)
    def test_unaffected_old_column_stays_identical(self):
        seed=[F(0)]*1224;seed[782]=1
        old={0:{0:F(1),160:F(-2)}}
        new={p:{j:q for j,q in r.items()if j<1224}for p,r in rows().items()}
        self.assertEqual(A.backsubstitute(old,seed,b()),A.backsubstitute(new,seed,b()))
    def test_exact_center_plus_exported_dyadic_not_rounded_center(self):
        center=F(1)+F(1,1<<535);z=F(1,1<<268);D=F(1,4)
        exact=b().add(center,b().mul(D,z))
        self.assertEqual(exact-center,F(1,1<<270))
        self.assertNotEqual(exact,F(1)+D*z)
    def test_canonical_signed_and_storage_lift(self):
        retained,_=A.projection_layout({'shape':[366,613],'offset':1597,'specs':[['full_child',15],['full_parent',15],['storage_K',15]]})
        y=[F(0)]*1224;position={j:i for i,j in enumerate(retained)}
        y[position[366]]=F(-3);y[position[1597]]=F(2);y[position[1717]]=F(-7)
        x=A.lift(y,retained,b())
        self.assertEqual((x[366],x[367]),(0,3))
        self.assertEqual((x[1597],x[1717],x[1837]),(0,1,2))
    def test_actual_generic_composer_coupled_support(self):
        old=[{'pivot':0,'terms':[[0,'1'],[1,'-2']]}]
        appended=[{'pivot':1,'terms':[[1,'1'],[2,'-2'],[4,'5']]},{'pivot':2,'terms':[[2,'1'],[3,'4'],[4,'7']]}]
        chart,pivots,free,affected=P.compose_chart(old,appended,4,P.Budget(time.monotonic()+30))
        self.assertEqual((pivots,free,affected),([0,1,2],[3],[3]))
        homogeneous={p:{j:q for j,q in row.items()if j<4}for p,row in chart.items()}
        self.assertEqual(A.backsubstitute(homogeneous,[F(0),F(0),F(0),F(1)],b()),[-16,-8,-4,1])
    def test_actual_generic_composer_rejects_uneliminated_old_pivot(self):
        with self.assertRaises(ValueError):
            P.compose_chart([{'pivot':2,'terms':[[2,'1']]}],[{'pivot':1,'terms':[[1,'1'],[2,'1']]}],4,P.Budget(time.monotonic()+30))
    def test_augmented_negative_scalar_skips_psd_after_all_three_rows(self):
        x=[F(0)]*1957;x[1596]=F(-1,10**50)
        with patch.object(C.AFFINE,'exact_psd',side_effect=AssertionError('PSD must not run')):
            d=C.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[[F(0)]*1957 for _ in range(3)],[F(0)]*3,x,b())
        self.assertEqual(d['full_equations_checked'],5644)
        self.assertEqual(d['PSD_blocks_checked'],0);self.assertIsNone(d['PSD_failures'])
        self.assertIsNone(d['psd_blocks']);self.assertFalse(d['finite_candidate_feasible'])
    def test_augmented_passing_signs_requires_all_psd(self):
        with patch.object(C.AFFINE,'exact_psd',return_value={'psd':True})as psd:
            C.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[[F(0)]*1957 for _ in range(3)],[F(0)]*3,[F(0)]*1957,b())
        self.assertEqual(psd.call_count,3)
    def test_malformed_learned_row_cannot_silently_zip(self):
        with self.assertRaises(ValueError):
            C.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[[],[F(0)]*1957,[F(0)]*1957],[F(0)]*3,[F(0)]*1957,b())
    def test_resource_failure_not_a_partial_point(self):
        seed=[F(0)]*1224;seed[780]=F(1<<4095)
        with self.assertRaises(OverflowError):A.backsubstitute(rows(),seed,b())

if __name__=='__main__':unittest.main()
