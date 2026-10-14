"""Tiny exact recovery checks; no publication inputs or research runs."""
from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import check_primitive_state_backtracking_recovery as R
import check_primitive_state_feedback_affine as A

def budget(**kw):return A.Budget(time.monotonic()+30,**kw)

class Soundness(unittest.TestCase):
    def test_complete_backsub_including_learned_row(self):
        center=F(1)+F(1,1<<535);free=center+F(1,4)
        # Original row x0-2*x1=3; appended row x1+x2=0.
        rows={0:{0:F(1),1:F(-2),3:F(3)},1:{1:F(1),2:F(1)}}
        point=A.backsubstitute(rows,[F(0),F(0),free],budget())
        self.assertEqual(point,[3-2*free,-free,free])
        self.assertGreater(point[2].denominator.bit_length(),269)
        self.assertEqual(point[0]-2*point[1],3)
        self.assertEqual(point[1]+point[2],0)
    def test_omitting_learned_row_changes_point(self):
        rows={0:{0:F(1),1:F(-2),3:F(3)}}
        point=A.backsubstitute(rows,[F(0),F(0),F(5,4)],budget())
        self.assertNotEqual(point[1]+point[2],0)
    def test_sign_rejection_is_point_specific(self):
        # Equation x0+x1=1 has both infeasible and feasible points.
        bad=[F(-1,10**50),F(1)+F(1,10**50)]
        good=[F(1,2),F(1,2)]
        self.assertEqual(sum(bad),1);self.assertLess(bad[0],0)
        self.assertEqual(sum(good),1);self.assertTrue(all(q>=0 for q in good))
    def test_failed_producer_temporary_is_not_licensed_result(self):
        with self.assertRaises(OverflowError):budget().rational(F(1<<4203))
        with self.assertRaises(OverflowError):budget().mul(F(1<<2102),F(1<<2102))
    def test_negative_scalar_skips_all_psd(self):
        x=[F(0)]*1957;x[1596]=F(-1,10**50)
        with patch.object(R.CORE.AFFINE,'exact_psd',side_effect=AssertionError('PSD must not run')):
            d=R.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[F(0)]*1957,F(0),x,budget())
        self.assertFalse(d['finite_candidate_feasible'])
        self.assertEqual(d['psd_status'],'NOT_CHECKED_AFTER_SCALAR_REJECTION')
        self.assertIsNone(d['psd_blocks']);self.assertIsNone(d['PSD_failures'])
        self.assertEqual(d['scalar_rejection_witness']['coordinate'],1596)
    def test_passing_signs_requires_three_psd_blocks(self):
        with patch.object(R.CORE.AFFINE,'exact_psd',return_value={'psd':True})as psd:
            d=R.scalar_first_endpoint([{}for _ in range(5641)],[F(0)]*5641,[F(0)]*1957,F(0),[F(0)]*1957,budget())
        self.assertEqual(psd.call_count,3);self.assertEqual(d['PSD_blocks_checked'],3)
    def test_equation_failure_prevents_scalar_rejection_record(self):
        x=[F(0)]*1957;x[0]=F(-1)
        with patch.object(R.CORE.AFFINE,'exact_psd',side_effect=AssertionError('PSD must not run')):
            with self.assertRaises(ValueError):
                R.scalar_first_endpoint([{0:F(1)}]+[{}for _ in range(5640)],[F(0)]*5641,[F(0)]*1957,F(0),x,budget())
    def test_shared_budget_cannot_reset_between_phases(self):
        b=budget(max_operations=8)
        A.backsubstitute({0:{0:F(1),1:F(1)}},[F(0),F(1)],b)
        with self.assertRaises(OverflowError):
            for _ in range(10):b.rational(0)

if __name__=='__main__':unittest.main()
