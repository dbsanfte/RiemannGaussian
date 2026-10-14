"""Synthetic affine algebra only; no saved chart, endpoint or research source."""
from fractions import Fraction as F
import time
import unittest
import check_primitive_state_feedback_affine as C

def budget(**kw):return C.Budget(time.monotonic()+30,**kw)
def layout():
    return C.projection_layout(dict(shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',15]]))
def feedback():
    row={0:F(2),366:F(3),367:F(-3),1597:F(5),1717:F(7),1837:F(-23)}
    return dict(schema='primitive-state-formal-identity-necessary-row-v1',assignment=[2*n+1 for n in range(1,28)],width=1957,X=7,layout=dict(n_variables=1957),entries=[dict(index=i,coefficient=str(q))for i,q in sorted(row.items())],zero_coordinates=[i for i in range(1957)if i not in row],rhs='11')
class Soundness(unittest.TestCase):
    def test_leading_free_does_not_stop_elimination(self):
        basis={2:{2:F(1),3:F(3),4:F(5)}}
        kind,new,rec=C.reduce_feedback([F(0),F(1),F(2),F(0)],F(7),basis,budget())
        self.assertEqual(kind,'independent');self.assertEqual(new,{1:F(1),3:F(-6),4:F(-3)})
        out=C.backsubstitute(basis|{1:new},[F(0),F(99),F(88),F(2)],budget())
        self.assertEqual(out,[F(0),F(9),F(-1),F(2)])
    def test_old_source_order_is_not_pivot_order(self):
        basis={2:{2:F(1),3:F(1),4:F(4)},0:{0:F(1),2:F(2),4:F(9)}}
        kind,new,rec=C.reduce_feedback([F(1),F(1),F(0),F(0)],F(8),basis,budget())
        self.assertEqual(rec['multipliers'],[[0,'1'],[2,'-2']])
        self.assertEqual(new,{1:F(1),3:F(2),4:F(7)})
        out=C.backsubstitute(basis|{1:new},[F(0),F(0),F(0),F(3)],budget())
        self.assertEqual(out,list(map(F,[7,1,1,3])))
    def test_redundancy_and_contradiction_do_not_create_pivot(self):
        basis={0:{0:F(1),1:F(2),2:F(3)}}
        for rhs,expected in [(6,'redundant'),(7,'inconsistent')]:
            kind,new,rec=C.reduce_feedback([F(2),F(4)],F(rhs),basis,budget())
            self.assertEqual(kind,expected);self.assertIsNone(new);self.assertIsNone(rec['chosen_pivot'])
    def test_signed_storage_projection_and_canonical_lift(self):
        retained,recipes=layout();seed=['0']*1957
        for i,q in {366:2,367:5,1597:3,1717:7,1837:2}.items():seed[i]=str(q)
        original,y=C.projected_seed(seed,retained,recipes,budget());lift=C.lift(y,retained,budget());pos={i:k for k,i in enumerate(retained)}
        self.assertEqual(y[pos[366]],-3);self.assertEqual(y[pos[1597]],5);self.assertEqual(y[pos[1717]],-1)
        self.assertEqual([lift[i]for i in [366,367,1597,1717,1837]],list(map(F,[0,3,0,19,5])))
        f,p,rhs=C.decode_feedback(feedback(),retained,recipes,budget())
        self.assertEqual(sum(a*b for a,b in zip(f,original)),sum(a*b for a,b in zip(f,lift)))
        self.assertEqual(sum(a*b for a,b in zip(f,lift)),sum(a*b for a,b in zip(p,y)))
    def test_altered_storage_or_signed_pair_rejected(self):
        retained,recipes=layout()
        for index,value in [(1837,'-22'),(367,'3')]:
            f=feedback();next(e for e in f['entries']if e['index']==index)['coefficient']=value
            with self.assertRaises(ValueError):C.decode_feedback(f,retained,recipes,budget())
    def test_missing_zero_coordinate_rejected(self):
        retained,recipes=layout();f=feedback();f['zero_coordinates'].pop()
        with self.assertRaises(ValueError):C.decode_feedback(f,retained,recipes,budget())
    def test_wrong_parent_storage_map_rejected(self):
        original=dict(shape=[366,613],offset=1597,specs=[['full_child',15],['full_parent',15],['storage_K',14]])
        with self.assertRaises(ValueError):C.projection_layout(original)
    def test_changed_rhs_detected_at_complete_endpoint(self):
        x=[F(0)]*1957;x[0]=F(3);row=[F(0)]*1957;row[0]=F(2)
        good=C.endpoint_check([{0:F(2)}],[F(6)],row,F(6),x,budget())
        self.assertTrue(good['finite_original_candidate_feasible'])
        bad=C.endpoint_check([{0:F(2)}],[F(7)],row,F(8),x,budget())
        self.assertEqual(bad['equality_mismatch_count'],1);self.assertEqual(bad['new_row_residual'],'-2');self.assertFalse(bad['finite_original_candidate_feasible'])
    def test_zero_psd_pivot_with_cross_is_not_psd(self):
        answer=C.exact_psd([[F(0),F(1)],[F(1),F(0)]],budget())
        self.assertFalse(answer['psd']);self.assertLess(F(answer['quadratic_value']),0)
    def test_work_and_bit_caps(self):
        with self.assertRaises(OverflowError):C.reduce_feedback([F(2),F(4)],F(7),{0:{0:F(1),1:F(2),2:F(3)}},budget(max_operations=1))
        with self.assertRaises(OverflowError):C.projected_seed(['8']+['0']*1956,*layout(),budget(max_bits=3))
if __name__=='__main__':unittest.main()
