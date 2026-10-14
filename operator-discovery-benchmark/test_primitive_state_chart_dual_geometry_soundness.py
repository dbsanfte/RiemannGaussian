"""Small affine response and compression counterexamples only."""
from fractions import Fraction as F
import time
import unittest
import copy
import check_primitive_state_chart_dual_geometry_search as C
import primitive_state_chart_dual_geometry_search as P

def b():return P.Budget(time.monotonic()+30)
class Soundness(unittest.TestCase):
    def test_opposing_residuals_without_constant_cancellation_not_exposed(self):
        # s0+s1=1: s0=1-f, s1=f; both can bepositive.
        columns=[{0:F(-1),2:F(1)},{0:F(1)}]
        classes,zeros,exposures=P.discover_lines(columns,b())
        self.assertEqual(len(classes),2);self.assertEqual(zeros,[]);self.assertEqual(exposures,[])
    def test_full_opposite_classes_expose_every_member(self):
        columns=[{0:F(1),2:F(3)},{0:F(2),2:F(6)},{0:F(-1),2:F(-3)},{}]
        classes,zeros,exposures=P.discover_lines(columns,b())
        self.assertEqual(len(classes),1);self.assertEqual(zeros,[3])
        self.assertEqual([e['ray_index']for e in exposures],[0,1,2,3])
        for e in exposures:
            for coordinate in (0,2):
                self.assertEqual(sum((F(m['weight'])*columns[m['ray_index']].get(coordinate,F(0))for m in e['combination']),F(0)),0)
            self.assertTrue(all(F(m['weight'])>0 for m in e['combination']))
    def test_positive_only_column_merge_and_exact_representative_lift(self):
        columns=[{0:F(1),2:F(3)},{0:F(2),2:F(6)},{0:F(-1),2:F(-3)},{}]
        compressed,rhs,receipt=P.compress_model(columns,{2:F(-1)},[0,1,2],b())
        self.assertEqual(receipt['column_representatives'],[0,2])
        self.assertEqual(receipt['column_map'][1],{'representative':0,'positive_factor':'2'})
        self.assertIsNone(receipt['column_map'][3])
        self.assertEqual(receipt['column_map'][2]['representative'],2)
        # Mergeforward alpha=(0,1,0,0) toalpha_rep=(2,0), thenliftrep only.
        lifted=[F(2),F(0),F(0),F(0)]
        for i in (0,2):self.assertEqual(sum((a*c.get(i,F(0))for a,c in zip(lifted,columns)),F(0)),columns[1][i])
        self.assertNotEqual(sum(lifted),1) # L1 is intentionally changed.
    def test_augmented_row_compression_keeps_rhs_and_contradiction(self):
        columns=[{0:F(1),1:F(-2),2:F(1)}]
        compressed,rhs,receipt=P.compress_model(columns,{2:F(1),4:F(1)},[0,1,2,3,4],b())
        self.assertEqual(receipt['row_representatives'],[0,2,4])
        self.assertEqual(receipt['row_map'][1],{'representative':0,'signed_factor':'-2'})
        self.assertIsNone(receipt['row_map'][3])
        self.assertEqual(rhs[4],1);self.assertNotIn(4,compressed[0])
    def test_positive_line_alone_does_not_expose(self):
        _,_,exposures=P.discover_lines([{0:F(1)},{0:F(3)}],b())
        self.assertEqual(exposures,[])
    def test_zero_quadratic_face_implication_and_wrong_inference(self):
        # PSD matrixdiag(0,2) kills e0, but not the wholematrix.
        matrix=[[F(0),F(0)],[F(0),F(2)]];v=[F(1),F(0)]
        self.assertEqual([sum((row[j]*v[j]for j in range(2)),F(0))for row in matrix],[0,0])
        self.assertNotEqual(matrix,[[0,0],[0,0]])
        # WithoutPSD, v^T Mv=0 does NOT implyMv=0.
        indefinite=[[F(0),F(1)],[F(1),F(0)]]
        self.assertEqual(sum((v[i]*indefinite[i][j]*v[j]for i in range(2)for j in range(2)),F(0)),0)
        self.assertNotEqual([sum((row[j]*v[j]for j in range(2)),F(0))for row in indefinite],[0,0])
    def test_independent_geometry_and_compression_match(self):
        columns=[{0:F(1),1224:F(3)},{0:F(2),1224:F(6)},{0:F(-1),1224:F(-3)},{}]
        classes,zeros,exposures=P.discover_lines(columns,b())
        ib=C.Budget(time.monotonic()+30)
        z,c,e,keys,firsts,_=C.response_geometry(columns,ib)
        self.assertEqual((z,c,e),(zeros,classes,exposures))
        _,_,receipt=P.compress_model(columns,{1224:F(-1)},[0,1,1224],b())
        self.assertEqual(C.compressed_system(columns,[0,1],keys,firsts,ib),receipt)
    def test_complete_forms_constant_tampering_rejected(self):
        free=list(range(1,1224));records=[dict(coordinate=0,constant='0',terms=[[1,'-1']])]+[dict(coordinate=j,constant='0',terms=[[j,'1']])for j in free]
        rows=[{0:F(1),1:F(1)}]
        forms,_=C.verify_forms(rows,[0],free,records,C.Budget(time.monotonic()+30))
        self.assertEqual(forms[0],{1:F(-1)})
        tampered=copy.deepcopy(records);tampered[0]['constant']='1'
        with self.assertRaises(ValueError):C.verify_forms(rows,[0],free,tampered,C.Budget(time.monotonic()+30))
        tampered=copy.deepcopy(records);tampered[1]['terms']=[]
        with self.assertRaises(ValueError):C.verify_forms(rows,[0],free,tampered,C.Budget(time.monotonic()+30))
    def test_exposed_kernel_span_is_exact_and_not_ray_count(self):
        vectors=[['1','1']+['0']*13,['2','2']+['0']*13,['1','-1']+['0']*13]
        basis=C.kernel_basis(vectors,C.Budget(time.monotonic()+30))
        self.assertEqual(P.canonical_span(vectors,b()),basis)
        self.assertEqual(len(basis),2)
        self.assertEqual(basis[0],['1','0']+['0']*13)
        self.assertEqual(basis[1],['0','1']+['0']*13)
    def test_dimension_only_native_reserve_and_no_fit_failure(self):
        r=P.native_reservation(10,20,150000000)
        preparation=16*10*20+64*(10+20)+1048576
        base=preparation+10**3+2*10*20+1048576
        self.assertEqual(r['max_iterations'],min(10000,(150000000-base)//(2*10*20+10**2)))
        self.assertLessEqual(r['total'],150000000)
        # No solver is imported/called when even the fixed preflight cannotfit.
        out=P.native_proposal([{0:F(1)}],{0:F(-1)},[0],deadline=time.monotonic()+30,max_operations=1)
        self.assertFalse(out['success']);self.assertFalse(out['attempted'])
        self.assertEqual(out['options']['maxiter'],0);self.assertIn('resource_failure',out)
    def test_resource_cap_stops_before_partial_class_admission(self):
        with self.assertRaises(OverflowError):P.discover_lines([{0:F(1),1:F(2)}],P.Budget(time.monotonic()+30,max_operations=1))

if __name__=='__main__':unittest.main()
