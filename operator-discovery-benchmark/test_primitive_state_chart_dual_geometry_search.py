from fractions import Fraction as F
import time
import unittest
from unittest.mock import patch
import primitive_state_chart_dual_geometry_search as G


def budget():return G.Budget(time.monotonic()+30)

class GeometryTests(unittest.TestCase):
    def test_signed_lines_expose_but_positive_compression_stays_separate(self):
        columns=[{0:F(2),2:F(4)},{0:F(6),2:F(12)},{0:F(-1),2:F(-2)},{}]
        classes,zeros,exposed=G.discover_lines(columns,budget());self.assertEqual(zeros,[3]);self.assertEqual(len(classes),1);self.assertEqual(classes[0]['negative_indices'],[2]);self.assertEqual([r['ray_index']for r in exposed],[0,1,2,3])
        for witness in exposed:
            value={}
            for term in witness['combination']:
                for i,q in columns[term['ray_index']].items():value[i]=value.get(i,F(0))+F(term['weight'])*q
            self.assertTrue(all(q==0 for q in value.values()))
        reduced,rhs,mapping=G.compress_model(columns,{2:F(-1)},[0,1,2],budget());self.assertEqual(mapping['column_representatives'],[0,2]);self.assertEqual(mapping['column_map'][1],dict(representative=0,positive_factor='3'));self.assertIsNone(mapping['column_map'][3]);self.assertEqual(mapping['row_representatives'],[0,2]);self.assertEqual(rhs,{2:F(-1)})
    def test_augmented_rows_include_target_and_keep_contradiction(self):
        cols=[{0:F(1),1:F(-2)}];reduced,rhs,r=G.compress_model(cols,{1:F(-1),2:F(3)},[0,1,2,3],budget())
        self.assertEqual(r['row_representatives'],[0,1,2]);self.assertIsNone(r['row_map'][3]);self.assertEqual(rhs,{1:F(-1),2:F(3)});self.assertTrue(all(2 not in col for col in reduced))
        _,_,r=G.compress_model([{0:F(1),1:F(-2)}],{0:F(3),1:F(-6)},[0,1],budget());self.assertEqual(r['row_representatives'],[0]);self.assertEqual(r['row_map'][1]['signed_factor'],'-2')
    def test_exact_kernel_rref_and_forced_scalars(self):
        v=G.canonical_span([['1','2','0'],['2','4','0'],['0','1','1']],budget(),width=3);self.assertEqual(v,[['1','0','-2'],['0','1','1']])
        rays=dict(records=[dict(kind='scalar',coordinate=5),dict(kind='rank_one',block='C',vector=['1']+['0']*14),dict(kind='rank_one',block='C',vector=['2']+['0']*14),dict(kind='rank_one',block='H',vector=['0','1']+['0']*13)])
        scalar,spans=G.exposed_faces(rays,[dict(ray_index=i)for i in range(4)],budget());self.assertEqual(scalar,[5]);self.assertEqual([r['rank']for r in spans],[1,1])
    def test_dimension_only_native_reserve_and_tiny_call(self):
        a=G.native_reservation(2,2,150000000);self.assertEqual(a['max_iterations'],10000);self.assertLessEqual(a['total'],150000000)
        self.assertEqual(a['preparation_work_reserve'],16*4+64*4+1048576)
        compressed=[{0:F(1),2:F(-1)},{0:F(-1),2:F(-1)}]
        result=G.native_proposal(compressed,{2:F(-1)},[0,2],deadline=time.monotonic()+30);self.assertTrue(result['success'],result.get('message'));self.assertEqual(result['options']['maxiter'],10000);self.assertEqual(result['reservation'],a);self.assertFalse(result['options']['presolve'])
        other=G.native_proposal([{0:F(7),2:F(-3)},{0:F(-2),2:F(-8)}],{2:F(-1)},[0,2],deadline=time.monotonic()+30);self.assertEqual(other['options']['maxiter'],result['options']['maxiter'])
    def test_full_synthetic_geometry_and_negative_constant_route(self):
        P=G.P;retained=P.EXACT.full15_recipes([366,613],1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)[0]
        b=budget();rays=P.make_rays(retained,dict(complete=True,final_projected_vector=['0']*1224),b)
        pivots=list(range(782));rows={p:{p:F(1)}for p in pivots};rows[0][1224]=F(-2);free=list(range(782,1224))
        chart=dict(schema='primitive-state-augmented-cone-chart-v1',complete=True,width=1224,original_width=1957,normalized_rows=[dict(pivot=p,terms=[[i,str(q)]for i,q in sorted(row.items())])for p,row in rows.items()],pivot_columns=pivots,free_indices=free,retained_indices=retained)
        saved=[]
        with patch('hashlib.sha256',side_effect=AssertionError('no hashes')),patch.object(G,'native_proposal',side_effect=AssertionError('exact shortcut before LP')):out=G.search(chart,rays,deadline=time.monotonic()+30,save_geometry=saved.append)
        self.assertEqual(out['status'],'CERTIFICATE_PROPOSED',out.get('reason'));self.assertEqual(out['route'],'negative_constant_ray');self.assertEqual(out['certificate']['alpha'][0],'1/2');self.assertEqual(saved[0]['negative_constant_ray'],0);self.assertEqual(len(saved[0]['forms']),1224);self.assertEqual(len(saved[0]['responses']),851);self.assertEqual(out['certificate']['pairing'],'-1');self.assertTrue(out['geometry_complete'])
    def test_resource_gate_never_calls_native_and_retains_counts(self):
        out=G.search({}, {},deadline=time.monotonic()+30);self.assertEqual(out['status'],'UNKNOWN');self.assertFalse(out['geometry_complete']);self.assertIn('geometry',out['stage_counts'])
        with self.assertRaises(OverflowError):G.canonical_span([['1','2']],G.Budget(time.monotonic()+30,1),width=2)
        result=G.native_proposal([{0:F(1)}],{0:F(-1)},[0],deadline=time.monotonic()+30,max_operations=1);self.assertFalse(result['attempted']);self.assertFalse(result['success']);self.assertIn('counts',result)

    def test_native_exception_keeps_reservation_and_attempt(self):
        with patch('scipy.optimize.linprog',side_effect=RuntimeError('synthetic native failure'))as solve:
            result=G.native_proposal([{0:F(1)}],{0:F(-1)},[0],deadline=time.monotonic()+30)
        self.assertEqual(solve.call_count,1);self.assertTrue(result['attempted']);self.assertFalse(result['success'])
        self.assertEqual(result['reservation'],G.native_reservation(1,1,150000000))
        self.assertEqual((result['rows'],result['columns']),(1,1))
        self.assertEqual(result['resource_failure'],'synthetic native failure')
        self.assertGreater(result['counts']['operations'],0)

if __name__=='__main__':unittest.main()
