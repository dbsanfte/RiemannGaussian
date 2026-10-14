from fractions import Fraction as F
import hashlib
import json
import time
import unittest
import primitive_state_equation_projection as P
import primitive_state_exact_row_basis as B

class ProjectionTests(unittest.TestCase):
    def project(self,columns,lhs,domain,keep,recipes,**limits):
        return P.project_equations(columns,lhs,domain,keep,recipes,deadline=time.monotonic()+10,**limits)
    def test_verified_projection_preserves_augmented_row_dependencies(self):
        columns=[{'a':F(1),'b':F(2)},{'a':F(-1),'b':F(-2)},{'a':F(3),'b':F(6)},{'a':F(-11),'b':F(-22)}]
        lhs={'a':F(5),'b':F(10)}
        rows,rhs,r=self.project(columns,lhs,['a','b'],[0,2],{1:{0:F(-1)},3:{0:F(1),2:F(-4)}})
        self.assertTrue(r['complete']);self.assertEqual(rows,[{0:F(1),1:F(3)},{0:F(2),1:F(6)}]);self.assertEqual(rhs,[F(5),F(10)])
        selected,targets,basis=B.reduce_rows(rows,rhs,2,deadline=time.monotonic()+10)
        self.assertEqual(len(selected),1);self.assertEqual(basis['source_hash'],r['projected_rows_hash'])
        self.assertEqual(basis['retained_indices'],[0])
        # Reconstruct each full row from projected coordinates and exact recipes.
        for i,row in enumerate(rows):
            original={j:columns[j].get(['a','b'][i],F(0)) for j in range(4)}
            rebuilt={j:row.get(k,F(0)) for k,j in enumerate([0,2])}
            for omitted,recipe in {1:{0:F(-1)},3:{0:F(1),2:F(-4)}}.items():rebuilt[omitted]=sum((q*rebuilt[j] for j,q in recipe.items()),F(0))
            self.assertEqual(original,rebuilt)
    def test_false_recipe_is_rejected(self):
        with self.assertRaises(ValueError):self.project([{'a':F(1)},{'a':F(2)}],{},['a'],[0],{1:{0:F(-1)}})
    def test_complete_partition_and_domain_required(self):
        cases=[([0],{}),([0,1],{1:{0:F(1)}}),([0],{1:{1:F(1)}}),([True],{1:{0:F(1)}})]
        for keep,recipes in cases:
            with self.assertRaises(ValueError):self.project([{'a':F(1)},{'a':F(1)}],{},['a'],keep,recipes)
        with self.assertRaises(ValueError):self.project([{'a':F(1)}],{},[],[0],{})
        with self.assertRaises(ValueError):self.project([{'a':F(1)}],{},['a','a'],[0],{})
    def test_zero_columns_and_cancellation(self):
        rows,rhs,r=self.project([{'a':F(1)},{'a':F(0)}],{'b':F(1)},['b','a'],[0],{1:{0:F(0)}})
        self.assertEqual(rows,[{},{0:F(1)}]);self.assertEqual(rhs,[F(1),F(0)]);self.assertEqual(r['counts']['identities_verified'],1)
    def test_full15_declaration(self):
        keep,recipes=P.full15_recipes((366,613),1597,{'full_child':15,'full_parent':15,'storage_K':15},1957)
        self.assertEqual(len(keep),1224);self.assertEqual(len(recipes),733)
        self.assertEqual(recipes[367],{366:F(-1)});self.assertEqual(recipes[1837],{1597:F(1),1717:F(-4)})
        self.assertTrue(all(i in keep for i in range(1592,1837)))
        with self.assertRaises(ValueError):P.full15_recipes((1,1),3,{'full_child':14,'full_parent':15,'storage_K':15},363)
    def test_resource_limits_unknown(self):
        for cap in [dict(max_operations=1),dict(max_source_cells=1),dict(max_live_cells=1),dict(max_coefficient_bits=1),dict(max_receipt_bytes=256)]:
            rows,rhs,r=self.project([{'a':F(2)},{'a':F(4)}],{'a':F(1)},['a'],[0],{1:{0:F(2)}},**cap)
            self.assertIsNone(rows);self.assertIsNone(rhs);self.assertEqual(r['status'],'unknown');self.assertFalse(r['complete'])
            self.assertLessEqual(len(json.dumps(r,sort_keys=True,separators=(',',':')).encode()),cap.get('max_receipt_bytes',8388608))
    def test_deadline_and_intermediate_bit_growth(self):
        rows,rhs,r=P.project_equations([{'a':F(1)}],{},['a'],[0],{},deadline=time.monotonic()-1)
        self.assertEqual(r['reason'],'deadline');self.assertIsNone(rows)
        rows,rhs,r=self.project([{'a':F(7)},{}],{},['a'],[0],{1:{0:F(7)}},max_coefficient_bits=3)
        self.assertEqual(r['reason'],'coefficient bit cap');self.assertIsNone(rows)
    def test_exact_inputs_only(self):
        with self.assertRaises(ValueError):self.project([{'a':1.0}],{},['a'],[0],{})
        with self.assertRaises(ValueError):self.project([{'a':F(1)},{}],{},['a'],[0],{1:{0:0.0}})
    def test_receipt_hashes_and_size(self):
        rows,rhs,r=self.project([{'a':F(1)},{'a':F(3)}],{'a':F(2)},['a'],[0],{1:{0:F(3)}})
        def h(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        self.assertEqual(r['full_columns_hash'],h([[[0,'1']],[[0,'3']]]));self.assertEqual(r['target_hash'],h(['2']))
        self.assertEqual(r['projected_rows_hash'],h(dict(rows=[[[0,'1']]],rhs=['2'],variables=1)))
        self.assertEqual(r['counts']['receipt_bytes'],len(json.dumps(r,sort_keys=True,separators=(',',':')).encode()))

if __name__=='__main__':unittest.main()
