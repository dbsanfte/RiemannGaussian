import copy
from fractions import Fraction as F
import json
import time
import unittest
import primitive_state_exact_row_basis as B

# Independent synthetic transcript replay, does not call producer helpers.
def replay(rows,rhs,n,receipt):
    basis=[];selected=[]
    assert receipt['complete'] and receipt['status']=='complete'
    assert receipt['row_order']==sorted(range(len(rows)),key=lambda i:(sum(bool(q) for q in rows[i].values())+bool(rhs[i]),i))
    assert len(receipt['transcript'])==len(rows)
    for record,i in zip(receipt['transcript'],receipt['row_order']):
        assert record['source_row']==i
        r={j:F(q) for j,q in rows[i].items() if q}
        if rhs[i]:r[n]=F(rhs[i])
        for k,m in record['steps']:
            assert 0<=k<len(basis)
            assert min(r)==min(basis[k])
            assert F(m)==r[min(r)]
            for j,q in basis[k].items():
                r[j]=r.get(j,F(0))-F(m)*q
                if not r[j]:del r[j]
        if record['pivot_column']is None:assert not r
        else:
            p=record['pivot_column'];assert p==min(r)
            assert F(record['normalization'])==r[p]
            assert record['basis_index']==len(basis)
            basis.append({j:q/r[p] for j,q in r.items()});selected.append(i)
    assert selected==receipt['retained_indices']
    return basis

class BasisTests(unittest.TestCase):
    def reduce(self,rows,rhs,n=3,**kw):return B.reduce_rows(rows,list(map(F,rhs)),n,deadline=time.monotonic()+10,**kw)
    def test_nonproportional_dependency(self):
        rows=[{0:F(1),1:F(1)},{1:F(1),2:F(1)},{0:F(1),1:F(2),2:F(1)}]
        selected,targets,r=self.reduce(rows,[2,3,5]);replay(rows,list(map(F,[2,3,5])),3,r)
        self.assertEqual(len(selected),2);self.assertEqual(r['coefficient_consistency'],'consistent')
        self.assertTrue(all(any(x is original for original in rows) for x in selected))
    def test_contradictory_target_retained(self):
        rows=[{0:F(1)},{0:F(1)},{},{}]
        selected,targets,r=self.reduce(rows,[1,2,0,3],n=1);basis=replay(rows,list(map(F,[1,2,0,3])),1,r)
        self.assertEqual(r['coefficient_consistency'],'inconsistent');self.assertEqual(len(basis),2)
        self.assertIn(1,r['pivot_columns']);self.assertTrue(any(targets))
    def test_signed_fraction_and_zero(self):
        rows=[{0:F(0)},{0:F(-2),1:F(1,3)},{0:F(6),1:F(-1)}]
        _,_,r=self.reduce(rows,[0,-4,12]);replay(rows,list(map(F,[0,-4,12])),3,r)
        self.assertEqual(r['augmented_rank'],1)
    def test_limits_unknown_no_reduced_system(self):
        for options in [dict(max_operations=1),dict(max_source_cells=1),dict(max_live_cells=1),dict(max_fill_cells=1),dict(max_receipt_bytes=256),dict(max_coefficient_bits=1)]:
            selected,targets,r=self.reduce([{0:F(2),1:F(3)}],[1],**options)
            self.assertIsNone(selected);self.assertIsNone(targets);self.assertFalse(r['complete']);self.assertEqual(r['status'],'unknown')
            self.assertLessEqual(len(json.dumps(r,sort_keys=True,separators=(',',':')).encode()),options.get('max_receipt_bytes',8388608))
    def test_deadline_unknown(self):
        a,b,r=B.reduce_rows([{0:F(1)}],[F(1)],1,deadline=time.monotonic()-1)
        self.assertIsNone(a);self.assertEqual(r['reason'],'deadline')
    def test_tampered_replay_rejects(self):
        rows=[{0:F(1)},{0:F(2)}];_,_,r=self.reduce(rows,[1,2]);r=copy.deepcopy(r)
        r['transcript'][1]['steps'][0][1]='1'
        with self.assertRaises(AssertionError):replay(rows,[F(1),F(2)],3,r)
    def test_source_hash_and_size(self):
        rows=[{0:F(2),2:F(1,3)},{1:F(4)}];rhs=[F(5),F(6)];_,_,r=self.reduce(rows,rhs)
        import hashlib
        encoded={'rows':[[[j,str(q)] for j,q in sorted(row.items())] for row in rows],'rhs':list(map(str,rhs)),'variables':3}
        h=hashlib.sha256(json.dumps(encoded,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        self.assertEqual(h,r['source_hash']);self.assertEqual(len(json.dumps(r,sort_keys=True,separators=(',',':')).encode()),r['counts']['receipt_bytes'])
    def test_sparse_initial_order_not_global_pivot_order(self):
        rows=[{2:F(1)},{0:F(1),2:F(2)},{0:F(3),1:F(1),2:F(6)},{1:F(1)}]
        _,_,r=self.reduce(rows,[2,5,17,2]);replay(rows,list(map(F,[2,5,17,2])),3,r)
        self.assertEqual(r['augmented_rank'],3)
    def test_empty_domain(self):
        selected,targets,r=self.reduce([],[],n=1)
        self.assertEqual(selected,[]);self.assertEqual(targets,[]);self.assertEqual(r['augmented_rank'],0)
    def test_intermediate_bit_growth_limit(self):
        rows=[{0:F(3),1:F(7)},{0:F(7),1:F(3)}]
        selected,targets,r=self.reduce(rows,[1,1],max_coefficient_bits=3)
        self.assertIsNone(selected);self.assertEqual(r['reason'],'coefficient bit cap')
    def test_bad_input(self):
        with self.assertRaises(ValueError):self.reduce([{0:1.0}],[0])
        with self.assertRaises(ValueError):self.reduce([{3:F(1)}],[0])
        with self.assertRaises(ValueError):B.reduce_rows([],[],True,deadline=time.monotonic()+1)

if __name__=='__main__':unittest.main()
